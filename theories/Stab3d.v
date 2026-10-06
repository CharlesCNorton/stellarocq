(** A solution of the collocated three-dimensional problem within C h^2 of
    the exact one, at every fine enough step h = 2^-K.

    The unknowns are perturbations X of the exact node values on the nodes
    m = 2^(K-2) .. 4m, held at zero at both ends. The rows GS and GU of
    Disc3d are their linear part, Recur's rows with Lin3d's blocks, plus a
    remainder that the ball certificate bounds ([rows_s_crude],
    [rows_u_crude]). [Lsol] solves the linear rows for any sources; it is a
    function by Coquelicot's description operator, the solution being unique
    on the nodes by Lin3d.lin_bound. The map T X = Lsol (rows of X less
    GS X, GU X) has the solutions of the collocated problem as its fixed
    points. In the norm [nrm], the largest node value on m .. 4m, the slope
    into node m + 2 over a weight C2, and the largest slope into the nodes
    m + 3 .. 4m, the first row's sources enter the nodes only through the
    start inhomogeneity of Lin3d2 ([lin_nrm]); with consistency of order h^2
    at the exact solution, T contracts by 1/2 a ball of radius C h^2 into
    itself once h is small, and Contract.pseudo_fixed_point gives the
    solution. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat TMEval TMat Shoot Recur CFMS CFMS2 Step NBound Osc
  CellTM CellSound CellN CellMain Frames Assemble Check3d BMat Level3d Final3d Lin3d Lin3d2
  Ball3d Taylor Ball3dSound Affine Row3d Dep Disc3d Contract.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The cells of the ball certificate                                 *)

Lemma pRZm8 : powerRZ 2 (-8) = / 256.
Proof. change (powerRZ 2 (-8)) with (/ 2 ^ 8). f_equal. cbn. ring. Qed.

(** Every node of a level lies in one of the 192 cells of width 2^-8. *)
Lemma ball_cell :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  exists c, (c < 192)%nat /\ dyadR (clo c) <= sK K j <= dyadR (chi c).
Proof.
  intros K j HK Hj.
  destruct (Lin3d.row_split K j HK Hj) as [k [i [t [Hk [Hi [Ht Ej]]]]]].
  exists (16 * k + i / 256)%nat. split.
  - assert (i / 256 < 16)%nat by (apply Nat.Div0.div_lt_upper_bound; lia). lia.
  - unfold sK. rewrite Ej, cutK_s by exact HK.
    assert (Hh := hK_pos K).
    assert (Htf : INR t * hK K <= / 65536 - hK K).
    { rewrite <- (fK_h K HK). assert (Ht' : (t + 1 <= fK K)%nat) by lia. apply le_INR in Ht'.
      rewrite plus_INR in Ht'. cbn in Ht'. nra. }
    assert (Ht0 : 0 <= INR t * hK K) by (apply Rmult_le_pos; [apply pos_INR | lra]).
    assert (Hdm : INR i = 256 * INR (i / 256) + INR (i mod 256)).
    { rewrite (Nat.div_mod_eq i 256) at 1. rewrite plus_INR, mult_INR. cbn. ring. }
    assert (Hq : INR (i mod 256) <= 255).
    { assert (H := Nat.mod_upper_bound i 256 ltac:(lia)).
      replace 255 with (INR 255) by (cbn; ring). apply le_INR. lia. }
    assert (Hq0 := pos_INR (i mod 256)).
    unfold dyadR, clo, chi. cbn [fst snd]. rewrite <- !INR_IZR_INZ.
    rewrite !plus_INR, !mult_INR, pRZm8.
    replace (INR 64) with 64 by (cbn; ring). replace (INR 65) with 65 by (cbn; ring).
    replace (INR 16) with 16 by (cbn; ring).
    rewrite Hdm. split; lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The rows are linear and read three nodes                          *)

Lemma slope_vdiff : forall h X Y j c, slope h (vdiff X Y) j c = slope h X j c - slope h Y j c.
Proof. intros. unfold slope, vdiff. unfold Rdiv. ring. Qed.

Lemma rs_row_sub :
  forall h Pp Pm Sx X Y j i,
  rs_row h Pp Pm Sx (vdiff X Y) j i = rs_row h Pp Pm Sx X j i - rs_row h Pp Pm Sx Y j i.
Proof.
  intros h Pp Pm Sx X Y j i. unfold rs_row.
  rewrite (mv_extn 9 (Pp j) (slope h (vdiff X Y) (S j)) (fun c => slope h X (S j) c - slope h Y (S j) c))
    by (intros; apply slope_vdiff).
  rewrite (mv_extn 9 (Pm j) (slope h (vdiff X Y) j) (fun c => slope h X j c - slope h Y j c))
    by (intros; apply slope_vdiff).
  rewrite (mv_extn 9 (Sx j) (vdiff X Y j) (fun c => X j c - Y j c)) by (intros; reflexivity).
  rewrite !mv_sub. unfold Rdiv. ring.
Qed.

Lemma ru_row_sub :
  forall h Up V X Y j i, ru_row h Up V (vdiff X Y) j i = ru_row h Up V X j i - ru_row h Up V Y j i.
Proof.
  intros h Up V X Y j i. unfold ru_row.
  rewrite (mv_extn 9 (Up j) (slope h (vdiff X Y) (S j)) (fun c => slope h X (S j) c - slope h Y (S j) c))
    by (intros; apply slope_vdiff).
  rewrite (mv_extn 9 (V j) (vdiff X Y j) (fun c => X j c - Y j c)) by (intros; reflexivity).
  rewrite !mv_sub. ring.
Qed.

Lemma rs_row_ext :
  forall h Pp Pm Sx X Y j i, (1 <= j)%nat ->
  (forall l c, (j - 1 <= l <= S j)%nat -> (c < 9)%nat -> X l c = Y l c) ->
  rs_row h Pp Pm Sx X j i = rs_row h Pp Pm Sx Y j i.
Proof.
  intros h Pp Pm Sx X Y j i Hj H. unfold rs_row.
  rewrite (mv_extn 9 (Pp j) (slope h X (S j)) (slope h Y (S j)))
    by (intros c Hc; unfold slope; replace (S j - 1)%nat with j by lia; rewrite !H by lia; reflexivity).
  rewrite (mv_extn 9 (Pm j) (slope h X j) (slope h Y j))
    by (intros c Hc; unfold slope; rewrite !H by lia; reflexivity).
  rewrite (mv_extn 9 (Sx j) (X j) (Y j)) by (intros c Hc; apply H; lia).
  reflexivity.
Qed.

Lemma ru_row_ext :
  forall h Up V X Y j i,
  (forall l c, (j <= l <= S j)%nat -> (c < 9)%nat -> X l c = Y l c) ->
  ru_row h Up V X j i = ru_row h Up V Y j i.
Proof.
  intros h Up V X Y j i H. unfold ru_row.
  rewrite (mv_extn 9 (Up j) (slope h X (S j)) (slope h Y (S j)))
    by (intros c Hc; unfold slope; replace (S j - 1)%nat with j by lia; rewrite !H by lia; reflexivity).
  rewrite (mv_extn 9 (V j) (X j) (Y j)) by (intros c Hc; apply H; lia).
  reflexivity.
Qed.

Lemma mv_zero_vec : forall n A i, mv n A (fun _ => 0) i = 0.
Proof.
  intros n A i. unfold mv. rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
Qed.

Lemma zeta_zero : forall K j c, zeta3 K j (fun _ => 0) (fun _ => 0) c = 0.
Proof.
  intros K j c. unfold zeta3, zeta.
  assert (Hs0 : forall k, stack (fun i => hK K * 0) (fun _ => 0) k = 0)
    by (intros k; unfold stack; destruct (Nat.ltb k 5); cbv beta; ring).
  assert (Hb : forall i, mv 9 (Mi (Pp3 K j) (Up3 K j)) (stack (fun i => hK K * 0) (fun _ => 0)) i = 0).
  { intros i. rewrite (mv_extn 9 _ _ (fun _ => 0)) by (intros k _; apply Hs0). apply mv_zero_vec. }
  unfold zjoin. destruct (Nat.ltb c 9).
  - apply Hb.
  - rewrite (mv_extn 9 _ _ (fun _ => 0)) by (intros k _; apply Hb). rewrite mv_zero_vec. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* The linear rows solved as a function of their sources             *)

(** The linear rows with sources rs, ru and both ends held at zero. *)
Definition lrows (K : nat) (rs ru : nat -> vec) (X : nat -> vec) : Prop :=
  (forall i, (i < 9)%nat -> X (cutK K 0) i = 0) /\ (forall i, (i < 9)%nat -> X (cutK K 12) i = 0) /\
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs j i) /\
     (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru j i)).

Lemma lrows_sub :
  forall K rs ru rs' ru' X Y, lrows K rs ru X -> lrows K rs' ru' Y -> lrows K (vdiff rs rs') (vdiff ru ru') (vdiff X Y).
Proof.
  intros K rs ru rs' ru' X Y [HX0 [HX1 HX]] [HY0 [HY1 HY]]. split; [| split].
  - intros i Hi. unfold vdiff. rewrite HX0, HY0 by exact Hi. ring.
  - intros i Hi. unfold vdiff. rewrite HX1, HY1 by exact Hi. ring.
  - intros j Hj. destruct (HX j Hj) as [Hs Hu]. destruct (HY j Hj) as [Hs' Hu']. split.
    + intros i Hi. rewrite rs_row_sub, Hs, Hs' by exact Hi. reflexivity.
    + intros i Hi. rewrite ru_row_sub, Hu, Hu' by exact Hi. reflexivity.
Qed.

(** The solution of the linear rows on the interior nodes, zero elsewhere. *)
Definition Lsol (K : nat) (rs ru : nat -> vec) : nat -> vec :=
  fun j i => if Nat.ltb (cutK K 0) j && Nat.ltb j (cutK K 12) && Nat.ltb i 9
             then Hierarchy.iota (fun x : R => exists X, lrows K rs ru X /\ X j i = x) else 0.

Lemma Lsol_out :
  forall K rs ru j i, ~ ((cutK K 0 < j < cutK K 12)%nat /\ (i < 9)%nat) -> Lsol K rs ru j i = 0.
Proof.
  intros K rs ru j i H. unfold Lsol.
  destruct (Nat.ltb_spec (cutK K 0) j); destruct (Nat.ltb_spec j (cutK K 12)); destruct (Nat.ltb_spec i 9);
    cbn [andb]; try reflexivity.
  exfalso. apply H. lia.
Qed.

Section Lsol.

Variable prec : F.precision.
Variables d kn : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs0 : imat.
Variable Rd : list (list (list (list (Z * Z)))).
Variables BM BMM BQ : Z * Z.

Hypothesis Hcells2 : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges2 prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI BM BMM BQ
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hstart : forall WiI, owi prec frames 0 = Some WiI -> start_range prec d (mktab d) chh chh kn WiI = Some rs0.
Hypothesis Hok : assemble3d prec frames es cells rs0 Rd = true.

Let Hc1 := Lin3d2.Hcells prec d kn Hcov Hd frames cells BM BMM BQ Hcells2.

(** Two solutions of the same rows agree on the nodes. *)
Lemma lrows_unique :
  forall K, (16 <= K)%nat -> forall rs ru X Y, lrows K rs ru X -> lrows K rs ru Y ->
  forall j i, (cutK K 0 < j <= cutK K 12)%nat -> (i < 9)%nat -> X j i = Y j i.
Proof.
  intros K HK rs ru X Y HX HY j i Hj Hi.
  destruct (lin_bound prec d kn Hcov Hd frames es cells rs0 Rd Hc1 Hstart Hok) as [Sc [HS0 HS]].
  destruct (lrows_sub K rs ru rs ru X Y HX HY) as [H0 [H1 Hr]].
  assert (Hz : forall j, (cutK K 0 < j < cutK K 12)%nat ->
            (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) (vdiff X Y) j i = (fun _ _ => 0) j i) /\
            (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) (vdiff X Y) j i = (fun _ _ => 0) j i)).
  { intros l Hl. destruct (Hr l Hl) as [Hs Hu]. split.
    - intros c Hc. rewrite Hs by exact Hc. unfold vdiff. ring.
    - intros c Hc. rewrite Hu by exact Hc. unfold vdiff. ring. }
  assert (B := HS K HK (fun _ _ => 0) (fun _ _ => 0) (vdiff X Y) H0 H1 Hz j Hj).
  assert (E0 : srcw K (fun _ _ => 0) (fun _ _ => 0) = 0).
  { unfold srcw. transitivity (msum (fun _ : nat => 0) (cutK K 12 - S (cutK K 0))); [| apply msum_zero].
    apply msum_ext. intros l _.
    rewrite (vnorm_ext 14 _ (fun _ => 0)) by (intros c _; apply zeta_zero). rewrite vnorm_zero. ring. }
  rewrite E0, Rmult_0_r in B.
  assert (Hv : Rabs (vdiff X Y j i) <= 0).
  { eapply Rle_trans; [| exact B]. unfold state.
    replace (vdiff X Y j i) with (zjoin (vdiff X Y j) (mv 9 (Pm3 K j) (slope (hK K) (vdiff X Y) j)) i)
      by (apply zjoin_lo; exact Hi).
    apply vnorm_ge. lia. }
  unfold vdiff in Hv. assert (Hp := Rabs_pos (X j i - Y j i)).
  assert (E : Rabs (X j i - Y j i) = 0) by lra. apply Rabs_eq_0 in E. lra.
Qed.

Lemma Lsol_spec :
  forall K, (16 <= K)%nat -> forall rs ru X, lrows K rs ru X ->
  forall j i, (cutK K 0 < j < cutK K 12)%nat -> (i < 9)%nat -> Lsol K rs ru j i = X j i.
Proof.
  intros K HK rs ru X HX j i Hj Hi. unfold Lsol.
  replace (Nat.ltb (cutK K 0) j && Nat.ltb j (cutK K 12) && Nat.ltb i 9) with true
    by (symmetry; apply andb_true_intro; split; [apply andb_true_intro; split|]; apply Nat.ltb_lt; lia).
  apply (Hierarchy.iota_unique (V := R_CompleteNormedModule)).
  - intros y [Y [HY <-]]. exact (lrows_unique K HK rs ru Y X HY HX j i ltac:(lia) Hi).
  - exists X. split; [exact HX | reflexivity].
Qed.

Lemma Lsol_lrows : forall K, (16 <= K)%nat -> forall rs ru, lrows K rs ru (Lsol K rs ru).
Proof.
  intros K HK rs ru.
  destruct (lin_exists prec d kn Hcov Hd frames es cells rs0 Rd Hc1 Hstart Hok K HK rs ru) as [X [HX0 [HX1 HXr]]].
  assert (HX : lrows K rs ru X) by (split; [intros i Hi; apply HX0; lia | split; assumption]).
  assert (Hm := cutK_0_pos K). assert (H12 : (cutK K 0 < cutK K 12)%nat) by (rewrite cutK_12 by exact HK; lia).
  assert (Hag : forall l c, (cutK K 0 <= l <= cutK K 12)%nat -> (c < 9)%nat -> Lsol K rs ru l c = X l c).
  { intros l c Hl Hc. destruct (Nat.eq_dec l (cutK K 0)) as [->|H0].
    - rewrite Lsol_out by lia. rewrite HX0 by lia. reflexivity.
    - destruct (Nat.eq_dec l (cutK K 12)) as [->|H1].
      + rewrite Lsol_out by lia. rewrite HX1 by exact Hc. reflexivity.
      + apply (Lsol_spec K HK rs ru X HX); lia. }
  split; [| split].
  - intros i Hi. apply Lsol_out. lia.
  - intros i Hi. apply Lsol_out. lia.
  - intros j Hj. destruct (HXr j Hj) as [Hs Hu]. split.
    + intros i Hi. rewrite <- (Hs i Hi). apply rs_row_ext; [lia|]. intros l c Hl Hc. apply Hag; lia.
    + intros i Hi. rewrite <- (Hu i Hi). apply ru_row_ext. intros l c Hl Hc. apply Hag; lia.
Qed.

Lemma Lsol_sub :
  forall K, (16 <= K)%nat -> forall rs ru rs' ru' j i,
  Lsol K rs ru j i - Lsol K rs' ru' j i = Lsol K (vdiff rs rs') (vdiff ru ru') j i.
Proof.
  intros K HK rs ru rs' ru' j i.
  destruct (Nat.ltb_spec (cutK K 0) j); [destruct (Nat.ltb_spec j (cutK K 12)); [destruct (Nat.ltb_spec i 9)|]|].
  - symmetry. apply (Lsol_spec K HK (vdiff rs rs') (vdiff ru ru') (vdiff (Lsol K rs ru) (Lsol K rs' ru')));
      [| lia | exact H1].
    apply lrows_sub; apply Lsol_lrows; exact HK.
  - rewrite !Lsol_out by lia. ring.
  - rewrite !Lsol_out by lia. ring.
  - rewrite !Lsol_out by lia. ring.
Qed.

End Lsol.

(* ---------------------------------------------------------------- *)
(* The norm                                                          *)

(** The largest node value on m .. 4m, the slope into node m + 2 over the
    weight C2, and the largest slope into the nodes m + 3 .. 4m. *)
Definition nrm (K : nat) (C2 : R) (x : nat -> vec) : R :=
  Rmax (fmax (fun l => vnorm 9 (x (cutK K 0 + l)%nat)) (S (cutK K 12 - cutK K 0)))
       (Rmax (vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) / C2)
             (fmax (fun l => vnorm 9 (slope (hK K) x (S (S (S (cutK K 0))) + l)%nat))
                   (cutK K 12 - S (S (cutK K 0))))).

Definition dist (K : nat) (C2 : R) (x y : nat -> vec) : R := nrm K C2 (vdiff x y).

Lemma cutK_gap : forall K, (cutK K 0 + 3 <= cutK K 12)%nat.
Proof. intros K. assert (H := fK_pos K). unfold cutK. lia. Qed.

Lemma nrm_nonneg : forall K C2 x, 0 <= nrm K C2 x.
Proof. intros K C2 x. unfold nrm. eapply Rle_trans; [apply fmax_nonneg | apply Rmax_l]. Qed.

Lemma nrm_node :
  forall K C2 x j, (cutK K 0 <= j <= cutK K 12)%nat -> vnorm 9 (x j) <= nrm K C2 x.
Proof.
  intros K C2 x j Hj. unfold nrm. eapply Rle_trans; [| apply Rmax_l].
  replace j with (cutK K 0 + (j - cutK K 0))%nat at 1 by lia.
  apply (fmax_ge (fun l => vnorm 9 (x (cutK K 0 + l)%nat))). lia.
Qed.

Lemma nrm_slope2 :
  forall K C2 x, 0 < C2 -> vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) <= C2 * nrm K C2 x.
Proof.
  intros K C2 x HC.
  assert (H : vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) / C2 <= nrm K C2 x).
  { unfold nrm. eapply Rle_trans; [| apply Rmax_r]. apply Rmax_l. }
  apply (Rmult_le_compat_l C2) in H; [| lra]. unfold Rdiv in H.
  replace (C2 * (vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) * / C2)) with (vnorm 9 (slope (hK K) x (S (S (cutK K 0)))))
    in H by (field; lra).
  exact H.
Qed.

Lemma nrm_slope3 :
  forall K C2 x j, (S (S (S (cutK K 0))) <= j <= cutK K 12)%nat -> vnorm 9 (slope (hK K) x j) <= nrm K C2 x.
Proof.
  intros K C2 x j Hj. unfold nrm. eapply Rle_trans; [| apply Rmax_r]. eapply Rle_trans; [| apply Rmax_r].
  replace j with (S (S (S (cutK K 0))) + (j - S (S (S (cutK K 0)))))%nat at 1 by lia.
  apply (fmax_ge (fun l => vnorm 9 (slope (hK K) x (S (S (S (cutK K 0))) + l)%nat))). lia.
Qed.

Lemma nrm_le :
  forall K C2 x e, 0 <= e ->
  (forall j, (cutK K 0 <= j <= cutK K 12)%nat -> vnorm 9 (x j) <= e) ->
  vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) / C2 <= e ->
  (forall j, (S (S (S (cutK K 0))) <= j <= cutK K 12)%nat -> vnorm 9 (slope (hK K) x j) <= e) ->
  nrm K C2 x <= e.
Proof.
  intros K C2 x e He H1 H2 H3. assert (G := cutK_gap K).
  unfold nrm. apply Rmax_lub; [| apply Rmax_lub; [exact H2|]].
  - apply fmax_le; [exact He|]. intros l Hl. apply H1. lia.
  - apply fmax_le; [exact He|]. intros l Hl. apply H3. lia.
Qed.

Lemma vnorm_add_le : forall n a b, vnorm n (fun c => a c + b c) <= vnorm n a + vnorm n b.
Proof.
  intros n a b. apply vnorm_le; [apply Rplus_le_le_0_compat; apply vnorm_nonneg|].
  intros i Hi. eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; apply vnorm_ge; exact Hi.
Qed.

Lemma vnorm_ext_abs : forall n x y, (forall c, (c < n)%nat -> Rabs (x c) = Rabs (y c)) -> vnorm n x = vnorm n y.
Proof. intros n x y H. unfold vnorm. apply Rle_antisym; apply fmax_mono; intros i Hi; rewrite H by exact Hi; lra. Qed.

Lemma nrm_mono :
  forall K C2 x y, 0 < C2 ->
  (forall j, (cutK K 0 <= j <= cutK K 12)%nat -> vnorm 9 (x j) <= vnorm 9 (y j)) ->
  vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) <= vnorm 9 (slope (hK K) y (S (S (cutK K 0)))) ->
  (forall j, (S (S (S (cutK K 0))) <= j <= cutK K 12)%nat -> vnorm 9 (slope (hK K) x j) <= vnorm 9 (slope (hK K) y j)) ->
  nrm K C2 x <= nrm K C2 y.
Proof.
  intros K C2 x y HC H1 H2 H3. apply nrm_le; [apply nrm_nonneg | | |].
  - intros j Hj. eapply Rle_trans; [apply H1; exact Hj | apply nrm_node; exact Hj].
  - assert (H := nrm_slope2 K C2 y HC). apply (Rmult_le_reg_l C2); [lra|]. unfold Rdiv.
    replace (C2 * (vnorm 9 (slope (hK K) x (S (S (cutK K 0)))) * / C2))
      with (vnorm 9 (slope (hK K) x (S (S (cutK K 0))))) by (field; lra).
    lra.
  - intros j Hj. eapply Rle_trans; [apply H3; exact Hj | apply nrm_slope3; exact Hj].
Qed.

Lemma slope_vdiff3 :
  forall h (x y z : nat -> vec) j c, slope h (vdiff x z) j c = slope h (vdiff x y) j c + slope h (vdiff y z) j c.
Proof. intros. unfold slope, vdiff. unfold Rdiv. ring. Qed.

Lemma dist_nonneg : forall K C2 x y, 0 <= dist K C2 x y.
Proof. intros. apply nrm_nonneg. Qed.

Lemma dist_sym : forall K C2 x y, 0 < C2 -> dist K C2 x y = dist K C2 y x.
Proof.
  intros K C2 x y HC. unfold dist.
  assert (E1 : forall a b j, vnorm 9 (vdiff a b j) = vnorm 9 (vdiff b a j))
    by (intros a b j; apply vnorm_ext_abs; intros c _; unfold vdiff; apply Rabs_minus_sym).
  assert (E2 : forall a b j, vnorm 9 (slope (hK K) (vdiff a b) j) = vnorm 9 (slope (hK K) (vdiff b a) j))
    by (intros a b j; apply vnorm_ext_abs; intros c _; rewrite !slope_vdiff; apply Rabs_minus_sym).
  apply Rle_antisym; apply nrm_mono; try exact HC; intros; first [rewrite E1 | rewrite E2]; lra.
Qed.

Lemma dist_refl : forall K C2 x, 0 < C2 -> dist K C2 x x = 0.
Proof.
  intros K C2 x HC. unfold dist. apply Rle_antisym; [| apply nrm_nonneg].
  assert (E1 : forall j, vnorm 9 (vdiff x x j) = 0).
  { intros j. rewrite (vnorm_ext 9 _ (fun _ => 0)) by (intros c _; unfold vdiff; ring). apply vnorm_zero. }
  assert (E2 : forall j, vnorm 9 (slope (hK K) (vdiff x x) j) = 0).
  { intros j. rewrite (vnorm_ext 9 _ (fun _ => 0)) by (intros c _; rewrite slope_vdiff; ring). apply vnorm_zero. }
  apply nrm_le; [lra | | |].
  - intros j _. rewrite E1. lra.
  - rewrite E2. unfold Rdiv. rewrite Rmult_0_l. lra.
  - intros j _. rewrite E2. lra.
Qed.

Lemma dist_tri : forall K C2 x y z, 0 < C2 -> dist K C2 x z <= dist K C2 x y + dist K C2 y z.
Proof.
  intros K C2 x y z HC. unfold dist.
  assert (Hn1 := nrm_nonneg K C2 (vdiff x y)). assert (Hn2 := nrm_nonneg K C2 (vdiff y z)).
  apply nrm_le; [lra | | |].
  - intros j Hj. rewrite (vnorm_ext 9 (vdiff x z j) (fun c => vdiff x y j c + vdiff y z j c))
      by (intros c _; unfold vdiff; ring).
    eapply Rle_trans; [apply vnorm_add_le|].
    apply Rplus_le_compat; apply nrm_node; exact Hj.
  - rewrite (vnorm_ext 9 (slope (hK K) (vdiff x z) _)
               (fun c => slope (hK K) (vdiff x y) (S (S (cutK K 0))) c + slope (hK K) (vdiff y z) (S (S (cutK K 0))) c))
      by (intros c _; apply slope_vdiff3).
    assert (A := vnorm_add_le 9 (slope (hK K) (vdiff x y) (S (S (cutK K 0)))) (slope (hK K) (vdiff y z) (S (S (cutK K 0))))).
    assert (B1 := nrm_slope2 K C2 (vdiff x y) HC). assert (B2 := nrm_slope2 K C2 (vdiff y z) HC).
    apply (Rmult_le_reg_l C2); [lra|]. unfold Rdiv.
    match goal with |- C2 * (?v * / C2) <= _ => replace (C2 * (v * / C2)) with v by (field; lra) end.
    lra.
  - intros j Hj. rewrite (vnorm_ext 9 (slope (hK K) (vdiff x z) j)
                            (fun c => slope (hK K) (vdiff x y) j c + slope (hK K) (vdiff y z) j c))
      by (intros c _; apply slope_vdiff3).
    eapply Rle_trans; [apply vnorm_add_le|].
    apply Rplus_le_compat; apply nrm_slope3; exact Hj.
Qed.

(** The coordinates the distance reads. *)
Definition coordsK (K : nat) : list (nat * nat) :=
  list_prod (seq (cutK K 0) (S (cutK K 12 - cutK K 0))) (seq 0 9).

Lemma dist_coord :
  forall K C2 x y p, In p (coordsK K) -> Rabs (x (fst p) (snd p) - y (fst p) (snd p)) <= 1 * dist K C2 x y.
Proof.
  intros K C2 x y [j c] Hp. unfold coordsK in Hp. apply in_prod_iff in Hp. destruct Hp as [Hj Hc].
  apply in_seq in Hj, Hc. cbn [fst snd]. rewrite Rmult_1_l. unfold dist. assert (G := cutK_gap K).
  eapply Rle_trans; [| apply (nrm_node K C2 (vdiff x y) j); lia].
  apply (vnorm_ge 9 (vdiff x y j) c). lia.
Qed.

Lemma dist_coords :
  forall K C2 x y e, 1 <= C2 -> 0 <= e ->
  (forall p, In p (coordsK K) -> Rabs (x (fst p) (snd p) - y (fst p) (snd p)) <= e) ->
  dist K C2 x y <= (1 + 2 / hK K) * e.
Proof.
  intros K C2 x y e HC He H. assert (Hh := hK_pos K).
  assert (Hin : forall j c, (cutK K 0 <= j <= cutK K 12)%nat -> (c < 9)%nat -> Rabs (vdiff x y j c) <= e).
  { intros j c Hj Hc. apply (H (j, c)). unfold coordsK. apply in_prod; apply in_seq; lia. }
  assert (Hsl : forall j c, (S (cutK K 0) <= j <= cutK K 12)%nat -> (c < 9)%nat ->
            Rabs (slope (hK K) (vdiff x y) j c) <= 2 / hK K * e).
  { intros j c Hj Hc. unfold slope. unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ hK K))
      by (left; apply Rinv_0_lt_compat; lra).
    assert (A1 := Hin j c ltac:(lia) Hc). assert (A2 := Hin (j - 1)%nat c ltac:(lia) Hc).
    assert (A3 := Rabs_triang (vdiff x y j c) (- vdiff x y (j - 1)%nat c)). rewrite Rabs_Ropp in A3.
    assert (Hi : 0 < / hK K) by (apply Rinv_0_lt_compat; lra).
    unfold Rminus. apply (Rle_trans _ ((e + e) * / hK K)); [apply Rmult_le_compat_r; lra | right; field; lra]. }
  assert (H2e : e <= (1 + 2 / hK K) * e).
  { assert (0 <= 2 / hK K * e) by (apply Rmult_le_pos; [unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra] | exact He]).
    nra. }
  assert (H2s : 2 / hK K * e <= (1 + 2 / hK K) * e) by nra.
  unfold dist. apply nrm_le; [nra | | |].
  - intros j Hj. eapply Rle_trans; [| exact H2e]. apply vnorm_le; [exact He|]. intros c Hc. apply Hin; assumption.
  - assert (Hv : vnorm 9 (slope (hK K) (vdiff x y) (S (S (cutK K 0)))) <= 2 / hK K * e).
    { apply vnorm_le; [apply Rmult_le_pos; [unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra] | exact He]|].
      intros c Hc. apply Hsl; [assert (G := cutK_gap K); lia | exact Hc]. }
    eapply Rle_trans; [| exact H2s]. unfold Rdiv at 1.
    apply (Rle_trans _ (vnorm 9 (slope (hK K) (vdiff x y) (S (S (cutK K 0)))) * 1)); [| lra].
    apply Rmult_le_compat_l; [apply vnorm_nonneg|]. rewrite <- Rinv_1. apply Rinv_le_contravar; lra.
  - intros j Hj. eapply Rle_trans; [| exact H2s]. apply vnorm_le;
      [apply Rmult_le_pos; [unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra] | exact He]|].
    intros c Hc. apply Hsl; [lia | exact Hc].
Qed.

(* ---------------------------------------------------------------- *)
(* The linear solution in the norm                                    *)

Lemma msum_const : forall c n, msum (fun _ => c) n = INR n * c.
Proof. intros c n. induction n as [|n IH]; cbn [msum]; [cbn; ring|]. rewrite IH, S_INR. ring. Qed.

Lemma vnorm_zjoin_lo : forall x p, vnorm 9 x <= vnorm 14 (zjoin x p).
Proof.
  intros x p. rewrite (vnorm_ext 9 x (zx (zjoin x p))) by (intros c Hc; unfold zx; rewrite zjoin_lo by exact Hc; reflexivity).
  apply vnorm_lo9.
Qed.

Lemma fK_ge2 : forall K, (17 <= K)%nat -> (1 < fK K)%nat.
Proof.
  intros K HK. unfold fK. replace (K - 16)%nat with (S (K - 17)) by lia. rewrite Nat.pow_succ_r'.
  assert (H := Nat.pow_nonzero 2 (K - 17) ltac:(lia)). lia.
Qed.

Section LinB.

Variable prec : F.precision.
Variables d kn : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs0 : imat.
Variable Rd : list (list (list (list (Z * Z)))).
Variables BM BMM BQ : Z * Z.

Hypothesis Hcells2 : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges2 prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI BM BMM BQ
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hstart : forall WiI, owi prec frames 0 = Some WiI -> start_range prec d (mktab d) chh chh kn WiI = Some rs0.
Hypothesis Hok : assemble3d prec frames es cells rs0 Rd = true.

Variable S2 : R.
Hypothesis HS2 :
  0 <= S2 /\
  forall K, (17 <= K)%nat -> forall (rs ru : nat -> vec) (X : nat -> vec) (Y : mat),
  is_inv 14 (PsiK K (S (cutK K 0))) Y ->
  (forall i, (i < 9)%nat -> X (cutK K 0) i = 0) ->
  (forall i, (i < 9)%nat -> X (cutK K 12) i = 0) ->
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs j i) /\
     (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru j i)) ->
  forall j, (S (S (cutK K 0)) <= j <= cutK K 12)%nat ->
  vnorm 14 (state (hK K) (Pm3 K) X j)
  <= S2 * (vnorm 5 (gst K Y (rs (S (cutK K 0))) (ru (S (cutK K 0)))) + srcw2 K rs ru).

Let NM := Nmax prec frames es cells.
Let PI := PsiInvB prec frames es cells.
Let CG := cg prec frames es cells BM BMM BQ.

Lemma NM_nonneg : 0 <= NM.
Proof. exact (Nmax_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok). Qed.
Lemma PI_nonneg : 0 <= PI.
Proof. exact (PsiInvB_nonneg prec d Hd frames es cells rs0 Rd Hok). Qed.
Lemma CG_nonneg : 0 <= CG.
Proof. exact (cg_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok). Qed.
Lemma BMr_nonneg : 0 <= dyadR BM.
Proof. exact (BM_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok). Qed.
Lemma BQr_nonneg : 0 <= dyadR BQ.
Proof. exact (BQ_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok). Qed.

(** A solution's next slope from its state and the row's sources. *)
Lemma slope_bnd :
  forall K (X : nat -> vec) rs ru j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs i) ->
  (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru i) ->
  vnorm 9 (slope (hK K) X (S j)) <= NM * vnorm 14 (state (hK K) (Pm3 K) X j) + dyadR BM * (hK K * vnorm 5 rs + vnorm 4 ru).
Proof.
  intros K X rs ru j HK Hj Hs Hu.
  assert (HN := N_bound prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K j HK Hj).
  assert (HZ := zeta_x_bound prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K j rs ru HK Hj).
  assert (H0 := NM_nonneg). assert (H1 := BMr_nonneg). assert (Hh := hK_pos K).
  apply vnorm_le.
  { apply Rplus_le_le_0_compat; [apply Rmult_le_pos; [exact H0 | apply vnorm_nonneg]|].
    apply Rmult_le_pos; [exact H1|]. apply Rplus_le_le_0_compat; [apply Rmult_le_pos; [lra | apply vnorm_nonneg] | apply vnorm_nonneg]. }
  intros i Hi. rewrite (slope_step prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K j X rs ru HK Hj Hs Hu i Hi).
  eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat.
  - eapply Rle_trans; [apply (vnorm_ge 14 (mv 14 (bN (INR j * hK K) (hK K)) (state (hK K) (Pm3 K) X j)) i); lia|].
    eapply Rle_trans; [apply vnorm_mv|]. apply Rmult_le_compat_r; [apply vnorm_nonneg | exact HN].
  - eapply Rle_trans; [| exact HZ]. change (zeta3 K j rs ru i) with (zx (zeta3 K j rs ru) i). apply vnorm_ge. exact Hi.
Qed.

(** The linear solution in the norm: the first row's sources reach the nodes
    through the start inhomogeneity, with h^2 and h, and the slope into
    node m + 2 through the first state. *)
Lemma lin_nrm :
  forall K C2 rs ru a1 b1 A B e, (17 <= K)%nat -> 0 < C2 ->
  0 <= a1 -> 0 <= b1 -> 0 <= A -> 0 <= B ->
  vnorm 5 (rs (S (cutK K 0))) <= a1 -> vnorm 4 (ru (S (cutK K 0))) <= b1 ->
  (forall j, (S (S (cutK K 0)) <= j < cutK K 12)%nat -> vnorm 5 (rs j) <= A /\ vnorm 4 (ru j) <= B) ->
  let h := hK K in
  let sb := S2 * (CG * (h * h * a1 + h * b1) + 3 / 4 * ((1 + dyadR BQ) * (dyadR BM * (h * A + B)) + A)) in
  let s2 := NM * (PI * (sb + h * ((1 + dyadR BQ) * (dyadR BM * (h * a1 + b1)) + a1))) + dyadR BM * (h * a1 + b1) in
  sb + h * s2 <= e -> s2 <= C2 * e -> NM * sb + dyadR BM * (h * A + B) <= e ->
  nrm K C2 (Lsol K rs ru) <= e.
Proof.
  intros K C2 rs ru a1 b1 A B e HK HC Ha1 Hb1 HA HB H1 H2 Hr h sb s2 E1 E2 E3.
  assert (HK16 : (16 <= K)%nat) by lia. assert (Hh := hK_pos K). assert (Hh' : 0 < h) by exact Hh.
  assert (Hm0 := cutK_0_pos K). assert (H12 := cutK_12 K HK16). assert (G := cutK_gap K).
  assert (HNM := NM_nonneg). assert (HPI := PI_nonneg). assert (HCG := CG_nonneg).
  assert (HBM := BMr_nonneg). assert (HBQ := BQr_nonneg). assert (HS0 := proj1 HS2).
  destruct (Lsol_lrows prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok K HK16 rs ru)
    as [HD0 [HD1 HDr]].
  destruct (Psi_first_inv prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K 1 HK16 (fK_ge2 K HK))
    as [Y [HY HYn]].
  rewrite Nat.add_1_r in HY. fold PI in HYn.
  (* the sources of the rows from m + 2 on *)
  set (X0 := (1 + dyadR BQ) * (dyadR BM * (h * A + B)) + A).
  assert (HX0 : 0 <= X0).
  { unfold X0. assert (0 <= dyadR BM * (h * A + B)) by (apply Rmult_le_pos; [lra | nra]). nra. }
  assert (Hsw : srcw2 K rs ru <= 3 / 4 * X0).
  { unfold srcw2.
    apply (Rle_trans _ (msum (fun _ => h * X0) (cutK K 12 - S (S (cutK K 0))))).
    - apply msum_le. intros l Hl. apply Rmult_le_compat_l; [unfold h; lra|].
      destruct (Hr (S (S (cutK K 0)) + l)%nat ltac:(lia)) as [Ha Hb].
      eapply Rle_trans;
        [apply (zeta_bound prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K (S (S (cutK K 0)) + l)%nat
                  (rs (S (S (cutK K 0)) + l)%nat) (ru (S (S (cutK K 0)) + l)%nat) HK16 ltac:(lia))|].
      unfold X0. apply Rplus_le_compat; [| exact Ha].
      apply Rmult_le_compat_l; [lra|]. apply Rmult_le_compat_l; [exact HBM|].
      apply Rplus_le_compat; [apply Rmult_le_compat_l; [unfold h; lra | exact Ha] | exact Hb].
    - rewrite msum_const.
      assert (Hn : INR (cutK K 12 - S (S (cutK K 0))) * h <= 3 / 4).
      { assert (Hle : (cutK K 12 - S (S (cutK K 0)) <= 3 * cutK K 0)%nat) by lia.
        apply le_INR in Hle. rewrite mult_INR in Hle. replace (INR 3) with 3 in Hle by (cbn; ring).
        assert (E := INR_cut0 K HK16). unfold h. nra. }
      assert (Hn0 : 0 <= INR (cutK K 12 - S (S (cutK K 0)))) by apply pos_INR.
      replace (INR (cutK K 12 - S (S (cutK K 0))) * (h * X0)) with (INR (cutK K 12 - S (S (cutK K 0))) * h * X0) by ring.
      apply Rmult_le_compat_r; [exact HX0 | exact Hn]. }
  (* the start inhomogeneity *)
  assert (Hg : vnorm 5 (gst K Y (rs (S (cutK K 0))) (ru (S (cutK K 0)))) <= CG * (h * h * a1 + h * b1)).
  { eapply Rle_trans; [apply (g_bound prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K Y _ _ HK HY HYn)|].
    fold CG. apply Rmult_le_compat_l; [exact HCG|]. unfold h in *. nra. }
  (* the states from m + 2 on *)
  assert (HSb0 : 0 <= sb).
  { unfold sb. apply Rmult_le_pos; [exact HS0|]. assert (0 <= CG * (h * h * a1 + h * b1)) by (apply Rmult_le_pos; [exact HCG | unfold h; nra]).
    fold X0. lra. }
  assert (Hst : forall j, (S (S (cutK K 0)) <= j <= cutK K 12)%nat -> vnorm 14 (state (hK K) (Pm3 K) (Lsol K rs ru) j) <= sb).
  { intros j Hj. eapply Rle_trans; [apply (proj2 HS2 K HK rs ru (Lsol K rs ru) Y HY HD0 HD1 HDr j Hj)|].
    unfold sb. apply Rmult_le_compat_l; [exact HS0|]. fold X0. lra. }
  assert (Hnd : forall j, (S (S (cutK K 0)) <= j <= cutK K 12)%nat -> vnorm 9 (Lsol K rs ru j) <= sb).
  { intros j Hj. eapply Rle_trans; [| apply (Hst j Hj)]. unfold state. apply vnorm_zjoin_lo. }
  (* the slope into m + 2 *)
  destruct (HDr (S (cutK K 0)) ltac:(lia)) as [Hs1 Hu1].
  assert (Hs2 : vnorm 9 (slope (hK K) (Lsol K rs ru) (S (S (cutK K 0)))) <= s2).
  { eapply Rle_trans; [apply (slope_bnd K (Lsol K rs ru) _ _ (S (cutK K 0)) HK16 ltac:(lia) Hs1 Hu1)|].
    assert (Hfs := first_state prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K (Lsol K rs ru)
                     (rs (S (cutK K 0))) (ru (S (cutK K 0))) Y HK HY HYn Hs1 Hu1).
    assert (Hz1 := zeta_bound prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok K (S (cutK K 0))
                     (rs (S (cutK K 0))) (ru (S (cutK K 0))) HK16 ltac:(lia)).
    fold PI in Hfs.
    set (zb := (1 + dyadR BQ) * (dyadR BM * (h * a1 + b1)) + a1).
    assert (Hzb : vnorm 14 (zeta3 K (S (cutK K 0)) (rs (S (cutK K 0))) (ru (S (cutK K 0)))) <= zb).
    { eapply Rle_trans; [exact Hz1|]. unfold zb. apply Rplus_le_compat; [| exact H1].
      apply Rmult_le_compat_l; [lra|]. apply Rmult_le_compat_l; [exact HBM|].
      apply Rplus_le_compat; [apply Rmult_le_compat_l; [unfold h; lra | exact H1] | exact H2]. }
    assert (Hs22 := Hst (S (S (cutK K 0))) ltac:(lia)).
    assert (A1 : vnorm 14 (state (hK K) (Pm3 K) (Lsol K rs ru) (S (cutK K 0))) <= PI * (sb + h * zb)).
    { eapply Rle_trans; [exact Hfs|]. apply Rmult_le_compat_l; [exact HPI|].
      apply Rplus_le_compat; [exact Hs22 | apply Rmult_le_compat_l; [unfold h; lra | exact Hzb]]. }
    unfold s2. fold zb. apply Rplus_le_compat.
    - apply Rmult_le_compat_l; [exact HNM | exact A1].
    - apply Rmult_le_compat_l; [exact HBM|]. apply Rplus_le_compat; [apply Rmult_le_compat_l; [unfold h; lra | exact H1] | exact H2]. }
  assert (Hs20 : 0 <= s2) by (eapply Rle_trans; [apply vnorm_nonneg | exact Hs2]).
  (* the node m + 1 *)
  assert (Hn1 : vnorm 9 (Lsol K rs ru (S (cutK K 0))) <= sb + h * s2).
  { apply vnorm_le; [unfold h in *; nra|]. intros c Hc.
    assert (E : Lsol K rs ru (S (cutK K 0)) c
                = Lsol K rs ru (S (S (cutK K 0))) c - hK K * slope (hK K) (Lsol K rs ru) (S (S (cutK K 0))) c).
    { unfold slope. replace (S (S (cutK K 0)) - 1)%nat with (S (cutK K 0)) by lia. field. lra. }
    rewrite E. unfold Rminus. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp, Rabs_mult, (Rabs_right (hK K)) by lra.
    apply Rplus_le_compat.
    - eapply Rle_trans; [apply vnorm_ge; exact Hc | apply Hnd; lia].
    - apply Rmult_le_compat_l; [lra|]. eapply Rle_trans; [apply vnorm_ge; exact Hc | exact Hs2]. }
  (* the slopes from m + 3 on *)
  assert (Hsl : forall j, (S (S (S (cutK K 0))) <= j <= cutK K 12)%nat ->
            vnorm 9 (slope (hK K) (Lsol K rs ru) j) <= NM * sb + dyadR BM * (h * A + B)).
  { intros j Hj. destruct (HDr (j - 1)%nat ltac:(lia)) as [Hs Hu].
    replace j with (S (j - 1)) at 1 by lia.
    eapply Rle_trans; [apply (slope_bnd K (Lsol K rs ru) _ _ (j - 1) HK16 ltac:(lia) Hs Hu)|].
    destruct (Hr (j - 1)%nat ltac:(lia)) as [Ha Hb].
    apply Rplus_le_compat.
    - apply Rmult_le_compat_l; [exact HNM | apply Hst; lia].
    - apply Rmult_le_compat_l; [exact HBM|]. apply Rplus_le_compat; [apply Rmult_le_compat_l; [unfold h; lra | exact Ha] | exact Hb]. }
  (* assemble *)
  assert (He0 : 0 <= e).
  { assert (0 <= dyadR BM * (h * A + B)) by (apply Rmult_le_pos; [exact HBM | unfold h; nra]).
    assert (0 <= NM * sb) by (apply Rmult_le_pos; assumption). lra. }
  apply nrm_le; [exact He0 | | |].
  - intros j Hj. destruct (Nat.eq_dec j (cutK K 0)) as [->|Hj0].
    + rewrite (vnorm_ext 9 _ (fun _ => 0)) by (intros c Hc; apply HD0; exact Hc). rewrite vnorm_zero. exact He0.
    + destruct (Nat.eq_dec j (S (cutK K 0))) as [->|Hj1].
      * exact (Rle_trans _ _ _ Hn1 E1).
      * eapply Rle_trans; [apply Hnd; lia|]. assert (0 <= h * s2) by (unfold h; nra). lra.
  - apply (Rmult_le_reg_l C2); [exact HC|]. unfold Rdiv.
    replace (C2 * (vnorm 9 (slope (hK K) (Lsol K rs ru) (S (S (cutK K 0)))) * / C2))
      with (vnorm 9 (slope (hK K) (Lsol K rs ru) (S (S (cutK K 0))))) by (field; lra).
    lra.
  - intros j Hj. eapply Rle_trans; [apply Hsl; exact Hj | exact E3].
Qed.

End LinB.

(* ---------------------------------------------------------------- *)
(* The jets the norm allows                                           *)

Lemma nrm_ext : forall K C2 x y, 0 < C2 -> (forall j i, x j i = y j i) -> nrm K C2 x = nrm K C2 y.
Proof.
  intros K C2 x y HC H.
  assert (E1 : forall j, vnorm 9 (x j) = vnorm 9 (y j)) by (intros j; apply vnorm_ext; intros; apply H).
  assert (E2 : forall j, vnorm 9 (slope (hK K) x j) = vnorm 9 (slope (hK K) y j))
    by (intros j; apply vnorm_ext; intros c _; unfold slope; rewrite !H; reflexivity).
  apply Rle_antisym; apply nrm_mono; try exact HC; intros; first [rewrite E1 | rewrite E2]; lra.
Qed.

Lemma nrm_neg : forall K C2 x, 0 < C2 -> nrm K C2 (vdiff (fun _ _ => 0) x) = nrm K C2 x.
Proof.
  intros K C2 x HC.
  assert (E1 : forall j, vnorm 9 (vdiff (fun _ _ => 0) x j) = vnorm 9 (x j))
    by (intros j; apply vnorm_ext_abs; intros c _; unfold vdiff; rewrite Rminus_0_l, Rabs_Ropp; reflexivity).
  assert (E2 : forall j, vnorm 9 (slope (hK K) (vdiff (fun _ _ => 0) x) j) = vnorm 9 (slope (hK K) x j)).
  { intros j. apply vnorm_ext_abs. intros c _. rewrite slope_vdiff. unfold slope at 1. unfold Rdiv.
    rewrite Rminus_0_r, Rmult_0_l, Rminus_0_l, Rabs_Ropp. reflexivity. }
  apply Rle_antisym; apply nrm_mono; try exact HC; intros; first [rewrite E1 | rewrite E2]; lra.
Qed.

Lemma slope_le :
  forall h (v : nat -> vec) j, 0 < h -> vnorm 9 (slope h v j) <= (vnorm 9 (v j) + vnorm 9 (v (j - 1)%nat)) / h.
Proof.
  intros h v j Hh. apply vnorm_le.
  { unfold Rdiv. apply Rmult_le_pos; [apply Rplus_le_le_0_compat; apply vnorm_nonneg | left; apply Rinv_0_lt_compat; exact Hh]. }
  intros c Hc. unfold slope, Rdiv. rewrite Rabs_mult, (Rabs_right (/ h)) by (left; apply Rinv_0_lt_compat; exact Hh).
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hh|].
  unfold Rminus. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp.
  apply Rplus_le_compat; apply vnorm_ge; exact Hc.
Qed.

(** The jet of the first row, where only the node values bound the slope
    into node m + 1. *)
Lemma jet_first :
  forall K C2 v r, 0 < C2 -> C2 * hK K <= 2 -> hK K <= 1 -> nrm K C2 v <= r ->
  (forall k, inxd k = true -> Rabs (zj (hK K) v (S (cutK K 0)) k) <= 2 * r / hK K) /\
  (forall e, ine e = true -> Rabs (wj (hK K) v (S (cutK K 0)) e) <= 4 * r / (hK K * hK K)).
Proof.
  intros K C2 v r HC HCh Hh1 Hv. assert (Hh := hK_pos K). assert (G := cutK_gap K).
  assert (Hr : 0 <= r) by (eapply Rle_trans; [apply nrm_nonneg | exact Hv]).
  assert (Hx1 : vnorm 9 (v (S (cutK K 0))) <= r)
    by (eapply Rle_trans; [apply (nrm_node K C2 v (S (cutK K 0))); lia | exact Hv]).
  assert (Hx0 : vnorm 9 (v (cutK K 0)) <= r) by (eapply Rle_trans; [apply (nrm_node K C2 v (cutK K 0)); lia | exact Hv]).
  assert (Hs1 : vnorm 9 (slope (hK K) v (S (cutK K 0))) <= 2 * r / hK K).
  { eapply Rle_trans; [apply slope_le; exact Hh|]. replace (S (cutK K 0) - 1)%nat with (cutK K 0) by lia.
    unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hh | lra]. }
  assert (H2r : r <= 2 * r / hK K).
  { apply (Rmult_le_reg_l (hK K)); [exact Hh|]. replace (hK K * (2 * r / hK K)) with (2 * r) by (field; lra). nra. }
  assert (Hs2 : vnorm 9 (slope (hK K) v (S (S (cutK K 0)))) <= 2 * r / hK K).
  { eapply Rle_trans; [apply (nrm_slope2 K C2 v HC)|].
    apply (Rle_trans _ (C2 * r)); [apply Rmult_le_compat_l; lra|].
    apply (Rmult_le_reg_l (hK K)); [exact Hh|]. replace (hK K * (2 * r / hK K)) with (2 * r) by (field; lra). nra. }
  split.
  - intros k Hk. eapply Rle_trans; [apply zj_bound; exact Hk|].
    apply Rmax_lub; [lra | apply Rmax_lub; assumption].
  - intros e He. eapply Rle_trans; [apply wj_bound; [exact Hh | exact He]|].
    unfold Rdiv. apply (Rle_trans _ ((2 * r / hK K + 2 * r / hK K) * / hK K)).
    + apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hh | lra].
    + right. field. lra.
Qed.

(** The jets of the rows from m + 2 on. *)
Lemma jet_rest :
  forall K C2 v r j, 1 <= C2 -> nrm K C2 v <= r -> (S (S (cutK K 0)) <= j < cutK K 12)%nat ->
  (forall k, inxd k = true -> Rabs (zj (hK K) v j k) <= C2 * r) /\
  (forall e, ine e = true -> Rabs (wj (hK K) v j e) <= 2 * (C2 * r) / hK K).
Proof.
  intros K C2 v r j HC Hv Hj. assert (Hh := hK_pos K).
  assert (Hr : 0 <= r) by (eapply Rle_trans; [apply nrm_nonneg | exact Hv]).
  assert (HCr : r <= C2 * r) by nra.
  assert (Hx : vnorm 9 (v j) <= C2 * r) by (eapply Rle_trans; [apply (nrm_node K C2 v j); lia | lra]).
  assert (Hsj : vnorm 9 (slope (hK K) v j) <= C2 * r).
  { destruct (Nat.eq_dec j (S (S (cutK K 0)))) as [->|Hne].
    - eapply Rle_trans; [apply (nrm_slope2 K C2 v ltac:(lra)) | apply Rmult_le_compat_l; lra].
    - eapply Rle_trans; [apply (nrm_slope3 K C2 v j); lia | lra]. }
  assert (Hsj1 : vnorm 9 (slope (hK K) v (S j)) <= C2 * r)
    by (eapply Rle_trans; [apply (nrm_slope3 K C2 v (S j)); lia | lra]).
  split.
  - intros k Hk. eapply Rle_trans; [apply zj_bound; exact Hk|]. apply Rmax_lub; [exact Hx | apply Rmax_lub; assumption].
  - intros e He. eapply Rle_trans; [apply wj_bound; [exact Hh | exact He]|].
    unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hh | lra].
Qed.

Lemma zball_of :
  forall rx rd z, (forall k, inxd k = false -> z k = 0) ->
  (forall k, inxd k = true -> Rabs (z k) <= Rmin (dyadR rx) (dyadR rd)) -> zball rx rd z.
Proof.
  intros rx rd z H0 H1. split; [exact H0|]. intros k Hk. unfold radk.
  destruct (inx k).
  - eapply Rle_trans; [apply H1; exact Hk | apply Rmin_l].
  - rewrite Hk. eapply Rle_trans; [apply H1; exact Hk | apply Rmin_r].
Qed.

Lemma rs_row_zero : forall h Pp Pm Sx j i, rs_row h Pp Pm Sx (fun _ _ => 0) j i = 0.
Proof.
  intros. unfold rs_row.
  rewrite (mv_extn 9 _ (slope h (fun _ _ => 0) (S j)) (fun _ => 0)) by (intros; unfold slope; unfold Rdiv; ring).
  rewrite (mv_extn 9 _ (slope h (fun _ _ => 0) j) (fun _ => 0)) by (intros; unfold slope; unfold Rdiv; ring).
  rewrite !mv_zero_vec. unfold Rdiv. ring.
Qed.

Lemma ru_row_zero : forall h Up V j i, ru_row h Up V (fun _ _ => 0) j i = 0.
Proof.
  intros. unfold ru_row.
  rewrite (mv_extn 9 _ (slope h (fun _ _ => 0) (S j)) (fun _ => 0)) by (intros; unfold slope; unfold Rdiv; ring).
  rewrite !mv_zero_vec. ring.
Qed.

(** The map whose fixed points solve the collocated rows. *)
Definition T (K : nat) (x : nat -> vec) : nat -> vec :=
  Lsol K (fun j i => rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x j i - GS K x j i)
         (fun j i => ru_row (hK K) (Up3 K) (V3 K) x j i - GU K x j i).

Lemma pos_div : forall a h, 0 <= a -> 0 < h -> 0 <= a / h.
Proof. intros a h Ha Hh. unfold Rdiv. apply Rmult_le_pos; [exact Ha | left; apply Rinv_0_lt_compat; exact Hh]. Qed.

Lemma rem_nonneg3 : forall a b c d : R, 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= 729 * a * b + 243 * a * c + 243 * b * d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  assert (0 <= a * b) by (apply Rmult_le_pos; assumption). assert (0 <= a * c) by (apply Rmult_le_pos; assumption).
  assert (0 <= b * d) by (apply Rmult_le_pos; assumption). nra.
Qed.

Section Stab.

Variable prec : F.precision.
Variables d kn : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs0 : imat.
Variable Rd : list (list (list (list (Z * Z)))).
Variables BM BMM BQ : Z * Z.

Hypothesis Hcells2 : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges2 prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI BM BMM BQ
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hstart : forall WiI, owi prec frames 0 = Some WiI -> start_range prec d (mktab d) chh chh kn WiI = Some rs0.
Hypothesis Hok : assemble3d prec frames es cells rs0 Rd = true.

Variable S2 : R.
Hypothesis HS2 :
  0 <= S2 /\
  forall K, (17 <= K)%nat -> forall (rs ru : nat -> vec) (X : nat -> vec) (Y : mat),
  is_inv 14 (PsiK K (S (cutK K 0))) Y ->
  (forall i, (i < 9)%nat -> X (cutK K 0) i = 0) ->
  (forall i, (i < 9)%nat -> X (cutK K 12) i = 0) ->
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs j i) /\
     (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru j i)) ->
  forall j, (S (S (cutK K 0)) <= j <= cutK K 12)%nat ->
  vnorm 14 (state (hK K) (Pm3 K) X j)
  <= S2 * (vnorm 5 (gst K Y (rs (S (cutK K 0))) (ru (S (cutK K 0)))) + srcw2 K rs ru).

Variables Kb rx rd hhi : Z * Z.
Hypothesis Hball : forall (r : bool) kp c, (kp < (if r then 5 else 4))%nat -> (c < 192)%nat ->
  ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true.
Hypothesis HKb : 0 <= dyadR Kb.
Hypothesis Hrx : 0 <= dyadR rx.
Hypothesis Hrd : 0 <= dyadR rd.

Let NM := Nmax prec frames es cells.
Let PI := PsiInvB prec frames es cells.
Let CG := cg prec frames es cells BM BMM BQ.

(** What a row moves away from its linear part, at the first row and at
    the others. *)
Lemma rem_first :
  forall K C2 x y rho dd, (17 <= K)%nat -> hK K <= dyadR hhi -> 1 <= C2 -> C2 * hK K <= 2 ->
  2 * rho / hK K <= Rmin (dyadR rx) (dyadR rd) ->
  nrm K C2 x <= rho -> nrm K C2 y <= rho -> nrm K C2 (vdiff x y) <= dd ->
  vnorm 5 (fun kp => GS K x (S (cutK K 0)) kp - GS K y (S (cutK K 0)) kp
                     - (rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x (S (cutK K 0)) kp
                        - rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) y (S (cutK K 0)) kp))
  <= dyadR Kb * (729 * (2 * rho / hK K) * (2 * dd / hK K) + 243 * (2 * rho / hK K) * (4 * dd / (hK K * hK K))
                 + 243 * (2 * dd / hK K) * (4 * rho / (hK K * hK K))) /\
  vnorm 4 (fun kp => GU K x (S (cutK K 0)) kp - GU K y (S (cutK K 0)) kp
                     - (ru_row (hK K) (Up3 K) (V3 K) x (S (cutK K 0)) kp - ru_row (hK K) (Up3 K) (V3 K) y (S (cutK K 0)) kp))
  <= dyadR Kb * (729 * (2 * rho / hK K) * (2 * dd / hK K)).
Proof.
  intros K C2 x y rho dd HK Hhh HC HCh Hz Hx Hy Hdd.
  assert (HK16 : (16 <= K)%nat) by lia. assert (Hh := hK_pos K).
  assert (Hh1 : hK K <= 1) by (assert (H := hK_le K HK16); lra). assert (G := cutK_gap K).
  destruct (ball_cell K (S (cutK K 0)) HK16 ltac:(lia)) as [c [Hc Hs]].
  destruct (jet_first K C2 x rho ltac:(lra) HCh Hh1 Hx) as [Zx Wx].
  destruct (jet_first K C2 y rho ltac:(lra) HCh Hh1 Hy) as [Zy Wy].
  destruct (jet_first K C2 (vdiff x y) dd ltac:(lra) HCh Hh1 Hdd) as [Zd Wd].
  assert (Hrho : 0 <= rho) by (eapply Rle_trans; [apply nrm_nonneg | exact Hx]).
  assert (Hd0 : 0 <= dd) by (eapply Rle_trans; [apply nrm_nonneg | exact Hdd]).
  assert (Hzx : zball rx rd (zj (hK K) x (S (cutK K 0)))).
  { apply zball_of; [intros k Hk; apply zj_out; exact Hk|]. intros k Hk. eapply Rle_trans; [apply Zx; exact Hk | exact Hz]. }
  assert (Hzy : zball rx rd (zj (hK K) y (S (cutK K 0)))).
  { apply zball_of; [intros k Hk; apply zj_out; exact Hk|]. intros k Hk. eapply Rle_trans; [apply Zy; exact Hk | exact Hz]. }
  assert (Hhh0 : 0 <= hK K <= dyadR hhi) by lra.
  assert (P1 : 0 <= 2 * rho / hK K) by (apply pos_div; lra).
  assert (P2 : 0 <= 2 * dd / hK K) by (apply pos_div; lra).
  assert (P3 : 0 <= 4 * rho / (hK K * hK K)) by (apply pos_div; nra).
  assert (P4 : 0 <= 4 * dd / (hK K * hK K)) by (apply pos_div; nra).
  assert (Hb : forall k, inxd k = true ->
            Rabs (zj (hK K) x (S (cutK K 0)) k) <= 2 * rho / hK K /\ Rabs (zj (hK K) y (S (cutK K 0)) k) <= 2 * rho / hK K /\
            Rabs (zj (hK K) x (S (cutK K 0)) k - zj (hK K) y (S (cutK K 0)) k) <= 2 * dd / hK K).
  { intros k Hk. split; [apply Zx; exact Hk | split; [apply Zy; exact Hk|]]. rewrite zj_sub. apply Zd. exact Hk. }
  assert (Hw : forall e, ine e = true ->
            Rabs (wj (hK K) y (S (cutK K 0)) e) <= 4 * rho / (hK K * hK K) /\
            Rabs (wj (hK K) x (S (cutK K 0)) e - wj (hK K) y (S (cutK K 0)) e) <= 4 * dd / (hK K * hK K)).
  { intros e He. split; [apply Wy; exact He|]. rewrite wj_sub. apply Wd. exact He. }
  split.
  - apply vnorm_le; [apply Rmult_le_pos; [exact HKb | apply rem_nonneg3; assumption]|].
    intros kp Hkp.
    exact (rows_s_crude prec Kb rx rd hhi K kp c (S (cutK K 0)) x y _ _ _ _ (Hball true kp c Hkp Hc) HKb Hrx Hrd Hs Hhh0
             Hzx Hzy P1 P2 P3 P4 Hb Hw).
  - apply vnorm_le; [apply Rmult_le_pos; [exact HKb | apply Rmult_le_pos; [apply Rmult_le_pos; [lra | exact P1] | exact P2]]|].
    intros kp Hkp.
    exact (rows_u_crude prec Kb rx rd hhi K kp c (S (cutK K 0)) x y _ _ (Hball false kp c Hkp Hc) HKb Hrx Hrd Hs Hhh0
             Hzx Hzy P1 P2 Hb).
Qed.

Lemma rem_rest :
  forall K C2 x y rho dd j, (17 <= K)%nat -> hK K <= dyadR hhi -> 1 <= C2 ->
  C2 * rho <= Rmin (dyadR rx) (dyadR rd) -> (S (S (cutK K 0)) <= j < cutK K 12)%nat ->
  nrm K C2 x <= rho -> nrm K C2 y <= rho -> nrm K C2 (vdiff x y) <= dd ->
  vnorm 5 (fun kp => GS K x j kp - GS K y j kp
                     - (rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x j kp - rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) y j kp))
  <= dyadR Kb * (729 * (C2 * rho) * (C2 * dd) + 243 * (C2 * rho) * (2 * (C2 * dd) / hK K)
                 + 243 * (C2 * dd) * (2 * (C2 * rho) / hK K)) /\
  vnorm 4 (fun kp => GU K x j kp - GU K y j kp
                     - (ru_row (hK K) (Up3 K) (V3 K) x j kp - ru_row (hK K) (Up3 K) (V3 K) y j kp))
  <= dyadR Kb * (729 * (C2 * rho) * (C2 * dd)).
Proof.
  intros K C2 x y rho dd j HK Hhh HC Hz Hj Hx Hy Hdd.
  assert (HK16 : (16 <= K)%nat) by lia. assert (Hh := hK_pos K).
  destruct (ball_cell K j HK16 ltac:(lia)) as [c [Hc Hs]].
  destruct (jet_rest K C2 x rho j HC Hx Hj) as [Zx Wx].
  destruct (jet_rest K C2 y rho j HC Hy Hj) as [Zy Wy].
  destruct (jet_rest K C2 (vdiff x y) dd j HC Hdd Hj) as [Zd Wd].
  assert (Hrho : 0 <= rho) by (eapply Rle_trans; [apply nrm_nonneg | exact Hx]).
  assert (Hd0 : 0 <= dd) by (eapply Rle_trans; [apply nrm_nonneg | exact Hdd]).
  assert (Hzx : zball rx rd (zj (hK K) x j)).
  { apply zball_of; [intros k Hk; apply zj_out; exact Hk|]. intros k Hk. eapply Rle_trans; [apply Zx; exact Hk | exact Hz]. }
  assert (Hzy : zball rx rd (zj (hK K) y j)).
  { apply zball_of; [intros k Hk; apply zj_out; exact Hk|]. intros k Hk. eapply Rle_trans; [apply Zy; exact Hk | exact Hz]. }
  assert (Hhh0 : 0 <= hK K <= dyadR hhi) by lra.
  assert (P1 : 0 <= C2 * rho) by nra. assert (P2 : 0 <= C2 * dd) by nra.
  assert (P3 : 0 <= 2 * (C2 * rho) / hK K) by (apply pos_div; lra).
  assert (P4 : 0 <= 2 * (C2 * dd) / hK K) by (apply pos_div; lra).
  assert (Hb : forall k, inxd k = true ->
            Rabs (zj (hK K) x j k) <= C2 * rho /\ Rabs (zj (hK K) y j k) <= C2 * rho /\
            Rabs (zj (hK K) x j k - zj (hK K) y j k) <= C2 * dd).
  { intros k Hk. split; [apply Zx; exact Hk | split; [apply Zy; exact Hk|]]. rewrite zj_sub. apply Zd. exact Hk. }
  assert (Hw : forall e, ine e = true ->
            Rabs (wj (hK K) y j e) <= 2 * (C2 * rho) / hK K /\
            Rabs (wj (hK K) x j e - wj (hK K) y j e) <= 2 * (C2 * dd) / hK K).
  { intros e He. split; [apply Wy; exact He|]. rewrite wj_sub. apply Wd. exact He. }
  split.
  - apply vnorm_le; [apply Rmult_le_pos; [exact HKb | apply rem_nonneg3; assumption]|].
    intros kp Hkp.
    exact (rows_s_crude prec Kb rx rd hhi K kp c j x y _ _ _ _ (Hball true kp c Hkp Hc) HKb Hrx Hrd Hs Hhh0
             Hzx Hzy P1 P2 P3 P4 Hb Hw).
  - apply vnorm_le; [apply Rmult_le_pos; [exact HKb | apply Rmult_le_pos; [apply Rmult_le_pos; [lra | exact P1] | exact P2]]|].
    intros kp Hkp.
    exact (rows_u_crude prec Kb rx rd hhi K kp c j x y _ _ (Hball false kp c Hkp Hc) HKb Hrx Hrd Hs Hhh0 Hzx Hzy P1 P2 Hb).
Qed.

(** The remainders per unit of distance, and the bounds of Lsol's lemma. *)
Definition a1f (h rho : R) : R :=
  dyadR Kb * (729 * (2 * rho / h) * (2 / h) + 243 * (2 * rho / h) * (4 / (h * h)) + 243 * (2 / h) * (4 * rho / (h * h))).
Definition b1f (h rho : R) : R := dyadR Kb * (729 * (2 * rho / h) * (2 / h)).
Definition Af (h rho C2 : R) : R :=
  dyadR Kb * (729 * (C2 * rho) * C2 + 243 * (C2 * rho) * (2 * C2 / h) + 243 * C2 * (2 * (C2 * rho) / h)).
Definition Bf (rho C2 : R) : R := dyadR Kb * (729 * (C2 * rho) * C2).
Definition sbf (h a1 b1 A B : R) : R :=
  S2 * (CG * (h * h * a1 + h * b1) + 3 / 4 * ((1 + dyadR BQ) * (dyadR BM * (h * A + B)) + A)).
Definition s2f (h a1 b1 A B : R) : R :=
  NM * (PI * (sbf h a1 b1 A B + h * ((1 + dyadR BQ) * (dyadR BM * (h * a1 + b1)) + a1))) + dyadR BM * (h * a1 + b1).

Lemma sbf_scal : forall h a1 b1 A B t, sbf h (t * a1) (t * b1) (t * A) (t * B) = t * sbf h a1 b1 A B.
Proof. intros. unfold sbf. ring. Qed.

Lemma s2f_scal : forall h a1 b1 A B t, s2f h (t * a1) (t * b1) (t * A) (t * B) = t * s2f h a1 b1 A B.
Proof. intros. unfold s2f. rewrite sbf_scal. ring. Qed.

Lemma src_abs :
  forall p q u v : R, Rabs ((p - q) - (u - v)) = Rabs (q - v - (p - u)).
Proof. intros p q u v. replace ((p - q) - (u - v)) with (- (q - v - (p - u))) by ring. apply Rabs_Ropp. Qed.

(** T contracts the ball of radius rho by 1/2. *)
Lemma contract :
  forall K C2 rho, (17 <= K)%nat -> hK K <= dyadR hhi -> 1 <= C2 -> C2 * hK K <= 2 ->
  2 * rho / hK K <= Rmin (dyadR rx) (dyadR rd) -> C2 * rho <= Rmin (dyadR rx) (dyadR rd) ->
  sbf (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2)
  + hK K * s2f (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2) <= 1 / 2 ->
  s2f (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2) <= C2 * (1 / 2) ->
  NM * sbf (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2)
  + dyadR BM * (hK K * Af (hK K) rho C2 + Bf rho C2) <= 1 / 2 ->
  forall x y, dist K C2 (fun _ _ => 0) x <= rho -> dist K C2 (fun _ _ => 0) y <= rho ->
  dist K C2 (T K x) (T K y) <= 1 / 2 * dist K C2 x y.
Proof.
  intros K C2 rho HK Hhh HC HCh Hz1 Hz2 E1 E2 E3 x y Hx Hy.
  assert (HK16 : (16 <= K)%nat) by lia. assert (Hh := hK_pos K). assert (HC0 : 0 < C2) by lra.
  assert (G := cutK_gap K).
  unfold dist in Hx, Hy. rewrite nrm_neg in Hx, Hy by exact HC0.
  assert (Hrho : 0 <= rho) by (eapply Rle_trans; [apply nrm_nonneg | exact Hx]).
  set (dd := dist K C2 x y).
  assert (Hdd : nrm K C2 (vdiff x y) <= dd) by (unfold dd, dist; lra).
  assert (Hd0 : 0 <= dd) by apply dist_nonneg.
  set (sx := fun j i => rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x j i - GS K x j i).
  set (ux := fun j i => ru_row (hK K) (Up3 K) (V3 K) x j i - GU K x j i).
  set (sy := fun j i => rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) y j i - GS K y j i).
  set (uy := fun j i => ru_row (hK K) (Up3 K) (V3 K) y j i - GU K y j i).
  assert (ET : dist K C2 (T K x) (T K y) = nrm K C2 (Lsol K (vdiff sx sy) (vdiff ux uy))).
  { unfold dist, T. apply nrm_ext; [exact HC0|]. intros j i. unfold vdiff at 1.
    apply (Lsol_sub prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok K HK16). }
  rewrite ET.
  set (a1 := a1f (hK K) rho). set (b1 := b1f (hK K) rho). set (A := Af (hK K) rho C2). set (B := Bf rho C2).
  assert (Hb1 : 0 <= b1).
  { unfold b1, b1f. apply Rmult_le_pos; [exact HKb|].
    apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply pos_div; lra] | apply pos_div; lra]. }
  assert (Ha1 : 0 <= a1).
  { unfold a1, a1f. apply Rmult_le_pos; [exact HKb|].
    apply rem_nonneg3; apply pos_div; nra. }
  assert (HA : 0 <= A).
  { unfold A, Af. apply Rmult_le_pos; [exact HKb|].
    apply rem_nonneg3; [nra | lra | apply pos_div; lra | apply pos_div; nra]. }
  assert (HB : 0 <= B) by (unfold B, Bf; apply Rmult_le_pos; [exact HKb | nra]).
  assert (L := lin_nrm prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok S2 HS2
                 K C2 (vdiff sx sy) (vdiff ux uy) (dd * a1) (dd * b1) (dd * A) (dd * B) (1 / 2 * dd) HK HC0
                 ltac:(nra) ltac:(nra) ltac:(nra) ltac:(nra)).
  apply L.
  - destruct (rem_first K C2 x y rho dd HK Hhh HC HCh Hz1 Hx Hy Hdd) as [R1 _].
    rewrite (vnorm_ext_abs 5 _ (fun kp => GS K x (S (cutK K 0)) kp - GS K y (S (cutK K 0)) kp
                     - (rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x (S (cutK K 0)) kp
                        - rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) y (S (cutK K 0)) kp)))
      by (intros c _; unfold vdiff, sx, sy; apply src_abs).
    eapply Rle_trans; [exact R1|]. right. unfold a1, a1f. unfold Rdiv. ring.
  - destruct (rem_first K C2 x y rho dd HK Hhh HC HCh Hz1 Hx Hy Hdd) as [_ R2].
    rewrite (vnorm_ext_abs 4 _ (fun kp => GU K x (S (cutK K 0)) kp - GU K y (S (cutK K 0)) kp
                     - (ru_row (hK K) (Up3 K) (V3 K) x (S (cutK K 0)) kp - ru_row (hK K) (Up3 K) (V3 K) y (S (cutK K 0)) kp)))
      by (intros c _; unfold vdiff, ux, uy; apply src_abs).
    eapply Rle_trans; [exact R2|]. right. unfold b1, b1f. unfold Rdiv. ring.
  - intros j Hj. destruct (rem_rest K C2 x y rho dd j HK Hhh HC Hz2 Hj Hx Hy Hdd) as [R1 R2]. split.
    + rewrite (vnorm_ext_abs 5 _ (fun kp => GS K x j kp - GS K y j kp
                     - (rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x j kp - rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) y j kp)))
        by (intros c _; unfold vdiff, sx, sy; apply src_abs).
      eapply Rle_trans; [exact R1|]. right. unfold A, Af. unfold Rdiv. ring.
    + rewrite (vnorm_ext_abs 4 _ (fun kp => GU K x j kp - GU K y j kp
                     - (ru_row (hK K) (Up3 K) (V3 K) x j kp - ru_row (hK K) (Up3 K) (V3 K) y j kp)))
        by (intros c _; unfold vdiff, ux, uy; apply src_abs).
      eapply Rle_trans; [exact R2|]. right. unfold B, Bf. ring.
  - change (sbf (hK K) (dd * a1) (dd * b1) (dd * A) (dd * B) + hK K * s2f (hK K) (dd * a1) (dd * b1) (dd * A) (dd * B)
            <= 1 / 2 * dd).
    rewrite sbf_scal, s2f_scal. fold a1 b1 A B in E1. nra.
  - change (s2f (hK K) (dd * a1) (dd * b1) (dd * A) (dd * B) <= C2 * (1 / 2 * dd)).
    rewrite s2f_scal. fold a1 b1 A B in E2. nra.
  - change (NM * sbf (hK K) (dd * a1) (dd * b1) (dd * A) (dd * B) + dyadR BM * (hK K * (dd * A) + dd * B) <= 1 / 2 * dd).
    rewrite sbf_scal. fold a1 b1 A B in E3. nra.
Qed.

(** T moves the exact solution by at most half the radius. *)
Lemma small :
  forall K C2 rho cc, (17 <= K)%nat -> 1 <= C2 -> 0 <= cc ->
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall kp, (kp < 5)%nat -> Rabs (GS K (fun _ _ => 0) j kp) <= cc) /\
     (forall kp, (kp < 4)%nat -> Rabs (GU K (fun _ _ => 0) j kp) <= cc)) ->
  sbf (hK K) cc cc cc cc + hK K * s2f (hK K) cc cc cc cc <= rho / 2 ->
  s2f (hK K) cc cc cc cc <= C2 * (rho / 2) ->
  NM * sbf (hK K) cc cc cc cc + dyadR BM * (hK K * cc + cc) <= rho / 2 ->
  dist K C2 (fun _ _ => 0) (T K (fun _ _ => 0)) <= (1 - 1 / 2) * rho.
Proof.
  intros K C2 rho cc HK HC Hcc Hcons E1 E2 E3.
  assert (HC0 : 0 < C2) by lra. assert (G := cutK_gap K).
  unfold dist. rewrite nrm_neg by exact HC0. replace ((1 - 1 / 2) * rho) with (rho / 2) by field.
  assert (Hs : forall j, (cutK K 0 < j < cutK K 12)%nat ->
            vnorm 5 ((fun j i => rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) (fun _ _ => 0) j i - GS K (fun _ _ => 0) j i) j) <= cc /\
            vnorm 4 ((fun j i => ru_row (hK K) (Up3 K) (V3 K) (fun _ _ => 0) j i - GU K (fun _ _ => 0) j i) j) <= cc).
  { intros j Hj. destruct (Hcons j Hj) as [H1 H2]. split.
    - apply vnorm_le; [exact Hcc|]. intros kp Hkp. cbv beta. rewrite rs_row_zero, Rminus_0_l, Rabs_Ropp. apply H1; exact Hkp.
    - apply vnorm_le; [exact Hcc|]. intros kp Hkp. cbv beta. rewrite ru_row_zero, Rminus_0_l, Rabs_Ropp. apply H2; exact Hkp. }
  destruct (Hs (S (cutK K 0)) ltac:(lia)) as [H1 H2].
  unfold T.
  apply (lin_nrm prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok S2 HS2
           K C2 _ _ cc cc cc cc (rho / 2) HK HC0 Hcc Hcc Hcc Hcc H1 H2).
  - intros j Hj. apply Hs. lia.
  - exact E1.
  - exact E2.
  - exact E3.
Qed.

(** A fixed point of T in the ball. *)
Lemma fixed :
  forall K C2 rho cc, (17 <= K)%nat -> hK K <= dyadR hhi -> 1 <= C2 -> C2 * hK K <= 2 -> 0 <= rho ->
  2 * rho / hK K <= Rmin (dyadR rx) (dyadR rd) -> C2 * rho <= Rmin (dyadR rx) (dyadR rd) ->
  sbf (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2)
  + hK K * s2f (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2) <= 1 / 2 ->
  s2f (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2) <= C2 * (1 / 2) ->
  NM * sbf (hK K) (a1f (hK K) rho) (b1f (hK K) rho) (Af (hK K) rho C2) (Bf rho C2)
  + dyadR BM * (hK K * Af (hK K) rho C2 + Bf rho C2) <= 1 / 2 ->
  0 <= cc ->
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall kp, (kp < 5)%nat -> Rabs (GS K (fun _ _ => 0) j kp) <= cc) /\
     (forall kp, (kp < 4)%nat -> Rabs (GU K (fun _ _ => 0) j kp) <= cc)) ->
  sbf (hK K) cc cc cc cc + hK K * s2f (hK K) cc cc cc cc <= rho / 2 ->
  s2f (hK K) cc cc cc cc <= C2 * (rho / 2) ->
  NM * sbf (hK K) cc cc cc cc + dyadR BM * (hK K * cc + cc) <= rho / 2 ->
  exists x, nrm K C2 x <= rho /\
    (forall j i, (cutK K 0 <= j <= cutK K 12)%nat -> (i < 9)%nat -> T K x j i = x j i).
Proof.
  intros K C2 rho cc HK Hhh HC HCh Hrho Hz1 Hz2 E1 E2 E3 Hcc Hcons F1 F2 F3.
  assert (HC0 : 0 < C2) by lra. assert (Hh := hK_pos K).
  assert (HB0 : 0 <= 1 + 2 / hK K) by (assert (0 <= 2 / hK K) by (apply pos_div; lra); lra).
  destruct (pseudo_fixed_point (nat -> vec) (dist K C2) (dist_nonneg K C2) (fun x => dist_refl K C2 x HC0)
              (fun x y => dist_sym K C2 x y HC0) (fun x y z => dist_tri K C2 x y z HC0) (T K) (fun _ _ => 0)
              (1 / 2) rho ltac:(lra) ltac:(lra) Hrho
              (contract K C2 rho HK Hhh HC HCh Hz1 Hz2 E1 E2 E3)
              (small K C2 rho cc HK HC Hcc Hcons F1 F2 F3)
              (coords_complete (coordsK K) (dist K C2) 1 (1 + 2 / hK K) ltac:(lra) HB0 (dist_coord K C2)
                 (fun x y e He H => dist_coords K C2 x y e HC He H)
                 (fun x y => dist_sym K C2 x y HC0) (fun x y z => dist_tri K C2 x y z HC0) (fun _ _ => 0) rho))
    as [x [Hx Hfix]].
  exists x. split.
  - unfold dist in Hx. rewrite nrm_neg in Hx by exact HC0. exact Hx.
  - intros j i Hj Hi.
    assert (Hc := dist_coord K C2 (T K x) x (j, i) ltac:(unfold coordsK; apply in_prod; apply in_seq; lia)).
    cbn [fst snd] in Hc. rewrite Hfix, Rmult_0_r in Hc.
    assert (Hp := Rabs_pos (T K x j i - x j i)).
    assert (E : Rabs (T K x j i - x j i) = 0) by lra. apply Rabs_eq_0 in E. lra.
Qed.

(** A fixed point of T solves the collocated rows. *)
Lemma fixed_solves :
  forall K x, (16 <= K)%nat ->
  (forall j i, (cutK K 0 <= j <= cutK K 12)%nat -> (i < 9)%nat -> T K x j i = x j i) ->
  (forall i, (i < 9)%nat -> x (cutK K 0) i = 0) /\ (forall i, (i < 9)%nat -> x (cutK K 12) i = 0) /\
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall kp, (kp < 5)%nat -> GS K x j kp = 0) /\ (forall kp, (kp < 4)%nat -> GU K x j kp = 0)).
Proof.
  intros K x HK Hfix. assert (G := cutK_gap K).
  destruct (Lsol_lrows prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok K HK
              (fun j i => rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) x j i - GS K x j i)
              (fun j i => ru_row (hK K) (Up3 K) (V3 K) x j i - GU K x j i)) as [HT0 [HT1 HTr]].
  fold (T K x) in HT0, HT1, HTr.
  split; [| split].
  - intros i Hi. rewrite <- (Hfix (cutK K 0) i ltac:(lia) Hi). apply HT0. exact Hi.
  - intros i Hi. rewrite <- (Hfix (cutK K 12) i ltac:(lia) Hi). apply HT1. exact Hi.
  - intros j Hj. destruct (HTr j Hj) as [Hs Hu]. split.
    + intros kp Hkp. assert (E := Hs kp Hkp). cbv beta in E.
      rewrite (rs_row_ext (hK K) (Pp3 K) (Pm3 K) (Sx3 K) (T K x) x j kp ltac:(lia)) in E
        by (intros l c Hl Hc; apply Hfix; [lia | exact Hc]).
      lra.
    + intros kp Hkp. assert (E := Hu kp Hkp). cbv beta in E.
      rewrite (ru_row_ext (hK K) (Up3 K) (V3 K) (T K x) x j kp) in E by (intros l c Hl Hc; apply Hfix; [lia | exact Hc]).
      lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The constants                                                     *)

Lemma consts_nonneg : 0 <= S2 /\ 0 <= CG /\ 0 <= NM /\ 0 <= PI /\ 0 <= dyadR BM /\ 0 <= dyadR BQ.
Proof.
  split; [exact (proj1 HS2)|]. split; [exact (CG_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok)|].
  split; [exact (NM_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok)|].
  split; [exact (PI_nonneg prec d Hd frames es cells rs0 Rd Hok)|].
  split; [exact (BMr_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok)|].
  exact (BQr_nonneg prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hok).
Qed.

(** The conditions of [small] at the consistency bound cc = Cc h^2. *)
Lemma alg_small :
  forall h cc C2, 0 < h -> h <= 1 -> 0 <= cc -> 1 <= C2 ->
  let L1 := S2 * (2 * CG + 3 / 4 * (2 * (1 + dyadR BQ) * dyadR BM + 1)) in
  let L2 := NM * PI * (L1 + 2 * (1 + dyadR BQ) * dyadR BM + 1) + 2 * dyadR BM in
  let L0 := L1 + L2 + NM * L1 + 2 * dyadR BM in
  sbf h cc cc cc cc + h * s2f h cc cc cc cc <= L0 * cc /\
  s2f h cc cc cc cc <= C2 * (L0 * cc) /\
  NM * sbf h cc cc cc cc + dyadR BM * (h * cc + cc) <= L0 * cc.
Proof.
  intros h cc C2 Hh Hh1 Hc HC L1 L2 L0.
  destruct consts_nonneg as (HS & HCG & HNM & HPI & HBM & HBQ).
  set (bm := dyadR BM) in *. set (bq := dyadR BQ) in *.
  assert (Hhc : h * cc <= cc) by nra.
  assert (Hhhc : h * h * cc <= cc) by nra.
  set (X := (1 + bq) * (bm * (h * cc + cc)) + cc).
  assert (HX : X <= (2 * (1 + bq) * bm + 1) * cc).
  { unfold X. assert (bm * (h * cc + cc) <= bm * (2 * cc)) by (apply Rmult_le_compat_l; lra).
    assert ((1 + bq) * (bm * (h * cc + cc)) <= (1 + bq) * (bm * (2 * cc))) by (apply Rmult_le_compat_l; lra).
    nra. }
  assert (HX0 : 0 <= X).
  { unfold X. apply Rplus_le_le_0_compat; [| exact Hc].
    apply Rmult_le_pos; [lra | apply Rmult_le_pos; [exact HBM | nra]]. }
  assert (Hbqm : 0 <= bq * bm) by (apply Rmult_le_pos; assumption).
  assert (HL1 : 0 <= L1) by (unfold L1; apply Rmult_le_pos; [exact HS | lra]).
  assert (Hsb : sbf h cc cc cc cc <= L1 * cc).
  { unfold sbf. fold bm bq X. unfold L1.
    assert (A1 : CG * (h * h * cc + h * cc) <= CG * (2 * cc)) by (apply Rmult_le_compat_l; lra).
    assert (A2 : CG * (h * h * cc + h * cc) + 3 / 4 * X <= (2 * CG + 3 / 4 * (2 * (1 + bq) * bm + 1)) * cc) by nra.
    replace (S2 * (2 * CG + 3 / 4 * (2 * (1 + bq) * bm + 1)) * cc) with (S2 * ((2 * CG + 3 / 4 * (2 * (1 + bq) * bm + 1)) * cc))
      by ring.
    apply Rmult_le_compat_l; [exact HS | exact A2]. }
  assert (Hsb0 : 0 <= sbf h cc cc cc cc).
  { unfold sbf. fold bm bq X. apply Rmult_le_pos; [exact HS|]. assert (0 <= CG * (h * h * cc + h * cc)) by (apply Rmult_le_pos; nra). nra. }
  assert (Hs2 : s2f h cc cc cc cc <= L2 * cc).
  { unfold s2f. fold bm bq X. unfold L2.
    assert (A1 : sbf h cc cc cc cc + h * X <= L1 * cc + (2 * (1 + bq) * bm + 1) * cc) by nra.
    assert (A2 : NM * (PI * (sbf h cc cc cc cc + h * X)) <= NM * (PI * (L1 * cc + (2 * (1 + bq) * bm + 1) * cc))).
    { apply Rmult_le_compat_l; [exact HNM|]. apply Rmult_le_compat_l; [exact HPI | exact A1]. }
    assert (A3 : bm * (h * cc + cc) <= bm * (2 * cc)) by (apply Rmult_le_compat_l; lra).
    replace ((NM * PI * (L1 + 2 * (1 + bq) * bm + 1) + 2 * bm) * cc)
      with (NM * (PI * (L1 * cc + (2 * (1 + bq) * bm + 1) * cc)) + bm * (2 * cc)) by ring.
    lra. }
  assert (Hs20 : 0 <= s2f h cc cc cc cc).
  { unfold s2f. fold bm bq X. apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; [exact HNM|]. apply Rmult_le_pos; [exact HPI|].
      assert (0 <= h * X) by (apply Rmult_le_pos; lra). lra.
    - apply Rmult_le_pos; [exact HBM|]. assert (0 <= h * cc) by (apply Rmult_le_pos; lra). lra. }
  assert (HL2 : 0 <= L2).
  { unfold L2. assert (0 <= NM * PI * (L1 + 2 * (1 + bq) * bm + 1)) by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | lra]).
    lra. }
  assert (HNL : 0 <= NM * L1 * cc) by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact Hc]).
  assert (Hbc : 0 <= bm * cc) by (apply Rmult_le_pos; assumption).
  assert (HL1c : 0 <= L1 * cc) by (apply Rmult_le_pos; assumption).
  assert (HL2c : 0 <= L2 * cc) by (apply Rmult_le_pos; assumption).
  assert (HL0 : L0 * cc = L1 * cc + L2 * cc + NM * L1 * cc + 2 * (bm * cc)) by (unfold L0; ring).
  split; [| split].
  - assert (h * s2f h cc cc cc cc <= 1 * s2f h cc cc cc cc) by (apply Rmult_le_compat_r; lra). lra.
  - assert (L0 * cc <= C2 * (L0 * cc)) by (rewrite <- (Rmult_1_l (L0 * cc)) at 1; apply Rmult_le_compat_r; lra). lra.
  - assert (NM * sbf h cc cc cc cc <= NM * (L1 * cc)) by (apply Rmult_le_compat_l; assumption).
    assert (bm * (h * cc + cc) <= bm * (2 * cc)) by (apply Rmult_le_compat_l; lra).
    assert (NM * (L1 * cc) = NM * L1 * cc) by ring. lra.
Qed.

(** The conditions of [contract] at rho = C h^2, once h is small. *)
Lemma alg_contract :
  forall h C C2, 0 < h -> h <= 1 -> 0 <= C -> 1 <= C2 ->
  let rho := C * (h * h) in
  let L3 := 6804 * NM * PI + 9720 * dyadR BM in
  4 * L3 * dyadR Kb * C <= C2 ->
  let G1 := S2 * dyadR Kb * C * (9720 * CG + 3 / 4 * (C2 * C2) * (2430 * (1 + dyadR BQ) * dyadR BM + 1701)) in
  let G2 := NM * PI * (G1 + 9720 * (1 + dyadR BQ) * dyadR BM * dyadR Kb * C) in
  let G3 := NM * G1 + 2430 * dyadR BM * dyadR Kb * (C2 * C2) * C in
  h * (G1 + L3 * dyadR Kb * C + G2 + G3) <= 1 / 4 ->
  sbf h (a1f h rho) (b1f h rho) (Af h rho C2) (Bf rho C2) + h * s2f h (a1f h rho) (b1f h rho) (Af h rho C2) (Bf rho C2)
    <= 1 / 2 /\
  s2f h (a1f h rho) (b1f h rho) (Af h rho C2) (Bf rho C2) <= C2 * (1 / 2) /\
  NM * sbf h (a1f h rho) (b1f h rho) (Af h rho C2) (Bf rho C2) + dyadR BM * (h * Af h rho C2 + Bf rho C2) <= 1 / 2.
Proof.
  intros h C C2 Hh Hh1 HC HC2 rho L3 HL3 G1 G2 G3 HG.
  destruct consts_nonneg as (HS & HCG & HNM & HPI & HBM & HBQ).
  set (kb := dyadR Kb) in *. set (bm := dyadR BM) in *. set (bq := dyadR BQ) in *.
  assert (Hkb : 0 <= kb) by exact HKb.
  set (a1 := a1f h rho). set (b1 := b1f h rho). set (A := Af h rho C2). set (B := Bf rho C2).
  assert (Ea1 : h * a1 = kb * C * (2916 * h + 3888)) by (unfold a1, a1f, rho; fold kb; field; lra).
  assert (Eb1 : b1 = 2916 * kb * C) by (unfold b1, b1f, rho; fold kb; field; lra).
  assert (EA : A = kb * (C2 * C2) * C * (729 * (h * h) + 972 * h)) by (unfold A, Af, rho; fold kb; field; lra).
  assert (EB : B = 729 * kb * (C2 * C2) * C * (h * h)) by (unfold B, Bf, rho; fold kb; ring).
  assert (HkC : 0 <= kb * C) by nra.
  assert (Hc2 : 0 <= kb * (C2 * C2) * C) by (apply Rmult_le_pos; [nra | exact HC]).
  assert (Hhh : h * h <= h) by nra. assert (Hhhh : h * h * h <= h) by nra.
  assert (P1 : h * h * a1 + h * b1 <= 9720 * kb * C * h).
  { replace (h * h * a1 + h * b1) with (h * (h * a1) + h * b1) by ring. rewrite Ea1, Eb1. nra. }
  assert (P2 : h * a1 + b1 <= 9720 * kb * C) by (rewrite Ea1, Eb1; nra).
  assert (P3 : h * A + B <= 2430 * kb * (C2 * C2) * C * h).
  { rewrite EA, EB. replace (h * (kb * (C2 * C2) * C * (729 * (h * h) + 972 * h)) + 729 * kb * (C2 * C2) * C * (h * h))
      with (kb * (C2 * C2) * C * (729 * (h * h * h) + 972 * (h * h) + 729 * (h * h))) by ring. nra. }
  assert (P4 : A <= 1701 * kb * (C2 * C2) * C * h) by (rewrite EA; nra).
  assert (PA0 : 0 <= A) by (rewrite EA; nra).
  assert (PB0 : 0 <= B) by (rewrite EB; nra).
  assert (Pa0 : 0 <= h * a1) by (rewrite Ea1; nra).
  assert (Pb0 : 0 <= b1) by (rewrite Eb1; nra).
  (* the bound on sbf *)
  assert (Hsb : sbf h a1 b1 A B <= h * G1).
  { unfold sbf. fold bm bq. unfold G1.
    assert (B1 : CG * (h * h * a1 + h * b1) <= CG * (9720 * kb * C * h)) by (apply Rmult_le_compat_l; assumption).
    assert (B2 : bm * (h * A + B) <= bm * (2430 * kb * (C2 * C2) * C * h)) by (apply Rmult_le_compat_l; assumption).
    assert (B3 : (1 + bq) * (bm * (h * A + B)) <= (1 + bq) * (bm * (2430 * kb * (C2 * C2) * C * h)))
      by (apply Rmult_le_compat_l; lra).
    assert (B4 : CG * (h * h * a1 + h * b1) + 3 / 4 * ((1 + bq) * (bm * (h * A + B)) + A)
                 <= h * (kb * C * (9720 * CG + 3 / 4 * (C2 * C2) * (2430 * (1 + bq) * bm + 1701)))).
    { replace (h * (kb * C * (9720 * CG + 3 / 4 * (C2 * C2) * (2430 * (1 + bq) * bm + 1701))))
        with (CG * (9720 * kb * C * h) + 3 / 4 * ((1 + bq) * (bm * (2430 * kb * (C2 * C2) * C * h)) + 1701 * kb * (C2 * C2) * C * h))
        by ring.
      lra. }
    replace (h * (S2 * kb * C * (9720 * CG + 3 / 4 * (C2 * C2) * (2430 * (1 + bq) * bm + 1701))))
      with (S2 * (h * (kb * C * (9720 * CG + 3 / 4 * (C2 * C2) * (2430 * (1 + bq) * bm + 1701))))) by ring.
    apply Rmult_le_compat_l; [exact HS | exact B4]. }
  assert (Hsb0 : 0 <= sbf h a1 b1 A B).
  { unfold sbf. fold bm bq. apply Rmult_le_pos; [exact HS|].
    assert (0 <= CG * (h * h * a1 + h * b1)) by (apply Rmult_le_pos; [exact HCG | nra]).
    assert (0 <= (1 + bq) * (bm * (h * A + B))) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; nra]). lra. }
  assert (Hbqm : 0 <= bq * bm) by (apply Rmult_le_pos; assumption).
  assert (HC22 : 0 <= C2 * C2) by nra.
  assert (HG1 : 0 <= G1).
  { unfold G1. apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact HC]|].
    assert (0 <= (C2 * C2) * (2430 * (1 + bq) * bm + 1701)) by (apply Rmult_le_pos; [exact HC22 | lra]). lra. }
  (* the bound on s2f *)
  assert (Hs2 : s2f h a1 b1 A B <= L3 * kb * C + h * G2).
  { unfold s2f. fold bm bq.
    assert (B1 : h * ((1 + bq) * (bm * (h * a1 + b1)) + a1) <= 9720 * (1 + bq) * bm * kb * C * h + 6804 * kb * C).
    { replace (h * ((1 + bq) * (bm * (h * a1 + b1)) + a1)) with ((1 + bq) * bm * h * (h * a1 + b1) + h * a1) by ring.
      assert ((1 + bq) * bm * h * (h * a1 + b1) <= (1 + bq) * bm * h * (9720 * kb * C))
        by (apply Rmult_le_compat_l; [nra | exact P2]).
      rewrite Ea1 at 2. nra. }
    assert (B2 : NM * (PI * (sbf h a1 b1 A B + h * ((1 + bq) * (bm * (h * a1 + b1)) + a1)))
                 <= NM * (PI * (h * G1 + (9720 * (1 + bq) * bm * kb * C * h + 6804 * kb * C)))).
    { apply Rmult_le_compat_l; [exact HNM|]. apply Rmult_le_compat_l; [exact HPI | lra]. }
    assert (B3 : bm * (h * a1 + b1) <= bm * (9720 * kb * C)) by (apply Rmult_le_compat_l; assumption).
    unfold L3, G2.
    replace (NM * (PI * (h * G1 + (9720 * (1 + bq) * bm * kb * C * h + 6804 * kb * C))) + bm * (9720 * kb * C))
      with ((6804 * NM * PI + 9720 * bm) * kb * C + h * (NM * PI * (G1 + 9720 * (1 + bq) * bm * kb * C))) in B2 |- *
      by ring.
    lra. }
  assert (HNP : 0 <= NM * PI) by (apply Rmult_le_pos; assumption).
  assert (HL30 : 0 <= L3 * kb * C).
  { unfold L3. apply Rmult_le_pos; [| exact HC]. apply Rmult_le_pos; [| exact Hkb]. lra. }
  assert (HbkC : 0 <= bm * kb * C) by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact HC]).
  assert (HG2 : 0 <= G2).
  { unfold G2. apply Rmult_le_pos; [exact HNP|].
    assert (0 <= bq * (bm * kb * C)) by (apply Rmult_le_pos; assumption). lra. }
  assert (HG3 : 0 <= G3).
  { unfold G3. apply Rplus_le_le_0_compat; [apply Rmult_le_pos; assumption|].
    apply Rmult_le_pos; [| exact HC]. apply Rmult_le_pos; [| exact HC22]. apply Rmult_le_pos; [lra | exact Hkb]. }
  assert (HhG1 : 0 <= h * G1) by nra. assert (HhG2 : 0 <= h * G2) by nra. assert (HhG3 : 0 <= h * G3) by nra.
  assert (HhL : 0 <= h * (L3 * kb * C)) by nra.
  split; [| split].
  - assert (h * s2f h a1 b1 A B <= h * (L3 * kb * C + h * G2)) by (apply Rmult_le_compat_l; lra).
    assert (h * (h * G2) <= h * G2) by nra. nra.
  - assert (L3 * kb * C <= C2 / 4) by lra. assert (h * G2 <= 1 / 4) by nra. lra.
  - assert (NM * sbf h a1 b1 A B <= NM * (h * G1)) by (apply Rmult_le_compat_l; assumption).
    assert (bm * (h * A + B) <= bm * (2430 * kb * (C2 * C2) * C * h)) by (apply Rmult_le_compat_l; assumption).
    assert (h * G3 = NM * (h * G1) + bm * (2430 * kb * (C2 * C2) * C * h)) by (unfold G3; ring).
    nra.
Qed.

Lemma INR_lt_pow2 : forall n, INR n < 2 ^ n.
Proof.
  induction n as [|n IH]; [cbn; lra|]. rewrite S_INR. cbn [pow].
  assert (H := pow_R1_Rle 2 n ltac:(lra)). lra.
Qed.

Lemma hK_small : forall eps, 0 < eps -> exists K0, forall K, (K0 <= K)%nat -> hK K <= eps.
Proof.
  intros eps He. destruct (archimed (/ eps)) as [Hup _].
  assert (Hpos : 0 < / eps) by (apply Rinv_0_lt_compat; lra).
  exists (Z.to_nat (up (/ eps))). intros K HK.
  assert (Hup0 : (0 < up (/ eps))%Z) by (apply lt_IZR; lra).
  assert (HK' : / eps < INR K).
  { apply (Rlt_le_trans _ (IZR (up (/ eps)))); [exact Hup|].
    rewrite <- (Z2Nat.id (up (/ eps))) by lia. rewrite <- INR_IZR_INZ. apply le_INR. exact HK. }
  assert (H2 := INR_lt_pow2 K).
  unfold hK. rewrite <- (Rinv_inv eps). left. apply Rinv_lt_contravar; [| lra].
  apply Rmult_lt_0_compat; [exact Hpos | lra].
Qed.

(** With consistency of order h^2 at the exact solution, the collocated
    rows have at every fine enough step a solution within C h^2 of it. *)
Theorem stab_solution :
  forall (Cc : R) (K1 : nat), 0 <= Cc -> 0 < dyadR rx -> 0 < dyadR rd -> 0 < dyadR hhi ->
  (forall K, (K1 <= K)%nat -> forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall kp, (kp < 5)%nat -> Rabs (GS K (fun _ _ => 0) j kp) <= Cc * (hK K * hK K)) /\
     (forall kp, (kp < 4)%nat -> Rabs (GU K (fun _ _ => 0) j kp) <= Cc * (hK K * hK K))) ->
  exists C K0, 0 <= C /\ forall K, (K0 <= K)%nat ->
  exists x : nat -> vec,
    (forall i, (i < 9)%nat -> x (cutK K 0) i = 0) /\ (forall i, (i < 9)%nat -> x (cutK K 12) i = 0) /\
    (forall j, (cutK K 0 < j < cutK K 12)%nat ->
       (forall kp, (kp < 5)%nat -> GS K x j kp = 0) /\ (forall kp, (kp < 4)%nat -> GU K x j kp = 0)) /\
    (forall j, (cutK K 0 <= j <= cutK K 12)%nat -> vnorm 9 (x j) <= C * (hK K * hK K)).
Proof.
  intros Cc K1 HCc Hrx' Hrd' Hhhi Hcons.
  destruct consts_nonneg as (HS & HCG & HNM & HPI & HBM & HBQ).
  pose (bm := dyadR BM). pose (bq := dyadR BQ). pose (kb := dyadR Kb).
  pose (L1 := S2 * (2 * CG + 3 / 4 * (2 * (1 + bq) * bm + 1))).
  pose (L2 := NM * PI * (L1 + 2 * (1 + bq) * bm + 1) + 2 * bm).
  pose (L0 := L1 + L2 + NM * L1 + 2 * bm).
  pose (C := 2 * L0 * Cc).
  pose (L3 := 6804 * NM * PI + 9720 * bm).
  pose (C2 := Rmax 1 (4 * L3 * kb * C)).
  pose (G1 := S2 * kb * C * (9720 * CG + 3 / 4 * (C2 * C2) * (2430 * (1 + bq) * bm + 1701))).
  pose (G2 := NM * PI * (G1 + 9720 * (1 + bq) * bm * kb * C)).
  pose (G3 := NM * G1 + 2430 * bm * kb * (C2 * C2) * C).
  pose (Gm := G1 + L3 * kb * C + G2 + G3).
  assert (Hbqm : 0 <= bq * bm) by (apply Rmult_le_pos; assumption).
  assert (HL1 : 0 <= L1) by (unfold L1; apply Rmult_le_pos; [exact HS | unfold bq, bm in *; lra]).
  assert (HL2 : 0 <= L2).
  { unfold L2. assert (0 <= NM * PI * (L1 + 2 * (1 + bq) * bm + 1))
      by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | unfold bq, bm in *; lra]).
    unfold bm in *. lra. }
  assert (HL0 : 0 <= L0) by (unfold L0; assert (0 <= NM * L1) by (apply Rmult_le_pos; assumption); unfold bm in *; lra).
  assert (HC : 0 <= C) by (unfold C; apply Rmult_le_pos; [lra | exact HCc]).
  assert (HC21 : 1 <= C2) by (unfold C2; apply Rmax_l).
  assert (HL3c : 4 * L3 * kb * C <= C2) by (unfold C2; apply Rmax_r).
  assert (HL3 : 0 <= L3) by (unfold L3; assert (0 <= NM * PI) by (apply Rmult_le_pos; assumption); unfold bm in *; nra).
  assert (Hkb : 0 <= kb) by exact HKb.
  assert (HC22 : 0 <= C2 * C2) by nra.
  assert (HG1 : 0 <= G1).
  { unfold G1. apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact HC]|].
    assert (0 <= (C2 * C2) * (2430 * (1 + bq) * bm + 1701)) by (apply Rmult_le_pos; [exact HC22 | unfold bq, bm in *; lra]).
    lra. }
  assert (HG2 : 0 <= G2).
  { unfold G2. apply Rmult_le_pos; [apply Rmult_le_pos; assumption|].
    assert (0 <= bm * kb * C) by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact HC]).
    assert (0 <= bq * (bm * kb * C)) by (apply Rmult_le_pos; assumption). lra. }
  assert (HG3 : 0 <= G3).
  { unfold G3. apply Rplus_le_le_0_compat; [apply Rmult_le_pos; assumption|].
    apply Rmult_le_pos; [| exact HC]. apply Rmult_le_pos; [| exact HC22]. apply Rmult_le_pos; [unfold bm in *; lra | exact Hkb]. }
  assert (HLk : 0 <= L3 * kb * C) by (apply Rmult_le_pos; [apply Rmult_le_pos; assumption | exact HC]).
  assert (HGm : 0 <= Gm) by (unfold Gm; lra).
  pose (rmin := Rmin (dyadR rx) (dyadR rd)).
  assert (Hrmin : 0 < rmin) by (unfold rmin; apply Rmin_glb_lt; assumption).
  pose (eps := Rmin (Rmin (/ (4 * Gm + 1)) (2 / C2)) (Rmin (rmin / (2 * C + C2 * C + 1)) (dyadR hhi))).
  assert (Hden : 0 < 2 * C + C2 * C + 1) by nra.
  assert (Heps : 0 < eps).
  { unfold eps. apply Rmin_glb_lt; apply Rmin_glb_lt.
    - apply Rinv_0_lt_compat. lra.
    - unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra].
    - unfold Rdiv. apply Rmult_lt_0_compat; [exact Hrmin | apply Rinv_0_lt_compat; exact Hden].
    - exact Hhhi. }
  destruct (hK_small eps Heps) as [K0' HK0'].
  exists C, (Nat.max (Nat.max K0' 17) K1). split; [exact HC|].
  intros K HK.
  assert (HK17 : (17 <= K)%nat) by lia. assert (HK16 : (16 <= K)%nat) by lia.
  assert (Hh := hK_pos K). assert (Hh1 : hK K <= 1) by (assert (H := hK_le K HK16); lra).
  assert (Heh : hK K <= eps) by (apply HK0'; lia).
  assert (He1 : hK K <= / (4 * Gm + 1)) by (eapply Rle_trans; [exact Heh|]; unfold eps; eapply Rle_trans; apply Rmin_l).
  assert (He2 : hK K <= 2 / C2) by (eapply Rle_trans; [exact Heh|]; unfold eps; eapply Rle_trans; [apply Rmin_l | apply Rmin_r]).
  assert (He3 : hK K <= rmin / (2 * C + C2 * C + 1))
    by (eapply Rle_trans; [exact Heh|]; unfold eps; eapply Rle_trans; [apply Rmin_r | apply Rmin_l]).
  assert (He4 : hK K <= dyadR hhi) by (eapply Rle_trans; [exact Heh|]; unfold eps; eapply Rle_trans; apply Rmin_r).
  assert (HhG : hK K * Gm <= 1 / 4).
  { apply (Rle_trans _ (/ (4 * Gm + 1) * Gm)); [apply Rmult_le_compat_r; assumption|].
    apply (Rmult_le_reg_l (4 * Gm + 1)); [lra|]. rewrite <- Rmult_assoc, Rinv_r by lra. lra. }
  assert (HhC2 : C2 * hK K <= 2).
  { apply (Rle_trans _ (C2 * (2 / C2))); [apply Rmult_le_compat_l; lra|]. right. field. lra. }
  assert (Hhz : hK K * (2 * C + C2 * C) <= rmin).
  { apply (Rle_trans _ (rmin / (2 * C + C2 * C + 1) * (2 * C + C2 * C))).
    - apply Rmult_le_compat_r; [nra | exact He3].
    - apply (Rmult_le_reg_l (2 * C + C2 * C + 1)); [exact Hden|].
      replace ((2 * C + C2 * C + 1) * (rmin / (2 * C + C2 * C + 1) * (2 * C + C2 * C)))
        with (rmin * (2 * C + C2 * C)) by (field; lra).
      nra. }
  pose (rho := C * (hK K * hK K)). pose (cc := Cc * (hK K * hK K)).
  assert (Hrho : 0 <= rho) by (unfold rho; apply Rmult_le_pos; [exact HC | nra]).
  assert (Hcc : 0 <= cc) by (unfold cc; apply Rmult_le_pos; [exact HCc | nra]).
  assert (Hz1 : 2 * rho / hK K <= rmin).
  { replace (2 * rho / hK K) with (hK K * (2 * C)) by (unfold rho; field; lra).
    assert (0 <= hK K * (C2 * C)) by (apply Rmult_le_pos; [lra | nra]). nra. }
  assert (Hz2 : C2 * rho <= rmin).
  { assert (C2 * rho <= hK K * (C2 * C)).
    { unfold rho. replace (C2 * (C * (hK K * hK K))) with (hK K * (C2 * C) * hK K) by ring.
      replace (hK K * (C2 * C)) with (hK K * (C2 * C) * 1) at 2 by ring.
      apply Rmult_le_compat_l; [apply Rmult_le_pos; [lra | nra] | exact Hh1]. }
    assert (0 <= hK K * (2 * C)) by nra. nra. }
  destruct (alg_contract (hK K) C C2 Hh Hh1 HC HC21 HL3c HhG) as [E1 [E2 E3]].
  destruct (alg_small (hK K) cc C2 Hh Hh1 Hcc HC21) as [F1 [F2 F3]].
  assert (EL : L0 * cc = rho / 2) by (unfold rho, cc, C; field).
  destruct (fixed K C2 rho cc HK17 He4 HC21 HhC2 Hrho Hz1 Hz2 E1 E2 E3 Hcc
              (fun j Hj => Hcons K ltac:(lia) j Hj)
              ltac:(fold L1 L2 L0 in F1; rewrite <- EL; exact F1)
              ltac:(fold L1 L2 L0 in F2; rewrite <- EL; exact F2)
              ltac:(fold L1 L2 L0 in F3; rewrite <- EL; exact F3)) as [x [Hx Hfix]].
  destruct (fixed_solves K x HK16 Hfix) as [H0 [H1 Hrows]].
  exists x. split; [exact H0 | split; [exact H1 | split; [exact Hrows|]]].
  intros j Hj. eapply Rle_trans; [apply (nrm_node K C2 x j Hj) | exact Hx].
Qed.

End Stab.

Section Final.

Variable prec : F.precision.
Variables d kn : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs0 : imat.
Variable Rd : list (list (list (list (Z * Z)))).
Variables BM BMM BQ : Z * Z.

Hypothesis Hcells2 : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges2 prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI BM BMM BQ
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hstart : forall WiI, owi prec frames 0 = Some WiI -> start_range prec d (mktab d) chh chh kn WiI = Some rs0.
Hypothesis Hok : assemble3d prec frames es cells rs0 Rd = true.

Variables Kb rx rd hhi : Z * Z.
Hypothesis Hball : forall (r : bool) kp c, (kp < (if r then 5 else 4))%nat -> (c < 192)%nat ->
  ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true.
Hypothesis HKb : 0 <= dyadR Kb.
Hypothesis Hrx : 0 < dyadR rx.
Hypothesis Hrd : 0 < dyadR rd.
Hypothesis Hhhi : 0 < dyadR hhi.

(** The verdicts of the cell, start, assembly and ball checks, with
    consistency of order h^2 at the exact solution, give at every step
    h = 2^-K past some K0 a solution of the collocated rows within C h^2 of
    the exact node values. *)
Theorem colloc3d_second_order :
  forall (Cc : R) (K1 : nat), 0 <= Cc ->
  (forall K, (K1 <= K)%nat -> forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall kp, (kp < 5)%nat -> Rabs (GS K (fun _ _ => 0) j kp) <= Cc * (hK K * hK K)) /\
     (forall kp, (kp < 4)%nat -> Rabs (GU K (fun _ _ => 0) j kp) <= Cc * (hK K * hK K))) ->
  exists C K0, 0 <= C /\ forall K, (K0 <= K)%nat ->
  exists x : nat -> vec,
    (forall i, (i < 9)%nat -> x (cutK K 0) i = 0) /\ (forall i, (i < 9)%nat -> x (cutK K 12) i = 0) /\
    (forall j, (cutK K 0 < j < cutK K 12)%nat ->
       (forall kp, (kp < 5)%nat -> GS K x j kp = 0) /\ (forall kp, (kp < 4)%nat -> GU K x j kp = 0)) /\
    (forall j, (cutK K 0 <= j <= cutK K 12)%nat -> vnorm 9 (x j) <= C * (hK K * hK K)).
Proof.
  intros Cc K1 HCc Hcons.
  destruct (lin_bound2 prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok) as [S2 HS2].
  exact (stab_solution prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok S2 HS2 Kb rx rd hhi Hball HKb
           (Rlt_le _ _ Hrx) (Rlt_le _ _ Hrd) Cc K1 HCc Hrx Hrd Hhhi Hcons).
Qed.

End Final.
