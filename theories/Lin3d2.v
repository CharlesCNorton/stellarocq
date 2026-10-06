(** The constants of the linearized rows, and their bound with the first
    row folded into the start.

    Over the cells of [CellTM.cell_ranges2], every row's M^-1, M and Q are
    bounded by the certificate's BM, BMM and BQ ([row_bounds]), and the
    frames bound N ([N_bound]). A row's sources enter the recursion as zeta,
    whose first nine entries carry the radial source with a factor h
    ([zeta_x_bound], [zeta_bound]), and a solution's next slope is N z + zeta
    in its first nine entries ([slope_step]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat TMEval TMat Shoot Recur CFMS CFMS2 Step NBound Osc
  CellTM CellSound CellN CellMain Frames Assemble Check3d BMat Level3d Final3d Lin3d.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Vectors                                                           *)

Lemma vnorm_stack :
  forall a b, vnorm 9 (stack a b) <= vnorm 5 a + vnorm 4 b.
Proof.
  intros a b. assert (Ha := vnorm_nonneg 5 a). assert (Hb := vnorm_nonneg 4 b).
  apply vnorm_le; [lra|]. intros i Hi. unfold stack. destruct (Nat.ltb_spec i 5) as [H5|H5].
  - assert (H := vnorm_ge 5 a i H5). lra.
  - assert (H := vnorm_ge 4 b (i - 5) ltac:(lia)). lra.
Qed.

Lemma vnorm_zjoin :
  forall x p, vnorm 14 (zjoin x p) <= vnorm 9 x + vnorm 5 p.
Proof.
  intros x p. assert (Hx := vnorm_nonneg 9 x). assert (Hp := vnorm_nonneg 5 p).
  apply vnorm_le; [lra|]. intros i Hi. unfold zjoin. destruct (Nat.ltb_spec i 9) as [H9|H9].
  - assert (H := vnorm_ge 9 x i H9). lra.
  - assert (H := vnorm_ge 5 p (i - 9) ltac:(lia)). lra.
Qed.

Lemma vnorm_scal_nonneg : forall n a x, 0 <= a -> vnorm n (fun i => a * x i) = a * vnorm n x.
Proof. intros n a x Ha. rewrite vnorm_scal, Rabs_right by lra. reflexivity. Qed.

Lemma vnorm_lo9 : forall z, vnorm 9 (zx z) <= vnorm 14 z.
Proof.
  intros z. apply vnorm_le; [apply vnorm_nonneg|]. intros i Hi. unfold zx. apply vnorm_ge. lia.
Qed.

Section Lin2.

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

Lemma Hcells : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Proof.
  intros k WiI Hk Hw j Hj.
  exact (proj1 (cell_ranges2_sound prec d Hcov Hd _ _ _ _ kn 4 _ _ BM BMM BQ _ (Hcells2 k WiI Hk Hw j Hj))).
Qed.

(** The cells bound M^-1, M and Q at every row. *)
Lemma row_bounds :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  mnorm 9 9 (Mi3 K j) <= dyadR BM /\ mnorm 9 9 (mstack (Pp3 K j) (Up3 K j)) <= dyadR BMM /\
  mnorm 5 9 (Qm (hK K) (Pp3 K j) (Pm3 K (S j))) <= dyadR BQ.
Proof.
  intros K j HK Hj.
  destruct (row_split K j HK Hj) as [k [i [t [Hk [Hi [Ht Ej]]]]]].
  destruct (Xk_inv prec d Hd frames es cells rs0 Rd Hok k Hk) as [_ [_ Howi]].
  destruct (cell_point K k i t HK Hi Ht) as [_ [Hu [Hw Hp]]].
  assert (Hj16 : (i / 16 < 256)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  destruct (cell_ranges2_sound prec d Hcov Hd (csc k (i / 16)) chh chalf chh kn 4 (gW frames k) (gWiI prec frames k)
              BM BMM BQ _ (Hcells2 k _ Hk Howi _ Hj16)) as [_ HB].
  destruct (HB _ _ Hu Hw Hp) as [B1 [B2 B3]].
  replace (dyadR (csc k (i / 16)) + (INR (cutK K k + i * fK K + t) * hK K - dyadR (csc k (i / 16))))
    with (INR j * hK K) in B1, B2, B3 by (rewrite Ej; ring).
  replace (dyadR chh + (hK K - dyadR chh)) with (hK K) in B1, B2, B3 by ring.
  split; [exact B1 | split; [exact B2|]].
  unfold Pm3. rewrite INR_S_h. exact B3.
Qed.

Lemma BM_nonneg : 0 <= dyadR BM.
Proof.
  destruct (row_bounds 16 (cutK 16 0) ltac:(lia) ltac:(split; [lia | rewrite cutK_12 by lia; assert (H := cutK_0_pos 16); lia]))
    as [H _].
  eapply Rle_trans; [apply mnorm_nonneg | exact H].
Qed.

Lemma BQ_nonneg : 0 <= dyadR BQ.
Proof.
  destruct (row_bounds 16 (cutK 16 0) ltac:(lia) ltac:(split; [lia | rewrite cutK_12 by lia; assert (H := cutK_0_pos 16); lia]))
    as [_ [_ H]].
  eapply Rle_trans; [apply mnorm_nonneg | exact H].
Qed.

Lemma BMM_nonneg : 0 <= dyadR BMM.
Proof.
  destruct (row_bounds 16 (cutK 16 0) ltac:(lia) ltac:(split; [lia | rewrite cutK_12 by lia; assert (H := cutK_0_pos 16); lia]))
    as [_ [H _]].
  eapply Rle_trans; [apply mnorm_nonneg | exact H].
Qed.

(** The frames bound N at every row. *)
Definition Nmax : R := Wimax frames es * msum (nuk prec cells) 12 * Wmax frames es.

Lemma N_bound :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  mnorm 14 14 (bN (INR j * hK K) (hK K)) <= Nmax.
Proof.
  intros K j HK Hj.
  destruct (row_split K j HK Hj) as [k [i [t [Hk [Hi [Ht Ej]]]]]].
  set (A := Aseg (gW frames k) (ge es k) (Xk frames k) K j).
  assert (HA : mnorm 14 14 A <= nuk prec cells k).
  { exact (Ak_nuk prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok k K j Hk HK
             ltac:(rewrite lenK; split; [lia | nia])). }
  assert (HM : meq 14 (bN (INR j * hK K) (hK K)) (mm 14 (mm 14 (Wis frames es k) A) (Ws frames es k))).
  { apply (unconj prec d Hd frames es cells rs0 Rd Hok k _ A Hk). apply meq_refl. }
  rewrite (mnorm_meq 14 _ _ HM).
  eapply Rle_trans; [apply mnorm_mm|].
  eapply Rle_trans; [apply Rmult_le_compat_r; [apply mnorm_nonneg | apply mnorm_mm]|].
  unfold Nmax.
  assert (H1 : mnorm 14 14 (Wis frames es k) <= Wimax frames es)
    by exact (msum_ge12 (fun k => mnorm 14 14 (Wis frames es k)) k (fun _ => mnorm_nonneg _ _ _) Hk).
  assert (H2 : mnorm 14 14 (Ws frames es k) <= Wmax frames es)
    by exact (msum_ge12 (fun k => mnorm 14 14 (Ws frames es k)) k (fun _ => mnorm_nonneg _ _ _) Hk).
  assert (H3 : nuk prec cells k <= msum (nuk prec cells) 12)
    by exact (msum_ge12 (nuk prec cells) k (nuk_nonneg prec cells) Hk).
  apply Rmult_le_compat; [apply Rmult_le_pos; apply mnorm_nonneg | apply mnorm_nonneg | | exact H2].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact H1 | lra].
Qed.

Lemma Nmax_nonneg : 0 <= Nmax.
Proof.
  assert (H := N_bound 16 (cutK 16 0) ltac:(lia)
                 ltac:(split; [lia | rewrite cutK_12 by lia; assert (H := cutK_0_pos 16); lia])).
  eapply Rle_trans; [apply mnorm_nonneg | exact H].
Qed.

(** A row's sources in the recursion. *)
Lemma zeta_x :
  forall K j rs ru i, (i < 9)%nat -> zeta3 K j rs ru i = mv 9 (Mi3 K j) (stack (fun c => hK K * rs c) ru) i.
Proof. intros K j rs ru i Hi. unfold zeta3, zeta. rewrite zjoin_lo by exact Hi. reflexivity. Qed.

Lemma zeta_x_bound :
  forall K j rs ru, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  vnorm 9 (zx (zeta3 K j rs ru)) <= dyadR BM * (hK K * vnorm 5 rs + vnorm 4 ru).
Proof.
  intros K j rs ru HK Hj. destruct (row_bounds K j HK Hj) as [B1 _].
  assert (Hh := hK_pos K).
  rewrite (vnorm_ext 9 (zx (zeta3 K j rs ru)) (mv 9 (Mi3 K j) (stack (fun c => hK K * rs c) ru)))
    by (intros c Hc; unfold zx; apply zeta_x; exact Hc).
  eapply Rle_trans; [apply vnorm_mv|].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact B1|].
  eapply Rle_trans; [apply vnorm_stack|]. rewrite vnorm_scal_nonneg by lra. lra.
Qed.

Lemma zeta_bound :
  forall K j rs ru, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  vnorm 14 (zeta3 K j rs ru) <= (1 + dyadR BQ) * (dyadR BM * (hK K * vnorm 5 rs + vnorm 4 ru)) + vnorm 5 rs.
Proof.
  intros K j rs ru HK Hj. destruct (row_bounds K j HK Hj) as [B1 [_ B3]].
  assert (Hh := hK_pos K).
  set (b := mv 9 (Mi (Pp3 K j) (Up3 K j)) (stack (fun i => hK K * rs i) ru)).
  assert (Hb : vnorm 9 b <= dyadR BM * (hK K * vnorm 5 rs + vnorm 4 ru)).
  { unfold b. eapply Rle_trans; [apply vnorm_mv|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact B1|].
    eapply Rle_trans; [apply vnorm_stack|]. rewrite vnorm_scal_nonneg by lra. lra. }
  unfold zeta3, zeta. fold b.
  eapply Rle_trans; [apply vnorm_zjoin|].
  assert (Hp : vnorm 5 (fun i => rs i + mv 9 (Qm (hK K) (Pp3 K j) (Pm3 K (S j))) b i)
               <= vnorm 5 rs + dyadR BQ * vnorm 9 b).
  { apply vnorm_le; [apply Rplus_le_le_0_compat; [apply vnorm_nonneg | apply Rmult_le_pos; [apply BQ_nonneg | apply vnorm_nonneg]]|].
    intros i Hi. eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [apply vnorm_ge; exact Hi|].
    eapply Rle_trans; [apply (vnorm_ge 5 (mv 9 (Qm (hK K) (Pp3 K j) (Pm3 K (S j))) b) i Hi)|].
    assert (Hmv : vnorm 5 (mv 9 (Qm (hK K) (Pp3 K j) (Pm3 K (S j))) b)
                  <= mnorm 5 9 (Qm (hK K) (Pp3 K j) (Pm3 K (S j))) * vnorm 9 b).
    { apply vnorm_le; [apply Rmult_le_pos; [apply mnorm_nonneg | apply vnorm_nonneg]|].
      intros r Hr. unfold mv. eapply Rle_trans; [apply msum_abs|].
      eapply Rle_trans with (msum (fun c => Rabs (Qm (hK K) (Pp3 K j) (Pm3 K (S j)) r c) * vnorm 9 b) 9).
      - apply msum_le. intros c Hc. rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | apply vnorm_ge; exact Hc].
      - rewrite msum_scal_r. apply Rmult_le_compat_r; [apply vnorm_nonneg|].
        apply (fmax_ge (mrow 9 (Qm (hK K) (Pp3 K j) (Pm3 K (S j))))). exact Hr. }
    eapply Rle_trans; [exact Hmv|]. apply Rmult_le_compat_r; [apply vnorm_nonneg | exact B3]. }
  assert (HQ0 := BQ_nonneg). assert (Hb0 := vnorm_nonneg 9 b). nra.
Qed.

(** A solution's next slope: N z + zeta in the first nine entries. *)
Lemma slope_step :
  forall K j (X : nat -> vec) rs ru, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs i) ->
  (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru i) ->
  forall i, (i < 9)%nat ->
  slope (hK K) X (S j) i = mv 14 (bN (INR j * hK K) (hK K)) (state (hK K) (Pm3 K) X j) i + zeta3 K j rs ru i.
Proof.
  intros K j X rs ru HK Hj Hs Hu i Hi.
  assert (Hh := hK_pos K).
  assert (HS := rows_step (hK K) Hh (Pp3 K) (Pm3 K) (Sx3 K) (Up3 K) (V3 K) (Mi3 K) X rs ru j
                  (fun a c Ha Hc => proj1 (Mi3_inv prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K j HK Hj a c Ha Hc))
                  Hs Hu i ltac:(lia)).
  rewrite (step3 prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K j HK Hj _ rs ru i ltac:(lia)) in HS.
  unfold PsiK in HS. rewrite mv_madd_mat, mv_scal_mat, mv_mI in HS by lia.
  assert (E1 : state (hK K) (Pm3 K) X j i = X j i) by (unfold state; apply zjoin_lo; exact Hi).
  assert (E2 : state (hK K) (Pm3 K) X (S j) i = X (S j) i) by (unfold state; apply zjoin_lo; exact Hi).
  rewrite E1, E2 in HS.
  unfold slope. replace (S j - 1)%nat with j by lia.
  rewrite <- HS. field. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The first reference step                                          *)

(** The steps of segment 0's first reference step are within
    th0 = 2^-16 nu of the identity in frame 0, so their inverses are bounded
    by PsiInvB. *)
Definition th0 : R := / 65536 * nu prec (gcell cells 0 0).
Definition PsiInvB : R := mnorm 14 14 (Wis frames es 0) * mnorm 14 14 (Ws frames es 0) / (1 - th0).

Lemma th0_lt : th0 < 1.
Proof.
  destruct (checks prec d Hd frames es cells rs0 Rd Hok) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  unfold psi0_ok in H10.
  assert (Hnu : contains (I.convert (inu prec (gcell cells 0 0))) (Xreal (nu prec (gcell cells 0 0)))) by apply iupmax_in.
  assert (Hhr : contains (I.convert (ihr prec)) (Xreal hr)) by apply dyad_correct.
  assert (Hs := I.sub_correct prec _ _ (Xreal (IZR 1)) _ (I.fromZ_correct prec 1) (I.mul_correct prec _ _ _ _ Hhr Hnu)).
  apply (sign_pos _ _ Hs) in H10.
  assert (Ehr : hr = / 65536) by (unfold hr, dyadR; cbn [fst snd]; rewrite pRZ16; ring).
  unfold th0. rewrite <- Ehr. lra.
Qed.

Lemma PsiInvB_nonneg : 0 <= PsiInvB.
Proof.
  assert (H := th0_lt). unfold PsiInvB. apply Rmult_le_pos; [apply Rmult_le_pos; apply mnorm_nonneg|].
  left. apply Rinv_0_lt_compat. lra.
Qed.

Lemma Psi_first_inv :
  forall K t, (16 <= K)%nat -> (t < fK K)%nat ->
  exists Y, is_inv 14 (PsiK K (cutK K 0 + t)) Y /\ mnorm 14 14 Y <= PsiInvB.
Proof.
  intros K t HK Ht.
  assert (Hh := hK_pos K). assert (Hle := hK_le K HK). assert (Hth0 := th0_lt).
  assert (E0 : (cutK K 0 + 0 * fK K + t)%nat = (cutK K 0 + t)%nat) by lia.
  pose proof (Ak_nu prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok 0 K 0 t ltac:(lia) HK ltac:(lia) Ht) as HA.
  rewrite E0 in HA. cbv beta in HA.
  set (A := Aseg (gW frames 0) (ge es 0) (Xk frames 0) K (cutK K 0 + t)) in HA.
  set (th := hK K * mnorm 14 14 A).
  assert (Hthle : th <= th0).
  { unfold th, th0. apply Rmult_le_compat; [lra | apply mnorm_nonneg | lra | exact HA]. }
  assert (Hth : th < 1) by lra.
  set (E := fun r c => mI r c + hK K * A r c).
  assert (HD : forall M, meq 14 M E -> mnorm 14 14 (msub mI M) <= th).
  { intros M HM. rewrite (mnorm_meq 14 _ (fun r c => (- hK K) * A r c)).
    - rewrite mnorm_scal_abs, Rabs_Ropp, Rabs_right by lra. unfold th. lra.
    - intros r c Hr Hc. unfold msub. rewrite HM by assumption. unfold E. ring. }
  destruct (approx_inverse 14 E mI th (HD _ (mm_mI_meq_l 14 E)) (HD _ (mm_mI_meq_r 14 E)) Hth)
    as [Z [HZ1 [HZ2 HZn]]].
  assert (HZ : is_inv 14 E Z) by (intros i j Hi Hj; split; [apply HZ1 | apply HZ2]; assumption).
  assert (HC : meq 14 (mm 14 (mm 14 (Ws frames es 0) (PsiK K (cutK K 0 + t))) (Wis frames es 0)) E).
  { unfold PsiK. eapply meq_trans;
      [apply (conj_step 14 (Ws frames es 0) (Wis frames es 0) (HWW' prec d Hd frames es cells rs0 Rd Hok 0 ltac:(lia)))|].
    intros r c Hr Hc. reflexivity. }
  assert (HU := unconj prec d Hd frames es cells rs0 Rd Hok 0 _ _ ltac:(lia) HC).
  exists (mm 14 (mm 14 (Wis frames es 0) Z) (Ws frames es 0)). split.
  - apply (is_inv_meq (mm 14 (mm 14 (Wis frames es 0) E) (Ws frames es 0))).
    + apply meq_sym. exact HU.
    + apply is_inv_conj; [exact (Wk_inv prec d Hd frames es cells rs0 Rd Hok 0 ltac:(lia)) | exact HZ].
  - eapply Rle_trans; [apply mnorm_mm|].
    eapply Rle_trans; [apply Rmult_le_compat_r; [apply mnorm_nonneg | apply mnorm_mm]|].
    assert (HZb : mnorm 14 14 Z <= / (1 - th0)).
    { eapply Rle_trans; [exact HZn|]. assert (H1 := mnorm_mI 14).
      apply (Rle_trans _ (1 / (1 - th))).
      - unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact H1].
      - unfold Rdiv. rewrite Rmult_1_l. apply Rinv_le_contravar; lra. }
    unfold PsiInvB. unfold Rdiv.
    replace (mnorm 14 14 (Wis frames es 0) * mnorm 14 14 (Ws frames es 0) * / (1 - th0))
      with (mnorm 14 14 (Wis frames es 0) * / (1 - th0) * mnorm 14 14 (Ws frames es 0)) by ring.
    apply Rmult_le_compat_r; [apply mnorm_nonneg|]. apply Rmult_le_compat_l; [apply mnorm_nonneg | exact HZb].
Qed.

(** The first row's sources: the rows from m + 2 on as the recursion's
    sources, none at m and m + 1. *)
Definition src4 (K : nat) (rs ru : nat -> vec) (j : nat) : vec :=
  if Nat.leb j (S (cutK K 0)) then (fun _ => 0) else zeta3 K j (rs j) (ru j).

Definition srcw2 (K : nat) (rs ru : nat -> vec) : R :=
  msum (fun l => hK K * vnorm 14 (zeta3 K (S (S (cutK K 0)) + l)%nat (rs (S (S (cutK K 0)) + l)%nat)
                                     (ru (S (S (cutK K 0)) + l)%nat)))
       (cutK K 12 - S (S (cutK K 0)))%nat.

Lemma swt_src4 : forall K rs ru, (16 <= K)%nat -> swt (hK K) 12 (cutK K) (src4 K rs ru) = srcw2 K rs ru.
Proof.
  intros K rs ru HK. assert (Hh := hK_pos K). assert (Hm := cutK_0_pos K).
  assert (H12 : (cutK K 0 < cutK K 12)%nat) by (rewrite cutK_12 by exact HK; lia).
  assert (H12' : (S (S (cutK K 0)) <= cutK K 12)%nat) by (rewrite cutK_12 by exact HK; lia).
  unfold swt, srcw2. replace (cutK K 12 - cutK K 0)%nat with (2 + (cutK K 12 - S (S (cutK K 0))))%nat by lia.
  rewrite msum_add. cbn [msum]. rewrite !Nat.add_0_r.
  unfold src4 at 1 2.
  replace (Nat.leb (cutK K 0) (S (cutK K 0))) with true by (symmetry; apply Nat.leb_le; lia).
  replace (Nat.leb (cutK K 0 + 1) (S (cutK K 0))) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite vnorm_zero, Rmult_0_r, !Rplus_0_l.
  apply msum_ext. intros l Hl. unfold src4.
  replace (Nat.leb (cutK K 0 + (2 + l)) (S (cutK K 0))) with false by (symmetry; apply Nat.leb_gt; lia).
  replace (cutK K 0 + (2 + l))%nat with (S (S (cutK K 0)) + l)%nat by lia.
  rewrite Rabs_right by lra. reflexivity.
Qed.

(** The start inhomogeneity: h C Psi_{m+1}^-1 zeta_{m+1}. *)
Definition gst (K : nat) (Y : mat) (rs ru : vec) : vec :=
  fun r => hK K * mv 14 (bC (/ 4) (hK K)) (mv 14 Y (zeta3 K (S (cutK K 0)) rs ru)) r.

Lemma mv_inv_r :
  forall (A Y : mat) x r, is_inv 14 A Y -> (r < 14)%nat -> mv 14 A (mv 14 Y x) r = x r.
Proof. intros A Y x r HY Hr. apply mv_inv_cancel; [intros i j Hi Hj; exact (proj2 (HY i j Hi Hj)) | exact Hr]. Qed.

Lemma mv_inv_l :
  forall (A Y : mat) x r, is_inv 14 A Y -> (r < 14)%nat -> mv 14 Y (mv 14 A x) r = x r.
Proof. intros A Y x r HY Hr. apply mv_inv_cancel; [intros i j Hi Hj; exact (proj1 (HY i j Hi Hj)) | exact Hr]. Qed.

(** With the first row's step folded into the start condition, every
    solution's state from node m + 2 on is bounded by the start
    inhomogeneity and the remaining sources. *)
Theorem lin_bound2 :
  exists S2, 0 <= S2 /\
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
Proof.
  destruct (assemble3d_sound prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hstart Hok) as [q Hq].
  assert (Hq0 : 0 <= q).
  { destruct (Hq 16%nat ltac:(lia)) as [X16 [_ [_ H16]]]. eapply Rle_trans; [apply mnorm_nonneg | exact H16]. }
  assert (HG0 : 0 <= Gall prec frames es cells) by (apply msum_nonneg; intros; apply Gk_nonneg).
  assert (HW0 : 0 <= Wmax frames es) by (apply msum_nonneg; intros; apply mnorm_nonneg).
  assert (HWi0 : 0 <= Wimax frames es) by (apply msum_nonneg; intros; apply mnorm_nonneg).
  assert (A1 : 0 <= Gall prec frames es cells * (Wimax frames es * q)) by (repeat apply Rmult_le_pos; assumption).
  assert (A2 : 0 <= Gall prec frames es cells * (Wimax frames es * (q * (Wmax frames es * Gall prec frames es cells))))
    by (repeat apply Rmult_le_pos; assumption).
  exists (Gall prec frames es cells * (Wimax frames es * q)
          + Gall prec frames es cells * (Wimax frames es * (q * (Wmax frames es * Gall prec frames es cells)))
          + Gall prec frames es cells). split.
  { apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat|]; assumption. }
  intros K HK rs ru X Y HY HXm HXe Hrows j Hj.
  assert (HK16 : (16 <= K)%nat) by lia.
  assert (Hh := hK_pos K). assert (Hm0 := cutK_0_pos K).
  assert (H12 : (S (S (cutK K 0)) < cutK K 12)%nat) by (rewrite cutK_12 by exact HK16; lia).
  destruct (Hq K HK16) as [XK [HXl [_ HXq]]].
  destruct (Psi0_inv prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K HK16) as [Y0 HY0].
  set (m := cutK K 0) in *.
  set (st := state (hK K) (Pm3 K) X).
  (* the run: st from m + 2, its preimages under the first two steps before *)
  set (z := fun l => if Nat.eqb l m then mv 14 Y0 (mv 14 Y (st (S (S m))))
                     else if Nat.eqb l (S m) then mv 14 Y (st (S (S m))) else st l).
  assert (Hz : forall l, (S (S m) <= l)%nat -> z l = st l).
  { intros l Hl. unfold z. replace (Nat.eqb l m) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb l (S m)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
  assert (Hz1 : z (S m) = mv 14 Y (st (S (S m)))).
  { unfold z. replace (Nat.eqb (S m) m) with false by (symmetry; apply Nat.eqb_neq; lia). rewrite Nat.eqb_refl.
    reflexivity. }
  assert (Hz0 : z m = mv 14 Y0 (mv 14 Y (st (S (S m))))) by (unfold z; rewrite Nat.eqb_refl; reflexivity).
  (* the rows from m + 1 on are steps of the recursion *)
  assert (Hstep : forall l, (m < l < cutK K 12)%nat -> forall r, (r < 14)%nat ->
            st (S l) r = mv 14 (PsiK K l) (st l) r + hK K * zeta3 K l (rs l) (ru l) r).
  { intros l Hl r Hr. destruct (Hrows l Hl) as [Hs Hu].
    unfold st. rewrite <- (rows_step (hK K) Hh (Pp3 K) (Pm3 K) (Sx3 K) (Up3 K) (V3 K) (Mi3 K) X (rs l) (ru l) l
                            (fun i k Hi Hk => proj1 (Mi3_inv prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K l HK16
                                                       ltac:(lia) i k Hi Hk)) Hs Hu r Hr).
    exact (step3 prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K l HK16 ltac:(lia) _ (rs l) (ru l) r Hr). }
  assert (Hrun : runs (hK K) (PsiK K) z (src4 K rs ru) (cutK K 0) (cutK K 12)).
  { intros l Hl r Hr. fold m in Hl.
    destruct (Nat.eq_dec l m) as [->|Hne0].
    - rewrite Hz1, Hz0, (mv_inv_r _ _ _ r HY0 Hr). unfold src4.
      replace (Nat.leb m (S (cutK K 0))) with true by (symmetry; apply Nat.leb_le; unfold m; lia). ring.
    - destruct (Nat.eq_dec l (S m)) as [->|Hne1].
      + rewrite (Hz (S (S m))) by lia. rewrite Hz1, (mv_inv_r _ _ _ r HY Hr). unfold src4.
        replace (Nat.leb (S m) (S (cutK K 0))) with true by (symmetry; apply Nat.leb_le; unfold m; lia). ring.
      + rewrite (Hz (S l)) by lia. rewrite (Hz l) by lia. rewrite (Hstep l ltac:(lia) r Hr). unfold src4.
        replace (Nat.leb l (S (cutK K 0))) with false by (symmetry; apply Nat.leb_gt; unfold m in *; lia). reflexivity. }
  (* the start condition: C z_{m+1} = 0 at the solution, so Cs z_m = h C Y zeta_{m+1} *)
  assert (Hst : forall r, (r < 5)%nat ->
            mv 14 (bCs (/ 4) (hK K)) (z (cutK K 0)) r = gst K Y (rs (S m)) (ru (S m)) r).
  { intros r Hr. fold m. rewrite (start_cond K (z m) HK16 r Hr). fold m.
    assert (HP : forall c, (c < 14)%nat -> mv 14 (PsiK K m) (z m) c = mv 14 Y (st (S (S m))) c).
    { intros c Hc. rewrite Hz0. apply mv_inv_r; assumption. }
    rewrite (HP (9 + r)%nat ltac:(lia)).
    rewrite (mv_extn 9 (Pm3 K (S m)) (mv 14 (PsiK K m) (z m)) (mv 14 Y (st (S (S m)))) r)
      by (intros c Hc; apply HP; lia).
    (* Y st_{m+2} = st_{m+1} + h Y zeta_{m+1} *)
    assert (HYs : forall c, (c < 14)%nat ->
              mv 14 Y (st (S (S m))) c = st (S m) c + hK K * mv 14 Y (zeta3 K (S m) (rs (S m)) (ru (S m))) c).
    { intros c Hc.
      rewrite (mv_extn 14 Y (st (S (S m)))
                 (fun c' => mv 14 (PsiK K (S m)) (st (S m)) c' + hK K * zeta3 K (S m) (rs (S m)) (ru (S m)) c') c)
        by (intros c' Hc'; apply Hstep; [unfold m in *; lia | exact Hc']).
      rewrite mv_add, mv_scal_vec. rewrite (mv_inv_l _ _ _ c HY Hc). reflexivity. }
    rewrite (mv_extn 9 (Pm3 K (S m)) (mv 14 Y (st (S (S m))))
               (fun c => st (S m) c + hK K * mv 14 Y (zeta3 K (S m) (rs (S m)) (ru (S m))) c) r)
      by (intros c Hc; apply HYs; lia).
    rewrite (HYs (9 + r)%nat ltac:(lia)). rewrite mv_add, mv_scal_vec.
    (* C st_{m+1} = 0 *)
    assert (HC0 : mv 9 (Pm3 K (S m)) (st (S m)) r - hK K * st (S m) (9 + r)%nat = 0).
    { unfold st, state. rewrite zjoin_hi.
      rewrite (mv_extn 9 (Pm3 K (S m)) (zjoin (X (S m)) (mv 9 (Pm3 K (S m)) (slope (hK K) X (S m)))) (X (S m)) r)
        by (intros c Hc; apply zjoin_lo; exact Hc).
      rewrite (mv_extn 9 (Pm3 K (S m)) (slope (hK K) X (S m)) (fun c => / hK K * X (S m) c) r).
      2: { intros c Hc. unfold slope. replace (S m - 1)%nat with m by lia. unfold m. rewrite HXm by exact Hc.
           field. lra. }
      rewrite mv_scal_vec. field. lra. }
    unfold gst. fold m. rewrite (mv_bC (/ 4) (hK K) _ r Hr).
    assert (EPm : bPm (/ 4 + hK K) (hK K) = Pm3 K (S m)) by (unfold Pm3, m; rewrite INR_S_h, INR_cut0 by exact HK16; reflexivity).
    rewrite EPm. lra. }
  (* the end condition *)
  assert (Hen : forall r, (r < 9)%nat -> z (cutK K 12) r = 0).
  { intros r Hr. rewrite Hz by lia. unfold st, state. rewrite zjoin_lo by exact Hr. apply HXe. exact Hr. }
  (* the bound of the run *)
  destruct (node_seg K j HK16 ltac:(unfold m in *; lia)) as [k [i [Hk [Hi Ej]]]].
  assert (HB := run_bound_g (hK K) (PsiK K) 12 ltac:(lia) (cutK K) (fun k _ => cutK_mono K k (S k) (Nat.le_succ_diag_r k))
                  (Ws frames es) (Wis frames es) (HWW prec d Hd frames es cells rs0 Rd Hok) (bCs (/ 4) (hK K))
                  (Ws frames es 11%nat) XK q (Gall prec frames es cells) (Wmax frames es) (Wimax frames es) HXl HXq
                  (fun k Hk i i' Hii => Rle_trans _ _ _ (seg_prod_bound prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok
                                                           K k i i' HK16 Hk Hii)
                                          (msum_ge12 (Gk prec frames es cells) k (Gk_nonneg prec frames es cells) Hk))
                  (fun k Hk => msum_ge12 (fun k => mnorm 14 14 (Ws frames es k)) k (fun _ => mnorm_nonneg _ _ _) Hk)
                  (msum_ge12 (fun k => mnorm 14 14 (Ws frames es k)) 11 (fun _ => mnorm_nonneg _ _ _) ltac:(lia))
                  (fun k Hk => msum_ge12 (fun k => mnorm 14 14 (Wis frames es k)) k (fun _ => mnorm_nonneg _ _ _) Hk)
                  z (src4 K rs ru) (gst K Y (rs (S m)) (ru (S m))) Hrun Hst Hen k i Hk Hi).
  rewrite <- Ej in HB. rewrite (Hz j) in HB by (unfold m in *; lia). rewrite swt_src4 in HB by exact HK16.
  fold st. eapply Rle_trans; [exact HB|].
  set (gn := vnorm 5 (gst K Y (rs (S m)) (ru (S m)))).
  assert (Hg0 : 0 <= gn) by apply vnorm_nonneg.
  assert (Hs0 : 0 <= srcw2 K rs ru).
  { apply msum_nonneg. intros l _. apply Rmult_le_pos; [lra | apply vnorm_nonneg]. }
  assert (P1 := Rmult_le_pos _ _ A1 Hs0). assert (P2 := Rmult_le_pos _ _ A2 Hg0).
  assert (P3 := Rmult_le_pos _ _ HG0 Hg0).
  match goal with |- ?L <= ?Rr => assert (E : Rr - L =
      Gall prec frames es cells * (Wimax frames es * q) * srcw2 K rs ru
      + Gall prec frames es cells * (Wimax frames es * (q * (Wmax frames es * Gall prec frames es cells))) * gn
      + Gall prec frames es cells * gn) by ring end.
  lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The start inhomogeneity and the first state                      *)

Lemma mv_row_le :
  forall m n (A : mat) x r, (r < m)%nat -> Rabs (mv n A x r) <= mnorm m n A * vnorm n x.
Proof.
  intros m n A x r Hr. unfold mv. eapply Rle_trans; [apply msum_abs|].
  eapply Rle_trans with (msum (fun c => Rabs (A r c) * vnorm n x) n).
  - apply msum_le. intros c Hc. rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | apply vnorm_ge; exact Hc].
  - rewrite msum_scal_r. apply Rmult_le_compat_r; [apply vnorm_nonneg|]. apply (fmax_ge (mrow n A)). exact Hr.
Qed.

Lemma vnorm_9_14 : forall x, vnorm 9 x <= vnorm 14 x.
Proof. intros x. apply vnorm_le; [apply vnorm_nonneg|]. intros i Hi. apply vnorm_ge. lia. Qed.

Lemma Pm1_bound : forall K, (16 <= K)%nat -> mnorm 5 9 (Pm3 K (S (cutK K 0))) <= dyadR BMM + hK K * dyadR BQ.
Proof.
  intros K HK. assert (Hh := hK_pos K).
  destruct (row_bounds K (cutK K 0) HK
              ltac:(split; [lia | rewrite cutK_12 by exact HK; assert (H := cutK_0_pos K); lia])) as [_ [B2 B3]].
  rewrite (mnorm_ext 5 9 (Pm3 K (S (cutK K 0)))
             (fun i c => Pp3 K (cutK K 0) i c + hK K * Qm (hK K) (Pp3 K (cutK K 0)) (Pm3 K (S (cutK K 0))) i c)).
  2: { intros i c Hi Hc. unfold Qm. field. lra. }
  eapply Rle_trans; [apply mnorm_add_le|]. rewrite mnorm_scal_abs, Rabs_right by lra.
  apply Rplus_le_compat; [| apply Rmult_le_compat_l; [lra | exact B3]].
  eapply Rle_trans; [| exact B2].
  apply fmax_le; [apply mnorm_nonneg|]. intros i Hi. eapply Rle_trans; [| apply (fmax_ge _ 9 i); lia].
  unfold mrow, mstack. apply Req_le. apply msum_ext. intros c Hc.
  replace (Nat.ltb i 5) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Definition cg : R :=
  (dyadR BMM + 2 * dyadR BQ) * dyadR BM + 1
  + (dyadR BMM + dyadR BQ + 1) * Nmax * PsiInvB * ((1 + dyadR BQ) * dyadR BM + 1).

Lemma cg_nonneg : 0 <= cg.
Proof.
  assert (H1 := BM_nonneg). assert (H2 := BMM_nonneg). assert (H3 := BQ_nonneg).
  assert (H4 := Nmax_nonneg). assert (H5 := PsiInvB_nonneg). unfold cg.
  assert (0 <= (dyadR BMM + 2 * dyadR BQ) * dyadR BM) by (apply Rmult_le_pos; lra).
  assert (0 <= (dyadR BMM + dyadR BQ + 1) * Nmax * PsiInvB * ((1 + dyadR BQ) * dyadR BM + 1)).
  { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra] |].
    assert (0 <= (1 + dyadR BQ) * dyadR BM) by (apply Rmult_le_pos; lra). lra. }
  lra.
Qed.

(** The start inhomogeneity carries the first row's radial source with h^2
    and its poloidal source with h. *)
Lemma g_bound :
  forall K Y rs ru, (17 <= K)%nat -> is_inv 14 (PsiK K (S (cutK K 0))) Y -> mnorm 14 14 Y <= PsiInvB ->
  vnorm 5 (gst K Y rs ru) <= cg * (hK K * hK K * vnorm 5 rs + hK K * vnorm 4 ru).
Proof.
  intros K Y rs ru HK HY HYn.
  assert (HK16 : (16 <= K)%nat) by lia. assert (Hh := hK_pos K).
  assert (Hh1 : hK K <= 1) by (assert (H := hK_le K HK16); lra).
  assert (HBM := BM_nonneg). assert (HBMM := BMM_nonneg). assert (HBQ := BQ_nonneg).
  assert (HNm := Nmax_nonneg). assert (HPi := PsiInvB_nonneg).
  assert (Hm1 : (cutK K 0 <= S (cutK K 0) < cutK K 12)%nat)
    by (rewrite cutK_12 by exact HK16; assert (H := cutK_0_pos K); lia).
  set (m := cutK K 0) in *.
  set (zt := zeta3 K (S m) rs ru).
  set (yz := mv 14 Y zt).
  set (N1 := bN (INR (S m) * hK K) (hK K)).
  set (R5 := vnorm 5 rs). set (U4 := vnorm 4 ru).
  assert (HR0 : 0 <= R5) by apply vnorm_nonneg. assert (HU0 : 0 <= U4) by apply vnorm_nonneg.
  assert (Hb : vnorm 9 (zx zt) <= dyadR BM * (hK K * R5 + U4)) by exact (zeta_x_bound K (S m) rs ru HK16 Hm1).
  assert (Hz : vnorm 14 zt <= (1 + dyadR BQ) * (dyadR BM * (hK K * R5 + U4)) + R5)
    by exact (zeta_bound K (S m) rs ru HK16 Hm1).
  assert (HN : mnorm 14 14 N1 <= Nmax) by exact (N_bound K (S m) HK16 Hm1).
  assert (HQ1 : mnorm 5 9 (Qm (hK K) (Pp3 K (S m)) (Pm3 K (S (S m)))) <= dyadR BQ)
    by exact (proj2 (proj2 (row_bounds K (S m) HK16 Hm1))).
  assert (HP : mnorm 5 9 (Pm3 K (S m)) <= dyadR BMM + hK K * dyadR BQ) by exact (Pm1_bound K HK16).
  (* Y zt = zt - h N1 (Y zt) *)
  assert (HYz : forall c, (c < 14)%nat -> yz c = zt c - hK K * mv 14 N1 yz c).
  { intros c Hc. assert (E := mv_inv_r (PsiK K (S m)) Y zt c HY Hc). unfold PsiK in E.
    rewrite mv_madd_mat, mv_scal_mat, mv_mI in E by exact Hc. fold yz N1 in E. lra. }
  assert (Hyz : vnorm 14 yz <= PsiInvB * vnorm 14 zt).
  { unfold yz. eapply Rle_trans; [apply vnorm_mv|]. apply Rmult_le_compat_r; [apply vnorm_nonneg | exact HYn]. }
  set (Z := vnorm 14 zt) in *. set (B := vnorm 9 (zx zt)) in *.
  assert (HZ0 : 0 <= Z) by apply vnorm_nonneg. assert (HB0 : 0 <= B) by apply vnorm_nonneg.
  set (NZ := vnorm 14 (mv 14 N1 yz)).
  assert (HNZ : NZ <= Nmax * (PsiInvB * Z)).
  { unfold NZ. eapply Rle_trans; [apply vnorm_mv|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact HN | exact Hyz]. }
  assert (HNZ0 : 0 <= NZ) by apply vnorm_nonneg.
  (* each row of the start inhomogeneity *)
  assert (Hrow : forall r, (r < 5)%nat ->
            Rabs (gst K Y rs ru r)
            <= hK K * ((dyadR BMM + hK K * dyadR BQ) * B + hK K * (dyadR BMM + hK K * dyadR BQ) * NZ
                       + hK K * (R5 + dyadR BQ * B) + hK K * hK K * NZ)).
  { intros r Hr. unfold gst. fold m zt yz.
    rewrite (mv_bC (/ 4) (hK K) yz r Hr).
    assert (EPm : bPm (/ 4 + hK K) (hK K) = Pm3 K (S m)) by (unfold Pm3, m; rewrite INR_S_h, INR_cut0 by exact HK16; reflexivity).
    rewrite EPm.
    rewrite (mv_extn 9 (Pm3 K (S m)) yz (fun c => zt c - hK K * mv 14 N1 yz c) r) by (intros c Hc; apply HYz; lia).
    rewrite (HYz (9 + r)%nat ltac:(lia)). rewrite mv_sub, mv_scal_vec.
    assert (A1 : Rabs (mv 9 (Pm3 K (S m)) zt r) <= (dyadR BMM + hK K * dyadR BQ) * B).
    { rewrite (mv_extn 9 (Pm3 K (S m)) zt (zx zt) r) by (intros; reflexivity).
      eapply Rle_trans; [apply (mv_row_le 5 9); exact Hr|]. apply Rmult_le_compat_r; [exact HB0 | exact HP]. }
    assert (A2 : Rabs (mv 9 (Pm3 K (S m)) (mv 14 N1 yz) r) <= (dyadR BMM + hK K * dyadR BQ) * NZ).
    { eapply Rle_trans; [apply (mv_row_le 5 9); exact Hr|].
      apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact HP | apply vnorm_9_14]. }
    assert (A3 : Rabs (zt (9 + r)%nat) <= R5 + dyadR BQ * B).
    { unfold zt, zeta3, zeta. rewrite zjoin_hi.
      eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [apply vnorm_ge; exact Hr|].
      eapply Rle_trans; [apply (mv_row_le 5 9); exact Hr|]. apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact HQ1|].
      unfold B. apply Req_le. apply vnorm_ext. intros c Hc. unfold zx, zt, zeta3, zeta. rewrite zjoin_lo by exact Hc.
      reflexivity. }
    assert (A4 : Rabs (mv 14 N1 yz (9 + r)%nat) <= NZ) by (apply vnorm_ge; lia).
    rewrite Rabs_mult, Rabs_right by lra. apply Rmult_le_compat_l; [lra|].
    unfold Rminus. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp.
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang | apply Rle_refl]|].
    rewrite Rabs_Ropp, !Rabs_mult, !(Rabs_right (hK K)) by lra.
    assert (A5 : Rabs (zt (9 + r)%nat + - (hK K * mv 14 N1 yz (9 + r)%nat)) <= R5 + dyadR BQ * B + hK K * NZ).
    { eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp, Rabs_mult, (Rabs_right (hK K)) by lra.
      assert (hK K * Rabs (mv 14 N1 yz (9 + r)%nat) <= hK K * NZ) by (apply Rmult_le_compat_l; lra). lra. }
    assert (hK K * Rabs (mv 9 (Pm3 K (S m)) (mv 14 N1 yz) r) <= hK K * ((dyadR BMM + hK K * dyadR BQ) * NZ))
      by (apply Rmult_le_compat_l; lra).
    assert (hK K * Rabs (zt (9 + r)%nat + - (hK K * mv 14 N1 yz (9 + r)%nat)) <= hK K * (R5 + dyadR BQ * B + hK K * NZ))
      by (apply Rmult_le_compat_l; lra).
    lra. }
  (* the coefficients, with h <= 1 *)
  assert (Hcoef : forall r, (r < 5)%nat -> Rabs (gst K Y rs ru r) <= cg * (hK K * hK K * R5 + hK K * U4)).
  { intros r Hr. eapply Rle_trans; [exact (Hrow r Hr)|].
    set (h := hK K) in *.
    assert (Hhh : h * h <= h) by nra.
    assert (HB' : h * B <= dyadR BM * (h * h * R5 + h * U4)).
    { replace (dyadR BM * (h * h * R5 + h * U4)) with (h * (dyadR BM * (h * R5 + U4))) by ring.
      apply Rmult_le_compat_l; lra. }
    assert (HZ' : h * h * Z <= (1 + dyadR BQ) * dyadR BM * (h * h * R5 + h * U4) + h * h * R5).
    { assert (h * h * Z <= h * h * ((1 + dyadR BQ) * (dyadR BM * (h * R5 + U4)) + R5))
        by (apply Rmult_le_compat_l; [nra | exact Hz]).
      assert (E : h * h * ((1 + dyadR BQ) * (dyadR BM * (h * R5 + U4)) + R5)
                  = (1 + dyadR BQ) * dyadR BM * (h * (h * h * R5) + h * (h * U4)) + h * h * R5) by ring.
      assert (0 <= (1 + dyadR BQ) * dyadR BM) by (apply Rmult_le_pos; lra).
      assert (h * (h * h * R5) <= h * h * R5) by (rewrite <- (Rmult_1_l (h * h * R5)) at 2; apply Rmult_le_compat_r; nra).
      assert (h * (h * U4) <= h * U4) by (rewrite <- (Rmult_1_l (h * U4)) at 2; apply Rmult_le_compat_r; nra).
      assert ((1 + dyadR BQ) * dyadR BM * (h * (h * h * R5) + h * (h * U4))
              <= (1 + dyadR BQ) * dyadR BM * (h * h * R5 + h * U4)) by (apply Rmult_le_compat_l; lra).
      lra. }
    assert (HNZ' : h * h * NZ <= Nmax * PsiInvB * ((1 + dyadR BQ) * dyadR BM * (h * h * R5 + h * U4) + h * h * R5)).
    { assert (h * h * NZ <= h * h * (Nmax * (PsiInvB * Z))) by (apply Rmult_le_compat_l; [nra | exact HNZ]).
      replace (h * h * (Nmax * (PsiInvB * Z))) with (Nmax * PsiInvB * (h * h * Z)) in H by ring.
      assert (Nmax * PsiInvB * (h * h * Z)
              <= Nmax * PsiInvB * ((1 + dyadR BQ) * dyadR BM * (h * h * R5 + h * U4) + h * h * R5))
        by (apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact HZ']).
      lra. }
    assert (HT0 : 0 <= h * h * R5 + h * U4) by nra.
    assert (HR' : h * h * R5 <= h * h * R5 + h * U4) by nra.
    (* expand the row bound *)
    assert (Erow : h * ((dyadR BMM + h * dyadR BQ) * B + h * (dyadR BMM + h * dyadR BQ) * NZ
                        + h * (R5 + dyadR BQ * B) + h * h * NZ)
                   = (dyadR BMM + h * dyadR BQ + h * dyadR BQ) * (h * B)
                     + (dyadR BMM + h * dyadR BQ + h) * (h * h * NZ) + h * h * R5) by ring.
    rewrite Erow.
    assert (C1 : (dyadR BMM + h * dyadR BQ + h * dyadR BQ) * (h * B)
                 <= (dyadR BMM + 2 * dyadR BQ) * (dyadR BM * (h * h * R5 + h * U4))).
    { apply Rmult_le_compat; [nra | nra | nra | exact HB']. }
    assert (C2 : (dyadR BMM + h * dyadR BQ + h) * (h * h * NZ)
                 <= (dyadR BMM + dyadR BQ + 1)
                    * (Nmax * PsiInvB * ((1 + dyadR BQ) * dyadR BM * (h * h * R5 + h * U4) + (h * h * R5 + h * U4)))).
    { apply Rmult_le_compat; [nra | nra | nra |].
      eapply Rle_trans; [exact HNZ'|]. apply Rmult_le_compat_l; [apply Rmult_le_pos; lra|].
      apply Rplus_le_compat_l. exact HR'. }
    assert (Ecg : cg * (h * h * R5 + h * U4)
                  = (dyadR BMM + 2 * dyadR BQ) * (dyadR BM * (h * h * R5 + h * U4)) + (h * h * R5 + h * U4)
                    + (dyadR BMM + dyadR BQ + 1)
                      * (Nmax * PsiInvB * ((1 + dyadR BQ) * dyadR BM * (h * h * R5 + h * U4) + (h * h * R5 + h * U4))))
      by (unfold cg; ring).
    rewrite Ecg. lra. }
  apply vnorm_le; [apply Rmult_le_pos; [exact cg_nonneg | nra]|]. exact Hcoef.
Qed.

(** The state at the first node from the state at the second. *)
Lemma first_state :
  forall K (X : nat -> vec) rs ru Y, (17 <= K)%nat ->
  is_inv 14 (PsiK K (S (cutK K 0))) Y -> mnorm 14 14 Y <= PsiInvB ->
  (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X (S (cutK K 0)) i = rs i) ->
  (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X (S (cutK K 0)) i = ru i) ->
  vnorm 14 (state (hK K) (Pm3 K) X (S (cutK K 0)))
  <= PsiInvB * (vnorm 14 (state (hK K) (Pm3 K) X (S (S (cutK K 0)))) + hK K * vnorm 14 (zeta3 K (S (cutK K 0)) rs ru)).
Proof.
  intros K X rs ru Y HK HY HYn Hs Hu.
  assert (HK16 : (16 <= K)%nat) by lia. assert (Hh := hK_pos K).
  assert (Hm1 : (cutK K 0 <= S (cutK K 0) < cutK K 12)%nat)
    by (rewrite cutK_12 by exact HK16; assert (H := cutK_0_pos K); lia).
  set (m := cutK K 0) in *.
  set (st := state (hK K) (Pm3 K) X).
  assert (Hstep : forall r, (r < 14)%nat -> st (S (S m)) r = mv 14 (PsiK K (S m)) (st (S m)) r + hK K * zeta3 K (S m) rs ru r).
  { intros r Hr. unfold st.
    rewrite <- (rows_step (hK K) Hh (Pp3 K) (Pm3 K) (Sx3 K) (Up3 K) (V3 K) (Mi3 K) X rs ru (S m)
                 (fun i k Hi Hk => proj1 (Mi3_inv prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K (S m) HK16 Hm1 i k Hi Hk))
                 Hs Hu r Hr).
    exact (step3 prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hok K (S m) HK16 Hm1 _ rs ru r Hr). }
  rewrite (vnorm_ext 14 (st (S m)) (mv 14 Y (fun c => st (S (S m)) c - hK K * zeta3 K (S m) rs ru c))).
  - eapply Rle_trans; [apply vnorm_mv|]. apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact HYn|].
    apply vnorm_le; [apply Rplus_le_le_0_compat; [apply vnorm_nonneg | apply Rmult_le_pos; [lra | apply vnorm_nonneg]]|].
    intros c Hc. unfold Rminus. eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_Ropp, Rabs_mult, (Rabs_right (hK K)) by lra.
    apply Rplus_le_compat; [apply vnorm_ge; exact Hc | apply Rmult_le_compat_l; [lra | apply vnorm_ge; exact Hc]].
  - intros c Hc.
    rewrite (mv_extn 14 Y (fun c0 => st (S (S m)) c0 - hK K * zeta3 K (S m) rs ru c0) (mv 14 (PsiK K (S m)) (st (S m))) c)
      by (intros c' Hc'; rewrite Hstep by exact Hc'; ring).
    symmetry. apply mv_inv_l; assumption.
Qed.

End Lin2.
