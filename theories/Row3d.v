(** One collocation point's residual near the exact jet.

    For a point and a cell whose ball check passes, and s, h in the cell:
    with the slots x, dm, dp of the nine unknowns moved by z within the box
    of the check ([zball]) and their slots e moved by any w, the residual
    [Rv z w] less its value at z', w' and the partials at the exact jet
    applied to the steps is bounded by the check's K times quadratic terms
    ([row_expand]). The x, dm, dp part is Taylor.v's second-order bound,
    with the adjoint slots as partials and their tangents as second
    partials; the residual is affine in the e slots (Affine.v, [aff_true]),
    so the e part is the e partials at z applied to the e step, and those
    vary with z at most as K ([Az_osc]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra FunctionalExtensionality.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Newton TMEval LinCheck DerivSeq Adjoint AdjointSound
  CellTM QDiff Check3d Jet Mat Ball3d Taylor Ball3dSound Affine.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The slots                                                         *)

Definition inxd (k : nat) : bool := existsb (Nat.eqb k) xdslots.
Definition ine (k : nat) : bool := existsb (Nat.eqb k) eslots.
Definition xslots : list nat := map (uslot 0) (seq 0 9).
Definition inx (k : nat) : bool := existsb (Nat.eqb k) xslots.

Lemma existsb_eqb : forall L k, existsb (Nat.eqb k) L = true <-> In k L.
Proof.
  intros L k. rewrite existsb_exists. split.
  - intros [x [Hx Ex]]. apply Nat.eqb_eq in Ex. subst. exact Hx.
  - intros H. exists k. split; [exact H | apply Nat.eqb_refl].
Qed.

Fixpoint nodupb (L : list nat) : bool :=
  match L with [] => true | a :: L' => negb (existsb (Nat.eqb a) L') && nodupb L' end.

Lemma nodupb_NoDup : forall L, nodupb L = true -> NoDup L.
Proof.
  induction L as [|a L IH]; intros H; [constructor|].
  cbn [nodupb] in H. destruct (andb_prop _ _ H) as [H1 H2].
  constructor; [| exact (IH H2)].
  intros Hin. apply existsb_eqb in Hin. rewrite Hin in H1. discriminate.
Qed.

Lemma NoDup_xdslots : NoDup xdslots.
Proof. apply nodupb_NoDup. vm_compute. reflexivity. Qed.

Lemma NoDup_eslots : NoDup eslots.
Proof. apply nodupb_NoDup. vm_compute. reflexivity. Qed.

Lemma xd_facts : forallb (fun k => Nat.leb 12 k && Nat.ltb k 52 && negb (ine k)) xdslots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma e_facts : forallb (fun k => Nat.leb 12 k && Nat.ltb k 52) eslots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma x_facts : forallb inxd xslots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pc_facts : forallb (fun pc => Bool.eqb (inx (uslot (fst pc) (snd pc))) (Nat.eqb (fst pc) 0)) xdpc = true.
Proof. vm_compute. reflexivity. Qed.

Lemma inxd_range : forall k, inxd k = true -> (12 <= k < 52)%nat /\ ine k = false.
Proof.
  intros k Hk. apply existsb_eqb in Hk. assert (H := xd_facts). rewrite forallb_forall in H.
  specialize (H k Hk). destruct (andb_prop _ _ H) as [H1 He]. destruct (andb_prop _ _ H1) as [Ha Hb].
  apply Nat.leb_le in Ha. apply Nat.ltb_lt in Hb. apply negb_true_iff in He. split; [lia | exact He].
Qed.

Lemma ine_range : forall k, ine k = true -> (12 <= k < 52)%nat.
Proof.
  intros k Hk. apply existsb_eqb in Hk. assert (H := e_facts). rewrite forallb_forall in H.
  specialize (H k Hk). destruct (andb_prop _ _ H) as [Ha Hb].
  apply Nat.leb_le in Ha. apply Nat.ltb_lt in Hb. lia.
Qed.

Lemma x_xd : forall k, inx k = true -> inxd k = true.
Proof.
  intros k Hk. apply existsb_eqb in Hk. assert (H := x_facts). rewrite forallb_forall in H. exact (H k Hk).
Qed.

Lemma inx_pc : forall pc, In pc xdpc -> inx (uslot (fst pc) (snd pc)) = Nat.eqb (fst pc) 0.
Proof.
  intros pc Hpc. assert (H := pc_facts). rewrite forallb_forall in H. apply eqb_prop. exact (H pc Hpc).
Qed.

Lemma inxd_pc : forall pc, In pc xdpc -> inxd (uslot (fst pc) (snd pc)) = true.
Proof.
  intros pc Hpc. apply existsb_eqb. unfold xdslots.
  apply (in_map (fun pc => uslot (fst pc) (snd pc))). exact Hpc.
Qed.

Lemma in_tails : forall k, In k (xdslots ++ eslots) -> (12 <= k < 52)%nat.
Proof.
  intros k Hk. apply in_app_or in Hk. destruct Hk as [Hk|Hk].
  - exact (proj1 (inxd_range k (proj2 (existsb_eqb _ _) Hk))).
  - exact (ine_range k (proj2 (existsb_eqb _ _) Hk)).
Qed.

(* ---------------------------------------------------------------- *)
(* The perturbed environments                                        *)

Lemma fold_left_map' :
  forall (A B C : Type) (f : A -> B -> A) (g : C -> B) (l : list C) (a : A),
  fold_left f (map g l) a = fold_left (fun x y => f x (g y)) l a.
Proof. intros A B C f g l. induction l as [|y l IH]; intros a; [reflexivity|]. cbn [map fold_left]. apply IH. Qed.

(** Setting each slot of a list without repeats from its own value. *)
Lemma fold_set :
  forall (L : list nat) (v : nat -> ExtendedR -> ExtendedR) (E : env ExtendedR) k, NoDup L ->
  eget k (fold_left (fun E j => eset j E (v j (eget j E Xnan))) L E) Xnan
  = if existsb (Nat.eqb k) L then v k (eget k E Xnan) else eget k E Xnan.
Proof.
  induction L as [|a L IH]; intros v E k Hnd; [reflexivity|].
  inversion Hnd as [|? ? Hna HndL]; subst.
  cbn [fold_left existsb]. rewrite (IH v _ k HndL).
  destruct (Nat.eqb_spec k a) as [->|Hne].
  - cbn [orb]. destruct (existsb (Nat.eqb a) L) eqn:Ex.
    + exfalso. apply Hna. apply existsb_eqb. exact Ex.
    + apply eget_eset_eq.
  - cbn [orb]. rewrite !eget_eset_neq by exact Hne. reflexivity.
Qed.

Lemma Ez_fold :
  forall r kp s h z, Ez r kp s h z = fold_left (fun E j => eset j E (Xreal (xr (eget j E Xnan) + z j))) xdslots (Ex r kp s h).
Proof. intros. unfold Ez, xdslots. rewrite fold_left_map'. reflexivity. Qed.

Lemma Ez_get :
  forall r kp s h z k,
  eget k (Ez r kp s h z) Xnan = if inxd k then Xreal (xr (eget k (Ex r kp s h) Xnan) + z k) else eget k (Ex r kp s h) Xnan.
Proof.
  intros. rewrite Ez_fold. exact (fold_set xdslots (fun j x => Xreal (xr x + z j)) (Ex r kp s h) k NoDup_xdslots).
Qed.

Lemma Ez_at : forall r kp s h z i, inxd i = true -> xr (eget i (Ez r kp s h z) Xnan) = xr (eget i (Ex r kp s h) Xnan) + z i.
Proof. intros r kp s h z i Hi. rewrite Ez_get, Hi. reflexivity. Qed.

(** The e slots of the jet moved as well. *)
Definition Ezw (r : bool) (kp : nat) (s h : R) (z w : nat -> R) : env ExtendedR :=
  fold_left (fun E j => eset j E (Xreal (xr (eget j E Xnan) + w j))) eslots (Ez r kp s h z).

Lemma Ezw_get :
  forall r kp s h z w k,
  eget k (Ezw r kp s h z w) Xnan = if ine k then Xreal (xr (eget k (Ez r kp s h z) Xnan) + w k) else eget k (Ez r kp s h z) Xnan.
Proof. intros. exact (fold_set eslots (fun j x => Xreal (xr x + w j)) (Ez r kp s h z) k NoDup_eslots). Qed.

Lemma Ez_upd_in :
  forall r kp s h z i t, inxd i = true -> forall k,
  eget k (Ez r kp s h (upd z i t)) Xnan = eget k (eset i (Ez r kp s h z) (Xreal (xr (eget i (Ex r kp s h) Xnan) + t))) Xnan.
Proof.
  intros r kp s h z i t Hi k. rewrite Ez_get. destruct (Nat.eq_dec k i) as [->|Hne].
  - rewrite eget_eset_eq, Hi. unfold upd. rewrite Nat.eqb_refl. reflexivity.
  - rewrite eget_eset_neq by exact Hne. rewrite Ez_get. unfold upd. rewrite (proj2 (Nat.eqb_neq k i) Hne). reflexivity.
Qed.

Lemma Ez_upd_out :
  forall r kp s h z i t, inxd i = false -> forall k, eget k (Ez r kp s h (upd z i t)) Xnan = eget k (Ez r kp s h z) Xnan.
Proof.
  intros r kp s h z i t Hi k. rewrite !Ez_get. destruct (inxd k) eqn:Hk; [| reflexivity].
  unfold upd. destruct (Nat.eqb_spec k i) as [->|]; [rewrite Hi in Hk; discriminate | reflexivity].
Qed.

(* ---------------------------------------------------------------- *)
(* Real functions                                                    *)

Lemma dpl_shift : forall f a x l, derivable_pt_lim f (a + x) l -> derivable_pt_lim (fun t => f (a + t)) x l.
Proof.
  intros f a x l H eps Heps. destruct (H eps Heps) as [del Hd]. exists del. intros t Ht Htd.
  replace (a + (x + t)) with (a + x + t) by ring. apply Hd; assumption.
Qed.

Lemma dpl_affine : forall c L a x, derivable_pt_lim (fun t => c + L * (t - a)) x L.
Proof.
  intros c L a x eps Heps. exists (mkposreal 1 Rlt_0_1). intros t Ht _.
  replace ((c + L * (x + t - a) - (c + L * (x - a))) / t - L) with 0 by (field; exact Ht).
  rewrite Rabs_R0. exact Heps.
Qed.

Lemma msum_tail_zero : forall f n m, (forall j, (n <= j)%nat -> f j = 0) -> msum f (n + m) = msum f n.
Proof.
  intros f n m H. induction m as [|m IH]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite Nat.add_succ_r. cbn [msum]. rewrite IH, (H (n + m)%nat) by lia. ring.
Qed.

(** Every slot of the flattened residuals has degree at most one in the e slots. *)
Definition aff_of (a : list binding * env nat * nat) : bool := aff_ok 87 ine (fst (fst a)).

Lemma aff_true : forall r, aff_of (anfs r) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma aff_ab : forall r, aff_ok 87 ine (ab r) = true.
Proof. intros r. exact (aff_true r). Qed.

(** The poloidal output has degree zero in the e slots. *)
Definition deg_of (a : list binding * env nat * nat) : nat := eget (rget (snd (fst a)) rtop3) (degs 87 ine (fst (fst a))) 0%nat.

Lemma deg_of_p : deg_of (anfs false) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma deg_of_eq : forall r, deg_of (anfs r) = eget (tout r) (degs 87 ine (ab r)) 0%nat.
Proof. intros r. reflexivity. Qed.

Lemma deg_p : eget (tout false) (degs 87 ine (ab false)) 0%nat = 0%nat.
Proof. rewrite <- (deg_of_eq false). exact deg_of_p. Qed.

Lemma fib_Ezw : forall r kp s h z w, fib 87 ine (Ez r kp s h z) (Ezw r kp s h z w).
Proof.
  intros r kp s h z w. split.
  - intros i Hi Hm. rewrite Ezw_get, Hm. reflexivity.
  - intros i Hi Hm. rewrite Ezw_get, Hm. eexists. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* One point over one cell                                           *)

Section Row.

Variable prec : F.precision.
Variables (r : bool) (kp c : nat) (Kb rx rd hhi : Z * Z).
Hypothesis Hcell : ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true.
Hypothesis Hrx : 0 <= dyadR rx.
Hypothesis Hrd : 0 <= dyadR rd.
Variables s h : R.
Hypothesis Hs : dyadR (clo c) <= s <= dyadR (chi c).
Hypothesis Hh : 0 <= h <= dyadR hhi.

(** The box of the check: values within rx, slopes within rd, no other slot moved. *)
Definition radk (k : nat) : R := if inx k then dyadR rx else if inxd k then dyadR rd else 0.
Definition nradk (k : nat) : R := - radk k.

Lemma radk_nonneg : forall k, 0 <= radk k.
Proof. intros k. unfold radk. destruct (inx k); [exact Hrx|]. destruct (inxd k); [exact Hrd | lra]. Qed.

Lemma radk_out : forall k, inxd k = false -> radk k = 0.
Proof.
  intros k Hk. unfold radk. destruct (inx k) eqn:Ex; [rewrite (x_xd k Ex) in Hk; discriminate|]. rewrite Hk. reflexivity.
Qed.

Definition zball (z : nat -> R) : Prop :=
  (forall k, inxd k = false -> z k = 0) /\ (forall k, inxd k = true -> Rabs (z k) <= radk k).

Lemma zball_inbox : forall z, zball z -> inbox 52 nradk radk z.
Proof.
  intros z [H0 H1] k Hk. unfold nradk. destruct (inxd k) eqn:Ek.
  - assert (Ha := H1 k Ek). assert (Hb := Rle_abs (z k)). assert (Hc := Rle_abs (- z k)). rewrite Rabs_Ropp in Hc. lra.
  - rewrite (H0 k Ek), (radk_out k Ek). lra.
Qed.

Lemma zball_high : forall z, zball z -> forall j, (52 <= j)%nat -> z j = 0.
Proof. intros z [H0 _] j Hj. apply H0. destruct (inxd j) eqn:E; [| reflexivity]. destruct (inxd_range j E). lia. Qed.

Lemma zball_zero : zball (fun _ => 0).
Proof. split; intros; [reflexivity | rewrite Rabs_R0; apply radk_nonneg]. Qed.

Lemma inbox_ball :
  forall y, inbox 52 nradk radk y -> forall pc, In pc xdpc -> Rabs (y (uslot (fst pc) (snd pc))) <= rad rx rd pc.
Proof.
  intros y Hy pc Hpc. assert (Hx := inxd_pc pc Hpc). destruct (inxd_range _ Hx) as [Hr _].
  assert (Hb := Hy _ (proj2 Hr)). unfold nradk in Hb.
  replace (rad rx rd pc) with (radk (uslot (fst pc) (snd pc))).
  - apply Rabs_le. lra.
  - unfold radk, rad. rewrite (inx_pc pc Hpc), Hx. destruct (Nat.eqb (fst pc) 0); reflexivity.
Qed.

Lemma ball_at :
  forall y, inbox 52 nradk radk y ->
  tail_env (ab r) (ttop r) (tout r) (Ez r kp s h y) /\
  (forall l g, In l xdslots -> In g (gslots r) ->
     exists v, eget (g + length (tl r)) (xextend (Ez r kp s h y) (with_dseq l 87 (length (tl r)) (tl r))) Xnan = Xreal v /\
               Rabs v <= dyadR Kb).
Proof. intros y Hy. exact (ball_sound prec r kp c rx rd hhi Kb Hcell s h y Hs Hh (inbox_ball y Hy)). Qed.

(** The residual, its partial in slot k, and that partial's derivative along slot l. *)
Definition Fz (z : nat -> R) : R := xr (eget (tout r) (xextend (Ez r kp s h z) (tl r)) Xnan).

Definition Az (k : nat) (z : nat -> R) : R :=
  xr (eget (in_slot 87 (ttop r) (tout r) (k - 12)) (xextend (Ez r kp s h z) (tl r)) Xnan).

Definition Tz (k l : nat) (z : nat -> R) : R :=
  xr (eget (in_slot 87 (ttop r) (tout r) (k - 12) + length (tl r))
           (xextend (Ez r kp s h z) (with_dseq l 87 (length (tl r)) (tl r))) Xnan).

Lemma env_upd_in :
  forall z i t L k, inxd i = true ->
  eget k (xextend (Ez r kp s h (upd z i t)) L) Xnan
  = eget k (xextend (eset i (Ez r kp s h z) (Xreal (xr (eget i (Ex r kp s h) Xnan) + t))) L) Xnan.
Proof. intros z i t L k Hi. apply env_agree. intros j. apply Ez_upd_in. exact Hi. Qed.

Lemma env_upd_out :
  forall z i t L k, inxd i = false ->
  eget k (xextend (Ez r kp s h (upd z i t)) L) Xnan = eget k (xextend (Ez r kp s h z) L) Xnan.
Proof. intros z i t L k Hi. apply env_agree. intros j. apply Ez_upd_out. exact Hi. Qed.

Lemma Fz_flat : forall z i t, inxd i = false -> Fz (upd z i t) = Fz z.
Proof. intros z i t Hi. unfold Fz. rewrite env_upd_out by exact Hi. reflexivity. Qed.

Lemma Az_flat : forall k z i t, inxd i = false -> Az k (upd z i t) = Az k z.
Proof. intros k z i t Hi. unfold Az. rewrite env_upd_out by exact Hi. reflexivity. Qed.

Lemma Fz_partial :
  forall y, inbox 52 nradk radk y -> forall i, inxd i = true ->
  derivable_pt_lim (fun t => Fz (upd y i t)) (y i) (Az i y).
Proof.
  intros y Hy i Hi.
  destruct (tail_facts r) as [Hwf [Hsg [Htop [Ho [Hwft Hin]]]]].
  destruct (ball_at y Hy) as [HT _].
  destruct (inxd_range i Hi) as [Hr _].
  assert (HD := adj_partial (ab r) (ttop r) (tout r) Hwf Hsg Htop Ho Hwft Hin (Ez r kp s h y) HT (i - 12) ltac:(lia)).
  replace (12 + (i - 12))%nat with i in HD by lia.
  rewrite <- tl_split in HD. rewrite Ez_at in HD by exact Hi.
  apply dpl_shift in HD.
  eapply dpl_ext; [| exact HD]. intros t. cbv beta. unfold Fz. rewrite env_upd_in by exact Hi. reflexivity.
Qed.

Lemma Az_partial :
  forall y, inbox 52 nradk radk y -> forall k l, In k (xdslots ++ eslots) -> inxd l = true ->
  derivable_pt_lim (fun t => Az k (upd y l t)) (y l) (Tz k l y).
Proof.
  intros y Hy k l Hk Hl.
  destruct (tail_facts r) as [Hwf [Hsg [Htop [Ho [Hwft Hin]]]]].
  destruct (ball_at y Hy) as [HT HB].
  assert (Hkr := in_tails k Hk).
  destruct (inxd_range l Hl) as [Hlr _].
  assert (Hg : In (in_slot 87 (ttop r) (tout r) (k - 12)) (gslots r)).
  { unfold gslots. apply (in_map (fun k => in_slot 87 (ttop r) (tout r) (k - 12))). exact Hk. }
  destruct (HB l _ (proj1 (existsb_eqb _ _) Hl) Hg) as [v [Ev _]].
  assert (Hgr := in_slot_lt (ab r) (ttop r) (tout r) Htop Ho Hin (k - 12) ltac:(lia)).
  assert (HD := tan_partial (ab r) (ttop r) (tout r) Htop Ho Hwft (Ez r kp s h y) HT l
                  (in_slot 87 (ttop r) (tout r) (k - 12)) ltac:(lia) Hgr (ex_intro _ v Ev)).
  rewrite <- !tl_split in HD. rewrite Ez_at in HD by exact Hl.
  apply dpl_shift in HD.
  eapply dpl_ext; [| exact HD]. intros t. cbv beta. unfold Az. rewrite env_upd_in by exact Hl. reflexivity.
Qed.

Lemma Tz_bound :
  forall y, inbox 52 nradk radk y -> forall k l, In k (xdslots ++ eslots) -> inxd l = true ->
  Rabs (Tz k l y) <= dyadR Kb.
Proof.
  intros y Hy k l Hk Hl. destruct (ball_at y Hy) as [_ HB].
  assert (Hg : In (in_slot 87 (ttop r) (tout r) (k - 12)) (gslots r)).
  { unfold gslots. apply (in_map (fun k => in_slot 87 (ttop r) (tout r) (k - 12))). exact Hk. }
  destruct (HB l _ (proj1 (existsb_eqb _ _) Hl) Hg) as [v [Ev Hv]].
  unfold Tz. rewrite Ev. exact Hv.
Qed.

(** The second-order bound in the slots x, dm, dp. *)
Definition gT (i : nat) (z : nat -> R) : R := if inxd i then Az i z else 0.
Definition DgT (i l : nat) (z : nat -> R) : R := if inxd i && inxd l then Tz i l z else 0.
Definition KT (i l : nat) : R := if inxd i && inxd l then dyadR Kb else 0.

Lemma HF_T :
  forall y, inbox 52 nradk radk y -> forall i, (i < 52)%nat -> derivable_pt_lim (fun t => Fz (upd y i t)) (y i) (gT i y).
Proof.
  intros y Hy i Hi. unfold gT. destruct (inxd i) eqn:Ei.
  - apply Fz_partial; assumption.
  - apply (dpl_ext (fun _ => Fz y)); [intros t; cbv beta; symmetry; apply Fz_flat; exact Ei | apply dpl_const].
Qed.

Lemma Hg_T :
  forall y, inbox 52 nradk radk y -> forall i l, (i < 52)%nat -> (l < 52)%nat ->
  derivable_pt_lim (fun t => gT i (upd y l t)) (y l) (DgT i l y).
Proof.
  intros y Hy i l Hi Hl. unfold gT, DgT. destruct (inxd i) eqn:Ei; destruct (inxd l) eqn:El; cbn [andb].
  - apply Az_partial; [exact Hy | apply in_or_app; left; apply existsb_eqb; exact Ei | exact El].
  - apply (dpl_ext (fun _ => Az i y)); [intros t; cbv beta; symmetry; apply Az_flat; exact El | apply dpl_const].
  - apply (dpl_ext (fun _ => 0)); [intros t; reflexivity | apply dpl_const].
  - apply (dpl_ext (fun _ => 0)); [intros t; reflexivity | apply dpl_const].
Qed.

Lemma HK_T :
  forall y, inbox 52 nradk radk y -> forall i l, (i < 52)%nat -> (l < 52)%nat -> Rabs (DgT i l y) <= KT i l.
Proof.
  intros y Hy i l Hi Hl. unfold DgT, KT. destruct (inxd i) eqn:Ei; destruct (inxd l) eqn:El; cbn [andb].
  - apply Tz_bound; [exact Hy | apply in_or_app; left; apply existsb_eqb; exact Ei | exact El].
  - rewrite Rabs_R0. lra.
  - rewrite Rabs_R0. lra.
  - rewrite Rabs_R0. lra.
Qed.

Lemma Fz_taylor :
  forall z z', zball z -> zball z' ->
  Rabs (Fz z - Fz z' - msum (fun i => gT i (fun _ => 0) * (z i - z' i)) 52)
  <= msum (fun i => msum (fun l => KT i l * Rmax (Rabs (z l)) (Rabs (z' l))) 52 * Rabs (z i - z' i)) 52.
Proof.
  intros z z' Hz Hz'.
  assert (HT := taylor2 52 nradk radk Fz gT DgT KT HF_T Hg_T HK_T z z' (fun _ => 0)
                  (zball_inbox z Hz) (zball_inbox z' Hz') (zball_inbox _ zball_zero)
                  (fun j Hj => zball_high z Hz j Hj) (fun j Hj => zball_high z' Hz' j Hj)).
  eapply Rle_trans; [exact HT|]. cbv beta. apply Req_le. apply msum_ext. intros i _. f_equal.
  apply msum_ext. intros l _. rewrite !Rminus_0_r. reflexivity.
Qed.

(** The partials vary with z at most as K. *)
Definition KG (l : nat) : R := if inxd l then dyadR Kb else 0.
Definition DA (k l : nat) (z : nat -> R) : R := if inxd l then Tz k l z else 0.

Lemma Az_osc :
  forall k, In k (xdslots ++ eslots) -> forall z z', zball z -> zball z' ->
  Rabs (Az k z - Az k z') <= msum (fun l => KG l * Rabs (z l - z' l)) 52.
Proof.
  intros k Hk z z' Hz Hz'.
  apply (osc1 52 nradk radk (Az k) (DA k) KG); [| | exact (zball_inbox z Hz) | exact (zball_inbox z' Hz') |].
  - intros y Hy l Hl. unfold DA. destruct (inxd l) eqn:El.
    + apply Az_partial; assumption.
    + apply (dpl_ext (fun _ => Az k y)); [intros t; cbv beta; symmetry; apply Az_flat; exact El | apply dpl_const].
  - intros y Hy l Hl. unfold DA, KG. destruct (inxd l) eqn:El.
    + apply Tz_bound; assumption.
    + rewrite Rabs_R0. lra.
  - intros j Hj. rewrite (zball_high z Hz j Hj), (zball_high z' Hz' j Hj). reflexivity.
Qed.

(** The residual is affine in the e slots. *)
Definition Rv (z w : nat -> R) : R := xr (eget (tout r) (xextend (Ezw r kp s h z w) (tl r)) Xnan).

Lemma ab_real :
  forall z, inbox 52 nradk radk z -> forall k, (87 <= k < 87 + length (ab r))%nat ->
  exists y, eget k (xextend (Ez r kp s h z) (ab r)) Xnan = Xreal y.
Proof.
  intros z Hz k Hk.
  destruct (tail_facts r) as [_ [_ [_ [_ [Hwft _]]]]].
  destruct (ball_at z Hz) as [[_ [_ Htl]] _].
  rewrite <- (tail_low (ab r) (ttop r) (tout r) Hwft (Ez r kp s h z) k ltac:(lia)). apply Htl.
  rewrite length_app. lia.
Qed.

(** Where the output has degree zero in the e slots, moving them changes nothing. *)
Lemma Rv_flat :
  eget (tout r) (degs 87 ine (ab r)) 0%nat = 0%nat -> forall z w, inbox 52 nradk radk z -> Rv z w = Fz z.
Proof.
  intros H0 z w Hz.
  destruct (tail_facts r) as [Hwf [Hsg [Htop [Ho [Hwft Hin]]]]].
  destruct (ball_at z Hz) as [[_ [Hre _]] _].
  destruct (aff_sound 87 ine (Ez r kp s h z) Hre (ab r) Hwf Hsg (aff_ab r) (ab_real z Hz) (tout r) ltac:(lia))
    as [L [HL0 HL]].
  unfold Rv, Fz. rewrite !tl_split.
  rewrite (tail_low (ab r) (ttop r) (tout r) Hwft (Ezw r kp s h z w) (tout r)) by lia.
  rewrite (tail_low (ab r) (ttop r) (tout r) Hwft (Ez r kp s h z) (tout r)) by lia.
  rewrite (HL _ (fib_Ezw r kp s h z w)). cbn [xr]. rewrite (msum_zero_L 87 L _ (HL0 H0)). ring.
Qed.

Lemma Rv_affine :
  forall z w, inbox 52 nradk radk z -> Rv z w = Fz z + msum (fun j => if ine j then Az j z * w j else 0) 52.
Proof.
  intros z w Hz.
  destruct (tail_facts r) as [Hwf [Hsg [Htop [Ho [Hwft Hin]]]]].
  destruct (ball_at z Hz) as [HT _].
  assert (HT' := HT). destruct HT' as [Hun [Hre Htl]].
  destruct (aff_sound 87 ine (Ez r kp s h z) Hre (ab r) Hwf Hsg (aff_ab r) (ab_real z Hz) (tout r) ltac:(lia))
    as [L [_ HL]].
  (* the coefficient of slot j is the partial there *)
  assert (HLj : forall j, ine j = true -> L j = Az j z).
  { intros j Ej. assert (Hj := ine_range j Ej).
    assert (HD := adj_partial (ab r) (ttop r) (tout r) Hwf Hsg Htop Ho Hwft Hin (Ez r kp s h z) HT (j - 12) ltac:(lia)).
    replace (12 + (j - 12))%nat with j in HD by lia.
    assert (HD2 : derivable_pt_lim
              (fun t => xr (eget (tout r) (xextend (eset j (Ez r kp s h z) (Xreal t))
                                              (ab r ++ adj_binds 87 (ttop r) (tout r) (ab r) ks40)) Xnan))
              (xr (eget j (Ez r kp s h z) Xnan)) (L j)).
    { apply (dpl_ext (fun t => xr (eget (tout r) (xextend (Ez r kp s h z) (ab r)) Xnan)
                               + L j * (t - xr (eget j (Ez r kp s h z) Xnan)))); [| apply dpl_affine].
      intros t. rewrite (tail_low (ab r) (ttop r) (tout r) Hwft _ (tout r)) by lia.
      assert (Hf : fib 87 ine (Ez r kp s h z) (eset j (Ez r kp s h z) (Xreal t))).
      { split.
        - intros i Hi Hm. apply eget_eset_neq. intros ->. rewrite Ej in Hm. discriminate.
        - intros i Hi Hm. destruct (Nat.eq_dec i j) as [->|Hne].
          + rewrite eget_eset_eq. eexists. reflexivity.
          + rewrite eget_eset_neq by exact Hne. exact (Hre i Hi). }
      rewrite (HL _ Hf). cbn [xr]. f_equal.
      rewrite (msum_single _ 87 j) by (lia || (intros i Hi Hne; unfold dshift; destruct (ine i); [| ring];
                                         rewrite eget_eset_neq by exact Hne; ring)).
      unfold dshift. rewrite Ej, eget_eset_eq. reflexivity. }
    symmetry. exact (uniqueness_limite _ _ _ _ HD HD2). }
  unfold Rv, Fz. rewrite !tl_split.
  rewrite (tail_low (ab r) (ttop r) (tout r) Hwft (Ezw r kp s h z w) (tout r)) by lia.
  rewrite (tail_low (ab r) (ttop r) (tout r) Hwft (Ez r kp s h z) (tout r)) by lia.
  rewrite (HL _ (fib_Ezw r kp s h z w)). cbn [xr]. f_equal.
  change 87%nat with (52 + 35)%nat.
  rewrite msum_tail_zero.
  - apply msum_ext. intros j _. unfold dshift. destruct (ine j) eqn:Ej; [| ring].
    rewrite Ezw_get, Ej, (HLj j Ej). cbn [xr]. ring.
  - intros j Hj. unfold dshift. destruct (ine j) eqn:Ej; [| ring]. assert (H := ine_range j Ej). lia.
Qed.

(** The residual at (z, w) against (z', w'), less the partials at the exact jet applied to the steps. *)
Theorem row_expand :
  forall z z' w w', zball z -> zball z' ->
  Rabs (Rv z w - Rv z' w' - msum (fun i => gT i (fun _ => 0) * (z i - z' i)) 52
        - msum (fun j => (if ine j then Az j (fun _ => 0) else 0) * (w j - w' j)) 52)
  <= msum (fun i => msum (fun l => KT i l * Rmax (Rabs (z l)) (Rabs (z' l))) 52 * Rabs (z i - z' i)) 52
     + msum (fun j => (if ine j then msum (fun l => KG l * Rabs (z l)) 52 else 0) * Rabs (w j - w' j)) 52
     + msum (fun j => (if ine j then msum (fun l => KG l * Rabs (z l - z' l)) 52 else 0) * Rabs (w' j)) 52.
Proof.
  intros z z' w w' Hz Hz'.
  rewrite (Rv_affine z w (zball_inbox z Hz)), (Rv_affine z' w' (zball_inbox z' Hz')).
  assert (Hsum :
    msum (fun j => if ine j then Az j z * w j else 0) 52 - msum (fun j => if ine j then Az j z' * w' j else 0) 52
    - msum (fun j => (if ine j then Az j (fun _ => 0) else 0) * (w j - w' j)) 52
    = msum (fun j => if ine j then (Az j z - Az j (fun _ => 0)) * (w j - w' j) else 0) 52
      + msum (fun j => if ine j then (Az j z - Az j z') * w' j else 0) 52).
  { rewrite <- !msum_minus, <- msum_plus. apply msum_ext. intros j _. destruct (ine j); ring. }
  set (T := Fz z - Fz z' - msum (fun i => gT i (fun _ => 0) * (z i - z' i)) 52).
  set (E1 := msum (fun j => if ine j then (Az j z - Az j (fun _ => 0)) * (w j - w' j) else 0) 52).
  set (E2 := msum (fun j => if ine j then (Az j z - Az j z') * w' j else 0) 52).
  replace (Fz z + msum (fun j => if ine j then Az j z * w j else 0) 52
           - (Fz z' + msum (fun j => if ine j then Az j z' * w' j else 0) 52)
           - msum (fun i => gT i (fun _ => 0) * (z i - z' i)) 52
           - msum (fun j => (if ine j then Az j (fun _ => 0) else 0) * (w j - w' j)) 52)
    with (T + E1 + E2) by (unfold T, E1, E2; lra).
  eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [eapply Rle_trans; [apply Rabs_triang|]; apply Rplus_le_compat|].
  - exact (Fz_taylor z z' Hz Hz').
  - unfold E1. eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros j _. destruct (ine j) eqn:Ej.
    + rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos|].
      eapply Rle_trans; [apply (Az_osc j ltac:(apply in_or_app; right; apply existsb_eqb; exact Ej) z (fun _ => 0) Hz zball_zero)|].
      apply Req_le. apply msum_ext. intros l _. rewrite Rminus_0_r. reflexivity.
    + rewrite Rabs_R0, Rmult_0_l. lra.
  - unfold E2. eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros j _. destruct (ine j) eqn:Ej.
    + rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos|].
      exact (Az_osc j ltac:(apply in_or_app; right; apply existsb_eqb; exact Ej) z z' Hz Hz').
    + rewrite Rabs_R0, Rmult_0_l. lra.
Qed.

End Row.
