(** The collocated three-dimensional problem at level K, near the exact
    solution.

    The unknowns are perturbations X_j of the exact node values of the nine
    coefficients. At node j the jet of collocation point kp has its slots
    x, dm, dp moved by X_j and the slopes on either side ([zj]) and its
    slots e by the second difference ([wj]). The radial row is that jet's
    residual less the exact jet's residual at h = 0 ([GS]); the poloidal row
    reads the outer half point, with its source at s + h/2 ([GU]). The
    partials of a point's residual at the exact jet are CellTM's pval
    ([Az_pval]), so the linear part of the rows is Recur's rows with Lin3d's
    blocks ([lin_part_s], [lin_part_u]); the poloidal output reads neither
    the slots dm ([Az_dm_zero], Dep.v) nor e (Row3d.Rv_flat). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Newton TMEval LinCheck DerivSeq Adjoint AdjointSound
  CellTM QDiff Check3d Jet Mat Ball3d Taylor Ball3dSound Affine Row3d Dep Recur Step Level3d Lin3d.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Slots and sums                                                    *)

Definition upart (k : nat) : nat := if Nat.ltb k 32 then ((k - 12) / 5)%nat else ((k - 32) / 5)%nat.
Definition ucomp (k : nat) : nat := if Nat.ltb k 32 then ((k - 12) mod 5)%nat else ((k - 32) mod 5 + 4)%nat.

Definition dec_ok : bool :=
  forallb (fun pc => Nat.eqb (upart (uslot (fst pc) (snd pc))) (fst pc) && Nat.eqb (ucomp (uslot (fst pc) (snd pc))) (snd pc))
          (list_prod (seq 0 4) (seq 0 9)).

Lemma dec_ok_true : dec_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma udec : forall p c, (p < 4)%nat -> (c < 9)%nat -> upart (uslot p c) = p /\ ucomp (uslot p c) = c.
Proof.
  intros p c Hp Hc. assert (H := dec_ok_true). unfold dec_ok in H. rewrite forallb_forall in H.
  specialize (H (p, c) ltac:(apply in_prod; apply in_seq; lia)). cbn [fst snd] in H.
  destruct (andb_prop _ _ H) as [H1 H2]. split; apply Nat.eqb_eq; assumption.
Qed.

Lemma inxd_u : forall p c, (p < 3)%nat -> (c < 9)%nat -> inxd (uslot p c) = true.
Proof.
  intros p c Hp Hc. apply (inxd_pc (p, c)). unfold xdpc. apply in_prod; apply in_seq; lia.
Qed.

Lemma ine_u : forall c, (c < 9)%nat -> ine (uslot 3 c) = true.
Proof. intros c Hc. apply existsb_eqb. unfold eslots. apply in_map. apply in_seq. lia. Qed.

Fixpoint lsum (f : nat -> R) (L : list nat) : R := match L with [] => 0 | a :: L' => f a + lsum f L' end.

Lemma msum_filter :
  forall L f n, NoDup L -> (forall k, In k L -> (k < n)%nat) ->
  msum (fun i => if existsb (Nat.eqb i) L then f i else 0) n = lsum f L.
Proof.
  induction L as [|a L IH]; intros f n Hnd HL.
  - cbn [lsum existsb]. transitivity (msum (fun _ => 0) n); [apply msum_ext; intros; reflexivity | apply msum_zero].
  - inversion Hnd as [|? ? Hna HndL]; subst. cbn [lsum existsb].
    rewrite (msum_ext _ (fun i => (if Nat.eqb i a then f i else 0) + (if existsb (Nat.eqb i) L then f i else 0))).
    + rewrite msum_plus, (IH f n HndL (fun k Hk => HL k (or_intror Hk))).
      rewrite (msum_single _ n a (HL a (or_introl eq_refl))).
      * rewrite Nat.eqb_refl. reflexivity.
      * intros i Hi Hne. rewrite (proj2 (Nat.eqb_neq i a) Hne). reflexivity.
    + intros i Hi. destruct (Nat.eqb_spec i a) as [->|Hne]; cbn [orb].
      * destruct (existsb (Nat.eqb a) L) eqn:E; [exfalso; apply Hna; apply existsb_eqb; exact E | ring].
      * destruct (existsb (Nat.eqb i) L); ring.
Qed.

Lemma lsum_le : forall L f g, (forall k, In k L -> f k <= g k) -> lsum f L <= lsum g L.
Proof.
  induction L as [|a L IH]; intros f g H; cbn [lsum]; [lra|].
  apply Rplus_le_compat; [apply H; left; reflexivity | apply IH; intros k Hk; apply H; right; exact Hk].
Qed.

Lemma lsum_const : forall L c, lsum (fun _ => c) L = INR (length L) * c.
Proof. induction L as [|a L IH]; intros c; cbn [lsum length]; [rewrite Rmult_0_l; reflexivity|]. rewrite IH, S_INR. ring. Qed.

Lemma xdslots_eq :
  xdslots = [12; 13; 14; 15; 16; 33; 34; 35; 36; 17; 18; 19; 20; 21; 38; 39; 40; 41;
             22; 23; 24; 25; 26; 43; 44; 45; 46]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma eslots_eq : eslots = [27; 28; 29; 30; 31; 48; 49; 50; 51]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma xd_lt : forall k, In k xdslots -> (k < 52)%nat.
Proof. intros k Hk. apply existsb_eqb in Hk. exact (proj2 (proj1 (inxd_range k Hk))). Qed.

Lemma e_lt : forall k, In k eslots -> (k < 52)%nat.
Proof. intros k Hk. apply existsb_eqb in Hk. exact (proj2 (ine_range k Hk)). Qed.

(** Sums over the slots of the 27 moved unknowns, and of the nine e slots. *)
Lemma sum_xd :
  forall f, msum (fun i => if inxd i then f i else 0) 52 = msum (fun c => f (uslot 0 c) + f (uslot 1 c) + f (uslot 2 c)) 9.
Proof.
  intros f. unfold inxd. rewrite (msum_filter xdslots f 52 NoDup_xdslots xd_lt).
  rewrite xdslots_eq. cbn [lsum msum uslot Nat.ltb Nat.leb Nat.add Nat.mul Nat.sub]. ring.
Qed.

Lemma sum_e : forall f, msum (fun i => if ine i then f i else 0) 52 = msum (fun c => f (uslot 3 c)) 9.
Proof.
  intros f. unfold ine. rewrite (msum_filter eslots f 52 NoDup_eslots e_lt).
  rewrite eslots_eq. cbn [lsum msum uslot Nat.ltb Nat.leb Nat.add Nat.mul Nat.sub]. ring.
Qed.

Lemma sum_xd_le :
  forall f c, (forall i, inxd i = true -> f i <= c) -> msum (fun i => if inxd i then f i else 0) 52 <= 27 * c.
Proof.
  intros f c H. unfold inxd. rewrite (msum_filter xdslots f 52 NoDup_xdslots xd_lt).
  eapply Rle_trans; [apply (lsum_le xdslots f (fun _ => c)); intros k Hk; apply H; apply existsb_eqb; exact Hk|].
  rewrite lsum_const. rewrite xdslots_eq. cbn [length INR]. lra.
Qed.

Lemma sum_e_le :
  forall f c, (forall i, ine i = true -> f i <= c) -> msum (fun i => if ine i then f i else 0) 52 <= 9 * c.
Proof.
  intros f c H. unfold ine. rewrite (msum_filter eslots f 52 NoDup_eslots e_lt).
  eapply Rle_trans; [apply (lsum_le eslots f (fun _ => c)); intros k Hk; apply H; apply existsb_eqb; exact Hk|].
  rewrite lsum_const. rewrite eslots_eq. cbn [length INR]. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The node data and the rows                                        *)

Section Node.

Variable h : R.
Variable X : nat -> vec.

(** The jet's x, dm, dp slots moved by the node value and the two slopes. *)
Definition zj (j : nat) : nat -> R := fun k =>
  if inxd k then
    (if Nat.eqb (upart k) 0 then X j (ucomp k)
     else if Nat.eqb (upart k) 1 then slope h X j (ucomp k) else slope h X (S j) (ucomp k))
  else 0.

(** The jet's e slots moved by the second difference. *)
Definition wj (j : nat) : nat -> R := fun k =>
  if ine k then (slope h X (S j) (ucomp k) - slope h X j (ucomp k)) / h else 0.

Lemma zj_x : forall j c, (c < 9)%nat -> zj j (uslot 0 c) = X j c.
Proof.
  intros j c Hc. unfold zj. rewrite (inxd_u 0 c ltac:(lia) Hc).
  destruct (udec 0 c ltac:(lia) Hc) as [-> ->]. reflexivity.
Qed.

Lemma zj_dm : forall j c, (c < 9)%nat -> zj j (uslot 1 c) = slope h X j c.
Proof.
  intros j c Hc. unfold zj. rewrite (inxd_u 1 c ltac:(lia) Hc).
  destruct (udec 1 c ltac:(lia) Hc) as [-> ->]. reflexivity.
Qed.

Lemma zj_dp : forall j c, (c < 9)%nat -> zj j (uslot 2 c) = slope h X (S j) c.
Proof.
  intros j c Hc. unfold zj. rewrite (inxd_u 2 c ltac:(lia) Hc).
  destruct (udec 2 c ltac:(lia) Hc) as [-> ->]. reflexivity.
Qed.

Lemma wj_e : forall j c, (c < 9)%nat -> wj j (uslot 3 c) = (slope h X (S j) c - slope h X j c) / h.
Proof.
  intros j c Hc. unfold wj. rewrite (ine_u c Hc). destruct (udec 3 c ltac:(lia) Hc) as [_ ->]. reflexivity.
Qed.

Lemma zj_out : forall j k, inxd k = false -> zj j k = 0.
Proof. intros j k Hk. unfold zj. rewrite Hk. reflexivity. Qed.

End Node.

Definition sK (K j : nat) : R := INR j * hK K.

(** The rows of the collocated problem at node j, as functions of the
    perturbation X of the exact node values. *)
Definition GS (K : nat) (X : nat -> vec) (j kp : nat) : R :=
  Rv true kp (sK K j) (hK K) (zj (hK K) X j) (wj (hK K) X j) - Fz true kp (sK K j) 0 (fun _ => 0).

Definition GU (K : nat) (X : nat -> vec) (j kp : nat) : R :=
  Rv false kp (sK K j) (hK K) (zj (hK K) X j) (wj (hK K) X j) - Fz false kp (sK K j + hK K / 2) 0 (fun _ => 0).

(* ---------------------------------------------------------------- *)
(* The partials at the exact jet                                     *)

Lemma xr_xreal : forall x, xr x = xreal x.
Proof. intros [|x]; reflexivity. Qed.

(** Unfolded to the same terms on both sides first, so that no tactic
    compares the flattened lists by evaluation. *)
Lemma tail_tl_r : tail_r = tl true.
Proof. unfold tail_r, tl, ab, ttop, tout, top_r, out_r, anfs. cbv beta iota. reflexivity. Qed.

Lemma tail_tl_p : tail_p = tl false.
Proof. unfold tail_p, tl, ab, ttop, tout, top_p, out_p, anfs. cbv beta iota. reflexivity. Qed.

Lemma tail_tl : forall r : bool, (if r then tail_r else tail_p) = tl r.
Proof. intros [|]; [exact tail_tl_r | exact tail_tl_p]. Qed.

Lemma aslot_eq : forall r p c, aslot_in r p c = in_slot 87 (ttop r) (tout r) (uslot p c - 12).
Proof.
  intros [|] p c; unfold aslot_in, ttop, tout, top_r, out_r, top_p, out_p, anfs; cbv beta iota; reflexivity.
Qed.

Lemma Az_pval :
  forall prec r kp c Kb rx rd hhi, ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  forall p cc, (p < 4)%nat -> (cc < 9)%nat -> Az r kp s h (uslot p cc) (fun _ => 0) = pval r kp p cc s h.
Proof.
  intros prec r kp c Kb rx rd hhi Hok s h Hs Hh p cc Hp Hcc.
  assert (HJ := jet_real prec r kp c rx rd hhi Kb Hok s h Hs Hh).
  assert (Hag : forall k, eget k (Ez r kp s h (fun _ => 0)) Xnan = eget k (Ex r kp s h) Xnan).
  { intros k. rewrite Ez_get. destruct (inxd k) eqn:Ek; [| reflexivity].
    destruct (inxd_range k Ek) as [Hk _]. destruct (HJ k ltac:(lia)) as [x Hx]. rewrite Hx. cbn [xr].
    f_equal. ring. }
  unfold Az. rewrite (env_agree (tl r) _ _ Hag). unfold Ex.
  unfold pval, plist, alist. rewrite xextend_app.
  rewrite tail_tl, aslot_eq. apply xr_xreal.
Qed.

(** The poloidal output does not read the slots dm. *)
Definition dmslots : list nat := map (uslot 1) (seq 0 9).
Definition indm (k : nat) : bool := existsb (Nat.eqb k) dmslots.

Definition dep_of (a : list binding * env nat * nat) : bool :=
  eget (rget (snd (fst a)) rtop3) (deps 87 indm (fst (fst a))) false.

Lemma dep_of_p : dep_of (anfs false) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma dep_of_eq : forall r, dep_of (anfs r) = eget (tout r) (deps 87 indm (ab r)) false.
Proof. intros r. reflexivity. Qed.

Lemma dep_p : eget (tout false) (deps 87 indm (ab false)) false = false.
Proof. rewrite <- (dep_of_eq false). exact dep_of_p. Qed.

Lemma dm_facts : forallb inxd dmslots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dm_xd : forall k, indm k = true -> inxd k = true.
Proof.
  intros k Hk. apply existsb_eqb in Hk. assert (H := dm_facts). rewrite forallb_forall in H. exact (H k Hk).
Qed.

Lemma indm_u : forall c, (c < 9)%nat -> indm (uslot 1 c) = true.
Proof. intros c Hc. apply existsb_eqb. unfold dmslots. apply in_map. apply in_seq. lia. Qed.

(** Stated for any row type whose output is free of the slots dm, so that
    no step compares the concrete flattened lists. *)
Lemma Fz_dep_flat :
  forall r kp s h z i t, eget (tout r) (deps 87 indm (ab r)) false = false -> indm i = true ->
  Fz r kp s h (upd z i t) = Fz r kp s h z.
Proof.
  intros r kp s h z i t Hdep Hi.
  destruct (tail_facts r) as [Hwf [_ [Htop [Ho [Hwft _]]]]].
  unfold Fz. rewrite !tl_split.
  rewrite (tail_low (ab r) (ttop r) (tout r) Hwft (Ez r kp s h (upd z i t)) (tout r)) by lia.
  rewrite (tail_low (ab r) (ttop r) (tout r) Hwft (Ez r kp s h z) (tout r)) by lia.
  apply (f_equal xr). apply (dep_sound 87 indm (ab r) (Ez r kp s h z) (Ez r kp s h (upd z i t)) Hwf).
  - intros j Hj Hm. rewrite (Ez_upd_in r kp s h z i t (dm_xd i Hi) j). apply eget_eset_neq.
    intros ->. rewrite Hi in Hm. discriminate.
  - lia.
  - exact Hdep.
Qed.

Lemma Az_dep_zero :
  forall prec r kp c Kb rx rd hhi, ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true ->
  eget (tout r) (deps 87 indm (ab r)) false = false ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  forall y, inbox 52 (nradk rx rd) (radk rx rd) y -> forall i, indm i = true -> Az r kp s h i y = 0.
Proof.
  intros prec r kp c Kb rx rd hhi Hok Hdep s h Hs Hh y Hy i Hi.
  assert (HD := Fz_partial prec r kp c Kb rx rd hhi Hok s h Hs Hh y Hy i (dm_xd i Hi)).
  assert (HC : derivable_pt_lim (fun t => Fz r kp s h (upd y i t)) (y i) 0).
  { apply (dpl_ext (fun _ => Fz r kp s h y)); [intros t; cbv beta; symmetry; apply Fz_dep_flat; assumption | apply dpl_const]. }
  exact (uniqueness_limite _ _ _ _ HD HC).
Qed.

Lemma Az_dm_zero :
  forall prec kp c Kb rx rd hhi, ball_cell_ok prec Kb rx rd hhi false (dtails false) kp c = true ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  forall y, inbox 52 (nradk rx rd) (radk rx rd) y -> forall i, indm i = true -> Az false kp s h i y = 0.
Proof.
  intros prec kp c Kb rx rd hhi Hok. exact (Az_dep_zero prec false kp c Kb rx rd hhi Hok dep_p).
Qed.

(* ---------------------------------------------------------------- *)
(* The linear part of the rows                                       *)

Lemma gT_mul :
  forall r kp s h i z (f : R), gT r kp s h i z * f = if inxd i then Az r kp s h i z * f else 0.
Proof. intros. unfold gT. destruct (inxd i); ring. Qed.

Lemma ife_mul : forall (b : bool) (a f : R), (if b then a else 0) * f = if b then a * f else 0.
Proof. intros [|] a f; ring. Qed.

(** The radial row's linear part, from the partials of the exact jet. *)
Lemma lin_sum_s :
  forall (A : nat -> nat -> R) (X : nat -> vec) h j, h <> 0 ->
  msum (fun c => A 0%nat c * X j c + A 1%nat c * slope h X j c + A 2%nat c * slope h X (S j) c) 9
  + msum (fun c => A 3%nat c * ((slope h X (S j) c - slope h X j c) / h)) 9
  = (msum (fun c => (A 3%nat c + h * A 2%nat c) * slope h X (S j) c) 9
     - msum (fun c => (A 3%nat c - h * A 1%nat c) * slope h X j c) 9) / h
    + msum (fun c => A 0%nat c * X j c) 9.
Proof.
  intros A X h j Hh. rewrite <- msum_minus. unfold Rdiv. rewrite <- msum_scal_r, <- !msum_plus.
  apply msum_ext. intros c Hc. field. exact Hh.
Qed.

(** The poloidal row's, with no partial in the slots dm. *)
Lemma lin_sum_u :
  forall (A : nat -> nat -> R) (X : nat -> vec) h j, (forall c, (c < 9)%nat -> A 1%nat c = 0) ->
  msum (fun c => A 0%nat c * X j c + A 1%nat c * slope h X j c + A 2%nat c * slope h X (S j) c) 9
  = msum (fun c => A 2%nat c * slope h X (S j) c) 9 + msum (fun c => A 0%nat c * X j c) 9.
Proof.
  intros A X h j H1. rewrite <- msum_plus. apply msum_ext. intros c Hc. rewrite (H1 c Hc). ring.
Qed.

Lemma lin_part_s :
  forall K kp (X : nat -> vec) j,
  (forall p c, (p < 4)%nat -> (c < 9)%nat ->
     Az true kp (sK K j) (hK K) (uslot p c) (fun _ => 0) = pval true kp p c (sK K j) (hK K)) ->
  msum (fun i => gT true kp (sK K j) (hK K) i (fun _ => 0) * zj (hK K) X j i) 52
  + msum (fun e => (if ine e then Az true kp (sK K j) (hK K) e (fun _ => 0) else 0) * wj (hK K) X j e) 52
  = rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j kp.
Proof.
  intros K kp X j HA. assert (Hh := hK_pos K).
  rewrite (msum_ext _ (fun i => if inxd i then Az true kp (sK K j) (hK K) i (fun _ => 0) * zj (hK K) X j i else 0))
    by (intros i _; apply gT_mul).
  rewrite (msum_ext (fun e => (if ine e then Az true kp (sK K j) (hK K) e (fun _ => 0) else 0) * wj (hK K) X j e)
             (fun e => if ine e then Az true kp (sK K j) (hK K) e (fun _ => 0) * wj (hK K) X j e else 0))
    by (intros e _; apply ife_mul).
  rewrite sum_xd, sum_e.
  rewrite (msum_ext _ (fun c => pval true kp 0 c (sK K j) (hK K) * X j c
                                + pval true kp 1 c (sK K j) (hK K) * slope (hK K) X j c
                                + pval true kp 2 c (sK K j) (hK K) * slope (hK K) X (S j) c)).
  2: { intros c Hc. rewrite zj_x, zj_dm, zj_dp by exact Hc. rewrite !HA by lia. reflexivity. }
  rewrite (msum_ext (fun c => Az true kp (sK K j) (hK K) (uslot 3 c) (fun _ => 0) * wj (hK K) X j (uslot 3 c))
             (fun c => pval true kp 3 c (sK K j) (hK K) * ((slope (hK K) X (S j) c - slope (hK K) X j c) / hK K))).
  2: { intros c Hc. rewrite wj_e by exact Hc. rewrite HA by lia. reflexivity. }
  rewrite (lin_sum_s (fun p c => pval true kp p c (sK K j) (hK K)) X (hK K) j ltac:(lra)).
  unfold rs_row, mv, Pp3, Pm3, Sx3, bPp, bPm, bSx, sK. cbv beta. reflexivity.
Qed.

Lemma lin_part_u :
  forall K kp (X : nat -> vec) j,
  (forall p c, (p < 4)%nat -> (c < 9)%nat ->
     Az false kp (sK K j) (hK K) (uslot p c) (fun _ => 0) = pval false kp p c (sK K j) (hK K)) ->
  (forall c, (c < 9)%nat -> pval false kp 1 c (sK K j) (hK K) = 0) ->
  msum (fun i => gT false kp (sK K j) (hK K) i (fun _ => 0) * zj (hK K) X j i) 52
  = ru_row (hK K) (Up3 K) (V3 K) X j kp.
Proof.
  intros K kp X j HA H1.
  rewrite (msum_ext _ (fun i => if inxd i then Az false kp (sK K j) (hK K) i (fun _ => 0) * zj (hK K) X j i else 0))
    by (intros i _; apply gT_mul).
  rewrite sum_xd.
  rewrite (msum_ext _ (fun c => pval false kp 0 c (sK K j) (hK K) * X j c
                                + pval false kp 1 c (sK K j) (hK K) * slope (hK K) X j c
                                + pval false kp 2 c (sK K j) (hK K) * slope (hK K) X (S j) c)).
  2: { intros c Hc. rewrite zj_x, zj_dm, zj_dp by exact Hc. rewrite !HA by lia. reflexivity. }
  rewrite (lin_sum_u (fun p c => pval false kp p c (sK K j) (hK K)) X (hK K) j H1).
  unfold ru_row, mv, Up3, V3, bUp, bV, sK. cbv beta. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* The node data: linearity and bounds                               *)

Lemma xd_dec_facts : forallb (fun k => Nat.ltb (upart k) 3 && Nat.ltb (ucomp k) 9) xdslots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma e_dec_facts : forallb (fun k => Nat.ltb (ucomp k) 9) eslots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xd_dec : forall k, inxd k = true -> (upart k < 3)%nat /\ (ucomp k < 9)%nat.
Proof.
  intros k Hk. apply existsb_eqb in Hk. assert (H := xd_dec_facts). rewrite forallb_forall in H.
  specialize (H k Hk). destruct (andb_prop _ _ H) as [H1 H2]. apply Nat.ltb_lt in H1, H2. split; assumption.
Qed.

Lemma e_dec : forall k, ine k = true -> (ucomp k < 9)%nat.
Proof.
  intros k Hk. apply existsb_eqb in Hk. assert (H := e_dec_facts). rewrite forallb_forall in H.
  apply Nat.ltb_lt. exact (H k Hk).
Qed.

Definition vdiff (X X' : nat -> vec) : nat -> vec := fun j c => X j c - X' j c.

Lemma zj_sub : forall h X X' j k, zj h X j k - zj h X' j k = zj h (vdiff X X') j k.
Proof.
  intros h X X' j k. unfold zj, vdiff, slope. destruct (inxd k); [| ring].
  destruct (Nat.eqb (upart k) 0); [ring|]. destruct (Nat.eqb (upart k) 1); unfold Rdiv; ring.
Qed.

Lemma wj_sub : forall h X X' j e, wj h X j e - wj h X' j e = wj h (vdiff X X') j e.
Proof. intros h X X' j e. unfold wj, vdiff, slope. destruct (ine e); unfold Rdiv; ring. Qed.

Lemma zj_bound :
  forall h X j k, inxd k = true ->
  Rabs (zj h X j k) <= Rmax (vnorm 9 (X j)) (Rmax (vnorm 9 (slope h X j)) (vnorm 9 (slope h X (S j)))).
Proof.
  intros h X j k Hk. destruct (xd_dec k Hk) as [Hp Hc]. unfold zj. rewrite Hk.
  destruct (Nat.eqb (upart k) 0).
  - eapply Rle_trans; [apply (vnorm_ge 9 (X j) _ Hc) | apply Rmax_l].
  - eapply Rle_trans; [| apply Rmax_r]. destruct (Nat.eqb (upart k) 1).
    + eapply Rle_trans; [apply (vnorm_ge 9 (slope h X j) _ Hc) | apply Rmax_l].
    + eapply Rle_trans; [apply (vnorm_ge 9 (slope h X (S j)) _ Hc) | apply Rmax_r].
Qed.

Lemma wj_bound :
  forall h X j e, 0 < h -> ine e = true ->
  Rabs (wj h X j e) <= (vnorm 9 (slope h X (S j)) + vnorm 9 (slope h X j)) / h.
Proof.
  intros h X j e Hh He. assert (Hc := e_dec e He). unfold wj. rewrite He.
  unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ h)) by (left; apply Rinv_0_lt_compat; exact Hh).
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hh|].
  unfold Rminus. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp.
  apply Rplus_le_compat; apply vnorm_ge; exact Hc.
Qed.

(* ---------------------------------------------------------------- *)
(* Crude bounds on what a row moves away from its linear part         *)

Lemma sum_xd_bound :
  forall f c, (forall i, inxd i = false -> f i = 0) -> (forall i, inxd i = true -> f i <= c) -> msum f 52 <= 27 * c.
Proof.
  intros f c H0 H1. rewrite (msum_ext f (fun i => if inxd i then f i else 0)).
  - apply sum_xd_le. exact H1.
  - intros i _. destruct (inxd i) eqn:E; [reflexivity | apply H0; exact E].
Qed.

Lemma sum_e_bound :
  forall f c, (forall i, ine i = false -> f i = 0) -> (forall i, ine i = true -> f i <= c) -> msum f 52 <= 9 * c.
Proof.
  intros f c H0 H1. rewrite (msum_ext f (fun i => if ine i then f i else 0)).
  - apply sum_e_le. exact H1.
  - intros i _. destruct (ine i) eqn:E; [reflexivity | apply H0; exact E].
Qed.

Lemma KG_sum :
  forall Kb (g : nat -> R) c, 0 <= dyadR Kb -> (forall l, inxd l = true -> 0 <= g l <= c) ->
  0 <= msum (fun l => KG Kb l * g l) 52 <= 27 * (dyadR Kb * c).
Proof.
  intros Kb g c HK Hg. split.
  - apply msum_nonneg. intros l _. unfold KG. destruct (inxd l) eqn:El; [| lra].
    apply Rmult_le_pos; [exact HK | apply Hg; exact El].
  - apply sum_xd_bound.
    + intros l Hl. unfold KG. rewrite Hl. ring.
    + intros l Hl. unfold KG. rewrite Hl. apply Rmult_le_compat_l; [exact HK | apply Hg; exact Hl].
Qed.

Lemma rhs1_crude :
  forall Kb (z z' : nat -> R) Z DZ, 0 <= dyadR Kb -> 0 <= Z -> 0 <= DZ ->
  (forall k, inxd k = true -> Rabs (z k) <= Z /\ Rabs (z' k) <= Z /\ Rabs (z k - z' k) <= DZ) ->
  msum (fun i => msum (fun l => KT Kb i l * Rmax (Rabs (z l)) (Rabs (z' l))) 52 * Rabs (z i - z' i)) 52
  <= dyadR Kb * (729 * Z * DZ).
Proof.
  intros Kb z z' Z DZ HK HZ HDZ Hz.
  replace (dyadR Kb * (729 * Z * DZ)) with (27 * (27 * (dyadR Kb * Z) * DZ)) by ring.
  apply sum_xd_bound.
  - intros i Hi. rewrite (msum_ext _ (fun _ => 0)) by (intros l _; unfold KT; rewrite Hi; cbn [andb]; ring).
    rewrite msum_zero. ring.
  - intros i Hi. destruct (Hz i Hi) as [_ [_ Hd]].
    assert (Hin : 0 <= msum (fun l => KT Kb i l * Rmax (Rabs (z l)) (Rabs (z' l))) 52 <= 27 * (dyadR Kb * Z)).
    { rewrite (msum_ext _ (fun l => KG Kb l * Rmax (Rabs (z l)) (Rabs (z' l))))
        by (intros l _; unfold KT, KG; rewrite Hi; reflexivity).
      apply KG_sum; [exact HK|]. intros l Hl. destruct (Hz l Hl) as [A1 [A2 _]].
      split; [eapply Rle_trans; [apply Rabs_pos | apply Rmax_l] | apply Rmax_lub; assumption]. }
    apply Rmult_le_compat; [apply Hin | apply Rabs_pos | apply Hin | exact Hd].
Qed.

Lemma rhs_crude :
  forall Kb (z z' w w' : nat -> R) Z DZ W DW,
  0 <= dyadR Kb -> 0 <= Z -> 0 <= DZ -> 0 <= W -> 0 <= DW ->
  (forall k, inxd k = true -> Rabs (z k) <= Z /\ Rabs (z' k) <= Z /\ Rabs (z k - z' k) <= DZ) ->
  (forall e, ine e = true -> Rabs (w' e) <= W /\ Rabs (w e - w' e) <= DW) ->
  msum (fun i => msum (fun l => KT Kb i l * Rmax (Rabs (z l)) (Rabs (z' l))) 52 * Rabs (z i - z' i)) 52
  + msum (fun j => (if ine j then msum (fun l => KG Kb l * Rabs (z l)) 52 else 0) * Rabs (w j - w' j)) 52
  + msum (fun j => (if ine j then msum (fun l => KG Kb l * Rabs (z l - z' l)) 52 else 0) * Rabs (w' j)) 52
  <= dyadR Kb * (729 * Z * DZ + 243 * Z * DW + 243 * DZ * W).
Proof.
  intros Kb z z' w w' Z DZ W DW HK HZ HDZ HW HDW Hz Hw.
  assert (S1 := rhs1_crude Kb z z' Z DZ HK HZ HDZ Hz).
  assert (S2 : msum (fun j => (if ine j then msum (fun l => KG Kb l * Rabs (z l)) 52 else 0) * Rabs (w j - w' j)) 52
               <= 9 * (27 * (dyadR Kb * Z) * DW)).
  { apply sum_e_bound.
    - intros j Hj. rewrite Hj. ring.
    - intros j Hj. rewrite Hj. destruct (Hw j Hj) as [_ Hd].
      assert (Hin := KG_sum Kb (fun l => Rabs (z l)) Z HK (fun l Hl => conj (Rabs_pos _) (proj1 (Hz l Hl)))).
      apply Rmult_le_compat; [apply Hin | apply Rabs_pos | apply Hin | exact Hd]. }
  assert (S3 : msum (fun j => (if ine j then msum (fun l => KG Kb l * Rabs (z l - z' l)) 52 else 0) * Rabs (w' j)) 52
               <= 9 * (27 * (dyadR Kb * DZ) * W)).
  { apply sum_e_bound.
    - intros j Hj. rewrite Hj. ring.
    - intros j Hj. rewrite Hj. destruct (Hw j Hj) as [Hw' _].
      assert (Hin := KG_sum Kb (fun l => Rabs (z l - z' l)) DZ HK
                       (fun l Hl => conj (Rabs_pos _) (proj2 (proj2 (Hz l Hl))))).
      apply Rmult_le_compat; [apply Hin | apply Rabs_pos | apply Hin | exact Hw']. }
  lra.
Qed.

Lemma msum_mul_minus :
  forall (g x y : nat -> R) n, msum (fun i => g i * (x i - y i)) n = msum (fun i => g i * x i) n - msum (fun i => g i * y i) n.
Proof. intros g x y n. rewrite <- msum_minus. apply msum_ext. intros i _. ring. Qed.

(** The algebra behind the crude bounds, over opaque reals. *)
Lemma crude_alg :
  forall R1 R2 F0 G1 G2 A1 A2 Gd Ad B : R, Gd = G1 - G2 -> Ad = A1 - A2 ->
  Rabs (R1 - R2 - Gd - Ad) <= B -> Rabs (R1 - F0 - (R2 - F0) - (G1 + A1 - (G2 + A2))) <= B.
Proof.
  intros R1 R2 F0 G1 G2 A1 A2 Gd Ad B -> -> H.
  replace (R1 - F0 - (R2 - F0) - (G1 + A1 - (G2 + A2))) with (R1 - R2 - (G1 - G2) - (A1 - A2)) by ring. exact H.
Qed.

Lemma crude_alg_u :
  forall R1 R2 F1 F2 F0 G1 G2 Gd B : R, R1 = F1 -> R2 = F2 -> Gd = G1 - G2 ->
  Rabs (F1 - F2 - Gd) <= B -> Rabs (R1 - F0 - (R2 - F0) - (G1 - G2)) <= B.
Proof.
  intros R1 R2 F1 F2 F0 G1 G2 Gd B -> -> -> H.
  replace (F1 - F0 - (F2 - F0) - (G1 - G2)) with (F1 - F2 - (G1 - G2)) by ring. exact H.
Qed.

(** A radial row less its linear part, between two perturbations. *)
Lemma rows_s_crude :
  forall prec Kb rx rd hhi K kp c j (X X' : nat -> vec) Z DZ W DW,
  ball_cell_ok prec Kb rx rd hhi true (dtails true) kp c = true ->
  0 <= dyadR Kb -> 0 <= dyadR rx -> 0 <= dyadR rd ->
  dyadR (clo c) <= sK K j <= dyadR (chi c) -> 0 <= hK K <= dyadR hhi ->
  zball rx rd (zj (hK K) X j) -> zball rx rd (zj (hK K) X' j) ->
  0 <= Z -> 0 <= DZ -> 0 <= W -> 0 <= DW ->
  (forall k, inxd k = true -> Rabs (zj (hK K) X j k) <= Z /\ Rabs (zj (hK K) X' j k) <= Z /\
                             Rabs (zj (hK K) X j k - zj (hK K) X' j k) <= DZ) ->
  (forall e, ine e = true -> Rabs (wj (hK K) X' j e) <= W /\ Rabs (wj (hK K) X j e - wj (hK K) X' j e) <= DW) ->
  Rabs (GS K X j kp - GS K X' j kp
        - (rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j kp - rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X' j kp))
  <= dyadR Kb * (729 * Z * DZ + 243 * Z * DW + 243 * DZ * W).
Proof.
  intros prec Kb rx rd hhi K kp c j X X' Z DZ W DW Hok HK Hrx Hrd Hs Hh Hz Hz' HZ HDZ HW HDW Hb Hw.
  assert (HA : forall p cc, (p < 4)%nat -> (cc < 9)%nat ->
                 Az true kp (sK K j) (hK K) (uslot p cc) (fun _ => 0) = pval true kp p cc (sK K j) (hK K))
    by (intros p cc Hp Hcc; exact (Az_pval prec true kp c Kb rx rd hhi Hok (sK K j) (hK K) Hs Hh p cc Hp Hcc)).
  rewrite <- (lin_part_s K kp X j HA), <- (lin_part_s K kp X' j HA).
  assert (HE := row_expand prec true kp c Kb rx rd hhi Hok Hrx Hrd (sK K j) (hK K) Hs Hh
                  (zj (hK K) X j) (zj (hK K) X' j) (wj (hK K) X j) (wj (hK K) X' j) Hz Hz').
  assert (HC := rhs_crude Kb (zj (hK K) X j) (zj (hK K) X' j) (wj (hK K) X j) (wj (hK K) X' j) Z DZ W DW
                  HK HZ HDZ HW HDW Hb Hw).
  unfold GS.
  apply (crude_alg _ _ _ _ _ _ _ _ _ _ (msum_mul_minus _ _ _ 52) (msum_mul_minus _ _ _ 52)).
  eapply Rle_trans; [exact HE | exact HC].
Qed.

(** A poloidal row less its linear part: no e slots, no dm slots. *)
Lemma rows_u_crude :
  forall prec Kb rx rd hhi K kp c j (X X' : nat -> vec) Z DZ,
  ball_cell_ok prec Kb rx rd hhi false (dtails false) kp c = true ->
  0 <= dyadR Kb -> 0 <= dyadR rx -> 0 <= dyadR rd ->
  dyadR (clo c) <= sK K j <= dyadR (chi c) -> 0 <= hK K <= dyadR hhi ->
  zball rx rd (zj (hK K) X j) -> zball rx rd (zj (hK K) X' j) ->
  0 <= Z -> 0 <= DZ ->
  (forall k, inxd k = true -> Rabs (zj (hK K) X j k) <= Z /\ Rabs (zj (hK K) X' j k) <= Z /\
                             Rabs (zj (hK K) X j k - zj (hK K) X' j k) <= DZ) ->
  Rabs (GU K X j kp - GU K X' j kp
        - (ru_row (hK K) (Up3 K) (V3 K) X j kp - ru_row (hK K) (Up3 K) (V3 K) X' j kp))
  <= dyadR Kb * (729 * Z * DZ).
Proof.
  intros prec Kb rx rd hhi K kp c j X X' Z DZ Hok HK Hrx Hrd Hs Hh Hz Hz' HZ HDZ Hb.
  assert (HA : forall p cc, (p < 4)%nat -> (cc < 9)%nat ->
                 Az false kp (sK K j) (hK K) (uslot p cc) (fun _ => 0) = pval false kp p cc (sK K j) (hK K))
    by (intros p cc Hp Hcc; exact (Az_pval prec false kp c Kb rx rd hhi Hok (sK K j) (hK K) Hs Hh p cc Hp Hcc)).
  assert (H1 : forall cc, (cc < 9)%nat -> pval false kp 1 cc (sK K j) (hK K) = 0).
  { intros cc Hcc. rewrite <- (HA 1%nat cc ltac:(lia) Hcc).
    exact (Az_dm_zero prec kp c Kb rx rd hhi Hok (sK K j) (hK K) Hs Hh (fun _ => 0)
             (zball_inbox rx rd _ (zball_zero rx rd Hrx Hrd)) (uslot 1 cc) (indm_u cc Hcc)). }
  rewrite <- (lin_part_u K kp X j HA H1), <- (lin_part_u K kp X' j HA H1).
  assert (HT := Fz_taylor prec false kp c Kb rx rd hhi Hok Hrx Hrd (sK K j) (hK K) Hs Hh
                  (zj (hK K) X j) (zj (hK K) X' j) Hz Hz').
  assert (HC := rhs1_crude Kb (zj (hK K) X j) (zj (hK K) X' j) Z DZ HK HZ HDZ Hb).
  unfold GU.
  apply (crude_alg_u _ _ _ _ _ _ _ _ _
           (Rv_flat prec false kp c Kb rx rd hhi Hok (sK K j) (hK K) Hs Hh deg_p
              (zj (hK K) X j) (wj (hK K) X j) (zball_inbox rx rd _ Hz))
           (Rv_flat prec false kp c Kb rx rd hhi Hok (sK K j) (hK K) Hs Hh deg_p
              (zj (hK K) X' j) (wj (hK K) X' j) (zball_inbox rx rd _ Hz'))
           (msum_mul_minus _ _ _ 52)).
  eapply Rle_trans; [exact HT | exact HC].
Qed.
