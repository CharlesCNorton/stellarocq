(** Multiple shooting with an inhomogeneous start condition.

    CFMS.v's system with the start rows Cs z_{cut 0} = g in place of zero:
    the right-hand side carries g in its first five rows ([rhsg]), a run
    with that start and the end condition solves the system
    ([run_solves_g]), and with an inverse of the flat matrix every such run
    is bounded by |g| and the sources ([run_bound_g]). The rows after the
    start rows do not read Cs ([mblock_Cs]), so they are CFMS's rows. *)

From Coq Require Import Reals Bool Lra Lia.
From Stellarocq Require Import Mat Shoot Recur CFMS.

Local Open Scope R_scope.

Section MSg.

Variable h : R.
Variable Psi : nat -> mat.
Variable nseg : nat.
Hypothesis Hnseg : (1 <= nseg)%nat.
Variable cut : nat -> nat.
Hypothesis Hcut : forall k, (k < nseg)%nat -> (cut k <= cut (S k))%nat.
Variables W Wi : nat -> mat.
Hypothesis HWW : forall k, (k < nseg)%nat -> forall r c, (r < 14)%nat -> (c < 14)%nat ->
  mm 14 (Wi k) (W k) r c = mI r c.
Variable Cs : mat.
Variable We : mat.

Definition rhsg (g : vec) (src : nat -> vec) : vec :=
  fun r => if Nat.ltb r 5 then g r else rhs h Psi nseg cut W We src r.

Definition Z0 : mat := fun _ _ => 0.

Lemma mblock_Cs :
  forall I J, I <> 0%nat -> mblock Psi nseg cut W Wi Cs We I J = mblock Psi nseg cut W Wi Z0 We I J.
Proof. intros I J HI. unfold mblock. rewrite (proj2 (Nat.eqb_neq I 0) HI). reflexivity. Qed.

(** A run with the start Cs z = g and the end condition solves the system
    with right-hand side [rhsg]. *)
Theorem run_solves_g :
  forall z src g,
  runs h Psi z src (cut 0) (cut nseg) ->
  (forall r, (r < 5)%nat -> mv 14 Cs (z (cut 0)) r = g r) ->
  (forall r, (r < 9)%nat -> z (cut nseg) r = 0) ->
  forall c, (c < msdim nseg)%nat ->
  mv (msdim nseg) (msys Psi nseg cut W Wi Cs We) (ufrom nseg cut W z) c = rhsg g src c.
Proof.
  intros z src g Hrun Hs He c Hc.
  destruct (row_split nseg Hnseg c Hc) as [Ec [HI Hi]].
  revert Ec HI Hi. generalize (c / 14)%nat (c mod 14)%nat. intros I i Ec HI Hi. subst c.
  rewrite msys_row by assumption.
  destruct (Nat.eq_dec I 0) as [->|HI0].
  - rewrite (msum_two _ (S nseg) 0 nseg ltac:(lia) ltac:(lia) ltac:(lia)).
    2: { intros J HJ HJ0 HJn. unfold mblock. cbn [Nat.eqb].
         rewrite (proj2 (Nat.eqb_neq J 0) HJ0), (proj2 (Nat.eqb_neq J nseg) HJn). apply mv_zero_mat. }
    unfold mblock. cbn [Nat.eqb].
    replace (Nat.eqb nseg 0) with false by (symmetry; apply Nat.eqb_neq; lia). rewrite Nat.eqb_refl.
    rewrite (mv_extn 14 (mm 14 (padrows Cs) (Wi 0)) (blk (ufrom nseg cut W z) 0) (mv 14 (W 0) (z (cut 0))) i)
      by (intros c Hc'; apply blk_ufrom_lt; [lia | exact Hc']).
    rewrite (mv_mm_WiW nseg W Wi HWW) by lia. rewrite mv_padrows, mv_D9 by exact Hi.
    unfold rhsg. replace (14 * 0 + i)%nat with i by lia.
    destruct (Nat.ltb_spec i 5) as [H5|H5].
    + rewrite Hs by exact H5. replace (Nat.leb 5 i) with false by (symmetry; apply Nat.leb_gt; lia). ring.
    + replace (Nat.leb 5 i) with true by (symmetry; apply Nat.leb_le; lia).
      rewrite blk_ufrom_end by exact Hi. replace (Nat.ltb i 5) with false by (symmetry; apply Nat.ltb_ge; lia).
      change (rhs h Psi nseg cut W We src i) with (blk (rhs h Psi nseg cut W We src) 0 i).
      rewrite blk_rhs by exact Hi. cbn [Nat.eqb]. ring.
  - rewrite (msum_ext _ (fun J => mv 14 (mblock Psi nseg cut W Wi Z0 We I J) (blk (ufrom nseg cut W z) J) i))
      by (intros J _; rewrite mblock_Cs by exact HI0; reflexivity).
    rewrite <- msys_row by assumption.
    rewrite (run_solves h Psi nseg Hnseg cut Hcut W Wi HWW Z0 We z src Hrun (fun r _ => mv_zero_mat 14 _ r) He I i HI Hi).
    unfold rhsg. replace (Nat.ltb (14 * I + i) 5) with false by (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
Qed.

Section Bound.

Variable X : mat.
Variables q G Wm Wim : R.
Hypothesis HXl : forall r c, (r < msdim nseg)%nat -> (c < msdim nseg)%nat ->
  mm (msdim nseg) X (msys Psi nseg cut W Wi Cs We) r c = mI r c.
Hypothesis Hq : mnorm (msdim nseg) (msdim nseg) X <= q.
Hypothesis HG : forall k, (k < nseg)%nat -> forall i i', (i <= i' <= lenk cut k)%nat ->
  mnorm 14 14 (mprod 14 Psi (cut k + i) (i' - i)) <= G.
Hypothesis HWm : forall k, (k < nseg)%nat -> mnorm 14 14 (W k) <= Wm.
Hypothesis HWem : mnorm 14 14 We <= Wm.
Hypothesis HWim : forall k, (k < nseg)%nat -> mnorm 14 14 (Wi k) <= Wim.

Lemma rhsg_bound : forall g src, vnorm (msdim nseg) (rhsg g src) <= vnorm 5 g + Wm * (G * swt h nseg cut src).
Proof.
  intros g src. assert (H0 : 0 <= vnorm 5 g) by apply vnorm_nonneg.
  assert (H1 := rhs_bound h Psi nseg Hnseg cut Hcut W We G Wm HG HWm HWem src).
  assert (H2 : 0 <= vnorm (msdim nseg) (rhs h Psi nseg cut W We src)) by apply vnorm_nonneg.
  apply vnorm_le; [lra|]. intros r Hr. unfold rhsg. destruct (Nat.ltb_spec r 5) as [H5|H5].
  - eapply Rle_trans; [apply (vnorm_ge 5 g r H5)|]. lra.
  - eapply Rle_trans; [apply (vnorm_ge (msdim nseg) _ r Hr)|]. lra.
Qed.

(** Every run with the start Cs z = g and the end condition is bounded by
    |g| and its sources. *)
Theorem run_bound_g :
  forall z src g,
  runs h Psi z src (cut 0) (cut nseg) ->
  (forall r, (r < 5)%nat -> mv 14 Cs (z (cut 0)) r = g r) ->
  (forall r, (r < 9)%nat -> z (cut nseg) r = 0) ->
  forall k i, (k < nseg)%nat -> (i <= lenk cut k)%nat ->
  vnorm 14 (z (cut k + i)%nat)
  <= G * (Wim * (q * (vnorm 5 g + Wm * (G * swt h nseg cut src)))) + G * swt h nseg cut src.
Proof.
  intros z src g Hrun Hs He k i Hk Hi.
  set (u := ufrom nseg cut W z).
  assert (Hu : forall r, (r < msdim nseg)%nat -> u r = mv (msdim nseg) X (rhsg g src) r).
  { intros r Hr. rewrite <- (mv_inv_cancel (msdim nseg) (msys Psi nseg cut W Wi Cs We) X u r HXl Hr).
    apply mv_extn. intros c Hc. exact (run_solves_g z src g Hrun Hs He c Hc). }
  assert (Hun : vnorm (msdim nseg) u <= q * (vnorm 5 g + Wm * (G * swt h nseg cut src))).
  { rewrite (vnorm_ext (msdim nseg) u (mv (msdim nseg) X (rhsg g src))) by exact Hu.
    eapply Rle_trans; [apply vnorm_mv|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact Hq | apply rhsg_bound]. }
  assert (Hzc : vnorm 14 (z (cut k)) <= Wim * (q * (vnorm 5 g + Wm * (G * swt h nseg cut src)))).
  { rewrite (vnorm_ext 14 (z (cut k)) (mv 14 (Wi k) (blk u k))).
    - eapply Rle_trans; [apply vnorm_mv|].
      apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | apply HWim; exact Hk|].
      eapply Rle_trans; [apply (vnorm_blk nseg Hnseg); lia | exact Hun].
    - intros c Hc. unfold u. rewrite (mv_extn 14 (Wi k) (blk (ufrom nseg cut W z) k) (mv 14 (W k) (z (cut k))) c)
        by (intros c' Hc'; apply blk_ufrom_lt; assumption).
      symmetry. apply (WiW nseg W Wi HWW); assumption. }
  assert (H0 := cut_mono nseg Hnseg cut Hcut 0 k ltac:(lia)).
  assert (HN := cut_mono nseg Hnseg cut Hcut (S k) nseg ltac:(lia)).
  assert (H1 := cut_mono nseg Hnseg cut Hcut k (S k) ltac:(lia)).
  assert (Hsplit : forall r, (r < 14)%nat ->
            z (cut k + i)%nat r = mv 14 (mprod 14 Psi (cut k) i) (z (cut k)) r + part h Psi src (cut k) i r).
  { intros r Hr. apply (run_split h Psi z src (cut k) (cut nseg)); [| unfold lenk in Hi; lia | exact Hr].
    intros j Hj. apply Hrun. lia. }
  rewrite (vnorm_ext 14 (z (cut k + i)%nat)
             (fun r => mv 14 (mprod 14 Psi (cut k) i) (z (cut k)) r + part h Psi src (cut k) i r)) by exact Hsplit.
  eapply Rle_trans.
  { apply vnorm_le; [apply Rplus_le_le_0_compat; apply vnorm_nonneg|].
    intros r Hr. eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; apply vnorm_ge; exact Hr. }
  apply Rplus_le_compat.
  - eapply Rle_trans; [apply vnorm_mv|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | | exact Hzc].
    assert (HG0 := HG k Hk 0 i ltac:(lia)). rewrite Nat.add_0_r, Nat.sub_0_r in HG0. exact HG0.
  - eapply Rle_trans.
    + apply part_bound. intros i' Hi'. replace (S (cut k + i')) with (cut k + S i')%nat by lia.
      apply (HG k Hk (S i') i). lia.
    + apply Rmult_le_compat_l; [eapply Rle_trans; [apply mnorm_nonneg | apply (HG k Hk 0 0); lia]|].
      eapply Rle_trans; [| apply (swt_seg h nseg Hnseg cut Hcut src k Hk)].
      apply (msum_le_prefix (fun i' => Rabs h * vnorm 14 (src (cut k + i')%nat)) i (lenk cut k)); [|exact Hi].
      intros; apply Rmult_le_pos; [apply Rabs_pos | apply vnorm_nonneg].
Qed.

End Bound.

End MSg.
