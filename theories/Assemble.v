(** From cells to the propagators of every finer level, and from the
    propagators to the block system.

    [seg_bound]: a run of nb f steps I + h A_j, cut into nb blocks of f steps
    whose matrices lie within om_i of B_i and have norm at most nu_i, differs
    from the product of the reference steps G_i = I + f h B_i by at most
    sum_i (prod_{j > i} q_j) l_i (prod_{j < i} (q_j + l_j)), for any q_i >= |G_i|
    and l_i >= f h om_i + e^(f h nu_i) - 1 - f h nu_i ([Osc.osc_local] block by
    block, [Shoot.mprod_diff_norm] across blocks). The bound does not depend
    on f, so it holds for every level that refines the reference steps.
    [mprod_conj] and [conj_step] carry the steps into the constant
    coordinates of a frame. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Stellarocq Require Import Mat Shoot Recur CFMS Step NBound TMat Osc.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Products in constant coordinates                                  *)

Section Conj.

Variable n : nat.
Variables W Wi : mat.
Hypothesis HWiW : forall i j, (i < n)%nat -> (j < n)%nat -> mm n Wi W i j = mI i j.
Hypothesis HWWi : forall i j, (i < n)%nat -> (j < n)%nat -> mm n W Wi i j = mI i j.

Lemma conj_mul :
  forall A B, meq n (mm n (mm n (mm n W A) Wi) (mm n (mm n W B) Wi)) (mm n (mm n W (mm n A B)) Wi).
Proof.
  intros A B.
  eapply meq_trans; [apply mm_assoc_meq|].
  eapply meq_trans; [apply mm_meq; [apply meq_refl | apply meq_sym; apply mm_assoc_meq]|].
  eapply meq_trans; [apply mm_meq; [apply meq_refl | apply mm_meq; [apply meq_sym; apply mm_assoc_meq | apply meq_refl]]|].
  eapply meq_trans; [apply mm_meq; [apply meq_refl | apply mm_meq; [apply mm_meq; [exact HWiW | apply meq_refl] | apply meq_refl]]|].
  eapply meq_trans; [apply mm_meq; [apply meq_refl | apply mm_meq; [apply mm_mI_meq_l | apply meq_refl]]|].
  eapply meq_trans; [apply meq_sym; apply mm_assoc_meq|].
  apply mm_meq; [apply mm_assoc_meq | apply meq_refl].
Qed.

Lemma mprod_conj :
  forall (Ps : nat -> mat) a k,
  meq n (mprod n (fun j => mm n (mm n W (Ps j)) Wi) a k) (mm n (mm n W (mprod n Ps a k)) Wi).
Proof.
  intros Ps a k. induction k as [|k IH]; cbn [mprod].
  - eapply meq_trans; [apply meq_sym; exact HWWi|].
    apply mm_meq; [apply meq_sym; apply mm_mI_meq_r | apply meq_refl].
  - eapply meq_trans; [apply mm_meq; [apply meq_refl | exact IH]|]. apply conj_mul.
Qed.

(** One step in coordinates is I + h W N Wi. *)
Lemma conj_step :
  forall h (N : mat), meq n (mm n (mm n W (fun i j => mI i j + h * N i j)) Wi)
                            (fun i j => mI i j + h * mm n (mm n W N) Wi i j).
Proof.
  intros h N i j Hi Hj. unfold mm. cbv beta.
  rewrite (msum_ext (fun l => msum (fun k => W i k * (mI k l + h * N k l)) n * Wi l j)
                    (fun l => W i l * Wi l j + h * (msum (fun k => W i k * N k l) n * Wi l j))).
  - rewrite msum_plus, msum_scal. fold (mm n W Wi i j). rewrite HWWi by assumption. reflexivity.
  - intros l Hl.
    rewrite (msum_ext (fun k => W i k * (mI k l + h * N k l)) (fun k => W i k * mI k l + h * (W i k * N k l)))
      by (intros; ring).
    rewrite msum_plus, msum_scal. fold (mm n W mI i l). rewrite mm_mI_r by exact Hl. ring.
Qed.

End Conj.

(* ---------------------------------------------------------------- *)
(* Blocks of steps                                                   *)

Lemma mprod_blocks :
  forall n (Ps : nat -> mat) a f nb,
  meq n (mprod n Ps a (nb * f)) (mprod n (fun i => mprod n Ps (a + i * f) f) 0 nb).
Proof.
  intros n Ps a f nb. induction nb as [|nb IH].
  - cbn [mprod Nat.mul]. apply meq_refl.
  - replace (S nb * f)%nat with (nb * f + f)%nat by lia.
    eapply meq_trans; [apply mprod_split|]. cbn [mprod].
    replace (0 + nb)%nat with nb by lia. replace (a + nb * f)%nat with (a + nb * f)%nat by reflexivity.
    apply mm_meq; [apply meq_refl | exact IH].
Qed.

(* ---------------------------------------------------------------- *)
(* A segment of every level against the reference steps              *)

Section Segment.

Variable A : nat -> mat.
Variable B : nat -> mat.
Variables h : R.
Variables a f nb : nat.
Variables om nu q l : nat -> R.
Hypothesis Hh : 0 <= h.
Hypothesis Hf : (0 < f)%nat.
Hypothesis HA : forall i t, (i < nb)%nat -> (t < f)%nat -> mnorm 14 14 (msub (A (a + i * f + t)%nat) (B i)) <= om i.
Hypothesis Hnu : forall i t, (i < nb)%nat -> (t < f)%nat -> mnorm 14 14 (A (a + i * f + t)%nat) <= nu i.

Definition gstep (i : nat) : mat := fun r c => mI r c + INR f * h * B i r c.

Hypothesis Hq : forall i, (i < nb)%nat -> mnorm 14 14 (gstep i) <= q i.
Hypothesis Hl : forall i, (i < nb)%nat -> INR f * h * om i + (exp (INR f * h * nu i) - 1 - INR f * h * nu i) <= l i.

Lemma block_close :
  forall i, (i < nb)%nat -> mnorm 14 14 (msub (mprod 14 (fstep A h) (a + i * f) f) (gstep i)) <= l i.
Proof.
  intros i Hi.
  eapply Rle_trans; [apply (osc_local 14 A (B i) h (om i) (nu i) (a + i * f) f Hh)|].
  - intros t Ht. replace (a + i * f + t)%nat with (a + i * f + t)%nat by reflexivity. apply HA; assumption.
  - intros t Ht. apply Hnu; assumption.
  - eapply Rle_trans; [| apply (Hl i Hi)].
    assert (Hnu0 : 0 <= nu i) by (eapply Rle_trans; [apply mnorm_nonneg | apply (Hnu i 0%nat Hi Hf)]).
    assert (He := pow_exp (h * nu i) f ltac:(apply Rmult_le_pos; lra)).
    replace (INR f * (h * nu i)) with (INR f * h * nu i) in He by ring. lra.
Qed.

Theorem seg_bound :
  mnorm 14 14 (msub (mprod 14 (fstep A h) a (nb * f)) (mprod 14 gstep 0 nb))
  <= msum (fun i => gprodf q (S i) (nb - S i) * l i * gprodf (fun j => q j + l j) 0 i) nb.
Proof.
  rewrite (mnorm_meq 14 _ (msub (mprod 14 (fun i => mprod 14 (fstep A h) (a + i * f) f) 0 nb) (mprod 14 gstep 0 nb))).
  2: { intros r c Hr Hc. unfold msub. rewrite (mprod_blocks 14 (fstep A h) a f nb r c Hr Hc). reflexivity. }
  apply (mprod_diff_norm 14 (fun i => mprod 14 (fstep A h) (a + i * f) f) gstep (fun j => q j + l j) q l 0 nb).
  - lia.
  - intros i Hi. rewrite Nat.add_0_l.
    rewrite (mnorm_ext 14 14 (mprod 14 (fstep A h) (a + i * f) f)
               (fun r c => gstep i r c + msub (mprod 14 (fstep A h) (a + i * f) f) (gstep i) r c))
      by (intros; unfold msub; ring).
    eapply Rle_trans; [apply mnorm_add_le|]. apply Rplus_le_compat; [apply Hq | apply block_close]; exact Hi.
  - intros i Hi. rewrite Nat.add_0_l. apply Hq. exact Hi.
  - intros i Hi. rewrite Nat.add_0_l. apply block_close. exact Hi.
Qed.

End Segment.

(* ---------------------------------------------------------------- *)
(* Block systems of the CFMS shape                                   *)

(** The system from its start block, its junctions and its end block. *)
Definition gblock (nseg : nat) (B00 : mat) (J : nat -> mat) (Eb We : mat) (I K : nat) : mat :=
  if Nat.eqb I 0 then
    (if Nat.eqb K 0 then B00 else if Nat.eqb K nseg then D9 else fun _ _ => 0)
  else if Nat.eqb I nseg then
    (if Nat.eqb K (nseg - 1) then Eb else if Nat.eqb K nseg then (fun r c => - mm 14 We E0p r c) else fun _ _ => 0)
  else
    (if Nat.eqb K (I - 1) then (fun r c => - J (I - 1)%nat r c) else if Nat.eqb K I then mI else fun _ _ => 0).

Lemma mblock_gblock :
  forall Psi nseg cut W Wi Cs We I K,
  mblock Psi nseg cut W Wi Cs We I K
  = gblock nseg (mm 14 (padrows Cs) (Wi 0%nat)) (jun Psi cut W Wi) (endb Psi nseg cut Wi We) We I K.
Proof. reflexivity. Qed.

Lemma mrow_flat :
  forall (A : nat -> nat -> mat) ng I r, (r < 14)%nat ->
  mrow (14 * ng) (flat A) (14 * I + r) = msum (fun K => mrow 14 (A I K) r) ng.
Proof.
  intros A ng I r Hr. unfold mrow. rewrite msum_blocks. apply msum_ext. intros K HK.
  apply msum_ext. intros j Hj. unfold flat. rewrite !div14, !mod14 by assumption. reflexivity.
Qed.

Lemma mrow_zero : forall r, mrow 14 (fun _ _ => 0) r = 0.
Proof.
  intros r. unfold mrow. rewrite (msum_ext _ (fun _ => 0)) by (intros; apply Rabs_R0). apply msum_zero.
Qed.

Lemma mrow_msub_same : forall A r, mrow 14 (msub A A) r = 0.
Proof.
  intros A r. unfold mrow, msub. rewrite (msum_ext _ (fun _ => 0)).
  - apply msum_zero.
  - intros j _. replace (A r j - A r j) with 0 by ring. apply Rabs_R0.
Qed.

Lemma mrow_neg_sub : forall A B r, mrow 14 (msub (fun i j => - A i j) (fun i j => - B i j)) r = mrow 14 (msub A B) r.
Proof.
  intros A B r. unfold mrow, msub. apply msum_ext. intros j _.
  replace (- A r j - - B r j) with (- (A r j - B r j)) by ring. apply Rabs_Ropp.
Qed.

(** A row of the difference of two systems that share their identity,
    selector and end-coupling blocks. *)
Lemma gblock_diff_row :
  forall nseg B00 J Eb B00' J' Eb' We I r, (1 <= nseg)%nat -> (I <= nseg)%nat ->
  msum (fun K => mrow 14 (msub (gblock nseg B00 J Eb We I K) (gblock nseg B00' J' Eb' We I K)) r) (S nseg)
  = if Nat.eqb I 0 then mrow 14 (msub B00 B00') r
    else if Nat.eqb I nseg then mrow 14 (msub Eb Eb') r
    else mrow 14 (msub (J (I - 1)%nat) (J' (I - 1)%nat)) r.
Proof.
  intros nseg B00 J Eb B00' J' Eb' We I r Hn HI. unfold gblock.
  destruct (Nat.eqb_spec I 0) as [->|H0].
  - rewrite (msum_single _ (S nseg) 0 ltac:(lia)).
    + cbn [Nat.eqb]. reflexivity.
    + intros K HK HK0. destruct (Nat.eqb_spec K 0) as [|_]; [lia|].
      destruct (Nat.eqb K nseg); apply mrow_msub_same.
  - destruct (Nat.eqb_spec I nseg) as [->|Hn'].
    + rewrite (msum_single _ (S nseg) (nseg - 1) ltac:(lia)).
      * rewrite Nat.eqb_refl. reflexivity.
      * intros K HK HK1. destruct (Nat.eqb_spec K (nseg - 1)) as [|_]; [lia|].
        destruct (Nat.eqb K nseg); apply mrow_msub_same.
    + rewrite (msum_single _ (S nseg) (I - 1) ltac:(lia)).
      * rewrite Nat.eqb_refl. apply mrow_neg_sub.
      * intros K HK HK1. destruct (Nat.eqb_spec K (I - 1)) as [|_]; [lia|].
        destruct (Nat.eqb K I); apply mrow_msub_same.
Qed.

(** The system is invertible when an approximate inverse Ra of a reference
    system M0 meets the perturbation only through the row sums of the start,
    junction and end blocks. *)
Theorem block_system_inverse :
  forall nseg B00 J Eb B00' J' Eb' We (Ra : mat) (rho : nat -> R) th0 th1 th2,
  (1 <= nseg)%nat ->
  let N := (14 * S nseg)%nat in
  let M := flat (gblock nseg B00 J Eb We) in
  let M0 := flat (gblock nseg B00' J' Eb' We) in
  mnorm N N (msub mI (mm N Ra M0)) <= th0 ->
  mnorm N N (msub mI (mm N M0 Ra)) <= th2 -> th2 < 1 ->
  (forall r, (r < 14)%nat -> mrow 14 (msub B00 B00') r <= rho r) ->
  (forall I r, (1 <= I < nseg)%nat -> (r < 14)%nat ->
     mrow 14 (msub (J (I - 1)%nat) (J' (I - 1)%nat)) r <= rho (14 * I + r)%nat) ->
  (forall r, (r < 14)%nat -> mrow 14 (msub Eb Eb') r <= rho (14 * nseg + r)%nat) ->
  (forall i, (i < N)%nat -> msum (fun j => Rabs (Ra i j) * rho j) N <= th1) ->
  th0 + th1 < 1 ->
  exists X : mat,
    (forall i j, (i < N)%nat -> (j < N)%nat -> mm N X M i j = mI i j) /\
    (forall i j, (i < N)%nat -> (j < N)%nat -> mm N M X i j = mI i j) /\
    mnorm N N X <= mnorm N N Ra / (1 - (th0 + th1)).
Proof.
  intros nseg B00 J Eb B00' J' Eb' We Ra rho th0 th1 th2 Hn N M M0 H0 H2 Hlt2 Hs Hj He Hb Hlt.
  (* every row of M - M0 is bounded by rho *)
  assert (Hrow : forall j, (j < N)%nat -> mrow N (msub M M0) j <= rho j).
  { intros j Hj'. set (I := (j / 14)%nat). set (r := (j mod 14)%nat).
    assert (Hr : (r < 14)%nat) by (unfold r; apply Nat.mod_upper_bound; lia).
    assert (Ej : j = (14 * I + r)%nat) by (unfold I, r; apply Nat.div_mod; lia).
    assert (HI : (I <= nseg)%nat) by (unfold I, N in *; apply Nat.lt_succ_r; apply Nat.div_lt_upper_bound; lia).
    rewrite Ej.
    unfold N.
    change (mrow (14 * S nseg) (msub M M0) (14 * I + r))
      with (mrow (14 * S nseg) (flat (fun I' K => msub (gblock nseg B00 J Eb We I' K) (gblock nseg B00' J' Eb' We I' K)))
                 (14 * I + r)).
    rewrite (mrow_flat (fun I' K => msub (gblock nseg B00 J Eb We I' K) (gblock nseg B00' J' Eb' We I' K))
               (S nseg) I r Hr).
    rewrite gblock_diff_row by assumption.
    destruct (Nat.eqb_spec I 0) as [E0|E0].
    - rewrite E0. replace (14 * 0 + r)%nat with r by lia. apply Hs. exact Hr.
    - destruct (Nat.eqb_spec I nseg) as [En|En].
      + rewrite En. apply He. exact Hr.
      + apply Hj; [lia | exact Hr]. }
  assert (Hrho : forall j, (j < N)%nat -> 0 <= rho j)
    by (intros j Hj'; eapply Rle_trans; [| apply Hrow; exact Hj']; unfold mrow; apply msum_nonneg; intros; apply Rabs_pos).
  assert (Hth1 : 0 <= th1).
  { eapply Rle_trans; [| apply (Hb 0%nat); unfold N; lia]. apply msum_nonneg. intros j Hj'.
    apply Rmult_le_pos; [apply Rabs_pos | apply Hrho; exact Hj']. }
  apply (left_perturbed_inverse N M M0 Ra th0 th1 th2 H0); [| exact Hlt | exact H2 | exact Hlt2].
  apply (mnorm_mm_rowsums N Ra (msub M M0) rho th1); [exact Hrow | exact Hb | exact Hth1].
Qed.
