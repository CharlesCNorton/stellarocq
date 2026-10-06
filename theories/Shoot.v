(** Products of step matrices: their growth, and the difference of two
    products step by step.

    [mprod Ps a k] is Ps (a + k - 1) ... Ps (a + 1) Ps a, the propagator of
    the recursion z_{j+1} = Ps j z_j over k steps from a. Its norm is at most
    the product of the steps' norms ([mprod_norm]), it splits at any
    intermediate step ([mprod_split]), and two products of k steps differ by
    the sum over the steps of the second product after the step, the
    difference of the two steps, and the first product before it
    ([mprod_telescope]), which bounds their distance by the steps' distances
    ([mprod_diff_norm]). Applied to the steps of one grid against the steps
    of the grid of half the spacing taken two at a time, this is the
    comparison of propagators across grid levels. *)

From Coq Require Import Reals Lra Lia.
From Stellarocq Require Import Mat.

Local Open Scope R_scope.

Section Prod.

Variable n : nat.

Fixpoint mprod (Ps : nat -> mat) (a k : nat) : mat :=
  match k with
  | O => mI
  | S k' => mm n (Ps (a + k')%nat) (mprod Ps a k')
  end.

(** Matrices agreeing on the indices below n. *)
Definition meq (A B : mat) : Prop := forall i j, (i < n)%nat -> (j < n)%nat -> A i j = B i j.

Lemma meq_refl : forall A, meq A A.
Proof. intros A i j _ _. reflexivity. Qed.

Lemma meq_sym : forall A B, meq A B -> meq B A.
Proof. intros A B H i j Hi Hj. symmetry. apply H; assumption. Qed.

Lemma meq_trans : forall A B C, meq A B -> meq B C -> meq A C.
Proof. intros A B C H1 H2 i j Hi Hj. rewrite H1 by assumption. apply H2; assumption. Qed.

Lemma mm_meq :
  forall A A' B B', meq A A' -> meq B B' -> meq (mm n A B) (mm n A' B').
Proof.
  intros A A' B B' HA HB i j Hi Hj. apply mm_ext.
  - intros l Hl. apply HA; assumption.
  - intros l Hl. apply HB; assumption.
Qed.

Lemma mnorm_meq : forall A B, meq A B -> mnorm n n A = mnorm n n B.
Proof.
  intros A B H. unfold mnorm.
  apply Rle_antisym; apply fmax_mono; intros i Hi; unfold mrow; apply msum_le; intros j Hj;
    rewrite H by assumption; lra.
Qed.

Lemma mnorm_madd : forall A B, mnorm n n (madd A B) <= mnorm n n A + mnorm n n B.
Proof.
  intros A B. apply fmax_le; [apply Rplus_le_le_0_compat; apply mnorm_nonneg|].
  intros i Hi. unfold mrow, madd.
  eapply Rle_trans; [| apply Rplus_le_compat; apply mrow_le_mnorm; exact Hi].
  unfold mrow. rewrite <- msum_plus. apply msum_le. intros j Hj. apply Rabs_triang.
Qed.

Lemma mnorm_zero : mnorm n n (fun _ _ => 0) = 0.
Proof.
  apply Rle_antisym; [| apply mnorm_nonneg].
  apply fmax_le; [lra|]. intros i Hi. unfold mrow.
  rewrite (msum_ext _ (fun _ => 0)) by (intros; apply Rabs_R0). rewrite msum_zero. lra.
Qed.

Lemma mm_mI_meq_l : forall A, meq (mm n mI A) A.
Proof. intros A i j Hi Hj. apply mm_mI_l. exact Hi. Qed.

Lemma mm_mI_meq_r : forall A, meq (mm n A mI) A.
Proof. intros A i j Hi Hj. apply mm_mI_r. exact Hj. Qed.

Lemma mm_assoc_meq : forall A B C, meq (mm n (mm n A B) C) (mm n A (mm n B C)).
Proof. intros A B C i j _ _. apply mm_assoc. Qed.

(** The product over k + l steps is the product over the last l after the
    product over the first k. *)
Lemma mprod_split :
  forall Ps a k l, meq (mprod Ps a (k + l)) (mm n (mprod Ps (a + k) l) (mprod Ps a k)).
Proof.
  intros Ps a k l. induction l as [|l IH].
  - rewrite Nat.add_0_r. cbn [mprod]. apply meq_sym. apply mm_mI_meq_l.
  - replace (k + S l)%nat with (S (k + l)) by lia. cbn [mprod].
    replace (a + (k + l))%nat with (a + k + l)%nat by lia.
    eapply meq_trans; [apply mm_meq; [apply meq_refl | exact IH]|].
    apply meq_sym. apply mm_assoc_meq.
Qed.

Lemma mprod_ext :
  forall Ps Qs a k, (forall i, (i < k)%nat -> meq (Ps (a + i)%nat) (Qs (a + i)%nat)) ->
  meq (mprod Ps a k) (mprod Qs a k).
Proof.
  intros Ps Qs a k H. induction k as [|k IH]; cbn [mprod].
  - apply meq_refl.
  - apply mm_meq; [apply H; lia | apply IH; intros i Hi; apply H; lia].
Qed.

(** The product of the bounds of k steps from a. *)
Fixpoint gprodf (g : nat -> R) (a k : nat) : R :=
  match k with O => 1 | S k' => g (a + k')%nat * gprodf g a k' end.

Lemma gprodf_nonneg : forall g a k, (forall j, 0 <= g j) -> 0 <= gprodf g a k.
Proof.
  intros g a k Hg. induction k as [|k IH]; cbn [gprodf]; [lra|].
  apply Rmult_le_pos; [apply Hg | exact IH].
Qed.

Lemma gprodf_split :
  forall g a k l, gprodf g a (k + l) = gprodf g (a + k) l * gprodf g a k.
Proof.
  intros g a k l. induction l as [|l IH].
  - rewrite Nat.add_0_r. cbn [gprodf]. ring.
  - replace (k + S l)%nat with (S (k + l)) by lia. cbn [gprodf].
    rewrite IH. replace (a + (k + l))%nat with (a + k + l)%nat by lia. ring.
Qed.

Theorem mprod_norm :
  forall Ps g a k, (0 < n)%nat -> (forall i, (i < k)%nat -> mnorm n n (Ps (a + i)%nat) <= g (a + i)%nat) ->
  mnorm n n (mprod Ps a k) <= gprodf g a k.
Proof.
  intros Ps g a k Hn H. induction k as [|k IH]; cbn [mprod gprodf].
  - unfold mnorm. apply fmax_le; [lra|]. intros i Hi. unfold mrow, mI.
    rewrite (msum_single _ n i Hi).
    + rewrite Nat.eqb_refl, Rabs_R1. lra.
    + intros j Hj Hji. destruct (Nat.eqb_spec i j) as [->|]; [lia | apply Rabs_R0].
  - eapply Rle_trans; [apply mnorm_mm|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | apply H; lia |].
    apply IH. intros i Hi. apply H. lia.
Qed.

(** Two products of the same number of steps, as a sum over the steps. *)
Fixpoint telesum (Ps Qs : nat -> mat) (a k : nat) : mat :=
  match k with
  | O => fun _ _ => 0
  | S k' => madd (mm n (Qs (a + k')%nat) (telesum Ps Qs a k'))
                 (mm n (msub (Ps (a + k')%nat) (Qs (a + k')%nat)) (mprod Ps a k'))
  end.

Lemma mm_madd_r : forall A B C, meq (mm n A (madd B C)) (madd (mm n A B) (mm n A C)).
Proof.
  intros A B C i j _ _. unfold mm, madd.
  rewrite <- msum_plus. apply msum_ext. intros l _. ring.
Qed.

Lemma mm_msub_l : forall A B C, meq (mm n (msub A B) C) (msub (mm n A C) (mm n B C)).
Proof.
  intros A B C i j _ _. unfold mm, msub.
  rewrite <- msum_minus. apply msum_ext. intros l _. ring.
Qed.

Theorem mprod_telescope :
  forall Ps Qs a k, meq (msub (mprod Ps a k) (mprod Qs a k)) (telesum Ps Qs a k).
Proof.
  intros Ps Qs a k. induction k as [|k IH]; cbn [mprod telesum].
  - intros i j _ _. unfold msub. ring.
  - (* P_k X - Q_k Y = Q_k (X - Y) + (P_k - Q_k) X *)
    intros i j Hi Hj. unfold msub, madd, mm.
    rewrite (msum_ext (fun l => Qs (a + k)%nat i l * telesum Ps Qs a k l j)
                      (fun l => Qs (a + k)%nat i l * (mprod Ps a k l j - mprod Qs a k l j)))
      by (intros l Hl; rewrite <- (IH l j Hl Hj); reflexivity).
    rewrite <- msum_minus, <- msum_plus. apply msum_ext. intros l _. ring.
Qed.

(** The sum over the steps bounded by the steps' growths and distances. *)
Lemma telesum_norm :
  forall Ps Qs gP gQ e a k, (0 < n)%nat ->
  (forall i, (i < k)%nat -> mnorm n n (Ps (a + i)%nat) <= gP (a + i)%nat) ->
  (forall i, (i < k)%nat -> mnorm n n (Qs (a + i)%nat) <= gQ (a + i)%nat) ->
  (forall i, (i < k)%nat -> mnorm n n (msub (Ps (a + i)%nat) (Qs (a + i)%nat)) <= e (a + i)%nat) ->
  mnorm n n (telesum Ps Qs a k)
  <= msum (fun i => gprodf gQ (a + S i) (k - S i) * e (a + i)%nat * gprodf gP a i) k.
Proof.
  intros Ps Qs gP gQ e a k Hn. induction k as [|k IH]; intros HP HQ He.
  - cbn [telesum msum]. rewrite mnorm_zero. lra.
  - cbn [telesum msum].
    eapply Rle_trans; [apply mnorm_madd|].
    apply Rplus_le_compat.
    + (* the earlier steps, behind one more step of Q *)
      eapply Rle_trans; [apply mnorm_mm|].
      replace (msum (fun i => gprodf gQ (a + S i) (S k - S i) * e (a + i)%nat * gprodf gP a i) k)
        with (gQ (a + k)%nat * msum (fun i => gprodf gQ (a + S i) (k - S i) * e (a + i)%nat * gprodf gP a i) k).
      * apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | apply HQ; lia |].
        apply IH; intros i Hi; [apply HP | apply HQ | apply He]; lia.
      * rewrite <- msum_scal. apply msum_ext. intros i Hi.
        replace (S k - S i)%nat with (S (k - S i)) by lia. cbn [gprodf].
        replace (a + S i + (k - S i))%nat with (a + k)%nat by lia. ring.
    + (* the last step *)
      replace (S k - S k)%nat with O by lia. cbn [gprodf].
      eapply Rle_trans; [apply mnorm_mm|].
      rewrite Rmult_1_l.
      apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | apply He; lia |].
      apply mprod_norm; [exact Hn|]. intros i Hi. apply HP. lia.
Qed.

(** The distance of two products from the distances of their steps. *)
Theorem mprod_diff_norm :
  forall Ps Qs gP gQ e a k, (0 < n)%nat ->
  (forall i, (i < k)%nat -> mnorm n n (Ps (a + i)%nat) <= gP (a + i)%nat) ->
  (forall i, (i < k)%nat -> mnorm n n (Qs (a + i)%nat) <= gQ (a + i)%nat) ->
  (forall i, (i < k)%nat -> mnorm n n (msub (Ps (a + i)%nat) (Qs (a + i)%nat)) <= e (a + i)%nat) ->
  mnorm n n (msub (mprod Ps a k) (mprod Qs a k))
  <= msum (fun i => gprodf gQ (a + S i) (k - S i) * e (a + i)%nat * gprodf gP a i) k.
Proof.
  intros Ps Qs gP gQ e a k Hn HP HQ He.
  rewrite (mnorm_meq _ _ (mprod_telescope Ps Qs a k)).
  apply telesum_norm; assumption.
Qed.

End Prod.
