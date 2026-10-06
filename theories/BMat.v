(** Interval matrices of 14 x 14 blocks.

    A block matrix is a list of rows of interval matrices ([bimat]); [bcont]
    says that block (I, K) encloses the block function B I K. Products and
    differences are taken block by block ([bmm_cont], [bIsub_cont]), so a
    product of two nb x nb block matrices costs nb^3 products of 14 x 14
    blocks; [flat_mm] and [flat_mI] read the flat matrices of CFMS.flat by
    blocks, and [bnorm_le_correct] bounds the norm of a flat matrix by the row
    sums of its blocks. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat TMEval Shoot Recur CFMS Assemble.

Import ListNotations.
Local Open Scope R_scope.

Definition bimat : Type := list (list imat).
Definition bget (B : bimat) (I K : nat) : imat := nth K (nth I B []) [].
Definition btab (nb : nat) (f : nat -> nat -> imat) : bimat := map (fun I => map (fun K => f I K) (seq 0 nb)) (seq 0 nb).

Lemma bget_btab : forall nb f I K, (I < nb)%nat -> (K < nb)%nat -> bget (btab nb f) I K = f I K.
Proof.
  intros nb f I K HI HK. unfold bget, btab.
  rewrite (nth_map_seq_lt (fun I => map (fun K => f I K) (seq 0 nb)) nb I [] HI).
  exact (nth_map_seq_lt (fun K => f I K) nb K [] HK).
Qed.

Definition bcont (nb : nat) (Bi : bimat) (B : nat -> nat -> mat) : Prop :=
  forall I K, (I < nb)%nat -> (K < nb)%nat -> icont 14 14 (bget Bi I K) (B I K).

(* ---------------------------------------------------------------- *)
(* Flat matrices by blocks                                           *)

Lemma flat_entry :
  forall (B : nat -> nat -> mat) I K r c, (r < 14)%nat -> (c < 14)%nat ->
  flat B (14 * I + r)%nat (14 * K + c)%nat = B I K r c.
Proof. intros B I K r c Hr Hc. unfold flat. rewrite !div14, !mod14 by assumption. reflexivity. Qed.

Lemma flat_mm :
  forall (A B : nat -> nat -> mat) nb I K r c, (r < 14)%nat -> (c < 14)%nat ->
  mm (14 * nb) (flat A) (flat B) (14 * I + r)%nat (14 * K + c)%nat
  = msum (fun L => mm 14 (A I L) (B L K) r c) nb.
Proof.
  intros A B nb I K r c Hr Hc. unfold mm at 1. rewrite msum_blocks. apply msum_ext. intros L HL.
  unfold mm. apply msum_ext. intros j Hj. rewrite !flat_entry by assumption. reflexivity.
Qed.

Lemma flat_mI :
  forall I K r c, (r < 14)%nat -> (c < 14)%nat ->
  mI (14 * I + r)%nat (14 * K + c)%nat = (if Nat.eqb I K then mI r c else 0).
Proof.
  intros I K r c Hr Hc. unfold mI.
  destruct (Nat.eqb_spec I K) as [->|HIK].
  - destruct (Nat.eqb_spec (14 * K + r) (14 * K + c)) as [E|E]; destruct (Nat.eqb_spec r c); try reflexivity; lia.
  - destruct (Nat.eqb_spec (14 * I + r) (14 * K + c)) as [E|E]; [| reflexivity].
    exfalso. apply HIK. assert (E' := f_equal (fun x => x / 14)%nat E). cbv beta in E'.
    rewrite !div14 in E' by assumption. exact E'.
Qed.

(** A flat matrix entry at a flat index, through its block and position. *)
Lemma flat_split :
  forall nb j, (j < 14 * nb)%nat -> exists I r, (I < nb)%nat /\ (r < 14)%nat /\ j = (14 * I + r)%nat.
Proof.
  intros nb j Hj. exists (j / 14)%nat, (j mod 14)%nat.
  split; [apply Nat.div_lt_upper_bound; lia|]. split; [apply Nat.mod_upper_bound; lia|]. apply Nat.div_mod. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The operations                                                    *)

Section Ops.

Variable prec : F.precision.

Definition izmat : imat := itab 14 14 (fun _ _ => I.zero).

(** The sum of a list of 14 x 14 interval matrices. *)
Definition isumm (L : list imat) : imat := fold_right (iadd prec 14 14) izmat L.

(** Block (I, K) of the product: the sum over L of A(I, L) B(L, K). *)
Definition bmm (nb : nat) (A B : bimat) : bimat :=
  btab nb (fun I K => isumm (map (fun L => imm prec 14 14 14 (bget A I L) (bget B L K)) (seq 0 nb))).

(** I - B, block by block. *)
Definition bIsub (nb : nat) (B : bimat) : bimat :=
  btab nb (fun I K => isub prec 14 14 (if Nat.eqb I K then iI prec 14 else izmat) (bget B I K)).

Definition browsum (nb : nat) (B : bimat) (I r : nat) : I.type :=
  isum prec (map (fun K => irowsum prec 14 (bget B I K) r) (seq 0 nb)).

Definition bnorm_le (nb : nat) (B : bimat) (th : I.type) : bool :=
  forallb (fun I => forallb (fun r => nonneg (I.sub prec th (browsum nb B I r))) (seq 0 14)) (seq 0 nb).

End Ops.

Strategy expand [isumm bmm bIsub browsum bnorm_le].

Section Sound.

Variable prec : F.precision.

Lemma izmat_cont : icont 14 14 izmat (fun _ _ => 0).
Proof. apply itab_correct. intros. exact zero_contains. Qed.

Lemma isumm_cont :
  forall {A : Type} (F : A -> imat) (M : A -> mat) (L : list A),
  (forall x, In x L -> icont 14 14 (F x) (M x)) ->
  icont 14 14 (isumm prec (map F L)) (fun r c => lsum (fun x => M x r c) L).
Proof.
  intros A F M L. induction L as [|x L IH]; intros H.
  - exact izmat_cont.
  - cbn [map isumm fold_right]. change (fold_right (iadd prec 14 14) izmat (map F L)) with (isumm prec (map F L)).
    unfold lsum in IH |- *. cbn [fold_right].
    apply (iadd_correct prec 14 14 (F x) _ (M x) (fun r c => fold_right (fun y acc => M y r c + acc) 0 L)).
    + apply H. left. reflexivity.
    + apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma bmm_cont :
  forall nb A B Ar Br, bcont nb A Ar -> bcont nb B Br ->
  bcont nb (bmm prec nb A B) (fun I K => fun r c => msum (fun L => mm 14 (Ar I L) (Br L K) r c) nb).
Proof.
  intros nb A B Ar Br HA HB I K HI HK. unfold bmm. rewrite bget_btab by assumption.
  intros r c Hr Hc. rewrite <- lsum_seq.
  apply (isumm_cont (fun L => imm prec 14 14 14 (bget A I L) (bget B L K)) (fun L => mm 14 (Ar I L) (Br L K)));
    [| exact Hr | exact Hc].
  intros L HL. apply in_seq in HL. apply imm_correct; [apply HA | apply HB]; lia.
Qed.

Lemma bIsub_cont :
  forall nb B Br, bcont nb B Br ->
  bcont nb (bIsub prec nb B) (fun I K => msub (if Nat.eqb I K then mI else fun _ _ => 0) (Br I K)).
Proof.
  intros nb B Br HB I K HI HK. unfold bIsub. rewrite bget_btab by assumption.
  apply isub_correct; [| apply HB; assumption].
  destruct (Nat.eqb I K); [apply iI_correct | apply izmat_cont].
Qed.

Theorem bnorm_le_correct :
  forall nb B Br th theta, (0 < nb)%nat -> bcont nb B Br -> contains (I.convert th) (Xreal theta) ->
  bnorm_le prec nb B th = true -> mnorm (14 * nb) (14 * nb) (flat Br) <= theta.
Proof.
  intros nb B Br th theta Hnb HB Hth Hc.
  apply fmax_le.
  - unfold bnorm_le in Hc. rewrite forallb_forall in Hc.
    specialize (Hc 0%nat ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
    specialize (Hc 0%nat ltac:(apply in_seq; lia)).
    assert (Hs := I.sub_correct prec th _ (Xreal theta) _ Hth
                    (isum_msum prec (fun K => irowsum prec 14 (bget B 0 K) 0) (fun K => mrow 14 (Br 0%nat K) 0) nb
                       (fun K HK => irowsum_correct prec 14 14 _ _ 0 (HB 0%nat K Hnb HK) ltac:(lia)))).
    destruct (nonneg_correct _ _ Hs Hc) as [x [Ex Hx]]. injection Ex as <-.
    assert (0 <= msum (fun K => mrow 14 (Br 0%nat K) 0) nb) by (apply msum_nonneg; intros; unfold mrow; apply msum_nonneg;
                                                               intros; apply Rabs_pos).
    lra.
  - intros j Hj. destruct (flat_split nb j Hj) as [I [r [HI [Hr ->]]]].
    rewrite mrow_flat by exact Hr.
    unfold bnorm_le in Hc. rewrite forallb_forall in Hc.
    specialize (Hc I ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
    specialize (Hc r ltac:(apply in_seq; lia)).
    assert (Hs := I.sub_correct prec th _ (Xreal theta) _ Hth
                    (isum_msum prec (fun K => irowsum prec 14 (bget B I K) r) (fun K => mrow 14 (Br I K) r) nb
                       (fun K HK => irowsum_correct prec 14 14 _ _ r (HB I K HI HK) Hr))).
    destruct (nonneg_correct _ _ Hs Hc) as [x [Ex Hx]]. injection Ex as <-. lra.
Qed.

End Sound.
