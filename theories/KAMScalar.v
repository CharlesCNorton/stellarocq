(** The convergence of a Newton scheme that loses analyticity at each step.

    The KAM iteration corrects an approximately invariant torus by a Newton
    step whose solution is bounded on a narrower strip of complex angles than
    the error it corrects. Step n gives up a width delta_n of the strip, and
    its new error is at most C delta_n^-a times the square of the old one.
    With delta_n halving from step to step that factor grows geometrically,
    A q^n, and [kam_scalar] shows that the errors still fall
    super-exponentially once A q eps_0 <= 1/2:

      A q^(n+1) eps_n <= (A q eps_0)^(2^n).

    [kam_scalar_eps] gives eps_n <= eps_0 (2q)^-n from it, and
    [kam_scalar_sum] bounds the sum of the errors weighted by w^n, for any
    w <= q, by twice the first error: the corrections, whose own loss of
    analyticity costs such a weight, sum to a multiple of eps_0. *)

From Coq Require Import Reals Lra Lia.
Local Open Scope R_scope.

(** A sum over 0 .. n - 1. *)
Fixpoint fsum (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => fsum f k + f k end.

Lemma fsum_le (f g : nat -> R) (n : nat) :
  (forall k, (k < n)%nat -> f k <= g k) -> fsum f n <= fsum g n.
Proof.
  induction n as [| n IH]; intros H; simpl.
  - lra.
  - assert (fsum f n <= fsum g n) by (apply IH; intros k Hk; apply H; lia).
    assert (f n <= g n) by (apply H; lia).
    lra.
Qed.

Lemma fsum_half (n : nat) : fsum (fun k => (/ 2) ^ k) n = 2 - 2 * (/ 2) ^ n.
Proof.
  induction n as [| n IH]; simpl.
  - lra.
  - rewrite IH. field.
Qed.

(** Powers of a number in [0, 1] fall as the exponent grows. *)
Lemma pow_le_exp (x : R) (m n : nat) :
  0 <= x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof.
  intros Hx Hmn.
  replace n with (m + (n - m))%nat by lia.
  rewrite pow_add.
  assert (0 <= x ^ m) by (apply pow_le; lra).
  assert (Hk : forall k, 0 <= x ^ k <= 1).
  { intros k. induction k as [| k IHk]; simpl; [lra |]. nra. }
  destruct (Hk (n - m)%nat).
  nra.
Qed.

Section Scalar.

Variables A q : R.
Variable eps : nat -> R.
Hypothesis A_pos : 0 < A.
Hypothesis q_ge_1 : 1 <= q.
Hypothesis eps_nonneg : forall n, 0 <= eps n.
Hypothesis eps_step : forall n, eps (S n) <= A * q ^ n * eps n ^ 2.
Hypothesis small : A * q * eps 0 <= / 2.

Let eta0 := A * q * eps 0.

Lemma eta0_nonneg : 0 <= eta0.
Proof.
  unfold eta0. apply Rmult_le_pos; [apply Rmult_le_pos |]; auto; lra.
Qed.

Lemma scaled_nonneg (n : nat) : 0 <= A * q ^ n * eps n.
Proof.
  apply Rmult_le_pos; [apply Rmult_le_pos |]; auto.
  - lra.
  - apply pow_le; lra.
Qed.

Theorem kam_scalar (n : nat) : A * q ^ S n * eps n <= eta0 ^ (2 ^ n)%nat.
Proof.
  induction n as [| n IH].
  - unfold eta0. simpl. lra.
  - apply Rle_trans with (A * q ^ S (S n) * (A * q ^ n * eps n ^ 2)).
    { apply Rmult_le_compat_l; [| apply eps_step].
      apply Rmult_le_pos; [lra | apply pow_le; lra]. }
    replace (A * q ^ S (S n) * (A * q ^ n * eps n ^ 2))
      with ((A * q ^ S n * eps n) ^ 2) by (simpl; ring).
    replace (2 ^ S n)%nat with (2 ^ n * 2)%nat by (simpl; lia).
    rewrite pow_mult.
    apply pow_incr. split; [| exact IH].
    apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply pow_le; lra] | apply eps_nonneg].
Qed.

Theorem kam_scalar_eps (n : nat) : eps n <= eps 0 * (/ (2 * q)) ^ n.
Proof.
  pose proof (kam_scalar n) as H.
  assert (Hq : 0 < q) by lra.
  assert (Hqn : 0 < q ^ S n) by (apply pow_lt; lra).
  (* eta0^(2^n) <= eta0 (1/2)^n *)
  assert (He : eta0 ^ (2 ^ n)%nat <= eta0 * (/ 2) ^ n).
  { assert (Hp : (2 ^ n)%nat = S (2 ^ n - 1)).
    { pose proof (Nat.pow_gt_lin_r 2 n ltac:(lia)). lia. }
    rewrite Hp. simpl.
    apply Rmult_le_compat_l; [apply eta0_nonneg |].
    apply Rle_trans with ((/ 2) ^ (2 ^ n - 1)%nat).
    - apply pow_incr. pose proof eta0_nonneg. unfold eta0 in *. lra.
    - apply pow_le_exp; [lra |].
      pose proof (Nat.pow_gt_lin_r 2 n ltac:(lia)). lia. }
  assert (Hmain : A * q ^ S n * eps n <= A * q * eps 0 * (/ 2) ^ n).
  { apply Rle_trans with (eta0 ^ (2 ^ n)%nat); [exact H |]. unfold eta0 in *. exact He. }
  (* divide by A q^(n+1) *)
  assert (HA : 0 < A * q ^ S n) by (apply Rmult_lt_0_compat; lra).
  assert (Hqn' : 0 < q ^ n) by (apply pow_lt; lra).
  apply Rmult_le_reg_l with (A * q ^ S n); [exact HA |].
  apply Rle_trans with (A * q * eps 0 * (/ 2) ^ n); [exact Hmain |].
  right.
  rewrite Rinv_mult, Rpow_mult_distr, (pow_inv q n).
  change (q ^ S n) with (q * q ^ n).
  set (a := (/ 2) ^ n) in *. set (b := q ^ n) in *.
  field.
  repeat split; lra.
Qed.

Theorem kam_scalar_sum (w : R) (N : nat) :
  0 <= w <= q -> fsum (fun n => w ^ n * eps n) N <= 2 * eps 0.
Proof.
  intros Hw.
  assert (Hq : 0 < q) by lra.
  apply Rle_trans with (fsum (fun n => eps 0 * (/ 2) ^ n) N).
  - apply fsum_le. intros k _.
    apply Rle_trans with (w ^ k * (eps 0 * (/ (2 * q)) ^ k)).
    { apply Rmult_le_compat_l; [apply pow_le; lra | apply kam_scalar_eps]. }
    replace (w ^ k * (eps 0 * (/ (2 * q)) ^ k))
      with (eps 0 * (w * / (2 * q)) ^ k) by (rewrite Rpow_mult_distr; ring).
    apply Rmult_le_compat_l; [apply eps_nonneg |].
    apply pow_incr. split.
    + apply Rmult_le_pos; [lra |]. apply Rlt_le, Rinv_0_lt_compat. lra.
    + apply Rmult_le_reg_l with (2 * q); [lra |].
      replace (2 * q * (w * / (2 * q))) with w by (field; lra).
      lra.
  - assert (Hs : fsum (fun n => eps 0 * (/ 2) ^ n) N = eps 0 * fsum (fun n => (/ 2) ^ n) N).
    { clear. induction N as [| N IH]; simpl; [ring | rewrite IH; ring]. }
    rewrite Hs, fsum_half.
    assert (0 <= (/ 2) ^ N) by (apply pow_le; lra).
    pose proof (eps_nonneg 0). nra.
Qed.

End Scalar.
