(** Sums over Z x Z as limits of partial sums over squares.

    [sqsum g (S N)] is [sqsum g N] plus the layer of modes with max(|m|, |n|)
    = N + 1 ([sqsum_S]), whose absolute value is at most the layer of |g|
    ([layer_abs]). So when every partial sum of |g| is at most M, the partial
    sums of |g| rise to a limit, the partial sums of g form a Cauchy sequence
    ([sqsum_cauchy]), and [zz_sum g], their limit, exists and is at most M in
    absolute value ([zz_sum_bound]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier.
Local Open Scope R_scope.

Lemma zsum_abs (f : Z -> R) (N : nat) : Rabs (zsum f N) <= zsum (fun m => Rabs (f m)) N.
Proof.
  induction N as [| N IH]; [rewrite !zsum_0; lra |].
  rewrite !zsum_S.
  eapply Rle_trans; [apply Rabs_triang |].
  eapply Rplus_le_compat; [exact IH |].
  eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma zsum_nonneg (f : Z -> R) (N : nat) : (forall m, 0 <= f m) -> 0 <= zsum f N.
Proof.
  intros H. induction N as [| N IH]; [rewrite zsum_0; apply H |].
  rewrite zsum_S. pose proof (H (Z.of_nat (S N))). pose proof (H (- Z.of_nat (S N))%Z). lra.
Qed.

(** The modes with max(|m|, |n|) = N + 1. *)
Definition layer (g : Z -> Z -> R) (N : nat) : R :=
  let s := Z.of_nat (S N) in
  zsum (g s) N + zsum (g (- s)%Z) N + zsum (fun m => g m s + g m (- s)%Z) (S N).

Lemma sqsum_S (g : Z -> Z -> R) (N : nat) : sqsum g (S N) = sqsum g N + layer g N.
Proof.
  unfold sqsum, layer.
  set (s := Z.of_nat (S N)).
  rewrite (zsum_ext (fun m => zsum (fun n => g m n) (S N))
                    (fun m => zsum (fun n => g m n) N + (g m s + g m (- s)%Z))).
  2: { intros m. rewrite zsum_S. reflexivity. }
  rewrite zsum_plus, zsum_S.
  fold s.
  replace (zsum (fun n => g s n) N) with (zsum (g s) N) by reflexivity.
  replace (zsum (fun n => g (- s)%Z n) N) with (zsum (g (- s)%Z) N) by reflexivity.
  ring.
Qed.

Definition absf (g : Z -> Z -> R) : Z -> Z -> R := fun m n => Rabs (g m n).

Lemma layer_abs (g : Z -> Z -> R) (N : nat) : Rabs (layer g N) <= layer (absf g) N.
Proof.
  unfold layer, absf.
  set (s := Z.of_nat (S N)).
  eapply Rle_trans; [apply Rabs_triang |].
  apply Rplus_le_compat.
  - eapply Rle_trans; [apply Rabs_triang |].
    apply Rplus_le_compat; apply zsum_abs.
  - eapply Rle_trans; [apply zsum_abs |].
    apply zsum_le. intros m. apply Rabs_triang.
Qed.

Lemma layer_nonneg (g : Z -> Z -> R) (N : nat) : 0 <= layer (absf g) N.
Proof.
  eapply Rle_trans; [apply Rabs_pos | apply layer_abs].
Qed.

Lemma sqsum_abs_step (g : Z -> Z -> R) (N : nat) :
  sqsum (absf g) N <= sqsum (absf g) (S N).
Proof. rewrite sqsum_S. pose proof (layer_nonneg g N). lra. Qed.

(** The partial sums of g move by no more than those of |g|. *)
Lemma sqsum_diff (g : Z -> Z -> R) (N k : nat) :
  Rabs (sqsum g (N + k) - sqsum g N) <= sqsum (absf g) (N + k) - sqsum (absf g) N.
Proof.
  induction k as [| k IH].
  - rewrite Nat.add_0_r. unfold Rminus. rewrite !Rplus_opp_r, Rabs_R0. lra.
  - replace (N + S k)%nat with (S (N + k)) by lia.
    rewrite !sqsum_S.
    replace (sqsum g (N + k) + layer g (N + k) - sqsum g N)
      with ((sqsum g (N + k) - sqsum g N) + layer g (N + k)) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    pose proof (layer_abs g (N + k)). lra.
Qed.

(** Every partial sum of |g| is at most M. *)
Definition abs_summable (g : Z -> Z -> R) (M : R) : Prop :=
  forall N, sqsum (absf g) N <= M.

Lemma sqsum_abs_cv (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> ex_finite_lim_seq (fun N => sqsum (absf g) N).
Proof.
  intros H. apply ex_finite_lim_seq_incr with M.
  - intros n. apply sqsum_abs_step.
  - exact H.
Qed.

Lemma sqsum_abs_mono (g : Z -> Z -> R) (N N' : nat) :
  (N <= N')%nat -> sqsum (absf g) N <= sqsum (absf g) N'.
Proof.
  intros H. replace N' with (N + (N' - N))%nat by lia.
  generalize (N' - N)%nat as k. intros k.
  induction k as [| k IH]; [rewrite Nat.add_0_r; lra |].
  replace (N + S k)%nat with (S (N + k)) by lia.
  eapply Rle_trans; [exact IH | apply sqsum_abs_step].
Qed.

Theorem sqsum_cauchy (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> ex_finite_lim_seq (fun N => sqsum g N).
Proof.
  intros H. apply ex_lim_seq_cauchy_corr.
  pose proof (sqsum_abs_cv g M H) as Hcv.
  apply ex_lim_seq_cauchy_corr in Hcv.
  intros eps. destruct (Hcv eps) as [N0 HN0].
  exists N0. intros n m Hn Hm.
  destruct (Nat.le_ge_cases n m) as [Hnm | Hnm].
  - replace m with (n + (m - n))%nat by lia.
    rewrite Rabs_minus_sym.
    eapply Rle_lt_trans; [apply sqsum_diff |].
    specialize (HN0 (n + (m - n))%nat n ltac:(lia) Hn).
    eapply Rle_lt_trans; [apply Rle_abs | exact HN0].
  - replace n with (m + (n - m))%nat by lia.
    eapply Rle_lt_trans; [apply sqsum_diff |].
    specialize (HN0 (m + (n - m))%nat m ltac:(lia) Hm).
    eapply Rle_lt_trans; [apply Rle_abs | exact HN0].
Qed.

(** The sum over Z x Z. *)
Definition zz_sum (g : Z -> Z -> R) : R := real (Lim_seq (fun N => sqsum g N)).

Lemma zz_sum_is_lim (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> is_lim_seq (fun N => sqsum g N) (zz_sum g).
Proof.
  intros H. destruct (sqsum_cauchy g M H) as [l Hl].
  unfold zz_sum. rewrite (is_lim_seq_unique _ _ Hl). exact Hl.
Qed.

Lemma sqsum_abs (g : Z -> Z -> R) (N : nat) : Rabs (sqsum g N) <= sqsum (absf g) N.
Proof.
  unfold sqsum, absf. eapply Rle_trans; [apply zsum_abs |].
  apply zsum_le. intros m. apply zsum_abs.
Qed.

Theorem zz_sum_bound (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> Rabs (zz_sum g) <= M.
Proof.
  intros H.
  pose proof (zz_sum_is_lim g M H) as Hl.
  assert (HN : forall N, Rabs (sqsum g N) <= M).
  { intros N. eapply Rle_trans; [apply sqsum_abs | apply H]. }
  apply Rabs_le. split.
  - apply (is_lim_seq_le (fun _ => - M) (fun N => sqsum g N) (- M) (zz_sum g)).
    + intros N. pose proof (HN N) as HNN. apply Rabs_le_between in HNN. lra.
    + apply is_lim_seq_const.
    + exact Hl.
  - apply (is_lim_seq_le (fun N => sqsum g N) (fun _ => M) (zz_sum g) M).
    + intros N. pose proof (HN N) as HNN. apply Rabs_le_between in HNN. lra.
    + exact Hl.
    + apply is_lim_seq_const.
Qed.
