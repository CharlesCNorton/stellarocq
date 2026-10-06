(** Products of coefficient families.

    The product of a cos(k.x) + b sin(k.x) and a' cos(l.x) + b' sin(l.x)
    splits by the product-to-sum formulas into modes k + l and k - l, so the
    coefficients of a product are the convolutions

      conv_p f g j = sum_k f_k g_(j-k)    and    conv_m f g j = sum_k f_k g_(k-j)

    of the coefficient families ([fmul]). A partial sum over a square of a
    family shifted by k is at most a partial sum over a larger square
    ([sqsum_shift]), which with |j| <= |k| + |j - k| gives the Banach algebra
    bound |u v|_rho <= |u|_rho |v|_rho ([nbound_fmul]) on every strip rho >= 0. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval.
Local Open Scope R_scope.

(** * Sums over integer intervals *)

(** f a + f (a + 1) + ... + f (a + n - 1). *)
Fixpoint isum (f : Z -> R) (a : Z) (n : nat) : R :=
  match n with O => 0 | S k => f a + isum f (a + 1)%Z k end.

Lemma isum_0 (f : Z -> R) (a : Z) : isum f a 0 = 0.
Proof. reflexivity. Qed.

Lemma isum_cons (f : Z -> R) (a : Z) (n : nat) : isum f a (S n) = f a + isum f (a + 1)%Z n.
Proof. reflexivity. Qed.

Lemma isum_snoc (f : Z -> R) (a : Z) (n : nat) :
  isum f a (S n) = isum f a n + f (a + Z.of_nat n)%Z.
Proof.
  revert a. induction n as [| n IH]; intros a.
  - rewrite isum_cons, !isum_0. replace (a + Z.of_nat 0)%Z with a by lia. ring.
  - rewrite isum_cons, IH, isum_cons.
    replace (a + 1 + Z.of_nat n)%Z with (a + Z.of_nat (S n))%Z by lia. ring.
Qed.

Lemma isum_app (f : Z -> R) (a : Z) (n k : nat) :
  isum f a (n + k) = isum f a n + isum f (a + Z.of_nat n)%Z k.
Proof.
  revert a. induction n as [| n IH]; intros a.
  - rewrite Nat.add_0_l, isum_0. replace (a + Z.of_nat 0)%Z with a by lia. ring.
  - rewrite Nat.add_succ_l, !isum_cons, IH.
    replace (a + 1 + Z.of_nat n)%Z with (a + Z.of_nat (S n))%Z by lia. ring.
Qed.

Lemma isum_nonneg (f : Z -> R) (a : Z) (n : nat) :
  (forall m, 0 <= f m) -> 0 <= isum f a n.
Proof.
  intros H. revert a. induction n as [| n IH]; intros a; simpl; [lra |].
  pose proof (H a). pose proof (IH (a + 1)%Z). lra.
Qed.

Lemma isum_ext (f g : Z -> R) (a : Z) (n : nat) :
  (forall m, f m = g m) -> isum f a n = isum g a n.
Proof.
  intros H. revert a. induction n as [| n IH]; intros a; simpl; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

(** A sum over -N .. N is the interval sum from -N of length 2N + 1. *)
Lemma zsum_isum (f : Z -> R) (N : nat) : zsum f N = isum f (- Z.of_nat N)%Z (2 * N + 1).
Proof.
  induction N as [| N IH].
  - rewrite zsum_0. replace (2 * 0 + 1)%nat with 1%nat by lia.
    rewrite isum_cons, isum_0. replace (- Z.of_nat 0)%Z with 0%Z by lia. ring.
  - rewrite zsum_S, IH.
    replace (2 * S N + 1)%nat with (S (S (2 * N + 1))) by lia.
    rewrite isum_snoc.
    change (isum f (- Z.of_nat (S N))%Z (S (2 * N + 1)))
      with (f (- Z.of_nat (S N))%Z + isum f (- Z.of_nat (S N) + 1)%Z (2 * N + 1)).
    replace (- Z.of_nat (S N) + 1)%Z with (- Z.of_nat N)%Z by lia.
    replace (- Z.of_nat (S N) + Z.of_nat (S (2 * N + 1)))%Z with (Z.of_nat (S N)) by lia.
    ring.
Qed.

(** A sum over an interval inside a longer one is at most the longer sum. *)
Lemma isum_sub (f : Z -> R) (a b : Z) (n n' : nat) :
  (forall m, 0 <= f m) -> (b <= a)%Z -> (a + Z.of_nat n <= b + Z.of_nat n')%Z ->
  isum f a n <= isum f b n'.
Proof.
  intros Hf Hba Hend.
  set (d := Z.to_nat (a - b)).
  assert (Hd : a = (b + Z.of_nat d)%Z) by (unfold d; rewrite Z2Nat.id; lia).
  assert (Hn' : (d + n <= n')%nat).
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_add. lia. }
  replace n' with (d + n + (n' - (d + n)))%nat by lia.
  rewrite !isum_app. rewrite <- Hd.
  pose proof (isum_nonneg f b d Hf).
  pose proof (isum_nonneg f (b + Z.of_nat (d + n))%Z (n' - (d + n)) Hf).
  lra.
Qed.

Lemma zsum_shift (f : Z -> R) (c : Z) (N : nat) :
  (forall m, 0 <= f m) ->
  zsum (fun m => f (m - c)%Z) N <= zsum f (N + Z.to_nat (Z.abs c)).
Proof.
  intros Hf.
  rewrite !zsum_isum.
  (* shift the interval of the left side back by c *)
  assert (Hs : forall a n, isum (fun m => f (m - c)%Z) a n = isum f (a - c)%Z n).
  { intros a n. revert a. induction n as [| n IH]; intros a; simpl; [reflexivity |].
    rewrite IH. replace (a + 1 - c)%Z with (a - c + 1)%Z by lia. reflexivity. }
  rewrite Hs.
  apply isum_sub; [exact Hf | lia | lia].
Qed.

Lemma sqsum_nonneg (f : Z -> Z -> R) (N : nat) :
  (forall m n, 0 <= f m n) -> 0 <= sqsum f N.
Proof.
  intros H. unfold sqsum. apply zsum_nonneg. intros m. apply zsum_nonneg. intros n. apply H.
Qed.

Lemma zsum_mono_N (f : Z -> R) (N N' : nat) :
  (forall m, 0 <= f m) -> (N <= N')%nat -> zsum f N <= zsum f N'.
Proof.
  intros Hf H. replace N' with (N + (N' - N))%nat by lia.
  generalize (N' - N)%nat as k. intros k.
  induction k as [| k IH]; [rewrite Nat.add_0_r; lra |].
  replace (N + S k)%nat with (S (N + k)) by lia.
  rewrite zsum_S. pose proof (Hf (Z.of_nat (S (N + k)))). pose proof (Hf (- Z.of_nat (S (N + k)))%Z).
  lra.
Qed.

(** A partial sum of a family shifted by (c, d) is at most a partial sum over a
    larger square. *)
Lemma sqsum_shift (f : Z -> Z -> R) (c d : Z) (N : nat) :
  (forall m n, 0 <= f m n) ->
  sqsum (fun m n => f (m - c)%Z (n - d)%Z) N
    <= sqsum f (N + Z.to_nat (Z.abs c) + Z.to_nat (Z.abs d)).
Proof.
  intros Hf. unfold sqsum.
  set (N' := (N + Z.to_nat (Z.abs c) + Z.to_nat (Z.abs d))%nat).
  apply Rle_trans with (zsum (fun m => zsum (fun n => f (m - c)%Z n) N') N).
  - apply zsum_le. intros m.
    apply Rle_trans with (zsum (fun n => f (m - c)%Z n) (N + Z.to_nat (Z.abs d))).
    + apply zsum_shift. intros n. apply Hf.
    + apply zsum_mono_N; [intros; apply Hf | unfold N'; lia].
  - apply Rle_trans with (zsum (fun m => zsum (fun n => f m n) N') (N + Z.to_nat (Z.abs c))).
    + apply (zsum_shift (fun m => zsum (fun n => f m n) N')).
      intros m. apply zsum_nonneg. intros n. apply Hf.
    + apply zsum_mono_N; [| unfold N'; lia].
      intros m. apply zsum_nonneg. intros n. apply Hf.
Qed.

(** One term of a nonnegative family is at most a partial sum containing it. *)
Lemma zsum_single (g : Z -> R) (k : Z) (N : nat) :
  (forall x, 0 <= g x) -> (Z.abs k <= Z.of_nat N)%Z -> g k <= zsum g N.
Proof.
  intros Hg. induction N as [| N IH]; intros Hk.
  - rewrite zsum_0. replace k with 0%Z by lia. lra.
  - rewrite zsum_S.
    pose proof (Hg (Z.of_nat (S N))). pose proof (Hg (- Z.of_nat (S N))%Z).
    destruct (Z.le_gt_cases (Z.abs k) (Z.of_nat N)) as [Hle | Hgt].
    + pose proof (IH Hle). lra.
    + assert (Hks : k = Z.of_nat (S N) \/ k = (- Z.of_nat (S N))%Z) by lia.
      pose proof (zsum_nonneg g N Hg).
      destruct Hks as [-> | ->]; lra.
Qed.

Lemma single_le_sqsum (f : Z -> Z -> R) (m n : Z) (N : nat) :
  (forall m n, 0 <= f m n) ->
  (Z.abs m <= Z.of_nat N)%Z -> (Z.abs n <= Z.of_nat N)%Z -> f m n <= sqsum f N.
Proof.
  intros Hf Hm Hn. unfold sqsum.
  apply Rle_trans with (zsum (fun n' => f m n') N).
  - apply (zsum_single (fun n' => f m n')); [intros; apply Hf | exact Hn].
  - apply (zsum_single (fun m' => zsum (fun n' => f m' n') N)); [| exact Hm].
    intros x. apply zsum_nonneg. intros y. apply Hf.
Qed.

(** * Sums over Z x Z: linearity, order, absolute values *)

Lemma absf_plus_le (g h : Z -> Z -> R) (m n : Z) :
  absf (fun m n => g m n + h m n) m n <= absf g m n + absf h m n.
Proof. unfold absf. apply Rabs_triang. Qed.

Lemma summable_plus (g h : Z -> Z -> R) (Mg Mh : R) :
  abs_summable g Mg -> abs_summable h Mh ->
  abs_summable (fun m n => g m n + h m n) (Mg + Mh).
Proof.
  intros Hg Hh N.
  apply Rle_trans with (sqsum (fun m n => absf g m n + absf h m n) N).
  - apply sqsum_le. intros m n. apply absf_plus_le.
  - rewrite sqsum_plus. pose proof (Hg N). pose proof (Hh N). lra.
Qed.

Lemma summable_scal (c : R) (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> abs_summable (fun m n => c * g m n) (Rabs c * M).
Proof.
  intros Hg N.
  apply Rle_trans with (sqsum (fun m n => Rabs c * absf g m n) N).
  - apply sqsum_le. intros m n. unfold absf. rewrite Rabs_mult. lra.
  - rewrite sqsum_scal. apply Rmult_le_compat_l; [apply Rabs_pos | apply Hg].
Qed.

Lemma summable_dom (g h : Z -> Z -> R) (M : R) :
  (forall m n, Rabs (g m n) <= h m n) -> abs_summable h M -> abs_summable g M.
Proof.
  intros Hd Hh N. eapply Rle_trans; [| apply (Hh N)].
  apply sqsum_le. intros m n. unfold absf.
  pose proof (Hd m n). pose proof (Rle_abs (h m n)). lra.
Qed.

Lemma zz_sum_plus (g h : Z -> Z -> R) (Mg Mh : R) :
  abs_summable g Mg -> abs_summable h Mh ->
  zz_sum (fun m n => g m n + h m n) = zz_sum g + zz_sum h.
Proof.
  intros Hg Hh.
  pose proof (zz_sum_is_lim _ _ (summable_plus g h Mg Mh Hg Hh)) as H.
  assert (H' : is_lim_seq (fun N => sqsum (fun m n => g m n + h m n) N) (zz_sum g + zz_sum h)).
  { eapply is_lim_seq_ext.
    - intros N. symmetry. apply sqsum_plus.
    - apply is_lim_seq_plus'; [apply (zz_sum_is_lim g Mg Hg) | apply (zz_sum_is_lim h Mh Hh)]. }
  pose proof (is_lim_seq_unique _ _ H) as U1.
  pose proof (is_lim_seq_unique _ _ H') as U2.
  rewrite U1 in U2. injection U2. auto.
Qed.

Lemma zz_sum_scal (c : R) (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> zz_sum (fun m n => c * g m n) = c * zz_sum g.
Proof.
  intros Hg.
  pose proof (zz_sum_is_lim _ _ (summable_scal c g M Hg)) as H.
  assert (H' : is_lim_seq (fun N => sqsum (fun m n => c * g m n) N) (c * zz_sum g)).
  { eapply is_lim_seq_ext.
    - intros N. symmetry. apply sqsum_scal.
    - apply (is_lim_seq_mult' (fun _ => c) (fun N => sqsum g N) c (zz_sum g)).
      + apply is_lim_seq_const.
      + apply (zz_sum_is_lim g M Hg). }
  pose proof (is_lim_seq_unique _ _ H) as U1.
  pose proof (is_lim_seq_unique _ _ H') as U2.
  rewrite U1 in U2. injection U2. auto.
Qed.

Lemma zz_sum_le (g h : Z -> Z -> R) (Mg Mh : R) :
  abs_summable g Mg -> abs_summable h Mh ->
  (forall m n, g m n <= h m n) -> zz_sum g <= zz_sum h.
Proof.
  intros Hg Hh H.
  apply (is_lim_seq_le (fun N => sqsum g N) (fun N => sqsum h N) (zz_sum g) (zz_sum h)).
  - intros N. apply sqsum_le, H.
  - apply (zz_sum_is_lim g Mg Hg).
  - apply (zz_sum_is_lim h Mh Hh).
Qed.

Lemma summable_absf (g : Z -> Z -> R) (M : R) : abs_summable g M -> abs_summable (absf g) M.
Proof.
  intros Hg N. eapply Rle_trans; [| apply (Hg N)].
  apply sqsum_le. intros m n. unfold absf. rewrite Rabs_Rabsolu. lra.
Qed.

Lemma zz_sum_abs (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> Rabs (zz_sum g) <= zz_sum (absf g).
Proof.
  intros Hg. pose proof (summable_absf g M Hg) as Ha.
  apply Rabs_le. split.
  - replace (- zz_sum (absf g)) with (zz_sum (fun m n => -1 * absf g m n))
      by (rewrite (zz_sum_scal (-1) (absf g) M Ha); ring).
    apply (zz_sum_le _ _ (Rabs (-1) * M) M); [apply summable_scal, Ha | exact Hg |].
    intros m n. unfold absf. pose proof (Rle_abs (- g m n)). rewrite Rabs_Ropp in H. lra.
  - apply (zz_sum_le _ _ M M); [exact Hg | exact Ha |].
    intros m n. unfold absf. apply Rle_abs.
Qed.

Lemma zz_sum_nonneg_bound (g : Z -> Z -> R) (M : R) :
  (forall m n, 0 <= g m n) -> (forall N, sqsum g N <= M) -> zz_sum g <= M.
Proof.
  intros H0 HM.
  assert (Hs : abs_summable g M).
  { intros N. eapply Rle_trans; [| apply (HM N)].
    apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply H0. lra. }
  pose proof (zz_sum_bound g M Hs). pose proof (Rle_abs (zz_sum g)). lra.
Qed.
