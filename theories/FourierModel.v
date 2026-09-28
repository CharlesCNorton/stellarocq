(** The norm of a family from its values on a grid.

    Let u be canonical with norm at most Mw on a strip w' at least as wide as
    w. On the grid of N1 x N2 points, the transforms [dftc] and [dfts] at a
    mode of the box |k| <= K1, |l| <= K2, with 2 K1 < N1 and 2 K2 < N2,
    differ from u's coefficients by the coefficients aliased onto that mode,
    whose sizes |m| + kappa |n| are all at least [dal] = min(N1 - K1,
    kappa (N2 - K2)), so by at most Mw e^(-w' dal) ([dftc_err], [dfts_err]).
    Outside the box every mode has size at least [sout] = min(K1 + 1,
    kappa (K2 + 1)) and so weighs at most e^(-(w' - w) sout) of its weight on
    the wider strip ([out_box]). The norm of u on the strip w is therefore at
    most the weighted sum of its transforms over the box, plus twice the
    aliasing bound times the weights of the box, plus the tail
    ([nbound_model]). *)

From Coq Require Import ZArith Reals Lra Lia Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierDFT FourierCanon.
Local Open Scope R_scope.

(** The box |k| <= K1, |l| <= K2 and sums over it. *)
Definition in_box (K1 K2 : nat) (k l : Z) : bool :=
  (Z.leb (Z.abs k) (Z.of_nat K1) && Z.leb (Z.abs l) (Z.of_nat K2))%bool.

Definition bsum (K1 K2 : nat) (f : Z -> Z -> R) : R := zsum (fun k => zsum (fun l => f k l) K2) K1.

Definition dal (N1 N2 K1 K2 : nat) : R := Rmin (INR N1 - INR K1) (kappa * (INR N2 - INR K2)).
Definition sout (K1 K2 : nat) : R := Rmin (INR K1 + 1) (kappa * (INR K2 + 1)).

(** * Sums of functions carried by a range *)

Lemma zsum_carried (f : Z -> R) (K N : nat) :
  (forall m, 0 <= f m) -> (forall m, (Z.of_nat K < Z.abs m)%Z -> f m = 0) -> zsum f N <= zsum f K.
Proof.
  intros H0 Hc. destruct (Nat.le_ge_cases N K) as [HNK | HKN].
  - apply zsum_mono_N; assumption.
  - replace N with (K + (N - K))%nat by lia. generalize (N - K)%nat as j. intros j.
    induction j as [| j IH]; [rewrite Nat.add_0_r; lra |].
    replace (K + S j)%nat with (S (K + j)) by lia. rewrite zsum_S.
    rewrite (Hc (Z.of_nat (S (K + j)))) by lia. rewrite (Hc (- Z.of_nat (S (K + j)))%Z) by lia. lra.
Qed.

Lemma zsum_nonneg' (f : Z -> R) (N : nat) : (forall m, 0 <= f m) -> 0 <= zsum f N.
Proof. apply zsum_nonneg. Qed.

(** A nonnegative function carried by the box sums over any square to at most
    its sum over the box. *)
Lemma sqsum_box (f : Z -> Z -> R) (K1 K2 N : nat) :
  (forall m n, 0 <= f m n) -> (forall m n, in_box K1 K2 m n = false -> f m n = 0) ->
  sqsum f N <= bsum K1 K2 f.
Proof.
  intros H0 Hc. unfold sqsum, bsum.
  apply Rle_trans with (zsum (fun m => zsum (fun n => f m n) N) K1).
  - apply zsum_carried.
    + intros m. apply zsum_nonneg. intros n. apply H0.
    + intros m Hm. rewrite (zsum_ext _ (fun _ => 0)).
      * rewrite (zsum_ext _ (fun _ => 0 * 0)) by (intros; ring). rewrite zsum_scal. ring.
      * intros n. apply Hc. unfold in_box.
        destruct (Z.leb_spec (Z.abs m) (Z.of_nat K1)); [lia | reflexivity].
  - apply zsum_le. intros m. apply zsum_carried.
    + intros n. apply H0.
    + intros n Hn. apply Hc. unfold in_box.
      destruct (Z.leb (Z.abs m) (Z.of_nat K1)); [| reflexivity].
      destruct (Z.leb_spec (Z.abs n) (Z.of_nat K2)); [lia | reflexivity].
Qed.

Lemma bsum_le (f g : Z -> Z -> R) (K1 K2 : nat) :
  (forall m n, in_box K1 K2 m n = true -> f m n <= g m n) -> bsum K1 K2 f <= bsum K1 K2 g.
Proof.
  intros H. unfold bsum.
  (* compare term by term inside the box *)
  assert (Hz : forall (a b : Z -> R) (K : nat),
             (forall m, (Z.abs m <= Z.of_nat K)%Z -> a m <= b m) -> zsum a K <= zsum b K).
  { intros a b K Hab. induction K as [| K IH].
    - rewrite !zsum_0. apply Hab. simpl. lia.
    - rewrite !zsum_S. pose proof (Hab (Z.of_nat (S K)) ltac:(lia)).
      pose proof (Hab (- Z.of_nat (S K))%Z ltac:(lia)).
      assert (zsum a K <= zsum b K) by (apply IH; intros m Hm; apply Hab; lia). lra. }
  apply Hz. intros m Hm. apply Hz. intros n Hn. apply H.
  unfold in_box. apply andb_true_intro. split; apply Z.leb_le; assumption.
Qed.

Lemma bsum_plus (f g : Z -> Z -> R) (K1 K2 : nat) :
  bsum K1 K2 (fun m n => f m n + g m n) = bsum K1 K2 f + bsum K1 K2 g.
Proof.
  unfold bsum. rewrite <- zsum_plus. apply zsum_ext. intros m. apply zsum_plus.
Qed.

Lemma bsum_scal (c : R) (f : Z -> Z -> R) (K1 K2 : nat) :
  bsum K1 K2 (fun m n => c * f m n) = c * bsum K1 K2 f.
Proof.
  unfold bsum. rewrite <- zsum_scal. apply zsum_ext. intros m. apply zsum_scal.
Qed.

(** * Aliasing onto the box *)

Lemma alias_in_box (N1 N2 K1 K2 : nat) (k l m n : Z) :
  (0 < N1)%nat -> (0 < N2)%nat ->
  (Z.abs k <= Z.of_nat K1)%Z -> (Z.abs l <= Z.of_nat K2)%Z ->
  (Z.abs m < Z.of_nat N1 - Z.of_nat K1)%Z -> (Z.abs n < Z.of_nat N2 - Z.of_nat K2)%Z ->
  alias N1 N2 (m - k) (n - l) = at2 k l 1 m n /\ alias N1 N2 (m + k) (n + l) = at2 (- k) (- l) 1 m n.
Proof.
  intros H1 H2 Hk Hl Hm Hn. unfold alias, at2.
  rewrite (dvd_small N1 (m - k)), (dvd_small N2 (n - l)), (dvd_small N1 (m + k)), (dvd_small N2 (n + l))
    by (assumption || lia).
  split.
  - destruct (Z.eqb_spec (m - k) 0); destruct (Z.eqb_spec (n - l) 0);
      destruct (Z.eqb_spec m k); destruct (Z.eqb_spec n l); simpl; try lia; ring.
  - destruct (Z.eqb_spec (m + k) 0); destruct (Z.eqb_spec (n + l) 0);
      destruct (Z.eqb_spec m (- k)); destruct (Z.eqb_spec n (- l)); simpl; try lia; ring.
Qed.

(** Modes smaller than [dal] lie in the square where aliasing onto the box is
    trivial. *)
Lemma small_mode (N1 N2 K1 K2 : nat) (m n : Z) :
  msize m n < dal N1 N2 K1 K2 ->
  (Z.abs m < Z.of_nat N1 - Z.of_nat K1)%Z /\ (Z.abs n < Z.of_nat N2 - Z.of_nat K2)%Z.
Proof.
  unfold msize, dal. intros H.
  pose proof (Rmin_l (INR N1 - INR K1) (kappa * (INR N2 - INR K2))) as H1.
  pose proof (Rmin_r (INR N1 - INR K1) (kappa * (INR N2 - INR K2))) as H2.
  pose proof (Rabs_pos (IZR m)) as Pm. pose proof (kappa_abs_nonneg n) as Pn. pose proof kappa_pos as Hk.
  split.
  - apply lt_IZR. rewrite minus_IZR, <- !INR_IZR_INZ, abs_IZR. lra.
  - apply lt_IZR. rewrite minus_IZR, <- !INR_IZR_INZ, abs_IZR.
    apply (Rmult_lt_reg_l kappa); [exact Hk |]. lra.
Qed.

Section Alias.

Variables (N1 N2 K1 K2 : nat) (u : fser) (w' Mw : R).
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HN2 : (0 < N2)%nat.
Hypothesis Hw' : 0 <= w'.
Hypothesis Hu : nbound w' Mw u.

Let Hu0 : nbound 0 Mw u.
Proof. apply (nbound_mono w'); assumption. Qed.

(** A coefficient function with weights of size at most one that vanish
    below [dal] sums against u to at most Mw e^(-w' dal). *)
Lemma far_sum (sel : fser -> Z -> Z -> R) (v : Z -> Z -> R) :
  (sel = fc \/ sel = fs) -> (forall m n, Rabs (v m n) <= 1) ->
  (forall m n, msize m n < dal N1 N2 K1 K2 -> v m n = 0) ->
  Rabs (zz_sum (fun m n => sel u m n * v m n)) <= Mw * exp (- (w' * dal N1 N2 K1 K2)).
Proof.
  intros Hsel Hv H0. apply zz_sum_bound.
  apply (summable_dom _ (fun m n => nterm w' u m n * exp (- (w' * dal N1 N2 K1 K2)))).
  - intros m n. rewrite Rabs_mult.
    destruct (Rlt_le_dec (msize m n) (dal N1 N2 K1 K2)) as [Hs | Hs].
    + rewrite (H0 m n Hs), Rabs_R0, Rmult_0_r.
      apply Rmult_le_pos; [apply nterm_nonneg | apply Rlt_le, exp_pos].
    + unfold nterm, wt. rewrite Rmult_assoc, <- exp_plus.
      assert (He : 1 <= exp (w' * msize m n + - (w' * dal N1 N2 K1 K2))).
      { rewrite <- exp_0. apply exp_mono. pose proof (Rmult_le_compat_l w' _ _ Hw' Hs). lra. }
      pose proof (Hv m n). pose proof (Rabs_pos (v m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)).
      destruct Hsel as [-> | ->]; nra.
  - intros K. unfold absf.
    rewrite (sqsum_ext _ (fun m n => exp (- (w' * dal N1 N2 K1 K2)) * nterm w' u m n)).
    + rewrite sqsum_scal. rewrite Rmult_comm. apply Rmult_le_compat_r; [apply Rlt_le, exp_pos | apply Hu].
    + intros m n. rewrite Rabs_pos_eq; [ring |].
      apply Rmult_le_pos; [apply nterm_nonneg | apply Rlt_le, exp_pos].
Qed.

(** The same with any size D in place of [dal]. *)
Lemma far_sum_D (D : R) (sel : fser -> Z -> Z -> R) (v : Z -> Z -> R) :
  (sel = fc \/ sel = fs) -> (forall m n, Rabs (v m n) <= 1) ->
  (forall m n, msize m n < D -> v m n = 0) ->
  Rabs (zz_sum (fun m n => sel u m n * v m n)) <= Mw * exp (- (w' * D)).
Proof.
  intros Hsel Hv H0. apply zz_sum_bound.
  apply (summable_dom _ (fun m n => nterm w' u m n * exp (- (w' * D)))).
  - intros m n. rewrite Rabs_mult.
    destruct (Rlt_le_dec (msize m n) D) as [Hs | Hs].
    + rewrite (H0 m n Hs), Rabs_R0, Rmult_0_r.
      apply Rmult_le_pos; [apply nterm_nonneg | apply Rlt_le, exp_pos].
    + unfold nterm, wt. rewrite Rmult_assoc, <- exp_plus.
      assert (He : 1 <= exp (w' * msize m n + - (w' * D))).
      { rewrite <- exp_0. apply exp_mono. pose proof (Rmult_le_compat_l w' _ _ Hw' Hs). lra. }
      pose proof (Hv m n). pose proof (Rabs_pos (v m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)).
      destruct Hsel as [-> | ->]; nra.
  - intros K. unfold absf.
    rewrite (sqsum_ext _ (fun m n => exp (- (w' * D)) * nterm w' u m n)).
    + rewrite sqsum_scal. rewrite Rmult_comm. apply Rmult_le_compat_r; [apply Rlt_le, exp_pos | apply Hu].
    + intros m n. rewrite Rabs_pos_eq; [ring |].
      apply Rmult_le_pos; [apply nterm_nonneg | apply Rlt_le, exp_pos].
Qed.

Theorem dftc_err (k l : Z) :
  (Z.abs k <= Z.of_nat K1)%Z -> (Z.abs l <= Z.of_nat K2)%Z ->
  Rabs (dftc N1 N2 u k l - ccan u k l) <= Mw * exp (- (w' * dal N1 N2 K1 K2)).
Proof.
  intros Hk Hl.
  rewrite (dftc_alias N1 N2 u Mw k l HN1 HN2 Hu0), ccan_zz.
  assert (Hal : forall j1 j2, 0 <= alias N1 N2 j1 j2 <= 1).
  { intros j1 j2. unfold alias, dvd. destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
  assert (Hat : forall a b m n, 0 <= at2 a b 1 m n <= 1).
  { intros a b m n. unfold at2. destruct (_ && _)%bool; lra. }
  assert (S1 : forall v : Z -> Z -> R, (forall m n, Rabs (v m n) <= 1) ->
                 abs_summable (fun m n => fc u m n * v m n) Mw).
  { intros v Hv. apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      pose proof (Hv m n). pose proof (Rabs_pos (v m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K. eapply Rle_trans; [| apply (Hu0 K)].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  rewrite <- (zz_sum_minus _ _ Mw Mw).
  2: { apply S1. intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
       apply Rabs_le. lra. }
  2: { apply S1. intros m n. pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n).
       apply Rabs_le. lra. }
  rewrite (zz_sum_ext _ (fun m n => fc u m n *
             (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l))
              - / 2 * (at2 k l 1 m n + at2 (- k) (- l) 1 m n))))
    by (intros; ring).
  apply (far_sum fc _ (or_introl eq_refl)).
  - intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
    pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n). apply Rabs_le. lra.
  - intros m n Hs. destruct (small_mode N1 N2 K1 K2 m n Hs) as [Hm Hn].
    destruct (alias_in_box N1 N2 K1 K2 k l m n HN1 HN2 Hk Hl Hm Hn) as [E1 E2].
    rewrite E1, E2. ring.
Qed.

Theorem dfts_err (k l : Z) :
  (Z.abs k <= Z.of_nat K1)%Z -> (Z.abs l <= Z.of_nat K2)%Z ->
  Rabs (dfts N1 N2 u k l - scan u k l) <= Mw * exp (- (w' * dal N1 N2 K1 K2)).
Proof.
  intros Hk Hl.
  rewrite (dfts_alias N1 N2 u Mw k l HN1 HN2 Hu0), scan_zz.
  assert (Hal : forall j1 j2, 0 <= alias N1 N2 j1 j2 <= 1).
  { intros j1 j2. unfold alias, dvd. destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
  assert (Hat : forall a b m n, 0 <= at2 a b 1 m n <= 1).
  { intros a b m n. unfold at2. destruct (_ && _)%bool; lra. }
  assert (S1 : forall v : Z -> Z -> R, (forall m n, Rabs (v m n) <= 1) ->
                 abs_summable (fun m n => fs u m n * v m n) Mw).
  { intros v Hv. apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      pose proof (Hv m n). pose proof (Rabs_pos (v m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K. eapply Rle_trans; [| apply (Hu0 K)].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  rewrite <- (zz_sum_minus _ _ Mw Mw).
  2: { apply S1. intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
       apply Rabs_le. lra. }
  2: { apply S1. intros m n. pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n).
       apply Rabs_le. lra. }
  rewrite (zz_sum_ext _ (fun m n => fs u m n *
             (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l))
              - / 2 * (at2 k l 1 m n - at2 (- k) (- l) 1 m n))))
    by (intros; ring).
  apply (far_sum fs _ (or_intror eq_refl)).
  - intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
    pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n). apply Rabs_le. lra.
  - intros m n Hs. destruct (small_mode N1 N2 K1 K2 m n Hs) as [Hm Hn].
    destruct (alias_in_box N1 N2 K1 K2 k l m n HN1 HN2 Hk Hl Hm Hn) as [E1 E2].
    rewrite E1, E2. ring.
Qed.

End Alias.

(** * Aliasing mode by mode

    A mode (k, l) of the grid N1 x N2 receives aliases only from modes (m, n)
    with |m| >= N1 - |k| or |n| >= N2 - |l|, so its transforms differ from its
    coefficients by at most Mw e^(-w' dmode) with dmode = min(N1 - |k|,
    kappa (N2 - |l|)) ([dftc_err_kl], [dfts_err_kl]), a bound that weighs the
    modes near the edge of the box by their own distance from their
    aliases ([nbound_model_kl]). *)

Definition dmode (N1 N2 : nat) (k l : Z) : R :=
  Rmin (INR N1 - Rabs (IZR k)) (kappa * (INR N2 - Rabs (IZR l))).

Lemma small_mode_kl (N1 N2 : nat) (k l m n : Z) :
  msize m n < dmode N1 N2 k l ->
  (Z.abs m + Z.abs k < Z.of_nat N1)%Z /\ (Z.abs n + Z.abs l < Z.of_nat N2)%Z.
Proof.
  unfold msize, dmode. intros H.
  pose proof (Rmin_l (INR N1 - Rabs (IZR k)) (kappa * (INR N2 - Rabs (IZR l)))) as H1.
  pose proof (Rmin_r (INR N1 - Rabs (IZR k)) (kappa * (INR N2 - Rabs (IZR l)))) as H2.
  pose proof (Rabs_pos (IZR m)) as Pm. pose proof (kappa_abs_nonneg n) as Pn. pose proof kappa_pos as Hk.
  split.
  - apply lt_IZR. rewrite plus_IZR, <- INR_IZR_INZ, !abs_IZR. lra.
  - apply lt_IZR. rewrite plus_IZR, <- INR_IZR_INZ, !abs_IZR.
    apply (Rmult_lt_reg_l kappa); [exact Hk |]. lra.
Qed.

Lemma alias_near (N1 N2 : nat) (k l m n : Z) :
  (0 < N1)%nat -> (0 < N2)%nat ->
  (Z.abs m + Z.abs k < Z.of_nat N1)%Z -> (Z.abs n + Z.abs l < Z.of_nat N2)%Z ->
  alias N1 N2 (m - k) (n - l) = at2 k l 1 m n /\ alias N1 N2 (m + k) (n + l) = at2 (- k) (- l) 1 m n.
Proof.
  intros H1 H2 Hm Hn. unfold alias, at2.
  rewrite (dvd_small N1 (m - k)), (dvd_small N2 (n - l)), (dvd_small N1 (m + k)), (dvd_small N2 (n + l))
    by (assumption || lia).
  split.
  - destruct (Z.eqb_spec (m - k) 0); destruct (Z.eqb_spec (n - l) 0);
      destruct (Z.eqb_spec m k); destruct (Z.eqb_spec n l); simpl; try lia; ring.
  - destruct (Z.eqb_spec (m + k) 0); destruct (Z.eqb_spec (n + l) 0);
      destruct (Z.eqb_spec m (- k)); destruct (Z.eqb_spec n (- l)); simpl; try lia; ring.
Qed.

Section AliasKL.

Variables (N1 N2 : nat) (u : fser) (w' Mw : R).
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HN2 : (0 < N2)%nat.
Hypothesis Hw' : 0 <= w'.
Hypothesis Hu : nbound w' Mw u.

Let Hu0 : nbound 0 Mw u.
Proof. apply (nbound_mono w'); assumption. Qed.

Theorem dftc_err_kl (k l : Z) :
  Rabs (dftc N1 N2 u k l - ccan u k l) <= Mw * exp (- (w' * dmode N1 N2 k l)).
Proof.
  rewrite (dftc_alias N1 N2 u Mw k l HN1 HN2 Hu0), ccan_zz.
  assert (Hal : forall j1 j2, 0 <= alias N1 N2 j1 j2 <= 1).
  { intros j1 j2. unfold alias, dvd. destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
  assert (Hat : forall a b m n, 0 <= at2 a b 1 m n <= 1).
  { intros a b m n. unfold at2. destruct (_ && _)%bool; lra. }
  assert (S1 : forall v : Z -> Z -> R, (forall m n, Rabs (v m n) <= 1) ->
                 abs_summable (fun m n => fc u m n * v m n) Mw).
  { intros v Hv. apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      pose proof (Hv m n). pose proof (Rabs_pos (v m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K. eapply Rle_trans; [| apply (Hu0 K)].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  rewrite <- (zz_sum_minus _ _ Mw Mw).
  2: { apply S1. intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
       apply Rabs_le. lra. }
  2: { apply S1. intros m n. pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n).
       apply Rabs_le. lra. }
  rewrite (zz_sum_ext _ (fun m n => fc u m n *
             (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l))
              - / 2 * (at2 k l 1 m n + at2 (- k) (- l) 1 m n))))
    by (intros; ring).
  apply (far_sum_D u w' Mw Hw' Hu (dmode N1 N2 k l) fc _ (or_introl eq_refl)).
  - intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
    pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n). apply Rabs_le. lra.
  - intros m n Hs. destruct (small_mode_kl N1 N2 k l m n Hs) as [Hm Hn].
    destruct (alias_near N1 N2 k l m n HN1 HN2 Hm Hn) as [E1 E2].
    rewrite E1, E2. ring.
Qed.

Theorem dfts_err_kl (k l : Z) :
  Rabs (dfts N1 N2 u k l - scan u k l) <= Mw * exp (- (w' * dmode N1 N2 k l)).
Proof.
  rewrite (dfts_alias N1 N2 u Mw k l HN1 HN2 Hu0), scan_zz.
  assert (Hal : forall j1 j2, 0 <= alias N1 N2 j1 j2 <= 1).
  { intros j1 j2. unfold alias, dvd. destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
  assert (Hat : forall a b m n, 0 <= at2 a b 1 m n <= 1).
  { intros a b m n. unfold at2. destruct (_ && _)%bool; lra. }
  assert (S1 : forall v : Z -> Z -> R, (forall m n, Rabs (v m n) <= 1) ->
                 abs_summable (fun m n => fs u m n * v m n) Mw).
  { intros v Hv. apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      pose proof (Hv m n). pose proof (Rabs_pos (v m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K. eapply Rle_trans; [| apply (Hu0 K)].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  rewrite <- (zz_sum_minus _ _ Mw Mw).
  2: { apply S1. intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
       apply Rabs_le. lra. }
  2: { apply S1. intros m n. pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n).
       apply Rabs_le. lra. }
  rewrite (zz_sum_ext _ (fun m n => fs u m n *
             (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l))
              - / 2 * (at2 k l 1 m n - at2 (- k) (- l) 1 m n))))
    by (intros; ring).
  apply (far_sum_D u w' Mw Hw' Hu (dmode N1 N2 k l) fs _ (or_intror eq_refl)).
  - intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
    pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n). apply Rabs_le. lra.
  - intros m n Hs. destruct (small_mode_kl N1 N2 k l m n Hs) as [Hm Hn].
    destruct (alias_near N1 N2 k l m n HN1 HN2 Hm Hn) as [E1 E2].
    rewrite E1, E2. ring.
Qed.

End AliasKL.

(** * Outside the box *)

Lemma out_size (K1 K2 : nat) (m n : Z) : in_box K1 K2 m n = false -> sout K1 K2 <= msize m n.
Proof.
  unfold in_box, sout, msize. intros H.
  pose proof (Rmin_l (INR K1 + 1) (kappa * (INR K2 + 1))) as H1.
  pose proof (Rmin_r (INR K1 + 1) (kappa * (INR K2 + 1))) as H2.
  pose proof (Rabs_pos (IZR m)) as Pm. pose proof (kappa_abs_nonneg n) as Pn. pose proof kappa_pos as Hk.
  apply andb_false_iff in H. destruct H as [H | H]; apply Z.leb_gt in H.
  - assert (E : INR K1 + 1 <= Rabs (IZR m)).
    { rewrite INR_IZR_INZ, <- abs_IZR. replace 1 with (IZR 1) by reflexivity. rewrite <- plus_IZR.
      apply IZR_le. lia. }
    lra.
  - assert (E : INR K2 + 1 <= Rabs (IZR n)).
    { rewrite INR_IZR_INZ, <- abs_IZR. replace 1 with (IZR 1) by reflexivity. rewrite <- plus_IZR.
      apply IZR_le. lia. }
    pose proof (Rmult_le_compat_l kappa _ _ (Rlt_le _ _ Hk) E). lra.
Qed.

Lemma out_box (K1 K2 : nat) (u : fser) (w w' : R) (m n : Z) :
  w <= w' -> in_box K1 K2 m n = false ->
  nterm w u m n <= exp (- ((w' - w) * sout K1 K2)) * nterm w' u m n.
Proof.
  intros Hww H. pose proof (out_size K1 K2 m n H) as Hs.
  unfold nterm, wt.
  assert (E : exp (w * msize m n) <= exp (- ((w' - w) * sout K1 K2)) * exp (w' * msize m n)).
  { rewrite <- exp_plus. apply exp_mono.
    assert (0 <= w' - w) by lra. pose proof (Rmult_le_compat_l (w' - w) _ _ H0 Hs). nra. }
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)).
  pose proof (exp_pos (w * msize m n)). nra.
Qed.

(** * The norm from the transforms *)

Theorem nbound_model (N1 N2 K1 K2 : nat) (u : fser) (w w' Mw : R) :
  (0 < N1)%nat -> (0 < N2)%nat -> 0 <= w -> w <= w' -> is_canon u -> nbound w' Mw u ->
  nbound w (bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k l) + Rabs (dfts N1 N2 u k l)) * wt w k l)
            + 2 * bsum K1 K2 (fun k l => wt w k l) * (Mw * exp (- (w' * dal N1 N2 K1 K2)))
            + exp (- ((w' - w) * sout K1 K2)) * Mw) u.
Proof.
  intros HN1 HN2 Hw Hww Cu Hu N.
  assert (Hw' : 0 <= w') by lra.
  set (inp := fun m n => if in_box K1 K2 m n then nterm w u m n else 0).
  set (outp := fun m n => if in_box K1 K2 m n then 0 else nterm w u m n).
  rewrite (sqsum_ext _ (fun m n => inp m n + outp m n))
    by (intros m n; unfold inp, outp; destruct (in_box K1 K2 m n); ring).
  rewrite sqsum_plus.
  assert (Hin : sqsum inp N <=
                bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k l) + Rabs (dfts N1 N2 u k l)) * wt w k l)
                + 2 * bsum K1 K2 (fun k l => wt w k l) * (Mw * exp (- (w' * dal N1 N2 K1 K2)))).
  { apply Rle_trans with (bsum K1 K2 inp).
    - apply sqsum_box.
      + intros m n. unfold inp. destruct (in_box K1 K2 m n); [apply nterm_nonneg | lra].
      + intros m n H. unfold inp. rewrite H. reflexivity.
    - apply Rle_trans with
        (bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k l) + Rabs (dfts N1 N2 u k l)) * wt w k l
                                 + 2 * (Mw * exp (- (w' * dal N1 N2 K1 K2))) * wt w k l)).
      2: { rewrite bsum_plus.
           replace (bsum K1 K2 (fun k l => 2 * (Mw * exp (- (w' * dal N1 N2 K1 K2))) * wt w k l))
             with (2 * (Mw * exp (- (w' * dal N1 N2 K1 K2))) * bsum K1 K2 (fun k l => wt w k l))
             by (symmetry; apply (bsum_scal _ (fun k l => wt w k l))).
           right; ring. }
      apply bsum_le. intros k l Hkl. unfold inp. rewrite Hkl.
      unfold in_box in Hkl. apply andb_prop in Hkl. destruct Hkl as [Hk Hl].
      apply Z.leb_le in Hk. apply Z.leb_le in Hl.
      pose proof (dftc_err N1 N2 K1 K2 u w' Mw HN1 HN2 Hw' Hu k l Hk Hl) as Ec.
      pose proof (dfts_err N1 N2 K1 K2 u w' Mw HN1 HN2 Hw' Hu k l Hk Hl) as Es.
      destruct Cu as [Cc Cs].
      assert (Fc : fc u k l = ccan u k l) by (unfold ccan; rewrite (Cc k l); field).
      assert (Fs : fs u k l = scan u k l) by (unfold scan; rewrite (Cs k l); field).
      unfold nterm. rewrite Fc, Fs.
      pose proof (Rabs_triang_inv (dftc N1 N2 u k l) (ccan u k l)) as T1.
      pose proof (Rabs_triang_inv (dfts N1 N2 u k l) (scan u k l)) as T2.
      rewrite Rabs_minus_sym in Ec, Es.
      pose proof (Rabs_triang (ccan u k l - dftc N1 N2 u k l) (dftc N1 N2 u k l)) as U1.
      pose proof (Rabs_triang (scan u k l - dfts N1 N2 u k l) (dfts N1 N2 u k l)) as U2.
      replace (ccan u k l - dftc N1 N2 u k l + dftc N1 N2 u k l) with (ccan u k l) in U1 by ring.
      replace (scan u k l - dfts N1 N2 u k l + dfts N1 N2 u k l) with (scan u k l) in U2 by ring.
      pose proof (wt_pos w k l) as Hwt.
      set (e := Mw * exp (- (w' * dal N1 N2 K1 K2))) in *.
      nra. }
  assert (Hout : sqsum outp N <= exp (- ((w' - w) * sout K1 K2)) * Mw).
  { apply Rle_trans with (sqsum (fun m n => exp (- ((w' - w) * sout K1 K2)) * nterm w' u m n) N).
    - apply sqsum_le. intros m n. unfold outp.
      destruct (in_box K1 K2 m n) eqn:E.
      + apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply nterm_nonneg].
      + apply out_box; assumption.
    - rewrite sqsum_scal. apply Rmult_le_compat_l; [apply Rlt_le, exp_pos | apply Hu]. }
  lra.
Qed.

Theorem nbound_model_kl (N1 N2 K1 K2 : nat) (u : fser) (w w' Mw : R) :
  (0 < N1)%nat -> (0 < N2)%nat -> 0 <= w -> w <= w' -> is_canon u -> nbound w' Mw u ->
  nbound w (bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k l) + Rabs (dfts N1 N2 u k l)
                                     + 2 * (Mw * exp (- (w' * dmode N1 N2 k l)))) * wt w k l)
            + exp (- ((w' - w) * sout K1 K2)) * Mw) u.
Proof.
  intros HN1 HN2 Hw Hww Cu Hu N.
  assert (Hw' : 0 <= w') by lra.
  set (inp := fun m n => if in_box K1 K2 m n then nterm w u m n else 0).
  set (outp := fun m n => if in_box K1 K2 m n then 0 else nterm w u m n).
  rewrite (sqsum_ext _ (fun m n => inp m n + outp m n))
    by (intros m n; unfold inp, outp; destruct (in_box K1 K2 m n); ring).
  rewrite sqsum_plus.
  assert (Hin : sqsum inp N <=
                bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k l) + Rabs (dfts N1 N2 u k l)
                                        + 2 * (Mw * exp (- (w' * dmode N1 N2 k l)))) * wt w k l)).
  { apply Rle_trans with (bsum K1 K2 inp).
    - apply sqsum_box.
      + intros m n. unfold inp. destruct (in_box K1 K2 m n); [apply nterm_nonneg | lra].
      + intros m n H. unfold inp. rewrite H. reflexivity.
    - apply bsum_le. intros k l Hkl. unfold inp. rewrite Hkl.
      pose proof (dftc_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu k l) as Ec.
      pose proof (dfts_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu k l) as Es.
      destruct Cu as [Cc Cs].
      assert (Fc : fc u k l = ccan u k l) by (unfold ccan; rewrite (Cc k l); field).
      assert (Fs : fs u k l = scan u k l) by (unfold scan; rewrite (Cs k l); field).
      unfold nterm. rewrite Fc, Fs.
      rewrite Rabs_minus_sym in Ec, Es.
      pose proof (Rabs_triang (ccan u k l - dftc N1 N2 u k l) (dftc N1 N2 u k l)) as U1.
      pose proof (Rabs_triang (scan u k l - dfts N1 N2 u k l) (dfts N1 N2 u k l)) as U2.
      replace (ccan u k l - dftc N1 N2 u k l + dftc N1 N2 u k l) with (ccan u k l) in U1 by ring.
      replace (scan u k l - dfts N1 N2 u k l + dfts N1 N2 u k l) with (scan u k l) in U2 by ring.
      pose proof (wt_pos w k l) as Hwt.
      set (e := Mw * exp (- (w' * dmode N1 N2 k l))) in *.
      nra. }
  assert (Hout : sqsum outp N <= exp (- ((w' - w) * sout K1 K2)) * Mw).
  { apply Rle_trans with (sqsum (fun m n => exp (- ((w' - w) * sout K1 K2)) * nterm w' u m n) N).
    - apply sqsum_le. intros m n. unfold outp.
      destruct (in_box K1 K2 m n) eqn:E.
      + apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply nterm_nonneg].
      + apply out_box; assumption.
    - rewrite sqsum_scal. apply Rmult_le_compat_l; [apply Rlt_le, exp_pos | apply Hu]. }
  lra.
Qed.
