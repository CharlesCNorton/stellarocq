(** Grid sums, discrete transforms and the uniqueness of coefficient families.

    On the grid of N1 x N2 points (2 pi a / N1, 2 pi b / N2), the sum of
    cos(j1 t + j2 p) is N1 N2 when N1 divides j1 and N2 divides j2 and zero
    otherwise, and the sum of sin(j1 t + j2 p) is zero ([gsum2_cos],
    [gsum2_sin]). The discrete transforms [dftc] and [dfts] of the values of a
    family on the grid therefore sum its coefficients over the modes congruent
    to (k, l) and to (-k, -l) ([dftc_alias], [dfts_alias]). On the grid N x N
    those modes other than (k, l) and (-k, -l) lie outside the square of side
    N - |k| - |l| - 1, so the transforms approach the symmetrised coefficients
    [ccan] and [scan] as N grows ([dftc_ccan], [dfts_scan]); a family whose
    function vanishes has vanishing symmetrised coefficients ([canon_zero]),
    and two families with the same function have the same ones
    ([canon_unique]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim.
Local Open Scope R_scope.

(** * Sums over one grid *)

Definition gpt (N a : nat) : R := 2 * PI * INR a / INR N.

Definition dvd (N : nat) (j : Z) : R := if (j mod Z.of_nat N =? 0)%Z then 1 else 0.

Lemma sin_2piz (j : Z) : sin (2 * PI * IZR j) = 0.
Proof. apply sin_eq_0_1. exists (2 * j)%Z. rewrite mult_IZR. ring. Qed.

Lemma cos_2piz (j : Z) : cos (2 * PI * IZR j) = 1.
Proof.
  replace (2 * PI * IZR j) with (2 * (PI * IZR j)) by ring.
  rewrite cos_2a_sin, (sin_eq_0_1 (PI * IZR j)) by (exists j; ring). ring.
Qed.

Lemma fsum_const_1 (N : nat) : fsum (fun _ => 1) N = INR N.
Proof.
  induction N as [| N IH]; [simpl; reflexivity |].
  simpl fsum. rewrite IH, S_INR. reflexivity.
Qed.

Lemma fsum_telescope (g : nat -> R) (N : nat) : fsum (fun a => g (S a) - g a) N = g N - g O.
Proof. induction N as [| N IH]; simpl fsum; [ring | rewrite IH; ring]. Qed.

Section Grid.

Variable N : nat.
Hypothesis HN : (0 < N)%nat.

Lemma INR_N_neq : INR N <> 0.
Proof. apply not_0_INR. lia. Qed.

Lemma grid_div (j : Z) :
  (j mod Z.of_nat N = 0)%Z -> forall a, exists z : Z, IZR j * gpt N a = 2 * PI * IZR z.
Proof.
  intros Hj a.
  pose proof (Z_div_mod_eq_full j (Z.of_nat N)) as Hd. rewrite Hj, Z.add_0_r in Hd.
  exists (Z.of_nat a * (j / Z.of_nat N))%Z.
  unfold gpt. rewrite Hd at 1. rewrite !mult_IZR, <- !INR_IZR_INZ.
  field. exact INR_N_neq.
Qed.

Lemma half_angle_nonzero (j : Z) :
  (j mod Z.of_nat N <> 0)%Z -> sin (PI * IZR j / INR N) <> 0.
Proof.
  intros Hj H. apply sin_eq_0_0 in H. destruct H as [k Hk].
  apply Hj.
  assert (Hpi := PI_RGT_0).
  assert (Hn := INR_N_neq).
  assert (E : IZR j = IZR (k * Z.of_nat N)).
  { rewrite mult_IZR, <- INR_IZR_INZ.
    replace (IZR j) with (PI * IZR j / INR N * (INR N / PI)) by (field; lra).
    rewrite Hk. field. lra. }
  apply eq_IZR in E. rewrite E. apply Z.mod_mul. lia.
Qed.

Lemma grid_cos_sum (j : Z) : fsum (fun a => cos (IZR j * gpt N a)) N = INR N * dvd N j.
Proof.
  unfold dvd. destruct (Z.eqb_spec (j mod Z.of_nat N) 0) as [Hj | Hj].
  - rewrite (fsum_ext _ (fun _ => 1)).
    + rewrite fsum_const_1. ring.
    + intros a. destruct (grid_div j Hj a) as [z Hz]. rewrite Hz. apply cos_2piz.
  - rewrite Rmult_0_r.
    set (h := PI * IZR j / INR N).
    assert (Hh : sin h <> 0) by (apply half_angle_nonzero; exact Hj).
    set (g := fun a : nat => sin (INR a * (2 * h) - h)).
    assert (Hstep : forall a, g (S a) - g a = 2 * sin h * cos (IZR j * gpt N a)).
    { intros a. unfold g. rewrite S_INR.
      replace ((INR a + 1) * (2 * h) - h) with (INR a * (2 * h) + h) by ring.
      replace (IZR j * gpt N a) with (INR a * (2 * h))
        by (unfold gpt, h; field; exact INR_N_neq).
      rewrite sin_plus, sin_minus. ring. }
    assert (Hsum : fsum (fun a => g (S a) - g a) N = 0).
    { rewrite fsum_telescope. unfold g. rewrite INR_0.
      replace (INR N * (2 * h) - h) with (2 * PI * IZR j - h)
        by (unfold h; field; exact INR_N_neq).
      replace (0 * (2 * h) - h) with (- h) by ring.
      rewrite sin_minus, sin_2piz, cos_2piz, sin_neg. ring. }
    rewrite (fsum_ext _ (fun a => 2 * sin h * cos (IZR j * gpt N a))) in Hsum by exact Hstep.
    rewrite fsum_scal in Hsum.
    apply Rmult_integral in Hsum. destruct Hsum as [H0 | H0]; [exfalso; apply Hh; lra | exact H0].
Qed.

Lemma grid_sin_sum (j : Z) : fsum (fun a => sin (IZR j * gpt N a)) N = 0.
Proof.
  destruct (Z.eqb_spec (j mod Z.of_nat N) 0) as [Hj | Hj].
  - rewrite (fsum_ext _ (fun _ => 0 * 1)).
    + rewrite fsum_scal. ring.
    + intros a. destruct (grid_div j Hj a) as [z Hz]. rewrite Hz, sin_2piz. ring.
  - set (h := PI * IZR j / INR N).
    assert (Hh : sin h <> 0) by (apply half_angle_nonzero; exact Hj).
    set (g := fun a : nat => cos (INR a * (2 * h) - h)).
    assert (Hstep : forall a, g (S a) - g a = - (2 * sin h) * sin (IZR j * gpt N a)).
    { intros a. unfold g. rewrite S_INR.
      replace ((INR a + 1) * (2 * h) - h) with (INR a * (2 * h) + h) by ring.
      replace (IZR j * gpt N a) with (INR a * (2 * h))
        by (unfold gpt, h; field; exact INR_N_neq).
      rewrite cos_plus, cos_minus. ring. }
    assert (Hsum : fsum (fun a => g (S a) - g a) N = 0).
    { rewrite fsum_telescope. unfold g. rewrite INR_0.
      replace (INR N * (2 * h) - h) with (2 * PI * IZR j - h)
        by (unfold h; field; exact INR_N_neq).
      replace (0 * (2 * h) - h) with (- h) by ring.
      rewrite cos_minus, sin_2piz, cos_2piz, cos_neg. ring. }
    rewrite (fsum_ext _ (fun a => - (2 * sin h) * sin (IZR j * gpt N a))) in Hsum by exact Hstep.
    rewrite fsum_scal in Hsum.
    apply Rmult_integral in Hsum. destruct Hsum as [H0 | H0]; [exfalso; apply Hh; lra | exact H0].
Qed.

End Grid.

(** * Sums over a grid of two angles *)

Definition gsum2 (N1 N2 : nat) (F : R -> R -> R) : R :=
  fsum (fun a => fsum (fun b => F (gpt N1 a) (gpt N2 b)) N2) N1.

Lemma gsum2_ext (N1 N2 : nat) (F G : R -> R -> R) :
  (forall t p, F t p = G t p) -> gsum2 N1 N2 F = gsum2 N1 N2 G.
Proof. intros H. unfold gsum2. apply fsum_ext. intros a. apply fsum_ext. intros b. apply H. Qed.

Lemma gsum2_plus (N1 N2 : nat) (F G : R -> R -> R) :
  gsum2 N1 N2 (fun t p => F t p + G t p) = gsum2 N1 N2 F + gsum2 N1 N2 G.
Proof.
  unfold gsum2. rewrite <- fsum_plus. apply fsum_ext. intros a. apply fsum_plus.
Qed.

Lemma gsum2_scal (N1 N2 : nat) (c : R) (F : R -> R -> R) :
  gsum2 N1 N2 (fun t p => c * F t p) = c * gsum2 N1 N2 F.
Proof.
  unfold gsum2. rewrite <- fsum_scal. apply fsum_ext. intros a. apply fsum_scal.
Qed.

Lemma fsum_mult (f g : nat -> R) (N1 N2 : nat) :
  fsum (fun a => fsum (fun b => f a * g b) N2) N1 = fsum f N1 * fsum g N2.
Proof.
  rewrite (fsum_ext _ (fun a => fsum g N2 * f a)).
  - rewrite fsum_scal. ring.
  - intros a. rewrite fsum_scal. ring.
Qed.

Lemma gsum2_cos (N1 N2 : nat) (j1 j2 : Z) : (0 < N1)%nat -> (0 < N2)%nat ->
  gsum2 N1 N2 (fun t p => cos (IZR j1 * t + IZR j2 * p))
  = INR N1 * INR N2 * (dvd N1 j1 * dvd N2 j2).
Proof.
  intros H1 H2. unfold gsum2.
  rewrite (fsum_ext _ (fun a => fsum (fun b => cos (IZR j1 * gpt N1 a) * cos (IZR j2 * gpt N2 b)) N2
                               + -1 * fsum (fun b => sin (IZR j1 * gpt N1 a) * sin (IZR j2 * gpt N2 b)) N2)).
  2: { intros a. rewrite <- fsum_scal, <- fsum_plus. apply fsum_ext. intros b. rewrite cos_plus. ring. }
  rewrite fsum_plus, fsum_scal.
  rewrite (fsum_mult (fun a => cos (IZR j1 * gpt N1 a)) (fun b => cos (IZR j2 * gpt N2 b))).
  rewrite (fsum_mult (fun a => sin (IZR j1 * gpt N1 a)) (fun b => sin (IZR j2 * gpt N2 b))).
  rewrite (grid_cos_sum N1 H1), (grid_cos_sum N2 H2), (grid_sin_sum N1 H1). ring.
Qed.

Lemma gsum2_sin (N1 N2 : nat) (j1 j2 : Z) : (0 < N1)%nat -> (0 < N2)%nat ->
  gsum2 N1 N2 (fun t p => sin (IZR j1 * t + IZR j2 * p)) = 0.
Proof.
  intros H1 H2. unfold gsum2.
  rewrite (fsum_ext _ (fun a => fsum (fun b => sin (IZR j1 * gpt N1 a) * cos (IZR j2 * gpt N2 b)) N2
                               + fsum (fun b => cos (IZR j1 * gpt N1 a) * sin (IZR j2 * gpt N2 b)) N2)).
  2: { intros a. rewrite <- fsum_plus. apply fsum_ext. intros b. rewrite sin_plus. ring. }
  rewrite fsum_plus.
  rewrite (fsum_mult (fun a => sin (IZR j1 * gpt N1 a)) (fun b => cos (IZR j2 * gpt N2 b))).
  rewrite (fsum_mult (fun a => cos (IZR j1 * gpt N1 a)) (fun b => sin (IZR j2 * gpt N2 b))).
  rewrite (grid_sin_sum N1 H1), (grid_sin_sum N2 H2). ring.
Qed.

(** * Finite sums of summable families *)

Lemma zz_sum_const0 : zz_sum (fun _ _ => 0) = 0.
Proof.
  unfold zz_sum. rewrite (Lim_seq_ext _ (fun _ => 0)) by apply sqsum_zero.
  rewrite Lim_seq_const. reflexivity.
Qed.

Lemma summable_le (g : Z -> Z -> R) (M M' : R) : M <= M' -> abs_summable g M -> abs_summable g M'.
Proof. intros H Hg K. pose proof (Hg K). lra. Qed.

Lemma summable_fsum (G : nat -> Z -> Z -> R) (M : R) (N : nat) :
  (forall a, abs_summable (G a) M) ->
  abs_summable (fun m n => fsum (fun a => G a m n) N) (INR N * M).
Proof.
  intros H. induction N as [| N IH].
  - intros K. rewrite INR_0, Rmult_0_l. unfold absf. simpl fsum.
    rewrite (sqsum_ext _ (fun _ _ => 0)) by (intros; apply Rabs_R0).
    rewrite sqsum_zero. lra.
  - rewrite S_INR. replace ((INR N + 1) * M) with (INR N * M + M) by ring.
    exact (summable_plus (fun m n => fsum (fun a => G a m n) N) (G N) _ _ IH (H N)).
Qed.

Lemma zz_sum_fsum (G : nat -> Z -> Z -> R) (M : R) (N : nat) :
  (forall a, abs_summable (G a) M) ->
  fsum (fun a => zz_sum (G a)) N = zz_sum (fun m n => fsum (fun a => G a m n) N).
Proof.
  intros H. induction N as [| N IH].
  - simpl fsum. symmetry. apply zz_sum_const0.
  - simpl fsum. rewrite IH.
    rewrite (zz_sum_plus (fun m n => fsum (fun a => G a m n) N) (G N) (INR N * M) M).
    + reflexivity.
    + apply summable_fsum, H.
    + apply H.
Qed.

Lemma summable_trig_term (u : fser) (M t p c : R) :
  nbound 0 M u -> Rabs c <= 1 -> abs_summable (fun m n => c * term u t p m n) M.
Proof.
  intros Hu Hc. apply (summable_le _ (Rabs c * M)).
  - pose proof (nbound_nonneg 0 M u Hu). pose proof (Rabs_pos c). nra.
  - apply summable_scal, summable_term, Hu.
Qed.

Lemma Rabs_cos_le (x : R) : Rabs (cos x) <= 1.
Proof. apply Rabs_le. apply COS_bound. Qed.

Lemma Rabs_sin_le (x : R) : Rabs (sin x) <= 1.
Proof. apply Rabs_le. apply SIN_bound. Qed.

(** * Products of modes over the grid *)

Lemma cos_cos (a b : R) : cos a * cos b = / 2 * (cos (a - b) + cos (a + b)).
Proof. rewrite cos_minus, cos_plus. field. Qed.

Lemma sin_cos (a b : R) : sin a * cos b = / 2 * (sin (a + b) + sin (a - b)).
Proof. rewrite sin_minus, sin_plus. field. Qed.

Lemma cos_sin (a b : R) : cos a * sin b = / 2 * (sin (a + b) - sin (a - b)).
Proof. rewrite sin_minus, sin_plus. field. Qed.

Lemma sin_sin (a b : R) : sin a * sin b = / 2 * (cos (a - b) - cos (a + b)).
Proof. rewrite cos_minus, cos_plus. field. Qed.

Lemma mode_sum (m n k l : Z) (t p : R) :
  mode m n t p + (IZR k * t + IZR l * p) = IZR (m + k) * t + IZR (n + l) * p.
Proof. unfold mode. rewrite !plus_IZR. ring. Qed.

Lemma mode_diff (m n k l : Z) (t p : R) :
  mode m n t p - (IZR k * t + IZR l * p) = IZR (m - k) * t + IZR (n - l) * p.
Proof. unfold mode. rewrite !minus_IZR. ring. Qed.

Definition alias (N1 N2 : nat) (j1 j2 : Z) : R := dvd N1 j1 * dvd N2 j2.

Lemma gsum2_term_cos (N1 N2 : nat) (u : fser) (m n k l : Z) : (0 < N1)%nat -> (0 < N2)%nat ->
  gsum2 N1 N2 (fun t p => term u t p m n * cos (IZR k * t + IZR l * p))
  = INR N1 * INR N2 * (fc u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l)))).
Proof.
  intros H1 H2.
  rewrite (gsum2_ext _ _ _ (fun t p =>
      (fc u m n * / 2) * cos (IZR (m - k) * t + IZR (n - l) * p)
    + ((fc u m n * / 2) * cos (IZR (m + k) * t + IZR (n + l) * p)
    + ((fs u m n * / 2) * sin (IZR (m + k) * t + IZR (n + l) * p)
    + (fs u m n * / 2) * sin (IZR (m - k) * t + IZR (n - l) * p))))).
  2: { intros t p. unfold term.
       rewrite Rmult_plus_distr_r, !Rmult_assoc, cos_cos, sin_cos, mode_sum, mode_diff. ring. }
  rewrite !gsum2_plus, !gsum2_scal.
  rewrite (gsum2_cos N1 N2 (m - k) (n - l) H1 H2), (gsum2_cos N1 N2 (m + k) (n + l) H1 H2),
    (gsum2_sin N1 N2 (m + k) (n + l) H1 H2), (gsum2_sin N1 N2 (m - k) (n - l) H1 H2).
  unfold alias. ring.
Qed.

Lemma gsum2_term_sin (N1 N2 : nat) (u : fser) (m n k l : Z) : (0 < N1)%nat -> (0 < N2)%nat ->
  gsum2 N1 N2 (fun t p => term u t p m n * sin (IZR k * t + IZR l * p))
  = INR N1 * INR N2 * (fs u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l)))).
Proof.
  intros H1 H2.
  rewrite (gsum2_ext _ _ _ (fun t p =>
      (fc u m n * / 2) * sin (IZR (m + k) * t + IZR (n + l) * p)
    + (- (fc u m n * / 2) * sin (IZR (m - k) * t + IZR (n - l) * p)
    + ((fs u m n * / 2) * cos (IZR (m - k) * t + IZR (n - l) * p)
    + - (fs u m n * / 2) * cos (IZR (m + k) * t + IZR (n + l) * p))))).
  2: { intros t p. unfold term.
       rewrite Rmult_plus_distr_r, !Rmult_assoc, cos_sin, sin_sin, mode_sum, mode_diff. ring. }
  rewrite !gsum2_plus, !gsum2_scal.
  rewrite (gsum2_cos N1 N2 (m - k) (n - l) H1 H2), (gsum2_cos N1 N2 (m + k) (n + l) H1 H2),
    (gsum2_sin N1 N2 (m + k) (n + l) H1 H2), (gsum2_sin N1 N2 (m - k) (n - l) H1 H2).
  unfold alias. ring.
Qed.

(** * The discrete transforms and their aliasing *)

Definition dftc (N1 N2 : nat) (u : fser) (k l : Z) : R :=
  / (INR N1 * INR N2) * gsum2 N1 N2 (fun t p => feval u t p * cos (IZR k * t + IZR l * p)).

Definition dfts (N1 N2 : nat) (u : fser) (k l : Z) : R :=
  / (INR N1 * INR N2) * gsum2 N1 N2 (fun t p => feval u t p * sin (IZR k * t + IZR l * p)).

Lemma grid_nonzero (N1 N2 : nat) : (0 < N1)%nat -> (0 < N2)%nat -> INR N1 * INR N2 <> 0.
Proof. intros H1 H2. apply Rmult_integral_contrapositive_currified; apply not_0_INR; lia. Qed.

(** The grid sum of a family's values against a trigonometric weight, as one
    sum over the modes. *)
Lemma gsum2_feval (N1 N2 : nat) (u : fser) (M : R) (w : R -> R -> R) :
  nbound 0 M u -> (forall t p, Rabs (w t p) <= 1) ->
  gsum2 N1 N2 (fun t p => feval u t p * w t p)
  = zz_sum (fun m n => gsum2 N1 N2 (fun t p => term u t p m n * w t p)).
Proof.
  intros Hu Hw.
  rewrite (gsum2_ext _ _ _ (fun t p => zz_sum (fun m n => w t p * term u t p m n))).
  2: { intros t p. unfold feval.
       rewrite (zz_sum_scal (w t p) (term u t p) M) by (apply summable_term, Hu). ring. }
  unfold gsum2.
  rewrite (fsum_ext _ (fun a => zz_sum (fun m n =>
             fsum (fun b => w (gpt N1 a) (gpt N2 b) * term u (gpt N1 a) (gpt N2 b) m n) N2))).
  2: { intros a.
       apply (zz_sum_fsum (fun b m n => w (gpt N1 a) (gpt N2 b) * term u (gpt N1 a) (gpt N2 b) m n) M).
       intros b. apply summable_trig_term; [exact Hu | apply Hw]. }
  rewrite (zz_sum_fsum (fun a m n =>
             fsum (fun b => w (gpt N1 a) (gpt N2 b) * term u (gpt N1 a) (gpt N2 b) m n) N2)
             (INR N2 * M)).
  2: { intros a. apply summable_fsum. intros b. apply summable_trig_term; [exact Hu | apply Hw]. }
  apply zz_sum_ext. intros m n. apply fsum_ext. intros a. apply fsum_ext. intros b. ring.
Qed.

Theorem dftc_alias (N1 N2 : nat) (u : fser) (M : R) (k l : Z) :
  (0 < N1)%nat -> (0 < N2)%nat -> nbound 0 M u ->
  dftc N1 N2 u k l =
  zz_sum (fun m n => fc u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l)))).
Proof.
  intros H1 H2 Hu. pose proof (grid_nonzero N1 N2 H1 H2) as HN.
  unfold dftc.
  rewrite (gsum2_feval N1 N2 u M (fun t p => cos (IZR k * t + IZR l * p)) Hu)
    by (intros; apply Rabs_cos_le).
  rewrite (zz_sum_ext _ (fun m n => INR N1 * INR N2 *
             (fc u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l))))))
    by (intros m n; apply gsum2_term_cos; assumption).
  assert (HS : abs_summable
                 (fun m n => fc u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l))))
                 M).
  { apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      assert (Ha : Rabs (/ 2 * (alias N1 N2 (m - k) (n - l) + alias N1 N2 (m + k) (n + l))) <= 1).
      { unfold alias, dvd.
        destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; destruct (_ =? 0)%Z;
          rewrite Rabs_pos_eq; lra. }
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K. eapply Rle_trans; [| apply (Hu K)].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  rewrite (zz_sum_scal (INR N1 * INR N2) _ M HS).
  field. split; apply not_0_INR; lia.
Qed.

Theorem dfts_alias (N1 N2 : nat) (u : fser) (M : R) (k l : Z) :
  (0 < N1)%nat -> (0 < N2)%nat -> nbound 0 M u ->
  dfts N1 N2 u k l =
  zz_sum (fun m n => fs u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l)))).
Proof.
  intros H1 H2 Hu. pose proof (grid_nonzero N1 N2 H1 H2) as HN.
  unfold dfts.
  rewrite (gsum2_feval N1 N2 u M (fun t p => sin (IZR k * t + IZR l * p)) Hu)
    by (intros; apply Rabs_sin_le).
  rewrite (zz_sum_ext _ (fun m n => INR N1 * INR N2 *
             (fs u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l))))))
    by (intros m n; apply gsum2_term_sin; assumption).
  assert (HS : abs_summable
                 (fun m n => fs u m n * (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l))))
                 M).
  { apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      assert (Ha : Rabs (/ 2 * (alias N1 N2 (m - k) (n - l) - alias N1 N2 (m + k) (n + l))) <= 1).
      { unfold alias, dvd. apply Rabs_le.
        destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K. eapply Rle_trans; [| apply (Hu K)].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  rewrite (zz_sum_scal (INR N1 * INR N2) _ M HS).
  field. split; apply not_0_INR; lia.
Qed.

(** * Symmetrised coefficients and uniqueness *)

Definition ccan (u : fser) (k l : Z) : R := / 2 * (fc u k l + fc u (- k) (- l)).
Definition scan (u : fser) (k l : Z) : R := / 2 * (fs u k l - fs u (- k) (- l)).

Lemma dvd_small (N : nat) (j : Z) :
  (0 < N)%nat -> (Z.abs j < Z.of_nat N)%Z -> dvd N j = if (j =? 0)%Z then 1 else 0.
Proof.
  intros HN Hj. unfold dvd.
  destruct (Z.eqb_spec j 0) as [-> | Hj0].
  - rewrite Zmod_0_l. reflexivity.
  - destruct (Z.eqb_spec (j mod Z.of_nat N) 0) as [Hm | Hm]; [exfalso | reflexivity].
    apply Z.mod_divide in Hm; [| lia]. destruct Hm as [c Hc].
    assert (Hn : (0 < Z.of_nat N)%Z) by lia.
    destruct (Z.lt_trichotomy c 0) as [Hc0 | [Hc0 | Hc0]].
    + assert (c * Z.of_nat N <= - Z.of_nat N)%Z by nia. lia.
    + subst c. lia.
    + assert (Z.of_nat N <= c * Z.of_nat N)%Z by nia. lia.
Qed.

Lemma alias_in (N K : nat) (k l m n : Z) :
  (0 < N)%nat -> (Z.of_nat K + Z.abs k + Z.abs l < Z.of_nat N)%Z -> in_sq K m n = true ->
  alias N N (m - k) (n - l) = at2 k l 1 m n /\ alias N N (m + k) (n + l) = at2 (- k) (- l) 1 m n.
Proof.
  intros HN HK Hin. unfold in_sq in Hin. apply andb_prop in Hin. destruct Hin as [Hm Hn].
  apply Z.leb_le in Hm. apply Z.leb_le in Hn.
  unfold alias, at2.
  rewrite (dvd_small N (m - k)), (dvd_small N (n - l)), (dvd_small N (m + k)), (dvd_small N (n + l))
    by (assumption || lia).
  split.
  - destruct (Z.eqb_spec (m - k) 0); destruct (Z.eqb_spec (n - l) 0);
      destruct (Z.eqb_spec m k); destruct (Z.eqb_spec n l); simpl; try lia; ring.
  - destruct (Z.eqb_spec (m + k) 0); destruct (Z.eqb_spec (n + l) 0);
      destruct (Z.eqb_spec m (- k)); destruct (Z.eqb_spec n (- l)); simpl; try lia; ring.
Qed.

Lemma at2_pick (f : Z -> Z -> R) (k l m n : Z) : f m n * at2 k l 1 m n = at2 k l (f k l) m n.
Proof.
  unfold at2. destruct (Z.eqb_spec m k) as [-> | ]; destruct (Z.eqb_spec n l) as [-> | ]; simpl; ring.
Qed.

Lemma ccan_zz (u : fser) (k l : Z) :
  ccan u k l = zz_sum (fun m n => fc u m n * (/ 2 * (at2 k l 1 m n + at2 (- k) (- l) 1 m n))).
Proof.
  rewrite (zz_sum_ext _ (fun m n => at2 k l (/ 2 * fc u k l) m n + at2 (- k) (- l) (/ 2 * fc u (- k) (- l)) m n)).
  - rewrite (zz_sum_plus _ _ _ _ (summable_at2 k l _) (summable_at2 (- k) (- l) _)).
    rewrite !zz_sum_at2. unfold ccan. ring.
  - intros m n.
    replace (fc u m n * (/ 2 * (at2 k l 1 m n + at2 (- k) (- l) 1 m n)))
      with (/ 2 * (fc u m n * at2 k l 1 m n) + / 2 * (fc u m n * at2 (- k) (- l) 1 m n)) by ring.
    rewrite !(at2_pick (fc u)). unfold at2.
    destruct (_ && _)%bool; destruct (_ && _)%bool; ring.
Qed.

Lemma scan_zz (u : fser) (k l : Z) :
  scan u k l = zz_sum (fun m n => fs u m n * (/ 2 * (at2 k l 1 m n - at2 (- k) (- l) 1 m n))).
Proof.
  rewrite (zz_sum_ext _ (fun m n => at2 k l (/ 2 * fs u k l) m n + at2 (- k) (- l) (- (/ 2 * fs u (- k) (- l))) m n)).
  - rewrite (zz_sum_plus _ _ _ _ (summable_at2 k l _) (summable_at2 (- k) (- l) _)).
    rewrite !zz_sum_at2. unfold scan. ring.
  - intros m n.
    replace (fs u m n * (/ 2 * (at2 k l 1 m n - at2 (- k) (- l) 1 m n)))
      with (/ 2 * (fs u m n * at2 k l 1 m n) - / 2 * (fs u m n * at2 (- k) (- l) 1 m n)) by ring.
    rewrite !(at2_pick (fs u)). unfold at2.
    destruct (_ && _)%bool; destruct (_ && _)%bool; ring.
Qed.

Section Converge.

Variables (u : fser) (M : R).
Hypothesis Hu : nbound 0 M u.

(** A function of the modes vanishing on the square of side K and at most one
    outside it sums against the coefficients to at most the tail beyond K. *)
Lemma tail_sum (K : nat) (w : Z -> Z -> R) (sel : fser -> Z -> Z -> R) :
  (sel = fc \/ sel = fs) ->
  (forall m n, in_sq K m n = true -> w m n = 0) -> (forall m n, Rabs (w m n) <= 1) ->
  Rabs (zz_sum (fun m n => sel u m n * w m n)) <= nlim u - sqsum (nterm 0 u) K.
Proof.
  intros Hsel Hin Hw.
  apply zz_sum_bound. apply (summable_dom _ (nterm 0 (fsub u (trunc K u)))).
  - intros m n. rewrite nterm_fsub_trunc. unfold out_part.
    destruct (in_sq K m n) eqn:E.
    + rewrite (Hin m n E), Rmult_0_r, Rabs_R0. lra.
    + unfold nterm. rewrite wt_0, Rabs_mult.
      pose proof (Hw m n). pose proof (Rabs_pos (w m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)).
      destruct Hsel as [-> | ->]; nra.
  - intros K'. eapply Rle_trans; [| apply (nbound_tail u M Hu K K')].
    apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra.
Qed.

Theorem dftc_ccan (N K : nat) (k l : Z) :
  (0 < N)%nat -> (Z.of_nat K + Z.abs k + Z.abs l < Z.of_nat N)%Z ->
  Rabs (dftc N N u k l - ccan u k l) <= nlim u - sqsum (nterm 0 u) K.
Proof.
  intros HN HK.
  rewrite (dftc_alias N N u M k l HN HN Hu), ccan_zz.
  assert (S1 : forall w : Z -> Z -> R, (forall m n, Rabs (w m n) <= 1) ->
                 abs_summable (fun m n => fc u m n * w m n) M).
  { intros w Hw. apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      pose proof (Hw m n). pose proof (Rabs_pos (w m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K'. eapply Rle_trans; [| apply (Hu K')].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  assert (Hal : forall j1 j2, 0 <= alias N N j1 j2 <= 1).
  { intros j1 j2. unfold alias, dvd. destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
  assert (Hat : forall a b m n, 0 <= at2 a b 1 m n <= 1).
  { intros a b m n. unfold at2. destruct (_ && _)%bool; lra. }
  rewrite <- (zz_sum_minus _ _ M M).
  2: { apply S1. intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
       apply Rabs_le. lra. }
  2: { apply S1. intros m n. pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n).
       apply Rabs_le. lra. }
  rewrite (zz_sum_ext _ (fun m n => fc u m n *
             (/ 2 * (alias N N (m - k) (n - l) + alias N N (m + k) (n + l))
              - / 2 * (at2 k l 1 m n + at2 (- k) (- l) 1 m n))))
    by (intros; ring).
  apply (tail_sum K _ fc (or_introl eq_refl)).
  - intros m n Hin. destruct (alias_in N K k l m n HN HK Hin) as [E1 E2]. rewrite E1, E2. ring.
  - intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
    pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n). apply Rabs_le. lra.
Qed.

Theorem dfts_scan (N K : nat) (k l : Z) :
  (0 < N)%nat -> (Z.of_nat K + Z.abs k + Z.abs l < Z.of_nat N)%Z ->
  Rabs (dfts N N u k l - scan u k l) <= nlim u - sqsum (nterm 0 u) K.
Proof.
  intros HN HK.
  rewrite (dfts_alias N N u M k l HN HN Hu), scan_zz.
  assert (S1 : forall w : Z -> Z -> R, (forall m n, Rabs (w m n) <= 1) ->
                 abs_summable (fun m n => fs u m n * w m n) M).
  { intros w Hw. apply (summable_dom _ (nterm 0 u)).
    - intros m n. rewrite Rabs_mult. unfold nterm. rewrite wt_0.
      pose proof (Hw m n). pose proof (Rabs_pos (w m n)).
      pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
    - intros K'. eapply Rle_trans; [| apply (Hu K')].
      apply sqsum_le. intros m n. unfold absf. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  assert (Hal : forall j1 j2, 0 <= alias N N j1 j2 <= 1).
  { intros j1 j2. unfold alias, dvd. destruct (_ =? 0)%Z; destruct (_ =? 0)%Z; lra. }
  assert (Hat : forall a b m n, 0 <= at2 a b 1 m n <= 1).
  { intros a b m n. unfold at2. destruct (_ && _)%bool; lra. }
  rewrite <- (zz_sum_minus _ _ M M).
  2: { apply S1. intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
       apply Rabs_le. lra. }
  2: { apply S1. intros m n. pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n).
       apply Rabs_le. lra. }
  rewrite (zz_sum_ext _ (fun m n => fs u m n *
             (/ 2 * (alias N N (m - k) (n - l) - alias N N (m + k) (n + l))
              - / 2 * (at2 k l 1 m n - at2 (- k) (- l) 1 m n))))
    by (intros; ring).
  apply (tail_sum K _ fs (or_intror eq_refl)).
  - intros m n Hin. destruct (alias_in N K k l m n HN HK Hin) as [E1 E2]. rewrite E1, E2. ring.
  - intros m n. pose proof (Hal (m - k)%Z (n - l)%Z). pose proof (Hal (m + k)%Z (n + l)%Z).
    pose proof (Hat k l m n). pose proof (Hat (- k)%Z (- l)%Z m n). apply Rabs_le. lra.
Qed.

(** A real number within every tail of the norm series is zero. *)
Lemma below_tails (c : R) : (forall K, Rabs c <= nlim u - sqsum (nterm 0 u) K) -> c = 0.
Proof.
  intros H. destruct (Req_dec c 0) as [E | E]; [exact E | exfalso].
  assert (Hc : 0 < Rabs c / 2) by (apply Rdiv_lt_0_compat; [apply Rabs_pos_lt, E | lra]).
  destruct (tail_small u M Hu (mkposreal _ Hc)) as [K HK]. simpl in HK.
  pose proof (H K). pose proof (Rabs_pos c). lra.
Qed.

Lemma grid_size (K : nat) (k l : Z) :
  let N := (K + Z.to_nat (Z.abs k) + Z.to_nat (Z.abs l) + 1)%nat in
  (0 < N)%nat /\ (Z.of_nat K + Z.abs k + Z.abs l < Z.of_nat N)%Z.
Proof. simpl. split; [lia |]. rewrite !Nat2Z.inj_add, !Z2Nat.id by lia. lia. Qed.

Theorem canon_zero :
  (forall t p, feval u t p = 0) -> forall k l, ccan u k l = 0 /\ scan u k l = 0.
Proof.
  intros H0 k l.
  assert (Dc : forall N, dftc N N u k l = 0).
  { intros N. unfold dftc.
    rewrite (gsum2_ext _ _ _ (fun t p => 0 * cos (IZR k * t + IZR l * p)))
      by (intros; rewrite H0; ring).
    rewrite gsum2_scal. ring. }
  assert (Ds : forall N, dfts N N u k l = 0).
  { intros N. unfold dfts.
    rewrite (gsum2_ext _ _ _ (fun t p => 0 * sin (IZR k * t + IZR l * p)))
      by (intros; rewrite H0; ring).
    rewrite gsum2_scal. ring. }
  split; apply below_tails; intros K; destruct (grid_size K k l) as [HN HK].
  - pose proof (dftc_ccan _ K k l HN HK) as B. rewrite Dc in B.
    replace (0 - ccan u k l) with (- ccan u k l) in B by ring. rewrite Rabs_Ropp in B. exact B.
  - pose proof (dfts_scan _ K k l HN HK) as B. rewrite Ds in B.
    replace (0 - scan u k l) with (- scan u k l) in B by ring. rewrite Rabs_Ropp in B. exact B.
Qed.

End Converge.

Theorem canon_unique (u v : fser) (Mu Mv : R) :
  nbound 0 Mu u -> nbound 0 Mv v -> (forall t p, feval u t p = feval v t p) ->
  forall k l, ccan u k l = ccan v k l /\ scan u k l = scan v k l.
Proof.
  intros Hu Hv H k l.
  assert (Hw : nbound 0 (Mu + Mv) (fsub u v)) by (apply nbound_fsub; assumption).
  assert (H0 : forall t p, feval (fsub u v) t p = 0).
  { intros t p. rewrite (feval_fsub u v Mu Mv t p Hu Hv), H. ring. }
  destruct (canon_zero (fsub u v) (Mu + Mv) Hw H0 k l) as [Ec Es].
  unfold ccan, scan, fsub, fadd, fscal in Ec, Es. simpl in Ec, Es.
  unfold ccan, scan. split; lra.
Qed.
