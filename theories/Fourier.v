(** Functions on the torus as weighted Fourier coefficient families.

    A real function on T^2 is carried by two coefficient families a, b over
    Z x Z, the function sum a_mn cos(m t + n p) + b_mn sin(m t + n p). Its
    analytic norm on the strip of complex angles of width rho is

      |u|_rho = sum (|a_mn| + |b_mn|) exp(rho (|m| + |n|)),

    and [nbound rho M u] says that every partial sum of it over a square
    |m|, |n| <= N is at most M. The derivatives d_t and d_p and the operator
    L = rho0 d_t + d_p of the KAM step act mode by mode, and giving up a width
    delta of the strip bounds them: |d_t u|_(rho - delta) <= |u|_rho / (e delta)
    ([nbound_dt], [nbound_dp]). For a rotation number rho0 that is Diophantine
    with constant gamma <= 1, the inverse of L on the modes other than the
    average costs (1 + 1 / (e delta)) / gamma ([nbound_linv]), and
    L (L^-1 u) = u at every mode but (0, 0) ([lc_linv]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Stellarocq Require Import KAMScalar Dioph.
Local Open Scope R_scope.

(** * Finite sums over integer ranges and squares *)

(** A sum over m = -N .. N, one symmetric pair of terms at a time. *)
Fixpoint zsum (f : Z -> R) (N : nat) : R :=
  match N with
  | O => f 0%Z
  | S k => zsum f k + (f (Z.of_nat (S k)) + f (- Z.of_nat (S k))%Z)
  end.

(** A sum over the square |m|, |n| <= N. *)
Definition sqsum (f : Z -> Z -> R) (N : nat) : R :=
  zsum (fun m => zsum (fun n => f m n) N) N.

Lemma fsum_scal (c : R) (f : nat -> R) (n : nat) :
  fsum (fun k => c * f k) n = c * fsum f n.
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fsum_plus (f g : nat -> R) (n : nat) :
  fsum (fun k => f k + g k) n = fsum f n + fsum g n.
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma zsum_0 (f : Z -> R) : zsum f 0 = f 0%Z.
Proof. reflexivity. Qed.

Lemma zsum_S (f : Z -> R) (N : nat) :
  zsum f (S N) = zsum f N + (f (Z.of_nat (S N)) + f (- Z.of_nat (S N))%Z).
Proof. reflexivity. Qed.

Lemma zsum_le (f g : Z -> R) (N : nat) :
  (forall m, f m <= g m) -> zsum f N <= zsum g N.
Proof.
  intros H. induction N as [| N IH]; [rewrite !zsum_0; apply H |].
  rewrite !zsum_S.
  pose proof (H (Z.of_nat (S N))). pose proof (H (- Z.of_nat (S N))%Z). lra.
Qed.

Lemma zsum_scal (c : R) (f : Z -> R) (N : nat) :
  zsum (fun m => c * f m) N = c * zsum f N.
Proof.
  induction N as [| N IH]; [rewrite !zsum_0; ring |].
  rewrite !zsum_S, IH. ring.
Qed.

Lemma zsum_plus (f g : Z -> R) (N : nat) :
  zsum (fun m => f m + g m) N = zsum f N + zsum g N.
Proof.
  induction N as [| N IH]; [rewrite !zsum_0; ring |].
  rewrite !zsum_S, IH. ring.
Qed.

Lemma sqsum_le (f g : Z -> Z -> R) (N : nat) :
  (forall m n, f m n <= g m n) -> sqsum f N <= sqsum g N.
Proof. intros H. unfold sqsum. apply zsum_le. intros m. apply zsum_le. apply H. Qed.

Lemma fsum_ext (f g : nat -> R) (n : nat) :
  (forall k, f k = g k) -> fsum f n = fsum g n.
Proof. intros H. induction n as [| n IH]; simpl; [reflexivity | rewrite IH, H; reflexivity]. Qed.

Lemma zsum_ext (f g : Z -> R) (N : nat) :
  (forall m, f m = g m) -> zsum f N = zsum g N.
Proof.
  intros H. induction N as [| N IH]; [rewrite !zsum_0; apply H |].
  rewrite !zsum_S, IH, !H. reflexivity.
Qed.

Lemma sqsum_scal (c : R) (f : Z -> Z -> R) (N : nat) :
  sqsum (fun m n => c * f m n) N = c * sqsum f N.
Proof.
  unfold sqsum.
  rewrite (zsum_ext _ (fun m => c * zsum (fun n => f m n) N)).
  - apply zsum_scal.
  - intros m. apply zsum_scal.
Qed.

Lemma sqsum_plus (f g : Z -> Z -> R) (N : nat) :
  sqsum (fun m n => f m n + g m n) N = sqsum f N + sqsum g N.
Proof.
  unfold sqsum.
  rewrite (zsum_ext _ (fun m => zsum (fun n => f m n) N + zsum (fun n => g m n) N)).
  - apply zsum_plus.
  - intros m. apply zsum_plus.
Qed.

(** * Coefficient families and their norms *)

Record fser := { fc : Z -> Z -> R ; fs : Z -> Z -> R }.

(** |m| + |n|, and the weight of mode (m, n) on the strip of width rho. *)
Definition msize (m n : Z) : R := Rabs (IZR m) + Rabs (IZR n).

Definition wt (rho : R) (m n : Z) : R := exp (rho * msize m n).

Definition nterm (rho : R) (u : fser) (m n : Z) : R :=
  (Rabs (fc u m n) + Rabs (fs u m n)) * wt rho m n.

Definition nbound (rho M : R) (u : fser) : Prop :=
  forall N, sqsum (nterm rho u) N <= M.

Lemma msize_nonneg (m n : Z) : 0 <= msize m n.
Proof. unfold msize. pose proof (Rabs_pos (IZR m)). pose proof (Rabs_pos (IZR n)). lra. Qed.

Lemma wt_pos (rho : R) (m n : Z) : 0 < wt rho m n.
Proof. apply exp_pos. Qed.

Lemma exp_mono (x y : R) : x <= y -> exp x <= exp y.
Proof.
  intros H. destruct (Rle_lt_or_eq_dec x y H) as [Hl | He].
  - apply Rlt_le, exp_increasing, Hl.
  - subst. lra.
Qed.

Lemma wt_shift (rho delta : R) (m n : Z) :
  wt (rho - delta) m n = wt rho m n * exp (- (delta * msize m n)).
Proof. unfold wt. rewrite <- exp_plus. f_equal. ring. Qed.

(** s exp(-delta s) <= 1 / (e delta). *)
Lemma exp_decay (s delta : R) :
  0 <= s -> 0 < delta -> s * exp (- (delta * s)) <= / (exp 1 * delta).
Proof.
  intros Hs Hd.
  pose proof (exp_ineq1_le (delta * s - 1)) as H.
  assert (He1 : 0 < exp 1) by apply exp_pos.
  assert (Hes : 0 < exp (delta * s)) by apply exp_pos.
  replace (exp (delta * s - 1)) with (exp (delta * s) * / exp 1) in H.
  2: { unfold Rminus. rewrite exp_plus, exp_Ropp. reflexivity. }
  rewrite exp_Ropp.
  apply Rmult_le_reg_l with (exp 1 * delta * exp (delta * s)).
  { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; lra. }
  replace (exp 1 * delta * exp (delta * s) * (s * / exp (delta * s)))
    with (exp 1 * (delta * s)) by (field; lra).
  replace (exp 1 * delta * exp (delta * s) * / (exp 1 * delta))
    with (exp (delta * s)) by (field; lra).
  apply Rmult_le_reg_l with (/ exp 1).
  { apply Rinv_0_lt_compat, He1. }
  replace (/ exp 1 * (exp 1 * (delta * s))) with (delta * s) by (field; lra).
  lra.
Qed.

Lemma nterm_nonneg (rho : R) (u : fser) (m n : Z) : 0 <= nterm rho u m n.
Proof.
  unfold nterm. apply Rmult_le_pos.
  - pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). lra.
  - apply Rlt_le, wt_pos.
Qed.

(** Norms on narrower strips are smaller. *)
Lemma nbound_mono (rho rho' M : R) (u : fser) :
  rho' <= rho -> nbound rho M u -> nbound rho' M u.
Proof.
  intros Hr H N. apply Rle_trans with (sqsum (nterm rho u) N); [| apply H].
  apply sqsum_le. intros m n. unfold nterm.
  apply Rmult_le_compat_l.
  - pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). lra.
  - unfold wt. apply exp_mono. apply Rmult_le_compat_r; [apply msize_nonneg | exact Hr].
Qed.

(** * Derivatives *)

(** d_t (a cos + b sin)(m t + n p) = m b cos - m a sin, and d_p with n. *)
Definition dt (u : fser) : fser :=
  {| fc := fun m n => IZR m * fs u m n ; fs := fun m n => - (IZR m * fc u m n) |}.
Definition dp (u : fser) : fser :=
  {| fc := fun m n => IZR n * fs u m n ; fs := fun m n => - (IZR n * fc u m n) |}.

(** A multiplier bounded by the mode size costs 1 / (e delta) of the strip. *)
Lemma nterm_mult_shift (rho delta c : R) (u : fser) (m n : Z) :
  0 < delta -> Rabs c <= msize m n ->
  (Rabs (c * fs u m n) + Rabs (- (c * fc u m n))) * wt (rho - delta) m n
    <= / (exp 1 * delta) * nterm rho u m n.
Proof.
  intros Hd Hc.
  rewrite Rabs_Ropp, !Rabs_mult, wt_shift.
  unfold nterm.
  set (A := Rabs (fc u m n)). set (B := Rabs (fs u m n)).
  assert (HA : 0 <= A) by apply Rabs_pos. assert (HB : 0 <= B) by apply Rabs_pos.
  assert (Hw : 0 < wt rho m n) by apply wt_pos.
  assert (Hs := msize_nonneg m n).
  assert (Hdec := exp_decay (msize m n) delta Hs Hd).
  assert (He : 0 < exp (- (delta * msize m n))) by apply exp_pos.
  assert (Hc0 : 0 <= Rabs c) by apply Rabs_pos.
  apply Rle_trans with ((A + B) * wt rho m n * (msize m n * exp (- (delta * msize m n)))).
  - replace ((Rabs c * B + Rabs c * A) * (wt rho m n * exp (- (delta * msize m n))))
      with ((A + B) * wt rho m n * (Rabs c * exp (- (delta * msize m n)))) by ring.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; lra |].
    apply Rmult_le_compat_r; lra.
  - replace (/ (exp 1 * delta) * ((A + B) * wt rho m n))
      with ((A + B) * wt rho m n * / (exp 1 * delta)) by ring.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact Hdec].
Qed.

Theorem nbound_dt (rho delta M : R) (u : fser) :
  0 < delta -> nbound rho M u -> nbound (rho - delta) (/ (exp 1 * delta) * M) (dt u).
Proof.
  intros Hd H N.
  apply Rle_trans with (sqsum (fun m n => / (exp 1 * delta) * nterm rho u m n) N).
  - apply sqsum_le. intros m n. unfold nterm at 1. simpl.
    apply nterm_mult_shift; [exact Hd |].
    unfold msize. pose proof (Rabs_pos (IZR n)). lra.
  - rewrite sqsum_scal.
    apply Rmult_le_compat_l; [| apply H].
    apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; [apply exp_pos | exact Hd].
Qed.

Theorem nbound_dp (rho delta M : R) (u : fser) :
  0 < delta -> nbound rho M u -> nbound (rho - delta) (/ (exp 1 * delta) * M) (dp u).
Proof.
  intros Hd H N.
  apply Rle_trans with (sqsum (fun m n => / (exp 1 * delta) * nterm rho u m n) N).
  - apply sqsum_le. intros m n. unfold nterm at 1. simpl.
    apply nterm_mult_shift; [exact Hd |].
    unfold msize. pose proof (Rabs_pos (IZR m)). lra.
  - rewrite sqsum_scal.
    apply Rmult_le_compat_l; [| apply H].
    apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; [apply exp_pos | exact Hd].
Qed.

(** * The operator L = rho0 d_t + d_p and its inverse *)

Definition divisor (rho0 : R) (m n : Z) : R := rho0 * IZR m + IZR n.

Definition lc (rho0 : R) (u : fser) : fser :=
  {| fc := fun m n => divisor rho0 m n * fs u m n ;
     fs := fun m n => - (divisor rho0 m n * fc u m n) |}.

Definition is_mean (m n : Z) : bool := (Z.eqb m 0 && Z.eqb n 0)%bool.

Definition linv (rho0 : R) (u : fser) : fser :=
  {| fc := fun m n => if is_mean m n then 0 else - (fs u m n / divisor rho0 m n) ;
     fs := fun m n => if is_mean m n then 0 else fc u m n / divisor rho0 m n |}.

Section Divisors.

Variables rho0 gamma : R.
Hypothesis Hdio : diophantine1 rho0 gamma.
Hypothesis Hg : 0 < gamma <= 1.

(** 1 / |divisor| <= (1 + |m| + |n|) / gamma off the mean. *)
Lemma divisor_bound (m n : Z) :
  is_mean m n = false ->
  0 < Rabs (divisor rho0 m n) /\ gamma <= Rabs (divisor rho0 m n) * (1 + msize m n).
Proof.
  intros Hmn. unfold is_mean in Hmn.
  assert (Hs := msize_nonneg m n).
  destruct (Z.eq_dec m 0) as [Hm | Hm].
  - subst m. rewrite Z.eqb_refl in Hmn. simpl in Hmn.
    assert (Hn : n <> 0%Z) by (intros ->; discriminate).
    pose proof (abs_IZR_ge_1 n Hn) as H1.
    unfold divisor. rewrite Rmult_0_r, Rplus_0_l.
    split; [lra |].
    apply Rle_trans with (1 * 1); [lra |].
    apply Rmult_le_compat; lra.
  - pose proof (abs_IZR_ge_1 m Hm) as H1.
    pose proof (Hdio (- n)%Z m Hm) as Hd.
    rewrite opp_IZR in Hd.
    replace (IZR m * rho0 - - IZR n) with (divisor rho0 m n) in Hd
      by (unfold divisor; ring).
    assert (Hpos : 0 < gamma / Rabs (IZR m)).
    { apply Rdiv_lt_0_compat; lra. }
    split; [lra |].
    apply Rle_trans with (Rabs (divisor rho0 m n) * Rabs (IZR m)).
    + apply Rmult_le_reg_r with (/ Rabs (IZR m)).
      { apply Rinv_0_lt_compat. lra. }
      replace (Rabs (divisor rho0 m n) * Rabs (IZR m) * / Rabs (IZR m))
        with (Rabs (divisor rho0 m n)) by (field; lra).
      exact Hd.
    + apply Rmult_le_compat_l; [apply Rabs_pos |].
      unfold msize. pose proof (Rabs_pos (IZR n)). lra.
Qed.

Definition linv_const (delta : R) : R := (1 + / (exp 1 * delta)) / gamma.

Theorem nbound_linv (rho delta M : R) (u : fser) :
  0 < delta -> nbound rho M u -> nbound (rho - delta) (linv_const delta * M) (linv rho0 u).
Proof.
  intros Hd H N.
  assert (Hc : 0 <= linv_const delta).
  { unfold linv_const. apply Rmult_le_pos.
    - assert (0 < / (exp 1 * delta)).
      { apply Rinv_0_lt_compat, Rmult_lt_0_compat; [apply exp_pos | exact Hd]. }
      lra.
    - apply Rlt_le, Rinv_0_lt_compat. lra. }
  apply Rle_trans with (sqsum (fun m n => linv_const delta * nterm rho u m n) N).
  - apply sqsum_le. intros m n. unfold nterm at 1. simpl.
    destruct (is_mean m n) eqn:Hmn.
    + rewrite Rabs_R0, Rplus_0_l, Rmult_0_l.
      apply Rmult_le_pos; [exact Hc | apply nterm_nonneg].
    + destruct (divisor_bound m n Hmn) as [Hd0 Hdg].
      set (D := Rabs (divisor rho0 m n)) in *.
      assert (Hdn : divisor rho0 m n <> 0).
      { intros E. unfold D in Hd0. rewrite E, Rabs_R0 in Hd0. lra. }
      unfold Rdiv. rewrite Rabs_Ropp, !Rabs_mult, Rabs_Rinv by exact Hdn. fold D.
      unfold nterm. rewrite wt_shift.
      set (A := Rabs (fc u m n)). set (B := Rabs (fs u m n)).
      assert (HA : 0 <= A) by apply Rabs_pos. assert (HB : 0 <= B) by apply Rabs_pos.
      assert (Hw : 0 < wt rho m n) by apply wt_pos.
      assert (Hs := msize_nonneg m n).
      assert (Hdec := exp_decay (msize m n) delta Hs Hd).
      assert (Hle1 : exp (- (delta * msize m n)) <= 1).
      { rewrite <- exp_0. apply exp_mono.
        pose proof (Rmult_le_pos delta (msize m n) (Rlt_le _ _ Hd) Hs). lra. }
      assert (He : 0 < exp (- (delta * msize m n))) by apply exp_pos.
      (* 1 / D <= (1 + s) / gamma, and (1 + s) e^(-delta s) <= 1 + 1/(e delta) *)
      assert (Hinv : / D <= (1 + msize m n) / gamma).
      { apply Rmult_le_reg_l with (D * gamma); [apply Rmult_lt_0_compat; lra |].
        replace (D * gamma * / D) with gamma by (field; lra).
        replace (D * gamma * ((1 + msize m n) / gamma)) with (D * (1 + msize m n))
          by (field; lra).
        exact Hdg. }
      assert (Hdecay : (1 + msize m n) * exp (- (delta * msize m n)) <= 1 + / (exp 1 * delta)).
      { rewrite Rmult_plus_distr_r, Rmult_1_l. lra. }
      replace ((B * / D + A * / D) * (wt rho m n * exp (- (delta * msize m n))))
        with ((A + B) * wt rho m n * (/ D * exp (- (delta * msize m n)))) by ring.
      replace (linv_const delta * ((A + B) * wt rho m n))
        with ((A + B) * wt rho m n * linv_const delta) by ring.
      apply Rmult_le_compat_l; [apply Rmult_le_pos; lra |].
      unfold linv_const.
      apply Rle_trans with ((1 + msize m n) / gamma * exp (- (delta * msize m n))).
      * apply Rmult_le_compat_r; lra.
      * replace ((1 + msize m n) / gamma * exp (- (delta * msize m n)))
          with ((1 + msize m n) * exp (- (delta * msize m n)) / gamma) by (field; lra).
        apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Hdecay].
  - rewrite sqsum_scal.
    apply Rmult_le_compat_l; [exact Hc | apply H].
Qed.

Theorem lc_linv (u : fser) (m n : Z) :
  is_mean m n = false ->
  fc (lc rho0 (linv rho0 u)) m n = fc u m n /\ fs (lc rho0 (linv rho0 u)) m n = fs u m n.
Proof.
  intros Hmn. destruct (divisor_bound m n Hmn) as [Hd0 _].
  assert (Hdn : divisor rho0 m n <> 0).
  { intros E. rewrite E, Rabs_R0 in Hd0. lra. }
  simpl. rewrite Hmn. split; field; exact Hdn.
Qed.

End Divisors.
