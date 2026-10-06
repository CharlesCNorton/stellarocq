(** Landreman's equilibria with sheared iota are exact solutions of ideal MHD.

    Landreman (arXiv:2609.26742, section 3) gives, for eps, S, lambda > 0,
    w = x + i y and the square root of positive real part,

      K = conj(w) sqrt(1 + eps / conj(w)^2),   Xi = w K + pi/2 - S,
      B_x + i B_y = e^(-i lambda z) i sin(Xi) / (2 K),
      B_z = Re(e^(-i lambda z) cos Xi) / lambda,
      psi = (sin^2(lambda z) + (lambda B_z)^2) / 2,   p = p_a - psi / lambda^2,

    smooth wherever (x, y) avoids the segment x = 0, |y| <= sqrt eps. The
    definitions below are these quantities in real and imaginary parts, in
    the form [Physics.exact_b] builds them for family 1: T = 1 + eps /
    conj(w)^2 = [Tre] + i [Tim], its square root [mre] + i [mim] with
    [mre] > 0, K = [Kre] + i [Kim] and Xi = [Xre] + i [Xim]. On that domain,
    with every partial derivative the derivative of the function along that
    axis, this file proves

      [sheared_divergence]   div B = 0,
      [sheared_force]        (curl B) x B = grad p,
      [sheared_tangent]      B . grad p = 0,

    so that B and p are an ideal-MHD equilibrium whose field lines lie on the
    level sets of p, which are those of psi. The partial derivatives of K are
    dK/dx = conj(w) / K and dK/dy = -i conj(w) / K, which [der_K_1] and
    [der_K_2] obtain by differentiating K^2 = conj(w)^2 + eps on a
    neighbourhood of the point. *)

From Stdlib Require Import Reals Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Landreman.

Local Open Scope R_scope.

Section Sheared.

Variables eps S lam : R.
Hypothesis Heps : 0 < eps.
Hypothesis Hlam : 0 < lam.

(** T = 1 + eps / conj(w)^2, its modulus, and its square root m of positive
    real part, with conj(w)^2 = (x - i y)^2 and 1 / conj(w)^2 = w^2 / |w|^4. *)
Definition rsq (x y : R) : R := x * x + y * y.
Definition Tre (x y : R) : R := 1 + eps * (x * x - y * y) / (rsq x y * rsq x y).
Definition Tim (x y : R) : R := eps * (2 * (x * y)) / (rsq x y * rsq x y).
Definition Tab (x y : R) : R := sqrt (Tre x y * Tre x y + Tim x y * Tim x y).
Definition mre (x y : R) : R := sqrt ((Tab x y + Tre x y) / 2).
Definition mim (x y : R) : R := Tim x y / (2 * mre x y).

(** K = conj(w) m and Xi = w K + pi/2 - S. *)
Definition Kre (x y : R) : R := x * mre x y + y * mim x y.
Definition Kim (x y : R) : R := x * mim x y - y * mre x y.
Definition Xre (x y : R) : R := x * Kre x y - y * Kim x y + (PI / 2 - S).
Definition Xim (x y : R) : R := x * Kim x y + y * Kre x y.

(** sin Xi = sre + i sim, cos Xi = cre + i cim, and W = i sin Xi / (2 K). *)
Definition chX (x y : R) : R := (exp (Xim x y) + exp (- Xim x y)) / 2.
Definition shX (x y : R) : R := (exp (Xim x y) - exp (- Xim x y)) / 2.
Definition sre (x y : R) : R := sin (Xre x y) * chX x y.
Definition sim (x y : R) : R := cos (Xre x y) * shX x y.
Definition cre (x y : R) : R := cos (Xre x y) * chX x y.
Definition cim (x y : R) : R := - (sin (Xre x y) * shX x y).
Definition Kn2 (x y : R) : R := 2 * (Kre x y * Kre x y + Kim x y * Kim x y).
Definition Wre (x y : R) : R := ((- sim x y) * Kre x y + sre x y * Kim x y) / Kn2 x y.
Definition Wim (x y : R) : R := (sre x y * Kre x y + sim x y * Kim x y) / Kn2 x y.

(** The field, psi and the pressure. *)
Definition Pz (x y z : R) : R := cos (lam * z) * cre x y + sin (lam * z) * cim x y.
Definition B1S (x y z : R) : R := cos (lam * z) * Wre x y + sin (lam * z) * Wim x y.
Definition B2S (x y z : R) : R := cos (lam * z) * Wim x y - sin (lam * z) * Wre x y.
Definition B3S (x y z : R) : R := Pz x y z / lam.
Definition psiS (x y z : R) : R := (sin (lam * z) * sin (lam * z) + Pz x y z * Pz x y z) / 2.
Definition presS (pa x y z : R) : R := pa - psiS x y z / (lam * lam).

(** The domain: (x, y) off the segment x = 0, |y| <= sqrt eps. *)
Definition DomS (x y : R) : Prop := x <> 0 \/ eps < y ^ 2.

(* ---------------------------------------------------------------- *)
(* The square root of T                                              *)

Lemma rsq_pos : forall x y, DomS x y -> 0 < rsq x y.
Proof.
  intros x y [H | H]; unfold rsq.
  - pose proof (Rsqr_pos_lt x H) as Hx. unfold Rsqr in Hx. nra.
  - nra.
Qed.

Lemma Tab_abs : forall x y, Rabs (Tre x y) <= Tab x y.
Proof.
  intros x y. unfold Tab. rewrite <- sqrt_Rsqr_abs. apply sqrt_le_1_alt.
  unfold Rsqr. nra.
Qed.

Lemma Tab_gt : forall x y, Tim x y <> 0 -> Rabs (Tre x y) < Tab x y.
Proof.
  intros x y H. unfold Tab. rewrite <- sqrt_Rsqr_abs. apply sqrt_lt_1_alt.
  pose proof (Rsqr_pos_lt _ H) as Hi. unfold Rsqr in *. split; nra.
Qed.

(** T lies off the half-line of the non-positive reals. *)
Lemma Tsum_pos : forall x y, DomS x y -> 0 < Tab x y + Tre x y.
Proof.
  intros x y H. pose proof (rsq_pos x y H) as Hr.
  destruct (Req_dec (Tim x y) 0) as [H0 | H0].
  - assert (Hp : 0 < Tre x y).
    { assert (Hxy : x * y = 0).
      { unfold Tim, Rdiv in H0. apply Rmult_integral in H0. destruct H0 as [H0 | H0].
        - apply Rmult_integral in H0. destruct H0 as [H0 | H0]; lra.
        - exfalso. revert H0. apply Rinv_neq_0_compat.
          apply Rmult_integral_contrapositive_currified; lra. }
      apply Rmult_integral in Hxy.
      destruct H as [H | H]; destruct Hxy as [E | E].
      - exfalso. exact (H E).
      - subst y. unfold Tre, rsq.
        pose proof (Rsqr_pos_lt x H) as Hx. unfold Rsqr in Hx.
        replace (eps * (x * x - 0 * 0) / ((x * x + 0 * 0) * (x * x + 0 * 0)))
          with (eps / (x * x)) by (field; repeat split; first [exact H | nra]).
        assert (0 < eps / (x * x)) by (apply Rdiv_lt_0_compat; lra). lra.
      - subst x. unfold Tre, rsq.
        assert (Hy : 0 < y * y) by nra.
        replace (eps * (0 * 0 - y * y) / ((0 * 0 + y * y) * (0 * 0 + y * y)))
          with (- (eps / (y * y))) by (field; nra).
        assert (eps / (y * y) < 1).
        { apply (Rmult_lt_reg_r (y * y)); [exact Hy |].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
        lra.
      - subst y. exfalso. nra. }
    pose proof (Tab_abs x y) as Ha. rewrite Rabs_right in Ha by lra. lra.
  - pose proof (Tab_gt x y H0) as Ha. pose proof (Rabs_maj2 (Tre x y)). lra.
Qed.

Lemma T2_pos : forall x y, DomS x y -> 0 < Tre x y * Tre x y + Tim x y * Tim x y.
Proof.
  intros x y H. pose proof (Tsum_pos x y H) as Hs. pose proof (Tab_abs x y) as Ha.
  pose proof (Rle_abs (Tre x y)) as Hl.
  assert (Hn : 0 <= Tre x y * Tre x y + Tim x y * Tim x y) by nra.
  destruct Hn as [Hn | Hn]; [exact Hn |].
  exfalso. unfold Tab in Hs, Ha. rewrite <- Hn in Hs, Ha. rewrite sqrt_0 in Hs, Ha. lra.
Qed.

Lemma mre_pos : forall x y, DomS x y -> 0 < mre x y.
Proof. intros x y H. unfold mre. apply sqrt_lt_R0. pose proof (Tsum_pos x y H). lra. Qed.

Lemma mre_sq : forall x y, DomS x y -> mre x y * mre x y = (Tab x y + Tre x y) / 2.
Proof. intros x y H. unfold mre. apply sqrt_sqrt. pose proof (Tsum_pos x y H). lra. Qed.

Lemma Tab_sq : forall x y, Tab x y * Tab x y = Tre x y * Tre x y + Tim x y * Tim x y.
Proof. intros x y. unfold Tab. apply sqrt_sqrt. nra. Qed.

(** m^2 = T. *)
Lemma root_re : forall x y, DomS x y -> mre x y * mre x y - mim x y * mim x y = Tre x y.
Proof.
  intros x y H.
  pose proof (mre_pos x y H) as Hm. pose proof (mre_sq x y H) as Hm2.
  pose proof (Tab_sq x y) as HT2. pose proof (Tsum_pos x y H) as HT.
  unfold mim.
  replace (Tim x y / (2 * mre x y) * (Tim x y / (2 * mre x y)))
    with (Tim x y * Tim x y / (4 * (mre x y * mre x y))) by (field; lra).
  rewrite Hm2.
  replace (Tim x y * Tim x y) with ((Tab x y + Tre x y) * (Tab x y - Tre x y)) by nra.
  field. lra.
Qed.

Lemma root_im : forall x y, DomS x y -> 2 * mre x y * mim x y = Tim x y.
Proof. intros x y H. pose proof (mre_pos x y H). unfold mim. field. lra. Qed.

(** K^2 = conj(w)^2 + eps, and K is not zero. *)
Lemma K2_re : forall x y, DomS x y ->
  Kre x y * Kre x y - Kim x y * Kim x y = x * x - y * y + eps.
Proof.
  intros x y H. pose proof (rsq_pos x y H) as Hr.
  replace (Kre x y * Kre x y - Kim x y * Kim x y)
    with ((x * x - y * y) * (mre x y * mre x y - mim x y * mim x y)
          + 2 * (x * y) * (2 * mre x y * mim x y)) by (unfold Kre, Kim; ring).
  rewrite root_re, root_im by exact H.
  unfold Tre, Tim. unfold rsq in *. field. lra.
Qed.

Lemma K2_im : forall x y, DomS x y -> Kre x y * Kim x y = - (x * y).
Proof.
  intros x y H. pose proof (rsq_pos x y H) as Hr.
  replace (Kre x y * Kim x y)
    with ((x * x - y * y) * (2 * mre x y * mim x y) / 2
          - x * y * (mre x y * mre x y - mim x y * mim x y)) by (unfold Kre, Kim; field).
  rewrite root_re, root_im by exact H.
  unfold Tre, Tim. unfold rsq in *. field. lra.
Qed.

Lemma Kn_pos : forall x y, DomS x y -> 0 < Kre x y * Kre x y + Kim x y * Kim x y.
Proof.
  intros x y H. pose proof (rsq_pos x y H) as Hr. pose proof (mre_pos x y H) as Hm.
  replace (Kre x y * Kre x y + Kim x y * Kim x y)
    with (rsq x y * (mre x y * mre x y + mim x y * mim x y)) by (unfold Kre, Kim, rsq; ring).
  apply Rmult_lt_0_compat; [exact Hr | nra].
Qed.

(* ---------------------------------------------------------------- *)
(* The derivatives of K and Xi                                       *)

(** The domain is open along each horizontal axis. *)
Lemma sq_loc : forall c y, c < y ^ 2 -> locally y (fun t => c < t ^ 2).
Proof.
  intros c y H.
  assert (Hc : filterlim (fun t : R => t ^ 2) (locally y) (locally (y ^ 2))).
  { apply (@ex_derive_continuous R_AbsRing R_NormedModule (fun t : R => t ^ 2) y).
    auto_derive. exact I. }
  exact (Hc (fun u => c < u) (open_gt c (y ^ 2) H)).
Qed.

Lemma dom_locx : forall x y, DomS x y -> locally x (fun t => DomS t y).
Proof.
  intros x y [H | H].
  - assert (Hx : 0 < x ^ 2) by (pose proof (Rsqr_pos_lt x H) as Hs; unfold Rsqr in Hs; nra).
    apply (filter_imp (fun t => 0 < t ^ 2)); [| exact (sq_loc 0 x Hx)].
    intros t Ht. left. intros E. rewrite E in Ht. nra.
  - apply filter_forall. intros t. right. exact H.
Qed.

Lemma dom_locy : forall x y, DomS x y -> locally y (fun t => DomS x t).
Proof.
  intros x y [H | H].
  - apply filter_forall. intros t. left. exact H.
  - apply (filter_imp (fun t => eps < t ^ 2)); [| exact (sq_loc eps y H)].
    intros t Ht. right. exact Ht.
Qed.

(** The facts the side conditions of [auto_derive] need, in the unfolded
    form in which it states them, a - b as a + - b and a / b as a * / b. *)
Ltac dom_facts x y H :=
  let F1 := fresh "F" in let F2 := fresh "F" in
  let F3 := fresh "F" in let F4 := fresh "F" in
  pose proof (rsq_pos x y H) as F1; pose proof (Tsum_pos x y H) as F2;
  pose proof (mre_pos x y H) as F3; pose proof (T2_pos x y H) as F4;
  unfold mre, Tab, Tre, Tim, rsq, Rminus, Rdiv in F1, F2, F3, F4.

Ltac dom_side :=
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I | assumption | lra
        | apply Rmult_integral_contrapositive_currified; lra ].

Lemma ex_K_1 : forall x y, DomS x y ->
  ex_derive (fun t => Kre t y) x /\ ex_derive (fun t => Kim t y) x.
Proof.
  intros x y H. dom_facts x y H.
  split; unfold Kre, Kim, mim, mre, Tab, Tre, Tim, rsq; auto_derive; dom_side.
Qed.

Lemma ex_K_2 : forall x y, DomS x y ->
  ex_derive (fun t => Kre x t) y /\ ex_derive (fun t => Kim x t) y.
Proof.
  intros x y H. dom_facts x y H.
  split; unfold Kre, Kim, mim, mre, Tab, Tre, Tim, rsq; auto_derive; dom_side.
Qed.

(** dK/dx = conj(w) / K and dK/dy = -i conj(w) / K. *)
Definition dKre1 (x y : R) : R :=
  (x * Kre x y - y * Kim x y) / (Kre x y * Kre x y + Kim x y * Kim x y).
Definition dKim1 (x y : R) : R :=
  - (x * Kim x y + y * Kre x y) / (Kre x y * Kre x y + Kim x y * Kim x y).
Definition dKre2 (x y : R) : R :=
  - (x * Kim x y + y * Kre x y) / (Kre x y * Kre x y + Kim x y * Kim x y).
Definition dKim2 (x y : R) : R :=
  - (x * Kre x y - y * Kim x y) / (Kre x y * Kre x y + Kim x y * Kim x y).

Lemma der_K_1 : forall x y, DomS x y ->
  is_derive (fun t => Kre t y) x (dKre1 x y) /\ is_derive (fun t => Kim t y) x (dKim1 x y).
Proof.
  intros x y H. destruct (ex_K_1 x y H) as [EKr EKi].
  pose proof (Derive_correct _ _ EKr) as DKr. pose proof (Derive_correct _ _ EKi) as DKi.
  pose proof (Kn_pos x y H) as Hk.
  assert (E1 : Kre x y * Derive (fun t => Kre t y) x - Kim x y * Derive (fun t => Kim t y) x = x).
  { assert (D1 : is_derive (fun t => Kre t y * Kre t y - Kim t y * Kim t y) x
                   (2 * (Kre x y * Derive (fun t => Kre t y) x
                         - Kim x y * Derive (fun t => Kim t y) x))).
    { auto_derive; [repeat split; first [exact I | assumption] | ring]. }
    assert (D2 : is_derive (fun t => Kre t y * Kre t y - Kim t y * Kim t y) x (2 * x)).
    { apply (is_derive_ext_loc (fun t => t * t - y * y + eps)).
      - apply (filter_imp (fun t => DomS t y)); [| exact (dom_locx x y H)].
        intros t Ht. symmetry. exact (K2_re t y Ht).
      - auto_derive; [exact I | ring]. }
    pose proof (is_derive_unique _ _ _ D1) as U1. pose proof (is_derive_unique _ _ _ D2) as U2.
    lra. }
  assert (E2 : Derive (fun t => Kre t y) x * Kim x y + Kre x y * Derive (fun t => Kim t y) x = - y).
  { assert (D1 : is_derive (fun t => Kre t y * Kim t y) x
                   (Derive (fun t => Kre t y) x * Kim x y + Kre x y * Derive (fun t => Kim t y) x)).
    { auto_derive; [repeat split; first [exact I | assumption] | ring]. }
    assert (D2 : is_derive (fun t => Kre t y * Kim t y) x (- y)).
    { apply (is_derive_ext_loc (fun t => - (t * y))).
      - apply (filter_imp (fun t => DomS t y)); [| exact (dom_locx x y H)].
        intros t Ht. symmetry. exact (K2_im t y Ht).
      - auto_derive; [exact I | ring]. }
    pose proof (is_derive_unique _ _ _ D1) as U1. pose proof (is_derive_unique _ _ _ D2) as U2.
    lra. }
  assert (A : Derive (fun t => Kre t y) x * (Kre x y * Kre x y + Kim x y * Kim x y)
              = x * Kre x y - y * Kim x y).
  { transitivity (Kre x y * (Kre x y * Derive (fun t => Kre t y) x
                              - Kim x y * Derive (fun t => Kim t y) x)
                  + Kim x y * (Derive (fun t => Kre t y) x * Kim x y
                               + Kre x y * Derive (fun t => Kim t y) x)); [ring |].
    rewrite E1, E2. ring. }
  assert (B : Derive (fun t => Kim t y) x * (Kre x y * Kre x y + Kim x y * Kim x y)
              = - (x * Kim x y + y * Kre x y)).
  { transitivity (Kre x y * (Derive (fun t => Kre t y) x * Kim x y
                              + Kre x y * Derive (fun t => Kim t y) x)
                  - Kim x y * (Kre x y * Derive (fun t => Kre t y) x
                               - Kim x y * Derive (fun t => Kim t y) x)); [ring |].
    rewrite E1, E2. ring. }
  split.
  - replace (dKre1 x y) with (Derive (fun t => Kre t y) x)
      by (unfold dKre1; rewrite <- A; field; lra).
    exact DKr.
  - replace (dKim1 x y) with (Derive (fun t => Kim t y) x)
      by (unfold dKim1; rewrite <- B; field; lra).
    exact DKi.
Qed.

Lemma der_K_2 : forall x y, DomS x y ->
  is_derive (fun t => Kre x t) y (dKre2 x y) /\ is_derive (fun t => Kim x t) y (dKim2 x y).
Proof.
  intros x y H. destruct (ex_K_2 x y H) as [EKr EKi].
  pose proof (Derive_correct _ _ EKr) as DKr. pose proof (Derive_correct _ _ EKi) as DKi.
  pose proof (Kn_pos x y H) as Hk.
  assert (E1 : Kre x y * Derive (fun t => Kre x t) y - Kim x y * Derive (fun t => Kim x t) y = - y).
  { assert (D1 : is_derive (fun t => Kre x t * Kre x t - Kim x t * Kim x t) y
                   (2 * (Kre x y * Derive (fun t => Kre x t) y
                         - Kim x y * Derive (fun t => Kim x t) y))).
    { auto_derive; [repeat split; first [exact I | assumption] | ring]. }
    assert (D2 : is_derive (fun t => Kre x t * Kre x t - Kim x t * Kim x t) y (- (2 * y))).
    { apply (is_derive_ext_loc (fun t => x * x - t * t + eps)).
      - apply (filter_imp (fun t => DomS x t)); [| exact (dom_locy x y H)].
        intros t Ht. symmetry. exact (K2_re x t Ht).
      - auto_derive; [exact I | ring]. }
    pose proof (is_derive_unique _ _ _ D1) as U1. pose proof (is_derive_unique _ _ _ D2) as U2.
    lra. }
  assert (E2 : Derive (fun t => Kre x t) y * Kim x y + Kre x y * Derive (fun t => Kim x t) y = - x).
  { assert (D1 : is_derive (fun t => Kre x t * Kim x t) y
                   (Derive (fun t => Kre x t) y * Kim x y + Kre x y * Derive (fun t => Kim x t) y)).
    { auto_derive; [repeat split; first [exact I | assumption] | ring]. }
    assert (D2 : is_derive (fun t => Kre x t * Kim x t) y (- x)).
    { apply (is_derive_ext_loc (fun t => - (x * t))).
      - apply (filter_imp (fun t => DomS x t)); [| exact (dom_locy x y H)].
        intros t Ht. symmetry. exact (K2_im x t Ht).
      - auto_derive; [exact I | ring]. }
    pose proof (is_derive_unique _ _ _ D1) as U1. pose proof (is_derive_unique _ _ _ D2) as U2.
    lra. }
  assert (A : Derive (fun t => Kre x t) y * (Kre x y * Kre x y + Kim x y * Kim x y)
              = - (x * Kim x y + y * Kre x y)).
  { transitivity (Kre x y * (Kre x y * Derive (fun t => Kre x t) y
                              - Kim x y * Derive (fun t => Kim x t) y)
                  + Kim x y * (Derive (fun t => Kre x t) y * Kim x y
                               + Kre x y * Derive (fun t => Kim x t) y)); [ring |].
    rewrite E1, E2. ring. }
  assert (B : Derive (fun t => Kim x t) y * (Kre x y * Kre x y + Kim x y * Kim x y)
              = - (x * Kre x y - y * Kim x y)).
  { transitivity (Kre x y * (Derive (fun t => Kre x t) y * Kim x y
                              + Kre x y * Derive (fun t => Kim x t) y)
                  - Kim x y * (Kre x y * Derive (fun t => Kre x t) y
                               - Kim x y * Derive (fun t => Kim x t) y)); [ring |].
    rewrite E1, E2. ring. }
  split.
  - replace (dKre2 x y) with (Derive (fun t => Kre x t) y)
      by (unfold dKre2; rewrite <- A; field; lra).
    exact DKr.
  - replace (dKim2 x y) with (Derive (fun t => Kim x t) y)
      by (unfold dKim2; rewrite <- B; field; lra).
    exact DKi.
Qed.

Definition dXre1 (x y : R) : R := Kre x y + x * dKre1 x y - y * dKim1 x y.
Definition dXim1 (x y : R) : R := Kim x y + x * dKim1 x y + y * dKre1 x y.
Definition dXre2 (x y : R) : R := x * dKre2 x y - (Kim x y + y * dKim2 x y).
Definition dXim2 (x y : R) : R := x * dKim2 x y + (Kre x y + y * dKre2 x y).

Lemma der_X_1 : forall x y, DomS x y ->
  is_derive (fun t => Xre t y) x (dXre1 x y) /\ is_derive (fun t => Xim t y) x (dXim1 x y).
Proof.
  intros x y H. destruct (der_K_1 x y H) as [DKr DKi].
  assert (UKr : Derive (fun t : R => Kre t y) x = dKre1 x y) by exact (is_derive_unique _ _ _ DKr).
  assert (UKi : Derive (fun t : R => Kim t y) x = dKim1 x y) by exact (is_derive_unique _ _ _ DKi).
  split.
  - unfold Xre, dXre1. auto_derive.
    + repeat split; first [exact I | eexists; eassumption].
    + rewrite UKr, UKi. ring.
  - unfold Xim, dXim1. auto_derive.
    + repeat split; first [exact I | eexists; eassumption].
    + rewrite UKr, UKi. ring.
Qed.

Lemma der_X_2 : forall x y, DomS x y ->
  is_derive (fun t => Xre x t) y (dXre2 x y) /\ is_derive (fun t => Xim x t) y (dXim2 x y).
Proof.
  intros x y H. destruct (der_K_2 x y H) as [DKr DKi].
  assert (UKr : Derive (fun t : R => Kre x t) y = dKre2 x y) by exact (is_derive_unique _ _ _ DKr).
  assert (UKi : Derive (fun t : R => Kim x t) y = dKim2 x y) by exact (is_derive_unique _ _ _ DKi).
  split.
  - unfold Xre, dXre2. auto_derive.
    + repeat split; first [exact I | eexists; eassumption].
    + rewrite UKr, UKi. ring.
  - unfold Xim, dXim2. auto_derive.
    + repeat split; first [exact I | eexists; eassumption].
    + rewrite UKr, UKi. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* The identities                                                    *)

(** The derivatives of K and Xi along x and y, and the facts [field] needs. *)
Ltac atoms_der x y H :=
  destruct (der_K_1 x y H) as [DKr1 DKi1]; destruct (der_K_2 x y H) as [DKr2 DKi2];
  destruct (der_X_1 x y H) as [DXr1 DXi1]; destruct (der_X_2 x y H) as [DXr2 DXi2];
  assert (U1 : Derive (fun t : R => Kre t y) x = dKre1 x y) by exact (is_derive_unique _ _ _ DKr1);
  assert (U2 : Derive (fun t : R => Kim t y) x = dKim1 x y) by exact (is_derive_unique _ _ _ DKi1);
  assert (U3 : Derive (fun t : R => Kre x t) y = dKre2 x y) by exact (is_derive_unique _ _ _ DKr2);
  assert (U4 : Derive (fun t : R => Kim x t) y = dKim2 x y) by exact (is_derive_unique _ _ _ DKi2);
  assert (U5 : Derive (fun t : R => Xre t y) x = dXre1 x y) by exact (is_derive_unique _ _ _ DXr1);
  assert (U6 : Derive (fun t : R => Xim t y) x = dXim1 x y) by exact (is_derive_unique _ _ _ DXi1);
  assert (U7 : Derive (fun t : R => Xre x t) y = dXre2 x y) by exact (is_derive_unique _ _ _ DXr2);
  assert (U8 : Derive (fun t : R => Xim x t) y = dXim2 x y) by exact (is_derive_unique _ _ _ DXi2);
  pose proof (Kn_pos x y H) as Hk;
  assert (Hx : exp (Xim x y) <> 0) by (apply Rgt_not_eq, exp_pos).

Ltac pd_unfold :=
  unfold B1S, B2S, B3S, presS, psiS, Pz, Wre, Wim, Kn2, sre, sim, cre, cim, chX, shX.

Ltac pd_side :=
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I | eexists; eassumption | lra
        | apply Rmult_integral_contrapositive_currified; lra ].

(** [pd_eq E (pd1 f x y z)] proves E : pd1 f x y z = D, with D the
    derivative [auto_derive] computes, in terms of the derivatives of K and
    Xi. *)
Tactic Notation "pd_eq" ident(E) constr(t) :=
  eassert (E : t = _);
  [ unfold pd1, pd2, pd3; apply is_derive_unique; pd_unfold; auto_derive;
    [pd_side | reflexivity] | ].

Ltac pd_close :=
  repeat match goal with U : Derive ?f ?p = _ |- context [Derive ?f ?p] => rewrite U end;
  unfold dXre1, dXim1, dXre2, dXim2, dKre1, dKim1, dKre2, dKim2;
  pd_unfold; rewrite ?exp_Ropp.

Theorem sheared_divergence : forall x y z, DomS x y ->
  pd1 B1S x y z + pd2 B2S x y z + pd3 B3S x y z = 0.
Proof.
  intros x y z H. atoms_der x y H.
  pd_eq E1 (pd1 B1S x y z). pd_eq E2 (pd2 B2S x y z). pd_eq E3 (pd3 B3S x y z).
  rewrite E1, E2, E3. pd_close.
  field. repeat split; lra.
Qed.

(** Force balance, (curl B) x B = grad p, component by component, the curl
    and the gradient taken from the partial derivatives. *)
Theorem sheared_force : forall pa x y z, DomS x y ->
  let J1 := pd2 B3S x y z - pd3 B2S x y z in
  let J2 := pd3 B1S x y z - pd1 B3S x y z in
  let J3 := pd1 B2S x y z - pd2 B1S x y z in
  J2 * B3S x y z - J3 * B2S x y z = pd1 (presS pa) x y z /\
  J3 * B1S x y z - J1 * B3S x y z = pd2 (presS pa) x y z /\
  J1 * B2S x y z - J2 * B1S x y z = pd3 (presS pa) x y z.
Proof.
  intros pa x y z H J1 J2 J3. atoms_der x y H.
  pd_eq E11 (pd1 B1S x y z). pd_eq E21 (pd2 B1S x y z). pd_eq E31 (pd3 B1S x y z).
  pd_eq E12 (pd1 B2S x y z). pd_eq E22 (pd2 B2S x y z). pd_eq E32 (pd3 B2S x y z).
  pd_eq E13 (pd1 B3S x y z). pd_eq E23 (pd2 B3S x y z). pd_eq E33 (pd3 B3S x y z).
  pd_eq P1 (pd1 (presS pa) x y z). pd_eq P2 (pd2 (presS pa) x y z).
  pd_eq P3 (pd3 (presS pa) x y z).
  unfold J1, J2, J3.
  split; [| split].
  - rewrite ?E11, ?E21, ?E31, ?E12, ?E22, ?E32, ?E13, ?E23, ?E33, P1. pd_close.
    field. repeat split; lra.
  - rewrite ?E11, ?E21, ?E31, ?E12, ?E22, ?E32, ?E13, ?E23, ?E33, P2. pd_close.
    field. repeat split; lra.
  - (* the vertical component also uses sin^2 + cos^2 = 1 at Re Xi *)
    transitivity (pd3 (presS pa) x y z
                  + (- (cos (lam * z) * sin (lam * z)) / lam)
                    * (sin (Xre x y) * sin (Xre x y) + cos (Xre x y) * cos (Xre x y) - 1)).
    + rewrite ?E11, ?E21, ?E31, ?E12, ?E22, ?E32, ?E13, ?E23, ?E33, P3. pd_close.
      field. repeat split; lra.
    + pose proof (sin2_cos2 (Xre x y)) as T. unfold Rsqr in T. rewrite T. ring.
Qed.

(** The field lines lie on the level sets of p = p_a - psi / lambda^2, which
    are those of psi: B . grad p = B . ((curl B) x B) = 0. *)
Theorem sheared_tangent : forall pa x y z, DomS x y ->
  B1S x y z * pd1 (presS pa) x y z + B2S x y z * pd2 (presS pa) x y z
  + B3S x y z * pd3 (presS pa) x y z = 0.
Proof.
  intros pa x y z H.
  pose proof (sheared_force pa x y z H) as HF. cbv zeta in HF.
  destruct HF as (F1 & F2 & F3).
  rewrite <- F1, <- F2, <- F3. ring.
Qed.

End Sheared.
