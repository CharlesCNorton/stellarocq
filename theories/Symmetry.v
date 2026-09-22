(** A quasisymmetric field makes both certified quasisymmetry residuals
    vanish.

    A field is quasisymmetric when its strength depends on the angles of a
    surface only through one combination chi = M theta_B - N zeta_B of the
    Boozer angles. Two residuals of that property are certified: the
    two-term ratio (B x grad s . grad B) / (B . grad B) of Physics.qs2_b,
    which quasisymmetry makes a flux function, and the triple product
    grad s . (grad B x grad(B . grad B)) of Physics.qs_b, which it makes
    vanish. A verdict bounds one of them away from zero and reads that as a
    departure from quasisymmetry, so what a verdict rests on is the direction
    from quasisymmetry to the identity, and that direction is proven here on
    the reconstruction: the Boozer angles are the map Physics.v writes, with
    p = (w - I lambda) / (G + iota I), the covariant components are the
    stream function's, B_u = I + w_u and B_v = G + w_v, and the square field
    is B^u B_u + B^v B_v.

    Everything is a function of the two angles of one surface, with partial
    derivatives taken as derivatives of the sections in each angle, so the
    calculus is the one-variable calculus of the standard library and the
    rest is algebra. The converse, that a vanishing triple product forces
    quasisymmetry, is not needed by any verdict and is not proven. *)

From Coq Require Import Reals Lra Lia.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics.

Local Open Scope R_scope.

(** Two functions equal everywhere have the same derivatives. *)
Lemma derivable_pt_lim_ext :
  forall (f g : R -> R) x l,
  (forall y, f y = g y) -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros f g x l Hfg H eps Heps.
  destruct (H eps Heps) as [delta Hd].
  exists delta. intros h Hh Hhd.
  rewrite <- (Hfg (x + h)), <- (Hfg x). now apply Hd.
Qed.

(** The derivative of an affine combination of two functions. *)
Lemma derivable_pt_lim_lin :
  forall (f g : R -> R) x lf lg a b,
  derivable_pt_lim f x lf -> derivable_pt_lim g x lg ->
  derivable_pt_lim (fun y => a * f y + b * g y) x (a * lf + b * lg).
Proof.
  intros f g x lf lg a b Hf Hg.
  apply (derivable_pt_lim_ext (plus_fct (mult_real_fct a f) (mult_real_fct b g))).
  - intros y. unfold plus_fct, mult_real_fct. reflexivity.
  - apply derivable_pt_lim_plus; apply derivable_pt_lim_scal; assumption.
Qed.

Section Surface.

(** The stream function of the flux coordinates and the Boozer stream
    function, as functions of the two angles, with their partial
    derivatives. *)
Variable lam w lam_u lam_v w_u w_v : R -> R -> R.
Hypothesis Hlu : forall u v, derivable_pt_lim (fun x => lam x v) u (lam_u u v).
Hypothesis Hlv : forall u v, derivable_pt_lim (fun y => lam u y) v (lam_v u v).
Hypothesis Hwu : forall u v, derivable_pt_lim (fun x => w x v) u (w_u u v).
Hypothesis Hwv : forall u v, derivable_pt_lim (fun y => w u y) v (w_v u v).

(** The two flux functions of the Boozer form, the rotational transform, the
    flux derivative and the helicity. *)
Variable I G iota phip M N : R.
Hypothesis Hden : G + iota * I <> 0.
Hypothesis Hphip : phip <> 0.

(* ---------------------------------------------------------------- *)
(* The Boozer angles                                                 *)

Definition inv_den : R := / (G + iota * I).
Definition p (u v : R) : R := inv_den * (w u v - I * lam u v).
Definition p_u (u v : R) : R := inv_den * (w_u u v - I * lam_u u v).
Definition p_v (u v : R) : R := inv_den * (w_v u v - I * lam_v u v).

Lemma p_du : forall u v, derivable_pt_lim (fun x => p x v) u (p_u u v).
Proof.
  intros u v. unfold p, p_u.
  apply (derivable_pt_lim_ext
           (fun x => inv_den * (1 * w x v + (- I) * lam x v) + 0 * 0)).
  - intros y. ring.
  - replace (inv_den * (w_u u v - I * lam_u u v))
      with (inv_den * (1 * w_u u v + (- I) * lam_u u v) + 0 * 0) by ring.
    apply derivable_pt_lim_lin.
    + apply derivable_pt_lim_lin. apply Hwu. apply Hlu.
    + apply derivable_pt_lim_const.
Qed.

Lemma p_dv : forall u v, derivable_pt_lim (fun y => p u y) v (p_v u v).
Proof.
  intros u v. unfold p, p_v.
  apply (derivable_pt_lim_ext
           (fun y => inv_den * (1 * w u y + (- I) * lam u y) + 0 * 0)).
  - intros y. ring.
  - replace (inv_den * (w_v u v - I * lam_v u v))
      with (inv_den * (1 * w_v u v + (- I) * lam_v u v) + 0 * 0) by ring.
    apply derivable_pt_lim_lin.
    + apply derivable_pt_lim_lin. apply Hwv. apply Hlv.
    + apply derivable_pt_lim_const.
Qed.

Definition thB (u v : R) : R := u + lam u v + iota * p u v.
Definition zeB (u v : R) : R := v + p u v.
Definition chi (u v : R) : R := M * thB u v - N * zeB u v.

Definition th_u (u v : R) : R := 1 + lam_u u v + iota * p_u u v.
Definition th_v (u v : R) : R := lam_v u v + iota * p_v u v.
Definition ze_u (u v : R) : R := p_u u v.
Definition ze_v (u v : R) : R := 1 + p_v u v.
Definition chi_u (u v : R) : R := M * th_u u v - N * ze_u u v.
Definition chi_v (u v : R) : R := M * th_v u v - N * ze_v u v.

Lemma chi_du : forall u v, derivable_pt_lim (fun x => chi x v) u (chi_u u v).
Proof.
  intros u v. unfold chi, chi_u, thB, zeB, th_u, ze_u.
  apply (derivable_pt_lim_ext
           (fun x => M * (1 * (1 * x + 1 * lam x v) + iota * p x v)
                     + (- N) * (1 * v + 1 * p x v))).
  - intros y. ring.
  - replace (M * (1 + lam_u u v + iota * p_u u v) - N * p_u u v)
      with (M * (1 * (1 * 1 + 1 * lam_u u v) + iota * p_u u v)
            + (- N) * (1 * 0 + 1 * p_u u v)) by ring.
    apply derivable_pt_lim_lin.
    + apply derivable_pt_lim_lin.
      * apply derivable_pt_lim_lin. apply derivable_pt_lim_id. apply Hlu.
      * apply p_du.
    + apply derivable_pt_lim_lin. apply derivable_pt_lim_const. apply p_du.
Qed.

Lemma chi_dv : forall u v, derivable_pt_lim (fun y => chi u y) v (chi_v u v).
Proof.
  intros u v. unfold chi, chi_v, thB, zeB, th_v, ze_v.
  apply (derivable_pt_lim_ext
           (fun y => M * (1 * (1 * u + 1 * lam u y) + iota * p u y)
                     + (- N) * (1 * y + 1 * p u y))).
  - intros y. ring.
  - replace (M * (lam_v u v + iota * p_v u v) - N * (1 + p_v u v))
      with (M * (1 * (1 * 0 + 1 * lam_v u v) + iota * p_v u v)
            + (- N) * (1 * 1 + 1 * p_v u v)) by ring.
    apply derivable_pt_lim_lin.
    + apply derivable_pt_lim_lin.
      * apply derivable_pt_lim_lin. apply derivable_pt_lim_const. apply Hlv.
      * apply p_dv.
    + apply derivable_pt_lim_lin. apply derivable_pt_lim_id. apply p_dv.
Qed.

(* ---------------------------------------------------------------- *)
(* The field                                                         *)

(** The Jacobian of the flux coordinates, nowhere zero on the surface. *)
Variable J : R -> R -> R.
Hypothesis HJ : forall u v, J u v <> 0.

(** sqrt(g) B^u and sqrt(g) B^v from the ansatz, the covariant components
    from the Boozer stream function, and the square field. *)
Definition U (u v : R) : R := phip * (iota - lam_v u v).
Definition V (u v : R) : R := phip * (1 + lam_u u v).
Definition Bu (u v : R) : R := I + w_u u v.
Definition Bv (u v : R) : R := G + w_v u v.
Definition B2 (u v : R) : R := (U u v * Bu u v + V u v * Bv u v) / J u v.

(** The Jacobian of the Boozer angle map. *)
Definition D (u v : R) : R := th_u u v * ze_v u v - th_v u v * ze_u u v.

(** The covariant components through the map. *)
Lemma boozer_cov_u : forall u v, Bu u v = I * th_u u v + G * ze_u u v.
Proof.
  intros u v. unfold Bu, th_u, ze_u, p_u, inv_den. field. exact Hden.
Qed.

Lemma boozer_cov_v : forall u v, Bv u v = I * th_v u v + G * ze_v u v.
Proof.
  intros u v. unfold Bv, th_v, ze_v, p_v, inv_den. field. exact Hden.
Qed.

(** The flux-weighted field along chi, and the covariant components against
    it, are both the map's Jacobian times a flux function. *)
Lemma flux_weighted :
  forall u v, U u v * chi_u u v + V u v * chi_v u v = phip * (M * iota - N) * D u v.
Proof.
  intros u v. unfold U, V, chi_u, chi_v, D, th_u, th_v, ze_u, ze_v. ring.
Qed.

Lemma cov_kernel :
  forall u v, Bv u v * chi_u u v - Bu u v * chi_v u v = (I * N + G * M) * D u v.
Proof.
  intros u v. rewrite boozer_cov_u, boozer_cov_v. unfold chi_u, chi_v, D. ring.
Qed.

(** And so is the square field. *)
Lemma B2_D : forall u v, B2 u v * J u v = phip * (G + iota * I) * D u v.
Proof.
  intros u v. unfold B2. rewrite boozer_cov_u, boozer_cov_v.
  unfold U, V, D, th_u, th_v, ze_u, ze_v.
  field_simplify_eq; [ring | exact (HJ u v)].
Qed.

(* ---------------------------------------------------------------- *)
(* Quasisymmetry                                                     *)

(** The square field depends on the angles only through chi, with a twice
    differentiable profile. *)
Variable b b' b'' : R -> R.
Hypothesis Hb : forall x, derivable_pt_lim b x (b' x).
Hypothesis Hb' : forall x, derivable_pt_lim b' x (b'' x).
Hypothesis Hqs : forall u v, B2 u v = b (chi u v).

Definition dB2u (u v : R) : R := b' (chi u v) * chi_u u v.
Definition dB2v (u v : R) : R := b' (chi u v) * chi_v u v.

Lemma B2_du : forall u v, derivable_pt_lim (fun x => B2 x v) u (dB2u u v).
Proof.
  intros u v.
  apply (derivable_pt_lim_ext (fun x => b (chi x v))).
  - intros y. symmetry. apply Hqs.
  - unfold dB2u. apply (derivable_pt_lim_comp (fun x => chi x v) b).
    apply chi_du. apply Hb.
Qed.

Lemma B2_dv : forall u v, derivable_pt_lim (fun y => B2 u y) v (dB2v u v).
Proof.
  intros u v.
  apply (derivable_pt_lim_ext (fun y => b (chi u y))).
  - intros y. symmetry. apply Hqs.
  - unfold dB2v. apply (derivable_pt_lim_comp (fun y => chi u y) b).
    apply chi_dv. apply Hb.
Qed.

(* ---------------------------------------------------------------- *)
(* The two-term ratio is a flux function                             *)

(** The quantities of Physics.qs2_b at a point: the Jacobian-weighted
    covariant components, A_i = J^3 d_i B^2, C = U A_u + V A_v, and the two
    terms t1 = L_v A_u - L_u A_v and J C whose ratio the criterion asks to
    be constant. *)
Definition A_u (u v : R) : R := J u v ^ 3 * dB2u u v.
Definition A_v (u v : R) : R := J u v ^ 3 * dB2v u v.
Definition L_u (u v : R) : R := J u v * Bu u v.
Definition L_v (u v : R) : R := J u v * Bv u v.
Definition Cq (u v : R) : R := U u v * A_u u v + V u v * A_v u v.
Definition t1 (u v : R) : R := L_v u v * A_u u v - L_u u v * A_v u v.

(** The flux function the ratio equals. *)
Definition Fstar : R := (I * N + G * M) / (phip * (M * iota - N)).

Theorem two_term_flux_function :
  forall u v, t1 u v * (phip * (M * iota - N)) = (I * N + G * M) * (J u v * Cq u v).
Proof.
  intros u v.
  replace (t1 u v)
    with (J u v ^ 4 * b' (chi u v) * (Bv u v * chi_u u v - Bu u v * chi_v u v))
    by (unfold t1, L_u, L_v, A_u, A_v, dB2u, dB2v; ring).
  replace (J u v * Cq u v)
    with (J u v ^ 4 * b' (chi u v) * (U u v * chi_u u v + V u v * chi_v u v))
    by (unfold Cq, A_u, A_v, dB2u, dB2v; ring).
  rewrite cov_kernel, flux_weighted. ring.
Qed.

Corollary two_term_ratio :
  forall u v, phip * (M * iota - N) <> 0 -> J u v * Cq u v <> 0 ->
  t1 u v / (J u v * Cq u v) = Fstar.
Proof.
  intros u v Hres Hc. unfold Fstar.
  assert (H := two_term_flux_function u v).
  destruct (Rmult_neq_0_reg _ _ Hres) as [Hp0 Hmi0].
  destruct (Rmult_neq_0_reg _ _ Hc) as [HJ0 HC0].
  field_simplify_eq; [nra | repeat split; assumption].
Qed.

(** What a two-term certificate carries is the defect Q = t1 - F0 J C beside
    t2 = F0 J C, so on a quasisymmetric surface Q is one constant times t2 at
    every point, which is the premise of Project.two_term_refuted. *)
Corollary two_term_defect_proportional :
  forall F0, F0 <> 0 -> phip * (M * iota - N) <> 0 ->
  forall u v, t1 u v - F0 * (J u v * Cq u v)
              = (Fstar / F0 - 1) * (F0 * (J u v * Cq u v)).
Proof.
  intros F0 HF0 Hres u v. unfold Fstar.
  assert (H := two_term_flux_function u v).
  destruct (Rmult_neq_0_reg _ _ Hres) as [Hp0 Hmi0].
  field_simplify_eq; [nra | repeat split; assumption].
Qed.

(* ---------------------------------------------------------------- *)
(* The triple product vanishes                                       *)

(** B . grad(B^2), which with B^s = 0 is B^u d_u B^2 + B^v d_v B^2. *)
Definition W2 (u v : R) : R := (U u v * dB2u u v + V u v * dB2v u v) / J u v.

(** On a quasisymmetric surface it is itself a function of chi. *)
Definition phi (x : R) : R := (M * iota - N) / (G + iota * I) * (b' x * b x).
Definition phi' (x : R) : R :=
  (M * iota - N) / (G + iota * I) * (b'' x * b x + b' x * b' x).

Lemma phi_d : forall x, derivable_pt_lim phi x (phi' x).
Proof.
  intros x. unfold phi, phi'.
  apply (derivable_pt_lim_ext (mult_real_fct ((M * iota - N) / (G + iota * I))
                                             (mult_fct b' b))).
  - intros y. unfold mult_real_fct, mult_fct. reflexivity.
  - apply derivable_pt_lim_scal. apply derivable_pt_lim_mult. apply Hb'. apply Hb.
Qed.

Lemma W2_chi : forall u v, W2 u v = phi (chi u v).
Proof.
  intros u v. unfold W2, phi.
  replace (U u v * dB2u u v + V u v * dB2v u v)
    with (b' (chi u v) * (U u v * chi_u u v + V u v * chi_v u v))
    by (unfold dB2u, dB2v; ring).
  rewrite flux_weighted.
  assert (HD := B2_D u v). rewrite Hqs in HD.
  assert (HJ' := HJ u v).
  assert (HD' : D u v = b (chi u v) * J u v / (phip * (G + iota * I))).
  { field_simplify_eq; [nra | repeat split; assumption]. }
  rewrite HD'. field. repeat split; assumption.
Qed.

Definition dW2u (u v : R) : R := phi' (chi u v) * chi_u u v.
Definition dW2v (u v : R) : R := phi' (chi u v) * chi_v u v.

Lemma W2_du : forall u v, derivable_pt_lim (fun x => W2 x v) u (dW2u u v).
Proof.
  intros u v.
  apply (derivable_pt_lim_ext (fun x => phi (chi x v))).
  - intros y. symmetry. apply W2_chi.
  - unfold dW2u. apply (derivable_pt_lim_comp (fun x => chi x v) phi).
    apply chi_du. apply phi_d.
Qed.

Lemma W2_dv : forall u v, derivable_pt_lim (fun y => W2 u y) v (dW2v u v).
Proof.
  intros u v.
  apply (derivable_pt_lim_ext (fun y => phi (chi u y))).
  - intros y. symmetry. apply W2_chi.
  - unfold dW2v. apply (derivable_pt_lim_comp (fun y => chi u y) phi).
    apply chi_dv. apply phi_d.
Qed.

(** Whatever the partial derivatives of B^2 and of B . grad(B^2) are at a
    point, their Jacobian over the angles vanishes: both are functions of chi
    alone, so their gradients are parallel. *)
Theorem triple_product_vanishes :
  forall u v d1 d2 w1 w2,
  derivable_pt_lim (fun x => B2 x v) u d1 ->
  derivable_pt_lim (fun y => B2 u y) v d2 ->
  derivable_pt_lim (fun x => W2 x v) u w1 ->
  derivable_pt_lim (fun y => W2 u y) v w2 ->
  d1 * w2 - d2 * w1 = 0.
Proof.
  intros u v d1 d2 w1 w2 H1 H2 H3 H4.
  rewrite (uniqueness_limite _ _ _ _ H1 (B2_du u v)).
  rewrite (uniqueness_limite _ _ _ _ H2 (B2_dv u v)).
  rewrite (uniqueness_limite _ _ _ _ H3 (W2_du u v)).
  rewrite (uniqueness_limite _ _ _ _ H4 (W2_dv u v)).
  unfold dB2u, dB2v, dW2u, dW2v. ring.
Qed.

(** Read on the combinator Physics.qs_b assembles the residual with: with
    A_i = J^3 d_i B^2 and D_i = J^5 d_i W2 the four ingredients, and any
    nonzero denominator, the triple product is exactly zero. *)
Corollary qs_triple_vanishes :
  forall (env : env ExtendedR) eAu eAv eDu eDv eden u v d1 d2 w1 w2 den,
  derivable_pt_lim (fun x => B2 x v) u d1 ->
  derivable_pt_lim (fun y => B2 u y) v d2 ->
  derivable_pt_lim (fun x => W2 x v) u w1 ->
  derivable_pt_lim (fun y => W2 u y) v w2 ->
  xeval env eAu = Xreal (J u v ^ 3 * d1) -> xeval env eAv = Xreal (J u v ^ 3 * d2) ->
  xeval env eDu = Xreal (J u v ^ 5 * w1) -> xeval env eDv = Xreal (J u v ^ 5 * w2) ->
  xeval env eden = Xreal den -> den <> 0 ->
  xeval env (qs_triple_e eAu eAv eDu eDv eden) = Xreal 0.
Proof.
  intros env eAu eAv eDu eDv eden u v d1 d2 w1 w2 den H1 H2 H3 H4 EAu EAv EDu EDv Eden Hd.
  assert (Hdet := triple_product_vanishes u v d1 d2 w1 w2 H1 H2 H3 H4).
  unfold qs_triple_e. cbn [xeval].
  rewrite EAu, EAv, EDu, EDv, Eden.
  cbn [Xmul]. unfold Xdiv, Xdiv'.
  generalize (is_zero_spec den). case (is_zero den).
  - intros Hz. inversion Hz. contradiction.
  - intros _. cbn [Xsub]. f_equal. unfold Rdiv.
    replace (J u v ^ 3 * d1 * (J u v ^ 5 * w2) * / den
             - J u v ^ 3 * d2 * (J u v ^ 5 * w1) * / den)
      with (J u v ^ 8 * (d1 * w2 - d2 * w1) * / den) by ring.
    rewrite Hdet. ring.
Qed.

End Surface.
