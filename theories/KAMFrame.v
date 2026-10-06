(** The algebra of the Newton step at one point of the torus.

    At a point of an approximately invariant torus K of the field-line flow
    with error E = L K - V(K), the tangent a = d_t K and the normal
    N = J a g + b a, with g = 1 / (sigma |a|^2) for the invariant density
    sigma of the flow and any b, make a frame with a ^ N = 1 / sigma. The
    multiple b of the tangent leaves the frame's area alone and changes the
    torsion by L b, so a b solving L b = -(T - <T>) makes the torsion
    constant. Write eta = (sigma E ^ N, sigma a ^ E) for the coordinates of E
    in the frame, T = sigma (L N - DV N) ^ N for the torsion and dE = d_t E.
    If the correction xi solves L xi_1 + T xi_2 = -eta_1 and
    L xi_2 = -eta_2, then

      E + L (xi_1 a + xi_2 N) - DV (xi_1 a + xi_2 N)
        = (alpha xi_1) a + (beta xi_1 + c xi_2) N

    with alpha = sigma dE ^ N, beta = sigma a ^ dE and
    c = -(grad sigma . E) |a|^2 g - alpha ([frame_step]). Its inputs are the
    values at the point: L a = dE + DV a, which differentiating the error along
    the torus gives; L sigma = grad sigma . E - sigma tr DV, the Liouville
    identity of the flow along the torus; and L (sigma |a|^2 g) = 0, since
    sigma |a|^2 g is constant. Every term of the right side is a product of
    the error or its derivative with bounded quantities, so the error after
    the step is quadratic in the error before it. *)

From Coq Require Import Reals Lra.
Local Open Scope R_scope.

Theorem frame_step
    (a1 a2 g b s s1 s2 E1 E2 dE1 dE2 D11 D12 D21 D22 La1 La2 Lg Lb Ls xi1 xi2 Lxi1 Lxi2 : R)
    (N1 N2 LN1 LN2 eta1 eta2 T alpha beta c : R) :
  s * (a1 * a1 + a2 * a2) * g = 1 ->
  La1 = dE1 + (D11 * a1 + D12 * a2) ->
  La2 = dE2 + (D21 * a1 + D22 * a2) ->
  Ls = s1 * E1 + s2 * E2 - s * (D11 + D22) ->
  Ls * (a1 * a1 + a2 * a2) * g + s * (2 * (a1 * La1 + a2 * La2)) * g
    + s * (a1 * a1 + a2 * a2) * Lg = 0 ->
  N1 = - (a2 * g) + b * a1 -> N2 = a1 * g + b * a2 ->
  LN1 = - (La2 * g + a2 * Lg) + (Lb * a1 + b * La1) ->
  LN2 = La1 * g + a1 * Lg + (Lb * a2 + b * La2) ->
  eta1 = s * (E1 * N2 - E2 * N1) -> eta2 = s * (a1 * E2 - a2 * E1) ->
  T = s * ((LN1 - (D11 * N1 + D12 * N2)) * N2 - (LN2 - (D21 * N1 + D22 * N2)) * N1) ->
  Lxi1 = - (eta1 + T * xi2) -> Lxi2 = - eta2 ->
  alpha = s * (dE1 * N2 - dE2 * N1) -> beta = s * (a1 * dE2 - a2 * dE1) ->
  c = - ((s1 * E1 + s2 * E2) * (a1 * a1 + a2 * a2) * g) - alpha ->
  E1 + ((La1 * xi1 + a1 * Lxi1 + LN1 * xi2 + N1 * Lxi2)
        - (D11 * (a1 * xi1 + N1 * xi2) + D12 * (a2 * xi1 + N2 * xi2)))
    = a1 * (alpha * xi1) + N1 * (beta * xi1 + c * xi2) /\
  E2 + ((La2 * xi1 + a2 * Lxi1 + LN2 * xi2 + N2 * Lxi2)
        - (D21 * (a1 * xi1 + N1 * xi2) + D22 * (a2 * xi1 + N2 * xi2)))
    = a2 * (alpha * xi1) + N2 * (beta * xi1 + c * xi2).
Proof.
  intros Hg HLa1 HLa2 HLs HLg HN1 HN2 HLN1 HLN2 He1 He2 HT HLx1 HLx2 Hal Hbe Hc.
  set (A := a1 * a1 + a2 * a2) in *.
  assert (Hs : s <> 0) by (intros E; rewrite E in Hg; lra).
  assert (HA : A <> 0) by (intros E; rewrite E in Hg; lra).
  (* L g from the constancy of sigma |a|^2 g *)
  assert (HLg' : Lg = - (Ls * A * g + s * (2 * (a1 * La1 + a2 * La2)) * g) / (s * A)).
  { apply (Rmult_eq_reg_l (s * A)); [| apply Rmult_integral_contrapositive_currified; assumption].
    field_simplify; [| split; assumption]. lra. }
  assert (Hg' : g = / (s * A)).
  { apply (Rmult_eq_reg_l (s * A)); [| apply Rmult_integral_contrapositive_currified; assumption].
    rewrite Rinv_r by (apply Rmult_integral_contrapositive_currified; assumption). lra. }
  subst Lxi1 Lxi2 alpha beta c T eta1 eta2 LN1 LN2 N1 N2.
  rewrite HLg'. rewrite HLs. rewrite HLa1, HLa2. rewrite Hg'.
  unfold A. split; field; split; (assumption || (unfold A in HA; exact HA)).
Qed.
