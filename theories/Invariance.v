(** The invariance equation of the field-line flow, and invariant tori.

    With the toroidal angle phi as time, a field line of B in cylindrical
    coordinates (R, phi, Z) follows

      dR/dphi = R B_R / B_phi,   dZ/dphi = R B_Z / B_phi

    wherever B_phi is not zero. A torus R = KR(theta, phi), Z = KZ(theta, phi)
    at the geometric toroidal angle phi carries this flow as the rotation by
    omega in theta per radian of phi when

      d_phi K + omega d_theta K = (R B_R / B_phi, R B_Z / B_phi)  at K,

    the equation an a posteriori KAM theorem solves. [param_invariant_torus]
    proves that every solution is an invariant torus in the sense of
    Hypotheses.invariant_torus: the tangent d_phi T + omega d_theta T of the
    torus in space is a multiple of B, so B is tangent to the torus. *)

From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Hypotheses.

Local Open Scope R_scope.

Lemma is_derive_mul (f g : R -> R) (x df dg : R) :
  is_derive f x df -> is_derive g x dg ->
  is_derive (fun t => f t * g t) x (df * g x + f x * dg).
Proof.
  intros Hf Hg. apply (is_derive_mult f g x df dg Hf Hg). intros; apply Rmult_comm.
Qed.

Lemma is_derive_mul_const (f : R -> R) (x df k : R) :
  is_derive f x df -> is_derive (fun t => f t * k) x (df * k).
Proof.
  intros Hf.
  apply is_derive_ext with (f := fun t => k * f t).
  - intros t. apply Rmult_comm.
  - replace (df * k) with (k * df) by apply Rmult_comm. apply is_derive_scal, Hf.
Qed.

Section FieldLine.

Variable B : vec3 -> vec3.

(** The point at (R, phi, Z) in cylindrical coordinates, and the cylindrical
    components of the field there. *)
Definition cyl (R0 phi Z0 : R) : vec3 := (R0 * cos phi, R0 * sin phi, Z0).

Definition B_R (R0 phi Z0 : R) : R :=
  coord1 (B (cyl R0 phi Z0)) * cos phi + coord2 (B (cyl R0 phi Z0)) * sin phi.
Definition B_phi (R0 phi Z0 : R) : R :=
  - coord1 (B (cyl R0 phi Z0)) * sin phi + coord2 (B (cyl R0 phi Z0)) * cos phi.
Definition B_Z (R0 phi Z0 : R) : R := coord3 (B (cyl R0 phi Z0)).

(** The torus in space from its R and Z at the toroidal angle phi. *)
Definition torus_of (KR KZ : R -> R -> R) (theta phi : R) : vec3 :=
  cyl (KR theta phi) phi (KZ theta phi).

(** The invariance equation at every point, with B_phi not zero there. *)
Definition param_invariant (KR KZ : R -> R -> R) (omega : R) : Prop :=
  forall theta phi, exists Rt Rp Zt Zp : R,
    is_derive (fun t => KR t phi) theta Rt /\
    is_derive (fun p => KR theta p) phi Rp /\
    is_derive (fun t => KZ t phi) theta Zt /\
    is_derive (fun p => KZ theta p) phi Zp /\
    B_phi (KR theta phi) phi (KZ theta phi) <> 0 /\
    Rp + omega * Rt =
      KR theta phi * B_R (KR theta phi) phi (KZ theta phi)
        / B_phi (KR theta phi) phi (KZ theta phi) /\
    Zp + omega * Zt =
      KR theta phi * B_Z (KR theta phi) phi (KZ theta phi)
        / B_phi (KR theta phi) phi (KZ theta phi).

Theorem param_invariant_torus (KR KZ : R -> R -> R) (omega : R) :
  param_invariant KR KZ omega -> invariant_torus B (torus_of KR KZ).
Proof.
  intros H u v.
  destruct (H u v) as (Rt & Rp & Zt & Zp & HRt & HRp & HZt & HZp & Hb & HR & HZ).
  assert (Hc : is_derive cos v (- sin v)) by (auto_derive; [exact I | ring]).
  assert (Hs : is_derive sin v (cos v)) by (auto_derive; [exact I | ring]).
  exists (Rt * cos v, Rt * sin v, Zt).
  exists (Rp * cos v + KR u v * - sin v, Rp * sin v + KR u v * cos v, Zp).
  split.
  - unfold partials, torus_of, cyl; cbn [coord1 coord2 coord3].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + apply (is_derive_mul_const (fun t => KR t v)). exact HRt.
    + apply (is_derive_mul_const (fun t => KR t v)). exact HRt.
    + exact HZt.
    + apply (is_derive_mul (fun p => KR u p) cos). exact HRp. exact Hc.
    + apply (is_derive_mul (fun p => KR u p) sin). exact HRp. exact Hs.
    + exact HZp.
  - unfold torus_of.
    unfold B_R, B_phi, B_Z in Hb, HR, HZ.
    set (r := KR u v) in *. set (z := KZ u v) in *.
    destruct (B (cyl r v z)) as [[b1 b2] b3] eqn:EB.
    cbn [coord1 coord2 coord3] in Hb, HR, HZ.
    set (c := cos v) in *. set (s := sin v) in *.
    assert (Hcs : s * s + c * c = 1).
    { unfold s, c. rewrite <- (sin2_cos2 v). unfold Rsqr. ring. }
    set (bR := b1 * c + b2 * s) in *.
    set (bp := - b1 * s + b2 * c) in *.
    assert (Hb1 : b1 = bR * c - bp * s).
    { unfold bR, bp.
      replace ((b1 * c + b2 * s) * c - (- b1 * s + b2 * c) * s)
        with (b1 * (s * s + c * c)) by ring.
      rewrite Hcs. ring. }
    assert (Hb2 : b2 = bR * s + bp * c).
    { unfold bR, bp.
      replace ((b1 * c + b2 * s) * s + (- b1 * s + b2 * c) * c)
        with (b2 * (s * s + c * c)) by ring.
      rewrite Hcs. ring. }
    clearbody bR bp.
    set (Q := r / bp).
    assert (Hr : r = Q * bp) by (unfold Q; field; exact Hb).
    replace (r * bR / bp) with (Q * bR) in HR by (unfold Q; field; exact Hb).
    replace (r * b3 / bp) with (Q * b3) in HZ by (unfold Q; field; exact Hb).
    clearbody Q.
    assert (ERp : Rp = Q * bR - omega * Rt) by lra.
    assert (EZp : Zp = Q * b3 - omega * Zt) by lra.
    rewrite ERp, EZp, Hr, Hb1, Hb2.
    unfold dot3, cross3r. ring.
Qed.

End FieldLine.
