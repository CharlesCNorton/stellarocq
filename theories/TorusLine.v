(** Invariant tori given by Fourier families, and the field lines on them.

    [fourier_torus B KR KZ om] says that R and Z of the torus are the values
    of two coefficient families with finite norms on a strip of positive
    width, read at the toroidal angle scaled by some s, and that they solve
    the invariance equation of Invariance.v with rotation om per radian of
    the toroidal angle. Such a torus is invariant in the sense of
    Hypotheses.v ([fourier_torus_invariant]), and more: through each of its
    points it carries the curve phi |-> (KR (theta0 + om (phi - phi0)) phi,
    KZ (theta0 + om (phi - phi0)) phi), which solves the field-line
    equations R' = R B_R / B_phi, Z' = R B_Z / B_phi with the toroidal angle
    as time at every angle ([fourier_torus_line]). The derivative along the
    line comes from FourierLine.feval_line; the invariance equation names it
    through the partial derivatives, which are those of the families. *)

From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierAlg FourierLine
  Hypotheses Invariance.
Local Open Scope R_scope.

Definition fourier_torus (B : vec3 -> vec3) (KR KZ : R -> R -> R) (om : R) : Prop :=
  exists (u v : fser) (rho MR MZ s : R),
    0 < rho /\ nbound rho MR u /\ nbound rho MZ v /\
    (forall t p, KR t p = feval u t (s * p)) /\ (forall t p, KZ t p = feval v t (s * p)) /\
    param_invariant B KR KZ om.

Theorem fourier_torus_invariant (B : vec3 -> vec3) (KR KZ : R -> R -> R) (om : R) :
  fourier_torus B KR KZ om -> invariant_torus B (torus_of KR KZ).
Proof.
  intros (u & v & rho & MR & MZ & s & _ & _ & _ & _ & _ & H). exact (param_invariant_torus B KR KZ om H).
Qed.

(** The field-line velocity of B with the toroidal angle as time. *)
Definition flR (B : vec3 -> vec3) (R0 phi Z0 : R) : R := R0 * B_R B R0 phi Z0 / B_phi B R0 phi Z0.
Definition flZ (B : vec3 -> vec3) (R0 phi Z0 : R) : R := R0 * B_Z B R0 phi Z0 / B_phi B R0 phi Z0.

(** The line through (theta0, phi0) at the angle phi. *)
Definition lineR (KR : R -> R -> R) (om theta0 phi0 phi : R) : R := KR (theta0 + om * (phi - phi0)) phi.
Definition lineZ (KZ : R -> R -> R) (om theta0 phi0 phi : R) : R := KZ (theta0 + om * (phi - phi0)) phi.

Lemma is_derive_scale (s x : R) : is_derive (fun y => s * y) x s.
Proof. auto_derive; [exact I | ring]. Qed.

Lemma line_derive (u : fser) (rho M s om theta0 phi0 phi : R) (Rt Rp : R) :
  0 < rho -> nbound rho M u ->
  is_derive (fun t => feval u t (s * phi)) (theta0 + om * (phi - phi0)) Rt ->
  is_derive (fun p => feval u (theta0 + om * (phi - phi0)) (s * p)) phi Rp ->
  is_derive (fun y => feval u (theta0 + om * (y - phi0)) (s * y)) phi (Rp + om * Rt).
Proof.
  intros Hr H HRt HRp.
  set (th := theta0 + om * (phi - phi0)) in *.
  assert (E1 : Rt = feval (dt u) th (s * phi)).
  { rewrite <- (is_derive_unique _ _ _ HRt). apply is_derive_unique.
    exact (feval_dt rho M u (s * phi) th Hr H). }
  assert (E2 : Rp = s * feval (dp u) th (s * phi)).
  { rewrite <- (is_derive_unique _ _ _ HRp). apply is_derive_unique.
    exact (is_derive_comp (fun y => feval u th y) (fun x => s * x) phi _ s
             (feval_dp rho M u th (s * phi) Hr H) (is_derive_scale s phi)). }
  pose proof (feval_line rho M u (theta0 - om * phi0) 0 om s phi Hr H) as L.
  replace (theta0 - om * phi0 + om * phi) with th in L by (unfold th; ring).
  replace (0 + s * phi) with (s * phi) in L by ring.
  apply (is_derive_ext (fun y => feval u (theta0 - om * phi0 + om * y) (0 + s * y))).
  - intros y. f_equal; ring.
  - rewrite E1, E2. replace (s * feval (dp u) th (s * phi) + om * feval (dt u) th (s * phi))
      with (om * feval (dt u) th (s * phi) + s * feval (dp u) th (s * phi)) by ring.
    exact L.
Qed.

Theorem fourier_torus_line (B : vec3 -> vec3) (KR KZ : R -> R -> R) (om theta0 phi0 : R) :
  fourier_torus B KR KZ om -> forall phi,
    B_phi B (lineR KR om theta0 phi0 phi) phi (lineZ KZ om theta0 phi0 phi) <> 0 /\
    is_derive (lineR KR om theta0 phi0) phi
      (flR B (lineR KR om theta0 phi0 phi) phi (lineZ KZ om theta0 phi0 phi)) /\
    is_derive (lineZ KZ om theta0 phi0) phi
      (flZ B (lineR KR om theta0 phi0 phi) phi (lineZ KZ om theta0 phi0 phi)).
Proof.
  intros (u & v & rho & MR & MZ & s & Hr & HU & HV & ER & EZ & HP) phi.
  set (th := theta0 + om * (phi - phi0)).
  destruct (HP th phi) as (Rt & Rp & Zt & Zp & HRt & HRp & HZt & HZp & Hb & HR & HZ).
  unfold lineR, lineZ, flR, flZ. fold th. split; [exact Hb |]. split.
  - rewrite <- HR.
    apply (is_derive_ext (fun y => feval u (theta0 + om * (y - phi0)) (s * y))); [intros y; rewrite ER; reflexivity |].
    apply (line_derive u rho MR); [exact Hr | exact HU | |].
    + fold th. apply (is_derive_ext (fun t => KR t phi)); [intros t; apply ER | exact HRt].
    + fold th. apply (is_derive_ext (fun p => KR th p)); [intros p; apply ER | exact HRp].
  - rewrite <- HZ.
    apply (is_derive_ext (fun y => feval v (theta0 + om * (y - phi0)) (s * y))); [intros y; rewrite EZ; reflexivity |].
    apply (line_derive v rho MZ); [exact Hr | exact HV | |].
    + fold th. apply (is_derive_ext (fun t => KZ t phi)); [intros t; apply EZ | exact HZt].
    + fold th. apply (is_derive_ext (fun p => KZ th p)); [intros p; apply EZ | exact HZp].
Qed.
