(** The physical assumptions behind a certificate.

    The model is ideal magnetohydrodynamics in static equilibrium,
    J x B = grad p, with a scalar pressure, infinite conductivity, no flow
    and no anisotropy.

    Each entry is a proposition about explicit objects, so that a theorem
    taking one as a hypothesis is saying something. An entry that reads
    [:= True] would be discharged by [I] and would carry no content, which is
    worse than an axiom: an axiom at least shows up in [Print Assumptions].
    None of these is declared as an Axiom either; the ones a theorem needs are
    carried as explicit hypotheses of that theorem, so the audit reports the
    standard library and nothing else.

    Two of them turn out to be theorems about the reconstruction rather than
    assumptions about the plasma, and are proven here. What stays assumed is
    that the plasma is described by a field of the assumed form, which is a
    statement no proof about the reconstruction can reach.

    Limits that no amount of work here removes are at the end of this comment
    rather than in a definition, since they are a description of the
    development and not propositions it uses.

    A small residual is not by itself a nearby equilibrium. The certificates
    bound the residual of a reconstruction; concluding that a true solution
    sits close by needs a bound on the inverse of the linearized force
    operator. [Kantorovich.v] carries that argument in the abstract, so what
    is missing is exactly the inverse bound and nothing else. It is not merely
    unproven: the poloidal relabelling is a gauge symmetry, so the
    linearization is singular by construction, and [lambda_gauge] of
    Identities.v exhibits one exact kernel direction. Such an argument has to
    be made on the gauge-fixed quotient. In three dimensions the continuum
    statement is worse than unproven, since the inverse is genuinely unbounded
    at rational surfaces, which is what makes islands.

    The encoded physics is proven, not read. Physics.v is definitional, and
    [Continuum.continuum_force_coords] and
    [Residuals.continuum_force_asym_coords] prove that its expression trees at
    a free radius are the covariant components of mu0 (J x B - grad p) of the
    reconstructed field, with the curl written in the coordinates, and
    [Continuum.continuum_force] and [Residuals.continuum_force_asym] the same
    through any Cartesian field that agrees with it along the coordinate
    lines; [Residuals.node_residual] and [Residuals.node_residual_asym] prove
    that at a node they are VMEC's rule on the half-point fields. What stays
    with people is the reading of those statements.

    The obstruction is about the reconstructed form. [check_ccert_lower]
    proves no field of the certified form balances in a cell. Varying a
    coefficient slot rather than an angle widens that to every field whose
    coefficients lie in a box, which is as far as it goes: it does not exclude
    a true equilibrium there, only one this reconstruction can write.

    The radial interpolant is a choice. VMEC defines a value and a radial
    derivative at each half point; between them the cubic Hermite is ours, and
    a different interpolant would give a different continuum residual. What is
    not a choice is the agreement at the half points, where the rule is
    VMEC's own.

    Extraction and the runtime are trusted. The kernel checks the proofs; the
    extraction mechanism, the OCaml compiler, the primitive integer and float
    shims and the C stubs they bind to are not checked by anything here. *)

From Coq Require Import ZArith Reals List Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Deriv.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Assumptions that the reconstruction discharges                    *)

(** Nested flux surfaces. A field whose radial contravariant component
    vanishes identically leaves every surface s = const invariant, so a field
    line never leaves the one it starts on.

    In three dimensions a smooth equilibrium with continuous rotational
    transform generically develops islands at rational surfaces, where no such
    surface exists; Bruno and Laurence proved existence for stepped pressure
    in 1996 and the smooth case is open. A certificate states the residual of
    a nested-surface field, not that the true equilibrium is one.

    Contradicted by: an island chain or a stochastic region at the rational
    surfaces the equilibrium crosses. *)
Definition nested_flux_surfaces (Bs : expr) : Prop :=
  forall env, xeval env Bs = Xreal 0.

(** VMEC's ansatz sets that component to the zero expression, so for the
    reconstruction this is a theorem. What stays assumed is that the plasma is
    described by a field of this form. *)
Theorem ansatz_is_nested : nested_flux_surfaces e0.
Proof. intros env. reflexivity. Qed.

(** Static equilibrium with a scalar pressure. There is no velocity field, so
    the momentum equation carries no inertial term, and the pressure enters
    only through [pprime], which reads neither angle.

    Contradicted by: sonic or near-sonic flow, pressure anisotropy, or a
    pressure varying on a flux surface. *)
Definition scalar_pressure (pp : expr) : Prop :=
  var_free 1 pp = true /\ var_free 2 pp = true.

(** [pressure_is_a_flux_function] of Identities.v proves this of every
    parameterization the checker admits. It is stated here so that the model
    assumption and the theorem discharging it are the same proposition. *)

(* ---------------------------------------------------------------- *)
(* Assumptions that stay premises                                    *)

(** Consistency of the discretization. The discrete force operator
    approximates the continuum ideal-MHD force at second order on smooth data,
    so the worst certified residual of a reconstruction falls as the square of
    the grid spacing. Measured by manufactured solutions in
    proximafusion/vmecpp#784, which reports order 2.00 in the energy, the R
    and Z force and the lambda force. Needed by any statement about the
    continuum problem rather than about the grid.

    Contradicted by: a family of equilibria whose certified residual does not
    fall at that order. That is a measurement this development can make of
    itself, since the certified residual of a reconstruction is exactly
    [bound h]. *)
Definition second_order (bound : R -> R) : Prop :=
  exists C h0, 0 < C /\ 0 < h0 /\
    forall h, 0 < h < h0 -> bound h <= C * h * h.

Definition discretization_is_consistent (bound : R -> R) : Prop :=
  second_order bound.

(** The energy principle. Force balance is stationarity of

      W = integral of (B^2 / 2 mu0 + p / (gamma - 1)) sqrt(g),

    and a displacement with negative second variation at fixed boundary is
    unstable (Bernstein, Frieman, Kruskal and Kulsrud, 1958).

    The half of that which is physics is the identification of the force with
    the gradient of W. [Energy.energy_gradient_is_force] proves it pointwise
    for the reconstruction with gamma = 0: the Euler-Lagrange expressions of
    (B^2 / 2 - mu0 p) sqrt(g) in R and in Z, with the flux through the
    coordinate surfaces held, are -2 sqrt(g) times the cylindrical components
    of J x B - mu0 grad p as Physics.v writes them. What stays a premise is
    that W is the energy of the plasma, whose equilibria are its stationary
    points. The half which is calculus is proven below: where the gradient is
    negative the energy decreases, so a stationary point is not reached by
    staying put.

    Contradicted by: an equilibrium observed unstable whose second variation
    is positive. *)
Definition force_is_energy_gradient (W r : R -> R) : Prop :=
  forall t, is_derive W t (r t).

(** Where the derivative is negative there is a nearby point of lower energy.
    This is the step that turns a sign into a direction of instability. *)
Theorem descent_direction :
  forall (W : R -> R) (t0 d : R),
  is_derive W t0 d -> d < 0 ->
  exists t, t0 < t /\ W t < W t0.
Proof.
  intros W t0 d Hd Hneg.
  assert (Hd' := proj1 (is_derive_Reals W t0 d) Hd).
  destruct (Hd' (- d / 2) ltac:(lra)) as [delta Hdelta].
  assert (Hd0 : 0 < pos delta) by apply cond_pos.
  set (h := pos delta / 2).
  assert (Hh0 : 0 < h) by (unfold h; lra).
  assert (Hhd : Rabs h < delta).
  { unfold h. rewrite Rabs_right by lra. lra. }
  assert (Hne : h <> 0) by (intro HH; rewrite HH in Hh0; lra).
  specialize (Hdelta h Hne Hhd).
  (* the quotient is within -d/2 of d, so it is at most d/2, which is
     negative *)
  assert (Hq : (W (t0 + h) - W t0) / h < 0).
  { apply Rabs_def2 in Hdelta. destruct Hdelta as [Hlt _]. lra. }
  exists (t0 + h). split. lra.
  assert (Hinc : W (t0 + h) - W t0 < 0).
  { apply (Rmult_lt_reg_r (/ h)); [apply Rinv_0_lt_compat; lra|].
    rewrite Rmult_0_l. exact Hq. }
  lra.
Qed.

(** Resonance and island width. At a surface where iota = n/m, a resonant
    normal-field harmonic of size delta corresponds to a magnetic island of
    width 4 sqrt(delta / (m |iota'|)) in s. Needed to read a residual bounded
    away from zero at a rational surface as an island.

    Contradicted by: field-line tracing of the true field showing no island
    where the formula predicts one, or a width disagreeing with it. *)
Definition island_width (delta m iotap : R) : R :=
  4 * sqrt (delta / (m * Rabs iotap)).

Definition resonance_and_island_width (w delta m iotap : R) : Prop :=
  w = island_width delta m iotap.

(** The free boundary. Across the plasma-vacuum interface the total pressure
    is continuous: the plasma's p + B^2/2 matches the vacuum field's B^2/2, in
    the mu0-scaled units the reconstruction carries, and the vacuum field
    itself has to be produced by the coils.

    Every equilibrium certified here was solved with the boundary fixed, so
    nothing in the development constrains the field outside it and no
    certificate establishes this. The condition is written down so that what
    is missing is a quantity to bound rather than a statement to make: a
    covering of the boundary surface with [jump] as its component would
    certify it, given a vacuum field to read.

    Contradicted by: a boundary at which the total pressure jumps, or a vacuum
    field no coil set produces. *)
Definition jump (p B2 Bvac2 : expr) : expr :=
  Esub (Eadd p (Ediv B2 e2)) (Ediv Bvac2 e2).

Definition free_boundary_balanced (p B2 Bvac2 : expr) : Prop :=
  forall env, xeval env (jump p B2 Bvac2) = Xreal 0.

(** Quasisymmetry. The field strength depends on the angles only through one
    combination M theta_B - N zeta_B of the Boozer angles, for some helicity
    (M, N), which is the property that lets a stellarator confine as a
    tokamak does. Its coordinate-free form is that the triple product

      grad psi . (grad B x grad(B . grad B))

    vanishes, a scalar of the field at a point that needs neither the Boozer
    transform nor a choice of helicity (Helander 2014; Rodriguez, Paul and
    Bhattacharjee 2020). [Physics.qs_triple_e] builds it from the
    reconstruction and a covering bounds it. [Symmetry.triple_product_vanishes]
    proves that a quasisymmetric field makes it zero, and
    [Symmetry.two_term_flux_function] the same for the two-term ratio, which
    is the direction a verdict reads: a residual bounded away from zero
    refutes quasisymmetry. The converse, that a vanishing triple product
    forces quasisymmetry, is not needed by any verdict and is not proven.
    It also vanishes exactly for an axisymmetric reconstruction,
    [Identities.qs_triple_zero] with [Identities.toroidal_terms3_vanish].

    Contradicted by: a certified triple product bounded away from zero on a
    surface, which is a departure from quasisymmetry of every helicity at
    once, since the condition names none. *)
Definition quasisymmetric_at (T : expr) (e : env ExtendedR) : Prop :=
  xeval e T = Xreal 0.

(** Vectors of three reals, for fields and surfaces in Cartesian space. *)
Definition vec3 : Type := (R * R * R)%type.

Definition dot3 (a b : vec3) : R :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in a1 * b1 + a2 * b2 + a3 * b3.

Definition cross3r (a b : vec3) : vec3 :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in
  (a2 * b3 - a3 * b2, a3 * b1 - a1 * b3, a1 * b2 - a2 * b1).

Definition dist3 (a b : vec3) : R :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in
  sqrt ((a1 - b1) ^ 2 + (a2 - b2) ^ 2 + (a3 - b3) ^ 2).

(** The partial derivatives of a map of two angles into space, coordinate by
    coordinate. *)
Definition coord1 (a : vec3) : R := let '(x, _, _) := a in x.
Definition coord2 (a : vec3) : R := let '(_, y, _) := a in y.
Definition coord3 (a : vec3) : R := let '(_, _, z) := a in z.

Definition partials (T : R -> R -> vec3) (u v : R) (Tu Tv : vec3) : Prop :=
  is_derive (fun u' => coord1 (T u' v)) u (coord1 Tu) /\
  is_derive (fun u' => coord2 (T u' v)) u (coord2 Tu) /\
  is_derive (fun u' => coord3 (T u' v)) u (coord3 Tu) /\
  is_derive (fun v' => coord1 (T u v')) v (coord1 Tv) /\
  is_derive (fun v' => coord2 (T u v')) v (coord2 Tv) /\
  is_derive (fun v' => coord3 (T u v')) v (coord3 Tv).

(** Invariant tori. A torus T, a map of two angles, is invariant under the
    field-line flow of B when it has partial derivatives everywhere and B is
    tangent to it: B . (T_u x T_v) = 0 at every point, so a field line that
    starts on it stays on it. A family of them is a family of flux surfaces. *)
Definition invariant_torus (B : vec3 -> vec3) (T : R -> R -> vec3) : Prop :=
  forall u v, exists Tu Tv, partials T u v Tu Tv /\
    dot3 (B (T u v)) (cross3r Tu Tv) = 0.

(** From a nearly invariant torus to an invariant one (KAM). A certificate of
    Physics.RCoil bounds the sine of the angle between a coil field and a
    torus given by a finite Fourier series, at every point of it. No finite
    Fourier series is exactly invariant for a generic field, and a small
    bound is not invariance. What makes the step is an a posteriori KAM
    theorem for the field-line flow, a Hamiltonian system of one and a half
    degrees of freedom with the toroidal angle as time (de la Llave,
    Gonzalez, Jorba and Villanueva 2005; Figueras, Haro and Luque 2017): an
    approximately invariant torus whose rotational transform is Diophantine,
    whose twist is non-degenerate and whose invariance error lies below a
    threshold computed from those constants and from bounds on the torus and
    the field in a complex neighbourhood is within a computable distance of a
    true invariant torus with that transform. [kam_nearby] is that statement
    for one field, one torus, the sine a certificate bounds, the bound and
    the distance, as numbers; the constants that fix them are not certified
    here. That [sine] is the sine of the angle between B and T is a claim
    about the encoding, as it is for every expression Physics.v writes.

    Contradicted by: field-line tracing from the torus leaving the distance
    delta, or a Poincare section showing an island chain or a chaotic layer
    where the torus lies. *)
Definition kam_nearby (B : vec3 -> vec3) (T : R -> R -> vec3) (sine : R -> R -> R)
    (eps delta : R) : Prop :=
  (forall u v, 0 <= u <= 2 * PI -> 0 <= v <= 2 * PI -> Rabs (sine u v) <= eps) ->
  exists T', invariant_torus B T' /\ forall u v, dist3 (T' u v) (T u v) <= delta.

(** The same step from the values at the points of a grid. The torus and the
    coil field are analytic, so the angle between them is fixed, to within an
    amount that falls exponentially with the number of points, by its values
    at the points of a grid fine enough to resolve both. [kam_from_points]
    carries that interpolation along with the KAM step: a bound at every
    listed point, every point of the torus within h of a listed one in each
    angle, and the conclusion of [kam_nearby].

    Contradicted by: the angle between the field and the torus exceeding eps
    somewhere between the points by more than the interpolation allows, or
    anything that contradicts [kam_nearby]. *)
Definition kam_from_points (B : vec3 -> vec3) (T : R -> R -> vec3) (sine : R -> R -> R)
    (pts : list (R * R)) (h eps delta : R) : Prop :=
  (forall u v, 0 <= u <= 2 * PI -> 0 <= v <= 2 * PI ->
     exists p, In p pts /\ Rabs (u - fst p) <= h /\ Rabs (v - snd p) <= h) ->
  (forall p, In p pts -> Rabs (sine (fst p) (snd p)) <= eps) ->
  exists T', invariant_torus B T' /\ forall u v, dist3 (T' u v) (T u v) <= delta.
