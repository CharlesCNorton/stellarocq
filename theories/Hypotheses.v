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

    The encoded physics is read by people. [Print Assumptions] audits the
    theorems, and Physics.v is definitional: that its expression trees are the
    ideal-MHD residual is a claim about the encoding, checked by review and by
    the float reference of proto/continuum_ref.py, not by the kernel.

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
    the gradient of W, and it is the premise. The half which is calculus is
    proven below: where the gradient is negative the energy decreases, so a
    stationary point is not reached by staying put.

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
    reconstruction and a covering bounds it. That the vanishing of the
    triple product is equivalent to quasisymmetry is a theorem of the
    literature cited and is not proven here; what is proven is that the
    residual is that triple product and that it vanishes exactly for an
    axisymmetric reconstruction, [Identities.qs_triple_zero] with
    [Identities.toroidal_terms3_vanish].

    Contradicted by: a certified triple product bounded away from zero on a
    surface, which is a departure from quasisymmetry of every helicity at
    once, since the condition names none. *)
Definition quasisymmetric_at (T : expr) (e : env ExtendedR) : Prop :=
  xeval e T = Xreal 0.
