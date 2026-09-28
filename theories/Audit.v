(** Print the axioms the main theorems depend on. *)
From Stellarocq Require Import Checker Deriv Cell Cover Identities Quad Mercier
     Hypotheses Kantorovich Project Newton Colloc Symmetry Energy.
Print Assumptions check_cert_correct.
Print Assumptions harm_encloses.
Print Assumptions newton_correct.
Print Assumptions colloc_correct.
Print Assumptions harmonic_ratios_refute.
Print Assumptions two_term_refuted.
Print Assumptions residual_along_field.
Print Assumptions two_term_flux_function.
Print Assumptions triple_product_vanishes.
Print Assumptions qs_triple_vanishes.
Print Assumptions energy_gradient_is_force.
Print Assumptions check_cert_lower_correct.
Print Assumptions check_ccert_correct.
Print Assumptions check_ccert_lower_correct.
Print Assumptions divergence_free.
Print Assumptions pressure_is_a_flux_function.
Print Assumptions toroidal_terms_vanish.
Print Assumptions toroidal_lambda_terms_vanish.
Print Assumptions lambda_gauge.
Print Assumptions midpoint_encloses.
Print Assumptions assemble_value_zero.
Print Assumptions midpoint_sharp.
Print Assumptions tiling_encloses.
Print Assumptions tiling_var_encloses.
Print Assumptions cell_iterated_encloses.
Print Assumptions tiling2_encloses.
Print Assumptions lipschitz_ex_RInt.
Print Assumptions cauchy_schwarz_weighted.
Print Assumptions mercier_geodesic_nonpositive.
Print Assumptions inv2_bindings.
Print Assumptions covers_correct.
Print Assumptions tiling_covers.
Print Assumptions covers_app.
Print Assumptions check_ccert_over_range.
Print Assumptions taylor_sharp.
Print Assumptions diff_under_integral.
Print Assumptions check_ccert3_correct.
Print Assumptions taylor_step.
Print Assumptions taylor_leg.
Print Assumptions check_ccert_t_correct.
Print Assumptions check_ccert_t_lower_correct.
Print Assumptions isum_correct.
Print Assumptions mercier_encloses.
Print Assumptions dgeod_nonpositive.
Print Assumptions mercier_unstable_correct.
Print Assumptions mercier_stable_correct.
Print Assumptions ansatz_is_nested.
Print Assumptions descent_direction.
Print Assumptions contraction_fixed_point.
Print Assumptions newton_fixed_is_zero.
Print Assumptions kantorovich_is_gauge_fixed.
Print Assumptions gauge_is_fixed_on_the_ball.
Print Assumptions newton_contracts.
Print Assumptions gauge_quotient_equilibrium.
Print Assumptions toroidal_terms3_vanish.
Print Assumptions toroidal_lambda_terms3_vanish.
Print Assumptions qs_triple_zero.

From Stdlib Require Import ZArith Lia.
From Stellarocq Require Import FieldKAM KDioph KFix KFinal.
Print Assumptions field_kam.
Print Assumptions om_dioph_per.
Print Assumptions om_dioph.
Module AuditP192 <: Prec. Definition k : Z := 192%Z. Lemma k_nonneg : (0 <= k)%Z. Proof. unfold k. lia. Qed. End AuditP192.
Module AuditFX192 := FX AuditP192.
Module AuditKAM := Final AuditFX192.
Print Assumptions AuditKAM.cert_ok_torus.

From Stellarocq Require Import TorusLine FieldPath FieldVel KLohner.
Print Assumptions fourier_torus_line.
Print Assumptions taylor2.
Print Assumptions vel_path_R.
Print Assumptions lstep_ok.
Print Assumptions lescape_no_torus.

From Stellarocq Require Import KBracket.
Module AuditBracket := Bracket AuditFX192.
Print Assumptions AuditBracket.lcfs_bracket.

From Stellarocq Require Import Force Continuum.
Print Assumptions force_law.
Print Assumptions continuum_force.

From Stellarocq Require Import Residuals.
Print Assumptions continuum_force_asym.
Print Assumptions node_residual.
Print Assumptions node_residual_asym.
