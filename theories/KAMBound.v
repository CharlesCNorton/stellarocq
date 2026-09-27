(** The size of the Newton step.

    With the tangent of the torus bounded by A, the frame inverse by G, the
    normal by N, the density sigma, its gradient and the derivative of the
    field by S, S1 and D, the torsion by Tm with its average at least tau in
    size, the error by eps and the second-order remainder of the field by M2
    times the square of the correction, every part of the step is bounded by
    a multiple of eps
    ([bnd_corr]: the correction is at most kP eps on a strip narrower by
    2 delta), and the error of the next torus by a multiple of eps^2
    ([step_bound]: at most kE eps^2). The multiples depend on the constants,
    on delta through the derivative's 1 / (e delta) and the inverse of L's
    (1 + 1 / (e delta)) / gamma, and not on eps. The step keeps the next
    torus canonical and stellarator-symmetric ([next_canon], [next_sym]),
    and its error, which [KAMStep.step_identity] identifies with the
    quadratic expression at every point, inherits that expression's bound
    because both are canonical families with the same function. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon KAMFrame KAMVec KAMFin KAMStep.
Local Open Scope R_scope.

(** The constants a state of the iteration is held to. *)
Record kcon := { cA : R ; cG : R ; cN : R ; cB : R ; cS : R ; cS1 : R ; cD : R ; cMV : R ; cM2 : R ;
                 cTm : R ; ctau : R ; cLS : R ; cLD : R }.

(** The step's parts, per unit of the error. *)
Definition kN (c : kcon) : R := cN c.
Definition kH1 (c : kcon) : R := cS c * (2 * kN c).
Definition kH2 (c : kcon) : R := cS c * (2 * cA c).
Definition kW2 (c : kcon) (gamma d : R) : R := linv_const gamma d * kH2 c.
Definition kZ (c : kcon) (gamma d : R) : R := (kH1 c + cTm c * kW2 c gamma d) / ctau c.
Definition kX2 (c : kcon) (gamma d : R) : R := kW2 c gamma d + kZ c gamma d.
Definition kR1 (c : kcon) (gamma d : R) : R := kH1 c + (cTm c * kW2 c gamma d + kZ c gamma d * cTm c).
Definition kX1 (c : kcon) (gamma d : R) : R := linv_const gamma d * kR1 c gamma d.
Definition kP (c : kcon) (gamma d : R) : R := kX1 c gamma d * cA c + kX2 c gamma d * kN c.
Definition kdE (d : R) : R := / (exp 1 * d).
Definition kAl (c : kcon) (d : R) : R := cS c * (2 * (kdE d * kN c)).
Definition kBe (c : kcon) (d : R) : R := cS c * (2 * (cA c * kdE d)).
Definition kC (c : kcon) (d : R) : R := 2 * cS1 c * (2 * (cA c * cA c)) * cG c + kAl c d.
Definition kE (c : kcon) (gamma d : R) : R :=
  kAl c d * kX1 c gamma d * cA c + (kBe c d * kX1 c gamma d + kC c d * kX2 c gamma d) * kN c
  + cM2 c * (kP c gamma d * kP c gamma d).

Lemma Rabs_m1 : Rabs (-1) = 1.
Proof. rewrite Rabs_left by lra. ring. Qed.

Lemma vbound_feq (rho M : R) (u v : vf) :
  feq (vR u) (vR v) -> feq (vZ u) (vZ v) -> vbound rho M u -> vbound rho M v.
Proof. intros H1 H2 [B1 B2]. split; [apply (nbound_feq _ _ _ _ H1 B1) | apply (nbound_feq _ _ _ _ H2 B2)]. Qed.

Lemma next_sub_feq (F : fmodel) (om : R) (K : vf) (g b : fser) :
  feq (vR (vsub (knext F om K g b) K)) (vR (kcorr F om K g b)) /\
  feq (vZ (vsub (knext F om K g b) K)) (vZ (kcorr F om K g b)).
Proof.
  split; intros m n; unfold knext, vsub, vadd, fsub, fadd, fscal; simpl; split; ring.
Qed.

Lemma fsub_feq_r (u v v' : fser) : feq v v' -> feq (fsub u v) (fsub u v').
Proof.
  intros H m n. destruct (H m n) as [H1 H2]. unfold fsub, fadd, fscal. simpl. rewrite H1, H2.
  split; reflexivity.
Qed.

Lemma mapp_feq (A : mf) (u v : vf) :
  feq (vR u) (vR v) -> feq (vZ u) (vZ v) ->
  feq (vR (mapp A u)) (vR (mapp A v)) /\ feq (vZ (mapp A u)) (vZ (mapp A v)).
Proof.
  intros H1 H2. unfold mapp. simpl.
  split; apply fadd_feq; apply fmul_feq_r; assumption.
Qed.

Section StepBounds.

Variables (F : fmodel) (om gamma w d : R) (K : vf) (g b : fser) (c : kcon) (eps : R).
Hypothesis Hdio : diophantine1 om gamma.
Hypothesis Hgam : 0 < gamma <= 1.
Hypothesis Hd : 0 < d.
Hypothesis Hw : 3 * d < w.
Hypothesis Heps : 0 <= eps.

Hypothesis CK : vcanon K.
Hypothesis PK : vsym K.
Hypothesis Cg : is_canon g.
Hypothesis Pg : is_even g.
Hypothesis Cb : is_canon b.
Hypothesis Pb : is_odd b.
Hypothesis Fb : fin w b.
Hypothesis FK : vfin w K.
Hypothesis BA : vbound w (cA c) (ktng K).
Hypothesis BG : nbound w (cG c) g.
Hypothesis BN : vbound w (cN c) (knrm K g b).
Hypothesis BE : vbound w eps (kerr F om K).
Hypothesis BT : nbound (w - d) (cTm c) (ktwist F om K g b).
Hypothesis Htau : 0 < ctau c <= Rabs (fc (ktwist F om K g b) 0 0).
Hypothesis Hframe : forall t p,
  feval (Sf F K) t p * feval (vdot (ktng K) (ktng K)) t p * feval g t p = 1.

Hypothesis CV : vcanon (Vf F K).
Hypothesis PV : vasym (Vf F K).
Hypothesis CD : mcanon (DVf F K).
Hypothesis PD : mpar (DVf F K).
Hypothesis CS : is_canon (Sf F K).
Hypothesis PS : is_even (Sf F K).
Hypothesis CGS : vcanon (GSf F K).
Hypothesis PGS : vsym (GSf F K).
Hypothesis BV : vbound w (cMV c) (Vf F K).
Hypothesis BD : mbound w (cD c) (DVf F K).
Hypothesis BS : nbound w (cS c) (Sf F K).
Hypothesis BS1 : vbound w (cS1 c) (GSf F K).
Hypothesis Hchain_R : forall t p,
  feval (dt (vR (Vf F K))) t p
  = feval (mRR (DVf F K)) t p * feval (vR (ktng K)) t p
    + feval (mRZ (DVf F K)) t p * feval (vZ (ktng K)) t p.
Hypothesis Hchain_Z : forall t p,
  feval (dt (vZ (Vf F K))) t p
  = feval (mZR (DVf F K)) t p * feval (vR (ktng K)) t p
    + feval (mZZ (DVf F K)) t p * feval (vZ (ktng K)) t p.
Hypothesis Hliou : forall t p,
  feval (lc om (Sf F K)) t p
  = feval (vdot (GSf F K) (kerr F om K)) t p - feval (Sf F K) t p * feval (mtr (DVf F K)) t p.

Hypothesis CV' : vcanon (Vf F (knext F om K g b)).
Hypothesis PV' : vasym (Vf F (knext F om K g b)).
Hypothesis BV' : vbound (w - 2 * d) (cMV c) (Vf F (knext F om K g b)).
Hypothesis Htaylor : forall P, vbound (w - 2 * d) P (vsub (knext F om K g b) K) ->
  vbound (w - 2 * d) (cM2 c * (P * P))
    (vsub (vsub (Vf F (knext F om K g b)) (Vf F K)) (mapp (DVf F K) (vsub (knext F om K g b) K))).

Let w1 := w - d.
Let w2 := w - 2 * d.

Lemma bw0 : 0 <= w. Proof. lra. Qed.
Lemma bw1 : 0 <= w1. Proof. unfold w1. lra. Qed.
Lemma bw2 : 0 <= w2. Proof. unfold w2. lra. Qed.
Lemma bw10 : w1 <= w. Proof. unfold w1. lra. Qed.
Lemma bw21 : w2 <= w1. Proof. unfold w1, w2. lra. Qed.
Lemma bw20 : w2 <= w. Proof. unfold w2. lra. Qed.

Lemma cA_nonneg : 0 <= cA c. Proof. exact (vbound_nonneg _ _ _ BA). Qed.
Lemma cG_nonneg : 0 <= cG c. Proof. exact (nbound_nonneg _ _ _ BG). Qed.
Lemma cS_nonneg : 0 <= cS c. Proof. exact (nbound_nonneg _ _ _ BS). Qed.
Lemma cS1_nonneg : 0 <= cS1 c. Proof. exact (vbound_nonneg _ _ _ BS1). Qed.
Lemma cTm_nonneg : 0 <= cTm c. Proof. exact (nbound_nonneg _ _ _ BT). Qed.
Lemma lc_nonneg : 0 <= linv_const gamma d.
Proof.
  unfold linv_const. apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat; lra].
  assert (0 < / (exp 1 * d)) by (apply Rinv_0_lt_compat, Rmult_lt_0_compat; [apply exp_pos | exact Hd]).
  lra.
Qed.
Lemma kdE_nonneg : 0 <= kdE d.
Proof. unfold kdE. apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; [apply exp_pos | exact Hd]. Qed.

(** * Canonical families and their parities *)

Lemma C_tng : vcanon (ktng K). Proof. apply vcanon_vdt, CK. Qed.
Lemma P_tng : vasym (ktng K). Proof. apply vsym_vdt, PK. Qed.
Lemma C_nrm : vcanon (knrm K g b).
Proof.
  apply vcanon_vadd; [apply vcanon_vsmul; [exact Cg | apply vcanon_vJ, C_tng] |].
  apply vcanon_vsmul; [exact Cb | apply C_tng].
Qed.
Lemma P_nrm : vsym (knrm K g b).
Proof.
  apply vsym_vadd; [apply vsym_vsmul_even; [exact Pg | apply vasym_vJ, P_tng] |].
  apply vsym_vsmul_odd; [exact Pb | apply P_tng].
Qed.
Lemma C_err : vcanon (kerr F om K). Proof. apply vcanon_vsub; [apply vcanon_vlc, CK | exact CV]. Qed.
Lemma P_err : vasym (kerr F om K). Proof. apply vasym_vsub; [apply vsym_vlc, PK | exact PV]. Qed.
Lemma C_eta1 : is_canon (keta1 F om K g b).
Proof. apply fmul_canon; [exact CS | apply wedge_canon; [apply C_err | apply C_nrm]]. Qed.
Lemma P_eta1 : is_even (keta1 F om K g b).
Proof. apply fmul_even_even; [exact PS | apply wedge_asym_sym; [apply P_err | apply P_nrm]]. Qed.
Lemma C_eta2 : is_canon (keta2 F om K).
Proof. apply fmul_canon; [exact CS | apply wedge_canon; [apply C_tng | apply C_err]]. Qed.
Lemma P_eta2 : is_odd (keta2 F om K).
Proof. apply fmul_even_odd; [exact PS | apply wedge_asym_asym; [apply P_tng | apply P_err]]. Qed.
Lemma C_mln : vcanon (kmln F om K g b).
Proof. apply vcanon_vsub; [apply vcanon_vlc, C_nrm | apply mapp_canon; [exact CD | apply C_nrm]]. Qed.
Lemma P_mln : vasym (kmln F om K g b).
Proof. apply vasym_vsub; [apply vsym_vlc, P_nrm | apply mapp_sym; [exact PD | apply P_nrm]]. Qed.
Lemma C_twist : is_canon (ktwist F om K g b).
Proof. apply fmul_canon; [exact CS | apply wedge_canon; [apply C_mln | apply C_nrm]]. Qed.
Lemma P_twist : is_even (ktwist F om K g b).
Proof. apply fmul_even_even; [exact PS | apply wedge_asym_sym; [apply P_mln | apply P_nrm]]. Qed.
Lemma C_w2 : is_canon (kw2 F om K). Proof. apply fscal_canon, linv_canon, C_eta2. Qed.
Lemma P_w2 : is_even (kw2 F om K). Proof. apply fscal_even, linv_odd, P_eta2. Qed.
Lemma C_xi2 : is_canon (kxi2 F om K g b). Proof. apply fadd_canon; [apply C_w2 | apply fconst_canon]. Qed.
Lemma P_xi2 : is_even (kxi2 F om K g b). Proof. apply fadd_even; [apply P_w2 | apply fconst_even]. Qed.
Lemma C_rhs1 : is_canon (krhs1 F om K g b).
Proof.
  apply fadd_canon; [apply C_eta1 |].
  apply fadd_canon; [apply fmul_canon; [apply C_twist | apply C_w2] | apply fscal_canon, C_twist].
Qed.
Lemma P_rhs1 : is_even (krhs1 F om K g b).
Proof.
  apply fadd_even; [apply P_eta1 |].
  apply fadd_even; [apply fmul_even_even; [apply P_twist | apply P_w2] | apply fscal_even, P_twist].
Qed.
Lemma C_xi1 : is_canon (kxi1 F om K g b). Proof. apply fscal_canon, linv_canon, C_rhs1. Qed.
Lemma P_xi1 : is_odd (kxi1 F om K g b). Proof. apply fscal_odd, linv_even, P_rhs1. Qed.
Lemma C_corr : vcanon (kcorr F om K g b).
Proof.
  apply vcanon_vadd; apply vcanon_vsmul; [apply C_xi1 | apply C_tng | apply C_xi2 | apply C_nrm].
Qed.
Lemma P_corr : vsym (kcorr F om K g b).
Proof.
  apply vsym_vadd; [apply vsym_vsmul_odd; [apply P_xi1 | apply P_tng] |
                    apply vsym_vsmul_even; [apply P_xi2 | apply P_nrm]].
Qed.

Theorem next_canon : vcanon (knext F om K g b). Proof. apply vcanon_vadd; [exact CK | apply C_corr]. Qed.
Theorem next_sym : vsym (knext F om K g b). Proof. apply vsym_vadd; [exact PK | apply P_corr]. Qed.

Lemma C_dE : vcanon (vdt (kerr F om K)). Proof. apply vcanon_vdt, C_err. Qed.
Lemma P_dE : vsym (vdt (kerr F om K)). Proof. apply vasym_vdt, P_err. Qed.
Lemma C_alpha : is_canon (kalpha F om K g b).
Proof. apply fmul_canon; [exact CS | apply wedge_canon; [apply C_dE | apply C_nrm]]. Qed.
Lemma P_alpha : is_odd (kalpha F om K g b).
Proof. apply fmul_even_odd; [exact PS | apply wedge_sym_sym; [apply P_dE | apply P_nrm]]. Qed.
Lemma C_beta : is_canon (kbeta F om K).
Proof. apply fmul_canon; [exact CS | apply wedge_canon; [apply C_tng | apply C_dE]]. Qed.
Lemma P_beta : is_even (kbeta F om K).
Proof.
  apply fmul_even_even; [exact PS |].
  destruct P_tng as [H1 H2]. destruct P_dE as [H3 H4].
  apply fsub_even; [apply fmul_odd_odd | apply fmul_even_even]; assumption.
Qed.
Lemma C_c : is_canon (kc F om K g b).
Proof.
  apply fsub_canon; [| apply C_alpha]. apply fscal_canon.
  apply fmul_canon; [| exact Cg]. apply fmul_canon; apply vdot_canon;
    [exact CGS | apply C_err | apply C_tng | apply C_tng].
Qed.
Lemma P_c : is_odd (kc F om K g b).
Proof.
  apply fsub_odd; [| apply P_alpha]. apply fscal_odd.
  apply fmul_odd_even; [| exact Pg].
  apply fmul_odd_even; [apply vdot_sym_asym; [exact PGS | apply P_err] |
                        apply vdot_asym_asym; apply P_tng].
Qed.
Lemma C_remq : vcanon (kremq F om K g b).
Proof. apply vcanon_vsub; [apply vcanon_vsub; [exact CV' | exact CV] | apply mapp_canon; [exact CD | apply C_corr]]. Qed.
Lemma P_remq : vasym (kremq F om K g b).
Proof. apply vasym_vsub; [apply vasym_vsub; [exact PV' | exact PV] | apply mapp_sym; [exact PD | apply P_corr]]. Qed.
Lemma C_errx : vcanon (kerrx F om K g b).
Proof.
  apply vcanon_vsub; [| apply C_remq]. apply vcanon_vadd; apply vcanon_vsmul.
  - apply fmul_canon; [apply C_alpha | apply C_xi1].
  - apply C_tng.
  - apply fadd_canon; apply fmul_canon; [apply C_beta | apply C_xi1 | apply C_c | apply C_xi2].
  - apply C_nrm.
Qed.
Lemma P_errx : vasym (kerrx F om K g b).
Proof.
  apply vasym_vsub; [| apply P_remq]. apply vasym_vadd.
  - apply vasym_vsmul_even; [apply fmul_odd_odd; [apply P_alpha | apply P_xi1] | apply P_tng].
  - apply vasym_vsmul_odd; [| apply P_nrm].
    apply fadd_odd; [apply fmul_even_odd; [apply P_beta | apply P_xi1] |
                     apply fmul_odd_even; [apply P_c | apply P_xi2]].
Qed.
Lemma C_errn : vcanon (kerr F om (knext F om K g b)).
Proof. apply vcanon_vsub; [apply vcanon_vlc, next_canon | exact CV']. Qed.
Theorem next_err_asym : vasym (kerr F om (knext F om K g b)).
Proof. apply vasym_vsub; [apply vsym_vlc, next_sym | exact PV']. Qed.

(** * The bounds *)

Lemma B_nrm : vbound w (kN c) (knrm K g b).
Proof. exact BN. Qed.

Lemma B_eta1 : nbound w (kH1 c * eps) (keta1 F om K g b).
Proof.
  apply (nbound_le _ (cS c * (2 * (eps * kN c)))); [unfold kH1; right; ring |].
  apply nbound_fmul; [apply bw0 | exact BS | apply nbound_wedge; [apply bw0 | exact BE | apply B_nrm]].
Qed.

Lemma B_eta2 : nbound w (kH2 c * eps) (keta2 F om K).
Proof.
  apply (nbound_le _ (cS c * (2 * (cA c * eps)))); [unfold kH2; right; ring |].
  apply nbound_fmul; [apply bw0 | exact BS | apply nbound_wedge; [apply bw0 | exact BA | exact BE]].
Qed.

Lemma B_w2 : nbound w1 (kW2 c gamma d * eps) (kw2 F om K).
Proof.
  apply (nbound_le _ (Rabs (-1) * (linv_const gamma d * (kH2 c * eps)))); [rewrite Rabs_m1; unfold kW2; right; ring |].
  apply nbound_fscal. apply (nbound_linv om gamma Hdio Hgam w d); [exact Hd | apply B_eta2].
Qed.

Lemma B_Tw2 : nbound w1 (cTm c * (kW2 c gamma d * eps)) (fmul (ktwist F om K g b) (kw2 F om K)).
Proof. apply nbound_fmul; [apply bw1 | exact BT | apply B_w2]. Qed.

Lemma B_xi20 : Rabs (kxi20 F om K g b) <= kZ c gamma d * eps.
Proof.
  assert (H1 : Rabs (fc (keta1 F om K g b) 0 0) <= kH1 c * eps) by (apply (coef_le w); [apply bw0 | apply B_eta1]).
  assert (H2 : Rabs (fc (fmul (ktwist F om K g b) (kw2 F om K)) 0 0) <= cTm c * (kW2 c gamma d * eps))
    by (apply (coef_le w1); [apply bw1 | apply B_Tw2]).
  destruct Htau as [Ht0 Ht].
  assert (Hne : fc (ktwist F om K g b) 0 0 <> 0) by (intros E; rewrite E, Rabs_R0 in Ht; lra).
  unfold kxi20, kZ. unfold Rdiv. rewrite Rabs_mult, Rabs_Ropp, (Rabs_Rinv _ Hne).
  pose proof (Rabs_triang (fc (keta1 F om K g b) 0 0) (fc (fmul (ktwist F om K g b) (kw2 F om K)) 0 0)) as Tr.
  apply Rle_trans with ((kH1 c * eps + cTm c * (kW2 c gamma d * eps)) * / ctau c).
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | lra |].
    apply Rinv_le_contravar; lra.
  - right. field. lra.
Qed.

Lemma B_xi2 : nbound w1 (kX2 c gamma d * eps) (kxi2 F om K g b).
Proof.
  apply (nbound_le _ (kW2 c gamma d * eps + Rabs (kxi20 F om K g b))).
  - unfold kX2. pose proof B_xi20. lra.
  - apply nbound_fadd; [apply B_w2 | apply nbound_fconst].
Qed.

Lemma B_rhs1 : nbound w1 (kR1 c gamma d * eps) (krhs1 F om K g b).
Proof.
  apply (nbound_le _ (kH1 c * eps + (cTm c * (kW2 c gamma d * eps) + Rabs (kxi20 F om K g b) * cTm c))).
  - unfold kR1. pose proof B_xi20. pose proof cTm_nonneg.
    assert (Rabs (kxi20 F om K g b) * cTm c <= kZ c gamma d * eps * cTm c) by (apply Rmult_le_compat_r; assumption).
    lra.
  - apply nbound_fadd; [apply (nbound_mono w); [apply bw10 | apply B_eta1] |].
    apply nbound_fadd; [apply B_Tw2 | apply nbound_fscal, BT].
Qed.

Lemma B_xi1 : nbound w2 (kX1 c gamma d * eps) (kxi1 F om K g b).
Proof.
  apply (nbound_le _ (Rabs (-1) * (linv_const gamma d * (kR1 c gamma d * eps)))); [rewrite Rabs_m1; unfold kX1; right; ring |].
  apply nbound_fscal. replace w2 with (w1 - d) by (unfold w1, w2; ring).
  apply (nbound_linv om gamma Hdio Hgam w1 d); [exact Hd | apply B_rhs1].
Qed.

Theorem bnd_corr : vbound w2 (kP c gamma d * eps) (kcorr F om K g b).
Proof.
  apply (vbound_le _ (kX1 c gamma d * eps * cA c + kX2 c gamma d * eps * kN c)); [unfold kP; right; ring |].
  apply vbound_vadd; apply vbound_vsmul.
  - apply bw2.
  - apply B_xi1.
  - apply (vbound_mono w); [apply bw20 | exact BA].
  - apply bw2.
  - apply (nbound_mono w1); [apply bw21 | apply B_xi2].
  - apply (vbound_mono w); [apply bw20 | apply B_nrm].
Qed.

Lemma B_dE : vbound w1 (kdE d * eps) (vdt (kerr F om K)).
Proof. apply vbound_vdt; [exact Hd | exact BE]. Qed.

Lemma B_alpha : nbound w1 (kAl c d * eps) (kalpha F om K g b).
Proof.
  apply (nbound_le _ (cS c * (2 * (kdE d * eps * kN c)))); [unfold kAl; right; ring |].
  apply nbound_fmul; [apply bw1 | apply (nbound_mono w); [apply bw10 | exact BS] |].
  apply nbound_wedge; [apply bw1 | apply B_dE | apply (vbound_mono w); [apply bw10 | apply B_nrm]].
Qed.

Lemma B_beta : nbound w1 (kBe c d * eps) (kbeta F om K).
Proof.
  apply (nbound_le _ (cS c * (2 * (cA c * (kdE d * eps))))); [unfold kBe; right; ring |].
  apply nbound_fmul; [apply bw1 | apply (nbound_mono w); [apply bw10 | exact BS] |].
  apply nbound_wedge; [apply bw1 | apply (vbound_mono w); [apply bw10 | exact BA] | apply B_dE].
Qed.

Lemma B_c : nbound w1 (kC c d * eps) (kc F om K g b).
Proof.
  apply (nbound_le _ (Rabs (-1) * (2 * (cS1 c * eps) * (2 * (cA c * cA c)) * cG c) + kAl c d * eps));
    [rewrite Rabs_m1; unfold kC; right; ring |].
  apply nbound_fsub; [| apply B_alpha]. apply nbound_fscal.
  apply nbound_fmul; [apply bw1 | | apply (nbound_mono w); [apply bw10 | exact BG]].
  apply nbound_fmul; [apply bw1 | |].
  - apply nbound_vdot; [apply bw1 | apply (vbound_mono w); [apply bw10 | exact BS1] |
                        apply (vbound_mono w); [apply bw10 | exact BE]].
  - apply nbound_vdot; [apply bw1 | |]; apply (vbound_mono w); [apply bw10 | exact BA | apply bw10 | exact BA].
Qed.

Lemma B_remq : vbound w2 (cM2 c * (kP c gamma d * eps * (kP c gamma d * eps))) (kremq F om K g b).
Proof.
  destruct (next_sub_feq F om K g b) as [E1 E2].
  pose proof (Htaylor (kP c gamma d * eps)
                (vbound_feq _ _ _ _ (feq_sym _ _ E1) (feq_sym _ _ E2) bnd_corr)) as H.
  destruct (mapp_feq (DVf F K) _ _ E1 E2) as [M1 M2].
  refine (vbound_feq _ _ _ _ _ _ H).
  - unfold kremq. exact (fsub_feq_r _ _ _ M1).
  - unfold kremq. exact (fsub_feq_r _ _ _ M2).
Qed.

Lemma B_errx : vbound w2 (kE c gamma d * (eps * eps)) (kerrx F om K g b).
Proof.
  apply (vbound_le _ (kAl c d * eps * (kX1 c gamma d * eps) * cA c
                      + (kBe c d * eps * (kX1 c gamma d * eps) + kC c d * eps * (kX2 c gamma d * eps)) * kN c
                      + cM2 c * (kP c gamma d * eps * (kP c gamma d * eps))));
    [unfold kE; right; ring |].
  apply vbound_vsub; [| apply B_remq]. apply vbound_vadd; apply vbound_vsmul.
  - apply bw2.
  - apply nbound_fmul; [apply bw2 | apply (nbound_mono w1); [apply bw21 | apply B_alpha] | apply B_xi1].
  - apply (vbound_mono w); [apply bw20 | exact BA].
  - apply bw2.
  - apply nbound_fadd; apply nbound_fmul.
    + apply bw2.
    + apply (nbound_mono w1); [apply bw21 | apply B_beta].
    + apply B_xi1.
    + apply bw2.
    + apply (nbound_mono w1); [apply bw21 | apply B_c].
    + apply (nbound_mono w1); [apply bw21 | apply B_xi2].
  - apply (vbound_mono w); [apply bw20 | apply B_nrm].
Qed.

(** * The error of the next torus *)

Lemma fin_of (rho M : R) (u : fser) : nbound rho M u -> fin rho u.
Proof. intros H. exists M. exact H. Qed.

Lemma vfin_of (rho M : R) (u : vf) : vbound rho M u -> vfin rho u.
Proof. intros [H1 H2]. split; eapply fin_of; eassumption. Qed.

Lemma mfin_of (rho M : R) (A : mf) : mbound rho M A -> mfin rho A.
Proof. intros [H1 [H2 [H3 H4]]]. repeat split; eapply fin_of; eassumption. Qed.

Lemma FlK : vfin w (vlc om K).
Proof.
  destruct (vfin_of _ _ _ BE) as [E1 E2]. destruct (vfin_of _ _ _ BV) as [V1 V2].
  split.
  - destruct (fin_fadd _ _ _ E1 V1) as [M HM]. exists M.
    exact (nbound_feq _ _ _ _ (feq_sym _ _ (lc_err_R F om K)) HM).
  - destruct (fin_fadd _ _ _ E2 V2) as [M HM]. exists M.
    exact (nbound_feq _ _ _ _ (feq_sym _ _ (lc_err_Z F om K)) HM).
Qed.

Theorem step_bound : vbound w2 (kE c gamma d * (eps * eps)) (kerr F om (knext F om K g b)).
Proof.
  assert (Htw : fc (ktwist F om K g b) 0 0 <> 0).
  { intros E. destruct Htau as [H0 H1]. rewrite E, Rabs_R0 in H1. lra. }
  pose proof (step_identity F om gamma w d K g b Hdio Hgam Hd Hw FK (vfin_of _ _ _ BA) FlK
                (fin_of _ _ _ BG) Fb (fin_of _ _ _ BS) (vfin_of _ _ _ BS1) (mfin_of _ _ _ BD)
                (vfin_of _ _ _ BV) (vfin_of _ _ _ BV') Hframe Hchain_R Hchain_Z Hliou
                (P_eta2 0%Z 0%Z) Htw) as SI.
  assert (Hw2 : 0 < w2) by (unfold w2; lra).
  assert (Fn : vfin w2 (knext F om K g b)).
  { apply vfin_vadd; [apply (vfin_mono w); [apply bw20 | exact FK] | apply (vfin_of _ _ _ bnd_corr)]. }
  assert (Fe : vfin 0 (kerr F om (knext F om K g b))).
  { apply vfin_vsub.
    - replace 0 with (w2 - w2) by ring. apply vfin_vlc; [exact Hw2 | exact Fn].
    - apply (vfin_mono w2); [apply bw2 | apply (vfin_of _ _ _ BV')]. }
  assert (Fx : vfin 0 (kerrx F om K g b)).
  { apply (vfin_mono w2); [apply bw2 | apply (vfin_of _ _ _ B_errx)]. }
  destruct Fe as [[M1 H1] [M2 H2]]. destruct Fx as [[M3 H3] [M4 H4]].
  assert (ER : feq (vR (kerr F om (knext F om K g b))) (vR (kerrx F om K g b))).
  { apply (canon_feq _ _ M1 M3); [apply (proj1 C_errn) | apply (proj1 C_errx) | exact H1 | exact H3 |].
    intros t p. exact (proj1 (SI t p)). }
  assert (EZ : feq (vZ (kerr F om (knext F om K g b))) (vZ (kerrx F om K g b))).
  { apply (canon_feq _ _ M2 M4); [apply (proj2 C_errn) | apply (proj2 C_errx) | exact H2 | exact H4 |].
    intros t p. exact (proj2 (SI t p)). }
  exact (vbound_feq _ _ _ _ (feq_sym _ _ ER) (feq_sym _ _ EZ) B_errx).
Qed.

End StepBounds.
