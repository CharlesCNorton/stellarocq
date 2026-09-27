(** The frame and the twist after the Newton step.

    After the step K' = K + xi_1 a + xi_2 N, the new tangent a' = d_t K'
    differs from a by at most kdA eps ([U_dtng]). The next frame inverse is
    Newton's inverse g' of sigma' |a'|^2 started from g ([gnext]): since
    sigma |a|^2 g = 1 as canonical families, 1 - sigma' |a'|^2 g is
    (sigma |a|^2 - sigma' |a'|^2) g, of norm at most G kU eps, and g' stays
    within kdG eps of g ([U_g'sub]) while sigma' |a'|^2 g' = 1 at every point
    ([U_frame']). The normal N' = J a' g' + b a' stays within kdN eps of N
    ([U_dN]), b being fixed. The torsion T moves by at most kT eps on the
    strip of width w - 3 delta - delta / 2, where L costs the half loss
    delta / 2 and where the next step reads its torsion ([U_dT]); the same
    bound holds for the move of its average ([U_twist]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon KAMFrame KAMVec KAMFin KAMStep KAMBound KAMDiff.
Local Open Scope R_scope.

Definition kdA (c : kcon) (gamma d : R) : R := kdE d * kP c gamma d.
Definition kU (c : kcon) (gamma d : R) : R :=
  cLS c * kP c gamma d * (2 * (cA c * cA c)) + cS c * (6 * (cA c * kdA c gamma d)).
Definition kdG (c : kcon) (gamma d : R) : R := 8 * (cG c * (cG c * kU c gamma d)).
Definition kdN (c : kcon) (gamma d : R) : R :=
  kdG c gamma d * (2 * cA c) + cG c * kdA c gamma d + cB c * kdA c gamma d.
(** L's cost over the half loss on which the next step reads the torsion. *)
Definition kLd (om d : R) : R := (Rabs om + / kappa) * kdE (d / 2).
Definition kM (c : kcon) (om d : R) : R := kLd om d * cN c + 2 * (cD c * cN c).
Definition kdM (c : kcon) (om gamma d : R) : R :=
  kLd om d * kdN c gamma d + 2 * (cLD c * kP c gamma d * (2 * cN c) + cD c * kdN c gamma d).
Definition kW (c : kcon) (om d : R) : R := 2 * (kM c om d * cN c).
Definition kdW (c : kcon) (om gamma d : R) : R :=
  2 * (kdM c om gamma d * (2 * cN c) + kM c om d * kdN c gamma d).
Definition kT (c : kcon) (om gamma d : R) : R :=
  cLS c * kP c gamma d * (2 * kW c om d) + cS c * kdW c om gamma d.

(** The next frame inverse. *)
Definition gnext (F : fmodel) (om : R) (K : vf) (g b : fser) : fser :=
  finv (fmul (Sf F (knext F om K g b)) (vdot (ktng (knext F om K g b)) (ktng (knext F om K g b)))) g.

Lemma vbound_vsub_sym (rho M : R) (u v : vf) : vbound rho M (vsub u v) -> vbound rho M (vsub v u).
Proof. intros [H1 H2]. split; apply nbound_fsub_sym; assumption. Qed.

Lemma vbound_add_diff (rho M Md : R) (u u' : vf) :
  vbound rho M u -> vbound rho Md (vsub u' u) -> vbound rho (M + Md) u'.
Proof.
  intros [H1 H2] [H3 H4]. split.
  - exact (nbound_add_diff rho M Md (vR u) (vR u') H1 H3).
  - exact (nbound_add_diff rho M Md (vZ u) (vZ u') H2 H4).
Qed.

Lemma fsub_feq_l (u u' v : fser) : feq u u' -> feq (fsub u v) (fsub u' v).
Proof.
  intros H m n. destruct (H m n) as [H1 H2]. unfold fsub. fnorm. rewrite H1, H2. split; reflexivity.
Qed.

Lemma nbound_fsub_self (rho : R) (u : fser) : nbound rho 0 (fsub u u).
Proof.
  apply (nbound_feq _ _ fzero); [| apply nbound_fzero].
  intros m n. unfold fsub. fnorm. cbn [fc fs fzero]. split; ring.
Qed.

Lemma vJ_sub_feq (u u' : vf) :
  feq (vR (vsub (vJ u') (vJ u))) (vR (vJ (vsub u' u))) /\ feq (vZ (vsub (vJ u') (vJ u))) (vZ (vJ (vsub u' u))).
Proof. split; intros m n; cbn [vR vZ vsub vJ]; unfold fsub; fnorm; split; ring. Qed.

Lemma vadd_sub_feq (x x' y y' : vf) :
  feq (vR (vsub (vadd x' y') (vadd x y))) (vR (vadd (vsub x' x) (vsub y' y))) /\
  feq (vZ (vsub (vadd x' y') (vadd x y))) (vZ (vadd (vsub x' x) (vsub y' y))).
Proof. split; intros m n; cbn [vR vZ vsub vadd]; unfold fsub; fnorm; split; ring. Qed.

Lemma kmln_sub_feq (F : fmodel) (om : R) (K K' : vf) (g g' b : fser) :
  feq (vR (vsub (kmln F om K' g' b) (kmln F om K g b)))
      (vR (vsub (vsub (vlc om (knrm K' g' b)) (vlc om (knrm K g b)))
                (vsub (mapp (DVf F K') (knrm K' g' b)) (mapp (DVf F K) (knrm K g b))))) /\
  feq (vZ (vsub (kmln F om K' g' b) (kmln F om K g b)))
      (vZ (vsub (vsub (vlc om (knrm K' g' b)) (vlc om (knrm K g b)))
                (vsub (mapp (DVf F K') (knrm K' g' b)) (mapp (DVf F K) (knrm K g b))))).
Proof. unfold kmln. split; intros m n; cbn [vR vZ vsub]; unfold fsub; fnorm; split; ring. Qed.

Section Update.

Variables (F : fmodel) (om gamma w d : R) (K : vf) (g b : fser) (c : kcon) (eps : R).
Hypothesis Hdio : diophantine1 om gamma.
Hypothesis Hgam : 0 < gamma <= 1.
Hypothesis Hd : 0 < d.
Hypothesis Hw : 7 * d < 2 * w.
Hypothesis Heps : 0 <= eps.
Hypothesis CK : vcanon K.
Hypothesis PK : vsym K.
Hypothesis Cg : is_canon g.
Hypothesis Pg : is_even g.
Hypothesis Cb : is_canon b.
Hypothesis Pb : is_odd b.
Hypothesis BB : nbound w (cB c) b.
Hypothesis BA : vbound w (cA c) (ktng K).
Hypothesis BG : nbound w (cG c) g.
Hypothesis BN : vbound w (cN c) (knrm K g b).
Hypothesis BE : vbound w eps (kerr F om K).
Hypothesis BT : nbound (w - d) (cTm c) (ktwist F om K g b).
Hypothesis Htau : 0 < ctau c <= Rabs (fc (ktwist F om K g b) 0 0).
Hypothesis Hframe : forall t p,
  feval (Sf F K) t p * feval (vdot (ktng K) (ktng K)) t p * feval g t p = 1.
Hypothesis CV : vcanon (Vf F K).
Hypothesis CD : mcanon (DVf F K).
Hypothesis CS : is_canon (Sf F K).
Hypothesis PV : vasym (Vf F K).
Hypothesis PD : mpar (DVf F K).
Hypothesis PS : is_even (Sf F K).
Hypothesis BD : mbound w (cD c) (DVf F K).
Hypothesis BS : nbound w (cS c) (Sf F K).

Hypothesis CS' : is_canon (Sf F (knext F om K g b)).
Hypothesis PS' : is_even (Sf F (knext F om K g b)).
Hypothesis BS' : nbound (w - 2 * d) (cS c) (Sf F (knext F om K g b)).
Hypothesis HlipS : forall P, vbound (w - 2 * d) P (vsub (knext F om K g b) K) ->
  nbound (w - 2 * d) (cLS c * P) (fsub (Sf F (knext F om K g b)) (Sf F K)).
Hypothesis HlipD : forall P, vbound (w - 2 * d) P (vsub (knext F om K g b) K) ->
  mbound (w - 2 * d) (cLD c * P) (msub (DVf F (knext F om K g b)) (DVf F K)).
Hypothesis Hsm_a : kdA c gamma d * eps <= cA c.
Hypothesis Hsm_q : cG c * (kU c gamma d * eps) <= / 2.
Hypothesis Hsm_g : kdG c gamma d * eps <= cG c.
Hypothesis Hsm_n : kdN c gamma d * eps <= cN c.
Hypothesis Hsm_w : kdW c om gamma d * eps <= kW c om d.

Let w2 := w - 2 * d.
Let w3 := w - 3 * d.
Let w4 := w - 3 * d - d / 2.
Let K' := knext F om K g b.
Let g' := gnext F om K g b.

Lemma uw3d : 3 * d < w. Proof. lra. Qed.
Lemma uw2 : 0 < w2. Proof. unfold w2. lra. Qed.
Lemma uw3 : 0 < w3. Proof. unfold w3. lra. Qed.
Lemma uw4 : 0 < w4. Proof. unfold w4. lra. Qed.
Lemma uw32 : w3 <= w2. Proof. unfold w2, w3. lra. Qed.
Lemma uw30 : w3 <= w. Proof. unfold w3. lra. Qed.
Lemma uw43 : w4 <= w3. Proof. unfold w3, w4. lra. Qed.
Lemma uw42 : w4 <= w2. Proof. unfold w2, w4. lra. Qed.
Lemma uw40 : w4 <= w. Proof. unfold w4. lra. Qed.
Lemma uw41 : w4 <= w - d. Proof. unfold w4. lra. Qed.

Lemma uA : 0 <= cA c. Proof. exact (vbound_nonneg _ _ _ BA). Qed.
Lemma uG : 0 <= cG c. Proof. exact (nbound_nonneg _ _ _ BG). Qed.
Lemma uS : 0 <= cS c. Proof. exact (nbound_nonneg _ _ _ BS). Qed.
Lemma uD : 0 <= cD c. Proof. exact (mbound_nonneg _ _ _ BD). Qed.
Lemma uN : 0 <= cN c. Proof. exact (vbound_nonneg _ _ _ BN). Qed.

Lemma U_dK : vbound w2 (kP c gamma d * eps) (vsub K' K).
Proof.
  pose proof (bnd_corr F om gamma w d K g b c eps Hdio Hgam Hd uw3d BA BN BE BT Htau BS) as Hc.
  destruct (next_sub_feq F om K g b) as [E1 E2].
  exact (vbound_feq _ _ _ _ (feq_sym _ _ E1) (feq_sym _ _ E2) Hc).
Qed.

Lemma U_kP : 0 <= kP c gamma d * eps. Proof. exact (vbound_nonneg _ _ _ U_dK). Qed.

Lemma U_dtng : vbound w3 (kdA c gamma d * eps) (vsub (ktng K') (ktng K)).
Proof.
  apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vdt_sub_feq K K'))).
  replace w3 with (w2 - d) by (unfold w2, w3; ring).
  apply (vbound_le _ (/ (exp 1 * d) * (kP c gamma d * eps))); [unfold kdA, kdE; right; ring |].
  apply vbound_vdt; [exact Hd | exact U_dK].
Qed.

Lemma U_tng' : vbound w3 (2 * cA c) (ktng K').
Proof.
  apply (vbound_le _ (cA c + kdA c gamma d * eps)); [lra |].
  apply (vbound_add_diff _ _ _ (ktng K)); [apply (vbound_mono w); [apply uw30 | exact BA] | exact U_dtng].
Qed.

Lemma U_sig : nbound w3 (cLS c * (kP c gamma d * eps)) (fsub (Sf F K) (Sf F K')).
Proof. apply nbound_fsub_sym. apply (nbound_mono w2); [apply uw32 | apply HlipS, U_dK]. Qed.

Lemma U_aa : nbound w3 (6 * (cA c * (kdA c gamma d * eps)))
  (fsub (vdot (ktng K) (ktng K)) (vdot (ktng K') (ktng K'))).
Proof.
  assert (Hd' : vbound w3 (kdA c gamma d * eps) (vsub (ktng K) (ktng K'))) by (apply vbound_vsub_sym, U_dtng).
  apply (nbound_le _ (2 * (kdA c gamma d * eps * cA c + 2 * cA c * (kdA c gamma d * eps)))); [right; ring |].
  apply vdot_diff; [left; apply uw3 | exact U_tng' | apply (vbound_mono w); [apply uw30 | exact BA] | exact Hd' | exact Hd'].
Qed.

Lemma U_u : nbound w3 (kU c gamma d * eps)
  (fsub (fmul (Sf F K) (vdot (ktng K) (ktng K))) (fmul (Sf F K') (vdot (ktng K') (ktng K')))).
Proof.
  apply (nbound_le _ (cLS c * (kP c gamma d * eps) * (2 * (cA c * cA c))
                      + cS c * (6 * (cA c * (kdA c gamma d * eps))))); [unfold kU; right; ring |].
  apply fmul_diff.
  - left; apply uw3.
  - apply (nbound_mono w2); [apply uw32 | exact BS'].
  - apply nbound_vdot; [left; apply uw3 | |]; apply (vbound_mono w); [apply uw30 | exact BA | apply uw30 | exact BA].
  - exact U_sig.
  - exact U_aa.
Qed.

Lemma C_tng0 : vcanon (ktng K). Proof. apply vcanon_vdt, CK. Qed.
Lemma C_tng' : vcanon (ktng K').
Proof. apply vcanon_vdt. exact (next_canon F om K g b CK Cg Cb CV CD CS). Qed.
Lemma P_tng' : vasym (ktng K').
Proof. apply vsym_vdt. exact (next_sym F om K g b PK Pg Pb PV PD PS). Qed.

Lemma U_one : feq fone (fmul (fmul (Sf F K) (vdot (ktng K) (ktng K))) g).
Proof.
  assert (Baa : nbound w (2 * (cA c * cA c)) (vdot (ktng K) (ktng K))) by (apply nbound_vdot; [lra | exact BA | exact BA]).
  assert (Bu : nbound w (cS c * (2 * (cA c * cA c))) (fmul (Sf F K) (vdot (ktng K) (ktng K))))
    by (apply nbound_fmul; [lra | exact BS | exact Baa]).
  assert (Bug : nbound w (cS c * (2 * (cA c * cA c)) * cG c) (fmul (fmul (Sf F K) (vdot (ktng K) (ktng K))) g))
    by (apply nbound_fmul; [lra | exact Bu | exact BG]).
  assert (H0 : 0 <= w) by lra.
  apply (canon_feq _ _ 1 (cS c * (2 * (cA c * cA c)) * cG c)).
  - apply fone_canon.
  - apply fmul_canon; [apply fmul_canon; [exact CS | apply vdot_canon; apply C_tng0] | exact Cg].
  - apply nbound_fone.
  - apply (nbound_mono w); [exact H0 | exact Bug].
  - intros t p. rewrite feval_fone.
    rewrite (feval_fmul _ _ _ _ t p (nbound_mono w 0 _ _ H0 Bu) (nbound_mono w 0 _ _ H0 BG)).
    rewrite (feval_fmul _ _ _ _ t p (nbound_mono w 0 _ _ H0 BS) (nbound_mono w 0 _ _ H0 Baa)).
    symmetry. apply Hframe.
Qed.

Lemma U_res : nbound w3 (cG c * (kU c gamma d * eps))
  (fsub fone (fmul (fmul (Sf F K') (vdot (ktng K') (ktng K'))) g)).
Proof.
  set (u := fmul (Sf F K) (vdot (ktng K) (ktng K))).
  set (u' := fmul (Sf F K') (vdot (ktng K') (ktng K'))).
  assert (Hw3 : 0 <= w3) by (left; apply uw3).
  assert (Bu : nbound w3 (cS c * (2 * (cA c * cA c))) u).
  { apply nbound_fmul; [exact Hw3 | apply (nbound_mono w); [apply uw30 | exact BS] |].
    apply nbound_vdot; [exact Hw3 | |]; apply (vbound_mono w); [apply uw30 | exact BA | apply uw30 | exact BA]. }
  assert (Bu' : nbound w3 (cS c * (2 * (2 * cA c * (2 * cA c)))) u').
  { apply nbound_fmul; [exact Hw3 | apply (nbound_mono w2); [apply uw32 | exact BS'] |].
    apply nbound_vdot; [exact Hw3 | exact U_tng' | exact U_tng']. }
  assert (Bg : nbound w3 (cG c) g) by (apply (nbound_mono w); [apply uw30 | exact BG]).
  apply (nbound_feq _ _ (fmul (fsub u u') g)).
  - apply (feq_trans _ (fsub (fmul u g) (fmul u' g))).
    + intros m n.
      destruct (fmul_fadd_l w3 Hw3 u (fscal (-1) u') g _ _ _ Bu (nbound_fscal _ _ (-1) _ Bu') Bg m n) as [A1 A2].
      destruct (fmul_fscal_l w3 Hw3 (-1) u' g _ _ Bu' Bg m n) as [B1 B2].
      rewrite fc_fadd' in A1. rewrite fs_fadd' in A2. rewrite fc_fscal' in B1. rewrite fs_fscal' in B2.
      unfold fsub. fnorm. rewrite A1, A2, B1, B2. split; ring.
    + apply fsub_feq_l. apply feq_sym, U_one.
  - apply (nbound_le _ (kU c gamma d * eps * cG c)); [right; ring |].
    apply nbound_fmul; [exact Hw3 | exact U_u | exact Bg].
Qed.

Lemma U_q : 0 <= cG c * (kU c gamma d * eps) < 1.
Proof. split; [exact (nbound_nonneg _ _ _ U_res) | lra]. Qed.

Lemma inv_eps_le (G q : R) : 0 <= G -> 0 <= q <= / 2 -> inv_eps G q 0 <= 8 * (G * q).
Proof.
  intros HG [Hq0 Hq1]. unfold inv_eps, inv_T. simpl.
  replace (2 * (G / (1 - q) * (q * 1 / (1 - q)))) with (2 * (G * q) / ((1 - q) * (1 - q))) by (field; lra).
  apply (Rmult_le_reg_r ((1 - q) * (1 - q))); [nra |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. rewrite Rmult_1_r.
  assert (H4 : / 4 <= (1 - q) * (1 - q)) by nra.
  assert (H5 : 0 <= G * q) by nra.
  apply (Rle_trans _ (8 * (G * q) * / 4)); [lra |].
  apply Rmult_le_compat_l; [lra | exact H4].
Qed.

Lemma U_g'sub : nbound w3 (kdG c gamma d * eps) (fsub g' g).
Proof.
  apply nbound_fsub_sym.
  assert (Bg : nbound w3 (cG c) g) by (apply (nbound_mono w); [apply uw30 | exact BG]).
  pose proof (nbound_finv_sub w3 (Rlt_le _ _ uw3) _ g (cG c) (cG c * (kU c gamma d * eps)) Bg U_q U_res) as H.
  apply (nbound_le _ (inv_eps (cG c) (cG c * (kU c gamma d * eps)) 0)); [| exact H].
  apply (Rle_trans _ (8 * (cG c * (cG c * (kU c gamma d * eps))))).
  - apply inv_eps_le; [apply uG | split; [apply U_q | exact Hsm_q]].
  - unfold kdG. right. ring.
Qed.

Lemma U_g' : nbound w3 (2 * cG c) g'.
Proof.
  apply (nbound_le _ (cG c + kdG c gamma d * eps)); [lra |].
  apply (nbound_add_diff _ _ _ g); [apply (nbound_mono w); [apply uw30 | exact BG] | exact U_g'sub].
Qed.

Lemma U_frame' : forall t p,
  feval (Sf F K') t p * feval (vdot (ktng K') (ktng K')) t p * feval g' t p = 1.
Proof.
  intros t p.
  assert (Hw3 : 0 <= w3) by (left; apply uw3).
  assert (Baa : nbound w3 (2 * (2 * cA c * (2 * cA c))) (vdot (ktng K') (ktng K'))).
  { apply nbound_vdot; [exact Hw3 | exact U_tng' | exact U_tng']. }
  assert (BS3 : nbound w3 (cS c) (Sf F K')) by (apply (nbound_mono w2); [apply uw32 | exact BS']).
  assert (Bu' : nbound w3 (cS c * (2 * (2 * cA c * (2 * cA c)))) (fmul (Sf F K') (vdot (ktng K') (ktng K')))).
  { apply nbound_fmul; [exact Hw3 | exact BS3 | exact Baa]. }
  assert (Bg : nbound w3 (cG c) g) by (apply (nbound_mono w); [apply uw30 | exact BG]).
  pose proof (feval_finv w3 Hw3 _ g _ (cG c) (cG c * (kU c gamma d * eps)) Bu' Bg U_q U_res t p) as H.
  rewrite (feval_fmul _ _ _ _ t p (nbound_mono w3 0 _ _ Hw3 BS3) (nbound_mono w3 0 _ _ Hw3 Baa)) in H.
  exact H.
Qed.

Lemma U_g'canon : is_canon g'.
Proof.
  apply finv_canon; [| exact Cg]. apply fmul_canon; [exact CS' | apply vdot_canon; apply C_tng'].
Qed.

Lemma U_g'even : is_even g'.
Proof.
  apply finv_even; [| exact Pg]. apply fmul_even_even; [exact PS' | apply vdot_asym_asym; apply P_tng'].
Qed.

(** * The normal *)

Lemma U_N : vbound w3 (cN c) (knrm K g b).
Proof. apply (vbound_mono w); [apply uw30 | exact BN]. Qed.

Lemma U_dN : vbound w3 (kdN c gamma d * eps) (vsub (knrm K' g' b) (knrm K g b)).
Proof.
  assert (Hw3 : 0 <= w3) by (left; apply uw3).
  unfold knrm.
  apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vadd_sub_feq _ _ _ _))).
  apply (vbound_le _ ((kdG c gamma d * eps * (2 * cA c) + cG c * (kdA c gamma d * eps))
                      + (0 * (2 * cA c) + cB c * (kdA c gamma d * eps)))); [unfold kdN; right; ring |].
  apply vbound_vadd.
  - apply vsmul_diff.
    + exact Hw3.
    + apply (nbound_mono w); [apply uw30 | exact BG].
    + apply vbound_vJ, U_tng'.
    + exact U_g'sub.
    + apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vJ_sub_feq (ktng K) (ktng K')))). apply vbound_vJ, U_dtng.
  - apply vsmul_diff.
    + exact Hw3.
    + apply (nbound_mono w); [apply uw30 | exact BB].
    + exact U_tng'.
    + apply nbound_fsub_self.
    + exact U_dtng.
Qed.

Lemma U_N' : vbound w3 (2 * cN c) (knrm K' g' b).
Proof.
  apply (vbound_le _ (cN c + kdN c gamma d * eps)); [lra |].
  apply (vbound_add_diff _ _ _ (knrm K g b)); [exact U_N | exact U_dN].
Qed.

(** * The twist *)

Lemma Hd2 : 0 < d / 2. Proof. lra. Qed.

Lemma U_mln : vbound w4 (kM c om d) (kmln F om K g b).
Proof.
  unfold kM, kLd, kdE. apply vbound_vsub.
  - replace w4 with (w3 - d / 2) by (unfold w3, w4; ring). apply vbound_vlc; [exact Hd2 | exact U_N].
  - apply vbound_mapp; [left; apply uw4 | apply (mbound_mono w); [apply uw40 | exact BD] |
                        apply (vbound_mono w3); [apply uw43 | exact U_N]].
Qed.

Lemma U_dmln : vbound w4 (kdM c om gamma d * eps) (vsub (kmln F om K' g' b) (kmln F om K g b)).
Proof.
  apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (kmln_sub_feq F om K K' g g' b))).
  apply (vbound_le _ (kLd om d * (kdN c gamma d * eps)
                      + 2 * (cLD c * (kP c gamma d * eps) * (2 * cN c) + cD c * (kdN c gamma d * eps))));
    [unfold kdM; right; ring |].
  apply vbound_vsub.
  - apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vlc_sub_feq om (knrm K g b) (knrm K' g' b)))).
    unfold kLd, kdE. replace w4 with (w3 - d / 2) by (unfold w3, w4; ring).
    apply vbound_vlc; [exact Hd2 | exact U_dN].
  - apply mapp_diff.
    + left; apply uw4.
    + apply (mbound_mono w); [apply uw40 | exact BD].
    + apply (vbound_mono w3); [apply uw43 | exact U_N'].
    + apply (mbound_mono w2); [apply uw42 | apply HlipD, U_dK].
    + apply (vbound_mono w3); [apply uw43 | exact U_dN].
Qed.

Lemma U_W : nbound w4 (kW c om d) (wedge (kmln F om K g b) (knrm K g b)).
Proof.
  unfold kW. apply nbound_wedge; [left; apply uw4 | exact U_mln | apply (vbound_mono w3); [apply uw43 | exact U_N]].
Qed.

Lemma U_dW : nbound w4 (kdW c om gamma d * eps)
  (fsub (wedge (kmln F om K' g' b) (knrm K' g' b)) (wedge (kmln F om K g b) (knrm K g b))).
Proof.
  apply (nbound_le _ (2 * (kdM c om gamma d * eps * (2 * cN c) + kM c om d * (kdN c gamma d * eps))));
    [unfold kdW; right; ring |].
  apply wedge_diff.
  - left; apply uw4.
  - exact U_mln.
  - apply (vbound_mono w3); [apply uw43 | exact U_N'].
  - exact U_dmln.
  - apply (vbound_mono w3); [apply uw43 | exact U_dN].
Qed.

Lemma U_W' : nbound w4 (2 * kW c om d) (wedge (kmln F om K' g' b) (knrm K' g' b)).
Proof.
  apply (nbound_le _ (kW c om d + kdW c om gamma d * eps)); [lra |].
  apply (nbound_add_diff _ _ _ (wedge (kmln F om K g b) (knrm K g b))); [exact U_W | exact U_dW].
Qed.

Lemma U_dT : nbound w4 (kT c om gamma d * eps) (fsub (ktwist F om K' g' b) (ktwist F om K g b)).
Proof.
  apply (nbound_le _ (cLS c * (kP c gamma d * eps) * (2 * kW c om d) + cS c * (kdW c om gamma d * eps)));
    [unfold kT; right; ring |].
  unfold ktwist. apply fmul_diff.
  - left; apply uw4.
  - apply (nbound_mono w); [apply uw40 | exact BS].
  - exact U_W'.
  - apply nbound_fsub_sym. apply (nbound_mono w3); [apply uw43 | exact U_sig].
  - exact U_dW.
Qed.

Theorem U_T' : nbound w4 (cTm c + kT c om gamma d * eps) (ktwist F om K' g' b).
Proof.
  apply (nbound_add_diff _ _ _ (ktwist F om K g b)); [| exact U_dT].
  apply (nbound_mono (w - d)); [apply uw41 | exact BT].
Qed.

Theorem U_twist :
  Rabs (fc (ktwist F om K' g' b) 0 0 - fc (ktwist F om K g b) 0 0) <= kT c om gamma d * eps.
Proof.
  replace (fc (ktwist F om K' g' b) 0 0 - fc (ktwist F om K g b) 0 0)
    with (fc (fsub (ktwist F om K' g' b) (ktwist F om K g b)) 0 0) by (unfold fsub; fnorm; ring).
  apply (coef_le w4); [left; apply uw4 | exact U_dT].
Qed.

End Update.
