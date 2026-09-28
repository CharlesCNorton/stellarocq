(** Crude norms of the coil field along a torus, from the norms of its sources.

    From bounds r1, r2, r3 on the distance families of one source along a
    torus, yb on its inverse distance and cs on cos p and sin p, the
    cylindrical components of its field are bounded by products of those
    norms ([src_FR_nb], [src_FP_nb], [src_FZ_nb]), with the factors
    C1 = |d2| r3 + |d3| r2, C2 = |d3| r1 + |d1| r3, C3 = |d1| r2 + |d2| r1 of
    the weighted tangent. The components of the total field of the base
    sources and their images are bounded by the sums of those bounds
    ([tot_R_nb], [tot_P_nb], [tot_Z_nb]). No cancellation between the
    sources is used, so these bounds serve on the wide strips where a finer
    bound of the same families is read from their values on a grid. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon FourierPer KAMVec KAMFin
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTotal.
Local Open Scope R_scope.

Section Source.

Variables (sc : src) (Y : fser) (K : vf) (w r1 r2 r3 yb cs : R).
Hypothesis Hw : 0 <= w.
Hypothesis B1 : nbound w r1 (fr1 sc K).
Hypothesis B2 : nbound w r2 (fr2 sc K).
Hypothesis B3 : nbound w r3 (fr3 sc K).
Hypothesis BY : nbound w yb (fy sc Y K).
Hypothesis BC : nbound w cs cosf.
Hypothesis BS : nbound w cs sinf.

Definition cC1 : R := Rabs (sd2 sc) * r3 + Rabs (sd3 sc) * r2.
Definition cC2 : R := Rabs (sd3 sc) * r1 + Rabs (sd1 sc) * r3.
Definition cC3 : R := Rabs (sd1 sc) * r2 + Rabs (sd2 sc) * r1.
Definition cY3 : R := yb * (yb * yb).

Lemma nb_fc1 : nbound w cC1 (fc1 sc K).
Proof. unfold fc1, cC1. apply nbound_fsub; apply nbound_fscal; assumption. Qed.
Lemma nb_fc2 : nbound w cC2 (fc2 sc K).
Proof. unfold fc2, cC2. apply nbound_fsub; apply nbound_fscal; assumption. Qed.
Lemma nb_fc3 : nbound w cC3 (fc3 sc K).
Proof. unfold fc3, cC3. apply nbound_fsub; apply nbound_fscal; assumption. Qed.

Lemma nb_fh3 : nbound w cY3 (fh3 sc Y K).
Proof. unfold fh3, cY3. apply nbound_fmul; [exact Hw | exact BY | apply nbound_fmul; assumption]. Qed.

Lemma nb_fb1 : nbound w (cC1 * cY3) (fb1 sc Y K).
Proof. unfold fb1. apply nbound_fmul; [exact Hw | apply nb_fc1 | apply nb_fh3]. Qed.
Lemma nb_fb2 : nbound w (cC2 * cY3) (fb2 sc Y K).
Proof. unfold fb2. apply nbound_fmul; [exact Hw | apply nb_fc2 | apply nb_fh3]. Qed.
Lemma nb_fb3 : nbound w (cC3 * cY3) (fb3 sc Y K).
Proof. unfold fb3. apply nbound_fmul; [exact Hw | apply nb_fc3 | apply nb_fh3]. Qed.

Theorem src_FR_nb : nbound w ((cC1 + cC2) * cY3 * cs) (FR sc Y K).
Proof.
  unfold FR. apply (nbound_le _ (cC1 * cY3 * cs + cC2 * cY3 * cs)); [right; ring |].
  apply nbound_fadd; apply nbound_fmul; try assumption; [apply nb_fb1 | apply nb_fb2].
Qed.

Theorem src_FP_nb : nbound w ((cC1 + cC2) * cY3 * cs) (FP sc Y K).
Proof.
  unfold FP. apply (nbound_le _ (Rabs (-1) * (cC1 * cY3) * cs + cC2 * cY3 * cs)).
  { rewrite Rabs_left by lra. right; ring. }
  apply nbound_fadd; apply nbound_fmul; try assumption;
    [apply nbound_fscal, nb_fb1 | apply nb_fb2].
Qed.

Theorem src_FZ_nb : nbound w (cC3 * cY3) (FZ sc Y K).
Proof. unfold FZ. apply nb_fb3. Qed.

(** * The Jacobian of one source *)

Definition cY5 : R := cY3 * (yb * yb).

Lemma nb_fh5 : nbound w cY5 (fh5 sc Y K).
Proof. unfold fh5, cY5. apply nbound_fmul; [exact Hw | apply nb_fh3 | apply nbound_fmul; assumption]. Qed.

(** |d_j| h3 + 3 C_i r_k h5, and 3 C_i r_k h5 when the first term is absent. *)
Definition cJ (d C r : R) : R := Rabs d * cY3 + 3 * C * r * cY5.

Lemma nb_jterm (c r : fser) (C rr : R) :
  nbound w C c -> nbound w rr r -> nbound w (3 * C * rr * cY5) (fscal 3 (fmul (fmul c r) (fh5 sc Y K))).
Proof.
  intros Hc Hr. apply (nbound_le _ (Rabs 3 * (C * rr * cY5))); [rewrite Rabs_right by lra; right; ring |].
  apply nbound_fscal. apply nbound_fmul; [exact Hw | apply nbound_fmul; assumption | exact nb_fh5].
Qed.

Lemma nb_J11 : nbound w (cJ 0 cC1 r1) (fJ11 sc Y K).
Proof.
  unfold fJ11, cJ. rewrite Rabs_R0, Rmult_0_l, Rplus_0_l.
  apply (nbound_le _ (Rabs (-3) * (cC1 * r1 * cY5))); [rewrite Rabs_left by lra; right; ring |].
  apply nbound_fscal. apply nbound_fmul; [exact Hw | apply nbound_fmul; [exact Hw | apply nb_fc1 | exact B1] | exact nb_fh5].
Qed.

Lemma nb_J12 : nbound w (cJ (sd3 sc) cC1 r2) (fJ12 sc Y K).
Proof.
  unfold fJ12, cJ. apply nbound_fsub; [rewrite <- Rabs_Ropp; apply nbound_fscal, nb_fh3 | apply nb_jterm; [apply nb_fc1 | exact B2]].
Qed.

Lemma nb_J13 : nbound w (cJ (sd2 sc) cC1 r3) (fJ13 sc Y K).
Proof. unfold fJ13, cJ. apply nbound_fsub; [apply nbound_fscal, nb_fh3 | apply nb_jterm; [apply nb_fc1 | exact B3]]. Qed.

Lemma nb_J21 : nbound w (cJ (sd3 sc) cC2 r1) (fJ21 sc Y K).
Proof. unfold fJ21, cJ. apply nbound_fsub; [apply nbound_fscal, nb_fh3 | apply nb_jterm; [apply nb_fc2 | exact B1]]. Qed.

Lemma nb_J22 : nbound w (cJ 0 cC2 r2) (fJ22 sc Y K).
Proof.
  unfold fJ22, cJ. rewrite Rabs_R0, Rmult_0_l, Rplus_0_l.
  apply (nbound_le _ (Rabs (-3) * (cC2 * r2 * cY5))); [rewrite Rabs_left by lra; right; ring |].
  apply nbound_fscal. apply nbound_fmul; [exact Hw | apply nbound_fmul; [exact Hw | apply nb_fc2 | exact B2] | exact nb_fh5].
Qed.

Lemma nb_J23 : nbound w (cJ (sd1 sc) cC2 r3) (fJ23 sc Y K).
Proof.
  unfold fJ23, cJ. apply nbound_fsub; [rewrite <- Rabs_Ropp; apply nbound_fscal, nb_fh3 | apply nb_jterm; [apply nb_fc2 | exact B3]].
Qed.

Lemma nb_J31 : nbound w (cJ (sd2 sc) cC3 r1) (fJ31 sc Y K).
Proof.
  unfold fJ31, cJ. apply nbound_fsub; [rewrite <- Rabs_Ropp; apply nbound_fscal, nb_fh3 | apply nb_jterm; [apply nb_fc3 | exact B1]].
Qed.

Lemma nb_J32 : nbound w (cJ (sd1 sc) cC3 r2) (fJ32 sc Y K).
Proof. unfold fJ32, cJ. apply nbound_fsub; [apply nbound_fscal, nb_fh3 | apply nb_jterm; [apply nb_fc3 | exact B2]]. Qed.

Lemma nb_J33 : nbound w (cJ 0 cC3 r3) (fJ33 sc Y K).
Proof.
  unfold fJ33, cJ. rewrite Rabs_R0, Rmult_0_l, Rplus_0_l.
  apply (nbound_le _ (Rabs (-3) * (cC3 * r3 * cY5))); [rewrite Rabs_left by lra; right; ring |].
  apply nbound_fscal. apply nbound_fmul; [exact Hw | apply nbound_fmul; [exact Hw | apply nb_fc3 | exact B3] | exact nb_fh5].
Qed.

Definition cE1 : R := (cJ 0 cC1 r1 + cJ (sd3 sc) cC1 r2) * cs.
Definition cE2 : R := (cJ (sd3 sc) cC2 r1 + cJ 0 cC2 r2) * cs.
Definition cE3 : R := (cJ (sd2 sc) cC3 r1 + cJ (sd1 sc) cC3 r2) * cs.

Lemma nb_JeR1 : nbound w cE1 (fJeR1 sc Y K).
Proof.
  unfold fJeR1, cE1. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption; [apply nb_J11 | apply nb_J12].
Qed.
Lemma nb_JeR2 : nbound w cE2 (fJeR2 sc Y K).
Proof.
  unfold fJeR2, cE2. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption; [apply nb_J21 | apply nb_J22].
Qed.
Lemma nb_JeR3 : nbound w cE3 (fJeR3 sc Y K).
Proof.
  unfold fJeR3, cE3. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption; [apply nb_J31 | apply nb_J32].
Qed.

Definition cRR : R := (cE1 + cE2) * cs.
Definition cRZ : R := (cJ (sd2 sc) cC1 r3 + cJ (sd1 sc) cC2 r3) * cs.

Theorem src_FRR_nb : nbound w cRR (FR_R sc Y K).
Proof.
  unfold FR_R, cRR. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption; [apply nb_JeR1 | apply nb_JeR2].
Qed.
Theorem src_FRZ_nb : nbound w cRZ (FR_Z sc Y K).
Proof.
  unfold FR_Z, cRZ. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption; [apply nb_J13 | apply nb_J23].
Qed.
Theorem src_FPR_nb : nbound w cRR (FP_R sc Y K).
Proof.
  unfold FP_R, cRR. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption;
    [apply (nbound_le _ (Rabs (-1) * cE1)); [rewrite Rabs_left by lra; right; ring | apply nbound_fscal, nb_JeR1]
    | apply nb_JeR2].
Qed.
Theorem src_FPZ_nb : nbound w cRZ (FP_Z sc Y K).
Proof.
  unfold FP_Z, cRZ. rewrite Rmult_plus_distr_r.
  apply nbound_fadd; apply nbound_fmul; try assumption;
    [apply (nbound_le _ (Rabs (-1) * cJ (sd2 sc) cC1 r3)); [rewrite Rabs_left by lra; right; ring
                                                            | apply nbound_fscal, nb_J13]
    | apply nb_J23].
Qed.
Theorem src_FZR_nb : nbound w cE3 (FZ_R sc Y K).
Proof. unfold FZ_R. apply nb_JeR3. Qed.
Theorem src_FZZ_nb : nbound w (cJ 0 cC3 r3) (FZ_Z sc Y K).
Proof. unfold FZ_Z. apply nb_J33. Qed.

End Source.

(** * The total field *)

Section Total.

Variables (P : Z) (l : list (src * fser)) (K : vf) (w cs : R).
Variables (r1 r2 r3 yb : src * fser -> R).
Hypothesis Hw : 0 <= w.
Hypothesis BC : nbound w cs cosf.
Hypothesis BS : nbound w cs sinf.
Hypothesis Hsrc : List.Forall (fun sy =>
  nbound w (r1 sy) (fr1 (fst sy) K) /\ nbound w (r2 sy) (fr2 (fst sy) K) /\
  nbound w (r3 sy) (fr3 (fst sy) K) /\ nbound w (yb sy) (fy (fst sy) (snd sy) K)) l.

Definition sRP (sy : src * fser) : R :=
  (cC1 (fst sy) (r2 sy) (r3 sy) + cC2 (fst sy) (r1 sy) (r3 sy)) * cY3 (yb sy) * cs.
Definition sZ (sy : src * fser) : R := cC3 (fst sy) (r1 sy) (r2 sy) * cY3 (yb sy).

Lemma nbound_feq' (rho M : R) (u v : fser) : feq u v -> nbound rho M v -> nbound rho M u.
Proof. intros E H. apply (nbound_feq _ _ v); [apply feq_sym, E | exact H]. Qed.

Theorem tot_R_nb : nbound w (Rabs (IZR P) * ((1 + Rabs (-1)) * lsum sRP l)) (jR (tot P l K)).
Proof.
  apply (nbound_feq' _ _ _ _ (tot_R P K l)). apply tsum_nb.
  eapply Forall_impl; [| exact Hsrc]. intros sy [H1 [H2 [H3 H4]]]. unfold sfam, sRP.
  apply src_FR_nb; assumption.
Qed.

Theorem tot_P_nb : nbound w (Rabs (IZR P) * ((1 + Rabs 1) * lsum sRP l)) (jP (tot P l K)).
Proof.
  apply (nbound_feq' _ _ _ _ (tot_P P K l)). apply tsum_nb.
  eapply Forall_impl; [| exact Hsrc]. intros sy [H1 [H2 [H3 H4]]]. unfold sfam, sRP.
  apply src_FP_nb; assumption.
Qed.

Theorem tot_Z_nb : nbound w (Rabs (IZR P) * ((1 + Rabs 1) * lsum sZ l)) (jZ (tot P l K)).
Proof.
  apply (nbound_feq' _ _ _ _ (tot_Z P K l)). apply tsum_nb.
  eapply Forall_impl; [| exact Hsrc]. intros sy [H1 [H2 [H3 H4]]]. unfold sfam, sZ.
  apply src_FZ_nb; assumption.
Qed.

(** The derivatives of the total field. *)
Definition sRR (sy : src * fser) : R := cRR (fst sy) (r1 sy) (r2 sy) (r3 sy) (yb sy) cs.
Definition sRZ (sy : src * fser) : R := cRZ (fst sy) (r1 sy) (r2 sy) (r3 sy) (yb sy) cs.
Definition sZR (sy : src * fser) : R := cE3 (fst sy) (r1 sy) (r2 sy) (yb sy) cs.
Definition sZZ (sy : src * fser) : R := cJ (yb sy) 0 (cC3 (fst sy) (r1 sy) (r2 sy)) (r3 sy).

Ltac tot_d lem cmp sgn :=
  apply (nbound_feq' _ _ _ _ (cmp P K l)); apply tsum_nb;
  eapply Forall_impl; [| exact Hsrc]; intros sy [H1 [H2 [H3 H4]]]; unfold sfam;
  apply lem; assumption.

Theorem tot_RR_nb : nbound w (Rabs (IZR P) * ((1 + Rabs (-1)) * lsum sRR l)) (jR_R (tot P l K)).
Proof. tot_d src_FRR_nb tot_RR (-1). Qed.
Theorem tot_RZ_nb : nbound w (Rabs (IZR P) * ((1 + Rabs 1) * lsum sRZ l)) (jR_Z (tot P l K)).
Proof. tot_d src_FRZ_nb tot_RZ 1. Qed.
Theorem tot_PR_nb : nbound w (Rabs (IZR P) * ((1 + Rabs 1) * lsum sRR l)) (jP_R (tot P l K)).
Proof. tot_d src_FPR_nb tot_PR 1. Qed.
Theorem tot_PZ_nb : nbound w (Rabs (IZR P) * ((1 + Rabs (-1)) * lsum sRZ l)) (jP_Z (tot P l K)).
Proof. tot_d src_FPZ_nb tot_PZ (-1). Qed.
Theorem tot_ZR_nb : nbound w (Rabs (IZR P) * ((1 + Rabs 1) * lsum sZR l)) (jZ_R (tot P l K)).
Proof. tot_d src_FZR_nb tot_ZR 1. Qed.
Theorem tot_ZZ_nb : nbound w (Rabs (IZR P) * ((1 + Rabs (-1)) * lsum sZZ l)) (jZ_Z (tot P l K)).
Proof. tot_d src_FZZ_nb tot_ZZ (-1). Qed.

End Total.
