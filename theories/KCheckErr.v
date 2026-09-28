(** The error of a torus of the coil field through a numerator free of
    inverses.

    For the field-line model of the coil field, the error of a torus K is
    E = L K - R (B_R, B_Z) / B_phi. Its numerators F_R = B_phi (L K)_R - R B_R
    and F_Z = B_phi (L K)_Z - R B_Z ([errF_R], [errF_Z]) involve no inverse,
    so wider strips bound them from the norms of the field alone, and
    E = U F with U the inverse of B_phi ([kerr_R_feq], [kerr_Z_feq]); the
    norm of the error is at most the norm of U times that of F
    ([kerr_bound]). At a point, F is B_phi (om d_t K + d_p K) - R B of the coil
    field at the point of the torus ([feval_errF_R], [feval_errF_Z]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon FourierPer KAMFrame KAMVec KAMFin KAMPer KAMStep
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldLine.
Local Open Scope R_scope.

Section Err.

Variables (P : Z) (l : list (src * fser)) (Ub : fser) (om rho : R) (K : vf).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.
Hypothesis HU : inv_ok rho (jP (lj P l K)) Ub.
Hypothesis CK : vcanon K.
Hypothesis Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Hypothesis CU : is_canon Ub.

Definition errF_R : fser := fsub (fmul (jP (lj P l K)) (lc om (vR K))) (fmul (vR K) (jR (lj P l K))).
Definition errF_Z : fser := fsub (fmul (jP (lj P l K)) (lc om (vZ K))) (fmul (vR K) (jZ (lj P l K))).

Let J := lj P l K.

Lemma FJ : jfin rho J. Proof. exact (J_fin P l rho K Hr FK Hl). Qed.
Lemma FU : fin rho (lU P l Ub K). Proof. exact (U_fin P l Ub rho K Hr HU). Qed.

Lemma f0 (u : fser) : fin rho u -> fin 0 u. Proof. apply fin_mono. lra. Qed.

Lemma FR0 : fin 0 (vR K). Proof. apply f0, (proj1 FK). Qed.
Lemma FZ0 : fin 0 (vZ K). Proof. apply f0, (proj2 FK). Qed.
Lemma FLR : fin 0 (lc om (vR K)).
Proof. replace 0 with (rho - rho) by ring. apply fin_lc; [exact Hr | exact (proj1 FK)]. Qed.
Lemma FLZ : fin 0 (lc om (vZ K)).
Proof. replace 0 with (rho - rho) by ring. apply fin_lc; [exact Hr | exact (proj2 FK)]. Qed.

Lemma FJR : fin 0 (jR J). Proof. apply f0. destruct FJ as [A _]. exact A. Qed.
Lemma FJP : fin 0 (jP J). Proof. apply f0. destruct FJ as [_ [A _]]. exact A. Qed.
Lemma FJZ : fin 0 (jZ J). Proof. apply f0. destruct FJ as [_ [_ [A _]]]. exact A. Qed.

(** The values of the numerators at a point. *)
Theorem feval_errF_R (t p : R) :
  feval errF_R t p = feval (jP J) t p * feval (lc om (vR K)) t p - feval (vR K) t p * feval (jR J) t p.
Proof.
  unfold errF_R. fold J.
  rewrite (feval_fsub' t p _ _ (fin_fmul 0 _ _ (Rle_refl 0) FJP FLR) (fin_fmul 0 _ _ (Rle_refl 0) FR0 FJR)).
  rewrite (feval_fmul' t p _ _ FJP FLR), (feval_fmul' t p _ _ FR0 FJR). reflexivity.
Qed.

Theorem feval_errF_Z (t p : R) :
  feval errF_Z t p = feval (jP J) t p * feval (lc om (vZ K)) t p - feval (vR K) t p * feval (jZ J) t p.
Proof.
  unfold errF_Z. fold J.
  rewrite (feval_fsub' t p _ _ (fin_fmul 0 _ _ (Rle_refl 0) FJP FLZ) (fin_fmul 0 _ _ (Rle_refl 0) FR0 FJZ)).
  rewrite (feval_fmul' t p _ _ FJP FLZ), (feval_fmul' t p _ _ FR0 FJZ). reflexivity.
Qed.

(** * The error as U times the numerator *)

Lemma CJ : jcanon J. Proof. exact (proj1 (lj_canon P l Ub K HP CK Cl CU)). Qed.
Lemma CUK : is_canon (lU P l Ub K). Proof. exact (proj2 (lj_canon P l Ub K HP CK Cl CU)). Qed.

Lemma FU0 : fin 0 (lU P l Ub K). Proof. apply f0, FU. Qed.
Lemma FW : fin 0 (fmul (vR K) (lU P l Ub K)). Proof. exact (fin_fmul 0 _ _ (Rle_refl 0) FR0 FU0). Qed.

Lemma FER : fin 0 errF_R.
Proof.
  unfold errF_R. fold J.
  apply fin_fsub; [exact (fin_fmul 0 _ _ (Rle_refl 0) FJP FLR) | exact (fin_fmul 0 _ _ (Rle_refl 0) FR0 FJR)].
Qed.

Lemma FEZ : fin 0 errF_Z.
Proof.
  unfold errF_Z. fold J.
  apply fin_fsub; [exact (fin_fmul 0 _ _ (Rle_refl 0) FJP FLZ) | exact (fin_fmul 0 _ _ (Rle_refl 0) FR0 FJZ)].
Qed.

Theorem kerr_R_feq : feq (vR (kerr (lmodel P l Ub) om K)) (fmul (lU P l Ub K) errF_R).
Proof.
  change (vR (kerr (lmodel P l Ub) om K))
    with (fsub (lc om (vR K)) (fmul (fmul (vR K) (lU P l Ub K)) (jR (lj P l K)))).
  fold J.
  assert (FWJ : fin 0 (fmul (fmul (vR K) (lU P l Ub K)) (jR J))) by exact (fin_fmul 0 _ _ (Rle_refl 0) FW FJR).
  assert (F1 : fin 0 (fsub (lc om (vR K)) (fmul (fmul (vR K) (lU P l Ub K)) (jR J))))
    by exact (fin_fsub 0 _ _ FLR FWJ).
  assert (F2 : fin 0 (fmul (lU P l Ub K) errF_R)) by exact (fin_fmul 0 _ _ (Rle_refl 0) FU0 FER).
  destruct CJ as [CR [CP [CZ _]]].
  assert (C1 : is_canon (fsub (lc om (vR K)) (fmul (fmul (vR K) (lU P l Ub K)) (jR J)))).
  { apply fsub_canon; [apply lc_canon, (proj1 CK) |].
    apply fmul_canon; [apply fmul_canon; [exact (proj1 CK) | exact CUK] | exact CR]. }
  assert (C2 : is_canon (fmul (lU P l Ub K) errF_R)).
  { apply fmul_canon; [exact CUK |]. unfold errF_R. fold J. apply fsub_canon; apply fmul_canon.
    - exact CP.
    - apply lc_canon, (proj1 CK).
    - exact (proj1 CK).
    - exact CR. }
  destruct F1 as [M1 B1]. destruct F2 as [M2 B2].
  apply (canon_feq _ _ M1 M2 C1 C2 B1 B2). intros t p.
  rewrite (feval_fsub' t p _ _ FLR FWJ), (feval_fmul' t p _ _ FW FJR), (feval_fmul' t p _ _ FR0 FU0).
  rewrite (feval_fmul' t p _ _ FU0 FER), feval_errF_R.
  pose proof (U_inv P l Ub rho K Hr HU t p) as Hinv. fold J in Hinv.
  set (U := feval (lU P l Ub K) t p) in *. set (BP := feval (jP J) t p) in *.
  replace (U * (BP * feval (lc om (vR K)) t p - feval (vR K) t p * feval (jR J) t p))
    with (BP * U * feval (lc om (vR K)) t p - feval (vR K) t p * U * feval (jR J) t p) by ring.
  rewrite Hinv. ring.
Qed.

Theorem kerr_Z_feq : feq (vZ (kerr (lmodel P l Ub) om K)) (fmul (lU P l Ub K) errF_Z).
Proof.
  change (vZ (kerr (lmodel P l Ub) om K))
    with (fsub (lc om (vZ K)) (fmul (fmul (vR K) (lU P l Ub K)) (jZ (lj P l K)))).
  fold J.
  assert (FWJ : fin 0 (fmul (fmul (vR K) (lU P l Ub K)) (jZ J))) by exact (fin_fmul 0 _ _ (Rle_refl 0) FW FJZ).
  assert (F1 : fin 0 (fsub (lc om (vZ K)) (fmul (fmul (vR K) (lU P l Ub K)) (jZ J))))
    by exact (fin_fsub 0 _ _ FLZ FWJ).
  assert (F2 : fin 0 (fmul (lU P l Ub K) errF_Z)) by exact (fin_fmul 0 _ _ (Rle_refl 0) FU0 FEZ).
  destruct CJ as [CR [CP [CZ _]]].
  assert (C1 : is_canon (fsub (lc om (vZ K)) (fmul (fmul (vR K) (lU P l Ub K)) (jZ J)))).
  { apply fsub_canon; [apply lc_canon, (proj2 CK) |].
    apply fmul_canon; [apply fmul_canon; [exact (proj1 CK) | exact CUK] | exact CZ]. }
  assert (C2 : is_canon (fmul (lU P l Ub K) errF_Z)).
  { apply fmul_canon; [exact CUK |]. unfold errF_Z. fold J. apply fsub_canon; apply fmul_canon.
    - exact CP.
    - apply lc_canon, (proj2 CK).
    - exact (proj1 CK).
    - exact CZ. }
  destruct F1 as [M1 B1]. destruct F2 as [M2 B2].
  apply (canon_feq _ _ M1 M2 C1 C2 B1 B2). intros t p.
  rewrite (feval_fsub' t p _ _ FLZ FWJ), (feval_fmul' t p _ _ FW FJZ), (feval_fmul' t p _ _ FR0 FU0).
  rewrite (feval_fmul' t p _ _ FU0 FEZ), feval_errF_Z.
  pose proof (U_inv P l Ub rho K Hr HU t p) as Hinv. fold J in Hinv.
  set (U := feval (lU P l Ub K) t p) in *. set (BP := feval (jP J) t p) in *.
  replace (U * (BP * feval (lc om (vZ K)) t p - feval (vR K) t p * feval (jZ J) t p))
    with (BP * U * feval (lc om (vZ K)) t p - feval (vR K) t p * U * feval (jZ J) t p) by ring.
  rewrite Hinv. ring.
Qed.

(** The norm of the error from the norms of U and of the numerators. *)
Theorem kerr_bound (w MU MR MZ : R) :
  0 <= w -> nbound w MU (lU P l Ub K) -> nbound w MR errF_R -> nbound w MZ errF_Z ->
  vbound w (MU * Rmax MR MZ) (kerr (lmodel P l Ub) om K).
Proof.
  intros Hw BU BR BZ.
  assert (HMU : 0 <= MU) by exact (nbound_nonneg _ _ _ BU).
  split.
  - apply (nbound_feq _ _ _ _ (feq_sym _ _ kerr_R_feq)).
    apply (nbound_le _ (MU * MR)); [apply Rmult_le_compat_l; [exact HMU | apply Rmax_l] |].
    apply nbound_fmul; assumption.
  - apply (nbound_feq _ _ _ _ (feq_sym _ _ kerr_Z_feq)).
    apply (nbound_le _ (MU * MZ)); [apply Rmult_le_compat_l; [exact HMU | apply Rmax_r] |].
    apply nbound_fmul; assumption.
Qed.

End Err.
