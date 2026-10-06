(** Differences of products.

    The change of a product is bounded by the changes of its factors:
    |u' v' - u v| <= |u' - u| |v'| + |u| |v' - v| ([fmul_diff]), and the same
    for a scalar family times a vector ([vsmul_diff]), the wedge
    ([wedge_diff]), the dot product ([vdot_diff]) and a matrix times a vector
    ([mapp_diff]). L and d_t of a difference are the differences of L and
    d_t ([vlc_sub_feq], [vdt_sub_feq]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon KAMVec KAMFin.
Local Open Scope R_scope.

Definition msub (A B : mf) : mf :=
  mkmf (fsub (mRR A) (mRR B)) (fsub (mRZ A) (mRZ B)) (fsub (mZR A) (mZR B)) (fsub (mZZ A) (mZZ B)).

Lemma fc_fadd' (u v : fser) (m n : Z) : fc (fadd u v) m n = fc u m n + fc v m n.
Proof. reflexivity. Qed.
Lemma fs_fadd' (u v : fser) (m n : Z) : fs (fadd u v) m n = fs u m n + fs v m n.
Proof. reflexivity. Qed.
Lemma fc_fscal' (c : R) (u : fser) (m n : Z) : fc (fscal c u) m n = c * fc u m n.
Proof. reflexivity. Qed.
Lemma fs_fscal' (c : R) (u : fser) (m n : Z) : fs (fscal c u) m n = c * fs u m n.
Proof. reflexivity. Qed.

(** Coefficients of sums and multiples, as sums and multiples of coefficients. *)
Ltac fnorm := repeat first [rewrite fc_fadd' | rewrite fs_fadd' | rewrite fc_fscal' | rewrite fs_fscal'].

Lemma nbound_add_diff (rho Mu Md : R) (u u' : fser) :
  nbound rho Mu u -> nbound rho Md (fsub u' u) -> nbound rho (Mu + Md) u'.
Proof.
  intros Hu Hd. apply (nbound_feq _ _ (fadd u (fsub u' u))).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply nbound_fadd; assumption.
Qed.

Lemma nbound_sub_diff (rho Mv Md : R) (v v' : fser) :
  nbound rho Mv v' -> nbound rho Md (fsub v' v) -> nbound rho (Mv + Md) v.
Proof.
  intros Hv Hd. apply (nbound_feq _ _ (fsub v' (fsub v' v))).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply nbound_fsub; assumption.
Qed.

Lemma nbound_fsub_sym (rho M : R) (u v : fser) : nbound rho M (fsub u v) -> nbound rho M (fsub v u).
Proof.
  intros H. apply (nbound_feq _ _ (fscal (-1) (fsub u v))).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply (nbound_le _ (Rabs (-1) * M)); [rewrite Rabs_left by lra; lra | apply nbound_fscal, H].
Qed.

Theorem fmul_diff (rho Mu Mv' Mdu Mdv : R) (u u' v v' : fser) :
  0 <= rho -> nbound rho Mu u -> nbound rho Mv' v' ->
  nbound rho Mdu (fsub u' u) -> nbound rho Mdv (fsub v' v) ->
  nbound rho (Mdu * Mv' + Mu * Mdv) (fsub (fmul u' v') (fmul u v)).
Proof.
  intros Hr Hu Hv' Hdu Hdv.
  assert (Hu' := nbound_add_diff rho Mu Mdu u u' Hu Hdu).
  assert (Hv := nbound_sub_diff rho Mv' Mdv v v' Hv' Hdv).
  apply (nbound_feq _ _ (fadd (fmul (fsub u' u) v') (fmul u (fsub v' v)))).
  2: { apply nbound_fadd; apply nbound_fmul; assumption. }
  intros m n.
  destruct (fmul_fadd_l rho Hr u' (fscal (-1) u) v' _ _ _ Hu' (nbound_fscal _ _ (-1) _ Hu) Hv' m n) as [A1 A2].
  destruct (fmul_fscal_l rho Hr (-1) u v' _ _ Hu Hv' m n) as [B1 B2].
  destruct (fmul_fadd_r rho Hr u v' (fscal (-1) v) _ _ _ Hu Hv' (nbound_fscal _ _ (-1) _ Hv) m n) as [C1 C2].
  destruct (fmul_fscal_r rho Hr (-1) u v _ _ Hu Hv m n) as [D1 D2].
  rewrite fc_fadd' in A1, C1. rewrite fs_fadd' in A2, C2.
  rewrite fc_fscal' in B1, D1. rewrite fs_fscal' in B2, D2.
  unfold fsub. fnorm.
  rewrite A1, A2, B1, B2, C1, C2, D1, D2. split; ring.
Qed.

(** * Vectors and matrices *)

Lemma vsmul_diff (rho Ms Mu' Mds Mdu : R) (s s' : fser) (u u' : vf) :
  0 <= rho -> nbound rho Ms s -> vbound rho Mu' u' ->
  nbound rho Mds (fsub s' s) -> vbound rho Mdu (vsub u' u) ->
  vbound rho (Mds * Mu' + Ms * Mdu) (vsub (vsmul s' u') (vsmul s u)).
Proof.
  intros Hr Hs [H1 H2] Hds [H3 H4]. split; apply fmul_diff; assumption.
Qed.

Lemma vbound_feq' (rho M : R) (u v : vf) :
  feq (vR u) (vR v) /\ feq (vZ u) (vZ v) -> vbound rho M u -> vbound rho M v.
Proof. intros [H1 H2] [B1 B2]. split; [apply (nbound_feq _ _ _ _ H1 B1) | apply (nbound_feq _ _ _ _ H2 B2)]. Qed.

Lemma feq_sym2 (u v : vf) :
  feq (vR u) (vR v) /\ feq (vZ u) (vZ v) -> feq (vR v) (vR u) /\ feq (vZ v) (vZ u).
Proof. intros [H1 H2]. split; apply feq_sym; assumption. Qed.

Lemma wedge_sub_feq (u u' v v' : vf) :
  feq (fsub (wedge u' v') (wedge u v))
      (fsub (fsub (fmul (vR u') (vZ v')) (fmul (vR u) (vZ v))) (fsub (fmul (vZ u') (vR v')) (fmul (vZ u) (vR v)))).
Proof. intros m n. unfold wedge, fsub. fnorm. split; ring. Qed.

Theorem wedge_diff (rho Mu Mv' Mdu Mdv : R) (u u' v v' : vf) :
  0 <= rho -> vbound rho Mu u -> vbound rho Mv' v' ->
  vbound rho Mdu (vsub u' u) -> vbound rho Mdv (vsub v' v) ->
  nbound rho (2 * (Mdu * Mv' + Mu * Mdv)) (fsub (wedge u' v') (wedge u v)).
Proof.
  intros Hr [U1 U2] [V1 V2] [DU1 DU2] [DV1 DV2].
  apply (nbound_feq _ _ _ _ (feq_sym _ _ (wedge_sub_feq u u' v v'))).
  apply (nbound_le _ ((Mdu * Mv' + Mu * Mdv) + (Mdu * Mv' + Mu * Mdv))); [lra |].
  apply nbound_fsub; apply fmul_diff; assumption.
Qed.

Lemma vdot_sub_feq (u u' v v' : vf) :
  feq (fsub (vdot u' v') (vdot u v))
      (fadd (fsub (fmul (vR u') (vR v')) (fmul (vR u) (vR v))) (fsub (fmul (vZ u') (vZ v')) (fmul (vZ u) (vZ v)))).
Proof. intros m n. unfold vdot, fsub. fnorm. split; ring. Qed.

Theorem vdot_diff (rho Mu Mv' Mdu Mdv : R) (u u' v v' : vf) :
  0 <= rho -> vbound rho Mu u -> vbound rho Mv' v' ->
  vbound rho Mdu (vsub u' u) -> vbound rho Mdv (vsub v' v) ->
  nbound rho (2 * (Mdu * Mv' + Mu * Mdv)) (fsub (vdot u' v') (vdot u v)).
Proof.
  intros Hr [U1 U2] [V1 V2] [DU1 DU2] [DV1 DV2].
  apply (nbound_feq _ _ _ _ (feq_sym _ _ (vdot_sub_feq u u' v v'))).
  apply (nbound_le _ ((Mdu * Mv' + Mu * Mdv) + (Mdu * Mv' + Mu * Mdv))); [lra |].
  apply nbound_fadd; apply fmul_diff; assumption.
Qed.

Lemma mapp_sub_feq (A A' : mf) (u u' : vf) :
  feq (vR (vsub (mapp A' u') (mapp A u)))
      (fadd (fsub (fmul (mRR A') (vR u')) (fmul (mRR A) (vR u))) (fsub (fmul (mRZ A') (vZ u')) (fmul (mRZ A) (vZ u)))) /\
  feq (vZ (vsub (mapp A' u') (mapp A u)))
      (fadd (fsub (fmul (mZR A') (vR u')) (fmul (mZR A) (vR u))) (fsub (fmul (mZZ A') (vZ u')) (fmul (mZZ A) (vZ u)))).
Proof.
  split; intros m n; cbn [vR vZ vsub mapp]; unfold fsub; fnorm; split; ring.
Qed.

Theorem mapp_diff (rho MA Mu' MdA Mdu : R) (A A' : mf) (u u' : vf) :
  0 <= rho -> mbound rho MA A -> vbound rho Mu' u' ->
  mbound rho MdA (msub A' A) -> vbound rho Mdu (vsub u' u) ->
  vbound rho (2 * (MdA * Mu' + MA * Mdu)) (vsub (mapp A' u') (mapp A u)).
Proof.
  intros Hr [A1 [A2 [A3 A4]]] [U1 U2] [D1 [D2 [D3 D4]]] [E1 E2].
  destruct (mapp_sub_feq A A' u u') as [F1 F2].
  split.
  - apply (nbound_feq _ _ _ _ (feq_sym _ _ F1)).
    apply (nbound_le _ ((MdA * Mu' + MA * Mdu) + (MdA * Mu' + MA * Mdu))); [lra |].
    apply nbound_fadd; apply fmul_diff; assumption.
  - apply (nbound_feq _ _ _ _ (feq_sym _ _ F2)).
    apply (nbound_le _ ((MdA * Mu' + MA * Mdu) + (MdA * Mu' + MA * Mdu))); [lra |].
    apply nbound_fadd; apply fmul_diff; assumption.
Qed.

Lemma vlc_sub_feq (om : R) (u u' : vf) :
  feq (vR (vsub (vlc om u') (vlc om u))) (vR (vlc om (vsub u' u))) /\
  feq (vZ (vsub (vlc om u') (vlc om u))) (vZ (vlc om (vsub u' u))).
Proof.
  split; intros m n; cbn [vR vZ vsub vlc]; unfold fsub, lc; fnorm; cbn [fc fs]; fnorm; split; ring.
Qed.

Lemma vdt_sub_feq (u u' : vf) :
  feq (vR (vsub (vdt u') (vdt u))) (vR (vdt (vsub u' u))) /\
  feq (vZ (vsub (vdt u') (vdt u))) (vZ (vdt (vsub u' u))).
Proof.
  split; intros m n; cbn [vR vZ vsub vdt]; unfold fsub, dt; fnorm; cbn [fc fs]; fnorm; split; ring.
Qed.

Lemma vsub_vsub_feq (u v w : vf) :
  feq (vR (vsub u w)) (vR (vadd (vsub u v) (vsub v w))) /\
  feq (vZ (vsub u w)) (vZ (vadd (vsub u v) (vsub v w))).
Proof.
  split; intros m n; cbn [vR vZ vsub vadd]; unfold fsub; fnorm; split; ring.
Qed.

Lemma fsub_fsub_feq (u v w : fser) : feq (fsub u w) (fadd (fsub u v) (fsub v w)).
Proof. intros m n. unfold fsub. fnorm. split; ring. Qed.
