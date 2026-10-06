(** Vector and matrix families on the torus, and the calculus of their functions.

    A torus in the (R, Z) plane over the two angles, its error and the frame
    of the Newton step are pairs of coefficient families ([vf]); the
    derivative of the field along a torus is a two by two matrix of them
    ([mf]). Norms are taken componentwise ([vbound], [mbound]); a scalar family
    times a vector, the wedge a ^ b = a_R b_Z - a_Z b_R, the dot product and a
    matrix times a vector cost the product of the norms, and L = om d_t + d_p
    costs (|om| + 1) / (e delta) of the strip ([nbound_lc]). At a point, the
    function of L u is om d_t + d_p of the function of u ([feval_lc]), the
    derivatives obey the product rule ([feval_dt_fmul], [feval_lc_fmul]), a
    family whose function is constant has L of it zero ([feval_lc_const]),
    and L of L^-1 u is u less its average ([feval_lc_linv]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon.
Local Open Scope R_scope.

Record vf := mkvf { vR : fser ; vZ : fser }.
Record mf := mkmf { mRR : fser ; mRZ : fser ; mZR : fser ; mZZ : fser }.

Definition vadd (u v : vf) : vf := mkvf (fadd (vR u) (vR v)) (fadd (vZ u) (vZ v)).
Definition vsub (u v : vf) : vf := mkvf (fsub (vR u) (vR v)) (fsub (vZ u) (vZ v)).
Definition vscal (c : R) (u : vf) : vf := mkvf (fscal c (vR u)) (fscal c (vZ u)).
Definition vsmul (s : fser) (u : vf) : vf := mkvf (fmul s (vR u)) (fmul s (vZ u)).
Definition vdt (u : vf) : vf := mkvf (dt (vR u)) (dt (vZ u)).
Definition vlc (om : R) (u : vf) : vf := mkvf (lc om (vR u)) (lc om (vZ u)).
Definition vJ (u : vf) : vf := mkvf (fscal (-1) (vZ u)) (vR u).
Definition vcan (u : vf) : vf := mkvf (canon (vR u)) (canon (vZ u)).
Definition wedge (u v : vf) : fser := fsub (fmul (vR u) (vZ v)) (fmul (vZ u) (vR v)).
Definition vdot (u v : vf) : fser := fadd (fmul (vR u) (vR v)) (fmul (vZ u) (vZ v)).
Definition mapp (A : mf) (u : vf) : vf :=
  mkvf (fadd (fmul (mRR A) (vR u)) (fmul (mRZ A) (vZ u)))
       (fadd (fmul (mZR A) (vR u)) (fmul (mZZ A) (vZ u))).
Definition mtr (A : mf) : fser := fadd (mRR A) (mZZ A).

(** The constant c as a family. *)
Definition fconst (c : R) : fser := fsingle 0 0 c 0.

(** * Norms *)

Definition vbound (rho M : R) (u : vf) : Prop := nbound rho M (vR u) /\ nbound rho M (vZ u).
Definition mbound (rho M : R) (A : mf) : Prop :=
  nbound rho M (mRR A) /\ nbound rho M (mRZ A) /\ nbound rho M (mZR A) /\ nbound rho M (mZZ A).

Lemma vbound_mono (rho rho' M : R) (u : vf) : rho' <= rho -> vbound rho M u -> vbound rho' M u.
Proof. intros H [H1 H2]. split; apply (nbound_mono rho); assumption. Qed.

Lemma mbound_mono (rho rho' M : R) (A : mf) : rho' <= rho -> mbound rho M A -> mbound rho' M A.
Proof.
  intros H [H1 [H2 [H3 H4]]]. repeat split; apply (nbound_mono rho); assumption.
Qed.

Lemma vbound_le (rho M M' : R) (u : vf) : M <= M' -> vbound rho M u -> vbound rho M' u.
Proof. intros H [H1 H2]. split; apply (nbound_le _ M); assumption. Qed.

Lemma mbound_le (rho M M' : R) (A : mf) : M <= M' -> mbound rho M A -> mbound rho M' A.
Proof. intros H [H1 [H2 [H3 H4]]]. repeat split; apply (nbound_le _ M); assumption. Qed.

Lemma vbound_nonneg (rho M : R) (u : vf) : vbound rho M u -> 0 <= M.
Proof. intros [H _]. apply (nbound_nonneg _ _ _ H). Qed.

Lemma mbound_nonneg (rho M : R) (A : mf) : mbound rho M A -> 0 <= M.
Proof. intros [H _]. apply (nbound_nonneg _ _ _ H). Qed.

Lemma vbound_vadd (rho Mu Mv : R) (u v : vf) :
  vbound rho Mu u -> vbound rho Mv v -> vbound rho (Mu + Mv) (vadd u v).
Proof. intros [H1 H2] [H3 H4]. split; apply nbound_fadd; assumption. Qed.

Lemma vbound_vsub (rho Mu Mv : R) (u v : vf) :
  vbound rho Mu u -> vbound rho Mv v -> vbound rho (Mu + Mv) (vsub u v).
Proof. intros [H1 H2] [H3 H4]. split; apply nbound_fsub; assumption. Qed.

Lemma vbound_vscal (rho M c : R) (u : vf) : vbound rho M u -> vbound rho (Rabs c * M) (vscal c u).
Proof. intros [H1 H2]. split; apply nbound_fscal; assumption. Qed.

Lemma vbound_vsmul (rho Ms Mu : R) (s : fser) (u : vf) :
  0 <= rho -> nbound rho Ms s -> vbound rho Mu u -> vbound rho (Ms * Mu) (vsmul s u).
Proof. intros Hr Hs [H1 H2]. split; apply nbound_fmul; assumption. Qed.

Lemma vbound_vdt (rho d M : R) (u : vf) :
  0 < d -> vbound rho M u -> vbound (rho - d) (/ (exp 1 * d) * M) (vdt u).
Proof. intros Hd [H1 H2]. split; apply nbound_dt; assumption. Qed.

Lemma vbound_vJ (rho M : R) (u : vf) : vbound rho M u -> vbound rho M (vJ u).
Proof.
  intros [H1 H2]. split; [| exact H1]. simpl.
  apply (nbound_le _ (Rabs (-1) * M)); [rewrite Rabs_left by lra; lra | apply nbound_fscal, H2].
Qed.

Lemma vbound_vcan (rho M : R) (u : vf) : vbound rho M u -> vbound rho M (vcan u).
Proof. intros [H1 H2]. split; apply nbound_canon; assumption. Qed.

Lemma nbound_wedge (rho Mu Mv : R) (u v : vf) :
  0 <= rho -> vbound rho Mu u -> vbound rho Mv v -> nbound rho (2 * (Mu * Mv)) (wedge u v).
Proof.
  intros Hr [H1 H2] [H3 H4]. unfold wedge.
  apply (nbound_le _ (Mu * Mv + Mu * Mv)); [lra |].
  apply nbound_fsub; apply nbound_fmul; assumption.
Qed.

Lemma nbound_vdot (rho Mu Mv : R) (u v : vf) :
  0 <= rho -> vbound rho Mu u -> vbound rho Mv v -> nbound rho (2 * (Mu * Mv)) (vdot u v).
Proof.
  intros Hr [H1 H2] [H3 H4]. unfold vdot.
  apply (nbound_le _ (Mu * Mv + Mu * Mv)); [lra |].
  apply nbound_fadd; apply nbound_fmul; assumption.
Qed.

Lemma vbound_mapp (rho MA Mu : R) (A : mf) (u : vf) :
  0 <= rho -> mbound rho MA A -> vbound rho Mu u -> vbound rho (2 * (MA * Mu)) (mapp A u).
Proof.
  intros Hr [H1 [H2 [H3 H4]]] [H5 H6].
  split; simpl; (apply (nbound_le _ (MA * Mu + MA * Mu)); [lra |]);
    apply nbound_fadd; apply nbound_fmul; assumption.
Qed.

Lemma nbound_mtr (rho MA : R) (A : mf) : mbound rho MA A -> nbound rho (2 * MA) (mtr A).
Proof.
  intros [H1 [_ [_ H4]]]. unfold mtr.
  apply (nbound_le _ (MA + MA)); [lra | apply nbound_fadd; assumption].
Qed.

Lemma nbound_fconst (rho c : R) : nbound rho (Rabs c) (fconst c).
Proof.
  unfold fconst. pose proof (nbound_fsingle rho 0 0 c 0) as H.
  apply (nbound_le _ ((Rabs c + Rabs 0) * wt rho 0 0)); [| exact H].
  unfold wt, msize. rewrite !Rabs_R0. replace (rho * (0 + kappa * 0)) with 0 by ring.
  rewrite exp_0. lra.
Qed.

(** A single coefficient is at most the norm. *)
Lemma coef_le (rho M : R) (u : fser) (m n : Z) : 0 <= rho -> nbound rho M u -> Rabs (fc u m n) <= M.
Proof. intros Hr H. apply (tbound_fc rho M u Hr H). Qed.

(** * The operator L *)

Lemma lc_feq (om : R) (u : fser) : feq (lc om u) (fadd (fscal om (dt u)) (dp u)).
Proof. intros m n. unfold lc, divisor, fadd, fscal, dt, dp. simpl. split; ring. Qed.

Theorem nbound_lc (om rho d M : R) (u : fser) :
  0 < d -> nbound rho M u -> nbound (rho - d) ((Rabs om + / kappa) * / (exp 1 * d) * M) (lc om u).
Proof.
  intros Hd H. apply (nbound_feq _ _ _ _ (feq_sym _ _ (lc_feq om u))).
  apply (nbound_le _ (Rabs om * (/ (exp 1 * d) * M) + / kappa * (/ (exp 1 * d) * M)));
    [right; ring |].
  apply nbound_fadd; [apply nbound_fscal, nbound_dt | apply nbound_dp]; assumption.
Qed.

Lemma vbound_vlc (om rho d M : R) (u : vf) :
  0 < d -> vbound rho M u -> vbound (rho - d) ((Rabs om + / kappa) * / (exp 1 * d) * M) (vlc om u).
Proof. intros Hd [H1 H2]. split; apply nbound_lc; assumption. Qed.

Lemma dt_lc_feq (om : R) (u : fser) : feq (dt (lc om u)) (lc om (dt u)).
Proof. intros m n. unfold lc, dt. simpl. split; ring. Qed.

(** * Canonicity and parity *)

Definition vcanon (u : vf) : Prop := is_canon (vR u) /\ is_canon (vZ u).
Definition mcanon (A : mf) : Prop :=
  is_canon (mRR A) /\ is_canon (mRZ A) /\ is_canon (mZR A) /\ is_canon (mZZ A).

(** A stellarator-symmetric torus has an even R and an odd Z; its tangent and
    its error are the reverse. *)
Definition vsym (u : vf) : Prop := is_even (vR u) /\ is_odd (vZ u).
Definition vasym (u : vf) : Prop := is_odd (vR u) /\ is_even (vZ u).
Definition mpar (A : mf) : Prop :=
  is_odd (mRR A) /\ is_even (mRZ A) /\ is_even (mZR A) /\ is_odd (mZZ A).

Lemma fconst_canon (c : R) : is_canon (fconst c).
Proof.
  split; intros k l; unfold fconst, fsingle; simpl; rewrite at2_00_opp; [reflexivity |].
  unfold at2. destruct (_ && _)%bool; ring.
Qed.

Lemma fconst_even (c : R) : is_even (fconst c).
Proof. intros m n. unfold fconst, fsingle, at2. simpl. destruct (_ && _)%bool; reflexivity. Qed.

Lemma vcanon_vadd (u v : vf) : vcanon u -> vcanon v -> vcanon (vadd u v).
Proof. intros [H1 H2] [H3 H4]. split; apply fadd_canon; assumption. Qed.

Lemma vcanon_vsub (u v : vf) : vcanon u -> vcanon v -> vcanon (vsub u v).
Proof. intros [H1 H2] [H3 H4]. split; apply fsub_canon; assumption. Qed.

Lemma vcanon_vscal (c : R) (u : vf) : vcanon u -> vcanon (vscal c u).
Proof. intros [H1 H2]. split; apply fscal_canon; assumption. Qed.

Lemma vcanon_vsmul (s : fser) (u : vf) : is_canon s -> vcanon u -> vcanon (vsmul s u).
Proof. intros Hs [H1 H2]. split; apply fmul_canon; assumption. Qed.

Lemma vcanon_vdt (u : vf) : vcanon u -> vcanon (vdt u).
Proof. intros [H1 H2]. split; apply dt_canon; assumption. Qed.

Lemma vcanon_vlc (om : R) (u : vf) : vcanon u -> vcanon (vlc om u).
Proof. intros [H1 H2]. split; apply lc_canon; assumption. Qed.

Lemma vcanon_vJ (u : vf) : vcanon u -> vcanon (vJ u).
Proof. intros [H1 H2]. split; [apply fscal_canon, H2 | exact H1]. Qed.

Lemma vcanon_vcan (u : vf) : vcanon (vcan u).
Proof. split; apply canon_is_canon. Qed.

Lemma wedge_canon (u v : vf) : vcanon u -> vcanon v -> is_canon (wedge u v).
Proof. intros [H1 H2] [H3 H4]. apply fsub_canon; apply fmul_canon; assumption. Qed.

Lemma vdot_canon (u v : vf) : vcanon u -> vcanon v -> is_canon (vdot u v).
Proof. intros [H1 H2] [H3 H4]. apply fadd_canon; apply fmul_canon; assumption. Qed.

Lemma mapp_canon (A : mf) (u : vf) : mcanon A -> vcanon u -> vcanon (mapp A u).
Proof.
  intros [H1 [H2 [H3 H4]]] [H5 H6].
  split; apply fadd_canon; apply fmul_canon; assumption.
Qed.

Lemma mtr_canon (A : mf) : mcanon A -> is_canon (mtr A).
Proof. intros [H1 [_ [_ H4]]]. apply fadd_canon; assumption. Qed.

Lemma vsym_vdt (u : vf) : vsym u -> vasym (vdt u).
Proof. intros [H1 H2]. split; [apply dt_even, H1 | apply dt_odd, H2]. Qed.

Lemma vasym_vdt (u : vf) : vasym u -> vsym (vdt u).
Proof. intros [H1 H2]. split; [apply dt_odd, H1 | apply dt_even, H2]. Qed.

Lemma vsym_vlc (om : R) (u : vf) : vsym u -> vasym (vlc om u).
Proof. intros [H1 H2]. split; [apply lc_even, H1 | apply lc_odd, H2]. Qed.

Lemma vasym_vlc (om : R) (u : vf) : vasym u -> vsym (vlc om u).
Proof. intros [H1 H2]. split; [apply lc_odd, H1 | apply lc_even, H2]. Qed.

Lemma vasym_vJ (u : vf) : vasym u -> vsym (vJ u).
Proof. intros [H1 H2]. split; [apply fscal_even, H2 | exact H1]. Qed.

Lemma vsym_vadd (u v : vf) : vsym u -> vsym v -> vsym (vadd u v).
Proof. intros [H1 H2] [H3 H4]. split; [apply fadd_even | apply fadd_odd]; assumption. Qed.

Lemma vasym_vadd (u v : vf) : vasym u -> vasym v -> vasym (vadd u v).
Proof. intros [H1 H2] [H3 H4]. split; [apply fadd_odd | apply fadd_even]; assumption. Qed.

Lemma vasym_vsub (u v : vf) : vasym u -> vasym v -> vasym (vsub u v).
Proof. intros [H1 H2] [H3 H4]. split; [apply fsub_odd | apply fsub_even]; assumption. Qed.

Lemma vasym_vscal (c : R) (u : vf) : vasym u -> vasym (vscal c u).
Proof. intros [H1 H2]. split; [apply fscal_odd | apply fscal_even]; assumption. Qed.

Lemma vsym_vsmul_even (s : fser) (u : vf) : is_even s -> vsym u -> vsym (vsmul s u).
Proof. intros Hs [H1 H2]. split; [apply fmul_even_even | apply fmul_even_odd]; assumption. Qed.

Lemma vsym_vsmul_odd (s : fser) (u : vf) : is_odd s -> vasym u -> vsym (vsmul s u).
Proof. intros Hs [H1 H2]. split; [apply fmul_odd_odd | apply fmul_odd_even]; assumption. Qed.

Lemma vasym_vsmul_even (s : fser) (u : vf) : is_even s -> vasym u -> vasym (vsmul s u).
Proof. intros Hs [H1 H2]. split; [apply fmul_even_odd | apply fmul_even_even]; assumption. Qed.

Lemma vasym_vsmul_odd (s : fser) (u : vf) : is_odd s -> vsym u -> vasym (vsmul s u).
Proof. intros Hs [H1 H2]. split; [apply fmul_odd_even | apply fmul_odd_odd]; assumption. Qed.

Lemma wedge_asym_sym (u v : vf) : vasym u -> vsym v -> is_even (wedge u v).
Proof.
  intros [H1 H2] [H3 H4]. apply fsub_even; [apply fmul_odd_odd | apply fmul_even_even]; assumption.
Qed.

Lemma wedge_asym_asym (u v : vf) : vasym u -> vasym v -> is_odd (wedge u v).
Proof.
  intros [H1 H2] [H3 H4]. apply fsub_odd; [apply fmul_odd_even | apply fmul_even_odd]; assumption.
Qed.

Lemma wedge_sym_sym (u v : vf) : vsym u -> vsym v -> is_odd (wedge u v).
Proof.
  intros [H1 H2] [H3 H4]. apply fsub_odd; [apply fmul_even_odd | apply fmul_odd_even]; assumption.
Qed.

Lemma vdot_sym_asym (u v : vf) : vsym u -> vasym v -> is_odd (vdot u v).
Proof.
  intros [H1 H2] [H3 H4]. apply fadd_odd; [apply fmul_even_odd | apply fmul_odd_even]; assumption.
Qed.

Lemma vdot_asym_asym (u v : vf) : vasym u -> vasym v -> is_even (vdot u v).
Proof.
  intros [H1 H2] [H3 H4]. apply fadd_even; [apply fmul_odd_odd | apply fmul_even_even]; assumption.
Qed.

Lemma mapp_sym (A : mf) (u : vf) : mpar A -> vsym u -> vasym (mapp A u).
Proof.
  intros [H1 [H2 [H3 H4]]] [H5 H6]. split; simpl.
  - apply fadd_odd; [apply fmul_odd_even | apply fmul_even_odd]; assumption.
  - apply fadd_even; [apply fmul_even_even | apply fmul_odd_odd]; assumption.
Qed.

Lemma mapp_asym (A : mf) (u : vf) : mpar A -> vasym u -> vsym (mapp A u).
Proof.
  intros [H1 [H2 [H3 H4]]] [H5 H6]. split; simpl.
  - apply fadd_even; [apply fmul_odd_odd | apply fmul_even_even]; assumption.
  - apply fadd_odd; [apply fmul_even_odd | apply fmul_odd_even]; assumption.
Qed.

Lemma mtr_odd (A : mf) : mpar A -> is_odd (mtr A).
Proof. intros [H1 [_ [_ H4]]]. apply fadd_odd; assumption. Qed.

Lemma canon_even (u : fser) : is_even u -> is_even (canon u).
Proof. intros H m n. unfold canon, scan. simpl. rewrite !H. ring. Qed.

Lemma canon_odd (u : fser) : is_odd u -> is_odd (canon u).
Proof. intros H m n. unfold canon, ccan. simpl. rewrite !H. ring. Qed.

Lemma vasym_vcan (u : vf) : vasym u -> vasym (vcan u).
Proof. intros [H1 H2]. split; [apply canon_odd | apply canon_even]; assumption. Qed.

(** * The functions of the families at a point *)

Lemma feval_fconst (c t p : R) : feval (fconst c) t p = c.
Proof.
  unfold fconst. rewrite feval_fsingle. unfold mode.
  replace (0 * t + 0 * p) with 0 by ring. rewrite cos_0, sin_0. ring.
Qed.

Lemma fc_fmul_fconst (u : fser) (c : R) (m n : Z) : fc (fmul u (fconst c)) m n = c * fc u m n.
Proof.
  unfold fmul, fconst, fsingle. cbn [fc fs].
  rewrite !conv_p_unit, !conv_m_unit. field.
Qed.

Lemma nbound0 (rho M : R) (u : fser) : 0 <= rho -> nbound rho M u -> nbound 0 M u.
Proof. intros Hr H. apply (nbound_mono rho); [exact Hr | exact H]. Qed.

Theorem feval_lc (om rho M : R) (u : fser) (t p : R) :
  0 < rho -> nbound rho M u ->
  feval (lc om u) t p = om * feval (dt u) t p + feval (dp u) t p.
Proof.
  intros Hr H.
  assert (Hdt : nbound 0 (/ (exp 1 * rho) * M) (dt u)).
  { replace 0 with (rho - rho) by ring. apply nbound_dt; assumption. }
  assert (Hdp : nbound 0 (/ kappa * (/ (exp 1 * rho) * M)) (dp u)).
  { replace 0 with (rho - rho) by ring. apply nbound_dp; assumption. }
  rewrite (feval_feq _ _ t p (lc_feq om u)).
  rewrite (feval_fadd _ _ (Rabs om * (/ (exp 1 * rho) * M)) (/ kappa * (/ (exp 1 * rho) * M)) t p).
  - rewrite (feval_fscal om (dt u) (/ (exp 1 * rho) * M) t p Hdt). reflexivity.
  - apply nbound_fscal, Hdt.
  - exact Hdp.
Qed.

Theorem feval_dt_fmul (rho Mu Mv : R) (u v : fser) (t p : R) :
  0 < rho -> nbound rho Mu u -> nbound rho Mv v ->
  feval (dt (fmul u v)) t p = feval (dt u) t p * feval v t p + feval u t p * feval (dt v) t p.
Proof.
  intros Hr Hu Hv.
  assert (Huv := nbound_fmul rho Mu Mv u v (Rlt_le _ _ Hr) Hu Hv).
  assert (Hu0 := nbound0 rho Mu u (Rlt_le _ _ Hr) Hu).
  assert (Hv0 := nbound0 rho Mv v (Rlt_le _ _ Hr) Hv).
  pose proof (feval_dt rho (Mu * Mv) (fmul u v) p t Hr Huv) as D1.
  pose proof (is_derive_mult (fun y => feval u y p) (fun y => feval v y p) t _ _
                (feval_dt rho Mu u p t Hr Hu) (feval_dt rho Mv v p t Hr Hv)
                (fun a b => Rmult_comm a b)) as D2.
  apply (is_derive_ext _ (fun y => feval (fmul u v) y p)) in D2.
  2: { intros y. symmetry. apply (feval_fmul u v Mu Mv y p Hu0 Hv0). }
  apply is_derive_unique in D1. apply is_derive_unique in D2.
  rewrite <- D1, D2. reflexivity.
Qed.

Theorem feval_dp_fmul (rho Mu Mv : R) (u v : fser) (t p : R) :
  0 < rho -> nbound rho Mu u -> nbound rho Mv v ->
  feval (dp (fmul u v)) t p = feval (dp u) t p * feval v t p + feval u t p * feval (dp v) t p.
Proof.
  intros Hr Hu Hv.
  assert (Huv := nbound_fmul rho Mu Mv u v (Rlt_le _ _ Hr) Hu Hv).
  assert (Hu0 := nbound0 rho Mu u (Rlt_le _ _ Hr) Hu).
  assert (Hv0 := nbound0 rho Mv v (Rlt_le _ _ Hr) Hv).
  pose proof (feval_dp rho (Mu * Mv) (fmul u v) t p Hr Huv) as D1.
  pose proof (is_derive_mult (fun y => feval u t y) (fun y => feval v t y) p _ _
                (feval_dp rho Mu u t p Hr Hu) (feval_dp rho Mv v t p Hr Hv)
                (fun a b => Rmult_comm a b)) as D2.
  apply (is_derive_ext _ (fun y => feval (fmul u v) t y)) in D2.
  2: { intros y. symmetry. apply (feval_fmul u v Mu Mv t y Hu0 Hv0). }
  apply is_derive_unique in D1. apply is_derive_unique in D2.
  rewrite <- D1, D2. reflexivity.
Qed.

Theorem feval_lc_fmul (om rho Mu Mv : R) (u v : fser) (t p : R) :
  0 < rho -> nbound rho Mu u -> nbound rho Mv v ->
  feval (lc om (fmul u v)) t p
  = feval (lc om u) t p * feval v t p + feval u t p * feval (lc om v) t p.
Proof.
  intros Hr Hu Hv.
  assert (Huv := nbound_fmul rho Mu Mv u v (Rlt_le _ _ Hr) Hu Hv).
  rewrite (feval_lc om rho (Mu * Mv) (fmul u v) t p Hr Huv),
    (feval_lc om rho Mu u t p Hr Hu), (feval_lc om rho Mv v t p Hr Hv),
    (feval_dt_fmul rho Mu Mv u v t p Hr Hu Hv), (feval_dp_fmul rho Mu Mv u v t p Hr Hu Hv).
  ring.
Qed.

Theorem feval_lc_const (om rho M c : R) (u : fser) :
  0 < rho -> nbound rho M u -> (forall t p, feval u t p = c) ->
  forall t p, feval (lc om u) t p = 0.
Proof.
  intros Hr Hu Hc t p. rewrite (feval_lc om rho M u t p Hr Hu).
  pose proof (feval_dt rho M u p t Hr Hu) as D1. pose proof (feval_dp rho M u t p Hr Hu) as D2.
  apply (is_derive_ext _ (fun _ => c)) in D1; [| intros y; apply Hc].
  apply (is_derive_ext _ (fun _ => c)) in D2; [| intros y; apply Hc].
  apply is_derive_unique in D1. apply is_derive_unique in D2.
  rewrite Derive_const in D1, D2. rewrite <- D1, <- D2. ring.
Qed.

Theorem feval_lc_linv (om gamma M : R) (u : fser) (t p : R) :
  diophantine1 om gamma -> 0 < gamma <= 1 -> nbound 0 M u ->
  feval (lc om (linv om u)) t p = feval u t p - fc u 0 0.
Proof.
  intros Hd Hg Hu.
  assert (E : feq (lc om (linv om u)) (fsub u (fsingle 0 0 (fc u 0 0) (fs u 0 0)))).
  { intros m n. destruct (is_mean m n) eqn:Hmn.
    - unfold is_mean in Hmn. apply andb_prop in Hmn. destruct Hmn as [H1 H2].
      apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
      unfold lc, linv, fsub, fadd, fscal, fsingle, at2, divisor. simpl. split; ring.
    - destruct (lc_linv om gamma Hd Hg u m n Hmn) as [E1 E2].
      rewrite E1, E2. unfold fsub, fadd, fscal, fsingle, at2. simpl.
      unfold is_mean in Hmn. rewrite Hmn. split; ring. }
  rewrite (feval_feq _ _ t p E).
  rewrite (feval_fsub u _ M _ t p Hu (nbound_fsingle 0 0 0 (fc u 0 0) (fs u 0 0))).
  rewrite feval_fsingle. unfold mode. rewrite !Rmult_0_l, Rplus_0_l, cos_0, sin_0. ring.
Qed.
