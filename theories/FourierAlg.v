(** Sums, multiples and differences of coefficient families.

    Families add and scale mode by mode ([fadd], [fscal], [fsub]); the norm
    bounds add ([nbound_fadd]) and scale ([nbound_fscal]); the functions they
    carry add and scale ([feval_fadd], [feval_fscal]); and the product is
    linear in each factor ([fmul_fadd_l], [fmul_fadd_r], [fmul_fscal_l],
    [fmul_fscal_r]), all up to [feq], equality mode by mode. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul.
Local Open Scope R_scope.

Definition feq (u v : fser) : Prop := forall m n, fc u m n = fc v m n /\ fs u m n = fs v m n.

Definition fadd (u v : fser) : fser :=
  {| fc := fun m n => fc u m n + fc v m n ; fs := fun m n => fs u m n + fs v m n |}.
Definition fscal (c : R) (u : fser) : fser :=
  {| fc := fun m n => c * fc u m n ; fs := fun m n => c * fs u m n |}.
Definition fsub (u v : fser) : fser := fadd u (fscal (-1) v).
Definition fzero : fser := {| fc := fun _ _ => 0 ; fs := fun _ _ => 0 |}.

Lemma feq_refl (u : fser) : feq u u.
Proof. intros m n. split; reflexivity. Qed.

Lemma feq_sym (u v : fser) : feq u v -> feq v u.
Proof. intros H m n. destruct (H m n). split; symmetry; assumption. Qed.

Lemma feq_trans (u v w : fser) : feq u v -> feq v w -> feq u w.
Proof. intros H1 H2 m n. destruct (H1 m n), (H2 m n). split; congruence. Qed.

Lemma nbound_feq (rho M : R) (u v : fser) : feq u v -> nbound rho M u -> nbound rho M v.
Proof.
  intros He H N. eapply Rle_trans; [| apply (H N)]. apply Req_le.
  apply sqsum_ext. intros m n. unfold nterm. destruct (He m n) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Lemma feval_feq (u v : fser) (t p : R) : feq u v -> feval u t p = feval v t p.
Proof.
  intros He. unfold feval. apply zz_sum_ext. intros m n. unfold term.
  destruct (He m n) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Lemma nbound_nonneg (rho M : R) (u : fser) : nbound rho M u -> 0 <= M.
Proof.
  intros H. eapply Rle_trans; [| apply (H 0%nat)].
  apply sqsum_nonneg. intros; apply nterm_nonneg.
Qed.

Lemma nbound_fadd (rho Mu Mv : R) (u v : fser) :
  nbound rho Mu u -> nbound rho Mv v -> nbound rho (Mu + Mv) (fadd u v).
Proof.
  intros Hu Hv N.
  apply Rle_trans with (sqsum (fun m n => nterm rho u m n + nterm rho v m n) N).
  - apply sqsum_le. intros m n. unfold nterm. simpl.
    pose proof (Rabs_triang (fc u m n) (fc v m n)). pose proof (Rabs_triang (fs u m n) (fs v m n)).
    pose proof (wt_pos rho m n). nra.
  - rewrite sqsum_plus. pose proof (Hu N). pose proof (Hv N). lra.
Qed.

Lemma nbound_fscal (rho M c : R) (u : fser) :
  nbound rho M u -> nbound rho (Rabs c * M) (fscal c u).
Proof.
  intros Hu N.
  apply Rle_trans with (sqsum (fun m n => Rabs c * nterm rho u m n) N).
  - apply sqsum_le. intros m n. unfold nterm. simpl. rewrite !Rabs_mult. apply Req_le. ring.
  - rewrite sqsum_scal. apply Rmult_le_compat_l; [apply Rabs_pos | apply Hu].
Qed.

Lemma nbound_fsub (rho Mu Mv : R) (u v : fser) :
  nbound rho Mu u -> nbound rho Mv v -> nbound rho (Mu + Mv) (fsub u v).
Proof.
  intros Hu Hv. unfold fsub.
  replace (Mu + Mv) with (Mu + Rabs (-1) * Mv) by (rewrite Rabs_left by lra; ring).
  apply nbound_fadd; [exact Hu | apply nbound_fscal, Hv].
Qed.

Lemma nbound_fzero (rho : R) : nbound rho 0 fzero.
Proof.
  intros N. apply Req_le. unfold sqsum.
  rewrite (zsum_ext _ (fun _ => 0 * 0)).
  - rewrite zsum_scal. ring.
  - intros m. rewrite (zsum_ext _ (fun _ => 0 * 0)); [rewrite zsum_scal; ring |].
    intros n. unfold nterm. simpl. rewrite Rabs_R0. ring.
Qed.

Lemma summable_term (u : fser) (M t p : R) : nbound 0 M u -> abs_summable (term u t p) M.
Proof. apply summable_of_nbound. Qed.

Lemma feval_fadd (u v : fser) (Mu Mv t p : R) :
  nbound 0 Mu u -> nbound 0 Mv v -> feval (fadd u v) t p = feval u t p + feval v t p.
Proof.
  intros Hu Hv. unfold feval.
  rewrite <- (zz_sum_plus _ _ _ _ (summable_term u Mu t p Hu) (summable_term v Mv t p Hv)).
  apply zz_sum_ext. intros m n. unfold term. simpl. ring.
Qed.

Lemma feval_fscal (c : R) (u : fser) (M t p : R) :
  nbound 0 M u -> feval (fscal c u) t p = c * feval u t p.
Proof.
  intros Hu. unfold feval.
  rewrite <- (zz_sum_scal c _ _ (summable_term u M t p Hu)).
  apply zz_sum_ext. intros m n. unfold term. simpl. ring.
Qed.

Lemma feval_fsub (u v : fser) (Mu Mv t p : R) :
  nbound 0 Mu u -> nbound 0 Mv v -> feval (fsub u v) t p = feval u t p - feval v t p.
Proof.
  intros Hu Hv. unfold fsub.
  rewrite (feval_fadd u (fscal (-1) v) Mu (Rabs (-1) * Mv)); [| exact Hu | apply nbound_fscal, Hv].
  rewrite (feval_fscal (-1) v Mv); [ring | exact Hv].
Qed.

(** * The product is linear in each factor *)

Section Linear.

Variables (rho : R) (Hr : 0 <= rho).

Lemma conv_p_add_l (f1 f2 g : Z -> Z -> R) (M1 M2 B : R) (m n : Z) :
  abs_summable f1 M1 -> abs_summable f2 M2 -> tbound g B ->
  conv_p (fun k l => f1 k l + f2 k l) g m n = conv_p f1 g m n + conv_p f2 g m n.
Proof.
  intros H1 H2 Hg. unfold conv_p.
  rewrite <- (zz_sum_plus _ _ _ _ (summable_mul_tbound f1 g M1 B m n true H1 Hg)
                               (summable_mul_tbound f2 g M2 B m n true H2 Hg)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma conv_m_add_l (f1 f2 g : Z -> Z -> R) (M1 M2 B : R) (m n : Z) :
  abs_summable f1 M1 -> abs_summable f2 M2 -> tbound g B ->
  conv_m (fun k l => f1 k l + f2 k l) g m n = conv_m f1 g m n + conv_m f2 g m n.
Proof.
  intros H1 H2 Hg. unfold conv_m.
  rewrite <- (zz_sum_plus _ _ _ _ (summable_mul_tbound f1 g M1 B m n false H1 Hg)
                               (summable_mul_tbound f2 g M2 B m n false H2 Hg)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma tbound_plus (g1 g2 : Z -> Z -> R) (B1 B2 : R) :
  tbound g1 B1 -> tbound g2 B2 -> tbound (fun k l => g1 k l + g2 k l) (B1 + B2).
Proof.
  intros H1 H2 k l. eapply Rle_trans; [apply Rabs_triang |].
  pose proof (H1 k l). pose proof (H2 k l). lra.
Qed.

Lemma conv_p_add_r (f g1 g2 : Z -> Z -> R) (M B1 B2 : R) (m n : Z) :
  abs_summable f M -> tbound g1 B1 -> tbound g2 B2 ->
  conv_p f (fun k l => g1 k l + g2 k l) m n = conv_p f g1 m n + conv_p f g2 m n.
Proof.
  intros Hf H1 H2. unfold conv_p.
  rewrite <- (zz_sum_plus _ _ _ _ (summable_mul_tbound f g1 M B1 m n true Hf H1)
                               (summable_mul_tbound f g2 M B2 m n true Hf H2)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma conv_m_add_r (f g1 g2 : Z -> Z -> R) (M B1 B2 : R) (m n : Z) :
  abs_summable f M -> tbound g1 B1 -> tbound g2 B2 ->
  conv_m f (fun k l => g1 k l + g2 k l) m n = conv_m f g1 m n + conv_m f g2 m n.
Proof.
  intros Hf H1 H2. unfold conv_m.
  rewrite <- (zz_sum_plus _ _ _ _ (summable_mul_tbound f g1 M B1 m n false Hf H1)
                               (summable_mul_tbound f g2 M B2 m n false Hf H2)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma conv_p_scal_l (c : R) (f g : Z -> Z -> R) (M B : R) (m n : Z) :
  abs_summable f M -> tbound g B ->
  conv_p (fun k l => c * f k l) g m n = c * conv_p f g m n.
Proof.
  intros Hf Hg. unfold conv_p.
  rewrite <- (zz_sum_scal c _ _ (summable_mul_tbound f g M B m n true Hf Hg)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma conv_m_scal_l (c : R) (f g : Z -> Z -> R) (M B : R) (m n : Z) :
  abs_summable f M -> tbound g B ->
  conv_m (fun k l => c * f k l) g m n = c * conv_m f g m n.
Proof.
  intros Hf Hg. unfold conv_m.
  rewrite <- (zz_sum_scal c _ _ (summable_mul_tbound f g M B m n false Hf Hg)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma conv_p_scal_r (c : R) (f g : Z -> Z -> R) (M B : R) (m n : Z) :
  abs_summable f M -> tbound g B ->
  conv_p f (fun k l => c * g k l) m n = c * conv_p f g m n.
Proof.
  intros Hf Hg. unfold conv_p.
  rewrite <- (zz_sum_scal c _ _ (summable_mul_tbound f g M B m n true Hf Hg)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Lemma conv_m_scal_r (c : R) (f g : Z -> Z -> R) (M B : R) (m n : Z) :
  abs_summable f M -> tbound g B ->
  conv_m f (fun k l => c * g k l) m n = c * conv_m f g m n.
Proof.
  intros Hf Hg. unfold conv_m.
  rewrite <- (zz_sum_scal c _ _ (summable_mul_tbound f g M B m n false Hf Hg)).
  apply zz_sum_ext. intros k l. simpl. ring.
Qed.

Theorem fmul_fadd_l (u1 u2 v : fser) (M1 M2 Mv : R) :
  nbound rho M1 u1 -> nbound rho M2 u2 -> nbound rho Mv v ->
  feq (fmul (fadd u1 u2) v) (fadd (fmul u1 v) (fmul u2 v)).
Proof.
  intros H1 H2 Hv m n.
  pose proof (summable_fc rho M1 u1 Hr H1) as A1. pose proof (summable_fs rho M1 u1 Hr H1) as B1.
  pose proof (summable_fc rho M2 u2 Hr H2) as A2. pose proof (summable_fs rho M2 u2 Hr H2) as B2.
  pose proof (tbound_fc rho Mv v Hr Hv) as Ta. pose proof (tbound_fs rho Mv v Hr Hv) as Tb.
  simpl. split.
  - rewrite (conv_p_add_l _ _ _ _ _ _ m n A1 A2 Ta), (conv_p_add_l _ _ _ _ _ _ m n B1 B2 Tb),
      (conv_m_add_l _ _ _ _ _ _ m n A1 A2 Ta), (conv_m_add_l _ _ _ _ _ _ m n B1 B2 Tb).
    ring.
  - rewrite (conv_p_add_l _ _ _ _ _ _ m n A1 A2 Tb), (conv_p_add_l _ _ _ _ _ _ m n B1 B2 Ta),
      (conv_m_add_l _ _ _ _ _ _ m n A1 A2 Tb), (conv_m_add_l _ _ _ _ _ _ m n B1 B2 Ta).
    ring.
Qed.

Theorem fmul_fadd_r (u v1 v2 : fser) (Mu M1 M2 : R) :
  nbound rho Mu u -> nbound rho M1 v1 -> nbound rho M2 v2 ->
  feq (fmul u (fadd v1 v2)) (fadd (fmul u v1) (fmul u v2)).
Proof.
  intros Hu H1 H2 m n.
  pose proof (summable_fc rho Mu u Hr Hu) as A. pose proof (summable_fs rho Mu u Hr Hu) as B.
  pose proof (tbound_fc rho M1 v1 Hr H1) as Ta1. pose proof (tbound_fs rho M1 v1 Hr H1) as Tb1.
  pose proof (tbound_fc rho M2 v2 Hr H2) as Ta2. pose proof (tbound_fs rho M2 v2 Hr H2) as Tb2.
  simpl. split.
  - rewrite (conv_p_add_r _ _ _ _ _ _ m n A Ta1 Ta2), (conv_p_add_r _ _ _ _ _ _ m n B Tb1 Tb2),
      (conv_m_add_r _ _ _ _ _ _ m n A Ta1 Ta2), (conv_m_add_r _ _ _ _ _ _ m n B Tb1 Tb2).
    ring.
  - rewrite (conv_p_add_r _ _ _ _ _ _ m n A Tb1 Tb2), (conv_p_add_r _ _ _ _ _ _ m n B Ta1 Ta2),
      (conv_m_add_r _ _ _ _ _ _ m n A Tb1 Tb2), (conv_m_add_r _ _ _ _ _ _ m n B Ta1 Ta2).
    ring.
Qed.

Theorem fmul_fscal_l (c : R) (u v : fser) (Mu Mv : R) :
  nbound rho Mu u -> nbound rho Mv v -> feq (fmul (fscal c u) v) (fscal c (fmul u v)).
Proof.
  intros Hu Hv m n.
  pose proof (summable_fc rho Mu u Hr Hu) as A. pose proof (summable_fs rho Mu u Hr Hu) as B.
  pose proof (tbound_fc rho Mv v Hr Hv) as Ta. pose proof (tbound_fs rho Mv v Hr Hv) as Tb.
  simpl. split.
  - rewrite (conv_p_scal_l c _ _ _ _ m n A Ta), (conv_p_scal_l c _ _ _ _ m n B Tb),
      (conv_m_scal_l c _ _ _ _ m n A Ta), (conv_m_scal_l c _ _ _ _ m n B Tb).
    ring.
  - rewrite (conv_p_scal_l c _ _ _ _ m n A Tb), (conv_p_scal_l c _ _ _ _ m n B Ta),
      (conv_m_scal_l c _ _ _ _ m n A Tb), (conv_m_scal_l c _ _ _ _ m n B Ta).
    ring.
Qed.

Theorem fmul_fscal_r (c : R) (u v : fser) (Mu Mv : R) :
  nbound rho Mu u -> nbound rho Mv v -> feq (fmul u (fscal c v)) (fscal c (fmul u v)).
Proof.
  intros Hu Hv m n.
  pose proof (summable_fc rho Mu u Hr Hu) as A. pose proof (summable_fs rho Mu u Hr Hu) as B.
  pose proof (tbound_fc rho Mv v Hr Hv) as Ta. pose proof (tbound_fs rho Mv v Hr Hv) as Tb.
  simpl. split.
  - rewrite (conv_p_scal_r c _ _ _ _ m n A Ta), (conv_p_scal_r c _ _ _ _ m n B Tb),
      (conv_m_scal_r c _ _ _ _ m n A Ta), (conv_m_scal_r c _ _ _ _ m n B Tb).
    ring.
  - rewrite (conv_p_scal_r c _ _ _ _ m n A Tb), (conv_p_scal_r c _ _ _ _ m n B Ta),
      (conv_m_scal_r c _ _ _ _ m n A Tb), (conv_m_scal_r c _ _ _ _ m n B Ta).
    ring.
Qed.

End Linear.
