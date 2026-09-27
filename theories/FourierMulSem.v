(** The product of families carries the product of the functions: finite
    sums, truncations and the limit.

    The truncation of a family to the square |m|, |n| <= N is the finite sum of
    its single modes ([trunc_sqfsum]); the function and the product both
    distribute over finite sums ([feval_sqfsum], [fmul_sqfsum_l],
    [fmul_sqfsum_r]), so the product of truncations carries the product of
    their functions ([feval_fmul_trunc]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval.
Local Open Scope R_scope.

(** * Finite sums of families *)

Fixpoint zfsum (F : Z -> fser) (N : nat) : fser :=
  match N with
  | O => F 0%Z
  | S k => fadd (zfsum F k) (fadd (F (Z.of_nat (S k))) (F (- Z.of_nat (S k))%Z))
  end.

Definition sqfsum (F : Z -> Z -> fser) (N : nat) : fser := zfsum (fun j1 => zfsum (F j1) N) N.

Lemma zfsum_S (F : Z -> fser) (N : nat) :
  zfsum F (S N) = fadd (zfsum F N) (fadd (F (Z.of_nat (S N))) (F (- Z.of_nat (S N))%Z)).
Proof. reflexivity. Qed.

Lemma fc_zfsum (F : Z -> fser) (N : nat) (m n : Z) :
  fc (zfsum F N) m n = zsum (fun j => fc (F j) m n) N.
Proof.
  induction N as [| N IH]; [rewrite zsum_0; reflexivity |].
  rewrite zfsum_S, zsum_S. cbn [fc fadd]. rewrite IH. ring.
Qed.

Lemma fs_zfsum (F : Z -> fser) (N : nat) (m n : Z) :
  fs (zfsum F N) m n = zsum (fun j => fs (F j) m n) N.
Proof.
  induction N as [| N IH]; [rewrite zsum_0; reflexivity |].
  rewrite zfsum_S, zsum_S. cbn [fs fadd]. rewrite IH. ring.
Qed.

Lemma fc_sqfsum (F : Z -> Z -> fser) (N : nat) (m n : Z) :
  fc (sqfsum F N) m n = sqsum (fun j1 j2 => fc (F j1 j2) m n) N.
Proof.
  unfold sqfsum, sqsum. rewrite fc_zfsum. apply zsum_ext. intros j1. apply fc_zfsum.
Qed.

Lemma fs_sqfsum (F : Z -> Z -> fser) (N : nat) (m n : Z) :
  fs (sqfsum F N) m n = sqsum (fun j1 j2 => fs (F j1 j2) m n) N.
Proof.
  unfold sqfsum, sqsum. rewrite fs_zfsum. apply zsum_ext. intros j1. apply fs_zfsum.
Qed.

(** * Truncation to a square *)

Definition in_sq (N : nat) (m n : Z) : bool :=
  (Z.leb (Z.abs m) (Z.of_nat N) && Z.leb (Z.abs n) (Z.of_nat N))%bool.

Definition trunc (N : nat) (u : fser) : fser :=
  {| fc := fun m n => if in_sq N m n then fc u m n else 0 ;
     fs := fun m n => if in_sq N m n then fs u m n else 0 |}.

Definition singles (u : fser) (j1 j2 : Z) : fser := fsingle j1 j2 (fc u j1 j2) (fs u j1 j2).

Lemma at2_swap (j1 j2 m n : Z) (f : Z -> Z -> R) :
  at2 j1 j2 (f j1 j2) m n = at2 m n (f m n) j1 j2.
Proof.
  unfold at2.
  destruct (Z.eqb_spec m j1) as [-> | H1]; destruct (Z.eqb_spec n j2) as [-> | H2];
    rewrite ?Z.eqb_refl; simpl; try reflexivity.
  - destruct (Z.eqb_spec j2 n); [congruence | reflexivity].
  - destruct (Z.eqb_spec j1 m); [congruence | reflexivity].
  - destruct (Z.eqb_spec j1 m); [congruence | reflexivity].
Qed.

Theorem trunc_sqfsum (N : nat) (u : fser) : feq (trunc N u) (sqfsum (singles u) N).
Proof.
  intros m n. split.
  - rewrite fc_sqfsum.
    rewrite (sqsum_ext _ (at2 m n (fc u m n)))
      by (intros j1 j2; apply (at2_swap j1 j2 m n (fc u))).
    rewrite sqsum_at2. reflexivity.
  - rewrite fs_sqfsum.
    rewrite (sqsum_ext _ (at2 m n (fs u m n)))
      by (intros j1 j2; apply (at2_swap j1 j2 m n (fs u))).
    rewrite sqsum_at2. reflexivity.
Qed.

(** * Bounds and functions of finite sums *)

Lemma zfsum_nbound (rho B : R) (F : Z -> fser) (N : nat) :
  (forall j, nbound rho B (F j)) -> nbound rho (INR (2 * N + 1) * B) (zfsum F N).
Proof.
  intros HF. induction N as [| N IH].
  - simpl. rewrite Rmult_1_l. apply HF.
  - rewrite zfsum_S.
    replace (INR (2 * S N + 1) * B) with (INR (2 * N + 1) * B + (B + B))
      by (rewrite !plus_INR, !mult_INR, !S_INR; simpl; ring).
    apply nbound_fadd; [exact IH | apply nbound_fadd; apply HF].
Qed.

Lemma sqfsum_nbound (rho B : R) (F : Z -> Z -> fser) (N : nat) :
  (forall j1 j2, nbound rho B (F j1 j2)) ->
  nbound rho (INR (2 * N + 1) * (INR (2 * N + 1) * B)) (sqfsum F N).
Proof.
  intros HF. unfold sqfsum. apply zfsum_nbound. intros j1. apply zfsum_nbound, HF.
Qed.

Lemma feval_zfsum (B : R) (F : Z -> fser) (N : nat) (t p : R) :
  (forall j, nbound 0 B (F j)) ->
  feval (zfsum F N) t p = zsum (fun j => feval (F j) t p) N.
Proof.
  intros HF. induction N as [| N IH]; [rewrite zsum_0; reflexivity |].
  rewrite zfsum_S, zsum_S.
  rewrite (feval_fadd _ _ _ (B + B) t p (zfsum_nbound 0 B F N HF)
             (nbound_fadd _ _ _ _ _ (HF _) (HF _))).
  rewrite (feval_fadd _ _ B B t p (HF _) (HF _)).
  rewrite IH. ring.
Qed.

Lemma feval_sqfsum (B : R) (F : Z -> Z -> fser) (N : nat) (t p : R) :
  (forall j1 j2, nbound 0 B (F j1 j2)) ->
  feval (sqfsum F N) t p = sqsum (fun j1 j2 => feval (F j1 j2) t p) N.
Proof.
  intros HF. unfold sqfsum, sqsum.
  rewrite (feval_zfsum (INR (2 * N + 1) * B) (fun j1 => zfsum (F j1) N) N t p).
  - apply zsum_ext. intros j1. apply (feval_zfsum B), HF.
  - intros j1. apply zfsum_nbound, HF.
Qed.

(** * The product distributes over finite sums *)

Lemma fadd_feq (u u' v v' : fser) : feq u u' -> feq v v' -> feq (fadd u v) (fadd u' v').
Proof.
  intros H1 H2 m n. destruct (H1 m n) as [A1 B1], (H2 m n) as [A2 B2].
  simpl. rewrite A1, B1, A2, B2. split; reflexivity.
Qed.

Lemma zfsum_feq (F G : Z -> fser) (N : nat) :
  (forall j, feq (F j) (G j)) -> feq (zfsum F N) (zfsum G N).
Proof.
  intros H. induction N as [| N IH]; [apply H |].
  rewrite !zfsum_S. apply fadd_feq; [exact IH | apply fadd_feq; apply H].
Qed.

Lemma conv_p_ext_l (f f' g : Z -> Z -> R) (m n : Z) :
  (forall k l, f k l = f' k l) -> conv_p f g m n = conv_p f' g m n.
Proof. intros H. unfold conv_p. apply zz_sum_ext. intros k l. rewrite H. reflexivity. Qed.

Lemma conv_m_ext_l (f f' g : Z -> Z -> R) (m n : Z) :
  (forall k l, f k l = f' k l) -> conv_m f g m n = conv_m f' g m n.
Proof. intros H. unfold conv_m. apply zz_sum_ext. intros k l. rewrite H. reflexivity. Qed.

Lemma conv_p_ext_r (f g g' : Z -> Z -> R) (m n : Z) :
  (forall k l, g k l = g' k l) -> conv_p f g m n = conv_p f g' m n.
Proof. intros H. unfold conv_p. apply zz_sum_ext. intros k l. rewrite H. reflexivity. Qed.

Lemma conv_m_ext_r (f g g' : Z -> Z -> R) (m n : Z) :
  (forall k l, g k l = g' k l) -> conv_m f g m n = conv_m f g' m n.
Proof. intros H. unfold conv_m. apply zz_sum_ext. intros k l. rewrite H. reflexivity. Qed.

Lemma fmul_feq_l (u u' v : fser) : feq u u' -> feq (fmul u v) (fmul u' v).
Proof.
  intros H m n. simpl.
  assert (Ec : forall k l, fc u k l = fc u' k l) by (intros k l; apply (H k l)).
  assert (Es : forall k l, fs u k l = fs u' k l) by (intros k l; apply (H k l)).
  split.
  - rewrite (conv_p_ext_l _ _ _ m n Ec), (conv_p_ext_l _ _ _ m n Es),
      (conv_m_ext_l _ _ _ m n Ec), (conv_m_ext_l _ _ _ m n Es). reflexivity.
  - rewrite (conv_p_ext_l _ _ _ m n Ec), (conv_p_ext_l _ _ _ m n Es),
      (conv_m_ext_l _ _ _ m n Ec), (conv_m_ext_l _ _ _ m n Es). reflexivity.
Qed.

Lemma fmul_feq_r (u v v' : fser) : feq v v' -> feq (fmul u v) (fmul u v').
Proof.
  intros H m n. simpl.
  assert (Ec : forall k l, fc v k l = fc v' k l) by (intros k l; apply (H k l)).
  assert (Es : forall k l, fs v k l = fs v' k l) by (intros k l; apply (H k l)).
  split.
  - rewrite (conv_p_ext_r _ _ _ m n Ec), (conv_p_ext_r _ _ _ m n Es),
      (conv_m_ext_r _ _ _ m n Ec), (conv_m_ext_r _ _ _ m n Es). reflexivity.
  - rewrite (conv_p_ext_r _ _ _ m n Ec), (conv_p_ext_r _ _ _ m n Es),
      (conv_m_ext_r _ _ _ m n Ec), (conv_m_ext_r _ _ _ m n Es). reflexivity.
Qed.

Section Distribute.

Variables (rho : R) (Hr : 0 <= rho).

Lemma fmul_zfsum_l (B Mv : R) (F : Z -> fser) (v : fser) (N : nat) :
  (forall j, nbound rho B (F j)) -> nbound rho Mv v ->
  feq (fmul (zfsum F N) v) (zfsum (fun j => fmul (F j) v) N).
Proof.
  intros HF Hv. induction N as [| N IH]; [apply feq_refl |].
  rewrite !zfsum_S.
  eapply feq_trans.
  { apply (fmul_fadd_l rho Hr _ _ v _ (B + B) Mv (zfsum_nbound rho B F N HF)
             (nbound_fadd _ _ _ _ _ (HF _) (HF _)) Hv). }
  apply fadd_feq; [exact IH |].
  apply (fmul_fadd_l rho Hr _ _ v B B Mv (HF _) (HF _) Hv).
Qed.

Lemma fmul_zfsum_r (B Mu : R) (u : fser) (F : Z -> fser) (N : nat) :
  (forall j, nbound rho B (F j)) -> nbound rho Mu u ->
  feq (fmul u (zfsum F N)) (zfsum (fun j => fmul u (F j)) N).
Proof.
  intros HF Hu. induction N as [| N IH]; [apply feq_refl |].
  rewrite !zfsum_S.
  eapply feq_trans.
  { apply (fmul_fadd_r rho Hr u _ _ Mu _ (B + B) Hu (zfsum_nbound rho B F N HF)
             (nbound_fadd _ _ _ _ _ (HF _) (HF _))). }
  apply fadd_feq; [exact IH |].
  apply (fmul_fadd_r rho Hr u _ _ Mu B B Hu (HF _) (HF _)).
Qed.

Lemma fmul_sqfsum_l (B Mv : R) (F : Z -> Z -> fser) (v : fser) (N : nat) :
  (forall j1 j2, nbound rho B (F j1 j2)) -> nbound rho Mv v ->
  feq (fmul (sqfsum F N) v) (sqfsum (fun j1 j2 => fmul (F j1 j2) v) N).
Proof.
  intros HF Hv. unfold sqfsum.
  eapply feq_trans.
  { apply (fmul_zfsum_l (INR (2 * N + 1) * B) Mv (fun j1 => zfsum (F j1) N) v N); [| exact Hv].
    intros j1. apply zfsum_nbound, HF. }
  apply zfsum_feq. intros j1. apply (fmul_zfsum_l B Mv); [intros; apply HF | exact Hv].
Qed.

Lemma fmul_sqfsum_r (B Mu : R) (u : fser) (F : Z -> Z -> fser) (N : nat) :
  (forall j1 j2, nbound rho B (F j1 j2)) -> nbound rho Mu u ->
  feq (fmul u (sqfsum F N)) (sqfsum (fun j1 j2 => fmul u (F j1 j2)) N).
Proof.
  intros HF Hu. unfold sqfsum.
  eapply feq_trans.
  { apply (fmul_zfsum_r (INR (2 * N + 1) * B) Mu u (fun j1 => zfsum (F j1) N) N); [| exact Hu].
    intros j1. apply zfsum_nbound, HF. }
  apply zfsum_feq. intros j1. apply (fmul_zfsum_r B Mu); [intros; apply HF | exact Hu].
Qed.

End Distribute.

(** * Products of truncations *)

Lemma singles_nbound (u : fser) (Mu : R) (j1 j2 : Z) :
  nbound 0 Mu u -> nbound 0 Mu (singles u j1 j2).
Proof.
  intros Hu N. eapply Rle_trans; [apply (nbound_fsingle 0 j1 j2 (fc u j1 j2) (fs u j1 j2) N) |].
  change ((Rabs (fc u j1 j2) + Rabs (fs u j1 j2)) * wt 0 j1 j2) with (nterm 0 u j1 j2).
  apply (nterm_le_bound 0 Mu u j1 j2 Hu).
Qed.

Lemma sqsum_prod (a b : Z -> Z -> R) (N : nat) :
  sqsum (fun j1 j2 => sqsum (fun l1 l2 => a j1 j2 * b l1 l2) N) N = sqsum a N * sqsum b N.
Proof.
  assert (E1 : forall j1 j2, sqsum (fun l1 l2 => a j1 j2 * b l1 l2) N = sqsum b N * a j1 j2).
  { intros j1 j2. rewrite Rmult_comm. apply sqsum_scal. }
  rewrite (sqsum_ext _ _ N E1).
  assert (E2 : sqsum (fun j1 j2 => sqsum b N * a j1 j2) N = sqsum b N * sqsum a N)
    by apply sqsum_scal.
  rewrite E2. ring.
Qed.

Theorem feval_fmul_trunc (u v : fser) (Mu Mv : R) (N : nat) (t p : R) :
  nbound 0 Mu u -> nbound 0 Mv v ->
  feval (fmul (trunc N u) (trunc N v)) t p = feval (trunc N u) t p * feval (trunc N v) t p.
Proof.
  intros Hu Hv.
  set (Su := singles u). set (Sv := singles v).
  assert (HSu : forall j1 j2, nbound 0 Mu (Su j1 j2)) by (intros; apply singles_nbound, Hu).
  assert (HSv : forall j1 j2, nbound 0 Mv (Sv j1 j2)) by (intros; apply singles_nbound, Hv).
  set (C := INR (2 * N + 1) * (INR (2 * N + 1) * Mv)).
  assert (HsumV : nbound 0 C (sqfsum Sv N)) by (apply sqfsum_nbound, HSv).
  rewrite (feval_feq _ _ t p (fmul_feq_l _ _ _ (trunc_sqfsum N u))).
  rewrite (feval_feq _ _ t p (fmul_feq_r _ _ _ (trunc_sqfsum N v))).
  rewrite (feval_feq _ _ t p (trunc_sqfsum N u)), (feval_feq _ _ t p (trunc_sqfsum N v)).
  fold Su Sv.
  rewrite (feval_feq _ _ t p (fmul_sqfsum_l 0 (Rle_refl 0) Mu C Su (sqfsum Sv N) N HSu HsumV)).
  rewrite (feval_sqfsum (Mu * C) _ N t p).
  2: { intros j1 j2. apply nbound_fmul; [lra | apply HSu | exact HsumV]. }
  rewrite (sqsum_ext _ (fun j1 j2 =>
             sqsum (fun l1 l2 => feval (Su j1 j2) t p * feval (Sv l1 l2) t p) N)).
  2: { intros j1 j2.
       rewrite (feval_feq _ _ t p (fmul_sqfsum_r 0 (Rle_refl 0) Mv Mu (Su j1 j2) Sv N HSv (HSu j1 j2))).
       rewrite (feval_sqfsum (Mu * Mv) _ N t p).
       2: { intros l1 l2. apply nbound_fmul; [lra | apply HSu | apply HSv]. }
       apply sqsum_ext. intros l1 l2. unfold Su, Sv, singles. apply feval_fmul_fsingle. }
  rewrite (feval_sqfsum Mu Su N t p HSu), (feval_sqfsum Mv Sv N t p HSv).
  apply (sqsum_prod (fun j1 j2 => feval (Su j1 j2) t p) (fun l1 l2 => feval (Sv l1 l2) t p)).
Qed.
