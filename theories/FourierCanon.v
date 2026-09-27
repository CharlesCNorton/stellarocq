(** Canonical families.

    A family is canonical when its cosine coefficients are even and its sine
    coefficients odd under (m, n) -> (-m, -n), so that each mode of its
    function is split equally between (m, n) and (-m, -n). [canon] symmetrises
    a family without changing its function ([feval_canon]) or raising its norm
    ([nbound_canon]). Sums, multiples, the derivatives, L and its inverse,
    products ([fmul_canon]), limits, Newton inverses and inverse square roots
    keep families canonical, and two canonical families with the same function
    are equal ([canon_feq]). Identities between functions are therefore
    identities between canonical families: products commute ([fmul_comm]) and
    associate ([fmul_assoc]), one is a unit on both sides ([fmul_fone_l]), and a
    Newton inverse times its family is one ([fmul_finv]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierDFT.
Local Open Scope R_scope.

Definition zsym (f : Z -> Z -> R) : Prop := forall k l, f (- k)%Z (- l)%Z = f k l.
Definition zanti (f : Z -> Z -> R) : Prop := forall k l, f (- k)%Z (- l)%Z = - f k l.

Definition is_canon (u : fser) : Prop := zsym (fc u) /\ zanti (fs u).

Definition canon (u : fser) : fser := {| fc := ccan u ; fs := scan u |}.

Lemma canon_is_canon (u : fser) : is_canon (canon u).
Proof.
  split; intros k l; unfold canon, ccan, scan; simpl; rewrite !Z.opp_involutive; ring.
Qed.

Lemma canon_id (u : fser) : is_canon u -> feq (canon u) u.
Proof.
  intros [Hc Hs] m n. unfold canon, ccan, scan. simpl.
  rewrite (Hc m n), (Hs m n). split; field.
Qed.

(** * Reflection of sums *)

Lemma zz_sum_reflect (g : Z -> Z -> R) : zz_sum (fun m n => g (- m)%Z (- n)%Z) = zz_sum g.
Proof.
  unfold zz_sum. rewrite (Lim_seq_ext _ (fun N => sqsum g N)) by (intros; apply sqsum_reflect).
  reflexivity.
Qed.

Lemma zz_sum_opp (g : Z -> Z -> R) : zz_sum (fun m n => - g m n) = - zz_sum g.
Proof.
  unfold zz_sum.
  rewrite (Lim_seq_ext _ (fun N => - sqsum g N)).
  - rewrite Lim_seq_opp. destruct (Lim_seq (fun N => sqsum g N)); simpl; ring.
  - intros N. rewrite (sqsum_ext _ (fun m n => -1 * g m n)) by (intros; ring).
    rewrite sqsum_scal. ring.
Qed.

Lemma summable_reflect (g : Z -> Z -> R) (M : R) :
  abs_summable g M -> abs_summable (fun m n => g (- m)%Z (- n)%Z) M.
Proof.
  intros H N. unfold absf.
  rewrite (sqsum_reflect (fun m n => Rabs (g m n))). apply H.
Qed.

Lemma wt_opp (rho : R) (m n : Z) : wt rho (- m) (- n) = wt rho m n.
Proof. unfold wt, msize. rewrite !opp_IZR, !Rabs_Ropp. reflexivity. Qed.

Lemma mode_opp (m n : Z) (t p : R) : mode (- m) (- n) t p = - mode m n t p.
Proof. unfold mode. rewrite !opp_IZR. ring. Qed.

(** * The symmetrised family *)

Theorem nbound_canon (rho M : R) (u : fser) : nbound rho M u -> nbound rho M (canon u).
Proof.
  intros H N.
  apply Rle_trans with (sqsum (fun m n => / 2 * nterm rho u m n + / 2 * nterm rho u (- m) (- n)) N).
  - apply sqsum_le. intros m n. unfold nterm, canon, ccan, scan. simpl.
    rewrite wt_opp, !Rabs_mult, (Rabs_pos_eq (/ 2)) by lra.
    pose proof (Rabs_triang (fc u m n) (fc u (- m) (- n))).
    pose proof (Rabs_triang (fs u m n) (- fs u (- m) (- n))).
    rewrite Rabs_Ropp in H1.
    replace (fs u m n - fs u (- m) (- n)) with (fs u m n + - fs u (- m) (- n)) by ring.
    pose proof (wt_pos rho m n). nra.
  - rewrite sqsum_plus, !sqsum_scal, (sqsum_reflect (nterm rho u)).
    pose proof (H N). lra.
Qed.

Theorem feval_canon (u : fser) (M t p : R) : nbound 0 M u -> feval (canon u) t p = feval u t p.
Proof.
  intros Hu. unfold feval.
  assert (HS := summable_term u M t p Hu).
  rewrite (zz_sum_ext _ (fun m n => / 2 * term u t p m n + / 2 * term u t p (- m) (- n))).
  - rewrite (zz_sum_plus _ _ _ _ (summable_scal (/ 2) _ _ HS)
               (summable_scal (/ 2) _ _ (summable_reflect _ _ HS))).
    rewrite (zz_sum_scal (/ 2) _ _ HS), (zz_sum_scal (/ 2) _ _ (summable_reflect _ _ HS)).
    rewrite (zz_sum_reflect (term u t p)). field.
  - intros m n. unfold term, canon, ccan, scan. simpl.
    rewrite mode_opp, cos_neg, sin_neg. ring.
Qed.

Theorem canon_feq (u v : fser) (Mu Mv : R) :
  is_canon u -> is_canon v -> nbound 0 Mu u -> nbound 0 Mv v ->
  (forall t p, feval u t p = feval v t p) -> feq u v.
Proof.
  intros Cu Cv Bu Bv H m n.
  destruct (canon_unique u v Mu Mv Bu Bv H m n) as [Ec Es].
  destruct (canon_id u Cu m n) as [Au Su]. destruct (canon_id v Cv m n) as [Av Sv].
  simpl in Au, Su, Av, Sv. split; congruence.
Qed.

(** * Operations keep families canonical *)

Lemma fadd_canon (u v : fser) : is_canon u -> is_canon v -> is_canon (fadd u v).
Proof.
  intros [Hu1 Hu2] [Hv1 Hv2]. split; intros k l; simpl.
  - rewrite Hu1, Hv1. ring.
  - rewrite Hu2, Hv2. ring.
Qed.

Lemma fscal_canon (c : R) (u : fser) : is_canon u -> is_canon (fscal c u).
Proof. intros [H1 H2]. split; intros k l; simpl; [rewrite H1 | rewrite H2]; ring. Qed.

Lemma fsub_canon (u v : fser) : is_canon u -> is_canon v -> is_canon (fsub u v).
Proof. intros Hu Hv. apply fadd_canon; [exact Hu | apply fscal_canon, Hv]. Qed.

Lemma fzero_canon : is_canon fzero.
Proof. split; intros k l; simpl; ring. Qed.

Lemma at2_00_opp (x : R) (k l : Z) : at2 0 0 x (- k) (- l) = at2 0 0 x k l.
Proof.
  unfold at2. destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec l 0);
    destruct (Z.eqb_spec (- k) 0); destruct (Z.eqb_spec (- l) 0); simpl; try lia; reflexivity.
Qed.

Lemma fone_canon : is_canon fone.
Proof.
  split; intros k l; unfold fone, fsingle; simpl; rewrite at2_00_opp; [reflexivity |].
  unfold at2. destruct (_ && _)%bool; ring.
Qed.

Lemma dt_canon (u : fser) : is_canon u -> is_canon (dt u).
Proof.
  intros [H1 H2]. split; intros k l; simpl; rewrite ?H1, ?H2, opp_IZR; ring.
Qed.

Lemma dp_canon (u : fser) : is_canon u -> is_canon (dp u).
Proof.
  intros [H1 H2]. split; intros k l; simpl; rewrite ?H1, ?H2, opp_IZR; ring.
Qed.

Lemma divisor_opp (rho0 : R) (m n : Z) : divisor rho0 (- m) (- n) = - divisor rho0 m n.
Proof. unfold divisor. rewrite !opp_IZR. ring. Qed.

Lemma lc_canon (rho0 : R) (u : fser) : is_canon u -> is_canon (lc rho0 u).
Proof.
  intros [H1 H2]. split; intros k l; simpl; rewrite divisor_opp, ?H1, ?H2; ring.
Qed.

Lemma is_mean_opp (m n : Z) : is_mean (- m) (- n) = is_mean m n.
Proof.
  unfold is_mean. destruct (Z.eqb_spec m 0); destruct (Z.eqb_spec n 0);
    destruct (Z.eqb_spec (- m) 0); destruct (Z.eqb_spec (- n) 0); simpl; try lia; reflexivity.
Qed.

Lemma linv_canon (rho0 : R) (u : fser) : is_canon u -> is_canon (linv rho0 u).
Proof.
  intros [H1 H2]. split; intros k l; simpl; rewrite is_mean_opp;
    destruct (is_mean k l); try ring;
    rewrite divisor_opp, ?H1, ?H2; unfold Rdiv; rewrite Rinv_opp; ring.
Qed.

Lemma flim_canon (us : nat -> fser) : (forall n, is_canon (us n)) -> is_canon (flim us).
Proof.
  intros H. split; intros k l; simpl.
  - rewrite (Lim_seq_ext _ (fun n => fc (us n) k l)) by (intros n; apply (proj1 (H n))).
    reflexivity.
  - rewrite (Lim_seq_ext _ (fun n => - fs (us n) k l)) by (intros n; apply (proj2 (H n))).
    rewrite Lim_seq_opp. destruct (Lim_seq (fun n => fs (us n) k l)); simpl; ring.
Qed.

(** Convolutions of symmetric and antisymmetric coefficient functions. *)

Lemma conv_p_neg (f g : Z -> Z -> R) (m n : Z) :
  conv_p f g (- m) (- n) = zz_sum (fun k l => f (- k)%Z (- l)%Z * g (- (m - k))%Z (- (n - l))%Z).
Proof.
  unfold conv_p. rewrite <- (zz_sum_reflect (fun k l => f k l * g (- m - k)%Z (- n - l)%Z)).
  apply zz_sum_ext. intros k l. cbv beta.
  replace (- m - - k)%Z with (- (m - k))%Z by lia.
  replace (- n - - l)%Z with (- (n - l))%Z by lia. reflexivity.
Qed.

Lemma conv_m_neg (f g : Z -> Z -> R) (m n : Z) :
  conv_m f g (- m) (- n) = zz_sum (fun k l => f (- k)%Z (- l)%Z * g (- (k - m))%Z (- (l - n))%Z).
Proof.
  unfold conv_m. rewrite <- (zz_sum_reflect (fun k l => f k l * g (k - - m)%Z (l - - n)%Z)).
  apply zz_sum_ext. intros k l. cbv beta.
  replace (- k - - m)%Z with (- (k - m))%Z by lia.
  replace (- l - - n)%Z with (- (l - n))%Z by lia. reflexivity.
Qed.

Lemma conv_p_even (f g : Z -> Z -> R) (sf sg : R) (m n : Z) :
  (forall k l, f (- k)%Z (- l)%Z = sf * f k l) -> (forall k l, g (- k)%Z (- l)%Z = sg * g k l) ->
  (sf * sg = 1 \/ sf * sg = -1) ->
  conv_p f g (- m) (- n) = sf * sg * conv_p f g m n.
Proof.
  intros Hf Hg Hs. rewrite conv_p_neg. unfold conv_p.
  rewrite (zz_sum_ext _ (fun k l => sf * sg * (f k l * g (m - k)%Z (n - l)%Z)))
    by (intros k l; rewrite Hf, Hg; ring).
  destruct Hs as [-> | ->].
  - rewrite (zz_sum_ext _ (fun k l => f k l * g (m - k)%Z (n - l)%Z)) by (intros; ring). ring.
  - rewrite (zz_sum_ext _ (fun k l => - (f k l * g (m - k)%Z (n - l)%Z))) by (intros; ring).
    rewrite zz_sum_opp. ring.
Qed.

Lemma conv_m_even (f g : Z -> Z -> R) (sf sg : R) (m n : Z) :
  (forall k l, f (- k)%Z (- l)%Z = sf * f k l) -> (forall k l, g (- k)%Z (- l)%Z = sg * g k l) ->
  (sf * sg = 1 \/ sf * sg = -1) ->
  conv_m f g (- m) (- n) = sf * sg * conv_m f g m n.
Proof.
  intros Hf Hg Hs. rewrite conv_m_neg. unfold conv_m.
  rewrite (zz_sum_ext _ (fun k l => sf * sg * (f k l * g (k - m)%Z (l - n)%Z)))
    by (intros k l; rewrite Hf, Hg; ring).
  destruct Hs as [-> | ->].
  - rewrite (zz_sum_ext _ (fun k l => f k l * g (k - m)%Z (l - n)%Z)) by (intros; ring). ring.
  - rewrite (zz_sum_ext _ (fun k l => - (f k l * g (k - m)%Z (l - n)%Z))) by (intros; ring).
    rewrite zz_sum_opp. ring.
Qed.

Theorem fmul_canon (u v : fser) : is_canon u -> is_canon v -> is_canon (fmul u v).
Proof.
  intros [Hu1 Hu2] [Hv1 Hv2].
  assert (Su : forall k l, fc u (- k)%Z (- l)%Z = 1 * fc u k l) by (intros; rewrite Hu1; ring).
  assert (Au : forall k l, fs u (- k)%Z (- l)%Z = -1 * fs u k l) by (intros; rewrite Hu2; ring).
  assert (Sv : forall k l, fc v (- k)%Z (- l)%Z = 1 * fc v k l) by (intros; rewrite Hv1; ring).
  assert (Av : forall k l, fs v (- k)%Z (- l)%Z = -1 * fs v k l) by (intros; rewrite Hv2; ring).
  split; intros m n; unfold fmul; simpl.
  - rewrite (conv_p_even _ _ _ _ m n Su Sv), (conv_p_even _ _ _ _ m n Au Av),
      (conv_m_even _ _ _ _ m n Su Sv), (conv_m_even _ _ _ _ m n Au Av) by lra. ring.
  - rewrite (conv_p_even _ _ _ _ m n Su Av), (conv_p_even _ _ _ _ m n Au Sv),
      (conv_m_even _ _ _ _ m n Su Av), (conv_m_even _ _ _ _ m n Au Sv) by lra. ring.
Qed.

Lemma finv_canon (u y0 : fser) : is_canon u -> is_canon y0 -> is_canon (finv u y0).
Proof.
  intros Hu Hy0. unfold finv. apply flim_canon. intros k.
  assert (H : is_canon (iy u y0 k) /\ is_canon (ie u y0 k)).
  { induction k as [| k [IHy IHe]].
    - unfold iy, ie. simpl. split; [exact Hy0 |].
      apply fsub_canon; [apply fone_canon | apply fmul_canon; assumption].
    - rewrite iy_S, ie_S. split.
      + apply fmul_canon; [exact IHy | apply fadd_canon; [apply fone_canon | exact IHe]].
      + apply fmul_canon; assumption. }
  apply H.
Qed.

Lemma fisqrt_canon (D y0 : fser) : is_canon D -> is_canon y0 -> is_canon (fisqrt D y0).
Proof.
  intros HD Hy0. unfold fisqrt. apply flim_canon. intros k.
  assert (H : is_canon (sy D y0 k) /\ is_canon (se D y0 k)).
  { induction k as [| k [IHy IHe]].
    - unfold sy, se. simpl. split; [exact Hy0 |].
      apply fsub_canon; [apply fone_canon |].
      apply fmul_canon; [exact HD | apply fmul_canon; assumption].
    - rewrite sy_S, se_S. unfold half_step, err_step. split.
      + apply fmul_canon; [exact IHy |].
        apply fadd_canon; [apply fone_canon | apply fscal_canon, IHe].
      + apply fadd_canon; apply fscal_canon.
        * apply fmul_canon; assumption.
        * apply fmul_canon; [apply fmul_canon; assumption | exact IHe]. }
  apply H.
Qed.

(** * The algebra of canonical families *)

Lemma nbound_fmul0 (u v : fser) (Mu Mv : R) :
  nbound 0 Mu u -> nbound 0 Mv v -> nbound 0 (Mu * Mv) (fmul u v).
Proof. intros Hu Hv. apply nbound_fmul; [lra | exact Hu | exact Hv]. Qed.

Theorem fmul_comm (u v : fser) (Mu Mv : R) :
  is_canon u -> is_canon v -> nbound 0 Mu u -> nbound 0 Mv v -> feq (fmul u v) (fmul v u).
Proof.
  intros Cu Cv Bu Bv.
  apply (canon_feq _ _ (Mu * Mv) (Mv * Mu)); try (apply fmul_canon; assumption);
    try (apply nbound_fmul0; assumption).
  intros t p. rewrite (feval_fmul u v Mu Mv t p Bu Bv), (feval_fmul v u Mv Mu t p Bv Bu). ring.
Qed.

Theorem fmul_assoc (u v w : fser) (Mu Mv Mw : R) :
  is_canon u -> is_canon v -> is_canon w -> nbound 0 Mu u -> nbound 0 Mv v -> nbound 0 Mw w ->
  feq (fmul (fmul u v) w) (fmul u (fmul v w)).
Proof.
  intros Cu Cv Cw Bu Bv Bw.
  apply (canon_feq _ _ (Mu * Mv * Mw) (Mu * (Mv * Mw))).
  - repeat apply fmul_canon; assumption.
  - apply fmul_canon; [assumption | apply fmul_canon; assumption].
  - apply nbound_fmul0; [apply nbound_fmul0 |]; assumption.
  - apply nbound_fmul0; [| apply nbound_fmul0]; assumption.
  - intros t p.
    rewrite (feval_fmul (fmul u v) w (Mu * Mv) Mw t p (nbound_fmul0 u v Mu Mv Bu Bv) Bw),
      (feval_fmul u v Mu Mv t p Bu Bv),
      (feval_fmul u (fmul v w) Mu (Mv * Mw) t p Bu (nbound_fmul0 v w Mv Mw Bv Bw)),
      (feval_fmul v w Mv Mw t p Bv Bw). ring.
Qed.

Theorem fmul_fone_l (u : fser) (M : R) : is_canon u -> nbound 0 M u -> feq (fmul fone u) u.
Proof.
  intros Cu Bu.
  apply (canon_feq _ _ (1 * M) M); [apply fmul_canon; [apply fone_canon | exact Cu] | exact Cu | | exact Bu |].
  - apply nbound_fmul0; [apply nbound_fone | exact Bu].
  - intros t p. rewrite (feval_fmul fone u 1 M t p (nbound_fone 0) Bu), feval_fone. ring.
Qed.
