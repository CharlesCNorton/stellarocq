(** The product of two coefficient families and its norm.

    [fmul u v] has the coefficients the product-to-sum formulas give, through
    the convolutions [conv_p] (modes k + l) and [conv_m] (modes k - l). A
    finite sum over a square of target modes exchanges with the sum over k
    ([zsum_zz_swap]), and the weight of mode j is at most the product of the
    weights of k and of j - k, so the norm of the product on a strip rho >= 0
    is at most the product of the norms ([nbound_fmul]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd.
Local Open Scope R_scope.

Definition conv_p (f g : Z -> Z -> R) (m n : Z) : R :=
  zz_sum (fun k l => f k l * g (m - k)%Z (n - l)%Z).
Definition conv_m (f g : Z -> Z -> R) (m n : Z) : R :=
  zz_sum (fun k l => f k l * g (k - m)%Z (l - n)%Z).

Definition fmul (u v : fser) : fser :=
  {| fc := fun m n => / 2 * (conv_p (fc u) (fc v) m n - conv_p (fs u) (fs v) m n
                             + conv_m (fc u) (fc v) m n + conv_m (fs u) (fs v) m n) ;
     fs := fun m n => / 2 * (conv_p (fc u) (fs v) m n + conv_p (fs u) (fc v) m n
                             - conv_m (fc u) (fs v) m n + conv_m (fs u) (fc v) m n) |}.

(** * Termwise bounds and summability *)

Definition tbound (g : Z -> Z -> R) (B : R) : Prop := forall m n, Rabs (g m n) <= B.

Lemma wt_ge_1 (rho : R) (m n : Z) : 0 <= rho -> 1 <= wt rho m n.
Proof.
  intros Hr. unfold wt. rewrite <- exp_0. apply exp_mono.
  pose proof (msize_nonneg m n). nra.
Qed.

Lemma nterm_ge_fc (rho : R) (u : fser) (m n : Z) :
  0 <= rho -> Rabs (fc u m n) <= nterm rho u m n.
Proof.
  intros Hr. unfold nterm. pose proof (wt_ge_1 rho m n Hr).
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
Qed.

Lemma nterm_ge_fs (rho : R) (u : fser) (m n : Z) :
  0 <= rho -> Rabs (fs u m n) <= nterm rho u m n.
Proof.
  intros Hr. unfold nterm. pose proof (wt_ge_1 rho m n Hr).
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). nra.
Qed.

Lemma nterm_le_bound (rho M : R) (u : fser) (m n : Z) :
  nbound rho M u -> nterm rho u m n <= M.
Proof.
  intros H.
  set (N := (Z.to_nat (Z.abs m) + Z.to_nat (Z.abs n))%nat).
  apply Rle_trans with (sqsum (nterm rho u) N); [| apply H].
  apply single_le_sqsum; [intros; apply nterm_nonneg | unfold N; lia | unfold N; lia].
Qed.

Lemma tbound_fc (rho M : R) (u : fser) : 0 <= rho -> nbound rho M u -> tbound (fc u) M.
Proof.
  intros Hr H m n. eapply Rle_trans; [apply (nterm_ge_fc rho) | apply (nterm_le_bound rho)]; assumption.
Qed.

Lemma tbound_fs (rho M : R) (u : fser) : 0 <= rho -> nbound rho M u -> tbound (fs u) M.
Proof.
  intros Hr H m n. eapply Rle_trans; [apply (nterm_ge_fs rho) | apply (nterm_le_bound rho)]; assumption.
Qed.

Lemma summable_fc (rho M : R) (u : fser) : 0 <= rho -> nbound rho M u -> abs_summable (fc u) M.
Proof.
  intros Hr H N. eapply Rle_trans; [| apply (H N)].
  apply sqsum_le. intros m n. unfold absf. apply (nterm_ge_fc rho); assumption.
Qed.

Lemma summable_fs (rho M : R) (u : fser) : 0 <= rho -> nbound rho M u -> abs_summable (fs u) M.
Proof.
  intros Hr H N. eapply Rle_trans; [| apply (H N)].
  apply sqsum_le. intros m n. unfold absf. apply (nterm_ge_fs rho); assumption.
Qed.

Lemma summable_mul_tbound (f g : Z -> Z -> R) (Mf B : R) (c d : Z) (sgn : bool) :
  abs_summable f Mf -> tbound g B ->
  abs_summable (fun k l => f k l * (if sgn then g (c - k)%Z (d - l)%Z else g (k - c)%Z (l - d)%Z))
               (Mf * B).
Proof.
  intros Hf Hg N.
  assert (HB : 0 <= B) by (eapply Rle_trans; [apply Rabs_pos | apply (Hg 0%Z 0%Z)]).
  apply Rle_trans with (sqsum (fun k l => B * absf f k l) N).
  - apply sqsum_le. intros k l. unfold absf. rewrite Rabs_mult.
    destruct sgn; rewrite Rmult_comm; apply Rmult_le_compat_r; try apply Rabs_pos; apply Hg.
  - rewrite sqsum_scal. rewrite Rmult_comm. apply Rmult_le_compat_r; [exact HB | apply Hf].
Qed.

(** * Exchanging a finite sum with a sum over Z x Z *)

Lemma sqsum_ext (f g : Z -> Z -> R) (N : nat) :
  (forall m n, f m n = g m n) -> sqsum f N = sqsum g N.
Proof.
  intros H. unfold sqsum. apply zsum_ext. intros m. apply zsum_ext. intros n. apply H.
Qed.

Lemma zz_sum_ext (f g : Z -> Z -> R) :
  (forall m n, f m n = g m n) -> zz_sum f = zz_sum g.
Proof.
  intros H. unfold zz_sum. f_equal. apply Lim_seq_ext. intros N. apply sqsum_ext, H.
Qed.

Lemma zsum_const (c : R) (N : nat) : zsum (fun _ => c) N = INR (2 * N + 1) * c.
Proof.
  induction N as [| N IH]; [rewrite zsum_0; simpl; ring |].
  rewrite zsum_S, IH. rewrite !plus_INR, !mult_INR, !S_INR. simpl. ring.
Qed.

Lemma sqsum_zsum_comm (H : Z -> Z -> Z -> R) (N M : nat) :
  sqsum (fun k l => zsum (fun j => H j k l) N) M = zsum (fun j => sqsum (H j) M) N.
Proof.
  induction N as [| N IH].
  - rewrite zsum_0. apply sqsum_ext. intros k l. rewrite zsum_0. reflexivity.
  - rewrite zsum_S, <- IH.
    rewrite <- !sqsum_plus. apply sqsum_ext. intros k l. rewrite zsum_S. reflexivity.
Qed.

Lemma zsum_summable (G : Z -> Z -> Z -> R) (B : R) (N : nat) :
  (forall j, abs_summable (G j) B) ->
  abs_summable (fun k l => zsum (fun j => G j k l) N) (INR (2 * N + 1) * B).
Proof.
  intros HG M.
  apply Rle_trans with (sqsum (fun k l => zsum (fun j => absf (G j) k l) N) M).
  - apply sqsum_le. intros k l. unfold absf at 1. apply zsum_abs.
  - rewrite sqsum_zsum_comm, <- zsum_const.
    apply zsum_le. intros j. apply HG.
Qed.

Lemma zsum_zz_swap (G : Z -> Z -> Z -> R) (B : R) (N : nat) :
  (forall j, abs_summable (G j) B) ->
  zsum (fun j => zz_sum (G j)) N = zz_sum (fun k l => zsum (fun j => G j k l) N).
Proof.
  intros HG. induction N as [| N IH].
  - rewrite zsum_0. apply zz_sum_ext. intros k l. rewrite zsum_0. reflexivity.
  - rewrite zsum_S, IH.
    set (s := Z.of_nat (S N)).
    rewrite <- (zz_sum_plus (G s) (G (- s)%Z) B B (HG s) (HG (- s)%Z)).
    rewrite <- (zz_sum_plus _ _ _ (B + B) (zsum_summable G B N HG)
                  (summable_plus _ _ B B (HG s) (HG (- s)%Z))).
    apply zz_sum_ext. intros k l. rewrite zsum_S. reflexivity.
Qed.

Lemma sqsum_zz_swap (G : Z -> Z -> Z -> Z -> R) (B : R) (N : nat) :
  (forall j1 j2, abs_summable (G j1 j2) B) ->
  sqsum (fun j1 j2 => zz_sum (G j1 j2)) N
    = zz_sum (fun k l => sqsum (fun j1 j2 => G j1 j2 k l) N).
Proof.
  intros HG. unfold sqsum.
  rewrite (zsum_ext _ (fun j1 => zz_sum (fun k l => zsum (fun j2 => G j1 j2 k l) N))).
  2: { intros j1. apply (zsum_zz_swap (G j1) B N (HG j1)). }
  apply (zsum_zz_swap (fun j1 k l => zsum (fun j2 => G j1 j2 k l) N) (INR (2 * N + 1) * B) N).
  intros j1. apply zsum_summable, HG.
Qed.

(** * The product's coefficients, one mode at a time *)

Lemma zz_sum_minus (g h : Z -> Z -> R) (Mg Mh : R) :
  abs_summable g Mg -> abs_summable h Mh ->
  zz_sum (fun m n => g m n - h m n) = zz_sum g - zz_sum h.
Proof.
  intros Hg Hh.
  rewrite (zz_sum_ext _ (fun m n => g m n + -1 * h m n)) by (intros; ring).
  rewrite (zz_sum_plus g (fun m n => -1 * h m n) Mg (Rabs (-1) * Mh) Hg (summable_scal _ _ _ Hh)).
  rewrite (zz_sum_scal (-1) h Mh Hh). ring.
Qed.

Section Product.

Variables (rho Mu Mv : R) (u v : fser).
Hypothesis Hr : 0 <= rho.
Hypothesis Hu : nbound rho Mu u.
Hypothesis Hv : nbound rho Mv v.

Let a := fc u. Let b := fs u. Let a' := fc v. Let b' := fs v.

Lemma sp (f g : Z -> Z -> R) (m n : Z) :
  abs_summable f Mu -> tbound g Mv ->
  abs_summable (fun k l => f k l * g (m - k)%Z (n - l)%Z) (Mu * Mv).
Proof. intros Hf Hg. exact (summable_mul_tbound f g Mu Mv m n true Hf Hg). Qed.

Lemma sm (f g : Z -> Z -> R) (m n : Z) :
  abs_summable f Mu -> tbound g Mv ->
  abs_summable (fun k l => f k l * g (k - m)%Z (l - n)%Z) (Mu * Mv).
Proof. intros Hf Hg. exact (summable_mul_tbound f g Mu Mv m n false Hf Hg). Qed.

Let Sa := summable_fc rho Mu u Hr Hu.
Let Sb := summable_fs rho Mu u Hr Hu.
Let Ta' := tbound_fc rho Mv v Hr Hv.
Let Tb' := tbound_fs rho Mv v Hr Hv.

Definition alpha (k l : Z) : R := Rabs (a k l) + Rabs (b k l).
Definition beta (k l : Z) : R := Rabs (a' k l) + Rabs (b' k l).

Lemma pair_bound (x y x' y' : R) :
  Rabs (x * x' - y * y') + Rabs (x * y' + y * x')
    <= (Rabs x + Rabs y) * (Rabs x' + Rabs y').
Proof.
  assert (H1 : Rabs (x * x' - y * y') <= Rabs x * Rabs x' + Rabs y * Rabs y').
  { unfold Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp, !Rabs_mult. lra. }
  assert (H2 : Rabs (x * y' + y * x') <= Rabs x * Rabs y' + Rabs y * Rabs x').
  { eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult. lra. }
  replace ((Rabs x + Rabs y) * (Rabs x' + Rabs y'))
    with (Rabs x * Rabs x' + Rabs y * Rabs y' + (Rabs x * Rabs y' + Rabs y * Rabs x')) by ring.
  lra.
Qed.

Lemma pair_bound' (x y x' y' : R) :
  Rabs (x * x' + y * y') + Rabs (y * x' - x * y')
    <= (Rabs x + Rabs y) * (Rabs x' + Rabs y').
Proof.
  assert (H1 : Rabs (x * x' + y * y') <= Rabs x * Rabs x' + Rabs y * Rabs y').
  { eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult. lra. }
  assert (H2 : Rabs (y * x' - x * y') <= Rabs x * Rabs y' + Rabs y * Rabs x').
  { unfold Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp, !Rabs_mult. lra. }
  replace ((Rabs x + Rabs y) * (Rabs x' + Rabs y'))
    with (Rabs x * Rabs x' + Rabs y * Rabs y' + (Rabs x * Rabs y' + Rabs y * Rabs x')) by ring.
  lra.
Qed.

Definition P1 (m n k l : Z) : R := a k l * a' (m - k)%Z (n - l)%Z - b k l * b' (m - k)%Z (n - l)%Z.
Definition Q1 (m n k l : Z) : R := a k l * b' (m - k)%Z (n - l)%Z + b k l * a' (m - k)%Z (n - l)%Z.
Definition P2 (m n k l : Z) : R := a k l * a' (k - m)%Z (l - n)%Z + b k l * b' (k - m)%Z (l - n)%Z.
Definition Q2 (m n k l : Z) : R := b k l * a' (k - m)%Z (l - n)%Z - a k l * b' (k - m)%Z (l - n)%Z.

Lemma sP1 (m n : Z) : abs_summable (P1 m n) (Mu * Mv + Mu * Mv).
Proof.
  unfold P1. eapply summable_dom.
  2: { apply (summable_plus _ _ _ _ (summable_absf _ _ (sp a a' m n Sa Ta'))
                                    (summable_absf _ _ (sp b b' m n Sb Tb'))). }
  intros k l. unfold absf, Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra.
Qed.

Lemma sQ1 (m n : Z) : abs_summable (Q1 m n) (Mu * Mv + Mu * Mv).
Proof.
  unfold Q1. eapply summable_dom.
  2: { apply (summable_plus _ _ _ _ (summable_absf _ _ (sp a b' m n Sa Tb'))
                                    (summable_absf _ _ (sp b a' m n Sb Ta'))). }
  intros k l. unfold absf. apply Rabs_triang.
Qed.

Lemma sP2 (m n : Z) : abs_summable (P2 m n) (Mu * Mv + Mu * Mv).
Proof.
  unfold P2. eapply summable_dom.
  2: { apply (summable_plus _ _ _ _ (summable_absf _ _ (sm a a' m n Sa Ta'))
                                    (summable_absf _ _ (sm b b' m n Sb Tb'))). }
  intros k l. unfold absf. apply Rabs_triang.
Qed.

Lemma sQ2 (m n : Z) : abs_summable (Q2 m n) (Mu * Mv + Mu * Mv).
Proof.
  unfold Q2. eapply summable_dom.
  2: { apply (summable_plus _ _ _ _ (summable_absf _ _ (sm b a' m n Sb Ta'))
                                    (summable_absf _ _ (sm a b' m n Sa Tb'))). }
  intros k l. unfold absf, Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra.
Qed.

Lemma fmul_fc_eq (m n : Z) :
  fc (fmul u v) m n = / 2 * zz_sum (P1 m n) + / 2 * zz_sum (P2 m n).
Proof.
  simpl. unfold conv_p, conv_m, P1, P2.
  rewrite (zz_sum_minus _ _ _ _ (sp a a' m n Sa Ta') (sp b b' m n Sb Tb')).
  rewrite (zz_sum_plus _ _ _ _ (sm a a' m n Sa Ta') (sm b b' m n Sb Tb')).
  fold a b a' b'. ring.
Qed.

Lemma fmul_fs_eq (m n : Z) :
  fs (fmul u v) m n = / 2 * zz_sum (Q1 m n) + / 2 * zz_sum (Q2 m n).
Proof.
  simpl. unfold conv_p, conv_m, Q1, Q2.
  rewrite (zz_sum_plus _ _ _ _ (sp a b' m n Sa Tb') (sp b a' m n Sb Ta')).
  rewrite (zz_sum_minus _ _ _ _ (sm b a' m n Sb Ta') (sm a b' m n Sa Tb')).
  fold a b a' b'. ring.
Qed.

(** * The norm of the product *)

Lemma alpha_le (k l : Z) : alpha k l <= nterm rho u k l.
Proof. unfold alpha, nterm, a, b. pose proof (wt_ge_1 rho k l Hr).
  pose proof (Rabs_pos (fc u k l)). pose proof (Rabs_pos (fs u k l)). nra. Qed.

Lemma beta_le (k l : Z) : beta k l <= nterm rho v k l.
Proof. unfold beta, nterm, a', b'. pose proof (wt_ge_1 rho k l Hr).
  pose proof (Rabs_pos (fc v k l)). pose proof (Rabs_pos (fs v k l)). nra. Qed.

Lemma alpha_nonneg (k l : Z) : 0 <= alpha k l.
Proof. unfold alpha. pose proof (Rabs_pos (a k l)). pose proof (Rabs_pos (b k l)). lra. Qed.

Lemma beta_nonneg (k l : Z) : 0 <= beta k l.
Proof. unfold beta. pose proof (Rabs_pos (a' k l)). pose proof (Rabs_pos (b' k l)). lra. Qed.

Lemma alpha_summable : abs_summable alpha Mu.
Proof.
  intros N. eapply Rle_trans; [| apply (Hu N)].
  apply sqsum_le. intros k l. unfold absf. rewrite Rabs_pos_eq by apply alpha_nonneg.
  apply alpha_le.
Qed.

Lemma beta_tbound : tbound beta Mv.
Proof.
  intros k l. rewrite Rabs_pos_eq by apply beta_nonneg.
  eapply Rle_trans; [apply beta_le | apply (nterm_le_bound rho Mv v k l Hv)].
Qed.

Lemma coef_bound (m n : Z) :
  Rabs (fc (fmul u v) m n) + Rabs (fs (fmul u v) m n)
    <= / 2 * conv_p alpha beta m n + / 2 * conv_m alpha beta m n.
Proof.
  rewrite fmul_fc_eq, fmul_fs_eq.
  assert (Hh : forall x y, Rabs (/ 2 * x + / 2 * y) <= / 2 * Rabs x + / 2 * Rabs y).
  { intros x y. eapply Rle_trans; [apply Rabs_triang |].
    rewrite !Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. lra. }
  pose proof (Hh (zz_sum (P1 m n)) (zz_sum (P2 m n))) as H1.
  pose proof (Hh (zz_sum (Q1 m n)) (zz_sum (Q2 m n))) as H2.
  pose proof (zz_sum_abs _ _ (sP1 m n)) as A1.
  pose proof (zz_sum_abs _ _ (sP2 m n)) as A2.
  pose proof (zz_sum_abs _ _ (sQ1 m n)) as A3.
  pose proof (zz_sum_abs _ _ (sQ2 m n)) as A4.
  assert (E1 : zz_sum (absf (P1 m n)) + zz_sum (absf (Q1 m n)) <= conv_p alpha beta m n).
  { rewrite <- (zz_sum_plus _ _ _ _ (summable_absf _ _ (sP1 m n)) (summable_absf _ _ (sQ1 m n))).
    unfold conv_p.
    apply (zz_sum_le _ _ ((Mu * Mv + Mu * Mv) + (Mu * Mv + Mu * Mv)) (Mu * Mv)).
    - apply summable_plus; apply summable_absf; [apply sP1 | apply sQ1].
    - exact (summable_mul_tbound alpha beta Mu Mv m n true alpha_summable beta_tbound).
    - intros k l. unfold absf, P1, Q1, alpha, beta. apply pair_bound. }
  assert (E2 : zz_sum (absf (P2 m n)) + zz_sum (absf (Q2 m n)) <= conv_m alpha beta m n).
  { rewrite <- (zz_sum_plus _ _ _ _ (summable_absf _ _ (sP2 m n)) (summable_absf _ _ (sQ2 m n))).
    unfold conv_m.
    apply (zz_sum_le _ _ ((Mu * Mv + Mu * Mv) + (Mu * Mv + Mu * Mv)) (Mu * Mv)).
    - apply summable_plus; apply summable_absf; [apply sP2 | apply sQ2].
    - exact (summable_mul_tbound alpha beta Mu Mv m n false alpha_summable beta_tbound).
    - intros k l. unfold absf, P2, Q2, alpha, beta. apply pair_bound'. }
  lra.
Qed.

Lemma wt_triang_p (m n k l : Z) : wt rho m n <= wt rho k l * wt rho (m - k)%Z (n - l)%Z.
Proof.
  unfold wt. rewrite <- exp_plus. apply exp_mono. rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l; [exact Hr |]. unfold msize.
  rewrite !minus_IZR.
  pose proof (Rabs_triang (IZR k) (IZR m - IZR k)).
  pose proof (Rabs_triang (IZR l) (IZR n - IZR l)).
  replace (IZR k + (IZR m - IZR k)) with (IZR m) in * by ring.
  replace (IZR l + (IZR n - IZR l)) with (IZR n) in * by ring.
  lra.
Qed.

Lemma wt_triang_m (m n k l : Z) : wt rho m n <= wt rho k l * wt rho (k - m)%Z (l - n)%Z.
Proof.
  unfold wt. rewrite <- exp_plus. apply exp_mono. rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l; [exact Hr |]. unfold msize.
  rewrite !minus_IZR.
  pose proof (Rabs_triang (IZR k) (- (IZR k - IZR m))).
  pose proof (Rabs_triang (IZR l) (- (IZR l - IZR n))).
  rewrite !Rabs_Ropp in *.
  replace (IZR k + - (IZR k - IZR m)) with (IZR m) in * by ring.
  replace (IZR l + - (IZR l - IZR n)) with (IZR n) in * by ring.
  lra.
Qed.

Lemma zsum_reflect (f : Z -> R) (N : nat) : zsum (fun m => f (- m)%Z) N = zsum f N.
Proof.
  induction N as [| N IH]; [rewrite !zsum_0; reflexivity |].
  rewrite !zsum_S, IH, Z.opp_involutive. ring.
Qed.

Lemma sqsum_reflect (f : Z -> Z -> R) (N : nat) :
  sqsum (fun m n => f (- m)%Z (- n)%Z) N = sqsum f N.
Proof.
  unfold sqsum.
  rewrite (zsum_ext _ (fun m => zsum (fun n => f (- m)%Z n) N)).
  - apply (zsum_reflect (fun m => zsum (fun n => f m n) N)).
  - intros m. apply (zsum_reflect (fun n => f (- m)%Z n)).
Qed.

Let aw := nterm rho u.
Let bw := nterm rho v.

Lemma nterm_alpha (k l : Z) : nterm rho u k l = alpha k l * wt rho k l.
Proof. reflexivity. Qed.

Lemma nterm_beta (k l : Z) : nterm rho v k l = beta k l * wt rho k l.
Proof. reflexivity. Qed.

Lemma aw_summable : abs_summable aw Mu.
Proof.
  intros N. eapply Rle_trans; [| apply (Hu N)].
  apply sqsum_le. intros k l. unfold absf, aw. rewrite Rabs_pos_eq by apply nterm_nonneg. lra.
Qed.

Lemma bw_tbound : tbound bw Mv.
Proof.
  intros k l. unfold bw. rewrite Rabs_pos_eq by apply nterm_nonneg. apply nterm_le_bound, Hv.
Qed.

Lemma wsum_conv (sgn : bool) (N : nat) :
  sqsum (fun m n => wt rho m n *
                    (if sgn then conv_p alpha beta m n else conv_m alpha beta m n)) N
    <= Mu * Mv.
Proof.
  set (G := fun m n k l => aw k l *
                           (if sgn then bw (m - k)%Z (n - l)%Z else bw (k - m)%Z (l - n)%Z)).
  assert (HG : forall m n, abs_summable (G m n) (Mu * Mv)).
  { intros m n. exact (summable_mul_tbound aw bw Mu Mv m n sgn aw_summable bw_tbound). }
  apply Rle_trans with (sqsum (fun m n => zz_sum (G m n)) N).
  - apply sqsum_le. intros m n.
    assert (Hs : abs_summable (fun k l => alpha k l *
                   (if sgn then beta (m - k)%Z (n - l)%Z else beta (k - m)%Z (l - n)%Z)) (Mu * Mv))
      by exact (summable_mul_tbound alpha beta Mu Mv m n sgn alpha_summable beta_tbound).
    replace (wt rho m n * (if sgn then conv_p alpha beta m n else conv_m alpha beta m n))
      with (zz_sum (fun k l => wt rho m n * (alpha k l *
              (if sgn then beta (m - k)%Z (n - l)%Z else beta (k - m)%Z (l - n)%Z)))).
    2: { rewrite (zz_sum_scal (wt rho m n) _ _ Hs). destruct sgn; reflexivity. }
    apply (zz_sum_le _ _ (Rabs (wt rho m n) * (Mu * Mv)) (Mu * Mv)).
    + apply summable_scal, Hs.
    + apply HG.
    + intros k l. unfold G, aw, bw.
      rewrite nterm_alpha.
      pose proof (alpha_nonneg k l).
      destruct sgn.
      * rewrite nterm_beta.
        pose proof (beta_nonneg (m - k)%Z (n - l)%Z).
        pose proof (wt_triang_p m n k l).
        replace (alpha k l * wt rho k l * (beta (m - k)%Z (n - l)%Z * wt rho (m - k)%Z (n - l)%Z))
          with (alpha k l * beta (m - k)%Z (n - l)%Z * (wt rho k l * wt rho (m - k)%Z (n - l)%Z))
          by ring.
        replace (wt rho m n * (alpha k l * beta (m - k)%Z (n - l)%Z))
          with (alpha k l * beta (m - k)%Z (n - l)%Z * wt rho m n) by ring.
        apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption | assumption].
      * rewrite nterm_beta.
        pose proof (beta_nonneg (k - m)%Z (l - n)%Z).
        pose proof (wt_triang_m m n k l).
        replace (alpha k l * wt rho k l * (beta (k - m)%Z (l - n)%Z * wt rho (k - m)%Z (l - n)%Z))
          with (alpha k l * beta (k - m)%Z (l - n)%Z * (wt rho k l * wt rho (k - m)%Z (l - n)%Z))
          by ring.
        replace (wt rho m n * (alpha k l * beta (k - m)%Z (l - n)%Z))
          with (alpha k l * beta (k - m)%Z (l - n)%Z * wt rho m n) by ring.
        apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption | assumption].
  - rewrite (sqsum_zz_swap G (Mu * Mv) N HG).
    apply zz_sum_nonneg_bound.
    + intros k l. apply sqsum_nonneg. intros m n. unfold G, aw, bw.
      apply Rmult_le_pos; [apply nterm_nonneg | destruct sgn; apply nterm_nonneg].
    + intros N'.
      apply Rle_trans with (sqsum (fun k l => Mv * aw k l) N').
      * apply sqsum_le. intros k l. unfold G.
        rewrite (sqsum_scal (aw k l)
                   (fun m n => if sgn then bw (m - k)%Z (n - l)%Z else bw (k - m)%Z (l - n)%Z) N).
        rewrite Rmult_comm. apply Rmult_le_compat_r; [apply nterm_nonneg |].
        destruct sgn.
        -- eapply Rle_trans; [apply (sqsum_shift bw k l N); intros; apply nterm_nonneg |].
           apply Hv.
        -- rewrite (sqsum_ext _ (fun m n => (fun x y => bw (- x)%Z (- y)%Z) (m - k)%Z (n - l)%Z))
             by (intros; f_equal; lia).
           eapply Rle_trans; [apply (sqsum_shift (fun x y => bw (- x)%Z (- y)%Z) k l N);
                              intros; apply nterm_nonneg |].
           rewrite sqsum_reflect. apply Hv.
      * rewrite sqsum_scal, (Rmult_comm Mu Mv). apply Rmult_le_compat_l.
        -- eapply Rle_trans; [apply Rabs_pos | apply (bw_tbound 0%Z 0%Z)].
        -- apply Hu.
Qed.

Theorem nbound_fmul : nbound rho (Mu * Mv) (fmul u v).
Proof.
  intros N.
  apply Rle_trans with
    (sqsum (fun m n => / 2 * (wt rho m n * conv_p alpha beta m n)
                     + / 2 * (wt rho m n * conv_m alpha beta m n)) N).
  - apply sqsum_le. intros m n. unfold nterm.
    pose proof (coef_bound m n). pose proof (wt_pos rho m n). nra.
  - rewrite sqsum_plus, !sqsum_scal.
    pose proof (wsum_conv true N) as Hp. pose proof (wsum_conv false N) as Hm.
    simpl in Hp, Hm. lra.
Qed.

End Product.
