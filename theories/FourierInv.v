(** Inverses of families by Newton's iteration.

    From an approximate inverse y0 of u with error e0 = 1 - u y0 of norm
    q < 1 on a strip rho >= 0, the iteration y' = y (1 + e), e' = e^2 keeps
    e = 1 - u y at the level of the functions ([inv_invariant]); its errors
    fall as q^(2^k), its iterates stay within |y0| / (1 - q), and its steps
    sum, so the iterates converge to a family [finv] whose function times the
    function of u is one ([feval_finv]), within 2 |y0| q / (1 - q)^2 of y0
    ([nbound_finv_sub]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulLim FourierLim.
Local Open Scope R_scope.

(** * The constant one *)

Definition fone : fser := fsingle 0 0 1 0.

Lemma feval_fone (t p : R) : feval fone t p = 1.
Proof. unfold fone. rewrite feval_fsingle. unfold mode. simpl. rewrite !Rmult_0_l, Rplus_0_l, cos_0. ring. Qed.

Lemma nbound_fone (rho : R) : nbound rho 1 fone.
Proof.
  pose proof (nbound_fsingle rho 0 0 1 0) as H.
  replace ((Rabs 1 + Rabs 0) * wt rho 0 0) with 1 in H.
  - exact H.
  - unfold wt, msize. rewrite !Rabs_R0, Rabs_R1.
    replace (rho * (0 + kappa * 0)) with 0 by ring. rewrite exp_0. ring.
Qed.

Lemma conv_p_unit (f : Z -> Z -> R) (x : R) (m n : Z) : conv_p f (at2 0 0 x) m n = x * f m n.
Proof.
  unfold conv_p. rewrite (zz_sum_ext _ (at2 m n (f m n * x))).
  - rewrite zz_sum_at2. ring.
  - intros k l. unfold at2.
    destruct (Z.eqb_spec k m) as [-> | Hk]; destruct (Z.eqb_spec l n) as [-> | Hl].
    + rewrite !Z.sub_diag. simpl. ring.
    + rewrite Z.sub_diag. destruct (Z.eqb_spec (n - l) 0); [lia |]. simpl. ring.
    + destruct (Z.eqb_spec (m - k) 0); [lia |]. simpl. ring.
    + destruct (Z.eqb_spec (m - k) 0); [lia |]. simpl. ring.
Qed.

Lemma conv_m_unit (f : Z -> Z -> R) (x : R) (m n : Z) : conv_m f (at2 0 0 x) m n = x * f m n.
Proof.
  unfold conv_m. rewrite (zz_sum_ext _ (at2 m n (f m n * x))).
  - rewrite zz_sum_at2. ring.
  - intros k l. unfold at2.
    destruct (Z.eqb_spec k m) as [-> | Hk]; destruct (Z.eqb_spec l n) as [-> | Hl].
    + rewrite !Z.sub_diag. simpl. ring.
    + rewrite Z.sub_diag. destruct (Z.eqb_spec (l - n) 0); [lia |]. simpl. ring.
    + destruct (Z.eqb_spec (k - m) 0); [lia |]. simpl. ring.
    + destruct (Z.eqb_spec (k - m) 0); [lia |]. simpl. ring.
Qed.

(** One on the right leaves every coefficient as it is. *)
Lemma fmul_fone (u : fser) : feq (fmul u fone) u.
Proof.
  intros m n. unfold fmul, fone, fsingle. cbn [fc fs].
  rewrite !conv_p_unit, !conv_m_unit. split; field.
Qed.

(** * Sums of steps *)

(** 2^(N + i) >= 2^N + i. *)
Lemma pow2_ge (N i : nat) : (2 ^ N + i <= 2 ^ (N + i))%nat.
Proof.
  induction i as [| i IH].
  - rewrite !Nat.add_0_r. lia.
  - replace (N + S i)%nat with (S (N + i)) by lia.
    rewrite Nat.pow_succ_r'. pose proof (Nat.pow_nonzero 2 (N + i) ltac:(lia)). lia.
Qed.

Lemma geom_fsum (q : R) (L : nat) : 0 <= q < 1 -> fsum (fun i => q ^ i) L <= / (1 - q).
Proof.
  intros Hq.
  assert (E : fsum (fun i => q ^ i) L * (1 - q) = 1 - q ^ L).
  { induction L as [| L IH]; simpl; [ring |]. rewrite Rmult_plus_distr_r, IH. ring. }
  assert (0 <= q ^ L) by (apply pow_le; lra).
  apply Rmult_le_reg_r with (1 - q); [lra |].
  rewrite E, Rinv_l by lra. lra.
Qed.

Lemma qpow_tail (q : R) (N : nat) (L : nat) :
  0 <= q < 1 -> fsum (fun i => q ^ (2 ^ (N + i))%nat) L <= q ^ (2 ^ N)%nat / (1 - q).
Proof.
  intros Hq.
  apply Rle_trans with (fsum (fun i => q ^ (2 ^ N)%nat * q ^ i) L).
  - apply fsum_le. intros i _. rewrite <- pow_add.
    apply pow_le_exp; [lra | apply pow2_ge].
  - rewrite fsum_scal.
    assert (0 <= q ^ (2 ^ N)%nat) by (apply pow_le; lra).
    unfold Rdiv. apply Rmult_le_compat_l; [assumption | apply geom_fsum, Hq].
Qed.

Lemma qpow_lim (q : R) : 0 <= q < 1 -> is_lim_seq (fun N => q ^ (2 ^ N)%nat) 0.
Proof.
  intros Hq.
  apply (is_lim_seq_le_le (fun _ => 0) (fun N => q ^ (2 ^ N)%nat) (fun N => q ^ N)).
  - intros N. split; [apply pow_le; lra |].
    apply pow_le_exp; [lra |]. apply Nat.lt_le_incl, Nat.pow_gt_lin_r. lia.
  - apply is_lim_seq_const.
  - apply is_lim_seq_geom. rewrite Rabs_pos_eq; lra.
Qed.

Section Steps.

Variables (rho : R) (ys : nat -> fser) (s : nat -> R).
Hypothesis Hs : forall k, nbound rho (s k) (fsub (ys (S k)) (ys k)).

Lemma steps_bound (n L : nat) :
  nbound rho (fsum (fun i => s (n + i)%nat) L) (fsub (ys (n + L)) (ys n)).
Proof.
  induction L as [| L IH].
  - simpl. rewrite Nat.add_0_r.
    apply (nbound_feq _ _ fzero); [| apply nbound_fzero].
    intros k l. simpl. split; ring.
  - simpl.
    replace (n + S L)%nat with (S (n + L)) by lia.
    apply (nbound_feq _ _ (fadd (fsub (ys (S (n + L))) (ys (n + L))) (fsub (ys (n + L)) (ys n)))).
    + intros k l. simpl. split; ring.
    + rewrite Rplus_comm. apply nbound_fadd; [apply Hs | exact IH].
Qed.

Variable T : nat -> R.
Hypothesis HT : forall N L, fsum (fun i => s (N + i)%nat) L <= T N.

Lemma steps_cauchy (N n m : nat) :
  (N <= n)%nat -> (N <= m)%nat -> nbound rho (2 * T N) (fsub (ys n) (ys m)).
Proof.
  intros Hn Hm.
  assert (Hn' : nbound rho (T N) (fsub (ys n) (ys N))).
  { replace n with (N + (n - N))%nat by lia.
    intros K. eapply Rle_trans; [apply (steps_bound N (n - N)) |]. apply HT. }
  assert (Hm' : nbound rho (T N) (fsub (ys m) (ys N))).
  { replace m with (N + (m - N))%nat by lia.
    intros K. eapply Rle_trans; [apply (steps_bound N (m - N)) |]. apply HT. }
  apply (nbound_feq _ _ (fadd (fsub (ys n) (ys N)) (fscal (-1) (fsub (ys m) (ys N))))).
  - intros k l. simpl. split; ring.
  - replace (2 * T N) with (T N + Rabs (-1) * T N) by (rewrite Rabs_left by lra; ring).
    apply nbound_fadd; [exact Hn' | apply nbound_fscal, Hm'].
Qed.

End Steps.

(** * The inverse *)

Section Inverse.

Variables (rho : R) (Hr : 0 <= rho).
Variables (u y0 : fser) (Mu Y0 q : R).
Hypothesis Hu : nbound rho Mu u.
Hypothesis Hy0 : nbound rho Y0 y0.
Hypothesis Hq : 0 <= q < 1.
Hypothesis He0 : nbound rho q (fsub fone (fmul u y0)).

Fixpoint inv_it (k : nat) : fser * fser :=
  match k with
  | O => (y0, fsub fone (fmul u y0))
  | S j => let '(y, e) := inv_it j in (fmul y (fadd fone e), fmul e e)
  end.

Definition iy (k : nat) : fser := fst (inv_it k).
Definition ie (k : nat) : fser := snd (inv_it k).

Lemma iy_S (k : nat) : iy (S k) = fmul (iy k) (fadd fone (ie k)).
Proof. unfold iy, ie. simpl. destruct (inv_it k). reflexivity. Qed.

Lemma ie_S (k : nat) : ie (S k) = fmul (ie k) (ie k).
Proof. unfold ie. simpl. destruct (inv_it k). reflexivity. Qed.

Lemma ie_bound (k : nat) : nbound rho (q ^ (2 ^ k)%nat) (ie k).
Proof.
  induction k as [| k IH].
  - replace (q ^ (2 ^ 0)%nat) with q by (simpl; ring). exact He0.
  - rewrite ie_S. replace (q ^ (2 ^ S k)%nat) with (q ^ (2 ^ k)%nat * q ^ (2 ^ k)%nat).
    + apply nbound_fmul; assumption.
    + rewrite <- pow_add. f_equal. simpl. lia.
Qed.

Fixpoint qprod (k : nat) : R :=
  match k with O => 1 | S j => qprod j * (1 + q ^ (2 ^ j)%nat) end.

Lemma qprod_eq (k : nat) : qprod k * (1 - q) = 1 - q ^ (2 ^ k)%nat.
Proof.
  induction k as [| k IH]; simpl; [ring |].
  replace (qprod k * (1 + q ^ (2 ^ k)%nat) * (1 - q))
    with (qprod k * (1 - q) * (1 + q ^ (2 ^ k)%nat)) by ring.
  rewrite IH. replace (2 ^ k + (2 ^ k + 0))%nat with (2 ^ k + 2 ^ k)%nat by lia.
  rewrite pow_add. ring.
Qed.

Lemma qprod_le (k : nat) : qprod k <= / (1 - q).
Proof.
  apply Rmult_le_reg_r with (1 - q); [lra |].
  rewrite qprod_eq, Rinv_l by lra.
  assert (0 <= q ^ (2 ^ k)%nat) by (apply pow_le; lra). lra.
Qed.

Lemma qprod_pos (k : nat) : 0 < qprod k.
Proof.
  induction k as [| k IH]; simpl; [lra |].
  assert (0 <= q ^ (2 ^ k)%nat) by (apply pow_le; lra). nra.
Qed.

Lemma iy_bound (k : nat) : nbound rho (Y0 * qprod k) (iy k).
Proof.
  induction k as [| k IH].
  - simpl. rewrite Rmult_1_r. exact Hy0.
  - rewrite iy_S. simpl qprod. rewrite <- Rmult_assoc.
    apply nbound_fmul; [exact Hr | exact IH |].
    apply nbound_fadd; [apply nbound_fone | apply ie_bound].
Qed.

Lemma Y0_nonneg : 0 <= Y0.
Proof. apply (nbound_nonneg rho Y0 y0 Hy0). Qed.

Lemma iy_step (k : nat) :
  nbound rho (Y0 / (1 - q) * q ^ (2 ^ k)%nat) (fsub (iy (S k)) (iy k)).
Proof.
  rewrite iy_S.
  (* y (1 + e) - y = y e *)
  apply (nbound_feq _ _ (fmul (iy k) (ie k))).
  - pose proof (fmul_fadd_r rho Hr (iy k) fone (ie k) _ 1 _ (iy_bound k) (nbound_fone rho) (ie_bound k))
      as E.
    pose proof (fmul_fone (iy k)) as F.
    intros a b. destruct (E a b) as [E1 E2]. destruct (F a b) as [F1 F2].
    cbn [fsub fadd fscal fc fs] in E1, E2 |- *.
    rewrite E1, E2, F1, F2. split; ring.
  - intros K. eapply Rle_trans; [apply (nbound_fmul rho _ _ _ _ Hr (iy_bound k) (ie_bound k) K) |].
    pose proof (qprod_le k). pose proof (qprod_pos k). pose proof Y0_nonneg.
    assert (0 <= q ^ (2 ^ k)%nat) by (apply pow_le; lra).
    unfold Rdiv. apply Rmult_le_compat_r; [assumption |]. apply Rmult_le_compat_l; assumption.
Qed.

Theorem inv_invariant (k : nat) (t p : R) :
  feval (ie k) t p = 1 - feval u t p * feval (iy k) t p.
Proof.
  assert (Hu0 : nbound 0 Mu u) by (apply (nbound_mono rho); [exact Hr | exact Hu]).
  assert (Hy00 : nbound 0 Y0 y0) by (apply (nbound_mono rho); [exact Hr | exact Hy0]).
  induction k as [| k IH].
  - unfold iy, ie. simpl.
    rewrite (feval_fsub _ _ 1 (Mu * Y0) t p (nbound_fone 0)
               (nbound_fmul 0 _ _ _ _ (Rle_refl 0) Hu0 Hy00)).
    rewrite feval_fone, (feval_fmul u y0 Mu Y0 t p Hu0 Hy00). ring.
  - assert (Hy : nbound 0 (Y0 * qprod k) (iy k))
      by (apply (nbound_mono rho); [exact Hr | apply iy_bound]).
    assert (He : nbound 0 (q ^ (2 ^ k)%nat) (ie k))
      by (apply (nbound_mono rho); [exact Hr | apply ie_bound]).
    rewrite ie_S, iy_S.
    rewrite (feval_fmul _ _ _ _ t p He He).
    rewrite (feval_fmul _ _ (Y0 * qprod k) (1 + q ^ (2 ^ k)%nat) t p Hy
               (nbound_fadd _ _ _ _ _ (nbound_fone 0) He)).
    rewrite (feval_fadd _ _ 1 (q ^ (2 ^ k)%nat) t p (nbound_fone 0) He), feval_fone.
    rewrite IH. ring.
Qed.

(** * The limit *)

Definition inv_T (N : nat) : R := Y0 / (1 - q) * (q ^ (2 ^ N)%nat / (1 - q)).
Definition inv_eps (N : nat) : R := 2 * inv_T N.

Lemma inv_tail (N L : nat) :
  fsum (fun i => Y0 / (1 - q) * q ^ (2 ^ (N + i))%nat) L <= inv_T N.
Proof.
  unfold inv_T. rewrite fsum_scal.
  apply Rmult_le_compat_l.
  - pose proof Y0_nonneg. apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra].
  - apply qpow_tail. exact Hq.
Qed.

Lemma inv_eps_lim : is_lim_seq inv_eps 0.
Proof.
  unfold inv_eps, inv_T.
  eapply is_lim_seq_ext.
  { intros N. replace (2 * (Y0 / (1 - q) * (q ^ (2 ^ N)%nat / (1 - q))))
      with ((2 * (Y0 / (1 - q)) * / (1 - q)) * q ^ (2 ^ N)%nat) by (field; lra).
    reflexivity. }
  replace 0 with ((2 * (Y0 / (1 - q)) * / (1 - q)) * 0) by ring.
  apply is_lim_seq_mult'; [apply is_lim_seq_const | apply qpow_lim, Hq].
Qed.

Lemma inv_cauchy (N n m : nat) :
  (N <= n)%nat -> (N <= m)%nat -> nbound rho (inv_eps N) (fsub (iy n) (iy m)).
Proof.
  intros Hn Hm. unfold inv_eps.
  apply (steps_cauchy rho iy (fun k => Y0 / (1 - q) * q ^ (2 ^ k)%nat) iy_step inv_T inv_tail);
    assumption.
Qed.

Definition finv : fser := flim iy.

Theorem nbound_finv_sub : nbound rho (inv_eps 0) (fsub y0 finv).
Proof.
  apply (nbound_flim_sub rho Hr iy inv_eps inv_eps_lim inv_cauchy 0 0 (le_n 0)).
Qed.

Theorem nbound_finv : nbound rho (Y0 + inv_eps 0) finv.
Proof.
  apply (nbound_flim rho Hr iy inv_eps inv_eps_lim inv_cauchy 0 Y0). exact Hy0.
Qed.

Theorem feval_finv (t p : R) : feval u t p * feval finv t p = 1.
Proof.
  pose proof (feval_flim rho Hr iy inv_eps inv_eps_lim inv_cauchy t p 0 Y0 Hy0) as Hlim.
  fold finv in Hlim.
  (* u y_k = 1 - e_k, and e_k falls to zero *)
  assert (He : is_lim_seq (fun k => feval (ie k) t p) 0).
  { apply (is_lim_seq_le_le (fun k => - q ^ (2 ^ k)%nat) (fun k => feval (ie k) t p)
                            (fun k => q ^ (2 ^ k)%nat)).
    - intros k. pose proof (feval_bound (ie k) (q ^ (2 ^ k)%nat) t p
                              (nbound_mono rho 0 _ _ Hr (ie_bound k))) as B.
      apply Rabs_le_between in B. exact B.
    - replace 0 with (-1 * 0) by ring.
      apply (is_lim_seq_ext (fun k => -1 * q ^ (2 ^ k)%nat)); [intros k; ring |].
      apply is_lim_seq_mult'; [apply is_lim_seq_const | apply qpow_lim, Hq].
    - apply qpow_lim, Hq. }
  assert (H1 : is_lim_seq (fun k => feval u t p * feval (iy k) t p) (feval u t p * feval finv t p)).
  { apply is_lim_seq_mult'; [apply is_lim_seq_const | exact Hlim]. }
  assert (H2 : is_lim_seq (fun k => feval u t p * feval (iy k) t p) 1).
  { assert (H2' : is_lim_seq (fun k => 1 - feval (ie k) t p) (1 - 0)).
    { apply is_lim_seq_minus'; [apply is_lim_seq_const | exact He]. }
    rewrite Rminus_0_r in H2'.
    apply (is_lim_seq_ext (fun k => 1 - feval (ie k) t p)); [| exact H2'].
    intros k. rewrite (inv_invariant k t p). ring. }
  pose proof (is_lim_seq_unique _ _ H1) as U1. pose proof (is_lim_seq_unique _ _ H2) as U2.
  rewrite U1 in U2. injection U2. auto.
Qed.

End Inverse.
