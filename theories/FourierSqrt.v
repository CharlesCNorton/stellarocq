(** Inverse square roots of families by Newton's iteration.

    From y0 with e0 = 1 - D y0^2 of norm q < 1 on a strip rho >= 0, the
    iteration y' = y (1 + e/2), e' = 3/4 e^2 + 1/4 e^3 keeps e = 1 - D y^2 at the
    level of the functions ([isq_invariant]); its errors fall as q^(2^k) and its
    steps sum as for the inverse, so the iterates converge to a family [fisqrt]
    with (function of D) (function of fisqrt)^2 = 1 ([feval_fisqrt]), within
    2 |y0| q / (1 - q)^2 of y0 ([nbound_fisqrt_sub]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulLim FourierLim FourierInv.
Local Open Scope R_scope.

Lemma nbound_le (rho M M' : R) (u : fser) : M <= M' -> nbound rho M u -> nbound rho M' u.
Proof. intros H Hu N. eapply Rle_trans; [apply Hu | exact H]. Qed.

Section InvSqrt.

Variables (rho : R) (Hr : 0 <= rho).
Variables (D y0 : fser) (MD Y0 q : R).
Hypothesis HD : nbound rho MD D.
Hypothesis Hy0 : nbound rho Y0 y0.
Hypothesis Hq : 0 <= q < 1.
Hypothesis He0 : nbound rho q (fsub fone (fmul D (fmul y0 y0))).

Definition half_step (y e : fser) : fser := fmul y (fadd fone (fscal (/ 2) e)).
Definition err_step (e : fser) : fser :=
  fadd (fscal (3 / 4) (fmul e e)) (fscal (/ 4) (fmul (fmul e e) e)).

Fixpoint isq_it (k : nat) : fser * fser :=
  match k with
  | O => (y0, fsub fone (fmul D (fmul y0 y0)))
  | S j => let '(y, e) := isq_it j in (half_step y e, err_step e)
  end.

Definition sy (k : nat) : fser := fst (isq_it k).
Definition se (k : nat) : fser := snd (isq_it k).

Lemma sy_S (k : nat) : sy (S k) = half_step (sy k) (se k).
Proof. unfold sy, se. simpl. destruct (isq_it k). reflexivity. Qed.

Lemma se_S (k : nat) : se (S k) = err_step (se k).
Proof. unfold se. simpl. destruct (isq_it k). reflexivity. Qed.

Lemma qpow_le_1 (k : nat) : 0 <= q ^ (2 ^ k)%nat <= 1.
Proof.
  split; [apply pow_le; lra |].
  rewrite <- (pow1 (2 ^ k)). apply pow_incr. lra.
Qed.

Lemma se_bound (k : nat) : nbound rho (q ^ (2 ^ k)%nat) (se k).
Proof.
  induction k as [| k IH].
  - replace (q ^ (2 ^ 0)%nat) with q by (simpl; ring). exact He0.
  - rewrite se_S. unfold err_step.
    set (a := q ^ (2 ^ k)%nat).
    assert (Ha : 0 <= a <= 1) by apply qpow_le_1.
    apply (nbound_le _ (Rabs (3 / 4) * (a * a) + Rabs (/ 4) * (a * a * a))).
    + replace (q ^ (2 ^ S k)%nat) with (a * a) by (unfold a; rewrite <- pow_add; f_equal; simpl; lia).
      rewrite (Rabs_pos_eq (3 / 4)) by lra. rewrite (Rabs_pos_eq (/ 4)) by lra.
      assert (a * a * a <= a * a) by (pose proof (Rmult_le_pos a a (proj1 Ha) (proj1 Ha)); nra).
      lra.
    + apply nbound_fadd; apply nbound_fscal.
      * apply nbound_fmul; assumption.
      * apply nbound_fmul; [exact Hr | apply nbound_fmul; assumption | exact IH].
Qed.

Lemma sy_bound (k : nat) : nbound rho (Y0 * qprod q k) (sy k).
Proof.
  induction k as [| k IH].
  - simpl. rewrite Rmult_1_r. exact Hy0.
  - rewrite sy_S. unfold half_step. simpl qprod. rewrite <- Rmult_assoc.
    apply nbound_fmul; [exact Hr | exact IH |].
    apply (nbound_le _ (1 + Rabs (/ 2) * q ^ (2 ^ k)%nat)).
    + rewrite (Rabs_pos_eq (/ 2)) by lra. pose proof (qpow_le_1 k). lra.
    + apply nbound_fadd; [apply nbound_fone | apply nbound_fscal, se_bound].
Qed.

Lemma Y0_nonneg' : 0 <= Y0.
Proof. apply (nbound_nonneg rho Y0 y0 Hy0). Qed.

Lemma sy_step (k : nat) :
  nbound rho (Y0 / (1 - q) * q ^ (2 ^ k)%nat) (fsub (sy (S k)) (sy k)).
Proof.
  rewrite sy_S. unfold half_step.
  (* y (1 + e/2) - y = y (e/2) *)
  apply (nbound_feq _ _ (fmul (sy k) (fscal (/ 2) (se k)))).
  - pose proof (fmul_fadd_r rho Hr (sy k) fone (fscal (/ 2) (se k)) _ 1 _ (sy_bound k)
                  (nbound_fone rho) (nbound_fscal _ _ (/ 2) _ (se_bound k))) as E.
    pose proof (fmul_fone (sy k)) as F.
    intros a b. destruct (E a b) as [E1 E2]. destruct (F a b) as [F1 F2].
    cbn [fsub fadd fscal fc fs] in E1, E2 |- *.
    rewrite E1, E2, F1, F2. split; ring.
  - apply (nbound_le _ (Y0 * qprod q k * (Rabs (/ 2) * q ^ (2 ^ k)%nat))).
    + rewrite (Rabs_pos_eq (/ 2)) by lra.
      pose proof (qprod_le q Hq k). pose proof (qprod_pos q Hq k). pose proof Y0_nonneg'.
      pose proof (qpow_le_1 k).
      assert (Y0 * qprod q k <= Y0 / (1 - q)) by (unfold Rdiv; apply Rmult_le_compat_l; assumption).
      assert (0 <= Y0 * qprod q k) by (apply Rmult_le_pos; lra).
      nra.
    + apply nbound_fmul; [exact Hr | apply sy_bound | apply nbound_fscal, se_bound].
Qed.

Theorem isq_invariant (k : nat) (t p : R) :
  feval (se k) t p = 1 - feval D t p * (feval (sy k) t p * feval (sy k) t p).
Proof.
  assert (HD0 : nbound 0 MD D) by (apply (nbound_mono rho); [exact Hr | exact HD]).
  assert (Hy00 : nbound 0 Y0 y0) by (apply (nbound_mono rho); [exact Hr | exact Hy0]).
  induction k as [| k IH].
  - unfold sy, se. simpl.
    rewrite (feval_fsub _ _ 1 (MD * (Y0 * Y0)) t p (nbound_fone 0)
               (nbound_fmul 0 _ _ _ _ (Rle_refl 0) HD0 (nbound_fmul 0 _ _ _ _ (Rle_refl 0) Hy00 Hy00))).
    rewrite feval_fone, (feval_fmul D (fmul y0 y0) MD (Y0 * Y0) t p HD0
                           (nbound_fmul 0 _ _ _ _ (Rle_refl 0) Hy00 Hy00)).
    rewrite (feval_fmul y0 y0 Y0 Y0 t p Hy00 Hy00). reflexivity.
  - assert (Hy : nbound 0 (Y0 * qprod q k) (sy k))
      by (apply (nbound_mono rho); [exact Hr | apply sy_bound]).
    set (a := q ^ (2 ^ k)%nat).
    assert (He : nbound 0 a (se k)) by (apply (nbound_mono rho); [exact Hr | apply se_bound]).
    rewrite se_S, sy_S. unfold err_step, half_step.
    rewrite (feval_fadd _ _ (Rabs (3 / 4) * (a * a)) (Rabs (/ 4) * (a * a * a)) t p
               (nbound_fscal _ _ _ _ (nbound_fmul 0 _ _ _ _ (Rle_refl 0) He He))
               (nbound_fscal _ _ _ _ (nbound_fmul 0 _ _ _ _ (Rle_refl 0)
                  (nbound_fmul 0 _ _ _ _ (Rle_refl 0) He He) He))).
    rewrite (feval_fscal _ _ (a * a) t p (nbound_fmul 0 _ _ _ _ (Rle_refl 0) He He)).
    rewrite (feval_fscal _ _ (a * a * a) t p
               (nbound_fmul 0 _ _ _ _ (Rle_refl 0) (nbound_fmul 0 _ _ _ _ (Rle_refl 0) He He) He)).
    rewrite (feval_fmul (fmul (se k) (se k)) (se k) (a * a) a t p
               (nbound_fmul 0 _ _ _ _ (Rle_refl 0) He He) He).
    rewrite !(feval_fmul (se k) (se k) a a t p He He).
    set (Hh := nbound_fadd 0 _ _ _ _ (nbound_fone 0) (nbound_fscal 0 _ (/ 2) _ He)).
    rewrite !(feval_fmul (sy k) (fadd fone (fscal (/ 2) (se k))) _ _ t p Hy Hh).
    rewrite (feval_fadd _ _ 1 (Rabs (/ 2) * a) t p (nbound_fone 0) (nbound_fscal 0 _ (/ 2) _ He)).
    rewrite feval_fone, (feval_fscal _ _ a t p He).
    rewrite IH. field.
Qed.

(** * The limit *)

Lemma isq_cauchy (N n m : nat) :
  (N <= n)%nat -> (N <= m)%nat -> nbound rho (inv_eps Y0 q N) (fsub (sy n) (sy m)).
Proof.
  intros Hn Hm. unfold inv_eps.
  apply (steps_cauchy rho sy (fun k => Y0 / (1 - q) * q ^ (2 ^ k)%nat) sy_step (inv_T Y0 q)
           (inv_tail rho y0 Y0 q Hy0 Hq)); assumption.
Qed.

Definition fisqrt : fser := flim sy.

Theorem nbound_fisqrt_sub : nbound rho (inv_eps Y0 q 0) (fsub y0 fisqrt).
Proof.
  apply (nbound_flim_sub rho Hr sy (inv_eps Y0 q) (inv_eps_lim Y0 q Hq) isq_cauchy 0 0 (le_n 0)).
Qed.

Theorem nbound_fisqrt : nbound rho (Y0 + inv_eps Y0 q 0) fisqrt.
Proof.
  apply (nbound_flim rho Hr sy (inv_eps Y0 q) (inv_eps_lim Y0 q Hq) isq_cauchy 0 Y0). exact Hy0.
Qed.

Theorem feval_fisqrt (t p : R) : feval D t p * (feval fisqrt t p * feval fisqrt t p) = 1.
Proof.
  pose proof (feval_flim rho Hr sy (inv_eps Y0 q) (inv_eps_lim Y0 q Hq) isq_cauchy t p 0 Y0 Hy0)
    as Hlim.
  fold fisqrt in Hlim.
  assert (He : is_lim_seq (fun k => feval (se k) t p) 0).
  { apply (is_lim_seq_le_le (fun k => - q ^ (2 ^ k)%nat) (fun k => feval (se k) t p)
                            (fun k => q ^ (2 ^ k)%nat)).
    - intros k. pose proof (feval_bound (se k) (q ^ (2 ^ k)%nat) t p
                              (nbound_mono rho 0 _ _ Hr (se_bound k))) as B.
      apply Rabs_le_between in B. exact B.
    - replace 0 with (-1 * 0) by ring.
      apply (is_lim_seq_ext (fun k => -1 * q ^ (2 ^ k)%nat)); [intros k; ring |].
      apply is_lim_seq_mult'; [apply is_lim_seq_const | apply qpow_lim, Hq].
    - apply qpow_lim, Hq. }
  assert (H1 : is_lim_seq (fun k => feval D t p * (feval (sy k) t p * feval (sy k) t p))
                          (feval D t p * (feval fisqrt t p * feval fisqrt t p))).
  { apply is_lim_seq_mult'; [apply is_lim_seq_const |]. apply is_lim_seq_mult'; exact Hlim. }
  assert (H2 : is_lim_seq (fun k => feval D t p * (feval (sy k) t p * feval (sy k) t p)) 1).
  { assert (H2' : is_lim_seq (fun k => 1 - feval (se k) t p) (1 - 0)).
    { apply is_lim_seq_minus'; [apply is_lim_seq_const | exact He]. }
    rewrite Rminus_0_r in H2'.
    apply (is_lim_seq_ext (fun k => 1 - feval (se k) t p)); [| exact H2'].
    intros k. rewrite (isq_invariant k t p). ring. }
  pose proof (is_lim_seq_unique _ _ H1) as U1. pose proof (is_lim_seq_unique _ _ H2) as U2.
  rewrite U1 in U2. injection U2. auto.
Qed.

End InvSqrt.
