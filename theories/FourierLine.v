(** The derivative of a Fourier family along a line of the torus.

    A family with a finite norm on a strip of positive width is differentiable
    along every line (t0 + a y, p0 + b y) of the torus, and its derivative
    there is a d_t u + b d_p u, the family [lder a b u] ([feval_line]). The
    proof is that of FourierEval.feval_dt: the partial sums and the partial
    sums of their derivatives converge uniformly along the line, the tail
    bound of a family being uniform over the torus. A field line on an
    invariant torus runs along such a line, and this is what makes it a
    solution of the field-line equations. *)

From Coq Require Import ZArith Reals Lra.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierAlg.
Local Open Scope R_scope.

(** The derivative family along the line of direction (a, b). *)
Definition lder (a b : R) (u : fser) : fser := fadd (fscal a (dt u)) (fscal b (dp u)).

Lemma is_derive_term_line (u : fser) (t0 p0 a b y : R) (m n : Z) :
  is_derive (fun z => term u (t0 + a * z) (p0 + b * z) m n) y
    (term (lder a b u) (t0 + a * y) (p0 + b * y) m n).
Proof.
  unfold term, mode, lder, fadd, fscal, dt, dp. simpl.
  auto_derive; [exact I |]. ring.
Qed.

Lemma line_cvu (w : fser) (K t0 p0 a b : R) :
  nbound 0 K w ->
  CVU_dom (fun N y => sqsum (term w (t0 + a * y) (p0 + b * y)) N) (fun _ => True).
Proof.
  intros Hw eps.
  destruct (nbound_cv w K Hw) as [A HA].
  pose proof HA as HA'. apply is_lim_seq_spec in HA'.
  destruct (HA' eps) as [N0 HN0].
  exists N0. intros N HN y _.
  pose proof (feval_tail w K (t0 + a * y) (p0 + b * y) N Hw) as Ht.
  unfold feval, zz_sum in Ht.
  rewrite (is_lim_seq_unique _ _ HA) in Ht. simpl in Ht.
  specialize (HN0 N HN).
  apply Rle_lt_trans with (A - sqsum (nterm 0 w) N); [exact Ht |].
  rewrite Rabs_minus_sym in HN0.
  pose proof (Rle_abs (A - sqsum (nterm 0 w) N)). lra.
Qed.

Lemma nbound_lder (rho M a b : R) (u : fser) :
  0 < rho -> nbound rho M u ->
  nbound 0 (Rabs a * (/ (exp 1 * rho) * M) + Rabs b * (/ kappa * (/ (exp 1 * rho) * M))) (lder a b u).
Proof.
  intros Hr H. unfold lder. apply nbound_fadd; apply nbound_fscal.
  - replace 0 with (rho - rho) by ring. apply nbound_dt; assumption.
  - replace 0 with (rho - rho) by ring. apply nbound_dp; assumption.
Qed.

Theorem feval_line (rho M : R) (u : fser) (t0 p0 a b s : R) :
  0 < rho -> nbound rho M u ->
  is_derive (fun y => feval u (t0 + a * y) (p0 + b * y)) s
    (a * feval (dt u) (t0 + a * s) (p0 + b * s) + b * feval (dp u) (t0 + a * s) (p0 + b * s)).
Proof.
  intros Hr H.
  assert (H0 : nbound 0 M u) by (apply (nbound_mono rho); [lra | exact H]).
  assert (Hdt : nbound 0 (/ (exp 1 * rho) * M) (dt u)).
  { replace 0 with (rho - rho) by ring. apply nbound_dt; assumption. }
  assert (Hdp : nbound 0 (/ kappa * (/ (exp 1 * rho) * M)) (dp u)).
  { replace 0 with (rho - rho) by ring. apply nbound_dp; assumption. }
  pose proof (nbound_lder rho M a b u Hr H) as Hv.
  set (v := lder a b u) in *.
  set (fn := fun N y => sqsum (term u (t0 + a * y) (p0 + b * y)) N).
  assert (Hder : forall N y, is_derive (fn N) y (sqsum (term v (t0 + a * y) (p0 + b * y)) N)).
  { intros N y. unfold fn.
    apply (is_derive_sqsum (fun m n z => term u (t0 + a * z) (p0 + b * z) m n)
                           (fun m n z => term v (t0 + a * z) (p0 + b * z) m n)).
    intros m n. apply is_derive_term_line. }
  assert (HD : forall N y, Derive (fn N) y = sqsum (term v (t0 + a * y) (p0 + b * y)) N).
  { intros N y. apply is_derive_unique, Hder. }
  pose proof (CVU_Derive fn (fun _ => True) open_true
                ltac:(intros a' b' _ _ c _; exact I)
                (line_cvu u M t0 p0 a b H0)
                ltac:(intros N y _; eexists; apply Hder)) as HC.
  assert (Hcont : forall N y, True -> continuity_pt (Derive (fn N)) y).
  { intros N y _.
    apply (continuity_of_derive (fn N) (fun y => sqsum (term v (t0 + a * y) (p0 + b * y)) N)).
    - intros z. apply Hder.
    - intros z. eexists.
      apply (is_derive_sqsum (fun m n y => term v (t0 + a * y) (p0 + b * y) m n)
                             (fun m n y => term (lder a b v) (t0 + a * y) (p0 + b * y) m n)).
      intros m n. apply is_derive_term_line. }
  specialize (HC Hcont).
  assert (Hcvu' : CVU_dom (fun N y => Derive (fn N) y) (fun _ => True)).
  { intros eps. destruct (line_cvu v _ t0 p0 a b Hv eps) as [N0 HN0].
    exists N0. intros N HN y Hy.
    rewrite (Lim_seq_ext (fun n0 => Derive (fn n0) y)
               (fun n0 => sqsum (term v (t0 + a * y) (p0 + b * y)) n0)) by (intros; apply HD).
    rewrite HD. apply HN0; assumption. }
  specialize (HC Hcvu' s I).
  rewrite (Lim_seq_ext (fun n0 => Derive (fn n0) s)
             (fun n0 => sqsum (term v (t0 + a * s) (p0 + b * s)) n0)) in HC by (intros; apply HD).
  assert (Ev : feval v (t0 + a * s) (p0 + b * s)
               = a * feval (dt u) (t0 + a * s) (p0 + b * s) + b * feval (dp u) (t0 + a * s) (p0 + b * s)).
  { unfold v, lder.
    rewrite (feval_fadd _ _ (Rabs a * (/ (exp 1 * rho) * M)) (Rabs b * (/ kappa * (/ (exp 1 * rho) * M))));
      [| apply nbound_fscal, Hdt | apply nbound_fscal, Hdp].
    rewrite (feval_fscal a (dt u) (/ (exp 1 * rho) * M)) by exact Hdt.
    rewrite (feval_fscal b (dp u) (/ kappa * (/ (exp 1 * rho) * M))) by exact Hdp. reflexivity. }
  rewrite <- Ev. exact HC.
Qed.
