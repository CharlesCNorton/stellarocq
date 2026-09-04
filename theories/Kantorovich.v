(** From a small residual to a nearby zero, and what stops it here.

    A certificate bounds the residual of a reconstruction. That a true
    equilibrium sits nearby is a different statement, and the step between them
    is Newton-Kantorovich: with a bound on the inverse of the linearized
    operator, an approximate zero has an exact one within a computable
    distance. This file carries that argument in the abstract, so that what is
    missing from the development is one quantity rather than a theory.

    Three parts. The first is the contraction mapping theorem on a closed
    ball, proven from the metric axioms and completeness, both taken as
    hypotheses so that the result applies to whatever space a later
    formalization of the force operator uses. The second is the Newton map: a
    fixed point of x - A F(x) is a zero of F whenever A kills only zero. The
    third is the obstruction, and it is the reason the second cannot be
    applied to VMEC's force operator as it stands.

    The obstruction is not that the inverse bound is unproven. Poloidal
    relabelling is a gauge symmetry, so the residual is constant along a gauge
    orbit, and [kantorovich_is_gauge_fixed] shows that a ball carrying the
    Kantorovich condition meets each orbit at most once. A ball around a
    reconstruction contains its whole orbit, so no such ball exists: the
    argument has to be made on the gauge-fixed quotient, and [lambda_gauge] of
    Identities.v exhibits one exact direction of that orbit. This is a theorem
    about why the naive attempt fails rather than a note saying that it does.

    Nothing here is specific to plasmas, and nothing here is applied to the
    certificates: it is the shape of the missing step, stated so that the
    missing part is exactly the hypothesis [Hkant] at a concrete operator. *)

From Coq Require Import Reals Lra Lia.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The contraction mapping theorem on a closed ball                  *)

Section Contraction.

(** A space with a distance. The axioms are hypotheses rather than a
    structure, so that any concrete space satisfying them can be used. *)
Variable X : Type.
Variable d : X -> X -> R.

Hypothesis d_nonneg : forall x y, 0 <= d x y.
Hypothesis d_refl : forall x, d x x = 0.
Hypothesis d_eq : forall x y, d x y = 0 -> x = y.
Hypothesis d_sym : forall x y, d x y = d y x.
Hypothesis d_tri : forall x y z, d x z <= d x y + d y z.

(** The map, the centre of the ball, the contraction factor and the radius. *)
Variable G : X -> X.
Variable x0 : X.
Variable k r : R.

Hypothesis Hk0 : 0 <= k.
Hypothesis Hk1 : k < 1.
Hypothesis Hr : 0 <= r.

(** G contracts on the ball. *)
Hypothesis Hcontract :
  forall x y, d x0 x <= r -> d x0 y <= r -> d (G x) (G y) <= k * d x y.

(** The first step is small enough that the iteration stays in the ball. This
    is the Kantorovich condition: the residual at the starting point, times
    the inverse bound, is at most (1 - k) r. *)
Hypothesis Hsmall : d x0 (G x0) <= (1 - k) * r.

(** The iterates. *)
Fixpoint iter (n : nat) : X :=
  match n with O => x0 | S m => G (iter m) end.

Lemma iter_in_ball : forall n, d x0 (iter n) <= r.
Proof.
  induction n as [|n IH].
  - simpl. rewrite d_refl. exact Hr.
  - simpl.
    apply Rle_trans with (d x0 (G x0) + d (G x0) (G (iter n))).
    { apply d_tri. }
    assert (Hc : d (G x0) (G (iter n)) <= k * d x0 (iter n)).
    { apply Hcontract. rewrite d_refl. exact Hr. exact IH. }
    assert (Hkr : k * d x0 (iter n) <= k * r)
      by (apply Rmult_le_compat_l; assumption).
    lra.
Qed.

(** Successive iterates are a geometric sequence apart. *)
Lemma iter_step :
  forall n, d (iter n) (iter (S n)) <= k ^ n * d x0 (G x0).
Proof.
  induction n as [|n IH].
  - simpl. lra.
  - change (iter (S n)) with (G (iter n)) at 1.
    change (iter (S (S n))) with (G (iter (S n))).
    apply Rle_trans with (k * d (iter n) (iter (S n))).
    { apply Hcontract; apply iter_in_ball. }
    apply Rle_trans with (k * (k ^ n * d x0 (G x0))).
    { apply Rmult_le_compat_l; assumption. }
    simpl. lra.
Qed.

(** So the iterates are Cauchy, with the usual geometric tail. *)
Lemma iter_close :
  forall p n,
  d (iter n) (iter (n + p)) <= (k ^ n - k ^ (n + p)) / (1 - k) * d x0 (G x0).
Proof.
  assert (Hd0 : 0 <= d x0 (G x0)) by apply d_nonneg.
  assert (H1k : 0 < 1 - k) by lra.
  induction p as [|p IH]; intros n.
  - rewrite Nat.add_0_r, d_refl.
    replace (k ^ n - k ^ n) with 0 by ring.
    unfold Rdiv. rewrite Rmult_0_l, Rmult_0_l. apply Rle_refl.
  - replace (n + S p)%nat with (S (n + p)) by lia.
    apply Rle_trans with (d (iter n) (iter (n + p))
                          + d (iter (n + p)) (iter (S (n + p)))).
    { apply d_tri. }
    assert (Hstep := iter_step (n + p)).
    assert (Hpow : 0 <= k ^ (n + p)) by (apply pow_le; exact Hk0).
    apply Rle_trans with ((k ^ n - k ^ (n + p)) / (1 - k) * d x0 (G x0)
                          + k ^ (n + p) * d x0 (G x0)).
    { apply Rplus_le_compat. apply IH. exact Hstep. }
    (* the two geometric pieces add to the next one *)
    replace (k ^ S (n + p)) with (k * k ^ (n + p)) by (simpl; ring).
    apply Rle_trans with
      (((k ^ n - k ^ (n + p)) + (1 - k) * k ^ (n + p)) / (1 - k)
       * d x0 (G x0)).
    { right. field. lra. }
    right. f_equal. field. lra.
Qed.

(** Completeness of the ball, as a hypothesis: a Cauchy sequence inside it
    converges inside it. Any complete space supplies this. *)
Hypothesis Hcomplete :
  forall u : nat -> X,
  (forall n, d x0 (u n) <= r) ->
  (forall eps, 0 < eps ->
     exists N, forall m n, (N <= m)%nat -> (N <= n)%nat -> d (u m) (u n) < eps) ->
  exists x, d x0 x <= r /\
    forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> d x (iter n) < eps.

(** The iterates are Cauchy. *)
Lemma iter_cauchy :
  forall eps, 0 < eps ->
  exists N, forall m n, (N <= m)%nat -> (N <= n)%nat -> d (iter m) (iter n) < eps.
Proof.
  intros eps Heps.
  assert (Hd0 : 0 <= d x0 (G x0)) by apply d_nonneg.
  assert (H1k : 0 < 1 - k) by lra.
  (* choose N so that k^N is small enough for the whole tail *)
  set (c := (d x0 (G x0) + 1) / (1 - k)).
  assert (Hc : 0 < c) by (unfold c; apply Rdiv_lt_0_compat; lra).
  destruct (pow_lt_1_zero k ltac:(rewrite Rabs_right; lra) (eps / c)
              ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  exists N.
  assert (Hhalf : forall m n, (N <= n)%nat -> (n <= m)%nat ->
            d (iter n) (iter m) < eps).
  { intros m n Hn Hnm.
    destruct (Nat.le_exists_sub n m Hnm) as [p [Hp _]].
    assert (Hm : m = (n + p)%nat) by lia.
    clear Hp. rewrite Hm. clear Hm.
    apply Rle_lt_trans with ((k ^ n - k ^ (n + p)) / (1 - k) * d x0 (G x0)).
    { apply iter_close. }
    assert (Hpow : 0 <= k ^ (n + p)) by (apply pow_le; exact Hk0).
    assert (Hkn0 : 0 <= k ^ n) by (apply pow_le; exact Hk0).
    assert (Hkn : Rabs (k ^ n) < eps / c) by (apply HN; lia).
    rewrite Rabs_right in Hkn by (now apply Rle_ge).
    (* drop the tail, then pay one more unit of first step so that the
       constant does not depend on it *)
    apply Rle_lt_trans with (k ^ n * c).
    { apply Rle_trans with (k ^ n / (1 - k) * d x0 (G x0)).
      - apply Rmult_le_compat_r. exact Hd0.
        apply Rmult_le_compat_r. left. apply Rinv_0_lt_compat. lra. lra.
      - apply Rle_trans with (k ^ n / (1 - k) * (d x0 (G x0) + 1)).
        + apply Rmult_le_compat_l.
          * apply Rmult_le_pos. exact Hkn0.
            left. apply Rinv_0_lt_compat. lra.
          * lra.
        + unfold c. right. field. lra. }
    apply Rlt_le_trans with (eps / c * c).
    { apply Rmult_lt_compat_r. exact Hc. exact Hkn. }
    right. field. lra. }
  intros m n Hm Hn.
  destruct (Nat.le_ge_cases n m) as [Hle|Hge].
  - apply Rlt_le_trans with eps. rewrite d_sym. now apply Hhalf. apply Rle_refl.
  - now apply Hhalf.
Qed.

(** The fixed point exists in the ball. *)
Theorem contraction_fixed_point :
  exists x, d x0 x <= r /\ G x = x.
Proof.
  destruct (Hcomplete iter iter_in_ball iter_cauchy) as [x [Hx Hlim]].
  exists x. split. exact Hx.
  apply d_eq.
  (* the distance from G x to x is below every positive number *)
  assert (Hall : forall eps, 0 < eps -> d (G x) x < eps).
  { intros eps Heps.
    set (e2 := eps / 2 / (k + 1)).
    assert (He2 : 0 < e2) by (unfold e2; apply Rdiv_lt_0_compat; lra).
    destruct (Hlim e2 He2) as [N1 H1].
    destruct (Hlim (eps / 2) ltac:(lra)) as [N2 H2].
    set (n := Nat.max N1 N2).
    assert (Hn1 : (N1 <= n)%nat) by (unfold n; lia).
    assert (Hn2 : (N2 <= S n)%nat) by (unfold n; lia).
    apply Rle_lt_trans with (d (G x) (G (iter n)) + d (G (iter n)) x).
    { apply d_tri. }
    assert (Hc : d (G x) (G (iter n)) <= k * d x (iter n)).
    { apply Hcontract. exact Hx. apply iter_in_ball. }
    assert (Hx1 : d x (iter n) < e2) by (apply H1; lia).
    assert (Hx2 : d x (iter (S n)) < eps / 2) by (apply H2; lia).
    change (G (iter n)) with (iter (S n)) in *.
    rewrite (d_sym (iter (S n)) x).
    assert (Hke2 : k * d x (iter n) <= k * e2).
    { apply Rmult_le_compat_l. exact Hk0. lra. }
    assert (He2b : k * e2 < eps / 2).
    { unfold e2.
      apply Rlt_le_trans with ((k + 1) * (eps / 2 / (k + 1))).
      - apply Rmult_lt_compat_r. exact He2. lra.
      - right. field. lra. }
    lra. }
  destruct (Rle_lt_or_eq_dec 0 (d (G x) x) (d_nonneg _ _)) as [Hlt|Heq].
  - exfalso. specialize (Hall (d (G x) x) Hlt). lra.
  - now symmetry.
Qed.

End Contraction.

(* ---------------------------------------------------------------- *)
(* The Newton map                                                    *)

Section Newton.

(** A space with subtraction, a norm and an approximate inverse. The algebra
    is hypotheses for the same reason the metric was. *)
Variable X : Type.
Variable sub : X -> X -> X.
Variable norm : X -> R.
Variable zero : X.

Hypothesis sub_self : forall x, sub x x = zero.
Hypothesis sub_zero_r : forall x, sub x zero = x.
Hypothesis sub_eq_zero : forall x y, sub x y = zero -> x = y.
Hypothesis sub_eq_self : forall x y, sub x y = x -> y = zero.
Hypothesis norm_nonneg : forall x, 0 <= norm x.
Hypothesis norm_zero : forall x, norm x = 0 -> x = zero.

(** The operator whose zero is wanted, and the approximate inverse of its
    linearization. *)
Variable F A : X -> X.
Hypothesis A_zero : A zero = zero.
Hypothesis A_only_zero : forall y, A y = zero -> y = zero.

(** The Newton map. *)
Definition newton (x : X) : X := sub x (A (F x)).

(** A fixed point of it is a zero of F, which is the whole point of the
    construction: the fixed point the contraction gives is an equilibrium and
    not merely a nearby point. *)
Theorem newton_fixed_is_zero :
  forall x, newton x = x -> F x = zero.
Proof.
  intros x Hfix. unfold newton in Hfix.
  apply A_only_zero. now apply (sub_eq_self x).
Qed.

(* ---------------------------------------------------------------- *)
(* The gauge obstruction                                             *)

(** The Kantorovich condition in affine covariant form, on a ball: the Newton
    correction reproduces the difference of two points to within k of it.
    This is what a bound on the inverse of the linearization buys, and it is
    the hypothesis the development does not have at VMEC's force operator. *)
Variable x0 : X.
Variable k r : R.
Hypothesis Hk1 : k < 1.

Definition in_ball (x : X) : Prop := norm (sub x0 x) <= r.

Hypothesis Hkant :
  forall x y, in_ball x -> in_ball y ->
  norm (sub (sub y x) (A (sub (F y) (F x)))) <= k * norm (sub y x).

(** Two points of the ball with the same residual are the same point.

    That is the obstruction. A gauge symmetry leaves the residual unchanged,
    so a ball carrying this condition meets each gauge orbit at most once. A
    ball around a reconstruction contains a whole neighbourhood of it, and so
    contains nearby points of its orbit, so no such ball exists and the
    argument cannot be made where it is wanted. It has to be made on the
    quotient by the gauge action, where the orbit is a point. *)
Theorem kantorovich_is_gauge_fixed :
  forall x y, in_ball x -> in_ball y -> F y = F x -> y = x.
Proof.
  intros x y Hx Hy Heq.
  assert (H := Hkant x y Hx Hy).
  rewrite Heq, sub_self, A_zero, sub_zero_r in H.
  assert (Hn := norm_nonneg (sub y x)).
  assert (Hz : norm (sub y x) = 0) by nra.
  apply sub_eq_zero. now apply norm_zero.
Qed.

(** Read at a gauge transformation: on such a ball the gauge is already
    fixed, since a transformation that moves a point of the ball to another
    point of the ball does not move it at all. *)
Corollary gauge_is_fixed_on_the_ball :
  forall (act : X -> X),
  (forall x, F (act x) = F x) ->
  forall x, in_ball x -> in_ball (act x) -> act x = x.
Proof.
  intros act Hinv x Hx Hax.
  apply (kantorovich_is_gauge_fixed x (act x) Hx Hax). apply Hinv.
Qed.

End Newton.
