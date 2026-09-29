(** The checker's field of Landreman's family with iota = 2 is Landreman.v's.

    [Physics.exact_b] builds, for family 0, the field and flux label that the
    outputs [Physics.RExactField 0] and [Physics.RExactFlux 0] compare the
    reconstruction with. [exact_b_iota2] states that, in any environment whose
    bindings hold their values, the four expressions it returns evaluate at a
    point of the analytic domain to [Landreman.B1], [B2], [B3] and [psiL] with
    the semiaxes the two parameter slots carry, the field that
    [Landreman.iota2_force] proves an ideal-MHD equilibrium. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Continuum Landreman.

Local Open Scope R_scope.

Lemma is_negative_false (x : R) : 0 <= x -> is_negative x = false.
Proof.
  intros H. generalize (is_negative_spec x).
  case (is_negative x); [intros Hn; inversion Hn; lra | reflexivity].
Qed.

Lemma exact_b_iota2 (exps : list Z) (bld : builder) (lasym : bool) (K : nat)
    (x y z : expr) (bld' : builder) (Bx By Bz psi : expr) :
  Physics.exact_b exps bld lasym K 0%Z x y z = (bld', (Bx, By, Bz, psi)) ->
  forall E, sound E (b_binds bld') ->
  forall a b xv yv zv : R,
  xeval E (slot_vac exps lasym K 0) = Xreal a ->
  xeval E (slot_vac exps lasym K 1) = Xreal b ->
  xeval E x = Xreal xv -> xeval E y = Xreal yv -> xeval E z = Xreal zv ->
  0 < a -> 0 < b -> 0 < radL a b xv yv zv ->
  xeval E Bx = Xreal (B1 a b xv yv zv) /\ xeval E By = Xreal (B2 a b xv yv zv) /\
  xeval E Bz = Xreal (B3 a b xv yv zv) /\ xeval E psi = Xreal (psiL a b xv yv zv).
Proof.
  unfold Physics.exact_b. intros H. cbv zeta in H. repeat stepH H. cbn [Z.eqb] in H.
  repeat stepH H. injection H as <- <- <- <- <-.
  intros E S ra rb xv yv zv Ha Hb Hx Hy Hz Pa Pb Pr.
  peel.
  pose proof (sL_pos ra rb Pa Pb xv yv zv Pr) as Ps.
  assert (Seq : xv * xv / (ra * ra) + yv * yv / (rb * rb) = sL ra rb xv yv)
    by (unfold sL; field; repeat split; lra).
  assert (Sz : xv * xv / (ra * ra) + yv * yv / (rb * rb) <> 0) by (rewrite Seq; lra).
  assert (Rad : 1 - (1 - (xv * xv / (ra * ra) + yv * yv / (rb * rb)))
                    * (1 - (xv * xv / (ra * ra) + yv * yv / (rb * rb))) - 4 * (zv * zv)
                = radL ra rb xv yv zv)
    by (unfold radL, sL; field; repeat split; lra).
  assert (Rp : 0 <= 1 - (1 - (xv * xv / (ra * ra) + yv * yv / (rb * rb)))
                     * (1 - (xv * xv / (ra * ra) + yv * yv / (rb * rb))) - 4 * (zv * zv))
    by (rewrite Rad; lra).
  assert (Az : ra * ra <> 0) by (apply Rmult_integral_contrapositive_currified; lra).
  assert (Bz0 : rb * rb <> 0) by (apply Rmult_integral_contrapositive_currified; lra).
  unfold psiL, B1, B2, B3, FL.
  unfold Physics.e1, Physics.e2, Physics.e4, Physics.esq in *.
  splits; xcalc;
    cbv [Xbind2 Xbind Xdiv' Xsqrt'];
    repeat match goal with
           | |- context [is_zero ?d] => rewrite (is_zero_false d) by (first [nz | lra])
           | |- context [is_negative ?d] => rewrite (is_negative_false d) by lra
           end;
    rewrite ?Rad, ?Seq; f_equal; field; repeat split; lra.
Qed.
