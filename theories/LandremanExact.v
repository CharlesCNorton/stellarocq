(** The checker's fields of Landreman's two families are Landreman.v's and
    LandremanSheared.v's.

    [Physics.exact_b] builds, for family 0, the field and flux label that the
    outputs [Physics.RExactField 0] and [Physics.RExactFlux 0] compare the
    reconstruction with. [exact_b_iota2] states that, in any environment whose
    bindings hold their values, the four expressions it returns evaluate at a
    point of the analytic domain to [Landreman.B1], [B2], [B3] and [psiL] with
    the semiaxes the two parameter slots carry, the field that
    [Landreman.iota2_force] proves an ideal-MHD equilibrium. [exact_b_sheared]
    states the same for family 1, with eps, S and lambda in the three slots,
    of [LandremanSheared.B1S], [B2S], [B3S] and [psiS], the field that
    [LandremanSheared.sheared_force] proves an ideal-MHD equilibrium. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Continuum Landreman LandremanSheared.

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

(** The family test of [Physics.exact_b], rewritten rather than reduced: the
    kernel then never compares the test with the chain of bindings after it. *)
Lemma eqb_1_0 : Z.eqb 1 0 = false.
Proof. reflexivity. Qed.

(** One binding of the sheared family's builder whose operands all have real
    values: its value, with every function of LandremanSheared.v that it
    spells out folded back into that function. *)
Ltac sheared_step E ev Sv lv xv yv zv :=
  match goal with
  | V : xeval E ?v = xeval E ?e |- _ =>
      let T := fresh "W" in
      pose proof V as T; cbn [xeval] in T;
      repeat match type of T with
             | context [xeval E ?w] =>
                 match goal with W : xeval E w = Xreal _ |- _ => rewrite W in T end
             end;
      lazymatch type of T with
      | _ = ?rhs => lazymatch rhs with context [xeval E _] => fail | _ => idtac end
      end;
      cbv [Xbind2 Xbind Xdiv' Xsqrt'] in T;
      repeat (match type of T with
              | context [is_zero ?d] => rewrite (is_zero_false d) in T by nz
              | context [is_negative ?d] => rewrite (is_negative_false d) in T by lra
              end; cbv beta iota zeta in T);
      fold (rsq xv yv) (Tre ev xv yv) (Tim ev xv yv) (Tab ev xv yv) (mre ev xv yv)
           (mim ev xv yv) (Kre ev xv yv) (Kim ev xv yv) (Xre ev Sv xv yv) (Xim ev xv yv)
           (chX ev xv yv) (shX ev xv yv) (sre ev Sv xv yv) (sim ev Sv xv yv)
           (cre ev Sv xv yv) (cim ev Sv xv yv) (Kn2 ev xv yv) (Wre ev Sv xv yv)
           (Wim ev Sv xv yv) (Pz ev Sv lv xv yv zv) (B1S ev Sv lv xv yv zv)
           (B2S ev Sv lv xv yv zv) (B3S ev Sv lv xv yv zv) (psiS ev Sv lv xv yv zv) in T;
      clear V
  end.

Lemma exact_b_sheared (exps : list Z) (bld : builder) (lasym : bool) (K : nat)
    (x y z : expr) (bld' : builder) (Bx By Bz psi : expr) :
  Physics.exact_b exps bld lasym K 1%Z x y z = (bld', (Bx, By, Bz, psi)) ->
  forall E, sound E (b_binds bld') ->
  forall eps S lam xv yv zv : R,
  xeval E (slot_vac exps lasym K 0) = Xreal eps ->
  xeval E (slot_vac exps lasym K 1) = Xreal S ->
  xeval E (slot_vac exps lasym K 2) = Xreal lam ->
  xeval E x = Xreal xv -> xeval E y = Xreal yv -> xeval E z = Xreal zv ->
  0 < eps -> 0 < lam -> DomS eps xv yv ->
  xeval E Bx = Xreal (B1S eps S lam xv yv zv) /\ xeval E By = Xreal (B2S eps S lam xv yv zv) /\
  xeval E Bz = Xreal (B3S eps S lam xv yv zv) /\ xeval E psi = Xreal (psiS eps S lam xv yv zv).
Proof.
  unfold Physics.exact_b. intros H. cbv zeta in H. repeat stepH H.
  rewrite eqb_1_0 in H. cbv iota in H.
  repeat stepH H. injection H as <- <- <- <- <-.
  intros E Sd ev Sv lv xv yv zv He Hs Hl Hx Hy Hz Pe Pl D.
  peel.
  pose proof (rsq_pos ev Pe xv yv D) as F1. pose proof (Tsum_pos ev Pe xv yv D) as F2.
  pose proof (mre_pos ev Pe xv yv D) as F3. pose proof (T2_pos ev Pe xv yv D) as F4.
  assert (F5 : 0 < Kn2 ev xv yv) by (unfold Kn2; pose proof (Kn_pos ev Pe xv yv D); lra).
  unfold Physics.e1, Physics.e2, Physics.esq in *.
  repeat sheared_step E ev Sv lv xv yv zv.
  splits; assumption.
Qed.
