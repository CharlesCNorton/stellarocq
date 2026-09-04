(** Symbolic differentiation of expressions, with its soundness over extended
    reals.

    [deriv dvar e] is the derivative of e with respect to a parameter t on
    which the environment depends; [dvar k] is the expression giving the
    t-derivative of environment slot k. The lemma [xderive_deriv] states
    the chain rule: whenever every slot's derivative is given by [dvar],
    the value of [deriv e] is a derivative of the value of e, in the
    extended-real sense of CoqInterval ([Xderive_pt]), which makes a NaN
    derivative value a vacuous claim and a real one a claim that the value
    is real and differentiable with that derivative.

    [with_derivs] doubles a binding list with the derivative of each
    binding, stored in a slot shifted by delta, and [inv_bindings] states
    that after the doubled bindings every derivative slot holds a
    derivative of its value slot along the varied input slot. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive.
From Interval Require Import Interval.Interval.
From Stellarocq Require Import Expr.

Import ListNotations.

(* ---------------------------------------------------------------- *)
(* Xderive_pt depends on the function's real values only             *)

(** Two functions equal on real arguments have the same derivatives at
    real points. *)
Lemma Xderive_pt_ext_real :
  forall (f g : ExtendedR -> ExtendedR) r y',
  (forall t, f (Xreal t) = g (Xreal t)) ->
  Xderive_pt f (Xreal r) y' ->
  Xderive_pt g (Xreal r) y'.
Proof.
  intros f g r y' Hfg Hd.
  unfold Xderive_pt in *.
  destruct y' as [|d]. exact I.
  rewrite <- Hfg.
  destruct (f (Xreal r)) as [|fr]. exact Hd.
  intros v.
  specialize (Hd v).
  intros eps Heps.
  destruct (Hd eps Heps) as [delta Hdelta].
  exists delta.
  intros h Hh Hhd.
  unfold proj_fun.
  rewrite <- !Hfg.
  exact (Hdelta h Hh Hhd).
Qed.

(** A NaN derivative value is a vacuous claim at a real point. *)
Lemma Xderive_pt_nan :
  forall (f : ExtendedR -> ExtendedR) r, Xderive_pt f (Xreal r) Xnan.
Proof. intros f r. exact I. Qed.

(** The square of an extended real is its product with itself. Xsqr lifts
    Rsqr through one match and Xmul matches both arguments, so the two are
    equal but not convertible, and the atan derivative rule needs the
    equation to reach the product form the expression language has. *)
Lemma Xsqr_mul : forall y, Xsqr y = Xmul y y.
Proof. intros [|y]; reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* Variables of an expression                                        *)

(** True when slot n does not occur in e. *)
Fixpoint var_free (n : nat) (e : expr) : bool :=
  match e with
  | Evar k     => negb (Nat.eqb k n)
  | EfromZ _   => true
  | Epi        => true
  | Eneg a     => var_free n a
  | Eadd a b   => var_free n a && var_free n b
  | Esub a b   => var_free n a && var_free n b
  | Emul a b   => var_free n a && var_free n b
  | Ediv a b   => var_free n a && var_free n b
  | Esqrt a    => var_free n a
  | Esin a     => var_free n a
  | Ecos a     => var_free n a
  | Eexp a     => var_free n a
  | Eatan a    => var_free n a
  | Epow2 _    => true
  end.

(** True when every slot occurring in e is below n. *)
Fixpoint vars_below (n : nat) (e : expr) : bool :=
  match e with
  | Evar k     => Nat.ltb k n
  | EfromZ _   => true
  | Epi        => true
  | Eneg a     => vars_below n a
  | Eadd a b   => vars_below n a && vars_below n b
  | Esub a b   => vars_below n a && vars_below n b
  | Emul a b   => vars_below n a && vars_below n b
  | Ediv a b   => vars_below n a && vars_below n b
  | Esqrt a    => vars_below n a
  | Esin a     => vars_below n a
  | Ecos a     => vars_below n a
  | Eexp a     => vars_below n a
  | Eatan a    => vars_below n a
  | Epow2 _    => true
  end.

(** A slot at or above the bound of an expression does not occur in it. *)
Lemma vars_below_free :
  forall n m e, vars_below n e = true -> n <= m -> var_free m e = true.
Proof.
  intros n m e Hb Hnm.
  induction e; simpl in *;
    try (apply andb_prop in Hb; destruct Hb as [H1 H2]);
    try (rewrite IHe by assumption);
    try (rewrite IHe1 by assumption);
    try (rewrite IHe2 by assumption);
    try reflexivity.
  apply Nat.ltb_lt in Hb.
  apply negb_true_iff, Nat.eqb_neq. lia.
Qed.

(** Updating a slot that does not occur in e leaves its value unchanged. *)
Lemma xeval_eset_free :
  forall n e env v,
  var_free n e = true ->
  xeval (eset n env v) e = xeval env e.
Proof.
  intros n e.
  induction e; intros env v Hf; simpl in *;
    try (apply andb_prop in Hf; destruct Hf as [Ha Hb]);
    try (rewrite IHe by assumption);
    try (rewrite IHe1 by assumption);
    try (rewrite IHe2 by assumption);
    try reflexivity.
  apply negb_true_iff, Nat.eqb_neq in Hf.
  now apply eget_eset_neq.
Qed.

(* ---------------------------------------------------------------- *)
(* The derivative expression                                         *)

Section Deriv.

(** Expression giving the t-derivative of environment slot k. *)
Variable dvar : nat -> expr.

(** Symbolic derivative of e with respect to the parameter t. *)
Fixpoint deriv (e : expr) : expr :=
  match e with
  | Evar n     => dvar n
  | EfromZ _   => EfromZ 0
  | Epi        => EfromZ 0
  | Eneg a     => Eneg (deriv a)
  | Eadd a b   => Eadd (deriv a) (deriv b)
  | Esub a b   => Esub (deriv a) (deriv b)
  | Emul a b   => Eadd (Emul (deriv a) b) (Emul (deriv b) a)
  | Ediv a b   => Ediv (Esub (Emul (deriv a) b) (Emul (deriv b) a)) (Emul b b)
  | Esqrt a    => Ediv (deriv a) (Eadd (Esqrt a) (Esqrt a))
  | Esin a     => Emul (deriv a) (Ecos a)
  | Ecos a     => Emul (deriv a) (Eneg (Esin a))
  | Eexp a     => Emul (deriv a) (Eexp a)
  | Eatan a    => Ediv (deriv a) (Eadd (EfromZ 1) (Emul a a))
  | Epow2 _    => EfromZ 0
  end.

(** The slots of [deriv e] are those of e and those of their dvar images:
    when e is over slots below n, slot m at or above n is absent from
    [deriv e] as soon as it is absent from every dvar k with k < n. *)
Lemma var_free_deriv :
  forall m n e,
  vars_below n e = true -> n <= m ->
  (forall k, k < n -> var_free m (dvar k) = true) ->
  var_free m (deriv e) = true.
Proof.
  intros m n e Hb Hnm Hd.
  induction e; simpl in *;
    try (apply andb_prop in Hb; destruct Hb as [H1 H2]);
    try (specialize (IHe Hb)); try (specialize (IHe1 H1));
    try (specialize (IHe2 H2)).
  - apply Hd. now apply Nat.ltb_lt.
  - reflexivity.
  - reflexivity.
  - exact IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2.
  - rewrite IHe1, IHe2.
    now rewrite (vars_below_free n m e1 H1 Hnm), (vars_below_free n m e2 H2 Hnm).
  - rewrite IHe1, IHe2.
    now rewrite (vars_below_free n m e1 H1 Hnm), (vars_below_free n m e2 H2 Hnm).
  - now rewrite IHe, (vars_below_free n m e Hb Hnm).
  - now rewrite IHe, (vars_below_free n m e Hb Hnm).
  - now rewrite IHe, (vars_below_free n m e Hb Hnm).
  - now rewrite IHe, (vars_below_free n m e Hb Hnm).
  - now rewrite IHe, (vars_below_free n m e Hb Hnm).
  - reflexivity.
Qed.

(** The environment as a function of the real parameter t. *)
Variable E : R -> env ExtendedR.

(** The value of e along t, as a function on extended reals. *)
Definition along (e : expr) (T : ExtendedR) : ExtendedR :=
  match T with
  | Xreal t => xeval (E t) e
  | Xnan => Xnan
  end.

(** The value of slot k along t. *)
Definition slot_along (k : nat) (T : ExtendedR) : ExtendedR :=
  match T with
  | Xreal t => eget k (E t) Xnan
  | Xnan => Xnan
  end.

(** Hypothesis: dvar gives the derivative of every slot. *)
Hypothesis Hdvar :
  forall k t, Xderive_pt (slot_along k) (Xreal t) (xeval (E t) (dvar k)).

(** Chain rule: [deriv e] is a derivative of e along t. *)
Lemma xderive_deriv :
  forall e t, Xderive_pt (along e) (Xreal t) (xeval (E t) (deriv e)).
Proof.
  induction e; intros t; simpl deriv.
  - apply (Xderive_pt_ext_real (slot_along n)).
    + intros s. reflexivity.
    + apply Hdvar.
  - apply (Xderive_pt_ext_real (fun _ => Xreal (IZR z))).
    + intros s. reflexivity.
    + change (xeval (E t) (EfromZ 0)) with (Xreal (IZR 0)).
      exact (Xderive_pt_constant (IZR z) (Xreal t)).
  - apply (Xderive_pt_ext_real (fun _ => Xreal PI)).
    + intros s. reflexivity.
    + change (xeval (E t) (EfromZ 0)) with (Xreal (IZR 0)).
      exact (Xderive_pt_constant PI (Xreal t)).
  - apply (Xderive_pt_ext_real (fun T => Xneg (along e T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_neg _ _ _ (IHe t)).
  - apply (Xderive_pt_ext_real (fun T => Xadd (along e1 T) (along e2 T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_add _ _ _ _ _ (IHe1 t) (IHe2 t)).
  - apply (Xderive_pt_ext_real (fun T => Xsub (along e1 T) (along e2 T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_sub _ _ _ _ _ (IHe1 t) (IHe2 t)).
  - apply (Xderive_pt_ext_real (fun T => Xmul (along e1 T) (along e2 T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_mul _ _ _ _ _ (IHe1 t) (IHe2 t)).
  - apply (Xderive_pt_ext_real (fun T => Xdiv (along e1 T) (along e2 T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_div _ _ _ _ _ (IHe1 t) (IHe2 t)).
  - apply (Xderive_pt_ext_real (fun T => Xsqrt (along e T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_sqrt _ _ _ (IHe t)).
  - apply (Xderive_pt_ext_real (fun T => Xsin (along e T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_sin _ _ _ (IHe t)).
  - apply (Xderive_pt_ext_real (fun T => Xcos (along e T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_cos _ _ _ (IHe t)).
  - apply (Xderive_pt_ext_real (fun T => Xexp (along e T))).
    + intros s. reflexivity.
    + exact (Xderive_pt_exp _ _ _ (IHe t)).
  - apply (Xderive_pt_ext_real (fun T => Xatan (along e T))).
    + intros s. reflexivity.
    + assert (H := Xderive_pt_atan (along e) (xeval (E t) (deriv e))
                     (Xreal t) (IHe t)).
      rewrite Xsqr_mul in H.
      exact H.
  - apply (Xderive_pt_ext_real (fun _ => Xreal (powerRZ 2%R z))).
    + intros s. reflexivity.
    + change (xeval (E t) (EfromZ 0)) with (Xreal (IZR 0)).
      exact (Xderive_pt_constant (powerRZ 2%R z) (Xreal t)).
Qed.

End Deriv.

(* ---------------------------------------------------------------- *)
(* Derivatives through a binding list                                *)

Section Bindings.

(** The varied input slot, the first scratch slot, and the offset of the
    derivative slots. Inputs are the slots below base. *)
Variable x base delta : nat.
Hypothesis Hx : x < base.
Hypothesis Hdelta : 0 < delta.

(** The t-derivative of slot k: 1 for the varied input, 0 for the other
    inputs, and the shifted slot for a scratch value. *)
Definition dvar_of (k : nat) : expr :=
  if Nat.eqb k x then EfromZ 1
  else if Nat.ltb k base then EfromZ 0
  else Evar (k + delta).

(** Each binding followed by the binding of its derivative. *)
Definition with_derivs (bs : list binding) : list binding :=
  flat_map (fun b => [b; (fst b + delta, deriv dvar_of (snd b))]) bs.

(** Bindings numbered next, next + 1, ..., each expression over lower
    slots only. *)
Fixpoint well_formed (next : nat) (bs : list binding) : bool :=
  match bs with
  | [] => true
  | (n, e) :: tl => Nat.eqb n next && vars_below n e && well_formed (S next) tl
  end.

(** What holds of the environment along t after the bindings below next:
    every slot's derivative is given by dvar_of, the value slots from next
    on are unset, and so are the derivative slots from next + delta on. *)
Definition inv (F : R -> env ExtendedR) (next : nat) : Prop :=
  (forall k t, Xderive_pt (slot_along F k) (Xreal t) (xeval (F t) (dvar_of k))) /\
  (forall k t, next <= k -> k < base + delta -> eget k (F t) Xnan = Xnan) /\
  (forall k t, next + delta <= k -> eget k (F t) Xnan = Xnan).

(** The invariant only depends on the values of the environment. *)
Lemma inv_ext :
  forall F G m, (forall t, F t = G t) -> inv F m -> inv G m.
Proof.
  intros F G m HFG [Ha [Hb Hc]].
  split; [|split].
  - intros k t. rewrite <- (HFG t).
    apply (Xderive_pt_ext_real (slot_along F k)).
    + intros s. unfold slot_along. now rewrite HFG.
    + apply Ha.
  - intros k t H1 H2. rewrite <- (HFG t). now apply Hb.
  - intros k t H1. rewrite <- (HFG t). now apply Hc.
Qed.

(** dvar_of k mentions no slot other than k + delta, and that one only for a
    scratch slot k. *)
Lemma var_free_dvar_of :
  forall m k, (k < base \/ k + delta <> m) -> var_free m (dvar_of k) = true.
Proof.
  intros m k Hk.
  unfold dvar_of.
  destruct (Nat.eqb k x) eqn:Hkx. reflexivity.
  destruct (Nat.ltb k base) eqn:Hkb. reflexivity.
  apply Nat.ltb_ge in Hkb.
  simpl. apply negb_true_iff, Nat.eqb_neq.
  destruct Hk as [Hk|Hk]. lia. exact Hk.
Qed.

(** The environment after one binding and its derivative binding. *)
Definition two_step (F : R -> env ExtendedR) (n : nat) (e : expr) (t : R)
    : env ExtendedR :=
  xextend (F t) [(n, e); (n + delta, deriv dvar_of e)].

(** Its slots, spelled out. *)
Lemma two_step_eq :
  forall F n e t,
  two_step F n e t =
  eset (n + delta) (eset n (F t) (xeval (F t) e)) (xeval (eset n (F t) (xeval (F t) e)) (deriv dvar_of e)).
Proof. reflexivity. Qed.

(** One binding and its derivative binding preserve the invariant. *)
Lemma inv_step :
  forall F next n e,
  inv F next ->
  n = next -> vars_below n e = true -> base <= n -> n < base + delta ->
  inv (two_step F n e) (S next).
Proof.
  intros F next n e [Ha [Hb Hc]] Hn He Hbn Hnd.
  subst next.
  (* the derivative expression of e mentions neither n nor n + delta *)
  assert (Hfree : forall m, m = n \/ m = n + delta ->
                  var_free m (deriv dvar_of e) = true).
  { intros m Hm.
    apply (var_free_deriv dvar_of m n e He).
    - lia.
    - intros k Hk.
      apply var_free_dvar_of.
      destruct (Nat.lt_ge_cases k base) as [H|H]. now left.
      right. lia. }
  assert (Hd_unch : forall t,
            xeval (eset n (F t) (xeval (F t) e)) (deriv dvar_of e)
            = xeval (F t) (deriv dvar_of e)).
  { intros t. apply xeval_eset_free. apply Hfree. now left. }
  assert (Hval : forall s,
            eget n (two_step F n e s) Xnan = xeval (F s) e).
  { intros s. rewrite two_step_eq.
    rewrite eget_eset_neq by lia.
    now rewrite eget_eset_eq. }
  assert (Hdval : forall s,
            eget (n + delta) (two_step F n e s) Xnan = xeval (F s) (deriv dvar_of e)).
  { intros s. rewrite two_step_eq.
    rewrite eget_eset_eq. apply Hd_unch. }
  assert (Hother : forall k s, k <> n -> k <> n + delta ->
            eget k (two_step F n e s) Xnan = eget k (F s) Xnan).
  { intros k s Hk1 Hk2. rewrite two_step_eq.
    rewrite eget_eset_neq by lia.
    now rewrite eget_eset_neq by lia. }
  split; [|split].
  - (* every slot's derivative is still given by dvar_of *)
    intros k t.
    destruct (Nat.eq_dec k n) as [->|Hkn].
    + (* the new value slot: its derivative is the new derivative slot *)
      assert (Hder : xeval (two_step F n e t) (dvar_of n)
                     = xeval (F t) (deriv dvar_of e)).
      { unfold dvar_of.
        replace (Nat.eqb n x) with false
          by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.ltb n base) with false
          by (symmetry; apply Nat.ltb_ge; lia).
        simpl. apply Hdval. }
      rewrite Hder.
      apply (Xderive_pt_ext_real (along F e)).
      * intros s. unfold slot_along, along. symmetry. apply Hval.
      * apply xderive_deriv. exact Ha.
    + destruct (Nat.eq_dec k (n + delta)) as [->|Hkd].
      * (* the new derivative slot: its own derivative slot is unset *)
        assert (Hnan : xeval (two_step F n e t) (dvar_of (n + delta)) = Xnan).
        { unfold dvar_of.
          replace (Nat.eqb (n + delta) x) with false
            by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.ltb (n + delta) base) with false
            by (symmetry; apply Nat.ltb_ge; lia).
          simpl. rewrite Hother by lia.
          apply Hc. lia. }
        rewrite Hnan. apply Xderive_pt_nan.
      * (* an untouched slot *)
        assert (Hsame : xeval (two_step F n e t) (dvar_of k)
                        = xeval (F t) (dvar_of k)).
        { rewrite two_step_eq.
          rewrite xeval_eset_free.
          - rewrite xeval_eset_free. reflexivity.
            apply var_free_dvar_of.
            destruct (Nat.lt_ge_cases k base) as [H|H]. now left. right. lia.
          - apply var_free_dvar_of.
            destruct (Nat.lt_ge_cases k base) as [H|H]. now left. right. lia. }
        rewrite Hsame.
        apply (Xderive_pt_ext_real (slot_along F k)).
        -- intros s. unfold slot_along. symmetry. now apply Hother.
        -- apply Ha.
  - (* value slots from S n on are unset *)
    intros k t Hk Hkd.
    rewrite Hother by lia.
    apply Hb; lia.
  - (* derivative slots from S n + delta on are unset *)
    intros k t Hk.
    rewrite Hother by lia.
    apply Hc; lia.
Qed.

(** The invariant at the start: the inputs, with slot x set to t. *)
Lemma inv_base :
  forall env0,
  (forall k, base <= k -> eget k env0 Xnan = Xnan) ->
  (forall k, k < base -> exists v, eget k env0 Xnan = Xreal v) ->
  inv (fun t => eset x env0 (Xreal t)) base.
Proof.
  intros env0 Hunset Hreal.
  split; [|split].
  - intros k t.
    unfold dvar_of.
    destruct (Nat.eqb k x) eqn:Hkx.
    + apply Nat.eqb_eq in Hkx. subst k.
      change (xeval (eset x env0 (Xreal t)) (EfromZ 1))
        with (Xreal (IZR 1)).
      apply (Xderive_pt_ext_real (fun T => T)).
      * intros s. unfold slot_along. now rewrite eget_eset_eq.
      * exact (Xderive_pt_identity (Xreal t)).
    + apply Nat.eqb_neq in Hkx.
      destruct (Nat.ltb k base) eqn:Hkb.
      * apply Nat.ltb_lt in Hkb.
        destruct (Hreal k Hkb) as [v Hv].
        change (xeval (eset x env0 (Xreal t)) (EfromZ 0))
          with (Xreal (IZR 0)).
        apply (Xderive_pt_ext_real (fun _ => Xreal v)).
        -- intros s. unfold slot_along.
           rewrite eget_eset_neq by assumption. now rewrite Hv.
        -- exact (Xderive_pt_constant v (Xreal t)).
      * apply Nat.ltb_ge in Hkb.
        simpl.
        rewrite eget_eset_neq by lia.
        rewrite Hunset by lia.
        exact I.
  - intros k2 t2 Hk2 _.
    rewrite eget_eset_neq by lia.
    apply Hunset. lia.
  - intros k2 t2 Hk2.
    rewrite eget_eset_neq by lia.
    apply Hunset. lia.
Qed.

(** Extending along a concatenation is extending twice. *)
Lemma xextend_app :
  forall env l1 l2, xextend env (l1 ++ l2) = xextend (xextend env l1) l2.
Proof.
  intros env l1 l2. unfold xextend. apply fold_left_app.
Qed.

(** Well-formed bindings preserve the invariant, binding by binding. *)
Lemma inv_bindings :
  forall bs F next,
  inv F next ->
  well_formed next bs = true ->
  base <= next ->
  next + length bs <= base + delta ->
  inv (fun t => xextend (F t) (with_derivs bs)) (next + length bs).
Proof.
  induction bs as [|[n e] tl IH]; intros F next Hinv Hwf Hbn Hlen.
  - apply (inv_ext F).
    + intros t. reflexivity.
    + rewrite Nat.add_0_r. exact Hinv.
  - simpl in Hwf.
    apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He].
    apply Nat.eqb_eq in Hn.
    simpl length in Hlen. simpl length.
    replace (next + S (length tl)) with (S next + length tl) by lia.
    assert (Hstep := inv_step F next n e Hinv Hn He
                       ltac:(lia) ltac:(lia)).
    assert (Hrec := IH _ (S next) Hstep Htl ltac:(lia) ltac:(lia)).
    eapply inv_ext.
    2: exact Hrec.
    intros t. cbv beta.
    unfold two_step.
    rewrite <- xextend_app.
    reflexivity.
Qed.

End Bindings.

(* ---------------------------------------------------------------- *)
(* Second derivatives through a binding list                         *)

Section Bindings3.

(** The same varied slot, first scratch slot and offset. Three levels now
    sit above base: the values in [base, base + delta), their first
    derivatives in [base + delta, base + 2 delta), and their second
    derivatives in [base + 2 delta, base + 3 delta). Every scratch slot
    still has its derivative one delta above it, so [dvar_of] is unchanged
    and serves all three levels. *)
Variable x base delta : nat.
Hypothesis Hx : x < base.
Hypothesis Hdelta : 0 < delta.

(** Each binding, then its derivative, then its second derivative. *)
Definition with_derivs2 (bs : list binding) : list binding :=
  flat_map
    (fun b =>
       [b;
        (fst b + delta, deriv (dvar_of x base delta) (snd b));
        (fst b + 2 * delta,
         deriv (dvar_of x base delta)
               (deriv (dvar_of x base delta) (snd b)))])
    bs.

(** The slots of a derivative expression stay below n + delta. *)
Lemma vars_below_deriv :
  forall n e,
  vars_below n e = true ->
  vars_below (n + delta) (deriv (dvar_of x base delta) e) = true.
Proof.
  intros n e Hb.
  assert (Hd : forall k, k < n ->
            vars_below (n + delta) (dvar_of x base delta k) = true).
  { intros k Hk. unfold dvar_of.
    destruct (Nat.eqb k x). reflexivity.
    destruct (Nat.ltb k base). reflexivity.
    simpl. apply Nat.ltb_lt. lia. }
  assert (Hmono : forall m e', vars_below m e' = true -> m <= n + delta ->
            vars_below (n + delta) e' = true).
  { intros m e'. induction e'; simpl; intros H Hm;
      try (apply andb_prop in H; destruct H as [H1 H2]);
      try (rewrite IHe'1 by assumption); try (rewrite IHe'2 by assumption);
      try (rewrite IHe' by assumption); try reflexivity.
    apply Nat.ltb_lt. apply Nat.ltb_lt in H. lia. }
  induction e; simpl in *;
    try (apply andb_prop in Hb; destruct Hb as [H1 H2]);
    try (specialize (IHe Hb)); try (specialize (IHe1 H1));
    try (specialize (IHe2 H2)).
  - apply Hd. now apply Nat.ltb_lt.
  - reflexivity.
  - reflexivity.
  - exact IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2.
  - rewrite IHe1, IHe2.
    now rewrite (Hmono n e1 H1 ltac:(lia)), (Hmono n e2 H2 ltac:(lia)).
  - rewrite IHe1, IHe2.
    now rewrite (Hmono n e1 H1 ltac:(lia)), (Hmono n e2 H2 ltac:(lia)).
  - now rewrite IHe, (Hmono n e Hb ltac:(lia)).
  - now rewrite IHe, (Hmono n e Hb ltac:(lia)).
  - now rewrite IHe, (Hmono n e Hb ltac:(lia)).
  - now rewrite IHe, (Hmono n e Hb ltac:(lia)).
  - now rewrite IHe, (Hmono n e Hb ltac:(lia)).
  - reflexivity.
Qed.


(** A slot that occurs in an expression is below its bound. *)
Lemma vars_below_occ :
  forall n k e, vars_below n e = true -> var_free k e = false -> k < n.
Proof.
  intros n k e Hb Hf.
  destruct (Nat.le_gt_cases n k) as [H|H].
  - rewrite (vars_below_free n k e Hb H) in Hf. discriminate.
  - exact H.
Qed.

(** Freedom in a derivative, from freedom in the expression and in the
    images of the slots that actually occur in it. The bound-based form is
    too weak for a second derivative, whose expression legitimately reads
    the first-derivative slots. *)
Lemma var_free_deriv_occ :
  forall dvar m e,
  var_free m e = true ->
  (forall k, var_free k e = false -> var_free m (dvar k) = true) ->
  var_free m (deriv dvar e) = true.
Proof.
  intros dvar m e. induction e; simpl; intros Hf Hd.
  - apply Hd. simpl. now rewrite Nat.eqb_refl.
  - reflexivity.
  - reflexivity.
  - apply IHe. exact Hf. exact Hd.
  - apply andb_prop in Hf. destruct Hf as [H1 H2].
    assert (D1 : forall k, var_free k e1 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro1. }
    assert (D2 : forall k, var_free k e2 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro2. }
    now rewrite (IHe1 H1 D1), (IHe2 H2 D2).
  - apply andb_prop in Hf. destruct Hf as [H1 H2].
    assert (D1 : forall k, var_free k e1 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro1. }
    assert (D2 : forall k, var_free k e2 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro2. }
    now rewrite (IHe1 H1 D1), (IHe2 H2 D2).
  - apply andb_prop in Hf. destruct Hf as [H1 H2].
    assert (D1 : forall k, var_free k e1 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro1. }
    assert (D2 : forall k, var_free k e2 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro2. }
    now rewrite (IHe1 H1 D1), (IHe2 H2 D2), H1, H2.
  - apply andb_prop in Hf. destruct Hf as [H1 H2].
    assert (D1 : forall k, var_free k e1 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro1. }
    assert (D2 : forall k, var_free k e2 = false -> var_free m (dvar k) = true).
    { intros k Hk. apply Hd. simpl. now apply andb_false_intro2. }
    now rewrite (IHe1 H1 D1), (IHe2 H2 D2), H1, H2.
  - now rewrite (IHe Hf Hd), Hf.
  - now rewrite (IHe Hf Hd), Hf.
  - now rewrite (IHe Hf Hd), Hf.
  - now rewrite (IHe Hf Hd), Hf.
  - now rewrite (IHe Hf Hd), Hf.
  - reflexivity.
Qed.

(** After the bindings below next: every slot's derivative is given by
    dvar_of, and each of the three levels is unset from its own frontier
    on. *)
Definition inv2 (F : R -> env ExtendedR) (next : nat) : Prop :=
  (forall k t, Xderive_pt (slot_along F k) (Xreal t)
                 (xeval (F t) (dvar_of x base delta k))) /\
  (forall k t, next <= k -> k < base + delta -> eget k (F t) Xnan = Xnan) /\
  (forall k t, next + delta <= k -> k < base + 2 * delta ->
     eget k (F t) Xnan = Xnan) /\
  (forall k t, next + 2 * delta <= k -> eget k (F t) Xnan = Xnan).

(** The invariant only depends on the values of the environment. *)
Lemma inv2_ext :
  forall F G m, (forall t, F t = G t) -> inv2 F m -> inv2 G m.
Proof.
  intros F G m HFG [Ha [Hb [Hc Hd]]].
  split; [|split; [|split]].
  - intros k t. rewrite <- (HFG t).
    apply (Xderive_pt_ext_real (slot_along F k)).
    + intros s. unfold slot_along. now rewrite HFG.
    + apply Ha.
  - intros k t H1 H2. rewrite <- (HFG t). now apply Hb.
  - intros k t H1 H2. rewrite <- (HFG t). now apply Hc.
  - intros k t H1. rewrite <- (HFG t). now apply Hd.
Qed.

(** The environment after one binding, its derivative and its second
    derivative. *)
Definition three_step (F : R -> env ExtendedR) (n : nat) (e : expr) (t : R)
    : env ExtendedR :=
  xextend (F t)
    [(n, e);
     (n + delta, deriv (dvar_of x base delta) e);
     (n + 2 * delta,
      deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e))].

(** One binding and its two derivative bindings preserve the invariant. *)
Lemma inv2_step :
  forall F next n e,
  inv2 F next ->
  n = next -> vars_below n e = true -> base <= n -> n < base + delta ->
  inv2 (three_step F n e) (S next).
Proof.
  intros F next n e [Ha [Hb [Hc Hd]]] Hn He Hbn Hnd.
  subst next.
  (* the first derivative expression avoids all three new slots *)
  assert (Hfree1 : forall m, m = n \/ m = n + delta \/ m = n + 2 * delta ->
                   var_free m (deriv (dvar_of x base delta) e) = true).
  { intros m Hm.
    apply (var_free_deriv (dvar_of x base delta) m n e He).
    - lia.
    - intros k Hk. apply (var_free_dvar_of x base delta Hx Hdelta).
      destruct (Nat.lt_ge_cases k base) as [H|H]. now left. right. lia. }
  (* so does the second, since the first mentions no slot at or above
     n + delta and the images of what it does mention land at or above
     base + 2 delta *)
  assert (Hbelow : vars_below (n + delta) (deriv (dvar_of x base delta) e) = true)
    by (apply vars_below_deriv; exact He).
  assert (Hfree2 : forall m, m = n \/ m = n + delta \/ m = n + 2 * delta ->
                   var_free m (deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e)) = true).
  { intros m Hm.
    apply var_free_deriv_occ.
    - apply Hfree1. exact Hm.
    - intros k Hk.
      assert (Hkb : k < n + delta) by exact (vars_below_occ _ _ _ Hbelow Hk).
      assert (Hkn : k <> n).
      { intros ->. rewrite (Hfree1 n ltac:(now left)) in Hk. discriminate. }
      apply (var_free_dvar_of x base delta Hx Hdelta).
      destruct (Nat.lt_ge_cases k base) as [H|H]. now left. right. lia. }
  assert (Hunch1 : forall t,
            xeval (eset n (F t) (xeval (F t) e)) (deriv (dvar_of x base delta) e)
            = xeval (F t) (deriv (dvar_of x base delta) e)).
  { intros t. apply xeval_eset_free. apply Hfree1. now left. }
  set (E1 := fun t => eset n (F t) (xeval (F t) e)).
  set (E2 := fun t => eset (n + delta) (E1 t) (xeval (E1 t) (deriv (dvar_of x base delta) e))).
  assert (Hunch2 : forall t,
            xeval (E2 t) (deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e)) = xeval (F t) (deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e))).
  { intros t. unfold E2, E1.
    rewrite xeval_eset_free by (apply Hfree2; right; now left).
    rewrite xeval_eset_free by (apply Hfree2; now left).
    reflexivity. }
  assert (Hstep : forall t, three_step F n e t
            = eset (n + 2 * delta) (E2 t) (xeval (E2 t) (deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e)))).
  { intros t. reflexivity. }
  assert (Hval : forall t, eget n (three_step F n e t) Xnan = xeval (F t) e).
  { intros t. rewrite Hstep.
    rewrite eget_eset_neq by lia. unfold E2.
    rewrite eget_eset_neq by lia. unfold E1.
    now rewrite eget_eset_eq. }
  assert (Hd1 : forall t, eget (n + delta) (three_step F n e t) Xnan
                  = xeval (F t) (deriv (dvar_of x base delta) e)).
  { intros t. rewrite Hstep.
    rewrite eget_eset_neq by lia. unfold E2.
    rewrite eget_eset_eq. unfold E1. apply Hunch1. }
  assert (Hd2 : forall t, eget (n + 2 * delta) (three_step F n e t) Xnan
                  = xeval (F t) (deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e))).
  { intros t. rewrite Hstep. rewrite eget_eset_eq. apply Hunch2. }
  assert (Hother : forall k t, k <> n -> k <> n + delta -> k <> n + 2 * delta ->
            eget k (three_step F n e t) Xnan = eget k (F t) Xnan).
  { intros k t H1 H2 H3. rewrite Hstep.
    rewrite eget_eset_neq by lia. unfold E2.
    rewrite eget_eset_neq by lia. unfold E1.
    now rewrite eget_eset_neq by lia. }
  split; [|split; [|split]].
  - intros k t.
    destruct (Nat.eq_dec k n) as [->|Hkn].
    + assert (Hder : xeval (three_step F n e t) ((dvar_of x base delta) n) = xeval (F t) (deriv (dvar_of x base delta) e)).
      { unfold dvar_of.
        replace (Nat.eqb n x) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.ltb n base) with false by (symmetry; apply Nat.ltb_ge; lia).
        simpl. apply Hd1. }
      rewrite Hder.
      apply (Xderive_pt_ext_real (along F e)).
      * intros s. unfold slot_along, along. symmetry. apply Hval.
      * apply xderive_deriv. exact Ha.
    + destruct (Nat.eq_dec k (n + delta)) as [->|Hkd].
      * assert (Hder : xeval (three_step F n e t) ((dvar_of x base delta) (n + delta))
                       = xeval (F t) (deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e))).
        { unfold dvar_of.
          replace (Nat.eqb (n + delta) x) with false
            by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.ltb (n + delta) base) with false
            by (symmetry; apply Nat.ltb_ge; lia).
          simpl. replace (n + delta + delta) with (n + 2 * delta) by lia.
          apply Hd2. }
        rewrite Hder.
        apply (Xderive_pt_ext_real (along F (deriv (dvar_of x base delta) e))).
        -- intros s. unfold slot_along, along. symmetry. apply Hd1.
        -- apply xderive_deriv. exact Ha.
      * destruct (Nat.eq_dec k (n + 2 * delta)) as [->|Hkd2].
        -- assert (Hnan : xeval (three_step F n e t) ((dvar_of x base delta) (n + 2 * delta)) = Xnan).
           { unfold dvar_of.
             replace (Nat.eqb (n + 2 * delta) x) with false
               by (symmetry; apply Nat.eqb_neq; lia).
             replace (Nat.ltb (n + 2 * delta) base) with false
               by (symmetry; apply Nat.ltb_ge; lia).
             simpl. rewrite Hother by lia. apply Hd. lia. }
           rewrite Hnan. apply Xderive_pt_nan.
        -- assert (Hsame : xeval (three_step F n e t) ((dvar_of x base delta) k) = xeval (F t) ((dvar_of x base delta) k)).
           { rewrite Hstep.
             rewrite xeval_eset_free
               by (apply (var_free_dvar_of x base delta Hx Hdelta);
                   destruct (Nat.lt_ge_cases k base) as [H|H];
                   [now left | right; lia]).
             unfold E2.
             rewrite xeval_eset_free
               by (apply (var_free_dvar_of x base delta Hx Hdelta);
                   destruct (Nat.lt_ge_cases k base) as [H|H];
                   [now left | right; lia]).
             unfold E1.
             rewrite xeval_eset_free
               by (apply (var_free_dvar_of x base delta Hx Hdelta);
                   destruct (Nat.lt_ge_cases k base) as [H|H];
                   [now left | right; lia]).
             reflexivity. }
           rewrite Hsame.
           apply (Xderive_pt_ext_real (slot_along F k)).
           ++ intros s. unfold slot_along. symmetry. now apply Hother.
           ++ apply Ha.
  - intros k t Hk Hkd. rewrite Hother by lia. apply Hb; lia.
  - intros k t Hk Hkd. rewrite Hother by lia. apply Hc; lia.
  - intros k t Hk. rewrite Hother by lia. apply Hd; lia.
Qed.

(** The invariant at the start: the inputs, with slot x set to t. *)
Lemma inv2_base :
  forall env0,
  (forall k, base <= k -> eget k env0 Xnan = Xnan) ->
  (forall k, k < base -> exists v, eget k env0 Xnan = Xreal v) ->
  inv2 (fun t => eset x env0 (Xreal t)) base.
Proof.
  intros env0 Hunset Hreal.
  split; [|split; [|split]].
  - intros k t.
    unfold dvar_of.
    destruct (Nat.eqb k x) eqn:Hkx.
    + apply Nat.eqb_eq in Hkx. subst k.
      change (xeval (eset x env0 (Xreal t)) (EfromZ 1))
        with (Xreal (IZR 1)).
      apply (Xderive_pt_ext_real (fun T => T)).
      * intros s. unfold slot_along. now rewrite eget_eset_eq.
      * exact (Xderive_pt_identity (Xreal t)).
    + apply Nat.eqb_neq in Hkx.
      destruct (Nat.ltb k base) eqn:Hkb.
      * apply Nat.ltb_lt in Hkb.
        destruct (Hreal k Hkb) as [v Hv].
        change (xeval (eset x env0 (Xreal t)) (EfromZ 0))
          with (Xreal (IZR 0)).
        apply (Xderive_pt_ext_real (fun _ => Xreal v)).
        -- intros s. unfold slot_along.
           rewrite eget_eset_neq by assumption. now rewrite Hv.
        -- exact (Xderive_pt_constant v (Xreal t)).
      * apply Nat.ltb_ge in Hkb.
        simpl. rewrite eget_eset_neq by lia.
        rewrite Hunset by lia. exact I.
  - intros k2 t2 Hk2 _. rewrite eget_eset_neq by lia.
    apply Hunset. lia.
  - intros k2 t2 Hk2 _. rewrite eget_eset_neq by lia.
    apply Hunset. lia.
  - intros k2 t2 Hk2. rewrite eget_eset_neq by lia.
    apply Hunset. lia.
Qed.

(** Well-formed bindings preserve the invariant, binding by binding. *)
Lemma inv2_bindings :
  forall bs F next,
  inv2 F next ->
  well_formed next bs = true ->
  base <= next ->
  next + length bs <= base + delta ->
  inv2 (fun t => xextend (F t) (with_derivs2 bs)) (next + length bs).
Proof.
  induction bs as [|[n e] tl IH]; intros F next Hinv Hwf Hbn Hlen.
  - apply (inv2_ext F).
    + intros t. reflexivity.
    + rewrite Nat.add_0_r. exact Hinv.
  - simpl in Hwf.
    apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He].
    apply Nat.eqb_eq in Hn.
    simpl length in Hlen. simpl length.
    replace (next + S (length tl)) with (S next + length tl) by lia.
    assert (Hstep := inv2_step F next n e Hinv Hn He ltac:(lia) ltac:(lia)).
    assert (Hrec := IH _ (S next) Hstep Htl ltac:(lia) ltac:(lia)).
    eapply inv2_ext.
    2: exact Hrec.
    intros t. cbv beta.
    unfold three_step.
    rewrite <- xextend_app.
    reflexivity.
Qed.

End Bindings3.
