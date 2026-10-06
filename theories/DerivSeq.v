(** Derivatives through a binding list, laid out so that they nest.

    [with_dseq x base len bs] is the list bs followed by the derivative of
    each of its bindings along the input slot x, the derivative of slot k in
    slot k + len. For a well-formed list of length len from base, the result
    is again well-formed from base ([with_dseq_wf]), with its derivative
    bindings in the slots base + len, ..., base + 2 len - 1, so the
    transformation applies to its own output: a second application along
    another input gives the mixed second derivatives, a third the third ones.

    [dseq_correct] states what the slots hold: along a family of
    environments in which slot x has derivative 1 and the other inputs are
    constant, the slot base + len + i holds a derivative of the slot base + i
    in the extended-real sense of Deriv.v. The invariant behind it
    ([sinv]) asks only that every slot's derivative be given by
    [dvar_of]; a slot whose derivative slot is not yet written reads NaN
    there, which is a vacuous claim, so the values can be bound first and the
    derivatives after. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive.
From Stellarocq Require Import Expr Deriv DivDiff.

Import ListNotations.

Section Seq.

Variables x base len : nat.
Hypothesis Hx : (x < base)%nat.
Hypothesis Hlen : (0 < len)%nat.

Let dv : nat -> expr := dvar_of x base len.

(** The derivative bindings, len slots above their values. *)
Definition dbinds (bs : list binding) : list binding :=
  map (fun b => (fst b + len, deriv dv (snd b))%nat) bs.

Definition with_dseq (bs : list binding) : list binding := bs ++ dbinds bs.

(** Every slot's derivative is given by dv, and the slots from the frontier
    on are unset. *)
Definition sinv (F : R -> env ExtendedR) (front : nat) : Prop :=
  (forall k t, Xderive_pt (slot_along F k) (Xreal t) (xeval (F t) (dv k))) /\
  (forall k t, (front <= k)%nat -> eget k (F t) Xnan = Xnan).

Lemma sinv_ext :
  forall F G m, (forall t, F t = G t) -> sinv F m -> sinv G m.
Proof.
  intros F G m HFG [Ha Hb]. split.
  - intros k t. rewrite <- (HFG t).
    apply (Xderive_pt_ext_real (slot_along F k)).
    + intros s. unfold slot_along. now rewrite HFG.
    + apply Ha.
  - intros k t Hk. rewrite <- (HFG t). now apply Hb.
Qed.

Lemma dv_input : forall k, (k < base)%nat -> forall E, exists c, xeval E (dv k) = Xreal c.
Proof.
  intros k Hk E. unfold dv, dvar_of.
  destruct (Nat.eqb k x); [exists 1%R; reflexivity|].
  rewrite (proj2 (Nat.ltb_lt k base) Hk). exists 0%R. reflexivity.
Qed.

Lemma dv_scratch : forall k, (base <= k)%nat -> dv k = Evar (k + len).
Proof.
  intros k Hk. unfold dv, dvar_of.
  replace (Nat.eqb k x) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.ltb k base) with false by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

(** dv k reads no slot other than k + len. *)
Lemma xeval_dv_eset :
  forall k n E v, (k < base \/ k + len <> n)%nat -> xeval (eset n E v) (dv k) = xeval E (dv k).
Proof.
  intros k n E v Hk. apply xeval_eset_free. unfold dv. apply (var_free_dvar_of x base len Hx Hlen). exact Hk.
Qed.

(** A value binding in the value region keeps the invariant. *)
Lemma sinv_value :
  forall F n e, sinv F n -> (base <= n < base + len)%nat ->
  sinv (fun t => eset n (F t) (xeval (F t) e)) (S n).
Proof.
  intros F n e [Ha Hb] Hn. split.
  - intros k t. destruct (Nat.eq_dec k n) as [->|Hkn].
    + rewrite dv_scratch by lia. cbn [xeval]. rewrite eget_eset_neq by lia.
      rewrite Hb by lia. exact I.
    + rewrite xeval_dv_eset by lia.
      apply (Xderive_pt_ext_real (slot_along F k)); [| apply Ha].
      intros s. unfold slot_along. rewrite eget_eset_neq by exact Hkn. reflexivity.
  - intros k t Hk. rewrite eget_eset_neq by lia. apply Hb. lia.
Qed.

Lemma sinv_values :
  forall bs F next, sinv F next -> well_formed next bs = true -> (base <= next)%nat ->
  (next + length bs <= base + len)%nat ->
  sinv (fun t => xextend (F t) bs) (next + length bs).
Proof.
  induction bs as [|[n e] tl IH]; intros F next HF Hwf Hb Hl.
  - rewrite Nat.add_0_r. apply (sinv_ext F); [reflexivity | exact HF].
  - simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn _]. apply Nat.eqb_eq in Hn. subst n.
    simpl length in Hl |- *. replace (next + S (length tl))%nat with (S next + length tl)%nat by lia.
    assert (H1 := sinv_value F next e HF ltac:(lia)).
    apply (sinv_ext (fun t => xextend (eset next (F t) (xeval (F t) e)) tl)); [reflexivity|].
    apply IH; [exact H1 | exact Htl | lia | lia].
Qed.

(** A derivative binding at the frontier keeps the invariant, when the slot
    it differentiates holds the value of its expression. *)
Lemma sinv_deriv :
  forall G n e, sinv G (n + len) -> (base <= n)%nat ->
  vars_below n e = true ->
  (forall t, eget n (G t) Xnan = xeval (G t) e) ->
  sinv (fun t => eset (n + len) (G t) (xeval (G t) (deriv dv e))) (S (n + len)).
Proof.
  intros G n e [Ha Hb] Hn He Hrel. split.
  - intros k t. destruct (Nat.eq_dec k n) as [->|Hkn].
    + rewrite dv_scratch by lia. cbn [xeval]. rewrite eget_eset_eq.
      apply (Xderive_pt_ext_real (along G e)).
      * intros s. unfold slot_along, along. rewrite eget_eset_neq by lia. symmetry. apply Hrel.
      * apply xderive_deriv. exact Ha.
    + destruct (Nat.eq_dec k (n + len)) as [->|Hkd].
      * rewrite dv_scratch by lia. cbn [xeval]. rewrite eget_eset_neq by lia.
        rewrite Hb by lia. exact I.
      * rewrite xeval_dv_eset by lia.
        apply (Xderive_pt_ext_real (slot_along G k)); [| apply Ha].
        intros s. unfold slot_along. rewrite eget_eset_neq by exact Hkd. reflexivity.
  - intros k t Hk. rewrite eget_eset_neq by lia. apply Hb. lia.
Qed.

Lemma xeval_eset_below :
  forall n e E v m, vars_below n e = true -> (n <= m)%nat -> xeval (eset m E v) e = xeval E e.
Proof. intros n e E v m He Hm. apply xeval_eset_free. exact (vars_below_free n m e He Hm). Qed.

Lemma sinv_derivs :
  forall bs G next, sinv G (next + len) -> well_formed next bs = true -> (base <= next)%nat ->
  (next + length bs <= base + len)%nat ->
  (forall n e, In (n, e) bs -> forall t, eget n (G t) Xnan = xeval (G t) e) ->
  sinv (fun t => xextend (G t) (dbinds bs)) (next + len + length bs).
Proof.
  induction bs as [|[n e] tl IH]; intros G next HG Hwf Hb Hl Hrel.
  - rewrite Nat.add_0_r. apply (sinv_ext G); [reflexivity | exact HG].
  - simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He]. apply Nat.eqb_eq in Hn. subst n.
    simpl length in Hl |- *.
    replace (next + len + S (length tl))%nat with (S next + len + length tl)%nat by lia.
    assert (H1 := sinv_deriv G next e HG Hb He (Hrel next e (or_introl eq_refl))).
    apply (sinv_ext (fun t => xextend (eset (next + len) (G t) (xeval (G t) (deriv dv e))) (dbinds tl)));
      [reflexivity|].
    apply IH; [replace (S next + len)%nat with (S (next + len)) by lia; exact H1 | exact Htl | lia | lia |].
    intros n' e' Hin t.
    destruct (well_formed_in tl (S next) n' e' Htl Hin) as [Hn' He'].
    rewrite eget_eset_neq by lia. rewrite (xeval_eset_below n' e') by (exact He' || lia).
    apply Hrel. right. exact Hin.
Qed.

(** The invariant at the start: the inputs, with slot x set to t and the
    rest of the environment unset from base on. *)
Lemma sinv_base :
  forall env0,
  (forall k, (base <= k)%nat -> eget k env0 Xnan = Xnan) ->
  (forall k, (k < base)%nat -> exists v, eget k env0 Xnan = Xreal v) ->
  sinv (fun t => eset x env0 (Xreal t)) base.
Proof.
  intros env0 Hunset Hreal.
  destruct (inv_base x base len Hx Hlen env0 Hunset Hreal) as [Ha [_ Hc]].
  split; [exact Ha|].
  intros k t Hk. rewrite eget_eset_neq by lia. apply Hunset. exact Hk.
Qed.

(** The derivative slots hold derivatives of the value slots. *)
Theorem dseq_correct :
  forall bs (E0 : R -> env ExtendedR),
  well_formed base bs = true -> length bs = len ->
  sinv E0 base ->
  sinv (fun t => xextend (E0 t) (with_dseq bs)) (base + 2 * len) /\
  (forall i t, (i < len)%nat ->
     Xderive_pt (slot_along (fun t => xextend (E0 t) (with_dseq bs)) (base + i)) (Xreal t)
       (eget (base + len + i) (xextend (E0 t) (with_dseq bs)) Xnan)).
Proof.
  intros bs E0 Hwf Hl HE0.
  assert (H1 := sinv_values bs E0 base HE0 Hwf ltac:(lia) ltac:(lia)).
  rewrite Hl in H1.
  assert (Hrel : forall n e, In (n, e) bs -> forall t,
            eget n (xextend (E0 t) bs) Xnan = xeval (xextend (E0 t) bs) e).
  { intros n e Hin t. exact (wf_holds bs (E0 t) base n e Hwf Hin). }
  assert (H2 := sinv_derivs bs (fun t => xextend (E0 t) bs) base H1 Hwf ltac:(lia) ltac:(lia) Hrel).
  rewrite Hl in H2.
  assert (HS : sinv (fun t => xextend (E0 t) (with_dseq bs)) (base + 2 * len)).
  { apply (sinv_ext (fun t => xextend (xextend (E0 t) bs) (dbinds bs))).
    - intros t. unfold with_dseq. rewrite xextend_app. reflexivity.
    - replace (base + 2 * len)%nat with (base + len + len)%nat by lia. exact H2. }
  split; [exact HS|].
  intros i t Hi. destruct HS as [Ha _]. specialize (Ha (base + i)%nat t).
  rewrite dv_scratch in Ha by lia. cbn [xeval] in Ha.
  replace (base + len + i)%nat with (base + i + len)%nat by lia. exact Ha.
Qed.

(** The output is well formed from base, so the transformation nests. *)
Lemma vars_below_dv :
  forall n e, (base <= n)%nat -> vars_below n e = true -> vars_below (n + len) (deriv dv e) = true.
Proof.
  intros n e Hn He.
  assert (Hd : forall k, (k < n)%nat -> vars_below (n + len) (dv k) = true).
  { intros k Hk. unfold dv, dvar_of. destruct (Nat.eqb k x); [reflexivity|].
    destruct (Nat.ltb k base); [reflexivity|]. cbn. apply Nat.ltb_lt. lia. }
  assert (Hmono : forall m e', vars_below m e' = true -> (m <= n + len)%nat -> vars_below (n + len) e' = true).
  { intros m e' H Hm. induction e'; cbn in *;
      try (apply andb_prop in H; destruct H as [H1 H2]; rewrite IHe'1, IHe'2 by assumption; reflexivity);
      try (apply IHe'; assumption); try reflexivity.
    apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia. }
  induction e; cbn in He |- *;
    try (apply andb_prop in He; destruct He as [H1 H2]);
    repeat (match goal with
            | |- (_ && _)%bool = true => apply andb_true_iff; split
            end);
    try (apply IHe; assumption); try (apply IHe1; assumption); try (apply IHe2; assumption);
    try reflexivity;
    try (apply (Hmono n); [assumption | lia]).
  apply Nat.ltb_lt in He. apply Hd. exact He.
Qed.

Lemma well_formed_app :
  forall l1 l2 next, well_formed next l1 = true -> well_formed (next + length l1) l2 = true ->
  well_formed next (l1 ++ l2) = true.
Proof.
  induction l1 as [|[n e] tl IH]; intros l2 next H1 H2; cbn in *.
  - rewrite Nat.add_0_r in H2. exact H2.
  - apply andb_prop in H1. destruct H1 as [H1 Htl]. rewrite H1. cbn.
    apply IH; [exact Htl|]. replace (S next + length tl)%nat with (next + S (length tl))%nat by lia. exact H2.
Qed.

Lemma dbinds_wf :
  forall bs next, well_formed next bs = true -> (base <= next)%nat ->
  well_formed (next + len) (dbinds bs) = true.
Proof.
  induction bs as [|[n e] tl IH]; intros next Hwf Hb; [reflexivity|].
  cbn in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn He]. apply Nat.eqb_eq in Hn. subst n.
  cbn [dbinds map fst snd well_formed].
  rewrite Nat.eqb_refl. rewrite (vars_below_dv next e Hb He). cbn.
  replace (S (next + len)) with (S next + len)%nat by lia.
  apply (IH (S next)); [exact Htl | lia].
Qed.

Theorem with_dseq_wf :
  forall bs, well_formed base bs = true -> length bs = len -> well_formed base (with_dseq bs) = true.
Proof.
  intros bs Hwf Hl. unfold with_dseq. apply well_formed_app; [exact Hwf|].
  rewrite Hl. exact (dbinds_wf bs base Hwf ltac:(lia)).
Qed.

Lemma length_with_dseq : forall bs, length (with_dseq bs) = (2 * length bs)%nat.
Proof.
  intros bs. unfold with_dseq, dbinds. rewrite length_app, length_map.
  cbn [Nat.mul]. rewrite Nat.add_0_r. reflexivity.
Qed.

End Seq.
