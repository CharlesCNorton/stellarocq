(** Divided differences of expressions, exact and free of the step.

    An environment carries three layers of the same slots, interleaved: slot
    k of the minus layer at 3k, of the plus layer at 3k + 1, and of the
    difference layer at 3k + 2, related on the inputs by x+ - x- = h d. [dd]
    turns an expression over the slots into one over the three layers whose
    value D satisfies e+ - e- = h D, e- and e+ the values of e in the two
    layers ([dd_correct]). It divides by nothing that vanishes with h: the
    difference of a product is (a+ - a-) b+ + a- (b+ - b-) and that of a
    quotient ((a+ - a-) b- - a- (b+ - b-)) / (b+ b-). That of a square root
    is (a+ - a-) / (sqrt a+ + sqrt a-), each root written a / sqrt a so that
    the denominator has a value only when both arguments are positive. A
    subterm over fixed slots, which take the same value in both layers, has
    divided difference 0; transcendental functions are allowed only there,
    and elsewhere [dd] gives an expression with no value. The half-point field is
    rational in the coefficients, the stream function and the transform, and
    its sines and cosines are of the fixed angles, so this is all its
    difference between two half points needs.

    [with_dd] triples a binding list: binding n becomes the binding over the
    minus layer at 3n, over the plus layer at 3n + 1, and its divided
    difference at 3n + 2. A well-formed list stays well-formed
    ([with_dd_wf]), so the derivatives of Deriv.v run through it; every slot
    of the three layers is then related as the inputs are ([dd_bindings]),
    and each value layer, read as an environment of its own, holds what the
    plain bindings compute from its inputs ([layer_sound]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Deriv.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Evaluation against a function of the slots                        *)

(** [xeval] with the slots read from a function rather than an environment,
    so that a layer of an environment can be read as the environment of its
    own slots. *)
Fixpoint xevalf (g : nat -> ExtendedR) (e : expr) : ExtendedR :=
  match e with
  | Evar n     => g n
  | EfromZ z   => Xreal (IZR z)
  | Epi        => Xreal PI
  | Eneg a     => Xneg (xevalf g a)
  | Eadd a b   => Xadd (xevalf g a) (xevalf g b)
  | Esub a b   => Xsub (xevalf g a) (xevalf g b)
  | Emul a b   => Xmul (xevalf g a) (xevalf g b)
  | Ediv a b   => Xdiv (xevalf g a) (xevalf g b)
  | Esqrt a    => Xsqrt (xevalf g a)
  | Esin a     => Xsin (xevalf g a)
  | Ecos a     => Xcos (xevalf g a)
  | Eexp a     => Xexp (xevalf g a)
  | Eatan a    => Xatan (xevalf g a)
  | Epow2 z    => Xreal (powerRZ 2%R z)
  end.

Lemma xeval_f : forall env e, xeval env e = xevalf (fun k => eget k env Xnan) e.
Proof. intros env e. induction e; simpl; congruence. Qed.

(** The slots an expression reads. *)
Fixpoint occurs (k : nat) (e : expr) : Prop :=
  match e with
  | Evar n     => n = k
  | EfromZ _ | Epi | Epow2 _ => False
  | Eneg a | Esqrt a | Esin a | Ecos a | Eexp a | Eatan a => occurs k a
  | Eadd a b | Esub a b | Emul a b | Ediv a b => occurs k a \/ occurs k b
  end.

Lemma xevalf_ext :
  forall g g' e, (forall k, occurs k e -> g k = g' k) -> xevalf g e = xevalf g' e.
Proof.
  intros g g' e. induction e; simpl; intros H.
  - apply H. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHe by exact H. reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe by exact H. reflexivity.
  - rewrite IHe by exact H. reflexivity.
  - rewrite IHe by exact H. reflexivity.
  - rewrite IHe by exact H. reflexivity.
  - rewrite IHe by exact H. reflexivity.
  - reflexivity.
Qed.

Lemma occurs_below :
  forall m e k, vars_below m e = true -> occurs k e -> (k < m)%nat.
Proof.
  intros m e k. induction e; simpl; intros Hb Ho.
  - subst. apply Nat.ltb_lt. exact Hb.
  - contradiction.
  - contradiction.
  - exact (IHe Hb Ho).
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - exact (IHe Hb Ho).
  - exact (IHe Hb Ho).
  - exact (IHe Hb Ho).
  - exact (IHe Hb Ho).
  - exact (IHe Hb Ho).
  - contradiction.
Qed.

Lemma below_occurs :
  forall m e, (forall k, occurs k e -> (k < m)%nat) -> vars_below m e = true.
Proof.
  intros m e. induction e; simpl; intros H.
  - apply Nat.ltb_lt. apply H. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHe. exact H.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* Renaming slots                                                    *)

Fixpoint ren (f : nat -> nat) (e : expr) : expr :=
  match e with
  | Evar n     => Evar (f n)
  | EfromZ z   => EfromZ z
  | Epi        => Epi
  | Eneg a     => Eneg (ren f a)
  | Eadd a b   => Eadd (ren f a) (ren f b)
  | Esub a b   => Esub (ren f a) (ren f b)
  | Emul a b   => Emul (ren f a) (ren f b)
  | Ediv a b   => Ediv (ren f a) (ren f b)
  | Esqrt a    => Esqrt (ren f a)
  | Esin a     => Esin (ren f a)
  | Ecos a     => Ecos (ren f a)
  | Eexp a     => Eexp (ren f a)
  | Eatan a    => Eatan (ren f a)
  | Epow2 z    => Epow2 z
  end.

Lemma xevalf_ren :
  forall f g e, xevalf g (ren f e) = xevalf (fun k => g (f k)) e.
Proof. intros f g e. induction e; simpl; congruence. Qed.

Lemma occurs_ren :
  forall f k e, occurs k (ren f e) -> exists j, occurs j e /\ k = f j.
Proof.
  intros f k e. induction e; simpl; intros H.
  - exists n. split; [reflexivity | symmetry; exact H].
  - contradiction.
  - contradiction.
  - exact (IHe H).
  - destruct H as [H|H]; [destruct (IHe1 H) as [j [Hj ->]] | destruct (IHe2 H) as [j [Hj ->]]];
      exists j; split; [simpl; tauto | reflexivity | simpl; tauto | reflexivity].
  - destruct H as [H|H]; [destruct (IHe1 H) as [j [Hj ->]] | destruct (IHe2 H) as [j [Hj ->]]];
      exists j; split; [simpl; tauto | reflexivity | simpl; tauto | reflexivity].
  - destruct H as [H|H]; [destruct (IHe1 H) as [j [Hj ->]] | destruct (IHe2 H) as [j [Hj ->]]];
      exists j; split; [simpl; tauto | reflexivity | simpl; tauto | reflexivity].
  - destruct H as [H|H]; [destruct (IHe1 H) as [j [Hj ->]] | destruct (IHe2 H) as [j [Hj ->]]];
      exists j; split; [simpl; tauto | reflexivity | simpl; tauto | reflexivity].
  - exact (IHe H).
  - exact (IHe H).
  - exact (IHe H).
  - exact (IHe H).
  - exact (IHe H).
  - contradiction.
Qed.

(** The three layers. *)
Definition lm (k : nat) : nat := 3 * k.
Definition lp (k : nat) : nat := 3 * k + 1.
Definition ld (k : nat) : nat := 3 * k + 2.

(* ---------------------------------------------------------------- *)
(* Fixed slots                                                       *)

Section Transform.

(** The fixed slots, which take the same value in both layers. *)
Variable fx : nat -> bool.

Fixpoint fixed (e : expr) : bool :=
  match e with
  | Evar n     => fx n
  | EfromZ _ | Epi | Epow2 _ => true
  | Eneg a | Esqrt a | Esin a | Ecos a | Eexp a | Eatan a => fixed a
  | Eadd a b | Esub a b | Emul a b | Ediv a b => fixed a && fixed b
  end.

Lemma fixed_occurs : forall e k, fixed e = true -> occurs k e -> fx k = true.
Proof.
  intros e k. induction e; simpl; intros Hf Ho.
  - subst. exact Hf.
  - contradiction.
  - contradiction.
  - exact (IHe Hf Ho).
  - apply andb_prop in Hf. destruct Hf as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - apply andb_prop in Hf. destruct Hf as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - apply andb_prop in Hf. destruct Hf as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - apply andb_prop in Hf. destruct Hf as [H1 H2]. destruct Ho as [Ho|Ho]; auto.
  - exact (IHe Hf Ho).
  - exact (IHe Hf Ho).
  - exact (IHe Hf Ho).
  - exact (IHe Hf Ho).
  - exact (IHe Hf Ho).
  - contradiction.
Qed.

(** An expression over fixed slots has the same value in both layers. *)
Lemma fixed_layers :
  forall g e,
  (forall k, occurs k e -> fx k = true -> g (lp k) = g (lm k)) ->
  fixed e = true -> xevalf g (ren lp e) = xevalf g (ren lm e).
Proof.
  intros g e Hg Hf. rewrite !xevalf_ren. apply xevalf_ext.
  intros k Hk. apply Hg; [exact Hk | exact (fixed_occurs e k Hf Hk)].
Qed.

(* ---------------------------------------------------------------- *)
(* The divided difference                                            *)

(** An expression with no value, for a varying square root or
    transcendental function. *)
Definition no_value : expr := Ediv (EfromZ 0) (EfromZ 0).

Lemma xevalf_no_value : forall g, xevalf g no_value = Xnan.
Proof.
  intros g. simpl. cbn [Xbind2]. unfold Xdiv'.
  destruct (is_zero_spec (IZR 0)) as [Hz|Hz]; [reflexivity | exfalso; apply Hz; reflexivity].
Qed.

Fixpoint dd (e : expr) : expr :=
  if fixed e then EfromZ 0 else
  match e with
  | Evar n     => Evar (ld n)
  | Eneg a     => Eneg (dd a)
  | Eadd a b   => Eadd (dd a) (dd b)
  | Esub a b   => Esub (dd a) (dd b)
  | Emul a b   => Eadd (Emul (dd a) (ren lp b)) (Emul (ren lm a) (dd b))
  | Ediv a b   => Ediv (Esub (Emul (dd a) (ren lm b)) (Emul (ren lm a) (dd b)))
                       (Emul (ren lp b) (ren lm b))
  | Esqrt a    => Ediv (dd a) (Eadd (Ediv (ren lp a) (Esqrt (ren lp a))) (Ediv (ren lm a) (Esqrt (ren lm a))))
  | _          => no_value
  end.

(** One step of [dd] on a varying expression. *)
Definition dd_step (e : expr) : expr :=
  match e with
  | Evar n     => Evar (ld n)
  | Eneg a     => Eneg (dd a)
  | Eadd a b   => Eadd (dd a) (dd b)
  | Esub a b   => Esub (dd a) (dd b)
  | Emul a b   => Eadd (Emul (dd a) (ren lp b)) (Emul (ren lm a) (dd b))
  | Ediv a b   => Ediv (Esub (Emul (dd a) (ren lm b)) (Emul (ren lm a) (dd b)))
                       (Emul (ren lp b) (ren lm b))
  | Esqrt a    => Ediv (dd a) (Eadd (Ediv (ren lp a) (Esqrt (ren lp a))) (Ediv (ren lm a) (Esqrt (ren lm a))))
  | _          => no_value
  end.

Lemma dd_fixed : forall e, fixed e = true -> dd e = EfromZ 0.
Proof. intros e H. destruct e; simpl in *; try rewrite H; reflexivity. Qed.

Lemma dd_nonfixed : forall e, fixed e = false -> dd e = dd_step e.
Proof. intros e H. destruct e; simpl in *; try discriminate; rewrite H; reflexivity. Qed.

(** The slots [dd e] reads: the three layers of the slots e reads. *)
Lemma occurs_dd :
  forall k e, occurs k (dd e) ->
  exists j, occurs j e /\ (k = lm j \/ k = lp j \/ k = ld j).
Proof.
  intros k e. induction e; intros H;
    lazymatch type of H with occurs _ (dd ?E) =>
      destruct (fixed E) eqn:Hf;
      [rewrite (dd_fixed E Hf) in H; simpl in H; contradiction
      | rewrite (dd_nonfixed E Hf) in H; simpl in H] end;
    try (simpl in Hf; discriminate).
  - exists n. split; [reflexivity | right; right; symmetry; exact H].
  - destruct (IHe H) as [j [Hj Hk]]. exists j. split; [exact Hj | exact Hk].
  - destruct H as [H|H].
    + destruct (IHe1 H) as [j [Hj Hk]]. exists j. split; [simpl; left; exact Hj | exact Hk].
    + destruct (IHe2 H) as [j [Hj Hk]]. exists j. split; [simpl; right; exact Hj | exact Hk].
  - destruct H as [H|H].
    + destruct (IHe1 H) as [j [Hj Hk]]. exists j. split; [simpl; left; exact Hj | exact Hk].
    + destruct (IHe2 H) as [j [Hj Hk]]. exists j. split; [simpl; right; exact Hj | exact Hk].
  - destruct H as [[H|H]|[H|H]].
    + destruct (IHe1 H) as [j [Hj Hk]]. exists j. split; [simpl; left; exact Hj | exact Hk].
    + destruct (occurs_ren lp k e2 H) as [j [Hj ->]].
      exists j. split; [simpl; right; exact Hj | right; left; reflexivity].
    + destruct (occurs_ren lm k e1 H) as [j [Hj ->]].
      exists j. split; [simpl; left; exact Hj | left; reflexivity].
    + destruct (IHe2 H) as [j [Hj Hk]]. exists j. split; [simpl; right; exact Hj | exact Hk].
  - destruct H as [[[H|H]|[H|H]]|[H|H]].
    + destruct (IHe1 H) as [j [Hj Hk]]. exists j. split; [simpl; left; exact Hj | exact Hk].
    + destruct (occurs_ren lm k e2 H) as [j [Hj ->]].
      exists j. split; [simpl; right; exact Hj | left; reflexivity].
    + destruct (occurs_ren lm k e1 H) as [j [Hj ->]].
      exists j. split; [simpl; left; exact Hj | left; reflexivity].
    + destruct (IHe2 H) as [j [Hj Hk]]. exists j. split; [simpl; right; exact Hj | exact Hk].
    + destruct (occurs_ren lp k e2 H) as [j [Hj ->]].
      exists j. split; [simpl; right; exact Hj | right; left; reflexivity].
    + destruct (occurs_ren lm k e2 H) as [j [Hj ->]].
      exists j. split; [simpl; right; exact Hj | left; reflexivity].
  - destruct H as [H|[[H|H]|[H|H]]].
    + destruct (IHe H) as [j [Hj Hk]]. exists j. split; [exact Hj | exact Hk].
    + destruct (occurs_ren lp k e H) as [j [Hj ->]].
      exists j. split; [exact Hj | right; left; reflexivity].
    + destruct (occurs_ren lp k e H) as [j [Hj ->]].
      exists j. split; [exact Hj | right; left; reflexivity].
    + destruct (occurs_ren lm k e H) as [j [Hj ->]].
      exists j. split; [exact Hj | left; reflexivity].
    + destruct (occurs_ren lm k e H) as [j [Hj ->]].
      exists j. split; [exact Hj | left; reflexivity].
  - unfold no_value in H. simpl in H. tauto.
  - unfold no_value in H. simpl in H. tauto.
  - unfold no_value in H. simpl in H. tauto.
  - unfold no_value in H. simpl in H. tauto.
Qed.

(* Inversion of real-valued extended arithmetic. *)

Lemma Xneg_inv : forall a z, Xneg a = Xreal z -> exists x, a = Xreal x /\ z = - x.
Proof. intros [|x] z H; simpl in H; try discriminate. injection H as <-. eauto. Qed.

Lemma Xadd_inv :
  forall a b z, Xadd a b = Xreal z -> exists x y, a = Xreal x /\ b = Xreal y /\ z = x + y.
Proof. intros [|x] [|y] z H; simpl in H; try discriminate. injection H as <-. eauto. Qed.

Lemma Xsub_inv :
  forall a b z, Xsub a b = Xreal z -> exists x y, a = Xreal x /\ b = Xreal y /\ z = x - y.
Proof. intros [|x] [|y] z H; simpl in H; try discriminate. injection H as <-. eauto. Qed.

Lemma Xmul_inv :
  forall a b z, Xmul a b = Xreal z -> exists x y, a = Xreal x /\ b = Xreal y /\ z = x * y.
Proof. intros [|x] [|y] z H; simpl in H; try discriminate. injection H as <-. eauto. Qed.

Lemma Xdiv_inv :
  forall a b z, Xdiv a b = Xreal z ->
  exists x y, a = Xreal x /\ b = Xreal y /\ y <> 0 /\ z = x / y.
Proof.
  intros [|x] [|y] z H; cbn [Xbind2] in H; try discriminate.
  unfold Xdiv' in H. destruct (is_zero_spec y) as [Hz|Hz]; [discriminate|].
  injection H as <-. exists x, y. auto.
Qed.

Lemma Xsqrt_inv : forall a z, Xsqrt a = Xreal z -> exists x, a = Xreal x /\ z = sqrt x.
Proof.
  intros a z H. destruct a as [|x]; [discriminate H|].
  cbn [Xbind] in H. unfold Xsqrt' in H. injection H as <-. exists x. split; reflexivity.
Qed.

(** x / sqrt x is real only for positive x, and is then sqrt x. *)
Lemma div_sqrt : forall x, sqrt x <> 0 -> 0 < x /\ x / sqrt x = sqrt x.
Proof.
  intros x Hx. assert (Hp : 0 < x).
  { destruct (Rle_or_lt x 0) as [Hle|Hlt]; [exfalso; apply Hx; apply sqrt_neg_0; exact Hle | exact Hlt]. }
  split; [exact Hp|]. assert (Hs := sqrt_sqrt x (Rlt_le _ _ Hp)).
  apply (Rmult_eq_reg_r (sqrt x)); [|exact Hx]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hx.
  rewrite Hs. ring.
Qed.

(** The divided difference is the difference of the two layers over h,
    wherever the three values are real and the slots it reads are related
    as the inputs are. *)
Lemma dd_correct :
  forall (g : nat -> ExtendedR) (h : R) e,
  (forall k am ap d, occurs k e -> g (lm k) = Xreal am -> g (lp k) = Xreal ap ->
     g (ld k) = Xreal d -> ap - am = h * d) ->
  (forall k, occurs k e -> fx k = true -> g (lp k) = g (lm k)) ->
  forall am ap d,
  xevalf g (ren lm e) = Xreal am -> xevalf g (ren lp e) = Xreal ap ->
  xevalf g (dd e) = Xreal d -> ap - am = h * d.
Proof.
  intros g h e. induction e; intros Hrel Hfx am ap d Ha Hp Hd;
    lazymatch type of Hd with xevalf _ (dd ?E) = _ =>
      destruct (fixed E) eqn:Hf;
      [rewrite (dd_fixed E Hf) in Hd; simpl in Hd; injection Hd as <-;
       rewrite (fixed_layers g E Hfx Hf) in Hp; rewrite Ha in Hp; injection Hp as ->; lra
      | rewrite (dd_nonfixed E Hf) in Hd; cbn [dd_step] in Hd] end;
    try (simpl in Hf; discriminate);
    try (rewrite xevalf_no_value in Hd; discriminate).
  - (* a varying slot *)
    simpl in Ha, Hp, Hd. exact (Hrel n am ap d eq_refl Ha Hp Hd).
  - (* negation *)
    simpl in Ha, Hp, Hd.
    destruct (Xneg_inv _ _ Ha) as [x [Hx ->]]. destruct (Xneg_inv _ _ Hp) as [y [Hy ->]].
    destruct (Xneg_inv _ _ Hd) as [z [Hz ->]].
    specialize (IHe Hrel Hfx x y z Hx Hy Hz). lra.
  - (* sum *)
    simpl in Ha, Hp, Hd.
    destruct (Xadd_inv _ _ _ Ha) as [a1 [a2 [Ha1 [Ha2 ->]]]].
    destruct (Xadd_inv _ _ _ Hp) as [p1 [p2 [Hp1 [Hp2 ->]]]].
    destruct (Xadd_inv _ _ _ Hd) as [d1 [d2 [Hd1 [Hd2 ->]]]].
    assert (R1 := IHe1 (fun k am ap d Hk => Hrel k am ap d (or_introl Hk))
                       (fun k Hk => Hfx k (or_introl Hk)) a1 p1 d1 Ha1 Hp1 Hd1).
    assert (R2 := IHe2 (fun k am ap d Hk => Hrel k am ap d (or_intror Hk))
                       (fun k Hk => Hfx k (or_intror Hk)) a2 p2 d2 Ha2 Hp2 Hd2).
    lra.
  - (* difference *)
    simpl in Ha, Hp, Hd.
    destruct (Xsub_inv _ _ _ Ha) as [a1 [a2 [Ha1 [Ha2 ->]]]].
    destruct (Xsub_inv _ _ _ Hp) as [p1 [p2 [Hp1 [Hp2 ->]]]].
    destruct (Xsub_inv _ _ _ Hd) as [d1 [d2 [Hd1 [Hd2 ->]]]].
    assert (R1 := IHe1 (fun k am ap d Hk => Hrel k am ap d (or_introl Hk))
                       (fun k Hk => Hfx k (or_introl Hk)) a1 p1 d1 Ha1 Hp1 Hd1).
    assert (R2 := IHe2 (fun k am ap d Hk => Hrel k am ap d (or_intror Hk))
                       (fun k Hk => Hfx k (or_intror Hk)) a2 p2 d2 Ha2 Hp2 Hd2).
    lra.
  - (* product *)
    simpl in Ha, Hp, Hd.
    destruct (Xmul_inv _ _ _ Ha) as [a1 [a2 [Ha1 [Ha2 ->]]]].
    destruct (Xmul_inv _ _ _ Hp) as [p1 [p2 [Hp1 [Hp2 ->]]]].
    destruct (Xadd_inv _ _ _ Hd) as [t1 [t2 [Ht1 [Ht2 ->]]]].
    destruct (Xmul_inv _ _ _ Ht1) as [d1 [q2 [Hd1 [Hq2 ->]]]].
    destruct (Xmul_inv _ _ _ Ht2) as [q1 [d2 [Hq1 [Hd2 ->]]]].
    rewrite Hp2 in Hq2. injection Hq2 as <-. rewrite Ha1 in Hq1. injection Hq1 as <-.
    assert (R1 := IHe1 (fun k am ap d Hk => Hrel k am ap d (or_introl Hk))
                       (fun k Hk => Hfx k (or_introl Hk)) a1 p1 d1 Ha1 Hp1 Hd1).
    assert (R2 := IHe2 (fun k am ap d Hk => Hrel k am ap d (or_intror Hk))
                       (fun k Hk => Hfx k (or_intror Hk)) a2 p2 d2 Ha2 Hp2 Hd2).
    replace (p1 * p2 - a1 * a2) with ((p1 - a1) * p2 + a1 * (p2 - a2)) by ring.
    rewrite R1, R2. ring.
  - (* quotient *)
    simpl in Ha, Hp, Hd.
    destruct (Xdiv_inv _ _ _ Ha) as [a1 [a2 [Ha1 [Ha2 [Hnz2 ->]]]]].
    destruct (Xdiv_inv _ _ _ Hp) as [p1 [p2 [Hp1 [Hp2 [Hnp2 ->]]]]].
    destruct (Xdiv_inv _ _ _ Hd) as [num [den [Hnum [Hden [Hnd ->]]]]].
    destruct (Xsub_inv _ _ _ Hnum) as [t1 [t2 [Ht1 [Ht2 ->]]]].
    destruct (Xmul_inv _ _ _ Ht1) as [d1 [b1 [Hd1 [Hb1' ->]]]].
    destruct (Xmul_inv _ _ _ Ht2) as [c1 [d2 [Hc1 [Hd2 ->]]]].
    destruct (Xmul_inv _ _ _ Hden) as [s1 [s2 [Hs1 [Hs2 ->]]]].
    rewrite Ha2 in Hb1'. injection Hb1' as <-. rewrite Ha1 in Hc1. injection Hc1 as <-.
    rewrite Hp2 in Hs1. injection Hs1 as <-. rewrite Ha2 in Hs2. injection Hs2 as <-.
    assert (R1 := IHe1 (fun k am ap d Hk => Hrel k am ap d (or_introl Hk))
                       (fun k Hk => Hfx k (or_introl Hk)) a1 p1 d1 Ha1 Hp1 Hd1).
    assert (R2 := IHe2 (fun k am ap d Hk => Hrel k am ap d (or_intror Hk))
                       (fun k Hk => Hfx k (or_intror Hk)) a2 p2 d2 Ha2 Hp2 Hd2).
    assert (Hp1' : p1 = a1 + h * d1) by lra. assert (Hp2' : p2 = a2 + h * d2) by lra.
    subst p1 p2. field. split; assumption.
  - (* square root: sqrt p - sqrt a = (p - a) / (sqrt p + sqrt a), the two
       roots read as p / sqrt p and a / sqrt a so that they are real only
       for positive p and a *)
    simpl in Ha, Hp, Hd.
    destruct (Xsqrt_inv _ _ Ha) as [a1 [Ha1 ->]].
    destruct (Xsqrt_inv _ _ Hp) as [p1 [Hp1 ->]].
    destruct (Xdiv_inv _ _ _ Hd) as [d1 [den [Hd1 [Hden [Hnd ->]]]]].
    destruct (Xadd_inv _ _ _ Hden) as [xp [xm [Hxp [Hxm ->]]]].
    destruct (Xdiv_inv _ _ _ Hxp) as [p2 [sp [Hp2 [Hsp [Hspnz ->]]]]].
    destruct (Xdiv_inv _ _ _ Hxm) as [a2 [sm [Ha2 [Hsm [Hsmnz ->]]]]].
    rewrite Hp1 in Hp2. injection Hp2 as <-. rewrite Ha1 in Ha2. injection Ha2 as <-.
    rewrite Hp1 in Hsp. destruct (Xsqrt_inv _ _ Hsp) as [p' [Hp' ->]]. injection Hp' as <-.
    rewrite Ha1 in Hsm. destruct (Xsqrt_inv _ _ Hsm) as [a' [Ha' ->]]. injection Ha' as <-.
    destruct (div_sqrt p1 Hspnz) as [Hp1p Hpp]. destruct (div_sqrt a1 Hsmnz) as [Ha1p Haa].
    rewrite Hpp, Haa in *.
    assert (R1 := IHe Hrel Hfx a1 p1 d1 Ha1 Hp1 Hd1).
    assert (Hd2 : p1 - a1 = (sqrt p1 - sqrt a1) * (sqrt p1 + sqrt a1)).
    { replace ((sqrt p1 - sqrt a1) * (sqrt p1 + sqrt a1)) with (sqrt p1 * sqrt p1 - sqrt a1 * sqrt a1) by ring.
      rewrite (sqrt_sqrt a1 (Rlt_le _ _ Ha1p)), (sqrt_sqrt p1 (Rlt_le _ _ Hp1p)). reflexivity. }
    replace (h * (d1 / (sqrt p1 + sqrt a1))) with ((h * d1) / (sqrt p1 + sqrt a1)) by (field; exact Hnd).
    rewrite <- R1, Hd2. field. exact Hnd.
Qed.

End Transform.

(* ---------------------------------------------------------------- *)
(* Well-formed lists                                                 *)

(** A slot no binding writes keeps its value. *)
Lemma eget_xextend_notin :
  forall L E k, ~ In k (map fst L) -> eget k (xextend E L) Xnan = eget k E Xnan.
Proof.
  induction L as [|[s e] L IH]; intros E k Hk; [reflexivity|].
  simpl in Hk. change (xextend E ((s, e) :: L)) with (xextend (eset s E (xeval E e)) L).
  rewrite IH by tauto. apply eget_eset_neq. intros ->. tauto.
Qed.

(** The slots of a well-formed list are next, next + 1, ... *)
Lemma well_formed_slots :
  forall bs next k, well_formed next bs = true -> In k (map fst bs) ->
  (next <= k < next + length bs)%nat.
Proof.
  induction bs as [|[n e] tl IH]; intros next k Hwf Hin; [destruct Hin|].
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn _]. apply Nat.eqb_eq in Hn. subst n.
  simpl in Hin. simpl length. destruct Hin as [->|Hin]; [lia|].
  specialize (IH (S next) k Htl Hin). lia.
Qed.

Lemma well_formed_in :
  forall bs next n e, well_formed next bs = true -> In (n, e) bs ->
  (next <= n < next + length bs)%nat /\ vars_below n e = true.
Proof.
  induction bs as [|[n' e'] tl IH]; intros next n e Hwf Hin; [destruct Hin|].
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn He]. apply Nat.eqb_eq in Hn. subst n'.
  simpl length. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. split; [lia | exact He].
  - destruct (IH (S next) n e Htl Hin) as [H1 H2]. split; [lia | exact H2].
Qed.

(** Every binding of a well-formed list holds its value in the final
    environment. *)
Lemma wf_holds :
  forall bs E next n e,
  well_formed next bs = true -> In (n, e) bs ->
  eget n (xextend E bs) Xnan = xeval (xextend E bs) e.
Proof.
  induction bs as [|[n0 e0] tl IH]; intros E next n e Hwf Hin; [destruct Hin|].
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn0 He0]. apply Nat.eqb_eq in Hn0. subst n0.
  change (xextend E ((next, e0) :: tl)) with (xextend (eset next E (xeval E e0)) tl).
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-.
    rewrite eget_xextend_notin
      by (intros H; pose proof (well_formed_slots tl (S next) next Htl H); lia).
    rewrite eget_eset_eq. rewrite !xeval_f. apply xevalf_ext. intros k Hk.
    pose proof (occurs_below next e0 k He0 Hk) as Hkn.
    rewrite eget_xextend_notin
      by (intros Hm; pose proof (well_formed_slots tl (S next) k Htl Hm); lia).
    rewrite eget_eset_neq by lia. reflexivity.
  - exact (IH _ (S next) n e Htl Hin).
Qed.

(* ---------------------------------------------------------------- *)
(* Through a binding list                                            *)

Section Bindings.

Variable fx : nat -> bool.
Variable h : R.

(** Each binding over the minus layer, over the plus layer, and its divided
    difference. *)
Definition with_dd (bs : list binding) : list binding :=
  flat_map (fun b => [(lm (fst b), ren lm (snd b)); (lp (fst b), ren lp (snd b));
                      (ld (fst b), dd fx (snd b))]) bs.

Lemma well_formed_app :
  forall L1 L2 n, well_formed n (L1 ++ L2) = well_formed n L1 && well_formed (n + length L1) L2.
Proof.
  induction L1 as [|[k e] L1 IH]; intros L2 n.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. replace (S n + length L1)%nat with (n + S (length L1))%nat by lia.
    destruct (Nat.eqb k n), (vars_below k e), (well_formed (S n) L1); reflexivity.
Qed.

Lemma with_dd_triple_wf :
  forall n e, vars_below n e = true ->
  well_formed (lm n) [(lm n, ren lm e); (lp n, ren lp e); (ld n, dd fx e)] = true.
Proof.
  intros n e He.
  assert (Hr : forall k, occurs k e -> (k < n)%nat) by (intros k; apply occurs_below; exact He).
  assert (E1 : (lm n =? lm n)%nat = true) by (apply Nat.eqb_eq; reflexivity).
  assert (E2 : (lp n =? S (lm n))%nat = true) by (unfold lp, lm; apply Nat.eqb_eq; lia).
  assert (E3 : (ld n =? S (S (lm n)))%nat = true) by (unfold ld, lm; apply Nat.eqb_eq; lia).
  assert (V1 : vars_below (lm n) (ren lm e) = true).
  { apply below_occurs. intros k Hk. destruct (occurs_ren lm k e Hk) as [j [Hj ->]].
    pose proof (Hr j Hj). unfold lm. lia. }
  assert (V2 : vars_below (lp n) (ren lp e) = true).
  { apply below_occurs. intros k Hk. destruct (occurs_ren lp k e Hk) as [j [Hj ->]].
    pose proof (Hr j Hj). unfold lp. lia. }
  assert (V3 : vars_below (ld n) (dd fx e) = true).
  { apply below_occurs. intros k Hk. destruct (occurs_dd fx k e Hk) as [j [Hj Hjk]].
    pose proof (Hr j Hj). unfold lm, lp, ld in *. lia. }
  cbn [well_formed]. rewrite E1, E2, E3, V1, V2, V3. reflexivity.
Qed.

Lemma with_dd_wf :
  forall bs next, well_formed next bs = true -> well_formed (lm next) (with_dd bs) = true.
Proof.
  induction bs as [|[n e] tl IH]; intros next Hwf; [reflexivity|].
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn He]. apply Nat.eqb_eq in Hn. subst n.
  change (with_dd ((next, e) :: tl))
    with ([(lm next, ren lm e); (lp next, ren lp e); (ld next, dd fx e)] ++ with_dd tl).
  rewrite well_formed_app, with_dd_triple_wf by exact He. simpl andb. simpl length.
  replace (lm next + 3)%nat with (lm (S next)) by (unfold lm; lia).
  apply IH. exact Htl.
Qed.

Section Related.

(** The slots the invariant speaks for: the inputs an expression reads and
    every binding. *)
Variable cov : nat -> bool.

(** The three layers related on the covered slots below next, and fixed
    covered slots equal in the two value layers. *)
Definition dd_inv (E : env ExtendedR) (next : nat) : Prop :=
  (forall k am ap d, (k < next)%nat -> cov k = true -> eget (lm k) E Xnan = Xreal am ->
     eget (lp k) E Xnan = Xreal ap -> eget (ld k) E Xnan = Xreal d -> ap - am = h * d) /\
  (forall k, (k < next)%nat -> cov k = true -> fx k = true ->
     eget (lp k) E Xnan = eget (lm k) E Xnan).

Lemma dd_inv_step :
  forall E n e,
  dd_inv E n -> vars_below n e = true -> cov n = true ->
  (forall k, occurs k e -> cov k = true) ->
  (fx n = true -> fixed fx e = true) ->
  dd_inv (xextend E [(lm n, ren lm e); (lp n, ren lp e); (ld n, dd fx e)]) (S n).
Proof.
  intros E n e [Hrel Hfx] Hb Hcn Hcov Hfxn.
  set (g := fun k => eget k E Xnan).
  set (v0 := xeval E (ren lm e)).
  set (E1 := eset (lm n) E v0).
  set (v1 := xeval E1 (ren lp e)).
  set (E2 := eset (lp n) E1 v1).
  set (v2 := xeval E2 (dd fx e)).
  assert (HE : xextend E [(lm n, ren lm e); (lp n, ren lp e); (ld n, dd fx e)]
               = eset (ld n) E2 v2) by reflexivity.
  assert (Hr : forall k, occurs k e -> (k < n)%nat) by (intros k; apply occurs_below; exact Hb).
  assert (Hv0 : v0 = xevalf g (ren lm e)) by (unfold v0; apply xeval_f).
  assert (Hv1 : v1 = xevalf g (ren lp e)).
  { unfold v1. rewrite xeval_f. apply xevalf_ext. intros k Hk.
    destruct (occurs_ren lp k e Hk) as [j [Hj ->]]. pose proof (Hr j Hj).
    unfold E1, g, lm, lp in *. rewrite eget_eset_neq by lia. reflexivity. }
  assert (Hv2 : v2 = xevalf g (dd fx e)).
  { unfold v2. rewrite xeval_f. apply xevalf_ext. intros k Hk.
    destruct (occurs_dd fx k e Hk) as [j [Hj Hjk]]. pose proof (Hr j Hj).
    unfold E2, E1, g, lm, lp, ld in *. rewrite !eget_eset_neq by lia. reflexivity. }
  assert (Hold0 : forall k, (k < n)%nat -> eget (lm k) (eset (ld n) E2 v2) Xnan = eget (lm k) E Xnan).
  { intros k Hk. unfold E2, E1, lm, lp, ld. rewrite !eget_eset_neq by lia. reflexivity. }
  assert (Hold1 : forall k, (k < n)%nat -> eget (lp k) (eset (ld n) E2 v2) Xnan = eget (lp k) E Xnan).
  { intros k Hk. unfold E2, E1, lm, lp, ld. rewrite !eget_eset_neq by lia. reflexivity. }
  assert (Hold2 : forall k, (k < n)%nat -> eget (ld k) (eset (ld n) E2 v2) Xnan = eget (ld k) E Xnan).
  { intros k Hk. unfold E2, E1, lm, lp, ld. rewrite !eget_eset_neq by lia. reflexivity. }
  assert (Hn0 : eget (lm n) (eset (ld n) E2 v2) Xnan = v0).
  { unfold E2, E1, lm, lp, ld. rewrite !eget_eset_neq by lia. apply eget_eset_eq. }
  assert (Hn1 : eget (lp n) (eset (ld n) E2 v2) Xnan = v1).
  { unfold E2, lp, ld. rewrite eget_eset_neq by lia. apply eget_eset_eq. }
  assert (Hn2 : eget (ld n) (eset (ld n) E2 v2) Xnan = v2) by apply eget_eset_eq.
  rewrite HE. split.
  - intros k am ap d Hk Hck Ha Hp Hd.
    destruct (Nat.eq_dec k n) as [->|Hkn].
    + rewrite Hn0, Hv0 in Ha. rewrite Hn1, Hv1 in Hp. rewrite Hn2, Hv2 in Hd.
      apply (dd_correct fx g h e); try assumption.
      * intros k' am' ap' d' Hk'. apply Hrel; [exact (Hr k' Hk') | exact (Hcov k' Hk')].
      * intros k' Hk'. apply Hfx; [exact (Hr k' Hk') | exact (Hcov k' Hk')].
    + assert (Hk' : (k < n)%nat) by lia.
      rewrite (Hold0 k Hk') in Ha. rewrite (Hold1 k Hk') in Hp. rewrite (Hold2 k Hk') in Hd.
      exact (Hrel k am ap d Hk' Hck Ha Hp Hd).
  - intros k Hk Hck Hfk.
    destruct (Nat.eq_dec k n) as [->|Hkn].
    + rewrite Hn0, Hn1, Hv0, Hv1. apply (fixed_layers fx); [| exact (Hfxn Hfk)].
      intros k' Hk' Hfk'. unfold g. apply Hfx; [exact (Hr k' Hk') | exact (Hcov k' Hk') | exact Hfk'].
    + assert (Hk' : (k < n)%nat) by lia.
      rewrite (Hold1 k Hk'), (Hold0 k Hk'). exact (Hfx k Hk' Hck Hfk).
Qed.

(** Well-formed bindings, each fixed slot bound to a fixed expression, keep
    the layers related through the tripled list. *)
Lemma dd_bindings :
  forall bs E next,
  dd_inv E next -> well_formed next bs = true ->
  (forall n e, In (n, e) bs ->
     cov n = true /\ (forall k, occurs k e -> cov k = true) /\
     (fx n = true -> fixed fx e = true)) ->
  dd_inv (xextend E (with_dd bs)) (next + length bs).
Proof.
  induction bs as [|[n e] tl IH]; intros E next Hinv Hwf Hb.
  - simpl. rewrite Nat.add_0_r. exact Hinv.
  - simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He]. apply Nat.eqb_eq in Hn. subst n.
    simpl length.
    replace (next + S (length tl))%nat with (S next + length tl)%nat by lia.
    destruct (Hb next e (or_introl eq_refl)) as [Hc1 [Hc2 Hc3]].
    assert (Hstep := dd_inv_step E next e Hinv He Hc1 Hc2 Hc3).
    change (with_dd ((next, e) :: tl))
      with ([(lm next, ren lm e); (lp next, ren lp e); (ld next, dd fx e)] ++ with_dd tl).
    rewrite xextend_app.
    apply IH; [exact Hstep | exact Htl |].
    intros n' e' Hin. apply Hb. right. exact Hin.
Qed.

End Related.

(** A value layer read as an environment of its own. *)
Definition layer_env (F : env ExtendedR) (f : nat -> nat) (top : nat) : env ExtendedR :=
  of_list (map (fun k => eget (f k) F Xnan) (seq 0 top)).

Lemma nth_map_seq0 :
  forall (f : nat -> ExtendedR) top k d, (k < top)%nat -> nth k (map f (seq 0 top)) d = f k.
Proof.
  intros f top k d Hk.
  rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma eget_layer_env :
  forall F f top k, (k < top)%nat -> eget k (layer_env F f top) Xnan = eget (f k) F Xnan.
Proof.
  intros F f top k Hk. unfold layer_env. rewrite eget_of_list. apply nth_map_seq0. exact Hk.
Qed.

Lemma in_with_dd :
  forall bs n e, In (n, e) bs ->
  In (lm n, ren lm e) (with_dd bs) /\ In (lp n, ren lp e) (with_dd bs) /\
  In (ld n, dd fx e) (with_dd bs).
Proof.
  intros bs n e Hin. unfold with_dd.
  repeat split; apply in_flat_map; exists (n, e); split; try exact Hin; simpl; tauto.
Qed.

(** After the tripled list, each value layer holds what the plain bindings
    compute from that layer's inputs: every binding of the plain list holds
    its value in the layer read as an environment. *)
Lemma layer_sound :
  forall bs E next f, (f = lm \/ f = lp) ->
  well_formed next bs = true ->
  forall n e, In (n, e) bs ->
  let F := xextend E (with_dd bs) in
  eget n (layer_env F f (next + length bs)) Xnan = xeval (layer_env F f (next + length bs)) e.
Proof.
  intros bs E next f Hf Hwf n e Hin F.
  destruct (well_formed_in bs next n e Hwf Hin) as [Hn He].
  assert (Hwf3 := with_dd_wf bs next Hwf).
  assert (Hin3 : In (f n, ren f e) (with_dd bs)).
  { destruct (in_with_dd bs n e Hin) as [H1 [H2 _]]. destruct Hf as [-> | ->]; assumption. }
  assert (Hs := wf_holds (with_dd bs) E (lm next) _ _ Hwf3 Hin3). fold F in Hs.
  rewrite eget_layer_env by lia. rewrite Hs.
  rewrite !xeval_f, xevalf_ren. apply xevalf_ext. intros k Hk.
  symmetry. apply eget_layer_env. pose proof (occurs_below n e k He Hk). lia.
Qed.

End Bindings.
