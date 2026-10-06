(** The divided difference along s of the e-slot partials of the radial
    rows, for the block Q = (Pm(s + h, h) - Pp(s, h)) / h of the one-step
    map, with no h in a denominator.

    [QL_with (fxenv q_in bs) bs] is a list bs over the inputs s, h and t in
    slots 0, 1 and 2, tripled by DivDiff's [with_dd] over the inputs s (minus
    layer), s + h (plus layer) and 1 (difference layer) in slot 0, and h and
    t, the same in both layers, in slots 1 and 2. Its minus and plus layers
    hold the list at s and at s + h, and its difference layer their
    difference over h ([QL_sound]). The fixed slots are found in one pass
    over the list ([fxenv], [fxenv_spec]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Deriv DivDiff LinCheck.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The fixed slots of a list                                         *)

(** Those of f0, and each bound slot whose expression reads fixed slots
    alone. *)
Definition fxenv (f0 : env bool) (bs : list binding) : env bool :=
  fold_left (fun f b => eset (fst b) f (fixed (fun k => eget k f false) (snd b))) bs f0.

Lemma fixed_ext :
  forall f g e, (forall k, occurs k e -> f k = g k) -> fixed f e = fixed g e.
Proof.
  intros f g e. induction e; simpl; intros H.
  - apply H. reflexivity.
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

Lemma fxenv_notin :
  forall bs f0 k, ~ In k (map fst bs) -> eget k (fxenv f0 bs) false = eget k f0 false.
Proof.
  induction bs as [|[n e] tl IH]; intros f0 k Hk; [reflexivity|].
  simpl in Hk. unfold fxenv. cbn [fold_left fst snd]. fold (fxenv (eset n f0 (fixed (fun j => eget j f0 false) e)) tl).
  rewrite IH by tauto. apply eget_eset_neq. intros ->. tauto.
Qed.

(** Every bound slot of a well-formed list is fixed exactly when its
    expression is. *)
Lemma fxenv_spec :
  forall bs f0 next, well_formed next bs = true ->
  forall n e, In (n, e) bs ->
  eget n (fxenv f0 bs) false = fixed (fun k => eget k (fxenv f0 bs) false) e.
Proof.
  induction bs as [|[n0 e0] tl IH]; intros f0 next Hwf n e Hin; [destruct Hin|].
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn0 He0]. apply Nat.eqb_eq in Hn0. subst n0.
  set (f1 := eset next f0 (fixed (fun j => eget j f0 false) e0)).
  change (fxenv f0 ((next, e0) :: tl)) with (fxenv f1 tl). destruct Hin as [Heq|Hin].
  - injection Heq as <- <-.
    assert (Hnot : forall k, (k <= next)%nat -> ~ In k (map fst tl)).
    { intros k Hk Hm. pose proof (well_formed_slots tl (S next) k Htl Hm). lia. }
    rewrite fxenv_notin by (apply Hnot; lia). unfold f1. rewrite eget_eset_eq.
    apply fixed_ext. intros k Hk. pose proof (occurs_below next e0 k He0 Hk) as Hkn.
    rewrite fxenv_notin by (apply Hnot; lia). unfold f1. rewrite eget_eset_neq by lia. reflexivity.
  - exact (IH f1 (S next) Htl n e Hin).
Qed.

(* ---------------------------------------------------------------- *)
(* The tripled list                                                  *)

(** h and t are fixed, s is not. *)
Definition q_in : env bool := eset 2 (eset 1 eempty true) true.

Definition QL_with (fe : env bool) (bs : list binding) : list binding :=
  with_dd (fun k => eget k fe false) bs.

(** The inputs of the three layers, slot j of layer f at f j. *)
Definition qin (s h t : R) : env ExtendedR :=
  of_list [Xreal s; Xreal (s + h); Xreal 1; Xreal h; Xreal h; Xreal 0; Xreal t; Xreal t; Xreal 0].

(** The inputs of the plain list. *)
Definition pin (s h t : R) : env ExtendedR :=
  eset 2 (eset 1 (eset 0 eempty (Xreal s)) (Xreal h)) (Xreal t).

(* ---------------------------------------------------------------- *)
(* Soundness                                                         *)

(** An environment in which every binding of a well-formed list holds its
    value, and which agrees with E below the list, agrees with the list
    evaluated from E. *)
Lemma wf_agree :
  forall bs next G E,
  well_formed next bs = true ->
  (forall k, (k < next)%nat -> eget k G Xnan = eget k E Xnan) ->
  (forall n e, In (n, e) bs -> eget n G Xnan = xeval G e) ->
  forall k, (k < next + length bs)%nat -> eget k G Xnan = eget k (xextend E bs) Xnan.
Proof.
  induction bs as [|[n0 e0] tl IH]; intros next G E Hwf Hlow Hb k Hk.
  - simpl in Hk. rewrite Nat.add_0_r in Hk. exact (Hlow k Hk).
  - simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn0 He0]. apply Nat.eqb_eq in Hn0. subst n0.
    change (xextend E ((next, e0) :: tl)) with (xextend (eset next E (xeval E e0)) tl).
    apply (IH (S next)); [exact Htl | | | simpl length in Hk; lia].
    + intros j Hj. destruct (Nat.eq_dec j next) as [->|Hne].
      * rewrite eget_eset_eq. rewrite (Hb next e0 (or_introl eq_refl)).
        rewrite !xeval_f. apply xevalf_ext. intros i Hi.
        apply Hlow. exact (occurs_below next e0 i He0 Hi).
      * rewrite eget_eset_neq by exact Hne. apply Hlow. lia.
    + intros n e Hin. apply Hb. right. exact Hin.
Qed.

Section Sound.

Variable bs : list binding.
Hypothesis Hwf : well_formed 3 bs = true.

Let fx : nat -> bool := fun j => eget j (fxenv q_in bs) false.
Let top : nat := (3 + length bs)%nat.
Let QL : list binding := QL_with (fxenv q_in bs) bs.

Lemma QL_eq : QL = with_dd fx bs.
Proof. reflexivity. Qed.

(** The inputs are not written by the tripled list. *)
Lemma qin_kept :
  forall s h t j, (j < 9)%nat -> eget j (xextend (qin s h t) QL) Xnan = eget j (qin s h t) Xnan.
Proof.
  intros s h t j Hj. rewrite QL_eq. apply eget_xextend_notin. intros Hin.
  pose proof (well_formed_slots _ (lm 3) j (with_dd_wf fx bs 3 Hwf) Hin) as H. unfold lm in H. lia.
Qed.

Lemma fx_inputs : fx 0 = false.
Proof.
  unfold fx. rewrite fxenv_notin; [reflexivity|].
  intros Hin. pose proof (well_formed_slots bs 3 0 Hwf Hin). lia.
Qed.

Lemma qin_inv : forall s h t, dd_inv fx h (fun _ => true) (qin s h t) 3.
Proof.
  intros s h t. split.
  - intros j am ap d Hj _ Ha Hp Hd.
    destruct j as [|[|[|j]]]; [| | | lia]; cbn in Ha, Hp, Hd;
      injection Ha as <-; injection Hp as <-; injection Hd as <-; ring.
  - intros j Hj _ Hf. destruct j as [|[|[|j]]]; [| reflexivity | reflexivity | lia].
    rewrite fx_inputs in Hf. discriminate.
Qed.

(** The two value layers are the plain list at s and at s + h, and the
    difference layer is their difference over h. *)
Theorem QL_sound :
  forall s h t n, (3 <= n < top)%nat ->
  let F := xextend (qin s h t) QL in
  eget (lm n) F Xnan = eget n (xextend (pin s h t) bs) Xnan /\
  eget (lp n) F Xnan = eget n (xextend (pin (s + h) h t) bs) Xnan /\
  (forall am ap d, eget (lm n) F Xnan = Xreal am -> eget (lp n) F Xnan = Xreal ap ->
     eget (ld n) F Xnan = Xreal d -> ap - am = h * d).
Proof.
  intros s h t n Hn F.
  assert (Hlay : forall f E, (f = lm \/ f = lp) ->
            (forall j, (j < 3)%nat -> eget (f j) (qin s h t) Xnan = eget j E Xnan) ->
            eget (f n) F Xnan = eget n (xextend E bs) Xnan).
  { intros f E Hf HE.
    rewrite <- (eget_layer_env F f top n) by lia.
    apply (wf_agree bs 3 (layer_env F f top) E Hwf); [| | unfold top in Hn |- *; lia].
    - intros j Hj. rewrite eget_layer_env by (unfold top; lia). unfold F.
      rewrite qin_kept by (destruct Hf as [-> | ->]; unfold lm, lp; lia). exact (HE j Hj).
    - intros m e Hin. unfold F. rewrite QL_eq.
      exact (layer_sound fx bs (qin s h t) 3 f Hf Hwf m e Hin). }
  split; [| split].
  - apply Hlay; [left; reflexivity|].
    intros j Hj. destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia].
  - apply Hlay; [right; reflexivity|].
    intros j Hj. destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia].
  - intros am ap d Ha Hp Hd.
    assert (Hinv := dd_bindings fx h (fun _ => true) bs (qin s h t) 3 (qin_inv s h t) Hwf).
    destruct Hinv as [Hrel _].
    + intros m e Hin. split; [reflexivity|]. split; [intros; reflexivity|].
      intros Hfm. unfold fx in *. rewrite <- (fxenv_spec bs q_in 3 Hwf m e Hin). exact Hfm.
    + unfold F in Ha, Hp, Hd. rewrite QL_eq in Ha, Hp, Hd.
      exact (Hrel n am ap d ltac:(unfold top in Hn; lia) eq_refl Ha Hp Hd).
Qed.

End Sound.
