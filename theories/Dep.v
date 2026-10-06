(** Independence of a binding list's slots from marked inputs.

    [deps] marks every slot whose expression reads a marked input or a
    marked slot. [dep_sound]: a slot left unmarked has the same value on two
    environments that agree on the unmarked inputs, whatever the marked ones
    hold. *)

From Coq Require Import ZArith Reals List Bool Lia.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Deriv DivDiff AdjointSound.

Import ListNotations.

Fixpoint edep (D : env bool) (e : expr) : bool :=
  match e with
  | Evar k => eget k D false
  | EfromZ _ | Epi | Epow2 _ => false
  | Eneg a | Esqrt a | Esin a | Ecos a | Eexp a | Eatan a => edep D a
  | Eadd a b | Esub a b | Emul a b | Ediv a b => edep D a || edep D b
  end.

(** An expression reading no marked slot below n has one value on
    environments that agree on the unmarked slots below n. *)
Lemma xeval_dep :
  forall e D n (E1 E2 : env ExtendedR), vars_below n e = true ->
  (forall k, (k < n)%nat -> eget k D false = false -> eget k E1 Xnan = eget k E2 Xnan) ->
  edep D e = false -> xeval E1 e = xeval E2 e.
Proof.
  induction e; intros D nb E1 E2 Hv Hag Hd; cbn [vars_below edep] in Hv, Hd; cbn [xeval]; try reflexivity.
  - apply Nat.ltb_lt in Hv. exact (Hag _ Hv Hd).
  - rewrite (IHe D nb E1 E2 Hv Hag Hd). reflexivity.
  - apply andb_prop in Hv. destruct Hv as [Ha Hb]. apply orb_false_iff in Hd. destruct Hd as [Da Db].
    rewrite (IHe1 D nb E1 E2 Ha Hag Da), (IHe2 D nb E1 E2 Hb Hag Db). reflexivity.
  - apply andb_prop in Hv. destruct Hv as [Ha Hb]. apply orb_false_iff in Hd. destruct Hd as [Da Db].
    rewrite (IHe1 D nb E1 E2 Ha Hag Da), (IHe2 D nb E1 E2 Hb Hag Db). reflexivity.
  - apply andb_prop in Hv. destruct Hv as [Ha Hb]. apply orb_false_iff in Hd. destruct Hd as [Da Db].
    rewrite (IHe1 D nb E1 E2 Ha Hag Da), (IHe2 D nb E1 E2 Hb Hag Db). reflexivity.
  - apply andb_prop in Hv. destruct Hv as [Ha Hb]. apply orb_false_iff in Hd. destruct Hd as [Da Db].
    rewrite (IHe1 D nb E1 E2 Ha Hag Da), (IHe2 D nb E1 E2 Hb Hag Db). reflexivity.
  - rewrite (IHe D nb E1 E2 Hv Hag Hd). reflexivity.
  - rewrite (IHe D nb E1 E2 Hv Hag Hd). reflexivity.
  - rewrite (IHe D nb E1 E2 Hv Hag Hd). reflexivity.
  - rewrite (IHe D nb E1 E2 Hv Hag Hd). reflexivity.
  - rewrite (IHe D nb E1 E2 Hv Hag Hd). reflexivity.
Qed.

Section Dep.

Variable base : nat.
Variable mark : nat -> bool.

Definition dp0 : env bool := fold_left (fun D k => eset k D (mark k)) (seq 0 base) eempty.

Definition deps (p : list binding) : env bool := fold_left (fun D b => eset (fst b) D (edep D (snd b))) p dp0.

Lemma dp0_get : forall k, (k < base)%nat -> eget k dp0 false = mark k.
Proof.
  intros k Hk. unfold dp0.
  assert (Gen : forall l D, NoDup l -> In k l ->
            eget k (fold_left (fun D k => eset k D (mark k)) l D) false = mark k).
  { induction l as [|a l IH]; intros D Hnd Hin; [destruct Hin|].
    cbn [fold_left]. inversion Hnd as [|? ? Hna Hnd']; subst.
    destruct Hin as [->|Hin].
    - assert (Hkeep : forall l' D', ~ In k l' ->
                eget k (fold_left (fun D k0 => eset k0 D (mark k0)) l' D') false = eget k D' false).
      { induction l' as [|a' l' IH']; intros D' Hn; [reflexivity|]. cbn [fold_left].
        rewrite IH' by (intros H; apply Hn; right; exact H). apply eget_eset_neq. intros E. apply Hn. left.
        symmetry. exact E. }
      rewrite Hkeep by exact Hna. apply eget_eset_eq.
    - apply IH; assumption. }
  apply Gen; [apply seq_NoDup | apply in_seq; lia].
Qed.

Lemma deps_snoc : forall p b, deps (p ++ [b]) = eset (fst b) (deps p) (edep (deps p) (snd b)).
Proof. intros p b. unfold deps. rewrite fold_left_app. reflexivity. Qed.

Theorem dep_sound :
  forall p (E E' : env ExtendedR), well_formed base p = true ->
  (forall j, (j < base)%nat -> mark j = false -> eget j E' Xnan = eget j E Xnan) ->
  forall k, (k < base + length p)%nat -> eget k (deps p) false = false ->
  eget k (xextend E' p) Xnan = eget k (xextend E p) Xnan.
Proof.
  induction p as [|[n e] p IH] using rev_ind; intros E E' Hwf Hun k Hk Hd.
  - cbn [length] in Hk. rewrite Nat.add_0_r in Hk. unfold deps in Hd. cbn [fold_left] in Hd.
    rewrite (dp0_get k Hk) in Hd. apply Hun; assumption.
  - rewrite DivDiff.well_formed_app in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfb].
    cbn [well_formed] in Hwfb. apply andb_prop in Hwfb. destruct Hwfb as [Hwfb _].
    apply andb_prop in Hwfb. destruct Hwfb as [Hn Hve]. apply Nat.eqb_eq in Hn.
    rewrite length_app in Hk. cbn [length] in Hk.
    rewrite deps_snoc in Hd. cbn [fst snd] in Hd.
    rewrite !xextend_snoc.
    destruct (Nat.eq_dec k n) as [->|Hkn].
    + rewrite eget_eset_eq in Hd. rewrite !eget_eset_eq.
      apply (xeval_dep e (deps p) (base + length p)); [rewrite <- Hn; exact Hve | | exact Hd].
      intros j Hj Hdj. apply IH; assumption.
    + rewrite eget_eset_neq in Hd by exact Hkn. rewrite !eget_eset_neq by exact Hkn.
      apply IH; [exact Hwfp | exact Hun | lia | exact Hd].
Qed.

End Dep.
