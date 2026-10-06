(** What the adjoint lists hold.

    [anf_sound]: for every environment of its inputs, the flattened list
    holds in slot [rget m n] the value that binding n of the original list
    holds. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive.
From Stellarocq Require Import Expr Deriv DivDiff DerivSeq Mat Adjoint.

Import ListNotations.

(* ---------------------------------------------------------------- *)
(* Lists that write above a slot                                     *)

Lemma vars_below_mono : forall n m e, vars_below n e = true -> (n <= m)%nat -> vars_below m e = true.
Proof.
  intros n m e H Hnm. induction e; cbn in *;
    try (apply andb_prop in H; destruct H as [H1 H2]; rewrite IHe1, IHe2 by assumption; reflexivity);
    try (apply IHe; assumption); try reflexivity.
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Lemma eget_above :
  forall L E n k, well_formed n L = true -> (k < n)%nat -> eget k (xextend E L) Xnan = eget k E Xnan.
Proof.
  intros L E n k Hwf Hk. apply eget_xextend_notin. intros Hin.
  pose proof (well_formed_slots L n k Hwf Hin). lia.
Qed.

Lemma xeval_above :
  forall L E n e, well_formed n L = true -> vars_below n e = true -> xeval (xextend E L) e = xeval E e.
Proof.
  intros L E n e Hwf He. rewrite !xeval_f. apply xevalf_ext. intros k Hk.
  apply (eget_above L E n k Hwf). exact (occurs_below n e k He Hk).
Qed.

Lemma xextend_snoc :
  forall E L n e, xextend E (L ++ [(n, e)]) = eset n (xextend E L) (xeval (xextend E L) e).
Proof. intros. rewrite xextend_app. reflexivity. Qed.

Lemma wf_snoc :
  forall L next n e, well_formed next L = true -> n = (next + length L)%nat -> vars_below n e = true ->
  well_formed next (L ++ [(n, e)]) = true.
Proof.
  intros L next n e HL Hn He. rewrite DivDiff.well_formed_app, HL. cbn [andb well_formed].
  rewrite <- Hn, Nat.eqb_refl, He. reflexivity.
Qed.

Lemma wf_cat :
  forall L1 L2 n1 n2, well_formed n1 L1 = true -> well_formed n2 L2 = true -> n2 = (n1 + length L1)%nat ->
  well_formed n1 (L1 ++ L2) = true.
Proof. intros L1 L2 n1 n2 H1 H2 Hn. rewrite DivDiff.well_formed_app, H1, <- Hn, H2. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* One expression                                                    *)

(** The value of e when slot j reads the slot rget m j of E. *)
Definition rval (m : env nat) (E : env ExtendedR) (e : expr) : ExtendedR :=
  xevalf (fun j => eget (rget m j) E Xnan) e.

Lemma anf_e_spec :
  forall e m next acc a next' acc',
  (forall j, occurs j e -> (rget m j < next)%nat) ->
  anf_e m e next acc = (a, next', acc') ->
  exists new, acc' = new ++ acc /\ length new = (next' - next)%nat /\ (next <= next')%nat /\
    well_formed next (rev new) = true /\ vars_below next' a = true /\
    forall E, xeval (xextend E (rev new)) a = rval m E e.
Proof.
  induction e; intros m next acc a next' acc' Hocc Hcall; cbn [anf_e] in Hcall.
  - (* Evar *)
    injection Hcall as <- <- <-. exists []. cbn [rev app length]. split; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + cbn. apply Nat.ltb_lt. apply Hocc. reflexivity.
    + intros E. reflexivity.
  - injection Hcall as <- <- <-. exists []. split; [reflexivity|]. split; [cbn; lia|]. split; [lia|].
    split; [reflexivity|]. split; [reflexivity|]. intros E; reflexivity.
  - injection Hcall as <- <- <-. exists []. split; [reflexivity|]. split; [cbn; lia|]. split; [lia|].
    split; [reflexivity|]. split; [reflexivity|]. intros E; reflexivity.
  - (* Eneg *)
    destruct (anf_e m e next acc) as [[a1 n1] acc1] eqn:H1. injection Hcall as <- <- <-.
    destruct (IHe m next acc a1 n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    exists ((n1, Eneg a1) :: new1). split; [rewrite E1; reflexivity|].
    split; [cbn [length]; lia|]. split; [lia|]. cbn [rev]. split.
    { apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1]. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval]. rewrite X1. reflexivity.
  - (* Eadd *)
    destruct (anf_e m e1 next acc) as [[a1 n1] acc1] eqn:H1.
    destruct (anf_e m e2 n1 acc1) as [[a2 n2] acc2] eqn:H2. injection Hcall as <- <- <-.
    destruct (IHe1 m next acc a1 n1 acc1 (fun j Hj => Hocc j (or_introl Hj)) H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    assert (Hocc2 : forall j, occurs j e2 -> (rget m j < n1)%nat) by (intros j Hj; specialize (Hocc j (or_intror Hj)); lia).
    destruct (IHe2 m n1 acc1 a2 n2 acc2 Hocc2 H2) as (new2 & E2 & L2 & N2 & W2 & V2 & X2).
    exists ((n2, Eadd a1 a2) :: new2 ++ new1). split; [rewrite E2, E1, app_assoc; reflexivity|].
    split; [cbn [length]; rewrite length_app; lia|]. split; [lia|]. cbn [rev]. rewrite rev_app_distr.
    split.
    { apply wf_snoc; [apply (wf_cat _ _ next n1); [exact W1 | exact W2 | rewrite length_rev; lia] |
                      rewrite length_app, !length_rev; lia |].
      cbn. rewrite (vars_below_mono n1 n2 a1 V1 N2), V2. reflexivity. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval].
    rewrite xextend_app. rewrite X2.
    rewrite (xeval_above (rev new2) _ n1 a1 W2 V1), X1.
    unfold rval. cbn [xevalf]. f_equal. apply xevalf_ext. intros j Hj.
    apply (eget_above (rev new1) E next); [exact W1 | apply Hocc; right; exact Hj].
  - (* Esub *)
    destruct (anf_e m e1 next acc) as [[a1 n1] acc1] eqn:H1.
    destruct (anf_e m e2 n1 acc1) as [[a2 n2] acc2] eqn:H2. injection Hcall as <- <- <-.
    destruct (IHe1 m next acc a1 n1 acc1 (fun j Hj => Hocc j (or_introl Hj)) H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    assert (Hocc2 : forall j, occurs j e2 -> (rget m j < n1)%nat) by (intros j Hj; specialize (Hocc j (or_intror Hj)); lia).
    destruct (IHe2 m n1 acc1 a2 n2 acc2 Hocc2 H2) as (new2 & E2 & L2 & N2 & W2 & V2 & X2).
    exists ((n2, Esub a1 a2) :: new2 ++ new1). split; [rewrite E2, E1, app_assoc; reflexivity|].
    split; [cbn [length]; rewrite length_app; lia|]. split; [lia|]. cbn [rev]. rewrite rev_app_distr.
    split.
    { apply wf_snoc; [apply (wf_cat _ _ next n1); [exact W1 | exact W2 | rewrite length_rev; lia] |
                      rewrite length_app, !length_rev; lia |].
      cbn. rewrite (vars_below_mono n1 n2 a1 V1 N2), V2. reflexivity. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval].
    rewrite xextend_app. rewrite X2.
    rewrite (xeval_above (rev new2) _ n1 a1 W2 V1), X1.
    unfold rval. cbn [xevalf]. f_equal. apply xevalf_ext. intros j Hj.
    apply (eget_above (rev new1) E next); [exact W1 | apply Hocc; right; exact Hj].
  - (* Emul *)
    destruct (anf_e m e1 next acc) as [[a1 n1] acc1] eqn:H1.
    destruct (anf_e m e2 n1 acc1) as [[a2 n2] acc2] eqn:H2. injection Hcall as <- <- <-.
    destruct (IHe1 m next acc a1 n1 acc1 (fun j Hj => Hocc j (or_introl Hj)) H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    assert (Hocc2 : forall j, occurs j e2 -> (rget m j < n1)%nat) by (intros j Hj; specialize (Hocc j (or_intror Hj)); lia).
    destruct (IHe2 m n1 acc1 a2 n2 acc2 Hocc2 H2) as (new2 & E2 & L2 & N2 & W2 & V2 & X2).
    exists ((n2, Emul a1 a2) :: new2 ++ new1). split; [rewrite E2, E1, app_assoc; reflexivity|].
    split; [cbn [length]; rewrite length_app; lia|]. split; [lia|]. cbn [rev]. rewrite rev_app_distr.
    split.
    { apply wf_snoc; [apply (wf_cat _ _ next n1); [exact W1 | exact W2 | rewrite length_rev; lia] |
                      rewrite length_app, !length_rev; lia |].
      cbn. rewrite (vars_below_mono n1 n2 a1 V1 N2), V2. reflexivity. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval].
    rewrite xextend_app. rewrite X2.
    rewrite (xeval_above (rev new2) _ n1 a1 W2 V1), X1.
    unfold rval. cbn [xevalf]. f_equal. apply xevalf_ext. intros j Hj.
    apply (eget_above (rev new1) E next); [exact W1 | apply Hocc; right; exact Hj].
  - (* Ediv *)
    destruct (anf_e m e1 next acc) as [[a1 n1] acc1] eqn:H1.
    destruct (anf_e m e2 n1 acc1) as [[a2 n2] acc2] eqn:H2. injection Hcall as <- <- <-.
    destruct (IHe1 m next acc a1 n1 acc1 (fun j Hj => Hocc j (or_introl Hj)) H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    assert (Hocc2 : forall j, occurs j e2 -> (rget m j < n1)%nat) by (intros j Hj; specialize (Hocc j (or_intror Hj)); lia).
    destruct (IHe2 m n1 acc1 a2 n2 acc2 Hocc2 H2) as (new2 & E2 & L2 & N2 & W2 & V2 & X2).
    exists ((n2, Ediv a1 a2) :: new2 ++ new1). split; [rewrite E2, E1, app_assoc; reflexivity|].
    split; [cbn [length]; rewrite length_app; lia|]. split; [lia|]. cbn [rev]. rewrite rev_app_distr.
    split.
    { apply wf_snoc; [apply (wf_cat _ _ next n1); [exact W1 | exact W2 | rewrite length_rev; lia] |
                      rewrite length_app, !length_rev; lia |].
      cbn. rewrite (vars_below_mono n1 n2 a1 V1 N2), V2. reflexivity. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval].
    rewrite xextend_app. rewrite X2.
    rewrite (xeval_above (rev new2) _ n1 a1 W2 V1), X1.
    unfold rval. cbn [xevalf]. f_equal. apply xevalf_ext. intros j Hj.
    apply (eget_above (rev new1) E next); [exact W1 | apply Hocc; right; exact Hj].
  - (* Esqrt *)
    destruct (anf_e m e next acc) as [[a1 n1] acc1] eqn:H1. injection Hcall as <- <- <-.
    destruct (IHe m next acc a1 n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    exists ((n1, Esqrt a1) :: new1). split; [rewrite E1; reflexivity|].
    split; [cbn [length]; lia|]. split; [lia|]. cbn [rev]. split.
    { apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1]. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval]. rewrite X1. reflexivity.
  - (* Esin *)
    destruct (anf_e m e next acc) as [[a1 n1] acc1] eqn:H1. injection Hcall as <- <- <-.
    destruct (IHe m next acc a1 n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    exists ((n1, Esin a1) :: new1). split; [rewrite E1; reflexivity|].
    split; [cbn [length]; lia|]. split; [lia|]. cbn [rev]. split.
    { apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1]. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval]. rewrite X1. reflexivity.
  - (* Ecos *)
    destruct (anf_e m e next acc) as [[a1 n1] acc1] eqn:H1. injection Hcall as <- <- <-.
    destruct (IHe m next acc a1 n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    exists ((n1, Ecos a1) :: new1). split; [rewrite E1; reflexivity|].
    split; [cbn [length]; lia|]. split; [lia|]. cbn [rev]. split.
    { apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1]. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval]. rewrite X1. reflexivity.
  - (* Eexp *)
    destruct (anf_e m e next acc) as [[a1 n1] acc1] eqn:H1. injection Hcall as <- <- <-.
    destruct (IHe m next acc a1 n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    exists ((n1, Eexp a1) :: new1). split; [rewrite E1; reflexivity|].
    split; [cbn [length]; lia|]. split; [lia|]. cbn [rev]. split.
    { apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1]. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval]. rewrite X1. reflexivity.
  - (* Eatan *)
    destruct (anf_e m e next acc) as [[a1 n1] acc1] eqn:H1. injection Hcall as <- <- <-.
    destruct (IHe m next acc a1 n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    exists ((n1, Eatan a1) :: new1). split; [rewrite E1; reflexivity|].
    split; [cbn [length]; lia|]. split; [lia|]. cbn [rev]. split.
    { apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1]. }
    split; [cbn [vars_below]; apply Nat.ltb_lt; lia|].
    intros E. rewrite xextend_snoc. cbn [xeval]. rewrite eget_eset_eq. cbn [xeval]. rewrite X1. reflexivity.
  - injection Hcall as <- <- <-. exists []. split; [reflexivity|]. split; [cbn; lia|]. split; [lia|].
    split; [reflexivity|]. split; [reflexivity|]. intros E; reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* The list                                                          *)

Lemma anf_l_spec :
  forall bs m next acc m' top racc n0 (Eo Ea : env ExtendedR),
  well_formed n0 bs = true ->
  (forall j, (j < n0)%nat -> (rget m j < next)%nat) ->
  (forall j, (j < n0)%nat -> eget (rget m j) Ea Xnan = eget j Eo Xnan) ->
  anf_l m bs next acc = (m', top, racc) ->
  exists new, racc = new ++ acc /\ length new = (top - next)%nat /\ (next <= top)%nat /\
    well_formed next (rev new) = true /\
    (forall j, (j < n0 + length bs)%nat -> (rget m' j < top)%nat) /\
    (forall j, (j < n0)%nat -> rget m' j = rget m j) /\
    (forall j, (j < n0 + length bs)%nat ->
       eget (rget m' j) (xextend Ea (rev new)) Xnan = eget j (xextend Eo bs) Xnan).
Proof.
  induction bs as [|[n e] tl IH]; intros m next acc m' top racc n0 Eo Ea Hwf Hlt Hf Hcall.
  - cbn [anf_l] in Hcall. injection Hcall as <- <- <-. exists [].
    split; [reflexivity|]. split; [cbn; lia|]. split; [lia|]. split; [reflexivity|].
    split; [intros j Hj; apply Hlt; cbn [length] in Hj; lia|]. split; [intros; reflexivity|].
    intros j Hj. cbn [length] in Hj. change (xextend Ea (rev [])) with Ea. change (xextend Eo []) with Eo.
    apply Hf. lia.
  - cbn [well_formed] in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He]. apply Nat.eqb_eq in Hn. subst n.
    cbn [anf_l] in Hcall.
    destruct (anf_e m e next acc) as [[a n1] acc1] eqn:H1. cbv beta iota zeta in Hcall.
    assert (Hocc : forall j, occurs j e -> (rget m j < next)%nat)
      by (intros j Hj; apply Hlt; exact (occurs_below n0 e j He Hj)).
    destruct (anf_e_spec e m next acc a n1 acc1 Hocc H1) as (new1 & E1 & L1 & N1 & W1 & V1 & X1).
    assert (Hval : xeval (xextend Ea (rev new1)) a = xeval Eo e).
    { rewrite X1. unfold rval. rewrite xeval_f. apply xevalf_ext. intros j Hj.
      apply Hf. exact (occurs_below n0 e j He Hj). }
    set (Eo1 := eset n0 Eo (xeval Eo e)).
    assert (HEo : xextend Eo ((n0, e) :: tl) = xextend Eo1 tl) by reflexivity.
    assert (Hold : forall j, (j < n0)%nat -> eget (rget m j) (xextend Ea (rev new1)) Xnan = eget j Eo1 Xnan).
    { intros j Hj. rewrite (eget_above (rev new1) Ea next) by (exact W1 || exact (Hlt j Hj)).
      unfold Eo1. rewrite eget_eset_neq by lia. exact (Hf j Hj). }
    assert (Hcases : (exists ja, a = Evar ja) \/
                     anf_l (eset n0 m n1) tl (S n1) ((n1, a) :: acc1) = (m', top, racc)).
    { destruct a; [left; eexists; reflexivity | right; exact Hcall ..]. }
    destruct Hcases as [[ja ->] | Hc].
    + (* the value is in slot ja already *)
      cbv beta iota in Hcall.
      assert (Hja : (ja < n1)%nat) by (cbn [vars_below] in V1; apply Nat.ltb_lt; exact V1).
      assert (Hlt' : forall j, (j < S n0)%nat -> (rget (eset n0 m ja) j < n1)%nat).
      { intros j Hj. unfold rget. destruct (Nat.eq_dec j n0) as [->|Hne].
        - rewrite eget_eset_eq. exact Hja.
        - rewrite eget_eset_neq by exact Hne. fold (rget m j). specialize (Hlt j ltac:(lia)). lia. }
      assert (Hf' : forall j, (j < S n0)%nat ->
                eget (rget (eset n0 m ja) j) (xextend Ea (rev new1)) Xnan = eget j Eo1 Xnan).
      { intros j Hj. unfold rget. destruct (Nat.eq_dec j n0) as [->|Hne].
        - rewrite eget_eset_eq. unfold Eo1. rewrite eget_eset_eq. exact Hval.
        - rewrite eget_eset_neq by exact Hne. fold (rget m j). apply Hold. lia. }
      destruct (IH (eset n0 m ja) n1 acc1 m' top racc (S n0) Eo1 (xextend Ea (rev new1)) Htl Hlt' Hf' Hcall)
        as (new2 & E2 & L2 & N2 & W2 & R2 & S2 & F2).
      exists (new2 ++ new1). split; [rewrite E2, E1, app_assoc; reflexivity|].
      split; [rewrite length_app; lia|]. split; [lia|].
      split; [rewrite rev_app_distr; apply (wf_cat _ _ next n1); [exact W1 | exact W2 | rewrite length_rev; lia]|].
      split; [intros j Hj; apply R2; cbn [length] in Hj; lia|].
      split; [intros j Hj; rewrite (S2 j ltac:(lia)); unfold rget; rewrite eget_eset_neq by lia; reflexivity|].
      intros j Hj. rewrite rev_app_distr, xextend_app. exact (F2 j ltac:(cbn [length] in Hj; lia)).
    + (* a constant: a slot of its own *)
      assert (Hlt' : forall j, (j < S n0)%nat -> (rget (eset n0 m n1) j < S n1)%nat).
      { intros j Hj. unfold rget. destruct (Nat.eq_dec j n0) as [->|Hne].
        - rewrite eget_eset_eq. lia.
        - rewrite eget_eset_neq by exact Hne. fold (rget m j). specialize (Hlt j ltac:(lia)). lia. }
      set (Ea1 := xextend Ea (rev ((n1, a) :: new1))).
      assert (HEa1 : Ea1 = eset n1 (xextend Ea (rev new1)) (xeval (xextend Ea (rev new1)) a))
        by (unfold Ea1; cbn [rev]; apply xextend_snoc).
      assert (Hf' : forall j, (j < S n0)%nat -> eget (rget (eset n0 m n1) j) Ea1 Xnan = eget j Eo1 Xnan).
      { intros j Hj. rewrite HEa1. unfold rget. destruct (Nat.eq_dec j n0) as [->|Hne].
        - rewrite !eget_eset_eq. unfold Eo1. rewrite eget_eset_eq. exact Hval.
        - rewrite (eget_eset_neq _ n0 j m) by exact Hne. fold (rget m j).
          rewrite eget_eset_neq by (specialize (Hlt j ltac:(lia)); lia). apply Hold. lia. }
      destruct (IH (eset n0 m n1) (S n1) ((n1, a) :: acc1) m' top racc (S n0) Eo1 Ea1 Htl Hlt' Hf' Hc)
        as (new2 & E2 & L2 & N2 & W2 & R2 & S2 & F2).
      exists (new2 ++ (n1, a) :: new1). split; [rewrite E2, E1; rewrite <- app_assoc; reflexivity|].
      split; [rewrite length_app; cbn [length]; lia|]. split; [lia|].
      split.
      { rewrite rev_app_distr. apply (wf_cat _ _ next (S n1)); [| exact W2 |].
        - cbn [rev]. apply wf_snoc; [exact W1 | rewrite length_rev; lia | exact V1].
        - cbn [rev]. rewrite length_app, length_rev. cbn [length]. lia. }
      split; [intros j Hj; apply R2; cbn [length] in Hj; lia|].
      split; [intros j Hj; rewrite (S2 j ltac:(lia)); unfold rget; rewrite eget_eset_neq by lia; reflexivity|].
      intros j Hj. rewrite rev_app_distr, xextend_app. exact (F2 j ltac:(cbn [length] in Hj; lia)).
Qed.

(** The flattened list holds every value of the original one. *)
Theorem anf_sound :
  forall base bs ab m top, well_formed base bs = true -> anf base bs = (ab, m, top) ->
  well_formed base ab = true /\ top = (base + length ab)%nat /\
  (forall j, (j < base)%nat -> rget m j = j) /\
  (forall j, (j < base + length bs)%nat -> (rget m j < top)%nat) /\
  (forall E j, (j < base + length bs)%nat -> eget (rget m j) (xextend E ab) Xnan = eget j (xextend E bs) Xnan).
Proof.
  intros base bs ab m top Hwf Ha. unfold anf in Ha.
  destruct (anf_l eempty bs base []) as [[m0 top0] racc] eqn:Hl. injection Ha as <- <- <-.
  assert (Hlt0 : forall j, (j < base)%nat -> (rget eempty j < base)%nat)
    by (intros j Hj; unfold rget; rewrite eget_eempty; exact Hj).
  assert (Hf0 : forall E j, (j < base)%nat -> eget (rget eempty j) E Xnan = eget j E Xnan)
    by (intros E j Hj; unfold rget; rewrite eget_eempty; reflexivity).
  destruct (anf_l_spec bs eempty base [] m0 top0 racc base eempty eempty Hwf Hlt0 (Hf0 eempty) Hl)
    as (new & Er & L & N & W & R & S & _).
  rewrite app_nil_r in Er. subst new.
  split; [exact W|]. split; [rewrite length_rev; lia|].
  split; [intros j Hj; rewrite (S j Hj); unfold rget; apply eget_eempty|].
  split; [exact R|].
  intros E j Hj.
  destruct (anf_l_spec bs eempty base [] m0 top0 racc base E E Hwf Hlt0 (Hf0 E) Hl)
    as (new & Er & _ & _ & _ & _ & _ & F).
  rewrite app_nil_r in Er. subst new. exact (F j Hj).
Qed.

(* ---------------------------------------------------------------- *)
(* Sums                                                              *)

Local Open Scope R_scope.

Lemma msum_shift : forall f n, msum f (S n) = f 0%nat + msum (fun k => f (S k)) n.
Proof.
  intros f n. induction n as [|n IH]; cbn [msum]; [ring|].
  cbn [msum] in IH. rewrite IH. ring.
Qed.

(** A sum over the slots next, next + 1, ... of a well-formed list. *)
Lemma lsum_msum :
  forall (F : nat -> expr -> R) bl next d, well_formed next bl = true ->
  fold_right (fun b s => F (fst b) (snd b) + s) 0 bl
  = msum (fun k => F (next + k)%nat (snd (nth k bl d))) (length bl).
Proof.
  induction bl as [|[n e] tl IH]; intros next d Hwf; [reflexivity|].
  cbn in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl]. apply andb_prop in Hwf. destruct Hwf as [Hn _].
  apply Nat.eqb_eq in Hn. subst n. cbn [length fold_right fst snd]. rewrite msum_shift.
  rewrite Nat.add_0_r. cbn [nth snd]. f_equal. rewrite (IH (S next) d Htl).
  apply msum_ext. intros k Hk. f_equal. lia.
Qed.

(** The terms of a sum from an offset, over all smaller indices with zeros. *)
Lemma msum_offset :
  forall (G : nat -> R) base len,
  msum (fun n => if Nat.leb base n then G n else 0) (base + len) = msum (fun k => G (base + k)%nat) len.
Proof.
  intros G base len. induction len as [|len IH].
  - rewrite Nat.add_0_r. cbn [msum]. rewrite (msum_ext _ (fun _ => 0)); [apply msum_zero|].
    intros n Hn. destruct (Nat.leb_spec base n); [lia | reflexivity].
  - replace (base + S len)%nat with (S (base + len)) by lia. cbn [msum]. rewrite IH.
    destruct (Nat.leb_spec base (base + len)); [reflexivity | lia].
Qed.

(** A sum whose terms vanish from m on. *)
Lemma msum_trunc :
  forall f m n, (m <= n)%nat -> (forall k, (m <= k < n)%nat -> f k = 0) -> msum f n = msum f m.
Proof.
  intros f m n Hmn H. induction n as [|n IH]; [replace m with O by lia; reflexivity|].
  destruct (Nat.eq_dec m (S n)) as [->|Hne]; [reflexivity|].
  cbn [msum]. rewrite IH by (lia || (intros k Hk; apply H; lia)). rewrite (H n) by lia. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* Single operations                                                 *)

Definition is_atom (e : expr) : bool :=
  match e with Evar _ | EfromZ _ | Epi | Epow2 _ => true | _ => false end.

(** One operation on atoms, or an atom alone; no square root. *)
Definition single (e : expr) : bool :=
  match e with
  | Evar _ | EfromZ _ | Epi | Epow2 _ => true
  | Eneg a | Esin a | Ecos a | Eexp a | Eatan a => is_atom a
  | Eadd a b | Esub a b | Emul a b | Ediv a b => is_atom a && is_atom b
  | Esqrt _ => false
  end.

Definition xr (y : ExtendedR) : R := match y with Xreal r => r | Xnan => 0 end.

Lemma Xdiv_ok : forall a b, b <> 0 -> Xdiv (Xreal a) (Xreal b) = Xreal (a / b).
Proof. intros a b Hb. cbn [Xbind2]. unfold Xdiv'. rewrite (is_zero_false b Hb). reflexivity. Qed.

Lemma Xadd_r : forall a b, Xadd (Xreal a) (Xreal b) = Xreal (a + b).
Proof. reflexivity. Qed.
Lemma Xsub_r : forall a b, Xsub (Xreal a) (Xreal b) = Xreal (a - b).
Proof. reflexivity. Qed.
Lemma Xmul_r : forall a b, Xmul (Xreal a) (Xreal b) = Xreal (a * b).
Proof. reflexivity. Qed.

Lemma Xdiv_real_nz : forall a b r, Xdiv (Xreal a) (Xreal b) = Xreal r -> b <> 0.
Proof. intros a b r H Hb. subst b. cbn [Xbind2] in H. unfold Xdiv' in H. rewrite is_zero_0 in H. discriminate. Qed.

Lemma wf_nth_fst :
  forall bs next k d, well_formed next bs = true -> (k < length bs)%nat -> fst (nth k bs d) = (next + k)%nat.
Proof.
  induction bs as [|[n e] tl IH]; intros next k d Hwf Hk; [cbn in Hk; lia|].
  cbn in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl]. apply andb_prop in Hwf. destruct Hwf as [Hn _].
  apply Nat.eqb_eq in Hn. destruct k as [|k]; [cbn; lia|]. cbn [nth].
  rewrite (IH (S next) k d Htl) by (cbn in Hk; lia). lia.
Qed.

Lemma env_agree :
  forall L E E', (forall k, eget k E Xnan = eget k E' Xnan) ->
  forall k, eget k (xextend E L) Xnan = eget k (xextend E' L) Xnan.
Proof.
  induction L as [|[n e] tl IH]; intros E E' H k; [exact (H k)|].
  change (xextend E ((n, e) :: tl)) with (xextend (eset n E (xeval E e)) tl).
  change (xextend E' ((n, e) :: tl)) with (xextend (eset n E' (xeval E' e)) tl).
  apply IH. intros j. destruct (Nat.eq_dec j n) as [->|Hne].
  - rewrite !eget_eset_eq. rewrite !xeval_f. apply xevalf_ext. intros i _. apply H.
  - rewrite !eget_eset_neq by exact Hne. apply H.
Qed.

(* ---------------------------------------------------------------- *)
(* The forward derivative of a flattened list                        *)

Section Adj.

(** A list pre from base0 to base, then the flattened list ab from base to
    top; the derivative is taken along the input xt below base0. *)
Variables (base0 base len o xt : nat) (pre ab : list binding) (ks : list nat) (E0 : env ExtendedR).

Hypothesis Hwfp : well_formed base0 pre = true.
Hypothesis Hbase : base = (base0 + length pre)%nat.
Hypothesis Hwf : well_formed base ab = true.
Hypothesis Hlen : length ab = len.
Hypothesis Hsingle : forallb (fun b => single (snd b)) ab = true.
Hypothesis Ho : (base <= o < base + len)%nat.
Hypothesis Hxt : (xt < base0)%nat.
Hypothesis Hks : forall k, In k ks -> (k < base)%nat.
Hypothesis Hwfa : well_formed base0 (pre ++ ab ++ adj_binds base (base + len) o ab ks) = true.
Hypothesis Hreal : forall j, (j < base + len)%nat -> exists r, eget j (xextend E0 (pre ++ ab)) Xnan = Xreal r.

Let top : nat := (base + len)%nat.
Let len0 : nat := (length pre + len)%nat.
Let E1 : env ExtendedR := xextend E0 (pre ++ ab).
Let dv : nat -> expr := dvar_of xt base0 len0.
Let Fw : env ExtendedR := xextend E0 (with_dseq xt base0 len0 (pre ++ ab)).

(** The tangents of pre are real. *)
Hypothesis Hpre_tan : forall k, (base0 <= k < base)%nat -> exists r, eget (k + len0) Fw Xnan = Xreal r.

Lemma Hlen0 : (0 < len0)%nat.
Proof. unfold len0. lia. Qed.

Lemma wf_all : well_formed base0 (pre ++ ab) = true.
Proof. apply (wf_cat pre ab base0 base Hwfp Hwf). exact Hbase. Qed.

Lemma len_all : length (pre ++ ab) = len0.
Proof. rewrite length_app, Hlen. reflexivity. Qed.

Definition v (j : nat) : R := xr (eget j E1 Xnan).

Lemma v_real : forall j, (j < top)%nat -> eget j E1 Xnan = Xreal (v j).
Proof. intros j Hj. destruct (Hreal j Hj) as [r Hr]. unfold v, E1. rewrite Hr. reflexivity. Qed.

(** The expression of binding n. *)
Definition bexp (n : nat) : expr := snd (nth (n - base) ab (0%nat, EfromZ 0)).

Lemma bexp_in : forall n, (base <= n < top)%nat -> In (n, bexp n) ab.
Proof.
  intros n Hn. unfold bexp.
  assert (Hk : (n - base < length ab)%nat) by (rewrite Hlen; unfold top in Hn; lia).
  assert (Hf := wf_nth_fst ab base (n - base) (0%nat, EfromZ 0) Hwf Hk).
  assert (Hb := nth_In ab (0%nat, EfromZ 0) Hk).
  destruct (nth (n - base) ab (0%nat, EfromZ 0)) as [n' e']. cbn [fst snd] in *.
  replace n with n' by lia. exact Hb.
Qed.

Lemma bexp_wf : forall n, (base <= n < top)%nat -> vars_below n (bexp n) = true /\ single (bexp n) = true.
Proof.
  intros n Hn. assert (Hin := bexp_in n Hn). split.
  - exact (proj2 (well_formed_in ab base n (bexp n) Hwf Hin)).
  - rewrite forallb_forall in Hsingle. exact (Hsingle (n, bexp n) Hin).
Qed.

Lemma val_bexp : forall n, (base <= n < top)%nat -> Xreal (v n) = xeval E1 (bexp n).
Proof.
  intros n Hn. rewrite <- (v_real n) by lia. unfold E1.
  apply (wf_holds (pre ++ ab) E0 base0 n (bexp n) wf_all). apply in_or_app. right. exact (bexp_in n Hn).
Qed.

Definition vat (a : expr) : R :=
  match a with Evar j => v j | EfromZ z => IZR z | Epi => PI | Epow2 z => powerRZ 2 z | _ => 0 end.

Definition ind (a : expr) (j : nat) : R := match a with Evar k => if Nat.eqb k j then 1 else 0 | _ => 0 end.

Lemma atom_val :
  forall a E, is_atom a = true -> vars_below top a = true ->
  (forall j, (j < top)%nat -> eget j E Xnan = eget j E1 Xnan) -> xeval E a = Xreal (vat a).
Proof.
  intros a E Ha Hb HE. destruct a as [k|z| |a1|a1 a2|a1 a2|a1 a2|a1 a2|a1|a1|a1|a1|a1|z]; try discriminate;
    cbn [xeval vat]; try reflexivity.
  cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb. rewrite HE by exact Hb. apply v_real. exact Hb.
Qed.

(** The forward list leaves the values below top as they are. *)
Lemma Fw_low : forall j, (j < top)%nat -> eget j Fw Xnan = eget j E1 Xnan.
Proof.
  intros j Hj. unfold Fw, with_dseq. rewrite xextend_app. fold E1.
  apply (eget_above (dbinds xt base0 len0 (pre ++ ab)) E1 top j); [| exact Hj].
  assert (H := dbinds_wf xt base0 len0 Hxt Hlen0 (pre ++ ab) base0 wf_all (le_n base0)).
  replace top with (base0 + len0)%nat by (unfold top, len0; lia). exact H.
Qed.

Lemma Fw_tan : forall n, (base <= n < top)%nat -> eget (n + len0) Fw Xnan = xeval Fw (deriv dv (bexp n)).
Proof.
  intros n Hn. unfold Fw.
  apply (wf_holds (with_dseq xt base0 len0 (pre ++ ab)) E0 base0 (n + len0) (deriv dv (bexp n))).
  - exact (with_dseq_wf xt base0 len0 Hxt Hlen0 (pre ++ ab) wf_all len_all).
  - unfold with_dseq. apply in_or_app. right. unfold dbinds.
    apply (in_map (fun b => (fst b + len0, deriv (dvar_of xt base0 len0) (snd b)))%nat (pre ++ ab) (n, bexp n)).
    apply in_or_app. right. exact (bexp_in n Hn).
Qed.

(** The tangent of every slot: one-hot at xt on the inputs. *)
Definition tau (j : nat) : R :=
  if Nat.ltb j base0 then (if Nat.eqb j xt then 1 else 0) else xr (eget (j + len0) Fw Xnan).

Definition tat (a : expr) : R := match a with Evar k => tau k | _ => 0 end.

Lemma pre_tau : forall k, (base0 <= k < base)%nat -> eget (k + len0) Fw Xnan = Xreal (tau k).
Proof.
  intros k Hk. destruct (Hpre_tan k Hk) as [r Hr]. unfold tau.
  rewrite (proj2 (Nat.ltb_ge k base0) ltac:(lia)), Hr. reflexivity.
Qed.

Lemma dv_val :
  forall j, ((base <= j)%nat -> eget (j + len0) Fw Xnan = Xreal (tau j)) -> xeval Fw (dv j) = Xreal (tau j).
Proof.
  intros j H. unfold dv, dvar_of.
  destruct (Nat.eqb_spec j xt) as [->|Hne].
  - unfold tau. rewrite (proj2 (Nat.ltb_lt xt base0) Hxt), Nat.eqb_refl. reflexivity.
  - destruct (Nat.ltb_spec j base0) as [Hb|Hb].
    + unfold tau. rewrite (proj2 (Nat.ltb_lt j base0) Hb), (proj2 (Nat.eqb_neq j xt) Hne). reflexivity.
    + cbn [xeval]. destruct (Nat.ltb_spec j base) as [Hb'|Hb']; [exact (pre_tau j ltac:(lia)) | exact (H Hb')].
Qed.

Lemma tat_val :
  forall a n, is_atom a = true -> vars_below n a = true ->
  (forall j, (base <= j < n)%nat -> eget (j + len0) Fw Xnan = Xreal (tau j)) ->
  xeval Fw (deriv dv a) = Xreal (tat a).
Proof.
  intros a n Ha Hb H. destruct a as [k|z| |a1|a1 a2|a1 a2|a1 a2|a1 a2|a1|a1|a1|a1|a1|z]; try discriminate;
    cbn [deriv tat]; try reflexivity.
  apply dv_val. intros Hk. cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb. apply H. lia.
Qed.

Lemma msum_ind :
  forall a (c : nat -> R) n, is_atom a = true -> vars_below n a = true ->
  msum (fun j => ind a j * c j) n = match a with Evar k => c k | _ => 0 end.
Proof.
  intros a c n Ha Hb. destruct a as [k|z| |a1|a1 a2|a1 a2|a1 a2|a1 a2|a1|a1|a1|a1|a1|z]; try discriminate;
    cbn [ind].
  - cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb.
    rewrite (msum_single _ n k Hb); [rewrite Nat.eqb_refl; ring|].
    intros j Hj Hne. destruct (Nat.eqb_spec k j); [subst; contradiction | ring].
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
Qed.

Lemma msum_tat :
  forall a K n, is_atom a = true -> vars_below n a = true ->
  msum (fun j => ind a j * K * tau j) n = K * tat a.
Proof.
  intros a K n Ha Hb.
  rewrite (msum_ext _ (fun j => ind a j * (K * tau j))) by (intros; ring).
  rewrite (msum_ind a (fun j => K * tau j) n Ha Hb).
  destruct a; try discriminate; cbn [tat]; ring.
Qed.

(** What binding n contributes to the derivative per unit of slot j's. *)
Definition rpart (n : nat) (e : expr) (j : nat) : R :=
  match e with
  | Evar a => if Nat.eqb a j then 1 else 0
  | Eneg p => - ind p j
  | Eadd p q => ind p j + ind q j
  | Esub p q => ind p j - ind q j
  | Emul p q => ind p j * vat q + ind q j * vat p
  | Ediv p q => ind p j / vat q - ind q j * (v n / vat q)
  | Esin p => ind p j * cos (vat p)
  | Ecos p => - (ind p j * sin (vat p))
  | Eexp p => ind p j * v n
  | Eatan p => ind p j / (1 + vat p * vat p)
  | _ => 0
  end.

Lemma ind_above : forall a n j, vars_below n a = true -> (n <= j)%nat -> ind a j = 0.
Proof.
  intros a n j Hb Hj. destruct a; cbn [ind]; try reflexivity.
  cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb. destruct (Nat.eqb_spec n0 j); [lia | reflexivity].
Qed.

Lemma rpart_above : forall n e j, vars_below n e = true -> single e = true -> (n <= j)%nat -> rpart n e j = 0.
Proof.
  intros n e j Hb Hs Hj.
  assert (I1 : forall a, vars_below n a = true -> ind a j = 0) by (intros a Ha; exact (ind_above a n j Ha Hj)).
  destruct e as [k|z| |p|p q|p q|p q|p q|p|p|p|p|p|z]; unfold rpart.
  - cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb. destruct (Nat.eqb_spec k j); [lia | reflexivity].
  - reflexivity.
  - reflexivity.
  - cbn [vars_below] in Hb. rewrite (I1 p Hb). ring.
  - cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. rewrite (I1 p Hb1), (I1 q Hb2). ring.
  - cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. rewrite (I1 p Hb1), (I1 q Hb2). ring.
  - cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. rewrite (I1 p Hb1), (I1 q Hb2). ring.
  - cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. rewrite (I1 p Hb1), (I1 q Hb2).
    unfold Rdiv. ring.
  - reflexivity.
  - cbn [vars_below] in Hb. rewrite (I1 p Hb). ring.
  - cbn [vars_below] in Hb. rewrite (I1 p Hb). ring.
  - cbn [vars_below] in Hb. rewrite (I1 p Hb). ring.
  - cbn [vars_below] in Hb. rewrite (I1 p Hb). unfold Rdiv. ring.
  - reflexivity.
Qed.

(** The forward rule of a binding, its earlier tangents real. *)
Lemma fw_rule :
  forall n, (base <= n < top)%nat ->
  (forall j, (base <= j < n)%nat -> eget (j + len0) Fw Xnan = Xreal (tau j)) ->
  eget (n + len0) Fw Xnan = Xreal (msum (fun j => rpart n (bexp n) j * tau j) n).
Proof.
  intros n Hn IH. rewrite Fw_tan by exact Hn.
  destruct (bexp_wf n Hn) as [Hb Hs]. assert (Hv := val_bexp n Hn).
  assert (HF : forall j, (j < top)%nat -> eget j Fw Xnan = eget j E1 Xnan) by exact Fw_low.
  assert (HE1 : forall j, (j < top)%nat -> eget j E1 Xnan = eget j E1 Xnan) by reflexivity.
  assert (Ht : forall a, is_atom a = true -> vars_below n a = true -> vars_below top a = true)
    by (intros a _ Ha; exact (vars_below_mono n top a Ha ltac:(unfold top in *; lia))).
  destruct (bexp n) as [k|z| |p|p q|p q|p q|p q|p|p|p|p|p|z];
    cbn [single] in Hs; try discriminate; cbn [rpart deriv].
  - (* a copy *)
    cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb.
    rewrite (dv_val k) by (intros Hk; apply IH; lia).
    rewrite (msum_single _ n k Hb); [rewrite Nat.eqb_refl; f_equal; ring|].
    intros j Hj Hne. destruct (Nat.eqb_spec k j); [subst; contradiction | ring].
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). rewrite msum_zero. reflexivity.
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). rewrite msum_zero. reflexivity.
  - (* neg *)
    cbn [vars_below] in Hb. cbn [xeval]. rewrite (tat_val p n Hs Hb IH). cbn.
    f_equal. rewrite (msum_ext _ (fun j => ind p j * (-1) * tau j)) by (intros; ring).
    rewrite (msum_tat p (-1) n Hs Hb). ring.
  - (* add *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
    apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    cbn [xeval]. rewrite (tat_val p n Hs1 Hb1 IH), (tat_val q n Hs2 Hb2 IH). cbn. f_equal.
    rewrite (msum_ext _ (fun j => ind p j * 1 * tau j + ind q j * 1 * tau j)) by (intros; ring).
    rewrite msum_plus, (msum_tat p 1 n Hs1 Hb1), (msum_tat q 1 n Hs2 Hb2). ring.
  - (* sub *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
    apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    cbn [xeval]. rewrite (tat_val p n Hs1 Hb1 IH), (tat_val q n Hs2 Hb2 IH). cbn. f_equal.
    rewrite (msum_ext _ (fun j => ind p j * 1 * tau j - ind q j * 1 * tau j)) by (intros; ring).
    rewrite msum_minus, (msum_tat p 1 n Hs1 Hb1), (msum_tat q 1 n Hs2 Hb2). ring.
  - (* mul *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
    apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    cbn [xeval]. rewrite (tat_val p n Hs1 Hb1 IH), (tat_val q n Hs2 Hb2 IH).
    rewrite (atom_val p Fw Hs1 (Ht p Hs1 Hb1) HF), (atom_val q Fw Hs2 (Ht q Hs2 Hb2) HF). cbn. f_equal.
    rewrite (msum_ext _ (fun j => ind p j * vat q * tau j + ind q j * vat p * tau j)) by (intros; ring).
    rewrite msum_plus, (msum_tat p (vat q) n Hs1 Hb1), (msum_tat q (vat p) n Hs2 Hb2). ring.
  - (* div *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
    apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    cbn [xeval] in Hv. rewrite (atom_val p E1 Hs1 (Ht p Hs1 Hb1) HE1), (atom_val q E1 Hs2 (Ht q Hs2 Hb2) HE1) in Hv.
    assert (Hq : vat q <> 0) by exact (Xdiv_real_nz _ _ _ (eq_sym Hv)).
    rewrite (Xdiv_ok _ _ Hq) in Hv. injection Hv as Hvn.
    cbn [xeval]. rewrite (tat_val p n Hs1 Hb1 IH), (tat_val q n Hs2 Hb2 IH).
    rewrite (atom_val p Fw Hs1 (Ht p Hs1 Hb1) HF), (atom_val q Fw Hs2 (Ht q Hs2 Hb2) HF).
    rewrite !Xmul_r, Xsub_r. rewrite Xdiv_ok by (intros H0; apply Hq; nra). f_equal.
    rewrite (msum_ext _ (fun j => ind p j * (/ vat q) * tau j - ind q j * (v n / vat q) * tau j))
      by (intros; unfold Rdiv; ring).
    rewrite msum_minus, (msum_tat p (/ vat q) n Hs1 Hb1), (msum_tat q (v n / vat q) n Hs2 Hb2).
    rewrite Hvn. field. exact Hq.
  - (* sin *)
    cbn [vars_below] in Hb. cbn [xeval]. rewrite (tat_val p n Hs Hb IH), (atom_val p Fw Hs (Ht p Hs Hb) HF). cbn.
    f_equal. rewrite (msum_tat p (cos (vat p)) n Hs Hb). ring.
  - (* cos *)
    cbn [vars_below] in Hb. cbn [xeval]. rewrite (tat_val p n Hs Hb IH), (atom_val p Fw Hs (Ht p Hs Hb) HF). cbn.
    f_equal. rewrite (msum_ext _ (fun j => ind p j * (- sin (vat p)) * tau j)) by (intros; ring).
    rewrite (msum_tat p (- sin (vat p)) n Hs Hb). ring.
  - (* exp *)
    cbn [vars_below] in Hb. cbn [xeval] in Hv. rewrite (atom_val p E1 Hs (Ht p Hs Hb) HE1) in Hv. cbn in Hv.
    injection Hv as Hvn.
    cbn [xeval]. rewrite (tat_val p n Hs Hb IH), (atom_val p Fw Hs (Ht p Hs Hb) HF). cbn.
    f_equal. rewrite (msum_tat p (v n) n Hs Hb). rewrite Hvn. ring.
  - (* atan *)
    cbn [vars_below] in Hb. cbn [xeval]. rewrite (tat_val p n Hs Hb IH), (atom_val p Fw Hs (Ht p Hs Hb) HF).
    assert (Hpos : 1 + vat p * vat p <> 0) by nra.
    rewrite Xmul_r. change (Xreal (IZR 1)) with (Xreal 1). rewrite Xadd_r, Xdiv_ok by exact Hpos. f_equal.
    rewrite (msum_ext _ (fun j => ind p j * (/ (1 + vat p * vat p)) * tau j)) by (intros; unfold Rdiv; ring).
    rewrite (msum_tat p (/ (1 + vat p * vat p)) n Hs Hb). unfold Rdiv. ring.
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). rewrite msum_zero. reflexivity.
Qed.

(** Every tangent of the flattened list is real, by the forward rule. *)
Lemma fw_all : forall n, (base <= n < top)%nat -> eget (n + len0) Fw Xnan = Xreal (tau n).
Proof.
  intros n. induction n as [n IHn] using lt_wf_ind. intros Hn.
  assert (IH : forall j, (base <= j < n)%nat -> eget (j + len0) Fw Xnan = Xreal (tau j))
    by (intros j Hj; apply IHn; lia).
  rewrite (fw_rule n Hn IH). f_equal. unfold tau.
  rewrite (proj2 (Nat.ltb_ge n base0) ltac:(lia)). rewrite (fw_rule n Hn IH). reflexivity.
Qed.

Lemma tau_rule : forall n, (base <= n < top)%nat -> tau n = msum (fun j => rpart n (bexp n) j * tau j) n.
Proof.
  intros n Hn. unfold tau at 1. rewrite (proj2 (Nat.ltb_ge n base0) ltac:(lia)).
  rewrite (fw_rule n Hn (fun j Hj => fw_all j ltac:(lia))). reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* The adjoints                                                      *)

Let Ad : env ExtendedR := xextend E0 (pre ++ ab ++ adj_binds base top o ab ks).
Let ins (cm' : env (list expr)) (jc : nat * expr) : env (list expr) := eset (fst jc) cm' (snd jc :: eget (fst jc) cm' []).

Definition alpha (j : nat) : R := xr (eget (aslot top o j) Ad Xnan).

Definition lval (l : list expr) : R := fold_right (fun c s => xr (xeval Ad c) + s) 0 l.
Definition lreal (l : list expr) : Prop := forall c, In c l -> exists r, xeval Ad c = Xreal r.
Definition csum (j : nat) (cl : list (nat * expr)) : R :=
  fold_right (fun jc s => (if Nat.eqb (fst jc) j then xr (xeval Ad (snd jc)) else 0) + s) 0 cl.

Lemma adj_wf : well_formed top (adj_binds base top o ab ks) = true.
Proof.
  assert (H := Hwfa). rewrite app_assoc, DivDiff.well_formed_app in H. apply andb_prop in H. destruct H as [_ H].
  rewrite length_app, Hlen in H. replace (base0 + (length pre + len))%nat with top in H by (unfold top; lia). exact H.
Qed.

Lemma Ad_low : forall j, (j < top)%nat -> eget j Ad Xnan = eget j E1 Xnan.
Proof.
  intros j Hj. unfold Ad. rewrite app_assoc, xextend_app. fold E1. exact (eget_above _ E1 top j adj_wf Hj).
Qed.

Lemma Ad_bind : forall k e, In (k, e) (adj_binds base top o ab ks) -> eget k Ad Xnan = xeval Ad e.
Proof.
  intros k e Hin. unfold Ad. apply (wf_holds _ E0 base0 k e Hwfa). apply in_or_app. right. apply in_or_app. right.
  exact Hin.
Qed.

Lemma esum_val : forall l, lreal l -> xeval Ad (esum l) = Xreal (lval l).
Proof.
  induction l as [|c tl IH]; intros Hl; [reflexivity|].
  destruct (Hl c (or_introl eq_refl)) as [r Hr].
  destruct tl as [|c' tl'].
  - cbn [esum lval fold_right]. rewrite Hr. cbn [xr]. f_equal. ring.
  - change (esum (c :: c' :: tl')) with (Eadd c (esum (c' :: tl'))). cbn [xeval].
    rewrite Hr, IH by (intros c0 Hc0; apply Hl; right; exact Hc0). cbn [lval fold_right].
    rewrite Hr. reflexivity.
Qed.

Lemma ins_fold :
  forall cl cm0 j,
  lval (eget j (fold_left ins cl cm0) []) = lval (eget j cm0 []) + csum j cl /\
  (lreal (eget j cm0 []) -> (forall jc, In jc cl -> fst jc = j -> exists r, xeval Ad (snd jc) = Xreal r) ->
   lreal (eget j (fold_left ins cl cm0) [])).
Proof.
  induction cl as [|[j' c] tl IH]; intros cm0 j.
  - cbn [fold_left csum fold_right]. split; [ring | intros H _; exact H].
  - cbn [fold_left]. destruct (IH (ins cm0 (j', c)) j) as [E1' R1'].
    change (csum j ((j', c) :: tl)) with ((if Nat.eqb j' j then xr (xeval Ad c) else 0) + csum j tl).
    destruct (Nat.eqb_spec j' j) as [->|Hne].
    + assert (Hg : eget j (ins cm0 (j, c)) [] = c :: eget j cm0 []) by (unfold ins; cbn [fst snd]; apply eget_eset_eq).
      rewrite Hg in E1', R1'. split.
      * rewrite E1'. cbn [lval fold_right]. unfold lval. ring.
      * intros Hl Hc. apply R1'; [| intros jc Hjc Hf; apply Hc; [right; exact Hjc | exact Hf]].
        intros c0 [Heq|Hc0]; [subst c0; exact (Hc (j, c) (or_introl eq_refl) eq_refl) | apply Hl; exact Hc0].
    + assert (Hg : eget j (ins cm0 (j', c)) [] = eget j cm0 [])
        by (unfold ins; cbn [fst snd]; apply eget_eset_neq; intros ->; contradiction).
      rewrite Hg in E1', R1'. split.
      * rewrite E1'. ring.
      * intros Hl Hc. apply R1'; [exact Hl | intros jc Hjc Hf; apply Hc; [right; exact Hjc | exact Hf]].
Qed.

Lemma csum_app : forall j l1 l2, csum j (l1 ++ l2) = csum j l1 + csum j l2.
Proof. intros j l1 l2. unfold csum. rewrite fold_right_app. induction l1 as [|a l1 IH]; cbn; [ring | rewrite IH; ring]. Qed.

Lemma sl_val :
  forall p c n j w, is_atom p = true -> vars_below n p = true -> ((j < n)%nat -> xeval Ad c = Xreal w) ->
  csum j (sl p c) = ind p j * w /\ (forall jc, In jc (sl p c) -> fst jc = j -> exists r, xeval Ad (snd jc) = Xreal r).
Proof.
  intros p c n j w Ha Hb Hc. destruct p as [k|z| |a1|a1 a2|a1 a2|a1 a2|a1 a2|a1|a1|a1|a1|a1|z]; try discriminate.
  - cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb. cbn [sl ind]. unfold csum. cbn [fold_right fst snd].
    destruct (Nat.eqb_spec k j) as [->|Hne].
    + rewrite (Hc Hb). cbn [xr]. split; [ring|]. intros jc [<-|[]] _. exists w. exact (Hc Hb).
    + split; [ring|]. intros jc [<-|[]] Hf. cbn [fst] in Hf. contradiction.
  - split; [cbn; ring | intros jc []].
  - split; [cbn; ring | intros jc []].
  - split; [cbn; ring | intros jc []].
Qed.

Lemma Ad_atom : forall a, is_atom a = true -> vars_below top a = true -> xeval Ad a = Xreal (vat a).
Proof. intros a Ha Hb. apply (atom_val a Ad Ha Hb). exact Ad_low. Qed.

(** What binding n contributes to the adjoint of slot j. *)
Lemma contribs_val :
  forall n j, (base <= n <= o)%nat -> ((j < n)%nat -> eget (aslot top o n) Ad Xnan = Xreal (alpha n)) ->
  csum j (contribs (aslot top o n) n (bexp n)) = alpha n * rpart n (bexp n) j /\
  (forall jc, In jc (contribs (aslot top o n) n (bexp n)) -> fst jc = j -> exists r, xeval Ad (snd jc) = Xreal r).
Proof.
  intros n j Hn HA.
  assert (Hn' : (base <= n < top)%nat) by (unfold top; lia).
  destruct (bexp_wf n Hn') as [Hb Hs]. assert (Hv := val_bexp n Hn').
  assert (Ht : forall a, vars_below n a = true -> vars_below top a = true)
    by (intros a Ha; exact (vars_below_mono n top a Ha ltac:(unfold top in *; lia))).
  assert (HA' : (j < n)%nat -> xeval Ad (Evar (aslot top o n)) = Xreal (alpha n)) by exact HA.
  assert (Hvn : xeval Ad (Evar n) = Xreal (v n)) by (cbn [xeval]; rewrite Ad_low by exact (proj2 Hn'); apply v_real; exact (proj2 Hn')).
  destruct (bexp n) as [k|z| |p|p q|p q|p q|p q|p|p|p|p|p|z];
    cbn [single] in Hs; try discriminate; cbn [contribs rpart].
  - (* a copy *)
    unfold csum. cbn [fold_right fst snd]. cbn [vars_below] in Hb. apply Nat.ltb_lt in Hb.
    destruct (Nat.eqb_spec k j) as [->|Hne].
    + rewrite (HA' Hb). cbn [xr]. split; [ring|]. intros jc [<-|[]] _. exists (alpha n). exact (HA' Hb).
    + split; [ring|]. intros jc [<-|[]] Hf. cbn [fst] in Hf. contradiction.
  - split; [cbn; ring | intros jc []].
  - split; [cbn; ring | intros jc []].
  - (* neg *)
    cbn [vars_below] in Hb.
    destruct (sl_val p (Eneg (Evar (aslot top o n))) n j (- alpha n) Hs Hb) as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj). reflexivity. }
    rewrite S1. split; [ring | exact R1].
  - (* add *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    destruct (sl_val p (Evar (aslot top o n)) n j (alpha n) Hs1 Hb1 HA') as [S1 R1].
    destruct (sl_val q (Evar (aslot top o n)) n j (alpha n) Hs2 Hb2 HA') as [S2 R2].
    rewrite csum_app, S1, S2. split; [ring|]. intros jc Hjc Hf. apply in_app_or in Hjc.
    destruct Hjc; [apply R1 | apply R2]; assumption.
  - (* sub *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    destruct (sl_val p (Evar (aslot top o n)) n j (alpha n) Hs1 Hb1 HA') as [S1 R1].
    destruct (sl_val q (Eneg (Evar (aslot top o n))) n j (- alpha n) Hs2 Hb2) as [S2 R2].
    { intros Hj. cbn [xeval]. rewrite (HA Hj). reflexivity. }
    rewrite csum_app, S1, S2. split; [ring|]. intros jc Hjc Hf. apply in_app_or in Hjc.
    destruct Hjc; [apply R1 | apply R2]; assumption.
  - (* mul *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    destruct (sl_val p (Emul (Evar (aslot top o n)) q) n j (alpha n * vat q) Hs1 Hb1) as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom q Hs2 (Ht q Hb2)). reflexivity. }
    destruct (sl_val q (Emul (Evar (aslot top o n)) p) n j (alpha n * vat p) Hs2 Hb2) as [S2 R2].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom p Hs1 (Ht p Hb1)). reflexivity. }
    rewrite csum_app, S1, S2. split; [ring|]. intros jc Hjc Hf. apply in_app_or in Hjc.
    destruct Hjc; [apply R1 | apply R2]; assumption.
  - (* div *)
    cbn [vars_below] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply andb_prop in Hs. destruct Hs as [Hs1 Hs2].
    assert (HE1 : forall j0, (j0 < top)%nat -> eget j0 E1 Xnan = eget j0 E1 Xnan) by reflexivity.
    cbn [xeval] in Hv. rewrite (atom_val p E1 Hs1 (Ht p Hb1) HE1), (atom_val q E1 Hs2 (Ht q Hb2) HE1) in Hv.
    assert (Hq : vat q <> 0) by exact (Xdiv_real_nz _ _ _ (eq_sym Hv)).
    destruct (sl_val p (Ediv (Evar (aslot top o n)) q) n j (alpha n / vat q) Hs1 Hb1) as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom q Hs2 (Ht q Hb2)). apply Xdiv_ok. exact Hq. }
    destruct (sl_val q (Eneg (Emul (Evar (aslot top o n)) (Ediv (Evar n) q))) n j (- (alpha n * (v n / vat q))) Hs2 Hb2)
      as [S2 R2].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom q Hs2 (Ht q Hb2)).
      change (xeval Ad (Evar n)) with (eget n Ad Xnan) in Hvn. rewrite Hvn, Xdiv_ok by exact Hq. reflexivity. }
    rewrite csum_app, S1, S2. split; [unfold Rdiv; ring|]. intros jc Hjc Hf. apply in_app_or in Hjc.
    destruct Hjc; [apply R1 | apply R2]; assumption.
  - (* sin *)
    cbn [vars_below] in Hb.
    destruct (sl_val p (Emul (Evar (aslot top o n)) (Ecos p)) n j (alpha n * cos (vat p)) Hs Hb) as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom p Hs (Ht p Hb)). reflexivity. }
    rewrite S1. split; [ring | exact R1].
  - (* cos *)
    cbn [vars_below] in Hb.
    destruct (sl_val p (Eneg (Emul (Evar (aslot top o n)) (Esin p))) n j (- (alpha n * sin (vat p))) Hs Hb) as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom p Hs (Ht p Hb)). reflexivity. }
    rewrite S1. split; [ring | exact R1].
  - (* exp *)
    cbn [vars_below] in Hb.
    destruct (sl_val p (Emul (Evar (aslot top o n)) (Evar n)) n j (alpha n * v n) Hs Hb) as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj). change (xeval Ad (Evar n)) with (eget n Ad Xnan) in Hvn.
      rewrite Hvn. reflexivity. }
    rewrite S1. split; [ring | exact R1].
  - (* atan *)
    cbn [vars_below] in Hb. assert (Hpos : 1 + vat p * vat p <> 0) by nra.
    destruct (sl_val p (Ediv (Evar (aslot top o n)) (Eadd (EfromZ 1) (Emul p p))) n j (alpha n / (1 + vat p * vat p)) Hs Hb)
      as [S1 R1].
    { intros Hj. cbn [xeval]. rewrite (HA Hj), (Ad_atom p Hs (Ht p Hb)). rewrite Xmul_r.
      change (Xreal (IZR 1)) with (Xreal 1). rewrite Xadd_r. apply Xdiv_ok. exact Hpos. }
    rewrite S1. split; [unfold Rdiv; ring | exact R1].
  - split; [cbn; ring | intros jc []].
Qed.

Lemma in_ab_bexp : forall n e, In (n, e) ab -> e = bexp n /\ (base <= n < top)%nat.
Proof.
  intros n e Hin. destruct (well_formed_in ab base n e Hwf Hin) as [Hn _]. rewrite Hlen in Hn.
  split; [| unfold top; lia].
  destruct (In_nth ab (n, e) (0%nat, EfromZ 0) Hin) as [k [Hk Hnth]].
  assert (Hf := wf_nth_fst ab base k (0%nat, EfromZ 0) Hwf Hk). rewrite Hnth in Hf. cbn [fst] in Hf.
  unfold bexp. replace (n - base)%nat with k by lia. rewrite Hnth. reflexivity.
Qed.

Let step (cm0 : env (list expr)) (b : binding) : env (list expr) :=
  if Nat.leb (fst b) o then fold_left ins (contribs (aslot top o (fst b)) (fst b) (snd b)) cm0 else cm0.

Lemma cm_fold :
  forall bl cm0 j, (forall b, In b bl -> In b ab) ->
  (forall n, (base <= n <= o)%nat -> (j < n)%nat -> eget (aslot top o n) Ad Xnan = Xreal (alpha n)) ->
  lval (eget j (fold_left step bl cm0) [])
  = lval (eget j cm0 []) + fold_right (fun b s => (if Nat.leb (fst b) o then alpha (fst b) * rpart (fst b) (snd b) j else 0) + s) 0 bl /\
  (lreal (eget j cm0 []) -> lreal (eget j (fold_left step bl cm0) [])).
Proof.
  induction bl as [|[n e] tl IH]; intros cm0 j Hsub HA.
  - cbn [fold_left fold_right]. split; [ring | auto].
  - cbn [fold_left fold_right fst snd].
    destruct (in_ab_bexp n e (Hsub _ (or_introl eq_refl))) as [-> Hn].
    destruct (IH (step cm0 (n, bexp n)) j (fun b Hb => Hsub b (or_intror Hb)) HA) as [E R].
    destruct (Nat.leb_spec n o) as [Hno|Hno].
    + assert (Hst : step cm0 (n, bexp n) = fold_left ins (contribs (aslot top o n) n (bexp n)) cm0)
        by (unfold step; cbn [fst snd]; rewrite (proj2 (Nat.leb_le n o) Hno); reflexivity).
      rewrite Hst in E, R. rewrite Hst.
      destruct (contribs_val n j ltac:(lia) (fun Hj => HA n ltac:(lia) Hj)) as [Cv Cr].
      destruct (ins_fold (contribs (aslot top o n) n (bexp n)) cm0 j) as [Fv Fr].
      split.
      * rewrite E, Fv, Cv. ring.
      * intros Hl. apply R. apply Fr; [exact Hl|]. intros jc Hjc Hf. exact (Cr jc Hjc Hf).
    + assert (Hst : step cm0 (n, bexp n) = cm0)
        by (unfold step; cbn [fst snd]; rewrite (proj2 (Nat.leb_gt n o) Hno); reflexivity).
      rewrite Hst in E, R. rewrite Hst.
      split; [rewrite E; ring | exact R].
Qed.

Definition Sadj (j : nat) : R := msum (fun n => if Nat.leb base n then alpha n * rpart n (bexp n) j else 0) (S o).

Lemma cm_val :
  forall j, (forall n, (base <= n <= o)%nat -> (j < n)%nat -> eget (aslot top o n) Ad Xnan = Xreal (alpha n)) ->
  xeval Ad (esum (eget j (cmap top o ab) [])) = Xreal (Sadj j).
Proof.
  intros j HA. change (cmap top o ab) with (fold_left step ab eempty).
  destruct (cm_fold ab eempty j (fun b Hb => Hb) HA) as [E R].
  rewrite eget_eempty in E, R.
  rewrite (esum_val _ (R (fun c Hc => match Hc with end))), E. f_equal.
  cbn [lval fold_right]. rewrite Rplus_0_l.
  rewrite (lsum_msum (fun n e => if Nat.leb n o then alpha n * rpart n e j else 0) ab base (0%nat, EfromZ 0) Hwf).
  rewrite Hlen.
  rewrite (msum_ext _ (fun k => (fun n => if Nat.leb n o then alpha n * rpart n (bexp n) j else 0) (base + k)%nat)).
  2: { intros k Hk. cbv beta. unfold bexp. replace (base + k - base)%nat with k by lia. reflexivity. }
  rewrite <- (msum_offset (fun n => if Nat.leb n o then alpha n * rpart n (bexp n) j else 0) base len).
  rewrite (msum_trunc _ (S o) (base + len)); [| unfold top in Ho; lia |].
  - unfold Sadj. apply msum_ext. intros n Hn. destruct (Nat.leb base n); [|reflexivity].
    rewrite (proj2 (Nat.leb_le n o) ltac:(lia)). reflexivity.
  - intros k Hk. destruct (Nat.leb base k); [|reflexivity].
    rewrite (proj2 (Nat.leb_gt k o) ltac:(lia)). reflexivity.
Qed.

(** The adjoints, from the output down. *)
Lemma aslot_vals :
  forall d, (d <= o - base)%nat ->
  eget (aslot top o (o - d)) Ad Xnan = Xreal (alpha (o - d)) /\
  alpha (o - d) = (if Nat.eqb d 0 then 1 else Sadj (o - d)).
Proof.
  intros d. induction d as [d IHd] using lt_wf_ind. intros Hd.
  destruct (Nat.eqb_spec d 0) as [->|Hd0].
  - assert (Hin : In (top, EfromZ 1) (adj_binds base top o ab ks)) by (left; reflexivity).
    assert (Ha : aslot top o (o - 0) = top) by (unfold aslot; lia).
    rewrite Ha. rewrite (Ad_bind _ _ Hin). cbn [xeval]. unfold alpha. rewrite Ha, (Ad_bind _ _ Hin).
    split; reflexivity.
  - set (j := (o - d)%nat).
    assert (Hin : In ((top + d)%nat, esum (eget j (cmap top o ab) [])) (adj_binds base top o ab ks)).
    { right. apply in_or_app. left.
      apply (in_map (fun dl => ((top + dl)%nat, esum (eget (o - dl)%nat (cmap top o ab) [])))). apply in_seq. lia. }
    assert (Ha : aslot top o j = (top + d)%nat) by (unfold aslot, j; lia).
    assert (HA : forall n, (base <= n <= o)%nat -> (j < n)%nat -> eget (aslot top o n) Ad Xnan = Xreal (alpha n)).
    { intros n Hn Hjn. destruct (IHd (o - n)%nat ltac:(unfold j in Hjn; lia) ltac:(lia)) as [H _].
      replace (o - (o - n))%nat with n in H by lia. exact H. }
    assert (Hv : eget (aslot top o j) Ad Xnan = Xreal (Sadj j)) by (rewrite Ha, (Ad_bind _ _ Hin); exact (cm_val j HA)).
    split.
    + unfold alpha. rewrite Hv. reflexivity.
    + unfold alpha. rewrite Hv. reflexivity.
Qed.

Lemma all_aslot : forall n, (base <= n <= o)%nat -> eget (aslot top o n) Ad Xnan = Xreal (alpha n).
Proof.
  intros n Hn. destruct (aslot_vals (o - n) ltac:(lia)) as [H _].
  replace (o - (o - n))%nat with n in H by lia. exact H.
Qed.

Lemma in_val :
  forall i, (i < length ks)%nat -> eget (in_slot base top o i) Ad Xnan = Xreal (Sadj (nth i ks 0%nat)).
Proof.
  intros i Hi.
  assert (Hin : In (in_slot base top o i, esum (eget (nth i ks 0%nat) (cmap top o ab) [])) (adj_binds base top o ab ks)).
  { right. apply in_or_app. right. unfold in_slot.
    apply (in_map (fun i => ((top + (o - base) + 1 + i)%nat, esum (eget (nth i ks 0%nat) (cmap top o ab) [])))).
    apply in_seq. lia. }
  rewrite (Ad_bind _ _ Hin). apply cm_val. intros n Hn _. apply all_aslot. exact Hn.
Qed.

(** The forward tangent of the output is the sum over the slots below base of
    their adjoints times their tangents. *)
Lemma identity : tau o = msum (fun k => Sadj k * tau k) base.
Proof.
  set (A := fun j => if Nat.ltb j base then Sadj j else alpha j).
  assert (HSA : forall j, Sadj j = msum (fun n => if Nat.leb base n then A n * rpart n (bexp n) j else 0) (S o)).
  { intros j. unfold Sadj. apply msum_ext. intros n Hn. unfold A.
    destruct (Nat.leb_spec base n) as [Hb|Hb]; [| reflexivity].
    rewrite (proj2 (Nat.ltb_ge n base) Hb). reflexivity. }
  assert (H1 : forall j, (j < S o)%nat ->
            A j = (if Nat.eqb j o then 1 else 0) + msum (fun n => if Nat.leb base n then A n * rpart n (bexp n) j else 0) (S o)).
  { intros j Hj. rewrite <- HSA. unfold A.
    destruct (Nat.ltb_spec j base) as [Hb|Hb].
    - rewrite (proj2 (Nat.eqb_neq j o) ltac:(lia)). ring.
    - destruct (Nat.eqb_spec j o) as [->|Hne].
      + destruct (aslot_vals 0 ltac:(lia)) as [_ Ha]. replace (o - 0)%nat with o in Ha by lia. rewrite Ha.
        cbn [Nat.eqb].
        assert (Hz : Sadj o = 0).
        { unfold Sadj. rewrite (msum_ext _ (fun _ => 0)); [apply msum_zero|]. intros n Hn.
          destruct (Nat.leb_spec base n) as [Hbn|Hbn]; [| reflexivity].
          destruct (bexp_wf n ltac:(unfold top in *; lia)) as [Hbw Hs].
          rewrite (rpart_above n (bexp n) o Hbw Hs ltac:(lia)). ring. }
        rewrite Hz. ring.
      + destruct (aslot_vals (o - j) ltac:(lia)) as [_ Ha]. replace (o - (o - j))%nat with j in Ha by lia.
        rewrite Ha. rewrite (proj2 (Nat.eqb_neq (o - j) 0) ltac:(lia)). ring. }
  assert (H2 : msum (fun j => A j * tau j) (S o)
               = tau o + msum (fun n => if Nat.leb base n then A n * tau n else 0) (S o)).
  { rewrite (msum_ext _ (fun j => (if Nat.eqb j o then 1 else 0) * tau j
                                  + msum (fun n => (if Nat.leb base n then A n * rpart n (bexp n) j else 0) * tau j) (S o)))
      by (intros j Hj; rewrite (H1 j Hj); rewrite msum_scal_r; ring).
    rewrite msum_plus. f_equal.
    - rewrite (msum_single _ (S o) o ltac:(lia)); [rewrite Nat.eqb_refl; ring|].
      intros j Hj Hne. rewrite (proj2 (Nat.eqb_neq j o) Hne). ring.
    - rewrite msum_swap. apply msum_ext. intros n Hn.
      destruct (Nat.leb_spec base n) as [Hb|Hb].
      + assert (Hnt : (base <= n < top)%nat) by (unfold top in *; lia).
        rewrite (tau_rule n Hnt). rewrite <- msum_scal.
        destruct (bexp_wf n Hnt) as [Hbw Hs].
        rewrite (msum_trunc (fun j => A n * rpart n (bexp n) j * tau j) n (S o)) by
          (lia || (intros k Hk; rewrite (rpart_above n (bexp n) k Hbw Hs ltac:(lia)); ring)).
        apply msum_ext. intros j Hj. ring.
      + rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero. }
  assert (H3 : msum (fun j => A j * tau j) (S o)
               = msum (fun j => if Nat.ltb j base then A j * tau j else 0) (S o)
                 + msum (fun n => if Nat.leb base n then A n * tau n else 0) (S o)).
  { rewrite <- msum_plus. apply msum_ext. intros j Hj.
    destruct (Nat.ltb_spec j base); destruct (Nat.leb_spec base j); try lia; ring. }
  assert (H4 : msum (fun j => if Nat.ltb j base then A j * tau j else 0) (S o) = tau o) by lra.
  rewrite (msum_trunc _ base (S o)) in H4;
    [| lia | intros k Hk; rewrite (proj2 (Nat.ltb_ge k base) ltac:(lia)); reflexivity].
  rewrite <- H4. apply msum_ext. intros k Hk. unfold A. rewrite (proj2 (Nat.ltb_lt k base) Hk). reflexivity.
Qed.

Theorem adj_tangent : eget (o + len0) Fw Xnan = Xreal (msum (fun k => Sadj k * tau k) base).
Proof. rewrite (fw_all o ltac:(unfold top; lia)), identity. reflexivity. Qed.

(** Along t in slot xt, the derivative of the output slot o of pre ++ ab is the
    sum over the slots below the start of ab of their adjoints times their
    tangents; the adjoint of input i of ks is in slot [in_slot]. *)
Theorem adj_directional :
  forall t0, (forall k, (base0 <= k)%nat -> eget k E0 Xnan = Xnan) ->
  (forall k, (k < base0)%nat -> exists r, eget k E0 Xnan = Xreal r) ->
  eget xt E0 Xnan = Xreal t0 ->
  Xderive_pt (slot_along (fun t => xextend (eset xt E0 (Xreal t)) (pre ++ ab)) o) (Xreal t0)
    (Xreal (msum (fun k => Sadj k * tau k) base)).
Proof.
  intros t0 Hun Hin Ht0.
  assert (HS := sinv_base xt base0 len0 Hxt Hlen0 E0 Hun Hin).
  destruct (dseq_correct xt base0 len0 Hxt Hlen0 (pre ++ ab) (fun t => eset xt E0 (Xreal t)) wf_all len_all HS)
    as [_ HD].
  specialize (HD (o - base0)%nat t0 ltac:(unfold len0; lia)).
  replace (base0 + (o - base0))%nat with o in HD by lia.
  replace (base0 + len0 + (o - base0))%nat with (o + len0)%nat in HD by lia.
  assert (HE : forall k, eget k (eset xt E0 (Xreal t0)) Xnan = eget k E0 Xnan).
  { intros k. destruct (Nat.eq_dec k xt) as [->|Hne].
    - rewrite eget_eset_eq. symmetry. exact Ht0.
    - rewrite eget_eset_neq by exact Hne. reflexivity. }
  rewrite (env_agree (with_dseq xt base0 len0 (pre ++ ab)) _ E0 HE (o + len0)) in HD.
  fold Fw in HD. rewrite adj_tangent in HD.
  apply (Xderive_pt_ext_real
           (slot_along (fun t => xextend (eset xt E0 (Xreal t)) (with_dseq xt base0 len0 (pre ++ ab))) o));
    [| exact HD].
  intros t. unfold slot_along. unfold with_dseq. rewrite xextend_app.
  apply (eget_above (dbinds xt base0 len0 (pre ++ ab)) _ (base0 + len0) o); [| unfold len0; lia].
  exact (dbinds_wf xt base0 len0 Hxt Hlen0 (pre ++ ab) base0 wf_all (le_n base0)).
Qed.

(** With no prefix, the derivative of the output along input i of ks is the
    value of adjoint slot i. *)
Theorem adj_input :
  pre = [] -> forall i, (i < length ks)%nat -> xt = nth i ks 0%nat ->
  forall t0, (forall k, (base0 <= k)%nat -> eget k E0 Xnan = Xnan) ->
  (forall k, (k < base0)%nat -> exists r, eget k E0 Xnan = Xreal r) ->
  eget xt E0 Xnan = Xreal t0 ->
  Xderive_pt (slot_along (fun t => xextend (eset xt E0 (Xreal t)) (pre ++ ab)) o) (Xreal t0)
    (eget (in_slot base top o i) Ad Xnan).
Proof.
  intros Hpre i Hi Hxi t0 Hun Hin Ht0.
  assert (Hb : base = base0) by (rewrite Hbase, Hpre; cbn; lia).
  rewrite (in_val i Hi). rewrite <- Hxi.
  replace (Sadj xt) with (msum (fun k => Sadj k * tau k) base).
  - apply adj_directional; assumption.
  - rewrite (msum_single _ base xt ltac:(lia)).
    + unfold tau. rewrite (proj2 (Nat.ltb_lt xt base0) Hxt), Nat.eqb_refl. ring.
    + intros k Hk Hne. unfold tau. rewrite (proj2 (Nat.ltb_lt k base0) ltac:(lia)), (proj2 (Nat.eqb_neq k xt) Hne). ring.
Qed.

End Adj.
