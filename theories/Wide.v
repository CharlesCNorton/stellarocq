(** The interval evaluator of Expr.v over floats of any precision.

    [ieval] runs on binary64 intervals, which is what makes a check fast and
    what limits how narrow an enclosure can be: an output that cancels terms
    many orders of magnitude larger than itself is enclosed only to the
    rounding of those terms. [weval] is the same evaluator over CoqInterval's
    floats with integer mantissas at a working precision the caller picks,
    and [narrow] rounds its result outward to a binary64 interval. A check
    that reads a few outputs at one point can read them this way, far more
    tightly than binary64 allows, and hand them to the rest of the check,
    which stays in binary64. [weval_correct] and [narrow_correct] are the
    two containments that makes sound. *)

From Coq Require Import ZArith Reals List Lia Lra.
From Flocq Require Import Core.
From Interval Require Import Real.Xreal Interval.Interval Interval.Float_full.
From Interval Require Import Float.Basic Float.Specific_ops Float.Specific_stdz.
From Interval Require Import Missing.Stdlib.
From Stellarocq Require Import Expr Checker.

Import ListNotations.

(** Floats with integer mantissas in radix 2, and verified intervals over
    them. *)
Module WF := SpecificFloat StdZRadix2.
Module WI := FloatIntervalFull WF.

Section Wide.

(** Working precision, in bits of mantissa. *)
Variable wprec : WF.precision.

Fixpoint weval (env : env WI.type) (e : expr) : WI.type :=
  match e with
  | Evar n     => eget n env WI.nai
  | EfromZ z   => WI.fromZ wprec z
  | Epi        => WI.pi wprec
  | Eneg a     => WI.neg (weval env a)
  | Eadd a b   => WI.add wprec (weval env a) (weval env b)
  | Esub a b   => WI.sub wprec (weval env a) (weval env b)
  | Emul a b   => WI.mul wprec (weval env a) (weval env b)
  | Ediv a b   => WI.div wprec (weval env a) (weval env b)
  | Esqrt a    => WI.sqrt wprec (weval env a)
  | Esin a     => WI.sin wprec (weval env a)
  | Ecos a     => WI.cos wprec (weval env a)
  | Eexp a     => WI.exp wprec (weval env a)
  | Eatan a    => WI.atan wprec (weval env a)
  | Epow2 e    => WI.power_int wprec (WI.fromZ wprec 2) e
  end.

Definition wenv_ok (ienv : env WI.type) (xenv : env ExtendedR) : Prop :=
  forall n, contains (WI.convert (eget n ienv WI.nai)) (eget n xenv Xnan).

Lemma weval_correct :
  forall ienv xenv e,
  wenv_ok ienv xenv ->
  contains (WI.convert (weval ienv e)) (xeval xenv e).
Proof.
  intros ienv xenv e Hnth.
  induction e; simpl.
  - apply Hnth.
  - now apply WI.fromZ_correct.
  - apply WI.pi_correct.
  - now apply WI.neg_correct.
  - now apply WI.add_correct.
  - now apply WI.sub_correct.
  - now apply WI.mul_correct.
  - now apply WI.div_correct.
  - now apply WI.sqrt_correct.
  - now apply WI.sin_correct.
  - now apply WI.cos_correct.
  - now apply WI.exp_correct.
  - now apply WI.atan_correct.
  - assert (Hc : contains (WI.convert (WI.fromZ wprec 2)) (Xreal (IZR 2)))
      by apply WI.fromZ_correct.
    assert (H := WI.power_int_correct wprec z _ _ Hc).
    unfold Xpower_int, Xpower_int' in H.
    destruct z as [|q|q]; cbv beta iota delta [Xbind] in H; try exact H.
    revert H. generalize (is_zero_spec 2%R). case (is_zero 2%R).
    + intros Hz0 H. exfalso. inversion Hz0 as [Heq|Hne]. lra.
    + intros Hz0 H. exact H.
Qed.

Definition wextend (ienv : env WI.type) (bs : list binding) : env WI.type :=
  fold_left (fun e b => eset (fst b) e (weval e (snd b))) bs ienv.

Lemma wenv_ok_eset :
  forall ienv xenv n vi vx,
  wenv_ok ienv xenv ->
  contains (WI.convert vi) vx ->
  wenv_ok (eset n ienv vi) (eset n xenv vx).
Proof.
  intros ienv xenv n vi vx Hnth Hv k.
  destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite !eget_eset_eq. exact Hv.
  - rewrite !eget_eset_neq by exact Hne. apply Hnth.
Qed.

Lemma wextend_correct :
  forall bs ienv xenv,
  wenv_ok ienv xenv ->
  wenv_ok (wextend ienv bs) (xextend xenv bs).
Proof.
  induction bs as [|[n e] bs IH]; intros ienv xenv Henv; simpl.
  - exact Henv.
  - apply IH. apply wenv_ok_eset.
    + exact Henv.
    + now apply weval_correct.
Qed.

(** One exact point interval per mantissa, as [ienv_of] builds in binary64. *)
Definition wenv_of (ms : list Z) : env WI.type :=
  of_list (map (WI.fromZ wprec) ms).

Lemma wenv_ok_fromZ :
  forall ms, wenv_ok (wenv_of ms) (xenv_of ms).
Proof.
  intros ms n.
  unfold wenv_of, xenv_of. rewrite !eget_of_list.
  revert ms.
  induction n as [|n IH]; intros [|z ms]; simpl.
  - rewrite ?WI.nai_correct. exact I.
  - apply WI.fromZ_correct.
  - rewrite ?WI.nai_correct. exact I.
  - apply IH.
Qed.

End Wide.

(* ---------------------------------------------------------------- *)
(* Back to binary64                                                  *)

(** The value of a wide float with mantissa m and exponent e. *)
Lemma WF_convert_float :
  forall m e : Z,
  WF.convert (Specific_ops.Float m e) = Xreal (IZR m * powerRZ 2 e)%R.
Proof.
  intros m e.
  change (WF.convert (Specific_ops.Float m e)) with (FtoX (WF.toF (Specific_ops.Float m e))).
  destruct m as [|p|p].
  - change (WF.toF (Specific_ops.Float 0%Z e)) with (@Basic.Fzero radix2).
    cbn [FtoX]. f_equal. simpl. ring.
  - change (WF.toF (Specific_ops.Float (Zpos p) e)) with (@Basic.Float radix2 false p e).
    cbn [FtoX]. f_equal. rewrite FtoR_split. unfold F2R. cbn [Fnum Fexp cond_Zopp].
    rewrite bpow_powerRZ. reflexivity.
  - change (WF.toF (Specific_ops.Float (Zneg p) e)) with (@Basic.Float radix2 true p e).
    cbn [FtoX]. f_equal. rewrite FtoR_split. unfold F2R. cbn [Fnum Fexp cond_Zopp].
    rewrite bpow_powerRZ. reflexivity.
Qed.

Lemma env_ok_empty : env_ok (eempty : env I.type) (eempty : env ExtendedR).
Proof. intros n. rewrite !eget_eempty, I.nai_correct. exact I. Qed.

(** A bound of a wide interval, enclosed in binary64, or nothing for an
    infinite one. *)
Definition wbound (prec : F.precision) (b : WF.type) : option I.type :=
  match b with
  | Specific_ops.Float m e => Some (ieval prec eempty (eps_e m e))
  | Specific_ops.Fnan => None
  end.

Lemma wbound_correct :
  forall prec b v, wbound prec b = Some v ->
  exists r, WF.convert b = Xreal r /\ contains (I.convert v) (Xreal r).
Proof.
  intros prec [|m e] v H; simpl in H; [discriminate|].
  injection H as <-. exists (IZR m * powerRZ 2 e)%R. split.
  - apply WF_convert_float.
  - assert (Hc := ieval_correct prec eempty eempty (eps_e m e) env_ok_empty).
    rewrite xeval_eps_e in Hc. exact Hc.
Qed.

(** A binary64 interval holding every value the wide interval holds: the
    hull of binary64 enclosures of its two bounds. *)
Definition narrow (prec : F.precision) (w : WI.type) : I.type :=
  match wbound prec (WI.lower w), wbound prec (WI.upper w) with
  | Some a, Some b => I.join a b
  | _, _ => I.nai
  end.

Lemma narrow_correct :
  forall prec w x,
  contains (WI.convert w) x -> contains (I.convert (narrow prec w)) x.
Proof.
  intros prec w x Hx. unfold narrow.
  destruct (wbound prec (WI.lower w)) as [a|] eqn:Ha;
    [|rewrite I.nai_correct; exact I].
  destruct (wbound prec (WI.upper w)) as [b|] eqn:Hb;
    [|rewrite I.nai_correct; exact I].
  destruct (wbound_correct _ _ _ Ha) as [l [Hl Hla]].
  destruct (wbound_correct _ _ _ Hb) as [u [Hu Hub]].
  destruct x as [|r].
  - (* a NaN is held only by the whole line, whose bounds are infinite *)
    apply contains_Xnan in Hx.
    assert (Hne : not_empty (WI.convert w)) by (rewrite Hx; exists 0%R; exact I).
    assert (H := WI.lower_correct w Hne).
    change (WF.convert (WI.lower w) = Xlower (WI.convert w)) in H.
    rewrite Hl, Hx in H. simpl in H. discriminate.
  - assert (Hne : not_empty (WI.convert w)) by (exists r; exact Hx).
    assert (HL := WI.lower_correct w Hne). assert (HU := WI.upper_correct w Hne).
    change (WF.convert (WI.lower w) = Xlower (WI.convert w)) in HL.
    change (WF.convert (WI.upper w) = Xupper (WI.convert w)) in HU.
    rewrite Hl in HL. rewrite Hu in HU.
    destruct (WI.convert w) as [|xl xu] eqn:Hw; [simpl in HL; discriminate|].
    simpl in HL, HU. subst xl xu. simpl in Hx. destruct Hx as [Hlr Hru].
    apply (contains_connected (I.convert (I.join a b)) l u).
    + apply I.join_correct. now left.
    + apply I.join_correct. now right.
    + split; assumption.
Qed.
