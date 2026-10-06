(** Expression language with a proven-sound interval evaluator.

    Physics.v builds the force residual as values of type [expr]. This file
    gives [expr] two meanings: the intended value over extended reals
    ([xeval]) and a computable value over CoqInterval floating-point
    intervals ([ieval]). The lemma [ieval_correct] states that the interval
    always contains the extended-real value.

    Extended reals make partiality visible: a division by zero or a square
    root of a negative number produces Xnan. If the checker later shows the
    output interval is bounded, containment alone proves that the value is a
    real number and lies within the bounds.

    Subexpressions shared between the residual components are evaluated once
    through bindings: a binding (n, e) stores the value of e in environment
    slot n, and later expressions refer to it as [Evar n]. [iextend_correct]
    states that extending both environments by the same bindings preserves
    containment, so sharing costs no soundness. *)

From Coq Require Import ZArith Reals List Lia Lra.
From Coq Require Import FSets.FMapPositive.
From Flocq Require Import Core.
From Interval Require Import Float.Primitive_ops.
From Interval Require Import Real.Xreal Interval.Interval.
From Interval Require Import Interval.Float_full.

Import ListNotations.

(** The floating-point carrier: IEEE-754 binary64 primitive floats. *)
Module F := PrimitiveFloat.

(** Verified interval arithmetic over that carrier. *)
Module I := FloatIntervalFull F.

(* ---------------------------------------------------------------- *)
(* The environment                                                   *)

(** A residual has thousands of slots and reads each of them many times, so
    the environment is a map from slot to value rather than a list: a read
    costs the number of bits of the slot instead of the slot itself, and a
    write allocates that many nodes instead of rebuilding every slot below
    it. *)
Definition env (A : Type) : Type := PositiveMap.t A.

(** The key of slot n is the binary representation of n + 1, built by
    halving. [Nat.div2], addition and [Nat.compare] are the operations
    extraction realizes natively, which is why the parity test is a
    comparison rather than [Nat.even], whose unary recursion would cost the
    slot itself. The fuel is a termination argument and is never exhausted,
    since halving reaches one in fewer than m steps. *)
Fixpoint key_aux (fuel m : nat) : positive :=
  match fuel with
  | O => xH
  | S f =>
      match m with
      | O => xH
      | S O => xH
      | _ =>
          let h := Nat.div2 m in
          match Nat.compare (h + h) m with
          | Eq => xO (key_aux f h)
          | _ => xI (key_aux f h)
          end
      end
  end.

Definition key (n : nat) : positive := key_aux (S n) (S n).

(** Halving computes the standard injection. *)
Lemma key_aux_spec :
  forall fuel m, 0 < m -> m <= fuel -> key_aux fuel m = Pos.of_nat m.
Proof.
  induction fuel as [|f IH]; intros m Hm Hf. lia.
  destruct m as [|[|m']]. lia. reflexivity.
  cbn [key_aux].
  change (Nat.div2 (S (S m'))) with (S (Nat.div2 m')).
  assert (Hm' := Nat.div2_odd m').
  set (d := Nat.div2 m') in *. clearbody d.
  assert (Hb : Nat.b2n (Nat.odd m') <= 1)
    by (destruct (Nat.odd m'); cbn [Nat.b2n]; lia).
  assert (Hh : 0 < S d) by lia.
  assert (Hhf : S d <= f) by lia.
  rewrite (IH _ Hh Hhf).
  destruct (Nat.odd m') eqn:Ho; cbn [Nat.b2n] in Hm'.
  - replace (Nat.compare (S d + S d) (S (S m'))) with Lt
      by (symmetry; apply Nat.compare_lt_iff; lia).
    replace (S (S m')) with (S (S d + S d)) by lia.
    rewrite (Nat2Pos.inj_succ (S d + S d)) by lia.
    rewrite Nat2Pos.inj_add by lia.
    now rewrite Pos.add_diag.
  - replace (Nat.compare (S d + S d) (S (S m'))) with Eq
      by (symmetry; apply Nat.compare_eq_iff; lia).
    replace (S (S m')) with (S d + S d) by lia.
    rewrite Nat2Pos.inj_add by lia.
    now rewrite Pos.add_diag.
Qed.

Lemma key_spec : forall n, key n = Pos.of_succ_nat n.
Proof.
  intros n. unfold key. rewrite key_aux_spec by lia.
  now rewrite <- Pos.of_nat_succ.
Qed.

(** So distinct slots have distinct keys. *)
Lemma key_inj : forall n m, key n = key m -> n = m.
Proof.
  intros n m. rewrite !key_spec. apply SuccNat2Pos.inj.
Qed.

(** The environment with no slot written. *)
Definition eempty {A : Type} : env A := PositiveMap.empty A.

(** Read slot n, or the default when it has never been written. *)
Definition eget {A : Type} (n : nat) (e : env A) (d : A) : A :=
  match PositiveMap.find (key n) e with Some v => v | None => d end.

(** Every slot of the empty environment reads the default. *)
Lemma eget_eempty :
  forall (A : Type) n (d : A), eget n eempty d = d.
Proof.
  intros A n d. unfold eget, eempty. now rewrite PositiveMap.gempty.
Qed.

(** Write slot n. *)
Definition eset {A : Type} (n : nat) (e : env A) (v : A) : env A :=
  PositiveMap.add (key n) v e.

(** The written slot holds the new value. *)
Lemma eget_eset_eq :
  forall (A : Type) n (e : env A) d v, eget n (eset n e v) d = v.
Proof.
  intros A n e d v. unfold eget, eset. now rewrite PositiveMap.gss.
Qed.

(** Every other slot is unchanged. *)
Lemma eget_eset_neq :
  forall (A : Type) n k (e : env A) d v,
  k <> n -> eget k (eset n e v) d = eget k e d.
Proof.
  intros A n k e d v Hk. unfold eget, eset.
  rewrite PositiveMap.gso. reflexivity.
  intros Heq. apply Hk. now apply key_inj.
Qed.

(** Two writes to the same slot leave only the second. *)
Lemma add_overwrite :
  forall (A : Type) i (e : PositiveMap.t A) a b,
  PositiveMap.add i b (PositiveMap.add i a e) = PositiveMap.add i b e.
Proof.
  intros A i. induction i as [i IH|i IH|]; intros [|l o r] a b; simpl;
    try reflexivity; now rewrite IH.
Qed.

Lemma eset_overwrite :
  forall (A : Type) n (e : env A) a b, eset n (eset n e a) b = eset n e b.
Proof. intros A n e a b. unfold eset. apply add_overwrite. Qed.

(** Writes to different slots commute. *)
Lemma add_comm :
  forall (A : Type) i j (e : PositiveMap.t A) v w,
  i <> j ->
  PositiveMap.add i v (PositiveMap.add j w e)
  = PositiveMap.add j w (PositiveMap.add i v e).
Proof.
  intros A i. induction i as [i IH|i IH|];
    intros [j|j|] [|l o r] v w Hij; simpl; try reflexivity;
    try (now rewrite IH by congruence);
    try (destruct i; reflexivity);
    try (destruct j; reflexivity);
    congruence.
Qed.

Lemma eset_comm :
  forall (A : Type) n m (e : env A) v w,
  n <> m ->
  eset n (eset m e w) v = eset m (eset n e v) w.
Proof.
  intros A n m e v w Hnm. unfold eset. apply add_comm.
  intros Heq. apply Hnm. now apply key_inj.
Qed.

(** Writing the value a slot already holds changes nothing. *)
Lemma add_same :
  forall (A : Type) i (e : PositiveMap.t A) v,
  PositiveMap.find i e = Some v -> PositiveMap.add i v e = e.
Proof.
  intros A i. induction i as [i IH|i IH|]; intros [|l o r] v Hf;
    simpl in *; try discriminate; try (now rewrite IH).
  destruct o; simpl in Hf; try discriminate. now injection Hf as <-.
Qed.

Lemma eset_same :
  forall (A : Type) n (e : env A) v,
  PositiveMap.find (key n) e = Some v -> eset n e v = e.
Proof. intros A n e v H. unfold eset. now apply add_same. Qed.

(** A write to another slot leaves this one's binding alone, which is what
    lets a slot already holding its own value be written again for nothing. *)
Lemma find_eset_neq :
  forall (A : Type) n m (e : env A) v,
  n <> m -> PositiveMap.find (key n) (eset m e v) = PositiveMap.find (key n) e.
Proof.
  intros A n m e v H. unfold eset. apply PositiveMap.gso.
  intros Heq. apply H. now apply key_inj.
Qed.

(* ---------------------------------------------------------------- *)
(* The environment of a list of slot values                          *)

(** The inputs of a point arrive as a list, one entry per slot. *)
Fixpoint of_list_from {A : Type} (n : nat) (l : list A) : env A :=
  match l with
  | [] => PositiveMap.empty A
  | x :: tl => eset n (of_list_from (S n) tl) x
  end.

Definition of_list {A : Type} (l : list A) : env A := of_list_from 0 l.

Lemma eget_of_list_from :
  forall (A : Type) (l : list A) n k d,
  eget (n + k) (of_list_from n l) d = nth k l d.
Proof.
  intros A l. induction l as [|x tl IH]; intros n k d.
  - unfold eget. simpl. rewrite PositiveMap.gempty. now destruct k.
  - destruct k as [|k].
    + rewrite Nat.add_0_r. simpl. apply eget_eset_eq.
    + simpl of_list_from. rewrite eget_eset_neq by lia.
      replace (n + S k) with (S n + k) by lia. apply IH.
Qed.

(** So a slot of that environment is the matching entry of the list. *)
Lemma eget_of_list :
  forall (A : Type) (l : list A) k d, eget k (of_list l) d = nth k l d.
Proof. intros A l k d. exact (eget_of_list_from A l 0 k d). Qed.

(** And a slot inside the list is present, not merely readable. *)
Lemma find_of_list_from :
  forall (A : Type) (l : list A) n k d,
  k < length l ->
  PositiveMap.find (key (n + k)) (of_list_from n l) = Some (nth k l d).
Proof.
  intros A l. induction l as [|x tl IH]; intros n k d Hk. simpl in Hk. lia.
  destruct k as [|k].
  - rewrite Nat.add_0_r. simpl. unfold eset. now rewrite PositiveMap.gss.
  - simpl of_list_from. unfold eset.
    rewrite PositiveMap.gso by (intros Heq; assert (n + S k = n) by (now apply key_inj); lia).
    replace (n + S k) with (S n + k) by lia.
    apply IH. simpl in Hk. lia.
Qed.

Lemma find_of_list :
  forall (A : Type) (l : list A) k d,
  k < length l -> PositiveMap.find (key k) (of_list l) = Some (nth k l d).
Proof. intros A l k d Hk. exact (find_of_list_from A l 0 k d Hk). Qed.

(** So writing back the entry a slot already holds changes nothing. *)
Lemma eset_of_list_same :
  forall (A : Type) (l : list A) k (d : A),
  k < length l -> eset k (of_list l) (nth k l d) = of_list l.
Proof. intros A l k d Hk. apply eset_same. now apply find_of_list. Qed.

Section Expr.

(** Working precision of the interval operations. *)
Variable prec : F.precision.

(** Arithmetic expressions over environment variables, integers, and pi. *)
Inductive expr : Type :=
  | Evar   : nat -> expr
  | EfromZ : Z -> expr
  | Epi    : expr
  | Eneg   : expr -> expr
  | Eadd   : expr -> expr -> expr
  | Esub   : expr -> expr -> expr
  | Emul   : expr -> expr -> expr
  | Ediv   : expr -> expr -> expr
  | Esqrt  : expr -> expr
  | Esin   : expr -> expr
  | Ecos   : expr -> expr
  | Eexp   : expr -> expr
  | Eatan  : expr -> expr
  | Epow2  : Z -> expr.

(** Intended value over extended reals; an out-of-range variable is Xnan. *)
Fixpoint xeval (env : env ExtendedR) (e : expr) : ExtendedR :=
  match e with
  | Evar n     => eget n env Xnan
  | EfromZ z   => Xreal (IZR z)
  | Epi        => Xreal PI
  | Eneg a     => Xneg (xeval env a)
  | Eadd a b   => Xadd (xeval env a) (xeval env b)
  | Esub a b   => Xsub (xeval env a) (xeval env b)
  | Emul a b   => Xmul (xeval env a) (xeval env b)
  | Ediv a b   => Xdiv (xeval env a) (xeval env b)
  | Esqrt a    => Xsqrt (xeval env a)
  | Esin a     => Xsin (xeval env a)
  | Ecos a     => Xcos (xeval env a)
  | Eexp a     => Xexp (xeval env a)
  | Eatan a    => Xatan (xeval env a)
  | Epow2 e    => Xreal (powerRZ 2%R e)
  end.

(** Computable value over intervals; this is what the checker executes. *)
Fixpoint ieval (env : env I.type) (e : expr) : I.type :=
  match e with
  | Evar n     => eget n env I.nai
  | EfromZ z   => I.fromZ prec z
  | Epi        => I.pi prec
  | Eneg a     => I.neg (ieval env a)
  | Eadd a b   => I.add prec (ieval env a) (ieval env b)
  | Esub a b   => I.sub prec (ieval env a) (ieval env b)
  | Emul a b   => I.mul prec (ieval env a) (ieval env b)
  | Ediv a b   => I.div prec (ieval env a) (ieval env b)
  | Esqrt a    => I.sqrt prec (ieval env a)
  | Esin a     => I.sin prec (ieval env a)
  | Ecos a     => I.cos prec (ieval env a)
  | Eexp a     => I.exp prec (ieval env a)
  | Eatan a    => I.atan prec (ieval env a)
  | Epow2 e    => I.power_int prec (I.fromZ prec 2) e
  end.

(** Each interval environment entry contains its extended-real counterpart. *)
Definition env_ok (ienv : env I.type) (xenv : env ExtendedR) : Prop :=
  forall n, contains (I.convert (eget n ienv I.nai)) (eget n xenv Xnan).

(** Soundness: the evaluated interval contains the extended-real value. *)
Lemma ieval_correct :
  forall ienv xenv e,
  env_ok ienv xenv ->
  contains (I.convert (ieval ienv e)) (xeval xenv e).
Proof.
  intros ienv xenv e Hnth.
  induction e; simpl.
  - apply Hnth.
  - now apply I.fromZ_correct.
  - apply I.pi_correct.
  - now apply I.neg_correct.
  - now apply I.add_correct.
  - now apply I.sub_correct.
  - now apply I.mul_correct.
  - now apply I.div_correct.
  - now apply I.sqrt_correct.
  - now apply I.sin_correct.
  - now apply I.cos_correct.
  - now apply I.exp_correct.
  - now apply I.atan_correct.
  - (* a power of two *)
    assert (Hc : contains (I.convert (I.fromZ prec 2)) (Xreal (IZR 2)))
      by apply I.fromZ_correct.
    assert (H := I.power_int_correct prec z _ _ Hc).
    unfold Xpower_int, Xpower_int' in H.
    destruct z as [|q|q]; cbv beta iota delta [Xbind] in H; try exact H.
    revert H. generalize (is_zero_spec 2%R). case (is_zero 2%R).
    + intros Hz0 H. exfalso. inversion Hz0 as [Heq|Hne]. lra.
    + intros Hz0 H. exact H.
Qed.

(* ---------------------------------------------------------------- *)
(* Bindings: shared subexpressions stored in environment slots       *)

(** A binding stores the value of an expression in a slot. *)
Definition binding : Type := (nat * expr)%type.

(** Extended-real environment after the bindings, in order. *)
Definition xextend (xenv : env ExtendedR) (bs : list binding) : env ExtendedR :=
  fold_left (fun e b => eset (fst b) e (xeval e (snd b))) bs xenv.

(** Interval environment after the bindings, in order. *)
Definition iextend (ienv : env I.type) (bs : list binding) : env I.type :=
  fold_left (fun e b => eset (fst b) e (ieval e (snd b))) bs ienv.

(** Storing a contained value in the same slot of both environments keeps
    every slot contained. *)
Lemma env_ok_eset :
  forall ienv xenv n vi vx,
  env_ok ienv xenv ->
  contains (I.convert vi) vx ->
  env_ok (eset n ienv vi) (eset n xenv vx).
Proof.
  intros ienv xenv n vi vx Hnth Hv k.
  destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite !eget_eset_eq. exact Hv.
  - rewrite !eget_eset_neq by exact Hne. apply Hnth.
Qed.

(** Extending both environments by the same bindings preserves containment. *)
Lemma iextend_correct :
  forall bs ienv xenv,
  env_ok ienv xenv ->
  env_ok (iextend ienv bs) (xextend xenv bs).
Proof.
  induction bs as [|[n e] bs IH]; intros ienv xenv Henv; simpl.
  - exact Henv.
  - apply IH.
    apply env_ok_eset.
    + exact Henv.
    + now apply ieval_correct.
Qed.

End Expr.
