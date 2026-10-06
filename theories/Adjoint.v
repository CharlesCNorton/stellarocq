(** Reverse-mode derivative lists.

    [anf base bs] flattens a well-formed binding list into single operations
    on atoms, slots or constants, from slot base on; binding n of bs lands on
    slot [rget m n] of the flattened list, m the renaming it returns.
    [adj_binds] appends to a flattened list ab, whose output is in slot o, the
    adjoint of every slot from o down to base, each the sum of what the
    bindings that read the slot contribute, and then the adjoint of each input
    slot of a list ks. One evaluation of the whole list then holds the
    partial derivative of the output in every input of ks, where a forward
    derivative list holds it in one. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Deriv DivDiff.

Import ListNotations.

(* ---------------------------------------------------------------- *)
(* Flattening                                                        *)

(** The renaming, kept as an environment; an unwritten slot keeps its number. *)
Definition rget (m : env nat) (k : nat) : nat := eget k m k.

(** The bindings of e from slot next on, prepended in reverse to acc, and the
    atom that holds the value of e. *)
Fixpoint anf_e (m : env nat) (e : expr) (next : nat) (acc : list binding) : expr * nat * list binding :=
  match e with
  | Evar k => (Evar (rget m k), next, acc)
  | EfromZ _ | Epi | Epow2 _ => (e, next, acc)
  | Eneg a => let '(a', n1, acc1) := anf_e m a next acc in (Evar n1, S n1, (n1, Eneg a') :: acc1)
  | Eadd a b =>
    let '(a', n1, acc1) := anf_e m a next acc in
    let '(b', n2, acc2) := anf_e m b n1 acc1 in (Evar n2, S n2, (n2, Eadd a' b') :: acc2)
  | Esub a b =>
    let '(a', n1, acc1) := anf_e m a next acc in
    let '(b', n2, acc2) := anf_e m b n1 acc1 in (Evar n2, S n2, (n2, Esub a' b') :: acc2)
  | Emul a b =>
    let '(a', n1, acc1) := anf_e m a next acc in
    let '(b', n2, acc2) := anf_e m b n1 acc1 in (Evar n2, S n2, (n2, Emul a' b') :: acc2)
  | Ediv a b =>
    let '(a', n1, acc1) := anf_e m a next acc in
    let '(b', n2, acc2) := anf_e m b n1 acc1 in (Evar n2, S n2, (n2, Ediv a' b') :: acc2)
  | Esqrt a => let '(a', n1, acc1) := anf_e m a next acc in (Evar n1, S n1, (n1, Esqrt a') :: acc1)
  | Esin a => let '(a', n1, acc1) := anf_e m a next acc in (Evar n1, S n1, (n1, Esin a') :: acc1)
  | Ecos a => let '(a', n1, acc1) := anf_e m a next acc in (Evar n1, S n1, (n1, Ecos a') :: acc1)
  | Eexp a => let '(a', n1, acc1) := anf_e m a next acc in (Evar n1, S n1, (n1, Eexp a') :: acc1)
  | Eatan a => let '(a', n1, acc1) := anf_e m a next acc in (Evar n1, S n1, (n1, Eatan a') :: acc1)
  end.

(** Each binding in turn; a binding whose value is a constant atom gets a
    slot of its own. *)
Fixpoint anf_l (m : env nat) (bs : list binding) (next : nat) (acc : list binding)
    : env nat * nat * list binding :=
  match bs with
  | [] => (m, next, acc)
  | (n, e) :: tl =>
    let '(a, n1, acc1) := anf_e m e next acc in
    match a with
    | Evar j => anf_l (eset n m j) tl n1 acc1
    | _ => anf_l (eset n m n1) tl (S n1) ((n1, a) :: acc1)
    end
  end.

(** The flattened list, the renaming and the first slot after the list. *)
Definition anf (base : nat) (bs : list binding) : list binding * env nat * nat :=
  let '(m, top, racc) := anf_l eempty bs base [] in (rev racc, m, top).

(* ---------------------------------------------------------------- *)
(* Adjoints                                                          *)

Definition sl (x c : expr) : list (nat * expr) := match x with Evar a => [(a, c)] | _ => [] end.

(** What binding n, of the single operation e, contributes to the adjoints of
    the slots it reads, its own adjoint being in slot an. *)
Definition contribs (an n : nat) (e : expr) : list (nat * expr) :=
  let A := Evar an in
  match e with
  | Evar a => [(a, A)]
  | Eneg x => sl x (Eneg A)
  | Eadd x y => sl x A ++ sl y A
  | Esub x y => sl x A ++ sl y (Eneg A)
  | Emul x y => sl x (Emul A y) ++ sl y (Emul A x)
  | Ediv x y => sl x (Ediv A y) ++ sl y (Eneg (Emul A (Ediv (Evar n) y)))
  | Esqrt x => sl x (Ediv A (Emul (EfromZ 2) (Evar n)))
  | Esin x => sl x (Emul A (Ecos x))
  | Ecos x => sl x (Eneg (Emul A (Esin x)))
  | Eexp x => sl x (Emul A (Evar n))
  | Eatan x => sl x (Ediv A (Eadd (EfromZ 1) (Emul x x)))
  | _ => []
  end.

Fixpoint esum (l : list expr) : expr :=
  match l with
  | [] => EfromZ 0
  | [c] => c
  | c :: tl => Eadd c (esum tl)
  end.

(** The adjoint of slot j <= o, the adjoints starting at slot top. *)
Definition aslot (top o j : nat) : nat := (top + (o - j))%nat.

(** For every slot, the contributions of the bindings up to o that read it. *)
Definition cmap (top o : nat) (ab : list binding) : env (list expr) :=
  fold_left (fun cm b =>
      if Nat.leb (fst b) o then
        fold_left (fun cm' jc => eset (fst jc) cm' (snd jc :: eget (fst jc) cm' []))
                  (contribs (aslot top o (fst b)) (fst b) (snd b)) cm
      else cm) ab eempty.

(** The adjoints of o, o - 1, ..., base in slots top, top + 1, ..., and then
    those of the inputs ks. *)
Definition adj_binds (base top o : nat) (ab : list binding) (ks : list nat) : list binding :=
  let cm := cmap top o ab in
  (top, EfromZ 1) ::
  map (fun dl => ((top + dl)%nat, esum (eget (o - dl)%nat cm []))) (seq 1 (o - base)) ++
  map (fun i => ((top + (o - base) + 1 + i)%nat, esum (eget (nth i ks 0%nat) cm []))) (seq 0 (length ks)).

(** The slot of the adjoint of the i-th input of ks. *)
Definition in_slot (base top o i : nat) : nat := (top + (o - base) + 1 + i)%nat.

(** The flattened list of bs from base, its output being binding o of bs,
    followed by the adjoints of the inputs ks. *)
Definition adj_list (base : nat) (bs : list binding) (o : nat) (ks : list nat) : list binding :=
  let '(ab, m, top) := anf base bs in ab ++ adj_binds base top (rget m o) ab ks.

Definition adj_in (base : nat) (bs : list binding) (o i : nat) : nat :=
  let '(ab, m, top) := anf base bs in in_slot base top (rget m o) i.
