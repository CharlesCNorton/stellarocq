(** The checks behind the nonlinear step and the consistency of the
    three-dimensional problem, over cells of the radius.

    [ball_tab]: over s in a cell, h in [0, hhi], and every perturbation of
    the 27 unknown slots x, dm, dp of a collocation point's jet within rx
    (values) and rd (slopes) about the exact jet, every slot of the point's
    residual tail is real, and the tangent along each of the 27 slots of each
    of the 36 adjoint slots (the residual's partials in x, dm, dp and e of the
    nine unknowns) is real and bounded. The tangents are DerivSeq's forward
    derivatives of the adjoint list, so they bound the second partials of the
    residual on that box. [ball_cell_ok] also checks that the exact jet's
    inputs are real over the cell.

    [cons_tab]: over s in a cell and h in [0, hhi], the residual of the exact
    jet and its first two derivatives in h are real, and the second is
    bounded. *)

From Coq Require Import ZArith Reals List Bool Lia.
From Interval Require Import Interval.Interval.
From Stellarocq Require Import Expr Checker Newton TMEval LinCheck DerivSeq Adjoint CellTM.

Import ListNotations.

Section Ball.

Variable prec : F.precision.

(** The exact jet of point (u, v) over the box s in [slo, shi], h in [0, hhi]. *)
Definition jetbox (u v : expr) (slo shi hhi : Z * Z) : env I.type :=
  iextend prec (box_env prec (ival prec slo shi) (ival prec (0%Z, 0%Z) hhi)) (jet_layer u v 0).

(** The perturbed unknown slots: x, dm and dp of each of the nine unknowns. *)
Definition xdpc : list (nat * nat) := list_prod (seq 0 3) (seq 0 9).
Definition xdslots : list nat := map (fun pc => uslot (fst pc) (snd pc)) xdpc.
Definition eslots : list nat := map (uslot 3) (seq 0 9).

Definition sym (r : Z * Z) : I.type := let R := Newton.dyad prec r in I.join (I.neg R) R.

Definition widen (E : env I.type) (rx rd : Z * Z) : env I.type :=
  fold_left (fun E pc => let k := uslot (fst pc) (snd pc) in
                         eset k E (I.add prec (eget k E I.nai) (sym (if Nat.eqb (fst pc) 0 then rx else rd))))
            xdpc E.

(** A point bound on |X|, and the check that X is real and within it. *)
Definition ibound (X : I.type) : I.type := iupmax prec [I.abs X].
Definition rb (X : I.type) : bool := let B := ibound X in nonneg (I.sub prec B X) && nonneg (I.add prec X B).

(** The tails of the radial and poloidal points: the flattened residual and
    its adjoints. *)
Definition anfs (r : bool) : list binding * env nat * nat := if r then anf_r else anf_p.
Definition ab (r : bool) : list binding := fst (fst (anfs r)).
Definition ttop (r : bool) : nat := snd (anfs r).
Definition tout (r : bool) : nat := rget (snd (fst (anfs r))) rtop3.
Definition tl (r : bool) : list binding := ab r ++ adj_binds 87 (ttop r) (tout r) (ab r) ks40.

(** The adjoint slots of the 27 perturbed unknowns and of the nine e slots. *)
Definition gslots (r : bool) : list nat := map (fun k => in_slot 87 (ttop r) (tout r) (k - 12)) (xdslots ++ eslots).

(** The tails differentiated along each perturbed slot, built once and
    passed in. *)
Definition dtails (r : bool) : list (list binding) := map (fun l => with_dseq l 87 (length (tl r)) (tl r)) xdslots.

Definition ball_tab (r : bool) (dts : list (list binding)) (E : env I.type) : option (list (list I.type)) :=
  let n := length (tl r) in
  let F := iextend prec E (tl r) in
  if forallb (fun k => rb (eget k E I.nai)) (seq 0 87) && forallb (fun k => rb (eget k F I.nai)) (seq 87 n) then
    let T := map (fun bs => let G := iextend prec E bs in map (fun g => eget (g + n) G I.nai) (gslots r)) dts in
    if forallb (forallb rb) T then Some (map (map ibound) T) else None
  else None.

(** The exact residual's second derivative in h, from the output list with
    no perturbation, differentiated twice along slot 1. *)
Definition hlist (u v : expr) (r : bool) : list binding := with_dseq 1 3 (2 * len0) (with_dseq 1 3 len0 (out_list u v 0 r)).

Definition cons_tab (u v : expr) (r : bool) (slo shi hhi : Z * Z) : option I.type :=
  let F := iextend prec (box_env prec (ival prec slo shi) (ival prec (0%Z, 0%Z) hhi)) (hlist u v r) in
  if rb (eget rtop3 F I.nai) && rb (eget (rtop3 + len0) F I.nai) && rb (eget (rtop3 + 3 * len0) F I.nai)
  then Some (ibound (eget (rtop3 + 3 * len0) F I.nai)) else None.

(** Cell c of the radius: s in [1/4 + c 2^-8, 1/4 + (c + 1) 2^-8]. *)
Definition clo (c : nat) : Z * Z := (Z.of_nat (64 + c), (-8)%Z).
Definition chi (c : nat) : Z * Z := (Z.of_nat (65 + c), (-8)%Z).

Definition le_bound (K : Z * Z) (B : I.type) : bool := nonneg (I.sub prec (Newton.dyad prec K) B).

(** The verdicts of one point over one cell: the exact jet's inputs are real
    over the cell, and the tables of the moved jet are within K. *)
Definition ball_cell_ok (K rx rd hhi : Z * Z) (r : bool) (dts : list (list binding)) (kp c : nat) : bool :=
  let J := jetbox (fst (pt r kp)) (snd (pt r kp)) (clo c) (chi c) hhi in
  forallb (fun k => rb (eget k J I.nai)) (seq 0 87) &&
  match ball_tab r dts (widen J rx rd) with
  | Some T => forallb (forallb (le_bound K)) T
  | None => false
  end.

Definition cons_cell_ok (C hhi : Z * Z) (r : bool) (kp c : nat) : bool :=
  match cons_tab (fst (pt r kp)) (snd (pt r kp)) r (clo c) (chi c) hhi with
  | Some B => le_bound C B
  | None => false
  end.

End Ball.

Strategy expand [jetbox widen ibound rb tl ttop tout gslots dtails ball_tab hlist cons_tab clo chi le_bound
                 ball_cell_ok cons_cell_ok].
