(** The linear stability checker of the three-dimensional manufactured
    problem: the binding lists it evaluates. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff RegResidual Jet DerivSeq Newton Adjoint.

Import ListNotations.

(** The collocation angles of the radial and the poloidal rows. *)
Definition ang (m e : Z) : expr := edyad m e.
Definition pts_s : list (expr * expr) :=
  [(ang 4716158501352293 (-53), EfromZ 0); (ang 5895198126690367 (-51), EfromZ 0);
   (ang 4716158501352293 (-53), ang 176855943800711 (-47));
   (ang 5895198126690367 (-51), ang 7545853602163669 (-53));
   (ang 884279719003555 (-49), ang 7545853602163669 (-54))].
Definition pts_u : list (expr * expr) :=
  [(ang 884279719003555 (-49), EfromZ 0); (ang 884279719003555 (-49), ang 7545853602163669 (-53));
   (ang 5895198126690367 (-51), ang 7545853602163669 (-52));
   (ang 4716158501352293 (-53), ang 7545853602163669 (-52))].

(** The outer environment from the inputs s (slot 0), h (slot 1) and the
    perturbation t (slot 2), which moves slot k. The sources do not enter a
    derivative in the coefficients and are taken as zero. *)
Definition jet_layer (u v : expr) (k : nat) : list binding :=
  map (fun i => (3 + i, let e := jet_e u v (EfromZ 0) (EfromZ 0) (3 + i) in
                        if Nat.eqb (3 + i) k then Eadd e (Evar 2) else e)%nat)
      (seq 0 (ntop - 3)).

Definition rtop3 : nat := (ntop + length (reg_binds modes3d))%nat.

(** The radial or poloidal output, bound to the slot after the residual's. *)
Definition out_list (u v : expr) (k : nat) (radial : bool) : list binding :=
  jet_layer u v k ++ reg_binds modes3d ++ [(rtop3, if radial then reg_fs modes3d else reg_fu modes3d)].

Definition len0 : nat := (ntop - 3 + length (reg_binds modes3d) + 1)%nat.

Lemma out_list_len : forall u v k r, length (out_list u v k r) = len0.
Proof. intros. unfold out_list, len0, jet_layer. rewrite !length_app, length_map, length_seq. reflexivity. Qed.

Definition chk_wf : bool := well_formed 87 (reg_binds modes3d).

(* ---------------------------------------------------------------- *)
(* The adjoint lists                                                 *)

(** The residual's bindings and the radial or poloidal output, over the jet's
    slots below 87. *)
Definition tail (radial : bool) : list binding :=
  reg_binds modes3d ++ [(rtop3, if radial then reg_fs modes3d else reg_fu modes3d)].

(** The coefficient slots of the jet, whose adjoints the lists end with. *)
Definition ks40 : list nat := seq 12 40.

Definition anf_r : list binding * env nat * nat := anf 87 (tail true).
Definition anf_p : list binding * env nat * nat := anf 87 (tail false).
Definition top_r : nat := snd anf_r.
Definition top_p : nat := snd anf_p.
Definition out_r : nat := rget (snd (fst anf_r)) rtop3.
Definition out_p : nat := rget (snd (fst anf_p)) rtop3.

(** The flattened output list and its adjoints, radial and poloidal. *)
Definition tail_r : list binding := fst (fst anf_r) ++ adj_binds 87 top_r out_r (fst (fst anf_r)) ks40.
Definition tail_p : list binding := fst (fst anf_p) ++ adj_binds 87 top_p out_p (fst (fst anf_p)) ks40.

(** The adjoint list of the point (u, v): its jet, then the flattened
    residual and the adjoints. *)
Definition alist (u v : expr) (radial : bool) : list binding :=
  jet_layer u v 0 ++ (if radial then tail_r else tail_p).

(* ---------------------------------------------------------------- *)
(* The derivative lists                                              *)

(** Along t, the coefficient slot's perturbation: the partial derivative in
    slot k. Its output derivative is at rtop3 + len0. *)
Definition L1 (u v : expr) (k : nat) (r : bool) : list binding := with_dseq 2 3 len0 (out_list u v k r).
(** Then along s and along h: their derivatives of slot rtop3 + len0 are at
    rtop3 + 3 len0. *)
Definition L2 (x : nat) (u v : expr) (k : nat) (r : bool) : list binding := with_dseq x 3 (2 * len0) (L1 u v k r).
(** And along s again, or along h, of the s-derivative: at rtop3 + 7 len0. *)
Definition L3 (x : nat) (u v : expr) (k : nat) (r : bool) : list binding := with_dseq x 3 (4 * len0) (L2 0 u v k r).

Definition sl_d1 : nat := (rtop3 + len0)%nat.
Definition sl_d2 : nat := (rtop3 + 3 * len0)%nat.
Definition sl_d3 : nat := (rtop3 + 7 * len0)%nat.

(** The interval inputs: s and h over a box, t zero. *)
Definition box_env (prec : F.precision) (si hi : I.type) : env I.type :=
  eset 2 (eset 1 (eset 0 eempty si) hi) (I.fromZ prec 0).

Definition ival (prec : F.precision) (lo hi : Z * Z) : I.type :=
  I.join (Newton.dyad prec lo) (Newton.dyad prec hi).

(** The slots of the coefficient perturbed: x, dm, dp, e of each of the nine
    unknowns, R modes 0 .. 4 and Z modes 1 .. 4. *)
Definition uslot (part c : nat) : nat :=
  let RZ := if Nat.ltb c 5 then (part * 5 + c)%nat else (20 + part * 5 + (c - 4))%nat in
  (12 + RZ)%nat.

(** The slot of the adjoint list that holds the partial in part (x, dm, dp, e)
    of unknown c. *)
Definition aslot_in (radial : bool) (part c : nat) : nat :=
  if radial then in_slot 87 top_r out_r (uslot part c - 12) else in_slot 87 top_p out_p (uslot part c - 12).

(** One cell, one point, one slot: the partial derivative, its s- and
    h-derivatives, and for a second difference slot the two second
    derivatives of its s-derivative. *)
Definition probe_slot (prec : F.precision) (si hi : I.type) (u v : expr) (k : nat) (r third : bool)
    : list I.type :=
  let e0 := box_env prec si hi in
  let F2s := iextend prec e0 (L2 0 u v k r) in
  let F2h := iextend prec e0 (L2 1 u v k r) in
  let base := [eget sl_d1 F2s I.nai; eget sl_d2 F2s I.nai; eget sl_d2 F2h I.nai] in
  if third then
    base ++ [eget sl_d3 (iextend prec e0 (L3 0 u v k r)) I.nai; eget sl_d3 (iextend prec e0 (L3 1 u v k r)) I.nai]
  else base.

Definition probe_point (prec : F.precision) (si hi : I.type) (u v : expr) (r : bool) : list (list I.type) :=
  map (fun pc => let part := fst pc in let c := snd pc in
                 probe_slot prec si hi u v (uslot part c) r (r && Nat.eqb part 3))
      (if r then list_prod (seq 0 4) (seq 0 9) else list_prod [0%nat; 2%nat] (seq 0 9)).
