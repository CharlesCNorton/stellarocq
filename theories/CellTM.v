(** The step matrix of the collocated three-dimensional problem over one cell
    of (s, h), in Taylor models.

    The blocks of the one-step map are partial derivatives of the radial and
    poloidal residuals at the collocation points in the jet's coefficient
    slots, all of one point held by the adjoint slots of its LinCheck list
    ([plist]); [pval] reads them as real functions of (s, h), and [bN] is
    Step.v's N built from them: Pp = Re + h Rdp, Pm = Re - h Rdm, Sx = Rx,
    Up = Rdp of the poloidal rows, V = Rx of the poloidal rows, with Pm taken
    at s + h.

    [cell_core] evaluates the list of each point once in Taylor models over
    the cell s in sc +- a, h in hc +- b, the radial points' lists tripled by
    QDiff ([qlist]), so that their layers hold every partial at s and at
    s + h and Q = (Pm(s + h, h) - Pp(s, h)) / h comes from the difference
    layer with no h in a denominator. M = [Pp; Up] is inverted by
    a Neumann series preconditioned with a binary64 inverse of M at the centre
    ([finv], whose accuracy nothing depends on), its tail bounded by
    TMat.neu_tail and added to every remainder. [cell_range] conjugates N by a
    frame W and returns the entrywise range of W N W^-1 over the cell;
    [start_range] returns that of the start rows [Pm(s + h, h), -h I] (I + h N)
    W^-1 at s = 1/4 over the steps h. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Cell Newton Mat IMat LinCheck TMEval TMat QDiff
  Recur Step.

Import ListNotations.

(* ---------------------------------------------------------------- *)
(* The blocks as real functions                                      *)

Definition ptsr (r : bool) : list (expr * expr) := if r then pts_s else pts_u.

Definition pt (r : bool) (kp : nat) : expr * expr := nth kp (ptsr r) (EfromZ 0, EfromZ 0).

(** The adjoint list of point kp's residual, radial or poloidal, and the
    tripled list of a radial point. *)
Definition plist (r : bool) (kp : nat) : list binding := alist (fst (pt r kp)) (snd (pt r kp)) r.

Definition qlist (kp : nat) : list binding := QL_with (fxenv q_in (plist true kp)) (plist true kp).

Definition xreal (x : ExtendedR) : R := match x with Xreal r => r | Xnan => 0%R end.

(** The partial of point kp's residual in part (x, dm, dp, e) of unknown c. *)
Definition pval (r : bool) (kp part c : nat) (s h : R) : R :=
  xreal (eget (aslot_in r part c) (xextend (pin s h 0) (plist r kp)) Xnan).

Local Open Scope R_scope.

Definition bPp (s h : R) : mat := fun i c => pval true i 3 c s h + h * pval true i 2 c s h.
Definition bPm (s h : R) : mat := fun i c => pval true i 3 c s h - h * pval true i 1 c s h.
Definition bSx (s h : R) : mat := fun i c => pval true i 0 c s h.
Definition bUp (s h : R) : mat := fun i c => pval false i 2 c s h.
Definition bV (s h : R) : mat := fun i c => pval false i 0 c s h.

Definition bN (s h : R) : mat := Nmat h (bPp s h) (bPm (s + h) h) (bSx s h) (bUp s h) (bV s h).

(** The start rows [Pm(s + h, h), -h I] (I + h N) at s. *)
Definition bC (s h : R) : mat := fun i c => if Nat.ltb c 9 then bPm (s + h) h i c else if Nat.eqb (c - 9) i then - h else 0.
Definition bCs (s h : R) : mat := mm 14 (bC s h) (fun i c => mI i c + h * bN s h i c).

Local Close Scope R_scope.

(* ---------------------------------------------------------------- *)
(* A binary64 inverse, for the preconditioner                        *)

Definition fz : F.type := F.fromZ 0.
Definition fone : F.type := F.fromZ 1.
Definition fget (A : list (list F.type)) (i j : nat) : F.type := nth j (nth i A []) fz.

Definition fswap (A : list (list F.type)) (i j : nat) : list (list F.type) :=
  map (fun k => nth (if Nat.eqb k i then j else if Nat.eqb k j then i else k) A []) (seq 0 (length A)).

Definition fpivot (A : list (list F.type)) (col n : nat) : nat :=
  fold_left (fun b r => if PrimFloat.ltb (PrimFloat.abs (fget A b col)) (PrimFloat.abs (fget A r col)) then r else b)
            (seq col (n - col)) col.

Definition fgj_col (n : nat) (A : list (list F.type)) (col : nat) : list (list F.type) :=
  let A1 := fswap A col (fpivot A col n) in
  let rc := map (fun x => PrimFloat.div x (fget A1 col col)) (nth col A1 []) in
  map (fun r => if Nat.eqb r col then rc
                else let f := fget A1 r col in
                     map (fun xy => PrimFloat.sub (fst xy) (PrimFloat.mul f (snd xy))) (combine (nth r A1 []) rc))
      (seq 0 n).

(** Gauss-Jordan elimination with partial pivoting on [A | I]. *)
Definition finv (n : nat) (A : list (list F.type)) : list (list F.type) :=
  let aug := map (fun i => map (fun j => fget A i j) (seq 0 n) ++ map (fun j => if Nat.eqb i j then fone else fz) (seq 0 n))
                 (seq 0 n) in
  map (fun row => skipn n row) (fold_left (fgj_col n) (seq 0 n) aug).

(* ---------------------------------------------------------------- *)
(* The cell                                                          *)

Section Cell.

Variable prec : F.precision.
Variable d : nat.
Variable tab : tmtab.

(** A point above the largest upper bound of a list, by a relative 2^-40
    and an absolute 2^-1000, so that it stays above every bound after an
    outward-rounded subtraction. *)
Definition iupmax (L : list I.type) : I.type :=
  let mx := I.singleton (fold_left (fun acc X => F.max acc (I.upper X)) L fz) in
  I.singleton (I.upper (I.add prec (I.mul prec mx (Newton.dyad prec (1%Z, (-40)%Z)))
                                   (I.add prec mx (Newton.dyad prec (1%Z, (-1000)%Z))))).

Definition mrlo_of (U W : I.type) : list I.type :=
  map (fun m => I.mul prec (ipow prec U (fst m)) (ipow prec W (snd m))) (mons d).

Definition tenv_p (ts th : tm) : env otm :=
  eset 2 (eset 1 (eset 0 eempty (Some ts)) (Some th)) (Some (tconst d I.zero)).

Definition tenv_q (ts tsh th : tm) : env otm :=
  eset 8 (eset 7 (eset 6 (eset 5 (eset 4 (eset 3 (eset 2 (eset 1 (eset 0 eempty
    (Some ts)) (Some tsh)) (Some (tconst d (I.fromZ prec 1)))) (Some th)) (Some th))
    (Some (tconst d I.zero))) (Some (tconst d I.zero))) (Some (tconst d I.zero))) (Some (tconst d I.zero)).

(** The evaluated lists of the five radial points, tripled, and of the four
    poloidal ones, each evaluated once. *)
Definition renvs (mrlo : list I.type) (te : env otm) : list (env otm) :=
  map (fun kp => tmextend prec d tab mrlo te (qlist kp)) (seq 0 5).
Definition penvs (mrlo : list I.type) (te : env otm) : list (env otm) :=
  map (fun kp => tmextend prec d tab mrlo te (plist false kp)) (seq 0 4).

(** A block read from the evaluated lists: layer f of the partials in part. *)
Definition rblk (Fs : list (env otm)) (f : nat -> nat) (part : nat) : list (list otm) :=
  map (fun kp => map (fun c => eget (f (aslot_in true part c)) (nth kp Fs eempty) None) (seq 0 9)) (seq 0 5).
Definition pblk (Gs : list (env otm)) (part : nat) : list (list otm) :=
  map (fun kp => map (fun c => eget (aslot_in false part c) (nth kp Gs eempty) None) (seq 0 9)) (seq 0 4).

Definition osome (o : otm) : bool := match o with Some _ => true | None => false end.
Definition oval (o : otm) : tm := match o with Some t => t | None => tz d end.
Definition ofull (M : list (list otm)) : option tmat :=
  if forallb (forallb osome) M then Some (map (map oval) M) else None.

Definition obind {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.

(** The blocks over the cell. *)
Record blocks : Type := Blocks {
  b_Rx : tmat; b_Rdp : tmat; b_Rdm' : tmat; b_Ux : tmat; b_Up : tmat; b_Re : tmat; b_Rep : tmat; b_DD : tmat }.

Definition cell_mrlo (a b : Z * Z) : list I.type :=
  let Ia := Newton.dyad prec a in let Ib := Newton.dyad prec b in
  mrlo_of (I.join (I.neg Ia) Ia) (I.join (I.neg Ib) Ib).

(** The blocks from the evaluated lists Fs and Gs, passed in by the caller:
    Rx, Rdp and Re at s and Rdm and Re at s + h from the layers of the
    radial lists, their difference layer for Q, Ux and Up from the poloidal
    lists. *)
Definition blocks_of (Fs Gs : list (env otm)) : option blocks :=
  obind (ofull (rblk Fs lm 0)) (fun Rx =>
  obind (ofull (rblk Fs lm 2)) (fun Rdp =>
  obind (ofull (rblk Fs lp 1)) (fun Rdm' =>
  obind (ofull (pblk Gs 0)) (fun Ux =>
  obind (ofull (pblk Gs 2)) (fun Up =>
  obind (ofull (rblk Fs lm 3)) (fun Re =>
  obind (ofull (rblk Fs lp 3)) (fun Rep =>
  obind (ofull (rblk Fs ld 3)) (fun DD =>
  Some (Blocks Rx Rdp Rdm' Ux Up Re Rep DD))))))))).

Definition cell_blocks (mrlo : list I.type) (ts th : tm) : option blocks :=
  blocks_of (renvs mrlo (tenv_q ts (tadd prec d ts th) th)) (penvs mrlo (tenv_p ts th)).

Definition t_Pp (mrlo : list I.type) (th : tm) (B : blocks) : tmat :=
  ttab 5 9 (fun i c => tadd prec d (tget d (b_Re B) i c) (tmul prec d tab mrlo th (tget d (b_Rdp B) i c))).
Definition t_Q (B : blocks) : tmat :=
  ttab 5 9 (fun i c => tsub prec d (tsub prec d (tget d (b_DD B) i c) (tget d (b_Rdm' B) i c)) (tget d (b_Rdp B) i c)).
Definition t_M (mrlo : list I.type) (th : tm) (B : blocks) : tmat :=
  ttab 9 9 (fun i c => if Nat.ltb i 5 then tget d (t_Pp mrlo th B) i c else tget d (b_Up B) (i - 5) c).
Definition t_SVE (mrlo : list I.type) (th : tm) (B : blocks) : tmat :=
  ttab 9 14 (fun i c =>
    if Nat.ltb c 9 then
      (if Nat.ltb i 5 then tneg d (tmul prec d tab mrlo th (tget d (b_Rx B) i c)) else tneg d (tget d (b_Ux B) (i - 5) c))
    else if Nat.ltb i 5 && Nat.eqb (c - 9) i then tconst d (I.fromZ prec 1) else tz d).
Definition t_Id (n : nat) : tmat := ttab n n (fun i c => tconst d (I.fromZ prec (if Nat.eqb i c then 1%Z else 0%Z))).

(** The preconditioner: a binary64 inverse of the centre of M. *)
Definition t_P (M : tmat) : imat :=
  let Pf := finv 9 (map (fun i => map (fun c => I.midpoint (cget (tpoly (tget d M i c)) 0)) (seq 0 9)) (seq 0 9)) in
  itab 9 9 (fun i c => I.singleton (fget Pf i c)).

(** Y = M^-1 [SV E5] and then N, when the preconditioned M is within th0 < 1
    of the identity on both sides. *)
Definition t_N (mrlo : list I.type) (th : tm) (B : blocks) (kn : nat) : option tmat :=
  let M := t_M mrlo th B in
  let PI := t_P M in
  let E := tmsub prec d 9 9 (t_Id 9) (tcm prec d 9 9 9 PI M) in
  let E' := tmsub prec d 9 9 (t_Id 9) (tmc prec d 9 9 9 M PI) in
  let RE := tmrange prec d tab mrlo 9 9 E in
  let RE' := tmrange prec d tab mrlo 9 9 E' in
  let th0 := iupmax (map (irowsum prec 9 RE) (seq 0 9) ++ map (irowsum prec 9 RE') (seq 0 9)) in
  let C := tcm prec d 9 9 14 PI (t_SVE mrlo th B) in
  let RC := tmrange prec d tab mrlo 9 14 C in
  let gam := iupmax (map (irowsum prec 14 RC) (seq 0 9)) in
  if inorm_le prec 9 9 RE th0 && inorm_le prec 9 9 RE' th0 && inorm_le prec 9 14 RC gam
     && ipos (I.sub prec (I.fromZ prec 1) th0) then
    let tau := I.mul prec (I.div prec (ipow prec th0 (S kn)) (I.sub prec (I.fromZ prec 1) th0)) gam in
    let Y := tmball prec d 9 14 (I.join (I.neg tau) tau) (tneu prec d tab mrlo 9 14 E C kn) in
    let QY := tmm prec d tab mrlo 5 9 14 (t_Q B) Y in
    Some (ttab 14 14 (fun i c =>
            if Nat.ltb i 9 then tget d Y i c
            else if Nat.ltb c 9 then tsub prec d (tget d QY (i - 9) c) (tget d (b_Rx B) (i - 9) c)
            else tget d QY (i - 9) c))
  else None.

Definition cell_core (sc hc a b : Z * Z) (kn : nat) : option (list I.type * tm * tmat * blocks) :=
  let mrlo := cell_mrlo a b in
  let th := tvar_w prec d (Newton.dyad prec hc) in
  obind (cell_blocks mrlo (tvar_u prec d (Newton.dyad prec sc)) th) (fun B =>
  obind (t_N mrlo th B kn) (fun N => Some (mrlo, th, N, B))).

(** The range of W N W^-1 over the cell, WiI enclosing W^-1. *)
Definition cell_range (sc hc a b : Z * Z) (kn : nat) (W : list (list (Z * Z))) (WiI : imat) : option imat :=
  obind (cell_core sc hc a b kn) (fun r =>
    let '(mrlo, _, N, _) := r in
    Some (tmrange prec d tab mrlo 14 14 (tmc prec d 14 14 14 (tcm prec d 14 14 14 (idmat prec 14 14 W) N) WiI))).

(** The q-th of the 2^p equal parts of the cell's s-interval: u in uc +- r,
    with r = a / 2^p and uc = (2q + 1 - 2^p) r. *)
Definition urad (a : Z * Z) (p : nat) : Z * Z := (fst a, (snd a - Z.of_nat p)%Z).
Definition ucen (a : Z * Z) (p q : nat) : Z * Z :=
  ((fst a * (2 * Z.of_nat q + 1 - 2 ^ Z.of_nat p))%Z, (snd a - Z.of_nat p)%Z).

(** The monomial ranges over that part. *)
Definition sub_mrlo (a b : Z * Z) (p q : nat) : list I.type :=
  let Ir := Newton.dyad prec (urad a p) in
  let Ib := Newton.dyad prec b in
  mrlo_of (I.add prec (Newton.dyad prec (ucen a p q)) (I.join (I.neg Ir) Ir)) (I.join (I.neg Ib) Ib).

(** The ranges of W N W^-1 over the 2^p parts of the cell's s-interval, all
    from the one model of the cell. *)
Definition cell_ranges (sc hc a b : Z * Z) (kn p : nat) (W : list (list (Z * Z))) (WiI : imat)
    : option (list imat) :=
  obind (cell_core sc hc a b kn) (fun r =>
    let '(mrlo, _, N, _) := r in
    let NW := tmc prec d 14 14 14 (tcm prec d 14 14 14 (idmat prec 14 14 W) N) WiI in
    Some (map (fun q => tmrange prec d tab (sub_mrlo a b p q) 14 14 NW) (seq 0 (2 ^ p)))).

(** Bounds over the cell: |M^-1| <= |P| / (1 - th0) through the
    preconditioner P, with P M and M P within th0 < 1 of the identity, and
    |M| and |Q| from their ranges. *)
Definition t_Mb (mrlo : list I.type) (th : tm) (B : blocks) : option (I.type * I.type * I.type) :=
  let M := t_M mrlo th B in
  let PI := t_P M in
  let RE := tmrange prec d tab mrlo 9 9 (tmsub prec d 9 9 (t_Id 9) (tcm prec d 9 9 9 PI M)) in
  let RE' := tmrange prec d tab mrlo 9 9 (tmsub prec d 9 9 (t_Id 9) (tmc prec d 9 9 9 M PI)) in
  let th0 := iupmax (map (irowsum prec 9 RE) (seq 0 9) ++ map (irowsum prec 9 RE') (seq 0 9)) in
  let nP := iupmax (map (irowsum prec 9 PI) (seq 0 9)) in
  let RM := tmrange prec d tab mrlo 9 9 M in
  let nM := iupmax (map (irowsum prec 9 RM) (seq 0 9)) in
  let RQ := tmrange prec d tab mrlo 5 9 (t_Q B) in
  let nQ := iupmax (map (irowsum prec 9 RQ) (seq 0 5)) in
  if inorm_le prec 9 9 RE th0 && inorm_le prec 9 9 RE' th0 && ipos (I.sub prec (I.fromZ prec 1) th0)
     && inorm_le prec 9 9 PI nP && inorm_le prec 9 9 RM nM && inorm_le prec 5 9 RQ nQ
  then Some (I.div prec nP (I.sub prec (I.fromZ prec 1) th0), nM, nQ) else None.

Definition le_dy (K : Z * Z) (X : I.type) : bool := nonneg (I.sub prec (Newton.dyad prec K) X).

(** [cell_ranges] with the bounds on |M^-1|, |M| and |Q| checked against
    BM, BMM and BQ. *)
Definition cell_ranges2 (sc hc a b : Z * Z) (kn p : nat) (W : list (list (Z * Z))) (WiI : imat) (BM BMM BQ : Z * Z)
    : option (list imat) :=
  obind (cell_core sc hc a b kn) (fun r =>
    let '(mrlo, th, N, B) := r in
    obind (t_Mb mrlo th B) (fun bs =>
      let '(bMi, bM, bQ) := bs in
      if le_dy BM bMi && le_dy BMM bM && le_dy BQ bQ then
        let NW := tmc prec d 14 14 14 (tcm prec d 14 14 14 (idmat prec 14 14 W) N) WiI in
        Some (map (fun q => tmrange prec d tab (sub_mrlo a b p q) 14 14 NW) (seq 0 (2 ^ p)))
      else None)).

(** The start rows [Pm(s + h, h), -h I] and the step I + h N. *)
Definition t_C (mrlo : list I.type) (th : tm) (B : blocks) : tmat :=
  ttab 5 14 (fun i c =>
    if Nat.ltb c 9 then tsub prec d (tget d (b_Rep B) i c) (tmul prec d tab mrlo th (tget d (b_Rdm' B) i c))
    else if Nat.eqb (c - 9) i then tneg d th else tz d).
Definition t_Psi (mrlo : list I.type) (th : tm) (N : tmat) : tmat :=
  ttab 14 14 (fun i c => tadd prec d (tget d (t_Id 14) i c) (tmul prec d tab mrlo th (tget d N i c))).

(** The range of the start rows times W0^-1 over the steps h in hc +- b, at
    s = 1/4. *)
Definition start_range (hc b : Z * Z) (kn : nat) (WiI : imat) : option imat :=
  obind (cell_core (1%Z, (-2)%Z) hc (0%Z, 0%Z) b kn) (fun r =>
    let '(mrlo, th, N, B) := r in
    Some (tmrange prec d tab mrlo 5 14
            (tmc prec d 5 14 14 (tmm prec d tab mrlo 5 14 14 (t_C mrlo th B) (t_Psi mrlo th N)) WiI))).

End Cell.

(** Conversion unfolds the wrappers before the tables and evaluations they
    call, so that checking a proof about a cell never evaluates a table. *)
Strategy expand [mrlo_of cell_mrlo blocks_of cell_blocks t_Pp t_Q t_M t_SVE t_Id t_P t_N cell_core cell_range
                 t_C t_Psi start_range iupmax rblk pblk sub_mrlo cell_ranges t_Mb le_dy cell_ranges2].
Strategy 1000 [ofull renvs penvs plist qlist].
