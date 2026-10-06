From Stdlib Require Import ZArith List Bool.
From Interval Require Import Interval.Interval.
From Stellarocq Require Import Expr Checker Newton IMat TMEval TMat LinCheck CellTM Frames Check3d BMat Final3d Ball3d
  ConsCheck.
Import ListNotations.
Definition prec53 : F.precision := F.PtoP 53.
Definition deg : nat := 3.
Definition tab3 : tmtab := mktab deg.
Definition cellr := cell_ranges prec53 deg tab3.
Definition startr := start_range prec53 deg tab3.
Definition winv := winv_encl prec53.
Definition asm := assemble3d prec53.
(** The three constants the assembly bounds, for the report. *)
Definition asm_th (frames : list frame) (es : list Z) (cells : list (list imat)) (rs : imat)
    (Rd : list (list (list (list (Z * Z))))) : I.type * I.type * I.type :=
  let RB := iR prec53 Rd in
  let M0 := iM0 prec53 frames es rs (gPs prec53 cells) in
  let rv := map (irho prec53 es rs (gdls prec53 cells) (gTs prec53 frames es)) (seq 0 182) in
  (th_of prec53 (iRM0 prec53 RB M0), ith1 prec53 RB rv, th_of prec53 (iM0R prec53 RB M0)).
(** Each conjunct of the assembly check, for the report. *)
Definition asm_diag (frames : list frame) (es : list Z) (cells : list (list imat)) (rs : imat)
    (Rd : list (list (list (list (Z * Z))))) : list bool :=
  let prec := prec53 in
  let RB := iR prec Rd in
  let M0 := iM0 prec frames es rs (gPs prec cells) in
  let dls := gdls prec cells in
  let Ts := gTs prec frames es in
  let rv := map (irho prec es rs dls Ts) (seq 0 182) in
  let rr := map (irho_raw prec es rs dls Ts) (seq 0 182) in
  let RM0 := iRM0 prec RB M0 in
  let M0R := iM0R prec RB M0 in
  let th0 := th_of prec RM0 in
  let th2 := th_of prec M0R in
  let th1 := ith1 prec RB rv in
  [forallb (fun k => match owi prec frames k with Some _ => true | None => false end) (seq 0 12);
   forallb (fun k => forallb (fun i => cell_ok prec (gcell cells k i)) (seq 0 4096)) (seq 0 12);
   forallb (fun k => delta_ok prec (gcell cells k) 4096) (seq 0 12);
   forallb (fun j => nonneg (I.sub prec (nth j rv I.zero) (nth j rr I.zero)) && nonneg (nth j rv I.zero)) (seq 0 182);
   bnorm_le prec 13 RM0 th0; bnorm_le prec 13 M0R th2;
   forallb (fun Ir => nonneg (I.sub prec th1 (irow1 prec RB rv (fst Ir) (snd Ir)))) rows;
   ipos (I.sub prec (I.fromZ prec 1) (I.add prec th0 th1)); ipos (I.sub prec (I.fromZ prec 1) th2);
   psi0_ok prec cells].
(** The ball and consistency checks of one point over one cell, the tails
    differentiated once for all calls. *)
Definition dts_r : list (list binding) := dtails true.
Definition dts_p : list (list binding) := dtails false.
Definition ballc (K rx rd hhi : Z * Z) (r : bool) (kp c : nat) : bool :=
  ball_cell_ok prec53 K rx rd hhi r (if r then dts_r else dts_p) kp c.
Definition consc (C hhi : Z * Z) (r : bool) (kp c : nat) : bool := cons_cell_ok prec53 C hhi r kp c.
(** The tables themselves, for the report. *)
Definition ballt (rx rd hhi : Z * Z) (r : bool) (kp c : nat) : option (list (list I.type)) :=
  ball_tab prec53 r (if r then dts_r else dts_p)
    (widen prec53 (jetbox prec53 (fst (pt r kp)) (snd (pt r kp)) (clo c) (chi c) hhi) rx rd).
Definition const (hhi : Z * Z) (r : bool) (kp c : nat) : option I.type :=
  cons_tab prec53 (fst (pt r kp)) (snd (pt r kp)) r (clo c) (chi c) hhi.
(** The cell stage with the bounds on |M^-1|, |M| and |Q| checked, and the
    bounds themselves over one cell, for choosing them. *)
Definition cellr2 := cell_ranges2 prec53 deg tab3.
Definition mbprobe (sc hc a b : Z * Z) (kn : nat) : option (I.type * I.type * I.type) :=
  obind (cell_core prec53 deg tab3 sc hc a b kn) (fun r => let '(mrlo, th, _, B) := r in t_Mb prec53 deg tab3 mrlo th B).
(** The consistency check of one point over one cell of s (radial) or t
    (poloidal) for h in [-hhi, hhi], and its bound on the second derivative,
    for choosing C. *)
Definition cons2c (C hhi : Z * Z) (r : bool) (kp c : nat) : bool := cons2_cell_ok prec53 C hhi r kp c.
Definition cons2t (hhi : Z * Z) (r : bool) (kp c : nat) : option I.type :=
  cons2_tab prec53 (fst (pt r kp)) (snd (pt r kp)) r (clo c) (chi c) hhi.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt ExtrOCamlInt63 ExtrOCamlFloats.
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".
Extract Constant ClassicalDedekindReals.sig_forall_dec => "(fun _ -> assert false)".
Extract Constant Rdefinitions.RbaseSymbolsImpl.R0 => "(Obj.magic (fun _ -> assert false))".
Extract Constant Rdefinitions.RbaseSymbolsImpl.R1 => "(Obj.magic (fun _ -> assert false))".
Extract Inductive FloatClass.float_class =>
  "Float64.float_class"
  [ "Float64.PNormal" "Float64.NNormal" "Float64.PSubn" "Float64.NSubn" "Float64.PZero"
    "Float64.NZero" "Float64.PInf" "Float64.NInf" "Float64.NaN" ].
Extract Inductive PrimFloat.float_comparison =>
  "Float64.float_comparison" [ "Float64.FEq" "Float64.FLt" "Float64.FGt" "Float64.FNotComparable" ].
Extraction Language OCaml.
Separate Extraction cellr startr winv asm asm_th asm_diag ballc consc ballt const cellr2 mbprobe cons2c cons2t.
