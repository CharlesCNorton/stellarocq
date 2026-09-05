(* Stellarocq certificate driver.

   Unverified shell around the extracted checker: parses a certificate file,
   expands its node tables into per-point environments (the layout fixed in
   theories/Physics.v), hands the result to Checker.check_cert or
   Cell.check_ccert, and reports. Everything that decides validity happens
   inside the extracted code.

   The points are split into shards checked by forked worker processes
   (STELLAROCQ_JOBS, default: the number of processors). The verdict is the
   conjunction of the shard verdicts, which is the theorem's own conjunction
   over points.

   "--tighten in out" writes the bounds of a cell certificate rather than
   checking them: for each cell it reads the enclosures the extracted code
   computes and emits the smallest claim that code accepts. The result is an
   ordinary certificate, checked by an ordinary run. *)

open BinNums

(* Binary positive from a positive int64. *)
let rec pos_of_int64 (n : int64) : positive =
  if Int64.equal n 1L then Coq_xH
  else
    let q = Int64.div n 2L and r = Int64.rem n 2L in
    if Int64.equal r 0L then Coq_xO (pos_of_int64 q)
    else Coq_xI (pos_of_int64 q)

(* Extracted integer from an int64. *)
(* the mantissa of a slot, as the extracted integers want it *)
let rec nth_list l k = match l, k with
  | x :: _, 0 -> Some x
  | _ :: tl, k -> nth_list tl (k - 1)
  | [], _ -> None

let nth_z (l : coq_Z list) (k : int) : coq_Z =
  match nth_list l k with Some z -> z | None -> Z0

let z_of_int64 (n : int64) : coq_Z =
  if Int64.equal n 0L then Z0
  else if Int64.compare n 0L > 0 then Zpos (pos_of_int64 n)
  else Zneg (pos_of_int64 (Int64.neg n))

(* Approximate float of an extracted integer. *)
let rec float_of_pos (p : positive) : float =
  match p with
  | Coq_xH -> 1.0
  | Coq_xO q -> 2.0 *. float_of_pos q
  | Coq_xI q -> 2.0 *. float_of_pos q +. 1.0

let float_of_z (z : coq_Z) : float =
  match z with
  | Z0 -> 0.0
  | Zpos p -> float_of_pos p
  | Zneg p -> -. (float_of_pos p)

(* ---- reading a bound back out of an enclosure ---------------------------- *)

(* Largest absolute value in an interval, as a float; infinity if unbounded. *)
let mag (i : Expr.I.coq_type) =
  match i with
  | Float.Inan -> infinity
  | Float.Ibnd (lo, hi) ->
      let a = Stdlib.abs_float lo and b = Stdlib.abs_float hi in
      if a >= b then a else b

(* Smallest absolute value in an interval; zero when it straddles zero, in
   which case no floor is provable. *)
let mag_min (i : Expr.I.coq_type) =
  match i with
  | Float.Inan -> 0.0
  | Float.Ibnd (lo, hi) ->
      if lo > 0.0 then lo else if hi < 0.0 then -. hi else 0.0

(* A dyadic m * 2^e at or just below x > 0, or zero. *)
let dyadic_le (x : float) =
  if x <> x || x <= 0.0 || x = infinity || x < 1.0e-280 then (0L, 0L)
  else
    let (f, e) = Stdlib.frexp x in
    let m = Int64.of_float (Stdlib.floor (f *. 9007199254740992.0)) in
    if Int64.compare m 8L < 0 then (0L, 0L)
    else (Int64.sub m 4L, Int64.of_int (e - 53))

(* A dyadic m * 2^e at or just above x > 0. *)
let dyadic_ge (x : float) =
  if x <> x || x = infinity then begin
    prerr_endline
      ("the enclosure over this cell is unbounded: the box is wide enough "
       ^ "for the Jacobian to straddle zero. Refine the cells (--nu, --nv).");
    exit 3
  end;
  (* 2^q underflows to zero below the smallest denormal, which would turn a
     claim into the false claim of an exact zero, so the exponent has a floor *)
  if x <= 0.0 || x < 1.0e-280 then (1L, -900L)
  else
    let (f, e) = Stdlib.frexp x in
    let m = Int64.of_float (Stdlib.ceil (f *. 9007199254740992.0)) in
    (Int64.add m 4L, Int64.of_int (e - 53))

(* ---- tokenizer ---------------------------------------------------------- *)

(* Whitespace-separated tokens of a file, in order. *)
let tokens_of_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  let toks = ref [] in
  let i = ref 0 in
  let n = String.length s in
  while !i < n do
    while !i < n && (s.[!i] = ' ' || s.[!i] = '\n' || s.[!i] = '\r' || s.[!i] = '\t') do incr i done;
    if !i < n then begin
      let j = ref !i in
      while !j < n && not (s.[!j] = ' ' || s.[!j] = '\n' || s.[!j] = '\r' || s.[!j] = '\t') do incr j done;
      toks := String.sub s !i (!j - !i) :: !toks;
      i := !j
    end
  done;
  Array.of_list (Stdlib.List.rev !toks)

(* ---- workers ------------------------------------------------------------ *)

(* Number of worker processes: STELLAROCQ_JOBS, else the processor count. *)
let jobs () =
  match Sys.getenv_opt "STELLAROCQ_JOBS" with
  | Some s -> (try max 1 (int_of_string s) with _ -> 1)
  | None ->
      (try
         let ic = Unix.open_process_in "nproc 2>/dev/null" in
         let line = input_line ic in
         ignore (Unix.close_process_in ic);
         max 1 (int_of_string (String.trim line))
       with _ -> 1)

(* Which conjunct of a cell check fails, for diagnosing a rejected
   certificate. Set STELLAROCQ_DEBUG to print it for the first cell. *)
let debug_cell xu xv (c : Cell.ccert) (cl : Cell.ccell) =
  let prec = Cell.cprec_of c in
  let ms = cl.Cell.cc_pt.Checker.pt_ms in
  let es = cl.Cell.cc_pt.Checker.pt_es in
  let base = Cell.n_inputs c in
  let r3 = Physics.residual es c.Cell.cc_cfg c.Cell.cc_modes in
  let binds = r3.Physics.r_binds in
  let len = Stdlib.List.length binds in
  Printf.printf "  slots: |ms|=%d base=%d |binds|=%d  slot_u=%d slot_v=%d\n%!"
    (Stdlib.List.length ms) base len xu xv;
  Printf.printf "  well_formed=%b\n%!" (Deriv.well_formed base binds);
  let box = Cell.box_ienv xu xv prec ms cl.Cell.cc_du cl.Cell.cc_dv in
  let at_centre = Expr.iextend prec (Checker.ienv_of prec ms) binds in
  let at_box slot =
    Expr.iextend prec box (Deriv.with_derivs slot base len binds) in
  let env_du = at_box xu in
  let env_dv = at_box xv in
  (* the same derivative read at the centre instead of over the box: the
     ratio is what a Taylor bound would save, since it would charge the box
     only for a second-order remainder *)
  let at_pt slot =
    Expr.iextend prec (Checker.ienv_of prec ms)
      (Deriv.with_derivs slot base len binds) in
  let pt_du = at_pt xu in
  let pt_dv = at_pt xv in
  (* the first scratch slot whose value, or whose derivative, comes out
     with no bound over the box: it names the binding that loses the
     enclosure, which is where a diverging cell has to be diagnosed *)
  let first_nan env off =
    let rec go k =
      if k >= len then None
      else if mag (Expr.ieval prec env (Expr.Evar (base + k + off))) = infinity
      then Some k else go (k + 1) in
    go 0 in
  (match first_nan env_du 0 with
   | None -> Printf.printf "  box values: all bounded
%!"
   | Some k -> Printf.printf "  box values: slot %d (binding %d) unbounded
%!"
                 (base + k) k);
  (match first_nan env_du len with
   | None -> Printf.printf "  box du derivatives: all bounded
%!"
   | Some k -> Printf.printf
                 "  box du derivatives: slot %d (derivative of binding %d) unbounded
%!"
                 (base + k + len) k);
  Stdlib.List.iter (fun (nm, r, cb) ->
      let ok =
        Cell.check_component prec base len cl.Cell.cc_du cl.Cell.cc_dv
          at_centre env_du env_dv r cb in
      (match Cell.slot_of r with
       | None -> Printf.printf "  component %s: not a slot reference\n%!" nm
       | Some n ->
           let centre = Checker.check1 prec at_centre r cb.Cell.cb_N0 cb.Cell.cb_q0 in
           let du_ok =
             Checker.check1 prec env_du
               (Expr.Evar (n + len)) cb.Cell.cb_NDu cb.Cell.cb_qDu in
           let dv_ok =
             Checker.check1 prec env_dv
               (Expr.Evar (n + len)) cb.Cell.cb_NDv cb.Cell.cb_qDv in
           let comb =
             Checker.nonneg
               (Expr.ieval prec Expr.eempty
                  (Cell.combination_e cl.Cell.cc_du cl.Cell.cc_dv cb)) in
           Printf.printf
             "  component %s: slot=%d centre=%b du=%b dv=%b comb=%b\n%!"
             nm n centre du_ok dv_ok comb;
           Printf.printf
             "  component %s: claim  centre=%.6e du=%.6e dv=%.6e comb=%.6e\n%!"
             nm
             (float_of_z cb.Cell.cb_N0 *. (2.0 ** float_of_z cb.Cell.cb_q0))
             (float_of_z cb.Cell.cb_NDu *. (2.0 ** float_of_z cb.Cell.cb_qDu))
             (float_of_z cb.Cell.cb_NDv *. (2.0 ** float_of_z cb.Cell.cb_qDv))
             (float_of_z cb.Cell.cb_Nc *. (2.0 ** float_of_z cb.Cell.cb_qc));
           Printf.printf
             "  component %s: needed centre=%.6e du=%.6e dv=%.6e\n%!"
             nm (mag (Expr.ieval prec at_centre r))
             (mag (Expr.ieval prec env_du (Expr.Evar (n + len))))
             (mag (Expr.ieval prec env_dv (Expr.Evar (n + len))));
           let bu = mag (Expr.ieval prec env_du (Expr.Evar (n + len)))
           and cu = mag (Expr.ieval prec pt_du (Expr.Evar (n + len)))
           and bv = mag (Expr.ieval prec env_dv (Expr.Evar (n + len)))
           and cv = mag (Expr.ieval prec pt_dv (Expr.Evar (n + len))) in
           Printf.printf
             "  component %s: centre du=%.4e dv=%.4e  box/centre %.2f %.2f\n%!"
             nm cu cv (bu /. cu) (bv /. cv));
      Printf.printf "  component %s: %b\n%!" nm ok)
    [ ("r_s", r3.Physics.r_s, cl.Cell.cc_s);
      ("r_u", r3.Physics.r_u, cl.Cell.cc_u);
      ("r_v", r3.Physics.r_v, cl.Cell.cc_v) ]

(* ---- what the cells of a node share ------------------------------------- *)

(* The residual expression tree and its derivative bindings depend on the
   exponents of the point, not on its mantissas, and every cell of a node
   carries the node's exponents: the angles are written on a fixed dyadic
   grid, so their exponent is the same for every cell. So all of this is
   built once per node instead of once per cell, which at the cell counts a
   continuum bound needs is most of the work.

   [nc_du] and [nc_dv] carry the first derivative along each varied slot,
   [nc_ddu] and [nc_ddv] the first and second, and each is built only when
   the caller asks for it. *)
type nodectx = {
  nc_r3 : Physics.residual3 ;
  nc_base : int ;
  nc_len : int ;
  (* the leading bindings that read neither varied slot, and how many they
     are. Which bindings those are is decided here with the extracted
     var_free rather than assumed from the order Physics.v happens to
     allocate in, so a reordering there can only make the run slower, never
     wrong. *)
  nc_pre : (int * Expr.expr) list ;
  nc_suf : (int * Expr.expr) list ;
  nc_du : (int * Expr.expr) list Lazy.t ;
  nc_dv : (int * Expr.expr) list Lazy.t ;
  nc_du_suf : (int * Expr.expr) list Lazy.t ;
  nc_dv_suf : (int * Expr.expr) list Lazy.t ;
  nc_ddu : (int * Expr.expr) list Lazy.t ;
  nc_ddv : (int * Expr.expr) list Lazy.t ;
}

let node_ctx xu xv (c : Cell.ccert) (cl : Cell.ccell) =
  let base = Cell.n_inputs c in
  let r3 =
    Physics.residual cl.Cell.cc_pt.Checker.pt_es c.Cell.cc_cfg c.Cell.cc_modes in
  let binds = r3.Physics.r_binds in
  let len = Stdlib.List.length binds in
  let rec split acc = function
    | (s, e) :: tl when Deriv.var_free xu e && Deriv.var_free xv e ->
        split ((s, e) :: acc) tl
    | rest -> (Stdlib.List.rev acc, rest) in
  (* STELLAROCQ_NOHOIST forces an empty prefix, so the same binary measures
     what sharing it is worth *)
  let (pre, suf) =
    if Sys.getenv_opt "STELLAROCQ_NOHOIST" <> None then ([], binds)
    else split [] binds in
  { nc_r3 = r3; nc_base = base; nc_len = len; nc_pre = pre; nc_suf = suf;
    nc_du = lazy (Deriv.with_derivs xu base len binds);
    nc_dv = lazy (Deriv.with_derivs xv base len binds);
    (* the derivative bindings of the suffix alone: the prefix reads neither
       varied slot, so its derivatives are zero and its slots are already in
       the shared environment *)
    nc_du_suf = lazy (Deriv.with_derivs xu base len suf);
    nc_dv_suf = lazy (Deriv.with_derivs xv base len suf);
    nc_ddu = lazy (Deriv.with_derivs2 xu base len binds);
    nc_ddv = lazy (Deriv.with_derivs2 xv base len binds) }

(* The context of the node cell k belongs to, rebuilt only when the node
   changes. Cells are ordered node by node, so one slot suffices. *)
let node_cache = ref (-1, None)

(* The environments after the shared prefix, per node and per derivative
   level. A suffix binding's derivative reads the derivative slots of the
   prefix bindings it mentions, so sharing only the values would leave those
   slots unset and the enclosure unbounded; each level carries its own.

   The base these are built on has the varied slots at whatever cell came
   first. The prefix reads neither, and every use overwrites both before
   extending by the suffix, so that value is never read. *)
type prectx = {
  pe_val : Expr.I.coq_type Expr.env ;
  pe_du : Expr.I.coq_type Expr.env ;
  pe_dv : Expr.I.coq_type Expr.env ;
}

let pre_cache = ref (-1, None)

let pre_env_for xu xv prec node ctx base =
  match !pre_cache with
  | (nd, Some p) when nd = node -> p
  | _ ->
      let base_ = ctx.nc_base and len = ctx.nc_len in
      let p =
        { pe_val = Expr.iextend prec base ctx.nc_pre ;
          pe_du = Expr.iextend prec base
                    (Deriv.with_derivs xu base_ len ctx.nc_pre) ;
          pe_dv = Expr.iextend prec base
                    (Deriv.with_derivs xv base_ len ctx.nc_pre) } in
      pre_cache := (node, Some p);
      p

let ctx_for xu xv nangles k (c : Cell.ccert) (cl : Cell.ccell) =
  match !node_cache with
  | (node, Some ctx) when node = k / nangles -> ctx
  | _ ->
      let ctx = node_ctx xu xv c cl in
      node_cache := (k / nangles, Some ctx);
      ctx

(* A mantissa below 2^53, so that a claim is exactly representable. *)
let renorm (m, q) =
  let rec go m q =
    if Int64.compare m 9007199254740992L >= 0
    then go (Int64.div m 2L) (Int64.add q 1L) else (m, q) in
  go m q

(* The smallest bound of the form m * 2^q the checker accepts for e: the
   magnitude of its enclosure, grown until the check passes. The claim is
   itself built in interval arithmetic, so the magnitude alone can fall an
   ulp short, and the check settles it. *)
let bound_for prec env e =
  let (m0, q0) = dyadic_ge (mag (Expr.ieval prec env e)) in
  let rec go m q k =
    if k > 200 then (prerr_endline "no bound accepted for a component"; exit 2)
    else if Checker.check1 prec env e (z_of_int64 m) (z_of_int64 q) then (m, q)
    else
      let (m, q) = renorm (Int64.add m (Int64.add 1L (Int64.div m 4096L)), q) in
      go m q (k + 1) in
  let (m0, q0) = renorm (m0, q0) in
  go m0 q0 0

(* The largest floor of the form m * 2^q the checker accepts for e: the
   smallest magnitude of its enclosure, shrunk until the reversed check
   passes. Zero when the enclosure straddles zero, which is the honest
   answer: nothing is provable there. *)
let floor_for prec env e =
  let (m0, q0) = dyadic_le (mag_min (Expr.ieval prec env e)) in
  if Int64.compare m0 1L < 0 then (0L, 0L)
  else
    let rec go m q k =
      if k > 200 || Int64.compare m 1L < 0 then (0L, 0L)
      else if Checker.check1_lower prec env e (z_of_int64 m) (z_of_int64 q)
      then (m, q)
      else go (Int64.sub m (Int64.add 1L (Int64.div m 4096L))) q (k + 1) in
    go m0 q0 0

(* The three bound lines of one cell, set to the enclosures the checker
   computes for it: the centre value, and the two angular derivatives over the
   whole box. A generator cannot predict these, because the width of an
   interval enclosure of a cancelling expression is a property of the
   arithmetic and not of the function, so the bounds are read back from the
   extracted code and then verified by an ordinary run over the result. *)
let tighten_cell ?slot3 xu xv node ctx (c : Cell.ccert) (cl : Cell.ccell)
    (du_i : int64) (dv_i : int64) =
  let prec = Cell.cprec_of c in
  let ms = cl.Cell.cc_pt.Checker.pt_ms in
  let r3 = ctx.nc_r3 in
  let len = ctx.nc_len in
  (* The shared prefix, evaluated once for the node. Both varied slots are
     written afterwards, so whichever cell's values it was built over are
     overwritten before anything reads them. *)
  let pre = pre_env_for xu xv prec node ctx (Checker.ienv_of prec ms) in
  let at_pt e = Expr.eset xu (Expr.eset xv e
                                (Expr.I.fromZ prec (nth_z ms xv)))
                  (Expr.I.fromZ prec (nth_z ms xu)) in
  let at_box e =
    Expr.eset xu
      (Expr.eset xv e (Cell.slot_box prec (nth_z ms xv) cl.Cell.cc_dv))
      (Cell.slot_box prec (nth_z ms xu) cl.Cell.cc_du) in
  (* The three environments do not depend on the component, so they are built
     once for the cell rather than once per component. *)
  let env0 = Expr.iextend prec (at_pt pre.pe_val) ctx.nc_suf in
  let env_du =
    Expr.iextend prec (at_box pre.pe_du) (Lazy.force ctx.nc_du_suf) in
  (* a cell with no toroidal width needs no bound on the toroidal derivative,
     and Cell.check_component_flat does not ask for one, so neither the
     environment nor the search that reads it is built *)
  let flat = Int64.compare dv_i 0L = 0 in
  let env_dv =
    lazy (Expr.iextend prec (at_box pre.pe_dv) (Lazy.force ctx.nc_dv_suf)) in
  (* With a third slot the derivative along it is enclosed over a box wide in
     all three, and the cell bound has to carry that step as well. *)
  let env_dw =
    lazy (match slot3 with
          | None -> Expr.eempty
          | Some (xw, _) ->
              let box3 =
                Cell.box_ienv3 xu xv xw prec ms cl.Cell.cc_du cl.Cell.cc_dv
                  (z_of_int64 (match slot3 with Some (_, d) -> d | None -> 0L)) in
              Expr.iextend prec box3
                (Deriv.with_derivs xw ctx.nc_base ctx.nc_len
                   ctx.nc_r3.Physics.r_binds)) in
  let line r =
    match Cell.slot_of r with
    | None -> prerr_endline "residual component is not a slot reference"; exit 2
    | Some n ->
        let (n0, q0) = bound_for prec env0 r in
        let (ndu, qdu) = bound_for prec env_du (Expr.Evar (n + len)) in
        let (ndv, qdv) =
          if flat then (1L, 0L)
          else bound_for prec (Lazy.force env_dv) (Expr.Evar (n + len)) in
        let f m e = Int64.to_float m *. (2.0 ** Int64.to_float e) in
        let cb nc qc =
          { Cell.cb_N0 = z_of_int64 n0; Cell.cb_q0 = z_of_int64 q0;
            Cell.cb_NDu = z_of_int64 ndu; Cell.cb_qDu = z_of_int64 qdu;
            Cell.cb_NDv = z_of_int64 ndv; Cell.cb_qDv = z_of_int64 qdv;
            Cell.cb_Nc = z_of_int64 nc; Cell.cb_qc = z_of_int64 qc } in
        let (ndw, qdw) =
          match slot3 with
          | None -> (1L, 0L)
          | Some _ ->
              bound_for prec (Lazy.force env_dw) (Expr.Evar (n + len)) in
        let dw_i = match slot3 with None -> 0L | Some (_, d) -> d in
        let total =
          f n0 q0
          +. Int64.to_float du_i *. f ndu qdu
          +. Int64.to_float dv_i *. f ndv qdv
          +. Int64.to_float dw_i *. f ndw qdw in
        (* the combination the checker will evaluate, with the third step when
           there is one *)
        let accepts nc qc =
          match slot3 with
          | None ->
              Checker.nonneg
                (Expr.ieval prec Expr.eempty
                   (Cell.combination_e cl.Cell.cc_du cl.Cell.cc_dv
                      (cb nc qc)))
          | Some _ ->
              let eps a b = Checker.eps_e a b in
              let e_c = eps (z_of_int64 nc) (z_of_int64 qc) in
              let e_0 = eps (z_of_int64 n0) (z_of_int64 q0) in
              let e_du = eps (z_of_int64 ndu) (z_of_int64 qdu) in
              let e_dv = eps (z_of_int64 ndv) (z_of_int64 qdv) in
              let e_dw = eps (z_of_int64 ndw) (z_of_int64 qdw) in
              let step d e = Expr.Emul (Expr.EfromZ d, e) in
              let tail =
                Expr.Eadd (step cl.Cell.cc_dv e_dv,
                           step (z_of_int64 dw_i) e_dw) in
              let sum =
                Expr.Eadd (e_0, Expr.Eadd (step cl.Cell.cc_du e_du, tail)) in
              Checker.nonneg
                (Expr.ieval prec Expr.eempty (Expr.Esub (e_c, sum))) in
        let rec grow (nc, qc) k =
          if k > 200 then (prerr_endline "no cell bound accepted"; exit 2)
          else if accepts nc qc then (nc, qc)
          else grow (renorm (Int64.add nc (Int64.add 1L (Int64.div nc 4096L)), qc))
                 (k + 1) in
        let (nc, qc) = grow (renorm (dyadic_ge total)) 0 in
        ((match slot3 with
          | None ->
              Printf.sprintf "%Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld"
                n0 q0 ndu qdu ndv qdv nc qc
          | Some _ ->
              Printf.sprintf "%Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld"
                n0 q0 ndu qdu ndv qdv nc qc ndw qdw),
         f nc qc) in
  [ line r3.Physics.r_s; line r3.Physics.r_u; line r3.Physics.r_v ]

(* The same three lines for a floor rather than a ceiling: the centre value
   read from below, the two angular derivatives from above, and the cell
   floor f0 - du Du - dv Dv shrunk until the reversed combination accepts. A
   component whose enclosure straddles zero at the centre, or whose
   derivative step eats the whole floor, gets zeros, which the check then
   rejects. *)
let tighten_cell_lower xu xv _node ctx (c : Cell.ccert) (cl : Cell.ccell)
    (du_i : int64) (dv_i : int64) =
  let prec = Cell.cprec_of c in
  let ms = cl.Cell.cc_pt.Checker.pt_ms in
  let r3 = ctx.nc_r3 in
  let binds = r3.Physics.r_binds in
  let len = ctx.nc_len in
  let box = Cell.box_ienv xu xv prec ms cl.Cell.cc_du cl.Cell.cc_dv in
  let env0 = Expr.iextend prec (Checker.ienv_of prec ms) binds in
  let env_du = Expr.iextend prec box (Lazy.force ctx.nc_du) in
  let env_dv = Expr.iextend prec box (Lazy.force ctx.nc_dv) in
  let zero_line = "0 0 1 0 1 0 0 0" in
  let line r =
    match Cell.slot_of r with
    | None -> (zero_line, 0.0)
    | Some n ->
        let (n0, q0) = floor_for prec env0 r in
        if Int64.compare n0 1L < 0 then (zero_line, 0.0)
        else
          let (ndu, qdu) = bound_for prec env_du (Expr.Evar (n + len)) in
          let (ndv, qdv) = bound_for prec env_dv (Expr.Evar (n + len)) in
          let f m e = Int64.to_float m *. (2.0 ** Int64.to_float e) in
          let slack =
            f n0 q0
            -. Int64.to_float du_i *. f ndu qdu
            -. Int64.to_float dv_i *. f ndv qdv in
          if slack <= 0.0 then (zero_line, 0.0)
          else
            let cb nc qc =
              { Cell.cb_N0 = z_of_int64 n0; Cell.cb_q0 = z_of_int64 q0;
                Cell.cb_NDu = z_of_int64 ndu; Cell.cb_qDu = z_of_int64 qdu;
                Cell.cb_NDv = z_of_int64 ndv; Cell.cb_qDv = z_of_int64 qdv;
                Cell.cb_Nc = z_of_int64 nc; Cell.cb_qc = z_of_int64 qc } in
            let rec shrink (nc, qc) k =
              if k > 200 || Int64.compare nc 1L < 0 then (0L, 0L)
              else if Checker.nonneg
                        (Expr.ieval prec Expr.eempty
                           (Cell.combination_lower_e cl.Cell.cc_du
                              cl.Cell.cc_dv (cb nc qc)))
              then (nc, qc)
              else
                shrink (Int64.sub nc (Int64.add 1L (Int64.div nc 4096L)), qc)
                  (k + 1) in
            let (nc, qc) = shrink (dyadic_le slack) 0 in
            if Int64.compare nc 1L < 0 then (zero_line, 0.0)
            else
              (Printf.sprintf "%Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld"
                 n0 q0 ndu qdu ndv qdv nc qc, f nc qc) in
  [ line r3.Physics.r_s; line r3.Physics.r_u; line r3.Physics.r_v ]

(* The three ten-number bound lines of one cell, charged the Taylor way: the
   first varied slot against its derivative at the centre, a thin evaluation,
   with the box paying only for a second derivative against the square of the
   half-width. The second slot keeps the mean-value step. This is the same
   computation the "--taylor" verdict does, written to a file so that another
   party re-checks it with Cell.check_ccert_t rather than trusting this run. *)
let tighten_cell_taylor xu xv _node ctx (c : Cell.ccert) (cl : Cell.ccell)
    (du_i : int64) (dv_i : int64) =
  let prec = Cell.cprec_of c in
  let ms = cl.Cell.cc_pt.Checker.pt_ms in
  let r3 = ctx.nc_r3 in
  let binds = r3.Physics.r_binds in
  let len = ctx.nc_len in
  let base = ctx.nc_base in
  let box = Cell.box_ienv xu xv prec ms cl.Cell.cc_du cl.Cell.cc_dv in
  let d2 = Deriv.with_derivs2 xu base len binds in
  let env0 = Expr.iextend prec (Checker.ienv_of prec ms) binds in
  let envd = Expr.iextend prec (Checker.ienv_of prec ms) d2 in
  let envb = Expr.iextend prec box d2 in
  let envv = Expr.iextend prec box (Deriv.with_derivs xv base len binds) in
  let f m e = Int64.to_float m *. (2.0 ** Int64.to_float e) in
  let line r =
    match Cell.slot_of r with
    | None -> prerr_endline "residual component is not a slot reference"; exit 2
    | Some n ->
        let (n0, q0) = bound_for prec env0 r in
        let (nu, qu) = bound_for prec envd (Expr.Evar (n + len)) in
        let (nuu, quu) = bound_for prec envb (Expr.Evar (n + 2 * len)) in
        let (nv, qv) = bound_for prec envv (Expr.Evar (n + len)) in
        let total =
          f n0 q0
          +. Int64.to_float du_i *. f nu qu
          +. Int64.to_float du_i *. Int64.to_float du_i *. f nuu quu
          +. Int64.to_float dv_i *. f nv qv in
        let at nc qc =
          { Cell.tb_N0 = z_of_int64 n0; Cell.tb_q0 = z_of_int64 q0;
            Cell.tb_Nu = z_of_int64 nu; Cell.tb_qu = z_of_int64 qu;
            Cell.tb_Nuu = z_of_int64 nuu; Cell.tb_quu = z_of_int64 quu;
            Cell.tb_Nv = z_of_int64 nv; Cell.tb_qv = z_of_int64 qv;
            Cell.tb_Nc = z_of_int64 nc; Cell.tb_qc = z_of_int64 qc } in
        let rec grow (nc, qc) k =
          if k > 200 then (prerr_endline "no Taylor cell bound accepted"; exit 2)
          else if Checker.nonneg
                    (Expr.ieval prec Expr.eempty
                       (Cell.combination_t cl.Cell.cc_du cl.Cell.cc_dv
                          (at nc qc)))
          then (nc, qc)
          else grow (renorm (Int64.add nc (Int64.add 1L (Int64.div nc 4096L)),
                             qc)) (k + 1) in
        let (nc, qc) = grow (renorm (dyadic_ge total)) 0 in
        (Printf.sprintf "%Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld %Ld"
           n0 q0 nu qu nuu quu nv qv nc qc, f nc qc) in
  [ line r3.Physics.r_s; line r3.Physics.r_u; line r3.Physics.r_v ]

(* Copy a certificate, replacing the bound lines of every cell. The file is
   line oriented inside a CELLS block: a count, then three lines per cell. *)
let rewrite_bounds src dst (lines : string array) =
  let ic = open_in src in
  let all = ref [] in
  (try while true do all := input_line ic :: !all done with End_of_file -> ());
  close_in ic;
  let all = Array.of_list (Stdlib.List.rev !all) in
  let oc = open_out dst in
  let next = ref 0 in
  let i = ref 0 in
  while !i < Array.length all do
    let l = all.(!i) in
    output_string oc (l ^ "\n");
    incr i;
    if String.length l >= 5 && String.sub l 0 5 = "CELLS" then begin
      let k = int_of_string (String.trim (String.sub l 5 (String.length l - 5))) in
      for _ = 1 to 3 * k do
        if !next >= Array.length lines then
          (prerr_endline "more bound lines in the file than cells"; exit 2);
        output_string oc (lines.(!next) ^ "\n");
        incr next;
        incr i
      done
    end
  done;
  close_out oc;
  if !next <> Array.length lines then
    (prerr_endline "fewer bound lines in the file than cells"; exit 2)

(* Copy a certificate keeping only the cells whose floor came out nonzero.
   A cell whose residual passes through zero carries no floor, and a run over
   the unfiltered file reports a count rather than a verdict; over the
   filtered one every cell carries a claim, so an ordinary "--lower" run
   returns VALID and Cell.check_ccert_lower_correct applies to exactly the
   cells the file lists. The angle list is shared by every node, so this only
   makes sense for a single-node file. *)
let rewrite_filtered src dst (lines : string array) (keep : bool array) =
  let ic = open_in src in
  let all = ref [] in
  (try while true do all := input_line ic :: !all done with End_of_file -> ());
  close_in ic;
  let all = Array.of_list (Stdlib.List.rev !all) in
  let kept = Array.fold_left (fun a b -> if b then a + 1 else a) 0 keep in
  let oc = open_out dst in
  let i = ref 0 in
  let starts p l = String.length l >= String.length p
                   && String.sub l 0 (String.length p) = p in
  let count p l =
    int_of_string
      (String.trim (String.sub l (String.length p)
                      (String.length l - String.length p))) in
  while !i < Array.length all do
    let l = all.(!i) in
    if starts "NANGLES " l then begin
      let n = count "NANGLES " l in
      if n <> Array.length keep then
        (prerr_endline "the angle count differs from the cell count"; exit 2);
      output_string oc (Printf.sprintf "NANGLES %d\n" kept);
      incr i;
      for k = 0 to n - 1 do
        if keep.(k) then output_string oc (all.(!i) ^ "\n");
        incr i
      done
    end else if starts "CELLS " l then begin
      let n = count "CELLS " l in
      output_string oc (Printf.sprintf "CELLS %d\n" kept);
      incr i;
      for k = 0 to n - 1 do
        if keep.(k) then
          for j = 0 to 2 do output_string oc (lines.(3 * k + j) ^ "\n") done;
        i := !i + 3
      done
    end else begin
      output_string oc (l ^ "\n"); incr i
    end
  done;
  close_out oc

(* The integral of each component over the angles the cells cover, node by
   node, from the per-cell midpoint rules.

   With the toroidal half-width zero the cells tile a curve and the rule is
   the one-dimensional one: Quad.midpoint_sharp per cell, Quad.tiling_encloses
   for the sum, so the total lies within 2 sum(M2) h^3 of 2 h sum(v), with v
   the value at the centre of each cell and M2 a bound on the second angular
   derivative over it.

   With both half-widths positive the cells tile a patch of the surface and
   the rule is the iterated one: Quad.cell_iterated_encloses per cell,
   Quad.tiling2_encloses for the sum, so the total lies within
   4 sum(Muu hu^3 hv + Mvv hu hv^3) of 4 hu hv sum(v). The two directions are
   separated before either is estimated, so the cost is one more derivative
   environment per cell and no mixed partial.

   Value and error are both accumulated in the verified interval arithmetic,
   so the rounding of the sums is enclosed rather than ignored. Work is in
   mantissa units of the angle slots, and the result is scaled to radians at
   the end. Cells are split over forked shards whose partial sums round-trip
   through seventeen significant digits, which is exact for a double. *)

let ival (x : float) : Expr.I.coq_type = Float.Ibnd (x, x)
let ilo (i : Expr.I.coq_type) =
  match i with Float.Inan -> neg_infinity | Float.Ibnd (a, _) -> a
let ihi (i : Expr.I.coq_type) =
  match i with Float.Inan -> infinity | Float.Ibnd (_, b) -> b

let integrate_cells prec
    (cell_of : int -> Cell.ccert * Cell.ccell * int64 * int64)
    (xu : int) (xv : int) (nnodes : int) (nangles : int) (nplanes : int)
    (eu : float) (ev : float) (jobs : int) (tmp : string)
    (labels : string list) =
  let ncells = nnodes * nangles in
  let two = Expr.I.fromZ prec (z_of_int64 2L) in
  let four = Expr.I.fromZ prec (z_of_int64 4L) in
  (* A cell with toroidal width covers a patch of the surface, so every cell
     of a node belongs to the same integral; one with none covers a curve at
     a fixed toroidal plane, and the planes stay apart. *)
  let two_d = let (_, _, _, dv0) = cell_of 0 in Int64.compare dv0 0L > 0 in
  let np = if two_d then 1 else nplanes in
  let width = 3 * nnodes * np in
  (* Each cell's contribution is kept and handed to Cell.isum, which is the
     summation theories/Cell.v proves encloses the sum of whatever the terms
     enclose. The loop used to add them itself and correspond to Quad.rsum by
     inspection; now the correspondence is a call. *)
  let shard lo hi =
    let av = Array.make width [] in
    let ae = Array.make width [] in
    for k = lo to hi - 1 do
      let group =
        (k / nangles) * np
        + (if two_d then 0 else (k mod nangles) mod np) in
      let (c, cl, du, dv) = cell_of k in
      let ctx = ctx_for xu xv nangles k c cl in
      let ms = cl.Cell.cc_pt.Checker.pt_ms in
      let r3 = ctx.nc_r3 in
      let binds = r3.Physics.r_binds in
      let len = ctx.nc_len in
      let box = Cell.box_ienv xu xv prec ms cl.Cell.cc_du cl.Cell.cc_dv in
      let env0 = Expr.iextend prec (Checker.ienv_of prec ms) binds in
      let env_ddu = Expr.iextend prec box (Lazy.force ctx.nc_ddu) in
      let env_ddv =
        if two_d then Expr.iextend prec box (Lazy.force ctx.nc_ddv)
        else Expr.eempty in
      let hu = ival (Int64.to_float du) in
      let hv = ival (Int64.to_float dv) in
      let hu3 = Expr.I.mul prec hu (Expr.I.mul prec hu hu) in
      let hv3 = Expr.I.mul prec hv (Expr.I.mul prec hv hv) in
      let mul3 a b c = Expr.I.mul prec a (Expr.I.mul prec b c) in
      Stdlib.List.iteri (fun i r ->
          match Cell.slot_of r with
          | None -> ()
          | Some n ->
              let j = 3 * group + i in
              (* An enclosure that runs to infinity carries no bound, and
                 accumulating it would poison the whole sum, so it stops the
                 run where it happens rather than at the report. *)
              let need name x =
                if x <> x || Stdlib.abs_float x = infinity then begin
                  Printf.eprintf
                    "cell %d, component %d: the %s enclosure over the box is \
                     unbounded, so no quadrature error follows. Refine the \
                     cells (--nu, --nv).\n%!" k i name;
                  exit 3
                end;
                x in
              let v = Expr.ieval prec env0 r in
              ignore (need "value" (ilo v)); ignore (need "value" (ihi v));
              let m2u =
                ival (need "second u derivative"
                        (mag (Expr.ieval prec env_ddu (Expr.Evar (n + 2 * len))))) in
              if two_d then begin
                let m2v =
                  ival (need "second v derivative"
                          (mag (Expr.ieval prec env_ddv (Expr.Evar (n + 2 * len))))) in
                av.(j) <-
                  mul3 four (Expr.I.mul prec hu hv) v :: av.(j);
                ae.(j) <-
                  Expr.I.add prec
                    (mul3 four m2u (Expr.I.mul prec hu3 hv))
                    (mul3 four m2v (Expr.I.mul prec hu hv3)) :: ae.(j)
              end else begin
                av.(j) <-
                  Expr.I.mul prec (Expr.I.mul prec two hu) v :: av.(j);
                ae.(j) <-
                  Expr.I.mul prec (Expr.I.mul prec two m2u) hu3 :: ae.(j)
              end)
        [ r3.Physics.r_s; r3.Physics.r_u; r3.Physics.r_v ]
    done;
    let sv = Array.map (fun l -> Cell.isum prec l) av in
    let se = Array.map (fun l -> Cell.isum prec l) ae in
    (sv, se) in
  let n = max 1 (min jobs (max 1 ncells)) in
  let sv = Array.make width Expr.I.zero in
  let se = Array.make width Expr.I.zero in
  if n = 1 then begin
    let (a, b) = shard 0 ncells in
    Array.blit a 0 sv 0 width; Array.blit b 0 se 0 width
  end else begin
    let part i = Printf.sprintf "%s.int%d" tmp i in
    let pids =
      Stdlib.List.init n (fun i ->
          match Unix.fork () with
          | 0 ->
              let lo = i * ncells / n and hi = (i + 1) * ncells / n in
              let (a, b) = shard lo hi in
              let oc = open_out (part i) in
              for j = 0 to width - 1 do
                (* hexadecimal floats round-trip exactly *)
                Printf.fprintf oc "%h %h %h %h\n"
                  (ilo a.(j)) (ihi a.(j)) (ilo b.(j)) (ihi b.(j))
              done;
              close_out oc; exit 0
          | pid -> pid) in
    Stdlib.List.iter (fun pid ->
        match snd (Unix.waitpid [] pid) with
        | Unix.WEXITED 0 -> ()
        | _ -> prerr_endline "an integration shard failed"; exit 3) pids;
    for i = 0 to n - 1 do
      let ic = open_in (part i) in
      for j = 0 to width - 1 do
        Scanf.sscanf (input_line ic) "%h %h %h %h"
          (fun a b c d ->
             sv.(j) <- Expr.I.add prec sv.(j) (Float.Ibnd (a, b));
             se.(j) <- Expr.I.add prec se.(j) (Float.Ibnd (c, d)))
      done;
      close_in ic; Sys.remove (part i)
    done
  end;
  let scale = if two_d then 2.0 ** (eu +. ev) else 2.0 ** eu in
  let unit = if two_d then "rad^2" else "rad" in
  for node = 0 to nnodes - 1 do
    for plane = 0 to np - 1 do
      if np = 1 then Printf.printf "  node %d:\n%!" node
      else Printf.printf "  node %d, plane %d:\n%!" node plane;
      Stdlib.List.iteri (fun i nm ->
          let j = 3 * (node * np + plane) + i in
          let e = ihi se.(j) in
          let lo = (ilo sv.(j) -. e) *. scale
          and hi = (ihi sv.(j) +. e) *. scale in
          Printf.printf
            "    %-12s [%.9e, %.9e] %s, quadrature error at most %.3e\n%!"
            nm lo hi unit (e *. scale);
          (* the same endpoints in hexadecimal, which round-trips exactly,
             so what a later stage reads is what this run established *)
          Printf.printf "    %-12s exact  %h %h\n%!" nm lo hi)
        labels
    done
  done

(* ---- the Mercier criterion ---------------------------------------------- *)

(* The criterion is assembled by theories/Mercier.v, in the same interval
   arithmetic as everything else, from ten enclosures a covering produces.
   This reads them and prints what the extracted code computes; the rational
   arithmetic that used to do this in Python is gone, and with it the question
   of whether it agreed with the checker.

   The input file is ten tagged lines of four integers, the dyadic endpoints
   of each enclosure, in the slot order theories/Mercier.v fixes. *)
let merc_tags =
  [| "TPP"; "TBB"; "TJB"; "TJJ"; "VPP"; "PP"; "IOTAP"; "IPINT"; "PHIP";
     "SIGNGS" |]

let read_mercier path =
  let t = tokens_of_file path in
  let p = ref 0 in
  let tok () = let x = t.(!p) in incr p; x in
  let expect w =
    let x = tok () in
    if x <> w then (Printf.eprintf "expected %s, got %s\n" w x; exit 2) in
  let i64 () = Int64.of_string (tok ()) in
  expect "STELLAROCQ-MERC"; expect "1";
  expect "PREC"; let prec = i64 () in
  let boxes =
    Array.map (fun tag ->
        expect tag;
        let mlo = i64 () in let elo = i64 () in
        let mhi = i64 () in let ehi = i64 () in
        { Mercier.mb_mlo = z_of_int64 mlo; Mercier.mb_elo = z_of_int64 elo;
          Mercier.mb_mhi = z_of_int64 mhi; Mercier.mb_ehi = z_of_int64 ehi })
      merc_tags in
  (prec, Array.to_list boxes)

let run_mercier path =
  let (prec, boxes) = read_mercier path in
  (* the precision is built the way a certificate's is *)
  let cfg0 = { Physics.pc_lasym = false; Physics.pc_prof = Physics.PPower;
               Physics.pc_out = Physics.RResidual } in
  let p = Cell.cprec_of
            { Cell.cc_prec = z_of_int64 prec; Cell.cc_cfg = cfg0;
              Cell.cc_modes = []; Cell.cc_cells = [] } in
  Printf.printf
    "assembling the Mercier criterion from ten enclosures, precision %Ld bits\n%!"
    prec;
  let show name e =
    let i = Mercier.merc_i p boxes e in
    Printf.printf "  %-7s [%+.6e, %+.6e]\n%!" name (ilo i) (ihi i);
    i in
  ignore (show "DShear" Mercier.e_dshear);
  ignore (show "DCurr" Mercier.e_dcurr);
  ignore (show "DWell" Mercier.e_dwell);
  let dg = show "DGeod" Mercier.e_dgeod in
  let ds = show "DStable" Mercier.e_dstable in
  let dm = show "DMerc" Mercier.e_dmerc in
  Printf.printf
    "  DGeod is at most 0 by mercier_geodesic_nonpositive, whatever its \
     enclosure says\n%!";
  ignore dg;
  (* the largest margin the checker accepts on the three terms an enclosure
     decides, which with the sign of DGeod is a margin on the criterion *)
  let margin = -. (ihi ds) in
  if margin > 0.0 then begin
    let rec shrink (m, q) k =
      if k > 200 || Int64.compare m 1L < 0 then None
      else if Mercier.check_unstable p boxes (z_of_int64 m) (z_of_int64 q)
      then Some (m, q)
      else shrink (Int64.sub m (Int64.add 1L (Int64.div m 4096L)), q) (k + 1) in
    match shrink (dyadic_le margin) 0 with
    | Some (m, q) ->
        let v = Int64.to_float m *. (2.0 ** Int64.to_float q) in
        Printf.printf
          "verdict: UNSTABLE   DMerc <= %.6e on this surface\n%!" (-. v)
    | None ->
        Printf.printf "verdict: OPEN   no margin was accepted\n%!"
  end else if ilo dm > 0.0 then begin
    let rec shrink (m, q) k =
      if k > 200 || Int64.compare m 1L < 0 then None
      else if Mercier.check_stable p boxes (z_of_int64 m) (z_of_int64 q)
      then Some (m, q)
      else shrink (Int64.sub m (Int64.add 1L (Int64.div m 4096L)), q) (k + 1) in
    match shrink (dyadic_le (ilo dm)) 0 with
    | Some (m, q) ->
        let v = Int64.to_float m *. (2.0 ** Int64.to_float q) in
        Printf.printf
          "verdict: STABLE   DMerc >= %.6e on this surface\n%!" v
    | None -> Printf.printf "verdict: OPEN   no margin was accepted\n%!"
  end else
    Printf.printf
      "verdict: OPEN   the enclosure of DMerc straddles zero\n%!"

(* ---- certificate parsing ------------------------------------------------ *)

(* A dyadic rational m * 2^e. *)
type dy = { m : int64 ; e : int64 }

(* Parse the certificate, expand nodes into points, run the checker. *)
let () =
  (* "--lower" reverses the test: instead of proving every component small,
     prove some component at least the claimed size, which says the field is
     not in force balance there by that margin. It combines with --tighten,
     which then reads floors back instead of ceilings. *)
  let args = Stdlib.List.tl (Array.to_list Sys.argv) in
  let has f = Stdlib.List.mem f args in
  let tighten = has "--tighten" in
  let lower = has "--lower" in
  let integrate = has "--integrate" in
  (* "--filter" keeps only the cells a floor run certifies, so that an
     ordinary run over the result carries a verdict rather than a count *)
  let filter = has "--filter" in
  (* "--verify" runs the check over the file just written, in one command.
     The check is a fresh process that re-reads that file and knows nothing of
     the run that produced it, so the separation the design rests on is
     intact: the tightening chooses the numbers and an independent run
     establishes them. *)
  let verify = has "--verify" in
  (* "--taylor" recomputes each cell bound with the first slot charged against
     its derivative at the centre rather than over the box, and establishes the
     result with Cell.check_ccert_t. The centre derivative is a thin
     evaluation; the box pays only for a second derivative against the square
     of the half-width. *)
  let taylor = has "--taylor" in
  (* "--mercier FILE" assembles the criterion from the enclosures a covering
     produced, inside the extracted code. *)
  (if has "--mercier" then begin
     let rec find = function
       | "--mercier" :: f :: _ -> f
       | _ :: tl -> find tl
       | [] -> prerr_endline "--mercier needs a file"; exit 2 in
     run_mercier (find args);
     exit 0
   end);
  (* "--slot3 W DW" widens a tightened cell certificate to a third coordinate.
     For each cell the third derivative is bounded over a box wide in all
     three slots, the cell bound is grown by that step, and Cell.check_ccert3
     establishes the result. The widening and the check happen in one run, so
     what this produces is a verdict rather than a file another party can
     re-check; the check itself is the extracted one and re-evaluates
     everything, which is what the theorem needs. *)
  let slot3 =
    let rec find = function
      | "--slot3" :: w :: d :: _ ->
          (try Some (int_of_string w, Int64.of_string d) with _ -> None)
      | _ :: tl -> find tl
      | [] -> None in
    find args in
  let positional =
    (* the two words after --slot3 are its arguments, not file names *)
    let rec strip = function
      | "--slot3" :: _ :: _ :: tl -> strip tl
      | x :: tl -> x :: strip tl
      | [] -> [] in
    Stdlib.List.filter
      (fun s -> String.length s < 2 || String.sub s 0 2 <> "--")
      (strip args) in
  let usage () =
    prerr_endline
      ("usage: main [--lower] [--taylor] [--slot3 W DW] <cert> | "
       ^ "main --integrate <cert> | "
       ^ "main --tighten [--lower [--filter]] [--verify] <in> <out>");
    exit 2 in
  let src = match positional with s :: _ -> s | [] -> usage () in
  let dst = match positional with _ :: d :: _ -> d | _ -> if tighten then usage () else "" in
  let toks = tokens_of_file src in
  let p = ref 0 in
  let tok () = let t = toks.(!p) in incr p; t in
  let expect w = let t = tok () in
    if t <> w then (Printf.eprintf "expected %s, got %s (tok %d)\n" w t !p; exit 2) in
  let int64 () = Int64.of_string (tok ()) in
  let dyadic () = let m = int64 () in let e = int64 () in { m; e } in

  let cells_mode = (toks.(0) = "STELLAROCQ-CCERT") in
  if cells_mode then (expect "STELLAROCQ-CCERT"; expect "7")
  else (expect "STELLAROCQ-CERT"; expect "6");
  expect "PREC"; let prec = int64 () in
  if Int64.compare prec 2L < 0 then (prerr_endline "PREC must be at least 2"; exit 2);
  (* Whether the reconstruction carries the antisymmetric half, and which
     closed form the pressure takes. Both fix the shape of the environment
     and of the residual, so they are read before anything numeric. *)
  expect "LASYM"; let lasym = (tok () = "1") in
  expect "PROFILE";
  let prof =
    match tok () with
    | "POWER" -> Physics.PPower
    | "TWOPOWER" ->
        let p = Int64.to_int (int64 ()) in
        let q = Int64.to_int (int64 ()) in Physics.PTwoPower (p, q)
    | "CUBIC" -> Physics.PCubic
    | "RATIONAL" ->
        let a = Int64.to_int (int64 ()) in
        let b = Int64.to_int (int64 ()) in Physics.PRational (a, b)
    | "GAUSSTRUNC" -> Physics.PGaussTrunc
    | "TWOPOWERGS" ->
        let p = Int64.to_int (int64 ()) in
        let q = Int64.to_int (int64 ()) in
        let g = Int64.to_int (int64 ()) in Physics.PTwoPowerGs (p, q, g)
    | "PEDESTAL" -> Physics.PPedestal
    | "TWOLORENTZ" ->
        let p = Int64.to_int (int64 ()) in
        let q = Int64.to_int (int64 ()) in
        let r = Int64.to_int (int64 ()) in
        let t = Int64.to_int (int64 ()) in Physics.PTwoLorentz (p, q, r, t)
    | s -> Printf.eprintf "unknown PROFILE %s
" s; exit 2 in
  (* What the three components carry: the residual, the residual times one
     angular kernel, or the integrands of the flux-surface averages. *)
  (* the two input slots a cell ranges over; 1 and 2 are the angles *)
  expect "SLOTS";
  let xu = Int64.to_int (int64 ()) in
  let xv = Int64.to_int (int64 ()) in
  (* A third varied slot carried by the file rather than by the command line.
     With it a cell certificate is checked by Cell.check_ccert3, and what the
     run establishes is a bound at every point of a cell in three coordinates
     at once. Each bound line then carries two more numbers, the bound on the
     third derivative of that component. *)
  let slot3_file =
    if !p < Array.length toks && toks.(!p) = "SLOT3" then begin
      ignore (tok ());
      let w = Int64.to_int (int64 ()) in
      let dw = int64 () in
      Some (w, dw)
    end else None in
  (* A TAYLOR line marks a certificate whose first varied slot is charged
     against its derivative at the centre, so every bound line carries ten
     numbers rather than eight: N0 q0 Nu qu Nuu quu Nv qv Nc qc. "--tighten
     --taylor" writes such a file and an ordinary run of it establishes it
     with Cell.check_ccert_t, the way a SLOT3 file is checked by
     check_ccert3. *)
  let taylor_file =
    if !p < Array.length toks && toks.(!p) = "TAYLOR"
    then (ignore (tok ()); true) else false in
  let n_bound =
    match slot3_file with Some _ -> 10 | None -> if taylor_file then 10 else 8 in
  expect "OUTPUT";
  let out =
    match tok () with
    | "residual" -> Physics.RResidual
    | "geometry" -> Physics.RGeometry
    | "mercier-a" -> Physics.RMercierA
    | "mercier-b" -> Physics.RMercierB
    | "radial" -> Physics.RRadial
    | "radial-geometry" -> Physics.RRadialGeom
    | "radial-shear" -> Physics.RRadialShear
    | "radial-axis" -> Physics.RRadialAxis
    | "terms" -> Physics.RTerms
    | "radial-terms" -> Physics.RRadialTerms
    | "current-terms" -> Physics.RJsTerms
    | "radial-current-terms" -> Physics.RRadialJsTerms
    | "quasisym" -> Physics.RQuasiSym
    | "quasisym-two" -> Physics.RQuasiTwo
    | "covariant" ->
        let hm = int64 () in
        let hn = int64 () in
        Physics.RCovHarm (z_of_int64 hm, z_of_int64 hn)
    | "covariant-sin" ->
        let hm = int64 () in
        let hn = int64 () in
        Physics.RCovHarmS (z_of_int64 hm, z_of_int64 hn)
    | "stream-defect" -> Physics.RStreamDefect
    | "boozer" ->
        let hm = int64 () in
        let hn = int64 () in
        Physics.RBoozer (z_of_int64 hm, z_of_int64 hn)
    | "harmonic" ->
        let hm = int64 () in
        let hn = int64 () in
        Physics.RHarmonic (z_of_int64 hm, z_of_int64 hn)
    | s -> prerr_endline ("unknown OUTPUT " ^ s); exit 2 in
  let cfg =
    { Physics.pc_lasym = lasym; Physics.pc_prof = prof;
      Physics.pc_out = out } in
  expect "MODES";
  let nk = Int64.to_int (int64 ()) in
  let modes = Array.init nk (fun _ -> let m = int64 () in let n = int64 () in (m, n)) in
  expect "PHIP"; let phip = dyadic () in
  expect "AM"; expect "21";
  let am = Array.init 21 (fun _ -> dyadic ()) in
  let eps =
    if cells_mode then [||]
    else begin
      expect "EPS_S"; let a = dyadic () in
      expect "EPS_U"; let b = dyadic () in
      expect "EPS_V"; let c = dyadic () in
      [| a; b; c |]
    end in
  expect "NANGLES";
  let na = Int64.to_int (int64 ()) in
  (* in cell mode each angle carries the half-widths of its cell, in units of
     the mantissa of that angle *)
  let angles = Array.init na (fun _ ->
      let u = dyadic () in let v = dyadic () in
      let du = if cells_mode then int64 () else 0L in
      let dv = if cells_mode then int64 () else 0L in
      (u, v, du, dv)) in
  expect "NNODES";
  let nb = Int64.to_int (int64 ()) in
  (* The bounds of every cell are held as unboxed ints and turned into the
     extracted record only for the cell being checked. A coq_Z is a boxed
     binary-positive tree, so converting a whole certificate up front costs
     gigabytes at the cell counts a volume covering needs, and the forked
     workers each pay for it again as the collector touches the pages. *)
  let cbounds () = Array.init n_bound (fun _ -> Int64.to_int (int64 ())) in
  let mk_cb (a : int array) =
    let z i = z_of_int64 (Int64.of_int a.(i)) in
    { Cell.cb_N0 = z 0; Cell.cb_q0 = z 1;
      Cell.cb_NDu = z 2; Cell.cb_qDu = z 3;
      Cell.cb_NDv = z 4; Cell.cb_qDv = z 5;
      Cell.cb_Nc = z 6; Cell.cb_qc = z 7 } in
  (* the third slot's derivative bound, when the file carries one *)
  let mk_w (a : int array) =
    (z_of_int64 (Int64.of_int a.(8)), z_of_int64 (Int64.of_int a.(9))) in
  (* a Taylor bound line: value, first and second derivative in the first
     slot, the mean-value step in the second, and the cell bound *)
  let mk_tb (a : int array) =
    let z i = z_of_int64 (Int64.of_int a.(i)) in
    { Cell.tb_N0 = z 0; Cell.tb_q0 = z 1;
      Cell.tb_Nu = z 2; Cell.tb_qu = z 3;
      Cell.tb_Nuu = z 4; Cell.tb_quu = z 5;
      Cell.tb_Nv = z 6; Cell.tb_qv = z 7;
      Cell.tb_Nc = z 8; Cell.tb_qc = z 9 } in
  (* Everything a node block fixes. Consecutive radial cells of one node
     differ only in their radius and half-width, so a block may say SAME and
     take the coefficients of the one before it, which is what keeps a volume
     certificate from repeating the same few thousand numbers once per cell. *)
  let nodes = Array.make nb None in
  for i = 0 to nb - 1 do
    expect "NODE";
    let same = (!p < Array.length toks && toks.(!p) = "SAME") in
    if same then ignore (tok ());
    expect "S"; let s = dyadic () in
    (* A node may carry its own half-width for the first varied slot. The
       angle list is shared by every node, so without this every radial cell
       is the same width, and the bound over a plasma is set near the axis
       while the resolvable region is left coarser than it need be. *)
    let node_du =
      if !p < Array.length toks && toks.(!p) = "DU"
      then (ignore (tok ()); Some (int64 ()))
      else None in
    (* A node may also carry its own pressure coefficients. A piecewise
       profile is one cubic on each piece, so a covering that crosses a knot
       needs the piece to change with the node rather than once for the file.
       Absent, the file's own AM block is used. *)
    let node_am =
      if !p < Array.length toks && toks.(!p) = "AMLOCAL"
      then begin
        ignore (tok ()); expect "21";
        Some (Array.init 21 (fun _ -> dyadic ()))
      end else None in
    let (snodes, shalf, iota, rn, zn, ln, anti) =
      if same then begin
        if i = 0 then (prerr_endline "the first NODE cannot be SAME"; exit 2);
        match nodes.(i - 1) with
        | None -> prerr_endline "no previous node"; exit 2
        | Some (_, sn, sh, io, rn, zn, ln, an, _, _, _) ->
            (sn, sh, io, rn, zn, ln, an)
      end else begin
        expect "SNODES"; let snodes = Array.init 3 (fun _ -> dyadic ()) in
        expect "SHALF"; let shalf = Array.init 2 (fun _ -> dyadic ()) in
        expect "IOTA";  let iota  = Array.init 2 (fun _ -> dyadic ()) in
        expect "RNODES"; let rn = Array.init (3*nk) (fun _ -> dyadic ()) in
        expect "ZNODES"; let zn = Array.init (3*nk) (fun _ -> dyadic ()) in
        expect "LHALF"; let ln = Array.init (2*nk) (fun _ -> dyadic ()) in
        let anti =
          if not lasym then [||]
          else begin
            expect "RNODES_A";
            let rna = Array.init (3*nk) (fun _ -> dyadic ()) in
            expect "ZNODES_A";
            let zna = Array.init (3*nk) (fun _ -> dyadic ()) in
            expect "LHALF_A";
            let lna = Array.init (2*nk) (fun _ -> dyadic ()) in
            Array.concat [rna; zna; lna]
          end in
        (snodes, shalf, iota, rn, zn, ln, anti)
      end in
    (* An output that reads a Boozer stream function carries one more block:
       its coefficients, then the two flux functions I and G. The
       reconstruction never computes it, so it is data the certificate carries
       and whose defect a stream-defect covering bounds. *)
    let wblock =
      if !p < Array.length toks && toks.(!p) = "WCOEF"
      then begin
        ignore (tok ());
        let m = Int64.to_int (int64 ()) in
        if m <> nk then
          (prerr_endline "WCOEF count differs from MODES"; exit 2);
        Array.init (nk + 2) (fun _ -> dyadic ())
      end else [||] in
    (* the flux function a two-term quasisymmetry certificate claims the
       ratio equals; one number, read the way the stream function block is *)
    let f0block =
      if !p < Array.length toks && toks.(!p) = "FZERO"
      then (ignore (tok ()); [| dyadic () |])
      else [||] in
    let bounds =
      if cells_mode then begin
        expect "CELLS";
        let m = Int64.to_int (int64 ()) in
        if m <> na then
          (prerr_endline "CELLS count differs from NANGLES"; exit 2);
        Array.init m (fun _ ->
            let bs = cbounds () in
            let bu = cbounds () in
            let bv = cbounds () in
            (bs, bu, bv))
      end else [||] in
    nodes.(i) <-
      Some (s, snodes, shalf, iota, rn, zn, ln,
            Array.append anti (Array.append wblock f0block),
            bounds, node_du, node_am)
  done;
  let node_at i =
    match nodes.(i) with
    | Some n -> n
    | None -> prerr_endline "a node block is missing"; exit 2 in

  (* ---- expand into per-point environments ------------------------------ *)
  (* Environment of one point, in the slot order of Physics.v. *)
  let env_of (s, snodes, shalf, iota, rn, zn, ln, anti, _, _, node_am)
        (u, v, _, _) =
    let am = match node_am with Some a -> a | None -> am in
    let entries =
      Array.concat [
        [| s; u; v; phip |];
        snodes; shalf; iota; am; rn; zn; ln; anti ] in
    let ms = Array.to_list (Array.map (fun d -> z_of_int64 d.m) entries) in
    let es = Array.to_list (Array.map (fun d -> z_of_int64 d.e) entries) in
    { Checker.pt_ms = ms; Checker.pt_es = es }
  in
  let coq_modes =
    Array.to_list (Array.map (fun (m, n) -> (z_of_int64 m, z_of_int64 n)) modes) in
  let ncells = nb * na in
  let n = min (jobs ()) (max 1 ncells) in
  (* Approximate float value of a dyadic, for display only. *)
  let f_of d = Int64.to_float d.m *. (2.0 ** Int64.to_float d.e) in
  (* Cell k of the certificate, built on demand. A whole certificate of
     environments does not fit in memory at the cell counts a continuum bound
     needs, so nothing here holds more than one at a time. *)
  let cell_at k =
    let b = node_at (k / na) in
    let a = angles.(k mod na) in
    let (_, _, du, dv) = a in
    let (_, _, _, _, _, _, _, _, bounds, ndu, _) = b in
    let du = match ndu with Some d -> d | None -> du in
    let (bs, bu, bv) = bounds.(k mod na) in
    ({ Cell.cc_pt = env_of b a;
       Cell.cc_du = z_of_int64 du; Cell.cc_dv = z_of_int64 dv;
       Cell.cc_s = mk_cb bs; Cell.cc_u = mk_cb bu; Cell.cc_v = mk_cb bv },
     du, dv) in
  (* the same cell as a three-slot one, when the file carries a third slot *)
  let cell3_at k dw =
    let b = node_at (k / na) in
    let a = angles.(k mod na) in
    let (_, _, du, dv) = a in
    let (_, _, _, _, _, _, _, _, bounds, ndu, _) = b in
    let du = match ndu with Some d -> d | None -> du in
    let (bs, bu, bv) = bounds.(k mod na) in
    let (nws, qws) = mk_w bs and (nwu, qwu) = mk_w bu
    and (nwv, qwv) = mk_w bv in
    { Cell.c3_pt = env_of b a;
      Cell.c3_du = z_of_int64 du; Cell.c3_dv = z_of_int64 dv;
      Cell.c3_dw = z_of_int64 dw;
      Cell.c3_s = mk_cb bs; Cell.c3_u = mk_cb bu; Cell.c3_v = mk_cb bv;
      Cell.c3_Nws = nws; Cell.c3_qws = qws;
      Cell.c3_Nwu = nwu; Cell.c3_qwu = qwu;
      Cell.c3_Nwv = nwv; Cell.c3_qwv = qwv } in
  (* the same cell as a Taylor cell, when the file carries ten-number bounds *)
  let tcell_at k =
    let b = node_at (k / na) in
    let a = angles.(k mod na) in
    let (_, _, du, dv) = a in
    let (_, _, _, _, _, _, _, _, bounds, ndu, _) = b in
    let du = match ndu with Some d -> d | None -> du in
    let (bs, bu, bv) = bounds.(k mod na) in
    { Cell.tc_pt = env_of b a;
      Cell.tc_du = z_of_int64 du; Cell.tc_dv = z_of_int64 dv;
      Cell.tc_s = mk_tb bs; Cell.tc_u = mk_tb bu; Cell.tc_v = mk_tb bv } in
  let ccert_of cl =
    { Cell.cc_prec = z_of_int64 prec; Cell.cc_cfg = cfg;
      Cell.cc_modes = coq_modes; Cell.cc_cells = [cl] } in
  let cert_of pt =
    { Checker.c_prec = z_of_int64 prec; Checker.c_cfg = cfg;
      Checker.c_modes = coq_modes;
      Checker.c_NS = z_of_int64 eps.(0).m; Checker.c_qS = z_of_int64 eps.(0).e;
      Checker.c_NU = z_of_int64 eps.(1).m; Checker.c_qU = z_of_int64 eps.(1).e;
      Checker.c_NV = z_of_int64 eps.(2).m; Checker.c_qV = z_of_int64 eps.(2).e;
      Checker.c_points = [pt] } in
  let range i = (i * ncells / n, (i + 1) * ncells / n) in
  (* How many indices f accepts, over forked shards. A floor verdict is a
     theorem about the one cell it is checked on, so the count is the
     result, where a ceiling verdict is the conjunction. *)
  let count_over_shards f =
    if n = 1 then begin
      let c = ref 0 in
      for k = 0 to ncells - 1 do if f k then incr c done;
      !c
    end else begin
      let part i = Printf.sprintf "%s.count%d" src i in
      let pids =
        Stdlib.List.init n (fun i ->
            match Unix.fork () with
            | 0 ->
                let (lo, hi) = range i in
                let c = ref 0 in
                for k = lo to hi - 1 do if f k then incr c done;
                let oc = open_out (part i) in
                output_string oc (string_of_int !c);
                close_out oc; exit 0
            | pid -> pid) in
      Stdlib.List.iter (fun pid -> ignore (Unix.waitpid [] pid)) pids;
      let total = ref 0 in
      for i = 0 to n - 1 do
        let ic = open_in (part i) in
        (try total := !total + int_of_string (String.trim (input_line ic))
         with _ -> ());
        close_in ic; Sys.remove (part i)
      done;
      !total
    end in
  (* Run f over every index in forked shards, gathering both the verdict and
     the largest bound any cell reported. A child's ref is its own, so the
     maximum travels back through a file the way the counts do. *)
  let over_shards_max f =
    let worst = ref 0.0 in
    let step k = let (ok, m) = f k in
                 if m > !worst then worst := m; ok in
    if n = 1 then begin
      let ok = ref true in
      for k = 0 to ncells - 1 do if not (step k) then ok := false done;
      (!ok, !worst)
    end else begin
      let part i = Printf.sprintf "%s.max%d" src i in
      let pids =
        Stdlib.List.init n (fun i ->
            match Unix.fork () with
            | 0 ->
                let (lo, hi) = range i in
                let ok = ref true in
                for k = lo to hi - 1 do if not (step k) then ok := false done;
                let oc = open_out (part i) in
                Printf.fprintf oc "%h" !worst;
                close_out oc;
                exit (if !ok then 0 else 1)
            | pid -> pid) in
      let ok =
        Stdlib.List.fold_left (fun acc pid ->
            match snd (Unix.waitpid [] pid) with
            | Unix.WEXITED 0 -> acc
            | _ -> false) true pids in
      for i = 0 to n - 1 do
        (try
           let ic = open_in (part i) in
           (try Scanf.sscanf (input_line ic) "%h"
                  (fun m -> if m > !worst then worst := m)
            with _ -> ());
           close_in ic; Sys.remove (part i)
         with _ -> ())
      done;
      (ok, !worst)
    end in

  (* Run f over every index in forked shards; true iff every shard says so.

     A verdict is a conjunction over the cells the file carries, so a shard
     that quietly checked nothing would leave the conjunction true and the
     cells unchecked. Each shard reports how many indices it visited and the
     total has to be the cell count, which turns that from something the
     ranges are trusted to get right into something the run checks. *)
  let over_shards f =
    if n = 1 then begin
      let ok = ref true in
      let seen = ref 0 in
      for k = 0 to ncells - 1 do incr seen; if not (f k) then ok := false done;
      if !seen <> ncells then
        (prerr_endline "the run did not visit every cell"; exit 3);
      !ok
    end else begin
      let part i = Printf.sprintf "%s.seen%d" src i in
      let pids =
        Stdlib.List.init n (fun i ->
            match Unix.fork () with
            | 0 ->
                let (lo, hi) = range i in
                let ok = ref true in
                let seen = ref 0 in
                for k = lo to hi - 1 do
                  incr seen;
                  if not (f k) then ok := false
                done;
                let oc = open_out (part i) in
                output_string oc (string_of_int !seen);
                close_out oc;
                exit (if !ok then 0 else 1)
            | pid -> pid) in
      let ok =
        Stdlib.List.fold_left (fun acc pid ->
            match snd (Unix.waitpid [] pid) with
            | Unix.WEXITED 0 -> acc
            | _ -> false) true pids in
      let total = ref 0 in
      for i = 0 to n - 1 do
        (try
           let ic = open_in (part i) in
           (try total := !total + int_of_string (String.trim (input_line ic))
            with _ -> ());
           close_in ic; Sys.remove (part i)
         with _ -> ())
      done;
      if !total <> ncells then begin
        Printf.eprintf
          "the shards visited %d cells of %d: the split lost some\n%!"
          !total ncells;
        exit 3
      end;
      ok
    end in
  (* Do the cells leave a gap?

     Cell.v certifies each cell on its own, so a passing certificate is a
     conjunction over the cells the file happens to carry. Cover.covers is the
     extracted check that they also abut, which is what makes their union an
     interval and lets a verdict speak about every angle or radius of a range
     rather than about a list of rectangles. The mantissa of a varied slot
     comes from the node for slot 0 and from the cell list for slots 1 and 2,
     which is the layout env_of builds. *)
  let slot_dyadic k slot =
    let (s_, _, _, _, _, _, _, _, _, _, _) = node_at (k / na) in
    let (u, v, _, _) = angles.(k mod na) in
    match slot with
    | 0 -> Some s_
    | 1 -> Some u
    | 2 -> Some v
    | _ -> None in
  let slot_width k slot =
    let (_, _, du, dv) = angles.(k mod na) in
    let (_, _, _, _, _, _, _, _, _, ndu, _) = node_at (k / na) in
    let du = match ndu with Some d -> d | None -> du in
    if slot = xu then Some du else if slot = xv then Some dv else None in
  let covering_report slot name =
    let good = ref false in
    let pairs = ref [] in
    let expo = ref None in
    let ok = ref true in
    (* Cells written at different exponents still describe one range, so
       every centre and half-width is carried to the finest exponent present.
       That exponent is the smallest, so each shift is upward and exact: no
       cell is claimed wider than it is, and a range too wide to shift is
       saturated rather than wrapped. *)
    let fine = ref None in
    for k = 0 to ncells - 1 do
      match slot_dyadic k slot with
      | Some d ->
          (match !fine with
           | None -> fine := Some d.e
           | Some e -> if Int64.compare d.e e < 0 then fine := Some d.e)
      | None -> ()
    done;
    let fine = match !fine with Some e -> e | None -> 0L in
    let rescale m e =
      let sh = Int64.to_int (Int64.sub e fine) in
      if sh <= 0 then m
      else if sh > 62 then Int64.max_int
      else Int64.shift_left m sh in
    for k = 0 to ncells - 1 do
      match slot_dyadic k slot, slot_width k slot with
      | Some d, Some w ->
          expo := Some fine;
          pairs := (rescale d.m d.e, rescale w d.e) :: !pairs
      | _ -> ok := false
    done;
    if not !ok then
      Printf.printf "  %s: a cell carries no width for this slot\n%!" name
    else begin
      (* sorted by lower endpoint, which is the order the chain walks *)
      let ps = Stdlib.List.sort_uniq
                 (fun (c1, d1) (c2, d2) ->
                    compare (Int64.sub c1 d1, c1, d1) (Int64.sub c2 d2, c2, d2))
                 !pairs in
      match ps with
      | [] -> ()
      | (c0, d0) :: _ ->
          let lo = Int64.sub c0 d0 in
          let hi = Stdlib.List.fold_left
                     (fun acc (c, d) -> max acc (Int64.add c d)) lo ps in
          let zs = Stdlib.List.map
                     (fun (c, d) -> (z_of_int64 c, z_of_int64 d)) ps in
          let e = match !expo with Some e -> Int64.to_float e | None -> 0.0 in
          let scale = 2.0 ** e in
          if Cover.covers (z_of_int64 lo) (z_of_int64 hi) zs then begin
            good := true;
            Printf.printf
              "  %s: %d cells cover [%.6f, %.6f] with no gap\n%!"
              name (Stdlib.List.length ps)
              (Int64.to_float lo *. scale) (Int64.to_float hi *. scale)
          end else
            Printf.printf
              "  %s: the cells leave a gap inside [%.6f, %.6f]\n%!"
              name (Int64.to_float lo *. scale) (Int64.to_float hi *. scale)
    end;
    !good in
  let names = [| "radius"; "poloidal angle"; "toroidal angle" |] in
  if cells_mode && not tighten && not integrate then begin
    Stdlib.List.iter
      (fun sl -> if sl >= 0 && sl <= 2 then ignore (covering_report sl names.(sl)))
      [xu; xv]
  end;
  let t0 = Unix.gettimeofday () in
  let ok =
    if cells_mode then begin
      if tighten then begin
        let part i = Printf.sprintf "%s.part%d" dst i in
        let pids =
          Stdlib.List.init n (fun i ->
              match Unix.fork () with
              | 0 ->
                  let (lo, hi) = range i in
                  let oc = open_out (part i) in
                  for k = lo to hi - 1 do
                    let (cl, du, dv) = cell_at k in
                    let ct = ccert_of cl in
                    let ctx = ctx_for xu xv na k ct cl in
                    let lines =
                      if lower then
                        tighten_cell_lower xu xv (k / na) ctx ct cl du dv
                      else if taylor || taylor_file then
                        tighten_cell_taylor xu xv (k / na) ctx ct cl du dv
                      else
                        tighten_cell ?slot3:slot3_file xu xv (k / na) ctx ct cl
                          du dv in
                    Stdlib.List.iter
                      (fun (ln, _) -> output_string oc (ln ^ "\n")) lines
                  done;
                  close_out oc;
                  exit 0
              | pid -> pid) in
        Stdlib.List.iter (fun pid ->
            match snd (Unix.waitpid [] pid) with
            | Unix.WEXITED 0 -> ()
            | _ -> exit 3) pids;
        let out = ref [] in
        (* the ceiling run reports the widest cell bound; the floor run
           reports the narrowest floor, taking the best of the three
           components of each cell, since one suffices to put it out of
           balance *)
        let worst = ref 0.0 in
        let best_of_triple = ref 0.0 in
        let narrowest = ref infinity in
        let certified = ref 0 in
        let seen = ref 0 in
        let keep = ref [] in
        for i = 0 to n - 1 do
          let ic = open_in (part i) in
          (try
             while true do
               let l = input_line ic in
               (* the cell bound is the fourth pair of an ordinary line, and
                  the fifth of a Taylor line, whose value, first and second
                  derivative in the first slot push it two fields along *)
               let fields = Array.of_list (String.split_on_char ' ' l) in
               let ci = if taylor || taylor_file then 8 else 6 in
               (match
                  (if Array.length fields > ci + 1
                   then Some (fields.(ci), fields.(ci + 1)) else None)
                with
                | Some (nc, qc) when
                    (try ignore (float_of_string nc);
                         ignore (float_of_string qc); true
                     with _ ->
                       Printf.eprintf "unparsable bound line: %s\n%!" l; false) ->
                    let v = float_of_string nc *. (2.0 ** float_of_string qc) in
                    if v > !worst then worst := v;
                    if v > !best_of_triple then best_of_triple := v;
                    incr seen;
                    if !seen mod 3 = 0 then begin
                      keep := (!best_of_triple > 0.0) :: !keep;
                      if !best_of_triple > 0.0 then begin
                        incr certified;
                        if !best_of_triple < !narrowest then
                          narrowest := !best_of_triple
                      end;
                      best_of_triple := 0.0
                    end
                | _ -> ());
               out := l :: !out
             done
           with End_of_file -> ());
          close_in ic;
          Sys.remove (part i)
        done;
        let lines = Array.of_list (Stdlib.List.rev !out) in
        if filter then begin
          if not lower then begin
            prerr_endline
              "--filter drops the cells with no floor, so it needs --lower";
            exit 2
          end;
          if nb <> 1 then begin
            prerr_endline
              ("--filter rewrites the shared angle list, so it needs a "
               ^ "single-node certificate (--node)");
            exit 2
          end;
          rewrite_filtered src dst lines (Array.of_list (Stdlib.List.rev !keep))
        end else rewrite_bounds src dst lines;
        if lower then
          Printf.printf
            "tightened %d cells into %s: %d certified out of balance%s, best floor %.6e, narrowest nonzero floor %.6e\n%!"
            ncells dst !certified
            (if filter then " (the rest dropped)" else "") !worst
            (if !narrowest = infinity then 0.0 else !narrowest)
        else
          Printf.printf
            "tightened %d cells into %s: worst cell bound %.6e\n%!"
            ncells dst !worst;
        if verify then begin
          (* hand the written file to a fresh process, which reads it with no
             knowledge of how its numbers were chosen *)
          let args =
            Array.of_list
              ([Sys.argv.(0)] @ (if lower then ["--lower"] else []) @ [dst]) in
          Printf.printf "verifying %s in a fresh process\n%!" dst;
          (try Unix.execv Sys.argv.(0) args
           with _ -> prerr_endline "could not start the verifying run"; exit 3)
        end;
        exit 0
      end;
      Printf.printf
        "stellarocq checker: %d modes, %d nodes x %d cells = %d cells, precision %Ld bits, %d workers\n%!"
        nk nb na ncells prec n;
      if integrate then begin
        (* An integral over cells is the sum of theorems about them, and
           which theorem depends on the covering. Quad.tiling_var_encloses
           sums cells that tile a range, each with its own width, which is
           what a covering by curves is. Quad.tiling2_encloses sums a
           rectangle of cells of one width in each angle, which is what a
           surface covering is, and it does need the widths uniform. Both
           need the cells to tile, and neither is assumed here. *)
        let (_, _, du0, dv0) = angles.(0) in
        if Int64.compare dv0 0L > 0 then
          Array.iter (fun (_, _, du, dv) ->
              if Int64.compare du du0 <> 0 || Int64.compare dv dv0 <> 0
              then begin
                prerr_endline
                  "this covers a surface, and the rule for one is a rectangle \
                   of cells of a common width in each angle; these differ";
                exit 3
              end) angles;
        Stdlib.List.iter
          (fun sl ->
             if sl >= 0 && sl <= 2 then begin
               let ok = covering_report sl names.(sl) in
               (* the toroidal angle of a covering by curves has no width at
                  all, and the run reports one integral per plane rather than
                  one over the surface, which is a different statement and an
                  honest one *)
               if not ok && not (sl = xv && Int64.compare dv0 0L = 0) then begin
                 prerr_endline
                   "the cells leave a gap, so their sum is not an integral \
                    over the range they claim";
                 exit 3
               end
             end)
          [xu; xv];
        Printf.printf
          "integrating each component over the %s the %d cells cover\n%!"
          (if Int64.compare dv0 0L > 0 then "surface patch" else "angles")
          ncells;
        let (u0, v0, _, _) = angles.(0) in
        (* the angle list runs v fastest, so the leading run of entries
           sharing the first u counts the toroidal planes *)
        let nplanes =
          let c = ref 1 in
          (try
             while !c < na do
               let (u, _, _, _) = angles.(!c) in
               if u.m <> u0.m || u.e <> u0.e then raise Exit;
               incr c
             done
           with Exit -> ());
          !c in
        let prec0 = Cell.cprec_of (let (cl, _, _) = cell_at 0 in ccert_of cl) in
        integrate_cells prec0
          (fun k -> let (cl, du, dv) = cell_at k in (ccert_of cl, cl, du, dv))
          xu xv nb na nplanes (Int64.to_float u0.e) (Int64.to_float v0.e) n src
          (match out with
           | Physics.RGeometry -> [ "sqrt(g)"; "sqrt(g) B^2"; "B_u" ]
           | Physics.RMercierA -> [ "tpp"; "tbb"; "tjb" ]
           | Physics.RMercierB -> [ "tjj"; "gf"; "B^2" ]
           | Physics.RRadialGeom -> [ "dV/ds"; "V''"; "B_u" ]
           | Physics.RRadialShear -> [ "iota'"; "dB_u/ds"; "mu0 p'" ]
           | Physics.RTerms | Physics.RRadialTerms ->
               [ "(dvBs-dsBv)Bv"; "(dsBu-duBs)Bu"; "mu0 p'" ]
           | Physics.RJsTerms | Physics.RRadialJsTerms ->
               [ "d_u B_v"; "d_v B_u"; "mu0 sqrtg J^s" ]
           | Physics.RQuasiSym -> [ "qs triple"; "term uv"; "term vu" ]
           | Physics.RQuasiTwo -> [ "qs defect"; "B x grad s . grad B";
                                    "F0 B . grad B" ]
           | Physics.RCovHarm (_, _) -> [ "B_u k"; "B_v k"; "mu0 sqrtg J^s k" ]
           | Physics.RCovHarmS (_, _) -> [ "B_u k"; "B_v k"; "mu0 sqrtg J^s k" ]
           | Physics.RStreamDefect ->
               [ "w_u defect"; "w_v defect"; "mu0 sqrtg J^s" ]
           | Physics.RBoozer (_, _) -> [ "|B| cos J"; "|B| sin J"; "J" ]
           | _ -> [ "r_s"; "r_u"; "r_v" ]);
        exit 0
      end;
      if taylor then begin
        let prec0 = Cell.cprec_of (let (cl, _, _) = cell_at 0 in ccert_of cl) in
        Printf.printf
          "recomputing each cell against the derivative at its centre\n%!";
        let (ok, worst) = over_shards_max (fun k ->
            let worst = ref 0.0 in
            let (cl, du, dv) = cell_at k in
            let ct = ccert_of cl in
            let ctx = ctx_for xu xv na k ct cl in
            let ms = cl.Cell.cc_pt.Checker.pt_ms in
            let r3 = ctx.nc_r3 in
            let len = ctx.nc_len in
            let base = ctx.nc_base in
            let binds = r3.Physics.r_binds in
            let box = Cell.box_ienv xu xv prec0 ms cl.Cell.cc_du cl.Cell.cc_dv in
            let d2 = Deriv.with_derivs2 xu base len binds in
            let env0 = Expr.iextend prec0 (Checker.ienv_of prec0 ms) binds in
            let envd = Expr.iextend prec0 (Checker.ienv_of prec0 ms) d2 in
            let envb = Expr.iextend prec0 box d2 in
            let envv =
              Expr.iextend prec0 box (Deriv.with_derivs xv base len binds) in
            let f m e = Int64.to_float m *. (2.0 ** Int64.to_float e) in
            let tb r =
              match Cell.slot_of r with
              | None -> None
              | Some n ->
                  let (n0, q0) = bound_for prec0 env0 r in
                  let (nu, qu) = bound_for prec0 envd (Expr.Evar (n + len)) in
                  let (nuu, quu) =
                    bound_for prec0 envb (Expr.Evar (n + 2 * len)) in
                  let (nv, qv) = bound_for prec0 envv (Expr.Evar (n + len)) in
                  let total =
                    f n0 q0
                    +. Int64.to_float du *. f nu qu
                    +. Int64.to_float du *. Int64.to_float du *. f nuu quu
                    +. Int64.to_float dv *. f nv qv in
                  let at nc qc =
                    { Cell.tb_N0 = z_of_int64 n0; Cell.tb_q0 = z_of_int64 q0;
                      Cell.tb_Nu = z_of_int64 nu; Cell.tb_qu = z_of_int64 qu;
                      Cell.tb_Nuu = z_of_int64 nuu;
                      Cell.tb_quu = z_of_int64 quu;
                      Cell.tb_Nv = z_of_int64 nv; Cell.tb_qv = z_of_int64 qv;
                      Cell.tb_Nc = z_of_int64 nc;
                      Cell.tb_qc = z_of_int64 qc } in
                  let rec grow (nc, qc) j =
                    if j > 200 then
                      (prerr_endline "no Taylor cell bound accepted"; exit 2)
                    else if Checker.nonneg
                              (Expr.ieval prec0 Expr.eempty
                                 (Cell.combination_t cl.Cell.cc_du
                                    cl.Cell.cc_dv (at nc qc)))
                    then (nc, qc)
                    else grow (renorm (Int64.add nc
                                         (Int64.add 1L (Int64.div nc 4096L)),
                                       qc)) (j + 1) in
                  let (nc, qc) = grow (renorm (dyadic_ge total)) 0 in
                  if f nc qc > !worst then worst := f nc qc;
                  Some (at nc qc) in
            match tb r3.Physics.r_s, tb r3.Physics.r_u, tb r3.Physics.r_v with
            | Some bs, Some bu, Some bv ->
                let cl_t =
                  { Cell.tc_pt = cl.Cell.cc_pt;
                    Cell.tc_du = cl.Cell.cc_du; Cell.tc_dv = cl.Cell.cc_dv;
                    Cell.tc_s = bs; Cell.tc_u = bu; Cell.tc_v = bv } in
                let ct_t =
                  { Cell.tc_prec = z_of_int64 prec; Cell.tc_cfg = cfg;
                    Cell.tc_modes = coq_modes; Cell.tc_cells = [cl_t] } in
                (Cell.check_ccert_t xu xv ct_t, !worst)
            | _ -> (false, !worst)) in
        Printf.printf
          "verdict: %s   with the Taylor bound, worst cell bound %.6e\n%!"
          (if ok then "VALID" else "INVALID") worst;
        exit (if ok then 0 else 1)
      end;
      (match slot3 with
       | Some (xw, dw) when xw <> xu && xw <> xv ->
           let prec0 = Cell.cprec_of (let (cl, _, _) = cell_at 0 in ccert_of cl) in
           Printf.printf
             "widening to slot %d with half-width %Ld, and checking all three\n%!"
             xw dw;
           let worst = ref 0.0 in
           let gather = ref [] in
           let ok = over_shards (fun k ->
               let (cl, du, dv) = cell_at k in
               let ct = ccert_of cl in
               let ctx = ctx_for xu xv na k ct cl in
               let ms = cl.Cell.cc_pt.Checker.pt_ms in
               let r3 = ctx.nc_r3 in
               let len = ctx.nc_len in
               let base = ctx.nc_base in
               let binds = r3.Physics.r_binds in
               let box3 =
                 Cell.box_ienv3 xu xv xw prec0 ms cl.Cell.cc_du cl.Cell.cc_dv
                   (z_of_int64 dw) in
               let envw =
                 Expr.iextend prec0 box3
                   (Deriv.with_derivs xw base len binds) in
               let widen r cb =
                 match Cell.slot_of r with
                 | None -> (cb, 0L, 0L, 0.0)
                 | Some n ->
                     let (nw, qw) =
                       bound_for prec0 envw (Expr.Evar (n + len)) in
                     let f m e = Int64.to_float m *. (2.0 ** Int64.to_float e) in
                     let total =
                       float_of_z cb.Cell.cb_N0
                       *. (2.0 ** float_of_z cb.Cell.cb_q0)
                       +. Int64.to_float du
                          *. float_of_z cb.Cell.cb_NDu
                          *. (2.0 ** float_of_z cb.Cell.cb_qDu)
                       +. Int64.to_float dv
                          *. float_of_z cb.Cell.cb_NDv
                          *. (2.0 ** float_of_z cb.Cell.cb_qDv)
                       +. Int64.to_float dw *. f nw qw in
                     let at nc qc =
                       { cb with Cell.cb_Nc = z_of_int64 nc;
                                 Cell.cb_qc = z_of_int64 qc } in
                     (* the same combination check_component3 evaluates.
                        Extracted constructors take a tuple, and eps_e is
                        Checker's. *)
                     let combo nc qc =
                       let eps a b = Checker.eps_e a b in
                       let e_c = eps (z_of_int64 nc) (z_of_int64 qc) in
                       let e_0 = eps cb.Cell.cb_N0 cb.Cell.cb_q0 in
                       let e_du = eps cb.Cell.cb_NDu cb.Cell.cb_qDu in
                       let e_dv = eps cb.Cell.cb_NDv cb.Cell.cb_qDv in
                       let e_dw = eps (z_of_int64 nw) (z_of_int64 qw) in
                       let step d e = Expr.Emul (Expr.EfromZ d, e) in
                       let tail =
                         Expr.Eadd (step cl.Cell.cc_dv e_dv,
                                    step (z_of_int64 dw) e_dw) in
                       let sum =
                         Expr.Eadd (e_0,
                                    Expr.Eadd (step cl.Cell.cc_du e_du, tail)) in
                       Checker.nonneg
                         (Expr.ieval prec0 Expr.eempty (Expr.Esub (e_c, sum))) in
                     let rec grow (nc, qc) k =
                       if k > 200 then
                         (prerr_endline "no three-slot cell bound accepted";
                          exit 2)
                       else if combo nc qc then (nc, qc)
                       else grow (renorm (Int64.add nc
                                            (Int64.add 1L (Int64.div nc 4096L)),
                                          qc)) (k + 1) in
                     let (nc, qc) = grow (renorm (dyadic_ge total)) 0 in
                     (at nc qc, nw, qw, f nc qc) in
               let (cbs, nws, qws, fs) = widen r3.Physics.r_s cl.Cell.cc_s in
               let (cbu, nwu, qwu, fu) = widen r3.Physics.r_u cl.Cell.cc_u in
               let (cbv, nwv, qwv, fv) = widen r3.Physics.r_v cl.Cell.cc_v in
               let m = max fs (max fu fv) in
               if m > !worst then worst := m;
               let cl3 =
                 { Cell.c3_pt = cl.Cell.cc_pt;
                   Cell.c3_du = cl.Cell.cc_du; Cell.c3_dv = cl.Cell.cc_dv;
                   Cell.c3_dw = z_of_int64 dw;
                   Cell.c3_s = cbs; Cell.c3_u = cbu; Cell.c3_v = cbv;
                   Cell.c3_Nws = z_of_int64 nws; Cell.c3_qws = z_of_int64 qws;
                   Cell.c3_Nwu = z_of_int64 nwu; Cell.c3_qwu = z_of_int64 qwu;
                   Cell.c3_Nwv = z_of_int64 nwv; Cell.c3_qwv = z_of_int64 qwv } in
               let ct3 =
                 { Cell.c3_prec = z_of_int64 prec; Cell.c3_cfg = cfg;
                   Cell.c3_modes = coq_modes; Cell.c3_cells = [cl3] } in
               Cell.check_ccert3 xu xv xw ct3) in
           ignore !gather;
           Printf.printf
             "verdict: %s   over three coordinates%s\n%!"
             (if ok then "VALID" else "INVALID")
             (if n = 1 then Printf.sprintf ", worst cell bound %.6e" !worst
              else "");
           exit (if ok then 0 else 1)
       | Some _ ->
           prerr_endline "--slot3 needs a slot different from the two the cells range over";
           exit 2
       | None -> ());
      (match slot3_file with
       | Some (xw, dw) ->
           (* the file carries the third slot, so the bounds were written by a
              tightening run and this one only establishes them *)
           Printf.printf
             "the file carries a third slot %d of half-width %Ld\n%!" xw dw;
           let ok = over_shards (fun k ->
               let cl3 = cell3_at k dw in
               let ct3 =
                 { Cell.c3_prec = z_of_int64 prec; Cell.c3_cfg = cfg;
                   Cell.c3_modes = coq_modes; Cell.c3_cells = [cl3] } in
               Cell.check_ccert3 xu xv xw ct3) in
           let t1 = Unix.gettimeofday () in
           Printf.printf
             "verdict: %s   over three coordinates at every point of every \
              cell (%.1f s)\n%!"
             (if ok then "VALID" else "INVALID") (t1 -. t0);
           exit (if ok then 0 else 1)
       | None -> ());
      if taylor_file then begin
        (* the file carries ten-number bounds a "--tighten --taylor" run
           wrote, so this one only establishes them, with the first slot
           charged against its derivative at the centre *)
        Printf.printf
          "the file carries a Taylor bound, checked against the derivative at \
           each cell centre\n%!";
        let ok = over_shards (fun k ->
            let cl_t = tcell_at k in
            let ct_t =
              { Cell.tc_prec = z_of_int64 prec; Cell.tc_cfg = cfg;
                Cell.tc_modes = coq_modes; Cell.tc_cells = [cl_t] } in
            Cell.check_ccert_t xu xv ct_t) in
        let t1 = Unix.gettimeofday () in
        Printf.printf "verdict: %s   (%.1f s)\n%!"
          (if ok then "VALID" else "INVALID") (t1 -. t0);
        exit (if ok then 0 else 1)
      end;
      if lower then
        Printf.printf
          "the floor is claimed at every angle of every cell: no field of this form balances there\n%!"
      else
        Printf.printf
          "the bound is claimed at every angle of every cell, not only at its centre\n%!";
      (match Sys.getenv_opt "STELLAROCQ_DEBUG" with
       | Some _ -> let (cl, _, _) = cell_at 0 in debug_cell xu xv (ccert_of cl) cl
       | None -> ());
      if lower then begin
        let c = count_over_shards (fun k -> let (cl, _, _) = cell_at k in
                                    Cell.check_ccert_lower xu xv (ccert_of cl)) in
        Printf.printf
          "%d of %d cells proven out of force balance at every angle they cover\n%!"
          c ncells;
        c > 0
      end else
        over_shards (fun k -> let (cl, _, _) = cell_at k in
                      Cell.check_ccert xu xv (ccert_of cl))
    end else begin
      Printf.printf
        "stellarocq checker: %d modes, %d nodes x %d angles = %d points, precision %Ld bits, %d workers\n%!"
        nk nb na ncells prec n;
      if lower then
        Printf.printf
          "claimed: every point carries a component at least  r_s %.6e  r_u %.6e  r_v %.6e\n%!"
          (f_of eps.(0)) (f_of eps.(1)) (f_of eps.(2))
      else
        Printf.printf "claimed bounds: |r_s| <= %.6e  |r_u| <= %.6e  |r_v| <= %.6e\n%!"
          (f_of eps.(0)) (f_of eps.(1)) (f_of eps.(2));
      over_shards (fun k ->
          let ct = cert_of (env_of (node_at (k / na)) angles.(k mod na)) in
          if lower then Checker.check_cert_lower ct else Checker.check_cert ct)
    end in
  let t1 = Unix.gettimeofday () in
  Printf.printf "verdict: %s   (%.1f s)\n%!"
    (if ok then "VALID" else "INVALID") (t1 -. t0);
  exit (if ok then 0 else 1)
