(* The cell and assembly stages of the three-dimensional stability check.

     main cells FRAMES OUTDIR NPROC
     main start FRAMES OUT
     main assemble FRAMES ES CELLDIR START R

   FRAMES holds, for each of the 12 segments s in [1/4 + k/16, 1/4 + (k+1)/16],
   the frame W_k and an approximate inverse D_k, 14 rows each, as hexadecimal
   binary64 numbers. Every number is converted exactly to a dyadic (m, e),
   and the enclosure of W_k^-1 is CellTM's winv_encl of W_k and D_k.

   The cells are s in [1/4 + k/16 + j 2^-12, 1/4 + k/16 + (j+1) 2^-12],
   h in [0, 2^-16], k < 12, j < 256: centre and radius (sc, a) and (hc, b) as
   dyadics. Each cell's Taylor model gives the ranges of W N W^-1 over its 16
   reference steps, the parts of width 2^-16 of its s-interval. The cells
   already recorded in OUTDIR are skipped; NPROC forked children take the
   others in turn, and child c appends one line per cell to
   OUTDIR/cells_T_c.txt, T the start time, as it finishes it:

     k j lo hi lo hi ...

   the 16 ranges of 196 entries each, row by row, each bound in hexadecimal,
   or "fail" when cell_ranges returns None. "start" writes the ranges of the
   start rows, 5 rows, for h in [0, 2^-16]. *)

let zi = Big_int_Z.big_int_of_int
let kn = 6
let nsub = 16
let nfields = 2 + nsub * 392

(* x = m 2^e exactly *)
let dyad_of x =
  if x = 0.0 then (zi 0, zi 0)
  else let (f, k) = Stdlib.Float.frexp x in
       (Big_int_Z.big_int_of_int64 (Int64.of_float (Stdlib.Float.ldexp f 53)), zi (k - 53))

let read_frames file =
  let ic = open_in file in
  let readm () = Array.init 14 (fun _ ->
    Array.of_list (Stdlib.List.map float_of_string
      (Stdlib.List.filter (fun s -> s <> "") (String.split_on_char ' ' (input_line ic))))) in
  let fr = Array.init 12 (fun _ -> let w = readm () in let d = readm () in (w, d)) in
  close_in ic;
  Array.map (fun (w, d) ->
    let dl m = Array.to_list (Array.map (fun row -> Array.to_list (Array.map dyad_of row)) m) in
    let wd = dl w and dd = dl d in
    match C3Ext.winv wd dd with
    | Some wi -> (wd, wi)
    | None -> failwith "a frame's inverse is not enclosed") fr

let bound_str = function
  | Float.Ibnd (a, b) -> Printf.sprintf "%h %h" a b
  | Float.Inan -> "nan nan"

let range_str r = String.concat " " (Stdlib.List.map bound_str (Stdlib.List.concat r))

let cell k j =
  ((zi (2048 + 512 * k + 2 * j + 1), zi (-13)), (zi 1, zi (-17)), (zi 1, zi (-13)), (zi 1, zi (-17)))

(* The cells already recorded in OUTDIR: lines of nfields fields or "k j fail". *)
let done_cells outdir =
  let tbl = Hashtbl.create 4096 in
  Array.iter (fun name ->
    if String.length name > 6 && String.sub name 0 6 = "cells_" then begin
      let ic = open_in (Filename.concat outdir name) in
      (try while true do
         let line = input_line ic in
         let fs = Stdlib.List.filter (fun s -> s <> "") (String.split_on_char ' ' line) in
         let n = Stdlib.List.length fs in
         if n = nfields || (n = 3 && Stdlib.List.nth fs 2 = "fail") then
           Hashtbl.replace tbl (int_of_string (Stdlib.List.nth fs 0), int_of_string (Stdlib.List.nth fs 1)) ()
       done with End_of_file -> ());
      close_in ic
    end) (Sys.readdir outdir);
  tbl

let run_cells ?bounds frames outdir nproc =
  let dn = done_cells outdir in
  let cells = Array.of_list (Stdlib.List.filter (fun c -> not (Hashtbl.mem dn c))
                (Stdlib.List.init (12 * 256) (fun n -> (n / 256, n mod 256)))) in
  Printf.eprintf "%d cells recorded, %d to do\n%!" (Hashtbl.length dn) (Array.length cells);
  let stamp = int_of_float (Unix.time ()) in
  let kids = Stdlib.List.init nproc (fun c ->
    match Unix.fork () with
    | 0 ->
      let oc = open_out_gen [Open_append; Open_creat] 0o644 (Printf.sprintf "%s/cells_%d_%d.txt" outdir stamp c) in
      Array.iteri (fun n (k, j) ->
        if n mod nproc = c then begin
          let (sc, hc, a, b) = cell k j in
          let (wd, wi) = frames.(k) in
          let t0 = Unix.gettimeofday () in
          let res = match bounds with
            | None -> C3Ext.cellr sc hc a b kn 4 wd wi
            | Some (bm, bmm, bq) -> C3Ext.cellr2 sc hc a b kn 4 wd wi bm bmm bq in
          let line = match res with
            | Some rr -> String.concat " " (Stdlib.List.map range_str rr)
            | None -> "fail" in
          Printf.fprintf oc "%d %d %s\n" k j line; flush oc;
          Printf.eprintf "cell %d %d %.1f s%s\n" k j (Unix.gettimeofday () -. t0) (if line = "fail" then " FAIL" else "");
          flush stderr
        end) cells;
      close_out oc; Unix._exit 0
    | pid -> pid) in
  Stdlib.List.iter (fun pid -> ignore (Unix.waitpid [] pid)) kids

(* The assembly: frames as dyadics, the exponents, the recorded ranges and the
   approximate inverse R of the reference system, 182 rows of hexadecimal
   numbers, read into 13 x 13 blocks of 14 x 14 dyadics. *)
let read_frames_raw file =
  let ic = open_in file in
  let readm () = Array.init 14 (fun _ ->
    Array.of_list (Stdlib.List.map float_of_string
      (Stdlib.List.filter (fun s -> s <> "") (String.split_on_char ' ' (input_line ic))))) in
  let dl m = Array.to_list (Array.map (fun row -> Array.to_list (Array.map dyad_of row)) m) in
  let fr = Stdlib.List.init 12 (fun _ -> let w = readm () in let d = readm () in (dl w, dl d)) in
  close_in ic; fr

let fields line = Stdlib.List.filter (fun s -> s <> "") (String.split_on_char ' ' line)

let rec pairs = function
  | a :: b :: tl -> (if a = "nan" then Float.Inan else Float.Ibnd (float_of_string a, float_of_string b)) :: pairs tl
  | _ -> []

let rec chunks n l = if l = [] then [] else
  let rec take k l acc = if k = 0 then (Stdlib.List.rev acc, l) else
    (match l with x :: tl -> take (k - 1) tl (x :: acc) | [] -> (Stdlib.List.rev acc, [])) in
  let (a, b) = take n l [] in a :: chunks n b

(* The reference steps of every segment: step 16 j + q is range q of cell j. *)
let read_cells outdir =
  let tbl = Hashtbl.create 65536 in
  Array.iter (fun name ->
    if String.length name > 6 && String.sub name 0 6 = "cells_" then begin
      let ic = open_in (Filename.concat outdir name) in
      (try while true do
         match fields (input_line ic) with
         | k :: j :: rest when Stdlib.List.length rest = nsub * 392 ->
           let k = int_of_string k and j = int_of_string j in
           Stdlib.List.iteri (fun q r -> Hashtbl.replace tbl (k, nsub * j + q) (chunks 14 r))
             (chunks 196 (pairs rest))
         | _ -> ()
       done with End_of_file -> ());
      close_in ic
    end) (Sys.readdir outdir);
  Printf.eprintf "%d reference steps read\n%!" (Hashtbl.length tbl);
  Stdlib.List.init 12 (fun k -> Stdlib.List.init (256 * nsub) (fun i ->
    match Hashtbl.find_opt tbl (k, i) with Some r -> r | None -> []))

let read_start file =
  let ic = open_in file in let l = input_line ic in close_in ic;
  chunks 14 (pairs (fields l))

let read_es file =
  let ic = open_in file in let l = input_line ic in close_in ic;
  Stdlib.List.map (fun s -> zi (int_of_string s)) (fields l)

let read_r file =
  let ic = open_in file in
  let rows = Array.init 182 (fun _ -> Array.of_list (Stdlib.List.map float_of_string (fields (input_line ic)))) in
  close_in ic;
  Stdlib.List.init 13 (fun bi -> Stdlib.List.init 13 (fun bk ->
    Stdlib.List.init 14 (fun r -> Stdlib.List.init 14 (fun c -> dyad_of rows.(14 * bi + r).(14 * bk + c)))))

let bnd_str = function Float.Ibnd (a, b) -> Printf.sprintf "[%.6e, %.6e]" a b | Float.Inan -> "nan"

let () =
  match Sys.argv with
  | [| _; "assemble"; ffile; esfile; celldir; sfile; rfile |] ->
    let frames = read_frames_raw ffile and es = read_es esfile and cells = read_cells celldir
    and rs = read_start sfile and rd = read_r rfile in
    let t0 = Unix.gettimeofday () in
    let ((th0, th1), th2) = C3Ext.asm_th frames es cells rs rd in
    Printf.printf "th0 %s  th1 %s  th2 %s  (%.1f s)\n%!" (bnd_str th0) (bnd_str th1) (bnd_str th2) (Unix.gettimeofday () -. t0);
    let ok = C3Ext.asm frames es cells rs rd in
    Printf.printf "assemble3d: %b  (%.1f s)\n%!" ok (Unix.gettimeofday () -. t0);
    if not ok then
      Printf.printf "checks: %s\n" (String.concat " " (Stdlib.List.map string_of_bool (C3Ext.asm_diag frames es cells rs rd)))
  | _ -> ()

let upper_of = function Float.Ibnd (_, b) -> b | Float.Inan -> Stdlib.Float.nan

(* Test modes: the ball tables and the consistency bound of the nine points
   over cell C, with their times. *)
let () =
  match Sys.argv with
  | [| _; "ballt"; c; rx; rd |] ->
    let c = int_of_string c in
    Stdlib.List.iter (fun (r, kp) ->
      let t0 = Unix.gettimeofday () in
      let s = match C3Ext.ballt (zi 1, zi (int_of_string rx)) (zi 1, zi (int_of_string rd)) (zi 1, zi (-16)) r kp c with
        | Some t -> Printf.sprintf "max %.3e" (Stdlib.List.fold_left (fun m row ->
                      Stdlib.List.fold_left (fun m x -> Stdlib.Float.max m (upper_of x)) m row) 0.0 t)
        | None -> "fail" in
      Printf.printf "ball r=%b kp=%d c=%d %s (%.2f s)\n%!" r kp c s (Unix.gettimeofday () -. t0))
      [(true, 0); (true, 1); (true, 2); (true, 3); (true, 4); (false, 0); (false, 1); (false, 2); (false, 3)];
    exit 0
  | [| _; "const"; c |] ->
    let c = int_of_string c in
    Stdlib.List.iter (fun (r, kp) ->
      let t0 = Unix.gettimeofday () in
      let s = match C3Ext.const (zi 1, zi (-16)) r kp c with
        | Some b -> Printf.sprintf "bound %.3e" (upper_of b)
        | None -> "fail" in
      Printf.printf "cons r=%b kp=%d c=%d %s (%.2f s)\n%!" r kp c s (Unix.gettimeofday () -. t0))
      [(true, 0); (true, 1); (true, 2); (true, 3); (true, 4); (false, 0); (false, 1); (false, 2); (false, 3)];
    exit 0
  | [| _; "mbprobe"; k; j |] ->
    let (sc, hc, a, b) = cell (int_of_string k) (int_of_string j) in
    let t0 = Unix.gettimeofday () in
    (match C3Ext.mbprobe sc hc a b kn with
     | Some ((bmi, bm), bq) ->
       Printf.printf "cell %s %s: |M^-1| <= %.4e  |M| <= %.4e  |Q| <= %.4e  (%.1f s)\n%!" k j
         (upper_of bmi) (upper_of bm) (upper_of bq) (Unix.gettimeofday () -. t0)
     | None -> Printf.printf "cell %s %s: fail\n%!" k j);
    exit 0
  | _ -> ()

(* The ball check of every point over every cell, the bound K = 2^KE and the
   radii 2^RXE, 2^RDE over h in [0, 2^HHE]; NPROC children take the 1728
   (r, kp, c) in turn, each exiting 1 on a failure. *)
let run_ball kbe rxe rde hhe nproc =
  let items = Array.of_list (Stdlib.List.concat (Stdlib.List.init 192 (fun c ->
                Stdlib.List.map (fun (r, kp) -> (r, kp, c))
                  [(true, 0); (true, 1); (true, 2); (true, 3); (true, 4); (false, 0); (false, 1); (false, 2); (false, 3)]))) in
  let dy e = (zi 1, zi e) in
  let kids = Stdlib.List.init nproc (fun ch ->
    match Unix.fork () with
    | 0 ->
      let bad = ref 0 in
      Array.iteri (fun n (r, kp, c) ->
        if n mod nproc = ch then begin
          let ok = C3Ext.ballc (dy kbe) (dy rxe) (dy rde) (dy hhe) r kp c in
          if not ok then (incr bad; Printf.printf "ball FAIL r=%b kp=%d c=%d\n%!" r kp c)
        end) items;
      Unix._exit (if !bad = 0 then 0 else 1)
    | pid -> pid) in
  let fails = Stdlib.List.fold_left (fun acc pid ->
    match Unix.waitpid [] pid with
    | (_, Unix.WEXITED 0) -> acc
    | _ -> acc + 1) 0 kids in
  Printf.printf "ball verdict over %d checks: %b\n%!" (Array.length items) (fails = 0)

(* The consistency check of every point over every cell, the bound C = 2^CE
   on the second derivative along h over h in [-2^HHE, 2^HHE]; NPROC children
   take the 1728 (r, kp, c) in turn, each exiting 1 on a failure. *)
let run_cons2 ce hhe nproc =
  let items = Array.of_list (Stdlib.List.concat (Stdlib.List.init 192 (fun c ->
                Stdlib.List.map (fun (r, kp) -> (r, kp, c))
                  [(true, 0); (true, 1); (true, 2); (true, 3); (true, 4); (false, 0); (false, 1); (false, 2); (false, 3)]))) in
  let dy e = (zi 1, zi e) in
  let kids = Stdlib.List.init nproc (fun ch ->
    match Unix.fork () with
    | 0 ->
      let bad = ref 0 in
      Array.iteri (fun n (r, kp, c) ->
        if n mod nproc = ch then begin
          let ok = C3Ext.cons2c (dy ce) (dy hhe) r kp c in
          if not ok then (incr bad; Printf.printf "cons FAIL r=%b kp=%d c=%d\n%!" r kp c)
        end) items;
      Unix._exit (if !bad = 0 then 0 else 1)
    | pid -> pid) in
  let fails = Stdlib.List.fold_left (fun acc pid ->
    match Unix.waitpid [] pid with
    | (_, Unix.WEXITED 0) -> acc
    | _ -> acc + 1) 0 kids in
  Printf.printf "consistency verdict over %d checks: %b\n%!" (Array.length items) (fails = 0)

(* The bounds of the nine points over the cells C0 <= c < C1, h in [-2^HHE, 2^HHE]. *)
let cons2_bounds c0 c1 hhe =
  for c = c0 to c1 - 1 do
    Stdlib.List.iter (fun (r, kp) ->
      let t0 = Unix.gettimeofday () in
      let s = match C3Ext.cons2t (zi 1, zi hhe) r kp c with
        | Some b -> Printf.sprintf "%.3e" (upper_of b)
        | None -> "fail" in
      Printf.printf "cons2 r=%b kp=%d c=%d %s (%.2f s)\n%!" r kp c s (Unix.gettimeofday () -. t0))
      [(true, 0); (true, 1); (true, 2); (true, 3); (true, 4); (false, 0); (false, 1); (false, 2); (false, 3)]
  done

let () =
  match Sys.argv with
  | [| _; "cons2"; ce; hhe; np |] ->
    run_cons2 (int_of_string ce) (int_of_string hhe) (int_of_string np); exit 0
  | [| _; "cons2t"; c0; c1; hhe |] ->
    cons2_bounds (int_of_string c0) (int_of_string c1) (int_of_string hhe); exit 0
  | _ -> ()

let () =
  match Sys.argv with
  | [| _; "ball"; kbe; rxe; rde; hhe; np |] ->
    run_ball (int_of_string kbe) (int_of_string rxe) (int_of_string rde) (int_of_string hhe) (int_of_string np); exit 0
  | [| _; "cells2"; ffile; outdir; np; bme; bmme; bqe |] ->
    let dy s = (zi 1, zi (int_of_string s)) in
    run_cells ~bounds:(dy bme, dy bmme, dy bqe) (read_frames ffile) outdir (int_of_string np); exit 0
  | _ -> ()

let () =
  match Sys.argv with
  | [| _; "assemble"; _; _; _; _; _ |] -> ()
  | [| _; "cells"; ffile; outdir; np |] -> run_cells (read_frames ffile) outdir (int_of_string np)
  | [| _; "start"; ffile; out |] ->
    let frames = read_frames ffile in
    let (_, wi0) = frames.(0) in
    let t0 = Unix.gettimeofday () in
    let oc = open_out out in
    (match C3Ext.startr (zi 1, zi (-17)) (zi 1, zi (-17)) kn wi0 with
     | Some r -> output_string oc (range_str r ^ "\n")
     | None -> output_string oc "fail\n");
    close_out oc;
    Printf.eprintf "start %.1f s\n" (Unix.gettimeofday () -. t0)
  | _ -> prerr_endline "usage: main cells FRAMES OUTDIR NPROC | main start FRAMES OUT | main assemble FRAMES ES CELLDIR START R"; exit 2
