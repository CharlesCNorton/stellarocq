(* Run the escape certificate KLohner.check_lescape on its data:

     esc MODE SRCDATA ESCDATA WORKERS

   SRCDATA is the source data of the KAM certificate (kam/main.ml reads it
   whole); the escape data takes from it the field period, the scale of the
   sources and the sources, so the two certificates speak of one coil field.
   ESCDATA holds M, J, the scale sb, R1, R_D and R_D2, then the number of
   boxes and per box its ends at 2^-sb and its fuel. MODE check prints
   check_lescape; MODE boxes prints box_ok for each box; MODE trace:K follows
   the chain of box K step by step through the extracted first_step and
   beyond, printing its angle and hull every hundred steps, as a diagnostic
   whose output is not a verdict. Every mode prints the digests of the files
   first. *)

let reader file =
  let ic = open_in file in
  let toks = ref [] in
  let fill () =
    let rec go () =
      match !toks with
      | [] ->
        let line = input_line ic in
        toks := Stdlib.List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.trim line));
        go ()
      | _ -> () in
    go () in
  let next () =
    (try fill () with End_of_file -> failwith (file ^ ": data ended early"));
    match !toks with t :: r -> toks := r; t | [] -> assert false in
  let rest_empty () =
    (try fill (); false with End_of_file -> true) in
  let nat () = int_of_string (next ()) in
  let z () = Big_int_Z.big_int_of_string (next ()) in
  (nat, z, rest_empty, fun () -> close_in ic)

(* The source data up to its sources: the layout of kam/main.ml's read_src. *)
let read_srcs file =
  let (nat, z, _, close) = reader file in
  let pn = nat () in let km = nat () in let kn = nat () in let _kr1 = nat () in let _kr2 = nat () in
  let _n1s = nat () in let _n2s = nat () in let _ky1 = nat () in let _ky2 = nat () in
  let kmu = nat () in let knu = nat () in let kmg = nat () in let kng = nat () in
  let _s0 = z () in let _sy = z () in let ssrc = z () in
  let skip a b = for _ = 1 to (2 * a + 1) * (2 * b + 1) do ignore (z ()) done in
  skip km kn; skip km kn; skip kmu knu; skip kmg kng;
  let ns = nat () in
  let srcs = Stdlib.List.init ns (fun _ -> let p1 = z () in let p2 = z () in let p3 = z () in
                                   let d1 = z () in let d2 = z () in let d3 = z () in (((p1, p2), p3), ((d1, d2), d3))) in
  close ();
  (pn, ssrc, srcs)

let read_esc file =
  let (nat, z, rest_empty, close) = reader file in
  let m = nat () in let j = nat () in
  let sb = z () in let r1 = z () in let rd = z () in let rd2 = z () in
  let nb = nat () in
  let boxes = Stdlib.List.init nb (fun _ -> let ra = z () in let rb = z () in let fuel = nat () in ((ra, rb), fuel)) in
  if not (rest_empty ()) then failwith (file ^ ": data longer than its layout");
  close ();
  (m, j, sb, r1, rd, rd2, boxes)

let bounds = function Float.Ibnd (a, b) -> (a, b) | Float.Inan -> (nan, nan)

let trace (d : KLohner.lescdata) k =
  let ((ra, rb), fuel) = Stdlib.List.nth d.KLohner.le_boxes k in
  let p = d.KLohner.le_P and j = d.KLohner.le_J and sb = d.KLohner.le_sb in
  let ss = KLohner.src_i d.KLohner.le_ssrc d.KLohner.le_srcs and hu = KLohner.iunit d.KLohner.le_M j in
  let rd = FloatRI.FI.of_q d.KLohner.le_RD sb and rd2 = FloatRI.FI.of_q d.KLohner.le_RD2 sb in
  let js = Stdlib.List.init (j + 1) (fun i -> i) in
  let u = 8.0 *. atan 1.0 /. (float_of_int d.KLohner.le_M *. 2.0 ** float_of_int j) in
  let t0 = Unix.gettimeofday () in
  let report s n st =
    let (a, b) = bounds (KLohner.hullR st) and (c, e) = bounds (KLohner.hullZ st) in
    Printf.printf "  step %d: phi %.4f R [%.5f, %.5f] Z [%.5f, %.5f] (%.1f s)\n%!" s
      (Big_int_Z.float_of_big_int n *. u) a b c e (Unix.gettimeofday () -. t0) in
  let rec go s n st =
    if KLohner.beyond p hu rd rd2 n st then (report s n st; Printf.printf "trace %d: beyond the region\n" k)
    else if s >= fuel then (report s n st; Printf.printf "trace %d: fuel spent\n" k)
    else match KLohner.first_step p ss hu j n st js with
      | None -> report s n st; Printf.printf "trace %d: no step passes its checks\n" k
      | Some (n', st') -> if s mod 100 = 0 then report s n st; go (s + 1) n' st' in
  go 0 Big_int_Z.zero_big_int (KLohner.init sb ra rb)

let () =
  let mode = Sys.argv.(1) and fsrc = Sys.argv.(2) and fesc = Sys.argv.(3) in
  Par.nproc := int_of_string Sys.argv.(4);
  Stdlib.List.iter (fun file -> Printf.printf "data %s md5 %s\n" file (Digest.to_hex (Digest.file file))) [fsrc; fesc];
  let t0 = Unix.gettimeofday () in
  let (pn, ssrc, srcs) = read_srcs fsrc in
  let (m, j, sb, r1, rd, rd2, boxes) = read_esc fesc in
  let d = EscExt.mk pn m j ssrc srcs sb r1 rd rd2 boxes in
  Printf.printf "read: P %d, %d sources, M %d, J %d, %d boxes (%.1f s)\n%!" pn (Stdlib.List.length srcs) m j
    (Stdlib.List.length boxes) (Unix.gettimeofday () -. t0);
  let t0 = Unix.gettimeofday () in
  match mode with
  | "check" ->
    let b = EscExt.check d in
    Printf.printf "check_lescape: %s (%.1f s)\n%!" (if b then "true" else "false") (Unix.gettimeofday () -. t0)
  | "boxes" ->
    let r = Par.pmap (EscExt.box d) boxes in
    Stdlib.List.iter2 (fun ((ra, rb), fuel) ok ->
      Printf.printf "box %s %s %d: %b\n" (Big_int_Z.string_of_big_int ra) (Big_int_Z.string_of_big_int rb) fuel ok)
      boxes r;
    Printf.printf "boxes: %d of %d hold (%.1f s)\n%!" (Stdlib.List.length (Stdlib.List.filter (fun b -> b) r))
      (Stdlib.List.length r) (Unix.gettimeofday () -. t0)
  | m when String.length m > 6 && String.sub m 0 6 = "trace:" ->
    trace d (int_of_string (String.sub m 6 (String.length m - 6)))
  | _ -> failwith "mode: check, boxes or trace:K"
