(* Run one part of the certificate KFinal.cert_ok on its data:

     cert MODE E0DATA SRCDATA JETSDATA FINDATA FSCAL WORKERS OFILE TRFILE

   MODE is head, src, e0, jets, twist or fin. Every mode prints the digests of
   the data files it reads. head prints cert_head; src computes run_src once,
   writes the enclosures it returns to OFILE, reads them back as O and prints
   check_src_with (run_src) O; e0 and jets print run_E0 and run_jets; twist
   computes run_twist once, writes it to TRFILE, reads it back as TR and prints
   check_twist_with (run_twist) TR; fin reads O and TR and prints check_fin O TR
   with each of its conditions. The grid parts read neither FSCAL nor the
   enclosures; the certificate holds when all six verdicts are true on the same
   files. *)

let tokens file =
  let ic = open_in file in
  let toks = ref [] in
  (try while true do
     let line = input_line ic in
     Stdlib.List.iter (fun s -> if s <> "" then toks := s :: !toks) (String.split_on_char ' ' (String.trim line))
   done with End_of_file -> ());
  close_in ic;
  ref (Stdlib.List.rev !toks)

let reader file =
  let toks = tokens file in
  let next () = match !toks with t :: r -> toks := r; t | [] -> failwith (file ^ ": data ended early") in
  let finish () = match !toks with [] -> () | _ -> failwith (file ^ ": data longer than its layout") in
  let nat () = int_of_string (next ()) in
  let z () = Big_int_Z.big_int_of_string (next ()) in
  (next, finish, nat, z)

let rows z a b = Stdlib.List.init (2 * a + 1) (fun _ -> Stdlib.List.init (2 * b + 1) (fun _ -> z ()))

let srcs_of nat z =
  let ns = nat () in
  Stdlib.List.init ns (fun _ -> let p1 = z () in let p2 = z () in let p3 = z () in
                        let d1 = z () in let d2 = z () in let d3 = z () in (((p1, p2), p3), ((d1, d2), d3)))

let iv z () = let lo = z () in let hi = z () in Some (lo, hi)

let read_e0 file =
  let (_, finish, nat, z) = reader file in
  let pn = nat () in let n1 = nat () in let m = nat () in let k1 = nat () in let k2 = nat () in
  let d = nat () in let km = nat () in let kn = nat () in let kmu = nat () in let knu = nat () in
  let kmg = nat () in let kng = nat () in
  let s0 = z () in
  let rr = rows z km kn in let rz = rows z km kn in let ru = rows z kmu knu in let rg = rows z kmg kng in
  let ssrc = z () in
  let srcs = srcs_of nat z in
  let a = z () in let b = z () in
  let trig = Stdlib.List.init 6 (fun _ -> iv z ()) in
  let ex = Stdlib.List.init 7 (fun _ -> iv z ()) in
  let bd = Stdlib.List.init 8 (fun _ -> iv z ()) in
  finish ();
  KCertExt.mke0 pn n1 m k1 k2 d km kn kmu knu kmg kng s0 rr rz ru rg ssrc srcs a b trig ex bd

let read_src file =
  let (_, finish, nat, z) = reader file in
  let pn = nat () in let km = nat () in let kn = nat () in let kr1 = nat () in let kr2 = nat () in
  let n1s = nat () in let n2s = nat () in let ky1 = nat () in let ky2 = nat () in
  let kmu = nat () in let knu = nat () in let kmg = nat () in let kng = nat () in
  let s0 = z () in let sy = z () in let ssrc = z () in
  let rr = rows z km kn in let rz = rows z km kn in let ru = rows z kmu knu in let rg = rows z kmg kng in
  let ns = nat () in
  let srcs = Stdlib.List.init ns (fun _ -> let p1 = z () in let p2 = z () in let p3 = z () in
                                   let d1 = z () in let d2 = z () in let d3 = z () in (((p1, p2), p3), ((d1, d2), d3))) in
  let seeds = Stdlib.List.init ns (fun _ ->
    Stdlib.List.init (2 * ky1 + 1) (fun _ -> Stdlib.List.init (2 * ky2 + 1) (fun _ -> let c = z () in let s = z () in (c, s)))) in
  let a = z () in let b = z () in
  let trig = Stdlib.List.init 4 (fun _ -> iv z ()) in
  let ex = Stdlib.List.init 6 (fun _ -> iv z ()) in
  let cl = Stdlib.List.init 4 (fun _ -> iv z ()) in
  finish ();
  KCertExt.mksd pn km kn kr1 kr2 n1s n2s ky1 ky2 kmu knu kmg kng s0 sy ssrc rr rz ru rg srcs seeds a b trig ex cl

let read_jets file =
  let (_, finish, nat, z) = reader file in
  let pn = nat () in let n1 = nat () in let m = nat () in let k1 = nat () in let k2 = nat () in let d = nat () in
  let km = nat () in let kn = nat () in let kj1 = nat () in let kj2 = nat () in
  let s0 = z () in let sj = z () in
  let rr = rows z km kn in let rz = rows z km kn in
  let rj = Stdlib.List.init 9 (fun _ -> rows z kj1 kj2) in
  let ssrc = z () in
  let srcs = srcs_of nat z in
  let trig = Stdlib.List.init 6 (fun _ -> iv z ()) in
  let ex = Stdlib.List.init 7 (fun _ -> iv z ()) in
  let ims = Stdlib.List.init 9 (fun _ -> iv z ()) in
  let ibs = Stdlib.List.init 9 (fun _ -> iv z ()) in
  finish ();
  KCertExt.mkjd pn n1 m k1 k2 d km kn kj1 kj2 s0 sj rr rz rj ssrc srcs trig ex ims ibs

(* The grid parameters (KFinal.findata, in its field order): w0 d0 w1 as
   rationals "num den", the claims Mw (4), B (4), JM (9) and JB (9) as
   rationals, Kmb Knb, the rows of b, and N1t Mt NP NT NE. *)
let read_fd file =
  let (_, finish, nat, z) = reader file in
  let q () = let n = z () in let d = z () in (n, d) in
  let w0 = q () in let d0 = q () in let w1 = q () in
  let mw = Stdlib.List.init 4 (fun _ -> q ()) in
  let b = Stdlib.List.init 4 (fun _ -> q ()) in
  let jm = Stdlib.List.init 9 (fun _ -> q ()) in
  let jb = Stdlib.List.init 9 (fun _ -> q ()) in
  let kmb = nat () in let knb = nat () in
  let rb = rows z kmb knb in
  let n1t = nat () in let mt = nat () in let np = nat () in let nt = nat () in let ne = nat () in
  finish ();
  KCertExt.mkfd w0 d0 w1 mw b jm jb kmb knb rb n1t mt np nt ne

(* The scalar parameters (KFinal.fscal, in its field order): fourteen rationals. *)
let read_fs file =
  let (_, finish, _, z) = reader file in
  let q () = let n = z () in let d = z () in (n, d) in
  let r = q () in let eps = q () in let delta = q () in
  let a0 = q () in let g0 = q () in let n0 = q () in let t0 = q () in let tau0 = q () in
  let xa = q () in let xg = q () in let xn = q () in let xb = q () in let xtm = q () in let xtau = q () in
  finish ();
  KCertExt.mkfs r eps delta a0 g0 n0 t0 tau0 xa xg xn xb xtm xtau

let write_ivs file l =
  let oc = open_out file in
  Printf.fprintf oc "%d\n" (Stdlib.List.length l);
  Stdlib.List.iter (function
    | Some (lo, hi) -> Printf.fprintf oc "%s %s\n" (Big_int_Z.string_of_big_int lo) (Big_int_Z.string_of_big_int hi)
    | None -> Printf.fprintf oc "none\n") l;
  close_out oc

let read_ivs file =
  let ic = open_in file in
  let n = int_of_string (String.trim (input_line ic)) in
  let l = Stdlib.List.init n (fun _ ->
    match String.split_on_char ' ' (String.trim (input_line ic)) with
    | [lo; hi] -> Some (Big_int_Z.big_int_of_string lo, Big_int_Z.big_int_of_string hi)
    | _ -> None) in
  close_in ic;
  l

let f x = Big_int_Z.float_of_big_int x /. (2.0 ** 192.0)
let show name = function
  | Some (lo, hi) -> Printf.printf "  %s in [%.9e, %.9e]\n" name (f lo) (f hi)
  | None -> Printf.printf "  %s: no enclosure\n" name
let verdict name b t0 = Printf.printf "%s: %s (%.1f s)\n%!" name (if b then "true" else "false") (Unix.gettimeofday () -. t0)

let () =
  let mode = Sys.argv.(1) in
  let fe0 = Sys.argv.(2) and fsrc = Sys.argv.(3) and fjets = Sys.argv.(4) and ffd = Sys.argv.(5) in
  let ffs = Sys.argv.(6) in
  Par.nproc := int_of_string Sys.argv.(7);
  let fo = Sys.argv.(8) and ftr = Sys.argv.(9) in
  let uses_fs = (mode = "head" || mode = "fin") in
  Stdlib.List.iter (fun file -> Printf.printf "data %s md5 %s\n" file (Digest.to_hex (Digest.file file)))
    ([fe0; fsrc; fjets; ffd] @ (if uses_fs then [ffs] else []) @ (if mode = "fin" then [fo; ftr] else []));
  let t0 = Unix.gettimeofday () in
  let ed = read_e0 fe0 in let sd = read_src fsrc in let jd = read_jets fjets in let fd = read_fd ffd in
  Printf.printf "read (%.1f s)\n%!" (Unix.gettimeofday () -. t0);
  let t0 = Unix.gettimeofday () in
  match mode with
  | "head" -> verdict "cert_head" (KCertExt.head ed sd jd fd (read_fs ffs)) t0
  | "src" ->
    let r = KCertExt.src sd fd in
    write_ivs fo (snd r);
    Printf.printf "run_src: flag %b, %d enclosures written to %s\n" (fst r) (Stdlib.List.length (snd r)) fo;
    Stdlib.List.iteri (fun i x -> if i < 13 then show (Printf.sprintf "out %d" i) x) (snd r);
    verdict "check_src" (KCertExt.src_with r (read_ivs fo)) t0
  | "e0" -> verdict "run_E0" (KCertExt.e0 ed sd fd) t0
  | "jets" -> verdict "run_jets" (KCertExt.jets sd jd fd) t0
  | "twist" ->
    let t = KCertExt.twist sd jd fd in
    write_ivs ftr t;
    Stdlib.List.iteri (fun i x -> show (Stdlib.List.nth ["|N_R|"; "|N_Z|"; "|kmln_R|"; "|kmln_Z|"; "|T_fin|"; "mean T_fin"] i) x) t;
    verdict "check_twist" (KCertExt.twist_with t (read_ivs ftr)) t0
  | "fin" ->
    let fs = read_fs ffs in
    let o = read_ivs fo and tr = read_ivs ftr in
    let (parts, (bools, vals)) = KCertExt.fin_diag sd jd fd fs o tr in
    Stdlib.List.iteri (fun i b -> Printf.printf "  part %d: %b\n" i b) parts;
    Stdlib.List.iteri (fun i b -> if not b then Printf.printf "  scalar condition %d fails\n" i) bools;
    Printf.printf "  scalar conditions: %d of %d hold\n" (Stdlib.List.length (Stdlib.List.filter (fun b -> b) bools))
      (Stdlib.List.length bools);
    Stdlib.List.iteri (fun i x ->
      show (Stdlib.List.nth ["thU"; "eU"; "eg"; "eN"; "nNf"; "nkmf"; "eDV"; "nDVf"; "cL"; "ekm"; "nkm"; "eT"; "epsx";
                             "kE"; "kP"; "kT"; "kdA"; "kdG"; "kdN"; "kU"; "kdW"; "kW"; "bBP"; "bS1"; "bDV"; "bMV";
                             "bM2"; "LBP"; "bLD"] i) x) vals;
    verdict "check_fin" (KCertExt.fin sd jd fd fs o tr) t0
  | _ -> failwith "mode: head, src, e0, jets, twist or fin"
