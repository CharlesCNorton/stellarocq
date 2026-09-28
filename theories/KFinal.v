(** The certificate of an invariant torus of the coil field.

    The data are the records of three grid checks (the first torus E0: the
    error and the defects of the two seeds; the sources along it; the nine
    field jets), the grid parameters (the strips, the claimed bounds of the
    grid checks, the straightening family b and the grid of the finite twist),
    the scalar parameters (the radius of the ball, the error, the distance
    claimed, the frame and twist bounds and the constants of the iteration),
    and two lists of enclosures, [O] for what the check of the sources returns
    and [TR] for what the grid of the finite twist returns. [cert_ok] is the
    conjunction of six parts: the three grid records describe the same torus,
    sources and seeds and the seeds computed from the parameters are
    admissible ([cert_head]); the check of the sources, whose enclosures [O]
    holds ([check_src]); the first torus ([run_E0]); the jets ([run_jets]);
    the finite twist, whose enclosures [TR] holds ([check_twist]); and the
    scalar conditions over [O] and [TR] ([check_fin]). Only the first and the
    last read the scalar parameters, so the grid parts serve for any of them.
    [cert_ok_torus] turns the verdict into an invariant torus of the coil
    field within the claimed distance of the first torus, by the KAM theorem
    [field_kam_fourier]: a pair of Fourier families on a strip solving the
    invariance equation with the rotation of the data, so a torus carrying
    the field lines of TorusLine.fourier_torus_line. *)

From Coq Require Import ZArith Reals Lra Lia List Bool QArith.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity FourierDFT
  FourierCanon FourierPer FourierSym FourierList FourierModel FourierSupp FourierModelPer KAMVec KAMFin KAMPer
  KAMStep KAMBound KAMUpdate KAMDiff KAMIter Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTaylor
  FieldTotal FieldCrude FieldBall FieldLine FieldConst FieldKAM KCheckErr KFix KCheckKern KEngine KTab KDense KGrid
  KCheckE0 KE0 KSrc KSrcCheck KRef KSrcReal KSrcRun KJets KScal KTwist KTfin KTgrid KFinScal KSeed DiophQ KDioph
  TorusLine.
Import ListNotations.
Local Open Scope R_scope.

(** * Rationals *)

Definition qr (x : Z * Z) : R := IZR (fst x) / IZR (snd x).
Definition qok (x : Z * Z) : bool := (0 <? snd x)%Z.

(** * Equality of data *)

Definition eqb_dec {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if dec x y then true else false.

Lemma eqb_dec_ok {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x y : A) : eqb_dec dec x y = true -> x = y.
Proof. unfold eqb_dec. destruct (dec x y); [auto | discriminate]. Qed.

Definition dec_lz : forall x y : list Z, {x = y} + {x <> y} := list_eq_dec Z.eq_dec.
Definition dec_llz : forall x y : list (list Z), {x = y} + {x <> y} := list_eq_dec dec_lz.
Definition dec_z2 : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition dec_z3 : forall x y : Z * Z * Z, {x = y} + {x <> y}.
Proof. decide equality; first [apply Z.eq_dec | apply dec_z2]. Defined.
Definition dec_src : forall x y : (Z * Z * Z) * (Z * Z * Z), {x = y} + {x <> y}.
Proof. decide equality; apply dec_z3. Defined.
Definition dec_srcs : forall x y : list ((Z * Z * Z) * (Z * Z * Z)), {x = y} + {x <> y} := list_eq_dec dec_src.

(** * The parameters *)

(** The strips, the claims of the grid checks, the family b and the grid of
    the finite twist, which the grid checks read. *)
Record findata := mkfd {
  fd_w0 : Z * Z ; fd_d0 : Z * Z ; fd_w1 : Z * Z ;
  fd_Mw : list (Z * Z) ; fd_B : list (Z * Z) ; fd_JM : list (Z * Z) ; fd_JB : list (Z * Z) ;
  fd_Kmb : nat ; fd_Knb : nat ; fd_rowsB : list (list Z) ;
  fd_N1t : nat ; fd_Mt : nat ; fd_NP : nat ; fd_NT : nat ; fd_NE : nat }.

(** The radius of the ball, the error, the distance claimed, the frame and
    twist bounds and the constants of the iteration, which only the scalar
    check reads. *)
Record fscal := mkfs {
  fs_r : Z * Z ; fs_eps : Z * Z ; fs_delta : Z * Z ;
  fs_A0 : Z * Z ; fs_G0 : Z * Z ; fs_N0 : Z * Z ; fs_T0 : Z * Z ; fs_tau0 : Z * Z ;
  fs_xA : Z * Z ; fs_xG : Z * Z ; fs_xN : Z * Z ; fs_xB : Z * Z ; fs_xTm : Z * Z ; fs_xtau : Z * Z }.

Definition scal_ok (fs : fscal) : bool :=
  forallb qok [fs_r fs; fs_eps fs; fs_delta fs; fs_A0 fs; fs_G0 fs; fs_N0 fs; fs_T0 fs; fs_tau0 fs; fs_xA fs;
               fs_xG fs; fs_xN fs; fs_xB fs; fs_xTm fs; fs_xtau fs].

Definition q0 : Z * Z := (0%Z, 1%Z).

Module Final (J : RI).

Module FS := FinScal J.
Module JC := JetsCheck J.
Module TG := TGrid J.
Module SD := Seeds J.
Module E := FS.SC.SR.E.
Import FS FS.SC FS.SC.SR FS.SC.SR.E.TB FS.SC.SR.E.TB.E FS.SC.SR.E.TB.E.KO.

Definition iqq (x : Z * Z) : J.t := SD.iq (fst x) (snd x).
Definition ten : J.t := J.of_q 10 0.

(** * The seeds from the parameters *)

Section Seeds.

Variable fd : findata.

Definition iw0 : J.t := iqq (fd_w0 fd).
Definition iw1 : J.t := iqq (fd_w1 fd).
Definition id0 : J.t := iqq (fd_d0 fd).
Definition iwd : J.t := J.sub iw0 id0.

(** The arguments of the exponentials, each in [0, 1]. *)
Definition eargs : list J.t :=
  [iw0; J.div iw0 ten; iw1; J.div iw1 ten; iwd; J.div iwd ten; J.div (J.sub iw1 iw0) ten; J.of_q 1 0].

Definition sW0 : J.t := SD.iexp_pos iw0 (fd_NE fd).
Definition sW0k : J.t := SD.iexp_pos (J.div iw0 ten) (fd_NE fd).
Definition sW1 : J.t := SD.iexp_pos iw1 (fd_NE fd).
Definition sW1k : J.t := SD.iexp_pos (J.div iw1 ten) (fd_NE fd).
Definition sW1m : J.t := SD.iexp_neg iw1 (fd_NE fd).
Definition sW1km : J.t := SD.iexp_neg (J.div iw1 ten) (fd_NE fd).
Definition sWd : J.t := SD.iexp_pos iwd (fd_NE fd).
Definition sWdk : J.t := SD.iexp_pos (J.div iwd ten) (fd_NE fd).
Definition sDk : J.t := SD.iexp_neg (J.div (J.sub iw1 iw0) ten) (fd_NE fd).
Definition sE1 : J.t := SD.iexp_pos (J.of_q 1 0) (fd_NE fd).

Definition seeds_ok : bool :=
  forallb (fun X => J.nonneg X && ile X (J.of_q 1 0)) eargs &&
  SD.iexp_pos_flag iw0 (fd_NE fd) && SD.iexp_pos_flag (J.div iw0 ten) (fd_NE fd) &&
  SD.iexp_pos_flag iw1 (fd_NE fd) && SD.iexp_pos_flag (J.div iw1 ten) (fd_NE fd) &&
  SD.iexp_pos_flag iwd (fd_NE fd) && SD.iexp_pos_flag (J.div iwd ten) (fd_NE fd) &&
  SD.iexp_pos_flag (J.of_q 1 0) (fd_NE fd) &&
  qok (fd_w0 fd) && qok (fd_w1 fd) && qok (fd_d0 fd) && ile iw0 iw1.

Definition trig (N : nat) : J.t * J.t := SD.itrig (fd_NP fd) (fd_NT fd) N.

End Seeds.

(** Each enclosure of the first list holds every number the enclosure of the
    second list at its place holds. *)
Fixpoint incl_list (A B : list J.t) : bool :=
  match A, B with
  | [], [] => true
  | X :: A', Y :: B' => J.incl X Y && incl_list A' B'
  | _, _ => false
  end.

(** * The checks on grids *)

Section Runs.

Variables (ed : E.e0data) (sd : srcdata) (jd : JC.jetsdata) (fd : findata) (fs : fscal).

Definition cP : nat := sd_P sd.

Definition claim (L : list (Z * Z)) (i : nat) : J.t := iqq (nth i L q0).

Definition run_src : bool * list J.t :=
  src_check cP (sd_Km sd) (sd_Kn sd) (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd)
    (sd_s0 sd) (sd_sY sd) (sd_ssrc sd) (sd_rowsR sd) (sd_rowsZ sd) (trig fd (sd_N1s sd)) (trig fd (sd_N2s sd))
    (sW0 fd) (sW0k fd) (SD.ipow (sW0k fd) cP) (sW1 fd) (sW1k fd) (SD.ipow (sW1k fd) cP)
    (sd_Kmu sd) (sd_Knu sd) (sd_Kmg sd) (sd_Kng sd) (sd_rowsU sd) (sd_rowsG sd) (E.om_i cP (sd_a sd) (sd_b sd))
    (claim (fd_Mw fd) 0) (claim (fd_Mw fd) 1) (claim (fd_Mw fd) 2) (claim (fd_Mw fd) 3) (sd_srcs sd) (sd_seeds sd).

Definition run_E0 : bool :=
  let N1 := E.e0_N1 ed in let M := E.e0_M ed in let K1 := E.e0_K1 ed in let K2 := E.e0_K2 ed in
  let D := E.e0_D ed in
  fst (E.e0_res cP N1 M K1 K2 D (sd_Km sd) (sd_Kn sd) (sd_Kmu sd) (sd_Knu sd) (sd_Kmg sd) (sd_Kng sd) (sd_s0 sd)
         (sd_rowsR sd) (sd_rowsZ sd) (sd_rowsU sd) (sd_rowsG sd) (E.src_i (sd_ssrc sd) (sd_srcs sd))
         (E.om_i cP (sd_a sd) (sd_b sd)) (trig fd N1) (trig fd M) (trig fd (cP * M))
         (sW0 fd) (sW1m fd) (SD.ipow (sW1m fd) (N1 - K1)) (SD.ipow (sW0k fd) cP) (SD.ipow (sW1km fd) cP)
         (SD.ipow (sW1km fd) (cP * M - cP * K2)) (SD.ipow (sDk fd) (S D))
         (claim (fd_Mw fd) 0) (claim (fd_Mw fd) 1) (claim (fd_Mw fd) 2) (claim (fd_Mw fd) 3)
         (claim (fd_B fd) 0) (claim (fd_B fd) 1) (claim (fd_B fd) 2) (claim (fd_B fd) 3)).

Definition run_jets : bool :=
  let N1 := JC.jd_N1 jd in let M := JC.jd_M jd in let K1 := JC.jd_K1 jd in let K2 := JC.jd_K2 jd in
  let D := JC.jd_D jd in
  JC.check_jets cP N1 M K1 K2 D (sd_Km sd) (sd_Kn sd) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (sd_s0 sd) (JC.jd_sJ jd)
    (sd_rowsR sd) (sd_rowsZ sd) (JC.jd_rowsJ jd) (JC.E.src_i (sd_ssrc sd) (sd_srcs sd))
    (trig fd N1) (trig fd M) (trig fd (cP * M))
    (sW0 fd) (sW1m fd) (SD.ipow (sW1m fd) (N1 - K1)) (SD.ipow (sW0k fd) cP) (SD.ipow (sW1km fd) cP)
    (SD.ipow (sW1km fd) (cP * M - cP * K2)) (SD.ipow (sDk fd) (S D))
    (map (claim (fd_JM fd)) (seq 0 9)) (map (claim (fd_JB fd)) (seq 0 9)).

Definition run_twist : list J.t :=
  TG.tcheck_res cP (fd_N1t fd) (fd_Mt fd) (sd_s0 sd) (JC.jd_sJ jd) (sd_Km sd) (sd_Kn sd) (sd_Kmg sd) (sd_Kng sd)
    (fd_Kmb fd) (fd_Knb fd) (sd_Kmu sd) (sd_Knu sd) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (sd_rowsR sd) (sd_rowsZ sd)
    (sd_rowsG sd) (fd_rowsB fd) (sd_rowsU sd) (JC.jd_rowsJ jd) (trig fd (fd_N1t fd)) (trig fd (fd_Mt fd))
    (E.om_i cP (sd_a sd) (sd_b sd)) (sW0 fd) (SD.ipow (sW0k fd) cP) (sWd fd) (SD.ipow (sWdk fd) cP).

(** The data of the three grid checks agree, with the field period 5 and the
    rotation number 5 (337 + sqrt 5) / 1958. *)
Definition cons_ok : bool :=
  Nat.eqb (sd_P sd) 5 && Z.eqb (sd_a sd) 979 && Z.eqb (sd_b sd) (-337) && Nat.eqb (E.e0_P ed) 5 &&
  Nat.eqb (JC.jd_P jd) 5 &&
  Nat.eqb (E.e0_Km ed) (sd_Km sd) && Nat.eqb (E.e0_Kn ed) (sd_Kn sd) && Z.eqb (E.e0_s0 ed) (sd_s0 sd) &&
  eqb_dec dec_llz (E.e0_rowsR ed) (sd_rowsR sd) && eqb_dec dec_llz (E.e0_rowsZ ed) (sd_rowsZ sd) &&
  Nat.eqb (JC.jd_Km jd) (sd_Km sd) && Nat.eqb (JC.jd_Kn jd) (sd_Kn sd) && Z.eqb (JC.jd_s0 jd) (sd_s0 sd) &&
  eqb_dec dec_llz (JC.jd_rowsR jd) (sd_rowsR sd) && eqb_dec dec_llz (JC.jd_rowsZ jd) (sd_rowsZ sd).

(** The sizes every check assumes. *)
Definition lens_ok (rows : list (list Z)) (Kx Ky : nat) : bool :=
  Nat.eqb (length rows) (length (zrange Kx)) &&
  forallb (fun r => Nat.eqb (length r) (length (pns (Z.of_nat cP) Ky))) rows.

Definition shape_ok : bool :=
  let N1 := E.e0_N1 ed in let M := E.e0_M ed in let K1 := E.e0_K1 ed in let K2 := E.e0_K2 ed in let D := E.e0_D ed in
  let jN1 := JC.jd_N1 jd in let jM := JC.jd_M jd in let jK1 := JC.jd_K1 jd in let jK2 := JC.jd_K2 jd in
  let jD := JC.jd_D jd in
  (Z.leb 0 (sd_s0 sd) && Z.leb 0 (sd_sY sd) && Z.leb 0 (sd_ssrc sd) && Z.leb 0 (JC.jd_sJ jd)) &&
  (lens_ok (sd_rowsR sd) (sd_Km sd) (sd_Kn sd) && lens_ok (sd_rowsZ sd) (sd_Km sd) (sd_Kn sd) &&
   lens_ok (sd_rowsU sd) (sd_Kmu sd) (sd_Knu sd) && lens_ok (sd_rowsG sd) (sd_Kmg sd) (sd_Kng sd) &&
   lens_ok (fd_rowsB fd) (fd_Kmb fd) (fd_Knb fd) &&
   Nat.eqb (length (JC.jd_rowsJ jd)) 9 &&
   forallb (fun rows => lens_ok rows (JC.jd_Kj1 jd) (JC.jd_Kj2 jd)) (JC.jd_rowsJ jd)) &&
  (Nat.leb 4 N1 && Nat.leb 4 M && Nat.ltb D (10 * S K1) && Nat.ltb D (cP * S K2) && Nat.leb K1 N1 &&
   Nat.leb K2 M) &&
  (Nat.leb 4 jN1 && Nat.leb 4 jM && Nat.ltb jD (10 * S jK1) && Nat.ltb jD (cP * S jK2) && Nat.leb jK1 jN1 &&
   Nat.leb jK2 jM) &&
  (Nat.leb 4 (sd_N1s sd) && Nat.leb 4 (sd_N2s sd) &&
   Nat.ltb (2 * K1x (sd_Kr1 sd) (sd_Ky1 sd)) (sd_N1s sd) && Nat.ltb (2 * K2x (sd_Kr2 sd) (sd_Ky2 sd)) (sd_N2s sd)) &&
  (Nat.leb 4 (fd_N1t fd) && Nat.leb 4 (fd_Mt fd) && Nat.leb (fd_Kmb fd) (sd_Kmg sd) && Nat.leb (fd_Knb fd) (sd_Kng sd) &&
   Nat.ltb (2 * bT1 (sd_Km sd) (sd_Kmg sd) (sd_Kmu sd) (JC.jd_Kj1 jd)) (fd_N1t fd) &&
   Nat.ltb (2 * Kfull (Z.of_nat cP) (bT2 (sd_Kn sd) (sd_Kng sd) (sd_Knu sd) (JC.jd_Kj2 jd))) (cP * fd_Mt fd)) &&
  (forallb qok (fd_Mw fd) && forallb qok (fd_B fd) && forallb qok (fd_JM fd) && forallb qok (fd_JB fd) &&
   Nat.eqb (length (fd_Mw fd)) 4 && Nat.eqb (length (fd_B fd)) 4 && Nat.eqb (length (fd_JM fd)) 9 &&
   Nat.eqb (length (fd_JB fd)) 9).

(** * The finite norms on the strip of the iteration and on the wide strip *)

Let P := Z.of_nat cP.

Definition iFR : list (Z * list (Z * (J.t * J.t))) := E.DO.ifam (sd_s0 sd) (zrange (sd_Km sd)) (pns P (sd_Kn sd)) (crows (sd_rowsR sd)).
Definition iFZ : list (Z * list (Z * (J.t * J.t))) := E.DO.ifam (sd_s0 sd) (zrange (sd_Km sd)) (pns P (sd_Kn sd)) (srows (sd_rowsZ sd)).
Definition iFU : list (Z * list (Z * (J.t * J.t))) :=
  E.DO.ifam (sd_s0 sd) (zrange (sd_Kmu sd)) (pns P (sd_Knu sd)) (crows (sd_rowsU sd)).
Definition iFG : list (Z * list (Z * (J.t * J.t))) :=
  E.DO.ifam (sd_s0 sd) (zrange (sd_Kmg sd)) (pns P (sd_Kng sd)) (crows (sd_rowsG sd)).
Definition iFB : list (Z * list (Z * (J.t * J.t))) :=
  E.DO.ifam (sd_s0 sd) (zrange (fd_Kmb fd)) (pns P (fd_Knb fd)) (srows (fd_rowsB fd)).
Definition iFJ (i : nat) : list (Z * list (Z * (J.t * J.t))) :=
  nth i (map (fun x : bool * list (list Z) =>
                E.DO.ifam (JC.jd_sJ jd) (zrange (JC.jd_Kj1 jd)) (pns P (JC.jd_Kj2 jd))
                  (if fst x then crows (snd x) else srows (snd x))) (combine tjpar (JC.jd_rowsJ jd))) [].

Definition inorm (F : list (Z * list (Z * (J.t * J.t)))) (Kx Ky : nat) (Ew EwP : J.t) : J.t :=
  SC.iesum F (E.WA Kx Ew) (E.WB Ky EwP).

Definition NJw0 : list J.t :=
  map (fun i => inorm (iFJ i) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (sW0 fd) (SD.ipow (sW0k fd) cP)) (seq 0 9).
Definition NJw1 : list J.t :=
  map (fun i => inorm (iFJ i) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (sW1 fd) (SD.ipow (sW1k fd) cP)) (seq 0 9).

(** The crude norms of the jets less their finite families on the wide strip,
    from the crude norms of the jets, against the claims of the jets check. *)
Definition jcrude_ok (outs : list J.t) : bool :=
  forallb (fun i => ile (J.add (nth i outs J.zero) (nth i NJw1 J.zero)) (claim (fd_JM fd) i)) (seq 0 9).

(** The triples of bounds of the sources, in order. *)
Fixpoint trips (L : list J.t) : list (J.t * J.t * J.t) :=
  match L with a :: b :: c :: t => (a, b, c) :: trips t | _ => [] end.

Definition fin_ok (outs : list J.t) (TR : list J.t) : bool :=
  let '(NR0, NZ0, RR0) := gnorms cP (sd_Km sd) (sd_Kn sd) (sd_Kr1 sd) (sd_Kr2 sd) (sd_s0 sd) (sd_rowsR sd) (sd_rowsZ sd)
                            (sW0 fd) (SD.ipow (sW0k fd) cP) in
  let IR := iqq (fs_r fs) in
  let res := map (src_final (sd_ssrc sd) NR0 NZ0 RR0 (sW0k fd) IR (J.mul two IR))
                 (combine (sd_srcs sd) (trips (skipn 13 outs))) in
  let Ew0 := sW0 fd in let EwP0 := SD.ipow (sW0k fd) cP in
  Nat.eqb (length (trips (skipn 13 outs))) (length (sd_srcs sd)) && forallb fst res && jcrude_ok outs &&
  fin_scal P IR (iw0 fd) (id0 fd) (iqq (fs_eps fs)) (iqq (fs_delta fs)) (iqq (fs_A0 fs)) (iqq (fs_G0 fs))
    (iqq (fs_N0 fs)) (iqq (fs_T0 fs)) (iqq (fs_tau0 fs)) (iqq (fs_xA fs)) (iqq (fs_xG fs)) (iqq (fs_xN fs))
    (iqq (fs_xB fs)) (iqq (fs_xTm fs)) (iqq (fs_xtau fs)) (sW0k fd) (sE1 fd) (E.om_i cP (sd_a sd) (sd_b sd))
    (J.mul (J.of_q 5 0) (iqq (17%Z, 100%Z)))
    (inorm iFR (sd_Km sd) (sd_Kn sd) Ew0 EwP0) (inorm iFU (sd_Kmu sd) (sd_Knu sd) Ew0 EwP0)
    (inorm iFG (sd_Kmg sd) (sd_Kng sd) Ew0 EwP0) (inorm (E.DO.ifam_dt iFR) (sd_Km sd) (sd_Kn sd) Ew0 EwP0)
    (inorm (E.DO.ifam_dt iFZ) (sd_Km sd) (sd_Kn sd) Ew0 EwP0) (inorm iFB (fd_Kmb fd) (fd_Knb fd) Ew0 EwP0) NJw0
    (claim (fd_B fd) 0) (claim (fd_B fd) 1) (claim (fd_B fd) 2) (claim (fd_B fd) 3) (map (claim (fd_JB fd)) (seq 0 9))
    (nth 0 TR J.zero) (nth 1 TR J.zero) (nth 2 TR J.zero) (nth 3 TR J.zero) (nth 4 TR J.zero) (nth 5 TR J.zero)
    (map snd res).

(** The certificate, in six parts that run separately: the data and the seeds;
    the check of the sources, whose enclosures [O] hold what it returns; the
    first torus; the jets; the finite twist on its grid, whose enclosures [TR]
    hold what it returns; and the scalar conditions over [O] and [TR]. *)
Definition cert_head : bool := cons_ok && shape_ok && seeds_ok fd && scal_ok fs.
Definition check_src_with (r : bool * list J.t) (O : list J.t) : bool := fst r && incl_list O (snd r).
Definition check_src (O : list J.t) : bool := check_src_with run_src O.
Definition check_twist_with (T : list J.t) (TR : list J.t) : bool := incl_list TR T.
Definition check_twist (TR : list J.t) : bool := check_twist_with run_twist TR.
Definition check_fin (O TR : list J.t) : bool := fin_ok O TR.

(** The parts of [fin_ok] and each scalar condition, for the report of a run. *)
Definition fin_diag (outs : list J.t) (TR : list J.t) : list bool * (list bool * list J.t) :=
  let '(NR0, NZ0, RR0) := gnorms cP (sd_Km sd) (sd_Kn sd) (sd_Kr1 sd) (sd_Kr2 sd) (sd_s0 sd) (sd_rowsR sd) (sd_rowsZ sd)
                            (sW0 fd) (SD.ipow (sW0k fd) cP) in
  let IR := iqq (fs_r fs) in
  let res := map (src_final (sd_ssrc sd) NR0 NZ0 RR0 (sW0k fd) IR (J.mul two IR))
                 (combine (sd_srcs sd) (trips (skipn 13 outs))) in
  let Ew0 := sW0 fd in let EwP0 := SD.ipow (sW0k fd) cP in
  ([Nat.eqb (length (trips (skipn 13 outs))) (length (sd_srcs sd)); forallb fst res; jcrude_ok outs],
   fin_report P IR (iw0 fd) (id0 fd) (iqq (fs_eps fs)) (iqq (fs_delta fs)) (iqq (fs_A0 fs)) (iqq (fs_G0 fs))
    (iqq (fs_N0 fs)) (iqq (fs_T0 fs)) (iqq (fs_tau0 fs)) (iqq (fs_xA fs)) (iqq (fs_xG fs)) (iqq (fs_xN fs))
    (iqq (fs_xB fs)) (iqq (fs_xTm fs)) (iqq (fs_xtau fs)) (sW0k fd) (sE1 fd) (E.om_i cP (sd_a sd) (sd_b sd))
    (J.mul (J.of_q 5 0) (iqq (17%Z, 100%Z)))
    (inorm iFR (sd_Km sd) (sd_Kn sd) Ew0 EwP0) (inorm iFU (sd_Kmu sd) (sd_Knu sd) Ew0 EwP0)
    (inorm iFG (sd_Kmg sd) (sd_Kng sd) Ew0 EwP0) (inorm (E.DO.ifam_dt iFR) (sd_Km sd) (sd_Kn sd) Ew0 EwP0)
    (inorm (E.DO.ifam_dt iFZ) (sd_Km sd) (sd_Kn sd) Ew0 EwP0) (inorm iFB (fd_Kmb fd) (fd_Knb fd) Ew0 EwP0) NJw0
    (claim (fd_B fd) 0) (claim (fd_B fd) 1) (claim (fd_B fd) 2) (claim (fd_B fd) 3) (map (claim (fd_JB fd)) (seq 0 9))
    (nth 0 TR J.zero) (nth 1 TR J.zero) (nth 2 TR J.zero) (nth 3 TR J.zero) (nth 4 TR J.zero) (nth 5 TR J.zero)
    (map snd res)).

Definition cert_ok (O TR : list J.t) : bool :=
  cert_head && check_src O && run_E0 && run_jets && check_twist TR && check_fin O TR.

End Runs.

(** * From the certificate to the facts *)

Lemma iqq_ok (x : Z * Z) : qok x = true -> inR (iqq x) (qr x).
Proof. intros H. unfold qok in H. apply Z.ltb_lt in H. exact (SD.iq_ok (fst x) (snd x) H). Qed.

Lemma lens_facts (sd : srcdata) (rows : list (list Z)) (Kx Ky : nat) : lens_ok sd rows Kx Ky = true ->
  length rows = length (zrange Kx) /\ List.Forall (fun r => length r = length (pns (Z.of_nat (cP sd)) Ky)) rows.
Proof.
  unfold lens_ok. intros H. apply andb_prop in H. destruct H as [H1 H2]. apply Nat.eqb_eq in H1.
  split; [exact H1 |]. apply Forall_forall. intros r Hr. rewrite forallb_forall in H2. apply Nat.eqb_eq, H2, Hr.
Qed.

Lemma forallb_nth_qok (L : list (Z * Z)) (i : nat) : forallb qok L = true -> qok (nth i L q0) = true.
Proof.
  intros H. destruct (Nat.lt_ge_cases i (length L)) as [Hi | Hi].
  - rewrite forallb_forall in H. apply H, nth_In, Hi.
  - rewrite nth_overflow by exact Hi. reflexivity.
Qed.

Lemma mbound_max4 (w a b c d : R) (M : mf) :
  nbound w a (mRR M) -> nbound w b (mRZ M) -> nbound w c (mZR M) -> nbound w d (mZZ M) ->
  mbound w (Rmax (Rmax a b) (Rmax c d)) M.
Proof.
  intros A B C D. pose proof (Rmax_l a b). pose proof (Rmax_r a b). pose proof (Rmax_l c d). pose proof (Rmax_r c d).
  pose proof (Rmax_l (Rmax a b) (Rmax c d)). pose proof (Rmax_r (Rmax a b) (Rmax c d)).
  refine (conj _ (conj _ (conj _ _))).
  - apply (nbound_le w a); [lra | exact A].
  - apply (nbound_le w b); [lra | exact B].
  - apply (nbound_le w c); [lra | exact C].
  - apply (nbound_le w d); [lra | exact D].
Qed.

Lemma incl_list_f2 (A B : list J.t) : incl_list A B = true -> Forall2 (fun X Y => forall x, inR Y x -> inR X x) A B.
Proof.
  revert B. induction A as [| X A IH]; intros [| Y B] H; cbn [incl_list] in H; try discriminate; [constructor |].
  apply andb_prop in H. destruct H as [H1 H2]. constructor; [intros x Hx; exact (J.incl_ok X Y x H1 Hx) | exact (IH B H2)].
Qed.

Lemma f2_transfer (A B : list J.t) (xs : list R) :
  Forall2 (fun X Y => forall x, inR Y x -> inR X x) A B -> Forall2 inR B xs -> Forall2 inR A xs.
Proof.
  intros H. revert xs. induction H as [| X Y A B HXY _ IH]; intros xs HB.
  - inversion HB. constructor.
  - inversion HB as [| Y' x B' xs' HY HB']; subst. constructor; [exact (HXY x HY) | exact (IH xs' HB')].
Qed.

Lemma f2_firstn {A B : Type} (Rl : A -> B -> Prop) (n : nat) (l1 : list A) (l2 : list B) :
  Forall2 Rl l1 l2 -> Forall2 Rl (firstn n l1) (firstn n l2).
Proof. intros H. revert n. induction H as [| x y l1 l2 Hxy _ IH]; intros [| n]; cbn [firstn]; constructor; auto. Qed.

Lemma f2_skipn {A B : Type} (Rl : A -> B -> Prop) (n : nat) (l1 : list A) (l2 : list B) :
  Forall2 Rl l1 l2 -> Forall2 Rl (skipn n l1) (skipn n l2).
Proof.
  intros H. revert n. induction H as [| x y l1 l2 Hxy H' IH]; intros [| n]; cbn [skipn]; [constructor | constructor |
    constructor; assumption | apply IH].
Qed.

Lemma trips_ok {A : Type} (L : list J.t) (l : list A) (f g h : A -> R) :
  Forall2 inR L (concat (map (fun a => [f a; g a; h a]) l)) ->
  Forall2 (fun T a => inR (fst (fst T)) (f a) /\ inR (snd (fst T)) (g a) /\ inR (snd T) (h a)) (trips L) l.
Proof.
  revert L. induction l as [| a l IH]; intros L H; cbn [map concat app] in H.
  - inversion H; subst. constructor.
  - inversion H as [| X1 x1 L1 l1 H1 H']; subst. inversion H' as [| X2 x2 L2 l2 H2 H'']; subst.
    inversion H'' as [| X3 x3 L3 l3 H3 H''']; subst. cbn [trips fst snd]. constructor; [auto | apply IH; exact H'''].
Qed.

Lemma src_in_srcl (s sY : Z) (Ky1 Ky2 : nat) (xs : list ((Z * Z * Z) * (Z * Z * Z)))
    (ys : list (list (list (Z * Z)))) :
  (0 <= s)%Z -> length xs = length ys -> E.EO.JO.src_in (E.src_i s xs) (srcl s sY Ky1 Ky2 xs ys).
Proof.
  intros Hs. revert ys. induction xs as [| x xs IH]; intros ys HL; [destruct ys; constructor |].
  destruct ys as [| y ys]; [discriminate |]. unfold srcl, E.src_i in *. cbn [combine map]. constructor.
  - destruct x as [[[p1 p2] p3] [[e1 e2] e3]]. cbn [fst snd E.i3q src_of sp1 sp2 sp3 sd1 sd2 sd3]. unfold inR3.
    unfold dy. split; (split; [| split]); apply inR_q, Hs.
  - apply IH. simpl in HL. lia.
Qed.

Section Sound.

Variables (ed : E.e0data) (sd : srcdata) (jd : JC.jetsdata) (fd : findata) (fs : fscal) (O TR : list J.t).
Hypothesis Hc : cert_ok ed sd jd fd fs O TR = true.

Lemma cert_parts : cons_ok ed sd jd = true /\ shape_ok ed sd jd fd = true /\ seeds_ok fd = true /\
  fst (run_src sd fd) = true /\ run_E0 ed sd fd = true /\ run_jets sd jd fd = true /\
  fin_ok sd jd fd fs O TR = true /\ incl_list O (snd (run_src sd fd)) = true /\
  incl_list TR (run_twist sd jd fd) = true /\ scal_ok fs = true.
Proof.
  pose proof Hc as H.
  unfold cert_ok, cert_head, check_src, check_src_with, check_twist, check_twist_with, check_fin in H.
  repeat rewrite Bool.andb_true_iff in H. tauto.
Qed.

Let Pn := sd_P sd.
Let P := Z.of_nat Pn.

Lemma cons_facts : Pn = 5%nat /\ sd_a sd = 979%Z /\ sd_b sd = (-337)%Z.
Proof.
  destruct cert_parts as [H _]. unfold cons_ok in H. repeat rewrite Bool.andb_true_iff in H.
  assert (H1 : Nat.eqb (sd_P sd) 5 = true) by tauto.
  assert (H2 : Z.eqb (sd_a sd) 979 = true) by tauto.
  assert (H3 : Z.eqb (sd_b sd) (-337) = true) by tauto.
  apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. exact (conj H1 (conj H2 H3)).
Qed.

Lemma HPn : (0 < Pn)%nat. Proof. rewrite (proj1 cons_facts). lia. Qed.

(** The sizes. *)
Lemma shape_facts :
  let N1 := E.e0_N1 ed in let M := E.e0_M ed in let K1 := E.e0_K1 ed in let K2 := E.e0_K2 ed in
  let D := E.e0_D ed in
  let jN1 := JC.jd_N1 jd in let jM := JC.jd_M jd in let jK1 := JC.jd_K1 jd in let jK2 := JC.jd_K2 jd in
  let jD := JC.jd_D jd in
  ((0 <= sd_s0 sd)%Z /\ (0 <= sd_sY sd)%Z /\ (0 <= sd_ssrc sd)%Z /\ (0 <= JC.jd_sJ jd)%Z) /\
  (lens_ok sd (sd_rowsR sd) (sd_Km sd) (sd_Kn sd) = true /\ lens_ok sd (sd_rowsZ sd) (sd_Km sd) (sd_Kn sd) = true /\
   lens_ok sd (sd_rowsU sd) (sd_Kmu sd) (sd_Knu sd) = true /\ lens_ok sd (sd_rowsG sd) (sd_Kmg sd) (sd_Kng sd) = true /\
   lens_ok sd (fd_rowsB fd) (fd_Kmb fd) (fd_Knb fd) = true /\ length (JC.jd_rowsJ jd) = 9%nat /\
   forallb (fun rows => lens_ok sd rows (JC.jd_Kj1 jd) (JC.jd_Kj2 jd)) (JC.jd_rowsJ jd) = true) /\
  ((4 <= N1)%nat /\ (4 <= M)%nat /\ (D < 10 * S K1)%nat /\ (D < Pn * S K2)%nat /\ (K1 <= N1)%nat /\ (K2 <= M)%nat) /\
  ((4 <= jN1)%nat /\ (4 <= jM)%nat /\ (jD < 10 * S jK1)%nat /\ (jD < Pn * S jK2)%nat /\ (jK1 <= jN1)%nat /\
   (jK2 <= jM)%nat) /\
  ((4 <= sd_N1s sd)%nat /\ (4 <= sd_N2s sd)%nat /\ (2 * K1x (sd_Kr1 sd) (sd_Ky1 sd) < sd_N1s sd)%nat /\
   (2 * K2x (sd_Kr2 sd) (sd_Ky2 sd) < sd_N2s sd)%nat) /\
  ((4 <= fd_N1t fd)%nat /\ (4 <= fd_Mt fd)%nat /\ (fd_Kmb fd <= sd_Kmg sd)%nat /\ (fd_Knb fd <= sd_Kng sd)%nat /\
   (2 * bT1 (sd_Km sd) (sd_Kmg sd) (sd_Kmu sd) (JC.jd_Kj1 jd) < fd_N1t fd)%nat /\
   (2 * Kfull (Z.of_nat Pn) (bT2 (sd_Kn sd) (sd_Kng sd) (sd_Knu sd) (JC.jd_Kj2 jd)) < Pn * fd_Mt fd)%nat) /\
  (forallb qok (fd_Mw fd) = true /\ forallb qok (fd_B fd) = true /\ forallb qok (fd_JM fd) = true /\
   forallb qok (fd_JB fd) = true /\ length (fd_Mw fd) = 4%nat /\ length (fd_B fd) = 4%nat /\
   length (fd_JM fd) = 9%nat /\ length (fd_JB fd) = 9%nat).
Proof.
  destruct cert_parts as [_ [H _]]. unfold shape_ok in H. cbv zeta in H |- *. fold Pn in H |- *.
  repeat rewrite Bool.andb_true_iff in H.
  repeat rewrite Z.leb_le in H. repeat rewrite Nat.leb_le in H. repeat rewrite Nat.ltb_lt in H.
  repeat rewrite Nat.eqb_eq in H.
  tauto.
Qed.

(** * The seeds *)

Let w0 := qr (fd_w0 fd).
Let w1 := qr (fd_w1 fd).
Let d0 := qr (fd_d0 fd).

Lemma seeds_parts :
  (forall X, In X (eargs fd) -> (J.nonneg X && ile X (J.of_q 1 0))%bool = true) /\
  SD.iexp_pos_flag (iw0 fd) (fd_NE fd) = true /\ SD.iexp_pos_flag (J.div (iw0 fd) ten) (fd_NE fd) = true /\
  SD.iexp_pos_flag (iw1 fd) (fd_NE fd) = true /\ SD.iexp_pos_flag (J.div (iw1 fd) ten) (fd_NE fd) = true /\
  SD.iexp_pos_flag (iwd fd) (fd_NE fd) = true /\ SD.iexp_pos_flag (J.div (iwd fd) ten) (fd_NE fd) = true /\
  SD.iexp_pos_flag (J.of_q 1 0) (fd_NE fd) = true /\ qok (fd_w0 fd) = true /\ qok (fd_w1 fd) = true /\
  qok (fd_d0 fd) = true /\ ile (iw0 fd) (iw1 fd) = true.
Proof.
  destruct cert_parts as [_ [_ [H _]]]. unfold seeds_ok in H. repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11] H12]. rewrite forallb_forall in H1.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 H12))))))))))).
Qed.

Lemma Hw0i : inR (iw0 fd) w0. Proof. apply iqq_ok, seeds_parts. Qed.
Lemma Hw1i : inR (iw1 fd) w1. Proof. apply iqq_ok, seeds_parts. Qed.
Lemma Hd0i : inR (id0 fd) d0. Proof. apply iqq_ok, seeds_parts. Qed.
Lemma Hwdi : inR (iwd fd) (w0 - d0). Proof. unfold iwd. apply inR_sub; [exact Hw0i | exact Hd0i]. Qed.

Lemma ten_ok (X : J.t) (x : R) : inR X x -> inR (J.div X ten) (x * kappa).
Proof. intros H. unfold kappa. exact (inR_div _ _ _ _ H (inR_Z 10) ltac:(lra)). Qed.

Lemma unit_arg (X : J.t) (x : R) : inR X x -> In X (eargs fd) -> 0 <= x <= 1.
Proof.
  intros Hx HI. destruct seeds_parts as [H _]. specialize (H X HI). apply andb_prop in H. destruct H as [A B].
  split; [exact (inR_nonneg _ _ A Hx) | exact (ile_correct _ _ _ _ B Hx (inR_Z 1))].
Qed.

Ltac earg := unfold eargs; cbn [In]; tauto.

Lemma HEw0 : inR (sW0 fd) (exp w0).
Proof.
  destruct seeds_parts as [_ [F _]].
  exact (SD.iexp_pos_ok (iw0 fd) w0 (fd_NE fd) Hw0i (unit_arg _ _ Hw0i ltac:(earg)) F).
Qed.
Lemma HEwk0 : inR (sW0k fd) (exp (w0 * kappa)).
Proof.
  pose proof (ten_ok _ _ Hw0i) as H. destruct seeds_parts as [_ [_ [F _]]].
  exact (SD.iexp_pos_ok (J.div (iw0 fd) ten) (w0 * kappa) (fd_NE fd) H (unit_arg _ _ H ltac:(earg)) F).
Qed.
Lemma HEw1 : inR (sW1 fd) (exp w1).
Proof.
  destruct seeds_parts as [_ [_ [_ [F _]]]].
  exact (SD.iexp_pos_ok (iw1 fd) w1 (fd_NE fd) Hw1i (unit_arg _ _ Hw1i ltac:(earg)) F).
Qed.
Lemma HEwk1 : inR (sW1k fd) (exp (w1 * kappa)).
Proof.
  pose proof (ten_ok _ _ Hw1i) as H. destruct seeds_parts as [_ [_ [_ [_ [F _]]]]].
  exact (SD.iexp_pos_ok (J.div (iw1 fd) ten) (w1 * kappa) (fd_NE fd) H (unit_arg _ _ H ltac:(earg)) F).
Qed.
Lemma HEw1m : inR (sW1m fd) (exp (- w1)).
Proof. exact (SD.iexp_neg_ok (iw1 fd) w1 (fd_NE fd) Hw1i (unit_arg _ _ Hw1i ltac:(earg))). Qed.
Lemma HEwk1m : inR (sW1km fd) (exp (- (w1 * kappa))).
Proof.
  pose proof (ten_ok _ _ Hw1i) as H.
  exact (SD.iexp_neg_ok (J.div (iw1 fd) ten) (w1 * kappa) (fd_NE fd) H (unit_arg _ _ H ltac:(earg))).
Qed.
Lemma HEwd : inR (sWd fd) (exp (w0 - d0)).
Proof.
  destruct seeds_parts as [_ [_ [_ [_ [_ [F _]]]]]].
  exact (SD.iexp_pos_ok (iwd fd) (w0 - d0) (fd_NE fd) Hwdi (unit_arg _ _ Hwdi ltac:(earg)) F).
Qed.
Lemma HEwdk : inR (sWdk fd) (exp ((w0 - d0) * kappa)).
Proof.
  pose proof (ten_ok _ _ Hwdi) as H. destruct seeds_parts as [_ [_ [_ [_ [_ [_ [F _]]]]]]].
  exact (SD.iexp_pos_ok (J.div (iwd fd) ten) ((w0 - d0) * kappa) (fd_NE fd) H (unit_arg _ _ H ltac:(earg)) F).
Qed.
Lemma HEdk : inR (sDk fd) (exp (- ((w1 - w0) * kappa))).
Proof.
  pose proof (ten_ok _ _ (inR_sub _ _ _ _ Hw1i Hw0i)) as H.
  exact (SD.iexp_neg_ok (J.div (J.sub (iw1 fd) (iw0 fd)) ten) ((w1 - w0) * kappa) (fd_NE fd) H
           (unit_arg _ _ H ltac:(earg))).
Qed.
Lemma HE1 : inR (sE1 fd) (exp 1).
Proof.
  pose proof (inR_Z 1) as H. destruct seeds_parts as [_ [_ [_ [_ [_ [_ [_ [F _]]]]]]]].
  exact (SD.iexp_pos_ok (J.of_q 1 0) 1 (fd_NE fd) H (unit_arg _ _ H ltac:(earg)) F).
Qed.

Lemma HEP (E : J.t) (w : R) : inR E (exp (w * kappa)) -> inR (SD.ipow E Pn) (exp (w * (kappa * INR Pn))).
Proof. intros H. pose proof (SD.ipow_exp E _ Pn H) as A. replace (w * (kappa * INR Pn)) with (INR Pn * (w * kappa)) by ring. exact A. Qed.

Lemma HEPm (E : J.t) (w : R) : inR E (exp (- (w * kappa))) ->
  inR (SD.ipow E Pn) (exp (- (w * (kappa * INR Pn)))).
Proof.
  intros H. pose proof (SD.ipow_exp E _ Pn H) as A.
  replace (- (w * (kappa * INR Pn))) with (INR Pn * - (w * kappa)) by ring. exact A.
Qed.

Lemma HEAt (N1 K1 : nat) : (K1 <= N1)%nat -> inR (SD.ipow (sW1m fd) (N1 - K1)) (exp (- (w1 * (INR N1 - INR K1)))).
Proof.
  intros HK. pose proof (SD.ipow_exp _ _ (N1 - K1) HEw1m) as A. rewrite minus_INR in A by exact HK.
  replace (- (w1 * (INR N1 - INR K1))) with ((INR N1 - INR K1) * - w1) by ring. exact A.
Qed.

Lemma HEBt (M K2 : nat) : (K2 <= M)%nat ->
  inR (SD.ipow (sW1km fd) (Pn * M - Pn * K2)) (exp (- (w1 * (kappa * (INR (Pn * M) - INR Pn * INR K2))))).
Proof.
  intros HK. pose proof (SD.ipow_exp _ _ (Pn * M - Pn * K2) HEwk1m) as A.
  rewrite minus_INR in A by (apply Nat.mul_le_mono_l, HK). rewrite !mult_INR in A. rewrite mult_INR.
  replace (- (w1 * (kappa * (INR Pn * INR M - INR Pn * INR K2))))
    with ((INR Pn * INR M - INR Pn * INR K2) * - (w1 * kappa)) by ring. exact A.
Qed.

Lemma HET (D : nat) : inR (SD.ipow (sDk fd) (S D)) (exp (- ((w1 - w0) * (kappa * INR (S D))))).
Proof.
  pose proof (SD.ipow_exp _ _ (S D) HEdk) as A.
  replace (- ((w1 - w0) * (kappa * INR (S D)))) with (INR (S D) * - ((w1 - w0) * kappa)) by ring. exact A.
Qed.

Lemma Htrig (N : nat) : (4 <= N)%nat -> pinR (trig fd N) (cos (2 * PI / INR N), sin (2 * PI / INR N)).
Proof. intros HN. exact (SD.itrig_ok (fd_NP fd) (fd_NT fd) N HN). Qed.

(** The rotation number. *)
Lemma HOM : inR (E.om_i Pn (sd_a sd) (sd_b sd)) om_w7x.
Proof.
  destruct cons_facts as [E1 [E2 E3]]. unfold Pn in *. rewrite E1, E2, E3.
  unfold E.om_i, om_w7x, beta_w7x, nw. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  apply inR_mul; [exact (inR_Z 5) |].
  replace (- IZR (-337) + sqrt 5) with (IZR (- -337) + sqrt (IZR 5)) by (rewrite opp_IZR; reflexivity).
  replace (2 * IZR 979) with (IZR (2 * 979)) by (rewrite mult_IZR; reflexivity).
  apply inR_div; [| exact (inR_Z (2 * 979)) | apply not_0_IZR; lia].
  apply inR_add; [exact (inR_Z (- -337)) | apply inR_sqrt; [exact (inR_Z 5) | apply IZR_le; lia]].
Qed.

(** * The strips *)

Lemma Hw01 : w0 <= w1.
Proof. destruct seeds_parts as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ F]]]]]]]]]]]. exact (ile_correct _ _ _ _ F Hw0i Hw1i). Qed.

Lemma w_unit : 0 <= w0 <= 1 /\ 0 <= w1 <= 1 /\ 0 <= w0 - d0 <= 1.
Proof.
  refine (conj (unit_arg _ _ Hw0i ltac:(earg)) (conj (unit_arg _ _ Hw1i ltac:(earg)) (unit_arg _ _ Hwdi ltac:(earg)))).
Qed.

(** * The check of the sources *)

Let Km := sd_Km sd.
Let Kn := sd_Kn sd.
Let s0 := sd_s0 sd.
Let rowsR := sd_rowsR sd.
Let rowsZ := sd_rowsZ sd.
Let l := srcl (sd_ssrc sd) (sd_sY sd) (sd_Ky1 sd) (sd_Ky2 sd) (sd_srcs sd) (sd_seeds sd).
Let K0 := K0v P Km Kn s0 rowsR rowsZ.
Let outs := snd (run_src sd fd).
Let fU := dfam s0 (zrange (sd_Kmu sd)) (pns P (sd_Knu sd)) (crows (sd_rowsU sd)).
Let fG := dfam s0 (zrange (sd_Kmg sd)) (pns P (sd_Kng sd)) (crows (sd_rowsG sd)).
Let crude (w : R) := crude_ok P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd)
                       (sd_Ky2 sd) l w.

Lemma claim_ok (L : list (Z * Z)) (i : nat) : forallb qok L = true -> inR (claim L i) (qr (nth i L q0)).
Proof. intros H. unfold claim. apply iqq_ok, forallb_nth_qok, H. Qed.

Lemma fin_ok_true : fin_ok sd jd fd fs O TR = true.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cert_parts))))))). Qed.

Lemma d0w0 : 0 < d0 /\ 6 * d0 < w0.
Proof.
  pose proof fin_ok_true as H. unfold fin_ok in H. set (G := gnorms _ _ _ _ _ _ _ _ _ _) in H.
  destruct G as [[NR0 NZ0] RR0]. cbv beta iota zeta in H.
  unfold fin_scal, fin_pos in H. repeat rewrite Bool.andb_true_iff in H.
  assert (A : J.pos (id0 fd) = true) by tauto.
  assert (B : J.pos (J.sub (iw0 fd) (J.mul (J.of_q 6 0) (id0 fd))) = true) by tauto.
  pose proof (inR_pos _ _ A Hd0i).
  pose proof (inR_pos _ _ B (inR_sub _ _ _ _ Hw0i (inR_mul _ _ _ _ (inR_Z 6) Hd0i))). lra.
Qed.

Lemma lensR : length rowsR = length (zrange Km) /\ List.Forall (fun r => length r = length (pns P Kn)) rowsR.
Proof. destruct shape_facts as [_ [[A _] _]]. exact (lens_facts sd _ _ _ A). Qed.
Lemma lensZ : length rowsZ = length (zrange Km) /\ List.Forall (fun r => length r = length (pns P Kn)) rowsZ.
Proof. destruct shape_facts as [_ [[_ [A _]] _]]. exact (lens_facts sd _ _ _ A). Qed.
Lemma lensU : length (sd_rowsU sd) = length (zrange (sd_Kmu sd)) /\
              List.Forall (fun r => length r = length (pns P (sd_Knu sd))) (sd_rowsU sd).
Proof. destruct shape_facts as [_ [[_ [_ [A _]]] _]]. exact (lens_facts sd _ _ _ A). Qed.
Lemma lensG : length (sd_rowsG sd) = length (zrange (sd_Kmg sd)) /\
              List.Forall (fun r => length r = length (pns P (sd_Kng sd))) (sd_rowsG sd).
Proof. destruct shape_facts as [_ [[_ [_ [_ [A _]]]] _]]. exact (lens_facts sd _ _ _ A). Qed.

Lemma src_facts :
  length (sd_srcs sd) = length (sd_seeds sd) /\
  List.Forall (fun sy => supp (sd_Ky1 sd) (sd_Ky2 sd) (snd sy) /\ is_canon (snd sy)) l /\
  crude w0 /\ crude w1 /\
  nbound w1 (qr (nth 0 (fd_Mw fd) q0)) (errF_R P l om_w7x K0) /\
  nbound w1 (qr (nth 1 (fd_Mw fd) q0)) (errF_Z P l om_w7x K0) /\
  nbound w1 (qr (nth 2 (fd_Mw fd) q0)) (defU P l K0 (cden fU)) /\
  nbound w1 (qr (nth 3 (fd_Mw fd) q0)) (defG P l K0 (cden fG)) /\
  Forall2 inR (firstn 9 outs)
    [tR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tP P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tRR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tRZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tPR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tPZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1] /\
  Forall2 inR (skipn 13 outs)
    (concat (map (fun sy => [THr P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd)
                               (sd_Ky2 sd) w0 sy; MYr (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 sy;
                             feval (snd sy) 0 0]) l)).
Proof.
  destruct shape_facts as [[Hs0 [HsY [Hssrc _]]] [_ [_ [_ [[HN1 [HN2 [HN1x HN2x]]] [_ [HMw _]]]]]]].
  destruct lensR as [LR LRn]. destruct lensZ as [LZ LZn]. destruct lensU as [LU LUn]. destruct lensG as [LG LGn].
  pose proof HOM as Hom. pose proof Hw01 as W01. pose proof d0w0 as [D0 D1].
  assert (Hw1 : 0 < w1) by lra.
  exact (src_check_ok Pn Km Kn (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) s0 (sd_sY sd)
           (sd_ssrc sd) rowsR rowsZ (trig fd (sd_N1s sd)) (trig fd (sd_N2s sd)) (sW0 fd) (sW0k fd)
           (SD.ipow (sW0k fd) Pn) (sW1 fd) (sW1k fd) (SD.ipow (sW1k fd) Pn) (sd_Kmu sd) (sd_Knu sd) (sd_Kmg sd)
           (sd_Kng sd) (sd_rowsU sd) (sd_rowsG sd) (E.om_i Pn (sd_a sd) (sd_b sd))
           (claim (fd_Mw fd) 0) (claim (fd_Mw fd) 1) (claim (fd_Mw fd) 2) (claim (fd_Mw fd) 3) w0 w1 om_w7x
           (qr (nth 0 (fd_Mw fd) q0)) (qr (nth 1 (fd_Mw fd) q0)) (qr (nth 2 (fd_Mw fd) q0)) (qr (nth 3 (fd_Mw fd) q0))
           HPn ltac:(lia) ltac:(lia) HN1x HN2x Hs0 HsY Hssrc LR LZ LU LG LRn LZn LUn LGn (Htrig _ HN1) (Htrig _ HN2)
           Hw1 HEw0 HEwk0 (HEP _ _ HEwk0) HEw1 HEwk1 (HEP _ _ HEwk1) HOM (claim_ok _ 0 HMw) (claim_ok _ 1 HMw)
           (claim_ok _ 2 HMw) (claim_ok _ 3 HMw) (sd_srcs sd) (sd_seeds sd) (proj1 (proj2 (proj2 (proj2 cert_parts))))).
Qed.

(** The enclosures [O] hold the ones the check of the sources returns. *)
Lemma src_facts_O :
  Forall2 inR (firstn 9 O)
    [tR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tP P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tRR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tRZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tPR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tPZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1] /\
  Forall2 inR (skipn 13 O)
    (concat (map (fun sy => [THr P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd)
                               (sd_Ky2 sd) w0 sy; MYr (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 sy;
                             feval (snd sy) 0 0]) l)).
Proof.
  destruct src_facts as [_ [_ [_ [_ [_ [_ [_ [_ [F9 F13]]]]]]]]].
  pose proof (incl_list_f2 _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cert_parts))))))))) as HI.
  split; eapply f2_transfer; [apply f2_firstn, HI | exact F9 | apply f2_skipn, HI | exact F13].
Qed.

Let HN1x : (2 * K1x (sd_Kr1 sd) (sd_Ky1 sd) < sd_N1s sd)%nat.
Proof. destruct shape_facts as [_ [_ [_ [_ [[_ [_ [A _]]] _]]]]]. exact A. Qed.
Let HN2x : (2 * K2x (sd_Kr2 sd) (sd_Ky2 sd) < sd_N2s sd)%nat.
Proof. destruct shape_facts as [_ [_ [_ [_ [[_ [_ [_ A]]] _]]]]]. exact A. Qed.

(** Every source converges from its seed along the first torus. *)
Lemma srcs0 : srcs_ok w0 l K0.
Proof.
  destruct src_facts as [_ [SC [C0 _]]]. pose proof d0w0 as [D0 D1].
  unfold srcs_ok. unfold crude, crude_ok in C0. rewrite Forall_forall in SC, C0 |- *. intros sy I.
  destruct (SC sy I) as [Sy Cy].
  destruct (src_at P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd)
              HN1x HN2x w0 sy ltac:(lra) Sy Cy (C0 sy I)) as [_ [_ [_ [_ [_ [_ [_ [Hq Hy]]]]]]]].
  exact (conj Hq Hy).
Qed.

Lemma srcs_in : E.EO.JO.src_in (E.src_i (sd_ssrc sd) (sd_srcs sd)) l.
Proof.
  destruct src_facts as [HL _]. destruct shape_facts as [[_ [_ [Hs _]]] _].
  exact (src_in_srcl (sd_ssrc sd) (sd_sY sd) (sd_Ky1 sd) (sd_Ky2 sd) (sd_srcs sd) (sd_seeds sd) Hs HL).
Qed.

Lemma Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Proof. apply srcl_canon. Qed.

(** * The error and the defects of the seeds on the strip of the iteration *)

Let BR := qr (nth 0 (fd_B fd) q0).
Let BZ := qr (nth 1 (fd_B fd) q0).
Let BU := qr (nth 2 (fd_B fd) q0).
Let BG := qr (nth 3 (fd_B fd) q0).

Lemma e0_facts :
  nbound w0 BR (errF_R P l om_w7x K0) /\ nbound w0 BZ (errF_Z P l om_w7x K0) /\
  nbound w0 BU (defU P l K0 (cden fU)) /\ nbound w0 BG (defG P l K0 (cden fG)).
Proof.
  destruct shape_facts as [[Hs0 _] [_ [[N4 [M4 [HD1 [HD2 [HK1 HK2]]]]] [_ [_ [_ [HMw [HB _]]]]]]]].
  destruct lensR as [LR LRn]. destruct lensZ as [LZ LZn]. destruct lensU as [LU LUn]. destruct lensG as [LG LGn].
  destruct src_facts as [_ [_ [_ [_ [MR [MZ [MU [MG _]]]]]]]].
  pose proof d0w0 as [D0 D1]. pose proof Hw01 as W01.
  assert (PM4 : (4 <= Pn * E.e0_M ed)%nat) by (pose proof HPn; nia).
  exact (E.check_E0_ok Pn (E.e0_N1 ed) (E.e0_M ed) (E.e0_K1 ed) (E.e0_K2 ed) (E.e0_D ed) Km Kn (sd_Kmu sd)
           (sd_Knu sd) (sd_Kmg sd) (sd_Kng sd) s0 rowsR rowsZ (sd_rowsU sd) (sd_rowsG sd)
           (E.src_i (sd_ssrc sd) (sd_srcs sd)) (E.om_i Pn (sd_a sd) (sd_b sd)) (trig fd (E.e0_N1 ed))
           (trig fd (E.e0_M ed)) (trig fd (Pn * E.e0_M ed)) (sW0 fd) (sW1m fd)
           (SD.ipow (sW1m fd) (E.e0_N1 ed - E.e0_K1 ed)) (SD.ipow (sW0k fd) Pn) (SD.ipow (sW1km fd) Pn)
           (SD.ipow (sW1km fd) (Pn * E.e0_M ed - Pn * E.e0_K2 ed)) (SD.ipow (sDk fd) (S (E.e0_D ed)))
           (claim (fd_Mw fd) 0) (claim (fd_Mw fd) 1) (claim (fd_Mw fd) 2) (claim (fd_Mw fd) 3)
           (claim (fd_B fd) 0) (claim (fd_B fd) 1) (claim (fd_B fd) 2) (claim (fd_B fd) 3) l om_w7x w0 w0 w1
           (qr (nth 0 (fd_Mw fd) q0)) (qr (nth 1 (fd_Mw fd) q0)) (qr (nth 2 (fd_Mw fd) q0)) (qr (nth 3 (fd_Mw fd) q0))
           BR BZ BU BG HPn ltac:(lia) ltac:(lia) Hs0 LR LZ LU LG LRn LZn LUn LGn (Htrig _ N4) (Htrig _ M4)
           (Htrig _ PM4) HEw0 HEw1m (HEAt _ _ HK1) (HEP _ _ HEwk0) (HEPm _ _ HEwk1m) (HEBt _ _ HK2) (HET _)
           (claim_ok _ 0 HMw) (claim_ok _ 1 HMw) (claim_ok _ 2 HMw) (claim_ok _ 3 HMw) (claim_ok _ 0 HB)
           (claim_ok _ 1 HB) (claim_ok _ 2 HB) (claim_ok _ 3 HB) HOM srcs_in ltac:(lra) srcs0 Cl ltac:(lra) W01
           HD1 HD2 MR MZ MU MG (proj1 (proj2 (proj2 (proj2 (proj2 cert_parts)))))).
Qed.

(** * The jets on the strip of the iteration *)

Let Mws := map (fun i => qr (nth i (fd_JM fd) q0)) (seq 0 9).
Let Bs := map (fun i => qr (nth i (fd_JB fd) q0)) (seq 0 9).
Let fJs := JC.fJd P (JC.jd_sJ jd) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (JC.jd_rowsJ jd).

Lemma lensJ : List.Forall (fun rows => length rows = length (zrange (JC.jd_Kj1 jd))) (JC.jd_rowsJ jd) /\
              List.Forall (List.Forall (fun r => length r = length (pns P (JC.jd_Kj2 jd)))) (JC.jd_rowsJ jd).
Proof.
  destruct shape_facts as [_ [[_ [_ [_ [_ [_ [_ H]]]]]] _]]. rewrite forallb_forall in H.
  split; apply Forall_forall; intros rows Hr; destruct (lens_facts sd _ _ _ (H rows Hr)) as [A B]; assumption.
Qed.

Lemma claims_in (L : list (Z * Z)) : forallb qok L = true ->
  Forall2 inR (map (claim L) (seq 0 9)) (map (fun i => qr (nth i L q0)) (seq 0 9)).
Proof.
  intros H. generalize (seq 0 9). intros is. induction is as [| i is IH]; [constructor |].
  cbn [map]. constructor; [apply claim_ok, H | exact IH].
Qed.

Lemma jnorm_ok (w : R) (Ew Ek : J.t) (i : nat) : inR Ew (exp w) -> inR Ek (exp (w * kappa)) -> (i < 9)%nat ->
  inR (inorm (iFJ sd jd i) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) Ew (SD.ipow Ek Pn)) (fnorm w (nth i fJs [])).
Proof.
  intros HE HK Hi. destruct shape_facts as [[_ [_ [_ HsJ]]] [[_ [_ [_ [_ [_ [L9 _]]]]]] _]].
  destruct lensJ as [LJk LJn].
  pose proof (TG.jets_parts_gen Pn (JC.jd_sJ jd) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) tjpar (JC.jd_rowsJ jd) HsJ LJk LJn) as JP.
  assert (Hi' : (i < length (map (fun x : bool * list (list Z) =>
                   dfam (JC.jd_sJ jd) (zrange (JC.jd_Kj1 jd)) (pns (Z.of_nat Pn) (JC.jd_Kj2 jd))
                     (if fst x then crows (snd x) else srows (snd x))) (combine tjpar (JC.jd_rowsJ jd))))%nat)
    by (rewrite length_map, length_combine, L9; simpl; lia).
  destruct (forall2_nth _ _ _ [] [] i JP Hi') as [A [B C]].
  exact (fnorm_ok Pn (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (iFJ sd jd i) (nth i fJs []) w Ew (SD.ipow Ek Pn) A B C HE
           (HEP _ _ HK)).
Qed.

Lemma fin_parts :
  let '(NR0, NZ0, RR0) := gnorms Pn Km Kn (sd_Kr1 sd) (sd_Kr2 sd) s0 rowsR rowsZ (sW0 fd) (SD.ipow (sW0k fd) Pn) in
  let IR := iqq (fs_r fs) in
  let res := map (src_final (sd_ssrc sd) NR0 NZ0 RR0 (sW0k fd) IR (J.mul two IR))
                 (combine (sd_srcs sd) (trips (skipn 13 O))) in
  length (trips (skipn 13 O)) = length (sd_srcs sd) /\ forallb fst res = true /\ jcrude_ok sd jd fd O = true /\
  fin_scal P IR (iw0 fd) (id0 fd) (iqq (fs_eps fs)) (iqq (fs_delta fs)) (iqq (fs_A0 fs)) (iqq (fs_G0 fs))
    (iqq (fs_N0 fs)) (iqq (fs_T0 fs)) (iqq (fs_tau0 fs)) (iqq (fs_xA fs)) (iqq (fs_xG fs)) (iqq (fs_xN fs))
    (iqq (fs_xB fs)) (iqq (fs_xTm fs)) (iqq (fs_xtau fs)) (sW0k fd) (sE1 fd) (E.om_i Pn (sd_a sd) (sd_b sd))
    (J.mul (J.of_q 5 0) (iqq (17%Z, 100%Z)))
    (inorm (iFR sd) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn)) (inorm (iFU sd) (sd_Kmu sd) (sd_Knu sd) (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (iFG sd) (sd_Kmg sd) (sd_Kng sd) (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (E.DO.ifam_dt (iFR sd)) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (E.DO.ifam_dt (iFZ sd)) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (iFB sd fd) (fd_Kmb fd) (fd_Knb fd) (sW0 fd) (SD.ipow (sW0k fd) Pn)) (NJw0 sd jd fd)
    (claim (fd_B fd) 0) (claim (fd_B fd) 1) (claim (fd_B fd) 2) (claim (fd_B fd) 3) (map (claim (fd_JB fd)) (seq 0 9))
    (nth 0 TR J.zero) (nth 1 TR J.zero) (nth 2 TR J.zero) (nth 3 TR J.zero) (nth 4 TR J.zero) (nth 5 TR J.zero)
    (map snd res) = true.
Proof.
  pose proof fin_ok_true as H. unfold fin_ok in H. unfold cP in H. fold Pn P Km Kn s0 rowsR rowsZ in H |- *.
  destruct (gnorms Pn Km Kn (sd_Kr1 sd) (sd_Kr2 sd) s0 rowsR rowsZ (sW0 fd) (SD.ipow (sW0k fd) Pn))
    as [[NR0 NZ0] RR0].
  cbv beta iota zeta in H |- *. repeat rewrite Bool.andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Nat.eqb_eq in H1. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma jcrude_true : jcrude_ok sd jd fd O = true.
Proof.
  pose proof fin_parts as H.
  destruct (gnorms Pn Km Kn (sd_Kr1 sd) (sd_Kr2 sd) s0 rowsR rowsZ (sW0 fd) (SD.ipow (sW0k fd) Pn)) as [[NR0 NZ0] RR0].
  cbv beta iota zeta in H. exact (proj1 (proj2 (proj2 H))).
Qed.

(** The nine jets on the wide strip from the crude totals. *)
Lemma jsel_crude (i : nat) : (i < 9)%nat ->
  nbound w1 (nth i [tR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tP P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tRR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tRZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tPR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tPZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZR P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1;
     tZZ P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) l w1] 0)
    (jsel i (tot P l K0)).
Proof.
  intros Hi. destruct src_facts as [_ [SC [_ [C1 _]]]]. pose proof d0w0 as [D0 D1]. pose proof Hw01.
  destruct (crude_tot P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd)
              HN1x HN2x l SC w1 ltac:(lra) C1) as [T0 [T1 [T2 [T3 [T4 [T5 [T6 [T7 T8]]]]]]]].
  destruct i as [| [| [| [| [| [| [| [| [| i]]]]]]]]]; try assumption. lia.
Qed.

Lemma jets_crude (i : nat) : (i < 9)%nat -> nbound w1 (nth i Mws 0) (udef P l K0 fJs i).
Proof.
  intros Hi. destruct src_facts_O as [T9 _].
  destruct shape_facts as [_ [_ [_ [_ [_ [_ [_ [_ [HJM _]]]]]]]]].
  pose proof jcrude_true as JC0. unfold jcrude_ok in JC0. rewrite forallb_forall in JC0.
  specialize (JC0 i ltac:(apply in_seq; lia)).
  pose proof (forall2_nth inR _ _ J.zero 0 i T9 ltac:(simpl; lia)) as Ht.
  rewrite nth_firstn in Ht by lia. replace (i <? 9)%nat with true in Ht by (symmetry; apply Nat.ltb_lt, Hi).
  pose proof (jnorm_ok w1 (sW1 fd) (sW1k fd) i HEw1 HEwk1 Hi) as Hn.
  assert (En : nth i (NJw1 sd jd fd) J.zero = inorm (iFJ sd jd i) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (sW1 fd)
                                                  (SD.ipow (sW1k fd) Pn))
    by (unfold NJw1; rewrite nth_map_seq by exact Hi; reflexivity).
  rewrite En in JC0.
  assert (Em : nth i Mws 0 = qr (nth i (fd_JM fd) q0)) by (unfold Mws; rewrite nth_map_seq by exact Hi; reflexivity).
  rewrite Em.
  pose proof (ile_correct _ _ _ _ JC0 (inR_add _ _ _ _ Ht Hn) (claim_ok _ i HJM)) as Le.
  apply (nbound_le _ _ _ _ Le). unfold udef. apply nbound_fsub; [exact (jsel_crude i Hi) | apply nbound_cden].
Qed.

Lemma jets_facts (i : nat) : (i < 9)%nat -> nbound w0 (nth i Bs 0) (udef P l K0 fJs i).
Proof.
  destruct shape_facts as [[Hs0 [_ [_ HsJ]]] [[_ [_ [_ [_ [_ [L9 _]]]]]] [_ [[N4 [M4 [HD1 [HD2 [HK1 HK2]]]]] [_ [_ [_ [_ [HJM [HJB _]]]]]]]]]].
  destruct lensR as [LR LRn]. destruct lensZ as [LZ LZn]. destruct lensJ as [LJk LJn].
  pose proof d0w0 as [D0 D1]. pose proof Hw01 as W01.
  assert (PM4 : (4 <= Pn * JC.jd_M jd)%nat) by (pose proof HPn; nia).
  exact (JC.check_jets_ok Pn (JC.jd_N1 jd) (JC.jd_M jd) (JC.jd_K1 jd) (JC.jd_K2 jd) (JC.jd_D jd) Km Kn (JC.jd_Kj1 jd)
           (JC.jd_Kj2 jd) s0 (JC.jd_sJ jd) rowsR rowsZ (JC.jd_rowsJ jd) (JC.E.src_i (sd_ssrc sd) (sd_srcs sd))
           (trig fd (JC.jd_N1 jd)) (trig fd (JC.jd_M jd)) (trig fd (Pn * JC.jd_M jd)) (sW0 fd) (sW1m fd)
           (SD.ipow (sW1m fd) (JC.jd_N1 jd - JC.jd_K1 jd)) (SD.ipow (sW0k fd) Pn) (SD.ipow (sW1km fd) Pn)
           (SD.ipow (sW1km fd) (Pn * JC.jd_M jd - Pn * JC.jd_K2 jd)) (SD.ipow (sDk fd) (S (JC.jd_D jd)))
           (map (claim (fd_JM fd)) (seq 0 9)) (map (claim (fd_JB fd)) (seq 0 9)) l w0 w0 w1 Mws Bs HPn ltac:(lia)
           ltac:(lia) Hs0 HsJ LR LZ LRn LZn LJk LJn (Htrig _ N4) (Htrig _ M4) (Htrig _ PM4) HEw0 HEw1m
           (HEAt _ _ HK1) (HEP _ _ HEwk0) (HEPm _ _ HEwk1m) (HEBt _ _ HK2) (HET _) (claims_in _ HJM) (claims_in _ HJB)
           srcs_in ltac:(lra) srcs0 Cl ltac:(lra) W01 HD1 HD2 jets_crude
           (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 cert_parts)))))) i).
Qed.

(** * The finite twist *)

Let Nfin := tNf Pn s0 Km Kn (sd_Kmg sd) (sd_Kng sd) (fd_Kmb fd) (fd_Knb fd) rowsR rowsZ (sd_rowsG sd) (fd_rowsB fd).
Let kmfin := tkmf Pn s0 (JC.jd_sJ jd) Km Kn (sd_Kmg sd) (sd_Kng sd) (fd_Kmb fd) (fd_Knb fd) (sd_Kmu sd) (sd_Knu sd)
               (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) rowsR rowsZ (sd_rowsG sd) (fd_rowsB fd) (sd_rowsU sd) (JC.jd_rowsJ jd)
               om_w7x.
Let Tfin := tTf Pn s0 (JC.jd_sJ jd) Km Kn (sd_Kmg sd) (sd_Kng sd) (fd_Kmb fd) (fd_Knb fd) (sd_Kmu sd) (sd_Knu sd)
              (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) rowsR rowsZ (sd_rowsG sd) (fd_rowsB fd) (sd_rowsU sd) (JC.jd_rowsJ jd)
              om_w7x.
Let bxN (u : fser) := rexact Pn (fd_N1t fd) (fd_Mt fd) (bN1 Km (sd_Kmg sd)) (bN2 Kn (sd_Kng sd)) u w0.
Let bxK (u : fser) := rexact Pn (fd_N1t fd) (fd_Mt fd) (bK1 Km (sd_Kmg sd) (sd_Kmu sd) (JC.jd_Kj1 jd))
                        (bK2 Kn (sd_Kng sd) (sd_Knu sd) (JC.jd_Kj2 jd)) u (w0 - d0).
Let bxT (u : fser) := rexact Pn (fd_N1t fd) (fd_Mt fd) (bT1 Km (sd_Kmg sd) (sd_Kmu sd) (JC.jd_Kj1 jd))
                        (bT2 Kn (sd_Kng sd) (sd_Knu sd) (JC.jd_Kj2 jd)) u (w0 - d0).

Lemma twist_facts_run :
  (inR (nth 0 (run_twist sd jd fd) J.zero) (bxN (vR Nfin)) /\ nbound w0 (bxN (vR Nfin)) (vR Nfin)) /\
  (inR (nth 1 (run_twist sd jd fd) J.zero) (bxN (vZ Nfin)) /\ nbound w0 (bxN (vZ Nfin)) (vZ Nfin)) /\
  (inR (nth 2 (run_twist sd jd fd) J.zero) (bxK (vR kmfin)) /\ nbound (w0 - d0) (bxK (vR kmfin)) (vR kmfin)) /\
  (inR (nth 3 (run_twist sd jd fd) J.zero) (bxK (vZ kmfin)) /\ nbound (w0 - d0) (bxK (vZ kmfin)) (vZ kmfin)) /\
  (inR (nth 4 (run_twist sd jd fd) J.zero) (bxT Tfin) /\ nbound (w0 - d0) (bxT Tfin) Tfin) /\
  inR (nth 5 (run_twist sd jd fd) J.zero) (fc Tfin 0 0).
Proof.
  destruct shape_facts as [[Hs0 [_ [_ HsJ]]] [[_ [_ [LUb [LGb [LBb [L9 _]]]]]] [_ [_ [_ [[N4 [M4 [HBm [HBn [HNx HMx]]]]] _]]]]]].
  destruct lensR as [LR LRn]. destruct lensZ as [LZ LZn]. destruct lensU as [LU LUn]. destruct lensG as [LG LGn].
  destruct lensJ as [LJk LJn]. destruct (lens_facts sd _ _ _ LBb) as [LB LBn].
  exact (TG.tcheck_ok Pn (fd_N1t fd) (fd_Mt fd) s0 (JC.jd_sJ jd) Km Kn (sd_Kmg sd) (sd_Kng sd) (fd_Kmb fd) (fd_Knb fd)
           (sd_Kmu sd) (sd_Knu sd) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) rowsR rowsZ (sd_rowsG sd) (fd_rowsB fd) (sd_rowsU sd)
           (JC.jd_rowsJ jd) (trig fd (fd_N1t fd)) (trig fd (fd_Mt fd)) (E.om_i Pn (sd_a sd) (sd_b sd)) (sW0 fd)
           (SD.ipow (sW0k fd) Pn) (sWd fd) (SD.ipow (sWdk fd) Pn) om_w7x w0 (w0 - d0) HPn ltac:(lia) ltac:(lia) Hs0
           HsJ LR LZ LG LB LU LRn LZn LGn LBn LUn LJk LJn L9 (Htrig _ N4) (Htrig _ M4) HOM HEw0 (HEP _ _ HEwk0)
           HEwd (HEP _ _ HEwdk) HBm HBn HNx HMx).
Qed.

Lemma run_twist_len : length (run_twist sd jd fd) = 6%nat.
Proof. reflexivity. Qed.

(** The enclosures [TR] hold the ones the grid of the finite twist returns. *)
Lemma TR_in (i : nat) (x : R) : (i < 6)%nat -> inR (nth i (run_twist sd jd fd) J.zero) x -> inR (nth i TR J.zero) x.
Proof.
  intros Hi H.
  pose proof (incl_list_f2 _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cert_parts)))))))))) as HI.
  exact (forall2_nth _ _ _ J.zero J.zero i HI ltac:(rewrite run_twist_len; exact Hi) x H).
Qed.

Lemma twist_facts :
  (inR (nth 0 TR J.zero) (bxN (vR Nfin)) /\ nbound w0 (bxN (vR Nfin)) (vR Nfin)) /\
  (inR (nth 1 TR J.zero) (bxN (vZ Nfin)) /\ nbound w0 (bxN (vZ Nfin)) (vZ Nfin)) /\
  (inR (nth 2 TR J.zero) (bxK (vR kmfin)) /\ nbound (w0 - d0) (bxK (vR kmfin)) (vR kmfin)) /\
  (inR (nth 3 TR J.zero) (bxK (vZ kmfin)) /\ nbound (w0 - d0) (bxK (vZ kmfin)) (vZ kmfin)) /\
  (inR (nth 4 TR J.zero) (bxT Tfin) /\ nbound (w0 - d0) (bxT Tfin) Tfin) /\
  inR (nth 5 TR J.zero) (fc Tfin 0 0).
Proof.
  destruct twist_facts_run as [[A0 B0] [[A1 B1] [[A2 B2] [[A3 B3] [[A4 B4] A5]]]]].
  refine (conj (conj (TR_in 0 _ ltac:(lia) A0) B0) (conj (conj (TR_in 1 _ ltac:(lia) A1) B1)
          (conj (conj (TR_in 2 _ ltac:(lia) A2) B2) (conj (conj (TR_in 3 _ ltac:(lia) A3) B3)
          (conj (conj (TR_in 4 _ ltac:(lia) A4) B4) (TR_in 5 _ ltac:(lia) A5)))))).
Qed.

(** * The sources on the ball *)

Let r := qr (fs_r fs).
Let IR := iqq (fs_r fs).

Lemma HCS0 : inR (sW0k fd) (wt w0 0 1).
Proof. change (wt w0 0 1) with (csw w0). rewrite csw_exp. exact HEwk0. Qed.

Lemma loop_ok : forall (NR0 NZ0 RR0 : J.t),
  inR NR0 (NRr P Km Kn s0 rowsR (sd_Kr1 sd) (sd_Kr2 sd) w0) -> inR NZ0 (NZr P Km Kn s0 rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0) ->
  inR RR0 (rref P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0) -> inR IR r ->
  let res := map (src_final (sd_ssrc sd) NR0 NZ0 RR0 (sW0k fd) IR (J.mul two IR))
                 (combine (sd_srcs sd) (trips (skipn 13 O))) in
  length (trips (skipn 13 O)) = length (sd_srcs sd) -> forallb fst res = true ->
  List.Forall (sfin P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 r) l /\
  Forall2 (sd_in (fdr1 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0 r) (fdr2 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0 r)
                 (fdr3 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0 r)
                 (fdyb P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 r))
          (map snd res) l.
Proof.
  intros NR0 NZ0 RR0 HNR HNZ HRR HR res HLT Hf.
  destruct src_facts as [HL _]. destruct src_facts_O as [_ HT].
  pose proof (trips_ok _ _ _ _ _ HT) as TT.
  destruct shape_facts as [[_ [_ [Hssrc _]]] _].
  assert (HHM : inR (J.mul two IR) (2 * r)) by (apply inR_mul; [exact two_ok | exact HR]).
  unfold res in *. clear res. unfold l in TT |- *. unfold srcl in TT |- *.
  revert HL HLT Hf TT. generalize (trips (skipn 13 O)). intros TRs. revert TRs.
  generalize (sd_seeds sd). generalize (sd_srcs sd).
  induction l0 as [| x xs IH]; intros ys TRs HL HLT Hf TT; [destruct ys; split; constructor |].
  destruct ys as [| y ys]; [discriminate |]. destruct TRs as [| T TRs]; [discriminate |].
  cbn [combine map forallb] in Hf, TT |- *. apply andb_prop in Hf. destruct Hf as [Hf1 Hf2].
  inversion TT as [| T' sy' TRs' l' HT1 HT2]; subst.
  destruct (src_final_ok P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd)
              w0 r (sd_ssrc sd) NR0 NZ0 RR0 (sW0k fd) IR (J.mul two IR) Hssrc HNR HNZ HRR HCS0 HR HHM x T
              (yser (sd_sY sd) (sd_Ky1 sd) (sd_Ky2 sd) y) HT1 Hf1) as [S1 S2].
  destruct (IH ys TRs ltac:(simpl in HL; lia) ltac:(simpl in HLT; lia) Hf2 HT2) as [A B].
  split; constructor; assumption.
Qed.

(** * The scalar conditions *)

Let fR := fRf P Km Kn s0 rowsR.
Let fZ := fZf P Km Kn s0 rowsZ.
Let fB := dfam s0 (zrange (fd_Kmb fd)) (pns P (fd_Knb fd)) (srows (fd_rowsB fd)).
Let Ubf := cden fU.
Let gsf := cden fG.
Let bf := cden fB.
Let kR0 := fnorm w0 fR.
Let MU := fnorm w0 fU.
Let MG := fnorm w0 fG.
Let NAR := fnorm w0 (fam_dt fR).
Let NAZ := fnorm w0 (fam_dt fZ).
Let NB := fnorm w0 fB.
Let nj (i : nat) := fnorm w0 (nth i fJs []).
Let ej (i : nat) := nth i Bs 0.
Let bJ (i : nat) := nJ nj ej i.
Let eps0 := qr (fs_eps fs).
Let del0 := qr (fs_delta fs).
Let A0 := qr (fs_A0 fs).
Let G0 := qr (fs_G0 fs).
Let N0 := qr (fs_N0 fs).
Let T0 := qr (fs_T0 fs).
Let tau0 := qr (fs_tau0 fs).
Let xA := qr (fs_xA fs).
Let xG := qr (fs_xG fs).
Let xN := qr (fs_xN fs).
Let xB := qr (fs_xB fs).
Let xTm := qr (fs_xTm fs).
Let xtau := qr (fs_xtau fs).
Let gamma := IZR 5 * (17 / 100).
Let r10 := fr10 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0.
Let r20 := fr20 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0.
Let r30 := fr30 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0.
Let MY := fMY (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0.
Let th0 := fth0 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0.
Let MD0 := MDk P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0.
Let dr1 := fdr1 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0 r.
Let dr2 := fdr2 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0 r.
Let dr3 := fdr3 P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) w0 r.
Let dyb := fdyb P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 r.
Let kcf := FieldKAM.kc P l w0 r xA xG xN xB xTm xtau r10 r20 r30 MY th0 (bJ 0) (bJ 1) (bJ 2) (bJ 3) (bJ 4) (bJ 5)
             (bJ 6) (bJ 7) (bJ 8) kR0 MU BU.
Let eU := inv_eps MU BU 0.
Let eg := inv_eps MG BG 0.
Let eNr := eg * A0.
Let xNR := bxN (vR Nfin).
Let xNZ := bxN (vZ Nfin).
Let xKR := bxK (vR kmfin).
Let xKZ := bxK (vZ kmfin).
Let xT := bxT Tfin.
Let mean := fc Tfin 0 0.
Let nNf := Rmax xNR xNZ.
Let nkmf := Rmax xKR xKZ.
Let eDVr := reDV kR0 MU eU nj ej.
Let nDVr := rnDVf kR0 MU nj.
Let eTr := KTwist.eT om_w7x d0 eNr nNf nkmf (nj 1) (ej 1) eDVr nDVr.
Let g0 := g0f (jP (tot P l K0)) (vdot (vdt K0) (vdt K0)) gsf.

Lemma HP0 : (0 < P)%Z. Proof. pose proof HPn. unfold P. lia. Qed.

Lemma qoks : qok (fs_r fs) = true /\ qok (fs_eps fs) = true /\ qok (fs_delta fs) = true /\ qok (fs_A0 fs) = true /\
  qok (fs_G0 fs) = true /\ qok (fs_N0 fs) = true /\ qok (fs_T0 fs) = true /\ qok (fs_tau0 fs) = true /\
  qok (fs_xA fs) = true /\ qok (fs_xG fs) = true /\ qok (fs_xN fs) = true /\ qok (fs_xB fs) = true /\
  qok (fs_xTm fs) = true /\ qok (fs_xtau fs) = true.
Proof.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cert_parts))))))))) as Q.
  unfold scal_ok in Q. cbn [forallb] in Q. repeat rewrite Bool.andb_true_iff in Q. tauto.
Qed.

Lemma fJs_len9 : length fJs = 9%nat.
Proof.
  destruct shape_facts as [_ [[_ [_ [_ [_ [_ [L9 _]]]]]] _]].
  unfold fJs, JC.fJd. rewrite length_map, length_combine, L9. reflexivity.
Qed.

Lemma HNJ : forall i, inR (jn (NJw0 sd jd fd) i) (nj i).
Proof.
  intros i. unfold jn, nj. destruct (Nat.lt_ge_cases i 9) as [Hi | Hi].
  - unfold NJw0. rewrite nth_map_seq by exact Hi. exact (jnorm_ok w0 (sW0 fd) (sW0k fd) i HEw0 HEwk0 Hi).
  - rewrite (nth_overflow (NJw0 sd jd fd) J.zero) by (unfold NJw0; rewrite length_map, length_seq; exact Hi).
    rewrite (nth_overflow fJs []) by (rewrite fJs_len9; exact Hi). exact inR_zero.
Qed.

Lemma HEJ : forall i, inR (je (map (claim (fd_JB fd)) (seq 0 9)) i) (ej i).
Proof.
  intros i. unfold je, ej. destruct shape_facts as [_ [_ [_ [_ [_ [_ [_ [_ [_ [HJB _]]]]]]]]]].
  destruct (Nat.lt_ge_cases i 9) as [Hi | Hi].
  - rewrite (nth_map_seq (claim (fd_JB fd)) 9 i J.zero Hi). unfold Bs.
    rewrite (nth_map_seq (fun i => qr (nth i (fd_JB fd) q0)) 9 i 0 Hi). exact (claim_ok _ i HJB).
  - rewrite (nth_overflow (map (claim (fd_JB fd)) (seq 0 9)) J.zero) by (rewrite length_map, length_seq; exact Hi).
    rewrite (nth_overflow Bs 0) by (unfold Bs; rewrite length_map, length_seq; exact Hi). exact inR_zero.
Qed.

(** The norms of the finite families on the strip of the iteration. *)
Lemma norms_ok :
  inR (inorm (iFR sd) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn)) kR0 /\
  inR (inorm (iFU sd) (sd_Kmu sd) (sd_Knu sd) (sW0 fd) (SD.ipow (sW0k fd) Pn)) MU /\
  inR (inorm (iFG sd) (sd_Kmg sd) (sd_Kng sd) (sW0 fd) (SD.ipow (sW0k fd) Pn)) MG /\
  inR (inorm (E.DO.ifam_dt (iFR sd)) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn)) NAR /\
  inR (inorm (E.DO.ifam_dt (iFZ sd)) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn)) NAZ /\
  inR (inorm (iFB sd fd) (fd_Kmb fd) (fd_Knb fd) (sW0 fd) (SD.ipow (sW0k fd) Pn)) NB.
Proof.
  destruct shape_facts as [[Hs0 _] [[_ [_ [_ [_ [LBb _]]]]] _]].
  destruct lensR as [LR LRn]. destruct lensZ as [LZ LZn]. destruct lensU as [LU LUn]. destruct lensG as [LG LGn].
  destruct (lens_facts sd _ _ _ LBb) as [LB LBn].
  pose proof (HEP _ _ HEwk0) as HP1.
  assert (IR0 : E.TB.E.fam_in (iFR sd) fR) by (apply E.DO.ifam_in, Hs0).
  assert (IZ0 : E.TB.E.fam_in (iFZ sd) fZ) by (apply E.DO.ifam_in, Hs0).
  assert (NR : List.Forall (fun kr => map fst (snd kr) = pns P Kn) fR) by (apply dfam_ns, crows_len, LRn).
  assert (NZ : List.Forall (fun kr => map fst (snd kr) = pns P Kn) fZ) by (apply dfam_ns, srows_len, LZn).
  assert (KR : map fst fR = zrange Km) by (apply dfam_ks; unfold crows; rewrite length_map; exact LR).
  assert (KZ : map fst fZ = zrange Km) by (apply dfam_ks; unfold srows; rewrite length_map; exact LZ).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact (fnorm_ok Pn Km Kn _ _ w0 _ _ IR0 NR KR HEw0 HP1).
  - exact (fnorm_ok Pn (sd_Kmu sd) (sd_Knu sd) _ _ w0 _ _ (E.DO.ifam_in _ _ _ _ Hs0)
             (dfam_ns _ _ _ _ (crows_len _ _ LUn)) ltac:(apply dfam_ks; unfold crows; rewrite length_map; exact LU)
             HEw0 HP1).
  - exact (fnorm_ok Pn (sd_Kmg sd) (sd_Kng sd) _ _ w0 _ _ (E.DO.ifam_in _ _ _ _ Hs0)
             (dfam_ns _ _ _ _ (crows_len _ _ LGn)) ltac:(apply dfam_ks; unfold crows; rewrite length_map; exact LG)
             HEw0 HP1).
  - exact (fnorm_ok Pn Km Kn _ _ w0 _ _ (E.DO.ifam_dt_in _ _ IR0) (E.DO.fam_dt_ns _ _ NR)
             ltac:(rewrite E.DO.fam_dt_ks; exact KR) HEw0 HP1).
  - exact (fnorm_ok Pn Km Kn _ _ w0 _ _ (E.DO.ifam_dt_in _ _ IZ0) (E.DO.fam_dt_ns _ _ NZ)
             ltac:(rewrite E.DO.fam_dt_ks; exact KZ) HEw0 HP1).
  - exact (fnorm_ok Pn (fd_Kmb fd) (fd_Knb fd) _ _ w0 _ _ (E.DO.ifam_in _ _ _ _ Hs0)
             (dfam_ns _ _ _ _ (srows_len _ _ LBn)) ltac:(apply dfam_ks; unfold srows; rewrite length_map; exact LB)
             HEw0 HP1).
Qed.

(** The check of the sources on the ball and the scalar check. *)
Lemma run_facts : exists Ss : list sdat,
  List.Forall (sfin P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 r) l /\
  Forall2 (sd_in dr1 dr2 dr3 dyb) Ss l /\
  fin_scal P IR (iw0 fd) (id0 fd) (iqq (fs_eps fs)) (iqq (fs_delta fs)) (iqq (fs_A0 fs)) (iqq (fs_G0 fs))
    (iqq (fs_N0 fs)) (iqq (fs_T0 fs)) (iqq (fs_tau0 fs)) (iqq (fs_xA fs)) (iqq (fs_xG fs)) (iqq (fs_xN fs))
    (iqq (fs_xB fs)) (iqq (fs_xTm fs)) (iqq (fs_xtau fs)) (sW0k fd) (sE1 fd) (E.om_i Pn (sd_a sd) (sd_b sd))
    (J.mul (J.of_q 5 0) (iqq (17%Z, 100%Z)))
    (inorm (iFR sd) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (iFU sd) (sd_Kmu sd) (sd_Knu sd) (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (iFG sd) (sd_Kmg sd) (sd_Kng sd) (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (E.DO.ifam_dt (iFR sd)) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (E.DO.ifam_dt (iFZ sd)) Km Kn (sW0 fd) (SD.ipow (sW0k fd) Pn))
    (inorm (iFB sd fd) (fd_Kmb fd) (fd_Knb fd) (sW0 fd) (SD.ipow (sW0k fd) Pn)) (NJw0 sd jd fd)
    (claim (fd_B fd) 0) (claim (fd_B fd) 1) (claim (fd_B fd) 2) (claim (fd_B fd) 3) (map (claim (fd_JB fd)) (seq 0 9))
    (nth 0 TR J.zero) (nth 1 TR J.zero) (nth 2 TR J.zero) (nth 3 TR J.zero) (nth 4 TR J.zero) (nth 5 TR J.zero) Ss = true.
Proof.
  destruct shape_facts as [[Hs0 _] _]. destruct lensR as [LR LRn]. destruct lensZ as [LZ LZn].
  destruct qoks as [Qr _].
  pose proof fin_parts as FP.
  pose proof (gnorms_ok Pn Km Kn (sd_Kr1 sd) (sd_Kr2 sd) s0 rowsR rowsZ Hs0 LR LZ LRn LZn w0 (sW0 fd)
                (SD.ipow (sW0k fd) Pn) HEw0 (HEP _ _ HEwk0)) as G.
  destruct (gnorms Pn Km Kn (sd_Kr1 sd) (sd_Kr2 sd) s0 rowsR rowsZ (sW0 fd) (SD.ipow (sW0k fd) Pn))
    as [[NR0 NZ0] RR0].
  cbv beta iota zeta in G. destruct G as [GR [GZ GRR]].
  cbv beta iota zeta in FP. destruct FP as [HLT [Hf [_ Hsc]]].
  destruct (loop_ok NR0 NZ0 RR0 GR GZ GRR (iqq_ok _ Qr) HLT Hf) as [Hsf HS].
  eexists. exact (conj Hsf (conj HS Hsc)).
Qed.

Lemma scal_facts :
  FieldConst.thU P l r (2 * r) (wt w0 0 1) dr1 dr2 dr3 dyb (bJ 5) (bJ 6) MU BU < 1 /\ BU < 1 /\ BG < 1 /\
  NAR <= A0 /\ NAZ <= A0 /\ MG + eg <= G0 /\ nNf + eNr <= N0 /\ NB <= xB /\ (MU + eU) * Rmax BR BZ <= eps0 /\
  xT + eTr <= T0 /\ tau0 <= Rabs mean - eTr /\
  0 <= xA /\ 0 <= xG /\ 0 <= xN /\ 0 <= xB /\ 0 <= xTm /\ 0 < xtau /\ 0 <= eps0 /\ 0 < r /\ 0 < d0 /\
  6 * d0 < w0 /\ 0 < gamma <= 1 /\
  0 < itA gamma d0 kcf /\ itA gamma d0 kcf * 16 * eps0 <= / 2 /\
  A0 + 2 * (kdA kcf gamma d0 * eps0) <= xA /\ G0 + 2 * (kdG kcf gamma d0 * eps0) <= xG /\
  N0 + 2 * (kdN kcf gamma d0 * eps0) <= xN /\ T0 + 2 * (kT kcf om_w7x gamma d0 * eps0) <= xTm /\
  2 * (kP kcf gamma d0 * eps0) <= r /\ xtau <= tau0 - 2 * (kT kcf om_w7x gamma d0 * eps0) /\
  kdA kcf gamma d0 * eps0 <= xA /\ xG * (kU kcf gamma d0 * eps0) <= / 2 /\ kdG kcf gamma d0 * eps0 <= xG /\
  kdN kcf gamma d0 * eps0 <= xN /\ kdW kcf om_w7x gamma d0 * eps0 <= kW kcf om_w7x d0 /\
  2 * (kP kcf gamma d0 * eps0) <= del0.
Proof.
  destruct qoks as [Qr [Qeps [Qdel [QA0 [QG0 [QN0 [QT0 [Qtau0 [QxA [QxG [QxN [QxB [QxTm Qxtau]]]]]]]]]]]]].
  destruct shape_facts as [_ [_ [_ [_ [_ [_ [_ [HB _]]]]]]]].
  destruct run_facts as [Ss [Hsf [HS Hsc]]].
  destruct norms_ok as [NK [NU [NG [NR' [NZ' NB']]]]].
  destruct twist_facts as [[TN1 _] [[TN2 _] [[TK1 _] [[TK2 _] [[TT1 _] TM]]]]].
  assert (HGM : inR (J.mul (J.of_q 5 0) (iqq (17%Z, 100%Z))) gamma)
    by (apply inR_mul; [exact (inR_Z 5) | exact (iqq_ok (17%Z, 100%Z) eq_refl)]).
  exact (FS.fin_scal_ok P _ _ _ _ _ _ _ _ _ _
           _ _ _ _ _ _ _ _ _ _
           _ _ _ _ _ _ _ _ _ _
           _ _ _ _ _ _ _ _ _
           l Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd) w0 d0 r eps0
           del0 A0 G0 N0 T0 tau0 xA xG xN xB xTm xtau om_w7x gamma kR0 MU MG NAR NAZ NB BR BZ BU BG xNR xNZ xKR xKZ
           xT mean nj ej (iqq_ok _ Qr) Hw0i Hd0i (iqq_ok _ Qeps) (iqq_ok _ Qdel) (iqq_ok _ QA0) (iqq_ok _ QG0)
           (iqq_ok _ QN0) (iqq_ok _ QT0) (iqq_ok _ Qtau0) (iqq_ok _ QxA) (iqq_ok _ QxG) (iqq_ok _ QxN) (iqq_ok _ QxB)
           (iqq_ok _ QxTm) (iqq_ok _ Qxtau) HCS0 HE1 HOM HGM NK NU NG NR' NZ' NB' HNJ HEJ (claim_ok _ 0 HB)
           (claim_ok _ 1 HB) (claim_ok _ 2 HB) (claim_ok _ 3 HB) TN1 TN2 TK1 TK2 TT1 TM HS Hsf Hsc).
Qed.

(** Every source along the first torus and on the ball. *)
Lemma src0_all : List.Forall (src0 K0 w0 r r10 r20 r30 MY MD0 th0 fy00) l.
Proof.
  destruct run_facts as [_ [SF _]]. destruct src_facts as [_ [SC [C0 _]]]. pose proof d0w0 as [D0 D1].
  unfold crude, crude_ok in C0. rewrite Forall_forall in SF, SC, C0 |- *. intros sy I.
  destruct (SC sy I) as [Sy Cy].
  destruct (src_at P Km Kn s0 rowsR rowsZ (sd_Kr1 sd) (sd_Kr2 sd) (sd_N1s sd) (sd_N2s sd) (sd_Ky1 sd) (sd_Ky2 sd)
              HN1x HN2x w0 sy ltac:(lra) Sy Cy (C0 sy I)) as [B1 [B2 [B3 [BY [BD [BT _]]]]]].
  destruct (SF sy I) as [S1 [S2 [S3 S4]]].
  exact (conj B1 (conj B2 (conj B3 (conj BY (conj BD (conj BT (conj (Rle_refl _) (conj S1 (conj S2 (conj S3 S4)))))))))).
Qed.

(** The nine field jets along the first torus. *)
Lemma bJ_ok (i : nat) : (i < 9)%nat -> nbound w0 (bJ i) (jsel i (tot P l K0)).
Proof. intros Hi. exact (nbound_add_diff w0 _ _ _ _ (nbound_cden w0 (nth i fJs [])) (jets_facts i Hi)). Qed.

(** The classes of U, b and the frame inverse. *)
Lemma classes :
  is_canon Ubf /\ is_even Ubf /\ is_per P Ubf /\ is_canon bf /\ is_odd bf /\ is_per P bf /\
  is_canon g0 /\ is_even g0 /\ is_per P g0.
Proof.
  pose proof HP0 as HP.
  destruct (tot_canon P l K0 HP (K0v_canon P Km Kn s0 rowsR rowsZ) Cl) as [_ [CP _]].
  destruct (tot_per P l K0) as [_ [QP _]].
  destruct (tot_par P l K0) as [_ [EP _]].
  destruct (K0v_canon P Km Kn s0 rowsR rowsZ) as [CR CZ].
  destruct (K0v_sym P Km Kn s0 rowsR rowsZ) as [ER OZ].
  destruct (K0v_per P Km Kn s0 rowsR rowsZ HP) as [QR QZ].
  assert (Ca : is_canon (vdot (vdt K0) (vdt K0))).
  { unfold vdot, vdt. cbn [vR vZ]. apply fadd_canon; apply fmul_canon; apply dt_canon; assumption. }
  assert (Ea : is_even (vdot (vdt K0) (vdt K0))).
  { unfold vdot, vdt. cbn [vR vZ].
    apply fadd_even; [apply fmul_odd_odd; apply dt_even; exact ER | apply fmul_even_even; apply dt_odd; exact OZ]. }
  assert (Qa : is_per P (vdot (vdt K0) (vdt K0))).
  { unfold vdot, vdt. cbn [vR vZ]. apply fadd_per; apply (fmul_per P HP); apply dt_per; assumption. }
  unfold g0, g0f, Ubf, bf, gsf, fU, fB, fG.
  refine (conj (cden_canon _) (conj (cden_even _ _ _ _) (conj (cden_per _ _ _ _ _ HP) (conj (cden_canon _)
          (conj (cden_odd _ _ _ _) (conj (cden_per _ _ _ _ _ HP) (conj _ (conj _ _)))))))).
  - apply finv_canon; [apply fmul_canon; assumption | apply cden_canon].
  - apply finv_even; [apply fmul_even_even; assumption | apply cden_even].
  - apply (finv_per P HP); [apply (fmul_per P HP); assumption | apply cden_per, HP].
Qed.

Lemma Hdio : dioph_per P om_w7x gamma.
Proof. unfold P, gamma. rewrite (proj1 cons_facts). exact om_dioph_per. Qed.

(** The coil field has an invariant torus with the rotation of the data,
    given by Fourier families on a strip, within the claimed distance of the
    first torus. *)
Theorem cert_ok_torus :
  exists KR KZ : R -> R -> R,
    fourier_torus (coilB 5 l) KR KZ om_w7x /\
    forall theta phi,
      Rabs (KR theta phi - feval (vR K0) theta phi) <= del0 /\
      Rabs (KZ theta phi - feval (vZ K0) theta phi) <= del0.
Proof.
  destruct scal_facts as [HthU [HBU1 [HBG1 [HAR [HAZ [HGG [HNN [HBB [HEE [HTT [Htau [SA [SG [SN [SB [STm [Stau
    [Seps [Sr [Sd [Sw [Sg [HAE [Hsmall [HcA [HcG [HcN [HcT [Hrr [Hctau2 [Hsm_a0 [Hsm_q0 [Hsm_g0 [Hsm_n0
    [Hsm_w0 Hdel]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  pose proof HP0 as HP.
  assert (Hw : 0 < w0) by lra. assert (Hw' : 0 <= w0) by lra.
  destruct e0_facts as [EBR [EBZ [EBU EBG]]].
  pose proof (nbound_nonneg _ _ _ EBU) as BU0. pose proof (nbound_nonneg _ _ _ EBG) as BG0'.
  destruct classes as [CU [EU [QU [Cb [Pb [Qb [Cg0 [Pg0 Qg0]]]]]]]].
  destruct twist_facts as [[_ TN1] [[_ TN2] [[_ TK1] [[_ TK2] [[_ TT1] _]]]]].
  pose proof (K0v_fin P Km Kn s0 rowsR rowsZ w0) as FK0.
  pose proof (K0v_canon P Km Kn s0 rowsR rowsZ) as C0.
  pose proof (K0v_sym P Km Kn s0 rowsR rowsZ) as S0.
  pose proof (K0v_per P Km Kn s0 rowsR rowsZ HP) as Q0.
  (* the frame *)
  assert (HA : vbound w0 A0 (vdt K0)).
  { split; [apply (nbound_le w0 NAR); [exact HAR | apply dt_cden_nb]
           | apply (nbound_le w0 NAZ); [exact HAZ | apply dt_cden_nb]]. }
  assert (Hasq : nbound w0 (NAR * NAR + NAZ * NAZ) (vdot (vdt K0) (vdt K0))).
  { unfold vdot, vdt. cbn [vR vZ]. apply nbound_fadd; apply nbound_fmul; try exact Hw'; apply dt_cden_nb. }
  assert (Hth : 0 <= BG < 1) by lra.
  pose proof (frame_G w0 (jP (tot P l K0)) (vdot (vdt K0) (vdt K0)) gsf MG BG Hw (nbound_cden w0 fG) Hth EBG) as FG.
  pose proof (frame_eg w0 (jP (tot P l K0)) (vdot (vdt K0) (vdt K0)) gsf MG BG Hw (nbound_cden w0 fG) Hth EBG) as FE.
  pose proof (frame_id w0 (jP (tot P l K0)) (vdot (vdt K0) (vdt K0)) gsf (bJ 1) (NAR * NAR + NAZ * NAZ) MG BG Hw
                (bJ_ok 1 ltac:(lia)) Hasq (nbound_cden w0 fG) Hth EBG) as FI.
  assert (BG0 : nbound w0 G0 g0) by (apply (nbound_le _ (MG + eg)); [exact HGG | exact FG]).
  assert (BB0 : nbound w0 xB bf) by (apply (nbound_le _ NB); [exact HBB | exact (nbound_cden w0 fB)]).
  (* the normal *)
  pose proof (knrm_diff w0 K0 g0 gsf bf A0 eg MG NB Hw' HA FE (nbound_cden w0 fG) (nbound_cden w0 fB)) as HeN.
  assert (HNf : vbound w0 nNf Nfin).
  { split; [apply (nbound_le w0 xNR); [apply Rmax_l | exact TN1] | apply (nbound_le w0 xNZ); [apply Rmax_r | exact TN2]]. }
  pose proof (nb_N w0 (knrm K0 g0 bf) Nfin eNr nNf HeN HNf) as BN.
  assert (BN0 : vbound w0 N0 (knrm K0 g0 bf)).
  { destruct BN as [E1 E2]. split; apply (nbound_le _ (nNf + eNr)); assumption. }
  (* the inverse of B_phi and the error *)
  assert (HeU : nbound w0 eU (fsub (lU P l Ubf K0) Ubf)).
  { apply nbound_fsub_sym.
    exact (nbound_finv_sub w0 Hw' (jP (lj P l K0)) Ubf MU BU (nbound_cden w0 fU) (conj BU0 HBU1) EBU). }
  pose proof (nbound_add_diff w0 MU eU Ubf (lU P l Ubf K0) (nbound_cden w0 fU) HeU) as BUf.
  assert (HU : inv_ok w0 (jP (lj P l K0)) Ubf).
  { exists (bJ 1), MU, BU. exact (conj (bJ_ok 1 ltac:(lia)) (conj (nbound_cden w0 fU) (conj (conj BU0 HBU1) EBU))). }
  pose proof (kerr_bound P l Ubf om_w7x w0 K0 HP Hw FK0 srcs0 HU C0 Cl CU w0 (MU + eU) BR BZ Hw' BUf EBR EBZ) as BE.
  assert (BE0 : vbound w0 eps0 (kerr (lmodel P l Ubf) om_w7x K0)).
  { destruct BE as [E1 E2]. split; apply (nbound_le _ ((MU + eU) * Rmax BR BZ)); assumption. }
  (* the twist *)
  pose (Jt := fun i => jsel i (tot P l K0)).
  pose (Jf := tJf Pn (JC.jd_sJ jd) (JC.jd_Kj1 jd) (JC.jd_Kj2 jd) (JC.jd_rowsJ jd)).
  assert (Hnj : forall i, nbound w0 (nj i) (Jf i)) by (intros i; exact (nbound_cden w0 (nth i fJs []))).
  assert (Hej : forall i, (i < 9)%nat -> nbound w0 (ej i) (fsub (Jt i) (Jf i)))
    by (intros i Hi; exact (jets_facts i Hi)).
  destruct (dv_diff w0 (vR K0) (lU P l Ubf K0) Ubf Jt Jf kR0 MU eU nj ej Hw' (nbound_cden w0 fR) (nbound_cden w0 fU)
              HeU Hnj Hej) as [D1 [D2 [D3 D4]]].
  pose proof (mbound_max4 _ _ _ _ _ _ D1 D2 D3 D4) as HeDV.
  destruct (dvf_norm w0 (vR K0) Ubf Jf kR0 MU nj Hw' (nbound_cden w0 fR) (nbound_cden w0 fU) Hnj)
    as [F1 [F2 [F3 F4]]].
  pose proof (mbound_max4 _ _ _ _ _ _ F1 F2 F3 F4) as HDVf.
  assert (Hkmf : vbound (w0 - d0) nkmf kmfin).
  { split; [apply (nbound_le _ xKR); [apply Rmax_l | exact TK1] | apply (nbound_le _ xKZ); [apply Rmax_r | exact TK2]]. }
  pose proof (twist_norm om_w7x w0 d0 (Sf (lmodel P l Ubf) K0) (Jf 1%nat) (DVf (lmodel P l Ubf) K0)
                (fDV (vR K0) Ubf Jf) (knrm K0 g0 bf) Nfin eNr nNf nkmf (nj 1%nat) (ej 1%nat) eDVr nDVr Sd ltac:(lra)
                HeN HNf Hkmf (Hnj 1%nat) (Hej 1%nat ltac:(lia)) HeDV HDVf xT TT1) as BT.
  pose proof (twist_mean om_w7x w0 d0 (Sf (lmodel P l Ubf) K0) (Jf 1%nat) (DVf (lmodel P l Ubf) K0)
                (fDV (vR K0) Ubf Jf) (knrm K0 g0 bf) Nfin eNr nNf nkmf (nj 1%nat) (ej 1%nat) eDVr nDVr Sd ltac:(lra)
                HeN HNf Hkmf (Hnj 1%nat) (Hej 1%nat ltac:(lia)) HeDV HDVf) as TMn.
  assert (BT0 : nbound (w0 - d0) T0 (ktwist (lmodel P l Ubf) om_w7x K0 g0 bf))
    by (apply (nbound_le _ (xT + eTr)); [exact HTT | exact BT]).
  assert (Htau0 : tau0 <= Rabs (fc (ktwist (lmodel P l Ubf) om_w7x K0 g0 bf) 0 0)).
  { assert (TM' : Rabs mean - eTr <= Rabs (fc (ktwist (lmodel P l Ubf) om_w7x K0 g0 bf) 0 0)) by exact TMn. lra. }
  (* the theorem *)
  assert (HgamA : 0 < 17 / 100 / IZR 5 <= 1) by (split; lra).
  destruct (field_kam_fourier P l Ubf om_w7x gamma (17 / 100 / IZR 5) K0 g0 bf w0 d0 r A0 G0 N0 T0 tau0 eps0 xA xG xN xB xTm
              xtau r10 r20 r30 MY MD0 th0 fy00 (bJ 0) (bJ 1) (bJ 2) (bJ 3) (bJ 4) (bJ 5) (bJ 6) (bJ 7) (bJ 8) kR0 MU BU
              HP Sd Sw Sr FK0 C0 S0 Q0 Cl CU EU QU src0_all
              (bJ_ok 0 ltac:(lia)) (bJ_ok 1 ltac:(lia)) (bJ_ok 2 ltac:(lia)) (bJ_ok 3 ltac:(lia)) (bJ_ok 4 ltac:(lia))
              (bJ_ok 5 ltac:(lia)) (bJ_ok 6 ltac:(lia)) (bJ_ok 7 ltac:(lia)) (bJ_ok 8 ltac:(lia))
              (nbound_cden w0 fR) (nbound_cden w0 fU) EBU HthU Hdio Sg om_dioph HgamA SA SG SN SB STm Stau Seps HAE
              Hsmall Cg0 Pg0 Cb Pb Qg0 Qb BB0 HA BG0 BN0 BE0 FI BT0 Htau0 HcA HcG HcN HcT Hrr Hctau2 Hsm_a0 Hsm_q0
              Hsm_g0 Hsm_n0 Hsm_w0) as [KR [KZ [HI HD]]].
  assert (E5 : P = 5%Z) by (unfold P; rewrite (proj1 cons_facts); reflexivity).
  exists KR, KZ. split; [rewrite <- E5; exact HI |].
  intros theta phi. destruct (HD theta phi) as [D1' D2'].
  split; (eapply Rle_trans; [eassumption | exact Hdel]).
Qed.

End Sound.

End Final.
