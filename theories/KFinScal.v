(** The scalar conditions of the KAM theorem for the coil field, over intervals.

    After the checks on grids, what [field_kam] still asks is a list of
    inequalities between numbers the checks bound: for every base source the
    two conditions of its seed on the ball and the two smallness conditions
    of its Taylor bounds ([src_final], [src_final_ok]); the condition on the
    inverse of B_phi over the ball; the bounds of the frame, of the error and
    of the twist, the twist bounded through the finite twist and the
    constants of KTwist.v ([ieDV], [ieT]); and the smallness conditions of
    the Newton iteration with its constants. [fin_scal] evaluates them over
    intervals and [fin_scal_ok] gives them over the reals. *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity FourierDFT
  FourierCanon FourierPer FourierSym FourierList FourierModel FourierSupp FourierModelPer KAMVec KAMFin KAMPer
  KAMStep KAMBound KAMUpdate KAMDiff KAMIter Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTaylor
  FieldTotal FieldCrude FieldBall FieldLine FieldConst FieldKAM KFix KCheckKern KEngine KDense KSrcReal KSrcRun
  KScal KTwist.
Import ListNotations.
Local Open Scope R_scope.

Module FinScal (J : RI).

Module SC := Scal J.
Import SC SC.SR SC.SR.E.TB SC.SR.E.TB.E SC.SR.E.TB.E.KO.

Ltac irs := repeat (first [assumption | apply inR_add | apply inR_sub | apply inR_mul | apply inR_abs | apply inR_neg
                          | apply inR_Z | exact inR_zero]).

Definition m1 : J.t := J.of_q (-1) 0.
Lemma m1_ok : inR m1 (-1). Proof. exact (inR_Z (-1)). Qed.

(** * The constants of the twist bound *)

Section Twist.

Variables (KRi MUi EUi : J.t) (NJ EJ : list J.t).

Definition jn (i : nat) : J.t := nth i NJ J.zero.
Definition je (i : nat) : J.t := nth i EJ J.zero.
Definition inJ (i : nat) : J.t := J.add (jn i) (je i).
Definition inU : J.t := J.add MUi EUi.
Definition ieW : J.t := J.add (J.mul J.zero inU) (J.mul KRi EUi).
Definition inWf : J.t := J.mul KRi MUi.
Definition ieUP (i : nat) : J.t := J.add (J.mul EUi (inJ i)) (J.mul MUi (je i)).
Definition inUP (i : nat) : J.t := J.mul inU (inJ i).
Definition inUPf (i : nat) : J.t := J.mul MUi (jn i).
Definition ieWUP (i : nat) : J.t := J.add (J.mul ieW (inUP i)) (J.mul inWf (ieUP i)).
Definition ieWR : J.t := J.add EUi (ieWUP 5).
Definition inWRf : J.t := J.add MUi (J.mul inWf (inUPf 5)).
Definition ieWZ : J.t := J.mul (J.abs m1) (ieWUP 6).
Definition inWZf : J.t := J.mul (J.abs m1) (J.mul inWf (inUPf 6)).
Definition ieDVc (eX nXf : J.t) (i j : nat) : J.t :=
  J.add (J.add (J.mul eX (inJ i)) (J.mul nXf (je i))) (J.add (J.mul ieW (inJ j)) (J.mul inWf (je j))).
Definition inDVc (nXf : J.t) (i j : nat) : J.t := J.add (J.mul nXf (jn i)) (J.mul inWf (jn j)).
Definition ieDV : J.t :=
  imax (imax (ieDVc ieWR inWRf 0 3) (ieDVc ieWZ inWZf 0 4)) (imax (ieDVc ieWR inWRf 2 7) (ieDVc ieWZ inWZf 2 8)).
Definition inDVf : J.t :=
  imax (imax (inDVc inWRf 0 3) (inDVc inWZf 0 4)) (imax (inDVc inWRf 2 7) (inDVc inWZf 2 8)).

Variables (kR MU eU : R) (nj ej : nat -> R).
Hypothesis HKR : inR KRi kR.
Hypothesis HMU : inR MUi MU.
Hypothesis HEU : inR EUi eU.
Hypothesis HNJ : forall i, inR (jn i) (nj i).
Hypothesis HEJ : forall i, inR (je i) (ej i).

Definition reDV : R :=
  Rmax (Rmax (eDVc kR MU eU nj ej (eWR kR MU eU nj ej) (nWRf kR MU nj) 0 3)
             (eDVc kR MU eU nj ej (eWZ kR MU eU nj ej) (nWZf kR MU nj) 0 4))
       (Rmax (eDVc kR MU eU nj ej (eWR kR MU eU nj ej) (nWRf kR MU nj) 2 7)
             (eDVc kR MU eU nj ej (eWZ kR MU eU nj ej) (nWZf kR MU nj) 2 8)).
Definition rnDVf : R :=
  Rmax (Rmax (nDVc kR MU nj (nWRf kR MU nj) 0 3) (nDVc kR MU nj (nWZf kR MU nj) 0 4))
       (Rmax (nDVc kR MU nj (nWRf kR MU nj) 2 7) (nDVc kR MU nj (nWZf kR MU nj) 2 8)).

Lemma twc_ok :
  inR (inJ 0) (nJ nj ej 0) /\ inR ieW (eW kR MU eU) /\ inR inWf (nWf kR MU) /\
  inR ieWR (eWR kR MU eU nj ej) /\ inR inWRf (nWRf kR MU nj) /\ inR ieWZ (eWZ kR MU eU nj ej) /\
  inR inWZf (nWZf kR MU nj).
Proof.
  pose proof m1_ok as M1.
  assert (NJi : forall i, inR (inJ i) (nJ nj ej i)) by (intros i; unfold inJ, nJ; irs; [apply HNJ | apply HEJ]).
  assert (NU : inR inU (nU MU eU)) by (unfold inU, nU; irs).
  assert (EW : inR ieW (eW kR MU eU)) by (unfold ieW, eW; irs).
  assert (NW : inR inWf (nWf kR MU)) by (unfold inWf, nWf; irs).
  assert (EUP : forall i, inR (ieUP i) (eUP MU eU nj ej i))
    by (intros i; pose proof (NJi i); pose proof (HEJ i); unfold ieUP, eUP; irs).
  assert (NUP : forall i, inR (inUP i) (nUP MU eU nj ej i))
    by (intros i; pose proof (NJi i); unfold inUP, nUP; irs).
  assert (NUPf : forall i, inR (inUPf i) (nUPf MU nj i))
    by (intros i; pose proof (HNJ i); unfold inUPf, nUPf; irs).
  assert (EWUP : forall i, inR (ieWUP i) (eWUP kR MU eU nj ej i))
    by (intros i; pose proof (EUP i); pose proof (NUP i); unfold ieWUP, eWUP; irs).
  pose proof (EWUP 5%nat). pose proof (EWUP 6%nat). pose proof (NUPf 5%nat). pose proof (NUPf 6%nat).
  refine (conj (NJi 0%nat) (conj EW (conj NW (conj _ (conj _ (conj _ _)))))).
  - unfold ieWR, eWR. irs.
  - unfold inWRf, nWRf. irs.
  - unfold ieWZ, eWZ. irs.
  - unfold inWZf, nWZf. irs.
Qed.

Lemma ieDV_ok : inR ieDV reDV /\ inR inDVf rnDVf.
Proof.
  destruct twc_ok as [_ [EW [NW [EWR [NWR [EWZ NWZ]]]]]].
  assert (NJi : forall i, inR (inJ i) (nJ nj ej i)) by (intros i; unfold inJ, nJ; irs; [apply HNJ | apply HEJ]).
  assert (Ec : forall eX nXf EX NXf i j, inR EX eX -> inR NXf nXf ->
             inR (ieDVc EX NXf i j) (eDVc kR MU eU nj ej eX nXf i j)).
  { intros. unfold ieDVc, eDVc. pose proof (NJi i). pose proof (NJi j). pose proof (HEJ i). pose proof (HEJ j). irs. }
  assert (Nc : forall nXf NXf i j, inR NXf nXf -> inR (inDVc NXf i j) (nDVc kR MU nj nXf i j)).
  { intros. unfold inDVc, nDVc. pose proof (HNJ i). pose proof (HNJ j). irs. }
  unfold ieDV, inDVf, reDV, rnDVf. split; repeat apply imax_ok; auto.
Qed.

End Twist.

(** * One source on the ball *)

Definition src_final (ssrc : Z) (NR0 NZ0 RR0 CS0 Rr HM : J.t)
    (xT : ((Z * Z * Z) * (Z * Z * Z)) * (J.t * J.t * J.t)) : bool * sdat :=
  let '(x, (TH, MY, Y00)) := xT in
  let '((p1, p2, p3), _) := x in
  let r1 := J.add (J.mul NR0 CS0) (J.abs (J.of_q p1 ssrc)) in
  let r2 := J.add (J.mul NR0 CS0) (J.abs (J.of_q p2 ssrc)) in
  let r3 := J.add NZ0 (J.abs (J.of_q p3 ssrc)) in
  let th := ibth RR0 r1 r2 r3 MY TH CS0 in
  let R10 := J.add r1 (J.mul RR0 CS0) in let R20 := J.add r2 (J.mul RR0 CS0) in let R30 := J.add r3 RR0 in
  let bt := ibth Rr R10 R20 R30 MY th CS0 in
  let D1 := J.add R10 (J.mul Rr CS0) in let D2 := J.add R20 (J.mul Rr CS0) in let D3 := J.add R30 Rr in
  let DY := ibyb Rr R10 R20 R30 MY th CS0 in
  (J.pos (J.sub one bt) && J.pos (J.sub Y00 (iinv_eps MY bt)) && itsmall HM D1 D2 D3 DY CS0,
   (SC.SR.E.i3q ssrc (snd x), (D1, D2, D3, DY))).

Section Sources.

Variables (P : Z) (Km Kn : nat) (s0 : Z) (rowsR rowsZ : list (list Z)) (Kr1 Kr2 N1s N2s Ky1 Ky2 : nat) (w0 r : R).

Definition fr10 (sy : src * fser) : R := r1k P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0 (fst sy).
Definition fr20 (sy : src * fser) : R := r2k P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0 (fst sy).
Definition fr30 (sy : src * fser) : R := r3k P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0 (fst sy).
Definition fMY (sy : src * fser) : R := MYr N1s N2s Ky1 Ky2 w0 sy.
Definition fth0 (sy : src * fser) : R := thk P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy.
Definition fy00 (sy : src * fser) : R := feval (snd sy) 0 0.

Definition fdr1 (sy : src * fser) : R := fr10 sy + r * wt w0 0 1.
Definition fdr2 (sy : src * fser) : R := fr20 sy + r * wt w0 0 1.
Definition fdr3 (sy : src * fser) : R := fr30 sy + r.
Definition fdyb (sy : src * fser) : R := byb r (fr10 sy) (fr20 sy) (fr30 sy) (fMY sy) (fth0 sy) (wt w0 0 1).

(** What the check of one source gives. *)
Definition sfin (sy : src * fser) : Prop :=
  bth r (fr10 sy) (fr20 sy) (fr30 sy) (fMY sy) (fth0 sy) (wt w0 0 1) < 1 /\
  inv_eps (fMY sy) (bth r (fr10 sy) (fr20 sy) (fr30 sy) (fMY sy) (fth0 sy) (wt w0 0 1)) 0 < fy00 sy /\
  2 * r * (2 * r) * tT1 (2 * r) (fdr1 sy) (fdr2 sy) (fdr3 sy) (fdyb sy) (wt w0 0 1) < 1 /\
  2 * r * tP1 (2 * r) (fdr1 sy) (fdr2 sy) (fdr3 sy) (fdyb sy) (wt w0 0 1) / 2
    + 2 * r * (2 * r) * tRB (2 * r) (fdr1 sy) (fdr2 sy) (fdr3 sy) (fdyb sy) (wt w0 0 1) < 1.

Definition trip_in (T : J.t * J.t * J.t) (sy : src * fser) : Prop :=
  inR (fst (fst T)) (THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy) /\
  inR (snd (fst T)) (MYr N1s N2s Ky1 Ky2 w0 sy) /\ inR (snd T) (feval (snd sy) 0 0).

Variables (ssrc : Z) (NR0 NZ0 RR0 CS0 Rr HM : J.t).
Hypothesis Hssrc : (0 <= ssrc)%Z.
Hypothesis HNR : inR NR0 (NRr P Km Kn s0 rowsR Kr1 Kr2 w0).
Hypothesis HNZ : inR NZ0 (NZr P Km Kn s0 rowsZ Kr1 Kr2 w0).
Hypothesis HRR : inR RR0 (rref P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0).
Hypothesis HCS : inR CS0 (wt w0 0 1).
Hypothesis HR : inR Rr r.
Hypothesis HHM : inR HM (2 * r).

Theorem src_final_ok (x : (Z * Z * Z) * (Z * Z * Z)) (T : J.t * J.t * J.t) (Y : fser) :
  trip_in T (src_of ssrc x, Y) -> fst (src_final ssrc NR0 NZ0 RR0 CS0 Rr HM (x, T)) = true ->
  sfin (src_of ssrc x, Y) /\ sd_in fdr1 fdr2 fdr3 fdyb (snd (src_final ssrc NR0 NZ0 RR0 CS0 Rr HM (x, T))) (src_of ssrc x, Y).
Proof.
  intros [HTH [HMY HY0]] Hc. destruct T as [[TH MY] Y00]. destruct x as [[[p1 p2] p3] [[e1 e2] e3]].
  cbn [fst snd] in HTH, HMY, HY0. unfold src_final in Hc |- *. cbv zeta in Hc |- *. cbn [fst snd] in Hc |- *.
  set (sy := (src_of ssrc (p1, p2, p3, (e1, e2, e3)), Y)) in *.
  assert (E1 : inR (J.add (J.mul NR0 CS0) (J.abs (J.of_q p1 ssrc))) (r1r P Km Kn s0 rowsR Kr1 Kr2 w0 (fst sy)))
    by (unfold r1r, sy; cbn [fst src_of sp1]; irs; apply inR_q, Hssrc).
  assert (E2 : inR (J.add (J.mul NR0 CS0) (J.abs (J.of_q p2 ssrc))) (r2r P Km Kn s0 rowsR Kr1 Kr2 w0 (fst sy)))
    by (unfold r2r, sy; cbn [fst src_of sp2]; irs; apply inR_q, Hssrc).
  assert (E3 : inR (J.add NZ0 (J.abs (J.of_q p3 ssrc))) (r3r P Km Kn s0 rowsZ Kr1 Kr2 w0 (fst sy)))
    by (unfold r3r, sy; cbn [fst src_of sp3]; irs; apply inR_q, Hssrc).
  set (r1 := J.add (J.mul NR0 CS0) (J.abs (J.of_q p1 ssrc))) in *.
  set (r2 := J.add (J.mul NR0 CS0) (J.abs (J.of_q p2 ssrc))) in *.
  set (r3 := J.add NZ0 (J.abs (J.of_q p3 ssrc))) in *.
  assert (HT0 : inR (ibth RR0 r1 r2 r3 MY TH CS0) (fth0 sy))
    by (unfold fth0, thk; apply ibth_ok; assumption).
  assert (H10 : inR (J.add r1 (J.mul RR0 CS0)) (fr10 sy)) by (unfold fr10, r1k, csw; irs).
  assert (H20 : inR (J.add r2 (J.mul RR0 CS0)) (fr20 sy)) by (unfold fr20, r2k, csw; irs).
  assert (H30 : inR (J.add r3 RR0) (fr30 sy)) by (unfold fr30, r3k; irs).
  set (th := ibth RR0 r1 r2 r3 MY TH CS0) in *.
  set (R10 := J.add r1 (J.mul RR0 CS0)) in *. set (R20 := J.add r2 (J.mul RR0 CS0)) in *.
  set (R30 := J.add r3 RR0) in *.
  assert (HBT : inR (ibth Rr R10 R20 R30 MY th CS0) (bth r (fr10 sy) (fr20 sy) (fr30 sy) (fMY sy) (fth0 sy) (wt w0 0 1)))
    by (apply ibth_ok; assumption).
  apply andb_prop in Hc. destruct Hc as [Hc Hsm]. apply andb_prop in Hc. destruct Hc as [C1 C2].
  pose proof (inR_pos _ _ C1 (inR_sub _ _ _ _ one_ok HBT)) as P1.
  assert (Hb : bth r (fr10 sy) (fr20 sy) (fr30 sy) (fMY sy) (fth0 sy) (wt w0 0 1) < 1) by lra.
  pose proof (iinv_eps_ok MY _ _ _ HMY HBT Hb) as HIE.
  pose proof (inR_pos _ _ C2 (inR_sub _ _ _ _ HY0 HIE)) as P2.
  assert (HD1 : inR (J.add R10 (J.mul Rr CS0)) (fdr1 sy)) by (unfold fdr1; irs).
  assert (HD2 : inR (J.add R20 (J.mul Rr CS0)) (fdr2 sy)) by (unfold fdr2; irs).
  assert (HD3 : inR (J.add R30 Rr) (fdr3 sy)) by (unfold fdr3; irs).
  assert (HDY : inR (ibyb Rr R10 R20 R30 MY th CS0) (fdyb sy)) by (unfold fdyb; apply ibyb_ok; assumption).
  destruct (itsmall_ok _ _ _ _ _ _ _ _ _ _ _ _ HHM HD1 HD2 HD3 HDY HCS Hsm) as [S1 S2].
  split.
  - refine (conj Hb (conj _ (conj S1 S2))). unfold fy00, fMY in *. cbn [snd sy] in *. lra.
  - split; [| exact (conj HD1 (conj HD2 (conj HD3 HDY)))].
    cbn [snd fst SC.SR.E.i3q sy src_of sd1 sd2 sd3]. unfold inR3. split; [| split]; apply inR_q, Hssrc.
Qed.

End Sources.

(** * The scalar conditions *)

Definition half : J.t := J.of_q 1 1.
Lemma half_ok' : inR half (/ 2).
Proof.
  pose proof (inR_q 1 1 ltac:(lia)) as H. change (2 ^ 1)%Z with 2%Z in H.
  replace (/ 2) with (IZR 1 / IZR 2) by field. exact H.
Qed.

Section Check.

Variables (P : Z) (IR IW0 ID0 IEPS IDEL IA0 IG0 IN0 IT0 ITAU0 IXA IXG IXN IXB IXTM IXTAU : J.t).
Variables (CS0 E1 OM GM : J.t) (KR0i MUi MGi NARi NAZi NBi : J.t) (NJ : list J.t).
Variables (IBR IBZ IBU IBG : J.t) (IBJ : list J.t) (TNR TNZ TKR TKZ TT TMEAN : J.t) (Ss : list sdat).

Definition iHM : J.t := J.mul two IR.
Definition iJb : ijet9 := mkij9 (inJ NJ IBJ 0) (inJ NJ IBJ 1) (inJ NJ IBJ 2) (inJ NJ IBJ 3) (inJ NJ IBJ 4) (inJ NJ IBJ 5)
                                (inJ NJ IBJ 6) (inJ NJ IBJ 7) (inJ NJ IBJ 8).
Definition iC : ikcon :=
  mkik IXA IXG IXN IXB (ibBP P IR iHM CS0 Ss iJb) (ibS1 P IR iHM CS0 Ss iJb) (ibDV P IR iHM CS0 Ss iJb KR0i MUi IBU)
       (ibMV P IR iHM CS0 Ss iJb KR0i MUi IBU) (ibM2 P IR iHM CS0 Ss iJb KR0i MUi IBU) IXTM IXTAU
       (iLBP P IR iHM CS0 Ss iJb) (ibLD P IR iHM CS0 Ss iJb KR0i MUi IBU).
Definition iEU : J.t := iinv_eps MUi IBU.
Definition iEG : J.t := iinv_eps MGi IBG.
Definition iEN : J.t := J.mul iEG IA0.
Definition iNNF : J.t := imax TNR TNZ.
Definition iNKMF : J.t := imax TKR TKZ.
Definition iEDV : J.t := ieDV KR0i MUi iEU NJ IBJ.
Definition iNDVF : J.t := inDVf KR0i MUi NJ.
Definition iCL : J.t := J.mul (J.add (J.abs OM) (J.of_q 10 0)) (J.div one (J.mul E1 ID0)).
Definition iNNX : J.t := J.add iNNF iEN.
Definition iEKM : J.t := J.add (J.mul iCL iEN) (J.mul two (J.add (J.mul iEDV iNNX) (J.mul iNDVF iEN))).
Definition iNKM : J.t := J.add iNKMF iEKM.
Definition iET : J.t :=
  J.add (J.mul (je IBJ 1) (J.mul two (J.mul iNKM iNNX))) (J.mul (jn NJ 1) (J.mul two (J.add (J.mul iEKM iNNX) (J.mul iNKMF iEN)))).
Definition iEPSX : J.t := J.mul (J.add MUi (iinv_eps MUi IBU)) (imax IBR IBZ).

Definition fin_frame : bool :=
  J.pos (J.sub one (ithU P IR iHM CS0 Ss iJb MUi IBU)) && J.pos (J.sub one IBU) && J.pos (J.sub one IBG) &&
  ile NARi IA0 && ile NAZi IA0 && ile (J.add MGi iEG) IG0 && ile (J.add iNNF iEN) IN0 && ile NBi IXB &&
  ile iEPSX IEPS && ile (J.add TT iET) IT0 && ile ITAU0 (J.sub (J.abs TMEAN) iET).

Definition fin_pos : bool :=
  J.nonneg IXA && J.nonneg IXG && J.nonneg IXN && J.nonneg IXB && J.nonneg IXTM && J.pos IXTAU && J.nonneg IEPS &&
  J.pos IR && J.pos ID0 && J.pos (J.sub IW0 (J.mul (J.of_q 6 0) ID0)) && J.pos GM && ile GM one.

Definition fin_kam : bool :=
  let C := iC in
  J.pos (ikE C E1 GM ID0) && ile (J.mul (J.mul (ikE C E1 GM ID0) (J.of_q 16 0)) IEPS) half &&
  ile (J.add IA0 (J.mul two (J.mul (ikdA C E1 GM ID0) IEPS))) IXA &&
  ile (J.add IG0 (J.mul two (J.mul (ikdG C E1 GM ID0) IEPS))) IXG &&
  ile (J.add IN0 (J.mul two (J.mul (ikdN C E1 GM ID0) IEPS))) IXN &&
  ile (J.add IT0 (J.mul two (J.mul (ikT C E1 OM GM ID0) IEPS))) IXTM &&
  ile (J.mul two (J.mul (ikP C E1 GM ID0) IEPS)) IR &&
  ile IXTAU (J.sub ITAU0 (J.mul two (J.mul (ikT C E1 OM GM ID0) IEPS))) &&
  ile (J.mul (ikdA C E1 GM ID0) IEPS) IXA && ile (J.mul IXG (J.mul (ikU C E1 GM ID0) IEPS)) half &&
  ile (J.mul (ikdG C E1 GM ID0) IEPS) IXG && ile (J.mul (ikdN C E1 GM ID0) IEPS) IXN &&
  ile (J.mul (ikdW C E1 OM GM ID0) IEPS) (ikW C E1 OM ID0) &&
  ile (J.mul two (J.mul (ikP C E1 GM ID0) IEPS)) IDEL.

Definition fin_scal : bool := fin_frame && fin_pos && fin_kam.

(** Each condition of [fin_scal] on its own, and the enclosures they compare,
    for the report of a run. *)
Definition fin_bools : list bool :=
  let C := iC in
  [J.pos (J.sub one (ithU P IR iHM CS0 Ss iJb MUi IBU)); J.pos (J.sub one IBU); J.pos (J.sub one IBG);
   ile NARi IA0; ile NAZi IA0; ile (J.add MGi iEG) IG0; ile (J.add iNNF iEN) IN0; ile NBi IXB;
   ile iEPSX IEPS; ile (J.add TT iET) IT0; ile ITAU0 (J.sub (J.abs TMEAN) iET);
   J.nonneg IXA; J.nonneg IXG; J.nonneg IXN; J.nonneg IXB; J.nonneg IXTM; J.pos IXTAU; J.nonneg IEPS;
   J.pos IR; J.pos ID0; J.pos (J.sub IW0 (J.mul (J.of_q 6 0) ID0)); J.pos GM; ile GM one;
   J.pos (ikE C E1 GM ID0); ile (J.mul (J.mul (ikE C E1 GM ID0) (J.of_q 16 0)) IEPS) half;
   ile (J.add IA0 (J.mul two (J.mul (ikdA C E1 GM ID0) IEPS))) IXA;
   ile (J.add IG0 (J.mul two (J.mul (ikdG C E1 GM ID0) IEPS))) IXG;
   ile (J.add IN0 (J.mul two (J.mul (ikdN C E1 GM ID0) IEPS))) IXN;
   ile (J.add IT0 (J.mul two (J.mul (ikT C E1 OM GM ID0) IEPS))) IXTM;
   ile (J.mul two (J.mul (ikP C E1 GM ID0) IEPS)) IR;
   ile IXTAU (J.sub ITAU0 (J.mul two (J.mul (ikT C E1 OM GM ID0) IEPS)));
   ile (J.mul (ikdA C E1 GM ID0) IEPS) IXA; ile (J.mul IXG (J.mul (ikU C E1 GM ID0) IEPS)) half;
   ile (J.mul (ikdG C E1 GM ID0) IEPS) IXG; ile (J.mul (ikdN C E1 GM ID0) IEPS) IXN;
   ile (J.mul (ikdW C E1 OM GM ID0) IEPS) (ikW C E1 OM ID0);
   ile (J.mul two (J.mul (ikP C E1 GM ID0) IEPS)) IDEL].

Definition fin_vals : list J.t :=
  let C := iC in
  [ithU P IR iHM CS0 Ss iJb MUi IBU; iEU; iEG; iEN; iNNF; iNKMF; iEDV; iNDVF; iCL; iEKM; iNKM; iET; iEPSX;
   ikE C E1 GM ID0; ikP C E1 GM ID0; ikT C E1 OM GM ID0; ikdA C E1 GM ID0; ikdG C E1 GM ID0; ikdN C E1 GM ID0;
   ikU C E1 GM ID0; ikdW C E1 OM GM ID0; ikW C E1 OM ID0;
   ibBP P IR iHM CS0 Ss iJb; ibS1 P IR iHM CS0 Ss iJb; ibDV P IR iHM CS0 Ss iJb KR0i MUi IBU;
   ibMV P IR iHM CS0 Ss iJb KR0i MUi IBU; ibM2 P IR iHM CS0 Ss iJb KR0i MUi IBU; iLBP P IR iHM CS0 Ss iJb;
   ibLD P IR iHM CS0 Ss iJb KR0i MUi IBU].

Definition fin_report : list bool * list J.t := (fin_bools, fin_vals).

Lemma frame_split : fin_frame = true ->
  J.pos (J.sub one (ithU P IR iHM CS0 Ss iJb MUi IBU)) = true /\ J.pos (J.sub one IBU) = true /\
  J.pos (J.sub one IBG) = true /\ ile NARi IA0 = true /\ ile NAZi IA0 = true /\ ile (J.add MGi iEG) IG0 = true /\
  ile (J.add iNNF iEN) IN0 = true /\ ile NBi IXB = true /\ ile iEPSX IEPS = true /\ ile (J.add TT iET) IT0 = true /\
  ile ITAU0 (J.sub (J.abs TMEAN) iET) = true.
Proof. unfold fin_frame. intros H. repeat rewrite Bool.andb_true_iff in H. tauto. Qed.

Lemma pos_split : fin_pos = true ->
  J.nonneg IXA = true /\ J.nonneg IXG = true /\ J.nonneg IXN = true /\ J.nonneg IXB = true /\ J.nonneg IXTM = true /\
  J.pos IXTAU = true /\ J.nonneg IEPS = true /\ J.pos IR = true /\ J.pos ID0 = true /\
  J.pos (J.sub IW0 (J.mul (J.of_q 6 0) ID0)) = true /\ J.pos GM = true /\ ile GM one = true.
Proof. unfold fin_pos. intros H. repeat rewrite Bool.andb_true_iff in H. tauto. Qed.

Lemma kam_split : fin_kam = true ->
  let C := iC in
  J.pos (ikE C E1 GM ID0) = true /\ ile (J.mul (J.mul (ikE C E1 GM ID0) (J.of_q 16 0)) IEPS) half = true /\
  ile (J.add IA0 (J.mul two (J.mul (ikdA C E1 GM ID0) IEPS))) IXA = true /\
  ile (J.add IG0 (J.mul two (J.mul (ikdG C E1 GM ID0) IEPS))) IXG = true /\
  ile (J.add IN0 (J.mul two (J.mul (ikdN C E1 GM ID0) IEPS))) IXN = true /\
  ile (J.add IT0 (J.mul two (J.mul (ikT C E1 OM GM ID0) IEPS))) IXTM = true /\
  ile (J.mul two (J.mul (ikP C E1 GM ID0) IEPS)) IR = true /\
  ile IXTAU (J.sub ITAU0 (J.mul two (J.mul (ikT C E1 OM GM ID0) IEPS))) = true /\
  ile (J.mul (ikdA C E1 GM ID0) IEPS) IXA = true /\ ile (J.mul IXG (J.mul (ikU C E1 GM ID0) IEPS)) half = true /\
  ile (J.mul (ikdG C E1 GM ID0) IEPS) IXG = true /\ ile (J.mul (ikdN C E1 GM ID0) IEPS) IXN = true /\
  ile (J.mul (ikdW C E1 OM GM ID0) IEPS) (ikW C E1 OM ID0) = true /\
  ile (J.mul two (J.mul (ikP C E1 GM ID0) IEPS)) IDEL = true.
Proof. unfold fin_kam. intros H. repeat rewrite Bool.andb_true_iff in H. tauto. Qed.

Section Sound.

Variables (l : list (src * fser)) (Km Kn : nat) (s0 : Z) (rowsR rowsZ : list (list Z)) (Kr1 Kr2 N1s N2s Ky1 Ky2 : nat).
Variables (w0 d0 r eps0 delta A0 G0 N0 T0 tau0 xA xG xN xB xTm xtau om gamma : R).
Variables (kR0 MU MG NAR NAZ NB BR BZ BU BG xNR xNZ xKR xKZ xT mean : R) (nj ej : nat -> R).
Hypothesis HR : inR IR r.
Hypothesis HW0 : inR IW0 w0.
Hypothesis HD0 : inR ID0 d0.
Hypothesis HEPS : inR IEPS eps0.
Hypothesis HDEL : inR IDEL delta.
Hypothesis HA0 : inR IA0 A0.
Hypothesis HG0 : inR IG0 G0.
Hypothesis HN0 : inR IN0 N0.
Hypothesis HT0 : inR IT0 T0.
Hypothesis HTAU0 : inR ITAU0 tau0.
Hypothesis HXA : inR IXA xA.
Hypothesis HXG : inR IXG xG.
Hypothesis HXN : inR IXN xN.
Hypothesis HXB : inR IXB xB.
Hypothesis HXTM : inR IXTM xTm.
Hypothesis HXTAU : inR IXTAU xtau.
Hypothesis HCS : inR CS0 (wt w0 0 1).
Hypothesis HE1 : inR E1 (exp 1).
Hypothesis HOM : inR OM om.
Hypothesis HGM : inR GM gamma.
Hypothesis HKR0 : inR KR0i kR0.
Hypothesis HMU : inR MUi MU.
Hypothesis HMG : inR MGi MG.
Hypothesis HNAR : inR NARi NAR.
Hypothesis HNAZ : inR NAZi NAZ.
Hypothesis HNB : inR NBi NB.
Hypothesis HNJ : forall i, inR (jn NJ i) (nj i).
Hypothesis HEJ : forall i, inR (je IBJ i) (ej i).
Hypothesis HBR : inR IBR BR.
Hypothesis HBZ : inR IBZ BZ.
Hypothesis HBU : inR IBU BU.
Hypothesis HBG : inR IBG BG.
Hypothesis HTNR : inR TNR xNR.
Hypothesis HTNZ : inR TNZ xNZ.
Hypothesis HTKR : inR TKR xKR.
Hypothesis HTKZ : inR TKZ xKZ.
Hypothesis HTT : inR TT xT.
Hypothesis HTM : inR TMEAN mean.
Hypothesis HBU0 : 0 <= BU.
Hypothesis HBG0 : 0 <= BG.
Hypothesis HMU0 : 0 <= MU.
Hypothesis HMG0 : 0 <= MG.

Let dr1 := fdr1 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0 r.
Let dr2 := fdr2 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0 r.
Let dr3 := fdr3 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0 r.
Let dyb := fdyb P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 r.
Hypothesis HS : Forall2 (sd_in dr1 dr2 dr3 dyb) Ss l.
Hypothesis Hsf : List.Forall (sfin P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 r) l.

Let bJ (i : nat) : R := nJ nj ej i.
Let kcf : kcon :=
  FieldKAM.kc P l w0 r xA xG xN xB xTm xtau (fr10 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0)
    (fr20 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0) (fr30 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0) (fMY N1s N2s Ky1 Ky2 w0)
    (fth0 P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0) (bJ 0) (bJ 1) (bJ 2) (bJ 3) (bJ 4) (bJ 5) (bJ 6) (bJ 7)
    (bJ 8) kR0 MU BU.

Let eU := inv_eps MU BU 0.
Let eg := inv_eps MG BG 0.
Let eNr := eg * A0.
Let nNf := Rmax xNR xNZ.
Let nkmf := Rmax xKR xKZ.
Let eDVr := reDV kR0 MU eU nj ej.
Let nDVr := rnDVf kR0 MU nj.
Let eTr := KTwist.eT om d0 eNr nNf nkmf (nj 1) (ej 1) eDVr nDVr.

Lemma Hsm : List.Forall (fun sy => 2 * r * (2 * r) * tT1 (2 * r) (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) (wt w0 0 1) < 1) l.
Proof. eapply Forall_impl; [| exact Hsf]. intros sy [_ [_ [A _]]]. exact A. Qed.

Lemma HHM' : inR iHM (2 * r). Proof. pose proof two_ok. unfold iHM. irs. Qed.

Lemma HJb : inR (ij_R iJb) (bJ 0) /\ inR (ij_P iJb) (bJ 1) /\ inR (ij_Z iJb) (bJ 2) /\ inR (ij_RR iJb) (bJ 3) /\
            inR (ij_RZ iJb) (bJ 4) /\ inR (ij_PR iJb) (bJ 5) /\ inR (ij_PZ iJb) (bJ 6) /\ inR (ij_ZR iJb) (bJ 7) /\
            inR (ij_ZZ iJb) (bJ 8).
Proof.
  assert (H : forall i, inR (inJ NJ IBJ i) (bJ i)) by (intros i; unfold inJ, bJ, nJ; apply inR_add; [apply HNJ | apply HEJ]).
  cbn [iJb ij_R ij_P ij_Z ij_RR ij_RZ ij_PR ij_PZ ij_ZR ij_ZZ]. repeat split; apply H.
Qed.

Theorem fin_scal_ok : fin_scal = true ->
  (* the ball *)
  thU P l r (2 * r) (wt w0 0 1) dr1 dr2 dr3 dyb (bJ 5) (bJ 6) MU BU < 1 /\ BU < 1 /\ BG < 1 /\
  (* the frame and the error *)
  NAR <= A0 /\ NAZ <= A0 /\ MG + eg <= G0 /\ nNf + eNr <= N0 /\ NB <= xB /\ (MU + eU) * Rmax BR BZ <= eps0 /\
  (* the twist *)
  xT + eTr <= T0 /\ tau0 <= Rabs mean - eTr /\
  (* signs *)
  0 <= xA /\ 0 <= xG /\ 0 <= xN /\ 0 <= xB /\ 0 <= xTm /\ 0 < xtau /\ 0 <= eps0 /\ 0 < r /\ 0 < d0 /\
  6 * d0 < w0 /\ 0 < gamma <= 1 /\
  (* the iteration *)
  0 < itA gamma d0 kcf /\ itA gamma d0 kcf * 16 * eps0 <= / 2 /\
  A0 + 2 * (kdA kcf gamma d0 * eps0) <= xA /\ G0 + 2 * (kdG kcf gamma d0 * eps0) <= xG /\
  N0 + 2 * (kdN kcf gamma d0 * eps0) <= xN /\ T0 + 2 * (kT kcf om gamma d0 * eps0) <= xTm /\
  2 * (kP kcf gamma d0 * eps0) <= r /\ xtau <= tau0 - 2 * (kT kcf om gamma d0 * eps0) /\
  kdA kcf gamma d0 * eps0 <= xA /\ xG * (kU kcf gamma d0 * eps0) <= / 2 /\ kdG kcf gamma d0 * eps0 <= xG /\
  kdN kcf gamma d0 * eps0 <= xN /\ kdW kcf om gamma d0 * eps0 <= kW kcf om d0 /\
  2 * (kP kcf gamma d0 * eps0) <= delta.
Proof.
  intros Hc. unfold fin_scal in Hc. apply andb_prop in Hc. destruct Hc as [Hc Hk]. apply andb_prop in Hc.
  destruct Hc as [Hf Hp].
  destruct (frame_split Hf) as [CthU [CBU [CBG [CAR [CAZ [CG [CN [CB [CE [CT Ctau]]]]]]]]]].
  destruct (pos_split Hp) as [PA [PG [PN [PB [PTm [Ptau [Peps [Pr [Pd [Pw [Pg Pg1]]]]]]]]]]].
  pose proof (inR_nonneg _ _ PA HXA) as SA. pose proof (inR_nonneg _ _ PG HXG) as SG.
  pose proof (inR_nonneg _ _ PN HXN) as SN. pose proof (inR_nonneg _ _ PB HXB) as SB.
  pose proof (inR_nonneg _ _ PTm HXTM) as STm. pose proof (inR_pos _ _ Ptau HXTAU) as Stau.
  pose proof (inR_nonneg _ _ Peps HEPS) as Seps. pose proof (inR_pos _ _ Pr HR) as Sr.
  pose proof (inR_pos _ _ Pd HD0) as Sd.
  pose proof (inR_pos _ _ Pw (inR_sub _ _ _ _ HW0 (inR_mul _ _ _ _ (inR_Z 6) HD0))) as Sw.
  pose proof (inR_pos _ _ Pg HGM) as Sg. pose proof (ile_correct _ _ _ _ Pg1 HGM one_ok) as Sg1.
  pose proof HHM' as HHM. pose proof HJb as HJ. pose proof Hsm as HSM.
  (* the model on the ball *)
  destruct (bB_ok P IR iHM CS0 Ss iJb MUi IBU l r (2 * r) (wt w0 0 1) dr1 dr2 dr3 dyb (bJ 0) (bJ 1) (bJ 2) (bJ 3)
              (bJ 4) (bJ 5) (bJ 6) (bJ 7) (bJ 8) MU BU HR HHM HCS HS HSM HJ HMU HBU) as [BS [BS1 [BTH BLS]]].
  pose proof (inR_pos _ _ CthU (inR_sub _ _ _ _ one_ok BTH)) as PthU.
  pose proof (inR_pos _ _ CBU (inR_sub _ _ _ _ one_ok HBU)) as PBU.
  pose proof (inR_pos _ _ CBG (inR_sub _ _ _ _ one_ok HBG)) as PBG.
  assert (TU : thU P l r (2 * r) (wt w0 0 1) dr1 dr2 dr3 dyb (bJ 5) (bJ 6) MU BU < 1) by lra.
  destruct (bModel_ok P IR iHM CS0 Ss iJb KR0i MUi IBU l r (2 * r) (wt w0 0 1) dr1 dr2 dr3 dyb (bJ 0) (bJ 1) (bJ 2)
              (bJ 3) (bJ 4) (bJ 5) (bJ 6) (bJ 7) (bJ 8) kR0 MU BU HR HHM HCS HS HSM HJ HKR0 HMU HBU TU)
    as [BMV [BDV [BLD BM2]]].
  (* the constants of the iteration *)
  assert (HC : kin iC kcf).
  { unfold kin. cbn [iC iA iG iN iB iS iS1 iD iMV iM2 iTm itau iLS iLD].
    refine (conj HXA (conj HXG (conj HXN (conj HXB (conj BS (conj BS1 (conj BDV (conj BMV (conj BM2 (conj HXTM
             (conj HXTAU (conj BLS BLD)))))))))))). }
  assert (Htau : 0 < ctau kcf) by exact Stau.
  destruct (kP_parts iC E1 GM ID0 kcf gamma d0 HC HE1 HGM HD0 Sg Sd Htau) as [_ [_ [_ [_ [_ KP]]]]].
  pose proof (ikE_ok iC E1 GM ID0 kcf gamma d0 HC HE1 HGM HD0 Sg Sd Htau) as KE.
  destruct (ikU_parts iC E1 GM ID0 kcf gamma d0 HC HE1 HGM HD0 Sg Sd Htau) as [KdA [KU [KdG KdN]]].
  destruct (ikT_parts iC E1 OM GM ID0 kcf om gamma d0 HC HE1 HOM HGM HD0 Sg Sd Htau) as [KW [KdW KT]].
  destruct (kam_split Hk) as [K1 [K2 [K3 [K4 [K5 [K6 [K7 [K8 [K9 [K10 [K11 [K12 [K13 K14]]]]]]]]]]]]].
  pose proof half_ok' as H2. pose proof (inR_Z 16) as H16. pose proof two_ok as HTW.
  (* the frame, the error and the twist *)
  assert (HEU : inR iEU eU) by (unfold iEU, eU; apply iinv_eps_ok; [exact HMU | exact HBU | lra]).
  assert (HEG : inR iEG eg) by (unfold iEG, eg; apply iinv_eps_ok; [exact HMG | exact HBG | lra]).
  assert (HEN : inR iEN eNr) by (unfold iEN, eNr; irs).
  assert (HNNF : inR iNNF nNf) by (unfold iNNF, nNf; apply imax_ok; assumption).
  assert (HNKMF : inR iNKMF nkmf) by (unfold iNKMF, nkmf; apply imax_ok; assumption).
  destruct (ieDV_ok KR0i MUi iEU NJ IBJ kR0 MU eU nj ej HKR0 HMU HEU HNJ HEJ) as [HEDV HNDVF].
  assert (HCL : inR iCL (cL om d0)).
  { unfold iCL, cL. apply inR_mul.
    - apply inR_add; [apply inR_abs, HOM |]. unfold kappa. rewrite Rinv_inv. exact (inR_Z 10).
    - pose proof (exp_pos 1) as He.
      replace (/ (exp 1 * d0)) with (1 / (exp 1 * d0)) by (field; split; lra).
      apply inR_div; [exact one_ok | irs | apply Rgt_not_eq, Rmult_lt_0_compat; lra]. }
  assert (HET : inR iET eTr).
  { unfold iET, eTr, KTwist.eT, nkm, ekm, nNx, iNKM, iEKM, iNNX. fold nNf nkmf eDVr nDVr.
    pose proof (HNJ 1%nat). pose proof (HEJ 1%nat). unfold iEDV, iNDVF. irs. }
  assert (HEPSX : inR iEPSX ((MU + eU) * Rmax BR BZ)).
  { unfold iEPSX, eU. apply inR_mul; [| apply imax_ok; assumption]. apply inR_add; [exact HMU |].
    apply iinv_eps_ok; [exact HMU | exact HBU | lra]. }
  split; [exact TU |]. split; [lra |]. split; [lra |].
  refine (conj (ile_correct _ _ _ _ CAR HNAR HA0) (conj (ile_correct _ _ _ _ CAZ HNAZ HA0) _)).
  refine (conj (ile_correct _ _ _ _ CG (inR_add _ _ _ _ HMG HEG) HG0) _).
  refine (conj (ile_correct _ _ _ _ CN (inR_add _ _ _ _ HNNF HEN) HN0) _).
  refine (conj (ile_correct _ _ _ _ CB HNB HXB) (conj (ile_correct _ _ _ _ CE HEPSX HEPS) _)).
  refine (conj (ile_correct _ _ _ _ CT (inR_add _ _ _ _ HTT HET) HT0) _).
  refine (conj (ile_correct _ _ _ _ Ctau HTAU0 (inR_sub _ _ _ _ (inR_abs _ _ HTM) HET)) _).
  refine (conj SA (conj SG (conj SN (conj SB (conj STm (conj Stau (conj Seps (conj Sr (conj Sd _))))))))).
  split; [lra |]. split; [exact (conj Sg Sg1) |].
  unfold itA.
  refine (conj (inR_pos _ _ K1 KE) _).
  refine (conj (ile_correct _ _ _ _ K2 (inR_mul _ _ _ _ (inR_mul _ _ _ _ KE H16) HEPS) H2) _).
  refine (conj (ile_correct _ _ _ _ K3 (inR_add _ _ _ _ HA0 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KdA HEPS))) HXA) _).
  refine (conj (ile_correct _ _ _ _ K4 (inR_add _ _ _ _ HG0 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KdG HEPS))) HXG) _).
  refine (conj (ile_correct _ _ _ _ K5 (inR_add _ _ _ _ HN0 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KdN HEPS))) HXN) _).
  refine (conj (ile_correct _ _ _ _ K6 (inR_add _ _ _ _ HT0 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KT HEPS))) HXTM) _).
  refine (conj (ile_correct _ _ _ _ K7 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KP HEPS)) HR) _).
  refine (conj (ile_correct _ _ _ _ K8 HXTAU (inR_sub _ _ _ _ HTAU0 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KT HEPS)))) _).
  refine (conj (ile_correct _ _ _ _ K9 (inR_mul _ _ _ _ KdA HEPS) HXA) _).
  refine (conj (ile_correct _ _ _ _ K10 (inR_mul _ _ _ _ HXG (inR_mul _ _ _ _ KU HEPS)) H2) _).
  refine (conj (ile_correct _ _ _ _ K11 (inR_mul _ _ _ _ KdG HEPS) HXG) _).
  refine (conj (ile_correct _ _ _ _ K12 (inR_mul _ _ _ _ KdN HEPS) HXN) _).
  refine (conj (ile_correct _ _ _ _ K13 (inR_mul _ _ _ _ KdW HEPS) KW) _).
  exact (ile_correct _ _ _ _ K14 (inR_mul _ _ _ _ HTW (inR_mul _ _ _ _ KP HEPS)) HDEL).
Qed.

End Sound.

End Check.

End FinScal.
