(** The check of the sources along the reference torus and of the crude
    norms along the first torus.

    On a grid of N1s x N2s points of the whole torus the reference torus is
    evaluated once; for every base source its seed is evaluated, the defect
    1 - q Y^2 is formed at every point, and the weighted transforms of the
    defect and of the seed give their exact bounds on the strip of the
    iteration and on the wide strip ([srcv_ok]); the value of the seed at
    the origin is read from its coefficients. The sources are checked in
    parallel. From these bounds and the norms of the reference torus and of
    its distance to the first torus, the scalar formulas of FieldBall.v and
    FieldCrude.v, evaluated over intervals ([ibth], [iinv_eps], [isRP], ...),
    give the conditions under which the seeds serve along the first torus
    and the crude norms of the field there ([src_run_ok]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity FourierDFT
  FourierCanon FourierPer FourierSym FourierList FourierModel FourierSupp FourierModelPer KAMVec KAMFin KAMPer
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTaylor FieldTotal FieldCrude FieldBall FieldLine
  KCheckErr KFix KCheckKern KEngine KTab KDense KGrid KSrc KSrcCheck KRef KCheckE0 KE0 KSrcReal.
Import ListNotations.
Local Open Scope R_scope.

Module SrcRun (J : RI).

Module E := E0Check J.
Module SC := SrcCheck J.
Module RO := RefOps J.
Import E.TB E.TB.E E.TB.E.KO.

Definition one : J.t := J.of_q 1 0.
Definition two : J.t := J.of_q 2 0.
Definition three : J.t := J.of_q 3 0.

Ltac ir := repeat (first [apply inR_add | apply inR_sub | apply inR_mul | apply inR_abs | apply inR_neg
                         | apply inR_Z | exact inR_zero | assumption]).

(** * The scalar formulas over intervals *)

Section Scalars.

Definition itE1 (hm r1 r2 r3 cs : J.t) : J.t :=
  J.add (J.mul two (J.add (J.add (J.mul r1 cs) (J.mul r2 cs)) r3)) (J.mul hm (J.add (J.mul two (J.mul cs cs)) one)).

Lemma itE1_ok (HM R1 R2 R3 CS : J.t) (hm r1 r2 r3 cs : R) :
  inR HM hm -> inR R1 r1 -> inR R2 r2 -> inR R3 r3 -> inR CS cs -> inR (itE1 HM R1 R2 R3 CS) (tE1 hm r1 r2 r3 cs).
Proof. intros. unfold itE1, tE1, one, two. ir. Qed.

Definition ibth (r r10 r20 r30 MY th0 cs : J.t) : J.t :=
  J.add th0 (J.mul (J.mul r (itE1 r r10 r20 r30 cs)) (J.mul MY MY)).

Lemma ibth_ok (Rr R10 R20 R30 MYi TH CS : J.t) (r r10 r20 r30 MY th0 cs : R) :
  inR Rr r -> inR R10 r10 -> inR R20 r20 -> inR R30 r30 -> inR MYi MY -> inR TH th0 -> inR CS cs ->
  inR (ibth Rr R10 R20 R30 MYi TH CS) (bth r r10 r20 r30 MY th0 cs).
Proof.
  intros. unfold ibth, bth, bE1. apply inR_add; [assumption |].
  apply inR_mul; [apply inR_mul; [assumption | apply itE1_ok; assumption] | apply inR_mul; assumption].
Qed.

Definition iinv_eps (Y0 q : J.t) : J.t := J.mul two (J.mul (J.div Y0 (J.sub one q)) (J.div (J.mul q one) (J.sub one q))).

Lemma iinv_eps_ok (Y Q : J.t) (y q : R) : inR Y y -> inR Q q -> q < 1 -> inR (iinv_eps Y Q) (inv_eps y q 0).
Proof.
  intros HY HQ Hq. unfold iinv_eps, inv_eps, inv_T, one, two. simpl pow.
  apply inR_mul; [apply inR_Z |]. apply inR_mul; apply inR_div; try lra; ir.
Qed.

(** The factors of one source's field, with its weighted tangent D. *)
Definition iC1 (D : i3) (r2 r3 : J.t) : J.t := let '(D1, D2, D3) := D in J.add (J.mul (J.abs D2) r3) (J.mul (J.abs D3) r2).
Definition iC2 (D : i3) (r1 r3 : J.t) : J.t := let '(D1, D2, D3) := D in J.add (J.mul (J.abs D3) r1) (J.mul (J.abs D1) r3).
Definition iC3 (D : i3) (r1 r2 : J.t) : J.t := let '(D1, D2, D3) := D in J.add (J.mul (J.abs D1) r2) (J.mul (J.abs D2) r1).
Definition iY3 (yb : J.t) : J.t := J.mul yb (J.mul yb yb).
Definition iY5 (yb : J.t) : J.t := J.mul (iY3 yb) (J.mul yb yb).
Definition iJ (yb d C r : J.t) : J.t := J.add (J.mul (J.abs d) (iY3 yb)) (J.mul (J.mul (J.mul three C) r) (iY5 yb)).

Definition d1 (D : i3) : J.t := let '(D1, _, _) := D in D1.
Definition d2 (D : i3) : J.t := let '(_, D2, _) := D in D2.
Definition d3 (D : i3) : J.t := let '(_, _, D3) := D in D3.

Definition isRP (D : i3) (cs r1 r2 r3 yb : J.t) : J.t := J.mul (J.mul (J.add (iC1 D r2 r3) (iC2 D r1 r3)) (iY3 yb)) cs.
Definition isZ (D : i3) (r1 r2 yb : J.t) : J.t := J.mul (iC3 D r1 r2) (iY3 yb).
Definition iE1 (D : i3) (cs r1 r2 r3 yb : J.t) : J.t :=
  J.mul (J.add (iJ yb J.zero (iC1 D r2 r3) r1) (iJ yb (d3 D) (iC1 D r2 r3) r2)) cs.
Definition iE2 (D : i3) (cs r1 r2 r3 yb : J.t) : J.t :=
  J.mul (J.add (iJ yb (d3 D) (iC2 D r1 r3) r1) (iJ yb J.zero (iC2 D r1 r3) r2)) cs.
Definition isRR (D : i3) (cs r1 r2 r3 yb : J.t) : J.t := J.mul (J.add (iE1 D cs r1 r2 r3 yb) (iE2 D cs r1 r2 r3 yb)) cs.
Definition isRZ (D : i3) (cs r1 r2 r3 yb : J.t) : J.t :=
  J.mul (J.add (iJ yb (d2 D) (iC1 D r2 r3) r3) (iJ yb (d1 D) (iC2 D r1 r3) r3)) cs.
Definition isZR (D : i3) (cs r1 r2 yb : J.t) : J.t :=
  J.mul (J.add (iJ yb (d2 D) (iC3 D r1 r2) r1) (iJ yb (d1 D) (iC3 D r1 r2) r2)) cs.
Definition isZZ (D : i3) (r1 r2 r3 yb : J.t) : J.t := iJ yb J.zero (iC3 D r1 r2) r3.

Variables (D : i3) (sc : src) (Y0 : fser) (CS R1 R2 R3 YB : J.t) (cs r1 r2 r3 yb : R).
Hypothesis HD : inR3 D (sd1 sc, sd2 sc, sd3 sc).
Hypothesis HCS : inR CS cs.
Hypothesis H1 : inR R1 r1.
Hypothesis H2 : inR R2 r2.
Hypothesis H3 : inR R3 r3.
Hypothesis HY : inR YB yb.

Lemma dd_ok : inR (d1 D) (sd1 sc) /\ inR (d2 D) (sd2 sc) /\ inR (d3 D) (sd3 sc).
Proof. destruct D as [[D1 D2] D3]. exact HD. Qed.

Lemma iC_ok : inR (iC1 D R2 R3) (cC1 sc r2 r3) /\ inR (iC2 D R1 R3) (cC2 sc r1 r3) /\ inR (iC3 D R1 R2) (cC3 sc r1 r2).
Proof.
  destruct D as [[D1 D2] D3]. destruct HD as [E1 [E2 E3]].
  unfold iC1, iC2, iC3, cC1, cC2, cC3. split; [| split]; ir.
Qed.

Lemma iY_ok : inR (iY3 YB) (cY3 yb) /\ inR (iY5 YB) (cY5 yb).
Proof. unfold iY5, iY3, cY5, cY3. split; ir. Qed.

Lemma iJ_ok (Dd Cc Rr : J.t) (d C r : R) : inR Dd d -> inR Cc C -> inR Rr r -> inR (iJ YB Dd Cc Rr) (cJ yb d C r).
Proof. intros. destruct iY_ok. unfold iJ, cJ, three. ir. Qed.

Lemma izero_abs : inR J.zero 0. Proof. exact inR_zero. Qed.

Theorem iterms_ok :
  inR (isRP D CS R1 R2 R3 YB) (sRP cs (fun _ => r1) (fun _ => r2) (fun _ => r3) (fun _ => yb) (sc, Y0)) /\
  inR (isZ D R1 R2 YB) (sZ (fun _ => r1) (fun _ => r2) (fun _ => yb) (sc, Y0)) /\
  inR (isRR D CS R1 R2 R3 YB) (sRR cs (fun _ => r1) (fun _ => r2) (fun _ => r3) (fun _ => yb) (sc, Y0)) /\
  inR (isRZ D CS R1 R2 R3 YB) (sRZ cs (fun _ => r1) (fun _ => r2) (fun _ => r3) (fun _ => yb) (sc, Y0)) /\
  inR (isZR D CS R1 R2 YB) (sZR cs (fun _ => r1) (fun _ => r2) (fun _ => yb) (sc, Y0)) /\
  inR (isZZ D R1 R2 R3 YB) (sZZ (fun _ => r1) (fun _ => r2) (fun _ => r3) (fun _ => yb) (sc, Y0)).
Proof.
  destruct dd_ok as [E1 [E2 E3]]. destruct iC_ok as [C1 [C2 C3]]. destruct iY_ok as [Y3 Y5].
  unfold isRP, isZ, isRR, isRZ, isZR, isZZ, iE1, iE2, sRP, sZ, sRR, sRZ, sZR, sZZ, cRR, cRZ, cE1, cE2, cE3.
  cbn [fst snd].
  repeat split; repeat (first [apply iJ_ok | apply inR_add | apply inR_mul | exact inR_zero | assumption]).
Qed.

End Scalars.

(** * Tables of a grid of the whole torus *)

(** cos and sin of the modes P l at the points of a grid of N points of the
    whole torus, from the step of the point b read at P b. *)
Definition TsP (Pn N Kn : nat) (s2 : J.t * J.t) : list (list (J.t * J.t)) :=
  map (fun b => ztab (step (base s2 N) N (Z.of_nat (Pn * b))) Kn) (seq 0 N).

Lemma tsp_ok (Pn N Kn : nat) (s2 : J.t * J.t) : (0 < N)%nat ->
  pinR s2 (cos (2 * PI / INR N), sin (2 * PI / INR N)) ->
  Forall2 (fun T b => tab_in T (pns (Z.of_nat Pn) Kn) (gpt N b)) (TsP Pn N Kn s2) (seq 0 N).
Proof.
  intros HN Hs. unfold TsP. apply forall2_self. intros b _.
  pose proof (step_ok s2 N (Z.of_nat (Pn * b)) HN Hs) as H.
  pose proof (ztab_ok _ _ Kn H) as HZ.
  unfold tab_in, pns. apply forall2_map_r. eapply Forall2_impl; [| exact HZ].
  intros CS l [C S].
  replace (IZR (Z.of_nat Pn * l) * gpt N b) with (IZR l * (IZR (Z.of_nat (Pn * b)) * gpt N 1)); [split; assumption |].
  unfold gpt. rewrite !mult_IZR, <- !INR_IZR_INZ, mult_INR. change (INR 1) with 1. field. apply not_0_INR. lia.
Qed.

Lemma gpt1 (N b : nat) : gpt (1 * N) b = gpt N b.
Proof. rewrite Nat.mul_1_l. reflexivity. Qed.

Lemma ggrid_pb (G : list (list J.t)) (N1 N2 : nat) (f : R -> R -> R) (ta pb pb' : nat -> R) :
  (forall b, pb b = pb' b) -> E.GO.ggrid G N1 N2 f ta pb -> E.GO.ggrid G N1 N2 f ta pb'.
Proof.
  intros Hb H. unfold E.GO.ggrid in *. eapply Forall2_impl; [| exact H]. intros Row a HR.
  replace (map (fun b => f (ta a) (pb' b)) (seq 0 N2)) with (map (fun b => f (ta a) (pb b)) (seq 0 N2)); [exact HR |].
  apply map_ext. intros b. rewrite Hb. reflexivity.
Qed.

(** * One source *)

Section Source.

Variables (Pn Km Kn Kr1 Kr2 N1s N2s Ky1 Ky2 : nat) (s0 sY ssrc : Z) (rowsR rowsZ : list (list Z)).
Variables (s1s s2s : J.t * J.t) (Ew0 Ewk0 Ew1 Ewk1 : J.t).

Let P : Z := Z.of_nat Pn.
Let K1x : nat := K1x Kr1 Ky1.
Let K2x : nat := K2x Kr2 Ky2.

Definition FRd : list (Z * list (Z * (J.t * J.t))) := E.DO.ifam s0 (zrange Km) (pns P Kn) (crows rowsR).
Definition FZd : list (Z * list (Z * (J.t * J.t))) := E.DO.ifam s0 (zrange Km) (pns P Kn) (srows rowsZ).

(** The tables and the reference torus on the grid, formed once. *)
Record stabs := mkstabs {
  st_GR : list (list J.t) ; st_GZ : list (list J.t) ; st_CS : list (J.t * J.t) ;
  st_TTY : list (list (J.t * J.t)) ; st_TsY : list (list (J.t * J.t)) ;
  st_CTx : list (list (J.t * J.t)) ; st_TKx : list (list (J.t * J.t)) ;
  st_CTy : list (list (J.t * J.t)) ; st_TKy : list (list (J.t * J.t)) ; st_INV : J.t ;
  st_WAx0 : list J.t ; st_WBx0 : list J.t ; st_WAx1 : list J.t ; st_WBx1 : list J.t ;
  st_WAy0 : list J.t ; st_WBy0 : list J.t ; st_WAy1 : list J.t ; st_WBy1 : list J.t }.

Definition stabs0 : stabs :=
  let TTK := E.TTs N1s Km s1s in let TsK := TsP Pn N2s Kn s2s in
  mkstabs (E.GO.gvals (RO.imask Kr1 Kr2 FRd) TTK TsK) (E.GO.gvals (RO.imask Kr1 Kr2 FZd) TTK TsK) (base s2s N2s)
    (E.TTs N1s Ky1 s1s) (E.Ts N2s Ky2 s2s)
    (E.CT N2s K2x s2s) (E.TK N1s K1x s1s) (E.CT N2s Ky2 s2s) (E.TK N1s Ky1 s1s) (E.inv_NM N1s N2s)
    (E.WA K1x Ew0) (E.WB K2x Ewk0) (E.WA K1x Ew1) (E.WB K2x Ewk1)
    (E.WA Ky1 Ew0) (E.WB Ky2 Ewk0) (E.WA Ky1 Ew1) (E.WB Ky2 Ewk1).

(** The exact bounds of the defect and of the seed on the two strips, and the
    value of the seed at the origin. *)
Definition srcv (T : stabs) (x : (Z * Z * Z) * (Z * Z * Z)) (rows : list (list (Z * Z))) : J.t * J.t * J.t * J.t * J.t :=
  let FY := E.DO.ifam sY (zrange Ky1) (pns 1 Ky2) rows in
  let GY := E.GO.gvals FY (st_TTY T) (st_TsY T) in
  let Gd := SC.dgrid (E.i3q ssrc (fst x)) (st_CS T) (st_GR T) (st_GZ T) GY in
  let GHd := GHt K2x Gd (st_CTx T) in
  let GHy := GHt Ky2 GY (st_CTy T) in
  (ibox_xt K1x K2x (st_TKx T) (st_INV T) (st_WAx0 T) (st_WBx0 T) GHd,
   ibox_xt K1x K2x (st_TKx T) (st_INV T) (st_WAx1 T) (st_WBx1 T) GHd,
   ibox_xt Ky1 Ky2 (st_TKy T) (st_INV T) (st_WAy0 T) (st_WBy0 T) GHy,
   ibox_xt Ky1 Ky2 (st_TKy T) (st_INV T) (st_WAy1 T) (st_WBy1 T) GHy,
   ival (SC.t0 (length (zrange Ky1))) (iABs FY (SC.t0 (length (pns 1 Ky2))))).

Section Sound.

Variables (w0 w1 : R).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1s)%nat.
Hypothesis HN2 : (0 < N2s)%nat.
Hypothesis HN1x : (2 * K1x < N1s)%nat.
Hypothesis HN2x : (2 * K2x < N2s)%nat.
Hypothesis Hs0 : (0 <= s0)%Z.
Hypothesis HsY : (0 <= sY)%Z.
Hypothesis Hssrc : (0 <= ssrc)%Z.
Hypothesis LR : length rowsR = length (zrange Km).
Hypothesis LZ : length rowsZ = length (zrange Km).
Hypothesis LRn : List.Forall (fun r => length r = length (pns P Kn)) rowsR.
Hypothesis LZn : List.Forall (fun r => length r = length (pns P Kn)) rowsZ.
Hypothesis Hs1 : pinR s1s (cos (2 * PI / INR N1s), sin (2 * PI / INR N1s)).
Hypothesis Hs2 : pinR s2s (cos (2 * PI / INR N2s), sin (2 * PI / INR N2s)).
Hypothesis HEw0 : inR Ew0 (exp w0).
Hypothesis HEwk0 : inR Ewk0 (exp (w0 * kappa)).
Hypothesis HEw1 : inR Ew1 (exp w1).
Hypothesis HEwk1 : inR Ewk1 (exp (w1 * kappa)).

Lemma exp_k1 (w : R) (X : J.t) : inR X (exp (w * kappa)) -> inR X (exp (w * (kappa * INR 1))).
Proof. intros H. replace (w * (kappa * INR 1)) with (w * kappa) by (simpl; ring). exact H. Qed.

Let Kr := Kref P Km Kn s0 rowsR rowsZ Kr1 Kr2.

Lemma grid_ref :
  E.GO.ggrid (st_GR stabs0) N1s N2s (fun t p => feval (vR Kr) t p) (gpt N1s) (gpt N2s) /\
  E.GO.ggrid (st_GZ stabs0) N1s N2s (fun t p => feval (vZ Kr) t p) (gpt N1s) (gpt N2s).
Proof.
  assert (HTT : Forall2 (fun TT a => tab_in TT (zrange Km) (gpt N1s a)) (E.TTs N1s Km s1s) (seq 0 N1s))
    by exact (E.tts_ok N1s Km s1s HN1 Hs1).
  pose proof (tsp_ok Pn N2s Kn s2s HN2 Hs2) as HTs.
  split.
  - apply (E.ggrid_ext _ _ _ (fun t p => feval (flist (dents (fam_map (gmask Kr1 Kr2) (fRf P Km Kn s0 rowsR)))) t p)).
    { intros t p. cbn [vR Kref Kr]. rewrite feval_cden. rewrite feval_dents. reflexivity. }
    apply (E.GO.gvals_ok _ _ (pns P Kn)).
    + apply RO.imask_in, E.DO.ifam_in, Hs0.
    + apply RO.fam_map_ns, dfam_ns, crows_len, LRn.
    + exact HTs.
    + unfold fRf. rewrite RO.fam_map_ks, dfam_ks; [exact HTT |]. unfold crows. rewrite length_map. exact LR.
  - apply (E.ggrid_ext _ _ _ (fun t p => feval (flist (dents (fam_map (gmask Kr1 Kr2) (fZf P Km Kn s0 rowsZ)))) t p)).
    { intros t p. cbn [vZ Kref Kr]. rewrite feval_cden. rewrite feval_dents. reflexivity. }
    apply (E.GO.gvals_ok _ _ (pns P Kn)).
    + apply RO.imask_in, E.DO.ifam_in, Hs0.
    + apply RO.fam_map_ns, dfam_ns, srows_len, LZn.
    + exact HTs.
    + unfold fZf. rewrite RO.fam_map_ks, dfam_ks; [exact HTT |]. unfold srows. rewrite length_map. exact LZ.
Qed.

Theorem srcv_ok (x : (Z * Z * Z) * (Z * Z * Z)) (rows : list (list (Z * Z))) :
  length rows = length (zrange Ky1) -> List.Forall (fun r => length r = length (pns 1 Ky2)) rows ->
  let sy := (src_of ssrc x, yser sY Ky1 Ky2 rows) in
  let '(T0, T1, M0, M1, Y00) := srcv stabs0 x rows in
  inR T0 (THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy) /\
  inR T1 (THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w1 sy) /\
  inR M0 (MYr N1s N2s Ky1 Ky2 w0 sy) /\ inR M1 (MYr N1s N2s Ky1 Ky2 w1 sy) /\ inR Y00 (feval (snd sy) 0 0).
Proof.
  intros Hl1 Hl2 sy. unfold srcv, stabs0.
  cbn [st_GR st_GZ st_CS st_TTY st_TsY st_CTx st_TKx st_CTy st_TKy st_INV st_WAx0 st_WBx0 st_WAx1 st_WBx1
       st_WAy0 st_WBy0 st_WAy1 st_WBy1].
  set (FY := E.DO.ifam sY (zrange Ky1) (pns 1 Ky2) rows).
  set (fy := yfam sY Ky1 Ky2 rows).
  assert (IY : E.TB.E.fam_in FY fy) by (apply E.DO.ifam_in, HsY).
  assert (NY : List.Forall (fun kr => map fst (snd kr) = pns 1 Ky2) fy) by (apply dfam_ns, Hl2).
  assert (KY : map fst fy = zrange Ky1) by (apply dfam_ks, Hl1).
  assert (HPn1 : (0 < 1)%nat) by lia.
  assert (FYv : forall t p, feval (flist (dents fy)) t p = feval (snd sy) t p).
  { intros t p. cbn [snd sy]. unfold yser. rewrite feval_cden, feval_dents. reflexivity. }
  assert (GY : E.GO.ggrid (E.GO.gvals FY (E.TTs N1s Ky1 s1s) (E.Ts N2s Ky2 s2s)) N1s N2s
                 (fun t p => feval (snd sy) t p) (gpt N1s) (gpt (1 * N2s))).
  { apply (E.ggrid_ext _ _ _ (fun t p => feval (flist (dents fy)) t p)); [exact FYv |].
    apply (E.GO.gvals_ok FY fy (pns 1 Ky2)); [exact IY | exact NY | exact (E.ts_ok 1 N2s Ky2 s2s HPn1 HN2 Hs2) |].
    rewrite KY. exact (E.tts_ok N1s Ky1 s1s HN1 Hs1). }
  destruct grid_ref as [GR GZ].
  pose proof (ggrid_pb _ _ _ _ _ (gpt (1 * N2s)) (gpt N2s) (gpt1 N2s) GY) as GY'.
  assert (HCS : Forall2 (fun CS b => inR (fst CS) (cos (gpt N2s b)) /\ inR (snd CS) (sin (gpt N2s b)))
                        (base s2s N2s) (seq 0 N2s)).
  { pose proof (base_ok s2s N2s HN2 Hs2) as HB. apply forall2_map_r' in HB. exact HB. }
  assert (Hp : inR3 (E.i3q ssrc (fst x)) (spt (fst sy))).
  { destruct x as [[[p1 p2] p3] [[e1 e2] e3]]. cbn [fst snd sy src_of E.i3q spt sp1 sp2 sp3].
    unfold dy. split; [| split]; apply inR_q, Hssrc. }
  pose proof (SC.dgrid_ok _ (fst sy) _ _ _ _ N1s N2s _ _ _ (gpt N1s) (gpt N2s) Hp HCS GR GZ GY') as GD0.
  assert (Hdv : forall t p, SC.rdef (fst sy) (fun t p => feval (vR Kr) t p) (fun t p => feval (vZ Kr) t p)
                              (fun t p => feval (snd sy) t p) t p = feval (defect (fst sy) Kr (snd sy)) t p).
  { intros t p. unfold SC.rdef. symmetry. apply (defect_val (fst sy) Kr (snd sy) 1); [lra | apply Kref_fin |].
    exists (esum (ewt 0) (dents fy)). cbn [snd sy]. unfold yser. apply nbound_cden. }
  pose proof (E.ggrid_ext _ _ _ _ _ _ _ Hdv GD0) as GD1.
  pose proof (ggrid_pb _ _ _ _ _ (gpt N2s) (gpt (1 * N2s)) (fun b => eq_sym (gpt1 N2s b)) GD1) as GD.
  assert (Qd : forall a c b, (b < N2s)%nat ->
            feval (defect (fst sy) Kr (snd sy)) (gpt N1s a) (gpt (1 * N2s) (c * N2s + b))
            = feval (defect (fst sy) Kr (snd sy)) (gpt N1s a) (gpt (1 * N2s) b))
    by exact (per_grid 1 N1s N2s _ HPn1 HN2 (per1 _)).
  assert (QY : forall a c b, (b < N2s)%nat ->
            feval (snd sy) (gpt N1s a) (gpt (1 * N2s) (c * N2s + b)) = feval (snd sy) (gpt N1s a) (gpt (1 * N2s) b))
    by exact (per_grid 1 N1s N2s _ HPn1 HN2 (per1 _)).
  pose proof (E.ct_ok N2s K2x s2s HN2 Hs2) as CTx. pose proof (E.tk_ok N1s K1x s1s HN1 Hs1) as TKx.
  pose proof (E.ct_ok N2s Ky2 s2s HN2 Hs2) as CTy. pose proof (E.tk_ok N1s Ky1 s1s HN1 Hs1) as TKy.
  pose proof (E.inv_NM_ok 1 N1s N2s HN1 HN2) as HINV.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (ibox_x_rexact 1 N1s N2s K1x K2x _ HPn1 HN1 HN2 Qd _ GD _ _ _ CTx TKx HINV w0 _ _
             (E.wa_ok K1x w0 Ew0 HEw0) (E.wb_ok 1 K2x w0 Ewk0 (exp_k1 w0 Ewk0 HEwk0))).
  - exact (ibox_x_rexact 1 N1s N2s K1x K2x _ HPn1 HN1 HN2 Qd _ GD _ _ _ CTx TKx HINV w1 _ _
             (E.wa_ok K1x w1 Ew1 HEw1) (E.wb_ok 1 K2x w1 Ewk1 (exp_k1 w1 Ewk1 HEwk1))).
  - exact (ibox_x_rexact 1 N1s N2s Ky1 Ky2 _ HPn1 HN1 HN2 QY _ GY _ _ _ CTy TKy HINV w0 _ _
             (E.wa_ok Ky1 w0 Ew0 HEw0) (E.wb_ok 1 Ky2 w0 Ewk0 (exp_k1 w0 Ewk0 HEwk0))).
  - exact (ibox_x_rexact 1 N1s N2s Ky1 Ky2 _ HPn1 HN1 HN2 QY _ GY _ _ _ CTy TKy HINV w1 _ _
             (E.wa_ok Ky1 w1 Ew1 HEw1) (E.wb_ok 1 Ky2 w1 Ewk1 (exp_k1 w1 Ewk1 HEwk1))).
  - pose proof (SC.ival0_ok FY fy (pns 1 Ky2) IY NY) as H0. rewrite KY, FYv in H0. exact H0.
Qed.

End Sound.

End Source.

(** * The conditions of one source on a strip *)

Lemma csw_exp (w : R) : csw w = exp (w * kappa).
Proof. unfold csw, wt, msize. rewrite Rabs_R0, Rabs_R1. f_equal. ring. Qed.

(** From the norms NR, NZ of the reference torus, its distance RR to the
    first torus and the enclosure CS of cos p on the strip, and the bounds of
    one source's defect and seed and its seed at the origin: the flag of the
    two conditions and the bounds r1, r2, r3, |y| along the first torus. *)
Definition sscal (ssrc : Z) (NR NZ RR CS TH MY Y00 : J.t) (x : (Z * Z * Z) * (Z * Z * Z)) :
    bool * (J.t * J.t * J.t * J.t) :=
  let '((p1, p2, p3), _) := x in
  let r1 := J.add (J.mul NR CS) (J.abs (J.of_q p1 ssrc)) in
  let r2 := J.add (J.mul NR CS) (J.abs (J.of_q p2 ssrc)) in
  let r3 := J.add NZ (J.abs (J.of_q p3 ssrc)) in
  let th := ibth RR r1 r2 r3 MY TH CS in
  let ie := iinv_eps MY th in
  (J.pos (J.sub one th) && J.pos (J.sub Y00 ie),
   (J.add r1 (J.mul RR CS), J.add r2 (J.mul RR CS), J.add r3 RR, J.add MY ie)).

Section Scal.

Variables (P : Z) (Km Kn : nat) (s0 : Z) (rowsR rowsZ : list (list Z)) (Kr1 Kr2 N1s N2s Ky1 Ky2 : nat) (ssrc : Z).
Variables (w : R) (NR NZ RR CS : J.t).
Hypothesis HNR : inR NR (NRr P Km Kn s0 rowsR Kr1 Kr2 w).
Hypothesis HNZ : inR NZ (NZr P Km Kn s0 rowsZ Kr1 Kr2 w).
Hypothesis HRR : inR RR (rref P Km Kn s0 rowsR rowsZ Kr1 Kr2 w).
Hypothesis HCS : inR CS (csw w).
Hypothesis Hssrc : (0 <= ssrc)%Z.

Theorem sscal_ok (x : (Z * Z * Z) * (Z * Z * Z)) (Y : fser) (TH MY Y00 : J.t) :
  let sy := (src_of ssrc x, Y) in
  inR TH (THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w sy) -> inR MY (MYr N1s N2s Ky1 Ky2 w sy) ->
  inR Y00 (feval Y 0 0) ->
  fst (sscal ssrc NR NZ RR CS TH MY Y00 x) = true ->
  src_cond P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w sy /\
  let '(R1, R2, R3, YB) := snd (sscal ssrc NR NZ RR CS TH MY Y00 x) in
  inR R1 (kr1 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w sy) /\ inR R2 (kr2 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w sy) /\
  inR R3 (kr3 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w sy) /\ inR YB (ybk P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w sy).
Proof.
  intros sy HTH HMY HY0 Hc. destruct x as [[[p1 p2] p3] [[e1 e2] e3]].
  unfold sscal in *. cbn [fst snd] in Hc |- *.
  assert (E1 : inR (J.add (J.mul NR CS) (J.abs (J.of_q p1 ssrc))) (r1r P Km Kn s0 rowsR Kr1 Kr2 w (fst sy)))
    by (unfold r1r, sy; cbn [fst src_of sp1]; ir; apply inR_q, Hssrc).
  assert (E2 : inR (J.add (J.mul NR CS) (J.abs (J.of_q p2 ssrc))) (r2r P Km Kn s0 rowsR Kr1 Kr2 w (fst sy)))
    by (unfold r2r, sy; cbn [fst src_of sp2]; ir; apply inR_q, Hssrc).
  assert (E3 : inR (J.add NZ (J.abs (J.of_q p3 ssrc))) (r3r P Km Kn s0 rowsZ Kr1 Kr2 w (fst sy)))
    by (unfold r3r, sy; cbn [fst src_of sp3]; ir; apply inR_q, Hssrc).
  set (R1 := J.add (J.mul NR CS) (J.abs (J.of_q p1 ssrc))) in *.
  set (R2 := J.add (J.mul NR CS) (J.abs (J.of_q p2 ssrc))) in *.
  set (R3 := J.add NZ (J.abs (J.of_q p3 ssrc))) in *.
  pose proof (ibth_ok RR R1 R2 R3 MY TH CS _ _ _ _ _ _ _ HRR E1 E2 E3 HMY HTH HCS) as Hth.
  apply andb_prop in Hc. destruct Hc as [C1 C2].
  assert (Hlt : thk P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w sy < 1).
  { pose proof (inR_pos _ _ C1 (inR_sub _ _ _ _ (inR_Z 1) Hth)). unfold thk. lra. }
  pose proof (iinv_eps_ok MY (ibth RR R1 R2 R3 MY TH CS) _ _ HMY Hth Hlt) as Hie.
  split.
  - split; [exact Hlt |]. pose proof (inR_pos _ _ C2 (inR_sub _ _ _ _ HY0 Hie)). unfold thk. cbn [sy snd]. lra.
  - unfold kr1, kr2, kr3, r1k, r2k, r3k, ybk, byb. refine (conj _ (conj _ (conj _ _))).
    + apply inR_add; [exact E1 | apply inR_mul; assumption].
    + apply inR_add; [exact E2 | apply inR_mul; assumption].
    + apply inR_add; [exact E3 | exact HRR].
    + apply inR_add; [exact HMY | exact Hie].
Qed.

End Scal.

(** * All sources *)

Lemma col_ok {A : Type} (L : list A) (h : A -> bool * list J.t) (g : A -> list R) (i : nat) :
  (forall a, In a L -> fst (h a) = true -> Forall2 inR (snd (h a)) (g a) /\ (i < length (g a))%nat) ->
  forallb (fun a => fst (h a)) L = true ->
  encl (map (fun a => nth i (snd (h a)) J.zero) L) (map (fun a => nth i (g a) 0) L).
Proof.
  intros H Hb. induction L as [| a L IH]; [constructor |].
  cbn [forallb] in Hb. apply andb_prop in Hb. destruct Hb as [Ha Hb].
  cbn [map]. constructor.
  - destruct (H a (or_introl eq_refl) Ha) as [F Hi]. exact (forall2_nth inR _ _ J.zero 0 i F Hi).
  - apply IH; [intros b Hb' Hfb; apply H; [right; exact Hb' | exact Hfb] | exact Hb].
Qed.

Lemma lsum_map {A : Type} (f : A -> R) (g : list A) : lsum f g = rsuml (map f g).
Proof. reflexivity. Qed.

Lemma forallb_map' {A B : Type} (f : B -> bool) (g : A -> B) (l : list A) :
  forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. induction l as [| x l IH]; [reflexivity |]. cbn [map forallb]. rewrite IH. reflexivity. Qed.

Lemma one_abs1 : 1 + Rabs (-1) = 2. Proof. rewrite Rabs_left by lra. ring. Qed.
Lemma one_abs2 : 1 + Rabs 1 = 2. Proof. rewrite Rabs_R1. ring. Qed.

Section Run.

Variables (Pn Km Kn Kr1 Kr2 N1s N2s Ky1 Ky2 : nat) (s0 sY ssrc : Z) (rowsR rowsZ : list (list Z)).
Variables (s1s s2s : J.t * J.t) (Ew0 Ewk0 EwP0 Ew1 Ewk1 EwP1 : J.t).

Let P : Z := Z.of_nat Pn.
Let FR := FRd Pn Km Kn s0 rowsR.
Let FZ := FZd Pn Km Kn s0 rowsZ.

(** The norms of the reference torus and of the cleared modes on a strip. *)
Definition gnorms (Ew EwP : J.t) : J.t * J.t * J.t :=
  let WK := E.WA Km Ew in let WN := E.WB Kn EwP in
  (SC.iesum (RO.imask Kr1 Kr2 FR) WK WN, SC.iesum (RO.imask Kr1 Kr2 FZ) WK WN,
   J.add (SC.iesum (RO.itail Kr1 Kr2 FR) WK WN) (SC.iesum (RO.itail Kr1 Kr2 FZ) WK WN)).

(** One source: the flag of its checks, the terms of its field on the wide
    strip, and the bounds of its defect and seed on the strip of the
    iteration with its seed at the origin. *)
Definition src_one (T : stabs) (G0 G1 : J.t * J.t * J.t) (x : (Z * Z * Z) * (Z * Z * Z)) (rows : list (list (Z * Z))) :
    bool * list J.t :=
  let '(T0, T1, M0, M1, Y00) := srcv Kr1 Kr2 Ky1 Ky2 sY ssrc T x rows in
  let '(NR0, NZ0, RR0) := G0 in let '(NR1, NZ1, RR1) := G1 in
  let S0 := sscal ssrc NR0 NZ0 RR0 Ewk0 T0 M0 Y00 x in
  let S1 := sscal ssrc NR1 NZ1 RR1 Ewk1 T1 M1 Y00 x in
  let '(r1, r2, r3, yb) := snd S1 in
  let D := E.i3q ssrc (snd x) in
  (Nat.eqb (length rows) (length (zrange Ky1)) && forallb (fun r => Nat.eqb (length r) (length (pns 1 Ky2))) rows
     && fst S0 && fst S1,
   [isRP D Ewk1 r1 r2 r3 yb; isZ D r1 r2 yb; isRR D Ewk1 r1 r2 r3 yb; isRZ D Ewk1 r1 r2 r3 yb;
    isZR D Ewk1 r1 r2 yb; isZZ D r1 r2 r3 yb; T0; M0; Y00]).

(** Every source in parallel; the flag, the sums of the six terms, and the
    three bounds of every source in order. *)
Definition src_all (xs : list ((Z * Z * Z) * (Z * Z * Z))) (ys : list (list (list (Z * Z)))) : bool * list J.t :=
  let T := stabs0 Pn Km Kn Kr1 Kr2 N1s N2s Ky1 Ky2 s0 rowsR rowsZ s1s s2s Ew0 Ewk0 Ew1 Ewk1 in
  let G0 := gnorms Ew0 EwP0 in let G1 := gnorms Ew1 EwP1 in
  let res := pmap (fun xy => src_one T G0 G1 (fst xy) (snd xy)) (combine xs ys) in
  let col (i : nat) := isuml (map (fun r => nth i (snd r) J.zero) res) in
  (Nat.eqb (length xs) (length ys) && forallb fst res,
   [col 0; col 1; col 2; col 3; col 4; col 5]%nat ++ concat (map (fun r => skipn 6 (snd r)) res)).

Section Sound.

Variables (w0 w1 : R).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1s)%nat.
Hypothesis HN2 : (0 < N2s)%nat.
Hypothesis HN1x : (2 * K1x Kr1 Ky1 < N1s)%nat.
Hypothesis HN2x : (2 * K2x Kr2 Ky2 < N2s)%nat.
Hypothesis Hs0 : (0 <= s0)%Z.
Hypothesis HsY : (0 <= sY)%Z.
Hypothesis Hssrc : (0 <= ssrc)%Z.
Hypothesis LR : length rowsR = length (zrange Km).
Hypothesis LZ : length rowsZ = length (zrange Km).
Hypothesis LRn : List.Forall (fun r => length r = length (pns P Kn)) rowsR.
Hypothesis LZn : List.Forall (fun r => length r = length (pns P Kn)) rowsZ.
Hypothesis Hs1 : pinR s1s (cos (2 * PI / INR N1s), sin (2 * PI / INR N1s)).
Hypothesis Hs2 : pinR s2s (cos (2 * PI / INR N2s), sin (2 * PI / INR N2s)).
Hypothesis Hw0 : 0 < w0.
Hypothesis Hw1 : 0 < w1.
Hypothesis HEw0 : inR Ew0 (exp w0).
Hypothesis HEwk0 : inR Ewk0 (exp (w0 * kappa)).
Hypothesis HEwP0 : inR EwP0 (exp (w0 * (kappa * INR Pn))).
Hypothesis HEw1 : inR Ew1 (exp w1).
Hypothesis HEwk1 : inR Ewk1 (exp (w1 * kappa)).
Hypothesis HEwP1 : inR EwP1 (exp (w1 * (kappa * INR Pn))).

Lemma wn_ok (w : R) (EwP : J.t) : inR EwP (exp (w * (kappa * INR Pn))) ->
  Forall2 (fun X n => inR X (exp (w * (kappa * Rabs (IZR n))))) (E.WB Kn EwP) (pns P Kn).
Proof. intros H. unfold pns. apply forall2_map_r. exact (E.wb_ok Pn Kn w EwP H). Qed.

Theorem gnorms_ok (w : R) (Ew EwP : J.t) : inR Ew (exp w) -> inR EwP (exp (w * (kappa * INR Pn))) ->
  let '(NR, NZ, RR) := gnorms Ew EwP in
  inR NR (NRr P Km Kn s0 rowsR Kr1 Kr2 w) /\ inR NZ (NZr P Km Kn s0 rowsZ Kr1 Kr2 w) /\
  inR RR (rref P Km Kn s0 rowsR rowsZ Kr1 Kr2 w).
Proof.
  intros HEw HEwP. unfold gnorms.
  pose proof (E.wa_ok Km w Ew HEw) as HWK. pose proof (wn_ok w EwP HEwP) as HWN.
  assert (IR : E.TB.E.fam_in FR (fRf P Km Kn s0 rowsR)) by (apply E.DO.ifam_in, Hs0).
  assert (IZ : E.TB.E.fam_in FZ (fZf P Km Kn s0 rowsZ)) by (apply E.DO.ifam_in, Hs0).
  assert (NR : List.Forall (fun kr => map fst (snd kr) = pns P Kn) (fRf P Km Kn s0 rowsR))
    by (apply dfam_ns, crows_len, LRn).
  assert (NZ : List.Forall (fun kr => map fst (snd kr) = pns P Kn) (fZf P Km Kn s0 rowsZ))
    by (apply dfam_ns, srows_len, LZn).
  assert (KR : map fst (fRf P Km Kn s0 rowsR) = zrange Km)
    by (apply dfam_ks; unfold crows; rewrite length_map; exact LR).
  assert (KZ : map fst (fZf P Km Kn s0 rowsZ) = zrange Km)
    by (apply dfam_ks; unfold srows; rewrite length_map; exact LZ).
  refine (conj _ (conj _ _)).
  - apply (SC.iesum_ok _ _ (pns P Kn)); [apply RO.imask_in, IR | apply RO.fam_map_ns, NR | | exact HWN].
    rewrite RO.fam_map_ks, KR. exact HWK.
  - apply (SC.iesum_ok _ _ (pns P Kn)); [apply RO.imask_in, IZ | apply RO.fam_map_ns, NZ | | exact HWN].
    rewrite RO.fam_map_ks, KZ. exact HWK.
  - unfold rref. apply inR_add.
    + apply (SC.iesum_ok _ _ (pns P Kn)); [apply RO.itail_in, IR | apply RO.fam_map_ns, NR | | exact HWN].
      rewrite RO.fam_map_ks, KR. exact HWK.
    + apply (SC.iesum_ok _ _ (pns P Kn)); [apply RO.itail_in, IZ | apply RO.fam_map_ns, NZ | | exact HWN].
      rewrite RO.fam_map_ks, KZ. exact HWK.
Qed.

Let T := stabs0 Pn Km Kn Kr1 Kr2 N1s N2s Ky1 Ky2 s0 rowsR rowsZ s1s s2s Ew0 Ewk0 Ew1 Ewk1.

(** The real terms of one source's field on the wide strip, and its bounds on
    the strip of the iteration. *)
Definition rterms (sy : src * fser) : list R :=
  let r1 := kr1 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1 in let r2 := kr2 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1 in
  let r3 := kr3 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1 in
  let yb := ybk P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w1 in
  [sRP (csw w1) r1 r2 r3 yb sy; sZ r1 r2 yb sy; sRR (csw w1) r1 r2 r3 yb sy; sRZ (csw w1) r1 r2 r3 yb sy;
   sZR (csw w1) r1 r2 yb sy; sZZ r1 r2 r3 yb sy;
   THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy; MYr N1s N2s Ky1 Ky2 w0 sy; feval (snd sy) 0 0].

Theorem src_one_ok (G0 G1 : J.t * J.t * J.t) (x : (Z * Z * Z) * (Z * Z * Z)) (rows : list (list (Z * Z))) :
  (let '(NR, NZ, RR) := G0 in inR NR (NRr P Km Kn s0 rowsR Kr1 Kr2 w0) /\ inR NZ (NZr P Km Kn s0 rowsZ Kr1 Kr2 w0) /\
     inR RR (rref P Km Kn s0 rowsR rowsZ Kr1 Kr2 w0)) ->
  (let '(NR, NZ, RR) := G1 in inR NR (NRr P Km Kn s0 rowsR Kr1 Kr2 w1) /\ inR NZ (NZr P Km Kn s0 rowsZ Kr1 Kr2 w1) /\
     inR RR (rref P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1)) ->
  fst (src_one T G0 G1 x rows) = true ->
  let sy := (src_of ssrc x, yser sY Ky1 Ky2 rows) in
  src_cond P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy /\
  src_cond P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w1 sy /\
  Forall2 inR (snd (src_one T G0 G1 x rows)) (rterms sy).
Proof.
  intros HG0 HG1 Hc sy. unfold src_one in *.
  destruct G0 as [[NR0 NZ0] RR0]. destruct G1 as [[NR1 NZ1] RR1].
  destruct HG0 as [HNR0 [HNZ0 HRR0]]. destruct HG1 as [HNR1 [HNZ1 HRR1]].
  pose proof (srcv_ok Pn Km Kn Kr1 Kr2 N1s N2s Ky1 Ky2 s0 sY ssrc rowsR rowsZ s1s s2s Ew0 Ewk0 Ew1 Ewk1 w0 w1
                HPn HN1 HN2 HN1x HN2x Hs0 HsY Hssrc LR LZ LRn LZn Hs1 Hs2 HEw0 HEwk0 HEw1 HEwk1 x rows) as Hv.
  fold T in Hv, Hc |- *.
  destruct (srcv Kr1 Kr2 Ky1 Ky2 sY ssrc T x rows) as [[[[T0 T1] M0] M1] Y00] eqn:Ev.
  assert (HK0 : inR Ewk0 (csw w0)) by (rewrite csw_exp; exact HEwk0).
  assert (HK1 : inR Ewk1 (csw w1)) by (rewrite csw_exp; exact HEwk1).
  pose proof (sscal_ok P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 ssrc w0 NR0 NZ0 RR0 Ewk0 HNR0 HNZ0 HRR0 HK0
                Hssrc x (yser sY Ky1 Ky2 rows) T0 M0 Y00) as S0ok.
  pose proof (sscal_ok P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 ssrc w1 NR1 NZ1 RR1 Ewk1 HNR1 HNZ1 HRR1 HK1
                Hssrc x (yser sY Ky1 Ky2 rows) T1 M1 Y00) as S1ok.
  destruct (sscal ssrc NR0 NZ0 RR0 Ewk0 T0 M0 Y00 x) as [f0 v0] eqn:ES0.
  destruct (sscal ssrc NR1 NZ1 RR1 Ewk1 T1 M1 Y00 x) as [f1 [[[R1 R2] R3] YB]] eqn:ES1.
  cbn [fst snd] in Hc, S0ok, S1ok |- *.
  apply andb_prop in Hc. destruct Hc as [Hc Hc1]. apply andb_prop in Hc. destruct Hc as [Hc Hc0].
  apply andb_prop in Hc. destruct Hc as [HL1 HL2].
  apply Nat.eqb_eq in HL1.
  assert (HL2' : List.Forall (fun r => length r = length (pns 1 Ky2)) rows).
  { apply Forall_forall. intros r Hr. rewrite forallb_forall in HL2. apply Nat.eqb_eq, HL2, Hr. }
  specialize (Hv HL1 HL2'). destruct Hv as [HT0 [HT1 [HM0 [HM1 HY00]]]].
  destruct (S0ok HT0 HM0 HY00 Hc0) as [C0 _].
  destruct (S1ok HT1 HM1 HY00 Hc1) as [C1 [HR1 [HR2 [HR3 HYB]]]].
  refine (conj C0 (conj C1 _)).
  assert (HD : inR3 (E.i3q ssrc (snd x)) (sd1 (fst sy), sd2 (fst sy), sd3 (fst sy))).
  { destruct x as [[[p1 p2] p3] [[e1 e2] e3]]. cbn [fst snd sy src_of E.i3q sd1 sd2 sd3].
    unfold dy. split; [| split]; apply inR_q, Hssrc. }
  destruct (iterms_ok _ (fst sy) (snd sy) Ewk1 R1 R2 R3 YB _ _ _ _ _ HD HK1 HR1 HR2 HR3 HYB)
    as [A1 [A2 [A3 [A4 [A5 A6]]]]].
  unfold rterms. cbn [snd].
  apply Forall2_cons; [exact A1 |]. apply Forall2_cons; [exact A2 |]. apply Forall2_cons; [exact A3 |].
  apply Forall2_cons; [exact A4 |]. apply Forall2_cons; [exact A5 |]. apply Forall2_cons; [exact A6 |].
  apply Forall2_cons; [exact HT0 |]. apply Forall2_cons; [exact HM0 |]. apply Forall2_cons; [exact HY00 |].
  apply Forall2_nil.
Qed.

(** The six sums of the terms over the sources, then the three bounds of
    every source on the strip of the iteration. *)
Definition rsums (l : list (src * fser)) : list R :=
  let r1 := kr1 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1 in let r2 := kr2 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1 in
  let r3 := kr3 P Km Kn s0 rowsR rowsZ Kr1 Kr2 w1 in
  let yb := ybk P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w1 in
  [lsum (sRP (csw w1) r1 r2 r3 yb) l; lsum (sZ r1 r2 yb) l; lsum (sRR (csw w1) r1 r2 r3 yb) l;
   lsum (sRZ (csw w1) r1 r2 r3 yb) l; lsum (sZR (csw w1) r1 r2 yb) l; lsum (sZZ r1 r2 r3 yb) l] ++
  concat (map (fun sy => [THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy; MYr N1s N2s Ky1 Ky2 w0 sy;
                          feval (snd sy) 0 0]) l).

Lemma forall2_skipn {A B : Type} (Rel : A -> B -> Prop) (n : nat) (xs : list A) (ys : list B) :
  Forall2 Rel xs ys -> Forall2 Rel (skipn n xs) (skipn n ys).
Proof.
  revert xs ys. induction n as [| n IH]; intros xs ys H; [exact H |].
  destruct H as [| x y xs ys Hxy H]; [constructor | cbn [skipn]; apply IH, H].
Qed.

Lemma forall2_concat_map {A B C : Type} (Rel : B -> C -> Prop) (f : A -> list B) (g : A -> list C) (L : list A) :
  (forall a, In a L -> Forall2 Rel (f a) (g a)) -> Forall2 Rel (concat (map f L)) (concat (map g L)).
Proof.
  intros H. induction L as [| a L IH]; [constructor |]. cbn [map concat].
  apply Forall2_app; [apply H; left; reflexivity | apply IH; intros b Hb; apply H; right; exact Hb].
Qed.

Theorem src_all_ok (xs : list ((Z * Z * Z) * (Z * Z * Z))) (ys : list (list (list (Z * Z)))) :
  fst (src_all xs ys) = true ->
  let l := srcl ssrc sY Ky1 Ky2 xs ys in
  length xs = length ys /\
  List.Forall (fun sy => supp Ky1 Ky2 (snd sy) /\ is_canon (snd sy)) l /\
  crude_ok P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w0 /\
  crude_ok P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1 /\
  Forall2 inR (snd (src_all xs ys)) (rsums l).
Proof.
  intros Hc l. unfold src_all in *. cbv zeta in Hc |- *. fold T in Hc |- *. unfold pmap in *.
  cbn [fst snd] in Hc |- *. apply andb_prop in Hc. destruct Hc as [HL Hc]. apply Nat.eqb_eq in HL.
  pose proof (gnorms_ok w0 Ew0 EwP0 HEw0 HEwP0) as HG0. pose proof (gnorms_ok w1 Ew1 EwP1 HEw1 HEwP1) as HG1.
  set (G0 := gnorms Ew0 EwP0) in *. set (G1 := gnorms Ew1 EwP1) in *.
  set (h := fun xy : (Z * Z * Z) * (Z * Z * Z) * list (list (Z * Z)) => src_one T G0 G1 (fst xy) (snd xy)) in *.
  set (sy := fun xy : (Z * Z * Z) * (Z * Z * Z) * list (list (Z * Z)) => (src_of ssrc (fst xy), yser sY Ky1 Ky2 (snd xy))).
  assert (Hl : l = map sy (combine xs ys)) by reflexivity.
  rewrite forallb_map' in Hc.
  assert (Hone : forall xy, In xy (combine xs ys) -> fst (h xy) = true ->
            src_cond P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 (sy xy) /\
            src_cond P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w1 (sy xy) /\
            Forall2 inR (snd (h xy)) (rterms (sy xy))).
  { intros xy _ Hf. exact (src_one_ok G0 G1 (fst xy) (snd xy) HG0 HG1 Hf). }
  rewrite forallb_forall in Hc.
  refine (conj HL (conj _ (conj _ (conj _ _)))).
  - rewrite Hl. apply Forall_forall. intros s Hs. apply in_map_iff in Hs. destruct Hs as [xy [<- _]].
    split; [apply yser_supp | apply yser_canon].
  - unfold crude_ok. rewrite Hl. apply Forall_forall. intros s Hs. apply in_map_iff in Hs. destruct Hs as [xy [<- Hxy]].
    exact (proj1 (Hone xy Hxy (Hc _ Hxy))).
  - unfold crude_ok. rewrite Hl. apply Forall_forall. intros s Hs. apply in_map_iff in Hs. destruct Hs as [xy [<- Hxy]].
    exact (proj1 (proj2 (Hone xy Hxy (Hc _ Hxy)))).
  - assert (Hcol : forall i, (i < 6)%nat ->
              inR (isuml (map (fun xy => nth i (snd (h xy)) J.zero) (combine xs ys)))
                  (rsuml (map (fun xy => nth i (rterms (sy xy)) 0) (combine xs ys)))).
    { intros i Hi. apply isuml_ok. apply col_ok; [| rewrite forallb_forall; exact Hc].
      intros xy Hxy Hf. split; [exact (proj2 (proj2 (Hone xy Hxy Hf))) | unfold rterms; simpl; lia]. }
    unfold rsums. rewrite Hl, !lsum_map, !map_map. apply Forall2_app.
    + apply Forall2_cons; [apply (Hcol 0%nat); lia |]. apply Forall2_cons; [apply (Hcol 1%nat); lia |].
      apply Forall2_cons; [apply (Hcol 2%nat); lia |]. apply Forall2_cons; [apply (Hcol 3%nat); lia |].
      apply Forall2_cons; [apply (Hcol 4%nat); lia |]. apply Forall2_cons; [apply (Hcol 5%nat); lia |].
      apply Forall2_nil.
    + apply forall2_concat_map. intros xy Hxy.
      exact (forall2_skipn inR 6 _ _ (proj2 (proj2 (Hone xy Hxy (Hc _ Hxy))))).
Qed.

End Sound.

(** * The crude norms along the first torus and the claims they bound *)

Variables (Kmu Knu Kmg Kng : nat) (rowsU rowsG : list (list Z)) (OM IMR IMZ IMU IMG : J.t).

Definition FUd : list (Z * list (Z * (J.t * J.t))) := E.DO.ifam s0 (zrange Kmu) (pns P Knu) (crows rowsU).
Definition FGd : list (Z * list (Z * (J.t * J.t))) := E.DO.ifam s0 (zrange Kmg) (pns P Kng) (crows rowsG).

(** The verdict, and the crude norms on the wide strip: the nine components
    of the field and its R and Z derivatives, then the numerators of the
    error and the two defects. *)
Definition src_check (xs : list ((Z * Z * Z) * (Z * Z * Z))) (ys : list (list (list (Z * Z)))) : bool * list J.t :=
  let '(ok, cols) := src_all xs ys in
  let aP := J.abs (J.of_q P 0) in
  let tot (i : nat) := J.mul aP (J.mul two (nth i cols J.zero)) in
  let tR := tot 0%nat in let tP := tot 0%nat in let tZ := tot 1%nat in let tRR := tot 2%nat in let tRZ := tot 3%nat in
  let tPR := tot 2%nat in let tPZ := tot 3%nat in let tZR := tot 4%nat in let tZZ := tot 5%nat in
  let WK := E.WA Km Ew1 in let WN := E.WB Kn EwP1 in
  let dtR := SC.iesum (E.DO.ifam_dt FR) WK WN in let dpR := SC.iesum (E.DO.ifam_dp FR) WK WN in
  let dtZ := SC.iesum (E.DO.ifam_dt FZ) WK WN in let dpZ := SC.iesum (E.DO.ifam_dp FZ) WK WN in
  let KR := SC.iesum FR WK WN in
  let UB := SC.iesum FUd (E.WA Kmu Ew1) (E.WB Knu EwP1) in
  let GB := SC.iesum FGd (E.WA Kmg Ew1) (E.WB Kng EwP1) in
  let MR := J.add (J.mul tP (J.add (J.mul (J.abs OM) dtR) dpR)) (J.mul KR tR) in
  let MZ := J.add (J.mul tP (J.add (J.mul (J.abs OM) dtZ) dpZ)) (J.mul KR tZ) in
  let MU := J.add one (J.mul tP UB) in
  let MG := J.add one (J.mul (J.mul tP (J.add (J.mul dtR dtR) (J.mul dtZ dtZ))) GB) in
  (ok && ile MR IMR && ile MZ IMZ && ile MU IMU && ile MG IMG,
   [tR; tP; tZ; tRR; tRZ; tPR; tPZ; tZR; tZZ; MR; MZ; MU; MG] ++ skipn 6 cols).

Section Sound2.

Variables (w0 w1 om MwR MwZ MwU MwG : R).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1s)%nat.
Hypothesis HN2 : (0 < N2s)%nat.
Hypothesis HN1x : (2 * K1x Kr1 Ky1 < N1s)%nat.
Hypothesis HN2x : (2 * K2x Kr2 Ky2 < N2s)%nat.
Hypothesis Hs0 : (0 <= s0)%Z.
Hypothesis HsY : (0 <= sY)%Z.
Hypothesis Hssrc : (0 <= ssrc)%Z.
Hypothesis LR : length rowsR = length (zrange Km).
Hypothesis LZ : length rowsZ = length (zrange Km).
Hypothesis LU : length rowsU = length (zrange Kmu).
Hypothesis LG : length rowsG = length (zrange Kmg).
Hypothesis LRn : List.Forall (fun r => length r = length (pns P Kn)) rowsR.
Hypothesis LZn : List.Forall (fun r => length r = length (pns P Kn)) rowsZ.
Hypothesis LUn : List.Forall (fun r => length r = length (pns P Knu)) rowsU.
Hypothesis LGn : List.Forall (fun r => length r = length (pns P Kng)) rowsG.
Hypothesis Hs1 : pinR s1s (cos (2 * PI / INR N1s), sin (2 * PI / INR N1s)).
Hypothesis Hs2 : pinR s2s (cos (2 * PI / INR N2s), sin (2 * PI / INR N2s)).
Hypothesis Hw0 : 0 < w0.
Hypothesis Hw1 : 0 < w1.
Hypothesis HEw0 : inR Ew0 (exp w0).
Hypothesis HEwk0 : inR Ewk0 (exp (w0 * kappa)).
Hypothesis HEwP0 : inR EwP0 (exp (w0 * (kappa * INR Pn))).
Hypothesis HEw1 : inR Ew1 (exp w1).
Hypothesis HEwk1 : inR Ewk1 (exp (w1 * kappa)).
Hypothesis HEwP1 : inR EwP1 (exp (w1 * (kappa * INR Pn))).
Hypothesis HOM : inR OM om.
Hypothesis HIMR : inR IMR MwR.
Hypothesis HIMZ : inR IMZ MwZ.
Hypothesis HIMU : inR IMU MwU.
Hypothesis HIMG : inR IMG MwG.

Let fU : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmu) (pns P Knu) (crows rowsU).
Let fG : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmg) (pns P Kng) (crows rowsG).

Lemma fnorm_ok (Kx Ky : nat) (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) (w : R)
    (Ew EwP : J.t) :
  E.TB.E.fam_in F f -> List.Forall (fun kr => map fst (snd kr) = pns P Ky) f -> map fst f = zrange Kx ->
  inR Ew (exp w) -> inR EwP (exp (w * (kappa * INR Pn))) ->
  inR (SC.iesum F (E.WA Kx Ew) (E.WB Ky EwP)) (fnorm w f).
Proof.
  intros HF Hns Hks HE HEP. apply (SC.iesum_ok F f (pns P Ky)); [exact HF | exact Hns | | ].
  - rewrite Hks. exact (E.wa_ok Kx w Ew HE).
  - unfold pns. apply forall2_map_r. exact (E.wb_ok Pn Ky w EwP HEP).
Qed.

Theorem src_check_ok (xs : list ((Z * Z * Z) * (Z * Z * Z))) (ys : list (list (list (Z * Z)))) :
  fst (src_check xs ys) = true ->
  let l := srcl ssrc sY Ky1 Ky2 xs ys in
  let K := K0v P Km Kn s0 rowsR rowsZ in
  length xs = length ys /\
  List.Forall (fun sy => supp Ky1 Ky2 (snd sy) /\ is_canon (snd sy)) l /\
  crude_ok P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w0 /\
  crude_ok P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1 /\
  nbound w1 MwR (errF_R P l om K) /\ nbound w1 MwZ (errF_Z P l om K) /\
  nbound w1 MwU (defU P l K (cden fU)) /\ nbound w1 MwG (defG P l K (cden fG)) /\
  Forall2 inR (firstn 9 (snd (src_check xs ys)))
    [tR P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1; tP P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1;
     tZ P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1; tRR P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1;
     tRZ P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1; tPR P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1;
     tPZ P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1; tZR P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1;
     tZZ P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 l w1] /\
  Forall2 inR (skipn 13 (snd (src_check xs ys)))
    (concat (map (fun sy => [THr P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 w0 sy; MYr N1s N2s Ky1 Ky2 w0 sy;
                             feval (snd sy) 0 0]) l)).
Proof.
  intros Hc l K. unfold src_check in *.
  pose proof (src_all_ok w0 w1 HPn HN1 HN2 HN1x HN2x Hs0 HsY Hssrc LR LZ LRn LZn Hs1 Hs2 HEw0 HEwk0 HEwP0
                HEw1 HEwk1 HEwP1 xs ys) as HA.
  destruct (src_all xs ys) as [ok cols] eqn:Ea. cbv zeta in Hc |- *. cbn [fst snd] in Hc, HA |- *.
  apply andb_prop in Hc. destruct Hc as [Hc HcG]. apply andb_prop in Hc. destruct Hc as [Hc HcU].
  apply andb_prop in Hc. destruct Hc as [Hc HcZ]. apply andb_prop in Hc. destruct Hc as [Hok HcR].
  destruct (HA Hok) as [HL [Hsc [C0 [C1 Hcols]]]]. fold l in Hsc, C0, C1, Hcols.
  unfold rsums in Hcols.
  inversion Hcols as [| c0 s0' cs0 ss0 H0 Hc1]; subst. inversion Hc1 as [| c1 s1' cs1 ss1 H1 Hc2]; subst.
  inversion Hc2 as [| c2 s2' cs2 ss2 H2 Hc3]; subst. inversion Hc3 as [| c3 s3' cs3 ss3 H3 Hc4]; subst.
  inversion Hc4 as [| c4 s4' cs4 ss4 H4 Hc5]; subst. inversion Hc5 as [| c5 s5' cs5 ss5 H5 Hc6]; subst.
  cbn [nth] in *.
  assert (Hsum : forall (X : J.t) (x : R), inR X x ->
            inR (J.mul (J.abs (J.of_q P 0)) (J.mul two X)) (Rabs (IZR P) * ((1 + Rabs (-1)) * x)) /\
            inR (J.mul (J.abs (J.of_q P 0)) (J.mul two X)) (Rabs (IZR P) * ((1 + Rabs 1) * x))).
  { intros X x HX. rewrite one_abs1, one_abs2. split; apply inR_mul; [apply inR_abs, inR_Z | apply inR_mul; [apply inR_Z | exact HX]
                                                           | apply inR_abs, inR_Z | apply inR_mul; [apply inR_Z | exact HX]]. }
  destruct (Hsum _ _ H0) as [TR TP]. destruct (Hsum _ _ H1) as [_ TZ]. destruct (Hsum _ _ H2) as [TRR TPR].
  destruct (Hsum _ _ H3) as [TPZ TRZ]. destruct (Hsum _ _ H4) as [_ TZR]. destruct (Hsum _ _ H5) as [TZZ _].
  (* the finite families on the wide strip *)
  assert (IR : E.TB.E.fam_in FR (fRf P Km Kn s0 rowsR)) by (apply E.DO.ifam_in, Hs0).
  assert (IZ : E.TB.E.fam_in FZ (fZf P Km Kn s0 rowsZ)) by (apply E.DO.ifam_in, Hs0).
  assert (NR : List.Forall (fun kr => map fst (snd kr) = pns P Kn) (fRf P Km Kn s0 rowsR))
    by (apply dfam_ns, crows_len, LRn).
  assert (NZ : List.Forall (fun kr => map fst (snd kr) = pns P Kn) (fZf P Km Kn s0 rowsZ))
    by (apply dfam_ns, srows_len, LZn).
  assert (KR : map fst (fRf P Km Kn s0 rowsR) = zrange Km)
    by (apply dfam_ks; unfold crows; rewrite length_map; exact LR).
  assert (KZ : map fst (fZf P Km Kn s0 rowsZ) = zrange Km)
    by (apply dfam_ks; unfold srows; rewrite length_map; exact LZ).
  pose proof (fnorm_ok Km Kn _ _ w1 Ew1 EwP1 (E.DO.ifam_dt_in _ _ IR) (E.DO.fam_dt_ns _ _ NR)
                ltac:(rewrite E.DO.fam_dt_ks; exact KR) HEw1 HEwP1) as DtR.
  pose proof (fnorm_ok Km Kn _ _ w1 Ew1 EwP1 (E.DO.ifam_dp_in _ _ IR) (E.DO.fam_dp_ns _ _ NR)
                ltac:(rewrite E.DO.fam_dp_ks; exact KR) HEw1 HEwP1) as DpR.
  pose proof (fnorm_ok Km Kn _ _ w1 Ew1 EwP1 (E.DO.ifam_dt_in _ _ IZ) (E.DO.fam_dt_ns _ _ NZ)
                ltac:(rewrite E.DO.fam_dt_ks; exact KZ) HEw1 HEwP1) as DtZ.
  pose proof (fnorm_ok Km Kn _ _ w1 Ew1 EwP1 (E.DO.ifam_dp_in _ _ IZ) (E.DO.fam_dp_ns _ _ NZ)
                ltac:(rewrite E.DO.fam_dp_ks; exact KZ) HEw1 HEwP1) as DpZ.
  pose proof (fnorm_ok Km Kn _ _ w1 Ew1 EwP1 IR NR KR HEw1 HEwP1) as NKR.
  pose proof (fnorm_ok Kmu Knu FUd fU w1 Ew1 EwP1 (E.DO.ifam_in _ _ _ _ Hs0) (dfam_ns _ _ _ _ (crows_len _ _ LUn))
                ltac:(apply dfam_ks; unfold crows; rewrite length_map; exact LU) HEw1 HEwP1) as NU.
  pose proof (fnorm_ok Kmg Kng FGd fG w1 Ew1 EwP1 (E.DO.ifam_in _ _ _ _ Hs0) (dfam_ns _ _ _ _ (crows_len _ _ LGn))
                ltac:(apply dfam_ks; unfold crows; rewrite length_map; exact LG) HEw1 HEwP1) as NG.
  destruct (crude_num P Km Kn s0 rowsR rowsZ Kr1 Kr2 N1s N2s Ky1 Ky2 HN1x HN2x l Hsc om w1 (cden fU) (cden fG)
              (fnorm w1 fU) (fnorm w1 fG) Hw1 C1 (nbound_cden w1 fU) (nbound_cden w1 fG)) as [BR [BZ [BU BG]]].
  refine (conj HL (conj Hsc (conj C0 (conj C1 (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply (nbound_le w1 _ _ _ (ile_correct _ _ _ _ HcR (inR_add _ _ _ _ (inR_mul _ _ _ _ TP
             (inR_add _ _ _ _ (inR_mul _ _ _ _ (inR_abs _ _ HOM) DtR) DpR)) (inR_mul _ _ _ _ NKR TR)) HIMR) BR).
  - apply (nbound_le w1 _ _ _ (ile_correct _ _ _ _ HcZ (inR_add _ _ _ _ (inR_mul _ _ _ _ TP
             (inR_add _ _ _ _ (inR_mul _ _ _ _ (inR_abs _ _ HOM) DtZ) DpZ)) (inR_mul _ _ _ _ NKR TZ)) HIMZ) BZ).
  - apply (nbound_le w1 _ _ _ (ile_correct _ _ _ _ HcU (inR_add _ _ _ _ (inR_Z 1) (inR_mul _ _ _ _ TP NU)) HIMU) BU).
  - apply (nbound_le w1 _ _ _ (ile_correct _ _ _ _ HcG (inR_add _ _ _ _ (inR_Z 1) (inR_mul _ _ _ _
             (inR_mul _ _ _ _ TP (inR_add _ _ _ _ (inR_mul _ _ _ _ DtR DtR) (inR_mul _ _ _ _ DtZ DtZ))) NG)) HIMG) BG).
  - cbn [firstn app]. unfold tR, tP, tZ, tRR, tRZ, tPR, tPZ, tZR, tZZ.
    repeat (apply Forall2_cons; [assumption |]). apply Forall2_nil.
  - cbn [skipn app]. exact Hc6.
Qed.

End Sound2.

End Run.

(** * The check from raw data *)

Record srcdata := mksrcd {
  sd_P : nat ; sd_Km : nat ; sd_Kn : nat ; sd_Kr1 : nat ; sd_Kr2 : nat ; sd_N1s : nat ; sd_N2s : nat ;
  sd_Ky1 : nat ; sd_Ky2 : nat ; sd_Kmu : nat ; sd_Knu : nat ; sd_Kmg : nat ; sd_Kng : nat ;
  sd_s0 : Z ; sd_sY : Z ; sd_ssrc : Z ;
  sd_rowsR : list (list Z) ; sd_rowsZ : list (list Z) ; sd_rowsU : list (list Z) ; sd_rowsG : list (list Z) ;
  sd_srcs : list ((Z * Z * Z) * (Z * Z * Z)) ; sd_seeds : list (list (list (Z * Z))) ;
  sd_a : Z ; sd_b : Z ;
  sd_trig : list J.t ;
  sd_exp : list J.t ;
  sd_claims : list J.t }.

(** The verdict and the thirteen crude norms: the trigonometric seeds for N1s
    and N2s, the exponentials e^w0, e^(w0 kappa), e^(w0 kappa P), e^w1,
    e^(w1 kappa), e^(w1 kappa P), and the claims for F_R, F_Z and the two
    defects. *)
Definition res_src (d : srcdata) : bool * list J.t :=
  let tr := sd_trig d in let ex := sd_exp d in let cl := sd_claims d in
  src_check (sd_P d) (sd_Km d) (sd_Kn d) (sd_Kr1 d) (sd_Kr2 d) (sd_N1s d) (sd_N2s d) (sd_Ky1 d) (sd_Ky2 d)
    (sd_s0 d) (sd_sY d) (sd_ssrc d) (sd_rowsR d) (sd_rowsZ d)
    (E.nth0 tr 0, E.nth0 tr 1) (E.nth0 tr 2, E.nth0 tr 3)
    (E.nth0 ex 0) (E.nth0 ex 1) (E.nth0 ex 2) (E.nth0 ex 3) (E.nth0 ex 4) (E.nth0 ex 5)
    (sd_Kmu d) (sd_Knu d) (sd_Kmg d) (sd_Kng d) (sd_rowsU d) (sd_rowsG d)
    (E.om_i (sd_P d) (sd_a d) (sd_b d)) (E.nth0 cl 0) (E.nth0 cl 1) (E.nth0 cl 2) (E.nth0 cl 3)
    (sd_srcs d) (sd_seeds d).

End SrcRun.
