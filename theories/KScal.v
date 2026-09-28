(** The scalar constants of the KAM theorem for the coil field, over intervals.

    Every constant [field_kam] reads is a closed formula in bounds of the
    first torus, of the sources along it and of the field there: the
    per-source constants of the Taylor bounds (FieldTaylor.v), the ball of
    the seeds (FieldBall.v), the sums over the sources and the model
    constants built from them (FieldTotal.v, FieldConst.v), and the constants
    of the Newton iteration (KAMBound.v, KAMUpdate.v). Each has an interval
    form built from the same operations in the same order, which encloses it
    whenever the arguments are enclosed and every divisor is away from zero
    ([itRRb_ok] ... [ikT_ok]). Maxima are enclosed through
    max x y = (x + y + |x - y|) / 2 ([imax_ok]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity FourierDFT
  FourierCanon FourierPer FourierSym FourierList FourierModel FourierSupp FourierModelPer KAMVec KAMFin KAMPer
  KAMStep KAMBound KAMUpdate KAMDiff Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTaylor
  FieldTotal FieldCrude FieldBall FieldLine FieldConst KFix KCheckKern KEngine KSrcRun.
Import ListNotations.
Local Open Scope R_scope.

Lemma Rmax_abs (x y : R) : Rmax x y = (x + y + Rabs (x - y)) * (IZR 1 / IZR (2 ^ 1)).
Proof.
  change (2 ^ 1)%Z with 2%Z. unfold Rmax. destruct (Rle_dec x y) as [H | H].
  - rewrite Rabs_left1 by lra. field.
  - rewrite Rabs_right by lra. field.
Qed.

Module Scal (J : RI).

Module SR := SrcRun J.
Import SR SR.E.TB SR.E.TB.E SR.E.TB.E.KO.

Ltac irs := repeat (first [assumption | apply inR_add | apply inR_sub | apply inR_mul | apply inR_abs | apply inR_neg
                          | apply inR_Z | exact inR_zero]).

(** * Constants *)

Definition four : J.t := J.of_q 4 0.
Definition c34 : J.t := J.div three four.
Definition c32 : J.t := J.div three two.
Definition i4 : J.t := J.div one four.
Definition i8 : J.t := J.div one (J.of_q 8 0).
Definition half : J.t := J.of_q 1 1.

Lemma one_ok : inR one 1. Proof. exact (inR_Z 1). Qed.
Lemma two_ok : inR two 2. Proof. exact (inR_Z 2). Qed.
Lemma three_ok : inR three 3. Proof. exact (inR_Z 3). Qed.
Lemma c34_ok : inR c34 (3 / 4). Proof. apply inR_div; [exact three_ok | exact (inR_Z 4) | lra]. Qed.
Lemma c32_ok : inR c32 (3 / 2). Proof. apply inR_div; [exact three_ok | exact two_ok | lra]. Qed.
Lemma i4_ok : inR i4 (/ 4).
Proof. replace (/ 4) with (1 / 4) by field. apply inR_div; [exact one_ok | exact (inR_Z 4) | lra]. Qed.
Lemma i8_ok : inR i8 (/ 8).
Proof. replace (/ 8) with (1 / 8) by field. apply inR_div; [exact one_ok | exact (inR_Z 8) | lra]. Qed.
Lemma half_ok : inR half (IZR 1 / IZR (2 ^ 1)). Proof. apply inR_q. lia. Qed.

Lemma div2_ok (X : J.t) (x : R) : inR X x -> inR (J.div X two) (x / 2).
Proof. intros H. apply inR_div; [exact H | exact two_ok | lra]. Qed.

Definition imax (X Y : J.t) : J.t := J.mul (J.add (J.add X Y) (J.abs (J.sub X Y))) half.

Lemma imax_ok (X Y : J.t) (x y : R) : inR X x -> inR Y y -> inR (imax X Y) (Rmax x y).
Proof. intros HX HY. rewrite Rmax_abs. unfold imax. apply inR_mul; [irs | exact half_ok]. Qed.

(** * The Taylor constants of one source *)

Section Taylor.

Variables (HM R1 R2 R3 YB CS : J.t) (D : i3).

Definition itP1 : J.t := J.mul (itE1 HM R1 R2 R3 CS) (J.mul YB YB).
Definition itS2 : J.t := J.add one (J.div (J.mul HM itP1) two).
Definition itT1 : J.t := J.add (J.mul c34 (J.mul itP1 itP1)) (J.mul i4 (J.mul HM (J.mul itP1 (J.mul itP1 itP1)))).
Definition ihh : J.t := J.mul (J.mul HM HM) itT1.
Definition itRB : J.t := J.div (J.mul (J.mul two itS2) itT1) (J.mul (J.sub one ihh) (J.sub one ihh)).
Definition itA1 : J.t :=
  J.add (J.add (J.add (J.add (J.mul c34 (J.mul itP1 itP1)) (J.mul i8 (J.mul HM (J.mul itP1 (J.mul itP1 itP1)))))
                      (J.mul three (J.mul (J.mul itS2 itS2) itRB)))
               (J.mul three (J.mul itS2 (J.mul (J.mul HM HM) (J.mul itRB itRB)))))
        (J.mul (J.mul (J.mul HM HM) (J.mul HM HM)) (J.mul itRB (J.mul itRB itRB))).
Definition itB1 : J.t := J.add (J.mul c32 itP1) (J.mul HM itA1).
Definition iYY : J.t := J.mul YB (J.mul YB YB).
Definition itXb (Cc Dc : J.t) : J.t :=
  J.add (J.add (J.mul (J.mul Cc iYY) itA1) (J.mul (J.mul Dc iYY) itB1))
        (J.mul c32 (J.mul (J.mul Cc (J.add (J.mul two (J.mul CS CS)) one)) (J.mul iYY (J.mul YB YB)))).
Definition itD1 : J.t := J.add (J.abs (d2 D)) (J.mul (J.abs (d3 D)) CS).
Definition itD2 : J.t := J.add (J.mul (J.abs (d3 D)) CS) (J.abs (d1 D)).
Definition itD3 : J.t := J.add (J.mul (J.abs (d1 D)) CS) (J.mul (J.abs (d2 D)) CS).
Definition itRRb : J.t := J.mul (J.add (itXb (iC1 D R2 R3) itD1) (itXb (iC2 D R1 R3) itD2)) CS.
Definition itRZb : J.t := itXb (iC3 D R1 R2) itD3.
Definition itZb : J.t := J.add itS2 (J.mul (J.mul HM HM) itRB).
Definition itZ1 : J.t := J.add (J.div itP1 two) (J.mul HM itRB).
Definition itZ5 : J.t :=
  J.mul itZ1 (J.add (J.add (J.add (J.add one itZb) (J.mul itZb itZb)) (J.mul itZb (J.mul itZb itZb)))
                    (J.mul (J.mul itZb itZb) (J.mul itZb itZb))).
Definition itZb5 : J.t := J.mul (J.mul itZb (J.mul itZb itZb)) (J.mul itZb itZb).
Definition itJb (DV Cc Dc RE DE : J.t) : J.t :=
  J.add (J.mul (J.mul DV iYY) itB1)
        (J.mul three (J.mul (J.mul iYY (J.mul YB YB))
                            (J.add (J.mul (J.mul Cc RE) itZ5)
                                   (J.mul (J.add (J.add (J.mul Cc DE) (J.mul Dc RE)) (J.mul HM (J.mul Dc DE))) itZb5)))).
Definition itDVR1 : J.t := J.mul (J.abs (J.neg (d3 D))) CS.
Definition itDVR2 : J.t := J.mul (J.abs (d3 D)) CS.
Definition itDVR3 : J.t := J.add (J.mul (J.abs (d1 D)) CS) (J.mul (J.abs (d2 D)) CS).
Definition itRER : J.t := J.add (J.mul R1 CS) (J.mul R2 CS).
Definition itDER : J.t := J.mul two (J.mul CS CS).
Definition itLRRb : J.t :=
  J.mul (J.add (itJb itDVR1 (iC1 D R2 R3) itD1 itRER itDER) (itJb itDVR2 (iC2 D R1 R3) itD2 itRER itDER)) CS.
Definition itLRZb : J.t :=
  J.mul (J.add (itJb (J.abs (d2 D)) (iC1 D R2 R3) itD1 R3 one) (itJb (J.abs (J.neg (d1 D))) (iC2 D R1 R3) itD2 R3 one))
        CS.
Definition itLZRb : J.t := itJb itDVR3 (iC3 D R1 R2) itD3 itRER itDER.
Definition itLZZb : J.t := itJb (J.abs J.zero) (iC3 D R1 R2) itD3 R3 one.

(** The two smallness conditions of a source on the ball. *)
Definition itsmall : bool :=
  J.pos (J.sub one ihh) && J.pos (J.sub one (J.add (J.div (J.mul HM itP1) two) (J.mul (J.mul HM HM) itRB))).

Variables (sc : src) (hm r1 r2 r3 yb cs : R).
Hypothesis HHM : inR HM hm.
Hypothesis H1 : inR R1 r1.
Hypothesis H2 : inR R2 r2.
Hypothesis H3 : inR R3 r3.
Hypothesis HYB : inR YB yb.
Hypothesis HCS : inR CS cs.
Hypothesis HD : inR3 D (sd1 sc, sd2 sc, sd3 sc).

Lemma itP1_ok : inR itP1 (tP1 hm r1 r2 r3 yb cs).
Proof. unfold itP1, tP1. pose proof (itE1_ok HM R1 R2 R3 CS hm r1 r2 r3 cs HHM H1 H2 H3 HCS). irs. Qed.

Lemma itS2_ok : inR itS2 (tS2 hm r1 r2 r3 yb cs).
Proof. unfold itS2, tS2. pose proof itP1_ok. pose proof one_ok. apply inR_add; [assumption |]. apply div2_ok. irs. Qed.

Lemma itT1_ok : inR itT1 (tT1 hm r1 r2 r3 yb cs).
Proof. unfold itT1, tT1. pose proof itP1_ok. pose proof c34_ok. pose proof i4_ok. irs. Qed.

Lemma ihh_ok : inR ihh (hm * hm * tT1 hm r1 r2 r3 yb cs).
Proof. unfold ihh. pose proof itT1_ok. irs. Qed.

Hypothesis Hsm : hm * hm * tT1 hm r1 r2 r3 yb cs < 1.

Lemma itRB_ok : inR itRB (tRB hm r1 r2 r3 yb cs).
Proof.
  unfold itRB, tRB. pose proof itS2_ok. pose proof itT1_ok. pose proof ihh_ok. pose proof one_ok. pose proof two_ok.
  apply inR_div; [irs | irs |].
  apply Rgt_not_eq, Rmult_lt_0_compat; lra.
Qed.

Lemma itA1_ok : inR itA1 (tA1 hm r1 r2 r3 yb cs).
Proof.
  unfold itA1, tA1. pose proof itP1_ok. pose proof itS2_ok. pose proof itRB_ok. pose proof c34_ok. pose proof i8_ok.
  pose proof three_ok. irs.
Qed.

Lemma itB1_ok : inR itB1 (tB1 hm r1 r2 r3 yb cs).
Proof. unfold itB1, tB1. pose proof itP1_ok. pose proof itA1_ok. pose proof c32_ok. irs. Qed.

Lemma iYY_ok : inR iYY (yb * (yb * yb)). Proof. unfold iYY. irs. Qed.

Lemma itXb_ok (Cc Dc : J.t) (cc dc : R) : inR Cc cc -> inR Dc dc -> inR (itXb Cc Dc) (tXb hm r1 r2 r3 yb cs cc dc).
Proof.
  intros. unfold itXb, tXb. pose proof iYY_ok. pose proof itA1_ok. pose proof itB1_ok. pose proof c32_ok.
  pose proof two_ok. pose proof one_ok. irs.
Qed.

Lemma dd_ok' : inR (d1 D) (sd1 sc) /\ inR (d2 D) (sd2 sc) /\ inR (d3 D) (sd3 sc).
Proof. destruct D as [[D1 D2] D3]. exact HD. Qed.

Lemma itD_ok : inR itD1 (tD1 sc cs) /\ inR itD2 (tD2 sc cs) /\ inR itD3 (tD3 sc cs).
Proof. destruct dd_ok' as [E1 [E2 E3]]. unfold itD1, itD2, itD3, tD1, tD2, tD3. split; [| split]; irs. Qed.

Lemma itC_ok : inR (iC1 D R2 R3) (tC1 sc r2 r3) /\ inR (iC2 D R1 R3) (tC2 sc r1 r3) /\ inR (iC3 D R1 R2) (tC3 sc r1 r2).
Proof. destruct dd_ok' as [E1 [E2 E3]]. unfold iC1, iC2, iC3, tC1, tC2, tC3, d1, d2, d3 in *.
  destruct D as [[D1 D2] D3]. split; [| split]; irs.
Qed.

Lemma itRRb_ok : inR itRRb (tRRb sc hm r1 r2 r3 yb cs).
Proof.
  unfold itRRb, tRRb. destruct itD_ok as [A1 [A2 A3]]. destruct itC_ok as [C1 [C2 C3]].
  apply inR_mul; [| exact HCS]. apply inR_add; apply itXb_ok; assumption.
Qed.

Lemma itRZb_ok : inR itRZb (tRZb sc hm r1 r2 r3 yb cs).
Proof. unfold itRZb, tRZb. destruct itD_ok as [A1 [A2 A3]]. destruct itC_ok as [C1 [C2 C3]]. apply itXb_ok; assumption. Qed.

Lemma itZb_ok : inR itZb (tZb hm r1 r2 r3 yb cs).
Proof. unfold itZb, tZb. pose proof itS2_ok. pose proof itRB_ok. irs. Qed.

Lemma itZ1_ok : inR itZ1 (tZ1 hm r1 r2 r3 yb cs).
Proof. unfold itZ1, tZ1. pose proof itP1_ok. pose proof itRB_ok. apply inR_add; [apply div2_ok; exact itP1_ok | irs]. Qed.

Lemma itZ5_ok : inR itZ5 (tZ5 hm r1 r2 r3 yb cs).
Proof. unfold itZ5, tZ5. pose proof itZ1_ok. pose proof itZb_ok. pose proof one_ok. irs. Qed.

Lemma itZb5_ok : inR itZb5 (tZb5 hm r1 r2 r3 yb cs).
Proof. unfold itZb5, tZb5. pose proof itZb_ok. irs. Qed.

Lemma itJb_ok (DV Cc Dc RE DE : J.t) (dv cc dc re de : R) :
  inR DV dv -> inR Cc cc -> inR Dc dc -> inR RE re -> inR DE de -> inR (itJb DV Cc Dc RE DE) (tJb hm r1 r2 r3 yb cs dv cc dc re de).
Proof.
  intros. unfold itJb, tJb. pose proof iYY_ok. pose proof itB1_ok. pose proof itZ5_ok. pose proof itZb5_ok.
  pose proof three_ok. irs.
Qed.

Lemma itDVR_ok : inR itDVR1 (tDVR1 sc cs) /\ inR itDVR2 (tDVR2 sc cs) /\ inR itDVR3 (tDVR3 sc cs) /\
                 inR itRER (tRER r1 r2 cs) /\ inR itDER (tDER cs).
Proof.
  destruct dd_ok' as [E1 [E2 E3]]. pose proof two_ok.
  unfold itDVR1, itDVR2, itDVR3, itRER, itDER, tDVR1, tDVR2, tDVR3, tRER, tDER.
  refine (conj _ (conj _ (conj _ (conj _ _)))); irs.
Qed.

Lemma itLRRb_ok : inR itLRRb (tLRRb sc hm r1 r2 r3 yb cs).
Proof.
  unfold itLRRb, tLRRb. destruct itD_ok as [A1 [A2 A3]]. destruct itC_ok as [C1 [C2 C3]].
  destruct itDVR_ok as [V1 [V2 [V3 [V4 V5]]]].
  apply inR_mul; [| exact HCS]. apply inR_add; apply itJb_ok; assumption.
Qed.

Lemma itLRZb_ok : inR itLRZb (tLRZb sc hm r1 r2 r3 yb cs).
Proof.
  unfold itLRZb, tLRZb. destruct itD_ok as [A1 [A2 A3]]. destruct itC_ok as [C1 [C2 C3]].
  destruct dd_ok' as [E1 [E2 E3]]. pose proof one_ok.
  apply inR_mul; [| exact HCS]. apply inR_add; apply itJb_ok; irs.
Qed.

Lemma itLZRb_ok : inR itLZRb (tLZRb sc hm r1 r2 r3 yb cs).
Proof.
  unfold itLZRb, tLZRb. destruct itD_ok as [A1 [A2 A3]]. destruct itC_ok as [C1 [C2 C3]].
  destruct itDVR_ok as [V1 [V2 [V3 [V4 V5]]]]. apply itJb_ok; assumption.
Qed.

Lemma itLZZb_ok : inR itLZZb (tLZZb sc hm r1 r2 r3 yb cs).
Proof.
  unfold itLZZb, tLZZb. destruct itD_ok as [A1 [A2 A3]]. destruct itC_ok as [C1 [C2 C3]]. pose proof one_ok.
  apply itJb_ok; irs.
Qed.

End Taylor.

Lemma itsmall_ok (HM R1 R2 R3 YB CS : J.t) (hm r1 r2 r3 yb cs : R) :
  inR HM hm -> inR R1 r1 -> inR R2 r2 -> inR R3 r3 -> inR YB yb -> inR CS cs ->
  itsmall HM R1 R2 R3 YB CS = true ->
  hm * hm * tT1 hm r1 r2 r3 yb cs < 1 /\
  hm * tP1 hm r1 r2 r3 yb cs / 2 + hm * hm * tRB hm r1 r2 r3 yb cs < 1.
Proof.
  intros HHM H1 H2 H3 HYB HCS Hc. unfold itsmall in Hc. apply andb_prop in Hc. destruct Hc as [C1 C2].
  pose proof (ihh_ok HM R1 R2 R3 YB CS hm r1 r2 r3 yb cs HHM H1 H2 H3 HYB HCS) as Hh.
  pose proof (inR_pos _ _ C1 (inR_sub _ _ _ _ one_ok Hh)) as P1.
  assert (Hs : hm * hm * tT1 hm r1 r2 r3 yb cs < 1) by lra.
  split; [exact Hs |].
  pose proof (itP1_ok HM R1 R2 R3 YB CS hm r1 r2 r3 yb cs HHM H1 H2 H3 HYB HCS) as HP.
  pose proof (itRB_ok HM R1 R2 R3 YB CS hm r1 r2 r3 yb cs HHM H1 H2 H3 HYB HCS Hs) as HR.
  assert (Q : inR (J.add (J.div (J.mul HM (itP1 HM R1 R2 R3 YB CS)) two) (J.mul (J.mul HM HM) (itRB HM R1 R2 R3 YB CS)))
                  (hm * tP1 hm r1 r2 r3 yb cs / 2 + hm * hm * tRB hm r1 r2 r3 yb cs))
    by (apply inR_add; [apply div2_ok; irs | irs]).
  pose proof (inR_pos _ _ C2 (inR_sub _ _ _ _ one_ok Q)). lra.
Qed.

(** * The seed of a source on the ball *)

Definition ibyb (Rr R10 R20 R30 MYi TH CS : J.t) : J.t :=
  J.add MYi (iinv_eps MYi (ibth Rr R10 R20 R30 MYi TH CS)).

Lemma ibyb_ok (Rr R10 R20 R30 MYi TH CS : J.t) (r r10 r20 r30 MY th0 cs : R) :
  inR Rr r -> inR R10 r10 -> inR R20 r20 -> inR R30 r30 -> inR MYi MY -> inR TH th0 -> inR CS cs ->
  bth r r10 r20 r30 MY th0 cs < 1 ->
  inR (ibyb Rr R10 R20 R30 MYi TH CS) (byb r r10 r20 r30 MY th0 cs).
Proof.
  intros. unfold ibyb, byb. apply inR_add; [assumption |]. apply iinv_eps_ok; [assumption | | assumption].
  apply ibth_ok; assumption.
Qed.

(** * Sums over the sources *)

(** The weighted tangent of a source and its four bounds on the ball. *)
Definition sdat : Type := (i3 * (J.t * J.t * J.t * J.t))%type.

Definition sd_in (dr1 dr2 dr3 dyb : src * fser -> R) (S : sdat) (sy : src * fser) : Prop :=
  inR3 (fst S) (sd1 (fst sy), sd2 (fst sy), sd3 (fst sy)) /\
  let '(A1, A2, A3, A4) := snd S in
  inR A1 (dr1 sy) /\ inR A2 (dr2 sy) /\ inR A3 (dr3 sy) /\ inR A4 (dyb sy).

Lemma isum_lsum {A B : Type} (f : A -> J.t) (g : B -> R) (Ls : list A) (l : list B) :
  Forall2 (fun a b => inR (f a) (g b)) Ls l -> inR (isuml (map f Ls)) (lsum g l).
Proof.
  intros H. rewrite lsum_map. apply isuml_ok. induction H as [| a b Ls l Hab _ IH]; [constructor |].
  cbn [map]. constructor; assumption.
Qed.

Lemma forall2_forall_and {A B : Type} (R1 : A -> B -> Prop) (Q : B -> Prop) (xs : list A) (ys : list B) :
  Forall2 R1 xs ys -> List.Forall Q ys -> Forall2 (fun x y => R1 x y /\ Q y) xs ys.
Proof.
  intros H. induction H as [| x y xs ys Hxy _ IH]; intros HQ; [constructor |].
  inversion HQ as [| y' ys' Hy HQ']; subst. constructor; [split; assumption | apply IH; assumption].
Qed.

Definition iPabs (P : Z) : J.t := J.abs (J.of_q P 0).

Lemma iPabs_ok (P : Z) : inR (iPabs P) (Rabs (IZR P)). Proof. unfold iPabs. irs. Qed.

(** |P| 2 times the sum of a per-source term. *)
Definition itot (P : Z) (f : sdat -> J.t) (Ss : list sdat) : J.t := J.mul (iPabs P) (J.mul two (isuml (map f Ss))).

Section Sums.

Variables (P : Z) (HM CS : J.t) (hm cs : R) (Ss : list sdat) (l : list (src * fser)).
Variables (dr1 dr2 dr3 dyb : src * fser -> R).
Hypothesis HHM : inR HM hm.
Hypothesis HCS : inR CS cs.
Hypothesis HS : Forall2 (sd_in dr1 dr2 dr3 dyb) Ss l.
Hypothesis Hsm : List.Forall (fun sy => hm * hm * tT1 hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs < 1) l.

Definition sterm (g : J.t -> J.t -> J.t -> J.t -> J.t -> J.t -> i3 -> J.t) (S : sdat) : J.t :=
  let '(A1, A2, A3, A4) := snd S in g HM A1 A2 A3 A4 CS (fst S).

Lemma sterm_ok (g : J.t -> J.t -> J.t -> J.t -> J.t -> J.t -> i3 -> J.t)
    (h : src -> R -> R -> R -> R -> R -> R -> R) :
  (forall S sy, sd_in dr1 dr2 dr3 dyb S sy -> hm * hm * tT1 hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs < 1 ->
     inR (sterm g S) (h (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs)) ->
  inR (itot P (sterm g) Ss) (Rabs (IZR P) * (2 * lsum (fun sy => h (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l)).
Proof.
  intros Hg. unfold itot. apply inR_mul; [apply iPabs_ok |]. apply inR_mul; [exact two_ok |].
  apply isum_lsum. eapply Forall2_impl; [| exact (forall2_forall_and _ _ _ _ HS Hsm)].
  intros S sy [A B]. apply Hg; assumption.
Qed.

Ltac sterm_tac lem :=
  intros [D [[[A1 A2] A3] A4]] sy [HD Ha] Hs; cbn [snd fst sterm] in Ha |- *; destruct Ha as [B1 [B2 [B3 B4]]];
  apply lem; assumption.

Definition icR2R : J.t := itot P (sterm itRRb) Ss.
Definition icR2Z : J.t := itot P (sterm itRZb) Ss.
Definition icLRR : J.t := itot P (sterm itLRRb) Ss.
Definition icLRZ : J.t := itot P (sterm itLRZb) Ss.
Definition icLZR : J.t := itot P (sterm itLZRb) Ss.
Definition icLZZ : J.t := itot P (sterm itLZZb) Ss.

Lemma sums_ok :
  inR icR2R (TR2R P hm cs l dr1 dr2 dr3 dyb) /\ inR icR2Z (TR2Z P hm cs l dr1 dr2 dr3 dyb) /\
  inR icLRR (TLRR P hm cs l dr1 dr2 dr3 dyb) /\ inR icLRZ (TLRZ P hm cs l dr1 dr2 dr3 dyb) /\
  inR icLZR (TLZR P hm cs l dr1 dr2 dr3 dyb) /\ inR icLZZ (TLZZ P hm cs l dr1 dr2 dr3 dyb).
Proof.
  unfold icR2R, icR2Z, icLRR, icLRZ, icLZR, icLZZ, TR2R, TR2Z, TLRR, TLRZ, TLZR, TLZZ.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); apply sterm_ok.
  - sterm_tac itRRb_ok.
  - sterm_tac itRZb_ok.
  - sterm_tac itLRRb_ok.
  - sterm_tac itLRZb_ok.
  - sterm_tac itLZRb_ok.
  - sterm_tac itLZZb_ok.
Qed.

End Sums.

(** * The constants of the model on the ball *)

Record ijet9 := mkij9 { ij_R : J.t ; ij_P : J.t ; ij_Z : J.t ; ij_RR : J.t ; ij_RZ : J.t ; ij_PR : J.t ; ij_PZ : J.t ;
                        ij_ZR : J.t ; ij_ZZ : J.t }.

Section Model.

Variables (P : Z) (Rr HM CS : J.t) (Ss : list sdat) (Jb : ijet9) (KR MUi TU : J.t).

Let jR2R := icR2R P HM CS Ss.
Let jR2Z := icR2Z P HM CS Ss.
Let jLRR := icLRR P HM CS Ss.
Let jLRZ := icLRZ P HM CS Ss.
Let jLZR := icLZR P HM CS Ss.
Let jLZZ := icLZZ P HM CS Ss.

Definition ibRR : J.t := J.add (ij_RR Jb) (J.mul Rr jLRR).
Definition ibRZ : J.t := J.add (ij_RZ Jb) (J.mul Rr jLRZ).
Definition ibPR : J.t := J.add (ij_PR Jb) (J.mul Rr jLRR).
Definition ibPZ : J.t := J.add (ij_PZ Jb) (J.mul Rr jLRZ).
Definition ibZR : J.t := J.add (ij_ZR Jb) (J.mul Rr jLZR).
Definition ibZZ : J.t := J.add (ij_ZZ Jb) (J.mul Rr jLZZ).
Definition idBR : J.t := J.add (J.mul (J.add (ij_RR Jb) (ij_RZ Jb)) Rr) (J.mul (J.mul Rr Rr) jR2R).
Definition idBP : J.t := J.add (J.mul (J.add (ij_PR Jb) (ij_PZ Jb)) Rr) (J.mul (J.mul Rr Rr) jR2R).
Definition idBZ : J.t := J.add (J.mul (J.add (ij_ZR Jb) (ij_ZZ Jb)) Rr) (J.mul (J.mul Rr Rr) jR2Z).
Definition ibBR : J.t := J.add (ij_R Jb) idBR.
Definition ibBP : J.t := J.add (ij_P Jb) idBP.
Definition ibBZ : J.t := J.add (ij_Z Jb) idBZ.
Definition ikRb : J.t := J.add KR Rr.
Definition ithU : J.t := J.add TU (J.mul idBP MUi).
Definition iUbb : J.t := J.add MUi (iinv_eps MUi ithU).
Definition iLBR : J.t := J.add (J.add ibRR ibRZ) (J.mul HM jR2R).
Definition iLBP : J.t := J.add (J.add ibPR ibPZ) (J.mul HM jR2R).
Definition iLBZ : J.t := J.add (J.add ibZR ibZZ) (J.mul HM jR2Z).
Definition iLU : J.t := J.mul (J.mul iUbb iUbb) iLBP.
Definition icW : J.t := J.mul ikRb iUbb.
Definition iLW : J.t := J.add (J.mul one iUbb) (J.mul ikRb iLU).
Definition icUPR : J.t := J.mul iUbb ibPR.
Definition iLUPR : J.t := J.add (J.mul iLU ibPR) (J.mul iUbb jLRR).
Definition icUPZ : J.t := J.mul iUbb ibPZ.
Definition iLUPZ : J.t := J.add (J.mul iLU ibPZ) (J.mul iUbb jLRZ).
Definition icWR : J.t := J.add iUbb (J.mul icW icUPR).
Definition iLWR : J.t := J.add iLU (J.add (J.mul iLW icUPR) (J.mul icW iLUPR)).
Definition icWZ : J.t := J.mul (J.abs (J.of_q (-1) 0)) (J.mul icW icUPZ).
Definition iLWZ : J.t := J.mul (J.abs (J.of_q (-1) 0)) (J.add (J.mul iLW icUPZ) (J.mul icW iLUPZ)).
Definition icmRR : J.t := J.add (J.mul icWR ibBR) (J.mul icW ibRR).
Definition iLmRR : J.t := J.add (J.add (J.mul iLWR ibBR) (J.mul icWR iLBR)) (J.add (J.mul iLW ibRR) (J.mul icW jLRR)).
Definition icmRZ : J.t := J.add (J.mul icWZ ibBR) (J.mul icW ibRZ).
Definition iLmRZ : J.t := J.add (J.add (J.mul iLWZ ibBR) (J.mul icWZ iLBR)) (J.add (J.mul iLW ibRZ) (J.mul icW jLRZ)).
Definition icmZR : J.t := J.add (J.mul icWR ibBZ) (J.mul icW ibZR).
Definition iLmZR : J.t := J.add (J.add (J.mul iLWR ibBZ) (J.mul icWR iLBZ)) (J.add (J.mul iLW ibZR) (J.mul icW jLZR)).
Definition icmZZ : J.t := J.add (J.mul icWZ ibBZ) (J.mul icW ibZZ).
Definition iLmZZ : J.t := J.add (J.add (J.mul iLWZ ibBZ) (J.mul icWZ iLBZ)) (J.add (J.mul iLW ibZZ) (J.mul icW jLZZ)).
Definition ibMV : J.t := imax (J.mul icW ibBR) (J.mul icW ibBZ).
Definition ibDV : J.t := imax (imax icmRR icmRZ) (imax icmZR icmZZ).
Definition ibLD : J.t := imax (imax iLmRR iLmRZ) (imax iLmZR iLmZZ).
Definition ibS1 : J.t := imax ibPR ibPZ.
Definition iTMR : J.t :=
  J.add (J.add (J.add (J.add (J.add (J.mul (J.mul ikRb iUbb) jR2R)
                                    (J.mul (J.mul ikRb ibBR) (J.add (J.mul (J.mul iUbb iUbb) (J.mul iUbb (J.mul iLBP iLBP)))
                                                                    (J.mul (J.mul iUbb iUbb) jR2R))))
                             (J.mul iLU ibBR)) (J.mul iUbb iLBR))
               (J.mul (J.mul ikRb iLU) iLBR)) (J.mul (J.mul HM iLU) iLBR).
Definition iTMZ : J.t :=
  J.add (J.add (J.add (J.add (J.add (J.mul (J.mul ikRb iUbb) jR2Z)
                                    (J.mul (J.mul ikRb ibBZ) (J.add (J.mul (J.mul iUbb iUbb) (J.mul iUbb (J.mul iLBP iLBP)))
                                                                    (J.mul (J.mul iUbb iUbb) jR2R))))
                             (J.mul iLU ibBZ)) (J.mul iUbb iLBZ))
               (J.mul (J.mul ikRb iLU) iLBZ)) (J.mul (J.mul HM iLU) iLBZ).
Definition ibM2 : J.t := imax iTMR iTMZ.

Variables (l : list (src * fser)) (r hm cs : R) (dr1 dr2 dr3 dyb : src * fser -> R).
Variables (bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0 : R).
Hypothesis HR : inR Rr r.
Hypothesis HHM : inR HM hm.
Hypothesis HCS : inR CS cs.
Hypothesis HS : Forall2 (sd_in dr1 dr2 dr3 dyb) Ss l.
Hypothesis Hsm : List.Forall (fun sy => hm * hm * tT1 hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs < 1) l.
Hypothesis HJ : inR (ij_R Jb) bR0 /\ inR (ij_P Jb) bP0 /\ inR (ij_Z Jb) bZ0 /\ inR (ij_RR Jb) dRR0 /\
                inR (ij_RZ Jb) dRZ0 /\ inR (ij_PR Jb) dPR0 /\ inR (ij_PZ Jb) dPZ0 /\ inR (ij_ZR Jb) dZR0 /\
                inR (ij_ZZ Jb) dZZ0.
Hypothesis HKR : inR KR kR0.
Hypothesis HMU : inR MUi MU.
Hypothesis HTU : inR TU thU0.

Lemma HC6 :
  inR jR2R (cR2R P l hm cs dr1 dr2 dr3 dyb) /\ inR jR2Z (cR2Z P l hm cs dr1 dr2 dr3 dyb) /\
  inR jLRR (cLRR P l hm cs dr1 dr2 dr3 dyb) /\ inR jLRZ (cLRZ P l hm cs dr1 dr2 dr3 dyb) /\
  inR jLZR (cLZR P l hm cs dr1 dr2 dr3 dyb) /\ inR jLZZ (cLZZ P l hm cs dr1 dr2 dr3 dyb).
Proof.
  exact (sums_ok P HM CS hm cs Ss l dr1 dr2 dr3 dyb HHM HCS HS Hsm).
Qed.

Lemma bB_ok :
  inR ibBP (bBP P l r hm cs dr1 dr2 dr3 dyb bP0 dPR0 dPZ0) /\ inR ibS1 (bS1 P l r hm cs dr1 dr2 dr3 dyb dPR0 dPZ0) /\
  inR ithU (thU P l r hm cs dr1 dr2 dr3 dyb dPR0 dPZ0 MU thU0) /\
  inR iLBP (LBP P l r hm cs dr1 dr2 dr3 dyb dPR0 dPZ0).
Proof.
  destruct HC6 as [C1 [C2 [C3 [C4 [C5 C6]]]]]. destruct HJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 J9]]]]]]]].
  unfold ibBP, ibS1, ithU, iLBP, idBP, ibPR, ibPZ, bBP, bS1, thU, LBP, dBP, bPR, bPZ.
  refine (conj _ (conj _ (conj _ _))); [irs | apply imax_ok; irs | irs | irs].
Qed.

Hypothesis HthU : thU P l r hm cs dr1 dr2 dr3 dyb dPR0 dPZ0 MU thU0 < 1.

Lemma bModel_ok :
  inR ibMV (bMV P l r hm cs dr1 dr2 dr3 dyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0) /\
  inR ibDV (bDV P l r hm cs dr1 dr2 dr3 dyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0) /\
  inR ibLD (bLD P l r hm cs dr1 dr2 dr3 dyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0) /\
  inR ibM2 (bM2 P l r hm cs dr1 dr2 dr3 dyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0).
Proof.
  destruct HC6 as [C1 [C2 [C3 [C4 [C5 C6]]]]]. destruct HJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 J9]]]]]]]].
  destruct bB_ok as [_ [_ [HTH _]]].
  assert (HUbb : inR iUbb (Ubb P l r hm cs dr1 dr2 dr3 dyb dPR0 dPZ0 MU thU0))
    by (unfold iUbb, Ubb; apply inR_add; [exact HMU | apply iinv_eps_ok; assumption]).
  pose proof one_ok as O1.
  unfold ibMV, ibDV, ibLD, ibM2, bMV, bDV, bLD, bM2.
  unfold icmRR, icmRZ, icmZR, icmZZ, iLmRR, iLmRZ, iLmZR, iLmZZ, iTMR, iTMZ, cmRR, cmRZ, cmZR, cmZZ, LmRR, LmRZ,
    LmZR, LmZZ, TMR, TMZ.
  unfold icWR, iLWR, icWZ, iLWZ, icW, iLW, icUPR, iLUPR, icUPZ, iLUPZ, iLU, iLBR, iLBP, iLBZ, ikRb, ibBR, ibBZ,
    idBR, idBZ, ibRR, ibRZ, ibPR, ibPZ, ibZR, ibZZ.
  unfold cWR, LWR, cWZ, LWZ, cW, LW, cUPR, LUPR, cUPZ, LUPZ, LU, LBR, LBP, LBZ, kRb, bBR, bBZ, dBR, dBZ, bRR, bRZ,
    bPR, bPZ, bZR, bZZ.
  refine (conj _ (conj _ (conj _ _))); repeat (first [assumption | apply imax_ok | apply inR_add | apply inR_sub
                                                    | apply inR_mul | apply inR_abs | apply inR_neg | apply inR_Z]).
Qed.

End Model.

(** * The constants of the Newton iteration *)

Record ikcon := mkik { iA : J.t ; iG : J.t ; iN : J.t ; iB : J.t ; iS : J.t ; iS1 : J.t ; iD : J.t ; iMV : J.t ;
                       iM2 : J.t ; iTm : J.t ; itau : J.t ; iLS : J.t ; iLD : J.t }.

Definition kin (C : ikcon) (c : kcon) : Prop :=
  inR (iA C) (cA c) /\ inR (iG C) (cG c) /\ inR (iN C) (cN c) /\ inR (iB C) (cB c) /\ inR (iS C) (cS c) /\
  inR (iS1 C) (cS1 c) /\ inR (iD C) (cD c) /\ inR (iMV C) (cMV c) /\ inR (iM2 C) (cM2 c) /\ inR (iTm C) (cTm c) /\
  inR (itau C) (ctau c) /\ inR (iLS C) (cLS c) /\ inR (iLD C) (cLD c).

Section Iter.

Variables (C : ikcon) (E1 OM GM DD : J.t).

Definition ikdE (Dd : J.t) : J.t := J.div one (J.mul E1 Dd).
Definition ilinv : J.t := J.div (J.add one (ikdE DD)) GM.
Definition ikH1 : J.t := J.mul (iS C) (J.mul two (iN C)).
Definition ikH2 : J.t := J.mul (iS C) (J.mul two (iA C)).
Definition ikW2 : J.t := J.mul ilinv ikH2.
Definition ikZ : J.t := J.div (J.add ikH1 (J.mul (iTm C) ikW2)) (itau C).
Definition ikX2 : J.t := J.add ikW2 ikZ.
Definition ikR1 : J.t := J.add ikH1 (J.add (J.mul (iTm C) ikW2) (J.mul ikZ (iTm C))).
Definition ikX1 : J.t := J.mul ilinv ikR1.
Definition ikP : J.t := J.add (J.mul ikX1 (iA C)) (J.mul ikX2 (iN C)).
Definition ikAl : J.t := J.mul (iS C) (J.mul two (J.mul (ikdE DD) (iN C))).
Definition ikBe : J.t := J.mul (iS C) (J.mul two (J.mul (iA C) (ikdE DD))).
Definition ikC : J.t := J.add (J.mul (J.mul (J.mul two (iS1 C)) (J.mul two (J.mul (iA C) (iA C)))) (iG C)) ikAl.
Definition ikE : J.t :=
  J.add (J.add (J.mul (J.mul ikAl ikX1) (iA C)) (J.mul (J.add (J.mul ikBe ikX1) (J.mul ikC ikX2)) (iN C)))
        (J.mul (iM2 C) (J.mul ikP ikP)).
Definition ikdA : J.t := J.mul (ikdE DD) ikP.
Definition ikU : J.t :=
  J.add (J.mul (J.mul (iLS C) ikP) (J.mul two (J.mul (iA C) (iA C))))
        (J.mul (iS C) (J.mul (J.of_q 6 0) (J.mul (iA C) ikdA))).
Definition ikdG : J.t := J.mul (J.of_q 8 0) (J.mul (iG C) (J.mul (iG C) ikU)).
Definition ikdN : J.t := J.add (J.add (J.mul ikdG (J.mul two (iA C))) (J.mul (iG C) ikdA)) (J.mul (iB C) ikdA).
Definition ikLd : J.t := J.mul (J.add (J.abs OM) (J.of_q 10 0)) (ikdE (J.div DD two)).
Definition ikM : J.t := J.add (J.mul ikLd (iN C)) (J.mul two (J.mul (iD C) (iN C))).
Definition ikdM : J.t :=
  J.add (J.mul ikLd ikdN) (J.mul two (J.add (J.mul (J.mul (iLD C) ikP) (J.mul two (iN C))) (J.mul (iD C) ikdN))).
Definition ikW : J.t := J.mul two (J.mul ikM (iN C)).
Definition ikdW : J.t := J.mul two (J.add (J.mul ikdM (J.mul two (iN C))) (J.mul ikM ikdN)).
Definition ikT : J.t := J.add (J.mul (J.mul (iLS C) ikP) (J.mul two ikW)) (J.mul (iS C) ikdW).

Variables (c : kcon) (om gamma d : R).
Hypothesis HC : kin C c.
Hypothesis HE1 : inR E1 (exp 1).
Hypothesis HOM : inR OM om.
Hypothesis HGM : inR GM gamma.
Hypothesis HDD : inR DD d.
Hypothesis Hg : 0 < gamma.
Hypothesis Hd : 0 < d.
Hypothesis Htau : 0 < ctau c.

Lemma ikdE_ok (Dd : J.t) (x : R) : inR Dd x -> 0 < x -> inR (ikdE Dd) (kdE x).
Proof.
  intros H Hx. unfold ikdE, kdE. replace (/ (exp 1 * x)) with (1 / (exp 1 * x)) by (field; split; [lra |];
    apply Rgt_not_eq, exp_pos).
  apply inR_div; [exact one_ok | apply inR_mul; assumption |].
  apply Rgt_not_eq, Rmult_lt_0_compat; [apply exp_pos | exact Hx].
Qed.

Lemma ilinv_ok : inR ilinv (linv_const gamma d).
Proof.
  unfold ilinv, linv_const. apply inR_div; [| exact HGM | lra]. apply inR_add; [exact one_ok |].
  exact (ikdE_ok DD d HDD Hd).
Qed.

Lemma kP_parts :
  inR ikW2 (kW2 c gamma d) /\ inR ikZ (kZ c gamma d) /\ inR ikX2 (kX2 c gamma d) /\ inR ikR1 (kR1 c gamma d) /\
  inR ikX1 (kX1 c gamma d) /\ inR ikP (kP c gamma d).
Proof.
  destruct HC as [A [G [N [B [S [S1 [Dd [MV [M2 [Tm [TA [LS LD]]]]]]]]]]]].
  pose proof ilinv_ok as HL. pose proof two_ok.
  assert (H1 : inR ikH1 (kH1 c)) by (unfold ikH1, kH1, kN; irs).
  assert (H2 : inR ikH2 (kH2 c)) by (unfold ikH2, kH2; irs).
  assert (W2 : inR ikW2 (kW2 c gamma d)) by (unfold ikW2, kW2; irs).
  assert (Z : inR ikZ (kZ c gamma d)) by (unfold ikZ, kZ; apply inR_div; [irs | exact TA | lra]).
  assert (X2 : inR ikX2 (kX2 c gamma d)) by (unfold ikX2, kX2; irs).
  assert (R1 : inR ikR1 (kR1 c gamma d)) by (unfold ikR1, kR1; irs).
  assert (X1 : inR ikX1 (kX1 c gamma d)) by (unfold ikX1, kX1; irs).
  refine (conj W2 (conj Z (conj X2 (conj R1 (conj X1 _))))). unfold ikP, kP, kN. irs.
Qed.

Lemma ikE_ok : inR ikE (kE c gamma d).
Proof.
  destruct HC as [A [G [N [B [S [S1 [Dd [MV [M2 [Tm [TA [LS LD]]]]]]]]]]]].
  destruct kP_parts as [_ [_ [X2 [_ [X1 P]]]]]. pose proof two_ok. pose proof (ikdE_ok DD d HDD Hd) as DE.
  unfold ikE, kE, ikAl, ikBe, ikC, kAl, kBe, kC, kN. irs.
Qed.

Lemma ikU_parts :
  inR ikdA (kdA c gamma d) /\ inR ikU (kU c gamma d) /\ inR ikdG (kdG c gamma d) /\ inR ikdN (kdN c gamma d).
Proof.
  destruct HC as [A [G [N [B [S [S1 [Dd [MV [M2 [Tm [TA [LS LD]]]]]]]]]]]].
  destruct kP_parts as [_ [_ [_ [_ [_ P]]]]]. pose proof two_ok. pose proof (ikdE_ok DD d HDD Hd) as DE.
  pose proof (inR_Z 6). pose proof (inR_Z 8).
  assert (dA : inR ikdA (kdA c gamma d)) by (unfold ikdA, kdA; irs).
  assert (U : inR ikU (kU c gamma d)) by (unfold ikU, kU; irs).
  assert (dG : inR ikdG (kdG c gamma d)) by (unfold ikdG, kdG; irs).
  refine (conj dA (conj U (conj dG _))). unfold ikdN, kdN. irs.
Qed.

Lemma ikT_parts : inR ikW (kW c om d) /\ inR ikdW (kdW c om gamma d) /\ inR ikT (kT c om gamma d).
Proof.
  destruct HC as [A [G [N [B [S [S1 [Dd [MV [M2 [Tm [TA [LS LD]]]]]]]]]]]].
  destruct kP_parts as [_ [_ [_ [_ [_ P]]]]]. destruct ikU_parts as [_ [_ [_ dN]]]. pose proof two_ok.
  assert (Ld : inR ikLd (kLd om d)).
  { unfold ikLd, kLd. apply inR_mul.
    - apply inR_add; [apply inR_abs, HOM |]. unfold kappa. rewrite Rinv_inv. exact (inR_Z 10).
    - apply ikdE_ok; [apply div2_ok, HDD | lra]. }
  assert (M : inR ikM (kM c om d)) by (unfold ikM, kM; irs).
  assert (dM : inR ikdM (kdM c om gamma d)) by (unfold ikdM, kdM; irs).
  assert (W : inR ikW (kW c om d)) by (unfold ikW, kW; irs).
  assert (dW : inR ikdW (kdW c om gamma d)) by (unfold ikdW, kdW; irs).
  refine (conj W (conj dW _)). unfold ikT, kT. irs.
Qed.

End Iter.

End Scal.
