(** Affine enclosures of the field lines of the coil field over binary64
    intervals.

    A set of the plane at the angle a is c + A U: a centre c and a matrix A
    of floats and a box U of intervals. One step of length h carries every
    solution of the field-line equations through the set to the set
    c' + A' U' at a + h ([step_ok]): an a priori box B over the step, checked
    as in FieldStep.v; Taylor's formula at second order with its remainder
    over B ([FieldPath.taylor2], [FieldVel.vel_path_R]); the mean value form
    of the velocity about the centre at the angle a; and a new frame A' whose
    inverse is enclosed through its adjugate. [lchain] follows the steps,
    halving a step while its checks fail, until the hull of the set leaves the
    region R <= R_D2 at angles where cos (P phi) <= 0 and R <= R_D elsewhere,
    and [lescape_no_torus] turns a chain from every box of a segment of the
    plane phi = 0 into the statement that no invariant torus of TorusLine.v
    lying in that region meets the segment. *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Float.Primitive_ops Real.Xreal Interval.Interval Interval.Float_full.
From Stellarocq Require Import KAMScalar Fourier Hypotheses CoilSym FieldKern FieldModel Invariance TorusLine
  FieldStep FieldPath FieldVel KFix KCheckKern KDense KEngine KJet KJet12 KSrcReal FloatRI.
Import ListNotations.
Local Open Scope R_scope.

Module J12 := Jet12 FI.
Import J12 J12.JO J12.JO.KO.

Module F := FI.F.
Module I := FI.I.

(** * Points, boxes and comparisons of floats *)

Definition pt_ok (m : F.type) : bool := (F.real m && F.valid_lb m && F.valid_ub m)%bool.
Definition ptR (m : F.type) : R := proj_val (F.toX m).

Lemma pt_eq (m : F.type) : pt_ok m = true -> F.toX m = Xreal (ptR m).
Proof.
  unfold pt_ok, ptR. intros H. apply andb_prop in H. destruct H as [H _]. apply andb_prop in H. destruct H as [H _].
  rewrite F.real_correct in H. destruct (F.toX m); [discriminate | reflexivity].
Qed.

Definition box (l u : F.type) : FI.t := I.bnd l u.

Lemma box_in (l u : F.type) (z : R) : pt_ok l = true -> pt_ok u = true -> ptR l <= z <= ptR u -> inR (box l u) z.
Proof.
  intros Hl Hu Hz. unfold inR, FI.inR, box.
  assert (Vl : I.valid_lb l).
  { unfold I.valid_lb. unfold pt_ok in Hl. apply andb_prop in Hl. destruct Hl as [Hl _].
    apply andb_prop in Hl. destruct Hl as [_ Hl]. exact Hl. }
  assert (Vu : I.valid_ub u).
  { unfold I.valid_ub. unfold pt_ok in Hu. apply andb_prop in Hu. destruct Hu as [_ Hu]. exact Hu. }
  rewrite (I.bnd_correct l u Vl Vu), (pt_eq l Hl), (pt_eq u Hu). cbn. lra.
Qed.

Definition pt (m : F.type) : FI.t := box m m.

Lemma pt_in (m : F.type) : pt_ok m = true -> inR (pt m) (ptR m).
Proof. intros H. apply box_in; [exact H | exact H | lra]. Qed.

(** The lower and upper ends of an interval that holds a real. *)
Lemma lower_le (X : FI.t) (x : R) : inR X x -> pt_ok (I.lower X) = true -> ptR (I.lower X) <= x.
Proof.
  intros HX Hl. unfold inR, FI.inR in HX.
  assert (NE : not_empty (I.convert X)) by (exists x; exact HX).
  pose proof (I.lower_correct X NE) as E. rewrite (pt_eq _ Hl) in E.
  destruct (I.convert X) as [| xl xu]; [discriminate |]. cbn in E. subst xl. cbn in HX. lra.
Qed.

Lemma upper_ge (X : FI.t) (x : R) : inR X x -> pt_ok (I.upper X) = true -> x <= ptR (I.upper X).
Proof.
  intros HX Hu. unfold inR, FI.inR in HX.
  assert (NE : not_empty (I.convert X)) by (exists x; exact HX).
  pose proof (I.upper_correct X NE) as E. rewrite (pt_eq _ Hu) in E.
  destruct (I.convert X) as [| xl xu]; [discriminate |]. cbn in E. subst xu. cbn in HX. lra.
Qed.

Definition flt (a b : F.type) : bool := match F.cmp a b with Xlt => true | _ => false end.

Lemma flt_ok (a b : F.type) : pt_ok a = true -> pt_ok b = true -> flt a b = true -> ptR a < ptR b.
Proof.
  intros Ha Hb H. unfold flt in H. rewrite F.cmp_correct in H.
  assert (Ra : F.real a = true) by (unfold pt_ok in Ha; apply andb_prop in Ha; destruct Ha as [Ha _];
                                    apply andb_prop in Ha; destruct Ha as [Ha _]; exact Ha).
  assert (Rb : F.real b = true) by (unfold pt_ok in Hb; apply andb_prop in Hb; destruct Hb as [Hb _];
                                    apply andb_prop in Hb; destruct Hb as [Hb _]; exact Hb).
  rewrite F.classify_correct in Ra, Rb.
  destruct (F.classify a); try discriminate. destruct (F.classify b); try discriminate.
  rewrite (pt_eq a Ha), (pt_eq b Hb) in H. cbn in H.
  destruct (Raux.Rcompare_spec (ptR a) (ptR b)) as [L | E | G]; try discriminate; exact L.
Qed.

(** * The velocity and its partial derivatives from the field's enclosures *)

Record vel := mkvel { vFR : FI.t ; vFZ : FI.t ; vRR : FI.t ; vRZ : FI.t ; vRP : FI.t ;
                      vZR : FI.t ; vZZ : FI.t ; vZP : FI.t }.

Definition iquot (Rr b dB bP dP : FI.t) : FI.t :=
  FI.div (FI.mul Rr (FI.sub (FI.mul dB bP) (FI.mul b dP))) (FI.mul bP bP).

Definition ivel (X : j12) (Rr : FI.t) : vel :=
  let v := q9 X in
  mkvel (FI.mul Rr (FI.div (g_R v) (g_P v))) (FI.mul Rr (FI.div (g_Z v) (g_P v)))
        (FI.add (FI.div (g_R v) (g_P v)) (iquot Rr (g_R v) (g_RR v) (g_P v) (g_PR v)))
        (iquot Rr (g_R v) (g_RZ v) (g_P v) (g_PZ v)) (iquot Rr (g_R v) (qRP X) (g_P v) (qPP X))
        (FI.add (FI.div (g_Z v) (g_P v)) (iquot Rr (g_Z v) (g_ZR v) (g_P v) (g_PR v)))
        (iquot Rr (g_Z v) (g_ZZ v) (g_P v) (g_PZ v)) (iquot Rr (g_Z v) (qZP X) (g_P v) (qPP X)).

Section Vel.

Variables (P : nat) (l : list (src * fser)).
Notation BB := (coilB (Z.of_nat P) l).

Definition vel_in (V : vel) (R0 phi Z0 : R) : Prop :=
  inR (vFR V) (flR BB R0 phi Z0) /\ inR (vFZ V) (flZ BB R0 phi Z0) /\
  inR (vRR V) (VR_R P l R0 phi Z0) /\ inR (vRZ V) (VR_Z P l R0 phi Z0) /\ inR (vRP V) (VR_P P l R0 phi Z0) /\
  inR (vZR V) (VZ_R P l R0 phi Z0) /\ inR (vZZ V) (VZ_Z P l R0 phi Z0) /\ inR (vZP V) (VZ_P P l R0 phi Z0).

Lemma iquot_ok (Rr b dB bP dP : FI.t) (R0 rb rdB rbP rdP : R) :
  inR Rr R0 -> inR b rb -> inR dB rdB -> inR bP rbP -> inR dP rdP -> rbP <> 0 ->
  inR (iquot Rr b dB bP dP) (R0 * (rdB * rbP - rb * rdP) / (rbP * rbP)).
Proof.
  intros H1 H2 H3 H4 H5 Hn. unfold iquot. apply inR_div.
  - apply inR_mul; [exact H1 | apply inR_sub; apply inR_mul; assumption].
  - apply inR_mul; assumption.
  - apply Rmult_integral_contrapositive_currified; exact Hn.
Qed.

Theorem ivel_ok (X : j12) (Rr : FI.t) (R0 phi Z0 : R) :
  in12 X (rcomp12 l R0 Z0 (shiftsP P phi)) -> inR Rr R0 -> B_phi BB R0 phi Z0 <> 0 ->
  vel_in (ivel X Rr) R0 phi Z0.
Proof.
  intros [[H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]] [H10 [H11 H12]]] HR Hb.
  destruct (rcomp12_val P l R0 phi Z0) as [E1 [E2 [E3 [E4 [E5 [E6 [E7 [E8 [E9 [E10 [E11 E12]]]]]]]]]]].
  cbv zeta in *. rewrite E1 in H1. rewrite E2 in H2. rewrite E3 in H3. rewrite E4 in H4. rewrite E5 in H5.
  rewrite E6 in H10. rewrite E7 in H6. rewrite E8 in H7. rewrite E9 in H11. rewrite E10 in H8.
  rewrite E11 in H9. rewrite E12 in H12.
  unfold vel_in, ivel, flR, flZ, VR_R, VR_Z, VR_P, VZ_R, VZ_Z, VZ_P. cbn [vFR vFZ vRR vRZ vRP vZR vZZ vZP].
  repeat split.
  - replace (R0 * B_R BB R0 phi Z0 / B_phi BB R0 phi Z0) with (R0 * (B_R BB R0 phi Z0 / B_phi BB R0 phi Z0))
      by (field; exact Hb).
    apply inR_mul; [exact HR | apply inR_div; assumption].
  - replace (R0 * B_Z BB R0 phi Z0 / B_phi BB R0 phi Z0) with (R0 * (B_Z BB R0 phi Z0 / B_phi BB R0 phi Z0))
      by (field; exact Hb).
    apply inR_mul; [exact HR | apply inR_div; assumption].
  - apply inR_add; [apply inR_div; assumption | apply iquot_ok; assumption].
  - apply iquot_ok; assumption.
  - apply iquot_ok; assumption.
  - apply inR_add; [apply inR_div; assumption | apply iquot_ok; assumption].
  - apply iquot_ok; assumption.
  - apply iquot_ok; assumption.
Qed.

(** * Angles *)

Definition two : FI.t := FI.of_q 2 0.

Definition itheta (j : nat) : FI.t := FI.div (FI.mul (FI.of_q (Z.of_nat j) 0) (FI.mul two FI.pi)) (FI.of_q (Z.of_nat P) 0).

Definition ics (Phi : FI.t) : list (FI.t * FI.t) :=
  map (fun j => (FI.cos (FI.add Phi (itheta j)), FI.sin (FI.add Phi (itheta j)))) (seq 0 P).

Lemma ics_ok (Phi : FI.t) (phi : R) : (0 < P)%nat -> inR Phi phi ->
  Forall2 (fun CS a => inR (fst CS) (cos a) /\ inR (snd CS) (sin a)) (ics Phi) (shiftsP P phi).
Proof.
  intros HP HPhi. unfold ics, shiftsP. generalize (seq 0 P). intros js.
  induction js as [| j js IH]; cbn [map]; constructor; [| exact IH].
  assert (Ht : inR (itheta j) (INR j * (2 * PI / INR P))).
  { unfold itheta. replace (INR j * (2 * PI / INR P)) with (IZR (Z.of_nat j) * (IZR 2 * PI) / IZR (Z.of_nat P)).
    - apply inR_div; [apply inR_mul; [apply inR_Z | apply inR_mul; [apply inR_Z | exact FI.pi_ok]] | apply inR_Z |].
      apply not_0_IZR. lia.
    - rewrite <- !INR_IZR_INZ. field. apply not_0_INR. lia. }
  cbn [fst snd]. split; [apply FI.cos_ok | apply FI.sin_ok]; apply inR_add; assumption.
Qed.

(** The velocity over a box of (R, Z) and an interval of angles, with the
    check that every source stays away and B_phi away from zero. *)
Definition fvel (Ss : list (i3 * i3)) (Rr Zz Phi : FI.t) : bool * vel :=
  let X := icomp12 Ss Rr Zz (ics Phi) in
  ((cpos12 Ss Rr Zz (ics Phi) && (FI.pos (g_P (q9 X)) || FI.pos (FI.neg (g_P (q9 X)))))%bool, ivel X Rr).

Theorem fvel_ok (Ss : list (i3 * i3)) (Rr Zz Phi : FI.t) (R0 Z0 phi : R) :
  (0 < P)%nat -> src_in Ss l -> inR Rr R0 -> inR Zz Z0 -> inR Phi phi -> fst (fvel Ss Rr Zz Phi) = true ->
  apart P l R0 phi Z0 /\ B_phi BB R0 phi Z0 <> 0 /\ vel_in (snd (fvel Ss Rr Zz Phi)) R0 phi Z0.
Proof.
  intros HP Hs HR HZ HPhi Hc. unfold fvel in *. cbn [fst snd] in *.
  apply andb_prop in Hc. destruct Hc as [Hp Hb].
  destruct (icomp12_ok Ss l Rr Zz R0 Z0 (ics Phi) (shiftsP P phi) Hs HR HZ (ics_ok Phi phi HP HPhi) Hp) as [HX Ha].
  destruct (rcomp12_val P l R0 phi Z0) as [_ [E2 _]]. cbv zeta in E2.
  assert (HB : B_phi BB R0 phi Z0 <> 0).
  { destruct HX as [[_ [H2 _]] _]. rewrite E2 in H2. apply orb_prop in Hb. destruct Hb as [Hb | Hb].
    - pose proof (FI.pos_ok _ _ Hb H2). lra.
    - pose proof (FI.pos_ok _ _ Hb (inR_neg _ _ H2)). lra. }
  split; [exact Ha | split; [exact HB | apply ivel_ok; assumption]].
Qed.

End Vel.

(** * Intervals between their ends *)

Lemma between (X : FI.t) (x z : R) :
  inR X x -> pt_ok (I.lower X) = true -> pt_ok (I.upper X) = true ->
  ptR (I.lower X) <= z <= ptR (I.upper X) -> inR X z.
Proof.
  intros HX Hl Hu Hz. unfold inR, FI.inR in *.
  assert (NE : not_empty (I.convert X)) by (exists x; exact HX).
  pose proof (I.lower_correct X NE) as El. pose proof (I.upper_correct X NE) as Eu.
  rewrite (pt_eq _ Hl) in El. rewrite (pt_eq _ Hu) in Eu.
  destruct (I.convert X) as [| xl xu]; [discriminate |]. cbn in El, Eu. subst xl xu. cbn. lra.
Qed.

Lemma join_between (X Y : FI.t) (x y z : R) :
  inR X x -> inR Y y -> Rmin x y <= z <= Rmax x y -> inR (FI.join X Y) z.
Proof.
  intros HX HY Hz. unfold inR, FI.inR, FI.join.
  assert (Jx : contains (I.convert (I.join X Y)) (Xreal x)) by (apply I.join_correct; left; exact HX).
  assert (Jy : contains (I.convert (I.join X Y)) (Xreal y)) by (apply I.join_correct; right; exact HY).
  destruct (Rle_dec x y) as [E | E].
  - rewrite Rmin_left, Rmax_right in Hz by lra. exact (contains_connected _ x y Jx Jy z Hz).
  - rewrite Rmin_right, Rmax_left in Hz by lra. exact (contains_connected _ y x Jy Jx z Hz).
Qed.

(** * The affine sets *)

Record lstate := mkls { lcR : F.type ; lcZ : F.type ; lA11 : F.type ; lA12 : F.type ; lA21 : F.type ;
                        lA22 : F.type ; lU1 : FI.t ; lU2 : FI.t }.

Definition st_ok (st : lstate) : bool :=
  (pt_ok (lcR st) && pt_ok (lcZ st) && pt_ok (lA11 st) && pt_ok (lA12 st) && pt_ok (lA21 st) && pt_ok (lA22 st))%bool.

Definition holds (st : lstate) (x z : R) : Prop :=
  exists u1 u2, inR (lU1 st) u1 /\ inR (lU2 st) u2 /\
    x = ptR (lcR st) + ptR (lA11 st) * u1 + ptR (lA12 st) * u2 /\
    z = ptR (lcZ st) + ptR (lA21 st) * u1 + ptR (lA22 st) * u2.

Definition hullR (st : lstate) : FI.t :=
  FI.add (FI.add (pt (lcR st)) (FI.mul (pt (lA11 st)) (lU1 st))) (FI.mul (pt (lA12 st)) (lU2 st)).
Definition hullZ (st : lstate) : FI.t :=
  FI.add (FI.add (pt (lcZ st)) (FI.mul (pt (lA21 st)) (lU1 st))) (FI.mul (pt (lA22 st)) (lU2 st)).

Lemma st_pts (st : lstate) : st_ok st = true ->
  pt_ok (lcR st) = true /\ pt_ok (lcZ st) = true /\ pt_ok (lA11 st) = true /\ pt_ok (lA12 st) = true /\
  pt_ok (lA21 st) = true /\ pt_ok (lA22 st) = true.
Proof. unfold st_ok. intros H. repeat rewrite Bool.andb_true_iff in H. tauto. Qed.

Lemma hull_ok (st : lstate) (x z : R) : st_ok st = true -> holds st x z -> inR (hullR st) x /\ inR (hullZ st) z.
Proof.
  intros Hs (u1 & u2 & H1 & H2 & Ex & Ez). destruct (st_pts st Hs) as (P1 & P2 & P3 & P4 & P5 & P6).
  unfold hullR, hullZ. rewrite Ex, Ez.
  split; apply inR_add; [apply inR_add | | apply inR_add |]; try (apply inR_mul; [apply pt_in; assumption | assumption]);
    apply pt_in; assumption.
Qed.

(** An interval widened by three quarters of its width and by 2^-60. *)
Definition eps60 : FI.t := FI.join (FI.neg (FI.of_q 1 60)) (FI.of_q 1 60).
Definition grow (X : FI.t) : FI.t := FI.add (FI.add X (FI.mul (FI.sub X X) (FI.of_q 3 2))) eps60.

Lemma grow_in (X : FI.t) (x : R) : inR X x -> inR (grow X) x.
Proof.
  intros H. unfold grow. replace x with (x + (x - x) * (IZR 3 / IZR (2 ^ 2)) + 0) by ring.
  apply inR_add; [apply inR_add; [exact H | apply inR_mul; [apply inR_sub; exact H | apply inR_q; lia]] |].
  unfold eps60. apply (FI.join_ok _ _ (- (IZR 1 / IZR (2 ^ 60))) (IZR 1 / IZR (2 ^ 60))).
  - apply inR_neg, inR_q. lia.
  - apply inR_q. lia.
  - split; [| apply Rlt_le]; apply Rdiv_lt_0_compat || lra; try (apply IZR_lt; reflexivity);
      unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat, IZR_lt; reflexivity.
Qed.

(** * One step *)

(** The enclosures a step reads: [sPa] holds its first angle a, [sPs] every
    angle of [a, a + h], [sH] the length h, [sH0] every t in [0, h] and
    [sH2] h^2 / 2. *)
Record stepin := mkstep { sPa : FI.t ; sPs : FI.t ; sH : FI.t ; sH0 : FI.t ; sH2 : FI.t }.

Definition one : FI.t := FI.of_q 1 0.

Section Parts.

Variables (P : nat) (Ss : list (i3 * i3)) (si : stepin) (st : lstate).

Definition XR := hullR st.
Definition XZ := hullZ st.
Definition V0 := snd (fvel P Ss XR XZ (sPs si)).
(** The a priori box. *)
Definition GR := grow (FI.join XR (FI.add XR (FI.mul (sH0 si) (vFR V0)))).
Definition GZ := grow (FI.join XZ (FI.add XZ (FI.mul (sH0 si) (vFZ V0)))).
Definition VB := fvel P Ss GR GZ (sPs si).
Definition E2R := FI.add XR (FI.mul (sH0 si) (vFR (snd VB))).
Definition E2Z := FI.add XZ (FI.mul (sH0 si) (vFZ (snd VB))).
(** The second derivative of the solution over the box and the step. *)
Definition ER := FI.add (FI.add (FI.mul (vRR (snd VB)) (vFR (snd VB))) (FI.mul (vRZ (snd VB)) (vFZ (snd VB))))
                        (vRP (snd VB)).
Definition EZ := FI.add (FI.add (FI.mul (vZR (snd VB)) (vFR (snd VB))) (FI.mul (vZZ (snd VB)) (vFZ (snd VB))))
                        (vZP (snd VB)).
(** The velocity at the centre and its Jacobian between the centre and the set. *)
Definition VC := fvel P Ss (pt (lcR st)) (pt (lcZ st)) (sPa si).
Definition VX := fvel P Ss (FI.join (pt (lcR st)) XR) (FI.join (pt (lcZ st)) XZ) (sPa si).
Definition M11 := FI.add one (FI.mul (sH si) (vRR (snd VX))).
Definition M12 := FI.mul (sH si) (vRZ (snd VX)).
Definition M21 := FI.mul (sH si) (vZR (snd VX)).
Definition M22 := FI.add one (FI.mul (sH si) (vZZ (snd VX))).
Definition MA11 := FI.add (FI.mul M11 (pt (lA11 st))) (FI.mul M12 (pt (lA21 st))).
Definition MA12 := FI.add (FI.mul M11 (pt (lA12 st))) (FI.mul M12 (pt (lA22 st))).
Definition MA21 := FI.add (FI.mul M21 (pt (lA11 st))) (FI.mul M22 (pt (lA21 st))).
Definition MA22 := FI.add (FI.mul M21 (pt (lA12 st))) (FI.mul M22 (pt (lA22 st))).
(** The image of the centre with the remainder. *)
Definition YR := FI.add (FI.add (pt (lcR st)) (FI.mul (sH si) (vFR (snd VC)))) (FI.mul (sH2 si) ER).
Definition YZ := FI.add (FI.add (pt (lcZ st)) (FI.mul (sH si) (vFZ (snd VC)))) (FI.mul (sH2 si) EZ).
(** The new frame, a rotation along the first column of MA, and its inverse. *)
Definition nrm := FI.sqrt (FI.add (FI.mul (pt (I.midpoint MA11)) (pt (I.midpoint MA11)))
                                  (FI.mul (pt (I.midpoint MA21)) (pt (I.midpoint MA21)))).
Definition fc := I.midpoint (FI.div (pt (I.midpoint MA11)) nrm).
Definition fs := I.midpoint (FI.div (pt (I.midpoint MA21)) nrm).
Definition fms := F.neg fs.
Definition det := FI.sub (FI.mul (pt fc) (pt fc)) (FI.mul (pt fms) (pt fs)).
Definition i11 := FI.div (pt fc) det.
Definition i12 := FI.div (FI.neg (pt fms)) det.
Definition i21 := FI.div (FI.neg (pt fs)) det.
Definition i22 := FI.div (pt fc) det.
Definition cR' := I.midpoint YR.
Definition cZ' := I.midpoint YZ.
Definition U1' := FI.add (FI.add (FI.mul i11 (FI.sub YR (pt cR'))) (FI.mul i12 (FI.sub YZ (pt cZ'))))
                         (FI.add (FI.mul (FI.add (FI.mul i11 MA11) (FI.mul i12 MA21)) (lU1 st))
                                 (FI.mul (FI.add (FI.mul i11 MA12) (FI.mul i12 MA22)) (lU2 st))).
Definition U2' := FI.add (FI.add (FI.mul i21 (FI.sub YR (pt cR'))) (FI.mul i22 (FI.sub YZ (pt cZ'))))
                         (FI.add (FI.mul (FI.add (FI.mul i21 MA11) (FI.mul i22 MA21)) (lU1 st))
                                 (FI.mul (FI.add (FI.mul i21 MA12) (FI.mul i22 MA22)) (lU2 st))).
Definition st' := mkls cR' cZ' fc fms fs fc U1' U2'.

(** Every check of the step. *)
Definition checks : list bool :=
  [fst VB; fst VC; fst VX;
   pt_ok (I.lower XR); pt_ok (I.upper XR); pt_ok (I.lower XZ); pt_ok (I.upper XZ);
   pt_ok (I.lower GR); pt_ok (I.upper GR); pt_ok (I.lower GZ); pt_ok (I.upper GZ);
   pt_ok (I.lower (vFR (snd VB))); pt_ok (I.upper (vFR (snd VB)));
   pt_ok (I.lower (vFZ (snd VB))); pt_ok (I.upper (vFZ (snd VB)));
   pt_ok (I.lower E2R); pt_ok (I.upper E2R); pt_ok (I.lower E2Z); pt_ok (I.upper E2Z);
   flt (I.lower GR) (I.lower E2R); flt (I.upper E2R) (I.upper GR);
   flt (I.lower GZ) (I.lower E2Z); flt (I.upper E2Z) (I.upper GZ);
   FI.pos det; st_ok st'].

End Parts.

Definition lstep (P : nat) (Ss : list (i3 * i3)) (si : stepin) (st : lstate) : bool * lstate :=
  (forallb (fun b => b) (checks P Ss si st), st' P Ss si st).

(** The step with each of its parts bound once, which is how the extracted
    chain computes it: extracted, the definitions of the section are
    functions that recompute every part they read. *)
Definition lstepl (P : nat) (Ss : list (i3 * i3)) (si : stepin) (st : lstate) : bool * lstate :=
  let XR := hullR st in let XZ := hullZ st in
  let V0 := snd (fvel P Ss XR XZ (sPs si)) in
  let GR := grow (FI.join XR (FI.add XR (FI.mul (sH0 si) (vFR V0)))) in
  let GZ := grow (FI.join XZ (FI.add XZ (FI.mul (sH0 si) (vFZ V0)))) in
  let VB := fvel P Ss GR GZ (sPs si) in
  let vb := snd VB in
  let E2R := FI.add XR (FI.mul (sH0 si) (vFR vb)) in
  let E2Z := FI.add XZ (FI.mul (sH0 si) (vFZ vb)) in
  let ER := FI.add (FI.add (FI.mul (vRR vb) (vFR vb)) (FI.mul (vRZ vb) (vFZ vb))) (vRP vb) in
  let EZ := FI.add (FI.add (FI.mul (vZR vb) (vFR vb)) (FI.mul (vZZ vb) (vFZ vb))) (vZP vb) in
  let VC := fvel P Ss (pt (lcR st)) (pt (lcZ st)) (sPa si) in
  let VX := fvel P Ss (FI.join (pt (lcR st)) XR) (FI.join (pt (lcZ st)) XZ) (sPa si) in
  let vx := snd VX in
  let M11 := FI.add one (FI.mul (sH si) (vRR vx)) in
  let M12 := FI.mul (sH si) (vRZ vx) in
  let M21 := FI.mul (sH si) (vZR vx) in
  let M22 := FI.add one (FI.mul (sH si) (vZZ vx)) in
  let MA11 := FI.add (FI.mul M11 (pt (lA11 st))) (FI.mul M12 (pt (lA21 st))) in
  let MA12 := FI.add (FI.mul M11 (pt (lA12 st))) (FI.mul M12 (pt (lA22 st))) in
  let MA21 := FI.add (FI.mul M21 (pt (lA11 st))) (FI.mul M22 (pt (lA21 st))) in
  let MA22 := FI.add (FI.mul M21 (pt (lA12 st))) (FI.mul M22 (pt (lA22 st))) in
  let YR := FI.add (FI.add (pt (lcR st)) (FI.mul (sH si) (vFR (snd VC)))) (FI.mul (sH2 si) ER) in
  let YZ := FI.add (FI.add (pt (lcZ st)) (FI.mul (sH si) (vFZ (snd VC)))) (FI.mul (sH2 si) EZ) in
  let m11 := pt (I.midpoint MA11) in let m21 := pt (I.midpoint MA21) in
  let nrm := FI.sqrt (FI.add (FI.mul m11 m11) (FI.mul m21 m21)) in
  let fc := I.midpoint (FI.div m11 nrm) in
  let fs := I.midpoint (FI.div m21 nrm) in
  let fms := F.neg fs in
  let det := FI.sub (FI.mul (pt fc) (pt fc)) (FI.mul (pt fms) (pt fs)) in
  let i11 := FI.div (pt fc) det in
  let i12 := FI.div (FI.neg (pt fms)) det in
  let i21 := FI.div (FI.neg (pt fs)) det in
  let i22 := FI.div (pt fc) det in
  let cR' := I.midpoint YR in let cZ' := I.midpoint YZ in
  let U1' := FI.add (FI.add (FI.mul i11 (FI.sub YR (pt cR'))) (FI.mul i12 (FI.sub YZ (pt cZ'))))
                    (FI.add (FI.mul (FI.add (FI.mul i11 MA11) (FI.mul i12 MA21)) (lU1 st))
                            (FI.mul (FI.add (FI.mul i11 MA12) (FI.mul i12 MA22)) (lU2 st))) in
  let U2' := FI.add (FI.add (FI.mul i21 (FI.sub YR (pt cR'))) (FI.mul i22 (FI.sub YZ (pt cZ'))))
                    (FI.add (FI.mul (FI.add (FI.mul i21 MA11) (FI.mul i22 MA21)) (lU1 st))
                            (FI.mul (FI.add (FI.mul i21 MA12) (FI.mul i22 MA22)) (lU2 st))) in
  let st2 := mkls cR' cZ' fc fms fs fc U1' U2' in
  (forallb (fun b => b)
     [fst VB; fst VC; fst VX;
      pt_ok (I.lower XR); pt_ok (I.upper XR); pt_ok (I.lower XZ); pt_ok (I.upper XZ);
      pt_ok (I.lower GR); pt_ok (I.upper GR); pt_ok (I.lower GZ); pt_ok (I.upper GZ);
      pt_ok (I.lower (vFR vb)); pt_ok (I.upper (vFR vb));
      pt_ok (I.lower (vFZ vb)); pt_ok (I.upper (vFZ vb));
      pt_ok (I.lower E2R); pt_ok (I.upper E2R); pt_ok (I.lower E2Z); pt_ok (I.upper E2Z);
      flt (I.lower GR) (I.lower E2R); flt (I.upper E2R) (I.upper GR);
      flt (I.lower GZ) (I.lower E2Z); flt (I.upper E2Z) (I.upper GZ);
      FI.pos det; st_ok st2], st2).

Lemma lstepl_eq (P : nat) (Ss : list (i3 * i3)) (si : stepin) (st : lstate) :
  lstepl P Ss si st = lstep P Ss si st.
Proof.
  cbv delta [lstepl lstep checks st' XR XZ V0 GR GZ VB E2R E2Z ER EZ VC VX M11 M12 M21 M22 MA11 MA12 MA21 MA22
             YR YZ nrm fc fs fms det i11 i12 i21 i22 cR' cZ' U1' U2'] beta zeta.
  reflexivity.
Qed.

Ltac inlist := repeat (first [left; reflexivity | right]).

Section StepSound.

Variables (P : nat) (l : list (src * fser)) (Ss : list (i3 * i3)).
Hypothesis HP : (0 < P)%nat.
Hypothesis Hsrc : src_in Ss l.
Notation BB := (coilB (Z.of_nat P) l).

Lemma join_left (X Y : FI.t) (x : R) : inR X x -> inR (FI.join X Y) x.
Proof. intros H. unfold inR, FI.inR, FI.join. apply I.join_correct. left. exact H. Qed.

Lemma is_derive_idR (x : R) : is_derive (fun t : R => t) x 1.
Proof. auto_derive; [exact I | ring]. Qed.

Lemma is_derive_affine (c v x : R) : is_derive (fun t : R => c + t * v) x v.
Proof. auto_derive; [exact I | ring]. Qed.

Theorem lstep_ok (si : stepin) (st : lstate) (r z : R -> R) (a h : R) :
  0 < h -> inR (sPa si) a -> (forall t, a <= t <= a + h -> inR (sPs si) t) -> inR (sH si) h ->
  (forall t, 0 <= t <= h -> inR (sH0 si) t) -> inR (sH2 si) (h * h / 2) ->
  (forall s, a <= s <= a + h -> is_derive r s (flR BB (r s) s (z s)) /\ is_derive z s (flZ BB (r s) s (z s))) ->
  st_ok st = true -> holds st (r a) (z a) ->
  fst (lstep P Ss si st) = true ->
  st_ok (snd (lstep P Ss si st)) = true /\ holds (snd (lstep P Ss si st)) (r (a + h)) (z (a + h)).
Proof.
  intros Hh HPa HPs HH HH0 HH2 Hsol Hst Hhold Hc.
  assert (K : forall b, In b (checks P Ss si st) -> b = true).
  { unfold lstep in Hc. cbn [fst] in Hc. rewrite forallb_forall in Hc. exact Hc. }
  assert (CVB : fst (VB P Ss si st) = true) by (apply K; unfold checks; inlist).
  assert (CVC : fst (VC P Ss si st) = true) by (apply K; unfold checks; inlist).
  assert (CVX : fst (VX P Ss si st) = true) by (apply K; unfold checks; inlist).
  assert (PXl : pt_ok (I.lower (XR st)) = true) by (apply K; unfold checks; inlist).
  assert (PXu : pt_ok (I.upper (XR st)) = true) by (apply K; unfold checks; inlist).
  assert (PZl : pt_ok (I.lower (XZ st)) = true) by (apply K; unfold checks; inlist).
  assert (PZu : pt_ok (I.upper (XZ st)) = true) by (apply K; unfold checks; inlist).
  assert (PGl : pt_ok (I.lower (GR P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PGu : pt_ok (I.upper (GR P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PHl : pt_ok (I.lower (GZ P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PHu : pt_ok (I.upper (GZ P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PFl : pt_ok (I.lower (vFR (snd (VB P Ss si st)))) = true) by (apply K; unfold checks; inlist).
  assert (PFu : pt_ok (I.upper (vFR (snd (VB P Ss si st)))) = true) by (apply K; unfold checks; inlist).
  assert (PGFl : pt_ok (I.lower (vFZ (snd (VB P Ss si st)))) = true) by (apply K; unfold checks; inlist).
  assert (PGFu : pt_ok (I.upper (vFZ (snd (VB P Ss si st)))) = true) by (apply K; unfold checks; inlist).
  assert (PEl : pt_ok (I.lower (E2R P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PEu : pt_ok (I.upper (E2R P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PEZl : pt_ok (I.lower (E2Z P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (PEZu : pt_ok (I.upper (E2Z P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (F1 : flt (I.lower (GR P Ss si st)) (I.lower (E2R P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (F2 : flt (I.upper (E2R P Ss si st)) (I.upper (GR P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (F3 : flt (I.lower (GZ P Ss si st)) (I.lower (E2Z P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (F4 : flt (I.upper (E2Z P Ss si st)) (I.upper (GZ P Ss si st)) = true) by (apply K; unfold checks; inlist).
  assert (Cdet : FI.pos (det P Ss si st) = true) by (apply K; unfold checks; inlist).
  assert (Cst' : st_ok (st' P Ss si st) = true) by (apply K; unfold checks; inlist).
  unfold lstep. cbn [snd]. split; [exact Cst' |].
  (* the hull and the a priori box *)
  destruct (hull_ok st (r a) (z a) Hst Hhold) as [HXR HXZ].
  fold (XR st) in HXR. fold (XZ st) in HXZ.
  assert (HGR : inR (GR P Ss si st) (r a)) by (unfold GR; apply grow_in, join_left, HXR).
  assert (HGZ : inR (GZ P Ss si st) (z a)) by (unfold GZ; apply grow_in, join_left, HXZ).
  set (V := snd (VB P Ss si st)).
  set (bl := ptR (I.lower (GR P Ss si st))). set (bh := ptR (I.upper (GR P Ss si st))).
  set (cl := ptR (I.lower (GZ P Ss si st))). set (ch := ptR (I.upper (GZ P Ss si st))).
  assert (InB : forall R0 s Z0, bl <= R0 <= bh -> a <= s <= a + h -> cl <= Z0 <= ch ->
            apart P l R0 s Z0 /\ B_phi BB R0 s Z0 <> 0 /\ vel_in P l V R0 s Z0).
  { intros R0 s Z0 H1 H2 H3.
    exact (fvel_ok P l Ss _ _ _ R0 Z0 s HP Hsrc (between _ _ _ HGR PGl PGu H1) (between _ _ _ HGZ PHl PHu H3)
             (HPs s H2) CVB). }
  assert (Hra : bl <= r a <= bh) by (split; [apply lower_le | apply upper_ge]; assumption).
  assert (Hza : cl <= z a <= ch) by (split; [apply lower_le | apply upper_ge]; assumption).
  destruct (InB (r a) a (z a) Hra ltac:(lra) Hza) as (_ & _ & W1 & W2 & _).
  set (fl := ptR (I.lower (vFR V))). set (fh := ptR (I.upper (vFR V))).
  set (gl := ptR (I.lower (vFZ V))). set (gh := ptR (I.upper (vFZ V))).
  set (xl := ptR (I.lower (XR st))). set (xh := ptR (I.upper (XR st))).
  set (zl := ptR (I.lower (XZ st))). set (zh := ptR (I.upper (XZ st))).
  assert (HX : (xl <= r a <= xh) /\ (zl <= z a <= zh)) by (split; split; unfold xl, xh, zl, zh;
    first [apply lower_le | apply upper_ge]; assumption).
  assert (HF : forall R0 s Z0, bl <= R0 <= bh -> a <= s <= a + h -> cl <= Z0 <= ch ->
            (fl <= flR BB R0 s Z0 <= fh) /\ (gl <= flZ BB R0 s Z0 <= gh)).
  { intros R0 s Z0 H1 H2 H3. destruct (InB R0 s Z0 H1 H2 H3) as (_ & _ & V1 & V2 & _).
    split; split; unfold fl, fh, gl, gh; first [apply (lower_le _ _ V1) | apply (upper_ge _ _ V1) |
                                             apply (lower_le _ _ V2) | apply (upper_ge _ _ V2)]; assumption. }
  (* the strict inclusions from the checks *)
  assert (Hxlh : xl <= xh) by (destruct HX as [[? ?] _]; lra).
  assert (Hzlh : zl <= zh) by (destruct HX as [_ [? ?]]; lra).
  assert (Hflh : fl <= fh) by (unfold fl, fh; pose proof (lower_le _ _ W1 PFl); pose proof (upper_ge _ _ W1 PFu); lra).
  assert (Hglh : gl <= gh) by (unfold gl, gh; pose proof (lower_le _ _ W2 PGFl); pose proof (upper_ge _ _ W2 PGFu); lra).
  assert (Xl : inR (XR st) xl) by (apply (between _ (r a) _ HXR PXl PXu); fold xl xh; lra).
  assert (Xh : inR (XR st) xh) by (apply (between _ (r a) _ HXR PXl PXu); fold xl xh; lra).
  assert (Zl : inR (XZ st) zl) by (apply (between _ (z a) _ HXZ PZl PZu); fold zl zh; lra).
  assert (Zh : inR (XZ st) zh) by (apply (between _ (z a) _ HXZ PZl PZu); fold zl zh; lra).
  assert (Fl : inR (vFR V) fl) by (apply (between _ _ _ W1 PFl PFu); fold fl fh; lra).
  assert (Fh : inR (vFR V) fh) by (apply (between _ _ _ W1 PFl PFu); fold fl fh; lra).
  assert (Gl : inR (vFZ V) gl) by (apply (between _ _ _ W2 PGFl PGFu); fold gl gh; lra).
  assert (Gh : inR (vFZ V) gh) by (apply (between _ _ _ W2 PGFl PGFu); fold gl gh; lra).
  assert (E2in : forall x t f, inR (XR st) x -> 0 <= t <= h -> inR (vFR V) f ->
            bl < x + t * f < bh).
  { intros x t f Hx Ht Hf.
    assert (I2 : inR (E2R P Ss si st) (x + t * f)) by (unfold E2R; apply inR_add; [exact Hx | apply inR_mul; [apply HH0, Ht | exact Hf]]).
    pose proof (flt_ok _ _ PGl PEl F1). pose proof (flt_ok _ _ PEu PGu F2).
    pose proof (lower_le _ _ I2 PEl). pose proof (upper_ge _ _ I2 PEu). unfold bl, bh. lra. }
  assert (E2Zin : forall x t f, inR (XZ st) x -> 0 <= t <= h -> inR (vFZ V) f ->
            cl < x + t * f < ch).
  { intros x t f Hx Ht Hf.
    assert (I2 : inR (E2Z P Ss si st) (x + t * f)) by (unfold E2Z; apply inR_add; [exact Hx | apply inR_mul; [apply HH0, Ht | exact Hf]]).
    pose proof (flt_ok _ _ PHl PEZl F3). pose proof (flt_ok _ _ PEZu PHu F4).
    pose proof (lower_le _ _ I2 PEZl). pose proof (upper_ge _ _ I2 PEZu). unfold cl, ch. lra. }
  assert (HB : bl < xl + h * Rmin 0 fl /\ xh + h * Rmax 0 fh < bh /\
               cl < zl + h * Rmin 0 gl /\ zh + h * Rmax 0 gh < ch).
  { refine (conj _ (conj _ (conj _ _))).
    - destruct (Rle_dec 0 fl) as [E | E].
      + rewrite Rmin_left by lra. replace (xl + h * 0) with (xl + 0 * fl) by ring. apply (E2in xl 0 fl); [exact Xl | lra | exact Fl].
      + rewrite Rmin_right by lra. apply (E2in xl h fl); [exact Xl | lra | exact Fl].
    - destruct (Rle_dec 0 fh) as [E | E].
      + rewrite Rmax_right by lra. apply (E2in xh h fh); [exact Xh | lra | exact Fh].
      + rewrite Rmax_left by lra. replace (xh + h * 0) with (xh + 0 * fh) by ring. apply (E2in xh 0 fh); [exact Xh | lra | exact Fh].
    - destruct (Rle_dec 0 gl) as [E | E].
      + rewrite Rmin_left by lra. replace (zl + h * 0) with (zl + 0 * gl) by ring. apply (E2Zin zl 0 gl); [exact Zl | lra | exact Gl].
      + rewrite Rmin_right by lra. apply (E2Zin zl h gl); [exact Zl | lra | exact Gl].
    - destruct (Rle_dec 0 gh) as [E | E].
      + rewrite Rmax_right by lra. apply (E2Zin zh h gh); [exact Zh | lra | exact Gh].
      + rewrite Rmax_left by lra. replace (zh + h * 0) with (zh + 0 * gh) by ring. apply (E2Zin zh 0 gh); [exact Zh | lra | exact Gh]. }
  assert (Hin : forall s, a <= s <= a + h -> (bl < r s < bh) /\ (cl < z s < ch)).
  { intros s Hs. exact (step_inside (flR BB) (flZ BB) r z a h xl xh zl zh bl bh cl ch fl fh gl gh Hsol HX HF HB s Hs). }
  (* along the step the solution stays in the box *)
  assert (Along : forall t, a <= t <= a + h ->
            apart P l (r t) t (z t) /\ B_phi BB (r t) t (z t) <> 0 /\ vel_in P l V (r t) t (z t)).
  { intros t Ht. destruct (Hin t Ht) as [H1 H2]. apply InB; lra. }
  (* Taylor's formula to second order along the solution *)
  set (f2R := fun t => VR_R P l (r t) t (z t) * flR BB (r t) t (z t) + VR_Z P l (r t) t (z t) * flZ BB (r t) t (z t)
                       + VR_P P l (r t) t (z t)).
  set (f2Z := fun t => VZ_R P l (r t) t (z t) * flR BB (r t) t (z t) + VZ_Z P l (r t) t (z t) * flZ BB (r t) t (z t)
                       + VZ_P P l (r t) t (z t)).
  assert (D2R : forall t, a <= t <= a + h -> is_derive (fun t => flR BB (r t) t (z t)) t (f2R t)).
  { intros t Ht. destruct (Along t Ht) as (Ha & Hb & _). destruct (Hsol t Ht) as [Dr Dz].
    pose proof (vel_path_R P l r (fun t => t) z t _ 1 _ Dr (is_derive_idR t) Dz Ha Hb) as G.
    cbv beta in G. rewrite Rmult_1_r in G. exact G. }
  assert (D2Z : forall t, a <= t <= a + h -> is_derive (fun t => flZ BB (r t) t (z t)) t (f2Z t)).
  { intros t Ht. destruct (Along t Ht) as (Ha & Hb & _). destruct (Hsol t Ht) as [Dr Dz].
    pose proof (vel_path_Z P l r (fun t => t) z t _ 1 _ Dr (is_derive_idR t) Dz Ha Hb) as G.
    cbv beta in G. rewrite Rmult_1_r in G. exact G. }
  destruct (taylor2 r (fun t => flR BB (r t) t (z t)) f2R a (a + h) ltac:(lra) (fun t Ht => proj1 (Hsol t Ht)) D2R)
    as [zR [HzR TR]].
  destruct (taylor2 z (fun t => flZ BB (r t) t (z t)) f2Z a (a + h) ltac:(lra) (fun t Ht => proj2 (Hsol t Ht)) D2Z)
    as [zZ [HzZ TZ]].
  replace (a + h - a) with h in TR, TZ by ring.
  assert (IER : inR (ER P Ss si st) (f2R zR)).
  { destruct (Along zR ltac:(lra)) as (_ & _ & V1 & V2 & V3 & V4 & V5 & _). unfold ER, f2R. fold V.
    apply inR_add; [apply inR_add |]; try (apply inR_mul); assumption. }
  assert (IEZ : inR (EZ P Ss si st) (f2Z zZ)).
  { destruct (Along zZ ltac:(lra)) as (_ & _ & V1 & V2 & _ & _ & _ & V6 & V7 & V8). unfold EZ, f2Z. fold V.
    apply inR_add; [apply inR_add |]; try (apply inR_mul); assumption. }
  (* the mean value form of the velocity about the centre at the angle a *)
  set (cR := ptR (lcR st)). set (cZ := ptR (lcZ st)).
  destruct (st_pts st Hst) as (PcR & PcZ & PA11 & PA12 & PA21 & PA22).
  assert (Seg : forall t, 0 <= t <= 1 ->
            apart P l (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) /\
            B_phi BB (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) <> 0 /\
            vel_in P l (snd (VX P Ss si st)) (cR + t * (r a - cR)) a (cZ + t * (z a - cZ))).
  { intros t Ht. apply (fvel_ok P l Ss _ _ _ _ _ a HP Hsrc); [| | exact HPa | exact CVX].
    - apply (join_between _ _ cR (r a)); [apply pt_in, PcR | exact HXR |].
      destruct (Rle_dec cR (r a)); [rewrite Rmin_left, Rmax_right by lra | rewrite Rmin_right, Rmax_left by lra];
        split; nra.
    - apply (join_between _ _ cZ (z a)); [apply pt_in, PcZ | exact HXZ |].
      destruct (Rle_dec cZ (z a)); [rewrite Rmin_left, Rmax_right by lra | rewrite Rmin_right, Rmax_left by lra];
        split; nra. }
  assert (DG : forall (Fv : R -> R -> R -> R) (J1 J2 J3 : R -> R -> R -> R),
            (forall t, 0 <= t <= 1 ->
               is_derive (fun t => Fv (cR + t * (r a - cR)) a (cZ + t * (z a - cZ))) t
                 (J1 (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) * (r a - cR)
                  + J2 (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) * (z a - cZ)
                  + J3 (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) * 0)) ->
            exists tau, 0 < tau < 1 /\
              Fv (r a) a (z a) = Fv cR a cZ + J1 (cR + tau * (r a - cR)) a (cZ + tau * (z a - cZ)) * (r a - cR)
                                             + J2 (cR + tau * (r a - cR)) a (cZ + tau * (z a - cZ)) * (z a - cZ)).
  { intros Fv J1 J2 J3 HD.
    destruct (MVT_cor2 (fun t => Fv (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)))
                (fun t => J1 (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) * (r a - cR)
                          + J2 (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) * (z a - cZ)
                          + J3 (cR + t * (r a - cR)) a (cZ + t * (z a - cZ)) * 0) 0 1 ltac:(lra)) as [tau [E Ht]].
    { intros t Ht. apply is_derive_Reals, HD, Ht. }
    exists tau. split; [exact Ht |]. cbv beta in E.
    replace (cR + 1 * (r a - cR)) with (r a) in E by ring. replace (cZ + 1 * (z a - cZ)) with (z a) in E by ring.
    replace (cR + 0 * (r a - cR)) with cR in E by ring. replace (cZ + 0 * (z a - cZ)) with cZ in E by ring.
    lra. }
  assert (DPath : forall t, 0 <= t <= 1 ->
            is_derive (fun t => cR + t * (r a - cR)) t (r a - cR) /\ is_derive (fun _ : R => a) t 0 /\
            is_derive (fun t => cZ + t * (z a - cZ)) t (z a - cZ)).
  { intros t _. split; [apply is_derive_affine | split; [exact (is_derive_const a t) | apply is_derive_affine]]. }
  destruct (DG (flR BB) (VR_R P l) (VR_Z P l) (VR_P P l)) as [tR [HtR MR]].
  { intros t Ht. destruct (Seg t Ht) as (Ha & Hb & _). destruct (DPath t Ht) as (D1 & D2 & D3).
    exact (vel_path_R P l _ _ _ t _ _ _ D1 D2 D3 Ha Hb). }
  destruct (DG (flZ BB) (VZ_R P l) (VZ_Z P l) (VZ_P P l)) as [tZ [HtZ MZ]].
  { intros t Ht. destruct (Seg t Ht) as (Ha & Hb & _). destruct (DPath t Ht) as (D1 & D2 & D3).
    exact (vel_path_Z P l _ _ _ t _ _ _ D1 D2 D3 Ha Hb). }
  destruct (Seg tR ltac:(lra)) as (_ & _ & _ & _ & JRR & JRZ & _).
  destruct (Seg tZ ltac:(lra)) as (_ & _ & _ & _ & _ & _ & _ & JZR & JZZ & _).
  destruct (fvel_ok P l Ss _ _ _ cR cZ a HP Hsrc (pt_in _ PcR) (pt_in _ PcZ) HPa CVC) as (_ & _ & VC1 & VC2 & _).
  (* the new coordinates *)
  set (A11 := ptR (lA11 st)). set (A12 := ptR (lA12 st)). set (A21 := ptR (lA21 st)). set (A22 := ptR (lA22 st)).
  destruct Hhold as (u1 & u2 & Hu1 & Hu2 & Era & Eza). fold cR A11 A12 in Era. fold cZ A21 A22 in Eza.
  unfold st_ok in Cst'. cbn [lcR lcZ lA11 lA12 lA21 lA22 st'] in Cst'.
  repeat rewrite Bool.andb_true_iff in Cst'.
  destruct Cst' as [[[[[PcR' PcZ'] Pfc] Pfms] Pfs] _].
  set (fcr := ptR (fc P Ss si st)). set (fmsr := ptR (fms P Ss si st)). set (fsr := ptR (fs P Ss si st)).
  set (detr := fcr * fcr - fmsr * fsr).
  assert (Hdet : inR (det P Ss si st) detr) by (unfold det, detr; apply inR_sub; apply inR_mul; apply pt_in; assumption).
  assert (Dpos : 0 < detr) by exact (FI.pos_ok _ _ Cdet Hdet).
  set (cR'r := ptR (cR' P Ss si st)). set (cZ'r := ptR (cZ' P Ss si st)).
  set (JRRv := VR_R P l (cR + tR * (r a - cR)) a (cZ + tR * (z a - cZ))) in *.
  set (JRZv := VR_Z P l (cR + tR * (r a - cR)) a (cZ + tR * (z a - cZ))) in *.
  set (JZRv := VZ_R P l (cR + tZ * (r a - cR)) a (cZ + tZ * (z a - cZ))) in *.
  set (JZZv := VZ_Z P l (cR + tZ * (r a - cR)) a (cZ + tZ * (z a - cZ))) in *.
  set (YRv := cR + h * flR BB cR a cZ + h * h / 2 * f2R zR).
  set (YZv := cZ + h * flZ BB cR a cZ + h * h / 2 * f2Z zZ).
  set (MA11v := (1 + h * JRRv) * A11 + h * JRZv * A21). set (MA12v := (1 + h * JRRv) * A12 + h * JRZv * A22).
  set (MA21v := h * JZRv * A11 + (1 + h * JZZv) * A21). set (MA22v := h * JZRv * A12 + (1 + h * JZZv) * A22).
  assert (ER1 : r (a + h) = YRv + MA11v * u1 + MA12v * u2).
  { rewrite TR, MR. unfold YRv, MA11v, MA12v. rewrite Era, Eza. ring. }
  assert (EZ1 : z (a + h) = YZv + MA21v * u1 + MA22v * u2).
  { rewrite TZ, MZ. unfold YZv, MA21v, MA22v. rewrite Era, Eza. ring. }
  set (u1' := (fcr * (r (a + h) - cR'r) + - fmsr * (z (a + h) - cZ'r)) / detr).
  set (u2' := (- fsr * (r (a + h) - cR'r) + fcr * (z (a + h) - cZ'r)) / detr).
  exists u1', u2'. cbn [lU1 lU2 lcR lcZ lA11 lA12 lA21 lA22 st'].
  (* the memberships *)
  assert (IYR : inR (YR P Ss si st) YRv).
  { unfold YR, YRv. apply inR_add; [apply inR_add; [apply pt_in, PcR | apply inR_mul; assumption] |].
    apply inR_mul; assumption. }
  assert (IYZ : inR (YZ P Ss si st) YZv).
  { unfold YZ, YZv. apply inR_add; [apply inR_add; [apply pt_in, PcZ | apply inR_mul; assumption] |].
    apply inR_mul; assumption. }
  assert (IM11 : inR (M11 P Ss si st) (1 + h * JRRv)) by (unfold M11, one; apply inR_add; [apply inR_Z | apply inR_mul; assumption]).
  assert (IM12 : inR (M12 P Ss si st) (h * JRZv)) by (unfold M12; apply inR_mul; assumption).
  assert (IM21 : inR (M21 P Ss si st) (h * JZRv)) by (unfold M21; apply inR_mul; assumption).
  assert (IM22 : inR (M22 P Ss si st) (1 + h * JZZv)) by (unfold M22, one; apply inR_add; [apply inR_Z | apply inR_mul; assumption]).
  assert (IA11 : inR (MA11 P Ss si st) MA11v) by (unfold MA11, MA11v; apply inR_add; apply inR_mul; try assumption; apply pt_in; assumption).
  assert (IA12 : inR (MA12 P Ss si st) MA12v) by (unfold MA12, MA12v; apply inR_add; apply inR_mul; try assumption; apply pt_in; assumption).
  assert (IA21 : inR (MA21 P Ss si st) MA21v) by (unfold MA21, MA21v; apply inR_add; apply inR_mul; try assumption; apply pt_in; assumption).
  assert (IA22 : inR (MA22 P Ss si st) MA22v) by (unfold MA22, MA22v; apply inR_add; apply inR_mul; try assumption; apply pt_in; assumption).
  assert (Dn : detr <> 0) by lra.
  assert (Ii11 : inR (i11 P Ss si st) (fcr / detr)) by (unfold i11; apply inR_div; [apply pt_in, Pfc | exact Hdet | exact Dn]).
  assert (Ii12 : inR (i12 P Ss si st) (- fmsr / detr)) by (unfold i12; apply inR_div; [apply inR_neg, pt_in, Pfms | exact Hdet | exact Dn]).
  assert (Ii21 : inR (i21 P Ss si st) (- fsr / detr)) by (unfold i21; apply inR_div; [apply inR_neg, pt_in, Pfs | exact Hdet | exact Dn]).
  assert (Ii22 : inR (i22 P Ss si st) (fcr / detr)) by (unfold i22; apply inR_div; [apply pt_in, Pfc | exact Hdet | exact Dn]).
  assert (IDR : inR (FI.sub (YR P Ss si st) (pt (cR' P Ss si st))) (YRv - cR'r)) by (apply inR_sub; [exact IYR | apply pt_in, PcR']).
  assert (IDZ : inR (FI.sub (YZ P Ss si st) (pt (cZ' P Ss si st))) (YZv - cZ'r)) by (apply inR_sub; [exact IYZ | apply pt_in, PcZ']).
  refine (conj _ (conj _ (conj _ _))).
  - replace u1' with (fcr / detr * (YRv - cR'r) + - fmsr / detr * (YZv - cZ'r)
                      + ((fcr / detr * MA11v + - fmsr / detr * MA21v) * u1 + (fcr / detr * MA12v + - fmsr / detr * MA22v) * u2)).
    + unfold U1'. apply inR_add.
      * apply inR_add; apply inR_mul; assumption.
      * apply inR_add; apply inR_mul; [apply inR_add; apply inR_mul; assumption | assumption
                                     | apply inR_add; apply inR_mul; assumption | assumption].
    + unfold u1'. rewrite ER1, EZ1. field. exact Dn.
  - replace u2' with (- fsr / detr * (YRv - cR'r) + fcr / detr * (YZv - cZ'r)
                      + ((- fsr / detr * MA11v + fcr / detr * MA21v) * u1 + (- fsr / detr * MA12v + fcr / detr * MA22v) * u2)).
    + unfold U2'. apply inR_add.
      * apply inR_add; apply inR_mul; assumption.
      * apply inR_add; apply inR_mul; [apply inR_add; apply inR_mul; assumption | assumption
                                     | apply inR_add; apply inR_mul; assumption | assumption].
    + unfold u2'. rewrite ER1, EZ1. field. exact Dn.
  - fold cR'r fcr fmsr. unfold u1', u2', detr. field. fold detr. exact Dn.
  - fold cZ'r fsr fcr. unfold u1', u2', detr. field. fold detr. exact Dn.
Qed.

End StepSound.

(** * Chains *)

(** Angles count in units of u = 2 pi / (M 2^J): a step of exponent j has
    length 2^(J - j) u, and the chain takes at each angle the longest step
    of exponent j <= J whose checks pass. *)
Definition half : FI.t := FI.of_q 1 1.

Definition sin_at (Hu : FI.t) (n k : Z) : stepin :=
  let A := FI.mul (FI.of_q n 0) Hu in
  let H := FI.mul (FI.of_q k 0) Hu in
  mkstep A (FI.join A (FI.add A H)) H (FI.join FI.zero H) (FI.mul (FI.mul H H) half).

Fixpoint first_step (P : nat) (Ss : list (i3 * i3)) (Hu : FI.t) (J : nat) (n : Z) (st : lstate) (js : list nat)
    : option (Z * lstate) :=
  match js with
  | [] => None
  | j :: rest =>
      let k := (2 ^ Z.of_nat (J - j))%Z in
      let r := lstepl P Ss (sin_at Hu n k) st in
      if fst r then Some ((n + k)%Z, snd r) else first_step P Ss Hu J n st rest
  end.

(** The region: R <= R_D2 where cos (P phi) <= 0, a quarter period or more
    from the planes phi = 2 pi k / P, and R <= R_D elsewhere. The set has
    left it when its hull lies beyond R_D2 at an angle whose cos (P phi) is
    enclosed below zero, or beyond both bounds. *)
Definition rho (P : nat) (rD rD2 phi : R) : R := if Rle_dec (cos (INR P * phi)) 0 then rD2 else rD.

Definition beyond (P : nat) (Hu RD RD2 : FI.t) (n : Z) (st : lstate) : bool :=
  let C := FI.cos (FI.mul (FI.of_q (Z.of_nat P) 0) (FI.mul (FI.of_q n 0) Hu)) in
  ((FI.nonneg (FI.neg C) && FI.pos (FI.sub (hullR st) RD2)) ||
   (FI.pos (FI.sub (hullR st) RD) && FI.pos (FI.sub (hullR st) RD2)))%bool.

Fixpoint lchain (P : nat) (Ss : list (i3 * i3)) (Hu RD RD2 : FI.t) (J : nat) (fuel : nat) (n : Z) (st : lstate)
    : bool :=
  beyond P Hu RD RD2 n st ||
  match fuel with
  | O => false
  | S f =>
      match first_step P Ss Hu J n st (seq 0 (S J)) with
      | Some (n', st') => lchain P Ss Hu RD RD2 J f n' st'
      | None => false
      end
  end.

Section ChainSound.

Variables (P : nat) (l : list (src * fser)) (Ss : list (i3 * i3)).
Hypothesis HP : (0 < P)%nat.
Hypothesis Hsrc : src_in Ss l.
Notation BB := (coilB (Z.of_nat P) l).
Variables (Hu RD RD2 : FI.t) (u rD rD2 : R) (J : nat).
Hypothesis Hu_ok : inR Hu u.
Hypothesis Hu_pos : 0 < u.
Hypothesis HRD : inR RD rD.
Hypothesis HRD2 : inR RD2 rD2.

Lemma beyond_ok (n : Z) (st : lstate) (x z0 : R) :
  st_ok st = true -> holds st x z0 -> beyond P Hu RD RD2 n st = true -> rho P rD rD2 (IZR n * u) < x.
Proof.
  intros Hst Hh Hb. destruct (hull_ok st x z0 Hst Hh) as [HX _].
  assert (HC : inR (FI.cos (FI.mul (FI.of_q (Z.of_nat P) 0) (FI.mul (FI.of_q n 0) Hu))) (cos (INR P * (IZR n * u)))).
  { apply FI.cos_ok. rewrite INR_IZR_INZ. apply inR_mul; [apply inR_Z | apply inR_mul; [apply inR_Z | exact Hu_ok]]. }
  unfold beyond in Hb. apply orb_prop in Hb. unfold rho.
  destruct Hb as [Hb | Hb]; apply andb_prop in Hb; destruct Hb as [H1 H2].
  - pose proof (FI.nonneg_ok _ _ H1 (inR_neg _ _ HC)) as Hc.
    destruct (Rle_dec (cos (INR P * (IZR n * u))) 0) as [_ | Hn]; [| lra].
    pose proof (FI.pos_ok _ _ H2 (inR_sub _ _ _ _ HX HRD2)). lra.
  - pose proof (FI.pos_ok _ _ H1 (inR_sub _ _ _ _ HX HRD)). pose proof (FI.pos_ok _ _ H2 (inR_sub _ _ _ _ HX HRD2)).
    destruct (Rle_dec (cos (INR P * (IZR n * u))) 0); lra.
Qed.

Lemma sin_at_ok (n k : Z) : (0 < k)%Z ->
  let a := IZR n * u in let h := IZR k * u in
  0 < h /\ inR (sPa (sin_at Hu n k)) a /\ (forall t, a <= t <= a + h -> inR (sPs (sin_at Hu n k)) t) /\
  inR (sH (sin_at Hu n k)) h /\ (forall t, 0 <= t <= h -> inR (sH0 (sin_at Hu n k)) t) /\
  inR (sH2 (sin_at Hu n k)) (h * h / 2) /\ a + h = IZR (n + k) * u.
Proof.
  intros Hk. cbv zeta. unfold sin_at. cbn [sPa sPs sH sH0 sH2].
  assert (IA : inR (FI.mul (FI.of_q n 0) Hu) (IZR n * u)) by (apply inR_mul; [apply inR_Z | exact Hu_ok]).
  assert (IH : inR (FI.mul (FI.of_q k 0) Hu) (IZR k * u)) by (apply inR_mul; [apply inR_Z | exact Hu_ok]).
  assert (Hh : 0 < IZR k * u) by (apply Rmult_lt_0_compat; [apply IZR_lt; exact Hk | exact Hu_pos]).
  refine (conj Hh (conj IA (conj _ (conj IH (conj _ (conj _ _)))))).
  - intros t Ht. apply (FI.join_ok _ _ (IZR n * u) (IZR n * u + IZR k * u)); [exact IA | apply inR_add; assumption | exact Ht].
  - intros t Ht. apply (FI.join_ok _ _ 0 (IZR k * u)); [exact FI.zero_ok | exact IH | exact Ht].
  - replace (IZR k * u * (IZR k * u) / 2) with (IZR k * u * (IZR k * u) * (IZR 1 / IZR (2 ^ 1))).
    + apply inR_mul; [apply inR_mul; assumption | apply inR_q; lia].
    + change (2 ^ 1)%Z with 2%Z. field.
  - rewrite plus_IZR. ring.
Qed.

Lemma first_step_ok (n : Z) (st : lstate) (r z : R -> R) (js : list nat) (n' : Z) (st2 : lstate) :
  (forall s, IZR n * u <= s -> is_derive r s (flR BB (r s) s (z s)) /\ is_derive z s (flZ BB (r s) s (z s))) ->
  st_ok st = true -> holds st (r (IZR n * u)) (z (IZR n * u)) ->
  first_step P Ss Hu J n st js = Some (n', st2) ->
  (n < n')%Z /\ st_ok st2 = true /\ holds st2 (r (IZR n' * u)) (z (IZR n' * u)).
Proof.
  intros Hsol Hst Hhold. induction js as [| j rest IH]; cbn [first_step]; [discriminate |].
  set (k := (2 ^ Z.of_nat (J - j))%Z).
  assert (Hk : (0 < k)%Z) by (apply Z.pow_pos_nonneg; lia).
  rewrite lstepl_eq.
  destruct (lstep P Ss (sin_at Hu n k) st) as [ok st1] eqn:E. cbn [fst snd].
  destruct ok.
  - intros Hs. injection Hs as <- <-.
    destruct (sin_at_ok n k Hk) as (Hh & HPa & HPs & HH & HH0 & HH2 & Ea). cbv zeta in *.
    pose proof (lstep_ok P l Ss HP Hsrc (sin_at Hu n k) st r z (IZR n * u) (IZR k * u) Hh HPa HPs HH HH0 HH2
                  (fun s Hs => Hsol s ltac:(lra)) Hst Hhold) as G.
    rewrite E in G. cbn [fst snd] in G. destruct (G eq_refl) as [G1 G2].
    split; [lia | split; [exact G1 |]]. rewrite <- Ea. exact G2.
  - exact IH.
Qed.

(** A chain that returns true takes every solution through its first set
    out of the region. *)
Theorem lchain_escapes (fuel : nat) : forall (n : Z) (st : lstate) (r z : R -> R),
  (forall s, IZR n * u <= s -> is_derive r s (flR BB (r s) s (z s)) /\ is_derive z s (flZ BB (r s) s (z s))) ->
  st_ok st = true -> holds st (r (IZR n * u)) (z (IZR n * u)) ->
  lchain P Ss Hu RD RD2 J fuel n st = true ->
  exists s, IZR n * u <= s /\ rho P rD rD2 s < r s.
Proof.
  induction fuel as [| f IH]; intros n st r z Hsol Hst Hhold Hc; cbn [lchain] in Hc;
    apply orb_prop in Hc; destruct Hc as [He | Hc].
  - exists (IZR n * u). split; [lra | exact (beyond_ok n st _ _ Hst Hhold He)].
  - discriminate.
  - exists (IZR n * u). split; [lra | exact (beyond_ok n st _ _ Hst Hhold He)].
  - destruct (first_step P Ss Hu J n st (seq 0 (S J))) as [[n' st2] |] eqn:E; [| discriminate].
    destruct (first_step_ok n st r z (seq 0 (S J)) n' st2 Hsol Hst Hhold E) as (Hn & Hst2 & Hh2).
    assert (Hnn : IZR n * u <= IZR n' * u) by (apply Rmult_le_compat_r; [lra | apply IZR_le; lia]).
    destruct (IH n' st2 r z (fun s Hs => Hsol s ltac:(lra)) Hst2 Hh2 Hc) as [s [Hs Hr]].
    exists s. split; [lra | exact Hr].
Qed.

End ChainSound.

(** * The segment *)

(** Boxes (ra, rb) at 2^-sb whose union holds every point from x to top. *)
Fixpoint covers (x : Z) (bs : list (Z * Z * nat)) (top : Z) : bool :=
  match bs with
  | [] => (top <? x)%Z
  | (ra, rb, _) :: rest => ((ra <=? x)%Z && covers (Z.max x rb) rest top)%bool
  end.

Lemma covers_ok (sb : Z) (bs : list (Z * Z * nat)) : forall (x top : Z) (y : R),
  (0 <= sb)%Z -> covers x bs top = true -> IZR x / IZR (2 ^ sb) <= y <= IZR top / IZR (2 ^ sb) ->
  exists ra rb n, In (ra, rb, n) bs /\ IZR ra / IZR (2 ^ sb) <= y <= IZR rb / IZR (2 ^ sb).
Proof.
  pose proof (fun s Hs => Rinv_0_lt_compat _ (IZR_p2_pos s Hs)) as Hp.
  induction bs as [| [[ra rb] n] rest IH]; intros x top y Hsb Hc Hy; cbn [covers] in Hc.
  - apply Z.ltb_lt in Hc. exfalso.
    assert (IZR top / IZR (2 ^ sb) < IZR x / IZR (2 ^ sb)).
    { unfold Rdiv. apply Rmult_lt_compat_r; [apply Hp, Hsb | apply IZR_lt, Hc]. }
    lra.
  - apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1.
    assert (A : IZR ra / IZR (2 ^ sb) <= IZR x / IZR (2 ^ sb)).
    { unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Hp, Hsb | apply IZR_le, H1]. }
    destruct (Rle_dec y (IZR rb / IZR (2 ^ sb))) as [Hle | Hgt].
    + exists ra, rb, n. split; [left; reflexivity | lra].
    + destruct (IH (Z.max x rb) top y Hsb H2) as [ra' [rb' [n' [Hin Hy']]]].
      * split; [| lra]. destruct (Z.max_spec x rb) as [[_ E] | [_ E]]; rewrite E; lra.
      * exists ra', rb', n'. split; [right; exact Hin | exact Hy'].
Qed.

(** The data: the field period, the steps per turn M and the finest halving
    J, the sources at 2^-ssrc, the scale sb of R1, of the two bounds R_D and
    R_D2 of the region and of the ends of the boxes, and per box its fuel. *)
Record lescdata := mklesc {
  le_P : nat ; le_M : nat ; le_J : nat ;
  le_ssrc : Z ; le_srcs : list ((Z * Z * Z) * (Z * Z * Z)) ;
  le_sb : Z ; le_R1 : Z ; le_RD : Z ; le_RD2 : Z ;
  le_boxes : list (Z * Z * nat) }.

Definition i3q (s : Z) (x : Z * Z * Z) : i3 :=
  let '(x1, x2, x3) := x in (FI.of_q x1 s, FI.of_q x2 s, FI.of_q x3 s).
Definition src_i (s : Z) (xs : list ((Z * Z * Z) * (Z * Z * Z))) : list (i3 * i3) :=
  map (fun pd => (i3q s (fst pd), i3q s (snd pd))) xs.

(** 2 pi / (M 2^J). *)
Definition iunit (M J : nat) : FI.t :=
  FI.div (FI.mul two FI.pi) (FI.mul (FI.of_q (Z.of_nat M) 0) (FI.of_q (2 ^ Z.of_nat J) 0)).

(** The first set of a box: its centre, the identity frame and the box about
    the centre, at Z = 0. *)
Definition fone : F.type := F.fromZ 1.
Definition fzero : F.type := F.fromZ 0.
Definition init (sb ra rb : Z) : lstate :=
  let Bx := FI.join (FI.of_q ra sb) (FI.of_q rb sb) in
  let c := I.midpoint Bx in
  mkls c fzero fone fzero fzero fone (FI.sub Bx (pt c)) FI.zero.

Definition box_ok (d : lescdata) (b : Z * Z * nat) : bool :=
  let '(ra, rb, fuel) := b in
  let st := init (le_sb d) ra rb in
  (st_ok st && lchain (le_P d) (src_i (le_ssrc d) (le_srcs d)) (iunit (le_M d) (le_J d)) (FI.of_q (le_RD d) (le_sb d))
                (FI.of_q (le_RD2 d) (le_sb d)) (le_J d) fuel 0 st)%bool.

Definition check_lescape (d : lescdata) : bool :=
  ((0 <? le_P d)%nat && (0 <? le_M d)%nat && (0 <=? le_sb d)%Z && (0 <=? le_ssrc d)%Z &&
   covers (le_R1 d) (le_boxes d) (le_RD d) && forallb (fun b => b) (KEngine.pmap (box_ok d) (le_boxes d)))%bool.

Definition R1r (d : lescdata) : R := IZR (le_R1 d) / IZR (2 ^ le_sb d).
Definition RDr (d : lescdata) : R := IZR (le_RD d) / IZR (2 ^ le_sb d).
Definition RD2r (d : lescdata) : R := IZR (le_RD2 d) / IZR (2 ^ le_sb d).

(** The region the tori lie in: R <= R_D2 at angles whose cos (P phi) is not
    positive and R <= R_D elsewhere. *)
Definition region (d : lescdata) (phi : R) : R := rho (le_P d) (RDr d) (RD2r d) phi.

Lemma src_i_srcl (s sY : Z) (Ky1 Ky2 : nat) (xs : list ((Z * Z * Z) * (Z * Z * Z)))
    (ys : list (list (list (Z * Z)))) :
  (0 <= s)%Z -> length xs = length ys -> src_in (src_i s xs) (srcl s sY Ky1 Ky2 xs ys).
Proof.
  intros Hs. revert ys. induction xs as [| x xs IH]; intros ys HL; [destruct ys; constructor |].
  destruct ys as [| y ys]; [discriminate |]. unfold srcl, src_i in *. cbn [combine map]. constructor.
  - destruct x as [[[p1 p2] p3] [[e1 e2] e3]]. cbn [fst snd i3q src_of sp1 sp2 sp3 sd1 sd2 sd3]. unfold inR3.
    unfold dy. split; (split; [| split]); apply inR_q, Hs.
  - apply IH. simpl in HL. lia.
Qed.

Lemma init_holds (sb ra rb : Z) (R0 : R) :
  (0 <= sb)%Z -> st_ok (init sb ra rb) = true ->
  IZR ra / IZR (2 ^ sb) <= R0 <= IZR rb / IZR (2 ^ sb) -> holds (init sb ra rb) R0 0.
Proof.
  intros Hsb Hok HR. unfold init in *. cbn [lcR lcZ lA11 lA12 lA21 lA22 lU1 lU2] in *.
  unfold st_ok in Hok. cbn [lcR lcZ lA11 lA12 lA21 lA22] in Hok. repeat rewrite Bool.andb_true_iff in Hok.
  destruct Hok as [[[[[Pc Pz] P1] P0] _] _].
  assert (E1 : ptR fone = 1) by (unfold ptR, fone; rewrite F.fromZ_correct by lia; reflexivity).
  assert (E0 : ptR fzero = 0) by (unfold ptR, fzero; rewrite F.fromZ_correct by lia; reflexivity).
  unfold holds. cbn [lcR lcZ lA11 lA12 lA21 lA22 lU1 lU2].
  exists (R0 - ptR (I.midpoint (FI.join (FI.of_q ra sb) (FI.of_q rb sb)))), 0.
  refine (conj _ (conj _ (conj _ _))).
  - apply inR_sub; [| apply pt_in, Pc].
    apply (FI.join_ok _ _ (IZR ra / IZR (2 ^ sb)) (IZR rb / IZR (2 ^ sb))); [apply inR_q, Hsb | apply inR_q, Hsb | exact HR].
  - exact FI.zero_ok.
  - rewrite E1, E0. ring.
  - rewrite E1, E0. ring.
Qed.

(** No invariant torus of TorusLine.v lying in the region meets the segment
    R1 <= R <= R_D of the line Z = 0 in the plane phi = 0. *)
Theorem lescape_no_torus (d : lescdata) (l : list (src * fser)) :
  check_lescape d = true -> src_in (src_i (le_ssrc d) (le_srcs d)) l ->
  forall (KR KZ : R -> R -> R) (om : R), fourier_torus (coilB (Z.of_nat (le_P d)) l) KR KZ om ->
  (forall t p, KR t p <= region d p) ->
  forall theta, KZ theta 0 = 0 -> ~ (R1r d <= KR theta 0 <= RDr d).
Proof.
  intros Hc Hsrc KR KZ om HT Hin theta HZ0 Hseg.
  unfold check_lescape in Hc. repeat rewrite Bool.andb_true_iff in Hc.
  destruct Hc as [[[[[HP HM] Hsb] Hs] Hcov] Hall].
  apply Nat.ltb_lt in HP, HM. apply Z.leb_le in Hsb, Hs.
  destruct (covers_ok (le_sb d) (le_boxes d) (le_R1 d) (le_RD d) (KR theta 0) Hsb Hcov Hseg)
    as [ra [rb [fuel [Hb Hy]]]].
  assert (Hok : box_ok d (ra, rb, fuel) = true).
  { rewrite forallb_forall in Hall. apply Hall. unfold KEngine.pmap. apply in_map_iff.
    exists (ra, rb, fuel). split; [reflexivity | exact Hb]. }
  unfold box_ok in Hok. apply andb_prop in Hok. destruct Hok as [Hst Hch].
  set (u := 2 * PI / (INR (le_M d) * 2 ^ le_J d)).
  assert (Hu_pos : 0 < u).
  { unfold u. pose proof PI_RGT_0. apply Rdiv_lt_0_compat; [lra |].
    apply Rmult_lt_0_compat; [apply lt_0_INR; exact HM | apply pow_lt; lra]. }
  assert (Hu : inR (iunit (le_M d) (le_J d)) u).
  { unfold iunit, u. replace (2 * PI / (INR (le_M d) * 2 ^ le_J d))
      with (IZR 2 * PI / (IZR (Z.of_nat (le_M d)) * IZR (2 ^ Z.of_nat (le_J d)))).
    - apply inR_div; [apply inR_mul; [apply inR_Z | exact FI.pi_ok] | apply inR_mul; apply inR_Z |].
      apply Rmult_integral_contrapositive_currified; apply not_0_IZR; [lia |].
      apply Z.pow_nonzero; lia.
    - rewrite <- INR_IZR_INZ, pow_IZR. reflexivity. }
  assert (HRD : inR (FI.of_q (le_RD d) (le_sb d)) (RDr d)) by (apply inR_q, Hsb).
  set (r := lineR KR om theta 0). set (z := lineZ KZ om theta 0).
  assert (Hsol : forall s, IZR 0 * u <= s -> is_derive r s (flR (coilB (Z.of_nat (le_P d)) l) (r s) s (z s)) /\
                                            is_derive z s (flZ (coilB (Z.of_nat (le_P d)) l) (r s) s (z s))).
  { intros s _. destruct (fourier_torus_line _ KR KZ om theta 0 HT s) as [_ [D1 D2]]. split; assumption. }
  assert (Er : r (IZR 0 * u) = KR theta 0) by (unfold r, lineR; f_equal; ring).
  assert (Ez : z (IZR 0 * u) = KZ theta 0) by (unfold z, lineZ; f_equal; ring).
  assert (Hh : holds (init (le_sb d) ra rb) (r (IZR 0 * u)) (z (IZR 0 * u))).
  { rewrite Er, Ez, HZ0. apply init_holds; assumption. }
  assert (HRD2 : inR (FI.of_q (le_RD2 d) (le_sb d)) (RD2r d)) by (apply inR_q, Hsb).
  destruct (lchain_escapes (le_P d) l _ HP Hsrc _ _ _ u (RDr d) (RD2r d) (le_J d) Hu Hu_pos HRD HRD2 fuel 0 _ r z
              Hsol Hst Hh Hch) as [s [_ Hs']].
  unfold r, lineR in Hs'. specialize (Hin (theta + om * (s - 0)) s). unfold region in Hin. lra.
Qed.
