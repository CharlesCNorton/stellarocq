(** Interval enclosures of the jet of one source at a point of a torus.

    For a source with enclosed point and weighted tangent, at the point
    (R cos phi, R sin phi, Z) with R, Z, cos phi and sin phi enclosed, [ijet]
    encloses the cylindrical components of the field and of its R and Z
    derivatives, the nine functions fR ... fZ_Z of FieldKern.v, once the
    squared distance is positive ([ijet_correct]). The work is split as the
    definitions are: the point, the offset r, q = |r|^2, q^(-3/2) and
    q^(-5/2), c = d x r, then the Jacobian rows and their cylindrical
    combinations ([jfrom_correct]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Stellarocq Require Import KAMScalar Fourier FourierEval KAMVec Hypotheses Invariance CoilSym FieldKern FieldFam
  FieldModel FieldJetVal KFix KCheckKern KEngine.
Import ListNotations.
Local Open Scope R_scope.

Record j9 (A : Type) := mk9 { g_R : A ; g_P : A ; g_Z : A ; g_RR : A ; g_RZ : A ; g_PR : A ; g_PZ : A ; g_ZR : A ; g_ZZ : A }.
Arguments mk9 {A}.
Arguments g_R {A}. Arguments g_P {A}. Arguments g_Z {A}. Arguments g_RR {A}. Arguments g_RZ {A}.
Arguments g_PR {A}. Arguments g_PZ {A}. Arguments g_ZR {A}. Arguments g_ZZ {A}.

(** The nine functions of one source at (R, phi, Z). *)
Definition rjet (sc : src) (R0 phi Z0 : R) : j9 R :=
  mk9 (fR sc R0 phi Z0) (fP sc R0 phi Z0) (fZ sc R0 phi Z0) (fR_R sc R0 phi Z0) (fR_Z sc R0 phi Z0)
      (fP_R sc R0 phi Z0) (fP_Z sc R0 phi Z0) (fZ_R sc R0 phi Z0) (fZ_Z sc R0 phi Z0).

Module JetOps (J : RI).

Module KO := KernOps J.
Import KO.

Definition in9 (X : j9 J.t) (x : j9 R) : Prop :=
  inR (g_R X) (g_R x) /\ inR (g_P X) (g_P x) /\ inR (g_Z X) (g_Z x) /\ inR (g_RR X) (g_RR x) /\
  inR (g_RZ X) (g_RZ x) /\ inR (g_PR X) (g_PR x) /\ inR (g_PZ X) (g_PZ x) /\ inR (g_ZR X) (g_ZR x) /\
  inR (g_ZZ X) (g_ZZ x).

Definition cst (m : Z) : J.t := J.of_q m 0.

(** The constants the kernels use, formed once. *)
Definition one : J.t := J.of_q 1 0.
Definition three : J.t := J.of_q 3 0.

Definition kh3 (q : J.t) : J.t := J.div one (J.mul q (J.sqrt q)).
Definition kh5 (q : J.t) : J.t := J.div one (J.mul (J.mul q q) (J.sqrt q)).

(** The Jacobian entry (d x e_k)_i h3 - 3 c_i r_k h5 with a given first term. *)
Definition jent (first c r h5 : J.t) : J.t := J.sub first (J.mul (J.mul (J.mul three c) r) h5).

(** The nine outputs from r, c = d x r, d, h3, h5 and the angle. *)
Definition jfrom (r c d : i3) (h3 h5 C S : J.t) : j9 J.t :=
  let '(r1, r2, r3) := r in let '(c1, c2, c3) := c in let '(D1, D2, D3) := d in
  let b1 := J.mul c1 h3 in let b2 := J.mul c2 h3 in let b3 := J.mul c3 h3 in
  let j11 := jent J.zero c1 r1 h5 in
  let j12 := jent (J.neg (J.mul D3 h3)) c1 r2 h5 in
  let j13 := jent (J.mul D2 h3) c1 r3 h5 in
  let j21 := jent (J.mul D3 h3) c2 r1 h5 in
  let j22 := jent J.zero c2 r2 h5 in
  let j23 := jent (J.neg (J.mul D1 h3)) c2 r3 h5 in
  let j31 := jent (J.neg (J.mul D2 h3)) c3 r1 h5 in
  let j32 := jent (J.mul D1 h3) c3 r2 h5 in
  let j33 := jent J.zero c3 r3 h5 in
  let jeR1 := J.add (J.mul j11 C) (J.mul j12 S) in
  let jeR2 := J.add (J.mul j21 C) (J.mul j22 S) in
  let jeR3 := J.add (J.mul j31 C) (J.mul j32 S) in
  mk9 (J.add (J.mul b1 C) (J.mul b2 S)) (J.add (J.neg (J.mul b1 S)) (J.mul b2 C)) b3
      (J.add (J.mul jeR1 C) (J.mul jeR2 S)) (J.add (J.mul j13 C) (J.mul j23 S))
      (J.add (J.neg (J.mul jeR1 S)) (J.mul jeR2 C)) (J.add (J.neg (J.mul j13 S)) (J.mul j23 C))
      jeR3 j33.

Definition ijet (p d : i3) (Rr C S Zz : J.t) : j9 J.t :=
  let r := isub3 (icyl Rr C S Zz) p in
  let q := idot3 r r in
  jfrom r (icross3 d r) d (kh3 q) (kh5 q) C S.

Lemma jent_ok (F c r h5 : J.t) (f cr rr hr : R) :
  inR F f -> inR c cr -> inR r rr -> inR h5 hr -> inR (jent F c r h5) (f - 3 * cr * rr * hr).
Proof.
  intros HF Hc Hr Hh. unfold jent. apply inR_sub; [exact HF |].
  apply inR_mul; [apply inR_mul; [apply inR_mul; [apply inR_Z | exact Hc] | exact Hr] | exact Hh].
Qed.

Theorem jfrom_correct (sc : src) (R0 phi Z0 : R) (r c d : i3) (h3i h5i C S : J.t) :
  inR3 r (kx1 R0 phi - sp1 sc, kx2 R0 phi - sp2 sc, Z0 - sp3 sc) ->
  inR3 c (ck1 sc (kx1 R0 phi) (kx2 R0 phi) Z0, ck2 sc (kx1 R0 phi) (kx2 R0 phi) Z0,
          ck3 sc (kx1 R0 phi) (kx2 R0 phi) Z0) ->
  inR3 d (sd1 sc, sd2 sc, sd3 sc) ->
  inR h3i (h3 sc (kx1 R0 phi) (kx2 R0 phi) Z0) -> inR h5i (h5 sc (kx1 R0 phi) (kx2 R0 phi) Z0) ->
  inR C (cos phi) -> inR S (sin phi) ->
  in9 (jfrom r c d h3i h5i C S) (rjet sc R0 phi Z0).
Proof.
  destruct r as [[r1 r2] r3], c as [[c1 c2] c3], d as [[D1 D2] D3].
  intros [R1 [R2 R3]] [C1 [C2 C3]] [HD1 [HD2 HD3]] H3 H5 HC HS.
  set (x1 := kx1 R0 phi) in *. set (x2 := kx2 R0 phi) in *.
  assert (J11' : inR (jent J.zero c1 r1 h5i) (J11 sc x1 x2 Z0)).
  { unfold J11. replace (- 3 * ck1 sc x1 x2 Z0 * (x1 - sp1 sc) * h5 sc x1 x2 Z0)
      with (0 - 3 * ck1 sc x1 x2 Z0 * (x1 - sp1 sc) * h5 sc x1 x2 Z0) by ring.
    apply jent_ok; [exact inR_zero | assumption | assumption | assumption]. }
  assert (J12' : inR (jent (J.neg (J.mul D3 h3i)) c1 r2 h5i) (J12 sc x1 x2 Z0)).
  { unfold J12. replace (- sd3 sc * h3 sc x1 x2 Z0) with (- (sd3 sc * h3 sc x1 x2 Z0)) by ring.
    apply jent_ok; [apply inR_neg, inR_mul | | |]; assumption. }
  assert (J13' : inR (jent (J.mul D2 h3i) c1 r3 h5i) (J13 sc x1 x2 Z0)).
  { unfold J13. apply jent_ok; [apply inR_mul | | |]; assumption. }
  assert (J21' : inR (jent (J.mul D3 h3i) c2 r1 h5i) (J21 sc x1 x2 Z0)).
  { unfold J21. apply jent_ok; [apply inR_mul | | |]; assumption. }
  assert (J22' : inR (jent J.zero c2 r2 h5i) (J22 sc x1 x2 Z0)).
  { unfold J22. replace (- 3 * ck2 sc x1 x2 Z0 * (x2 - sp2 sc) * h5 sc x1 x2 Z0)
      with (0 - 3 * ck2 sc x1 x2 Z0 * (x2 - sp2 sc) * h5 sc x1 x2 Z0) by ring.
    apply jent_ok; [exact inR_zero | assumption | assumption | assumption]. }
  assert (J23' : inR (jent (J.neg (J.mul D1 h3i)) c2 r3 h5i) (J23 sc x1 x2 Z0)).
  { unfold J23. replace (- sd1 sc * h3 sc x1 x2 Z0) with (- (sd1 sc * h3 sc x1 x2 Z0)) by ring.
    apply jent_ok; [apply inR_neg, inR_mul | | |]; assumption. }
  assert (J31' : inR (jent (J.neg (J.mul D2 h3i)) c3 r1 h5i) (J31 sc x1 x2 Z0)).
  { unfold J31. replace (- sd2 sc * h3 sc x1 x2 Z0) with (- (sd2 sc * h3 sc x1 x2 Z0)) by ring.
    apply jent_ok; [apply inR_neg, inR_mul | | |]; assumption. }
  assert (J32' : inR (jent (J.mul D1 h3i) c3 r2 h5i) (J32 sc x1 x2 Z0)).
  { unfold J32. apply jent_ok; [apply inR_mul | | |]; assumption. }
  assert (J33' : inR (jent J.zero c3 r3 h5i) (J33 sc x1 x2 Z0)).
  { unfold J33. replace (- 3 * ck3 sc x1 x2 Z0 * (Z0 - sp3 sc) * h5 sc x1 x2 Z0)
      with (0 - 3 * ck3 sc x1 x2 Z0 * (Z0 - sp3 sc) * h5 sc x1 x2 Z0) by ring.
    apply jent_ok; [exact inR_zero | assumption | assumption | assumption]. }
  assert (B1 : inR (J.mul c1 h3i) (bk1 sc x1 x2 Z0)) by (unfold bk1; apply inR_mul; assumption).
  assert (B2 : inR (J.mul c2 h3i) (bk2 sc x1 x2 Z0)) by (unfold bk2; apply inR_mul; assumption).
  assert (B3 : inR (J.mul c3 h3i) (bk3 sc x1 x2 Z0)) by (unfold bk3; apply inR_mul; assumption).
  assert (E1 : inR (J.add (J.mul (jent J.zero c1 r1 h5i) C) (J.mul (jent (J.neg (J.mul D3 h3i)) c1 r2 h5i) S))
                   (JeR1 sc R0 phi Z0)) by (unfold JeR1; fold x1 x2; apply inR_add; apply inR_mul; assumption).
  assert (E2 : inR (J.add (J.mul (jent (J.mul D3 h3i) c2 r1 h5i) C) (J.mul (jent J.zero c2 r2 h5i) S))
                   (JeR2 sc R0 phi Z0)) by (unfold JeR2; fold x1 x2; apply inR_add; apply inR_mul; assumption).
  assert (E3 : inR (J.add (J.mul (jent (J.neg (J.mul D2 h3i)) c3 r1 h5i) C) (J.mul (jent (J.mul D1 h3i) c3 r2 h5i) S))
                   (JeR3 sc R0 phi Z0)) by (unfold JeR3; fold x1 x2; apply inR_add; apply inR_mul; assumption).
  unfold jfrom, in9, rjet. cbn [g_R g_P g_Z g_RR g_RZ g_PR g_PZ g_ZR g_ZZ].
  unfold fR, fP, fZ, fR_R, fR_Z, fP_R, fP_Z, fZ_R, fZ_Z. fold x1 x2.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - apply inR_add; apply inR_mul; assumption.
  - replace (- bk1 sc x1 x2 Z0 * sin phi) with (- (bk1 sc x1 x2 Z0 * sin phi)) by ring.
    apply inR_add; [apply inR_neg |]; apply inR_mul; assumption.
  - exact B3.
  - apply inR_add; apply inR_mul; assumption.
  - apply inR_add; apply inR_mul; assumption.
  - replace (- JeR1 sc R0 phi Z0 * sin phi) with (- (JeR1 sc R0 phi Z0 * sin phi)) by ring.
    apply inR_add; [apply inR_neg |]; apply inR_mul; assumption.
  - replace (- J13 sc x1 x2 Z0 * sin phi) with (- (J13 sc x1 x2 Z0 * sin phi)) by ring.
    apply inR_add; [apply inR_neg |]; apply inR_mul; assumption.
  - exact E3.
  - exact J33'.
Qed.

(** The positivity the check reads: the enclosure of |r|^2 above zero. *)
Definition iqpos (p : i3) (Rr C S Zz : J.t) : bool :=
  let r := isub3 (icyl Rr C S Zz) p in J.pos (idot3 r r).

Theorem ijet_correct (p d : i3) (sc : src) (Rr C S Zz : J.t) (R0 phi Z0 : R) :
  inR3 p (sp1 sc, sp2 sc, sp3 sc) -> inR3 d (sd1 sc, sd2 sc, sd3 sc) ->
  inR Rr R0 -> inR C (cos phi) -> inR S (sin phi) -> inR Zz Z0 ->
  iqpos p Rr C S Zz = true ->
  in9 (ijet p d Rr C S Zz) (rjet sc R0 phi Z0).
Proof.
  intros Hp Hd HR HC HS HZ Hpos. unfold ijet.
  pose proof (inR3_cyl Rr C S Zz R0 phi Z0 HR HC HS HZ) as Hx.
  pose proof (inR3_sub _ _ _ _ Hx Hp) as Hr. unfold cyl in Hr. simpl in Hr.
  set (r := isub3 (icyl Rr C S Zz) p) in *.
  set (x1 := kx1 R0 phi). set (x2 := kx2 R0 phi).
  assert (Hr' : inR3 r (x1 - sp1 sc, x2 - sp2 sc, Z0 - sp3 sc)) by exact Hr.
  pose proof (inR_dot3 r r _ _ Hr' Hr') as HQ. simpl in HQ.
  set (q := qk sc x1 x2 Z0).
  assert (EQ : (x1 - sp1 sc) * (x1 - sp1 sc) + (x2 - sp2 sc) * (x2 - sp2 sc) + (Z0 - sp3 sc) * (Z0 - sp3 sc) = q)
    by reflexivity.
  rewrite EQ in HQ.
  assert (Hq : 0 < q) by (exact (inR_pos _ _ Hpos HQ)).
  assert (Hs : 0 < sqrt q) by (apply sqrt_lt_R0, Hq).
  pose proof (inR_sqrt _ _ HQ (Rlt_le _ _ Hq)) as HSQ.
  apply jfrom_correct; fold x1 x2.
  - exact Hr'.
  - pose proof (inR3_cross d r _ _ Hd Hr') as Hc. simpl in Hc. unfold ck1, ck2, ck3. exact Hc.
  - exact Hd.
  - unfold kh3, h3. fold q. replace (/ (q * sqrt q)) with (1 / (q * sqrt q)) by (field; split; lra).
    apply inR_div; [apply inR_Z | apply inR_mul; assumption | apply Rgt_not_eq, Rmult_lt_0_compat; lra].
  - unfold kh5, h5. fold q. replace (/ (q * q * sqrt q)) with (1 / (q * q * sqrt q)) by (field; split; lra).
    apply inR_div; [apply inR_Z | apply inR_mul; [apply inR_mul |]; assumption |].
    apply Rgt_not_eq, Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; lra.
  - exact HC.
  - exact HS.
Qed.

(** * Sums over sources, shifts and images *)

Definition j9map2 {A : Type} (f : A -> A -> A) (X Y : j9 A) : j9 A :=
  mk9 (f (g_R X) (g_R Y)) (f (g_P X) (g_P Y)) (f (g_Z X) (g_Z Y)) (f (g_RR X) (g_RR Y)) (f (g_RZ X) (g_RZ Y))
      (f (g_PR X) (g_PR Y)) (f (g_PZ X) (g_PZ Y)) (f (g_ZR X) (g_ZR Y)) (f (g_ZZ X) (g_ZZ Y)).

Definition j9const {A : Type} (a : A) : j9 A := mk9 a a a a a a a a a.

(** A point and its stellarator image, each component with its sign. *)
Definition icomb (X Y : j9 J.t) : j9 J.t :=
  mk9 (J.sub (g_R X) (g_R Y)) (J.add (g_P X) (g_P Y)) (J.add (g_Z X) (g_Z Y)) (J.sub (g_RR X) (g_RR Y))
      (J.add (g_RZ X) (g_RZ Y)) (J.add (g_PR X) (g_PR Y)) (J.sub (g_PZ X) (g_PZ Y)) (J.add (g_ZR X) (g_ZR Y))
      (J.sub (g_ZZ X) (g_ZZ Y)).
Definition rcomb (x y : j9 R) : j9 R :=
  mk9 (g_R x - g_R y) (g_P x + g_P y) (g_Z x + g_Z y) (g_RR x - g_RR y) (g_RZ x + g_RZ y) (g_PR x + g_PR y)
      (g_PZ x - g_PZ y) (g_ZR x + g_ZR y) (g_ZZ x - g_ZZ y).

Lemma icomb_ok (X Y : j9 J.t) (x y : j9 R) : in9 X x -> in9 Y y -> in9 (icomb X Y) (rcomb x y).
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  unfold icomb, rcomb, in9. cbn [g_R g_P g_Z g_RR g_RZ g_PR g_PZ g_ZR g_ZZ].
  repeat split; first [apply inR_sub | apply inR_add]; assumption.
Qed.

Definition jsum (Xs : list (j9 J.t)) : j9 J.t := fold_right (j9map2 J.add) (j9const J.zero) Xs.
Definition rjsum (xs : list (j9 R)) : j9 R := fold_right (j9map2 Rplus) (j9const 0) xs.

Lemma jsum_ok (Xs : list (j9 J.t)) (xs : list (j9 R)) : Forall2 in9 Xs xs -> in9 (jsum Xs) (rjsum xs).
Proof.
  intros H. induction H as [| X x Xs xs Hx _ IH].
  - unfold in9. simpl. repeat split; exact inR_zero.
  - destruct Hx as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    destruct IH as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    unfold in9. cbn [jsum rjsum fold_right j9map2 g_R g_P g_Z g_RR g_RZ g_PR g_PZ g_ZR g_ZZ] in *.
    repeat split; apply inR_add; assumption.
Qed.

(** The jet of the base sources at a point of angle phi (enclosed by (C, S)) and
    at its image, summed. *)
Definition ipoint (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : j9 J.t :=
  jsum (map (fun Sd => icomb (ijet (fst Sd) (snd Sd) Rr C S Zz) (ijet (fst Sd) (snd Sd) Rr C (J.neg S) (J.neg Zz))) Ss).

Definition ppos (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : bool :=
  forallb (fun Sd => iqpos (fst Sd) Rr C S Zz && iqpos (fst Sd) Rr C (J.neg S) (J.neg Zz)) Ss.

(** Summed over the shifts. *)
Definition icomp (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : j9 J.t :=
  jsum (map (fun CS => ipoint Ss Rr Zz (fst CS) (snd CS)) CSk).

Definition cpos (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : bool :=
  forallb (fun CS => ppos Ss Rr Zz (fst CS) (snd CS)) CSk.

Definition src_in (Ss : list (i3 * i3)) (l : list (src * fser)) : Prop :=
  Forall2 (fun Sd sy => inR3 (fst Sd) (sp1 (fst sy), sp2 (fst sy), sp3 (fst sy)) /\
                        inR3 (snd Sd) (sd1 (fst sy), sd2 (fst sy), sd3 (fst sy))) Ss l.

Definition rpoint (l : list (src * fser)) (R0 phi Z0 : R) : j9 R :=
  rjsum (map (fun sy => rcomb (rjet (fst sy) R0 phi Z0) (rjet (fst sy) R0 (- phi) (- Z0))) l).

Lemma ipoint_ok (Ss : list (i3 * i3)) (l : list (src * fser)) (Rr Zz C S : J.t) (R0 Z0 phi : R) :
  src_in Ss l -> inR Rr R0 -> inR Zz Z0 -> inR C (cos phi) -> inR S (sin phi) -> ppos Ss Rr Zz C S = true ->
  in9 (ipoint Ss Rr Zz C S) (rpoint l R0 phi Z0).
Proof.
  intros H HR HZ HC HS Hp. unfold ipoint, rpoint. apply jsum_ok.
  unfold ppos in Hp. induction H as [| Sd sy Ss l [Hs Hd] _ IH]; [constructor |].
  cbn [forallb] in Hp. apply andb_prop in Hp. destruct Hp as [Hp1 Hrest]. apply andb_prop in Hp1.
  destruct Hp1 as [Hq1 Hq2].
  cbn [map]. constructor; [| exact (IH Hrest)].
  apply icomb_ok.
  - apply ijet_correct; assumption.
  - apply ijet_correct; try assumption.
    + rewrite cos_neg. exact HC.
    + rewrite sin_neg. apply inR_neg, HS.
    + apply inR_neg, HZ.
Qed.

Definition rcomp (l : list (src * fser)) (R0 Z0 : R) (phis : list R) : j9 R :=
  rjsum (map (fun ph => rpoint l R0 ph Z0) phis).

Theorem icomp_ok (Ss : list (i3 * i3)) (l : list (src * fser)) (Rr Zz : J.t) (R0 Z0 : R)
    (CSk : list (J.t * J.t)) (phis : list R) :
  src_in Ss l -> inR Rr R0 -> inR Zz Z0 ->
  Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk phis ->
  cpos Ss Rr Zz CSk = true -> in9 (icomp Ss Rr Zz CSk) (rcomp l R0 Z0 phis).
Proof.
  intros H HR HZ HT Hp. unfold icomp, rcomp. apply jsum_ok. unfold cpos in Hp.
  induction HT as [| CS ph CSk phis [HC HS] _ IH]; [constructor |].
  cbn [forallb] in Hp. apply andb_prop in Hp. destruct Hp as [Hp1 Hrest].
  cbn [map]. constructor; [apply ipoint_ok; assumption | exact (IH Hrest)].
Qed.

(** The components of [rcomp] are the sums of [symval] of FieldJetVal.v. *)
Lemma g_rjsum (sel : j9 R -> R) (Hs : forall x y, sel (j9map2 Rplus x y) = sel x + sel y)
    (H0 : sel (j9const 0) = 0) (xs : list (j9 R)) :
  sel (rjsum xs) = rsuml (map sel xs).
Proof. induction xs as [| x xs IH]; [exact H0 |]. cbn [rjsum fold_right map]. rewrite Hs. fold (rjsum xs). rewrite IH. reflexivity. Qed.

Lemma lsum_rsuml {A : Type} (f : A -> R) (l : list A) : lsum f l = rsuml (map f l).
Proof. reflexivity. Qed.

(** * The field alone *)

(** The three cylindrical components of one source, without the Jacobian. *)
Definition ijetv (p d : i3) (Rr C S Zz : J.t) : J.t * J.t * J.t :=
  let r := isub3 (icyl Rr C S Zz) p in
  let q := idot3 r r in
  let h3 := kh3 q in
  let '(c1, c2, c3) := icross3 d r in
  let b1 := J.mul c1 h3 in let b2 := J.mul c2 h3 in
  (J.add (J.mul b1 C) (J.mul b2 S), J.add (J.neg (J.mul b1 S)) (J.mul b2 C), J.mul c3 h3).

Lemma ijetv_eq (p d : i3) (Rr C S Zz : J.t) :
  ijetv p d Rr C S Zz = (g_R (ijet p d Rr C S Zz), g_P (ijet p d Rr C S Zz), g_Z (ijet p d Rr C S Zz)).
Proof.
  unfold ijetv, ijet, jfrom. destruct (isub3 (icyl Rr C S Zz) p) as [[r1 r2] r3].
  destruct d as [[D1 D2] D3]. cbn [icross3]. reflexivity.
Qed.

Definition v3j (X : J.t * J.t * J.t) : j9 J.t :=
  let '(a, b, c) := X in mk9 a b c J.zero J.zero J.zero J.zero J.zero J.zero.

Definition icombv (X Y : J.t * J.t * J.t) : J.t * J.t * J.t :=
  let '(a1, a2, a3) := X in let '(b1, b2, b3) := Y in (J.sub a1 b1, J.add a2 b2, J.add a3 b3).

Definition v3add' (X Y : J.t * J.t * J.t) : J.t * J.t * J.t :=
  let '(a1, a2, a3) := X in let '(b1, b2, b3) := Y in (J.add a1 b1, J.add a2 b2, J.add a3 b3).

Definition vsum (Xs : list (J.t * J.t * J.t)) : J.t * J.t * J.t := fold_right v3add' (J.zero, J.zero, J.zero) Xs.

Definition ipointv (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : J.t * J.t * J.t :=
  vsum (map (fun Sd => icombv (ijetv (fst Sd) (snd Sd) Rr C S Zz) (ijetv (fst Sd) (snd Sd) Rr C (J.neg S) (J.neg Zz))) Ss).

Definition icompv (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : J.t * J.t * J.t :=
  vsum (map (fun CS => ipointv Ss Rr Zz (fst CS) (snd CS)) CSk).

Definition in3 (X : J.t * J.t * J.t) (x : j9 R) : Prop :=
  let '(a, b, c) := X in inR a (g_R x) /\ inR b (g_P x) /\ inR c (g_Z x).

Lemma vsum_ok (Xs : list (J.t * J.t * J.t)) (xs : list (j9 R)) : Forall2 in3 Xs xs -> in3 (vsum Xs) (rjsum xs).
Proof.
  intros H. induction H as [| X x Xs xs Hx _ IH].
  - simpl. repeat split; exact inR_zero.
  - destruct X as [[a b] c]. destruct (vsum Xs) as [[A B] C] eqn:E.
    cbn [vsum fold_right]. fold (vsum Xs). rewrite E. cbn [v3add' rjsum fold_right j9map2 g_R g_P g_Z] in *.
    destruct Hx as [H1 [H2 H3]]. destruct IH as [I1 [I2 I3]].
    repeat split; apply inR_add; assumption.
Qed.

Lemma in3_of_in9 (p d : i3) (Rr C S Zz : J.t) (x : j9 R) :
  in9 (ijet p d Rr C S Zz) x -> in3 (ijetv p d Rr C S Zz) x.
Proof. intros (H1 & H2 & H3 & _). rewrite ijetv_eq. cbn. auto. Qed.

Lemma icombv_ok (X Y : J.t * J.t * J.t) (x y : j9 R) : in3 X x -> in3 Y y -> in3 (icombv X Y) (rcomb x y).
Proof.
  destruct X as [[a1 a2] a3], Y as [[b1 b2] b3]. intros [H1 [H2 H3]] [G1 [G2 G3]].
  cbn [icombv in3 rcomb g_R g_P g_Z]. repeat split; first [apply inR_sub | apply inR_add]; assumption.
Qed.

Theorem icompv_ok (Ss : list (i3 * i3)) (l : list (src * fser)) (Rr Zz : J.t) (R0 Z0 : R)
    (CSk : list (J.t * J.t)) (phis : list R) :
  src_in Ss l -> inR Rr R0 -> inR Zz Z0 ->
  Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk phis ->
  cpos Ss Rr Zz CSk = true -> in3 (icompv Ss Rr Zz CSk) (rcomp l R0 Z0 phis).
Proof.
  intros H HR HZ HT Hp. unfold icompv, rcomp. apply vsum_ok. unfold cpos in Hp.
  induction HT as [| CS ph CSk phis [HC HS] _ IH]; [constructor |].
  cbn [forallb] in Hp. apply andb_prop in Hp. destruct Hp as [Hp1 Hrest].
  cbn [map]. constructor; [| exact (IH Hrest)].
  unfold ipointv, rpoint. apply vsum_ok. unfold ppos in Hp1.
  clear IH Hrest. induction H as [| Sd sy Ss l [Hs Hd] _ IHs]; [constructor |].
  cbn [forallb] in Hp1. apply andb_prop in Hp1. destruct Hp1 as [Hq Hrest]. apply andb_prop in Hq.
  destruct Hq as [Hq1 Hq2].
  cbn [map]. constructor; [| exact (IHs Hrest)].
  apply icombv_ok; apply in3_of_in9; apply ijet_correct; try assumption.
  - rewrite cos_neg. exact HC.
  - rewrite sin_neg. apply inR_neg, HS.
  - apply inR_neg, HZ.
Qed.

(** * Positivity and field in one pass

    The check of positivity and the field read the same offset and squared
    distance; [icompvp] forms both from one of each and is the pair
    ([icompvp_eq]). *)
Definition ijetvp (p d : i3) (Rr C S Zz : J.t) : bool * (J.t * J.t * J.t) :=
  let r := isub3 (icyl Rr C S Zz) p in
  let q := idot3 r r in
  let h3 := kh3 q in
  let '(c1, c2, c3) := icross3 d r in
  let b1 := J.mul c1 h3 in let b2 := J.mul c2 h3 in
  (J.pos q, (J.add (J.mul b1 C) (J.mul b2 S), J.add (J.neg (J.mul b1 S)) (J.mul b2 C), J.mul c3 h3)).

Lemma ijetvp_eq (p d : i3) (Rr C S Zz : J.t) : ijetvp p d Rr C S Zz = (iqpos p Rr C S Zz, ijetv p d Rr C S Zz).
Proof.
  unfold ijetvp, iqpos, ijetv. cbv zeta. destruct (icross3 d (isub3 (icyl Rr C S Zz) p)) as [[c1 c2] c3].
  reflexivity.
Qed.

Definition vsump (Xs : list (bool * (J.t * J.t * J.t))) : bool * (J.t * J.t * J.t) :=
  fold_right (fun X acc => (fst X && fst acc, v3add' (snd X) (snd acc))) (true, (J.zero, J.zero, J.zero)) Xs.

Lemma vsump_map {A : Type} (f : A -> bool) (g : A -> J.t * J.t * J.t) (l : list A) :
  vsump (map (fun x => (f x, g x)) l) = (forallb f l, vsum (map g l)).
Proof.
  induction l as [| x l IH]; [reflexivity |].
  change (vsump (map (fun x => (f x, g x)) (x :: l)))
    with ((f x && fst (vsump (map (fun x => (f x, g x)) l)), v3add' (g x) (snd (vsump (map (fun x => (f x, g x)) l))))).
  rewrite IH. reflexivity.
Qed.

Definition ipointvp (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : bool * (J.t * J.t * J.t) :=
  vsump (map (fun Sd => let X := ijetvp (fst Sd) (snd Sd) Rr C S Zz in
                        let Y := ijetvp (fst Sd) (snd Sd) Rr C (J.neg S) (J.neg Zz) in
                        (fst X && fst Y, icombv (snd X) (snd Y))) Ss).

Lemma ipointvp_eq (Ss : list (i3 * i3)) (Rr Zz C S : J.t) :
  ipointvp Ss Rr Zz C S = (ppos Ss Rr Zz C S, ipointv Ss Rr Zz C S).
Proof.
  unfold ipointvp, ppos, ipointv. rewrite <- vsump_map. f_equal. apply map_ext. intros Sd.
  rewrite !ijetvp_eq. reflexivity.
Qed.

Definition icompvp (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : bool * (J.t * J.t * J.t) :=
  vsump (map (fun CS => ipointvp Ss Rr Zz (fst CS) (snd CS)) CSk).

Lemma icompvp_eq (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) :
  icompvp Ss Rr Zz CSk = (cpos Ss Rr Zz CSk, icompv Ss Rr Zz CSk).
Proof.
  unfold icompvp, cpos, icompv. rewrite <- vsump_map. f_equal. apply map_ext. intros CS. apply ipointvp_eq.
Qed.

(** The whole jet with the positivity, from one offset and one squared distance. *)
Definition ijetp (p d : i3) (Rr C S Zz : J.t) : bool * j9 J.t :=
  let r := isub3 (icyl Rr C S Zz) p in
  let q := idot3 r r in
  (J.pos q, jfrom r (icross3 d r) d (kh3 q) (kh5 q) C S).

Lemma ijetp_eq (p d : i3) (Rr C S Zz : J.t) : ijetp p d Rr C S Zz = (iqpos p Rr C S Zz, ijet p d Rr C S Zz).
Proof. reflexivity. Qed.

Definition jsump (Xs : list (bool * j9 J.t)) : bool * j9 J.t :=
  fold_right (fun X acc => (fst X && fst acc, j9map2 J.add (snd X) (snd acc))) (true, j9const J.zero) Xs.

Lemma jsump_map {A : Type} (f : A -> bool) (g : A -> j9 J.t) (l : list A) :
  jsump (map (fun x => (f x, g x)) l) = (forallb f l, jsum (map g l)).
Proof.
  induction l as [| x l IH]; [reflexivity |].
  change (jsump (map (fun x => (f x, g x)) (x :: l)))
    with ((f x && fst (jsump (map (fun x => (f x, g x)) l)), j9map2 J.add (g x) (snd (jsump (map (fun x => (f x, g x)) l))))).
  rewrite IH. reflexivity.
Qed.

Definition ipointp (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : bool * j9 J.t :=
  jsump (map (fun Sd => let X := ijetp (fst Sd) (snd Sd) Rr C S Zz in
                        let Y := ijetp (fst Sd) (snd Sd) Rr C (J.neg S) (J.neg Zz) in
                        (fst X && fst Y, icomb (snd X) (snd Y))) Ss).

Lemma ipointp_eq (Ss : list (i3 * i3)) (Rr Zz C S : J.t) :
  ipointp Ss Rr Zz C S = (ppos Ss Rr Zz C S, ipoint Ss Rr Zz C S).
Proof.
  unfold ipointp, ppos, ipoint. rewrite <- jsump_map. reflexivity.
Qed.

Definition icompp (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : bool * j9 J.t :=
  jsump (map (fun CS => ipointp Ss Rr Zz (fst CS) (snd CS)) CSk).

Lemma icompp_eq (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) :
  icompp Ss Rr Zz CSk = (cpos Ss Rr Zz CSk, icomp Ss Rr Zz CSk).
Proof.
  unfold icompp, cpos, icomp. rewrite <- jsump_map. f_equal. apply map_ext. intros CS. apply ipointp_eq.
Qed.

(** Each component of the enclosure at the P shifts of p encloses the value of
    that component of the total jet ([comp_val]). *)
Section Link.

Variables (P : Z) (K : vf) (l : list (src * fser)) (t p : R).
Hypothesis HP : (0 < P)%Z.

Let phis : list R := map (fun k => p + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P)).

Lemma comp_link (sel : j9 R -> R) (f : src -> R -> R -> R -> R) (sg : bool)
    (Hs : forall x y, sel (j9map2 Rplus x y) = sel x + sel y) (H0 : sel (j9const 0) = 0)
    (Hc : forall sc R0 phi Z0, sel (rcomb (rjet sc R0 phi Z0) (rjet sc R0 (- phi) (- Z0))) = symval f sg sc R0 phi Z0) :
  sel (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l f sg t p.
Proof.
  unfold rcomp, comp_val, phis. rewrite (g_rjsum sel Hs H0), !map_map, rsuml_map_seq.
  apply fsum_ext. intros k. cbn [plus]. unfold rpoint. rewrite (g_rjsum sel Hs H0), map_map.
  rewrite lsum_rsuml. f_equal. apply map_ext. intros sy. apply Hc.
Qed.

Ltac clink := apply comp_link; [intros x y; reflexivity | reflexivity | intros sc R0 phi Z0; reflexivity].

Lemma link_R : g_R (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fR true t p.
Proof. clink. Qed.
Lemma link_P : g_P (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fP false t p.
Proof. clink. Qed.
Lemma link_Z : g_Z (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fZ false t p.
Proof. clink. Qed.
Lemma link_RR : g_RR (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fR_R true t p.
Proof. clink. Qed.
Lemma link_RZ : g_RZ (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fR_Z false t p.
Proof. clink. Qed.
Lemma link_PR : g_PR (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fP_R false t p.
Proof. clink. Qed.
Lemma link_PZ : g_PZ (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fP_Z true t p.
Proof. clink. Qed.
Lemma link_ZR : g_ZR (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fZ_R false t p.
Proof. clink. Qed.
Lemma link_ZZ : g_ZZ (rcomp l (feval (vR K) t p) (feval (vZ K) t p) phis) = comp_val P K l fZ_Z true t p.
Proof. clink. Qed.

End Link.

End JetOps.
