(** Interval enclosures of the coil field, its R and Z derivatives and its
    phi derivatives, over boxes.

    [ijet12] encloses, for one source at (R, phi, Z), the nine functions of
    KJet.rjet and the three explicit phi derivatives fR_phi, fP_phi, fZ_phi of
    FieldKern.v ([ijet12_correct]). The squared distance is summed from the
    squares of the absolute values of the offsets, so that its enclosure stays
    above zero over a box that straddles a coordinate of the source. [icomp12]
    sums over the sources, their stellarator images and the shifts of the angle
    ([icomp12_ok]), and at the shifts of phi its components are the coil
    field and FieldPath.v's total partial derivatives ([rcomp12_val]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Stellarocq Require Import KAMScalar Fourier Hypotheses Invariance CoilSym FieldKern FieldModel FieldPath
  KFix KCheckKern KJet.
Import ListNotations.
Local Open Scope R_scope.

Record r12 := mkr12 { r9 : j9 R ; rRP : R ; rPP : R ; rZP : R }.

Definition rjet12 (sc : src) (R0 phi Z0 : R) : r12 :=
  mkr12 (rjet sc R0 phi Z0) (fR_phi sc R0 phi Z0) (fP_phi sc R0 phi Z0) (fZ_phi sc R0 phi Z0).

Definition rcomb12 (x y : r12) : r12 :=
  mkr12 (mk9 (g_R (r9 x) - g_R (r9 y)) (g_P (r9 x) + g_P (r9 y)) (g_Z (r9 x) + g_Z (r9 y))
             (g_RR (r9 x) - g_RR (r9 y)) (g_RZ (r9 x) + g_RZ (r9 y)) (g_PR (r9 x) + g_PR (r9 y))
             (g_PZ (r9 x) - g_PZ (r9 y)) (g_ZR (r9 x) + g_ZR (r9 y)) (g_ZZ (r9 x) - g_ZZ (r9 y)))
        (rRP x + rRP y) (rPP x - rPP y) (rZP x - rZP y).

Definition radd12 (x y : r12) : r12 :=
  mkr12 (mk9 (g_R (r9 x) + g_R (r9 y)) (g_P (r9 x) + g_P (r9 y)) (g_Z (r9 x) + g_Z (r9 y))
             (g_RR (r9 x) + g_RR (r9 y)) (g_RZ (r9 x) + g_RZ (r9 y)) (g_PR (r9 x) + g_PR (r9 y))
             (g_PZ (r9 x) + g_PZ (r9 y)) (g_ZR (r9 x) + g_ZR (r9 y)) (g_ZZ (r9 x) + g_ZZ (r9 y)))
        (rRP x + rRP y) (rPP x + rPP y) (rZP x + rZP y).

Definition rzero12 : r12 := mkr12 (mk9 0 0 0 0 0 0 0 0 0) 0 0 0.

Definition rsum12 (xs : list r12) : r12 := fold_right radd12 rzero12 xs.

Definition rpoint12 (l : list (src * fser)) (R0 ph Z0 : R) : r12 :=
  rsum12 (map (fun sy => rcomb12 (rjet12 (fst sy) R0 ph Z0) (rjet12 (fst sy) R0 (- ph) (- Z0))) l).

Definition rcomp12 (l : list (src * fser)) (R0 Z0 : R) (phis : list R) : r12 :=
  rsum12 (map (fun ph => rpoint12 l R0 ph Z0) phis).

(** Every selector of a sum is the sum of the selected components. *)
Lemma rsum12_sel (sel : r12 -> R) (Hs : forall x y, sel (radd12 x y) = sel x + sel y) (H0 : sel rzero12 = 0)
    (xs : list r12) : sel (rsum12 xs) = fold_right Rplus 0 (map sel xs).
Proof. induction xs as [| x xs IH]; [exact H0 |]. cbn [rsum12 fold_right map]. rewrite Hs. fold (rsum12 xs). rewrite IH. reflexivity. Qed.

Section Val.

Variables (P : nat) (l : list (src * fser)).

Ltac sel_tac := intros; reflexivity.

Lemma rcomp12_sel (sel : r12 -> R) (Hs : forall x y, sel (radd12 x y) = sel x + sel y) (H0 : sel rzero12 = 0)
    (g : src -> R -> R) (R0 phi Z0 : R) :
  (forall sc ph, sel (rcomb12 (rjet12 sc R0 ph Z0) (rjet12 sc R0 (- ph) (- Z0))) = g sc ph) ->
  sel (rcomp12 l R0 Z0 (shiftsP P phi)) = ssum P l g phi.
Proof.
  intros Hg. unfold rcomp12, ssum. rewrite (rsum12_sel sel Hs H0), map_map. f_equal. apply map_ext. intros ph.
  unfold rpoint12. rewrite (rsum12_sel sel Hs H0), map_map. f_equal. apply map_ext. intros sy. apply Hg.
Qed.

(** At the shifts of phi the components are the coil field and its total
    partial derivatives. *)
Theorem rcomp12_val (R0 phi Z0 : R) :
  let x := rcomp12 l R0 Z0 (shiftsP P phi) in
  g_R (r9 x) = B_R (coilB (Z.of_nat P) l) R0 phi Z0 /\
  g_P (r9 x) = B_phi (coilB (Z.of_nat P) l) R0 phi Z0 /\
  g_Z (r9 x) = B_Z (coilB (Z.of_nat P) l) R0 phi Z0 /\
  g_RR (r9 x) = BR_R P l R0 phi Z0 /\ g_RZ (r9 x) = BR_Z P l R0 phi Z0 /\ rRP x = BR_P P l R0 phi Z0 /\
  g_PR (r9 x) = BP_R P l R0 phi Z0 /\ g_PZ (r9 x) = BP_Z P l R0 phi Z0 /\ rPP x = BP_P P l R0 phi Z0 /\
  g_ZR (r9 x) = BZ_R P l R0 phi Z0 /\ g_ZZ (r9 x) = BZ_Z P l R0 phi Z0 /\ rZP x = BZ_P P l R0 phi Z0.
Proof.
  cbv zeta. destruct (coil_sum P l R0 phi Z0) as [C1 [C2 C3]].
  rewrite C1, C2, C3.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - apply (rcomp12_sel (fun x => g_R (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_P (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_Z (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_RR (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_RZ (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel rRP); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_PR (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_PZ (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel rPP); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_ZR (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel (fun x => g_ZZ (r9 x))); intros; reflexivity.
  - apply (rcomp12_sel rZP); intros; reflexivity.
Qed.

End Val.

Module Jet12 (J : RI).

Module JO := JetOps J.
Import JO JO.KO.

Record j12 := mk12 { q9 : j9 J.t ; qRP : J.t ; qPP : J.t ; qZP : J.t }.

Definition in12 (X : j12) (x : r12) : Prop :=
  in9 (q9 X) (r9 x) /\ inR (qRP X) (rRP x) /\ inR (qPP X) (rPP x) /\ inR (qZP X) (rZP x).

(** The squared distance from the squares of the absolute offsets. *)
Definition isq (X : J.t) : J.t := J.mul (J.abs X) (J.abs X).
Definition iq (r : i3) : J.t := let '(r1, r2, r3) := r in J.add (J.add (isq r1) (isq r2)) (isq r3).

Lemma isq_ok (X : J.t) (x : R) : inR X x -> inR (isq X) (x * x).
Proof.
  intros H. unfold isq. replace (x * x) with (Rabs x * Rabs x).
  - apply inR_mul; apply inR_abs, H.
  - rewrite <- Rabs_mult. apply Rabs_pos_eq, Rle_0_sqr.
Qed.

Lemma iq_ok (r : i3) (a b c : R) : inR3 r (a, b, c) -> inR (iq r) (a * a + b * b + c * c).
Proof. destruct r as [[r1 r2] r3]. intros [H1 [H2 H3]]. unfold iq. apply inR_add; [apply inR_add |]; apply isq_ok; assumption. Qed.

Definition jfrom12 (r c d : i3) (h3 h5 Rr C S : J.t) : j12 :=
  let v := jfrom r c d h3 h5 C S in
  let '(r1, r2, r3) := r in let '(c1, c2, c3) := c in let '(D1, D2, D3) := d in
  let j11 := jent J.zero c1 r1 h5 in
  let j12' := jent (J.neg (J.mul D3 h3)) c1 r2 h5 in
  let j21 := jent (J.mul D3 h3) c2 r1 h5 in
  let j22 := jent J.zero c2 r2 h5 in
  let j31 := jent (J.neg (J.mul D2 h3)) c3 r1 h5 in
  let j32 := jent (J.mul D1 h3) c3 r2 h5 in
  let jeP1 := J.add (J.neg (J.mul j11 S)) (J.mul j12' C) in
  let jeP2 := J.add (J.neg (J.mul j21 S)) (J.mul j22 C) in
  let jeP3 := J.add (J.neg (J.mul j31 S)) (J.mul j32 C) in
  mk12 v (J.add (J.mul Rr (J.add (J.mul jeP1 C) (J.mul jeP2 S))) (g_P v))
         (J.sub (J.mul Rr (J.add (J.neg (J.mul jeP1 S)) (J.mul jeP2 C))) (g_R v))
         (J.mul Rr jeP3).

Theorem jfrom12_correct (sc : src) (R0 phi Z0 : R) (r c d : i3) (h3i h5i Rr C S : J.t) :
  inR3 r (kx1 R0 phi - sp1 sc, kx2 R0 phi - sp2 sc, Z0 - sp3 sc) ->
  inR3 c (ck1 sc (kx1 R0 phi) (kx2 R0 phi) Z0, ck2 sc (kx1 R0 phi) (kx2 R0 phi) Z0,
          ck3 sc (kx1 R0 phi) (kx2 R0 phi) Z0) ->
  inR3 d (sd1 sc, sd2 sc, sd3 sc) ->
  inR h3i (h3 sc (kx1 R0 phi) (kx2 R0 phi) Z0) -> inR h5i (h5 sc (kx1 R0 phi) (kx2 R0 phi) Z0) ->
  inR Rr R0 -> inR C (cos phi) -> inR S (sin phi) ->
  in12 (jfrom12 r c d h3i h5i Rr C S) (rjet12 sc R0 phi Z0).
Proof.
  intros Hr Hc Hd H3 H5 HR HC HS.
  pose proof (jfrom_correct sc R0 phi Z0 r c d h3i h5i C S Hr Hc Hd H3 H5 HC HS) as V.
  destruct r as [[r1 r2] r3], c as [[c1 c2] c3], d as [[D1 D2] D3].
  destruct Hr as [R1 [R2 R3]], Hc as [C1 [C2 C3]], Hd as [HD1 [HD2 HD3]].
  set (x1 := kx1 R0 phi) in *. set (x2 := kx2 R0 phi) in *.
  assert (J11' : inR (jent J.zero c1 r1 h5i) (J11 sc x1 x2 Z0)).
  { unfold J11. replace (- 3 * ck1 sc x1 x2 Z0 * (x1 - sp1 sc) * h5 sc x1 x2 Z0)
      with (0 - 3 * ck1 sc x1 x2 Z0 * (x1 - sp1 sc) * h5 sc x1 x2 Z0) by ring.
    apply jent_ok; [exact inR_zero | assumption | assumption | assumption]. }
  assert (J12' : inR (jent (J.neg (J.mul D3 h3i)) c1 r2 h5i) (J12 sc x1 x2 Z0)).
  { unfold J12. replace (- sd3 sc * h3 sc x1 x2 Z0) with (- (sd3 sc * h3 sc x1 x2 Z0)) by ring.
    apply jent_ok; [apply inR_neg, inR_mul | | |]; assumption. }
  assert (J21' : inR (jent (J.mul D3 h3i) c2 r1 h5i) (J21 sc x1 x2 Z0)).
  { unfold J21. apply jent_ok; [apply inR_mul | | |]; assumption. }
  assert (J22' : inR (jent J.zero c2 r2 h5i) (J22 sc x1 x2 Z0)).
  { unfold J22. replace (- 3 * ck2 sc x1 x2 Z0 * (x2 - sp2 sc) * h5 sc x1 x2 Z0)
      with (0 - 3 * ck2 sc x1 x2 Z0 * (x2 - sp2 sc) * h5 sc x1 x2 Z0) by ring.
    apply jent_ok; [exact inR_zero | assumption | assumption | assumption]. }
  assert (J31' : inR (jent (J.neg (J.mul D2 h3i)) c3 r1 h5i) (J31 sc x1 x2 Z0)).
  { unfold J31. replace (- sd2 sc * h3 sc x1 x2 Z0) with (- (sd2 sc * h3 sc x1 x2 Z0)) by ring.
    apply jent_ok; [apply inR_neg, inR_mul | | |]; assumption. }
  assert (J32' : inR (jent (J.mul D1 h3i) c3 r2 h5i) (J32 sc x1 x2 Z0)).
  { unfold J32. apply jent_ok; [apply inR_mul | | |]; assumption. }
  assert (E1 : inR (J.add (J.neg (J.mul (jent J.zero c1 r1 h5i) S)) (J.mul (jent (J.neg (J.mul D3 h3i)) c1 r2 h5i) C))
                   (JeP1 sc R0 phi Z0)).
  { unfold JeP1. fold x1 x2. replace (- J11 sc x1 x2 Z0 * sin phi) with (- (J11 sc x1 x2 Z0 * sin phi)) by ring.
    apply inR_add; [apply inR_neg |]; apply inR_mul; assumption. }
  assert (E2 : inR (J.add (J.neg (J.mul (jent (J.mul D3 h3i) c2 r1 h5i) S)) (J.mul (jent J.zero c2 r2 h5i) C))
                   (JeP2 sc R0 phi Z0)).
  { unfold JeP2. fold x1 x2. replace (- J21 sc x1 x2 Z0 * sin phi) with (- (J21 sc x1 x2 Z0 * sin phi)) by ring.
    apply inR_add; [apply inR_neg |]; apply inR_mul; assumption. }
  assert (E3 : inR (J.add (J.neg (J.mul (jent (J.neg (J.mul D2 h3i)) c3 r1 h5i) S)) (J.mul (jent (J.mul D1 h3i) c3 r2 h5i) C))
                   (JeP3 sc R0 phi Z0)).
  { unfold JeP3. fold x1 x2. replace (- J31 sc x1 x2 Z0 * sin phi) with (- (J31 sc x1 x2 Z0 * sin phi)) by ring.
    apply inR_add; [apply inR_neg |]; apply inR_mul; assumption. }
  destruct V as [V1 [V2 _]].
  unfold jfrom12, in12, rjet12. cbn [q9 qRP qPP qZP r9 rRP rPP rZP].
  refine (conj _ (conj _ (conj _ _))).
  - apply jfrom_correct; try assumption; repeat split; assumption.
  - unfold fR_phi. apply inR_add; [apply inR_mul; [exact HR |] |].
    + apply inR_add; apply inR_mul; assumption.
    + exact V2.
  - unfold fP_phi. apply inR_sub; [apply inR_mul; [exact HR |] |].
    + replace (- JeP1 sc R0 phi Z0 * sin phi) with (- (JeP1 sc R0 phi Z0 * sin phi)) by ring.
      apply inR_add; [apply inR_neg |]; apply inR_mul; assumption.
    + exact V1.
  - unfold fZ_phi. apply inR_mul; assumption.
Qed.

(** The positivity the check reads: the squared distance above zero. *)
Definition iqpos12 (p : i3) (Rr C S Zz : J.t) : bool := J.pos (iq (isub3 (icyl Rr C S Zz) p)).

Definition ijet12 (p d : i3) (Rr C S Zz : J.t) : j12 :=
  let r := isub3 (icyl Rr C S Zz) p in
  let q := iq r in
  jfrom12 r (icross3 d r) d (kh3 q) (kh5 q) Rr C S.

Theorem ijet12_correct (p d : i3) (sc : src) (Rr C S Zz : J.t) (R0 phi Z0 : R) :
  inR3 p (sp1 sc, sp2 sc, sp3 sc) -> inR3 d (sd1 sc, sd2 sc, sd3 sc) ->
  inR Rr R0 -> inR C (cos phi) -> inR S (sin phi) -> inR Zz Z0 ->
  iqpos12 p Rr C S Zz = true ->
  in12 (ijet12 p d Rr C S Zz) (rjet12 sc R0 phi Z0) /\ 0 < qk sc (kx1 R0 phi) (kx2 R0 phi) Z0.
Proof.
  intros Hp Hd HR HC HS HZ Hpos. unfold ijet12, iqpos12 in *.
  pose proof (inR3_cyl Rr C S Zz R0 phi Z0 HR HC HS HZ) as Hx.
  pose proof (inR3_sub _ _ _ _ Hx Hp) as Hr. unfold cyl in Hr. simpl in Hr.
  set (r := isub3 (icyl Rr C S Zz) p) in *.
  set (x1 := kx1 R0 phi). set (x2 := kx2 R0 phi).
  assert (Hr' : inR3 r (x1 - sp1 sc, x2 - sp2 sc, Z0 - sp3 sc)) by exact Hr.
  pose proof (iq_ok r _ _ _ Hr') as HQ.
  set (q := qk sc x1 x2 Z0).
  assert (EQ : (x1 - sp1 sc) * (x1 - sp1 sc) + (x2 - sp2 sc) * (x2 - sp2 sc) + (Z0 - sp3 sc) * (Z0 - sp3 sc) = q)
    by reflexivity.
  rewrite EQ in HQ.
  assert (Hq : 0 < q) by (exact (inR_pos _ _ Hpos HQ)).
  assert (Hs : 0 < sqrt q) by (apply sqrt_lt_R0, Hq).
  pose proof (inR_sqrt _ _ HQ (Rlt_le _ _ Hq)) as HSQ.
  split; [| exact Hq].
  apply jfrom12_correct; fold x1 x2.
  - exact Hr'.
  - pose proof (inR3_cross d r _ _ Hd Hr') as Hc. simpl in Hc. unfold ck1, ck2, ck3. exact Hc.
  - exact Hd.
  - unfold kh3, h3. fold q. replace (/ (q * sqrt q)) with (1 / (q * sqrt q)) by (field; split; lra).
    apply inR_div; [apply inR_Z | apply inR_mul; assumption | apply Rgt_not_eq, Rmult_lt_0_compat; lra].
  - unfold kh5, h5. fold q. replace (/ (q * q * sqrt q)) with (1 / (q * q * sqrt q)) by (field; split; lra).
    apply inR_div; [apply inR_Z | apply inR_mul; [apply inR_mul |]; assumption |].
    apply Rgt_not_eq, Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; lra.
  - exact HR.
  - exact HC.
  - exact HS.
Qed.

(** * Images, sources and shifts *)

Definition icomb12 (X Y : j12) : j12 :=
  mk12 (icomb (q9 X) (q9 Y)) (J.add (qRP X) (qRP Y)) (J.sub (qPP X) (qPP Y)) (J.sub (qZP X) (qZP Y)).

Lemma icomb12_ok (X Y : j12) (x y : r12) : in12 X x -> in12 Y y -> in12 (icomb12 X Y) (rcomb12 x y).
Proof.
  intros [A1 [A2 [A3 A4]]] [B1 [B2 [B3 B4]]]. unfold icomb12, in12, rcomb12. cbn [q9 qRP qPP qZP r9 rRP rPP rZP].
  refine (conj _ (conj _ (conj _ _))).
  - exact (icomb_ok _ _ _ _ A1 B1).
  - apply inR_add; assumption.
  - apply inR_sub; assumption.
  - apply inR_sub; assumption.
Qed.

Definition iadd12 (X Y : j12) : j12 :=
  mk12 (j9map2 J.add (q9 X) (q9 Y)) (J.add (qRP X) (qRP Y)) (J.add (qPP X) (qPP Y)) (J.add (qZP X) (qZP Y)).
Definition izero12 : j12 := mk12 (j9const J.zero) J.zero J.zero J.zero.
Definition isum12 (Xs : list j12) : j12 := fold_right iadd12 izero12 Xs.

Lemma isum12_ok (Xs : list j12) (xs : list r12) : Forall2 in12 Xs xs -> in12 (isum12 Xs) (rsum12 xs).
Proof.
  intros H. induction H as [| X x Xs xs Hx _ IH].
  - unfold in12. simpl. repeat split; exact inR_zero.
  - destruct Hx as [[A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 A9]]]]]]]] [A10 [A11 A12]]].
    destruct IH as [[B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 B9]]]]]]]] [B10 [B11 B12]]].
    unfold in12, in9. cbn [isum12 rsum12 fold_right iadd12 radd12 q9 r9 qRP qPP qZP rRP rPP rZP j9map2
                           g_R g_P g_Z g_RR g_RZ g_PR g_PZ g_ZR g_ZZ] in *.
    repeat split; apply inR_add; assumption.
Qed.

Definition ipoint12 (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : j12 :=
  isum12 (map (fun Sd => icomb12 (ijet12 (fst Sd) (snd Sd) Rr C S Zz)
                                 (ijet12 (fst Sd) (snd Sd) Rr C (J.neg S) (J.neg Zz))) Ss).

Definition ppos12 (Ss : list (i3 * i3)) (Rr Zz C S : J.t) : bool :=
  forallb (fun Sd => iqpos12 (fst Sd) Rr C S Zz && iqpos12 (fst Sd) Rr C (J.neg S) (J.neg Zz)) Ss.

Definition icomp12 (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : j12 :=
  isum12 (map (fun CS => ipoint12 Ss Rr Zz (fst CS) (snd CS)) CSk).

Definition cpos12 (Ss : list (i3 * i3)) (Rr Zz : J.t) (CSk : list (J.t * J.t)) : bool :=
  forallb (fun CS => ppos12 Ss Rr Zz (fst CS) (snd CS)) CSk.

(** One shift: the sources and their images, and their distances. *)
Lemma ipoint12_ok (Ss : list (i3 * i3)) (l : list (src * fser)) (Rr Zz C S : J.t) (R0 Z0 ph : R) :
  src_in Ss l -> inR Rr R0 -> inR Zz Z0 -> inR C (cos ph) -> inR S (sin ph) -> ppos12 Ss Rr Zz C S = true ->
  Forall2 in12 (map (fun Sd => icomb12 (ijet12 (fst Sd) (snd Sd) Rr C S Zz)
                                      (ijet12 (fst Sd) (snd Sd) Rr C (J.neg S) (J.neg Zz))) Ss)
               (map (fun sy => rcomb12 (rjet12 (fst sy) R0 ph Z0) (rjet12 (fst sy) R0 (- ph) (- Z0))) l) /\
  Forall (fun sy => 0 < qk (fst sy) (kx1 R0 ph) (kx2 R0 ph) Z0 /\
                    0 < qk (fst sy) (kx1 R0 (- ph)) (kx2 R0 (- ph)) (- Z0)) l.
Proof.
  intros H HR HZ HC HS Hp. unfold ppos12 in Hp.
  induction H as [| Sd sy Ss l [Hs Hd] _ IH]; [split; constructor |].
  cbn [forallb] in Hp. apply andb_prop in Hp. destruct Hp as [Hq Hrest]. apply andb_prop in Hq.
  destruct Hq as [Hq1 Hq2]. destruct (IH Hrest) as [K1 K2].
  destruct (ijet12_correct (fst Sd) (snd Sd) (fst sy) Rr C S Zz R0 ph Z0 Hs Hd HR HC HS HZ Hq1) as [T1 Q1].
  destruct (ijet12_correct (fst Sd) (snd Sd) (fst sy) Rr C (J.neg S) (J.neg Zz) R0 (- ph) (- Z0)
              Hs Hd HR ltac:(rewrite cos_neg; exact HC) ltac:(rewrite sin_neg; apply inR_neg, HS)
              (inR_neg _ _ HZ) Hq2) as [T2 Q2].
  cbn [map]. split.
  - constructor; [apply icomb12_ok; assumption | exact K1].
  - constructor; [split; assumption | exact K2].
Qed.

Definition apart_l (l : list (src * fser)) (R0 Z0 : R) (phis : list R) : Prop :=
  Forall (fun ph => Forall (fun sy => 0 < qk (fst sy) (kx1 R0 ph) (kx2 R0 ph) Z0 /\
                                       0 < qk (fst sy) (kx1 R0 (- ph)) (kx2 R0 (- ph)) (- Z0)) l) phis.

Theorem icomp12_ok (Ss : list (i3 * i3)) (l : list (src * fser)) (Rr Zz : J.t) (R0 Z0 : R)
    (CSk : list (J.t * J.t)) (phis : list R) :
  src_in Ss l -> inR Rr R0 -> inR Zz Z0 ->
  Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk phis ->
  cpos12 Ss Rr Zz CSk = true ->
  in12 (icomp12 Ss Rr Zz CSk) (rcomp12 l R0 Z0 phis) /\ apart_l l R0 Z0 phis.
Proof.
  intros H HR HZ HT Hp. unfold icomp12, rcomp12, cpos12, apart_l in *.
  assert (G : Forall2 in12 (map (fun CS => ipoint12 Ss Rr Zz (fst CS) (snd CS)) CSk)
                           (map (fun ph => rpoint12 l R0 ph Z0) phis) /\
              Forall (fun ph => Forall (fun sy => 0 < qk (fst sy) (kx1 R0 ph) (kx2 R0 ph) Z0 /\
                                                 0 < qk (fst sy) (kx1 R0 (- ph)) (kx2 R0 (- ph)) (- Z0)) l) phis).
  { induction HT as [| CS ph CSk phis [HC HS] _ IH]; [split; constructor |].
    cbn [forallb] in Hp. apply andb_prop in Hp. destruct Hp as [Hp1 Hrest].
    destruct (IH Hrest) as [I1 I2].
    destruct (ipoint12_ok Ss l Rr Zz (fst CS) (snd CS) R0 Z0 ph H HR HZ HC HS Hp1) as [P1 P2].
    cbn [map]. split.
    - constructor; [unfold ipoint12, rpoint12; apply isum12_ok, P1 | exact I1].
    - constructor; [exact P2 | exact I2]. }
  destruct G as [G1 G2]. split; [apply isum12_ok, G1 | exact G2].
Qed.

End Jet12.
