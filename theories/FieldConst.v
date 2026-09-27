(** The constants of the field-line model on the ball of tori about K0.

    On the ball of tori within r of the first torus K0 on the strip w, every
    source converging ([Hball]), the components of the total field and their
    derivatives are within r of their values along K0, up to the second-order
    remainders and the changes of the derivatives bounded in FieldTotal.v
    ([ball_B], [ball_D]). The inverse U of B_phi converges from the seed Ub
    on the whole ball once the defect of Ub along K0 plus the change of B_phi
    times |Ub| is below one ([ball_U]). From these come the bounds of the
    model that the KAM iteration takes: the velocity, its derivative, the
    density and its gradient ([ball_model]), the second-order remainder of
    the velocity ([ball_taylor]) and the changes of the density and of the
    derivative ([ball_lipS], [ball_lipD]) between two tori of the ball. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer KAMStep KAMDiff Hypotheses Invariance
  CoilSym FieldKern FieldFam FieldModel FieldTaylor FieldTotal FieldBall FieldLine.
Local Open Scope R_scope.

Lemma fsub_self_nb (rho r : R) (u : fser) : 0 <= r -> nbound rho r (fsub u u).
Proof.
  intros Hr. apply (nbound_le rho 0); [exact Hr |].
  apply (nbound_feq _ _ fzero); [| apply nbound_fzero].
  intros m n. unfold fsub, fadd, fscal. simpl. split; ring.
Qed.

Lemma vsub_self (w r : R) (K : vf) : 0 <= r -> vbound w r (vsub K K).
Proof. intros Hr. split; apply fsub_self_nb, Hr. Qed.

(** A difference across the first torus: x' - x = (x' - x0) - (x - x0). *)
Lemma sub_mid_feq (x x' x0 : fser) : feq (fsub x' x) (fsub (fsub x' x0) (fsub x x0)).
Proof. intros m n. unfold fsub, fadd, fscal. simpl. split; ring. Qed.

Lemma add_mid_feq (x x0 : fser) : feq x (fadd x0 (fsub x x0)).
Proof. intros m n. unfold fsub, fadd, fscal. simpl. split; ring. Qed.

(** * The second-order remainder of R B / B_phi, over abstract families *)

Section GenTaylor.

Variables (w : R) (KR KR' KZ KZ' U U' BP BP' BPR BPZ B B' BRd BZd : fser).
Hypothesis Hw : 0 < w.
Hypothesis CKR : is_canon KR. Hypothesis CKR' : is_canon KR'.
Hypothesis CKZ : is_canon KZ. Hypothesis CKZ' : is_canon KZ'.
Hypothesis CU1 : is_canon U. Hypothesis CU2 : is_canon U'.
Hypothesis CBP : is_canon BP. Hypothesis CBP' : is_canon BP'.
Hypothesis CBPR : is_canon BPR. Hypothesis CBPZ : is_canon BPZ.
Hypothesis CB : is_canon B. Hypothesis CB' : is_canon B'.
Hypothesis CBRd : is_canon BRd. Hypothesis CBZd : is_canon BZd.
Hypothesis FKR : fin w KR. Hypothesis FKR' : fin w KR'.
Hypothesis FKZ : fin w KZ. Hypothesis FKZ' : fin w KZ'.
Hypothesis FU1 : fin w U. Hypothesis FU2 : fin w U'.
Hypothesis FBP : fin w BP. Hypothesis FBP' : fin w BP'.
Hypothesis FBPR : fin w BPR. Hypothesis FBPZ : fin w BPZ.
Hypothesis FB : fin w B. Hypothesis FB' : fin w B'.
Hypothesis FBRd : fin w BRd. Hypothesis FBZd : fin w BZd.
Hypothesis I1 : forall t p, feval BP t p * feval U t p = 1.
Hypothesis I2 : forall t p, feval BP' t p * feval U' t p = 1.

Definition gLHS : fser :=
  fsub (fsub (fmul (fmul KR' U') B') (fmul (fmul KR U) B))
       (fadd (fmul (fadd (fmul (fsub U (fmul (fmul KR U) (fmul U BPR))) B) (fmul (fmul KR U) BRd)) (fsub KR' KR))
             (fmul (fadd (fmul (fscal (-1) (fmul (fmul KR U) (fmul U BPZ))) B) (fmul (fmul KR U) BZd)) (fsub KZ' KZ))).

Definition gR2 : fser := fsub (fsub B' B) (fadd (fmul BRd (fsub KR' KR)) (fmul BZd (fsub KZ' KZ))).
Definition gR2P : fser := fsub (fsub BP' BP) (fadd (fmul BPR (fsub KR' KR)) (fmul BPZ (fsub KZ' KZ))).

Definition gX : fser :=
  fadd (fadd (fadd (fadd (fadd
    (fmul (fmul KR U) gR2)
    (fmul (fmul KR B) (fsub (fmul (fmul U U) (fmul U' (fmul (fsub BP' BP) (fsub BP' BP)))) (fmul (fmul U U) gR2P))))
    (fmul (fmul (fsub KR' KR) (fsub U' U)) B))
    (fmul (fmul (fsub KR' KR) U) (fsub B' B)))
    (fmul (fmul KR (fsub U' U)) (fsub B' B)))
    (fmul (fmul (fsub KR' KR) (fsub U' U)) (fsub B' B)).

Lemma g0 (u : fser) : fin w u -> fin 0 u. Proof. apply fin_mono. lra. Qed.

Ltac gfin :=
  repeat (first [apply g0; assumption | apply fin_fmul; [lra | |] | apply fin_fsub | apply fin_fadd | apply fin_fscal
                | assumption]).
Ltac gcanon :=
  repeat (first [assumption | apply fmul_canon | apply fsub_canon | apply fadd_canon | apply fscal_canon]).
Ltac gev :=
  repeat (first [rewrite feval_fadd' by gfin | rewrite feval_fsub' by gfin | rewrite feval_fmul' by gfin
                | rewrite feval_fscal' by gfin]).

Theorem gX_feq : feq gLHS gX.
Proof.
  assert (CL : is_canon gLHS) by (unfold gLHS; gcanon).
  assert (CX : is_canon gX) by (unfold gX, gR2, gR2P; gcanon).
  assert (FL : fin 0 gLHS) by (unfold gLHS; gfin).
  assert (FX : fin 0 gX) by (unfold gX, gR2, gR2P; gfin).
  destruct FL as [Ma Ha]. destruct FX as [Mb Hb].
  apply (canon_feq _ _ Ma Mb CL CX Ha Hb). intros t p. unfold gLHS, gX, gR2, gR2P. gev.
  pose proof (I1 t p) as J1. pose proof (I2 t p) as J2.
  assert (N1 : feval BP t p <> 0) by (intros Z; rewrite Z in J1; lra).
  assert (N2 : feval BP' t p <> 0) by (intros Z; rewrite Z in J2; lra).
  assert (E1 : feval U t p = / feval BP t p) by (field_simplify_eq; [lra | exact N1]).
  assert (E2 : feval U' t p = / feval BP' t p) by (field_simplify_eq; [lra | exact N2]).
  rewrite E1, E2. field. split; assumption.
Qed.

Theorem gX_nb (h hm kRb Ubb bB LB LBP T2 T2P : R) :
  0 <= h -> h <= hm ->
  nbound w kRb KR -> nbound w Ubb U -> nbound w Ubb U' -> nbound w bB B -> nbound w h (fsub KR' KR) ->
  nbound w (h * (Ubb * Ubb * LBP)) (fsub U' U) -> nbound w (h * LB) (fsub B' B) -> nbound w (h * LBP) (fsub BP' BP) ->
  nbound w (h * h * T2) gR2 -> nbound w (h * h * T2P) gR2P ->
  nbound w (h * h * (kRb * Ubb * T2 + kRb * bB * (Ubb * Ubb * (Ubb * (LBP * LBP)) + Ubb * Ubb * T2P)
                     + Ubb * Ubb * LBP * bB + Ubb * LB + kRb * (Ubb * Ubb * LBP) * LB
                     + hm * (Ubb * Ubb * LBP) * LB)) gX.
Proof.
  intros Hh Hhm NKR NU NU' NB NdR NdU NdB NdP NR2 NR2P.
  assert (Hw0 : 0 <= w) by lra.
  pose proof (nbound_fsub w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NU NU)
                (nbound_fmul w _ _ _ _ Hw0 NU' (nbound_fmul w _ _ _ _ Hw0 NdP NdP)))
                (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NU NU) NR2P)) as Q.
  pose proof (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _
                (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NKR NU) NR2)
                   (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NKR NB) Q))
                (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NdR NdU) NB))
                (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NdR NU) NdB))
                (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NKR NdU) NdB))
                (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 NdR NdU) NdB)) as T.
  unfold gX. refine (nbound_le w _ _ _ _ T).
  destruct (Req_dec h 0) as [Z | Z]; [rewrite Z; right; ring |].
  assert (Hp : 0 < h) by lra.
  pose proof (nbound_nonneg _ _ _ NdU) as LU0. pose proof (nbound_nonneg _ _ _ NdB) as LB0.
  set (LU := Ubb * Ubb * LBP) in *.
  assert (LU1 : 0 <= LU) by (destruct (Rle_or_lt 0 LU) as [A | A]; [exact A | nra]).
  assert (LB1 : 0 <= LB) by (destruct (Rle_or_lt 0 LB) as [A | A]; [exact A | nra]).
  assert (Pos : 0 <= h * h * (LU * LB) * (hm - h)).
  { apply Rmult_le_pos; [| lra]. apply Rmult_le_pos; [nra | apply Rmult_le_pos; assumption]. }
  match goal with |- ?A <= ?Bx => assert (E : Bx - A = h * h * (LU * LB) * (hm - h)) by (unfold LU; ring) end.
  lra.
Qed.

End GenTaylor.

Section Const.

Variables (P : Z) (l : list (src * fser)) (Ub : fser) (w r hm cs : R) (K0 : vf).
Variables (dr1 dr2 dr3 dyb : src * fser -> R).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hw : 0 < w.
Hypothesis Hr : 0 <= r.
Hypothesis Hhm : 2 * r <= hm.
Hypothesis Hcs : nbound w cs cosf /\ nbound w cs sinf.
Hypothesis FK0 : vfin w K0.
Hypothesis CK0 : vcanon K0.
Hypothesis SK0 : vsym K0.
Hypothesis QK0 : vper P K0.
Hypothesis Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Hypothesis CU : is_canon Ub.

(** A torus of the ball. *)
Definition inb (K : vf) : Prop := vcanon K /\ vsym K /\ vper P K /\ vbound w r (vsub K K0).

Hypothesis Hball : forall K, inb K ->
  List.Forall (fun sy => src_ok w hm cs K sy (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy)) l.

Lemma Hw0 : 0 <= w. Proof. lra. Qed.

Lemma inb_K0 : inb K0.
Proof. exact (conj CK0 (conj SK0 (conj QK0 (vsub_self w r K0 Hr)))). Qed.

Lemma inb_fin (K : vf) : inb K -> vfin w K.
Proof.
  intros [_ [_ [_ [BR BZ]]]]. destruct FK0 as [[M1 H1] [M2 H2]].
  split; [exists (M1 + r) | exists (M2 + r)];
    [apply (nbound_feq w _ _ _ (feq_sym _ _ (add_mid_feq (vR K) (vR K0))))
    | apply (nbound_feq w _ _ _ (feq_sym _ _ (add_mid_feq (vZ K) (vZ K0))))];
    apply nbound_fadd; assumption.
Qed.

(** Two tori of the ball are within 2 r. *)
Lemma inb_pair (K K' : vf) : inb K -> inb K' -> vbound w (2 * r) (vsub K' K).
Proof.
  intros [_ [_ [_ [A1 A2]]]] [_ [_ [_ [B1 B2]]]].
  replace (2 * r) with (r + r) by ring.
  split; [apply (nbound_feq w _ _ _ (feq_sym _ _ (sub_mid_feq (vR K) (vR K') (vR K0))))
         | apply (nbound_feq w _ _ _ (feq_sym _ _ (sub_mid_feq (vZ K) (vZ K') (vZ K0))))];
    apply nbound_fsub; assumption.
Qed.

(** The data of the sources for a pair of tori of the ball. *)
Lemma pair_src (K K' : vf) : inb K -> inb K' ->
  List.Forall (fun sy => src_ok w hm cs K sy (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) /\
                 isq_ok w (fq (fst sy) K') (snd sy) /\ 0 < feval (fy (fst sy) (snd sy) K') 0 0) l.
Proof.
  intros IK IK'. pose proof (Hball K IK) as A. pose proof (Hball K' IK') as B.
  rewrite Forall_forall in A, B |- *. intros sy I.
  destruct (B sy I) as [Q [Y0 _]]. exact (conj (A sy I) (conj Q Y0)).
Qed.

Lemma srcs_inb (K : vf) : inb K -> srcs_ok w l K.
Proof.
  intros IK. unfold srcs_ok. eapply Forall_impl; [| exact (Hball K IK)]. intros sy [Q [Y0 _]]. exact (conj Q Y0).
Qed.

(** The constants of the total field over the sources. *)
Definition cR2R : R := TR2R P hm cs l dr1 dr2 dr3 dyb.
Definition cR2Z : R := TR2Z P hm cs l dr1 dr2 dr3 dyb.
Definition cLRR : R := TLRR P hm cs l dr1 dr2 dr3 dyb.
Definition cLRZ : R := TLRZ P hm cs l dr1 dr2 dr3 dyb.
Definition cLZR : R := TLZR P hm cs l dr1 dr2 dr3 dyb.
Definition cLZZ : R := TLZZ P hm cs l dr1 dr2 dr3 dyb.

Lemma pair_r2 (K K' : vf) (h : R) : inb K -> inb K' -> 0 <= h -> h <= hm -> vbound w h (vsub K' K) ->
  nbound w (h * h * cR2R) (fsub (fsub (jR (tot P l K')) (jR (tot P l K)))
                              (fadd (fmul (jR_R (tot P l K)) (tdR K K')) (fmul (jR_Z (tot P l K)) (tdZ K K')))) /\
  nbound w (h * h * cR2R) (fsub (fsub (jP (tot P l K')) (jP (tot P l K)))
                              (fadd (fmul (jP_R (tot P l K)) (tdR K K')) (fmul (jP_Z (tot P l K)) (tdZ K K')))) /\
  nbound w (h * h * cR2Z) (fsub (fsub (jZ (tot P l K')) (jZ (tot P l K)))
                              (fadd (fmul (jZ_R (tot P l K)) (tdR K K')) (fmul (jZ_Z (tot P l K)) (tdZ K K')))).
Proof.
  intros IK IK' Hh Hh' HD. pose proof IK as [CK [SK [QK _]]]. pose proof IK' as [CK' [SK' [QK' _]]].
  exact (tot_r2 P w h hm cs K K' l dr1 dr2 dr3 dyb Hcs HP Hw SK SK' QK QK' (inb_fin K IK) (inb_fin K' IK')
           CK CK' Cl Hh Hh' HD (pair_src K K' IK IK')).
Qed.

Lemma pair_lip (K K' : vf) (h : R) : inb K -> inb K' -> 0 <= h -> h <= hm -> vbound w h (vsub K' K) ->
  nbound w (h * cLRR) (fsub (jR_R (tot P l K')) (jR_R (tot P l K))) /\
  nbound w (h * cLRZ) (fsub (jR_Z (tot P l K')) (jR_Z (tot P l K))) /\
  nbound w (h * cLRR) (fsub (jP_R (tot P l K')) (jP_R (tot P l K))) /\
  nbound w (h * cLRZ) (fsub (jP_Z (tot P l K')) (jP_Z (tot P l K))) /\
  nbound w (h * cLZR) (fsub (jZ_R (tot P l K')) (jZ_R (tot P l K))) /\
  nbound w (h * cLZZ) (fsub (jZ_Z (tot P l K')) (jZ_Z (tot P l K))).
Proof.
  intros IK IK' Hh Hh' HD. pose proof IK as [CK _]. pose proof IK' as [CK' _].
  exact (tot_lip P w h hm cs K K' l dr1 dr2 dr3 dyb Hcs Hw (inb_fin K IK) (inb_fin K' IK')
           CK CK' Cl Hh Hh' HD (pair_src K K' IK IK')).
Qed.

(** * The total field on the ball *)

Variables (bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0 : R).
Hypothesis BR0 : nbound w bR0 (jR (tot P l K0)).
Hypothesis BP0 : nbound w bP0 (jP (tot P l K0)).
Hypothesis BZ0 : nbound w bZ0 (jZ (tot P l K0)).
Hypothesis DRR0 : nbound w dRR0 (jR_R (tot P l K0)).
Hypothesis DRZ0 : nbound w dRZ0 (jR_Z (tot P l K0)).
Hypothesis DPR0 : nbound w dPR0 (jP_R (tot P l K0)).
Hypothesis DPZ0 : nbound w dPZ0 (jP_Z (tot P l K0)).
Hypothesis DZR0 : nbound w dZR0 (jZ_R (tot P l K0)).
Hypothesis DZZ0 : nbound w dZZ0 (jZ_Z (tot P l K0)).
Hypothesis KR0 : nbound w kR0 (vR K0).
Hypothesis BUb : nbound w MU Ub.
Hypothesis TU0 : nbound w thU0 (fsub fone (fmul (jP (tot P l K0)) Ub)).

Definition bRR : R := dRR0 + r * cLRR.
Definition bRZ : R := dRZ0 + r * cLRZ.
Definition bPR : R := dPR0 + r * cLRR.
Definition bPZ : R := dPZ0 + r * cLRZ.
Definition bZR : R := dZR0 + r * cLZR.
Definition bZZ : R := dZZ0 + r * cLZZ.
Definition dBR : R := (dRR0 + dRZ0) * r + r * r * cR2R.
Definition dBP : R := (dPR0 + dPZ0) * r + r * r * cR2R.
Definition dBZ : R := (dZR0 + dZZ0) * r + r * r * cR2Z.
Definition bBR : R := bR0 + dBR.
Definition bBP : R := bP0 + dBP.
Definition bBZ : R := bZ0 + dBZ.
Definition kRb : R := kR0 + r.

Lemma Hr_hm : r <= hm. Proof. lra. Qed.

Lemma mid_nb (x x0 : fser) (M0 D : R) : nbound w M0 x0 -> nbound w D (fsub x x0) -> nbound w (M0 + D) x.
Proof. intros A B. apply (nbound_feq w _ _ _ (feq_sym _ _ (add_mid_feq x x0))). apply nbound_fadd; assumption. Qed.

Lemma ball_D (K : vf) : inb K ->
  nbound w bRR (jR_R (tot P l K)) /\ nbound w bRZ (jR_Z (tot P l K)) /\
  nbound w bPR (jP_R (tot P l K)) /\ nbound w bPZ (jP_Z (tot P l K)) /\
  nbound w bZR (jZ_R (tot P l K)) /\ nbound w bZZ (jZ_Z (tot P l K)).
Proof.
  intros IK. pose proof IK as [_ [_ [_ HD]]].
  destruct (pair_lip K0 K r inb_K0 IK Hr Hr_hm HD) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
  exact (conj (mid_nb _ _ _ _ DRR0 L1) (conj (mid_nb _ _ _ _ DRZ0 L2) (conj (mid_nb _ _ _ _ DPR0 L3)
          (conj (mid_nb _ _ _ _ DPZ0 L4) (conj (mid_nb _ _ _ _ DZR0 L5) (mid_nb _ _ _ _ DZZ0 L6)))))).
Qed.

(** A component along K is its value along K0, plus the derivatives along K0
    applied to K - K0, plus the remainder. *)
Lemma three_feq (x x0 d : fser) : feq x (fadd x0 (fadd d (fsub (fsub x x0) d))).
Proof. intros m n. unfold fsub, fadd, fscal. simpl. split; ring. Qed.

Lemma ball_dB (K : vf) : inb K ->
  nbound w dBR (fsub (jR (tot P l K)) (jR (tot P l K0))) /\
  nbound w dBP (fsub (jP (tot P l K)) (jP (tot P l K0))) /\
  nbound w dBZ (fsub (jZ (tot P l K)) (jZ (tot P l K0))).
Proof.
  intros IK. pose proof IK as [_ [_ [_ HD]]].
  destruct (pair_r2 K0 K r inb_K0 IK Hr Hr_hm HD) as [R1 [R2 R3]].
  assert (T : forall (x x0 dR dZ : fser) (M1 M2 T : R), nbound w M1 dR -> nbound w M2 dZ ->
            nbound w (r * r * T) (fsub (fsub x x0) (fadd (fmul dR (tdR K0 K)) (fmul dZ (tdZ K0 K)))) ->
            nbound w ((M1 + M2) * r + r * r * T) (fsub x x0)).
  { intros x x0 dR dZ M1 M2 T A1 A2 A3.
    assert (E : feq (fsub x x0) (fadd (fadd (fmul dR (tdR K0 K)) (fmul dZ (tdZ K0 K)))
                                      (fsub (fsub x x0) (fadd (fmul dR (tdR K0 K)) (fmul dZ (tdZ K0 K)))))).
    { intros m n. unfold fsub, fadd, fscal. simpl. split; ring. }
    apply (nbound_feq w _ _ _ (feq_sym _ _ E)).
    replace ((M1 + M2) * r + r * r * T) with (M1 * r + M2 * r + r * r * T) by ring.
    apply nbound_fadd; [apply nbound_fadd |]; [apply (nbound_fmul w _ _ _ _ Hw0 A1) | apply (nbound_fmul w _ _ _ _ Hw0 A2) |];
      [exact (proj1 HD) | exact (proj2 HD) | exact A3]. }
  refine (conj _ (conj _ _)); [exact (T _ _ _ _ _ _ _ DRR0 DRZ0 R1) | exact (T _ _ _ _ _ _ _ DPR0 DPZ0 R2)
                              | exact (T _ _ _ _ _ _ _ DZR0 DZZ0 R3)].
Qed.

Lemma ball_B (K : vf) : inb K ->
  nbound w bBR (jR (tot P l K)) /\ nbound w bBP (jP (tot P l K)) /\ nbound w bBZ (jZ (tot P l K)).
Proof.
  intros IK. destruct (ball_dB K IK) as [A1 [A2 A3]].
  exact (conj (mid_nb _ _ _ _ BR0 A1) (conj (mid_nb _ _ _ _ BP0 A2) (mid_nb _ _ _ _ BZ0 A3))).
Qed.

Lemma ball_KR (K : vf) : inb K -> nbound w kRb (vR K).
Proof. intros [_ [_ [_ [HR _]]]]. exact (mid_nb _ _ _ _ KR0 HR). Qed.

(** * The inverse of B_phi on the ball *)

Definition thU : R := thU0 + dBP * MU.
Definition Ubb : R := MU + inv_eps MU thU 0.

Hypothesis HthU : thU < 1.

Lemma f0 (u : fser) : fin w u -> fin 0 u. Proof. apply fin_mono. lra. Qed.

Lemma tot_canon' (K : vf) : inb K -> jcanon (tot P l K).
Proof. intros [CK _]. apply tot_canon; assumption. Qed.

Lemma tot_fin' (K : vf) : inb K -> jfin w (tot P l K).
Proof. intros IK. apply tot_fin; [exact Hw | exact (inb_fin K IK) | exact (srcs_inb K IK)]. Qed.

Lemma defU_feq (K : vf) : inb K ->
  feq (fsub fone (fmul (jP (tot P l K)) Ub))
      (fsub (fsub fone (fmul (jP (tot P l K0)) Ub)) (fmul (fsub (jP (tot P l K)) (jP (tot P l K0))) Ub)).
Proof.
  intros IK.
  destruct (tot_canon' K IK) as [_ [C1 _]]. destruct (tot_canon' K0 inb_K0) as [_ [C0 _]].
  destruct (tot_fin' K IK) as [_ [F1 _]]. destruct (tot_fin' K0 inb_K0) as [_ [F0 _]].
  assert (FU : fin w Ub) by (exists MU; exact BUb).
  assert (A : is_canon (fsub fone (fmul (jP (tot P l K)) Ub)))
    by (apply fsub_canon; [apply fone_canon | apply fmul_canon; assumption]).
  assert (B : is_canon (fsub (fsub fone (fmul (jP (tot P l K0)) Ub)) (fmul (fsub (jP (tot P l K)) (jP (tot P l K0))) Ub))).
  { apply fsub_canon; [apply fsub_canon; [apply fone_canon | apply fmul_canon; assumption] |].
    apply fmul_canon; [apply fsub_canon |]; assumption. }
  assert (F1' := f0 _ F1). assert (F0' := f0 _ F0). assert (FU' := f0 _ FU).
  assert (Fo : fin 0 fone) by exact (fin_fconst 0 1).
  assert (M1 : fin 0 (fmul (jP (tot P l K)) Ub)) by (apply fin_fmul; [lra | assumption | assumption]).
  assert (M0 : fin 0 (fmul (jP (tot P l K0)) Ub)) by (apply fin_fmul; [lra | assumption | assumption]).
  assert (Fd : fin 0 (fsub (jP (tot P l K)) (jP (tot P l K0)))) by (apply fin_fsub; assumption).
  assert (Md : fin 0 (fmul (fsub (jP (tot P l K)) (jP (tot P l K0))) Ub)) by (apply fin_fmul; [lra | assumption | assumption]).
  destruct (fin_fsub 0 _ _ Fo M1) as [Ma Ha].
  destruct (fin_fsub 0 _ _ (fin_fsub 0 _ _ Fo M0) Md) as [Mb Hb].
  apply (canon_feq _ _ Ma Mb A B Ha Hb). intros t p.
  rewrite (feval_fsub' t p _ _ Fo M1), (feval_fsub' t p _ _ (fin_fsub 0 _ _ Fo M0) Md), (feval_fsub' t p _ _ Fo M0),
    (feval_fmul' t p _ _ F1' FU'), (feval_fmul' t p _ _ F0' FU'), (feval_fmul' t p _ _ Fd FU'),
    (feval_fsub' t p _ _ F1' F0').
  ring.
Qed.

Lemma dBP_nn : 0 <= dBP.
Proof. destruct (ball_dB K0 inb_K0) as [_ [A _]]. exact (nbound_nonneg _ _ _ A). Qed.

Lemma ball_defU (K : vf) : inb K -> nbound w thU (fsub fone (fmul (jP (tot P l K)) Ub)).
Proof.
  intros IK. apply (nbound_feq w _ _ _ (feq_sym _ _ (defU_feq K IK))). unfold thU.
  apply nbound_fsub; [exact TU0 |]. apply (nbound_fmul w _ _ _ _ Hw0); [exact (proj1 (proj2 (ball_dB K IK))) | exact BUb].
Qed.

Lemma thU_nn : 0 <= thU. Proof. exact (nbound_nonneg _ _ _ (ball_defU K0 inb_K0)). Qed.

Lemma ball_inv (K : vf) : inb K -> inv_ok w (jP (lj P l K)) Ub.
Proof.
  intros IK. exists bBP, MU, thU.
  exact (conj (proj1 (proj2 (ball_B K IK))) (conj BUb (conj (conj thU_nn HthU) (ball_defU K IK)))).
Qed.

Lemma ball_U (K : vf) : inb K -> nbound w Ubb (lU P l Ub K).
Proof. intros IK. exact (nbound_finv w Hw0 _ _ MU thU BUb (conj thU_nn HthU) (ball_defU K IK)). Qed.

Lemma ball_Uinv (K : vf) (t p : R) : inb K -> feval (jP (tot P l K)) t p * feval (lU P l Ub K) t p = 1.
Proof.
  intros IK. exact (feval_finv w Hw0 _ _ bBP MU thU (proj1 (proj2 (ball_B K IK))) BUb (conj thU_nn HthU)
                      (ball_defU K IK) t p).
Qed.

Lemma C_U (K : vf) : inb K -> is_canon (lU P l Ub K).
Proof. intros IK. unfold lU, lj. apply finv_canon; [exact (proj1 (proj2 (tot_canon' K IK))) | exact CU]. Qed.

(** * Differences between two tori of the ball *)

Definition LBR : R := bRR + bRZ + hm * cR2R.
Definition LBP : R := bPR + bPZ + hm * cR2R.
Definition LBZ : R := bZR + bZZ + hm * cR2Z.
Definition LU : R := Ubb * Ubb * LBP.

(** The norms and the changes of the factors of the model. *)
Definition cW : R := kRb * Ubb.
Definition LW : R := 1 * Ubb + kRb * LU.
Definition cUPR : R := Ubb * bPR.
Definition LUPR : R := LU * bPR + Ubb * cLRR.
Definition cUPZ : R := Ubb * bPZ.
Definition LUPZ : R := LU * bPZ + Ubb * cLRZ.
Definition cWR : R := Ubb + cW * cUPR.
Definition LWR : R := LU + (LW * cUPR + cW * LUPR).
Definition cWZ : R := Rabs (-1) * (cW * cUPZ).
Definition LWZ : R := Rabs (-1) * (LW * cUPZ + cW * LUPZ).
Definition cmRR : R := cWR * bBR + cW * bRR.
Definition LmRR : R := LWR * bBR + cWR * LBR + (LW * bRR + cW * cLRR).
Definition cmRZ : R := cWZ * bBR + cW * bRZ.
Definition LmRZ : R := LWZ * bBR + cWZ * LBR + (LW * bRZ + cW * cLRZ).
Definition cmZR : R := cWR * bBZ + cW * bZR.
Definition LmZR : R := LWR * bBZ + cWR * LBZ + (LW * bZR + cW * cLZR).
Definition cmZZ : R := cWZ * bBZ + cW * bZZ.
Definition LmZZ : R := LWZ * bBZ + cWZ * LBZ + (LW * bZZ + cW * cLZZ).

(** The constants of the model. *)
Definition bMV : R := Rmax (cW * bBR) (cW * bBZ).
Definition bDV : R := Rmax (Rmax cmRR cmRZ) (Rmax cmZR cmZZ).
Definition bLD : R := Rmax (Rmax LmRR LmRZ) (Rmax LmZR LmZZ).
Definition bS1 : R := Rmax bPR bPZ.
Definition TMR : R :=
  kRb * Ubb * cR2R + kRb * bBR * (Ubb * Ubb * (Ubb * (LBP * LBP)) + Ubb * Ubb * cR2R)
  + LU * bBR + Ubb * LBR + kRb * LU * LBR + hm * LU * LBR.
Definition TMZ : R :=
  kRb * Ubb * cR2Z + kRb * bBZ * (Ubb * Ubb * (Ubb * (LBP * LBP)) + Ubb * Ubb * cR2R)
  + LU * bBZ + Ubb * LBZ + kRb * LU * LBZ + hm * LU * LBZ.
Definition bM2 : R := Rmax TMR TMZ.

Section Pair.

Variables (K K' : vf) (h : R).
Hypothesis IK : inb K.
Hypothesis IK' : inb K'.
Hypothesis Hh : 0 <= h.
Hypothesis Hhh : h <= hm.
Hypothesis HD : vbound w h (vsub K' K).

(** u along K and u' along K', both of norm at most A, differing by at most h L. *)
Definition lp (u u' : fser) (A L : R) : Prop :=
  is_canon u /\ is_canon u' /\ nbound w A u /\ nbound w A u' /\ nbound w (h * L) (fsub u' u).

Lemma dmul_feq (a a' b b' : fser) :
  is_canon a -> is_canon a' -> is_canon b -> is_canon b' -> fin w a -> fin w a' -> fin w b -> fin w b' ->
  feq (fsub (fmul a' b') (fmul a b)) (fadd (fmul (fsub a' a) b') (fmul a (fsub b' b))).
Proof.
  intros Ca Ca' Cb Cb' Fa Fa' Fb Fb'.
  pose proof (f0 _ Fa) as A. pose proof (f0 _ Fa') as A'. pose proof (f0 _ Fb) as B. pose proof (f0 _ Fb') as B'.
  assert (M1 : fin 0 (fmul a' b')) by (apply fin_fmul; [lra | assumption | assumption]).
  assert (M2 : fin 0 (fmul a b)) by (apply fin_fmul; [lra | assumption | assumption]).
  assert (D1 : fin 0 (fsub a' a)) by (apply fin_fsub; assumption).
  assert (D2 : fin 0 (fsub b' b)) by (apply fin_fsub; assumption).
  assert (N1 : fin 0 (fmul (fsub a' a) b')) by (apply fin_fmul; [lra | assumption | assumption]).
  assert (N2 : fin 0 (fmul a (fsub b' b))) by (apply fin_fmul; [lra | assumption | assumption]).
  destruct (fin_fsub 0 _ _ M1 M2) as [Ma Ha]. destruct (fin_fadd 0 _ _ N1 N2) as [Mb Hb].
  apply (canon_feq _ _ Ma Mb); [apply fsub_canon; apply fmul_canon; assumption
    | apply fadd_canon; apply fmul_canon; try apply fsub_canon; assumption | exact Ha | exact Hb |].
  intros t p.
  rewrite (feval_fsub' t p _ _ M1 M2), (feval_fadd' t p _ _ N1 N2), (feval_fmul' t p _ _ A' B'),
    (feval_fmul' t p _ _ A B), (feval_fmul' t p _ _ D1 B'), (feval_fmul' t p _ _ A D2),
    (feval_fsub' t p _ _ A' A), (feval_fsub' t p _ _ B' B).
  ring.
Qed.

Lemma lp_fin (u u' : fser) (A L : R) : lp u u' A L -> fin w u /\ fin w u'.
Proof. intros [_ [_ [Bu [Bu' _]]]]. split; eexists; eassumption. Qed.

Lemma lp_mul (a a' b b' : fser) (A La B Lb : R) :
  lp a a' A La -> lp b b' B Lb -> lp (fmul a b) (fmul a' b') (A * B) (La * B + A * Lb).
Proof.
  intros Ha Hb. destruct (lp_fin _ _ _ _ Ha) as [Fa Fa']. destruct (lp_fin _ _ _ _ Hb) as [Fb Fb'].
  destruct Ha as [Ca [Ca' [Ba [Ba' Da]]]]. destruct Hb as [Cb [Cb' [Bb [Bb' Db]]]].
  refine (conj (fmul_canon _ _ Ca Cb) (conj (fmul_canon _ _ Ca' Cb')
           (conj (nbound_fmul w _ _ _ _ Hw0 Ba Bb) (conj (nbound_fmul w _ _ _ _ Hw0 Ba' Bb') _)))).
  apply (nbound_feq w _ _ _ (feq_sym _ _ (dmul_feq a a' b b' Ca Ca' Cb Cb' Fa Fa' Fb Fb'))).
  replace (h * (La * B + A * Lb)) with (h * La * B + A * (h * Lb)) by ring.
  apply nbound_fadd; apply (nbound_fmul w _ _ _ _ Hw0); assumption.
Qed.

Lemma lp_add (a a' b b' : fser) (A La B Lb : R) :
  lp a a' A La -> lp b b' B Lb -> lp (fadd a b) (fadd a' b') (A + B) (La + Lb).
Proof.
  intros [Ca [Ca' [Ba [Ba' Da]]]] [Cb [Cb' [Bb [Bb' Db]]]].
  refine (conj (fadd_canon _ _ Ca Cb) (conj (fadd_canon _ _ Ca' Cb')
           (conj (nbound_fadd w _ _ _ _ Ba Bb) (conj (nbound_fadd w _ _ _ _ Ba' Bb') _)))).
  assert (E : feq (fsub (fadd a' b') (fadd a b)) (fadd (fsub a' a) (fsub b' b))).
  { intros m n. unfold fsub, fadd, fscal. simpl. split; ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)). replace (h * (La + Lb)) with (h * La + h * Lb) by ring.
  apply nbound_fadd; assumption.
Qed.

Lemma lp_sub (a a' b b' : fser) (A La B Lb : R) :
  lp a a' A La -> lp b b' B Lb -> lp (fsub a b) (fsub a' b') (A + B) (La + Lb).
Proof.
  intros [Ca [Ca' [Ba [Ba' Da]]]] [Cb [Cb' [Bb [Bb' Db]]]].
  refine (conj (fsub_canon _ _ Ca Cb) (conj (fsub_canon _ _ Ca' Cb')
           (conj (nbound_fsub w _ _ _ _ Ba Bb) (conj (nbound_fsub w _ _ _ _ Ba' Bb') _)))).
  assert (E : feq (fsub (fsub a' b') (fsub a b)) (fsub (fsub a' a) (fsub b' b))).
  { intros m n. unfold fsub, fadd, fscal. simpl. split; ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)). replace (h * (La + Lb)) with (h * La + h * Lb) by ring.
  apply nbound_fsub; assumption.
Qed.

Lemma lp_scal (c : R) (a a' : fser) (A La : R) :
  lp a a' A La -> lp (fscal c a) (fscal c a') (Rabs c * A) (Rabs c * La).
Proof.
  intros [Ca [Ca' [Ba [Ba' Da]]]].
  refine (conj (fscal_canon _ _ Ca) (conj (fscal_canon _ _ Ca')
           (conj (nbound_fscal w _ _ _ Ba) (conj (nbound_fscal w _ _ _ Ba') _)))).
  assert (E : feq (fsub (fscal c a') (fscal c a)) (fscal c (fsub a' a))).
  { intros m n. unfold fsub, fadd, fscal. simpl. split; ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)). replace (h * (Rabs c * La)) with (Rabs c * (h * La)) by ring.
  apply nbound_fscal; assumption.
Qed.

(** The leaves. *)
Lemma lp_KR : lp (vR K) (vR K') kRb 1.
Proof.
  destruct IK as [[CR _] _]. destruct IK' as [[CR' _] _].
  refine (conj CR (conj CR' (conj (ball_KR K IK) (conj (ball_KR K' IK') _)))).
  rewrite Rmult_1_r. exact (proj1 HD).
Qed.

Lemma lp_Dall :
  lp (jR_R (tot P l K)) (jR_R (tot P l K')) bRR cLRR /\ lp (jR_Z (tot P l K)) (jR_Z (tot P l K')) bRZ cLRZ /\
  lp (jP_R (tot P l K)) (jP_R (tot P l K')) bPR cLRR /\ lp (jP_Z (tot P l K)) (jP_Z (tot P l K')) bPZ cLRZ /\
  lp (jZ_R (tot P l K)) (jZ_R (tot P l K')) bZR cLZR /\ lp (jZ_Z (tot P l K)) (jZ_Z (tot P l K')) bZZ cLZZ.
Proof.
  destruct (tot_canon' K IK) as [_ [_ [_ [C4 [C5 [_ [C7 [C8 [_ [C10 [C11 _]]]]]]]]]]].
  destruct (tot_canon' K' IK') as [_ [_ [_ [D4 [D5 [_ [D7 [D8 [_ [D10 [D11 _]]]]]]]]]]].
  destruct (ball_D K IK) as [A1 [A2 [A3 [A4 [A5 A6]]]]]. destruct (ball_D K' IK') as [B1 [B2 [B3 [B4 [B5 B6]]]]].
  destruct (pair_lip K K' h IK IK' Hh Hhh HD) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
  unfold lp. conjs; assumption.
Qed.

Lemma lp_Ball :
  lp (jR (tot P l K)) (jR (tot P l K')) bBR LBR /\ lp (jP (tot P l K)) (jP (tot P l K')) bBP LBP /\
  lp (jZ (tot P l K)) (jZ (tot P l K')) bBZ LBZ.
Proof.
  destruct (tot_canon' K IK) as [C1 [C2 [C3 _]]]. destruct (tot_canon' K' IK') as [D1 [D2 [D3 _]]].
  destruct (ball_B K IK) as [A1 [A2 A3]]. destruct (ball_B K' IK') as [B1 [B2 B3]].
  destruct (ball_D K IK) as [E1 [E2 [E3 [E4 [E5 E6]]]]].
  destruct (pair_r2 K K' h IK IK' Hh Hhh HD) as [R1 [R2 R3]].
  assert (T : forall (x x' dR dZ : fser) (M1 M2 T : R), nbound w M1 dR -> nbound w M2 dZ ->
            nbound w (h * h * T) (fsub (fsub x' x) (fadd (fmul dR (tdR K K')) (fmul dZ (tdZ K K')))) ->
            nbound w (h * (M1 + M2 + hm * T)) (fsub x' x)).
  { intros x x' dR dZ M1 M2 T N1 N2 N3.
    assert (E : feq (fsub x' x) (fadd (fadd (fmul dR (tdR K K')) (fmul dZ (tdZ K K')))
                                      (fsub (fsub x' x) (fadd (fmul dR (tdR K K')) (fmul dZ (tdZ K K')))))).
    { intros m n. unfold fsub, fadd, fscal. simpl. split; ring. }
    apply (nbound_feq w _ _ _ (feq_sym _ _ E)).
    pose proof (nbound_nonneg _ _ _ N3) as T0.
    apply (nbound_le w (M1 * h + M2 * h + h * h * T)).
    - destruct (Req_dec h 0) as [Z | Z]; [rewrite Z; right; ring |].
      assert (Hp : 0 < h) by lra.
      assert (T1 : 0 <= T).
      { destruct (Rle_or_lt 0 T) as [A | A]; [exact A |].
        assert (0 < h * h) by nra. assert (h * h * T < 0) by nra. lra. }
      assert (h * h * T <= h * (hm * T)).
      { rewrite Rmult_assoc. apply Rmult_le_compat_l; [lra |]. apply Rmult_le_compat_r; lra. }
      lra.
    - apply nbound_fadd; [apply nbound_fadd |]; [apply (nbound_fmul w _ _ _ _ Hw0 N1) | apply (nbound_fmul w _ _ _ _ Hw0 N2) |];
        [exact (proj1 HD) | exact (proj2 HD) | exact N3]. }
  unfold LBR, LBP, LBZ, lp.
  refine (conj _ (conj _ _)); (refine (conj _ (conj _ (conj _ (conj _ _)))); [assumption .. |]).
  - exact (T _ _ _ _ _ _ _ E1 E2 R1).
  - exact (T _ _ _ _ _ _ _ E3 E4 R2).
  - exact (T _ _ _ _ _ _ _ E5 E6 R3).
Qed.

Lemma lp_U : lp (lU P l Ub K) (lU P l Ub K') Ubb LU.
Proof.
  destruct lp_Ball as [_ [[C1 [C1' [B1 [B1' D1]]]] _]].
  pose proof (C_U K IK) as CU1. pose proof (C_U K' IK') as CU2.
  pose proof (ball_U K IK) as U1. pose proof (ball_U K' IK') as U2.
  refine (conj CU1 (conj CU2 (conj U1 (conj U2 _)))).
  assert (E : feq (fsub (lU P l Ub K') (lU P l Ub K))
                  (fscal (-1) (fmul (fmul (lU P l Ub K) (lU P l Ub K')) (fsub (jP (tot P l K')) (jP (tot P l K)))))).
  { assert (F1 : fin 0 (lU P l Ub K)) by (exists Ubb; exact (nbound_mono w 0 _ _ Hw0 U1)).
    assert (F2 : fin 0 (lU P l Ub K')) by (exists Ubb; exact (nbound_mono w 0 _ _ Hw0 U2)).
    assert (G1 : fin 0 (jP (tot P l K))) by (exists bBP; exact (nbound_mono w 0 _ _ Hw0 B1)).
    assert (G2 : fin 0 (jP (tot P l K'))) by (exists bBP; exact (nbound_mono w 0 _ _ Hw0 B1')).
    assert (M : fin 0 (fmul (lU P l Ub K) (lU P l Ub K'))) by (apply fin_fmul; [lra | assumption | assumption]).
    assert (D : fin 0 (fsub (jP (tot P l K')) (jP (tot P l K)))) by (apply fin_fsub; assumption).
    assert (MD : fin 0 (fmul (fmul (lU P l Ub K) (lU P l Ub K')) (fsub (jP (tot P l K')) (jP (tot P l K)))))
      by (apply fin_fmul; [lra | assumption | assumption]).
    destruct (fin_fsub 0 _ _ F2 F1) as [Ma Ha]. destruct (fin_fscal 0 (-1) _ MD) as [Mb Hb].
    apply (canon_feq _ _ Ma Mb); [apply fsub_canon; assumption
      | apply fscal_canon, fmul_canon; [apply fmul_canon; assumption | apply fsub_canon; assumption]
      | exact Ha | exact Hb |].
    intros t p. pose proof (ball_Uinv K t p IK) as I1. pose proof (ball_Uinv K' t p IK') as I2.
    rewrite (feval_fsub' t p _ _ F2 F1), (feval_fscal' t p _ _ MD), (feval_fmul' t p _ _ M D),
      (feval_fmul' t p _ _ F1 F2), (feval_fsub' t p _ _ G2 G1).
    unfold lj in I1, I2.
    set (u := feval (lU P l Ub K) t p) in *. set (u' := feval (lU P l Ub K') t p) in *.
    set (b := feval (jP (tot P l K)) t p) in *. set (b' := feval (jP (tot P l K')) t p) in *.
    replace u' with (u' * (b * u)) at 1 by (rewrite I1; ring).
    replace u with (u * (b' * u')) at 2 by (rewrite I2; ring).
    ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)). unfold LU.
  replace (h * (Ubb * Ubb * LBP)) with (Rabs (-1) * (Ubb * Ubb * (h * LBP))) by (rewrite Rabs_m1'; ring).
  apply nbound_fscal. apply (nbound_fmul w _ _ _ _ Hw0); [apply (nbound_fmul w _ _ _ _ Hw0); assumption | exact D1].
Qed.

Lemma lp_W : lp (lW P l Ub K) (lW P l Ub K') cW LW.
Proof. exact (lp_mul _ _ _ _ _ _ _ _ lp_KR lp_U). Qed.

Lemma lp_model :
  lp (mRR (lDV P l Ub K)) (mRR (lDV P l Ub K')) cmRR LmRR /\ lp (mRZ (lDV P l Ub K)) (mRZ (lDV P l Ub K')) cmRZ LmRZ /\
  lp (mZR (lDV P l Ub K)) (mZR (lDV P l Ub K')) cmZR LmZR /\ lp (mZZ (lDV P l Ub K)) (mZZ (lDV P l Ub K')) cmZZ LmZZ.
Proof.
  destruct lp_Dall as [DRR [DRZ [DPR [DPZ [DZR DZZ]]]]]. destruct lp_Ball as [BR [BP BZ]].
  pose proof lp_W as W. pose proof lp_U as U.
  pose proof (lp_sub _ _ _ _ _ _ _ _ U (lp_mul _ _ _ _ _ _ _ _ W (lp_mul _ _ _ _ _ _ _ _ U DPR))) as WR.
  pose proof (lp_scal (-1) _ _ _ _ (lp_mul _ _ _ _ _ _ _ _ W (lp_mul _ _ _ _ _ _ _ _ U DPZ))) as WZ.
  unfold lDV, lWR, lWZ, lj. cbn [mRR mRZ mZR mZZ].
  refine (conj _ (conj _ (conj _ _))); apply lp_add; apply lp_mul; assumption.
Qed.

Lemma lp_nb (u u' : fser) (A L M N : R) : lp u u' A L -> A <= M -> L <= N ->
  nbound w M u /\ nbound w M u' /\ nbound w (h * N) (fsub u' u).
Proof.
  intros [_ [_ [B1 [B2 B3]]]] HM HN.
  refine (conj (nbound_le w _ _ _ HM B1) (conj (nbound_le w _ _ _ HM B2) (nbound_le w _ _ _ _ B3))).
  apply Rmult_le_compat_l; assumption.
Qed.

(** The change of the derivative of the velocity between two tori of the ball. *)
Theorem ball_lipD : mbound w (h * bLD) (KAMDiff.msub (DVf (lmodel P l Ub) K') (DVf (lmodel P l Ub) K)).
Proof.
  destruct lp_model as [A1 [A2 [A3 A4]]]. cbn [DVf lmodel]. unfold KAMDiff.msub. cbn [mRR mRZ mZR mZZ].
  unfold bLD.
  refine (conj _ (conj _ (conj _ _))).
  - exact (proj2 (proj2 (lp_nb _ _ _ _ _ _ A1 (Rle_refl _) (Rle_trans _ _ _ (Rmax_l _ _) (Rmax_l _ _))))).
  - exact (proj2 (proj2 (lp_nb _ _ _ _ _ _ A2 (Rle_refl _) (Rle_trans _ _ _ (Rmax_r _ _) (Rmax_l _ _))))).
  - exact (proj2 (proj2 (lp_nb _ _ _ _ _ _ A3 (Rle_refl _) (Rle_trans _ _ _ (Rmax_l _ _) (Rmax_r _ _))))).
  - exact (proj2 (proj2 (lp_nb _ _ _ _ _ _ A4 (Rle_refl _) (Rle_trans _ _ _ (Rmax_r _ _) (Rmax_r _ _))))).
Qed.

(** The change of the density. *)
Theorem ball_lipS : nbound w (h * LBP) (fsub (Sf (lmodel P l Ub) K') (Sf (lmodel P l Ub) K)).
Proof. destruct lp_Ball as [_ [[_ [_ [_ [_ D]]]] _]]. exact D. Qed.

End Pair.

(** * The second-order remainder of the velocity *)

Section Taylor2.

Variables (K K' : vf) (h : R).
Hypothesis IK : inb K.
Hypothesis IK' : inb K'.
Hypothesis Hh : 0 <= h.
Hypothesis Hhh : h <= hm.
Hypothesis HD : vbound w h (vsub K' K).

Theorem ball_taylor :
  vbound w (h * h * bM2) (vsub (vsub (Vf (lmodel P l Ub) K') (Vf (lmodel P l Ub) K))
                                (mapp (DVf (lmodel P l Ub) K) (vsub K' K))).
Proof.
  destruct (tot_canon' K IK) as [C1 [C2 [C3 [C4 [C5 [_ [C7 [C8 [_ [C10 [C11 _]]]]]]]]]]].
  destruct (tot_canon' K' IK') as [D1 [D2 [D3 _]]].
  destruct (tot_fin' K IK) as [F1 [F2 [F3 [F4 [F5 [_ [F7 [F8 [_ [F10 [F11 _]]]]]]]]]]].
  destruct (tot_fin' K' IK') as [G1 [G2 [G3 _]]].
  pose proof (C_U K IK) as CU1. pose proof (C_U K' IK') as CU2.
  assert (FU1 : fin w (lU P l Ub K)) by (exists Ubb; exact (ball_U K IK)).
  assert (FU2 : fin w (lU P l Ub K')) by (exists Ubb; exact (ball_U K' IK')).
  destruct (inb_fin K IK) as [FR FZ]. destruct (inb_fin K' IK') as [FR' FZ'].
  destruct IK as [[CR CZ] _]. destruct IK' as [[CR' CZ'] _].
  assert (CdR : is_canon (tdR K K')) by (unfold tdR; apply fsub_canon; assumption).
  assert (CdZ : is_canon (tdZ K K')) by (unfold tdZ; apply fsub_canon; assumption).
  assert (FdR : fin w (tdR K K')) by (unfold tdR; apply fin_fsub; assumption).
  assert (FdZ : fin w (tdZ K K')) by (unfold tdZ; apply fin_fsub; assumption).
  destruct (pair_r2 K K' h IK IK' Hh Hhh HD) as [R1 [R2 R3]].
  destruct (lp_Ball K K' h IK IK' Hh Hhh HD) as [[_ [_ [BR [BR' DBR]]]] [[_ [_ [BP [BP' DBP]]]] [_ [_ [BZ [BZ' DBZ]]]]]].
  destruct (lp_U K K' h IK IK' Hh Hhh HD) as [_ [_ [U1 [U2 DU]]]].
  pose proof (ball_KR K IK) as KR.
  pose proof (fun t p => ball_Uinv K t p IK) as I1. pose proof (fun t p => ball_Uinv K' t p IK') as I2.
  pose proof (proj1 HD) as NdR.
  assert (Gen : forall (B B' BRd BZd : fser) (T2 LB bB : R),
            is_canon B -> is_canon B' -> is_canon BRd -> is_canon BZd ->
            fin w B -> fin w B' -> fin w BRd -> fin w BZd ->
            nbound w bB B -> nbound w (h * LB) (fsub B' B) ->
            nbound w (h * h * T2) (fsub (fsub B' B) (fadd (fmul BRd (fsub (vR K') (vR K))) (fmul BZd (fsub (vZ K') (vZ K))))) ->
            nbound w (h * h * (kRb * Ubb * T2 + kRb * bB * (Ubb * Ubb * (Ubb * (LBP * LBP)) + Ubb * Ubb * cR2R)
                               + Ubb * Ubb * LBP * bB + Ubb * LB + kRb * (Ubb * Ubb * LBP) * LB
                               + hm * (Ubb * Ubb * LBP) * LB))
              (gLHS (vR K) (vR K') (vZ K) (vZ K') (lU P l Ub K) (lU P l Ub K') (jP_R (tot P l K)) (jP_Z (tot P l K))
                    B B' BRd BZd)).
  { intros B B' BRd BZd T2 LB bB CB CB' CBR CBZ FB FB' FBR FBZ NB NDB NR2.
    apply (nbound_feq w _ _ _ (feq_sym _ _ (gX_feq w (vR K) (vR K') (vZ K) (vZ K') (lU P l Ub K) (lU P l Ub K')
             (jP (tot P l K)) (jP (tot P l K')) (jP_R (tot P l K)) (jP_Z (tot P l K)) B B' BRd BZd Hw
             CR CR' CZ CZ' CU1 CU2 C2 D2 C7 C8 CB CB' CBR CBZ FR FR' FZ FZ' FU1 FU2 F2 G2 F7 F8 FB FB' FBR FBZ I1 I2))).
    exact (gX_nb w (vR K) (vR K') (vZ K) (vZ K') (lU P l Ub K) (lU P l Ub K') (jP (tot P l K)) (jP (tot P l K'))
             (jP_R (tot P l K)) (jP_Z (tot P l K)) B B' BRd BZd Hw h hm kRb Ubb bB LB LBP T2 cR2R Hh Hhh
             KR U1 U2 NB NdR DU NDB DBP NR2 R2). }
  cbn [Vf DVf lmodel]. unfold lV, lDV, lW, lWR, lWZ, mapp, vsub, lj. cbn [vR vZ mRR mRZ mZR mZZ].
  pose proof (Gen _ _ _ _ cR2R LBR bBR C1 D1 C4 C5 F1 G1 F4 F5 BR DBR R1) as NR.
  pose proof (Gen _ _ _ _ cR2Z LBZ bBZ C3 D3 C10 C11 F3 G3 F10 F11 BZ DBZ R3) as NZ.
  unfold gLHS in NR, NZ.
  split.
  - refine (nbound_le w _ _ _ _ NR). apply Rmult_le_compat_l; [nra |]. unfold bM2, TMR, LU. apply Rmax_l.
  - refine (nbound_le w _ _ _ _ NZ). apply Rmult_le_compat_l; [nra |]. unfold bM2, TMZ, LU. apply Rmax_r.
Qed.

End Taylor2.

(** The bounds of the model on one torus of the ball. *)
Theorem ball_model (K : vf) : inb K ->
  vbound w bMV (Vf (lmodel P l Ub) K) /\ mbound w bDV (DVf (lmodel P l Ub) K) /\
  nbound w bBP (Sf (lmodel P l Ub) K) /\ vbound w bS1 (GSf (lmodel P l Ub) K).
Proof.
  intros IK. pose proof (vsub_self w 0 K (Rle_refl 0)) as H0.
  destruct (lp_model K K 0 IK IK (Rle_refl 0) ltac:(lra) H0) as [A1 [A2 [A3 A4]]].
  destruct (lp_Ball K K 0 IK IK (Rle_refl 0) ltac:(lra) H0) as [BR [BP BZ]].
  destruct (lp_Dall K K 0 IK IK (Rle_refl 0) ltac:(lra) H0) as [_ [_ [DPR [DPZ _]]]].
  pose proof (lp_W K K 0 IK IK (Rle_refl 0) ltac:(lra) H0) as W.
  cbn [Vf DVf Sf GSf lmodel]. unfold lV, lGS, lS, lj. cbn [vR vZ mRR mRZ mZR mZZ].
  unfold vbound, mbound, bMV, bDV, bS1.
  refine (conj (conj _ _) (conj (conj _ (conj _ (conj _ _))) (conj _ (conj _ _)))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ (lp_mul 0 _ _ _ _ _ _ _ _ W BR) (Rmax_l _ _) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ (lp_mul 0 _ _ _ _ _ _ _ _ W BZ) (Rmax_r _ _) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ A1 (Rle_trans _ _ _ (Rmax_l _ _) (Rmax_l _ _)) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ A2 (Rle_trans _ _ _ (Rmax_r _ _) (Rmax_l _ _)) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ A3 (Rle_trans _ _ _ (Rmax_l _ _) (Rmax_r _ _)) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ A4 (Rle_trans _ _ _ (Rmax_r _ _) (Rmax_r _ _)) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ BP (Rle_refl _) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ DPR (Rmax_l _ _) (Rle_refl _))).
  - exact (proj1 (lp_nb 0 (Rle_refl 0) _ _ _ _ _ _ DPZ (Rmax_r _ _) (Rle_refl _))).
Qed.

End Const.
