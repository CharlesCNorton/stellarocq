(** An invariant torus of the symmetric coil field, from data along a first
    torus.

    The field-line model of the coil set of P periods with the base sources
    of l ([lmodel]) satisfies every hypothesis the KAM iteration of
    KAMIter.v places on its model, on every strip of the iteration and every
    torus within r of the first torus K0, once the sources converge there
    from their seeds and the inverse of B_phi from its seed: the classes of
    its values come from FieldLine.v, its identities from FieldLine.v with
    the sources of FieldBall.v, and its bounds from FieldConst.v, with the
    data along K0 read on the widest strip and the norm of cos p and sin p
    there bounding it on every narrower one. What remains are the conditions
    on the first torus itself; under them the coil field [coilB P l] has an
    invariant torus within 2 kP eps0 of K0 ([field_kam]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer KAMStep KAMBound KAMDiff KAMUpdate
  KAMScale KAMIter Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTaylor FieldTotal
  FieldBall FieldLine FieldConst.
From Stellarocq Require TorusLine.
Local Open Scope R_scope.

Section FieldKAM.

Variables (P : Z) (l : list (src * fser)) (Ub : fser) (om gamma gammaA : R) (K0 : vf) (g0 b : fser)
  (w0 d0 r : R) (A0 G0 N0 T0 tau0 eps0 xA xG xN xB xTm xtau : R).
Variables (r10 r20 r30 MY MD0 th0 y00 : src * fser -> R).
Variables (bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0 : R).

Definition khm : R := 2 * r.
Definition kcs : R := wt w0 0 1.
Definition kdr1 (sy : src * fser) : R := r10 sy + r * kcs.
Definition kdr2 (sy : src * fser) : R := r20 sy + r * kcs.
Definition kdr3 (sy : src * fser) : R := r30 sy + r.
Definition kdyb (sy : src * fser) : R := byb r (r10 sy) (r20 sy) (r30 sy) (MY sy) (th0 sy) kcs.

Definition kS : R := bBP P l r khm kcs kdr1 kdr2 kdr3 kdyb bP0 dPR0 dPZ0.
Definition kS1 : R := bS1 P l r khm kcs kdr1 kdr2 kdr3 kdyb dPR0 dPZ0.
Definition kDV : R := bDV P l r khm kcs kdr1 kdr2 kdr3 kdyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0.
Definition kMV : R := bMV P l r khm kcs kdr1 kdr2 kdr3 kdyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0.
Definition kM2 : R := bM2 P l r khm kcs kdr1 kdr2 kdr3 kdyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0.
Definition kLD : R := bLD P l r khm kcs kdr1 kdr2 kdr3 kdyb bR0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0.
Definition kLS : R := LBP P l r khm kcs kdr1 kdr2 kdr3 kdyb dPR0 dPZ0.

(** The constants of the iteration. *)
Definition kc : kcon :=
  {| cA := xA ; cG := xG ; cN := xN ; cB := xB ; cS := kS ; cS1 := kS1 ; cD := kDV ; cMV := kMV ; cM2 := kM2 ;
     cTm := xTm ; ctau := xtau ; cLS := kLS ; cLD := kLD |}.

Definition kF : fmodel := lmodel P l Ub.

(** * The data along the first torus *)

Hypothesis HP : (0 < P)%Z.
Hypothesis Hd0 : 0 < d0.
Hypothesis Hw0 : 6 * d0 < w0.
Hypothesis Hr0 : 0 < r.
Hypothesis FK0 : vfin w0 K0.
Hypothesis C0 : vcanon K0.
Hypothesis S0 : vsym K0.
Hypothesis Q0 : vper P K0.
Hypothesis Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Hypothesis CU : is_canon Ub.
Hypothesis EU : is_even Ub.
Hypothesis QU : is_per P Ub.

(** Each source along K0, and its conditions on the ball. *)
Definition src0 (sy : src * fser) : Prop :=
  nbound w0 (r10 sy) (fr1 (fst sy) K0) /\ nbound w0 (r20 sy) (fr2 (fst sy) K0) /\
  nbound w0 (r30 sy) (fr3 (fst sy) K0) /\ nbound w0 (MY sy) (snd sy) /\
  nbound w0 (MD0 sy) (fq (fst sy) K0) /\
  nbound w0 (th0 sy) (fsub fone (fmul (fq (fst sy) K0) (fmul (snd sy) (snd sy)))) /\
  y00 sy <= feval (snd sy) 0 0 /\
  bth r (r10 sy) (r20 sy) (r30 sy) (MY sy) (th0 sy) kcs < 1 /\
  inv_eps (MY sy) (bth r (r10 sy) (r20 sy) (r30 sy) (MY sy) (th0 sy) kcs) 0 < y00 sy /\
  khm * khm * tT1 khm (kdr1 sy) (kdr2 sy) (kdr3 sy) (kdyb sy) kcs < 1 /\
  khm * tP1 khm (kdr1 sy) (kdr2 sy) (kdr3 sy) (kdyb sy) kcs / 2
    + khm * khm * tRB khm (kdr1 sy) (kdr2 sy) (kdr3 sy) (kdyb sy) kcs < 1.

Hypothesis Hsrc : List.Forall src0 l.

Hypothesis BR0 : nbound w0 bR0 (jR (tot P l K0)).
Hypothesis BP0 : nbound w0 bP0 (jP (tot P l K0)).
Hypothesis BZ0 : nbound w0 bZ0 (jZ (tot P l K0)).
Hypothesis DRR0 : nbound w0 dRR0 (jR_R (tot P l K0)).
Hypothesis DRZ0 : nbound w0 dRZ0 (jR_Z (tot P l K0)).
Hypothesis DPR0 : nbound w0 dPR0 (jP_R (tot P l K0)).
Hypothesis DPZ0 : nbound w0 dPZ0 (jP_Z (tot P l K0)).
Hypothesis DZR0 : nbound w0 dZR0 (jZ_R (tot P l K0)).
Hypothesis DZZ0 : nbound w0 dZZ0 (jZ_Z (tot P l K0)).
Hypothesis KR0 : nbound w0 kR0 (vR K0).
Hypothesis BUb : nbound w0 MU Ub.
Hypothesis TU0 : nbound w0 thU0 (fsub fone (fmul (jP (tot P l K0)) Ub)).
Hypothesis HthU : thU P l r khm kcs kdr1 kdr2 kdr3 kdyb dPR0 dPZ0 MU thU0 < 1.

(** * On every strip of the iteration *)

Lemma winf_pos' : 0 < winf w0 d0. Proof. unfold winf. lra. Qed.

Lemma w0_pos : 0 < w0. Proof. lra. Qed.

Section Strip.

Variable w : R.
Hypothesis Hw : 0 < w.
Hypothesis Hww : w <= w0.

Lemma Hw' : 0 <= w. Proof. lra. Qed.

Lemma mono (M : R) (u : fser) : nbound w0 M u -> nbound w M u.
Proof. apply nbound_mono. exact Hww. Qed.

Lemma cs_w : nbound w kcs cosf /\ nbound w kcs sinf.
Proof.
  assert (E : wt w 0 1 <= kcs).
  { unfold kcs, wt. apply exp_mono. apply Rmult_le_compat_r; [apply msize_nonneg | exact Hww]. }
  split; apply (nbound_le w (wt w 0 1)); try exact E; [apply nb_cosf | apply nb_sinf].
Qed.

Lemma FK0_w : vfin w K0. Proof. exact (vfin_mono w0 w K0 Hww FK0). Qed.

Lemma inb_vfin (K : vf) : inb P w r K0 K -> vfin w K.
Proof.
  intros [_ [_ [_ [HR HZ]]]]. destruct FK0_w as [[M1 H1] [M2 H2]].
  split; [exists (M1 + r) | exists (M2 + r)];
    [apply (nbound_feq w _ _ _ (feq_sym _ _ (add_mid_feq (vR K) (vR K0))))
    | apply (nbound_feq w _ _ _ (feq_sym _ _ (add_mid_feq (vZ K) (vZ K0))))];
    apply nbound_fadd; assumption.
Qed.

Lemma Hball_w : forall K, inb P w r K0 K ->
  List.Forall (fun sy => src_ok w khm kcs K sy (kdr1 sy) (kdr2 sy) (kdr3 sy) (kdyb sy)) l.
Proof.
  intros K IK. pose proof IK as [CK [_ [_ HD]]].
  apply Forall_forall. intros sy I. rewrite Forall_forall in Hsrc, Cl.
  destruct (Hsrc sy I) as [B1 [B2 [B3 [BY [BD [BT [H00 [Hth [Hpos [S1 S2]]]]]]]]]].
  destruct sy as [sc Y]. cbn [fst snd] in *.
  exact (ball_src sc Y K0 K w r (r10 (sc, Y)) (r20 (sc, Y)) (r30 (sc, Y)) (MY (sc, Y)) (MD0 (sc, Y))
           (th0 (sc, Y)) (y00 (sc, Y)) Hw (Rlt_le _ _ Hr0) FK0_w (inb_vfin K IK) C0 CK (Cl (sc, Y) I) HD
           (mono _ _ B1) (mono _ _ B2) (mono _ _ B3) (mono _ _ BY) (mono _ _ BD) (mono _ _ BT) H00
           kcs cs_w Hth Hpos khm S1 S2).
Qed.

Lemma Hhm : 2 * r <= khm. Proof. unfold khm. lra. Qed.

Ltac ball_args :=
  exact (P) || idtac.

(** The results of FieldConst.v at this strip. *)
Lemma bm (K : vf) : inb P w r K0 K ->
  vbound w kMV (Vf kF K) /\ mbound w kDV (DVf kF K) /\ nbound w kS (Sf kF K) /\ vbound w kS1 (GSf kF K).
Proof.
  intros IK.
  exact (ball_model P l Ub w r khm kcs K0 kdr1 kdr2 kdr3 kdyb HP Hw (Rlt_le _ _ Hr0) Hhm cs_w FK0_w C0 S0 Q0 Cl CU
           Hball_w bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0
           (mono _ _ BR0) (mono _ _ BP0) (mono _ _ BZ0) (mono _ _ DRR0) (mono _ _ DRZ0) (mono _ _ DPR0)
           (mono _ _ DPZ0) (mono _ _ DZR0) (mono _ _ DZZ0) (mono _ _ KR0) (mono _ _ BUb) (mono _ _ TU0) HthU K IK).
Qed.

Lemma bt (K K' : vf) (h : R) : inb P w r K0 K -> inb P w r K0 K' -> 0 <= h -> h <= khm -> vbound w h (vsub K' K) ->
  vbound w (h * h * kM2) (vsub (vsub (Vf kF K') (Vf kF K)) (mapp (DVf kF K) (vsub K' K))).
Proof.
  intros IK IK' Hh Hhh HD.
  exact (ball_taylor P l Ub w r khm kcs K0 kdr1 kdr2 kdr3 kdyb HP Hw (Rlt_le _ _ Hr0) Hhm cs_w FK0_w C0 S0 Q0 Cl CU
           Hball_w bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0
           (mono _ _ BR0) (mono _ _ BP0) (mono _ _ BZ0) (mono _ _ DRR0) (mono _ _ DRZ0) (mono _ _ DPR0)
           (mono _ _ DPZ0) (mono _ _ DZR0) (mono _ _ DZZ0) (mono _ _ KR0) (mono _ _ BUb) (mono _ _ TU0) HthU
           K K' h IK IK' Hh Hhh HD).
Qed.

Lemma bls (K K' : vf) (h : R) : inb P w r K0 K -> inb P w r K0 K' -> 0 <= h -> h <= khm -> vbound w h (vsub K' K) ->
  nbound w (h * kLS) (fsub (Sf kF K') (Sf kF K)).
Proof.
  intros IK IK' Hh Hhh HD.
  exact (ball_lipS P l Ub w r khm kcs K0 kdr1 kdr2 kdr3 kdyb HP Hw (Rlt_le _ _ Hr0) Hhm cs_w FK0_w C0 S0 Q0 Cl
           Hball_w bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0
           (mono _ _ BR0) (mono _ _ BP0) (mono _ _ BZ0) (mono _ _ DRR0) (mono _ _ DRZ0) (mono _ _ DPR0)
           (mono _ _ DPZ0) (mono _ _ DZR0) (mono _ _ DZZ0) K K' h IK IK' Hh Hhh HD).
Qed.

Lemma bld (K K' : vf) (h : R) : inb P w r K0 K -> inb P w r K0 K' -> 0 <= h -> h <= khm -> vbound w h (vsub K' K) ->
  mbound w (h * kLD) (KAMDiff.msub (DVf kF K') (DVf kF K)).
Proof.
  intros IK IK' Hh Hhh HD.
  exact (ball_lipD P l Ub w r khm kcs K0 kdr1 kdr2 kdr3 kdyb HP Hw (Rlt_le _ _ Hr0) Hhm cs_w FK0_w C0 S0 Q0 Cl CU
           Hball_w bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 kR0 MU thU0
           (mono _ _ BR0) (mono _ _ BP0) (mono _ _ BZ0) (mono _ _ DRR0) (mono _ _ DRZ0) (mono _ _ DPR0)
           (mono _ _ DPZ0) (mono _ _ DZR0) (mono _ _ DZZ0) (mono _ _ KR0) (mono _ _ BUb) (mono _ _ TU0) HthU
           K K' h IK IK' Hh Hhh HD).
Qed.

Lemma binv (K : vf) : inb P w r K0 K -> inv_ok w (jP (lj P l K)) Ub.
Proof.
  intros IK.
  exact (ball_inv P l Ub w r khm kcs K0 kdr1 kdr2 kdr3 kdyb HP Hw (Rlt_le _ _ Hr0) Hhm cs_w FK0_w C0 S0 Q0 Cl CU
           Hball_w bR0 bP0 bZ0 dRR0 dRZ0 dPR0 dPZ0 dZR0 dZZ0 MU thU0
           (mono _ _ BR0) (mono _ _ BP0) (mono _ _ BZ0) (mono _ _ DRR0) (mono _ _ DRZ0) (mono _ _ DPR0)
           (mono _ _ DPZ0) (mono _ _ DZR0) (mono _ _ DZZ0) (mono _ _ BUb) (mono _ _ TU0) HthU K IK).
Qed.

Lemma bsrcs (K : vf) : inb P w r K0 K -> srcs_ok w l K.
Proof.
  intros IK. unfold srcs_ok. eapply Forall_impl; [| exact (Hball_w K IK)]. intros sy [Q [Y0 _]]. exact (conj Q Y0).
Qed.

End Strip.

(** * The hypotheses of the iteration *)

Lemma good_strip (w : R) (K : vf) : good P K0 w0 d0 r w K -> 0 < w /\ w <= w0 /\ inb P w r K0 K.
Proof.
  intros [H1 [H2 [H3 [H4 [H5 H6]]]]]. pose proof winf_pos'.
  refine (conj _ (conj H2 (conj H3 (conj H4 (conj H5 H6))))). lra.
Qed.

(** A step of any size between two tori of the ball is at most 2 r. *)
Lemma step_cap (w : R) (K K' : vf) (Pb : R) : 0 < w -> w <= w0 ->
  inb P w r K0 K -> inb P w r K0 K' -> vbound w Pb (vsub K' K) ->
  exists h, 0 <= h /\ h <= khm /\ h <= Pb /\ vbound w h (vsub K' K).
Proof.
  intros Hw Hww IK IK' HB. pose proof (inb_pair P w r K0 K K' IK IK') as H2.
  pose proof (nbound_nonneg _ _ _ (proj1 HB)) as HP0.
  destruct (Rle_or_lt Pb khm) as [Hle | Hlt].
  - exists Pb. refine (conj HP0 (conj Hle (conj (Rle_refl _) HB))).
  - exists khm. unfold khm in *. refine (conj _ (conj (Rle_refl _) (conj _ H2))); lra.
Qed.

Lemma MQV' : forall w K, good P K0 w0 d0 r w K -> vper P (Vf kF K).
Proof. intros w K G. destruct (good_strip w K G) as [_ [_ [_ [_ [QK _]]]]]. exact (proj1 (line_per P l Ub K HP QU QK)). Qed.

Lemma MQD' : forall w K, good P K0 w0 d0 r w K -> mper P (DVf kF K).
Proof.
  intros w K G. destruct (good_strip w K G) as [_ [_ [_ [_ [QK _]]]]]. exact (proj1 (proj2 (line_per P l Ub K HP QU QK))).
Qed.

Lemma MQS' : forall w K, good P K0 w0 d0 r w K -> is_per P (Sf kF K).
Proof.
  intros w K G. destruct (good_strip w K G) as [_ [_ [_ [_ [QK _]]]]]. exact (proj2 (proj2 (line_per P l Ub K HP QU QK))).
Qed.

Lemma MC' (w : R) (K : vf) : good P K0 w0 d0 r w K ->
  vcanon (Vf kF K) /\ mcanon (DVf kF K) /\ is_canon (Sf kF K) /\ vcanon (GSf kF K).
Proof. intros G. destruct (good_strip w K G) as [_ [_ [CK _]]]. exact (line_canon P l Ub K HP CK Cl CU). Qed.

Lemma MP' (w : R) (K : vf) : good P K0 w0 d0 r w K -> vasym (Vf kF K) /\ mpar (DVf kF K) /\ is_even (Sf kF K).
Proof. intros G. destruct (good_strip w K G) as [_ [_ [_ [SK _]]]]. exact (line_par P l Ub K EU SK). Qed.

Lemma MB' (w : R) (K : vf) : good P K0 w0 d0 r w K ->
  vbound w kMV (Vf kF K) /\ mbound w kDV (DVf kF K) /\ nbound w kS (Sf kF K) /\ vbound w kS1 (GSf kF K).
Proof. intros G. destruct (good_strip w K G) as [Hw [Hww IK]]. exact (bm w Hw Hww K IK). Qed.

Lemma Mchain' (w : R) (K : vf) : good P K0 w0 d0 r w K -> forall t p,
  (feval (dt (vR (Vf kF K))) t p
   = feval (mRR (DVf kF K)) t p * feval (vR (ktng K)) t p + feval (mRZ (DVf kF K)) t p * feval (vZ (ktng K)) t p) /\
  (feval (dt (vZ (Vf kF K))) t p
   = feval (mZR (DVf kF K)) t p * feval (vR (ktng K)) t p + feval (mZZ (DVf kF K)) t p * feval (vZ (ktng K)) t p).
Proof.
  intros G t p. destruct (good_strip w K G) as [Hw [Hww IK]]. pose proof IK as [_ [SK [QK _]]].
  split; [exact (line_chain_R P l Ub w K HP Hw (inb_vfin w Hww K IK) SK QK (bsrcs w Hw Hww K IK)
                   (binv w Hw Hww K IK) t p)
         | exact (line_chain_Z P l Ub w K HP Hw (inb_vfin w Hww K IK) SK QK (bsrcs w Hw Hww K IK)
                   (binv w Hw Hww K IK) t p)].
Qed.

Lemma Mliou' (w : R) (K : vf) : good P K0 w0 d0 r w K -> forall t p,
  feval (lc om (Sf kF K)) t p
  = feval (vdot (GSf kF K) (kerr kF om K)) t p - feval (Sf kF K) t p * feval (mtr (DVf kF K)) t p.
Proof.
  intros G t p. destruct (good_strip w K G) as [Hw [Hww IK]]. pose proof IK as [_ [SK [QK _]]].
  exact (line_liou P l Ub w K HP Hw (inb_vfin w Hww K IK) SK QK (bsrcs w Hw Hww K IK) (binv w Hw Hww K IK) om t p).
Qed.

Lemma kM2_nn : 0 <= kM2.
Proof.
  assert (Hw : 0 < w0) by exact w0_pos.
  pose proof (inb_K0 P w0 r K0 (Rlt_le _ _ Hr0) C0 S0 Q0) as I0.
  assert (H2 : vbound w0 khm (vsub K0 K0)) by (apply vsub_self; unfold khm; lra).
  pose proof (bt w0 Hw (Rle_refl _) K0 K0 khm I0 I0 ltac:(unfold khm; lra) (Rle_refl _) H2) as [B _].
  pose proof (nbound_nonneg _ _ _ B) as N. unfold khm in N.
  assert (Q : 0 < 2 * r * (2 * r)) by nra.
  destruct (Rle_or_lt 0 kM2) as [A | A]; [exact A |]. nra.
Qed.

Lemma kLS_nn : 0 <= kLS.
Proof.
  assert (Hw : 0 < w0) by exact w0_pos.
  pose proof (inb_K0 P w0 r K0 (Rlt_le _ _ Hr0) C0 S0 Q0) as I0.
  assert (H2 : vbound w0 khm (vsub K0 K0)) by (apply vsub_self; unfold khm; lra).
  pose proof (bls w0 Hw (Rle_refl _) K0 K0 khm I0 I0 ltac:(unfold khm; lra) (Rle_refl _) H2) as B.
  pose proof (nbound_nonneg _ _ _ B) as N. unfold khm in N.
  assert (Q : 0 < 2 * r) by lra.
  destruct (Rle_or_lt 0 kLS) as [A | A]; [exact A |]. nra.
Qed.

Lemma kLD_nn : 0 <= kLD.
Proof.
  assert (Hw : 0 < w0) by exact w0_pos.
  pose proof (inb_K0 P w0 r K0 (Rlt_le _ _ Hr0) C0 S0 Q0) as I0.
  assert (H2 : vbound w0 khm (vsub K0 K0)) by (apply vsub_self; unfold khm; lra).
  pose proof (bld w0 Hw (Rle_refl _) K0 K0 khm I0 I0 ltac:(unfold khm; lra) (Rle_refl _) H2) as [B _].
  pose proof (nbound_nonneg _ _ _ B) as N. unfold khm in N.
  assert (Q : 0 < 2 * r) by lra.
  destruct (Rle_or_lt 0 kLD) as [A | A]; [exact A |]. nra.
Qed.

Lemma Mtaylor' : forall w K K', good P K0 w0 d0 r w K -> good P K0 w0 d0 r w K' -> forall Pb, vbound w Pb (vsub K' K) ->
  vbound w (kM2 * (Pb * Pb)) (vsub (vsub (Vf kF K') (Vf kF K)) (mapp (DVf kF K) (vsub K' K))).
Proof.
  intros w K K' G G' Pb HB. destruct (good_strip w K G) as [Hw [Hww IK]]. destruct (good_strip w K' G') as [_ [_ IK']].
  destruct (step_cap w K K' Pb Hw Hww IK IK' HB) as [h [Hh [Hhh [HhP HD]]]].
  destruct (bt w Hw Hww K K' h IK IK' Hh Hhh HD) as [A1 A2]. pose proof kM2_nn.
  assert (E : h * h * kM2 <= kM2 * (Pb * Pb)).
  { rewrite (Rmult_comm kM2). apply Rmult_le_compat_r; [lra |]. apply Rmult_le_compat; lra. }
  split; apply (nbound_le w (h * h * kM2)); assumption.
Qed.

Lemma MlipS' : forall w K K', good P K0 w0 d0 r w K -> good P K0 w0 d0 r w K' -> forall Pb, vbound w Pb (vsub K' K) ->
  nbound w (kLS * Pb) (fsub (Sf kF K') (Sf kF K)).
Proof.
  intros w K K' G G' Pb HB. destruct (good_strip w K G) as [Hw [Hww IK]]. destruct (good_strip w K' G') as [_ [_ IK']].
  destruct (step_cap w K K' Pb Hw Hww IK IK' HB) as [h [Hh [Hhh [HhP HD]]]].
  pose proof (bls w Hw Hww K K' h IK IK' Hh Hhh HD) as A. pose proof kLS_nn.
  apply (nbound_le w (h * kLS)); [rewrite (Rmult_comm kLS); apply Rmult_le_compat_r; lra | exact A].
Qed.

Lemma MlipD' : forall w K K', good P K0 w0 d0 r w K -> good P K0 w0 d0 r w K' -> forall Pb, vbound w Pb (vsub K' K) ->
  mbound w (kLD * Pb) (KAMDiff.msub (DVf kF K') (DVf kF K)).
Proof.
  intros w K K' G G' Pb HB. destruct (good_strip w K G) as [Hw [Hww IK]]. destruct (good_strip w K' G') as [_ [_ IK']].
  destruct (step_cap w K K' Pb Hw Hww IK IK' HB) as [h [Hh [Hhh [HhP HD]]]].
  destruct (bld w Hw Hww K K' h IK IK' Hh Hhh HD) as [A1 [A2 [A3 A4]]]. pose proof kLD_nn.
  assert (E : h * kLD <= kLD * Pb) by (rewrite (Rmult_comm kLD); apply Rmult_le_compat_r; lra).
  refine (conj _ (conj _ (conj _ _))); apply (nbound_le w (h * kLD)); assumption.
Qed.

Lemma Msem' : forall w K, good P K0 w0 d0 r w K -> forall t p,
  B_phi (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p) <> 0 /\
  1 * feval (vR (Vf kF K)) t p
    = feval (vR K) t p * B_R (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p)
      / B_phi (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p) /\
  1 * feval (vZ (Vf kF K)) t p
    = feval (vR K) t p * B_Z (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p)
      / B_phi (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p).
Proof.
  intros w K G t p. destruct (good_strip w K G) as [Hw [Hww IK]]. pose proof IK as [_ [SK [QK _]]].
  exact (line_sem P l Ub w K HP Hw (inb_vfin w Hww K IK) SK QK (bsrcs w Hw Hww K IK) (binv w Hw Hww K IK) t p).
Qed.

Lemma kB_nn : 0 <= kMV /\ 0 <= kDV /\ 0 <= kS /\ 0 <= kS1.
Proof.
  pose proof (inb_K0 P w0 r K0 (Rlt_le _ _ Hr0) C0 S0 Q0) as I0.
  destruct (bm w0 w0_pos (Rle_refl _) K0 I0) as [[A _] [[B _] [C [D _]]]].
  exact (conj (nbound_nonneg _ _ _ A) (conj (nbound_nonneg _ _ _ B) (conj (nbound_nonneg _ _ _ C)
           (nbound_nonneg _ _ _ D)))).
Qed.

(** * The invariant torus *)

Hypothesis Hdio : dioph_per P om gamma.
Hypothesis Hgam : 0 < gamma <= 1.
Hypothesis HdioA : diophantine1 om gammaA.
Hypothesis HgamA : 0 < gammaA <= 1.
Hypothesis HA : 0 <= xA.
Hypothesis HG : 0 <= xG.
Hypothesis HN : 0 <= xN.
Hypothesis HB : 0 <= xB.
Hypothesis HTm : 0 <= xTm.
Hypothesis Hctau : 0 < xtau.
Hypothesis Heps0 : 0 <= eps0.
Hypothesis HAE : 0 < itA gamma d0 kc.
Hypothesis Hsmall : itA gamma d0 kc * 16 * eps0 <= / 2.

Hypothesis Cg0 : is_canon g0.
Hypothesis Pg0 : is_even g0.
Hypothesis Cb : is_canon b.
Hypothesis Pb : is_odd b.
Hypothesis Qg0 : is_per P g0.
Hypothesis Qb : is_per P b.
Hypothesis BB0 : nbound w0 xB b.
Hypothesis BA0 : vbound w0 A0 (ktng K0).
Hypothesis BG0 : nbound w0 G0 g0.
Hypothesis BN0 : vbound w0 N0 (knrm K0 g0 b).
Hypothesis BE0 : vbound w0 eps0 (kerr kF om K0).
Hypothesis Hframe0 : forall t p,
  feval (Sf kF K0) t p * feval (vdot (ktng K0) (ktng K0)) t p * feval g0 t p = 1.
Hypothesis BT0 : nbound (w0 - d0) T0 (ktwist kF om K0 g0 b).
Hypothesis Htau0 : tau0 <= Rabs (fc (ktwist kF om K0 g0 b) 0 0).
Hypothesis HcA : A0 + 2 * (kdA kc gamma d0 * eps0) <= xA.
Hypothesis HcG : G0 + 2 * (kdG kc gamma d0 * eps0) <= xG.
Hypothesis HcN : N0 + 2 * (kdN kc gamma d0 * eps0) <= xN.
Hypothesis HcT : T0 + 2 * (kT kc om gamma d0 * eps0) <= xTm.
Hypothesis Hrr : 2 * (kP kc gamma d0 * eps0) <= r.
Hypothesis Hctau2 : xtau <= tau0 - 2 * (kT kc om gamma d0 * eps0).
Hypothesis Hsm_a0 : kdA kc gamma d0 * eps0 <= xA.
Hypothesis Hsm_q0 : xG * (kU kc gamma d0 * eps0) <= / 2.
Hypothesis Hsm_g0 : kdG kc gamma d0 * eps0 <= xG.
Hypothesis Hsm_n0 : kdN kc gamma d0 * eps0 <= xN.
Hypothesis Hsm_w0 : kdW kc om gamma d0 * eps0 <= kW kc om d0.

(** The coil field has an invariant torus within 2 kP eps0 of the first torus,
    in R and in Z, at every pair of angles. *)
Theorem field_kam :
  exists KR KZ : R -> R -> R,
    invariant_torus (coilB P l) (torus_of KR KZ) /\
    forall theta phi,
      Rabs (KR theta phi - feval (vR K0) theta phi) <= 2 * (kP kc gamma d0 * eps0) /\
      Rabs (KZ theta phi - feval (vZ K0) theta phi) <= 2 * (kP kc gamma d0 * eps0).
Proof.
  destruct kB_nn as [NMV [NDV [NS NS1]]].
  pose proof (fun w K G => proj1 (MC' w K G)) as MCV.
  pose proof (fun w K G => proj1 (proj2 (MC' w K G))) as MCD.
  pose proof (fun w K G => proj1 (proj2 (proj2 (MC' w K G)))) as MCS.
  pose proof (fun w K G => proj2 (proj2 (proj2 (MC' w K G)))) as MCG.
  pose proof (fun w K G => proj1 (MP' w K G)) as MPV.
  pose proof (fun w K G => proj1 (proj2 (MP' w K G))) as MPD.
  pose proof (fun w K G => proj2 (proj2 (MP' w K G))) as MPS.
  pose proof (fun w K G => proj1 (MB' w K G)) as MBV.
  pose proof (fun w K G => proj1 (proj2 (MB' w K G))) as MBD.
  pose proof (fun w K G => proj1 (proj2 (proj2 (MB' w K G)))) as MBS.
  pose proof (fun w K G => proj2 (proj2 (proj2 (MB' w K G)))) as MBG.
  pose proof (fun w K G t p => proj1 (Mchain' w K G t p)) as McR.
  pose proof (fun w K G t p => proj2 (Mchain' w K G t p)) as McZ.
  pose proof (kam_invariant_torus kF P om gamma gammaA K0 g0 b w0 d0 r kc A0 G0 N0 T0 tau0 eps0
                HP Hdio Hgam HdioA HgamA Hd0 Hw0 HA HG HN HB NS NS1 NDV kM2_nn HTm Hctau kLS_nn kLD_nn Heps0 HAE Hsmall
                MQV' MQD' MQS' MCV MPV MCD MPD MCS MPS MCG MBV MBD MBS MBG McR McZ Mliou' Mtaylor' MlipS' MlipD'
                C0 S0 Cg0 Pg0 Cb Pb Q0 Qg0 Qb FK0 BB0 BA0 BG0 BN0 BE0 Hframe0 BT0 Htau0 HcA HcG HcN HcT Hrr Hctau2
                Hsm_a0 Hsm_q0 Hsm_g0 Hsm_n0 Hsm_w0 (coilB P l) 1 Rlt_0_1 Msem') as IT.
  pose proof (kam_close kF P om gamma gammaA K0 g0 b w0 d0 r kc A0 G0 N0 T0 tau0 eps0
                HP Hdio Hgam HdioA HgamA Hd0 Hw0 HA HG HN HB NS NS1 NDV kM2_nn HTm Hctau kLS_nn kLD_nn Heps0 HAE Hsmall
                MQV' MQD' MQS' MCV MPV MCD MPD MCS MPS MCG MBV MBD MBS MBG McR McZ Mliou' Mtaylor' MlipS' MlipD'
                C0 S0 Cg0 Pg0 Cb Pb Q0 Qg0 Qb FK0 BB0 BA0 BG0 BN0 BE0 Hframe0 BT0 Htau0 HcA HcG HcN HcT Hrr Hctau2
                Hsm_a0 Hsm_q0 Hsm_g0 Hsm_n0 Hsm_w0 1) as CL.
  eexists; eexists. split; [exact IT |]. intros theta phi.
  destruct (CL theta phi) as [A1 A2]. rewrite Rmult_1_l in A1, A2. exact (conj A1 A2).
Qed.

(** The same torus is a pair of Fourier families on a strip, solving the
    invariance equation with rotation om, so that it carries the field lines
    of TorusLine.fourier_torus_line. *)
Theorem field_kam_fourier :
  exists KR KZ : R -> R -> R,
    TorusLine.fourier_torus (coilB P l) KR KZ om /\
    forall theta phi,
      Rabs (KR theta phi - feval (vR K0) theta phi) <= 2 * (kP kc gamma d0 * eps0) /\
      Rabs (KZ theta phi - feval (vZ K0) theta phi) <= 2 * (kP kc gamma d0 * eps0).
Proof.
  destruct kB_nn as [NMV [NDV [NS NS1]]].
  pose proof (fun w K G => proj1 (MC' w K G)) as MCV.
  pose proof (fun w K G => proj1 (proj2 (MC' w K G))) as MCD.
  pose proof (fun w K G => proj1 (proj2 (proj2 (MC' w K G)))) as MCS.
  pose proof (fun w K G => proj2 (proj2 (proj2 (MC' w K G)))) as MCG.
  pose proof (fun w K G => proj1 (MP' w K G)) as MPV.
  pose proof (fun w K G => proj1 (proj2 (MP' w K G))) as MPD.
  pose proof (fun w K G => proj2 (proj2 (MP' w K G))) as MPS.
  pose proof (fun w K G => proj1 (MB' w K G)) as MBV.
  pose proof (fun w K G => proj1 (proj2 (MB' w K G))) as MBD.
  pose proof (fun w K G => proj1 (proj2 (proj2 (MB' w K G)))) as MBS.
  pose proof (fun w K G => proj2 (proj2 (proj2 (MB' w K G)))) as MBG.
  pose proof (fun w K G t p => proj1 (Mchain' w K G t p)) as McR.
  pose proof (fun w K G t p => proj2 (Mchain' w K G t p)) as McZ.
  pose proof (kam_fourier kF P om gamma gammaA K0 g0 b w0 d0 r kc A0 G0 N0 T0 tau0 eps0
                HP Hdio Hgam HdioA HgamA Hd0 Hw0 HA HG HN HB NS NS1 NDV kM2_nn HTm Hctau kLS_nn kLD_nn Heps0 HAE Hsmall
                MQV' MQD' MQS' MCV MPV MCD MPD MCS MPS MCG MBV MBD MBS MBG McR McZ Mliou' Mtaylor' MlipS' MlipD'
                C0 S0 Cg0 Pg0 Cb Pb Q0 Qg0 Qb FK0 BB0 BA0 BG0 BN0 BE0 Hframe0 BT0 Htau0 HcA HcG HcN HcT Hrr Hctau2
                Hsm_a0 Hsm_q0 Hsm_g0 Hsm_n0 Hsm_w0 (coilB P l) 1 Rlt_0_1 Msem') as IT.
  pose proof (kam_close kF P om gamma gammaA K0 g0 b w0 d0 r kc A0 G0 N0 T0 tau0 eps0
                HP Hdio Hgam HdioA HgamA Hd0 Hw0 HA HG HN HB NS NS1 NDV kM2_nn HTm Hctau kLS_nn kLD_nn Heps0 HAE Hsmall
                MQV' MQD' MQS' MCV MPV MCD MPD MCS MPS MCG MBV MBD MBS MBG McR McZ Mliou' Mtaylor' MlipS' MlipD'
                C0 S0 Cg0 Pg0 Cb Pb Q0 Qg0 Qb FK0 BB0 BA0 BG0 BN0 BE0 Hframe0 BT0 Htau0 HcA HcG HcN HcT Hrr Hctau2
                Hsm_a0 Hsm_q0 Hsm_g0 Hsm_n0 Hsm_w0 1) as CL.
  rewrite Rmult_1_l in IT.
  eexists; eexists. split; [exact IT |]. intros theta phi.
  destruct (CL theta phi) as [A1 A2]. rewrite Rmult_1_l in A1, A2. exact (conj A1 A2).
Qed.

End FieldKAM.
