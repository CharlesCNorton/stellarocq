(** One source on the ball of tori about the first torus.

    From the norms of the distance families of a source along the first
    torus K0, of its seed Y, of q along K0 and of the defect 1 - q Y^2 there,
    every torus K within r of K0 has distance families within r (times the
    norm of cos p for the first two) of those along K0, q within r E1 of q
    along K0 ([ball_q]), and a defect at most the defect along K0 plus r E1
    |Y|^2. When that is below one, the inverse square root converges along K
    from the same seed, has norm at most |Y| + inv_eps, and is positive
    once the value of Y at the origin exceeds inv_eps ([ball_src]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer Hypotheses Invariance CoilSym
  FieldKern FieldFam FieldModel FieldTaylor FieldTotal.
Local Open Scope R_scope.

Lemma feq_ev (w : R) (u v : fser) (f g : R -> R -> R) :
  0 <= w -> is_canon u -> is_canon v -> ev w u f -> ev w v g -> (forall t p, f t p = g t p) -> feq u v.
Proof.
  intros Hw Cu Cv [Fu Eu] [Fv Ev] H.
  destruct (fin_mono w 0 u Hw Fu) as [Mu Bu]. destruct (fin_mono w 0 v Hw Fv) as [Mv Bv].
  apply (canon_feq u v Mu Mv Cu Cv Bu Bv). intros t p. rewrite Eu, Ev. apply H.
Qed.

Section Ball.

Variables (sc : src) (Y : fser) (K0 K : vf) (w r : R).
Variables (r10 r20 r30 MY MD0 th0 y00 : R).
Hypothesis Hw : 0 < w.
Hypothesis Hr : 0 <= r.
Hypothesis FK0 : vfin w K0.
Hypothesis FK : vfin w K.
Hypothesis CK0 : vcanon K0.
Hypothesis CK : vcanon K.
Hypothesis CY : is_canon Y.
Hypothesis HD : vbound w r (vsub K K0).
Hypothesis B10 : nbound w r10 (fr1 sc K0).
Hypothesis B20 : nbound w r20 (fr2 sc K0).
Hypothesis B30 : nbound w r30 (fr3 sc K0).
Hypothesis BY : nbound w MY Y.
Hypothesis BD0 : nbound w MD0 (fq sc K0).
Hypothesis BT0 : nbound w th0 (fsub fone (fmul (fq sc K0) (fmul Y Y))).
Hypothesis HY00 : y00 <= feval Y 0 0.

Lemma Hw0 : 0 <= w. Proof. lra. Qed.

Variable cs : R.
Hypothesis Hcs : nbound w cs cosf /\ nbound w cs sinf.

Lemma ball_dR : nbound w r (fsub (vR K) (vR K0)). Proof. exact (proj1 HD). Qed.
Lemma ball_dZ : nbound w r (fsub (vZ K) (vZ K0)). Proof. exact (proj2 HD). Qed.

Ltac canon_leaf :=
  destruct CK as [CKR CKZ]; destruct CK0 as [CKR0 CKZ0]; canon_tac.

Lemma ball_r1 : nbound w (r10 + r * cs) (fr1 sc K).
Proof.
  assert (E : feq (fr1 sc K) (fadd (fr1 sc K0) (fmul (fsub (vR K) (vR K0)) cosf))).
  { eapply (feq_ev w); [exact Hw0 | | | exact (E_r1 sc K w Hw FK)
      | exact (ev_fadd _ Hw0 _ _ _ _ (E_r1 sc K0 w Hw FK0)
                 (ev_fmul _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ (ev_self w _ (proj1 FK)) (ev_self w _ (proj1 FK0)))
                    (ev_cosf w Hw0))) |].
    - unfold fr1, fx1. canon_leaf.
    - unfold fr1, fx1. canon_leaf.
    - intros t p. cbv beta. unfold kx1. ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)).
  exact (nbound_fadd w _ _ _ _ B10 (nbound_fmul w _ _ _ _ Hw0 ball_dR (proj1 Hcs))).
Qed.

Lemma ball_r2 : nbound w (r20 + r * cs) (fr2 sc K).
Proof.
  assert (E : feq (fr2 sc K) (fadd (fr2 sc K0) (fmul (fsub (vR K) (vR K0)) sinf))).
  { eapply (feq_ev w); [exact Hw0 | | | exact (E_r2 sc K w Hw FK)
      | exact (ev_fadd _ Hw0 _ _ _ _ (E_r2 sc K0 w Hw FK0)
                 (ev_fmul _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ (ev_self w _ (proj1 FK)) (ev_self w _ (proj1 FK0)))
                    (ev_sinf w Hw0))) |].
    - unfold fr2, fx2. canon_leaf.
    - unfold fr2, fx2. canon_leaf.
    - intros t p. cbv beta. unfold kx2. ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)).
  exact (nbound_fadd w _ _ _ _ B20 (nbound_fmul w _ _ _ _ Hw0 ball_dR (proj2 Hcs))).
Qed.

Lemma ball_r3 : nbound w (r30 + r) (fr3 sc K).
Proof.
  assert (E : feq (fr3 sc K) (fadd (fr3 sc K0) (fsub (vZ K) (vZ K0)))).
  { intros m n. unfold fr3, fsub, fadd, fscal. simpl. split; ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)). exact (nbound_fadd w _ _ _ _ B30 ball_dZ).
Qed.

(** q along K is q along K0 plus e. *)
Lemma ball_q_feq : feq (fq sc K) (fadd (fq sc K0) (tee sc K0 K)).
Proof.
  eapply (feq_ev w); [exact Hw0 | | | exact (E_q sc K w Hw FK)
    | exact (ev_fadd _ Hw0 _ _ _ _ (E_q sc K0 w Hw FK0) (E_tee sc K0 K w Hw FK0 FK)) |].
  - unfold fq, fr1, fr2, fr3, fx1, fx2. canon_leaf.
  - unfold fq, fr1, fr2, fr3, fx1, fx2, tee, tx1, tx2, tdR, tdZ. canon_leaf.
  - intros t p. cbv beta. unfold qk, kx1, kx2. ring.
Qed.

Definition bE1 : R := tE1 r r10 r20 r30 cs.

Lemma ball_tee : nbound w (r * bE1) (tee sc K0 K).
Proof. exact (nb_tee sc K0 K w Hw r r r10 r20 r30 Hr (Rle_refl r) HD B10 B20 B30 cs Hcs). Qed.

Lemma ball_q : nbound w (MD0 + r * bE1) (fq sc K).
Proof. apply (nbound_feq w _ _ _ (feq_sym _ _ ball_q_feq)). exact (nbound_fadd w _ _ _ _ BD0 ball_tee). Qed.

Definition bth : R := th0 + r * bE1 * (MY * MY).

Lemma ball_def : nbound w bth (fsub fone (fmul (fq sc K) (fmul Y Y))).
Proof.
  assert (E : feq (fsub fone (fmul (fq sc K) (fmul Y Y)))
                  (fsub (fsub fone (fmul (fq sc K0) (fmul Y Y))) (fmul (tee sc K0 K) (fmul Y Y)))).
  { pose proof (ev_self w Y (ex_intro _ MY BY)) as EY. pose proof (ev_fconst w 1) as E1.
    eapply (feq_ev w); [exact Hw0 | | |
      exact (ev_fsub _ Hw0 _ _ _ _ E1 (ev_fmul _ Hw0 _ _ _ _ (E_q sc K w Hw FK) (ev_fmul _ Hw0 _ _ _ _ EY EY)))
    | exact (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ E1
               (ev_fmul _ Hw0 _ _ _ _ (E_q sc K0 w Hw FK0) (ev_fmul _ Hw0 _ _ _ _ EY EY)))
               (ev_fmul _ Hw0 _ _ _ _ (E_tee sc K0 K w Hw FK0 FK) (ev_fmul _ Hw0 _ _ _ _ EY EY))) |].
    - apply fsub_canon; [apply fone_canon |]. apply fmul_canon; [| apply fmul_canon; exact CY].
      unfold fq, fr1, fr2, fr3, fx1, fx2. canon_leaf.
    - apply fsub_canon; [apply fsub_canon; [apply fone_canon |] |];
        (apply fmul_canon; [| apply fmul_canon; exact CY]).
      + unfold fq, fr1, fr2, fr3, fx1, fx2. canon_leaf.
      + unfold tee, tx1, tx2, tdR, tdZ, fr1, fr2, fr3, fx1, fx2. canon_leaf.
    - intros t p. cbv beta. unfold qk, kx1, kx2. ring. }
  apply (nbound_feq w _ _ _ (feq_sym _ _ E)). unfold bth.
  exact (nbound_fsub w _ _ _ _ BT0 (nbound_fmul w _ _ _ _ Hw0 ball_tee (nbound_fmul w _ _ _ _ Hw0 BY BY))).
Qed.

Hypothesis Hth : bth < 1.

Lemma bth_nn : 0 <= bth. Proof. exact (nbound_nonneg _ _ _ ball_def). Qed.

Lemma ball_isq : isq_ok w (fq sc K) Y.
Proof.
  split; [exact Hw |]. exists (MD0 + r * bE1), MY, bth.
  refine (conj ball_q (conj BY (conj (conj bth_nn Hth) ball_def))).
Qed.

Definition byb : R := MY + inv_eps MY bth 0.

Lemma ball_y : nbound w byb (fy sc Y K).
Proof. exact (nbound_fisqrt w Hw0 _ _ MY bth BY (conj bth_nn Hth) ball_def). Qed.

Hypothesis Hpos : inv_eps MY bth 0 < y00.

Lemma ball_y0 : 0 < feval (fy sc Y K) 0 0.
Proof.
  pose proof (nbound_fisqrt_sub w Hw0 _ _ MY bth BY (conj bth_nn Hth) ball_def) as S.
  pose proof (feval_bound _ _ 0 0 (nbound_mono w 0 _ _ Hw0 S)) as A.
  assert (FY : fin 0 Y) by (exists MY; exact (nbound_mono w 0 _ _ Hw0 BY)).
  assert (Fy : fin 0 (fy sc Y K)) by (destruct (isq_fin w _ _ ball_isq) as [M HM]; exists M;
                                      exact (nbound_mono w 0 _ _ Hw0 HM)).
  unfold fy in *. rewrite (feval_fsub' 0 0 _ _ FY Fy) in A.
  apply Rabs_le_between in A. lra.
Qed.

(** The source on the ball, for steps up to hm. *)
Theorem ball_src (hm : R) :
  hm * hm * tT1 hm (r10 + r * cs) (r20 + r * cs) (r30 + r) byb cs < 1 ->
  hm * tP1 hm (r10 + r * cs) (r20 + r * cs) (r30 + r) byb cs / 2
    + hm * hm * tRB hm (r10 + r * cs) (r20 + r * cs) (r30 + r) byb cs < 1 ->
  src_ok w hm cs K (sc, Y) (r10 + r * cs) (r20 + r * cs) (r30 + r) byb.
Proof.
  intros S1 S2. unfold src_ok. cbn [fst snd].
  exact (conj ball_isq (conj ball_y0 (conj ball_r1 (conj ball_r2 (conj ball_r3 (conj ball_y (conj S1 S2))))))).
Qed.

End Ball.
