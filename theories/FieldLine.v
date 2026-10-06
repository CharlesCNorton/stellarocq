(** The field-line flow of the symmetric coil field, as the model of the KAM
    iteration.

    Along a torus K, parametrised by theta and the toroidal angle phi, a
    field line satisfies dR/dphi = R B_R / B_phi and dZ/dphi = R B_Z / B_phi.
    With the field the jet [tot] of the base sources, U the Newton inverse of
    B_phi from a seed ([lU]) and W = R U, the velocity is V = (W B_R, W B_Z)
    ([lV]) and its derivative in (R, Z) at fixed phi is [lDV]; the density
    preserved by the flow is sigma = B_phi ([lS]), with gradient
    (dB_phi/dR, dB_phi/dZ) ([lGS]). Along a torus that is stellarator
    symmetric and of the field period, with every seed converging, the model
    satisfies the chain rule in theta ([line_chain_R], [line_chain_Z]) and
    the Liouville identity ([line_liou]), and its velocity is the field-line
    velocity of the coil field [coilB] ([line_sem]). Its values have the
    canonical form, the period and the parities that the iteration uses. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer KAMStep Hypotheses Invariance CoilSym
  FieldKern FieldFam FieldModel.
Local Open Scope R_scope.

Section Line.

Variables (P : Z) (l : list (src * fser)) (Ub : fser).

Definition lj (K : vf) : cjet := tot P l K.
Definition lU (K : vf) : fser := finv (jP (lj K)) Ub.
Definition lW (K : vf) : fser := fmul (vR K) (lU K).
Definition lWR (K : vf) : fser := fsub (lU K) (fmul (lW K) (fmul (lU K) (jP_R (lj K)))).
Definition lWZ (K : vf) : fser := fscal (-1) (fmul (lW K) (fmul (lU K) (jP_Z (lj K)))).

Definition lV (K : vf) : vf := mkvf (fmul (lW K) (jR (lj K))) (fmul (lW K) (jZ (lj K))).
Definition lDV (K : vf) : mf :=
  mkmf (fadd (fmul (lWR K) (jR (lj K))) (fmul (lW K) (jR_R (lj K))))
       (fadd (fmul (lWZ K) (jR (lj K))) (fmul (lW K) (jR_Z (lj K))))
       (fadd (fmul (lWR K) (jZ (lj K))) (fmul (lW K) (jZ_R (lj K))))
       (fadd (fmul (lWZ K) (jZ (lj K))) (fmul (lW K) (jZ_Z (lj K)))).
Definition lS (K : vf) : fser := jP (lj K).
Definition lGS (K : vf) : vf := mkvf (jP_R (lj K)) (jP_Z (lj K)).

Definition lmodel : fmodel := {| Vf := lV ; DVf := lDV ; Sf := lS ; GSf := lGS |}.

(** The seed of an inverse makes its Newton iteration converge. *)
Definition inv_ok (rho : R) (u y0 : fser) : Prop :=
  exists Mu Y0 q, nbound rho Mu u /\ nbound rho Y0 y0 /\ 0 <= q < 1 /\ nbound rho q (fsub fone (fmul u y0)).

(** * Canonical form, period and parity *)

Section Classes.

Variable K : vf.
Hypothesis HP : (0 < P)%Z.

Lemma lj_canon : vcanon K -> List.Forall (fun sy => is_canon (snd sy)) l -> is_canon Ub ->
  jcanon (lj K) /\ is_canon (lU K).
Proof.
  intros CK Cl CU. pose proof (tot_canon P l K HP CK Cl) as C. split; [exact C |].
  apply finv_canon; [exact (proj1 (proj2 C)) | exact CU].
Qed.

Theorem line_canon : vcanon K -> List.Forall (fun sy => is_canon (snd sy)) l -> is_canon Ub ->
  vcanon (lV K) /\ mcanon (lDV K) /\ is_canon (lS K) /\ vcanon (lGS K).
Proof.
  intros CK Cl CU. destruct (lj_canon CK Cl CU) as [C CUK].
  destruct C as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 [C10 [C11 C12]]]]]]]]]]].
  destruct CK as [CR CZ].
  unfold vcanon, mcanon, lV, lDV, lS, lGS, lWR, lWZ, lW. cbn [vR vZ mRR mRZ mZR mZZ].
  conjs; repeat (first [assumption | apply fmul_canon | apply fsub_canon | apply fadd_canon
                       | apply fscal_canon]).
Qed.

Theorem line_per : is_per P Ub -> vper P K ->
  vper P (lV K) /\ mper P (lDV K) /\ is_per P (lS K).
Proof.
  intros QU [QR QZ].
  destruct (tot_per P l K) as [Q1 [Q2 [Q3 [Q4 [Q5 [Q6 [Q7 [Q8 [Q9 [Q10 [Q11 Q12]]]]]]]]]]].
  assert (QUK : is_per P (lU K)) by (apply finv_per; assumption).
  unfold vper, mper, lV, lDV, lS, lWR, lWZ, lW. cbn [vR vZ mRR mRZ mZR mZZ].
  conjs; repeat (first [assumption | apply (fmul_per P HP) | apply fsub_per | apply fadd_per
                       | apply fscal_per]).
Qed.

Theorem line_par : is_even Ub -> vsym K ->
  vasym (lV K) /\ mpar (lDV K) /\ is_even (lS K).
Proof.
  intros EU [ER OZ].
  destruct (tot_par P l K) as [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]].
  assert (EUK : is_even (lU K)) by (apply finv_even; assumption).
  assert (EW : is_even (lW K)) by (apply fmul_even_even; assumption).
  assert (EWR : is_even (lWR K)).
  { unfold lWR. apply fsub_even; [exact EUK |]. apply fmul_even_even; [exact EW |].
    apply fmul_even_even; assumption. }
  assert (OWZ : is_odd (lWZ K)).
  { unfold lWZ. apply fscal_odd. apply fmul_even_odd; [exact EW |]. apply fmul_even_odd; assumption. }
  unfold vasym, mpar, lV, lDV, lS. cbn [vR vZ mRR mRZ mZR mZZ].
  refine (conj (conj _ _) (conj (conj _ (conj _ (conj _ _))) _)).
  - apply fmul_even_odd; assumption.
  - apply fmul_even_even; assumption.
  - apply fadd_odd; [apply fmul_even_odd | apply fmul_even_odd]; assumption.
  - apply fadd_even; [apply fmul_odd_odd | apply fmul_even_even]; assumption.
  - apply fadd_even; [apply fmul_even_even | apply fmul_even_even]; assumption.
  - apply fadd_odd; [apply fmul_odd_even | apply fmul_even_odd]; assumption.
  - exact A2.
Qed.

End Classes.

(** * The identities along a torus *)

Section AtK.

Variables (rho : R) (K : vf).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.
Hypothesis HU : inv_ok rho (jP (lj K)) Ub.

Lemma J_fin : jfin rho (lj K).
Proof. exact (tot_fin P rho K l Hr FK Hl). Qed.

Lemma J_chain : jchain K (lj K).
Proof. exact (tot_chain P rho K l HP Hr FK SK QK Hl). Qed.

Lemma U_fin : fin rho (lU K).
Proof.
  destruct HU as [Mu [Y0 [q [Hu [Hy [Hq He]]]]]].
  exists (Y0 + inv_eps Y0 q 0). exact (nbound_finv rho (Rlt_le _ _ Hr) _ _ Y0 q Hy Hq He).
Qed.

Lemma U_inv (t p : R) : feval (jP (lj K)) t p * feval (lU K) t p = 1.
Proof.
  destruct HU as [Mu [Y0 [q [Hu [Hy [Hq He]]]]]].
  exact (feval_finv rho (Rlt_le _ _ Hr) _ _ Mu Y0 q Hu Hy Hq He t p).
Qed.

Lemma f0 (u : fser) : fin rho u -> fin 0 u.
Proof. apply fin_mono. lra. Qed.

Lemma fin_dt_mul (u v : fser) (t p : R) : fin rho u -> fin rho v ->
  feval (dt (fmul u v)) t p = feval (dt u) t p * feval v t p + feval u t p * feval (dt v) t p.
Proof. intros [Mu Hu] [Mv Hv]. exact (feval_dt_fmul rho Mu Mv u v t p Hr Hu Hv). Qed.

Lemma dt_const (u : fser) (c t p : R) : fin rho u -> (forall t p, feval u t p = c) -> feval (dt u) t p = 0.
Proof.
  intros [M HM] Hc. pose proof (feval_dt rho M u p t Hr HM) as D.
  apply (is_derive_ext _ (fun _ => c)) in D; [| intros y; apply Hc].
  apply is_derive_unique in D. rewrite Derive_const in D. rewrite <- D. reflexivity.
Qed.

Lemma dt_U (t p : R) :
  feval (dt (lU K)) t p = - (feval (lU K) t p * feval (lU K) t p * feval (dt (jP (lj K))) t p).
Proof.
  destruct J_fin as [_ [F2 _]]. pose proof U_fin as FU.
  assert (C : forall t p, feval (fmul (jP (lj K)) (lU K)) t p = 1).
  { intros t' p'. rewrite (feval_fmul' t' p' _ _ (f0 _ F2) (f0 _ FU)). apply U_inv. }
  pose proof (dt_const _ 1 t p (fin_fmul rho _ _ (Rlt_le _ _ Hr) F2 FU) C) as D.
  rewrite (fin_dt_mul _ _ t p F2 FU) in D.
  pose proof (U_inv t p) as E.
  set (b := feval (jP (lj K)) t p) in *. set (u := feval (lU K) t p) in *.
  set (db := feval (dt (jP (lj K))) t p) in *. set (du := feval (dt (lU K)) t p) in *.
  replace du with (du * (b * u)) by (rewrite E; ring).
  replace (du * (b * u)) with (u * (db * u + b * du) - u * u * db) by ring.
  rewrite D. ring.
Qed.

Ltac fin_side :=
  repeat (first [assumption | apply f0; assumption
                | apply fin_fmul; [lra | |] | apply fin_fsub | apply fin_fadd | apply fin_fscal]).

Ltac ev_side :=
  repeat (first [rewrite feval_fadd' by fin_side | rewrite feval_fsub' by fin_side
                | rewrite feval_fmul' by fin_side | rewrite feval_fscal' by fin_side]).

Theorem line_chain_R (t p : R) :
  feval (dt (vR (Vf lmodel K))) t p
  = feval (mRR (DVf lmodel K)) t p * feval (vR (ktng K)) t p
    + feval (mRZ (DVf lmodel K)) t p * feval (vZ (ktng K)) t p.
Proof.
  destruct J_fin as [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 F12]]]]]]]]]]].
  destruct (J_chain t p) as [C1 [C2 [C3 _]]].
  pose proof U_fin as FU. destruct FK as [FKR FKZ].
  assert (FW : fin rho (lW K)) by (apply fin_fmul; [lra | exact FKR | exact FU]).
  cbn [Vf DVf lmodel lV lDV vR vZ mRR mRZ]. unfold ktng, vdt. cbn [vR vZ].
  rewrite (fin_dt_mul _ _ t p FW F1). unfold lWR, lWZ, lW.
  rewrite (fin_dt_mul _ _ t p FKR FU), dt_U, C1, C2.
  ev_side. ring.
Qed.

Theorem line_chain_Z (t p : R) :
  feval (dt (vZ (Vf lmodel K))) t p
  = feval (mZR (DVf lmodel K)) t p * feval (vR (ktng K)) t p
    + feval (mZZ (DVf lmodel K)) t p * feval (vZ (ktng K)) t p.
Proof.
  destruct J_fin as [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 F12]]]]]]]]]]].
  destruct (J_chain t p) as [C1 [C2 [C3 _]]].
  pose proof U_fin as FU. destruct FK as [FKR FKZ].
  assert (FW : fin rho (lW K)) by (apply fin_fmul; [lra | exact FKR | exact FU]).
  cbn [Vf DVf lmodel lV lDV vR vZ mZR mZZ]. unfold ktng, vdt. cbn [vR vZ].
  rewrite (fin_dt_mul _ _ t p FW F3). unfold lWR, lWZ, lW.
  rewrite (fin_dt_mul _ _ t p FKR FU), dt_U, C3, C2.
  ev_side. ring.
Qed.

Theorem line_liou (om t p : R) :
  feval (lc om (Sf lmodel K)) t p
  = feval (vdot (GSf lmodel K) (kerr lmodel om K)) t p - feval (Sf lmodel K) t p * feval (mtr (DVf lmodel K)) t p.
Proof.
  destruct J_fin as [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 F12]]]]]]]]]]].
  destruct (J_chain t p) as [_ [C2 [_ [_ [C5 [_ C7]]]]]].
  pose proof U_fin as FU. pose proof (U_inv t p) as E. destruct FK as [FKR FKZ].
  assert (FW : fin rho (lW K)) by (apply fin_fmul; [lra | exact FKR | exact FU]).
  assert (FlR : fin 0 (lc om (vR K))).
  { replace 0 with (rho - rho) by ring. apply fin_lc; [exact Hr | exact FKR]. }
  assert (FlZ : fin 0 (lc om (vZ K))).
  { replace 0 with (rho - rho) by ring. apply fin_lc; [exact Hr | exact FKZ]. }
  unfold kerr. cbn [Sf GSf DVf Vf lmodel]. unfold vdot, mtr, vsub, vlc, lS, lGS, lDV, lV.
  cbn [vR vZ mRR mZZ].
  destruct F2 as [M2 H2]. destruct FKR as [MR HR]. destruct FKZ as [MZ HZ].
  rewrite (feval_lc om rho M2 _ t p Hr H2), C2, C5.
  unfold lWR, lWZ, lW.
  assert (FKR : fin rho (vR K)) by (exists MR; exact HR).
  assert (FKZ : fin rho (vZ K)) by (exists MZ; exact HZ).
  assert (F2 : fin rho (jP (lj K))) by (exists M2; exact H2).
  ev_side.
  rewrite (feval_lc om rho MR _ t p Hr HR), (feval_lc om rho MZ _ t p Hr HZ).
  assert (Hb : feval (jP (lj K)) t p <> 0) by (intros Z0; rewrite Z0 in E; lra).
  assert (Eu : feval (lU K) t p = / feval (jP (lj K)) t p) by (field_simplify_eq; [lra | exact Hb]).
  assert (Ephi : feval (jP_phi (lj K)) t p
                 = - feval (jR (lj K)) t p - feval (vR K) t p * (feval (jR_R (lj K)) t p + feval (jZ_Z (lj K)) t p))
    by lra.
  rewrite Eu, Ephi. field. exact Hb.
Qed.

(** The model's velocity is the field-line velocity of the coil field, with the
    toroidal angle itself as the second angle. *)
Theorem line_sem (t p : R) :
  B_phi (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p) <> 0 /\
  1 * feval (vR (Vf lmodel K)) t p
    = feval (vR K) t p * B_R (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p)
      / B_phi (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p) /\
  1 * feval (vZ (Vf lmodel K)) t p
    = feval (vR K) t p * B_Z (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p)
      / B_phi (coilB P l) (feval (vR K) t p) (p / 1) (feval (vZ K) t p).
Proof.
  replace (p / 1) with p by field.
  destruct (tot_val P rho K l HP Hr FK SK QK Hl t p) as [VR [VP VZ]].
  change (tot P l K) with (lj K) in VR, VP, VZ.
  rewrite <- VR, <- VP, <- VZ.
  destruct J_fin as [F1 [F2 [F3 _]]]. pose proof U_fin as FU. pose proof (U_inv t p) as E.
  destruct FK as [FKR FKZ].
  assert (Hb : feval (jP (lj K)) t p <> 0) by (intros Z0; rewrite Z0 in E; lra).
  assert (Eu : feval (lU K) t p = / feval (jP (lj K)) t p) by (field_simplify_eq; [lra | exact Hb]).
  cbn [Vf lmodel lV vR vZ]. unfold lW. ev_side. rewrite Eu.
  refine (conj Hb (conj _ _)); field; exact Hb.
Qed.

End AtK.

End Line.
