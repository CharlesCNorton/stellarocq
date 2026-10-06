(** How the constants of the Newton step grow as the strip's loss halves.

    [dscale j f] says that f is nonnegative and at most doubles j times when
    its argument, the loss delta of the step, is halved. Constants keep the
    property with j = 0, 1 / (e delta) and the inverse of L's
    (1 + 1 / (e delta)) / gamma have it with j = 1, and sums, multiples and
    products keep it ([dscale_plus], [dscale_scal], [dscale_mult]). With the
    constants of the state held fixed along the iteration, the error's
    multiple kE, the move of the twist kT and the move of the torsion's
    wedge kdW have it with j = 4, the correction's multiple kP with j = 2
    and the moves of the tangent, the frame inverse and the normal with
    j = 3 ([ds_kE], [ds_kT], [ds_kdW], [ds_kP], [ds_kdA], [ds_kdG], [ds_kdN]),
    so along deltas delta_0 / 2^n they grow at most as 16^n
    ([dscale_iter]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon KAMFrame KAMVec KAMFin KAMStep KAMBound KAMDiff KAMUpdate.
Local Open Scope R_scope.

Definition dscale (j : nat) (f : R -> R) : Prop :=
  forall d, 0 < d -> 0 <= f d /\ f (d / 2) <= 2 ^ j * f d.

Lemma dscale_const (j : nat) (a : R) : 0 <= a -> dscale j (fun _ => a).
Proof.
  intros Ha d Hd. split; [exact Ha |].
  assert (1 <= 2 ^ j) by (apply pow_R1_Rle; lra). nra.
Qed.

Lemma dscale_plus (j : nat) (f g : R -> R) : dscale j f -> dscale j g -> dscale j (fun d => f d + g d).
Proof.
  intros Hf Hg d Hd. destruct (Hf d Hd) as [F0 F1]. destruct (Hg d Hd) as [G0 G1]. split; lra.
Qed.

Lemma dscale_scal (j : nat) (a : R) (f : R -> R) : 0 <= a -> dscale j f -> dscale j (fun d => a * f d).
Proof.
  intros Ha Hf d Hd. destruct (Hf d Hd) as [F0 F1]. split; [nra |].
  replace (2 ^ j * (a * f d)) with (a * (2 ^ j * f d)) by ring. nra.
Qed.

Lemma dscale_mult (i j : nat) (f g : R -> R) :
  dscale i f -> dscale j g -> dscale (i + j) (fun d => f d * g d).
Proof.
  intros Hf Hg d Hd. destruct (Hf d Hd) as [F0 F1]. destruct (Hg d Hd) as [G0 G1].
  split; [nra |]. rewrite pow_add.
  assert (0 <= f (d / 2)) by (destruct (Hf (d / 2)) as [X _]; [lra | exact X]).
  assert (0 <= g (d / 2)) by (destruct (Hg (d / 2)) as [X _]; [lra | exact X]).
  replace (2 ^ i * 2 ^ j * (f d * g d)) with ((2 ^ i * f d) * (2 ^ j * g d)) by ring.
  apply Rmult_le_compat; assumption.
Qed.

Lemma dscale_mono (i j : nat) (f : R -> R) : (i <= j)%nat -> dscale i f -> dscale j f.
Proof.
  intros Hij Hf d Hd. destruct (Hf d Hd) as [F0 F1]. split; [exact F0 |].
  apply (Rle_trans _ (2 ^ i * f d)); [exact F1 |].
  apply Rmult_le_compat_r; [exact F0 |]. apply Rle_pow; [lra | exact Hij].
Qed.

Lemma dscale_ext (j : nat) (f g : R -> R) : (forall d, 0 < d -> f d = g d) -> dscale j f -> dscale j g.
Proof.
  intros He Hf d Hd. rewrite <- (He d Hd), <- (He (d / 2)) by lra. apply Hf, Hd.
Qed.

Lemma dscale_kdE : dscale 1 kdE.
Proof.
  intros d Hd. unfold kdE.
  assert (He : 0 < exp 1) by apply exp_pos.
  split; [apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; lra |].
  right. simpl. field. lra.
Qed.

Lemma dscale_lc (gamma : R) : 0 < gamma -> dscale 1 (linv_const gamma).
Proof.
  intros Hg d Hd. unfold linv_const.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (Hx : 0 < / (exp 1 * d)) by (apply Rinv_0_lt_compat, Rmult_lt_0_compat; lra).
  split; [apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra] |].
  replace (/ (exp 1 * (d / 2))) with (2 * / (exp 1 * d)) by (field; lra).
  simpl. apply (Rmult_le_reg_r gamma); [exact Hg |].
  unfold Rdiv. rewrite !Rmult_assoc, Rinv_l, !Rmult_1_r by lra. lra.
Qed.

Lemma dscale_iter (j : nat) (f : R -> R) (d0 : R) :
  dscale j f -> 0 < d0 -> forall n, f (d0 / 2 ^ n) <= (2 ^ j) ^ n * f d0.
Proof.
  intros Hf Hd0 n. induction n as [| n IH].
  - simpl. replace (d0 / 1) with d0 by field. lra.
  - assert (Hp : 0 < d0 / 2 ^ n) by (apply Rdiv_lt_0_compat; [exact Hd0 | apply pow_lt; lra]).
    destruct (Hf _ Hp) as [_ H1].
    assert (E : d0 / 2 ^ S n = d0 / 2 ^ n / 2).
    { assert (Hn : 2 ^ n <> 0) by (apply pow_nonzero; lra). simpl. field. exact Hn. }
    rewrite E.
    apply (Rle_trans _ (2 ^ j * f (d0 / 2 ^ n))); [exact H1 |].
    simpl. rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply pow_le; lra | exact IH].
Qed.

(** * The step's constants as the loss halves *)

Section Scale.

Variables (c : kcon) (om gamma : R).
Hypothesis Hgam : 0 < gamma.
Hypothesis HA : 0 <= cA c.
Hypothesis HG : 0 <= cG c.
Hypothesis HN : 0 <= cN c.
Hypothesis HB : 0 <= cB c.
Hypothesis HS : 0 <= cS c.
Hypothesis HS1 : 0 <= cS1 c.
Hypothesis HD : 0 <= cD c.
Hypothesis HM2 : 0 <= cM2 c.
Hypothesis HTm : 0 <= cTm c.
Hypothesis Htau : 0 < ctau c.
Hypothesis HLS : 0 <= cLS c.
Hypothesis HLD : 0 <= cLD c.

Lemma Habs : 0 <= Rabs om. Proof. apply Rabs_pos. Qed.

(** Nonnegativity of products and sums of the constants. *)
Ltac pos := repeat first [assumption | apply Rmult_le_pos | apply Rplus_le_le_0_compat |
                          apply Rlt_le, Rinv_0_lt_compat | apply Habs | exact kappa_pos | lra].

Lemma HkN : 0 <= kN c. Proof. unfold kN. exact HN. Qed.
Lemma HkH1 : 0 <= kH1 c. Proof. unfold kH1, kN. pos. Qed.
Lemma HkH2 : 0 <= kH2 c. Proof. unfold kH2. pos. Qed.

Lemma ds_kW2 : dscale 1 (kW2 c gamma).
Proof.
  apply (dscale_ext _ (fun d => kH2 c * linv_const gamma d)); [intros; unfold kW2; ring |].
  apply dscale_scal; [exact HkH2 | apply dscale_lc, Hgam].
Qed.

Lemma ds_kZ : dscale 1 (kZ c gamma).
Proof.
  apply (dscale_ext _ (fun d => / ctau c * (kH1 c + cTm c * kW2 c gamma d)));
    [intros; unfold kZ; field; lra |].
  apply dscale_scal; [apply Rlt_le, Rinv_0_lt_compat, Htau |].
  apply dscale_plus; [apply dscale_const, HkH1 | apply dscale_scal; [exact HTm | exact ds_kW2]].
Qed.

Lemma ds_kX2 : dscale 1 (kX2 c gamma).
Proof. unfold kX2. apply dscale_plus; [exact ds_kW2 | exact ds_kZ]. Qed.

Lemma ds_kR1 : dscale 1 (kR1 c gamma).
Proof.
  apply (dscale_ext _ (fun d => kH1 c + (cTm c * kW2 c gamma d + cTm c * kZ c gamma d)));
    [intros; unfold kR1; ring |].
  apply dscale_plus; [apply dscale_const, HkH1 |].
  apply dscale_plus; apply dscale_scal; [exact HTm | exact ds_kW2 | exact HTm | exact ds_kZ].
Qed.

Lemma ds_kX1 : dscale 2 (kX1 c gamma).
Proof. unfold kX1. apply (dscale_mult 1 1); [apply dscale_lc, Hgam | exact ds_kR1]. Qed.

Lemma ds_kP : dscale 2 (kP c gamma).
Proof.
  apply (dscale_ext _ (fun d => cA c * kX1 c gamma d + kN c * kX2 c gamma d)); [intros; unfold kP; ring |].
  apply dscale_plus.
  - apply dscale_scal; [exact HA | exact ds_kX1].
  - apply dscale_scal; [exact HkN |]. apply (dscale_mono 1); [lia | exact ds_kX2].
Qed.

Lemma ds_kAl : dscale 1 (kAl c).
Proof.
  apply (dscale_ext _ (fun d => cS c * 2 * kN c * kdE d)); [intros; unfold kAl; ring |].
  apply dscale_scal; [pose proof HkN; pos | exact dscale_kdE].
Qed.

Lemma ds_kBe : dscale 1 (kBe c).
Proof.
  apply (dscale_ext _ (fun d => cS c * 2 * cA c * kdE d)); [intros; unfold kBe; ring |].
  apply dscale_scal; [pos | exact dscale_kdE].
Qed.

Lemma ds_kC : dscale 1 (kC c).
Proof.
  apply (dscale_ext _ (fun d => 2 * cS1 c * (2 * (cA c * cA c)) * cG c + kAl c d)); [intros; unfold kC; ring |].
  apply dscale_plus; [apply dscale_const; pos | exact ds_kAl].
Qed.

Theorem ds_kE : dscale 4 (kE c gamma).
Proof.
  apply (dscale_ext _ (fun d => cA c * (kAl c d * kX1 c gamma d)
                             + kN c * (kBe c d * kX1 c gamma d + kC c d * kX2 c gamma d)
                             + cM2 c * (kP c gamma d * kP c gamma d)));
    [intros; unfold kE; ring |].
  apply dscale_plus; [apply dscale_plus |].
  - apply dscale_scal; [exact HA |]. apply (dscale_mono 3); [lia |].
    apply (dscale_mult 1 2); [exact ds_kAl | exact ds_kX1].
  - apply dscale_scal; [exact HkN |]. apply (dscale_mono 3); [lia |]. apply dscale_plus.
    + apply (dscale_mult 1 2); [exact ds_kBe | exact ds_kX1].
    + apply (dscale_mono 2); [lia |]. apply (dscale_mult 1 1); [exact ds_kC | exact ds_kX2].
  - apply dscale_scal; [exact HM2 |]. apply (dscale_mult 2 2); exact ds_kP.
Qed.

Theorem ds_kdA : dscale 3 (kdA c gamma).
Proof. unfold kdA. apply (dscale_mult 1 2); [exact dscale_kdE | exact ds_kP]. Qed.

Theorem ds_kU : dscale 3 (kU c gamma).
Proof.
  apply (dscale_ext _ (fun d => cLS c * (2 * (cA c * cA c)) * kP c gamma d + cS c * 6 * cA c * kdA c gamma d));
    [intros; unfold kU; ring |].
  apply dscale_plus.
  - apply dscale_scal; [pos |]. apply (dscale_mono 2); [lia | exact ds_kP].
  - apply dscale_scal; [pos | exact ds_kdA].
Qed.

Theorem ds_kdG : dscale 3 (kdG c gamma).
Proof.
  apply (dscale_ext _ (fun d => 8 * (cG c * cG c) * kU c gamma d)); [intros; unfold kdG; ring |].
  apply dscale_scal; [pos | exact ds_kU].
Qed.

Theorem ds_kdN : dscale 3 (kdN c gamma).
Proof.
  apply (dscale_ext _ (fun d => 2 * cA c * kdG c gamma d + (cG c + cB c) * kdA c gamma d));
    [intros; unfold kdN; ring |].
  apply dscale_plus; apply dscale_scal; [pos | exact ds_kdG | pos | exact ds_kdA].
Qed.

Lemma ds_kLd : dscale 1 (kLd om).
Proof.
  intros d Hd. unfold kLd, kdE.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (Hk : 0 <= Rabs om + / kappa) by (pose proof Habs; pose proof (Rinv_0_lt_compat _ kappa_pos); lra).
  set (k := Rabs om + / kappa) in *.
  split; [apply Rmult_le_pos; [exact Hk | apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; lra] |].
  right. simpl. field. lra.
Qed.

Lemma ds_kM : dscale 1 (kM c om).
Proof.
  apply (dscale_ext _ (fun d => cN c * kLd om d + 2 * (cD c * cN c))); [intros; unfold kM; ring |].
  apply dscale_plus; [apply dscale_scal; [exact HN | exact ds_kLd] | apply dscale_const; pos].
Qed.

Theorem ds_kdM : dscale 4 (kdM c om gamma).
Proof.
  apply (dscale_ext _ (fun d => kLd om d * kdN c gamma d
                             + (2 * cLD c * (2 * cN c) * kP c gamma d + 2 * cD c * kdN c gamma d)));
    [intros; unfold kdM; ring |].
  apply dscale_plus; [apply (dscale_mult 1 3); [exact ds_kLd | exact ds_kdN] |].
  apply dscale_plus.
  - apply dscale_scal; [pos |]. apply (dscale_mono 2); [lia | exact ds_kP].
  - apply dscale_scal; [pos |]. apply (dscale_mono 3); [lia | exact ds_kdN].
Qed.

Lemma ds_kW : dscale 1 (kW c om).
Proof.
  apply (dscale_ext _ (fun d => 2 * cN c * kM c om d)); [intros; unfold kW; ring |].
  apply dscale_scal; [pos | exact ds_kM].
Qed.

Theorem ds_kdW : dscale 4 (kdW c om gamma).
Proof.
  apply (dscale_ext _ (fun d => 2 * (2 * cN c) * kdM c om gamma d + 2 * (kM c om d * kdN c gamma d)));
    [intros; unfold kdW; ring |].
  apply dscale_plus; [apply dscale_scal; [pos | exact ds_kdM] |].
  apply dscale_scal; [lra |]. apply (dscale_mult 1 3); [exact ds_kM | exact ds_kdN].
Qed.

Theorem ds_kT : dscale 4 (kT c om gamma).
Proof.
  apply (dscale_ext _ (fun d => 2 * cLS c * (kP c gamma d * kW c om d) + cS c * kdW c om gamma d));
    [intros; unfold kT; ring |].
  apply dscale_plus.
  - apply dscale_scal; [pos |]. apply (dscale_mono 3); [lia |].
    apply (dscale_mult 2 1); [exact ds_kP | exact ds_kW].
  - apply dscale_scal; [exact HS | exact ds_kdW].
Qed.

(** The bound on the torsion's wedge grows as the loss shrinks. *)
Lemma kW_anti (d d' : R) : 0 < d' -> d' <= d -> kW c om d <= kW c om d'.
Proof.
  intros Hd' Hdd. unfold kW, kM, kLd, kdE.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (Hk : 0 <= Rabs om + / kappa) by (pose proof Habs; pose proof (Rinv_0_lt_compat _ kappa_pos); lra).
  assert (Hi : / (exp 1 * (d / 2)) <= / (exp 1 * (d' / 2))).
  { apply Rinv_le_contravar; [apply Rmult_lt_0_compat; lra |]. apply Rmult_le_compat_l; lra. }
  assert (Hm : (Rabs om + / kappa) * / (exp 1 * (d / 2)) <= (Rabs om + / kappa) * / (exp 1 * (d' / 2)))
    by (apply Rmult_le_compat_l; assumption).
  assert (0 <= cN c * cN c) by (apply Rmult_le_pos; exact HN).
  nra.
Qed.

End Scale.
