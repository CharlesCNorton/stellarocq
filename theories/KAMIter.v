(** The KAM iteration.

    From a torus K_0 with frame inverse g_0, normal N_0 = J a_0 g_0 + b a_0
    for a fixed family b, and error at most eps_0 on the strip of width w_0,
    the Newton step is repeated with losses delta_n = delta_0 / 2^n on strips
    of widths w_n = w_0 - 6 delta_0 + 6 delta_n, which stay above
    w_inf = w_0 - 6 delta_0 > 0 ([kit]). The field model is asked to hold on
    the tori within r of K_0 on strips of width between w_inf and w_0. The
    constants of the state are held fixed, so the error at step n is at most
    the scalar sequence eps_(n+1) = A 16^n eps_n^2 with A the error's
    multiple at the first step ([iteps]); the corrections, the changes of the
    tangent, the frame inverse and the normal and the moves of the torsion
    are at most their first-step multiples times 16^n eps_n, and they sum to
    at most twice their first-step values times eps_0 ([inv_all]). The
    torsion is carried as a bound on the strip where each step reads it,
    starting from its bound T_0 at K_0, and its average moves by no more.
    Every torus and frame inverse belongs to the field period P, so the
    inverse of L needs the rotation number to be Diophantine only against
    the multiples of P ([Hdio]); the Diophantine condition against every
    integer ([HdioA]) enters only through the finiteness of the step's
    parts. The conditions on eps_0 are finitely many inequalities between
    numbers at the first step. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon FourierPer KAMFrame KAMVec KAMFin KAMPer KAMStep KAMBound
  KAMDiff KAMUpdate KAMScale.
From Stellarocq Require Hypotheses Invariance TorusLine.
Local Open Scope R_scope.

Section Iter.

Variables (F : fmodel) (P : Z) (om gamma gammaA : R) (K0 : vf) (g0 b : fser) (w0 d0 r : R) (c : kcon)
  (A0 G0 N0 T0 tau0 eps0 : R).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hdio : dioph_per P om gamma.
Hypothesis Hgam : 0 < gamma <= 1.
Hypothesis HdioA : diophantine1 om gammaA.
Hypothesis HgamA : 0 < gammaA <= 1.
Hypothesis Hd0 : 0 < d0.
Hypothesis Hw0 : 6 * d0 < w0.
Hypothesis HA : 0 <= cA c.
Hypothesis HG : 0 <= cG c.
Hypothesis HN : 0 <= cN c.
Hypothesis HB : 0 <= cB c.
Hypothesis HS : 0 <= cS c.
Hypothesis HS1 : 0 <= cS1 c.
Hypothesis HD : 0 <= cD c.
Hypothesis HM2 : 0 <= cM2 c.
Hypothesis HTm : 0 <= cTm c.
Hypothesis Hctau : 0 < ctau c.
Hypothesis HLS : 0 <= cLS c.
Hypothesis HLD : 0 <= cLD c.
Hypothesis Heps0 : 0 <= eps0.

Definition itd (n : nat) : R := d0 / 2 ^ n.
Definition itw (n : nat) : R := w0 - 6 * d0 + 6 * itd n.
Definition winf : R := w0 - 6 * d0.
Definition itA : R := kE c gamma d0.

Fixpoint iteps (n : nat) : R :=
  match n with O => eps0 | S k => itA * 16 ^ k * iteps k ^ 2 end.

Hypothesis HAE : 0 < itA.
Hypothesis Hsmall : itA * 16 * eps0 <= / 2.

(** * The widths and the losses *)

Lemma pow2_pos (n : nat) : 0 < 2 ^ n. Proof. apply pow_lt. lra. Qed.

Lemma itd_pos (n : nat) : 0 < itd n.
Proof. unfold itd. apply Rdiv_lt_0_compat; [exact Hd0 | apply pow2_pos]. Qed.

Lemma itd_le (n : nat) : itd n <= d0.
Proof.
  unfold itd. pose proof (pow_R1_Rle 2 n ltac:(lra)) as H.
  apply (Rmult_le_reg_r (2 ^ n)); [apply pow2_pos |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq, pow2_pos). nra.
Qed.

Lemma itd0 : itd 0 = d0. Proof. unfold itd. simpl. field. Qed.

Lemma itd_S (n : nat) : itd (S n) = itd n / 2.
Proof. unfold itd. assert (H := pow2_pos n). simpl. field. lra. Qed.

Lemma winf_pos : 0 < winf. Proof. unfold winf. lra. Qed.

Lemma itw_S (n : nat) : itw (S n) = itw n - 3 * itd n.
Proof.
  unfold itw, itd. assert (H := pow2_pos n). simpl. field. lra.
Qed.

Lemma itw_gt (n : nat) : winf < itw n.
Proof. unfold itw, winf. pose proof (itd_pos n). lra. Qed.

Lemma itw_le (n : nat) : itw n <= w0.
Proof. unfold itw. pose proof (itd_le n). lra. Qed.

Lemma loss7 (n : nat) : 7 * itd n < 2 * itw n.
Proof. unfold itw. fold winf. pose proof winf_pos. pose proof (itd_pos n). lra. Qed.

Lemma loss_ok (n : nat) : 3 * itd n < itw n.
Proof. pose proof (loss7 n). pose proof (itd_pos n). lra. Qed.

(** * The scalar sequence of errors *)

Lemma iteps_nonneg (n : nat) : 0 <= iteps n.
Proof.
  induction n as [| n IH]; [exact Heps0 |].
  change (iteps (S n)) with (itA * 16 ^ n * iteps n ^ 2).
  apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply pow_le; lra] | apply pow_le, IH].
Qed.

Lemma iteps_step (n : nat) : iteps (S n) <= itA * 16 ^ n * iteps n ^ 2.
Proof. right. reflexivity. Qed.

Lemma Hsmall' : itA * 16 * iteps 0 <= / 2. Proof. exact Hsmall. Qed.

Lemma iteps_decay (n : nat) : iteps n <= eps0 * (/ 32) ^ n.
Proof.
  pose proof (kam_scalar_eps itA 16 iteps HAE ltac:(lra) iteps_nonneg iteps_step Hsmall' n) as H.
  replace (2 * 16) with 32 in H by ring. exact H.
Qed.

Lemma iteps_sum (N : nat) : fsum (fun n => 16 ^ n * iteps n) N <= 2 * eps0.
Proof. exact (kam_scalar_sum itA 16 iteps HAE ltac:(lra) iteps_nonneg iteps_step Hsmall' 16 N ltac:(lra)). Qed.

(** A constant growing at most as 16^n, times the error at step n, is at most
    its first value times eps_0, and sums to at most twice that. *)
Lemma small_step (f : nat -> R) (K : R) :
  0 <= K -> (forall n, f n <= 16 ^ n * K) -> forall n, 0 <= f n -> f n * iteps n <= K * eps0.
Proof.
  intros HK Hf n Hn.
  apply (Rle_trans _ (16 ^ n * K * (eps0 * (/ 32) ^ n))).
  - apply Rmult_le_compat; [exact Hn | apply iteps_nonneg | apply Hf | apply iteps_decay].
  - assert (E : 16 ^ n * K * (eps0 * (/ 32) ^ n) = K * eps0 * (16 * / 32) ^ n)
      by (rewrite Rpow_mult_distr; ring).
    rewrite E. rewrite <- (Rmult_1_r (K * eps0)) at 2.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption |].
    pose proof (pow_le_exp (16 * / 32) 0 n ltac:(lra) ltac:(lia)) as H. simpl in H. exact H.
Qed.

Lemma sum_step (f : nat -> R) (K : R) :
  0 <= K -> (forall n, 0 <= f n <= 16 ^ n * K) ->
  forall N, fsum (fun n => f n * iteps n) N <= 2 * (K * eps0).
Proof.
  intros HK Hf N.
  apply (Rle_trans _ (fsum (fun n => K * (16 ^ n * iteps n)) N)).
  - apply fsum_le. intros k _. pose proof (Hf k) as [H0 H1]. pose proof (iteps_nonneg k).
    replace (K * (16 ^ k * iteps k)) with (16 ^ k * K * iteps k) by ring.
    apply Rmult_le_compat_r; assumption.
  - rewrite fsum_scal. pose proof (iteps_sum N). nra.
Qed.

(** * The constants of the steps *)

Lemma Hgam0 : 0 < gamma. Proof. lra. Qed.

Lemma pow_2_4 (n : nat) : (2 ^ 4) ^ n = 16 ^ n.
Proof. f_equal. simpl. ring. Qed.

Lemma d4 (f : R -> R) (j : nat) : (j <= 4)%nat -> dscale j f -> forall n, f (itd n) <= 16 ^ n * f d0.
Proof.
  intros Hj Hf n. rewrite <- pow_2_4. apply (dscale_iter 4 f d0 (dscale_mono j 4 f Hj Hf) Hd0 n).
Qed.

Definition DkE := ds_kE c gamma Hgam0 HA HG HN HS HS1 HM2 HTm Hctau.
Definition DkP := ds_kP c gamma Hgam0 HA HN HS HTm Hctau.
Definition DkdA := ds_kdA c gamma Hgam0 HA HN HS HTm Hctau.
Definition DkdG := ds_kdG c gamma Hgam0 HA HG HN HS HTm Hctau HLS.
Definition DkU := ds_kU c gamma Hgam0 HA HN HS HTm Hctau HLS.
Definition DkdN := ds_kdN c gamma Hgam0 HA HG HN HB HS HTm Hctau HLS.
Definition DkdW := ds_kdW c om gamma Hgam0 HA HG HN HB HS HD HTm Hctau HLS HLD.
Definition DkT := ds_kT c om gamma Hgam0 HA HG HN HB HS HD HTm Hctau HLS HLD.

Lemma sc_kE (n : nat) : kE c gamma (itd n) <= 16 ^ n * itA.
Proof. exact (d4 _ 4 (le_n 4) DkE n). Qed.
Lemma sc_kP (n : nat) : kP c gamma (itd n) <= 16 ^ n * kP c gamma d0.
Proof. exact (d4 _ 2 ltac:(lia) DkP n). Qed.
Lemma sc_kdA (n : nat) : kdA c gamma (itd n) <= 16 ^ n * kdA c gamma d0.
Proof. exact (d4 _ 3 ltac:(lia) DkdA n). Qed.
Lemma sc_kdG (n : nat) : kdG c gamma (itd n) <= 16 ^ n * kdG c gamma d0.
Proof. exact (d4 _ 3 ltac:(lia) DkdG n). Qed.
Lemma sc_kU (n : nat) : kU c gamma (itd n) <= 16 ^ n * kU c gamma d0.
Proof. exact (d4 _ 3 ltac:(lia) DkU n). Qed.
Lemma sc_kdN (n : nat) : kdN c gamma (itd n) <= 16 ^ n * kdN c gamma d0.
Proof. exact (d4 _ 3 ltac:(lia) DkdN n). Qed.
Lemma sc_kdW (n : nat) : kdW c om gamma (itd n) <= 16 ^ n * kdW c om gamma d0.
Proof. exact (d4 _ 4 (le_n 4) DkdW n). Qed.
Lemma sc_kT (n : nat) : kT c om gamma (itd n) <= 16 ^ n * kT c om gamma d0.
Proof. exact (d4 _ 4 (le_n 4) DkT n). Qed.

Lemma nn_kP (n : nat) : 0 <= kP c gamma (itd n). Proof. exact (proj1 (DkP _ (itd_pos n))). Qed.
Lemma nn_kdA (n : nat) : 0 <= kdA c gamma (itd n). Proof. exact (proj1 (DkdA _ (itd_pos n))). Qed.
Lemma nn_kdG (n : nat) : 0 <= kdG c gamma (itd n). Proof. exact (proj1 (DkdG _ (itd_pos n))). Qed.
Lemma nn_kU (n : nat) : 0 <= kU c gamma (itd n). Proof. exact (proj1 (DkU _ (itd_pos n))). Qed.
Lemma nn_kdN (n : nat) : 0 <= kdN c gamma (itd n). Proof. exact (proj1 (DkdN _ (itd_pos n))). Qed.
Lemma nn_kdW (n : nat) : 0 <= kdW c om gamma (itd n). Proof. exact (proj1 (DkdW _ (itd_pos n))). Qed.
Lemma nn_kT (n : nat) : 0 <= kT c om gamma (itd n). Proof. exact (proj1 (DkT _ (itd_pos n))). Qed.
Lemma nn_kP0 : 0 <= kP c gamma d0. Proof. exact (proj1 (DkP _ Hd0)). Qed.
Lemma nn_kdA0 : 0 <= kdA c gamma d0. Proof. exact (proj1 (DkdA _ Hd0)). Qed.
Lemma nn_kdG0 : 0 <= kdG c gamma d0. Proof. exact (proj1 (DkdG _ Hd0)). Qed.
Lemma nn_kU0 : 0 <= kU c gamma d0. Proof. exact (proj1 (DkU _ Hd0)). Qed.
Lemma nn_kdN0 : 0 <= kdN c gamma d0. Proof. exact (proj1 (DkdN _ Hd0)). Qed.
Lemma nn_kdW0 : 0 <= kdW c om gamma d0. Proof. exact (proj1 (DkdW _ Hd0)). Qed.
Lemma nn_kT0 : 0 <= kT c om gamma d0. Proof. exact (proj1 (DkT _ Hd0)). Qed.

(** * The field model on the ball about K_0 *)

Definition good (w : R) (K : vf) : Prop :=
  winf <= w /\ w <= w0 /\ vcanon K /\ vsym K /\ vper P K /\ vbound w r (vsub K K0).

Hypothesis MQV : forall w K, good w K -> vper P (Vf F K).
Hypothesis MQD : forall w K, good w K -> mper P (DVf F K).
Hypothesis MQS : forall w K, good w K -> is_per P (Sf F K).
Hypothesis MCV : forall w K, good w K -> vcanon (Vf F K).
Hypothesis MPV : forall w K, good w K -> vasym (Vf F K).
Hypothesis MCD : forall w K, good w K -> mcanon (DVf F K).
Hypothesis MPD : forall w K, good w K -> mpar (DVf F K).
Hypothesis MCS : forall w K, good w K -> is_canon (Sf F K).
Hypothesis MPS : forall w K, good w K -> is_even (Sf F K).
Hypothesis MCG : forall w K, good w K -> vcanon (GSf F K).
Hypothesis MBV : forall w K, good w K -> vbound w (cMV c) (Vf F K).
Hypothesis MBD : forall w K, good w K -> mbound w (cD c) (DVf F K).
Hypothesis MBS : forall w K, good w K -> nbound w (cS c) (Sf F K).
Hypothesis MBG : forall w K, good w K -> vbound w (cS1 c) (GSf F K).
Hypothesis Mchain_R : forall w K, good w K -> forall t p,
  feval (dt (vR (Vf F K))) t p
  = feval (mRR (DVf F K)) t p * feval (vR (ktng K)) t p
    + feval (mRZ (DVf F K)) t p * feval (vZ (ktng K)) t p.
Hypothesis Mchain_Z : forall w K, good w K -> forall t p,
  feval (dt (vZ (Vf F K))) t p
  = feval (mZR (DVf F K)) t p * feval (vR (ktng K)) t p
    + feval (mZZ (DVf F K)) t p * feval (vZ (ktng K)) t p.
Hypothesis Mliou : forall w K, good w K -> forall t p,
  feval (lc om (Sf F K)) t p
  = feval (vdot (GSf F K) (kerr F om K)) t p - feval (Sf F K) t p * feval (mtr (DVf F K)) t p.
Hypothesis Mtaylor : forall w K K', good w K -> good w K' -> forall P, vbound w P (vsub K' K) ->
  vbound w (cM2 c * (P * P)) (vsub (vsub (Vf F K') (Vf F K)) (mapp (DVf F K) (vsub K' K))).
Hypothesis MlipS : forall w K K', good w K -> good w K' -> forall P, vbound w P (vsub K' K) ->
  nbound w (cLS c * P) (fsub (Sf F K') (Sf F K)).
Hypothesis MlipD : forall w K K', good w K -> good w K' -> forall P, vbound w P (vsub K' K) ->
  mbound w (cLD c * P) (msub (DVf F K') (DVf F K)).

(** * The first torus and the conditions on its error *)

Hypothesis C0 : vcanon K0.
Hypothesis P0 : vsym K0.
Hypothesis Cg0 : is_canon g0.
Hypothesis Pg0 : is_even g0.
Hypothesis Cb : is_canon b.
Hypothesis Pb : is_odd b.
Hypothesis Q0 : vper P K0.
Hypothesis Qg0 : is_per P g0.
Hypothesis Qb : is_per P b.
Hypothesis FK0 : vfin w0 K0.
Hypothesis BB0 : nbound w0 (cB c) b.
Hypothesis BA0 : vbound w0 A0 (ktng K0).
Hypothesis BG0 : nbound w0 G0 g0.
Hypothesis BN0 : vbound w0 N0 (knrm K0 g0 b).
Hypothesis BE0 : vbound w0 eps0 (kerr F om K0).
Hypothesis Hframe0 : forall t p,
  feval (Sf F K0) t p * feval (vdot (ktng K0) (ktng K0)) t p * feval g0 t p = 1.
Hypothesis BT0 : nbound (w0 - d0) T0 (ktwist F om K0 g0 b).
Hypothesis Htau0 : tau0 <= Rabs (fc (ktwist F om K0 g0 b) 0 0).

Hypothesis HcA : A0 + 2 * (kdA c gamma d0 * eps0) <= cA c.
Hypothesis HcG : G0 + 2 * (kdG c gamma d0 * eps0) <= cG c.
Hypothesis HcN : N0 + 2 * (kdN c gamma d0 * eps0) <= cN c.
Hypothesis HcT : T0 + 2 * (kT c om gamma d0 * eps0) <= cTm c.
Hypothesis Hr : 2 * (kP c gamma d0 * eps0) <= r.
Hypothesis Hctau2 : ctau c <= tau0 - 2 * (kT c om gamma d0 * eps0).
Hypothesis Hsm_a0 : kdA c gamma d0 * eps0 <= cA c.
Hypothesis Hsm_q0 : cG c * (kU c gamma d0 * eps0) <= / 2.
Hypothesis Hsm_g0 : kdG c gamma d0 * eps0 <= cG c.
Hypothesis Hsm_n0 : kdN c gamma d0 * eps0 <= cN c.
Hypothesis Hsm_w0 : kdW c om gamma d0 * eps0 <= kW c om d0.

(** * The sequence of tori and frame inverses *)

Fixpoint kit (n : nat) : vf * fser :=
  match n with
  | O => (K0, g0)
  | S k => (knext F om (fst (kit k)) (snd (kit k)) b, gnext F om (fst (kit k)) (snd (kit k)) b)
  end.

Definition sP (n : nat) : R := fsum (fun k => kP c gamma (itd k) * iteps k) n.
Definition sA (n : nat) : R := fsum (fun k => kdA c gamma (itd k) * iteps k) n.
Definition sG (n : nat) : R := fsum (fun k => kdG c gamma (itd k) * iteps k) n.
Definition sN (n : nat) : R := fsum (fun k => kdN c gamma (itd k) * iteps k) n.
Definition sT (n : nat) : R := fsum (fun k => kT c om gamma (itd k) * iteps k) n.

Definition inv (n : nat) : Prop :=
  vcanon (fst (kit n)) /\ vsym (fst (kit n)) /\ is_canon (snd (kit n)) /\ is_even (snd (kit n)) /\
  vper P (fst (kit n)) /\ is_per P (snd (kit n)) /\
  vbound (itw n) (sP n) (vsub (fst (kit n)) K0) /\
  vbound (itw n) (A0 + sA n) (ktng (fst (kit n))) /\
  nbound (itw n) (G0 + sG n) (snd (kit n)) /\
  vbound (itw n) (N0 + sN n) (knrm (fst (kit n)) (snd (kit n)) b) /\
  (forall t p, feval (Sf F (fst (kit n))) t p * feval (vdot (ktng (fst (kit n))) (ktng (fst (kit n)))) t p
               * feval (snd (kit n)) t p = 1) /\
  vbound (itw n) (iteps n) (kerr F om (fst (kit n))) /\
  nbound (itw n - itd n) (T0 + sT n) (ktwist F om (fst (kit n)) (snd (kit n)) b) /\
  tau0 - sT n <= Rabs (fc (ktwist F om (fst (kit n)) (snd (kit n)) b) 0 0).

Lemma sP_le (n : nat) : sP n <= 2 * (kP c gamma d0 * eps0).
Proof. exact (sum_step _ _ nn_kP0 (fun k => conj (nn_kP k) (sc_kP k)) n). Qed.
Lemma sA_le (n : nat) : sA n <= 2 * (kdA c gamma d0 * eps0).
Proof. exact (sum_step _ _ nn_kdA0 (fun k => conj (nn_kdA k) (sc_kdA k)) n). Qed.
Lemma sG_le (n : nat) : sG n <= 2 * (kdG c gamma d0 * eps0).
Proof. exact (sum_step _ _ nn_kdG0 (fun k => conj (nn_kdG k) (sc_kdG k)) n). Qed.
Lemma sN_le (n : nat) : sN n <= 2 * (kdN c gamma d0 * eps0).
Proof. exact (sum_step _ _ nn_kdN0 (fun k => conj (nn_kdN k) (sc_kdN k)) n). Qed.
Lemma sT_le (n : nat) : sT n <= 2 * (kT c om gamma d0 * eps0).
Proof. exact (sum_step _ _ nn_kT0 (fun k => conj (nn_kT k) (sc_kT k)) n). Qed.

Lemma vbound_zero (rho : R) (u : vf) : (forall m n, fc (vR u) m n = 0 /\ fs (vR u) m n = 0 /\
                                                     fc (vZ u) m n = 0 /\ fs (vZ u) m n = 0) ->
  vbound rho 0 u.
Proof.
  intros H. split; apply (nbound_feq _ _ fzero); try apply nbound_fzero;
    intros m n; destruct (H m n) as [A [B [C D]]]; simpl; auto.
Qed.

Lemma good_vfin (w : R) (K : vf) : good w K -> vfin w K.
Proof.
  intros [H1 [H2 [_ [_ [_ Hb]]]]].
  destruct (vfin_mono w0 w K0 H2 FK0) as [[M1 F1] [M2 F2]]. destruct Hb as [B1 B2].
  split.
  - exists (M1 + r). exact (nbound_add_diff w M1 r (vR K0) (vR K) F1 B1).
  - exists (M2 + r). exact (nbound_add_diff w M2 r (vZ K0) (vZ K) F2 B2).
Qed.

Lemma good_mono (w w' : R) (K : vf) : good w K -> winf <= w' -> w' <= w -> good w' K.
Proof.
  intros [H1 [H2 [H3 [H4 [H4' H5]]]]] H6 H7.
  assert (H8 : w' <= w0) by lra.
  exact (conj H6 (conj H8 (conj H3 (conj H4 (conj H4' (vbound_mono w w' _ _ H7 H5)))))).
Qed.

Lemma itw0 : itw 0 = w0.
Proof. unfold itw, itd. simpl. field. Qed.

Theorem inv0 : inv 0.
Proof.
  unfold inv, sP, sA, sG, sN, sT. cbn [kit fst snd fsum]. rewrite itw0, itd0.
  assert (Z0 : vbound w0 0 (vsub K0 K0)).
  { apply vbound_zero. intros m n. unfold vsub, fsub, fadd, fscal. simpl. repeat split; ring. }
  refine (conj C0 (conj P0 (conj Cg0 (conj Pg0 (conj Q0 (conj Qg0 (conj Z0 (conj _ (conj _ (conj _
            (conj Hframe0 (conj BE0 (conj _ _))))))))))))).
  - apply (vbound_le _ A0); [lra | exact BA0].
  - apply (nbound_le _ G0); [lra | exact BG0].
  - apply (vbound_le _ N0); [lra | exact BN0].
  - apply (nbound_le _ T0); [lra | exact BT0].
  - lra.
Qed.

Theorem inv_step (n : nat) : inv n -> inv (S n).
Proof.
  intros [CK [PK [Cg [Pg [QK [Qg [Bball [BAn [BGn [BNn [Hfr [BE [BTn Htw]]]]]]]]]]]]].
  set (K := fst (kit n)) in *. set (g := snd (kit n)) in *.
  set (w := itw n) in *. set (d := itd n) in *. set (e := iteps n) in *.
  assert (Hd : 0 < d) by apply itd_pos.
  assert (Hw7 : 7 * d < 2 * w) by apply loss7.
  assert (Hw : 3 * d < w) by lra.
  assert (He : 0 <= e) by apply iteps_nonneg.
  assert (Hwi : winf < w - 3 * d) by (unfold w, d; rewrite <- itw_S; apply itw_gt).
  assert (Hwl : w <= w0) by apply itw_le.
  pose proof (sP_le n) as SP. pose proof (sA_le n) as SA. pose proof (sG_le n) as SG.
  pose proof (sN_le n) as SN. pose proof (sT_le n) as ST. pose proof (sP_le (S n)) as SP1.
  (* the bounds of the state *)
  assert (BA : vbound w (cA c) (ktng K)) by (apply (vbound_le _ (A0 + sA n)); [lra | exact BAn]).
  assert (BG : nbound w (cG c) g) by (apply (nbound_le _ (G0 + sG n)); [lra | exact BGn]).
  assert (BN : vbound w (cN c) (knrm K g b)) by (apply (vbound_le _ (N0 + sN n)); [lra | exact BNn]).
  assert (BT : nbound (w - d) (cTm c) (ktwist F om K g b))
    by (apply (nbound_le _ (T0 + sT n)); [lra | exact BTn]).
  assert (BB : nbound w (cB c) b) by (apply (nbound_mono w0); [exact Hwl | exact BB0]).
  assert (Gd : good w K).
  { assert (Hb : vbound w r (vsub K K0)) by (apply (vbound_le _ (sP n)); [lra | exact Bball]).
    exact (conj (Rlt_le _ _ (itw_gt n)) (conj Hwl (conj CK (conj PK (conj QK Hb))))). }
  assert (FK : vfin w K) by (apply good_vfin, Gd).
  pose proof (MBS _ _ Gd) as BS. pose proof (MBD _ _ Gd) as BD.
  pose proof (MQV _ _ Gd) as QV. pose proof (MQD _ _ Gd) as QD. pose proof (MQS _ _ Gd) as QS.
  assert (Htau : 0 < ctau c <= Rabs (fc (ktwist F om K g b) 0 0)) by lra.
  (* the next torus is in the ball *)
  pose proof (U_dK F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 QK Qg Qb QV QD QS
                BA BN BE BT Htau BS) as DK.
  set (K' := knext F om K g b) in *.
  assert (Bball' : vbound (w - 2 * d) (sP (S n)) (vsub K' K0)).
  { apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vsub_vsub_feq K' K K0))).
    apply (vbound_le _ (kP c gamma d * e + sP n)); [unfold sP; simpl fsum; right; unfold d, e; ring |].
    apply vbound_vadd; [exact DK | apply (vbound_mono w); [lra | exact Bball]]. }
  pose proof (next_canon F om K g b CK Cg Cb (MCV _ _ Gd) (MCD _ _ Gd) (MCS _ _ Gd)) as CK'.
  pose proof (next_sym F om K g b PK Pg Pb (MPV _ _ Gd) (MPD _ _ Gd) (MPS _ _ Gd)) as PK'.
  pose proof (next_per F P om K g b HP QK Qg Qb QV QD QS) as QK'.
  assert (Gd' : good (w - 2 * d) K').
  { assert (X1 : winf <= w - 2 * d) by lra. assert (X2 : w - 2 * d <= w0) by lra.
    assert (Hb : vbound (w - 2 * d) r (vsub K' K0)) by (apply (vbound_le _ (sP (S n))); [lra | exact Bball']).
    exact (conj X1 (conj X2 (conj CK' (conj PK' (conj QK' Hb))))). }
  assert (Gd2 : good (w - 2 * d) K) by (apply (good_mono w); [exact Gd | lra | lra]).
  (* smallness at this step *)
  assert (Hsm_a : kdA c gamma d * e <= cA c).
  { pose proof (small_step _ _ nn_kdA0 sc_kdA n (nn_kdA n)) as H. unfold d, e. lra. }
  assert (Hsm_q : cG c * (kU c gamma d * e) <= / 2).
  { pose proof (small_step _ _ nn_kU0 sc_kU n (nn_kU n)) as H.
    apply (Rle_trans _ (cG c * (kU c gamma d0 * eps0))); [| exact Hsm_q0].
    apply Rmult_le_compat_l; [exact HG | unfold d, e; exact H]. }
  assert (Hsm_g : kdG c gamma d * e <= cG c).
  { pose proof (small_step _ _ nn_kdG0 sc_kdG n (nn_kdG n)) as H. unfold d, e. lra. }
  assert (Hsm_n : kdN c gamma d * e <= cN c).
  { pose proof (small_step _ _ nn_kdN0 sc_kdN n (nn_kdN n)) as H. unfold d, e. lra. }
  assert (Hsm_w : kdW c om gamma d * e <= kW c om d).
  { pose proof (small_step _ _ nn_kdW0 sc_kdW n (nn_kdW n)) as H.
    pose proof (kW_anti c om HN d0 d Hd (itd_le n)) as H2. unfold d, e in *. lra. }
  (* the step *)
  pose proof (step_bound F P om gamma gammaA w d K g b c e HP Hdio Hgam HdioA HgamA Hd Hw CK PK Cg Cb
                (fin_of _ _ _ BB) QK Qg Qb QV QD QS FK BA BG BN BE BT Htau Hfr
                (MCV _ _ Gd) (MPV _ _ Gd) (MCD _ _ Gd) (MCS _ _ Gd) (MPS _ _ Gd) (MCG _ _ Gd)
                (MBV _ _ Gd) BD BS (MBG _ _ Gd) (Mchain_R _ _ Gd) (Mchain_Z _ _ Gd) (Mliou _ _ Gd)
                (MCV _ _ Gd') (MBV _ _ Gd') (fun Q HQ => Mtaylor _ _ _ Gd2 Gd' Q HQ)) as SB.
  pose proof (U_dtng F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 QK Qg Qb QV QD QS
                BA BN BE BT Htau BS) as DT.
  pose proof (U_g'sub F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 CK Cg QK Qg Qb QV QD QS
                BA BG BN BE BT Htau Hfr
                (MCS _ _ Gd) BS (MBS _ _ Gd') (fun Q HQ => MlipS _ _ _ Gd2 Gd' Q HQ) Hsm_a Hsm_q) as DG.
  pose proof (U_frame' F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 CK Cg QK Qg Qb QV QD QS
                BA BG BN BE BT Htau Hfr
                (MCS _ _ Gd) BS (MBS _ _ Gd') (fun Q HQ => MlipS _ _ _ Gd2 Gd' Q HQ) Hsm_a Hsm_q) as FR.
  pose proof (U_dN F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 CK Cg QK Qg Qb QV QD QS
                BB BA BG BN BE BT Htau Hfr
                (MCS _ _ Gd) BS (MBS _ _ Gd') (fun Q HQ => MlipS _ _ _ Gd2 Gd' Q HQ) Hsm_a Hsm_q) as DN.
  pose proof (U_dT F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 CK Cg QK Qg Qb QV QD QS
                BB BA BG BN BE BT Htau Hfr
                (MCS _ _ Gd) BD BS (MBS _ _ Gd') (fun Q HQ => MlipS _ _ _ Gd2 Gd' Q HQ)
                (fun Q HQ => MlipD _ _ _ Gd2 Gd' Q HQ) Hsm_a Hsm_q Hsm_n Hsm_w) as DTw.
  pose proof (U_twist F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 CK Cg QK Qg Qb QV QD QS
                BB BA BG BN BE BT Htau Hfr
                (MCS _ _ Gd) BD BS (MBS _ _ Gd') (fun Q HQ => MlipS _ _ _ Gd2 Gd' Q HQ)
                (fun Q HQ => MlipD _ _ _ Gd2 Gd' Q HQ) Hsm_a Hsm_q Hsm_n Hsm_w) as TW.
  pose proof (U_g'canon F om K g b CK Cg Cb (MCV _ _ Gd) (MCD _ _ Gd) (MCS _ _ Gd) (MCS _ _ Gd')) as Cg'.
  pose proof (U_g'even F om K g b PK Pg Pb (MPV _ _ Gd) (MPD _ _ Gd) (MPS _ _ Gd) (MPS _ _ Gd')) as Pg'.
  pose proof (U_g'per F P om K g b HP QK Qg Qb QV QD QS (MQS _ _ Gd')) as Qg'.
  (* the invariant at the next step *)
  assert (EW : itw (S n) = w - 3 * d) by (unfold w, d; apply itw_S).
  assert (ED : itd (S n) = d / 2) by (unfold d; apply itd_S).
  assert (Hk : kE c gamma d * (e * e) <= iteps (S n)).
  { change (iteps (S n)) with (itA * 16 ^ n * iteps n ^ 2).
    pose proof (sc_kE n) as H. fold d in H. fold e.
    replace (e ^ 2) with (e * e) by ring.
    replace (itA * 16 ^ n * (e * e)) with (16 ^ n * itA * (e * e)) by ring.
    apply Rmult_le_compat_r; [apply Rmult_le_pos; exact He | exact H]. }
  assert (W32 : w - 3 * d <= w - 2 * d) by lra.
  assert (W30 : w - 3 * d <= w) by lra.
  assert (I5 : vbound (w - 3 * d) (sP (S n)) (vsub K' K0)) by exact (vbound_mono _ _ _ _ W32 Bball').
  assert (I6 : vbound (w - 3 * d) (A0 + sA (S n)) (ktng K')).
  { apply (vbound_le _ (A0 + sA n + kdA c gamma d * e)); [unfold sA; simpl fsum; unfold d, e; lra |].
    exact (vbound_add_diff _ _ _ _ _ (vbound_mono w _ _ _ W30 BAn) DT). }
  assert (I7 : nbound (w - 3 * d) (G0 + sG (S n)) (gnext F om K g b)).
  { apply (nbound_le _ (G0 + sG n + kdG c gamma d * e)); [unfold sG; simpl fsum; unfold d, e; lra |].
    exact (nbound_add_diff _ _ _ _ _ (nbound_mono w _ _ _ W30 BGn) DG). }
  assert (I8 : vbound (w - 3 * d) (N0 + sN (S n)) (knrm K' (gnext F om K g b) b)).
  { apply (vbound_le _ (N0 + sN n + kdN c gamma d * e)); [unfold sN; simpl fsum; unfold d, e; lra |].
    exact (vbound_add_diff _ _ _ _ _ (vbound_mono w _ _ _ W30 BNn) DN). }
  assert (I10 : vbound (w - 3 * d) (iteps (S n)) (kerr F om K'))
    by exact (vbound_le _ _ _ _ Hk (vbound_mono _ _ _ _ W32 SB)).
  assert (I11 : nbound (w - 3 * d - d / 2) (T0 + sT (S n)) (ktwist F om K' (gnext F om K g b) b)).
  { apply (nbound_le _ (T0 + sT n + kT c om gamma d * e)); [unfold sT; simpl fsum; unfold d, e; lra |].
    apply (nbound_add_diff _ _ _ (ktwist F om K g b)); [| exact DTw].
    apply (nbound_mono (w - d)); [lra | exact BTn]. }
  assert (I12 : tau0 - sT (S n) <= Rabs (fc (ktwist F om K' (gnext F om K g b) b) 0 0)).
  { unfold sT. simpl fsum. fold (sT n). fold d e.
    pose proof (Rabs_triang_inv (fc (ktwist F om K g b) 0 0) (fc (ktwist F om K' (gnext F om K g b) b) 0 0)) as T1.
    rewrite Rabs_minus_sym in T1. unfold K' in *. lra. }
  unfold inv. change (fst (kit (S n))) with K'. change (snd (kit (S n))) with (gnext F om K g b).
  rewrite EW, ED.
  exact (conj CK' (conj PK' (conj Cg' (conj Pg' (conj QK' (conj Qg' (conj I5 (conj I6 (conj I7 (conj I8
           (conj FR (conj I10 (conj I11 I12))))))))))))).
Qed.

Theorem inv_all (n : nat) : inv n.
Proof. induction n as [| n IH]; [exact inv0 | exact (inv_step n IH)]. Qed.

(** * The limit torus *)

Lemma state_step (n : nat) :
  vbound (itw (S n)) (kP c gamma (itd n) * iteps n) (vsub (fst (kit (S n))) (fst (kit n))).
Proof.
  destruct (inv_all n) as [CK [PK [Cg [Pg [QK [Qg [Bball [BAn [BGn [BNn [Hfr [BE [BTn Htw]]]]]]]]]]]]].
  set (K := fst (kit n)) in *. set (g := snd (kit n)) in *.
  set (w := itw n) in *. set (d := itd n) in *. set (e := iteps n) in *.
  assert (Hd : 0 < d) by apply itd_pos.
  assert (Hw7 : 7 * d < 2 * w) by apply loss7.
  assert (Hwl : w <= w0) by apply itw_le.
  pose proof (sP_le n) as SP. pose proof (sA_le n) as SA. pose proof (sN_le n) as SN. pose proof (sT_le n) as ST.
  assert (BA : vbound w (cA c) (ktng K)) by (apply (vbound_le _ (A0 + sA n)); [lra | exact BAn]).
  assert (BN : vbound w (cN c) (knrm K g b)) by (apply (vbound_le _ (N0 + sN n)); [lra | exact BNn]).
  assert (BT : nbound (w - d) (cTm c) (ktwist F om K g b))
    by (apply (nbound_le _ (T0 + sT n)); [lra | exact BTn]).
  assert (Gd : good w K).
  { assert (Hb : vbound w r (vsub K K0)) by (apply (vbound_le _ (sP n)); [lra | exact Bball]).
    exact (conj (Rlt_le _ _ (itw_gt n)) (conj Hwl (conj CK (conj PK (conj QK Hb))))). }
  pose proof (MBS _ _ Gd) as BS.
  assert (Htau : 0 < ctau c <= Rabs (fc (ktwist F om K g b) 0 0)) by lra.
  pose proof (U_dK F P om gamma w d K g b c e HP Hdio Hgam Hd Hw7 QK Qg Qb (MQV _ _ Gd) (MQD _ _ Gd)
                (MQS _ _ Gd) BA BN BE BT Htau BS) as DK.
  assert (EW : itw (S n) = w - 3 * d) by (unfold w, d; apply itw_S).
  change (fst (kit (S n))) with (knext F om K g b). rewrite EW.
  apply (vbound_mono (w - 2 * d)); [lra | exact DK].
Qed.

Lemma step_geom (k : nat) : kP c gamma (itd k) * iteps k <= kP c gamma d0 * eps0 * (/ 2) ^ k.
Proof.
  pose proof (sc_kP k) as H1. pose proof (iteps_decay k) as H2.
  pose proof (nn_kP k). pose proof (iteps_nonneg k).
  apply (Rle_trans _ (16 ^ k * kP c gamma d0 * (eps0 * (/ 32) ^ k))).
  - apply Rmult_le_compat; assumption.
  - right. replace (/ 2) with (16 * / 32) by field. rewrite Rpow_mult_distr. ring.
Qed.

Lemma geom2 (n j : nat) : fsum (fun i => (/ 2) ^ (n + i)) j <= (/ 2) ^ n * 2.
Proof.
  rewrite (fsum_ext _ (fun i => (/ 2) ^ n * (/ 2) ^ i)) by (intros; apply pow_add).
  rewrite fsum_scal. apply Rmult_le_compat_l; [apply pow_le; lra |].
  apply (Rle_trans _ (/ (1 - / 2))); [apply geom_fsum; lra | right; field].
Qed.

Lemma diff_bound (n j : nat) :
  vbound winf (kP c gamma d0 * eps0 * fsum (fun i => (/ 2) ^ (n + i)) j)
    (vsub (fst (kit (n + j))) (fst (kit n))).
Proof.
  induction j as [| j IH].
  - rewrite Nat.add_0_r. simpl fsum. rewrite Rmult_0_r. apply vbound_zero.
    intros; unfold vsub, fsub, fadd, fscal; simpl; repeat split; ring.
  - replace (n + S j)%nat with (S (n + j)) by lia.
    apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vsub_vsub_feq (fst (kit (S (n + j)))) (fst (kit (n + j))) (fst (kit n))))).
    apply (vbound_le _ (kP c gamma (itd (n + j)) * iteps (n + j)
                        + kP c gamma d0 * eps0 * fsum (fun i => (/ 2) ^ (n + i)) j)).
    + simpl fsum. rewrite Rmult_plus_distr_l. pose proof (step_geom (n + j)). lra.
    + apply vbound_vadd; [| exact IH].
      apply (vbound_mono (itw (S (n + j)))); [left; apply itw_gt | apply state_step].
Qed.

Definition tl (N : nat) : R := kP c gamma d0 * eps0 * ((/ 2) ^ N * 2).
Definition ceps (N : nat) : R := 2 * tl N.

Lemma tl_nonneg (N : nat) : 0 <= tl N.
Proof.
  unfold tl. apply Rmult_le_pos; [apply Rmult_le_pos; [apply nn_kP0 | exact Heps0] |].
  apply Rmult_le_pos; [apply pow_le; lra | lra].
Qed.

Lemma cauchy_K (N n : nat) : (N <= n)%nat -> vbound winf (tl N) (vsub (fst (kit n)) (fst (kit N))).
Proof.
  intros H. replace n with (N + (n - N))%nat by lia.
  apply (vbound_le _ (kP c gamma d0 * eps0 * fsum (fun i => (/ 2) ^ (N + i)) (n - N))).
  - unfold tl. apply Rmult_le_compat_l; [apply Rmult_le_pos; [apply nn_kP0 | exact Heps0] | apply geom2].
  - apply diff_bound.
Qed.

Lemma ceps_lim : is_lim_seq ceps 0.
Proof.
  assert (H : is_lim_seq (fun N => 2 * (kP c gamma d0 * eps0) * 2 * (/ 2) ^ N)
                         (2 * (kP c gamma d0 * eps0) * 2 * 0)).
  { apply (is_lim_seq_mult' (fun _ => 2 * (kP c gamma d0 * eps0) * 2) (fun N => (/ 2) ^ N)).
    - apply is_lim_seq_const.
    - apply is_lim_seq_geom. rewrite Rabs_pos_eq by lra. lra. }
  rewrite Rmult_0_r in H.
  apply (is_lim_seq_ext (fun N => 2 * (kP c gamma d0 * eps0) * 2 * (/ 2) ^ N) ceps 0).
  - intros N. unfold ceps, tl. ring.
  - exact H.
Qed.

Lemma cauchy_R (N n m : nat) : (N <= n)%nat -> (N <= m)%nat ->
  nbound winf (ceps N) (fsub (vR (fst (kit n))) (vR (fst (kit m)))).
Proof.
  intros Hn Hm. apply (nbound_feq _ _ _ _ (feq_sym _ _ (fsub_fsub_feq _ (vR (fst (kit N))) _))).
  unfold ceps. replace (2 * tl N) with (tl N + tl N) by ring.
  apply nbound_fadd; [exact (proj1 (cauchy_K N n Hn)) | apply nbound_fsub_sym; exact (proj1 (cauchy_K N m Hm))].
Qed.

Lemma cauchy_Z (N n m : nat) : (N <= n)%nat -> (N <= m)%nat ->
  nbound winf (ceps N) (fsub (vZ (fst (kit n))) (vZ (fst (kit m)))).
Proof.
  intros Hn Hm. apply (nbound_feq _ _ _ _ (feq_sym _ _ (fsub_fsub_feq _ (vZ (fst (kit N))) _))).
  unfold ceps. replace (2 * tl N) with (tl N + tl N) by ring.
  apply nbound_fadd; [exact (proj2 (cauchy_K N n Hn)) | apply nbound_fsub_sym; exact (proj2 (cauchy_K N m Hm))].
Qed.

Definition Kstar : vf := mkvf (flim (fun k => vR (fst (kit k)))) (flim (fun k => vZ (fst (kit k)))).

Lemma winf_nonneg : 0 <= winf. Proof. left. apply winf_pos. Qed.

Lemma Kstar_close (n : nat) : vbound winf (ceps n) (vsub (fst (kit n)) Kstar).
Proof.
  split.
  - exact (nbound_flim_sub winf winf_nonneg _ ceps ceps_lim cauchy_R n n (le_n n)).
  - exact (nbound_flim_sub winf winf_nonneg _ ceps ceps_lim cauchy_Z n n (le_n n)).
Qed.

Lemma Kstar_canon : vcanon Kstar.
Proof.
  split; apply flim_canon; intros n; destruct (inv_all n) as [[C1 C2] _]; assumption.
Qed.

Lemma Kstar_sym : vsym Kstar.
Proof.
  split; [apply flim_even | apply flim_odd]; intros n; destruct (inv_all n) as [_ [[P1 P2] _]]; assumption.
Qed.

Lemma Kstar_per : vper P Kstar.
Proof.
  split; apply flim_per; intros n; destruct (inv_all n) as [_ [_ [_ [_ [[Q1 Q2] _]]]]]; assumption.
Qed.

Lemma nbound_lim (rho M : R) (a : nat -> R) (u : fser) :
  is_lim_seq a 0 -> (forall n, nbound rho (M + a n) u) -> nbound rho M u.
Proof.
  intros Ha H N.
  assert (Hl : is_lim_seq (fun n => M + a n) (M + 0)) by (apply (is_lim_seq_plus' (fun _ => M) a M 0); [apply is_lim_seq_const | exact Ha]).
  rewrite Rplus_0_r in Hl.
  apply (is_lim_seq_le (fun _ => sqsum (nterm rho u) N) (fun n => M + a n) (sqsum (nterm rho u) N) M).
  - intros n. apply H.
  - apply is_lim_seq_const.
  - exact Hl.
Qed.

Lemma Kstar_ball : vbound winf (2 * (kP c gamma d0 * eps0)) (vsub Kstar K0).
Proof.
  assert (Hc : forall n, vbound winf (2 * (kP c gamma d0 * eps0) + ceps n) (vsub Kstar K0)).
  { intros n.
    apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (vsub_vsub_feq Kstar (fst (kit n)) K0))).
    apply (vbound_le _ (ceps n + sP n)); [pose proof (sP_le n); lra |].
    apply vbound_vadd; [apply vbound_vsub_sym, Kstar_close |].
    destruct (inv_all n) as [_ [_ [_ [_ [_ [_ [Bb _]]]]]]].
    apply (vbound_mono (itw n)); [left; apply itw_gt | exact Bb]. }
  split; apply (nbound_lim _ _ ceps); try exact ceps_lim; intros n; [exact (proj1 (Hc n)) | exact (proj2 (Hc n))].
Qed.

Lemma Kstar_good : good winf Kstar.
Proof.
  assert (Hb : vbound winf r (vsub Kstar K0)) by (apply (vbound_le _ _ _ _ Hr Kstar_ball)).
  assert (H1 : winf <= winf) by lra. assert (H2 : winf <= w0) by (unfold winf; lra).
  exact (conj H1 (conj H2 (conj Kstar_canon (conj Kstar_sym (conj Kstar_per Hb))))).
Qed.

Lemma Kn_good (n : nat) : good winf (fst (kit n)).
Proof.
  destruct (inv_all n) as [CK [PK [_ [_ [QK [_ [Bb _]]]]]]].
  assert (Hb : vbound winf r (vsub (fst (kit n)) K0)).
  { apply (vbound_le _ (sP n)); [pose proof (sP_le n); lra |].
    apply (vbound_mono (itw n)); [left; apply itw_gt | exact Bb]. }
  assert (H1 : winf <= winf) by lra. assert (H2 : winf <= w0) by (unfold winf; lra).
  exact (conj H1 (conj H2 (conj CK (conj PK (conj QK Hb))))).
Qed.

Lemma err_split_feq (K K' : vf) :
  feq (vR (kerr F om K')) (vR (vadd (kerr F om K) (vsub (vlc om (vsub K' K)) (vsub (Vf F K') (Vf F K))))) /\
  feq (vZ (kerr F om K')) (vZ (vadd (kerr F om K) (vsub (vlc om (vsub K' K)) (vsub (Vf F K') (Vf F K))))).
Proof.
  split; intros m n; unfold kerr; cbn [vR vZ vsub vadd vlc]; unfold fsub, lc; fnorm; cbn [fc fs]; fnorm;
    split; ring.
Qed.

Lemma Vdiff_feq (A : mf) (K K' : vf) :
  feq (vR (vsub (Vf F K') (Vf F K)))
      (vR (vadd (vsub (vsub (Vf F K') (Vf F K)) (mapp A (vsub K' K))) (mapp A (vsub K' K)))) /\
  feq (vZ (vsub (Vf F K') (Vf F K)))
      (vZ (vadd (vsub (vsub (Vf F K') (Vf F K)) (mapp A (vsub K' K))) (mapp A (vsub K' K)))).
Proof.
  split; intros m n; cbn [vR vZ vsub vadd]; unfold fsub; fnorm; split; ring.
Qed.

Definition errb (n : nat) : R :=
  iteps n + ((Rabs om + / kappa) * kdE winf * ceps n + (cM2 c * (ceps n * ceps n) + 2 * (cD c * ceps n))).

Lemma Kstar_err (n : nat) : vbound 0 (errb n) (kerr F om Kstar).
Proof.
  set (K := fst (kit n)).
  assert (Dn : vbound winf (ceps n) (vsub Kstar K)) by (apply vbound_vsub_sym, Kstar_close).
  apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (err_split_feq K Kstar))).
  unfold errb. apply vbound_vadd; [| apply vbound_vsub].
  - destruct (inv_all n) as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [BE _]]]]]]]]]]]].
    apply (vbound_mono (itw n)); [left; pose proof (itw_gt n); pose proof winf_pos; lra | exact BE].
  - unfold kdE. replace 0 with (winf - winf) by ring. apply vbound_vlc; [apply winf_pos | exact Dn].
  - apply (vbound_mono winf); [apply winf_nonneg |].
    apply (vbound_feq' _ _ _ _ (feq_sym2 _ _ (Vdiff_feq (DVf F K) K Kstar))).
    apply vbound_vadd.
    + exact (Mtaylor winf K Kstar (Kn_good n) Kstar_good (ceps n) Dn).
    + apply vbound_mapp; [apply winf_nonneg | exact (MBD _ _ (Kn_good n)) | exact Dn].
Qed.

Lemma errb_lim : is_lim_seq errb 0.
Proof.
  assert (Hi : is_lim_seq iteps 0).
  { apply (is_lim_seq_le_le (fun _ => 0) iteps (fun n => eps0 * (/ 32) ^ n)).
    - intros n. split; [apply iteps_nonneg | apply iteps_decay].
    - apply is_lim_seq_const.
    - replace (Finite 0) with (Rbar_mult eps0 0) by (simpl; f_equal; ring).
      apply is_lim_seq_scal_l. apply is_lim_seq_geom. rewrite Rabs_pos_eq by lra. lra. }
  assert (Hc := ceps_lim).
  assert (H : is_lim_seq errb (0 + ((Rabs om + / kappa) * kdE winf * 0 + (cM2 c * (0 * 0) + 2 * (cD c * 0))))).
  { unfold errb.
    apply is_lim_seq_plus'; [exact Hi |].
    apply is_lim_seq_plus'.
    - apply (is_lim_seq_mult' (fun _ => (Rabs om + / kappa) * kdE winf) ceps); [apply is_lim_seq_const | exact Hc].
    - apply is_lim_seq_plus'.
      + apply (is_lim_seq_mult' (fun _ => cM2 c) (fun n => ceps n * ceps n)); [apply is_lim_seq_const |].
        apply is_lim_seq_mult'; exact Hc.
      + apply (is_lim_seq_mult' (fun _ => 2) (fun n => cD c * ceps n)); [apply is_lim_seq_const |].
        apply (is_lim_seq_mult' (fun _ => cD c) ceps); [apply is_lim_seq_const | exact Hc]. }
  replace (0 + ((Rabs om + / kappa) * kdE winf * 0 + (cM2 c * (0 * 0) + 2 * (cD c * 0)))) with 0 in H by ring.
  exact H.
Qed.

Lemma zero_of_lim (x : R) (a : nat -> R) : is_lim_seq a 0 -> (forall n, Rabs x <= a n) -> x = 0.
Proof.
  intros Ha H. destruct (Req_dec x 0) as [E | E]; [exact E | exfalso].
  assert (Hp : 0 < Rabs x / 2) by (apply Rdiv_lt_0_compat; [apply Rabs_pos_lt, E | lra]).
  apply is_lim_seq_spec in Ha. destruct (Ha (mkposreal _ Hp)) as [Nn HNn].
  specialize (HNn Nn (le_n Nn)). simpl in HNn. pose proof (H Nn). apply Rabs_lt_between in HNn. lra.
Qed.

Lemma Kstar_err_coef (m n : Z) :
  fc (vR (kerr F om Kstar)) m n = 0 /\ fs (vR (kerr F om Kstar)) m n = 0 /\
  fc (vZ (kerr F om Kstar)) m n = 0 /\ fs (vZ (kerr F om Kstar)) m n = 0.
Proof.
  repeat split; apply (zero_of_lim _ errb errb_lim); intros k; destruct (Kstar_err k) as [B1 B2].
  - exact (coef_le 0 _ _ m n (Rle_refl 0) B1).
  - exact (tbound_fs 0 _ _ (Rle_refl 0) B1 m n).
  - exact (coef_le 0 _ _ m n (Rle_refl 0) B2).
  - exact (tbound_fs 0 _ _ (Rle_refl 0) B2 m n).
Qed.

Lemma feval_zero_coef (u : fser) (t p : R) : (forall m n, fc u m n = 0 /\ fs u m n = 0) -> feval u t p = 0.
Proof.
  intros H. unfold feval. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_const0 |].
  intros m n. unfold term. destruct (H m n) as [H1 H2]. rewrite H1, H2. ring.
Qed.

(** The limit torus solves the invariance equation L K = V(K) at every point. *)
Theorem kam_limit (t p : R) :
  feval (lc om (vR Kstar)) t p = feval (vR (Vf F Kstar)) t p /\
  feval (lc om (vZ Kstar)) t p = feval (vZ (Vf F Kstar)) t p.
Proof.
  assert (Fl : vfin 0 (vlc om Kstar)).
  { replace 0 with (winf - winf) by ring. apply vfin_vlc; [apply winf_pos | apply good_vfin, Kstar_good]. }
  assert (FV : vfin 0 (Vf F Kstar)).
  { apply (vfin_mono winf); [apply winf_nonneg |]. destruct (MBV _ _ Kstar_good) as [B1 B2].
    split; eexists; eassumption. }
  assert (ER : feval (vR (kerr F om Kstar)) t p = 0).
  { apply feval_zero_coef. intros m n. destruct (Kstar_err_coef m n) as [H1 [H2 _]]. split; assumption. }
  assert (EZ : feval (vZ (kerr F om Kstar)) t p = 0).
  { apply feval_zero_coef. intros m n. destruct (Kstar_err_coef m n) as [_ [_ [H3 H4]]]. split; assumption. }
  unfold kerr in ER, EZ. cbn [vR vZ vsub vlc] in ER, EZ.
  assert (FlR : fin 0 (lc om (vR Kstar))) by exact (proj1 Fl).
  assert (FlZ : fin 0 (lc om (vZ Kstar))) by exact (proj2 Fl).
  rewrite (feval_fsub' t p _ _ FlR (proj1 FV)) in ER.
  rewrite (feval_fsub' t p _ _ FlZ (proj2 FV)) in EZ.
  split; lra.
Qed.

(** * The invariant torus in space

    With p = s phi for s field periods, the field model gives the field-line
    velocity: s V(K) = (R B_R / B_phi, R B_Z / B_phi) at the torus. The limit
    torus, read at the geometric angle phi, then solves the invariance
    equation of Invariance.v with rotation s om per radian of phi, and is an
    invariant torus of B within 2 kP eps_0 of the first torus in R and in Z
    at every angle. *)

Variable B : Hypotheses.vec3 -> Hypotheses.vec3.
Variable s : R.
Hypothesis Hs : 0 < s.
Hypothesis Msem : forall w K, good w K -> forall t p,
  Invariance.B_phi B (feval (vR K) t p) (p / s) (feval (vZ K) t p) <> 0 /\
  s * feval (vR (Vf F K)) t p
    = feval (vR K) t p * Invariance.B_R B (feval (vR K) t p) (p / s) (feval (vZ K) t p)
      / Invariance.B_phi B (feval (vR K) t p) (p / s) (feval (vZ K) t p) /\
  s * feval (vZ (Vf F K)) t p
    = feval (vR K) t p * Invariance.B_Z B (feval (vR K) t p) (p / s) (feval (vZ K) t p)
      / Invariance.B_phi B (feval (vR K) t p) (p / s) (feval (vZ K) t p).

Definition KRs (theta phi : R) : R := feval (vR Kstar) theta (s * phi).
Definition KZs (theta phi : R) : R := feval (vZ Kstar) theta (s * phi).

Lemma is_derive_times (phi : R) : is_derive (fun x => s * x) phi s.
Proof. auto_derive; [exact I | ring]. Qed.

Theorem kam_param : Invariance.param_invariant B KRs KZs (s * om).
Proof.
  intros theta phi.
  destruct (good_vfin _ _ Kstar_good) as [[MR HR] [MZ HZ]].
  pose proof winf_pos as Hw.
  destruct (Msem _ _ Kstar_good theta (s * phi)) as [Hb [ER EZ]].
  replace (s * phi / s) with phi in Hb, ER, EZ by (field; lra).
  destruct (kam_limit theta (s * phi)) as [L1 L2].
  rewrite (feval_lc om winf MR (vR Kstar) theta (s * phi) Hw HR) in L1.
  rewrite (feval_lc om winf MZ (vZ Kstar) theta (s * phi) Hw HZ) in L2.
  exists (feval (dt (vR Kstar)) theta (s * phi)), (s * feval (dp (vR Kstar)) theta (s * phi)),
         (feval (dt (vZ Kstar)) theta (s * phi)), (s * feval (dp (vZ Kstar)) theta (s * phi)).
  unfold KRs, KZs.
  refine (conj _ (conj _ (conj _ (conj _ (conj Hb (conj _ _)))))).
  - exact (feval_dt winf MR (vR Kstar) (s * phi) theta Hw HR).
  - exact (is_derive_comp (fun y => feval (vR Kstar) theta y) (fun x => s * x) phi _ s
             (feval_dp winf MR (vR Kstar) theta (s * phi) Hw HR) (is_derive_times phi)).
  - exact (feval_dt winf MZ (vZ Kstar) (s * phi) theta Hw HZ).
  - exact (is_derive_comp (fun y => feval (vZ Kstar) theta y) (fun x => s * x) phi _ s
             (feval_dp winf MZ (vZ Kstar) theta (s * phi) Hw HZ) (is_derive_times phi)).
  - rewrite <- ER. rewrite <- L1. ring.
  - rewrite <- EZ. rewrite <- L2. ring.
Qed.

Theorem kam_invariant_torus : Hypotheses.invariant_torus B (Invariance.torus_of KRs KZs).
Proof. exact (Invariance.param_invariant_torus B KRs KZs (s * om) kam_param). Qed.

Theorem kam_close (theta phi : R) :
  Rabs (KRs theta phi - feval (vR K0) theta (s * phi)) <= 2 * (kP c gamma d0 * eps0) /\
  Rabs (KZs theta phi - feval (vZ K0) theta (s * phi)) <= 2 * (kP c gamma d0 * eps0).
Proof.
  destruct Kstar_ball as [B1 B2].
  destruct (good_vfin _ _ Kstar_good) as [[MR HR] [MZ HZ]].
  destruct (vfin_mono w0 winf K0 ltac:(unfold winf; lra) FK0) as [[M1 F1] [M2 F2]].
  pose proof winf_nonneg as Hw.
  unfold KRs, KZs. split.
  - rewrite <- (feval_fsub _ _ _ _ theta (s * phi) (nbound_mono winf 0 _ _ Hw HR) (nbound_mono winf 0 _ _ Hw F1)).
    apply feval_bound. exact (nbound_mono winf 0 _ _ Hw B1).
  - rewrite <- (feval_fsub _ _ _ _ theta (s * phi) (nbound_mono winf 0 _ _ Hw HZ) (nbound_mono winf 0 _ _ Hw F2)).
    apply feval_bound. exact (nbound_mono winf 0 _ _ Hw B2).
Qed.

(** The limit torus is the pair of families of K*, finite on the strip of
    width winf, read at s phi. *)
Theorem kam_fourier : TorusLine.fourier_torus B KRs KZs (s * om).
Proof.
  destruct (good_vfin _ _ Kstar_good) as [[MR HR] [MZ HZ]].
  exists (vR Kstar), (vZ Kstar), winf, MR, MZ, s.
  refine (conj winf_pos (conj HR (conj HZ (conj _ (conj _ kam_param))))); intros t p; reflexivity.
Qed.

End Iter.
