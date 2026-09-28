(** The twist of the first frame from a finite model of the field.

    The field enters the twist T = sigma (L N - DV N) ^ N of the Newton step
    through sigma = B_phi and the derivative DV of the field-line velocity,
    and the frame through N = g J a + b a ([twistx]). Replacing the nine
    field jets and the inverse of B_phi by finite families gives a finite
    model of DV ([fDV]), and replacing the frame inverse g by its finite seed
    gives a twist that is a finite family, whose norm and mean a grid gives
    exactly. The true DV lies within [eDVc] of the finite one, from the
    changes of the jets and of the inverse ([dv_diff]); the true N lies
    within eg |a| of the finite one ([knrm_diff]); and the true twist lies
    within [eT] of the finite one, L of the change of N costing the loss of
    a strip ([twist_diff]), so its mean lies within [eT] of the finite mean
    ([twist_mean]). The frame inverse is the inverse of sigma |a|^2 from a
    finite seed, and its bound and its distance to the seed follow from the
    defect of the seed ([frame_G], [frame_eg], [frame_id]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer KAMVec KAMFin KAMPer KAMStep KAMDiff.
Local Open Scope R_scope.

(** * Differences of sums and multiples *)

Lemma nbound_self (rho M : R) (u : fser) : nbound rho M u -> nbound rho 0 (fsub u u).
Proof.
  intros H. apply (nbound_feq rho 0 (fscal 0 u) (fsub u u)).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply (nbound_le _ (Rabs 0 * M)); [rewrite Rabs_R0; lra | apply nbound_fscal, H].
Qed.

Lemma nbound_sub_sub (rho A B : R) (u u' v v' : fser) :
  nbound rho A (fsub u u') -> nbound rho B (fsub v v') -> nbound rho (A + B) (fsub (fsub u v) (fsub u' v')).
Proof.
  intros H1 H2. apply (nbound_feq rho _ (fsub (fsub u u') (fsub v v'))).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply nbound_fsub; assumption.
Qed.

Lemma nbound_add_add (rho A B : R) (u u' v v' : fser) :
  nbound rho A (fsub u u') -> nbound rho B (fsub v v') -> nbound rho (A + B) (fsub (fadd u v) (fadd u' v')).
Proof.
  intros H1 H2. apply (nbound_feq rho _ (fadd (fsub u u') (fsub v v'))).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply nbound_fadd; assumption.
Qed.

Lemma nbound_scal_sub (rho A c : R) (u u' : fser) :
  nbound rho A (fsub u u') -> nbound rho (Rabs c * A) (fsub (fscal c u) (fscal c u')).
Proof.
  intros H. apply (nbound_feq rho _ (fscal c (fsub u u'))).
  - intros m n. unfold fsub. fnorm. split; ring.
  - apply nbound_fscal, H.
Qed.

(** * The derivative of the field-line velocity from nine jets and an inverse *)

Section Model.

Variables (KR U : fser) (Jt : nat -> fser).

Definition fW : fser := fmul KR U.
Definition fUP (i : nat) : fser := fmul U (Jt i).
Definition fWR : fser := fsub U (fmul fW (fUP 5)).
Definition fWZ : fser := fscal (-1) (fmul fW (fUP 6)).

(** The jets in the order R, phi, Z, then the R and Z derivatives of the
    three components. *)
Definition fDV : mf :=
  mkmf (fadd (fmul fWR (Jt 0)) (fmul fW (Jt 3))) (fadd (fmul fWZ (Jt 0)) (fmul fW (Jt 4)))
       (fadd (fmul fWR (Jt 2)) (fmul fW (Jt 7))) (fadd (fmul fWZ (Jt 2)) (fmul fW (Jt 8))).

End Model.

Section DVDiff.

Variables (rho : R) (KR U Ub : fser) (Jt Jf : nat -> fser) (kR MU eU : R) (nj ej : nat -> R).
Hypothesis Hr : 0 <= rho.
Hypothesis HKR : nbound rho kR KR.
Hypothesis HUb : nbound rho MU Ub.
Hypothesis HeU : nbound rho eU (fsub U Ub).
Hypothesis Hnj : forall i, nbound rho (nj i) (Jf i).
Hypothesis Hej : forall i, (i < 9)%nat -> nbound rho (ej i) (fsub (Jt i) (Jf i)).

Definition nJ (i : nat) : R := nj i + ej i.
Definition nU : R := MU + eU.
Definition eW : R := 0 * nU + kR * eU.
Definition nWf : R := kR * MU.
Definition eUP (i : nat) : R := eU * nJ i + MU * ej i.
Definition nUP (i : nat) : R := nU * nJ i.
Definition nUPf (i : nat) : R := MU * nj i.
Definition eWUP (i : nat) : R := eW * nUP i + nWf * eUP i.
Definition eWR : R := eU + eWUP 5.
Definition nWRf : R := MU + nWf * nUPf 5.
Definition eWZ : R := Rabs (-1) * eWUP 6.
Definition nWZf : R := Rabs (-1) * (nWf * nUPf 6).

(** The bound of the change of an entry X Jt i + W Jt j, and of the finite entry. *)
Definition eDVc (eX nXf : R) (i j : nat) : R := (eX * nJ i + nXf * ej i) + (eW * nJ j + nWf * ej j).
Definition nDVc (nXf : R) (i j : nat) : R := nXf * nj i + nWf * nj j.

Lemma nb_U : nbound rho nU U.
Proof. exact (nbound_add_diff rho MU eU Ub U HUb HeU). Qed.

Lemma nb_Jt (i : nat) : (i < 9)%nat -> nbound rho (nJ i) (Jt i).
Proof. intros Hi. exact (nbound_add_diff rho (nj i) (ej i) (Jf i) (Jt i) (Hnj i) (Hej i Hi)). Qed.

Lemma e_W : nbound rho eW (fsub (fW KR U) (fW KR Ub)).
Proof. exact (fmul_diff rho kR nU 0 eU KR KR Ub U Hr HKR nb_U (nbound_self rho kR KR HKR) HeU). Qed.

Lemma n_Wf : nbound rho nWf (fW KR Ub).
Proof. exact (nbound_fmul rho kR MU KR Ub Hr HKR HUb). Qed.

Lemma e_UP (i : nat) : (i < 9)%nat -> nbound rho (eUP i) (fsub (fUP U Jt i) (fUP Ub Jf i)).
Proof. intros Hi. exact (fmul_diff rho MU (nJ i) eU (ej i) Ub U (Jf i) (Jt i) Hr HUb (nb_Jt i Hi) HeU (Hej i Hi)). Qed.

Lemma n_UP (i : nat) : (i < 9)%nat -> nbound rho (nUP i) (fUP U Jt i).
Proof. intros Hi. exact (nbound_fmul rho nU (nJ i) U (Jt i) Hr nb_U (nb_Jt i Hi)). Qed.

Lemma n_UPf (i : nat) : nbound rho (nUPf i) (fUP Ub Jf i).
Proof. exact (nbound_fmul rho MU (nj i) Ub (Jf i) Hr HUb (Hnj i)). Qed.

Lemma e_WUP (i : nat) : (i < 9)%nat ->
  nbound rho (eWUP i) (fsub (fmul (fW KR U) (fUP U Jt i)) (fmul (fW KR Ub) (fUP Ub Jf i))).
Proof.
  intros Hi.
  exact (fmul_diff rho nWf (nUP i) eW (eUP i) (fW KR Ub) (fW KR U) (fUP Ub Jf i) (fUP U Jt i) Hr n_Wf (n_UP i Hi)
           e_W (e_UP i Hi)).
Qed.

Lemma e_WR : nbound rho eWR (fsub (fWR KR U Jt) (fWR KR Ub Jf)).
Proof. exact (nbound_sub_sub rho _ _ _ _ _ _ HeU (e_WUP 5 ltac:(lia))). Qed.

Lemma n_WRf : nbound rho nWRf (fWR KR Ub Jf).
Proof. exact (nbound_fsub rho _ _ _ _ HUb (nbound_fmul rho _ _ _ _ Hr n_Wf (n_UPf 5))). Qed.

Lemma e_WZ : nbound rho eWZ (fsub (fWZ KR U Jt) (fWZ KR Ub Jf)).
Proof. exact (nbound_scal_sub rho _ (-1) _ _ (e_WUP 6 ltac:(lia))). Qed.

Lemma n_WZf : nbound rho nWZf (fWZ KR Ub Jf).
Proof. exact (nbound_fscal rho _ (-1) _ (nbound_fmul rho _ _ _ _ Hr n_Wf (n_UPf 6))). Qed.

Lemma e_entry (X X' : fser) (eX nXf : R) (i j : nat) : (i < 9)%nat -> (j < 9)%nat ->
  nbound rho eX (fsub X' X) -> nbound rho nXf X ->
  nbound rho (eDVc eX nXf i j)
    (fsub (fadd (fmul X' (Jt i)) (fmul (fW KR U) (Jt j))) (fadd (fmul X (Jf i)) (fmul (fW KR Ub) (Jf j)))).
Proof.
  intros Hi Hj He Hn. apply nbound_add_add.
  - exact (fmul_diff rho nXf (nJ i) eX (ej i) X X' (Jf i) (Jt i) Hr Hn (nb_Jt i Hi) He (Hej i Hi)).
  - exact (fmul_diff rho nWf (nJ j) eW (ej j) (fW KR Ub) (fW KR U) (Jf j) (Jt j) Hr n_Wf (nb_Jt j Hj) e_W (Hej j Hj)).
Qed.

Lemma n_entry (X : fser) (nXf : R) (i j : nat) :
  nbound rho nXf X -> nbound rho (nDVc nXf i j) (fadd (fmul X (Jf i)) (fmul (fW KR Ub) (Jf j))).
Proof.
  intros Hn. apply nbound_fadd; [exact (nbound_fmul rho _ _ _ _ Hr Hn (Hnj i)) |].
  exact (nbound_fmul rho _ _ _ _ Hr n_Wf (Hnj j)).
Qed.

(** The four entries of DV less those of the finite model, and the finite ones. *)
Theorem dv_diff :
  nbound rho (eDVc eWR nWRf 0 3) (mRR (msub (fDV KR U Jt) (fDV KR Ub Jf))) /\
  nbound rho (eDVc eWZ nWZf 0 4) (mRZ (msub (fDV KR U Jt) (fDV KR Ub Jf))) /\
  nbound rho (eDVc eWR nWRf 2 7) (mZR (msub (fDV KR U Jt) (fDV KR Ub Jf))) /\
  nbound rho (eDVc eWZ nWZf 2 8) (mZZ (msub (fDV KR U Jt) (fDV KR Ub Jf))).
Proof.
  cbn [msub fDV mRR mRZ mZR mZZ].
  refine (conj _ (conj _ (conj _ _))).
  - exact (e_entry _ _ _ _ 0 3 ltac:(lia) ltac:(lia) e_WR n_WRf).
  - exact (e_entry _ _ _ _ 0 4 ltac:(lia) ltac:(lia) e_WZ n_WZf).
  - exact (e_entry _ _ _ _ 2 7 ltac:(lia) ltac:(lia) e_WR n_WRf).
  - exact (e_entry _ _ _ _ 2 8 ltac:(lia) ltac:(lia) e_WZ n_WZf).
Qed.

Theorem dvf_norm :
  nbound rho (nDVc nWRf 0 3) (mRR (fDV KR Ub Jf)) /\ nbound rho (nDVc nWZf 0 4) (mRZ (fDV KR Ub Jf)) /\
  nbound rho (nDVc nWRf 2 7) (mZR (fDV KR Ub Jf)) /\ nbound rho (nDVc nWZf 2 8) (mZZ (fDV KR Ub Jf)).
Proof.
  cbn [fDV mRR mRZ mZR mZZ].
  exact (conj (n_entry _ _ 0 3 n_WRf) (conj (n_entry _ _ 0 4 n_WZf) (conj (n_entry _ _ 2 7 n_WRf)
          (n_entry _ _ 2 8 n_WZf)))).
Qed.

End DVDiff.

(** * The twist *)

Definition kmlnx (om : R) (DV : mf) (N : vf) : vf := vsub (vlc om N) (mapp DV N).
Definition twistx (om : R) (sig : fser) (DV : mf) (N : vf) : fser := fmul sig (wedge (kmlnx om DV N) N).

Lemma ktwist_x (F : fmodel) (om : R) (K : vf) (g b : fser) :
  ktwist F om K g b = twistx om (Sf F K) (DVf F K) (knrm K g b).
Proof. reflexivity. Qed.

Section Normal.

Variables (w : R) (K : vf) (g gs b : fser) (A eg Mg Mb : R).
Hypothesis Hw : 0 <= w.
Hypothesis HA : vbound w A (vdt K).
Hypothesis Hg : nbound w eg (fsub g gs).
Hypothesis Hgs : nbound w Mg gs.
Hypothesis Hb : nbound w Mb b.

(** N moves by the change of g times J a. *)
Theorem knrm_diff : vbound w (eg * A) (vsub (knrm K g b) (knrm K gs b)).
Proof.
  destruct HA as [A1 A2].
  assert (J2 : nbound w (Rabs (-1) * A) (fscal (-1) (vZ (vdt K)))) by (apply nbound_fscal, A2).
  assert (E : Rabs (-1) = 1) by (rewrite Rabs_left by lra; ring).
  pose proof (nbound_nonneg _ _ _ A1) as HA0. pose proof (nbound_nonneg _ _ _ Hg) as Hg0.
  split; unfold knrm, ktng; cbn [vsub vadd vsmul vJ vR vZ].
  - pose proof (nbound_add_add w _ _ _ _ _ _
                  (fmul_diff w Mg (Rabs (-1) * A) eg 0 gs g _ _ Hw Hgs J2 Hg (nbound_self w _ _ J2))
                  (nbound_self w _ _ (nbound_fmul w _ _ _ _ Hw Hb A1))) as H.
    eapply nbound_le; [| exact H]. rewrite E. nra.
  - pose proof (nbound_add_add w _ _ _ _ _ _
                  (fmul_diff w Mg A eg 0 gs g _ _ Hw Hgs A1 Hg (nbound_self w _ _ A1))
                  (nbound_self w _ _ (nbound_fmul w _ _ _ _ Hw Hb A2))) as H.
    eapply nbound_le; [| exact H]. nra.
Qed.

End Normal.

Section Twist.

Variables (om w d : R) (sig sigf : fser) (DV DVf : mf) (N Nf : vf).
Variables (eN nNf nkmf nsf eS eDV nDVf : R).
Hypothesis Hd : 0 < d.
Hypothesis Hwd : d <= w.
Hypothesis HeN : vbound w eN (vsub N Nf).
Hypothesis HNf : vbound w nNf Nf.
Hypothesis Hkmf : vbound (w - d) nkmf (kmlnx om DVf Nf).
Hypothesis Hsf : nbound w nsf sigf.
Hypothesis HeS : nbound w eS (fsub sig sigf).
Hypothesis HeDV : mbound w eDV (msub DV DVf).
Hypothesis HDVf : mbound w nDVf DVf.

Definition cL : R := (Rabs om + / kappa) * / (exp 1 * d).
Definition nNx : R := nNf + eN.
Definition ekm : R := cL * eN + 2 * (eDV * nNx + nDVf * eN).
Definition nkm : R := nkmf + ekm.
Definition eT : R := eS * (2 * (nkm * nNx)) + nsf * (2 * (ekm * nNx + nkmf * eN)).

Lemma tw_w0 : 0 <= w. Proof. lra. Qed.
Lemma tw_wd0 : 0 <= w - d. Proof. lra. Qed.
Lemma tw_le : w - d <= w. Proof. lra. Qed.

Lemma nb_N : vbound w nNx N.
Proof.
  destruct HNf as [A1 A2]. destruct HeN as [E1 E2]. unfold nNx.
  split; [exact (nbound_add_diff w _ _ _ _ A1 E1) | exact (nbound_add_diff w _ _ _ _ A2 E2)].
Qed.

Lemma e_km : vbound (w - d) ekm (vsub (kmlnx om DV N) (kmlnx om DVf Nf)).
Proof.
  pose proof (vbound_vlc om w d eN (vsub N Nf) Hd HeN) as HL. fold cL in HL. destruct HL as [L1 L2].
  destruct (vlc_sub_feq om Nf N) as [F1 F2].
  pose proof (mapp_diff w nDVf nNx eDV eN DVf DV Nf N tw_w0 HDVf nb_N HeDV HeN) as HM.
  destruct (vbound_mono w (w - d) _ _ tw_le HM) as [M1 M2].
  unfold kmlnx, ekm. split; cbn [vsub vR vZ].
  - apply nbound_sub_sub; [| exact M1]. apply (nbound_feq _ _ _ _ (feq_sym _ _ F1)). exact L1.
  - apply nbound_sub_sub; [| exact M2]. apply (nbound_feq _ _ _ _ (feq_sym _ _ F2)). exact L2.
Qed.

Lemma nb_km : vbound (w - d) nkm (kmlnx om DV N).
Proof.
  destruct Hkmf as [A1 A2]. destruct e_km as [E1 E2]. unfold nkm.
  split; [exact (nbound_add_diff _ _ _ _ _ A1 E1) | exact (nbound_add_diff _ _ _ _ _ A2 E2)].
Qed.

(** The twist less the finite twist. *)
Theorem twist_diff : nbound (w - d) eT (fsub (twistx om sig DV N) (twistx om sigf DVf Nf)).
Proof.
  pose proof (vbound_mono w (w - d) _ _ tw_le nb_N) as BN.
  pose proof (vbound_mono w (w - d) _ _ tw_le HeN) as BeN.
  pose proof (wedge_diff (w - d) nkmf nNx ekm eN (kmlnx om DVf Nf) (kmlnx om DV N) Nf N tw_wd0 Hkmf BN e_km BeN)
    as HW.
  pose proof (nbound_wedge (w - d) nkm nNx (kmlnx om DV N) N tw_wd0 nb_km BN) as NW.
  unfold twistx, eT.
  exact (fmul_diff (w - d) nsf (2 * (nkm * nNx)) eS (2 * (ekm * nNx + nkmf * eN)) sigf sig
           (wedge (kmlnx om DVf Nf) Nf) (wedge (kmlnx om DV N) N) tw_wd0 (nbound_mono w (w - d) _ _ tw_le Hsf) NW
           (nbound_mono w (w - d) _ _ tw_le HeS) HW).
Qed.

Theorem twist_norm (nTf : R) : nbound (w - d) nTf (twistx om sigf DVf Nf) ->
  nbound (w - d) (nTf + eT) (twistx om sig DV N).
Proof. intros H. exact (nbound_add_diff _ _ _ _ _ H twist_diff). Qed.

Theorem twist_mean : Rabs (fc (twistx om sigf DVf Nf) 0 0) - eT <= Rabs (fc (twistx om sig DV N) 0 0).
Proof.
  pose proof (coef_le (w - d) eT _ 0 0 tw_wd0 twist_diff) as C.
  unfold fsub in C. rewrite fc_fadd', fc_fscal' in C.
  pose proof (Rabs_triang_inv (fc (twistx om sigf DVf Nf) 0 0) (fc (twistx om sig DV N) 0 0)) as T.
  replace (fc (twistx om sig DV N) 0 0 + -1 * fc (twistx om sigf DVf Nf) 0 0)
    with (- (fc (twistx om sigf DVf Nf) 0 0 - fc (twistx om sig DV N) 0 0)) in C by ring.
  rewrite Rabs_Ropp in C. lra.
Qed.

End Twist.

(** * The frame inverse *)

Section Frame.

Variables (rho : R) (sig asq gs : fser) (Ms Ma Mg th : R).
Hypothesis Hr : 0 < rho.
Hypothesis Hsig : nbound rho Ms sig.
Hypothesis Hasq : nbound rho Ma asq.
Hypothesis Hgs : nbound rho Mg gs.
Hypothesis Hth : 0 <= th < 1.
Hypothesis Hdef : nbound rho th (fsub fone (fmul (fmul sig asq) gs)).

Definition g0f : fser := finv (fmul sig asq) gs.

Lemma fr_r : 0 <= rho. Proof. lra. Qed.

Theorem frame_G : nbound rho (Mg + inv_eps Mg th 0) g0f.
Proof. exact (nbound_finv rho fr_r (fmul sig asq) gs Mg th Hgs Hth Hdef). Qed.

Theorem frame_eg : nbound rho (inv_eps Mg th 0) (fsub g0f gs).
Proof. apply nbound_fsub_sym. exact (nbound_finv_sub rho fr_r (fmul sig asq) gs Mg th Hgs Hth Hdef). Qed.

Theorem frame_id (t p : R) : feval sig t p * feval asq t p * feval g0f t p = 1.
Proof.
  pose proof (nbound_fmul rho _ _ _ _ fr_r Hsig Hasq) as Hu.
  pose proof (feval_finv rho fr_r (fmul sig asq) gs (Ms * Ma) Mg th Hu Hgs Hth Hdef t p) as E.
  rewrite (feval_fmul sig asq Ms Ma t p (nbound_mono rho 0 _ _ fr_r Hsig) (nbound_mono rho 0 _ _ fr_r Hasq)) in E.
  exact E.
Qed.

End Frame.
