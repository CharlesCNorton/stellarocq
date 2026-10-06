(** The finite twist on a grid.

    KTwist.v compares the twist with the twist of a finite model, built from
    the dense finite families of the certificate: the first torus, the seed
    gs of the frame inverse, the straightening family b, the seed Ub of
    1 / B_phi and the nine jet approximants. At a point, the finite normal N,
    the field L N - DV N of the finite model and the finite twist are one
    expression [tpt] in the values there of 23 dense families: R, the t
    derivatives of R and Z and the t and p derivatives of those, gs and b
    with their t and p derivatives, Ub and the jets ([tpt_ok]). Each of the
    five is carried by a box of modes that the boxes of its factors fix
    ([SN], [SK], [ST]), so a grid past that box gives its norm and its mean
    exactly; each is canonical and of the field period ([tf_canon],
    [tf_per]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierList FourierSupp KAMVec KAMFin KAMPer KAMStep KAMDiff
  KFix KCheckKern KEngine KDense KSrc KTwist.
Import ListNotations.
Local Open Scope R_scope.

(** * Families finite on every strip *)

Definition afin (u : fser) : Prop := forall rho, fin rho u.

Lemma afin_cden (f : list (Z * list (Z * (R * R)))) : afin (cden f).
Proof. intros rho. exists (esum (ewt rho) (dents f)). apply nbound_cden. Qed.

Lemma afin_fadd (u v : fser) : afin u -> afin v -> afin (fadd u v).
Proof. intros Hu Hv rho. apply fin_fadd; [apply Hu | apply Hv]. Qed.

Lemma afin_fsub (u v : fser) : afin u -> afin v -> afin (fsub u v).
Proof. intros Hu Hv rho. apply fin_fsub; [apply Hu | apply Hv]. Qed.

Lemma afin_fscal (c : R) (u : fser) : afin u -> afin (fscal c u).
Proof. intros Hu rho. apply fin_fscal, Hu. Qed.

Lemma afin_fmul (u v : fser) : afin u -> afin v -> afin (fmul u v).
Proof.
  intros Hu Hv rho. destruct (Rle_or_lt 0 rho) as [H | H].
  - apply fin_fmul; [exact H | apply Hu | apply Hv].
  - apply (fin_mono 0); [lra |]. apply fin_fmul; [lra | apply Hu | apply Hv].
Qed.

Lemma afin_dt (u : fser) : afin u -> afin (dt u).
Proof. intros Hu rho. replace rho with ((rho + 1) - 1) by ring. apply fin_dt; [lra | apply Hu]. Qed.

Lemma afin_dp (u : fser) : afin u -> afin (dp u).
Proof.
  intros Hu rho. destruct (Hu (rho + 1)) as [M H]. exists (/ kappa * (/ (exp 1 * 1) * M)).
  replace rho with ((rho + 1) - 1) by ring. apply nbound_dp; [lra | exact H].
Qed.

Lemma afin_lc (om : R) (u : fser) : afin u -> afin (lc om u).
Proof. intros Hu rho. replace rho with ((rho + 1) - 1) by ring. apply fin_lc; [lra | apply Hu]. Qed.

Ltac afin_tac := repeat (first [assumption | apply afin_fadd | apply afin_fsub | apply afin_fscal | apply afin_fmul
                                | apply afin_dt | apply afin_dp | apply afin_lc | apply afin_cden]).

(** * Values at a point *)

Lemma dt_feq_congr (u v : fser) : feq u v -> feq (dt u) (dt v).
Proof. intros H m n. destruct (H m n) as [A B]. cbn [dt fc fs]. rewrite A, B. split; reflexivity. Qed.

Lemma dp_feq_congr (u v : fser) : feq u v -> feq (dp u) (dp v).
Proof. intros H m n. destruct (H m n) as [A B]. cbn [dp fc fs]. rewrite A, B. split; reflexivity. Qed.

Section Eval.

Variables (om t p : R).

Lemma ev_add (u v : fser) : afin u -> afin v -> feval (fadd u v) t p = feval u t p + feval v t p.
Proof. intros Hu Hv. exact (feval_fadd' t p u v (Hu 0) (Hv 0)). Qed.

Lemma ev_sub (u v : fser) : afin u -> afin v -> feval (fsub u v) t p = feval u t p - feval v t p.
Proof. intros Hu Hv. exact (feval_fsub' t p u v (Hu 0) (Hv 0)). Qed.

Lemma ev_scal (c : R) (u : fser) : afin u -> feval (fscal c u) t p = c * feval u t p.
Proof. intros Hu. exact (feval_fscal' t p c u (Hu 0)). Qed.

Lemma ev_mul (u v : fser) : afin u -> afin v -> feval (fmul u v) t p = feval u t p * feval v t p.
Proof. intros Hu Hv. exact (feval_fmul' t p u v (Hu 0) (Hv 0)). Qed.

Lemma ev_lc (u : fser) : afin u -> feval (lc om u) t p = om * feval (dt u) t p + feval (dp u) t p.
Proof. intros Hu. destruct (Hu 1) as [M H]. exact (feval_lc om 1 M u t p Rlt_0_1 H). Qed.

Lemma ev_lc_mul (u v : fser) : afin u -> afin v ->
  feval (lc om (fmul u v)) t p = feval (lc om u) t p * feval v t p + feval u t p * feval (lc om v) t p.
Proof.
  intros Hu Hv. destruct (Hu 1) as [Mu A]. destruct (Hv 1) as [Mv B].
  exact (feval_lc_fmul om 1 Mu Mv u v t p Rlt_0_1 A B).
Qed.

Lemma ev_lc_add (u v : fser) : afin u -> afin v ->
  feval (lc om (fadd u v)) t p = feval (lc om u) t p + feval (lc om v) t p.
Proof.
  intros Hu Hv. rewrite (feval_feq _ (fadd (lc om u) (lc om v)) t p).
  - apply ev_add; apply afin_lc; assumption.
  - intros m n. cbn [lc fadd fc fs]. split; ring.
Qed.

Lemma ev_lc_scal (c : R) (u : fser) : afin u -> feval (lc om (fscal c u)) t p = c * feval (lc om u) t p.
Proof.
  intros Hu. rewrite (feval_feq _ (fscal c (lc om u)) t p).
  - apply ev_scal, afin_lc, Hu.
  - intros m n. cbn [lc fscal fc fs]. split; ring.
Qed.

Lemma ev_dcden (f : list (Z * list (Z * (R * R)))) : feval (dt (cden f)) t p = feval (cden (fam_dt f)) t p.
Proof. rewrite feval_dt_cden, feval_cden. reflexivity. Qed.

Lemma ev_pcden (f : list (Z * list (Z * (R * R)))) : feval (dp (cden f)) t p = feval (cden (fam_dp f)) t p.
Proof. rewrite feval_dp_cden, feval_cden. reflexivity. Qed.

Lemma ev_lcden (f : list (Z * list (Z * (R * R)))) :
  feval (lc om (cden f)) t p = om * feval (cden (fam_dt f)) t p + feval (cden (fam_dp f)) t p.
Proof. rewrite (ev_lc _ (afin_cden f)), ev_dcden, ev_pcden. reflexivity. Qed.

Lemma ev_lc_dcden (f : list (Z * list (Z * (R * R)))) :
  feval (lc om (dt (cden f))) t p
  = om * feval (cden (fam_dt (fam_dt f))) t p + feval (cden (fam_dp (fam_dt f))) t p.
Proof.
  rewrite (ev_lc _ (afin_dt _ (afin_cden f))).
  rewrite (feval_feq (dt (dt (cden f))) (dt (cden (fam_dt f))) t p (dt_feq_congr _ _ (dt_cden f))).
  rewrite (feval_feq (dp (dt (cden f))) (dp (cden (fam_dt f))) t p (dp_feq_congr _ _ (dt_cden f))).
  rewrite ev_dcden, ev_pcden. reflexivity.
Qed.

End Eval.

(** * Supports *)

Lemma supp_feq (K1 K2 : nat) (u v : fser) : feq u v -> supp K1 K2 u -> supp K1 K2 v.
Proof.
  intros E H m n Hb. destruct (E m n) as [A B]. destruct (H m n Hb) as [C D]. rewrite <- A, <- B. split; assumption.
Qed.

Lemma lc_supp (K1 K2 : nat) (om : R) (u : fser) : supp K1 K2 u -> supp K1 K2 (lc om u).
Proof.
  intros H. apply (supp_feq _ _ (fadd (fscal om (dt u)) (dp u))); [apply feq_sym, lc_feq |].
  apply fadd_supp; [apply fscal_supp, dt_supp, H | apply dp_supp, H].
Qed.

(** * The finite families of the certificate *)

Definition tjpar : list bool := [false; true; true; false; true; true; false; true; false].

Section TF.

Variables (Pn : nat) (s0 sJ : Z) (Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 : nat).
Variables (rowsR rowsZ rowsG rowsB rowsU : list (list Z)) (rowsJ : list (list (list Z))) (om : R).

Definition tfR : list (Z * list (Z * (R * R))) := dfam s0 (zrange Km) (pns (Z.of_nat Pn) Kn) (crows rowsR).
Definition tfZ : list (Z * list (Z * (R * R))) := dfam s0 (zrange Km) (pns (Z.of_nat Pn) Kn) (srows rowsZ).
Definition tfG : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmg) (pns (Z.of_nat Pn) Kng) (crows rowsG).
Definition tfB : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmb) (pns (Z.of_nat Pn) Knb) (srows rowsB).
Definition tfU : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmu) (pns (Z.of_nat Pn) Knu) (crows rowsU).
Definition tfJs : list (list (Z * list (Z * (R * R)))) :=
  map (fun x : bool * list (list Z) =>
         dfam sJ (zrange Kj1) (pns (Z.of_nat Pn) Kj2) (if fst x then crows (snd x) else srows (snd x)))
      (combine tjpar rowsJ).
Definition tfJ (i : nat) : list (Z * list (Z * (R * R))) := nth i tfJs [].

Definition tK0 : vf := mkvf (cden tfR) (cden tfZ).
Definition tgs : fser := cden tfG.
Definition tb : fser := cden tfB.
Definition tUb : fser := cden tfU.
Definition tJf (i : nat) : fser := cden (tfJ i).
Definition tNf : vf := knrm tK0 tgs tb.
Definition tDVf : mf := fDV (vR tK0) tUb tJf.
Definition tkmf : vf := kmlnx om tDVf tNf.
Definition tTf : fser := twistx om (tJf 1) tDVf tNf.

(** The 23 dense families a point reads. *)
Definition tbasics : list fser :=
  [cden tfR; cden (fam_dt tfR); cden (fam_dt tfZ); cden (fam_dt (fam_dt tfR)); cden (fam_dp (fam_dt tfR));
   cden (fam_dt (fam_dt tfZ)); cden (fam_dp (fam_dt tfZ)); tgs; cden (fam_dt tfG); cden (fam_dp tfG);
   tb; cden (fam_dt tfB); cden (fam_dp tfB); tUb] ++ map tJf (seq 0 9).

Definition tvals (t p : R) : list R :=
  [feval (vR tNf) t p; feval (vZ tNf) t p; feval (vR tkmf) t p; feval (vZ tkmf) t p; feval tTf t p].

Definition bvals (t p : R) : list R := map (fun u => feval u t p) tbasics.

End TF.

(** The five values at a point from the 23. *)
Definition tpt (om : R) (x : list R) : list R :=
  let v i := nth i x 0 in
  let aR := v 1%nat in let aZ := v 2%nat in
  let laR := om * v 3%nat + v 4%nat in let laZ := om * v 5%nat + v 6%nat in
  let g := v 7%nat in let lg := om * v 8%nat + v 9%nat in
  let bb := v 10%nat in let lb := om * v 11%nat + v 12%nat in
  let U := v 13%nat in let J i := v (14 + i)%nat in
  let W := v 0%nat * U in
  let WR := U - W * (U * J 5%nat) in let WZ := -1 * (W * (U * J 6%nat)) in
  let NR := g * (-1 * aZ) + bb * aR in let NZ := g * aR + bb * aZ in
  let lNR := (lg * (-1 * aZ) + g * (-1 * laZ)) + (lb * aR + bb * laR) in
  let lNZ := (lg * aR + g * laR) + (lb * aZ + bb * laZ) in
  let KR := lNR - ((WR * J 0%nat + W * J 3%nat) * NR + (WZ * J 0%nat + W * J 4%nat) * NZ) in
  let KZ := lNZ - ((WR * J 2%nat + W * J 7%nat) * NR + (WZ * J 2%nat + W * J 8%nat) * NZ) in
  [NR; NZ; KR; KZ; J 1%nat * (KR * NZ - KZ * NR)].

Section Values.

Variables (Pn : nat) (s0 sJ : Z) (Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 : nat).
Variables (rowsR rowsZ rowsG rowsB rowsU : list (list Z)) (rowsJ : list (list (list Z))) (om : R).

Let fR := tfR Pn s0 Km Kn rowsR.
Let fZ := tfZ Pn s0 Km Kn rowsZ.
Let fG := tfG Pn s0 Kmg Kng rowsG.
Let fB := tfB Pn s0 Kmb Knb rowsB.
Let fU := tfU Pn s0 Kmu Knu rowsU.
Let Jf := tJf Pn sJ Kj1 Kj2 rowsJ.
Let Nf := tNf Pn s0 Km Kn Kmg Kng Kmb Knb rowsR rowsZ rowsG rowsB.
Let DVf := tDVf Pn s0 sJ Km Kn Kmu Knu Kj1 Kj2 rowsR rowsZ rowsU rowsJ.
Let kmf := tkmf Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om.
Let Tf := tTf Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om.

Lemma AJ (i : nat) : afin (Jf i). Proof. apply afin_cden. Qed.

Lemma AN : afin (vR Nf) /\ afin (vZ Nf).
Proof.
  unfold Nf, tNf, knrm, ktng, tK0, tgs, tb. cbn [vadd vsmul vJ vdt vR vZ].
  split; afin_tac.
Qed.

Lemma ADV : afin (mRR DVf) /\ afin (mRZ DVf) /\ afin (mZR DVf) /\ afin (mZZ DVf).
Proof.
  pose proof AJ as HJ. unfold DVf, tDVf, fDV, fWR, fWZ, fW, fUP, tK0, tUb. cbn [mRR mRZ mZR mZZ vR].
  fold Jf. refine (conj _ (conj _ (conj _ _))); afin_tac.
Qed.

Lemma Akm : afin (vR kmf) /\ afin (vZ kmf).
Proof.
  destruct AN as [N1 N2]. destruct ADV as [D1 [D2 [D3 D4]]].
  unfold kmf, tkmf, kmlnx. fold Nf DVf. cbn [vsub vlc mapp vR vZ].
  split; afin_tac.
Qed.

(** Unfolding the finite twist into its factors. *)
Lemma Tf_eq : Tf = fmul (Jf 1) (fsub (fmul (vR kmf) (vZ Nf)) (fmul (vZ kmf) (vR Nf))).
Proof. reflexivity. Qed.

Section Point.

Variables (t p : R).

Lemma v_NR : feval (vR Nf) t p
  = feval (cden fG) t p * (-1 * feval (cden (fam_dt fZ)) t p) + feval (cden fB) t p * feval (cden (fam_dt fR)) t p.
Proof.
  unfold Nf, tNf, knrm, ktng, tK0, tgs, tb. cbn [vadd vsmul vJ vdt vR vZ]. fold fR fZ fG fB.
  rewrite ev_add by afin_tac. rewrite !ev_mul by afin_tac. rewrite ev_scal by afin_tac.
  rewrite !ev_dcden. ring.
Qed.

Lemma v_NZ : feval (vZ Nf) t p
  = feval (cden fG) t p * feval (cden (fam_dt fR)) t p + feval (cden fB) t p * feval (cden (fam_dt fZ)) t p.
Proof.
  unfold Nf, tNf, knrm, ktng, tK0, tgs, tb. cbn [vadd vsmul vJ vdt vR vZ]. fold fR fZ fG fB.
  rewrite ev_add by afin_tac. rewrite !ev_mul by afin_tac.
  rewrite !ev_dcden. ring.
Qed.

Lemma v_lNR : feval (lc om (vR Nf)) t p
  = ((om * feval (cden (fam_dt fG)) t p + feval (cden (fam_dp fG)) t p) * (-1 * feval (cden (fam_dt fZ)) t p)
     + feval (cden fG) t p * (-1 * (om * feval (cden (fam_dt (fam_dt fZ))) t p + feval (cden (fam_dp (fam_dt fZ))) t p)))
    + ((om * feval (cden (fam_dt fB)) t p + feval (cden (fam_dp fB)) t p) * feval (cden (fam_dt fR)) t p
       + feval (cden fB) t p * (om * feval (cden (fam_dt (fam_dt fR))) t p + feval (cden (fam_dp (fam_dt fR))) t p)).
Proof.
  unfold Nf, tNf, knrm, ktng, tK0, tgs, tb. cbn [vadd vsmul vJ vdt vR vZ]. fold fR fZ fG fB.
  rewrite ev_lc_add by afin_tac. rewrite !ev_lc_mul by afin_tac. rewrite ev_lc_scal by afin_tac.
  rewrite ev_scal by afin_tac. rewrite !ev_lcden, !ev_lc_dcden, !ev_dcden. ring.
Qed.

Lemma v_lNZ : feval (lc om (vZ Nf)) t p
  = ((om * feval (cden (fam_dt fG)) t p + feval (cden (fam_dp fG)) t p) * feval (cden (fam_dt fR)) t p
     + feval (cden fG) t p * (om * feval (cden (fam_dt (fam_dt fR))) t p + feval (cden (fam_dp (fam_dt fR))) t p))
    + ((om * feval (cden (fam_dt fB)) t p + feval (cden (fam_dp fB)) t p) * feval (cden (fam_dt fZ)) t p
       + feval (cden fB) t p * (om * feval (cden (fam_dt (fam_dt fZ))) t p + feval (cden (fam_dp (fam_dt fZ))) t p)).
Proof.
  unfold Nf, tNf, knrm, ktng, tK0, tgs, tb. cbn [vadd vsmul vJ vdt vR vZ]. fold fR fZ fG fB.
  rewrite ev_lc_add by afin_tac. rewrite !ev_lc_mul by afin_tac.
  rewrite !ev_lcden, !ev_lc_dcden, !ev_dcden. ring.
Qed.

Let W := feval (cden fR) t p * feval (cden fU) t p.
Let WR := feval (cden fU) t p - W * (feval (cden fU) t p * feval (Jf 5) t p).
Let WZ := -1 * (W * (feval (cden fU) t p * feval (Jf 6) t p)).

Lemma v_DV :
  feval (mRR DVf) t p = WR * feval (Jf 0) t p + W * feval (Jf 3) t p /\
  feval (mRZ DVf) t p = WZ * feval (Jf 0) t p + W * feval (Jf 4) t p /\
  feval (mZR DVf) t p = WR * feval (Jf 2) t p + W * feval (Jf 7) t p /\
  feval (mZZ DVf) t p = WZ * feval (Jf 2) t p + W * feval (Jf 8) t p.
Proof.
  pose proof AJ as HJ. unfold DVf, tDVf, fDV, fWR, fWZ, fW, fUP, tK0, tUb. cbn [mRR mRZ mZR mZZ vR]. fold fR fU Jf.
  unfold WR, WZ, W.
  refine (conj _ (conj _ (conj _ _)));
    (rewrite ev_add by afin_tac; rewrite !ev_mul by afin_tac;
     try (rewrite ev_sub by afin_tac); try (rewrite ev_scal by afin_tac); rewrite !ev_mul by afin_tac; ring).
Qed.

Lemma v_km :
  feval (vR kmf) t p = feval (lc om (vR Nf)) t p - (feval (mRR DVf) t p * feval (vR Nf) t p
                                                   + feval (mRZ DVf) t p * feval (vZ Nf) t p) /\
  feval (vZ kmf) t p = feval (lc om (vZ Nf)) t p - (feval (mZR DVf) t p * feval (vR Nf) t p
                                                   + feval (mZZ DVf) t p * feval (vZ Nf) t p).
Proof.
  destruct AN as [N1 N2]. destruct ADV as [D1 [D2 [D3 D4]]].
  unfold kmf, tkmf, kmlnx. fold Nf DVf. cbn [vsub vlc mapp vR vZ].
  split; (rewrite ev_sub by afin_tac; rewrite ev_add by afin_tac; rewrite !ev_mul by afin_tac; ring).
Qed.

Lemma v_T : feval Tf t p
  = feval (Jf 1) t p * (feval (vR kmf) t p * feval (vZ Nf) t p - feval (vZ kmf) t p * feval (vR Nf) t p).
Proof.
  destruct AN as [N1 N2]. destruct Akm as [M1 M2]. pose proof (AJ 1) as J1.
  rewrite Tf_eq. rewrite ev_mul by afin_tac. rewrite ev_sub by afin_tac. rewrite !ev_mul by afin_tac.
  reflexivity.
Qed.

End Point.

Theorem tpt_ok (t p : R) :
  tvals Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om t p
  = tpt om (bvals Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ t p).
Proof.
  unfold tvals, bvals, tbasics, tpt, tgs, tb, tUb. fold fR fZ fG fB fU Jf Nf kmf Tf.
  cbn [map app seq nth Nat.add].
  destruct (v_km t p) as [K1 K2]. destruct (v_DV t p) as [D1 [D2 [D3 D4]]].
  rewrite (v_T t p), K1, K2, D1, D2, D3, D4, (v_lNR t p), (v_lNZ t p), (v_NR t p), (v_NZ t p).
  assert (E5 : forall a b c d e a' b' c' d' e' : R, a = a' -> b = b' -> c = c' -> d = d' -> e = e' ->
                 [a; b; c; d; e] = [a'; b'; c'; d'; e']) by (intros; subst; reflexivity).
  apply E5; ring.
Qed.

(** * Canonical form and period *)

Lemma tf_canon : is_canon (vR Nf) /\ is_canon (vZ Nf) /\ is_canon (vR kmf) /\ is_canon (vZ kmf) /\ is_canon Tf.
Proof.
  assert (CJ : forall i, is_canon (Jf i)) by (intros i; apply cden_canon).
  assert (CN : is_canon (vR Nf) /\ is_canon (vZ Nf)).
  { unfold Nf, tNf, knrm, ktng, tK0, tgs, tb. cbn [vadd vsmul vJ vdt vR vZ].
    split; repeat (first [apply fadd_canon | apply fmul_canon | apply fscal_canon | apply dt_canon | apply cden_canon]). }
  assert (CD : is_canon (mRR DVf) /\ is_canon (mRZ DVf) /\ is_canon (mZR DVf) /\ is_canon (mZZ DVf)).
  { unfold DVf, tDVf, fDV, fWR, fWZ, fW, fUP, tK0, tUb. cbn [mRR mRZ mZR mZZ vR]. fold Jf.
    refine (conj _ (conj _ (conj _ _)));
      repeat (first [apply CJ | apply fadd_canon | apply fsub_canon | apply fmul_canon | apply fscal_canon
                    | apply cden_canon]). }
  destruct CN as [C1 C2]. destruct CD as [D1 [D2 [D3 D4]]].
  assert (CK : is_canon (vR kmf) /\ is_canon (vZ kmf)).
  { unfold kmf, tkmf, kmlnx. fold Nf DVf. cbn [vsub vlc mapp vR vZ].
    split; repeat (first [assumption | apply fsub_canon | apply fadd_canon | apply fmul_canon | apply lc_canon]). }
  destruct CK as [K1 K2].
  refine (conj C1 (conj C2 (conj K1 (conj K2 _)))).
  rewrite Tf_eq. apply fmul_canon; [apply CJ |]. apply fsub_canon; apply fmul_canon; assumption.
Qed.

Hypothesis HPn : (0 < Pn)%nat.

Lemma tf_HPz : (0 < Z.of_nat Pn)%Z. Proof. lia. Qed.

Lemma tfJ_per (i : nat) : is_per (Z.of_nat Pn) (Jf i).
Proof.
  unfold Jf, tJf, tfJ. destruct (Nat.lt_ge_cases i (length (tfJs Pn sJ Kj1 Kj2 rowsJ))) as [Hi | Hi].
  - pose proof (nth_In (tfJs Pn sJ Kj1 Kj2 rowsJ) [] Hi) as Hin. unfold tfJs in Hin |- *. apply in_map_iff in Hin.
    destruct Hin as [[b rows] [E _]]. rewrite <- E. apply cden_per, tf_HPz.
  - rewrite nth_overflow by exact Hi. intros m n _. unfold cden, canon, ccan, scan. simpl. split; ring.
Qed.

Lemma tf_per :
  is_per (Z.of_nat Pn) (vR Nf) /\ is_per (Z.of_nat Pn) (vZ Nf) /\ is_per (Z.of_nat Pn) (vR kmf) /\
  is_per (Z.of_nat Pn) (vZ kmf) /\ is_per (Z.of_nat Pn) Tf.
Proof.
  pose proof tf_HPz as HP. pose proof tfJ_per as QJ.
  assert (Qc : forall (s : Z) (Kx Ky : nat) (rows : list (list (Z * Z))),
             is_per (Z.of_nat Pn) (cden (dfam s (zrange Kx) (pns (Z.of_nat Pn) Ky) rows)))
    by (intros; apply cden_per, HP).
  assert (QN : is_per (Z.of_nat Pn) (vR Nf) /\ is_per (Z.of_nat Pn) (vZ Nf)).
  { unfold Nf, tNf, knrm, ktng, tK0, tgs, tb, tfR, tfZ, tfG, tfB. cbn [vadd vsmul vJ vdt vR vZ].
    split; repeat (first [apply Qc | apply (fadd_per _) | apply (fmul_per _ HP) | apply (fscal_per _)
                         | apply (dt_per _)]). }
  assert (QD : is_per (Z.of_nat Pn) (mRR DVf) /\ is_per (Z.of_nat Pn) (mRZ DVf) /\ is_per (Z.of_nat Pn) (mZR DVf) /\
               is_per (Z.of_nat Pn) (mZZ DVf)).
  { unfold DVf, tDVf, fDV, fWR, fWZ, fW, fUP, tK0, tUb, tfR, tfU. cbn [mRR mRZ mZR mZZ vR]. fold Jf.
    refine (conj _ (conj _ (conj _ _)));
      repeat (first [apply Qc | apply QJ | apply (fadd_per _) | apply (fsub_per _) | apply (fmul_per _ HP)
                    | apply (fscal_per _)]). }
  destruct QN as [Q1 Q2]. destruct QD as [D1 [D2 [D3 D4]]].
  assert (QK : is_per (Z.of_nat Pn) (vR kmf) /\ is_per (Z.of_nat Pn) (vZ kmf)).
  { unfold kmf, tkmf, kmlnx. fold Nf DVf. cbn [vsub vlc mapp vR vZ].
    split; repeat (first [assumption | apply (fsub_per _) | apply (fadd_per _) | apply (fmul_per _ HP)
                         | apply (lc_per _)]). }
  destruct QK as [K1 K2].
  refine (conj Q1 (conj Q2 (conj K1 (conj K2 _)))).
  rewrite Tf_eq. apply (fmul_per _ HP); [apply QJ |]. apply (fsub_per _); apply (fmul_per _ HP); assumption.
Qed.

(** * Boxes *)

Lemma dfam_supp (s : Z) (Kx Ky : nat) (rows : list (list (Z * Z))) :
  supp Kx (Pn * Ky) (cden (dfam s (zrange Kx) (pns (Z.of_nat Pn) Ky) rows)).
Proof.
  unfold cden. apply supp_canon, flist_supp. apply dfam_forall. intros k n c sn Hk Hn _.
  cbn [fe_m fe_n]. split; [apply in_zrange, Hk |].
  unfold pns in Hn. apply in_map_iff in Hn. destruct Hn as [l [El Hl]]. subst n.
  pose proof (in_zrange Ky l Hl) as H. rewrite Nat2Z.inj_mul, Z.abs_mul, (Z.abs_eq (Z.of_nat Pn)) by lia. nia.
Qed.

Lemma sR : supp Km (Pn * Kn) (cden fR). Proof. apply dfam_supp. Qed.
Lemma sG : supp Kmg (Pn * Kng) (cden fG). Proof. apply dfam_supp. Qed.
Lemma sB : supp Kmb (Pn * Knb) (cden fB). Proof. apply dfam_supp. Qed.
Lemma sU : supp Kmu (Pn * Knu) (cden fU). Proof. apply dfam_supp. Qed.
Lemma saR : supp Km (Pn * Kn) (dt (cden fR)). Proof. apply dt_supp, dfam_supp. Qed.
Lemma saZ : supp Km (Pn * Kn) (dt (cden fZ)). Proof. apply dt_supp, dfam_supp. Qed.

Definition bN1 : nat := Kmg + Km.
Definition bN2 : nat := Kng + Kn.
Definition bD1 : nat := Km + Kmu + (Kmu + Kj1) + Kj1.
Definition bD2 : nat := Kn + Knu + (Knu + Kj2) + Kj2.
Definition bK1 : nat := bD1 + bN1.
Definition bK2 : nat := bD2 + bN2.
Definition bT1 : nat := Kj1 + (bK1 + bN1).
Definition bT2 : nat := Kj2 + (bK2 + bN2).

Lemma tf_mul_split (a b : nat) : (Pn * a + Pn * b = Pn * (a + b))%nat. Proof. ring. Qed.

Lemma supp_mul (K1 K2 L1 L2 : nat) (u v : fser) :
  supp K1 (Pn * K2) u -> supp L1 (Pn * L2) v -> supp (K1 + L1) (Pn * (K2 + L2)) (fmul u v).
Proof. intros Hu Hv. rewrite <- tf_mul_split. apply fmul_supp; assumption. Qed.

Lemma supp_up (K1 K2 L1 L2 : nat) (u : fser) :
  (K1 <= L1)%nat -> (K2 <= L2)%nat -> supp K1 (Pn * K2) u -> supp L1 (Pn * L2) u.
Proof. intros H1 H2 H. apply (supp_mono K1 (Pn * K2)); [exact H1 | apply Nat.mul_le_mono_l, H2 | exact H]. Qed.

Lemma SJ (i : nat) : supp Kj1 (Pn * Kj2) (Jf i).
Proof.
  unfold Jf, tJf, tfJ. destruct (Nat.lt_ge_cases i (length (tfJs Pn sJ Kj1 Kj2 rowsJ))) as [Hi | Hi].
  - pose proof (nth_In (tfJs Pn sJ Kj1 Kj2 rowsJ) [] Hi) as Hin. unfold tfJs in Hin |- *. apply in_map_iff in Hin.
    destruct Hin as [[b rows] [E _]]. rewrite <- E. apply dfam_supp.
  - rewrite nth_overflow by exact Hi. intros m n _. unfold cden, canon, ccan, scan. simpl. split; ring.
Qed.

Hypothesis HBm : (Kmb <= Kmg)%nat.
Hypothesis HBn : (Knb <= Kng)%nat.

Lemma SN : supp bN1 (Pn * bN2) (vR Nf) /\ supp bN1 (Pn * bN2) (vZ Nf).
Proof.
  pose proof sG as G. pose proof saR as AR. pose proof saZ as AZ.
  assert (B : supp Kmg (Pn * Kng) (cden fB)) by (apply (supp_up Kmb Knb); [exact HBm | exact HBn | exact sB]).
  unfold Nf, tNf, knrm, ktng, tK0, tgs, tb, bN1, bN2. cbn [vadd vsmul vJ vdt vR vZ]. fold fR fZ fG fB.
  split; apply fadd_supp; apply supp_mul; try assumption; apply fscal_supp; assumption.
Qed.

Lemma SDV : supp bD1 (Pn * bD2) (mRR DVf) /\ supp bD1 (Pn * bD2) (mRZ DVf) /\ supp bD1 (Pn * bD2) (mZR DVf) /\
            supp bD1 (Pn * bD2) (mZZ DVf).
Proof.
  pose proof SJ as HJ. pose proof sR as HR. pose proof sU as HU.
  unfold DVf, tDVf, fDV, fWR, fWZ, fW, fUP, tK0, tUb, bD1, bD2. cbn [mRR mRZ mZR mZZ vR]. fold fR fU Jf.
  assert (HW : forall i, supp (Km + Kmu + (Kmu + Kj1)) (Pn * (Kn + Knu + (Knu + Kj2)))
                  (fmul (fmul (cden fR) (cden fU)) (fmul (cden fU) (Jf i))))
    by (intros i; apply supp_mul; apply supp_mul; auto).
  assert (HUw : supp (Km + Kmu + (Kmu + Kj1)) (Pn * (Kn + Knu + (Knu + Kj2))) (cden fU))
    by (apply (supp_up Kmu Knu); [lia | lia | exact HU]).
  assert (HWR : supp (Km + Kmu + (Kmu + Kj1)) (Pn * (Kn + Knu + (Knu + Kj2)))
                  (fsub (cden fU) (fmul (fmul (cden fR) (cden fU)) (fmul (cden fU) (Jf 5)))))
    by (apply fsub_supp; [exact HUw | apply HW]).
  assert (HWZ : supp (Km + Kmu + (Kmu + Kj1)) (Pn * (Kn + Knu + (Knu + Kj2)))
                  (fscal (-1) (fmul (fmul (cden fR) (cden fU)) (fmul (cden fU) (Jf 6)))))
    by (apply fscal_supp, HW).
  assert (HW2 : forall i, supp (Km + Kmu + (Kmu + Kj1) + Kj1) (Pn * (Kn + Knu + (Knu + Kj2) + Kj2))
                   (fmul (fmul (cden fR) (cden fU)) (Jf i))).
  { intros i. apply (supp_up (Km + Kmu + Kj1) (Kn + Knu + Kj2)); [lia | lia |]. apply supp_mul; [| apply HJ].
    apply supp_mul; assumption. }
  refine (conj _ (conj _ (conj _ _))); apply fadd_supp; try apply HW2; apply supp_mul; auto.
Qed.

Lemma SK : supp bK1 (Pn * bK2) (vR kmf) /\ supp bK1 (Pn * bK2) (vZ kmf).
Proof.
  destruct SN as [N1 N2]. destruct SDV as [D1 [D2 [D3 D4]]].
  assert (L1 : supp (bD1 + bN1) (Pn * (bD2 + bN2)) (lc om (vR Nf)))
    by (apply lc_supp, (supp_up bN1 bN2); [lia | lia | exact N1]).
  assert (L2 : supp (bD1 + bN1) (Pn * (bD2 + bN2)) (lc om (vZ Nf)))
    by (apply lc_supp, (supp_up bN1 bN2); [lia | lia | exact N2]).
  unfold kmf, tkmf, kmlnx, bK1, bK2. fold Nf DVf. cbn [vsub vlc mapp vR vZ].
  split; apply fsub_supp; try assumption; apply fadd_supp; apply supp_mul; assumption.
Qed.

Lemma ST : supp bT1 (Pn * bT2) Tf.
Proof.
  destruct SN as [N1 N2]. destruct SK as [K1 K2].
  rewrite Tf_eq. unfold bT1, bT2.
  apply supp_mul; [apply SJ |]. apply fsub_supp; apply supp_mul; assumption.
Qed.

End Values.
