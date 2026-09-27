(** The Newton step of the a posteriori KAM iteration.

    A field model carries, for every torus K given as a pair of families, the
    families of the field along it ([Vf]), of its derivative ([DVf]), of the
    invariant density sigma of the flow ([Sf]) and of its gradient ([GSf]).
    From an approximate inverse g of sigma |d_t K|^2 and a family b, fixed
    along the iteration, the step builds the frame a = d_t K and
    N = J a g + b a, the coordinates eta of the error E = L K - V(K) in
    it, the torsion T, and the correction xi solving L xi_2 = -eta_2 and
    L xi_1 + T xi_2 = -eta_1, with the constant part of xi_2 chosen so that
    the second has zero average; the next torus is K + xi_1 a + xi_2 N
    ([knext]). Its error is, at every point,

      (alpha xi_1) a + (beta xi_1 + c xi_2) N - Q

    with Q the second-order remainder of the field along the correction
    ([step_identity]), and each term is a product of the error, or its
    derivative, with the correction, or is Q. The hypotheses at the point are
    the frame identity sigma |a|^2 g = 1, the chain rule of the field along the
    torus, the Liouville identity L sigma = grad sigma . E - sigma tr DV, a
    zero average of eta_2, which stellarator symmetry gives, and a nonzero
    average of T, the twist. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon KAMFrame KAMVec KAMFin.
Local Open Scope R_scope.

Record fmodel := { Vf : vf -> vf ; DVf : vf -> mf ; Sf : vf -> fser ; GSf : vf -> vf }.

Section Construction.

Variables (F : fmodel) (om : R) (K : vf) (g b : fser).

Definition kerr (X : vf) : vf := vsub (vlc om X) (Vf F X).
Definition ktng : vf := vdt K.
Definition knrm : vf := vadd (vsmul g (vJ ktng)) (vsmul b ktng).
Definition keta1 : fser := fmul (Sf F K) (wedge (kerr K) knrm).
Definition keta2 : fser := fmul (Sf F K) (wedge ktng (kerr K)).
Definition kmln : vf := vsub (vlc om knrm) (mapp (DVf F K) knrm).
Definition ktwist : fser := fmul (Sf F K) (wedge kmln knrm).
Definition kw2 : fser := fscal (-1) (linv om keta2).
Definition kxi20 : R := - (fc keta1 0 0 + fc (fmul ktwist kw2) 0 0) / fc ktwist 0 0.
Definition kxi2 : fser := fadd kw2 (fconst kxi20).
Definition krhs1 : fser := fadd keta1 (fadd (fmul ktwist kw2) (fscal kxi20 ktwist)).
Definition kxi1 : fser := fscal (-1) (linv om krhs1).
Definition kcorr : vf := vadd (vsmul kxi1 ktng) (vsmul kxi2 knrm).
Definition knext : vf := vadd K kcorr.
Definition kalpha : fser := fmul (Sf F K) (wedge (vdt (kerr K)) knrm).
Definition kbeta : fser := fmul (Sf F K) (wedge ktng (vdt (kerr K))).
Definition kc : fser :=
  fsub (fscal (-1) (fmul (fmul (vdot (GSf F K) (kerr K)) (vdot ktng ktng)) g)) kalpha.
Definition kremq : vf := vsub (vsub (Vf F knext) (Vf F K)) (mapp (DVf F K) kcorr).
Definition kerrx : vf :=
  vsub (vadd (vsmul (fmul kalpha kxi1) ktng) (vsmul (fadd (fmul kbeta kxi1) (fmul kc kxi2)) knrm))
       kremq.

End Construction.

(** The average of the right side of the first cohomological equation is zero. *)
Lemma krhs1_mean (F : fmodel) (om : R) (K : vf) (g b : fser) :
  fc (ktwist F om K g b) 0 0 <> 0 -> fc (krhs1 F om K g b) 0 0 = 0.
Proof.
  intros H. unfold krhs1. cbn [fc fadd fscal]. unfold kxi20. field. exact H.
Qed.

Section Identity.

Variables (F : fmodel) (om gamma w d : R) (K : vf) (g b : fser).
Hypothesis Hdio : diophantine1 om gamma.
Hypothesis Hgam : 0 < gamma <= 1.
Hypothesis Hd : 0 < d.
Hypothesis Hw : 3 * d < w.

Hypothesis FK : vfin w K.
Hypothesis Fa : vfin w (ktng K).
Hypothesis FlK : vfin w (vlc om K).
Hypothesis Fg : fin w g.
Hypothesis Fb : fin w b.
Hypothesis FS : fin w (Sf F K).
Hypothesis FG : vfin w (GSf F K).
Hypothesis FD : mfin w (DVf F K).
Hypothesis FV : vfin w (Vf F K).
Hypothesis FV' : vfin (w - 2 * d) (Vf F (knext F om K g b)).

Hypothesis Hframe : forall t p,
  feval (Sf F K) t p * feval (vdot (ktng K) (ktng K)) t p * feval g t p = 1.
Hypothesis Hchain_R : forall t p,
  feval (dt (vR (Vf F K))) t p
  = feval (mRR (DVf F K)) t p * feval (vR (ktng K)) t p
    + feval (mRZ (DVf F K)) t p * feval (vZ (ktng K)) t p.
Hypothesis Hchain_Z : forall t p,
  feval (dt (vZ (Vf F K))) t p
  = feval (mZR (DVf F K)) t p * feval (vR (ktng K)) t p
    + feval (mZZ (DVf F K)) t p * feval (vZ (ktng K)) t p.
Hypothesis Hliou : forall t p,
  feval (lc om (Sf F K)) t p
  = feval (vdot (GSf F K) (kerr F om K)) t p - feval (Sf F K) t p * feval (mtr (DVf F K)) t p.
Hypothesis Hmean2 : fc (keta2 F om K) 0 0 = 0.
Hypothesis Htw : fc (ktwist F om K g b) 0 0 <> 0.

(** * Finite norms of the parts of the step *)

Let w1 := w - d.
Let w2 := w - 2 * d.
Let w3 := w - 3 * d.

Lemma Hw0 : 0 <= w. Proof. lra. Qed.
Lemma Hw1 : 0 < w1. Proof. unfold w1. lra. Qed.
Lemma Hw2 : 0 < w2. Proof. unfold w2. lra. Qed.
Lemma Hw3 : 0 < w3. Proof. unfold w3. lra. Qed.
Lemma Hw10 : w1 <= w. Proof. unfold w1. lra. Qed.
Lemma Hw20 : w2 <= w. Proof. unfold w2. lra. Qed.
Lemma Hw21 : w2 <= w1. Proof. unfold w1, w2. lra. Qed.

Lemma FN : vfin w (knrm K g b).
Proof.
  apply vfin_vadd; [apply vfin_vsmul; [exact Hw0 | exact Fg | apply vfin_vJ, Fa] |].
  apply vfin_vsmul; [exact Hw0 | exact Fb | exact Fa].
Qed.

Lemma FE : vfin w (kerr F om K).
Proof. apply vfin_vsub; assumption. Qed.

Lemma Feta1 : fin w (keta1 F om K g b).
Proof. apply fin_fmul; [exact Hw0 | exact FS | apply fin_wedge; [exact Hw0 | apply FE | apply FN]]. Qed.

Lemma Feta2 : fin w (keta2 F om K).
Proof. apply fin_fmul; [exact Hw0 | exact FS | apply fin_wedge; [exact Hw0 | exact Fa | apply FE]]. Qed.

Lemma FLN : vfin w1 (vlc om (knrm K g b)).
Proof. apply vfin_vlc; [exact Hd | apply FN]. Qed.

Lemma Fmln : vfin w1 (kmln F om K g b).
Proof.
  apply vfin_vsub; [apply FLN |].
  apply vfin_mapp; [left; apply Hw1 | apply (mfin_mono w); [apply Hw10 | exact FD] |
                    apply (vfin_mono w); [apply Hw10 | apply FN]].
Qed.

Lemma FT : fin w1 (ktwist F om K g b).
Proof.
  apply fin_fmul; [left; apply Hw1 | apply (fin_mono w); [apply Hw10 | exact FS] |].
  apply fin_wedge; [left; apply Hw1 | apply Fmln | apply (vfin_mono w); [apply Hw10 | apply FN]].
Qed.

Lemma Fw2 : fin w1 (kw2 F om K).
Proof. apply fin_fscal. apply (fin_linv om gamma); [exact Hdio | exact Hgam | exact Hd | apply Feta2]. Qed.

Lemma Fxi2 : fin w1 (kxi2 F om K g b).
Proof. apply fin_fadd; [apply Fw2 | apply fin_fconst]. Qed.

Lemma Frhs1 : fin w1 (krhs1 F om K g b).
Proof.
  apply fin_fadd; [apply (fin_mono w); [apply Hw10 | apply Feta1] |].
  apply fin_fadd; [apply fin_fmul; [left; apply Hw1 | apply FT | apply Fw2] | apply fin_fscal, FT].
Qed.

Lemma Flinv1 : fin w2 (linv om (krhs1 F om K g b)).
Proof.
  replace w2 with (w1 - d) by (unfold w1, w2; ring).
  apply (fin_linv om gamma); [exact Hdio | exact Hgam | exact Hd | apply Frhs1].
Qed.

Lemma Fxi1 : fin w2 (kxi1 F om K g b).
Proof. apply fin_fscal, Flinv1. Qed.

Lemma Fcorr : vfin w2 (kcorr F om K g b).
Proof.
  apply vfin_vadd.
  - apply vfin_vsmul; [left; apply Hw2 | apply Fxi1 | apply (vfin_mono w); [apply Hw20 | exact Fa]].
  - apply vfin_vsmul; [left; apply Hw2 | apply (fin_mono w1); [apply Hw21 | apply Fxi2] |
                       apply (vfin_mono w); [apply Hw20 | apply FN]].
Qed.

Lemma Fnext : vfin w2 (knext F om K g b).
Proof. apply vfin_vadd; [apply (vfin_mono w); [apply Hw20 | exact FK] | apply Fcorr]. Qed.

Lemma FdE : vfin w1 (vdt (kerr F om K)).
Proof. apply vfin_vdt; [exact Hd | apply FE]. Qed.

Lemma Falpha : fin w1 (kalpha F om K g b).
Proof.
  apply fin_fmul; [left; apply Hw1 | apply (fin_mono w); [apply Hw10 | exact FS] |].
  apply fin_wedge; [left; apply Hw1 | apply FdE | apply (vfin_mono w); [apply Hw10 | apply FN]].
Qed.

Lemma Fbeta : fin w1 (kbeta F om K).
Proof.
  apply fin_fmul; [left; apply Hw1 | apply (fin_mono w); [apply Hw10 | exact FS] |].
  apply fin_wedge; [left; apply Hw1 | apply (vfin_mono w); [apply Hw10 | exact Fa] | apply FdE].
Qed.

Lemma Fc : fin w1 (kc F om K g b).
Proof.
  apply fin_fsub; [| apply Falpha]. apply fin_fscal.
  apply fin_fmul; [left; apply Hw1 | | apply (fin_mono w); [apply Hw10 | exact Fg]].
  apply fin_fmul; [left; apply Hw1 | |].
  - apply fin_vdot; [left; apply Hw1 | apply (vfin_mono w); [apply Hw10 | exact FG] |
                     apply (vfin_mono w); [apply Hw10 | apply FE]].
  - apply fin_vdot; [left; apply Hw1 | |]; apply (vfin_mono w); [apply Hw10 | exact Fa | apply Hw10 | exact Fa].
Qed.

Lemma Fremq : vfin w2 (kremq F om K g b).
Proof.
  apply vfin_vsub; [apply vfin_vsub; [exact FV' | apply (vfin_mono w); [apply Hw20 | exact FV]] |].
  apply vfin_mapp; [left; apply Hw2 | apply (mfin_mono w); [apply Hw20 | exact FD] | apply Fcorr].
Qed.

Lemma Ferrx : vfin w2 (kerrx F om K g b).
Proof.
  apply vfin_vsub; [| apply Fremq]. apply vfin_vadd.
  - apply vfin_vsmul; [left; apply Hw2 | |].
    + apply fin_fmul; [left; apply Hw2 | apply (fin_mono w1); [apply Hw21 | apply Falpha] | apply Fxi1].
    + apply (vfin_mono w); [apply Hw20 | exact Fa].
  - apply vfin_vsmul; [left; apply Hw2 | |].
    + apply fin_fadd.
      * apply fin_fmul; [left; apply Hw2 | apply (fin_mono w1); [apply Hw21 | apply Fbeta] | apply Fxi1].
      * apply fin_fmul; [left; apply Hw2 | apply (fin_mono w1); [apply Hw21 | apply Fc] |
                         apply (fin_mono w1); [apply Hw21 | apply Fxi2]].
    + apply (vfin_mono w); [apply Hw20 | apply FN].
Qed.

Lemma Ferr' : vfin w3 (kerr F om (knext F om K g b)).
Proof.
  apply vfin_vsub.
  - replace w3 with (w2 - d) by (unfold w2, w3; ring). apply vfin_vlc; [exact Hd | apply Fnext].
  - apply (vfin_mono w2); [unfold w2, w3; lra | exact FV'].
Qed.

(** Finite norms on the strip of width zero, where the functions are read. *)
Lemma z1 (u : fser) : fin w1 u -> fin 0 u.
Proof. apply fin_mono. left. apply Hw1. Qed.
Lemma z2 (u : fser) : fin w2 u -> fin 0 u.
Proof. apply fin_mono. left. apply Hw2. Qed.
Lemma z0 (u : fser) : fin w u -> fin 0 u.
Proof. apply fin_mono. apply Hw0. Qed.
Lemma vz0 (u : vf) : vfin w u -> vfin 0 u.
Proof. apply vfin_mono. apply Hw0. Qed.
Lemma vz1 (u : vf) : vfin w1 u -> vfin 0 u.
Proof. apply vfin_mono. left. apply Hw1. Qed.
Lemma vz2 (u : vf) : vfin w2 u -> vfin 0 u.
Proof. apply vfin_mono. left. apply Hw2. Qed.
Lemma mz0 (A : mf) : mfin w A -> mfin 0 A.
Proof. apply mfin_mono. apply Hw0. Qed.

Lemma dt_feq (u v : fser) : feq u v -> feq (dt u) (dt v).
Proof. intros H m n. destruct (H m n) as [H1 H2]. simpl. rewrite H1, H2. split; reflexivity. Qed.

(** The components, in the forms the rewriting below meets. *)
Lemma FaR : fin w (vR (ktng K)). Proof. exact (proj1 Fa). Qed.
Lemma FaZ : fin w (vZ (ktng K)). Proof. exact (proj2 Fa). Qed.
Lemma FNR : fin w (vR (knrm K g b)). Proof. exact (proj1 FN). Qed.
Lemma FNZ : fin w (vZ (knrm K g b)). Proof. exact (proj2 FN). Qed.
Lemma FER : fin w (vR (kerr F om K)). Proof. exact (proj1 FE). Qed.
Lemma FEZ : fin w (vZ (kerr F om K)). Proof. exact (proj2 FE). Qed.
Lemma FVR : fin w (vR (Vf F K)). Proof. exact (proj1 FV). Qed.
Lemma FVZ : fin w (vZ (Vf F K)). Proof. exact (proj2 FV). Qed.
Lemma FV'R : fin w2 (vR (Vf F (knext F om K g b))). Proof. exact (proj1 FV'). Qed.
Lemma FV'Z : fin w2 (vZ (Vf F (knext F om K g b))). Proof. exact (proj2 FV'). Qed.
Lemma FLNR : fin w1 (lc om (vR (knrm K g b))). Proof. exact (proj1 FLN). Qed.
Lemma FLNZ : fin w1 (lc om (vZ (knrm K g b))). Proof. exact (proj2 FLN). Qed.
Lemma Fxi2' : fin w2 (kxi2 F om K g b). Proof. apply (fin_mono w1); [apply Hw21 | apply Fxi2]. Qed.
Lemma FcR : fin w2 (vR (kcorr F om K g b)). Proof. exact (proj1 Fcorr). Qed.
Lemma FcZ : fin w2 (vZ (kcorr F om K g b)). Proof. exact (proj2 Fcorr). Qed.
Lemma FnR : fin w2 (vR (knext F om K g b)). Proof. exact (proj1 Fnext). Qed.
Lemma FnZ : fin w2 (vZ (knext F om K g b)). Proof. exact (proj2 Fnext). Qed.
Lemma FKR : fin w2 (vR K). Proof. exact (proj1 (vfin_mono w w2 _ Hw20 FK)). Qed.
Lemma FKZ : fin w2 (vZ K). Proof. exact (proj2 (vfin_mono w w2 _ Hw20 FK)). Qed.
Lemma FlKR : fin w (lc om (vR K)). Proof. exact (proj1 FlK). Qed.
Lemma FlKZ : fin w (lc om (vZ K)). Proof. exact (proj2 FlK). Qed.
Lemma Fmp : vfin w2 (mapp (DVf F K) (kcorr F om K g b)).
Proof. apply vfin_mapp; [left; apply Hw2 | apply (mfin_mono w); [apply Hw20 | exact FD] | apply Fcorr]. Qed.
Lemma FqR : fin w2 (vR (kremq F om K g b)). Proof. exact (proj1 Fremq). Qed.
Lemma FqZ : fin w2 (vZ (kremq F om K g b)). Proof. exact (proj2 Fremq). Qed.

Section Point.

Variables t p : R.

Local Notation a1 := (feval (vR (ktng K)) t p).
Local Notation a2 := (feval (vZ (ktng K)) t p).
Local Notation g0 := (feval g t p).
Local Notation b0 := (feval b t p).
Local Notation Lb := (feval (lc om b) t p).
Local Notation s0 := (feval (Sf F K) t p).
Local Notation s1 := (feval (vR (GSf F K)) t p).
Local Notation s2 := (feval (vZ (GSf F K)) t p).
Local Notation E1 := (feval (vR (kerr F om K)) t p).
Local Notation E2 := (feval (vZ (kerr F om K)) t p).
Local Notation dE1 := (feval (dt (vR (kerr F om K))) t p).
Local Notation dE2 := (feval (dt (vZ (kerr F om K))) t p).
Local Notation D11 := (feval (mRR (DVf F K)) t p).
Local Notation D12 := (feval (mRZ (DVf F K)) t p).
Local Notation D21 := (feval (mZR (DVf F K)) t p).
Local Notation D22 := (feval (mZZ (DVf F K)) t p).
Local Notation La1 := (feval (lc om (vR (ktng K))) t p).
Local Notation La2 := (feval (lc om (vZ (ktng K))) t p).
Local Notation Lg := (feval (lc om g) t p).
Local Notation Ls := (feval (lc om (Sf F K)) t p).
Local Notation N1 := (feval (vR (knrm K g b)) t p).
Local Notation N2 := (feval (vZ (knrm K g b)) t p).
Local Notation LN1 := (feval (lc om (vR (knrm K g b))) t p).
Local Notation LN2 := (feval (lc om (vZ (knrm K g b))) t p).
Local Notation x1 := (feval (kxi1 F om K g b) t p).
Local Notation x2 := (feval (kxi2 F om K g b) t p).
Local Notation Lx1 := (feval (lc om (kxi1 F om K g b)) t p).
Local Notation Lx2 := (feval (lc om (kxi2 F om K g b)) t p).
Local Notation e1 := (feval (keta1 F om K g b) t p).
Local Notation e2 := (feval (keta2 F om K) t p).
Local Notation Tv := (feval (ktwist F om K g b) t p).
Local Notation al := (feval (kalpha F om K g b) t p).
Local Notation be := (feval (kbeta F om K) t p).
Local Notation cv := (feval (kc F om K g b) t p).

Lemma R_frame : s0 * (a1 * a1 + a2 * a2) * g0 = 1.
Proof.
  pose proof (Hframe t p) as H. rewrite (feval_vdot' t p _ _ (vz0 _ Fa) (vz0 _ Fa)) in H. exact H.
Qed.

Lemma lc_err_R : feq (lc om (vR K)) (fadd (vR (kerr F om K)) (vR (Vf F K))).
Proof. intros m n. unfold kerr, vsub, fsub, fadd, fscal. simpl. split; ring. Qed.

Lemma lc_err_Z : feq (lc om (vZ K)) (fadd (vZ (kerr F om K)) (vZ (Vf F K))).
Proof. intros m n. unfold kerr, vsub, fsub, fadd, fscal. simpl. split; ring. Qed.

Lemma R_La1 : La1 = dE1 + (D11 * a1 + D12 * a2).
Proof.
  assert (Hw' : 0 < w) by lra.
  transitivity (feval (dt (fadd (vR (kerr F om K)) (vR (Vf F K)))) t p).
  - rewrite <- (feval_feq _ _ t p (dt_feq _ _ lc_err_R)).
    rewrite (feval_feq _ _ t p (dt_lc_feq om (vR K))). reflexivity.
  - rewrite (feval_dt_fadd' t p w _ _ Hw' FER FVR), Hchain_R. reflexivity.
Qed.

Lemma R_La2 : La2 = dE2 + (D21 * a1 + D22 * a2).
Proof.
  assert (Hw' : 0 < w) by lra.
  transitivity (feval (dt (fadd (vZ (kerr F om K)) (vZ (Vf F K)))) t p).
  - rewrite <- (feval_feq _ _ t p (dt_feq _ _ lc_err_Z)).
    rewrite (feval_feq _ _ t p (dt_lc_feq om (vZ K))). reflexivity.
  - rewrite (feval_dt_fadd' t p w _ _ Hw' FEZ FVZ), Hchain_Z. reflexivity.
Qed.

Lemma R_Ls : Ls = s1 * E1 + s2 * E2 - s0 * (D11 + D22).
Proof.
  rewrite Hliou, (feval_vdot' t p _ _ (vz0 _ FG) (vz0 _ FE)), (feval_mtr' t p _ (mz0 _ FD)). reflexivity.
Qed.

Lemma R_Lg : Ls * (a1 * a1 + a2 * a2) * g0 + s0 * (2 * (a1 * La1 + a2 * La2)) * g0
             + s0 * (a1 * a1 + a2 * a2) * Lg = 0.
Proof.
  assert (Hw' : 0 < w) by lra.
  assert (Faa : fin w (vdot (ktng K) (ktng K))) by (apply fin_vdot; [apply Hw0 | exact Fa | exact Fa]).
  assert (Fsa : fin w (fmul (Sf F K) (vdot (ktng K) (ktng K)))) by (apply fin_fmul; [apply Hw0 | exact FS | exact Faa]).
  assert (Fu : fin w (fmul (fmul (Sf F K) (vdot (ktng K) (ktng K))) g)) by (apply fin_fmul; [apply Hw0 | exact Fsa | exact Fg]).
  assert (Hc : forall t' p', feval (fmul (fmul (Sf F K) (vdot (ktng K) (ktng K))) g) t' p' = 1).
  { intros t' p'.
    rewrite (feval_fmul' t' p' _ _ (z0 _ Fsa) (z0 _ Fg)), (feval_fmul' t' p' _ _ (z0 _ FS) (z0 _ Faa)).
    apply Hframe. }
  destruct Fu as [Mu HMu].
  pose proof (feval_lc_const om w Mu 1 _ Hw' HMu Hc t p) as H0.
  rewrite (feval_lc_fmul' t p om w _ _ Hw' Fsa Fg), (feval_lc_fmul' t p om w _ _ Hw' FS Faa) in H0.
  rewrite (feval_fmul' t p _ _ (z0 _ FS) (z0 _ Faa)) in H0.
  assert (FRR : fin w (fmul (vR (ktng K)) (vR (ktng K)))) by (apply fin_fmul; [apply Hw0 | exact FaR | exact FaR]).
  assert (FZZ : fin w (fmul (vZ (ktng K)) (vZ (ktng K)))) by (apply fin_fmul; [apply Hw0 | exact FaZ | exact FaZ]).
  assert (LA : feval (lc om (vdot (ktng K) (ktng K))) t p = La1 * a1 + a1 * La1 + (La2 * a2 + a2 * La2)).
  { unfold vdot.
    rewrite (feval_lc_fadd' t p om w _ _ Hw' FRR FZZ).
    rewrite (feval_lc_fmul' t p om w _ _ Hw' FaR FaR), (feval_lc_fmul' t p om w _ _ Hw' FaZ FaZ).
    reflexivity. }
  rewrite LA, (feval_vdot' t p _ _ (vz0 _ Fa) (vz0 _ Fa)) in H0.
  match type of H0 with ?X = _ => transitivity X; [ring | exact H0] end.
Qed.

Lemma FgJ1 : fin w (fmul g (fscal (-1) (vZ (ktng K)))).
Proof. apply fin_fmul; [apply Hw0 | exact Fg | apply fin_fscal, FaZ]. Qed.
Lemma FgJ2 : fin w (fmul g (vR (ktng K))).
Proof. apply fin_fmul; [apply Hw0 | exact Fg | exact FaR]. Qed.
Lemma Fba1 : fin w (fmul b (vR (ktng K))).
Proof. apply fin_fmul; [apply Hw0 | exact Fb | exact FaR]. Qed.
Lemma Fba2 : fin w (fmul b (vZ (ktng K))).
Proof. apply fin_fmul; [apply Hw0 | exact Fb | exact FaZ]. Qed.

Lemma R_N1 : N1 = - (a2 * g0) + b0 * a1.
Proof.
  transitivity (feval (fadd (fmul g (fscal (-1) (vZ (ktng K)))) (fmul b (vR (ktng K)))) t p);
    [reflexivity |].
  rewrite (feval_fadd' t p _ _ (z0 _ FgJ1) (z0 _ Fba1)).
  rewrite (feval_fmul' t p _ _ (z0 _ Fg) (z0 _ (fin_fscal w (-1) _ FaZ))).
  rewrite (feval_fscal' t p _ _ (z0 _ FaZ)), (feval_fmul' t p _ _ (z0 _ Fb) (z0 _ FaR)). ring.
Qed.

Lemma R_N2 : N2 = a1 * g0 + b0 * a2.
Proof.
  transitivity (feval (fadd (fmul g (vR (ktng K))) (fmul b (vZ (ktng K)))) t p); [reflexivity |].
  rewrite (feval_fadd' t p _ _ (z0 _ FgJ2) (z0 _ Fba2)).
  rewrite (feval_fmul' t p _ _ (z0 _ Fg) (z0 _ FaR)), (feval_fmul' t p _ _ (z0 _ Fb) (z0 _ FaZ)). ring.
Qed.

Lemma R_LN1 : LN1 = - (La2 * g0 + a2 * Lg) + (Lb * a1 + b0 * La1).
Proof.
  assert (Hw' : 0 < w) by lra.
  transitivity (feval (lc om (fadd (fmul g (fscal (-1) (vZ (ktng K)))) (fmul b (vR (ktng K))))) t p);
    [reflexivity |].
  rewrite (feval_lc_fadd' t p om w _ _ Hw' FgJ1 Fba1).
  rewrite (feval_lc_fmul' t p om w _ _ Hw' Fg (fin_fscal w (-1) _ FaZ)).
  rewrite (feval_lc_fscal' t p om w _ _ Hw' FaZ), (feval_fscal' t p _ _ (z0 _ FaZ)).
  rewrite (feval_lc_fmul' t p om w _ _ Hw' Fb FaR). ring.
Qed.

Lemma R_LN2 : LN2 = La1 * g0 + a1 * Lg + (Lb * a2 + b0 * La2).
Proof.
  assert (Hw' : 0 < w) by lra.
  transitivity (feval (lc om (fadd (fmul g (vR (ktng K))) (fmul b (vZ (ktng K))))) t p); [reflexivity |].
  rewrite (feval_lc_fadd' t p om w _ _ Hw' FgJ2 Fba2).
  rewrite (feval_lc_fmul' t p om w _ _ Hw' Fg FaR), (feval_lc_fmul' t p om w _ _ Hw' Fb FaZ). ring.
Qed.

Lemma R_e1 : e1 = s0 * (E1 * N2 - E2 * N1).
Proof.
  unfold keta1. rewrite (feval_fmul' t p _ _ (z0 _ FS) (z0 _ (fin_wedge w _ _ Hw0 FE FN))).
  rewrite (feval_wedge' t p _ _ (vz0 _ FE) (vz0 _ FN)). reflexivity.
Qed.

Lemma R_e2 : e2 = s0 * (a1 * E2 - a2 * E1).
Proof.
  unfold keta2. rewrite (feval_fmul' t p _ _ (z0 _ FS) (z0 _ (fin_wedge w _ _ Hw0 Fa FE))).
  rewrite (feval_wedge' t p _ _ (vz0 _ Fa) (vz0 _ FE)). reflexivity.
Qed.

Lemma R_T : Tv = s0 * ((LN1 - (D11 * N1 + D12 * N2)) * N2 - (LN2 - (D21 * N1 + D22 * N2)) * N1).
Proof.
  assert (FN1 : vfin w1 (knrm K g b)) by (apply (vfin_mono w); [apply Hw10 | apply FN]).
  assert (Fw : fin w1 (wedge (kmln F om K g b) (knrm K g b))) by (apply fin_wedge; [left; apply Hw1 | apply Fmln | exact FN1]).
  assert (Fmp1 : vfin w1 (mapp (DVf F K) (knrm K g b))).
  { apply vfin_mapp; [left; apply Hw1 | apply (mfin_mono w); [apply Hw10 | exact FD] | exact FN1]. }
  assert (MR : feval (vR (kmln F om K g b)) t p = LN1 - (D11 * N1 + D12 * N2)).
  { transitivity (feval (fsub (lc om (vR (knrm K g b))) (vR (mapp (DVf F K) (knrm K g b)))) t p); [reflexivity |].
    rewrite (feval_fsub' t p _ _ (z1 _ FLNR) (z1 _ (proj1 Fmp1))).
    rewrite (feval_mapp_R t p _ _ (mz0 _ FD) (vz0 _ FN)). reflexivity. }
  assert (MZ : feval (vZ (kmln F om K g b)) t p = LN2 - (D21 * N1 + D22 * N2)).
  { transitivity (feval (fsub (lc om (vZ (knrm K g b))) (vZ (mapp (DVf F K) (knrm K g b)))) t p); [reflexivity |].
    rewrite (feval_fsub' t p _ _ (z1 _ FLNZ) (z1 _ (proj2 Fmp1))).
    rewrite (feval_mapp_Z t p _ _ (mz0 _ FD) (vz0 _ FN)). reflexivity. }
  unfold ktwist. rewrite (feval_fmul' t p _ _ (z0 _ FS) (z1 _ Fw)).
  rewrite (feval_wedge' t p _ _ (vz1 _ Fmln) (vz0 _ FN)), MR, MZ. reflexivity.
Qed.

Lemma R_x2 : x2 = feval (kw2 F om K) t p + kxi20 F om K g b.
Proof.
  unfold kxi2. rewrite (feval_fadd' t p _ _ (z1 _ Fw2) (z1 _ (fin_fconst w1 _))), feval_fconst. reflexivity.
Qed.

Lemma R_Lx1 : Lx1 = - (e1 + Tv * x2).
Proof.
  assert (Hw2' : 0 < w2) by apply Hw2.
  assert (FTw : fin w1 (fmul (ktwist F om K g b) (kw2 F om K))) by (apply fin_fmul; [left; apply Hw1 | apply FT | apply Fw2]).
  assert (FsT : fin w1 (fscal (kxi20 F om K g b) (ktwist F om K g b))) by (apply fin_fscal, FT).
  assert (Fsum : fin w1 (fadd (fmul (ktwist F om K g b) (kw2 F om K)) (fscal (kxi20 F om K g b) (ktwist F om K g b))))
    by (apply fin_fadd; [exact FTw | exact FsT]).
  transitivity (feval (lc om (fscal (-1) (linv om (krhs1 F om K g b)))) t p); [reflexivity |].
  rewrite (feval_lc_fscal' t p om w2 _ _ Hw2' Flinv1).
  rewrite (feval_lc_linv' t p om gamma _ Hdio Hgam (z1 _ Frhs1)).
  rewrite (krhs1_mean F om K g b Htw).
  transitivity (-1 * (feval (fadd (keta1 F om K g b) (fadd (fmul (ktwist F om K g b) (kw2 F om K))
                                  (fscal (kxi20 F om K g b) (ktwist F om K g b)))) t p - 0)); [reflexivity |].
  rewrite (feval_fadd' t p _ _ (z0 _ Feta1) (z1 _ Fsum)), (feval_fadd' t p _ _ (z1 _ FTw) (z1 _ FsT)).
  rewrite (feval_fmul' t p _ _ (z1 _ FT) (z1 _ Fw2)), (feval_fscal' t p _ _ (z1 _ FT)), R_x2. ring.
Qed.

Lemma R_Lx2 : Lx2 = - e2.
Proof.
  assert (Hw1' : 0 < w1) by apply Hw1.
  assert (Fl : fin w1 (linv om (keta2 F om K))).
  { apply (fin_linv om gamma); [exact Hdio | exact Hgam | exact Hd | apply Feta2]. }
  transitivity (feval (lc om (fadd (kw2 F om K) (fconst (kxi20 F om K g b)))) t p); [reflexivity |].
  rewrite (feval_lc_fadd' t p om w1 _ _ Hw1' Fw2 (fin_fconst w1 _)), feval_lc_fconst.
  transitivity (feval (lc om (fscal (-1) (linv om (keta2 F om K)))) t p + 0); [reflexivity |].
  rewrite (feval_lc_fscal' t p om w1 _ _ Hw1' Fl).
  rewrite (feval_lc_linv' t p om gamma _ Hdio Hgam (z0 _ Feta2)), Hmean2. ring.
Qed.

Lemma R_alpha : al = s0 * (dE1 * N2 - dE2 * N1).
Proof.
  assert (Fw : fin w1 (wedge (vdt (kerr F om K)) (knrm K g b))).
  { apply fin_wedge; [left; apply Hw1 | apply FdE | apply (vfin_mono w); [apply Hw10 | apply FN]]. }
  unfold kalpha. rewrite (feval_fmul' t p _ _ (z0 _ FS) (z1 _ Fw)).
  rewrite (feval_wedge' t p _ _ (vz1 _ FdE) (vz0 _ FN)). reflexivity.
Qed.

Lemma R_beta : be = s0 * (a1 * dE2 - a2 * dE1).
Proof.
  assert (Fw : fin w1 (wedge (ktng K) (vdt (kerr F om K)))).
  { apply fin_wedge; [left; apply Hw1 | apply (vfin_mono w); [apply Hw10 | exact Fa] | apply FdE]. }
  unfold kbeta. rewrite (feval_fmul' t p _ _ (z0 _ FS) (z1 _ Fw)).
  rewrite (feval_wedge' t p _ _ (vz0 _ Fa) (vz1 _ FdE)). reflexivity.
Qed.

Lemma R_c : cv = - ((s1 * E1 + s2 * E2) * (a1 * a1 + a2 * a2) * g0) - al.
Proof.
  assert (Fge : fin w (vdot (GSf F K) (kerr F om K))) by (apply fin_vdot; [apply Hw0 | exact FG | apply FE]).
  assert (Faa : fin w (vdot (ktng K) (ktng K))) by (apply fin_vdot; [apply Hw0 | exact Fa | exact Fa]).
  assert (Fp : fin w (fmul (vdot (GSf F K) (kerr F om K)) (vdot (ktng K) (ktng K))))
    by (apply fin_fmul; [apply Hw0 | exact Fge | exact Faa]).
  assert (Fq : fin w (fmul (fmul (vdot (GSf F K) (kerr F om K)) (vdot (ktng K) (ktng K))) g))
    by (apply fin_fmul; [apply Hw0 | exact Fp | exact Fg]).
  unfold kc.
  rewrite (feval_fsub' t p _ _ (z0 _ (fin_fscal w (-1) _ Fq)) (z1 _ Falpha)).
  rewrite (feval_fscal' t p _ _ (z0 _ Fq)), (feval_fmul' t p _ _ (z0 _ Fp) (z0 _ Fg)),
    (feval_fmul' t p _ _ (z0 _ Fge) (z0 _ Faa)).
  rewrite (feval_vdot' t p _ _ (vz0 _ FG) (vz0 _ FE)), (feval_vdot' t p _ _ (vz0 _ Fa) (vz0 _ Fa)).
  ring.
Qed.

(** The correction, its image under L, the remainder and the next error at the point. *)

Lemma V_corrR : feval (vR (kcorr F om K g b)) t p = x1 * a1 + x2 * N1.
Proof.
  assert (G1 : fin 0 (fmul (kxi1 F om K g b) (vR (ktng K)))) by (apply fin_fmul; [lra | apply z2, Fxi1 | apply z0, FaR]).
  assert (G2 : fin 0 (fmul (kxi2 F om K g b) (vR (knrm K g b)))) by (apply fin_fmul; [lra | apply z1, Fxi2 | apply z0, FNR]).
  transitivity (feval (fadd (fmul (kxi1 F om K g b) (vR (ktng K))) (fmul (kxi2 F om K g b) (vR (knrm K g b)))) t p);
    [reflexivity |].
  rewrite (feval_fadd' t p _ _ G1 G2), (feval_fmul' t p _ _ (z2 _ Fxi1) (z0 _ FaR)),
    (feval_fmul' t p _ _ (z1 _ Fxi2) (z0 _ FNR)). reflexivity.
Qed.

Lemma V_corrZ : feval (vZ (kcorr F om K g b)) t p = x1 * a2 + x2 * N2.
Proof.
  assert (G1 : fin 0 (fmul (kxi1 F om K g b) (vZ (ktng K)))) by (apply fin_fmul; [lra | apply z2, Fxi1 | apply z0, FaZ]).
  assert (G2 : fin 0 (fmul (kxi2 F om K g b) (vZ (knrm K g b)))) by (apply fin_fmul; [lra | apply z1, Fxi2 | apply z0, FNZ]).
  transitivity (feval (fadd (fmul (kxi1 F om K g b) (vZ (ktng K))) (fmul (kxi2 F om K g b) (vZ (knrm K g b)))) t p);
    [reflexivity |].
  rewrite (feval_fadd' t p _ _ G1 G2), (feval_fmul' t p _ _ (z2 _ Fxi1) (z0 _ FaZ)),
    (feval_fmul' t p _ _ (z1 _ Fxi2) (z0 _ FNZ)). reflexivity.
Qed.

Lemma V_LcorrR : feval (lc om (vR (kcorr F om K g b))) t p = Lx1 * a1 + x1 * La1 + (Lx2 * N1 + x2 * LN1).
Proof.
  assert (Hw2' : 0 < w2) by apply Hw2.
  assert (Fa2 : fin w2 (vR (ktng K))) by (apply (fin_mono w); [apply Hw20 | exact FaR]).
  assert (FN2 : fin w2 (vR (knrm K g b))) by (apply (fin_mono w); [apply Hw20 | exact FNR]).
  assert (G1 : fin w2 (fmul (kxi1 F om K g b) (vR (ktng K)))) by (apply fin_fmul; [lra | apply Fxi1 | exact Fa2]).
  assert (G2 : fin w2 (fmul (kxi2 F om K g b) (vR (knrm K g b)))) by (apply fin_fmul; [lra | apply Fxi2' | exact FN2]).
  transitivity (feval (lc om (fadd (fmul (kxi1 F om K g b) (vR (ktng K))) (fmul (kxi2 F om K g b) (vR (knrm K g b))))) t p);
    [reflexivity |].
  rewrite (feval_lc_fadd' t p om w2 _ _ Hw2' G1 G2).
  rewrite (feval_lc_fmul' t p om w2 _ _ Hw2' Fxi1 Fa2), (feval_lc_fmul' t p om w2 _ _ Hw2' Fxi2' FN2).
  reflexivity.
Qed.

Lemma V_LcorrZ : feval (lc om (vZ (kcorr F om K g b))) t p = Lx1 * a2 + x1 * La2 + (Lx2 * N2 + x2 * LN2).
Proof.
  assert (Hw2' : 0 < w2) by apply Hw2.
  assert (Fa2 : fin w2 (vZ (ktng K))) by (apply (fin_mono w); [apply Hw20 | exact FaZ]).
  assert (FN2 : fin w2 (vZ (knrm K g b))) by (apply (fin_mono w); [apply Hw20 | exact FNZ]).
  assert (G1 : fin w2 (fmul (kxi1 F om K g b) (vZ (ktng K)))) by (apply fin_fmul; [lra | apply Fxi1 | exact Fa2]).
  assert (G2 : fin w2 (fmul (kxi2 F om K g b) (vZ (knrm K g b)))) by (apply fin_fmul; [lra | apply Fxi2' | exact FN2]).
  transitivity (feval (lc om (fadd (fmul (kxi1 F om K g b) (vZ (ktng K))) (fmul (kxi2 F om K g b) (vZ (knrm K g b))))) t p);
    [reflexivity |].
  rewrite (feval_lc_fadd' t p om w2 _ _ Hw2' G1 G2).
  rewrite (feval_lc_fmul' t p om w2 _ _ Hw2' Fxi1 Fa2), (feval_lc_fmul' t p om w2 _ _ Hw2' Fxi2' FN2).
  reflexivity.
Qed.

Lemma V_remR : feval (vR (kremq F om K g b)) t p
  = feval (vR (Vf F (knext F om K g b))) t p - feval (vR (Vf F K)) t p
    - (D11 * (x1 * a1 + x2 * N1) + D12 * (x1 * a2 + x2 * N2)).
Proof.
  assert (G : fin 0 (fsub (vR (Vf F (knext F om K g b))) (vR (Vf F K)))) by (apply fin_fsub; [apply z2, FV'R | apply z0, FVR]).
  transitivity (feval (fsub (fsub (vR (Vf F (knext F om K g b))) (vR (Vf F K)))
                            (vR (mapp (DVf F K) (kcorr F om K g b)))) t p); [reflexivity |].
  rewrite (feval_fsub' t p _ _ G (z2 _ (proj1 Fmp))), (feval_fsub' t p _ _ (z2 _ FV'R) (z0 _ FVR)).
  rewrite (feval_mapp_R t p _ _ (mz0 _ FD) (vz2 _ Fcorr)), V_corrR, V_corrZ. reflexivity.
Qed.

Lemma V_remZ : feval (vZ (kremq F om K g b)) t p
  = feval (vZ (Vf F (knext F om K g b))) t p - feval (vZ (Vf F K)) t p
    - (D21 * (x1 * a1 + x2 * N1) + D22 * (x1 * a2 + x2 * N2)).
Proof.
  assert (G : fin 0 (fsub (vZ (Vf F (knext F om K g b))) (vZ (Vf F K)))) by (apply fin_fsub; [apply z2, FV'Z | apply z0, FVZ]).
  transitivity (feval (fsub (fsub (vZ (Vf F (knext F om K g b))) (vZ (Vf F K)))
                            (vZ (mapp (DVf F K) (kcorr F om K g b)))) t p); [reflexivity |].
  rewrite (feval_fsub' t p _ _ G (z2 _ (proj2 Fmp))), (feval_fsub' t p _ _ (z2 _ FV'Z) (z0 _ FVZ)).
  rewrite (feval_mapp_Z t p _ _ (mz0 _ FD) (vz2 _ Fcorr)), V_corrR, V_corrZ. reflexivity.
Qed.

Lemma V_nextR : feval (vR (kerr F om (knext F om K g b))) t p
  = E1 + feval (vR (Vf F K)) t p + (Lx1 * a1 + x1 * La1 + (Lx2 * N1 + x2 * LN1))
    - feval (vR (Vf F (knext F om K g b))) t p.
Proof.
  assert (Hw2' : 0 < w2) by apply Hw2.
  assert (Fl : fin 0 (lc om (vR (knext F om K g b)))).
  { replace 0 with (w2 - w2) by ring. apply fin_lc; [exact Hw2' | exact FnR]. }
  transitivity (feval (fsub (lc om (vR (knext F om K g b))) (vR (Vf F (knext F om K g b)))) t p); [reflexivity |].
  rewrite (feval_fsub' t p _ _ Fl (z2 _ FV'R)).
  transitivity (feval (lc om (fadd (vR K) (vR (kcorr F om K g b)))) t p - feval (vR (Vf F (knext F om K g b))) t p);
    [reflexivity |].
  rewrite (feval_lc_fadd' t p om w2 _ _ Hw2' FKR FcR), V_LcorrR.
  rewrite (feval_feq _ _ t p lc_err_R), (feval_fadd' t p _ _ (z0 _ FER) (z0 _ FVR)). ring.
Qed.

Lemma V_nextZ : feval (vZ (kerr F om (knext F om K g b))) t p
  = E2 + feval (vZ (Vf F K)) t p + (Lx1 * a2 + x1 * La2 + (Lx2 * N2 + x2 * LN2))
    - feval (vZ (Vf F (knext F om K g b))) t p.
Proof.
  assert (Hw2' : 0 < w2) by apply Hw2.
  assert (Fl : fin 0 (lc om (vZ (knext F om K g b)))).
  { replace 0 with (w2 - w2) by ring. apply fin_lc; [exact Hw2' | exact FnZ]. }
  transitivity (feval (fsub (lc om (vZ (knext F om K g b))) (vZ (Vf F (knext F om K g b)))) t p); [reflexivity |].
  rewrite (feval_fsub' t p _ _ Fl (z2 _ FV'Z)).
  transitivity (feval (lc om (fadd (vZ K) (vZ (kcorr F om K g b)))) t p - feval (vZ (Vf F (knext F om K g b))) t p);
    [reflexivity |].
  rewrite (feval_lc_fadd' t p om w2 _ _ Hw2' FKZ FcZ), V_LcorrZ.
  rewrite (feval_feq _ _ t p lc_err_Z), (feval_fadd' t p _ _ (z0 _ FEZ) (z0 _ FVZ)). ring.
Qed.

Lemma V_errxR : feval (vR (kerrx F om K g b)) t p
  = al * x1 * a1 + (be * x1 + cv * x2) * N1 - feval (vR (kremq F om K g b)) t p.
Proof.
  assert (A0 : fin 0 (fmul (kalpha F om K g b) (kxi1 F om K g b))) by (apply fin_fmul; [lra | apply z1, Falpha | apply z2, Fxi1]).
  assert (B0 : fin 0 (fmul (kbeta F om K) (kxi1 F om K g b))) by (apply fin_fmul; [lra | apply z1, Fbeta | apply z2, Fxi1]).
  assert (C0 : fin 0 (fmul (kc F om K g b) (kxi2 F om K g b))) by (apply fin_fmul; [lra | apply z1, Fc | apply z1, Fxi2]).
  assert (BC0 : fin 0 (fadd (fmul (kbeta F om K) (kxi1 F om K g b)) (fmul (kc F om K g b) (kxi2 F om K g b))))
    by (apply fin_fadd; [exact B0 | exact C0]).
  assert (P0 : fin 0 (fmul (fmul (kalpha F om K g b) (kxi1 F om K g b)) (vR (ktng K)))) by (apply fin_fmul; [lra | exact A0 | apply z0, FaR]).
  assert (Q0 : fin 0 (fmul (fadd (fmul (kbeta F om K) (kxi1 F om K g b)) (fmul (kc F om K g b) (kxi2 F om K g b))) (vR (knrm K g b))))
    by (apply fin_fmul; [lra | exact BC0 | apply z0, FNR]).
  transitivity (feval (fsub (fadd (fmul (fmul (kalpha F om K g b) (kxi1 F om K g b)) (vR (ktng K)))
                                  (fmul (fadd (fmul (kbeta F om K) (kxi1 F om K g b)) (fmul (kc F om K g b) (kxi2 F om K g b)))
                                        (vR (knrm K g b))))
                            (vR (kremq F om K g b))) t p); [reflexivity |].
  rewrite (feval_fsub' t p _ _ (fin_fadd 0 _ _ P0 Q0) (z2 _ FqR)), (feval_fadd' t p _ _ P0 Q0).
  rewrite (feval_fmul' t p _ _ A0 (z0 _ FaR)), (feval_fmul' t p _ _ (z1 _ Falpha) (z2 _ Fxi1)).
  rewrite (feval_fmul' t p _ _ BC0 (z0 _ FNR)), (feval_fadd' t p _ _ B0 C0).
  rewrite (feval_fmul' t p _ _ (z1 _ Fbeta) (z2 _ Fxi1)), (feval_fmul' t p _ _ (z1 _ Fc) (z1 _ Fxi2)).
  reflexivity.
Qed.

Lemma V_errxZ : feval (vZ (kerrx F om K g b)) t p
  = al * x1 * a2 + (be * x1 + cv * x2) * N2 - feval (vZ (kremq F om K g b)) t p.
Proof.
  assert (A0 : fin 0 (fmul (kalpha F om K g b) (kxi1 F om K g b))) by (apply fin_fmul; [lra | apply z1, Falpha | apply z2, Fxi1]).
  assert (B0 : fin 0 (fmul (kbeta F om K) (kxi1 F om K g b))) by (apply fin_fmul; [lra | apply z1, Fbeta | apply z2, Fxi1]).
  assert (C0 : fin 0 (fmul (kc F om K g b) (kxi2 F om K g b))) by (apply fin_fmul; [lra | apply z1, Fc | apply z1, Fxi2]).
  assert (BC0 : fin 0 (fadd (fmul (kbeta F om K) (kxi1 F om K g b)) (fmul (kc F om K g b) (kxi2 F om K g b))))
    by (apply fin_fadd; [exact B0 | exact C0]).
  assert (P0 : fin 0 (fmul (fmul (kalpha F om K g b) (kxi1 F om K g b)) (vZ (ktng K)))) by (apply fin_fmul; [lra | exact A0 | apply z0, FaZ]).
  assert (Q0 : fin 0 (fmul (fadd (fmul (kbeta F om K) (kxi1 F om K g b)) (fmul (kc F om K g b) (kxi2 F om K g b))) (vZ (knrm K g b))))
    by (apply fin_fmul; [lra | exact BC0 | apply z0, FNZ]).
  transitivity (feval (fsub (fadd (fmul (fmul (kalpha F om K g b) (kxi1 F om K g b)) (vZ (ktng K)))
                                  (fmul (fadd (fmul (kbeta F om K) (kxi1 F om K g b)) (fmul (kc F om K g b) (kxi2 F om K g b)))
                                        (vZ (knrm K g b))))
                            (vZ (kremq F om K g b))) t p); [reflexivity |].
  rewrite (feval_fsub' t p _ _ (fin_fadd 0 _ _ P0 Q0) (z2 _ FqZ)), (feval_fadd' t p _ _ P0 Q0).
  rewrite (feval_fmul' t p _ _ A0 (z0 _ FaZ)), (feval_fmul' t p _ _ (z1 _ Falpha) (z2 _ Fxi1)).
  rewrite (feval_fmul' t p _ _ BC0 (z0 _ FNZ)), (feval_fadd' t p _ _ B0 C0).
  rewrite (feval_fmul' t p _ _ (z1 _ Fbeta) (z2 _ Fxi1)), (feval_fmul' t p _ _ (z1 _ Fc) (z1 _ Fxi2)).
  reflexivity.
Qed.

Theorem step_identity :
  feval (vR (kerr F om (knext F om K g b))) t p = feval (vR (kerrx F om K g b)) t p /\
  feval (vZ (kerr F om (knext F om K g b))) t p = feval (vZ (kerrx F om K g b)) t p.
Proof.
  pose proof (frame_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x1 _ _ _ _ _ _ _ _ _ _ _ _ _
                R_frame R_La1 R_La2 R_Ls R_Lg R_N1 R_N2 R_LN1 R_LN2 R_e1 R_e2 R_T R_Lx1 R_Lx2
                R_alpha R_beta R_c) as [F1 F2].
  split.
  - rewrite V_nextR, V_errxR, V_remR.
    transitivity (a1 * (al * x1) + N1 * (be * x1 + cv * x2)
                  + (feval (vR (Vf F K)) t p - feval (vR (Vf F (knext F om K g b))) t p
                     + (D11 * (a1 * x1 + N1 * x2) + D12 * (a2 * x1 + N2 * x2)))).
    + rewrite <- F1. ring.
    + ring.
  - rewrite V_nextZ, V_errxZ, V_remZ.
    transitivity (a2 * (al * x1) + N2 * (be * x1 + cv * x2)
                  + (feval (vZ (Vf F K)) t p - feval (vZ (Vf F (knext F om K g b))) t p
                     + (D21 * (a1 * x1 + N1 * x2) + D22 * (a2 * x1 + N2 * x2)))).
    + rewrite <- F2. ring.
    + ring.
Qed.

End Point.

End Identity.
