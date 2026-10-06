(** Families of finite norm on a strip, and the values of their functions.

    [fin rho u] says that u has some norm on the strip of width rho. It is
    kept by sums, multiples and products, and a derivative, L or L^-1 keeps
    it on any narrower strip ([fin_dt], [fin_lc], [fin_linv]). On a strip of
    positive width the function of a family is differentiable, and the
    values of the functions of sums, products, L and L^-1 at a point follow
    from the values of their parts ([feval_fmul'], [feval_lc_fmul'],
    [feval_lc_fadd'], [feval_lc_linv']). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon KAMVec.
Local Open Scope R_scope.

Definition fin (rho : R) (u : fser) : Prop := exists M, nbound rho M u.
Definition vfin (rho : R) (u : vf) : Prop := fin rho (vR u) /\ fin rho (vZ u).
Definition mfin (rho : R) (A : mf) : Prop :=
  fin rho (mRR A) /\ fin rho (mRZ A) /\ fin rho (mZR A) /\ fin rho (mZZ A).

(** * Closure *)

Lemma fin_mono (rho rho' : R) (u : fser) : rho' <= rho -> fin rho u -> fin rho' u.
Proof. intros H [M HM]. exists M. apply (nbound_mono rho); assumption. Qed.

Lemma vfin_mono (rho rho' : R) (u : vf) : rho' <= rho -> vfin rho u -> vfin rho' u.
Proof. intros H [H1 H2]. split; apply (fin_mono rho); assumption. Qed.

Lemma mfin_mono (rho rho' : R) (A : mf) : rho' <= rho -> mfin rho A -> mfin rho' A.
Proof. intros H [H1 [H2 [H3 H4]]]. repeat split; apply (fin_mono rho); assumption. Qed.

Lemma fin_fadd (rho : R) (u v : fser) : fin rho u -> fin rho v -> fin rho (fadd u v).
Proof. intros [M1 H1] [M2 H2]. exists (M1 + M2). apply nbound_fadd; assumption. Qed.

Lemma fin_fscal (rho c : R) (u : fser) : fin rho u -> fin rho (fscal c u).
Proof. intros [M H]. exists (Rabs c * M). apply nbound_fscal, H. Qed.

Lemma fin_fsub (rho : R) (u v : fser) : fin rho u -> fin rho v -> fin rho (fsub u v).
Proof. intros [M1 H1] [M2 H2]. exists (M1 + M2). apply nbound_fsub; assumption. Qed.

Lemma fin_fmul (rho : R) (u v : fser) : 0 <= rho -> fin rho u -> fin rho v -> fin rho (fmul u v).
Proof. intros Hr [M1 H1] [M2 H2]. exists (M1 * M2). apply nbound_fmul; assumption. Qed.

Lemma fin_dt (rho d : R) (u : fser) : 0 < d -> fin rho u -> fin (rho - d) (dt u).
Proof. intros Hd [M H]. exists (/ (exp 1 * d) * M). apply nbound_dt; assumption. Qed.

Lemma fin_lc (om rho d : R) (u : fser) : 0 < d -> fin rho u -> fin (rho - d) (lc om u).
Proof. intros Hd [M H]. eexists. apply nbound_lc; eassumption. Qed.

Lemma fin_linv (om gamma rho d : R) (u : fser) :
  diophantine1 om gamma -> 0 < gamma <= 1 -> 0 < d -> fin rho u -> fin (rho - d) (linv om u).
Proof. intros Hdio Hg Hd [M H]. eexists. apply (nbound_linv om gamma Hdio Hg); eassumption. Qed.

Lemma fin_fconst (rho c : R) : fin rho (fconst c).
Proof. exists (Rabs c). apply nbound_fconst. Qed.

Lemma fin_canon (rho : R) (u : fser) : fin rho u -> fin rho (canon u).
Proof. intros [M H]. exists M. apply nbound_canon, H. Qed.

Lemma vfin_vadd (rho : R) (u v : vf) : vfin rho u -> vfin rho v -> vfin rho (vadd u v).
Proof. intros [H1 H2] [H3 H4]. split; apply fin_fadd; assumption. Qed.

Lemma vfin_vsub (rho : R) (u v : vf) : vfin rho u -> vfin rho v -> vfin rho (vsub u v).
Proof. intros [H1 H2] [H3 H4]. split; apply fin_fsub; assumption. Qed.

Lemma vfin_vscal (rho c : R) (u : vf) : vfin rho u -> vfin rho (vscal c u).
Proof. intros [H1 H2]. split; apply fin_fscal; assumption. Qed.

Lemma vfin_vsmul (rho : R) (s : fser) (u : vf) :
  0 <= rho -> fin rho s -> vfin rho u -> vfin rho (vsmul s u).
Proof. intros Hr Hs [H1 H2]. split; apply fin_fmul; assumption. Qed.

Lemma vfin_vdt (rho d : R) (u : vf) : 0 < d -> vfin rho u -> vfin (rho - d) (vdt u).
Proof. intros Hd [H1 H2]. split; apply fin_dt; assumption. Qed.

Lemma vfin_vlc (om rho d : R) (u : vf) : 0 < d -> vfin rho u -> vfin (rho - d) (vlc om u).
Proof. intros Hd [H1 H2]. split; apply fin_lc; assumption. Qed.

Lemma vfin_vJ (rho : R) (u : vf) : vfin rho u -> vfin rho (vJ u).
Proof. intros [H1 H2]. split; [apply fin_fscal, H2 | exact H1]. Qed.

Lemma fin_wedge (rho : R) (u v : vf) : 0 <= rho -> vfin rho u -> vfin rho v -> fin rho (wedge u v).
Proof. intros Hr [H1 H2] [H3 H4]. apply fin_fsub; apply fin_fmul; assumption. Qed.

Lemma fin_vdot (rho : R) (u v : vf) : 0 <= rho -> vfin rho u -> vfin rho v -> fin rho (vdot u v).
Proof. intros Hr [H1 H2] [H3 H4]. apply fin_fadd; apply fin_fmul; assumption. Qed.

Lemma vfin_mapp (rho : R) (A : mf) (u : vf) :
  0 <= rho -> mfin rho A -> vfin rho u -> vfin rho (mapp A u).
Proof.
  intros Hr [H1 [H2 [H3 H4]]] [H5 H6].
  split; apply fin_fadd; apply fin_fmul; assumption.
Qed.

Lemma fin_mtr (rho : R) (A : mf) : mfin rho A -> fin rho (mtr A).
Proof. intros [H1 [_ [_ H4]]]. apply fin_fadd; assumption. Qed.

(** * Values at a point *)

Section Values.

Variables t p : R.

Lemma feval_fadd' (u v : fser) : fin 0 u -> fin 0 v -> feval (fadd u v) t p = feval u t p + feval v t p.
Proof. intros [M1 H1] [M2 H2]. apply (feval_fadd u v M1 M2 t p H1 H2). Qed.

Lemma feval_fscal' (c : R) (u : fser) : fin 0 u -> feval (fscal c u) t p = c * feval u t p.
Proof. intros [M H]. apply (feval_fscal c u M t p H). Qed.

Lemma feval_fsub' (u v : fser) : fin 0 u -> fin 0 v -> feval (fsub u v) t p = feval u t p - feval v t p.
Proof. intros [M1 H1] [M2 H2]. apply (feval_fsub u v M1 M2 t p H1 H2). Qed.

Lemma feval_fmul' (u v : fser) : fin 0 u -> fin 0 v -> feval (fmul u v) t p = feval u t p * feval v t p.
Proof. intros [M1 H1] [M2 H2]. apply (feval_fmul u v M1 M2 t p H1 H2). Qed.

Lemma feval_wedge' (u v : vf) : vfin 0 u -> vfin 0 v ->
  feval (wedge u v) t p = feval (vR u) t p * feval (vZ v) t p - feval (vZ u) t p * feval (vR v) t p.
Proof.
  intros [H1 H2] [H3 H4]. unfold wedge.
  rewrite feval_fsub', !feval_fmul' by (try apply fin_fmul; try lra; assumption). reflexivity.
Qed.

Lemma feval_vdot' (u v : vf) : vfin 0 u -> vfin 0 v ->
  feval (vdot u v) t p = feval (vR u) t p * feval (vR v) t p + feval (vZ u) t p * feval (vZ v) t p.
Proof.
  intros [H1 H2] [H3 H4]. unfold vdot.
  rewrite feval_fadd', !feval_fmul' by (try apply fin_fmul; try lra; assumption). reflexivity.
Qed.

Lemma feval_mapp_R (A : mf) (u : vf) : mfin 0 A -> vfin 0 u ->
  feval (vR (mapp A u)) t p
  = feval (mRR A) t p * feval (vR u) t p + feval (mRZ A) t p * feval (vZ u) t p.
Proof.
  intros [H1 [H2 [H3 H4]]] [H5 H6]. simpl.
  rewrite feval_fadd', !feval_fmul' by (try apply fin_fmul; try lra; assumption). reflexivity.
Qed.

Lemma feval_mapp_Z (A : mf) (u : vf) : mfin 0 A -> vfin 0 u ->
  feval (vZ (mapp A u)) t p
  = feval (mZR A) t p * feval (vR u) t p + feval (mZZ A) t p * feval (vZ u) t p.
Proof.
  intros [H1 [H2 [H3 H4]]] [H5 H6]. simpl.
  rewrite feval_fadd', !feval_fmul' by (try apply fin_fmul; try lra; assumption). reflexivity.
Qed.

Lemma feval_mtr' (A : mf) : mfin 0 A -> feval (mtr A) t p = feval (mRR A) t p + feval (mZZ A) t p.
Proof. intros [H1 [_ [_ H4]]]. unfold mtr. apply feval_fadd'; assumption. Qed.

Lemma lc_fadd_feq (om : R) (u v : fser) : feq (lc om (fadd u v)) (fadd (lc om u) (lc om v)).
Proof. intros m n. unfold lc, fadd. simpl. split; ring. Qed.

Lemma lc_fscal_feq (om c : R) (u : fser) : feq (lc om (fscal c u)) (fscal c (lc om u)).
Proof. intros m n. unfold lc, fscal. simpl. split; ring. Qed.

Lemma dt_fadd_feq (u v : fser) : feq (dt (fadd u v)) (fadd (dt u) (dt v)).
Proof. intros m n. unfold dt, fadd. simpl. split; ring. Qed.

Lemma feval_lc_fadd' (om rho : R) (u v : fser) : 0 < rho -> fin rho u -> fin rho v ->
  feval (lc om (fadd u v)) t p = feval (lc om u) t p + feval (lc om v) t p.
Proof.
  intros Hr Hu Hv. rewrite (feval_feq _ _ t p (lc_fadd_feq om u v)).
  apply feval_fadd'; replace 0 with (rho - rho) by ring; apply fin_lc; assumption.
Qed.

Lemma feval_lc_fscal' (om rho c : R) (u : fser) : 0 < rho -> fin rho u ->
  feval (lc om (fscal c u)) t p = c * feval (lc om u) t p.
Proof.
  intros Hr Hu. rewrite (feval_feq _ _ t p (lc_fscal_feq om c u)).
  apply feval_fscal'. replace 0 with (rho - rho) by ring. apply fin_lc; assumption.
Qed.

Lemma feval_lc_fsub' (om rho : R) (u v : fser) : 0 < rho -> fin rho u -> fin rho v ->
  feval (lc om (fsub u v)) t p = feval (lc om u) t p - feval (lc om v) t p.
Proof.
  intros Hr Hu Hv. unfold fsub.
  rewrite (feval_lc_fadd' om rho) by (try apply fin_fscal; assumption).
  rewrite (feval_lc_fscal' om rho) by assumption. ring.
Qed.

Lemma feval_lc_fmul' (om rho : R) (u v : fser) : 0 < rho -> fin rho u -> fin rho v ->
  feval (lc om (fmul u v)) t p
  = feval (lc om u) t p * feval v t p + feval u t p * feval (lc om v) t p.
Proof. intros Hr [M1 H1] [M2 H2]. apply (feval_lc_fmul om rho M1 M2 u v t p Hr H1 H2). Qed.

Lemma feval_dt_fadd' (rho : R) (u v : fser) : 0 < rho -> fin rho u -> fin rho v ->
  feval (dt (fadd u v)) t p = feval (dt u) t p + feval (dt v) t p.
Proof.
  intros Hr Hu Hv. rewrite (feval_feq _ _ t p (dt_fadd_feq u v)).
  apply feval_fadd'; replace 0 with (rho - rho) by ring; apply fin_dt; assumption.
Qed.

Lemma feval_lc_linv' (om gamma : R) (u : fser) :
  diophantine1 om gamma -> 0 < gamma <= 1 -> fin 0 u ->
  feval (lc om (linv om u)) t p = feval u t p - fc u 0 0.
Proof. intros Hd Hg [M H]. apply (feval_lc_linv om gamma M u t p Hd Hg H). Qed.

Lemma lc_fconst_feq (om c : R) : feq (lc om (fconst c)) fzero.
Proof.
  intros m n. unfold lc, fconst, fsingle, fzero, at2, divisor. simpl.
  destruct (Z.eqb_spec m 0) as [-> | Hm]; destruct (Z.eqb_spec n 0) as [-> | Hn]; simpl; split; ring.
Qed.

Lemma feval_fzero : feval fzero t p = 0.
Proof.
  unfold feval. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_const0 |].
  intros m n. unfold term, fzero. simpl. ring.
Qed.

Lemma feval_lc_fconst (om c : R) : feval (lc om (fconst c)) t p = 0.
Proof. rewrite (feval_feq _ _ t p (lc_fconst_feq om c)). apply feval_fzero. Qed.

End Values.
