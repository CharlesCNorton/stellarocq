(** The value of any component of the jet of the total field along a torus.

    Each component of [tot P l K] is P times the projection onto the modes of
    period P of the sum over the base sources of the source's component and
    its stellarator image. At a point of a stellarator-symmetric torus of
    period P, it is therefore the sum over the P shifts p + 2 pi k / P and
    over the base sources of the source's function at (R, p_k, Z) and, with
    the sign of the component under the reflection, at (R, -p_k, -Z)
    ([jet_val]). With the value components this is the field of FieldModel.v;
    with the R and Z derivatives it gives the Jacobian the checks evaluate
    at the points of a grid. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel.
Local Open Scope R_scope.

Section JetVal.

Variables (P : Z) (rho : R) (K : vf) (l : list (src * fser)).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.

(** The component, its function for one source, and its sign under the image. *)
Variable sel : cjet -> fser.
Variable fsrc : src -> R -> R -> R -> R.
Variable sg : bool.
Hypothesis Hsym : forall J, sel (symjet J) = if sg then fsub (sel J) (frefl (sel J)) else fadd (sel J) (frefl (sel J)).
Hypothesis Hadd : forall J1 J2, sel (jadd J1 J2) = fadd (sel J1) (sel J2).
Hypothesis Hzero : sel jzero = fzero.
Hypothesis Hproj : forall J, sel (jproj P J) = fscal (IZR P) (fproj P (sel J)).
Hypothesis Hfin : forall J, jfin rho J -> fin rho (sel J).
Hypothesis Hev : forall sc Y, isq_ok rho (fq sc K) Y -> 0 < feval (fy sc Y K) 0 0 ->
  forall t p, feval (sel (srcjet sc Y K)) t p = fsrc sc (feval (vR K) t p) p (feval (vZ K) t p).

Definition symval (sc : src) (R0 phi Z0 : R) : R :=
  if sg then fsrc sc R0 phi Z0 - fsrc sc R0 (- phi) (- Z0) else fsrc sc R0 phi Z0 + fsrc sc R0 (- phi) (- Z0).

Lemma f0 (u : fser) : fin rho u -> fin 0 u. Proof. apply fin_mono. lra. Qed.

Lemma src_symval (sc : src) (Y : fser) (t p : R) :
  isq_ok rho (fq sc K) Y -> 0 < feval (fy sc Y K) 0 0 ->
  feval (sel (symjet (srcjet sc Y K))) t p = symval sc (feval (vR K) t p) p (feval (vZ K) t p).
Proof.
  intros Hq Hy.
  pose proof (Hfin _ (srcjet_fin sc Y K rho Hr FK Hq Hy)) as F.
  assert (KR : feval (vR K) (- t) (- p) = feval (vR K) t p) by (apply feval_even_refl, (proj1 SK)).
  assert (KZ : feval (vZ K) (- t) (- p) = - feval (vZ K) t p).
  { apply feval_odd_refl; [apply (fin_mono rho); [lra | exact (proj2 FK)] | exact (proj2 SK)]. }
  rewrite Hsym. unfold symval. destruct sg.
  - rewrite (E_sub _ t p (f0 _ F)), !(Hev sc Y Hq Hy), KR, KZ. reflexivity.
  - rewrite (E_add _ t p (f0 _ F)), !(Hev sc Y Hq Hy), KR, KZ. reflexivity.
Qed.

Lemma srcjets_selval (t p : R) :
  feval (sel (srcjets l K)) t p = lsum (fun sy => symval (fst sy) (feval (vR K) t p) p (feval (vZ K) t p)) l.
Proof.
  induction Hl as [| sy l' [Hq Hy] Hl' IH].
  - unfold srcjets, lsum. cbn [fold_right map]. rewrite Hzero. apply feval_fzero'.
  - assert (Ej : srcjets (sy :: l') K = jadd (symjet (srcjet (fst sy) (snd sy) K)) (srcjets l' K))
      by reflexivity.
    rewrite Ej, Hadd.
    pose proof (Hfin _ (symjet_fin rho _ (srcjet_fin _ _ _ rho Hr FK Hq Hy))) as A.
    pose proof (Hfin _ (srcjets_fin rho K l' Hr FK Hl')) as B.
    rewrite (feval_fadd' t p _ _ (f0 _ A) (f0 _ B)), (src_symval (fst sy) (snd sy) t p Hq Hy).
    rewrite (IH Hl'). reflexivity.
Qed.

Theorem jet_val (t p : R) :
  feval (sel (tot P l K)) t p =
  fsum (fun k => lsum (fun sy => symval (fst sy) (feval (vR K) t p) (p + INR k * (2 * PI / IZR P))
                                        (feval (vZ K) t p)) l) (Z.to_nat P).
Proof.
  unfold tot. rewrite Hproj.
  pose proof (Hfin _ (srcjets_fin rho K l Hr FK Hl)) as F.
  rewrite (Epr P HP _ t p (f0 _ F)). apply fsum_ext. intros k.
  destruct QK as [QR QZ].
  rewrite srcjets_selval. rewrite !(feval_per_shift P _ t p k HP) by assumption. reflexivity.
Qed.

End JetVal.

(** * The components the checks read *)

Section Components.

Variables (P : Z) (rho : R) (K : vf) (l : list (src * fser)).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.

(** The value of a component at (t, p): sum over the P shifts and the base
    sources of the source's function at the point and at its image. *)
Definition comp_val (f : src -> R -> R -> R -> R) (sg : bool) (t p : R) : R :=
  fsum (fun k => lsum (fun sy => symval f sg (fst sy) (feval (vR K) t p) (p + INR k * (2 * PI / IZR P))
                                        (feval (vZ K) t p)) l) (Z.to_nat P).

Ltac jv sel f sg Ev Fin :=
  apply (jet_val P rho K l HP Hr FK SK QK Hl sel f sg);
  [ intros J; reflexivity | intros J1 J2; reflexivity | reflexivity | intros J; reflexivity
  | intros J HJ; unfold jfin in HJ; tauto
  | intros sc Y Hq Hy t0 p0; exact (proj2 (Ev sc Y K rho Hr FK Hq Hy) t0 p0) ].

Theorem val_R (t p : R) : feval (jR (tot P l K)) t p = comp_val fR true t p.
Proof. unfold comp_val. jv jR fR true E_FR jfin. Qed.
Theorem val_P (t p : R) : feval (jP (tot P l K)) t p = comp_val fP false t p.
Proof. unfold comp_val. jv jP fP false E_FP jfin. Qed.
Theorem val_Z (t p : R) : feval (jZ (tot P l K)) t p = comp_val fZ false t p.
Proof. unfold comp_val. jv jZ fZ false E_FZ jfin. Qed.
Theorem val_R_R (t p : R) : feval (jR_R (tot P l K)) t p = comp_val fR_R true t p.
Proof. unfold comp_val. jv jR_R fR_R true E_FR_R jfin. Qed.
Theorem val_R_Z (t p : R) : feval (jR_Z (tot P l K)) t p = comp_val fR_Z false t p.
Proof. unfold comp_val. jv jR_Z fR_Z false E_FR_Z jfin. Qed.
Theorem val_P_R (t p : R) : feval (jP_R (tot P l K)) t p = comp_val fP_R false t p.
Proof. unfold comp_val. jv jP_R fP_R false E_FP_R jfin. Qed.
Theorem val_P_Z (t p : R) : feval (jP_Z (tot P l K)) t p = comp_val fP_Z true t p.
Proof. unfold comp_val. jv jP_Z fP_Z true E_FP_Z jfin. Qed.
Theorem val_Z_R (t p : R) : feval (jZ_R (tot P l K)) t p = comp_val fZ_R false t p.
Proof. unfold comp_val. jv jZ_R fZ_R false E_FZ_R jfin. Qed.
Theorem val_Z_Z (t p : R) : feval (jZ_Z (tot P l K)) t p = comp_val fZ_Z true t p.
Proof. unfold comp_val. jv jZ_Z fZ_Z true E_FZ_Z jfin. Qed.

End Components.
