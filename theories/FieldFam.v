(** The field of one source along a torus, as families.

    [ev rho u f] says that the family u has finite norm on the strip of width
    rho and that its function is f; sums, multiples and products keep the
    relation with the sums, multiples and products of the functions. The
    inverse square root of a family D from an approximant Y, whose Newton
    iteration converges ([isq_ok]), is positive everywhere once it is
    positive at one point, since it is continuous in each angle and nowhere
    zero ([isq_pos]); its function is then 1 / sqrt D ([isq_ev]).

    Along a torus K, the families of one source [sfam] evaluate to the
    field of FieldKern in cylindrical components at the points of the torus,
    with its derivatives in R and Z and its explicit derivative in phi
    ([ev_fR], [ev_fR_R], ...), and they satisfy the chain rule in each angle
    ([dt_chain_R], [dp_chain_R], ...): d_t F = F_R d_t K_R + F_Z d_t K_Z and
    d_p F = F_R d_p K_R + F_Z d_p K_Z + F_phi. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon KAMVec KAMFin Hypotheses Invariance CoilSym FieldKern.
Local Open Scope R_scope.

(** * Families that evaluate to functions *)

Definition ev (rho : R) (u : fser) (f : R -> R -> R) : Prop := fin rho u /\ forall t p, feval u t p = f t p.

Section Ev.

Variable rho : R.
Hypothesis Hr : 0 <= rho.

Lemma fin0 (u : fser) : fin rho u -> fin 0 u.
Proof. apply fin_mono. exact Hr. Qed.

Lemma ev_ext (u : fser) (f g : R -> R -> R) : (forall t p, f t p = g t p) -> ev rho u f -> ev rho u g.
Proof. intros H [F E]. split; [exact F | intros t p; rewrite E; apply H]. Qed.

Lemma ev_fadd (u v : fser) (f g : R -> R -> R) :
  ev rho u f -> ev rho v g -> ev rho (fadd u v) (fun t p => f t p + g t p).
Proof.
  intros [Fu Eu] [Fv Ev]. split; [apply fin_fadd; assumption |].
  intros t p. rewrite (feval_fadd' t p _ _ (fin0 _ Fu) (fin0 _ Fv)), Eu, Ev. reflexivity.
Qed.

Lemma ev_fsub (u v : fser) (f g : R -> R -> R) :
  ev rho u f -> ev rho v g -> ev rho (fsub u v) (fun t p => f t p - g t p).
Proof.
  intros [Fu Eu] [Fv Ev]. split; [apply fin_fsub; assumption |].
  intros t p. rewrite (feval_fsub' t p _ _ (fin0 _ Fu) (fin0 _ Fv)), Eu, Ev. reflexivity.
Qed.

Lemma ev_fscal (c : R) (u : fser) (f : R -> R -> R) :
  ev rho u f -> ev rho (fscal c u) (fun t p => c * f t p).
Proof.
  intros [Fu Eu]. split; [apply fin_fscal; assumption |].
  intros t p. rewrite (feval_fscal' t p _ _ (fin0 _ Fu)), Eu. reflexivity.
Qed.

Lemma ev_fmul (u v : fser) (f g : R -> R -> R) :
  ev rho u f -> ev rho v g -> ev rho (fmul u v) (fun t p => f t p * g t p).
Proof.
  intros [Fu Eu] [Fv Ev]. split; [apply fin_fmul; assumption |].
  intros t p. rewrite (feval_fmul' t p _ _ (fin0 _ Fu) (fin0 _ Fv)), Eu, Ev. reflexivity.
Qed.

Lemma ev_fconst (c : R) : ev rho (fconst c) (fun _ _ => c).
Proof.
  split; [apply fin_fconst |]. intros t p. unfold fconst. rewrite feval_fsingle. unfold mode.
  replace (IZR 0 * t + IZR 0 * p) with 0 by (simpl; ring). rewrite cos_0, sin_0. ring.
Qed.

Lemma ev_self (u : fser) : fin rho u -> ev rho u (feval u).
Proof. intros F. split; [exact F | reflexivity]. Qed.

End Ev.

(** * cos p and sin p *)

Definition cosf : fser := fadd (fsingle 0 1 (/ 2) 0) (fsingle 0 (-1) (/ 2) 0).
Definition sinf : fser := fadd (fsingle 0 1 0 (/ 2)) (fsingle 0 (-1) 0 (- / 2)).

Lemma fin_fsingle (rho : R) (k1 k2 : Z) (c s : R) : fin rho (fsingle k1 k2 c s).
Proof. eexists. apply nbound_fsingle. Qed.

Lemma ev_cosf (rho : R) : 0 <= rho -> ev rho cosf (fun _ p => cos p).
Proof.
  intros Hr. split; [apply fin_fadd; apply fin_fsingle |]. intros t p. unfold cosf.
  rewrite (feval_fadd' t p _ _ (fin_fsingle 0 _ _ _ _) (fin_fsingle 0 _ _ _ _)), !feval_fsingle.
  unfold mode. replace (IZR 0 * t + IZR 1 * p) with p by (simpl; ring).
  replace (IZR 0 * t + IZR (-1) * p) with (- p) by (simpl; ring).
  rewrite cos_neg, sin_neg. field.
Qed.

Lemma ev_sinf (rho : R) : 0 <= rho -> ev rho sinf (fun _ p => sin p).
Proof.
  intros Hr. split; [apply fin_fadd; apply fin_fsingle |]. intros t p. unfold sinf.
  rewrite (feval_fadd' t p _ _ (fin_fsingle 0 _ _ _ _) (fin_fsingle 0 _ _ _ _)), !feval_fsingle.
  unfold mode. replace (IZR 0 * t + IZR 1 * p) with p by (simpl; ring).
  replace (IZR 0 * t + IZR (-1) * p) with (- p) by (simpl; ring).
  rewrite cos_neg, sin_neg. field.
Qed.

(** * Continuity in each angle *)

Lemma feval_cont_t (rho M : R) (u : fser) (p : R) :
  0 < rho -> nbound rho M u -> continuity (fun y => feval u y p).
Proof.
  intros Hr H y0. apply derivable_continuous_pt. exists (feval (dt u) y0 p).
  apply is_derive_Reals. exact (feval_dt rho M u p y0 Hr H).
Qed.

Lemma feval_cont_p (rho M : R) (u : fser) (t : R) :
  0 < rho -> nbound rho M u -> continuity (fun y => feval u t y).
Proof.
  intros Hr H y0. apply derivable_continuous_pt. exists (feval (dp u) t y0).
  apply is_derive_Reals. exact (feval_dp rho M u t y0 Hr H).
Qed.

(** A continuous function with no zero keeps the sign it has at one point. *)
Lemma sign_keep (f : R -> R) (a b : R) :
  continuity f -> (forall x, f x <> 0) -> 0 < f a -> 0 < f b.
Proof.
  intros Hc Hz Ha. destruct (Rlt_le_dec 0 (f b)) as [H | H]; [exact H | exfalso].
  assert (Hb : f b < 0) by (pose proof (Hz b); lra).
  destruct (Rle_dec a b) as [Hab | Hab].
  - destruct (IVT_cor f a b Hc Hab ltac:(nra)) as [z [_ Hz0]]. exact (Hz z Hz0).
  - destruct (IVT_cor f b a Hc ltac:(lra) ltac:(nra)) as [z [_ Hz0]]. exact (Hz z Hz0).
Qed.

(** * The positive inverse square root *)

Definition isq_ok (rho : R) (D Y : fser) : Prop :=
  0 < rho /\ exists MD MY th, nbound rho MD D /\ nbound rho MY Y /\ 0 <= th < 1 /\
    nbound rho th (fsub fone (fmul D (fmul Y Y))).

Section Isq.

Variables (rho : R) (D Y : fser).
Hypothesis H : isq_ok rho D Y.

Lemma isq_rho : 0 < rho. Proof. exact (proj1 H). Qed.

Lemma isq_nb : exists M, nbound rho M (fisqrt D Y).
Proof.
  destruct H as [Hr [MD [MY [th [HD [HY [Hth He]]]]]]].
  eexists. apply (nbound_fisqrt rho (Rlt_le _ _ Hr) D Y MY th HY Hth He).
Qed.

Lemma isq_fin : fin rho (fisqrt D Y).
Proof. exact isq_nb. Qed.

Lemma isq_sq (t p : R) : feval D t p * (feval (fisqrt D Y) t p * feval (fisqrt D Y) t p) = 1.
Proof.
  destruct H as [Hr [MD [MY [th [HD [HY [Hth He]]]]]]].
  exact (feval_fisqrt rho (Rlt_le _ _ Hr) D Y MD MY th HD HY Hth He t p).
Qed.

Lemma isq_nz (t p : R) : feval (fisqrt D Y) t p <> 0.
Proof. intros E. pose proof (isq_sq t p) as S. rewrite E in S. lra. Qed.

Theorem isq_pos : 0 < feval (fisqrt D Y) 0 0 -> forall t p, 0 < feval (fisqrt D Y) t p.
Proof.
  intros H0 t p. destruct isq_nb as [M HM]. pose proof isq_rho as Hr.
  assert (Ht : 0 < feval (fisqrt D Y) t 0).
  { apply (sign_keep (fun y => feval (fisqrt D Y) y 0) 0 t (feval_cont_t rho M _ 0 Hr HM));
      [intros x; apply isq_nz | exact H0]. }
  apply (sign_keep (fun y => feval (fisqrt D Y) t y) 0 p (feval_cont_p rho M _ t Hr HM));
    [intros x; apply isq_nz | exact Ht].
Qed.

Theorem isq_ev (f : R -> R -> R) :
  0 < feval (fisqrt D Y) 0 0 -> ev rho D f -> ev rho (fisqrt D Y) (fun t p => / sqrt (f t p)).
Proof.
  intros H0 [_ ED]. split; [exact isq_fin |]. intros t p.
  pose proof (isq_pos H0 t p) as Hy. pose proof (isq_sq t p) as S. rewrite ED in S.
  set (y := feval (fisqrt D Y) t p) in *.
  assert (Hf : 0 < f t p) by nra.
  assert (Hs : 0 < sqrt (f t p)) by (apply sqrt_lt_R0; exact Hf).
  assert (E2 : sqrt (f t p) * sqrt (f t p) = f t p) by (apply sqrt_sqrt; lra).
  apply (Rmult_eq_reg_l (sqrt (f t p))); [| lra].
  rewrite Rinv_r by lra.
  (* y sqrt f is positive and its square is 1 *)
  assert (Hsq : (sqrt (f t p) * y) * (sqrt (f t p) * y) = 1) by nra.
  assert (Hp : 0 < sqrt (f t p) * y) by nra.
  nra.
Qed.

End Isq.

(** * The families of one source along a torus *)

Section SourceFam.

Variables (sc : src) (Y : fser) (K : vf).
Let p1 := sp1 sc. Let p2 := sp2 sc. Let p3 := sp3 sc.
Let d1 := sd1 sc. Let d2 := sd2 sc. Let d3 := sd3 sc.

Definition fx1 : fser := fmul (vR K) cosf.
Definition fx2 : fser := fmul (vR K) sinf.
Definition fr1 : fser := fsub fx1 (fconst p1).
Definition fr2 : fser := fsub fx2 (fconst p2).
Definition fr3 : fser := fsub (vZ K) (fconst p3).
Definition fq : fser := fadd (fadd (fmul fr1 fr1) (fmul fr2 fr2)) (fmul fr3 fr3).
Definition fy : fser := fisqrt fq Y.
Definition fh3 : fser := fmul fy (fmul fy fy).
Definition fh5 : fser := fmul fh3 (fmul fy fy).
Definition fc1 : fser := fsub (fscal d2 fr3) (fscal d3 fr2).
Definition fc2 : fser := fsub (fscal d3 fr1) (fscal d1 fr3).
Definition fc3 : fser := fsub (fscal d1 fr2) (fscal d2 fr1).
Definition fb1 : fser := fmul fc1 fh3.
Definition fb2 : fser := fmul fc2 fh3.
Definition fb3 : fser := fmul fc3 fh3.

Definition fJ11 : fser := fscal (-3) (fmul (fmul fc1 fr1) fh5).
Definition fJ12 : fser := fsub (fscal (- d3) fh3) (fscal 3 (fmul (fmul fc1 fr2) fh5)).
Definition fJ13 : fser := fsub (fscal d2 fh3) (fscal 3 (fmul (fmul fc1 fr3) fh5)).
Definition fJ21 : fser := fsub (fscal d3 fh3) (fscal 3 (fmul (fmul fc2 fr1) fh5)).
Definition fJ22 : fser := fscal (-3) (fmul (fmul fc2 fr2) fh5).
Definition fJ23 : fser := fsub (fscal (- d1) fh3) (fscal 3 (fmul (fmul fc2 fr3) fh5)).
Definition fJ31 : fser := fsub (fscal (- d2) fh3) (fscal 3 (fmul (fmul fc3 fr1) fh5)).
Definition fJ32 : fser := fsub (fscal d1 fh3) (fscal 3 (fmul (fmul fc3 fr2) fh5)).
Definition fJ33 : fser := fscal (-3) (fmul (fmul fc3 fr3) fh5).

Definition fJeR1 : fser := fadd (fmul fJ11 cosf) (fmul fJ12 sinf).
Definition fJeR2 : fser := fadd (fmul fJ21 cosf) (fmul fJ22 sinf).
Definition fJeR3 : fser := fadd (fmul fJ31 cosf) (fmul fJ32 sinf).
Definition fJeP1 : fser := fadd (fmul (fscal (-1) fJ11) sinf) (fmul fJ12 cosf).
Definition fJeP2 : fser := fadd (fmul (fscal (-1) fJ21) sinf) (fmul fJ22 cosf).
Definition fJeP3 : fser := fadd (fmul (fscal (-1) fJ31) sinf) (fmul fJ32 cosf).

Definition FR : fser := fadd (fmul fb1 cosf) (fmul fb2 sinf).
Definition FP : fser := fadd (fmul (fscal (-1) fb1) sinf) (fmul fb2 cosf).
Definition FZ : fser := fb3.
Definition FR_R : fser := fadd (fmul fJeR1 cosf) (fmul fJeR2 sinf).
Definition FR_Z : fser := fadd (fmul fJ13 cosf) (fmul fJ23 sinf).
Definition FR_phi : fser := fadd (fmul (vR K) (fadd (fmul fJeP1 cosf) (fmul fJeP2 sinf))) FP.
Definition FP_R : fser := fadd (fmul (fscal (-1) fJeR1) sinf) (fmul fJeR2 cosf).
Definition FP_Z : fser := fadd (fmul (fscal (-1) fJ13) sinf) (fmul fJ23 cosf).
Definition FP_phi : fser := fsub (fmul (vR K) (fadd (fmul (fscal (-1) fJeP1) sinf) (fmul fJeP2 cosf))) FR.
Definition FZ_R : fser := fJeR3.
Definition FZ_Z : fser := fJ33.
Definition FZ_phi : fser := fmul (vR K) fJeP3.

(** The points of the torus in space. *)
Let KR (t p : R) : R := feval (vR K) t p.
Let KZ (t p : R) : R := feval (vZ K) t p.
Let X1 (t p : R) : R := kx1 (KR t p) p.
Let X2 (t p : R) : R := kx2 (KR t p) p.
Let X3 (t p : R) : R := KZ t p.

Variable rho : R.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis Hq : isq_ok rho fq Y.
Hypothesis Hy0 : 0 < feval fy 0 0.

Lemma Hr0 : 0 <= rho. Proof. lra. Qed.

Lemma E_KR : ev rho (vR K) KR. Proof. exact (ev_self rho (vR K) (proj1 FK)). Qed.
Lemma E_KZ : ev rho (vZ K) KZ. Proof. exact (ev_self rho (vZ K) (proj2 FK)). Qed.

Lemma E_r1 : ev rho fr1 (fun t p => X1 t p - p1).
Proof.
  apply (ev_ext _ _ (fun t p => KR t p * cos p - p1)); [intros; cbv beta; unfold X1, kx1; reflexivity |].
  apply (ev_fsub _ Hr0); [apply (ev_fmul _ Hr0); [exact E_KR | apply ev_cosf, Hr0] | apply ev_fconst].
Qed.
Lemma E_r2 : ev rho fr2 (fun t p => X2 t p - p2).
Proof.
  apply (ev_ext _ _ (fun t p => KR t p * sin p - p2)); [intros; cbv beta; unfold X2, kx2; reflexivity |].
  apply (ev_fsub _ Hr0); [apply (ev_fmul _ Hr0); [exact E_KR | apply ev_sinf, Hr0] | apply ev_fconst].
Qed.
Lemma E_r3 : ev rho fr3 (fun t p => X3 t p - p3).
Proof. apply (ev_fsub _ Hr0); [exact E_KZ | apply ev_fconst]. Qed.

Lemma E_q : ev rho fq (fun t p => qk sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => (X1 t p - p1) * (X1 t p - p1) + (X2 t p - p2) * (X2 t p - p2)
                                       + (X3 t p - p3) * (X3 t p - p3))); [intros; reflexivity |].
  apply (ev_fadd _ Hr0); [apply (ev_fadd _ Hr0) |]; apply (ev_fmul _ Hr0);
    first [exact E_r1 | exact E_r2 | exact E_r3].
Qed.

Lemma q_pos (t p : R) : 0 < qk sc (X1 t p) (X2 t p) (X3 t p).
Proof.
  pose proof (isq_sq rho fq Y Hq t p) as S. destruct E_q as [_ Eq]. rewrite Eq in S.
  assert (H : 0 <= qk sc (X1 t p) (X2 t p) (X3 t p)).
  { unfold qk. set (a := X1 t p - sp1 sc). set (b := X2 t p - sp2 sc). set (c := X3 t p - sp3 sc).
    pose proof (Rle_0_sqr a). pose proof (Rle_0_sqr b). pose proof (Rle_0_sqr c). unfold Rsqr in *. lra. }
  destruct (Rle_lt_or_eq_dec _ _ H) as [H1 | H1]; [exact H1 | rewrite <- H1 in S; lra].
Qed.

Lemma E_y : ev rho fy (fun t p => / sqrt (qk sc (X1 t p) (X2 t p) (X3 t p))).
Proof. exact (isq_ev rho fq Y Hq _ Hy0 E_q). Qed.

Lemma E_h3 : ev rho fh3 (fun t p => h3 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => / sqrt (qk sc (X1 t p) (X2 t p) (X3 t p))
                                     * (/ sqrt (qk sc (X1 t p) (X2 t p) (X3 t p))
                                        * / sqrt (qk sc (X1 t p) (X2 t p) (X3 t p))))).
  - intros t p. cbv beta. pose proof (q_pos t p) as Q. unfold h3.
    set (q := qk sc (X1 t p) (X2 t p) (X3 t p)) in *.
    assert (S : sqrt q * sqrt q = q) by (apply sqrt_sqrt; lra).
    assert (Sp : 0 < sqrt q) by (apply sqrt_lt_R0; lra).
    replace (q * sqrt q) with (sqrt q * sqrt q * sqrt q) by (rewrite S; reflexivity). field. lra.
  - apply (ev_fmul _ Hr0); [exact E_y | apply (ev_fmul _ Hr0); exact E_y].
Qed.

Lemma E_h5 : ev rho fh5 (fun t p => h5 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => h3 sc (X1 t p) (X2 t p) (X3 t p)
                                     * (/ sqrt (qk sc (X1 t p) (X2 t p) (X3 t p))
                                        * / sqrt (qk sc (X1 t p) (X2 t p) (X3 t p))))).
  - intros t p. cbv beta. pose proof (q_pos t p) as Q. unfold h3, h5.
    set (q := qk sc (X1 t p) (X2 t p) (X3 t p)) in *.
    assert (S : sqrt q * sqrt q = q) by (apply sqrt_sqrt; lra).
    assert (Sp : 0 < sqrt q) by (apply sqrt_lt_R0; lra).
    replace (q * q * sqrt q) with (q * (sqrt q * sqrt q) * sqrt q) by (rewrite S; reflexivity).
    field. lra.
  - apply (ev_fmul _ Hr0); [exact E_h3 | apply (ev_fmul _ Hr0); exact E_y].
Qed.

Lemma E_c1 : ev rho fc1 (fun t p => ck1 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => d2 * (X3 t p - p3) - d3 * (X2 t p - p2))); [intros; reflexivity |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0); [exact E_r3 | exact E_r2].
Qed.
Lemma E_c2 : ev rho fc2 (fun t p => ck2 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => d3 * (X1 t p - p1) - d1 * (X3 t p - p3))); [intros; reflexivity |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0); [exact E_r1 | exact E_r3].
Qed.
Lemma E_c3 : ev rho fc3 (fun t p => ck3 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => d1 * (X2 t p - p2) - d2 * (X1 t p - p1))); [intros; reflexivity |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0); [exact E_r2 | exact E_r1].
Qed.

Lemma E_b1 : ev rho fb1 (fun t p => bk1 sc (X1 t p) (X2 t p) (X3 t p)).
Proof. apply (ev_fmul _ Hr0); [exact E_c1 | exact E_h3]. Qed.
Lemma E_b2 : ev rho fb2 (fun t p => bk2 sc (X1 t p) (X2 t p) (X3 t p)).
Proof. apply (ev_fmul _ Hr0); [exact E_c2 | exact E_h3]. Qed.
Lemma E_b3 : ev rho fb3 (fun t p => bk3 sc (X1 t p) (X2 t p) (X3 t p)).
Proof. apply (ev_fmul _ Hr0); [exact E_c3 | exact E_h3]. Qed.

Ltac evJ E1 E2 :=
  intros; cbv beta; unfold J11, J12, J13, J21, J22, J23, J31, J32, J33; fold p1 p2 p3 d1 d2 d3; ring.

Lemma E_J11 : ev rho fJ11 (fun t p => J11 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -3 * (ck1 sc (X1 t p) (X2 t p) (X3 t p) * (X1 t p - p1)
                                          * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fscal _ Hr0), (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c1 | exact E_r1] | exact E_h5].
Qed.
Lemma E_J12 : ev rho fJ12 (fun t p => J12 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => - d3 * h3 sc (X1 t p) (X2 t p) (X3 t p)
     - 3 * (ck1 sc (X1 t p) (X2 t p) (X3 t p) * (X2 t p - p2) * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0);
    [exact E_h3 | apply (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c1 | exact E_r2] | exact E_h5]].
Qed.
Lemma E_J13 : ev rho fJ13 (fun t p => J13 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => d2 * h3 sc (X1 t p) (X2 t p) (X3 t p)
     - 3 * (ck1 sc (X1 t p) (X2 t p) (X3 t p) * (X3 t p - p3) * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0);
    [exact E_h3 | apply (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c1 | exact E_r3] | exact E_h5]].
Qed.
Lemma E_J21 : ev rho fJ21 (fun t p => J21 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => d3 * h3 sc (X1 t p) (X2 t p) (X3 t p)
     - 3 * (ck2 sc (X1 t p) (X2 t p) (X3 t p) * (X1 t p - p1) * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0);
    [exact E_h3 | apply (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c2 | exact E_r1] | exact E_h5]].
Qed.
Lemma E_J22 : ev rho fJ22 (fun t p => J22 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -3 * (ck2 sc (X1 t p) (X2 t p) (X3 t p) * (X2 t p - p2)
                                          * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fscal _ Hr0), (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c2 | exact E_r2] | exact E_h5].
Qed.
Lemma E_J23 : ev rho fJ23 (fun t p => J23 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => - d1 * h3 sc (X1 t p) (X2 t p) (X3 t p)
     - 3 * (ck2 sc (X1 t p) (X2 t p) (X3 t p) * (X3 t p - p3) * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0);
    [exact E_h3 | apply (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c2 | exact E_r3] | exact E_h5]].
Qed.
Lemma E_J31 : ev rho fJ31 (fun t p => J31 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => - d2 * h3 sc (X1 t p) (X2 t p) (X3 t p)
     - 3 * (ck3 sc (X1 t p) (X2 t p) (X3 t p) * (X1 t p - p1) * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0);
    [exact E_h3 | apply (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c3 | exact E_r1] | exact E_h5]].
Qed.
Lemma E_J32 : ev rho fJ32 (fun t p => J32 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => d1 * h3 sc (X1 t p) (X2 t p) (X3 t p)
     - 3 * (ck3 sc (X1 t p) (X2 t p) (X3 t p) * (X2 t p - p2) * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fsub _ Hr0); apply (ev_fscal _ Hr0);
    [exact E_h3 | apply (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c3 | exact E_r2] | exact E_h5]].
Qed.
Lemma E_J33 : ev rho fJ33 (fun t p => J33 sc (X1 t p) (X2 t p) (X3 t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -3 * (ck3 sc (X1 t p) (X2 t p) (X3 t p) * (X3 t p - p3)
                                          * h5 sc (X1 t p) (X2 t p) (X3 t p)))); [evJ 0 0 |].
  apply (ev_fscal _ Hr0), (ev_fmul _ Hr0); [apply (ev_fmul _ Hr0); [exact E_c3 | exact E_r3] | exact E_h5].
Qed.

Lemma E_cos : ev rho cosf (fun _ p => cos p). Proof. apply ev_cosf, Hr0. Qed.
Lemma E_sin : ev rho sinf (fun _ p => sin p). Proof. apply ev_sinf, Hr0. Qed.

Lemma E_FR : ev rho FR (fun t p => fR sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_b1 | exact E_b2 | exact E_cos | exact E_sin].
Qed.
Lemma E_FP : ev rho FP (fun t p => fP sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -1 * bk1 sc (X1 t p) (X2 t p) (X3 t p) * sin p
                                     + bk2 sc (X1 t p) (X2 t p) (X3 t p) * cos p));
    [intros; cbv beta; unfold fP; fold (X1 t p) (X2 t p); change (X3 t p) with (KZ t p); ring |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_b1 | exact E_b2 | exact E_cos | exact E_sin].
Qed.
Lemma E_FZ : ev rho FZ (fun t p => fZ sc (KR t p) p (KZ t p)).
Proof. exact E_b3. Qed.

Lemma E_JeR1 : ev rho fJeR1 (fun t p => JeR1 sc (KR t p) p (KZ t p)).
Proof. apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_J11 | exact E_J12 | exact E_cos | exact E_sin]. Qed.
Lemma E_JeR2 : ev rho fJeR2 (fun t p => JeR2 sc (KR t p) p (KZ t p)).
Proof. apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_J21 | exact E_J22 | exact E_cos | exact E_sin]. Qed.
Lemma E_JeR3 : ev rho fJeR3 (fun t p => JeR3 sc (KR t p) p (KZ t p)).
Proof. apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_J31 | exact E_J32 | exact E_cos | exact E_sin]. Qed.
Lemma E_JeP1 : ev rho fJeP1 (fun t p => JeP1 sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -1 * J11 sc (X1 t p) (X2 t p) (X3 t p) * sin p
                                     + J12 sc (X1 t p) (X2 t p) (X3 t p) * cos p));
    [intros; cbv beta; unfold JeP1; fold (X1 t p) (X2 t p); change (X3 t p) with (KZ t p); ring |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_J11 | exact E_J12 | exact E_cos | exact E_sin].
Qed.
Lemma E_JeP2 : ev rho fJeP2 (fun t p => JeP2 sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -1 * J21 sc (X1 t p) (X2 t p) (X3 t p) * sin p
                                     + J22 sc (X1 t p) (X2 t p) (X3 t p) * cos p));
    [intros; cbv beta; unfold JeP2; fold (X1 t p) (X2 t p); change (X3 t p) with (KZ t p); ring |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_J21 | exact E_J22 | exact E_cos | exact E_sin].
Qed.
Lemma E_JeP3 : ev rho fJeP3 (fun t p => JeP3 sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -1 * J31 sc (X1 t p) (X2 t p) (X3 t p) * sin p
                                     + J32 sc (X1 t p) (X2 t p) (X3 t p) * cos p));
    [intros; cbv beta; unfold JeP3; fold (X1 t p) (X2 t p); change (X3 t p) with (KZ t p); ring |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_J31 | exact E_J32 | exact E_cos | exact E_sin].
Qed.

Lemma E_FR_R : ev rho FR_R (fun t p => fR_R sc (KR t p) p (KZ t p)).
Proof. apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_JeR1 | exact E_JeR2 | exact E_cos | exact E_sin]. Qed.
Lemma E_FR_Z : ev rho FR_Z (fun t p => fR_Z sc (KR t p) p (KZ t p)).
Proof. apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_J13 | exact E_J23 | exact E_cos | exact E_sin]. Qed.
Lemma E_FR_phi : ev rho FR_phi (fun t p => fR_phi sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_fadd _ Hr0); [| exact E_FP].
  apply (ev_fmul _ Hr0); [exact E_KR |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0); first [exact E_JeP1 | exact E_JeP2 | exact E_cos | exact E_sin].
Qed.
Lemma E_FP_R : ev rho FP_R (fun t p => fP_R sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -1 * JeR1 sc (KR t p) p (KZ t p) * sin p + JeR2 sc (KR t p) p (KZ t p) * cos p));
    [intros; cbv beta; unfold fP_R; ring |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_JeR1 | exact E_JeR2 | exact E_cos | exact E_sin].
Qed.
Lemma E_FP_Z : ev rho FP_Z (fun t p => fP_Z sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => -1 * J13 sc (X1 t p) (X2 t p) (X3 t p) * sin p
                                     + J23 sc (X1 t p) (X2 t p) (X3 t p) * cos p));
    [intros; cbv beta; unfold fP_Z; fold (X1 t p) (X2 t p); change (X3 t p) with (KZ t p); ring |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_J13 | exact E_J23 | exact E_cos | exact E_sin].
Qed.
Lemma E_FP_phi : ev rho FP_phi (fun t p => fP_phi sc (KR t p) p (KZ t p)).
Proof.
  apply (ev_ext _ _ (fun t p => KR t p * (-1 * JeP1 sc (KR t p) p (KZ t p) * sin p
                                               + JeP2 sc (KR t p) p (KZ t p) * cos p) - fR sc (KR t p) p (KZ t p)));
    [intros; cbv beta; unfold fP_phi; ring |].
  apply (ev_fsub _ Hr0); [| exact E_FR].
  apply (ev_fmul _ Hr0); [exact E_KR |].
  apply (ev_fadd _ Hr0); apply (ev_fmul _ Hr0);
    first [apply (ev_fscal _ Hr0), E_JeP1 | exact E_JeP2 | exact E_cos | exact E_sin].
Qed.
Lemma E_FZ_R : ev rho FZ_R (fun t p => fZ_R sc (KR t p) p (KZ t p)).
Proof. exact E_JeR3. Qed.
Lemma E_FZ_Z : ev rho FZ_Z (fun t p => fZ_Z sc (KR t p) p (KZ t p)).
Proof. exact E_J33. Qed.
Lemma E_FZ_phi : ev rho FZ_phi (fun t p => fZ_phi sc (KR t p) p (KZ t p)).
Proof. apply (ev_fmul _ Hr0); [exact E_KR | exact E_JeP3]. Qed.

(** * The chain rule in each angle *)

Lemma d_id (x : R) : is_derive (fun y : R => y) x 1.
Proof. auto_derive; [exact I | reflexivity]. Qed.

Lemma deriv_uniq (f : R -> R) (x l1 l2 : R) : is_derive f x l1 -> is_derive f x l2 -> l1 = l2.
Proof. intros H1 H2. rewrite <- (is_derive_unique f x l1 H1). exact (is_derive_unique f x l2 H2). Qed.

Lemma deriv_t (F : fser) (f : R -> R -> R) (t p : R) :
  ev rho F f -> is_derive (fun y => f y p) t (feval (dt F) t p).
Proof.
  intros [[M HM] EF]. pose proof (feval_dt rho M F p t Hr HM) as D.
  apply (is_derive_ext (fun y => feval F y p)); [intros y; apply EF | exact D].
Qed.

Lemma deriv_p (F : fser) (f : R -> R -> R) (t p : R) :
  ev rho F f -> is_derive (fun y => f t y) p (feval (dp F) t p).
Proof.
  intros [[M HM] EF]. pose proof (feval_dp rho M F t p Hr HM) as D.
  apply (is_derive_ext (fun y => feval F t y)); [intros y; apply EF | exact D].
Qed.

Lemma DR_t (t p : R) : is_derive (fun y => KR y p) t (feval (dt (vR K)) t p).
Proof. exact (deriv_t (vR K) KR t p E_KR). Qed.
Lemma DZ_t (t p : R) : is_derive (fun y => KZ y p) t (feval (dt (vZ K)) t p).
Proof. exact (deriv_t (vZ K) KZ t p E_KZ). Qed.
Lemma DR_p (t p : R) : is_derive (fun y => KR t y) p (feval (dp (vR K)) t p).
Proof. exact (deriv_p (vR K) KR t p E_KR). Qed.
Lemma DZ_p (t p : R) : is_derive (fun y => KZ t y) p (feval (dp (vZ K)) t p).
Proof. exact (deriv_p (vZ K) KZ t p E_KZ). Qed.

Theorem dt_chain_R (t p : R) :
  feval (dt FR) t p = feval FR_R t p * feval (dt (vR K)) t p + feval FR_Z t p * feval (dt (vZ K)) t p.
Proof.
  pose proof (deriv_t FR _ t p E_FR) as D.
  pose proof (cyl_chain_R sc (fun y => KR y p) (fun _ => p) (fun y => KZ y p) t _ 0 _
                (DR_t t p) (d_const p t) (DZ_t t p) (q_pos t p)) as C.
  rewrite (deriv_uniq _ _ _ _ D C).
  rewrite (proj2 E_FR_R), (proj2 E_FR_Z). ring.
Qed.

Theorem dt_chain_P (t p : R) :
  feval (dt FP) t p = feval FP_R t p * feval (dt (vR K)) t p + feval FP_Z t p * feval (dt (vZ K)) t p.
Proof.
  pose proof (deriv_t FP _ t p E_FP) as D.
  pose proof (cyl_chain_P sc (fun y => KR y p) (fun _ => p) (fun y => KZ y p) t _ 0 _
                (DR_t t p) (d_const p t) (DZ_t t p) (q_pos t p)) as C.
  rewrite (deriv_uniq _ _ _ _ D C).
  rewrite (proj2 E_FP_R), (proj2 E_FP_Z). ring.
Qed.

Theorem dt_chain_Z (t p : R) :
  feval (dt FZ) t p = feval FZ_R t p * feval (dt (vR K)) t p + feval FZ_Z t p * feval (dt (vZ K)) t p.
Proof.
  pose proof (deriv_t FZ _ t p E_FZ) as D.
  pose proof (cyl_chain_Z sc (fun y => KR y p) (fun _ => p) (fun y => KZ y p) t _ 0 _
                (DR_t t p) (d_const p t) (DZ_t t p) (q_pos t p)) as C.
  rewrite (deriv_uniq _ _ _ _ D C).
  rewrite (proj2 E_FZ_R), (proj2 E_FZ_Z). ring.
Qed.

Theorem dp_chain_R (t p : R) :
  feval (dp FR) t p = feval FR_R t p * feval (dp (vR K)) t p + feval FR_Z t p * feval (dp (vZ K)) t p
                      + feval FR_phi t p.
Proof.
  pose proof (deriv_p FR _ t p E_FR) as D.
  pose proof (cyl_chain_R sc (fun y => KR t y) (fun y => y) (fun y => KZ t y) p _ 1 _
                (DR_p t p) (d_id p) (DZ_p t p) (q_pos t p)) as C.
  rewrite (deriv_uniq _ _ _ _ D C).
  rewrite (proj2 E_FR_R), (proj2 E_FR_Z), (proj2 E_FR_phi). ring.
Qed.

Theorem dp_chain_P (t p : R) :
  feval (dp FP) t p = feval FP_R t p * feval (dp (vR K)) t p + feval FP_Z t p * feval (dp (vZ K)) t p
                      + feval FP_phi t p.
Proof.
  pose proof (deriv_p FP _ t p E_FP) as D.
  pose proof (cyl_chain_P sc (fun y => KR t y) (fun y => y) (fun y => KZ t y) p _ 1 _
                (DR_p t p) (d_id p) (DZ_p t p) (q_pos t p)) as C.
  rewrite (deriv_uniq _ _ _ _ D C).
  rewrite (proj2 E_FP_R), (proj2 E_FP_Z), (proj2 E_FP_phi). ring.
Qed.

Theorem dp_chain_Z (t p : R) :
  feval (dp FZ) t p = feval FZ_R t p * feval (dp (vR K)) t p + feval FZ_Z t p * feval (dp (vZ K)) t p
                      + feval FZ_phi t p.
Proof.
  pose proof (deriv_p FZ _ t p E_FZ) as D.
  pose proof (cyl_chain_Z sc (fun y => KR t y) (fun y => y) (fun y => KZ t y) p _ 1 _
                (DR_p t p) (d_id p) (DZ_p t p) (q_pos t p)) as C.
  rewrite (deriv_uniq _ _ _ _ D C).
  rewrite (proj2 E_FZ_R), (proj2 E_FZ_Z), (proj2 E_FZ_phi). ring.
Qed.

(** The field of one source has no divergence, in these families. *)
Theorem fam_liouville (t p : R) :
  feval FP_phi t p + feval FR t p + feval (vR K) t p * (feval FR_R t p + feval FZ_Z t p) = 0.
Proof.
  rewrite (proj2 E_FP_phi), (proj2 E_FR), (proj2 E_FR_R), (proj2 E_FZ_Z).
  exact (src_liouville sc (KR t p) p (KZ t p)).
Qed.

End SourceFam.
