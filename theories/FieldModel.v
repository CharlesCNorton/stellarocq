(** The model of the symmetric coil field along tori, and its identities.

    A jet carries the three cylindrical components of a field along a torus K
    with their derivatives in R and Z and their explicit derivatives in phi
    ([cjet]). [jchain K J] says that the components satisfy the chain rule in
    each angle along K and that the field has no divergence there. The jet of
    one source satisfies it ([srcjet_chain]); so does the sum of a jet with
    its reflection, the field of the source and of its stellarator image,
    along a stellarator-symmetric torus ([symjet_chain]); so do sums
    ([jadd_chain]) and P times the projection onto one field period, the
    field of the P rotated images, along a torus of that period
    ([jproj_chain]). The field of all the images of the base sources is the
    jet [tot]. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer Hypotheses Invariance CoilSym
  FieldKern FieldFam.
Import ListNotations.
Local Open Scope R_scope.

(** * Evaluation under the reflection and the shifts of a period *)

Lemma feval_even_refl (u : fser) (t p : R) : is_even u -> feval u (- t) (- p) = feval u t p.
Proof.
  intros H. rewrite <- feval_frefl. apply feval_feq. intros m n. simpl. rewrite H. split; ring.
Qed.

Lemma feval_odd_refl (u : fser) (t p : R) : fin 0 u -> is_odd u -> feval u (- t) (- p) = - feval u t p.
Proof.
  intros F H. rewrite <- feval_frefl.
  rewrite (feval_feq _ (fscal (-1) u)); [rewrite (feval_fscal' t p _ _ F); ring |].
  intros m n. simpl. rewrite H. split; ring.
Qed.

Lemma feval_per_shift (P : Z) (u : fser) (t p : R) (k : nat) :
  (0 < P)%Z -> is_per P u -> feval u t (p + INR k * (2 * PI / IZR P)) = feval u t p.
Proof.
  intros HP H. rewrite <- feval_fshift. apply feval_feq. intros m n. simpl.
  destruct (Classical_Prop.classic (off P n)) as [Ho | Hon].
  - destruct (H m n Ho) as [A B]. rewrite A, B. split; ring.
  - assert (Hd : (P | n)%Z).
    { apply Z.mod_divide; [lia |]. unfold off in Hon.
      destruct (Z.eq_dec (n mod P) 0) as [E | E]; [exact E | contradiction]. }
    destruct Hd as [j Hj].
    assert (HPR : 0 < IZR P) by (apply IZR_lt; exact HP).
    assert (E : IZR n * (INR k * (2 * PI / IZR P)) = 0 + IZR (Z.of_nat k * j) * (2 * PI)).
    { rewrite Hj, mult_IZR, mult_IZR, <- INR_IZR_INZ. field. lra. }
    rewrite E, cos_zperiod, sin_zperiod, cos_0, sin_0. split; ring.
Qed.

Lemma fin_dt0 (rho : R) (u : fser) : 0 < rho -> fin rho u -> fin 0 (dt u).
Proof. intros Hr F. replace 0 with (rho - rho) by ring. apply fin_dt; assumption. Qed.

Lemma fin_dp0 (rho : R) (u : fser) : 0 < rho -> fin rho u -> fin 0 (dp u).
Proof.
  intros Hr [M HM]. exists (/ kappa * (/ (exp 1 * rho) * M)).
  replace 0 with (rho - rho) by ring. apply nbound_dp; assumption.
Qed.

(** * Jets *)

Record cjet := mkjet {
  jR : fser ; jP : fser ; jZ : fser ;
  jR_R : fser ; jR_Z : fser ; jR_phi : fser ;
  jP_R : fser ; jP_Z : fser ; jP_phi : fser ;
  jZ_R : fser ; jZ_Z : fser ; jZ_phi : fser }.

Definition jfin (rho : R) (J : cjet) : Prop :=
  fin rho (jR J) /\ fin rho (jP J) /\ fin rho (jZ J) /\
  fin rho (jR_R J) /\ fin rho (jR_Z J) /\ fin rho (jR_phi J) /\
  fin rho (jP_R J) /\ fin rho (jP_Z J) /\ fin rho (jP_phi J) /\
  fin rho (jZ_R J) /\ fin rho (jZ_Z J) /\ fin rho (jZ_phi J).

Section Chain.

Variable K : vf.
Let E (u : fser) (t p : R) : R := feval u t p.
Let tR (t p : R) : R := feval (dt (vR K)) t p.
Let tZ (t p : R) : R := feval (dt (vZ K)) t p.
Let pR (t p : R) : R := feval (dp (vR K)) t p.
Let pZ (t p : R) : R := feval (dp (vZ K)) t p.

Definition jchain (J : cjet) : Prop :=
  forall t p,
  feval (dt (jR J)) t p = feval (jR_R J) t p * tR t p + feval (jR_Z J) t p * tZ t p /\
  feval (dt (jP J)) t p = feval (jP_R J) t p * tR t p + feval (jP_Z J) t p * tZ t p /\
  feval (dt (jZ J)) t p = feval (jZ_R J) t p * tR t p + feval (jZ_Z J) t p * tZ t p /\
  feval (dp (jR J)) t p = feval (jR_R J) t p * pR t p + feval (jR_Z J) t p * pZ t p + feval (jR_phi J) t p /\
  feval (dp (jP J)) t p = feval (jP_R J) t p * pR t p + feval (jP_Z J) t p * pZ t p + feval (jP_phi J) t p /\
  feval (dp (jZ J)) t p = feval (jZ_R J) t p * pR t p + feval (jZ_Z J) t p * pZ t p + feval (jZ_phi J) t p /\
  feval (jP_phi J) t p + feval (jR J) t p + feval (vR K) t p * (feval (jR_R J) t p + feval (jZ_Z J) t p) = 0.

End Chain.

(** * The jet of one source *)

Definition srcjet (sc : src) (Y : fser) (K : vf) : cjet :=
  mkjet (FR sc Y K) (FP sc Y K) (FZ sc Y K)
        (FR_R sc Y K) (FR_Z sc Y K) (FR_phi sc Y K)
        (FP_R sc Y K) (FP_Z sc Y K) (FP_phi sc Y K)
        (FZ_R sc Y K) (FZ_Z sc Y K) (FZ_phi sc Y K).

Section Src.

Variables (sc : src) (Y : fser) (K : vf) (rho : R).
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis Hq : isq_ok rho (fq sc K) Y.
Hypothesis Hy0 : 0 < feval (fy sc Y K) 0 0.

Theorem srcjet_fin : jfin rho (srcjet sc Y K).
Proof.
  unfold jfin, srcjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  repeat split.
  - exact (proj1 (E_FR sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FP sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FZ sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FR_R sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FR_Z sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FR_phi sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FP_R sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FP_Z sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FP_phi sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FZ_R sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FZ_Z sc Y K rho Hr FK Hq Hy0)).
  - exact (proj1 (E_FZ_phi sc Y K rho Hr FK Hq Hy0)).
Qed.

Theorem srcjet_chain : jchain K (srcjet sc Y K).
Proof.
  intros t p. unfold srcjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - exact (dt_chain_R sc Y K rho Hr FK Hq Hy0 t p).
  - exact (dt_chain_P sc Y K rho Hr FK Hq Hy0 t p).
  - exact (dt_chain_Z sc Y K rho Hr FK Hq Hy0 t p).
  - exact (dp_chain_R sc Y K rho Hr FK Hq Hy0 t p).
  - exact (dp_chain_P sc Y K rho Hr FK Hq Hy0 t p).
  - exact (dp_chain_Z sc Y K rho Hr FK Hq Hy0 t p).
  - exact (fam_liouville sc Y K rho Hr FK Hq Hy0 t p).
Qed.

End Src.

(** * The source and its stellarator image *)

Definition symjet (J : cjet) : cjet :=
  mkjet (fsub (jR J) (frefl (jR J))) (fadd (jP J) (frefl (jP J))) (fadd (jZ J) (frefl (jZ J)))
        (fsub (jR_R J) (frefl (jR_R J))) (fadd (jR_Z J) (frefl (jR_Z J))) (fadd (jR_phi J) (frefl (jR_phi J)))
        (fadd (jP_R J) (frefl (jP_R J))) (fsub (jP_Z J) (frefl (jP_Z J))) (fsub (jP_phi J) (frefl (jP_phi J)))
        (fadd (jZ_R J) (frefl (jZ_R J))) (fsub (jZ_Z J) (frefl (jZ_Z J))) (fsub (jZ_phi J) (frefl (jZ_phi J))).

Section Sym.

Variable rho : R.
Hypothesis Hr : 0 < rho.

Lemma fin_frefl (r : R) (u : fser) : fin r u -> fin r (frefl u).
Proof. intros [M H]. exists M. apply nbound_frefl, H. Qed.

Lemma E_sub (u : fser) (t p : R) : fin 0 u ->
  feval (fsub u (frefl u)) t p = feval u t p - feval u (- t) (- p).
Proof. intros F. rewrite (feval_fsub' t p _ _ F (fin_frefl _ _ F)), feval_frefl. reflexivity. Qed.

Lemma E_add (u : fser) (t p : R) : fin 0 u ->
  feval (fadd u (frefl u)) t p = feval u t p + feval u (- t) (- p).
Proof. intros F. rewrite (feval_fadd' t p _ _ F (fin_frefl _ _ F)), feval_frefl. reflexivity. Qed.

Lemma dt_fsub_feq (u v : fser) : feq (dt (fsub u v)) (fsub (dt u) (dt v)).
Proof. intros m n. simpl. split; ring. Qed.
Lemma dp_fsub_feq (u v : fser) : feq (dp (fsub u v)) (fsub (dp u) (dp v)).
Proof. intros m n. simpl. split; ring. Qed.
Lemma dp_fadd_feq (u v : fser) : feq (dp (fadd u v)) (fadd (dp u) (dp v)).
Proof. intros m n. simpl. split; ring. Qed.

Lemma Et_sub (u : fser) (t p : R) : fin rho u ->
  feval (dt (fsub u (frefl u))) t p = feval (dt u) t p + feval (dt u) (- t) (- p).
Proof.
  intros F. pose proof (fin_dt0 rho u Hr F) as F0.
  rewrite (feval_feq _ _ t p (dt_fsub_feq _ _)).
  rewrite (feval_fsub' t p _ _ F0 (fin_dt0 rho _ Hr (fin_frefl _ _ F))).
  rewrite (feval_feq _ _ t p (dt_frefl u)).
  rewrite (feval_fscal' t p _ _ (fin_frefl _ _ F0)), feval_frefl. ring.
Qed.

Lemma Et_add (u : fser) (t p : R) : fin rho u ->
  feval (dt (fadd u (frefl u))) t p = feval (dt u) t p - feval (dt u) (- t) (- p).
Proof.
  intros F. pose proof (fin_dt0 rho u Hr F) as F0.
  rewrite (feval_feq _ _ t p (dt_fadd_feq _ _)).
  rewrite (feval_fadd' t p _ _ F0 (fin_dt0 rho _ Hr (fin_frefl _ _ F))).
  rewrite (feval_feq _ _ t p (dt_frefl u)).
  rewrite (feval_fscal' t p _ _ (fin_frefl _ _ F0)), feval_frefl. ring.
Qed.

Lemma Ep_sub (u : fser) (t p : R) : fin rho u ->
  feval (dp (fsub u (frefl u))) t p = feval (dp u) t p + feval (dp u) (- t) (- p).
Proof.
  intros F. pose proof (fin_dp0 rho u Hr F) as F0.
  rewrite (feval_feq _ _ t p (dp_fsub_feq _ _)).
  rewrite (feval_fsub' t p _ _ F0 (fin_dp0 rho _ Hr (fin_frefl _ _ F))).
  rewrite (feval_feq _ _ t p (dp_frefl u)).
  rewrite (feval_fscal' t p _ _ (fin_frefl _ _ F0)), feval_frefl. ring.
Qed.

Lemma Ep_add (u : fser) (t p : R) : fin rho u ->
  feval (dp (fadd u (frefl u))) t p = feval (dp u) t p - feval (dp u) (- t) (- p).
Proof.
  intros F. pose proof (fin_dp0 rho u Hr F) as F0.
  rewrite (feval_feq _ _ t p (dp_fadd_feq _ _)).
  rewrite (feval_fadd' t p _ _ F0 (fin_dp0 rho _ Hr (fin_frefl _ _ F))).
  rewrite (feval_feq _ _ t p (dp_frefl u)).
  rewrite (feval_fscal' t p _ _ (fin_frefl _ _ F0)), feval_frefl. ring.
Qed.

Variables (K : vf) (J : cjet).
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis FJ : jfin rho J.
Hypothesis CJ : jchain K J.

Lemma Kt_R (t p : R) : feval (dt (vR K)) (- t) (- p) = - feval (dt (vR K)) t p.
Proof. apply feval_odd_refl; [exact (fin_dt0 rho _ Hr (proj1 FK)) | apply dt_even, (proj1 SK)]. Qed.
Lemma Kt_Z (t p : R) : feval (dt (vZ K)) (- t) (- p) = feval (dt (vZ K)) t p.
Proof. apply feval_even_refl, dt_odd, (proj2 SK). Qed.
Lemma Kp_R (t p : R) : feval (dp (vR K)) (- t) (- p) = - feval (dp (vR K)) t p.
Proof. apply feval_odd_refl; [exact (fin_dp0 rho _ Hr (proj1 FK)) | apply dp_even, (proj1 SK)]. Qed.
Lemma Kp_Z (t p : R) : feval (dp (vZ K)) (- t) (- p) = feval (dp (vZ K)) t p.
Proof. apply feval_even_refl, dp_odd, (proj2 SK). Qed.
Lemma K_R (t p : R) : feval (vR K) (- t) (- p) = feval (vR K) t p.
Proof. apply feval_even_refl, (proj1 SK). Qed.

Lemma f0 (u : fser) : fin rho u -> fin 0 u.
Proof. apply fin_mono. lra. Qed.

Theorem symjet_fin : jfin rho (symjet J).
Proof.
  destruct FJ as [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 F12]]]]]]]]]]].
  unfold jfin, symjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  repeat split; first [apply fin_fsub | apply fin_fadd]; try apply fin_frefl; assumption.
Qed.

Theorem symjet_chain : jchain K (symjet J).
Proof.
  destruct FJ as [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 F12]]]]]]]]]]].
  intros t p. unfold symjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  destruct (CJ t p) as [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]].
  destruct (CJ (- t) (- p)) as [B1 [B2 [B3 [B4 [B5 [B6 B7]]]]]].
  pose proof (Kt_R t p) as T1. pose proof (Kt_Z t p) as T2.
  pose proof (Kp_R t p) as T3. pose proof (Kp_Z t p) as T4. pose proof (K_R t p) as T5.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite Et_sub, E_sub, E_add by (try exact F1; try exact (f0 _ F4); exact (f0 _ F5)).
    rewrite A1, B1, T1, T2. ring.
  - rewrite Et_add, E_add, E_sub by (try exact F2; try exact (f0 _ F7); exact (f0 _ F8)).
    rewrite A2, B2, T1, T2. ring.
  - rewrite Et_add, E_add, E_sub by (try exact F3; try exact (f0 _ F10); exact (f0 _ F11)).
    rewrite A3, B3, T1, T2. ring.
  - rewrite Ep_sub, E_sub, !E_add by (try exact F1; try exact (f0 _ F4); try exact (f0 _ F5); exact (f0 _ F6)).
    rewrite A4, B4, T3, T4. ring.
  - rewrite Ep_add, E_add, !E_sub by (try exact F2; try exact (f0 _ F7); try exact (f0 _ F8); exact (f0 _ F9)).
    rewrite A5, B5, T3, T4. ring.
  - rewrite Ep_add, E_add, !E_sub by (try exact F3; try exact (f0 _ F10); try exact (f0 _ F11); exact (f0 _ F12)).
    rewrite A6, B6, T3, T4. ring.
  - rewrite (E_sub _ t p (f0 _ F9)), (E_sub _ t p (f0 _ F1)), (E_sub _ t p (f0 _ F4)), (E_sub _ t p (f0 _ F11)).
    rewrite T5 in B7. lra.
Qed.

End Sym.

(** * Sums of jets *)

Definition jmap2 (f : fser -> fser -> fser) (J1 J2 : cjet) : cjet :=
  mkjet (f (jR J1) (jR J2)) (f (jP J1) (jP J2)) (f (jZ J1) (jZ J2))
        (f (jR_R J1) (jR_R J2)) (f (jR_Z J1) (jR_Z J2)) (f (jR_phi J1) (jR_phi J2))
        (f (jP_R J1) (jP_R J2)) (f (jP_Z J1) (jP_Z J2)) (f (jP_phi J1) (jP_phi J2))
        (f (jZ_R J1) (jZ_R J2)) (f (jZ_Z J1) (jZ_Z J2)) (f (jZ_phi J1) (jZ_phi J2)).

Definition jmap (f : fser -> fser) (J : cjet) : cjet :=
  mkjet (f (jR J)) (f (jP J)) (f (jZ J))
        (f (jR_R J)) (f (jR_Z J)) (f (jR_phi J))
        (f (jP_R J)) (f (jP_Z J)) (f (jP_phi J))
        (f (jZ_R J)) (f (jZ_Z J)) (f (jZ_phi J)).

Definition jadd (J1 J2 : cjet) : cjet := jmap2 fadd J1 J2.
Definition jzero : cjet := mkjet fzero fzero fzero fzero fzero fzero fzero fzero fzero fzero fzero fzero.

Lemma fin_fzero (r : R) : fin r fzero.
Proof. exists 0. apply nbound_fzero. Qed.

Section Add.

Variable rho : R.
Hypothesis Hr : 0 < rho.
Variable K : vf.

Lemma jzero_fin : jfin rho jzero.
Proof. unfold jfin, jzero. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi]. repeat split; apply fin_fzero. Qed.

Lemma feval_fzero' (t p : R) : feval fzero t p = 0.
Proof. unfold feval. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |]. intros m n. unfold term. simpl. ring. Qed.

Lemma dt_fzero (t p : R) : feval (dt fzero) t p = 0.
Proof. rewrite <- (feval_fzero' t p). apply feval_feq. intros m n. simpl. split; ring. Qed.
Lemma dp_fzero (t p : R) : feval (dp fzero) t p = 0.
Proof. rewrite <- (feval_fzero' t p). apply feval_feq. intros m n. simpl. split; ring. Qed.

Lemma jzero_chain : jchain K jzero.
Proof.
  intros t p. unfold jzero. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  rewrite !dt_fzero, !dp_fzero, !feval_fzero'. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); ring.
Qed.

Lemma jadd_fin (J1 J2 : cjet) : jfin rho J1 -> jfin rho J2 -> jfin rho (jadd J1 J2).
Proof.
  intros [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]]
         [B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 [B9 [B10 [B11 B12]]]]]]]]]]].
  unfold jfin, jadd, jmap2. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  repeat split; apply fin_fadd; assumption.
Qed.

Lemma Ed_add (u v : fser) (t p : R) : fin rho u -> fin rho v ->
  feval (dt (fadd u v)) t p = feval (dt u) t p + feval (dt v) t p /\
  feval (dp (fadd u v)) t p = feval (dp u) t p + feval (dp v) t p /\
  feval (fadd u v) t p = feval u t p + feval v t p.
Proof.
  intros Fu Fv. refine (conj _ (conj _ _)).
  - rewrite (feval_feq _ _ t p (dt_fadd_feq u v)).
    exact (feval_fadd' t p _ _ (fin_dt0 rho _ Hr Fu) (fin_dt0 rho _ Hr Fv)).
  - rewrite (feval_feq _ _ t p (dp_fadd_feq u v)).
    exact (feval_fadd' t p _ _ (fin_dp0 rho _ Hr Fu) (fin_dp0 rho _ Hr Fv)).
  - exact (feval_fadd' t p _ _ (fin_mono rho 0 _ ltac:(lra) Fu) (fin_mono rho 0 _ ltac:(lra) Fv)).
Qed.

Lemma jadd_chain (J1 J2 : cjet) :
  jfin rho J1 -> jfin rho J2 -> jchain K J1 -> jchain K J2 -> jchain K (jadd J1 J2).
Proof.
  intros [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]]
         [B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 [B9 [B10 [B11 B12]]]]]]]]]]] C1 C2 t p.
  destruct (C1 t p) as [X1 [X2 [X3 [X4 [X5 [X6 X7]]]]]].
  destruct (C2 t p) as [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 Y7]]]]]].
  unfold jadd, jmap2. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  destruct (Ed_add _ _ t p A1 B1) as [D1 [P1 E1]]. destruct (Ed_add _ _ t p A2 B2) as [D2 [P2 E2]].
  destruct (Ed_add _ _ t p A3 B3) as [D3 [P3 E3]].
  destruct (Ed_add _ _ t p A4 B4) as [_ [_ E4]]. destruct (Ed_add _ _ t p A5 B5) as [_ [_ E5]].
  destruct (Ed_add _ _ t p A6 B6) as [_ [_ E6]]. destruct (Ed_add _ _ t p A7 B7) as [_ [_ E7]].
  destruct (Ed_add _ _ t p A8 B8) as [_ [_ E8]]. destruct (Ed_add _ _ t p A9 B9) as [_ [_ E9]].
  destruct (Ed_add _ _ t p A10 B10) as [_ [_ E10]]. destruct (Ed_add _ _ t p A11 B11) as [_ [_ E11]].
  destruct (Ed_add _ _ t p A12 B12) as [_ [_ E12]].
  rewrite D1, D2, D3, P1, P2, P3, E1, E4, E5, E6, E7, E8, E9, E10, E11, E12.
  rewrite X1, X2, X3, X4, X5, X6, Y1, Y2, Y3, Y4, Y5, Y6.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); try ring. lra.
Qed.

End Add.

(** * The rotated images: P times the projection onto one period *)

Definition jproj (P : Z) (J : cjet) : cjet := jmap (fun u => fscal (IZR P) (fproj P u)) J.

Section Proj.

Variables (P : Z) (rho : R) (K : vf) (J : cjet).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis QK : vper P K.
Hypothesis FJ : jfin rho J.
Hypothesis CJ : jchain K J.

Let NP := Z.to_nat P.
Let sh (k : nat) (p : R) : R := p + INR k * (2 * PI / IZR P).

Lemma fin_proj (u : fser) : fin rho u -> fin rho (fscal (IZR P) (fproj P u)).
Proof. intros [M H]. apply fin_fscal. exists M. apply nbound_fproj, H. Qed.

Theorem jproj_fin : jfin rho (jproj P J).
Proof.
  destruct FJ as [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]].
  unfold jfin, jproj, jmap. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  repeat split; apply fin_proj; assumption.
Qed.

(** The value of a projected family, and of its derivatives. *)
Lemma Epr (u : fser) (t p : R) : fin 0 u ->
  feval (fscal (IZR P) (fproj P u)) t p = fsum (fun k => feval u t (sh k p)) NP.
Proof.
  intros [M H]. rewrite (feval_fscal' t p _ _ (ex_intro _ M (nbound_fproj P 0 M u H))).
  exact (feval_fproj P HP M u t p H).
Qed.

Lemma dt_fscal_feq (c : R) (u : fser) : feq (dt (fscal c u)) (fscal c (dt u)).
Proof. intros m n. simpl. split; ring. Qed.
Lemma dp_fscal_feq (c : R) (u : fser) : feq (dp (fscal c u)) (fscal c (dp u)).
Proof. intros m n. simpl. split; ring. Qed.

Lemma Etpr (u : fser) (t p : R) : fin rho u ->
  feval (dt (fscal (IZR P) (fproj P u))) t p = fsum (fun k => feval (dt u) t (sh k p)) NP.
Proof.
  intros F. pose proof (fin_dt0 rho u Hr F) as [M H].
  rewrite (feval_feq _ (fscal (IZR P) (fproj P (dt u))));
    [| intros m n; simpl; destruct (Z.eqb _ _); split; ring].
  rewrite (feval_fscal' t p _ _ (ex_intro _ M (nbound_fproj P 0 M _ H))).
  exact (feval_fproj P HP M (dt u) t p H).
Qed.

Lemma Eppr (u : fser) (t p : R) : fin rho u ->
  feval (dp (fscal (IZR P) (fproj P u))) t p = fsum (fun k => feval (dp u) t (sh k p)) NP.
Proof.
  intros F. pose proof (fin_dp0 rho u Hr F) as [M H].
  rewrite (feval_feq _ (fscal (IZR P) (fproj P (dp u))));
    [| intros m n; simpl; destruct (Z.eqb _ _); split; ring].
  rewrite (feval_fscal' t p _ _ (ex_intro _ M (nbound_fproj P 0 M _ H))).
  exact (feval_fproj P HP M (dp u) t p H).
Qed.

Lemma per_t (u : fser) (t p : R) (k : nat) : is_per P u -> feval u t (sh k p) = feval u t p.
Proof. intros H. apply feval_per_shift; assumption. Qed.

Lemma f0' (u : fser) : fin rho u -> fin 0 u.
Proof. apply fin_mono. lra. Qed.

Lemma fsum_lin2 (A B : nat -> R) (c d : R) (n : nat) :
  fsum (fun k => A k * c + B k * d) n = fsum A n * c + fsum B n * d.
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fsum_lin3 (A B C : nat -> R) (c d : R) (n : nat) :
  fsum (fun k => A k * c + B k * d + C k) n = fsum A n * c + fsum B n * d + fsum C n.
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fsum_liou (A B E F : nat -> R) (c : R) (n : nat) :
  fsum (fun k => A k + B k + c * (E k + F k)) n = fsum A n + fsum B n + c * (fsum E n + fsum F n).
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fsum_zero (A : nat -> R) (n : nat) : (forall k, A k = 0) -> fsum A n = 0.
Proof. intros H. induction n as [| n IH]; simpl; [ring | rewrite IH, H; ring]. Qed.

Theorem jproj_chain : jchain K (jproj P J).
Proof.
  destruct FJ as [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]].
  destruct QK as [QR QZ].
  intros t p. unfold jproj, jmap. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  assert (TR : forall k, feval (dt (vR K)) t (sh k p) = feval (dt (vR K)) t p) by (intros; apply per_t, dt_per, QR).
  assert (TZ : forall k, feval (dt (vZ K)) t (sh k p) = feval (dt (vZ K)) t p) by (intros; apply per_t, dt_per, QZ).
  assert (PR : forall k, feval (dp (vR K)) t (sh k p) = feval (dp (vR K)) t p) by (intros; apply per_t, dp_per, QR).
  assert (PZ : forall k, feval (dp (vZ K)) t (sh k p) = feval (dp (vZ K)) t p) by (intros; apply per_t, dp_per, QZ).
  assert (KR0 : forall k, feval (vR K) t (sh k p) = feval (vR K) t p) by (intros; apply per_t, QR).
  rewrite (Etpr _ t p A1), (Etpr _ t p A2), (Etpr _ t p A3), (Eppr _ t p A1), (Eppr _ t p A2), (Eppr _ t p A3).
  rewrite !(Epr _ t p (f0' _ A4)), !(Epr _ t p (f0' _ A5)), !(Epr _ t p (f0' _ A6)),
    !(Epr _ t p (f0' _ A7)), !(Epr _ t p (f0' _ A8)), !(Epr _ t p (f0' _ A9)),
    !(Epr _ t p (f0' _ A10)), !(Epr _ t p (f0' _ A11)), !(Epr _ t p (f0' _ A12)),
    !(Epr _ t p (f0' _ A1)).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite (fsum_ext _ (fun k => feval (jR_R J) t (sh k p) * feval (dt (vR K)) t p
                               + feval (jR_Z J) t (sh k p) * feval (dt (vZ K)) t p)); [apply fsum_lin2 |].
    intros k. destruct (CJ t (sh k p)) as [X _]. rewrite X, TR, TZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => feval (jP_R J) t (sh k p) * feval (dt (vR K)) t p
                               + feval (jP_Z J) t (sh k p) * feval (dt (vZ K)) t p)); [apply fsum_lin2 |].
    intros k. destruct (CJ t (sh k p)) as [_ [X _]]. rewrite X, TR, TZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => feval (jZ_R J) t (sh k p) * feval (dt (vR K)) t p
                               + feval (jZ_Z J) t (sh k p) * feval (dt (vZ K)) t p)); [apply fsum_lin2 |].
    intros k. destruct (CJ t (sh k p)) as [_ [_ [X _]]]. rewrite X, TR, TZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => feval (jR_R J) t (sh k p) * feval (dp (vR K)) t p
                               + feval (jR_Z J) t (sh k p) * feval (dp (vZ K)) t p
                               + feval (jR_phi J) t (sh k p))); [apply fsum_lin3 |].
    intros k. destruct (CJ t (sh k p)) as [_ [_ [_ [X _]]]]. rewrite X, PR, PZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => feval (jP_R J) t (sh k p) * feval (dp (vR K)) t p
                               + feval (jP_Z J) t (sh k p) * feval (dp (vZ K)) t p
                               + feval (jP_phi J) t (sh k p))); [apply fsum_lin3 |].
    intros k. destruct (CJ t (sh k p)) as [_ [_ [_ [_ [X _]]]]]. rewrite X, PR, PZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => feval (jZ_R J) t (sh k p) * feval (dp (vR K)) t p
                               + feval (jZ_Z J) t (sh k p) * feval (dp (vZ K)) t p
                               + feval (jZ_phi J) t (sh k p))); [apply fsum_lin3 |].
    intros k. destruct (CJ t (sh k p)) as [_ [_ [_ [_ [_ [X _]]]]]]. rewrite X, PR, PZ. reflexivity.
  - rewrite <- fsum_liou. apply fsum_zero. intros k.
    destruct (CJ t (sh k p)) as [_ [_ [_ [_ [_ [_ L]]]]]]. rewrite KR0 in L. exact L.
Qed.

End Proj.

(** * The field of all the images of the base sources *)

Definition srcjets (l : list (src * fser)) (K : vf) : cjet :=
  fold_right (fun sy acc => jadd (symjet (srcjet (fst sy) (snd sy) K)) acc) jzero l.

Definition tot (P : Z) (l : list (src * fser)) (K : vf) : cjet := jproj P (srcjets l K).

(** Each base source carries a seed from which its inverse square root
    converges along K, positive. *)
Definition srcs_ok (rho : R) (l : list (src * fser)) (K : vf) : Prop :=
  List.Forall (fun sy => isq_ok rho (fq (fst sy) K) (snd sy) /\ 0 < feval (fy (fst sy) (snd sy) K) 0 0) l.

Lemma srcjets_fin (rho : R) (K : vf) (l : list (src * fser)) :
  0 < rho -> vfin rho K -> srcs_ok rho l K -> jfin rho (srcjets l K).
Proof.
  intros Hr FK Hl. induction Hl as [| sy l' [Hq Hy] _ IH]; simpl; [apply jzero_fin |].
  apply jadd_fin; [apply symjet_fin, (srcjet_fin _ _ _ rho Hr FK Hq Hy) | exact IH].
Qed.

Lemma srcjets_chain (rho : R) (K : vf) (l : list (src * fser)) :
  0 < rho -> vfin rho K -> vsym K -> srcs_ok rho l K -> jchain K (srcjets l K).
Proof.
  intros Hr FK SK Hl. induction Hl as [| sy l' [Hq Hy] Hl' IH]; simpl; [apply jzero_chain |].
  apply (jadd_chain rho Hr).
  - apply symjet_fin, (srcjet_fin _ _ _ rho Hr FK Hq Hy).
  - exact (srcjets_fin rho K l' Hr FK Hl').
  - apply (symjet_chain rho Hr K _ FK SK); [apply (srcjet_fin _ _ _ rho Hr FK Hq Hy) |].
    exact (srcjet_chain _ _ _ rho Hr FK Hq Hy).
  - exact IH.
Qed.

Theorem tot_fin (P : Z) (rho : R) (K : vf) (l : list (src * fser)) :
  0 < rho -> vfin rho K -> srcs_ok rho l K -> jfin rho (tot P l K).
Proof. intros Hr FK Hl. apply jproj_fin, srcjets_fin; assumption. Qed.

Theorem tot_chain (P : Z) (rho : R) (K : vf) (l : list (src * fser)) :
  (0 < P)%Z -> 0 < rho -> vfin rho K -> vsym K -> vper P K -> srcs_ok rho l K -> jchain K (tot P l K).
Proof.
  intros HP Hr FK SK QK Hl. apply (jproj_chain P rho K _ HP Hr QK).
  - apply srcjets_fin; assumption.
  - apply (srcjets_chain rho); assumption.
Qed.

(** * The value of the total field *)

Definition spt (sc : src) : vec3 := (sp1 sc, sp2 sc, sp3 sc).
Definition sdt (sc : src) : vec3 := (sd1 sc, sd2 sc, sd3 sc).
Definition srcs3 (l : list (src * fser)) : list (vec3 * vec3) :=
  map (fun sy => (spt (fst sy), sdt (fst sy))) l.

Lemma fR_kern (sc : src) (R0 phi Z0 : R) :
  fR sc R0 phi Z0 = cylR phi (kern (spt sc) (sdt sc) (cyl R0 phi Z0)).
Proof. unfold cyl, spt, sdt. rewrite bk_kern. unfold fR, cylR, kx1, kx2. reflexivity. Qed.
Lemma fP_kern (sc : src) (R0 phi Z0 : R) :
  fP sc R0 phi Z0 = cylP phi (kern (spt sc) (sdt sc) (cyl R0 phi Z0)).
Proof. unfold cyl, spt, sdt. rewrite bk_kern. unfold fP, cylP, kx1, kx2. reflexivity. Qed.
Lemma fZ_kern (sc : src) (R0 phi Z0 : R) :
  fZ sc R0 phi Z0 = cylZ (kern (spt sc) (sdt sc) (cyl R0 phi Z0)).
Proof. unfold cyl, spt, sdt. rewrite bk_kern. unfold fZ, cylZ, kx1, kx2. reflexivity. Qed.

(** One source with its stellarator image, along a stellarator-symmetric torus. *)
Lemma sym_val (sc : src) (Y : fser) (K : vf) (rho t p : R) :
  0 < rho -> vfin rho K -> vsym K -> isq_ok rho (fq sc K) Y -> 0 < feval (fy sc Y K) 0 0 ->
  feval (jR (symjet (srcjet sc Y K))) t p = srcR (spt sc) (sdt sc) (feval (vR K) t p) p (feval (vZ K) t p) /\
  feval (jP (symjet (srcjet sc Y K))) t p = srcP (spt sc) (sdt sc) (feval (vR K) t p) p (feval (vZ K) t p) /\
  feval (jZ (symjet (srcjet sc Y K))) t p = srcZ (spt sc) (sdt sc) (feval (vR K) t p) p (feval (vZ K) t p).
Proof.
  intros Hr FK SK Hq Hy.
  destruct (E_FR sc Y K rho Hr FK Hq Hy) as [F1 E1].
  destruct (E_FP sc Y K rho Hr FK Hq Hy) as [F2 E2].
  destruct (E_FZ sc Y K rho Hr FK Hq Hy) as [F3 E3].
  assert (KR : feval (vR K) (- t) (- p) = feval (vR K) t p) by (apply feval_even_refl, (proj1 SK)).
  assert (KZ : feval (vZ K) (- t) (- p) = - feval (vZ K) t p).
  { apply feval_odd_refl; [apply (fin_mono rho); [lra | exact (proj2 FK)] | exact (proj2 SK)]. }
  unfold symjet, srcjet. cbn [jR jP jZ].
  rewrite (E_sub _ t p (fin_mono rho 0 _ ltac:(lra) F1)), (E_add _ t p (fin_mono rho 0 _ ltac:(lra) F2)),
    (E_add _ t p (fin_mono rho 0 _ ltac:(lra) F3)).
  rewrite !E1, !E2, !E3. cbv beta. rewrite KR, KZ.
  unfold srcR, srcP, srcZ. rewrite !fR_kern, !fP_kern, !fZ_kern. auto.
Qed.

Definition lsum {A : Type} (f : A -> R) (l : list A) : R := fold_right Rplus 0 (map f l).

Lemma srcjets_val (rho : R) (K : vf) (l : list (src * fser)) (t p : R) :
  0 < rho -> vfin rho K -> vsym K -> srcs_ok rho l K ->
  feval (jR (srcjets l K)) t p
    = lsum (fun s => srcR (fst s) (snd s) (feval (vR K) t p) p (feval (vZ K) t p)) (srcs3 l) /\
  feval (jP (srcjets l K)) t p
    = lsum (fun s => srcP (fst s) (snd s) (feval (vR K) t p) p (feval (vZ K) t p)) (srcs3 l) /\
  feval (jZ (srcjets l K)) t p
    = lsum (fun s => srcZ (fst s) (snd s) (feval (vR K) t p) p (feval (vZ K) t p)) (srcs3 l).
Proof.
  intros Hr FK SK Hl. induction Hl as [| sy l' [Hq Hy] Hl' IH].
  - unfold srcjets, jzero, lsum. cbn [jR jP jZ map fold_right srcs3]. rewrite feval_fzero'. auto.
  - assert (Ej : srcjets (sy :: l') K = jadd (symjet (srcjet (fst sy) (snd sy) K)) (srcjets l' K))
      by reflexivity.
    assert (Es : forall f : vec3 * vec3 -> R,
               lsum f (srcs3 (sy :: l')) = f (spt (fst sy), sdt (fst sy)) + lsum f (srcs3 l'))
      by reflexivity.
    rewrite Ej, !Es. unfold jadd, jmap2. cbn [jR jP jZ fst snd].
    destruct (symjet_fin rho _ (srcjet_fin _ _ _ rho Hr FK Hq Hy)) as [A1 [A2 [A3 _]]].
    destruct (srcjets_fin rho K l' Hr FK Hl') as [B1 [B2 [B3 _]]].
    destruct (sym_val (fst sy) (snd sy) K rho t p Hr FK SK Hq Hy) as [S1 [S2 S3]].
    destruct IH as [I1 [I2 I3]].
    rewrite (feval_fadd' t p _ _ (fin_mono rho 0 _ ltac:(lra) A1) (fin_mono rho 0 _ ltac:(lra) B1)),
      (feval_fadd' t p _ _ (fin_mono rho 0 _ ltac:(lra) A2) (fin_mono rho 0 _ ltac:(lra) B2)),
      (feval_fadd' t p _ _ (fin_mono rho 0 _ ltac:(lra) A3) (fin_mono rho 0 _ ltac:(lra) B3)).
    rewrite S1, S2, S3, I1, I2, I3. auto.
Qed.

Lemma lsum_fsum {A : Type} (f : nat -> A -> R) (l : list A) (n : nat) :
  fsum (fun k => lsum (f k) l) n = lsum (fun a => fsum (fun k => f k a) n) l.
Proof.
  induction l as [| a l IH]; unfold lsum; simpl.
  - induction n as [| n IHn]; simpl; [reflexivity | rewrite IHn; ring].
  - unfold lsum in IH. rewrite <- IH. clear IH.
    induction n as [| n IHn]; simpl; [ring | rewrite IHn; ring].
Qed.

Lemma lsum_ext {A : Type} (f g : A -> R) (l : list A) : (forall a, f a = g a) -> lsum f l = lsum g l.
Proof. intros H. unfold lsum. f_equal. apply map_ext, H. Qed.

Lemma seq_fsum (f : nat -> R) (n : nat) : fold_right Rplus 0 (map f (seq 0 n)) = fsum f n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  rewrite seq_S, map_app, fold_right_app. simpl. rewrite <- IH.
  generalize (map f (seq 0 n)). intros l. rewrite Rplus_0_r.
  induction l as [| a l IHl]; simpl; [ring | rewrite IHl; ring].
Qed.

Lemma fold_map_cyl' {A : Type} (f : A -> vec3) (l : list A) (phi : R) :
  cylR phi (fold_right v3add v3zero (map f l)) = lsum (fun a => cylR phi (f a)) l /\
  cylP phi (fold_right v3add v3zero (map f l)) = lsum (fun a => cylP phi (f a)) l /\
  cylZ (fold_right v3add v3zero (map f l)) = lsum (fun a => cylZ (f a)) l.
Proof.
  unfold lsum. induction l as [| a l [IR [IP IZ]]]; simpl.
  - apply cyl_zero.
  - rewrite cylR_add, cylP_add, cylZ_add, IR, IP, IZ. auto.
Qed.

Section TotVal.

Variables (P : Z) (rho : R) (K : vf) (l : list (src * fser)).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.

(** The field of the coil set of P periods with the base sources of l. *)
Definition coilB : vec3 -> vec3 := symfield (Z.to_nat P) (srcs3 l).

Lemma theta_sh (k : nat) (p : R) : p + theta (Z.to_nat P) k = p + INR k * (2 * PI / IZR P).
Proof. unfold theta. rewrite (INR_IZR_INZ (Z.to_nat P)), Z2Nat.id by lia. reflexivity. Qed.

Theorem tot_val (t p : R) :
  feval (jR (tot P l K)) t p = B_R coilB (feval (vR K) t p) p (feval (vZ K) t p) /\
  feval (jP (tot P l K)) t p = B_phi coilB (feval (vR K) t p) p (feval (vZ K) t p) /\
  feval (jZ (tot P l K)) t p = B_Z coilB (feval (vR K) t p) p (feval (vZ K) t p).
Proof.
  destruct (srcjets_fin rho K l Hr FK Hl) as [A1 [A2 [A3 _]]].
  destruct QK as [QR QZ].
  assert (KR : forall k, feval (vR K) t (p + INR k * (2 * PI / IZR P)) = feval (vR K) t p)
    by (intros; apply feval_per_shift; assumption).
  assert (KZ : forall k, feval (vZ K) t (p + INR k * (2 * PI / IZR P)) = feval (vZ K) t p)
    by (intros; apply feval_per_shift; assumption).
  unfold tot, jproj, jmap. cbn [jR jP jZ].
  rewrite !(Epr P HP _ t p (fin_mono rho 0 _ ltac:(lra) A1)), !(Epr P HP _ t p (fin_mono rho 0 _ ltac:(lra) A2)),
    !(Epr P HP _ t p (fin_mono rho 0 _ ltac:(lra) A3)).
  cbv beta.
  destruct (fold_map_cyl' (fun s => images (Z.to_nat P) (fst s) (snd s)
                                      (cyl (feval (vR K) t p) p (feval (vZ K) t p))) (srcs3 l) p)
    as [CR [CP CZ]].
  unfold B_R, B_phi, B_Z, coilB, symfield.
  change (coord1 ?v * cos p + coord2 ?v * sin p) with (cylR p v).
  change (- coord1 ?v * sin p + coord2 ?v * cos p) with (cylP p v).
  change (coord3 ?v) with (cylZ v).
  rewrite CR, CP, CZ.
  refine (conj _ (conj _ _)).
  - rewrite (fsum_ext _ (fun k => lsum (fun s => srcR (fst s) (snd s) (feval (vR K) t p)
                                          (p + INR k * (2 * PI / IZR P)) (feval (vZ K) t p)) (srcs3 l))).
    + rewrite lsum_fsum. apply lsum_ext. intros s.
      destruct (images_cyl (Z.to_nat P) (fst s) (snd s) (feval (vR K) t p) p (feval (vZ K) t p)) as [I _].
      cbv zeta in I. rewrite I, seq_fsum. apply fsum_ext. intros k. rewrite theta_sh. reflexivity.
    + intros k. destruct (srcjets_val rho K l t (p + INR k * (2 * PI / IZR P)) Hr FK SK Hl) as [V _].
      rewrite V, KR, KZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => lsum (fun s => srcP (fst s) (snd s) (feval (vR K) t p)
                                          (p + INR k * (2 * PI / IZR P)) (feval (vZ K) t p)) (srcs3 l))).
    + rewrite lsum_fsum. apply lsum_ext. intros s.
      destruct (images_cyl (Z.to_nat P) (fst s) (snd s) (feval (vR K) t p) p (feval (vZ K) t p)) as [_ [I _]].
      cbv zeta in I. rewrite I, seq_fsum. apply fsum_ext. intros k. rewrite theta_sh. reflexivity.
    + intros k. destruct (srcjets_val rho K l t (p + INR k * (2 * PI / IZR P)) Hr FK SK Hl) as [_ [V _]].
      rewrite V, KR, KZ. reflexivity.
  - rewrite (fsum_ext _ (fun k => lsum (fun s => srcZ (fst s) (snd s) (feval (vR K) t p)
                                          (p + INR k * (2 * PI / IZR P)) (feval (vZ K) t p)) (srcs3 l))).
    + rewrite lsum_fsum. apply lsum_ext. intros s.
      destruct (images_cyl (Z.to_nat P) (fst s) (snd s) (feval (vR K) t p) p (feval (vZ K) t p)) as [_ [_ I]].
      cbv zeta in I. rewrite I, seq_fsum. apply fsum_ext. intros k. rewrite theta_sh. reflexivity.
    + intros k. destruct (srcjets_val rho K l t (p + INR k * (2 * PI / IZR P)) Hr FK SK Hl) as [_ [_ V]].
      rewrite V, KR, KZ. reflexivity.
Qed.

End TotVal.

(** * Canonical form, period and parity *)

Definition jcanon (J : cjet) : Prop :=
  is_canon (jR J) /\ is_canon (jP J) /\ is_canon (jZ J) /\
  is_canon (jR_R J) /\ is_canon (jR_Z J) /\ is_canon (jR_phi J) /\
  is_canon (jP_R J) /\ is_canon (jP_Z J) /\ is_canon (jP_phi J) /\
  is_canon (jZ_R J) /\ is_canon (jZ_Z J) /\ is_canon (jZ_phi J).

Definition jper (P : Z) (J : cjet) : Prop :=
  is_per P (jR J) /\ is_per P (jP J) /\ is_per P (jZ J) /\
  is_per P (jR_R J) /\ is_per P (jR_Z J) /\ is_per P (jR_phi J) /\
  is_per P (jP_R J) /\ is_per P (jP_Z J) /\ is_per P (jP_phi J) /\
  is_per P (jZ_R J) /\ is_per P (jZ_Z J) /\ is_per P (jZ_phi J).

(** The parities of a stellarator-symmetric field along a stellarator-symmetric
    torus: B_R is odd and B_phi, B_Z even; a derivative in R keeps the parity
    of its component, and a derivative in Z or in phi reverses it. *)
Definition jpar (J : cjet) : Prop :=
  is_odd (jR J) /\ is_even (jP J) /\ is_even (jZ J) /\
  is_odd (jR_R J) /\ is_even (jR_Z J) /\ is_even (jR_phi J) /\
  is_even (jP_R J) /\ is_odd (jP_Z J) /\ is_odd (jP_phi J) /\
  is_even (jZ_R J) /\ is_odd (jZ_Z J) /\ is_odd (jZ_phi J).

Lemma at2_opp (a b : Z) (x : R) (k l : Z) : at2 a b x (- k) (- l) = at2 (- a) (- b) x k l.
Proof.
  unfold at2. destruct (Z.eqb_spec (- k) a); destruct (Z.eqb_spec (- l) b);
    destruct (Z.eqb_spec k (- a)); destruct (Z.eqb_spec l (- b)); simpl; try lia; reflexivity.
Qed.

Lemma at2_neg (a b : Z) (x : R) (k l : Z) : at2 a b (- x) k l = - at2 a b x k l.
Proof. unfold at2. destruct (_ && _)%bool; ring. Qed.

Lemma cosf_canon : is_canon cosf.
Proof.
  split; intros k l; unfold cosf, fsingle, fadd; cbn [fc fs]; rewrite !at2_opp; cbn [Z.opp].
  - ring.
  - unfold at2. repeat destruct (_ && _)%bool; ring.
Qed.

Lemma sinf_canon : is_canon sinf.
Proof.
  split; intros k l; unfold sinf, fsingle, fadd; cbn [fc fs]; rewrite !at2_opp; cbn [Z.opp].
  - unfold at2. repeat destruct (_ && _)%bool; ring.
  - rewrite !at2_neg. ring.
Qed.

Ltac conjs := repeat match goal with |- _ /\ _ => split end.

Ltac canon_tac :=
  repeat (first [apply cosf_canon | apply sinf_canon | apply fconst_canon
                | apply fmul_canon | apply fadd_canon | apply fsub_canon | apply fscal_canon
                | apply fisqrt_canon | assumption]).

Lemma srcjet_canon (sc : src) (Y : fser) (K : vf) : vcanon K -> is_canon Y -> jcanon (srcjet sc Y K).
Proof.
  intros [CR CZ] CY. unfold jcanon, srcjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  unfold FR, FP, FZ, FR_R, FR_Z, FR_phi, FP_R, FP_Z, FP_phi, FZ_R, FZ_Z, FZ_phi,
    fJeR1, fJeR2, fJeR3, fJeP1, fJeP2, fJeP3, fJ11, fJ12, fJ13, fJ21, fJ22, fJ23, fJ31, fJ32, fJ33,
    fb1, fb2, fb3, fc1, fc2, fc3, fh3, fh5, fy, fq, fr1, fr2, fr3, fx1, fx2.
  conjs; canon_tac.
Qed.

Lemma symjet_canon (J : cjet) : jcanon J -> jcanon (symjet J).
Proof.
  intros [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 [C10 [C11 C12]]]]]]]]]]].
  unfold jcanon, symjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; first [apply fsub_canon | apply fadd_canon]; try apply frefl_canon; assumption.
Qed.

Lemma jadd_canon (J1 J2 : cjet) : jcanon J1 -> jcanon J2 -> jcanon (jadd J1 J2).
Proof.
  intros [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]]
         [B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 [B9 [B10 [B11 B12]]]]]]]]]]].
  unfold jcanon, jadd, jmap2. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; apply fadd_canon; assumption.
Qed.

Lemma jzero_canon : jcanon jzero.
Proof. unfold jcanon, jzero. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi]. conjs; apply fzero_canon. Qed.

Lemma jproj_canon (P : Z) (J : cjet) : (0 < P)%Z -> jcanon J -> jcanon (jproj P J).
Proof.
  intros HP [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 [C10 [C11 C12]]]]]]]]]]].
  unfold jcanon, jproj, jmap. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; apply fscal_canon, fproj_canon; assumption.
Qed.

Theorem tot_canon (P : Z) (l : list (src * fser)) (K : vf) :
  (0 < P)%Z -> vcanon K -> List.Forall (fun sy => is_canon (snd sy)) l -> jcanon (tot P l K).
Proof.
  intros HP CK Hl. apply jproj_canon; [exact HP |].
  induction Hl as [| sy l' Hy _ IH]; [apply jzero_canon |].
  apply jadd_canon; [apply symjet_canon, srcjet_canon; assumption | exact IH].
Qed.

Theorem tot_per (P : Z) (l : list (src * fser)) (K : vf) : jper P (tot P l K).
Proof.
  unfold jper, tot, jproj, jmap. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; apply fscal_per, fproj_per.
Qed.

Lemma symjet_par (J : cjet) : jpar (symjet J).
Proof.
  unfold jpar, symjet. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; first [apply fsym_even | apply fasym_odd].
Qed.

Lemma jadd_par (J1 J2 : cjet) : jpar J1 -> jpar J2 -> jpar (jadd J1 J2).
Proof.
  intros [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]]
         [B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 [B9 [B10 [B11 B12]]]]]]]]]]].
  unfold jpar, jadd, jmap2. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; first [apply fadd_even | apply fadd_odd]; assumption.
Qed.

Lemma jzero_par : jpar jzero.
Proof.
  unfold jpar, jzero. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; first [apply fzero_even | apply fzero_odd].
Qed.

Lemma jproj_par (P : Z) (J : cjet) : jpar J -> jpar (jproj P J).
Proof.
  intros [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 [A10 [A11 A12]]]]]]]]]]].
  unfold jpar, jproj, jmap. cbn [jR jP jZ jR_R jR_Z jR_phi jP_R jP_Z jP_phi jZ_R jZ_Z jZ_phi].
  conjs; first [apply fscal_even, fproj_even | apply fscal_odd, fproj_odd]; assumption.
Qed.

Theorem tot_par (P : Z) (l : list (src * fser)) (K : vf) : jpar (tot P l K).
Proof.
  apply jproj_par. induction l as [| sy l' IH]; [apply jzero_par |].
  apply jadd_par; [apply symjet_par | exact IH].
Qed.
