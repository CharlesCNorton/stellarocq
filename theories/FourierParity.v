(** Even and odd families.

    A family is even when it has no sine coefficients and odd when it has no
    cosine coefficients; their functions are even and odd under (t, p) ->
    (-t, -p). Sums and multiples keep the class, products multiply classes
    as signs do ([fmul_even_even], [fmul_even_odd], [fmul_odd_even],
    [fmul_odd_odd]), the derivatives and the operator L and its inverse swap
    them, and limits, Newton inverses and inverse square roots of even
    families are even. The average of an odd family, its (0, 0) cosine
    coefficient, is zero. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt.
Local Open Scope R_scope.

Definition is_even (u : fser) : Prop := forall m n, fs u m n = 0.
Definition is_odd (u : fser) : Prop := forall m n, fc u m n = 0.

Lemma zz_sum_zero : zz_sum (fun _ _ => 0) = 0.
Proof.
  rewrite (zz_sum_ext _ (at2 0 0 0)); [apply zz_sum_at2 |].
  intros m n. unfold at2. destruct (_ && _)%bool; reflexivity.
Qed.

Lemma conv_p_zero_l (f g : Z -> Z -> R) (m n : Z) :
  (forall k l, f k l = 0) -> conv_p f g m n = 0.
Proof.
  intros H. unfold conv_p. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |].
  intros k l. rewrite H. ring.
Qed.

Lemma conv_p_zero_r (f g : Z -> Z -> R) (m n : Z) :
  (forall k l, g k l = 0) -> conv_p f g m n = 0.
Proof.
  intros H. unfold conv_p. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |].
  intros k l. rewrite H. ring.
Qed.

Lemma conv_m_zero_l (f g : Z -> Z -> R) (m n : Z) :
  (forall k l, f k l = 0) -> conv_m f g m n = 0.
Proof.
  intros H. unfold conv_m. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |].
  intros k l. rewrite H. ring.
Qed.

Lemma conv_m_zero_r (f g : Z -> Z -> R) (m n : Z) :
  (forall k l, g k l = 0) -> conv_m f g m n = 0.
Proof.
  intros H. unfold conv_m. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |].
  intros k l. rewrite H. ring.
Qed.

(** * Products *)

Lemma fmul_even_even (u v : fser) : is_even u -> is_even v -> is_even (fmul u v).
Proof.
  intros Hu Hv m n. simpl.
  rewrite (conv_p_zero_r (fc u) (fs v)), (conv_p_zero_l (fs u) (fc v)),
    (conv_m_zero_r (fc u) (fs v)), (conv_m_zero_l (fs u) (fc v)) by assumption. ring.
Qed.

Lemma fmul_odd_odd (u v : fser) : is_odd u -> is_odd v -> is_even (fmul u v).
Proof.
  intros Hu Hv m n. simpl.
  rewrite (conv_p_zero_l (fc u) (fs v)), (conv_p_zero_r (fs u) (fc v)),
    (conv_m_zero_l (fc u) (fs v)), (conv_m_zero_r (fs u) (fc v)) by assumption. ring.
Qed.

Lemma fmul_even_odd (u v : fser) : is_even u -> is_odd v -> is_odd (fmul u v).
Proof.
  intros Hu Hv m n. simpl.
  rewrite (conv_p_zero_r (fc u) (fc v)), (conv_p_zero_l (fs u) (fs v)),
    (conv_m_zero_r (fc u) (fc v)), (conv_m_zero_l (fs u) (fs v)) by assumption. ring.
Qed.

Lemma fmul_odd_even (u v : fser) : is_odd u -> is_even v -> is_odd (fmul u v).
Proof.
  intros Hu Hv m n. simpl.
  rewrite (conv_p_zero_l (fc u) (fc v)), (conv_p_zero_r (fs u) (fs v)),
    (conv_m_zero_l (fc u) (fc v)), (conv_m_zero_r (fs u) (fs v)) by assumption. ring.
Qed.

(** * Linear operations *)

Lemma fadd_even (u v : fser) : is_even u -> is_even v -> is_even (fadd u v).
Proof. intros Hu Hv m n. simpl. rewrite Hu, Hv. ring. Qed.

Lemma fadd_odd (u v : fser) : is_odd u -> is_odd v -> is_odd (fadd u v).
Proof. intros Hu Hv m n. simpl. rewrite Hu, Hv. ring. Qed.

Lemma fscal_even (c : R) (u : fser) : is_even u -> is_even (fscal c u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma fscal_odd (c : R) (u : fser) : is_odd u -> is_odd (fscal c u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma fsub_even (u v : fser) : is_even u -> is_even v -> is_even (fsub u v).
Proof. intros Hu Hv. apply fadd_even; [exact Hu | apply fscal_even, Hv]. Qed.

Lemma fsub_odd (u v : fser) : is_odd u -> is_odd v -> is_odd (fsub u v).
Proof. intros Hu Hv. apply fadd_odd; [exact Hu | apply fscal_odd, Hv]. Qed.

Lemma fone_even : is_even fone.
Proof. intros m n. unfold fone, fsingle, at2. simpl. destruct (_ && _)%bool; reflexivity. Qed.

Lemma fzero_even : is_even fzero.
Proof. intros m n. reflexivity. Qed.

Lemma fzero_odd : is_odd fzero.
Proof. intros m n. reflexivity. Qed.

(** * Derivatives and the operator L *)

Lemma dt_even (u : fser) : is_even u -> is_odd (dt u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma dt_odd (u : fser) : is_odd u -> is_even (dt u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma dp_even (u : fser) : is_even u -> is_odd (dp u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma dp_odd (u : fser) : is_odd u -> is_even (dp u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma lc_even (rho0 : R) (u : fser) : is_even u -> is_odd (lc rho0 u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma lc_odd (rho0 : R) (u : fser) : is_odd u -> is_even (lc rho0 u).
Proof. intros Hu m n. simpl. rewrite Hu. ring. Qed.

Lemma linv_even (rho0 : R) (u : fser) : is_even u -> is_odd (linv rho0 u).
Proof.
  intros Hu m n. simpl. destruct (is_mean m n); [reflexivity |]. rewrite Hu. unfold Rdiv. ring.
Qed.

Lemma linv_odd (rho0 : R) (u : fser) : is_odd u -> is_even (linv rho0 u).
Proof.
  intros Hu m n. simpl. destruct (is_mean m n); [reflexivity |]. rewrite Hu. unfold Rdiv. ring.
Qed.

(** * Limits, inverses and inverse square roots *)

Lemma flim_even (us : nat -> fser) : (forall n, is_even (us n)) -> is_even (flim us).
Proof.
  intros H m n. simpl.
  rewrite (Lim_seq_ext _ (fun _ => 0)) by (intros; apply H).
  rewrite Lim_seq_const. reflexivity.
Qed.

Lemma flim_odd (us : nat -> fser) : (forall n, is_odd (us n)) -> is_odd (flim us).
Proof.
  intros H m n. simpl.
  rewrite (Lim_seq_ext _ (fun _ => 0)) by (intros; apply H).
  rewrite Lim_seq_const. reflexivity.
Qed.

Lemma finv_even (u y0 : fser) : is_even u -> is_even y0 -> is_even (finv u y0).
Proof.
  intros Hu Hy0. unfold finv. apply flim_even. intros k.
  assert (H : is_even (iy u y0 k) /\ is_even (ie u y0 k)).
  { induction k as [| k [IHy IHe]].
    - unfold iy, ie. simpl. split; [exact Hy0 |].
      apply fsub_even; [apply fone_even | apply fmul_even_even; assumption].
    - rewrite iy_S, ie_S. split.
      + apply fmul_even_even; [exact IHy | apply fadd_even; [apply fone_even | exact IHe]].
      + apply fmul_even_even; assumption. }
  apply H.
Qed.

Lemma fisqrt_even (D y0 : fser) : is_even D -> is_even y0 -> is_even (fisqrt D y0).
Proof.
  intros HD Hy0. unfold fisqrt. apply flim_even. intros k.
  assert (H : is_even (sy D y0 k) /\ is_even (se D y0 k)).
  { induction k as [| k [IHy IHe]].
    - unfold sy, se. simpl. split; [exact Hy0 |].
      apply fsub_even; [apply fone_even |].
      apply fmul_even_even; [exact HD | apply fmul_even_even; assumption].
    - rewrite sy_S, se_S. unfold half_step, err_step. split.
      + apply fmul_even_even; [exact IHy |].
        apply fadd_even; [apply fone_even | apply fscal_even, IHe].
      + apply fadd_even; apply fscal_even.
        * apply fmul_even_even; assumption.
        * apply fmul_even_even; [apply fmul_even_even; assumption | exact IHe]. }
  apply H.
Qed.
