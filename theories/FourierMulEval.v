(** The product of families carries the product of the functions.

    A family with one nonzero mode carries c cos(k.x) + s sin(k.x)
    ([feval_fsingle]); the product of two such families is the pair of modes
    k + l and k - l the product-to-sum formulas give ([fmul_fsingle]), so the
    product of functions holds for them ([feval_fmul_fsingle]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg.
Local Open Scope R_scope.

(** * Families with one nonzero term *)

Definition at1 (k : Z) (x : R) (m : Z) : R := if Z.eqb m k then x else 0.
Definition at2 (k1 k2 : Z) (x : R) (m n : Z) : R := if (Z.eqb m k1 && Z.eqb n k2)%bool then x else 0.

Lemma zsum_at1 (k : Z) (x : R) (N : nat) :
  zsum (at1 k x) N = if Z.leb (Z.abs k) (Z.of_nat N) then x else 0.
Proof.
  induction N as [| N IH].
  - rewrite zsum_0. unfold at1.
    destruct (Z.eqb_spec 0 k) as [<- | Hk].
    + reflexivity.
    + destruct (Z.leb_spec (Z.abs k) (Z.of_nat 0)); [lia | reflexivity].
  - rewrite zsum_S, IH. unfold at1.
    destruct (Z.eqb_spec (Z.of_nat (S N)) k) as [Hp | Hp];
      destruct (Z.eqb_spec (- Z.of_nat (S N))%Z k) as [Hm | Hm];
      destruct (Z.leb_spec (Z.abs k) (Z.of_nat N)) as [Hl | Hl];
      destruct (Z.leb_spec (Z.abs k) (Z.of_nat (S N))) as [Hl' | Hl']; try lia; ring.
Qed.

Lemma at2_split (k1 k2 : Z) (x : R) (m n : Z) : at2 k1 k2 x m n = at1 k1 (at1 k2 x n) m.
Proof.
  unfold at2, at1. destruct (Z.eqb m k1), (Z.eqb n k2); reflexivity.
Qed.

Lemma sqsum_at2 (k1 k2 : Z) (x : R) (N : nat) :
  sqsum (at2 k1 k2 x) N
    = if (Z.leb (Z.abs k1) (Z.of_nat N) && Z.leb (Z.abs k2) (Z.of_nat N))%bool then x else 0.
Proof.
  unfold sqsum.
  rewrite (zsum_ext _ (fun m => at1 k1 (if Z.leb (Z.abs k2) (Z.of_nat N) then x else 0) m)).
  - rewrite zsum_at1. destruct (Z.leb (Z.abs k1) (Z.of_nat N)), (Z.leb (Z.abs k2) (Z.of_nat N));
      reflexivity.
  - intros m. rewrite (zsum_ext _ (fun n => at1 k1 (at1 k2 x n) m)) by (intros; apply at2_split).
    unfold at1 at 2.
    destruct (Z.eqb_spec m k1) as [-> | Hm].
    + unfold at1. rewrite Z.eqb_refl.
      rewrite (zsum_ext _ (at1 k2 x)) by (intros; unfold at1; reflexivity).
      rewrite zsum_at1. reflexivity.
    + unfold at1. destruct (Z.eqb_spec m k1); [contradiction |].
      rewrite (zsum_ext _ (fun _ => 0 * 0)) by (intros; ring).
      rewrite zsum_scal. ring.
Qed.

Lemma absf_at2 (k1 k2 : Z) (x : R) : forall m n, absf (at2 k1 k2 x) m n = at2 k1 k2 (Rabs x) m n.
Proof. intros m n. unfold absf, at2. destruct (Z.eqb m k1 && Z.eqb n k2)%bool; [reflexivity | apply Rabs_R0]. Qed.

Lemma summable_at2 (k1 k2 : Z) (x : R) : abs_summable (at2 k1 k2 x) (Rabs x).
Proof.
  intros N. rewrite (sqsum_ext _ (at2 k1 k2 (Rabs x))) by apply absf_at2.
  rewrite sqsum_at2. destruct (_ && _)%bool; [lra | apply Rabs_pos].
Qed.

Theorem zz_sum_at2 (k1 k2 : Z) (x : R) : zz_sum (at2 k1 k2 x) = x.
Proof.
  pose proof (zz_sum_is_lim _ _ (summable_at2 k1 k2 x)) as H.
  assert (H' : is_lim_seq (fun N => sqsum (at2 k1 k2 x) N) x).
  { apply is_lim_seq_incr_n with (N := (Z.to_nat (Z.abs k1) + Z.to_nat (Z.abs k2))%nat).
    eapply is_lim_seq_ext; [| apply is_lim_seq_const].
    intros N. rewrite sqsum_at2.
    destruct (Z.leb_spec (Z.abs k1) (Z.of_nat (N + (Z.to_nat (Z.abs k1) + Z.to_nat (Z.abs k2)))));
      destruct (Z.leb_spec (Z.abs k2) (Z.of_nat (N + (Z.to_nat (Z.abs k1) + Z.to_nat (Z.abs k2)))));
      try lia; reflexivity. }
  pose proof (is_lim_seq_unique _ _ H) as U1. pose proof (is_lim_seq_unique _ _ H') as U2.
  rewrite U1 in U2. injection U2. auto.
Qed.

(** * Single modes *)

Definition fsingle (k1 k2 : Z) (c s : R) : fser :=
  {| fc := at2 k1 k2 c ; fs := at2 k1 k2 s |}.

Lemma nbound_fsingle (rho : R) (k1 k2 : Z) (c s : R) :
  nbound rho ((Rabs c + Rabs s) * wt rho k1 k2) (fsingle k1 k2 c s).
Proof.
  intros N.
  rewrite (sqsum_ext _ (at2 k1 k2 ((Rabs c + Rabs s) * wt rho k1 k2))).
  - rewrite sqsum_at2. destruct (_ && _)%bool; [lra |].
    apply Rmult_le_pos; [pose proof (Rabs_pos c); pose proof (Rabs_pos s); lra |].
    apply Rlt_le, wt_pos.
  - intros m n. unfold nterm, fsingle, at2. simpl.
    destruct (Z.eqb_spec m k1) as [-> | Hm]; destruct (Z.eqb_spec n k2) as [-> | Hn];
      simpl; rewrite ?Rabs_R0; ring.
Qed.

Theorem feval_fsingle (k1 k2 : Z) (c s t p : R) :
  feval (fsingle k1 k2 c s) t p = c * cos (mode k1 k2 t p) + s * sin (mode k1 k2 t p).
Proof.
  unfold feval.
  rewrite (zz_sum_ext _ (at2 k1 k2 (c * cos (mode k1 k2 t p) + s * sin (mode k1 k2 t p)))).
  - apply zz_sum_at2.
  - intros m n. unfold term, fsingle, at2. simpl.
    destruct (Z.eqb_spec m k1) as [-> | Hm]; destruct (Z.eqb_spec n k2) as [-> | Hn];
      simpl; ring.
Qed.

(** * Products of single modes *)

Lemma conv_p_at2 (k1 k2 l1 l2 : Z) (x y : R) (m n : Z) :
  conv_p (at2 k1 k2 x) (at2 l1 l2 y) m n = at2 (k1 + l1) (k2 + l2) (x * y) m n.
Proof.
  unfold conv_p.
  rewrite (zz_sum_ext _ (at2 k1 k2 (x * at2 l1 l2 y (m - k1) (n - k2)))).
  - rewrite zz_sum_at2. unfold at2.
    destruct (Z.eqb_spec (m - k1) l1); destruct (Z.eqb_spec (n - k2) l2);
      destruct (Z.eqb_spec m (k1 + l1)); destruct (Z.eqb_spec n (k2 + l2));
      simpl; try lia; ring.
  - intros a b. unfold at2.
    destruct (Z.eqb_spec a k1) as [-> | Ha]; destruct (Z.eqb_spec b k2) as [-> | Hb];
      simpl; ring.
Qed.

Lemma conv_m_at2 (k1 k2 l1 l2 : Z) (x y : R) (m n : Z) :
  conv_m (at2 k1 k2 x) (at2 l1 l2 y) m n = at2 (k1 - l1) (k2 - l2) (x * y) m n.
Proof.
  unfold conv_m.
  rewrite (zz_sum_ext _ (at2 k1 k2 (x * at2 l1 l2 y (k1 - m) (k2 - n)))).
  - rewrite zz_sum_at2. unfold at2.
    destruct (Z.eqb_spec (k1 - m) l1); destruct (Z.eqb_spec (k2 - n) l2);
      destruct (Z.eqb_spec m (k1 - l1)); destruct (Z.eqb_spec n (k2 - l2));
      simpl; try lia; ring.
  - intros a b. unfold at2.
    destruct (Z.eqb_spec a k1) as [-> | Ha]; destruct (Z.eqb_spec b k2) as [-> | Hb];
      simpl; ring.
Qed.

Lemma at2_lin (k1 k2 : Z) (x y : R) (m n : Z) (c d : R) :
  c * at2 k1 k2 x m n + d * at2 k1 k2 y m n = at2 k1 k2 (c * x + d * y) m n.
Proof. unfold at2. destruct (_ && _)%bool; ring. Qed.

Theorem fmul_fsingle (k1 k2 l1 l2 : Z) (c s c' s' : R) :
  feq (fmul (fsingle k1 k2 c s) (fsingle l1 l2 c' s'))
      (fadd (fsingle (k1 + l1) (k2 + l2) (/ 2 * (c * c' - s * s')) (/ 2 * (c * s' + s * c')))
            (fsingle (k1 - l1) (k2 - l2) (/ 2 * (c * c' + s * s')) (/ 2 * (s * c' - c * s')))).
Proof.
  intros m n. simpl.
  rewrite !conv_p_at2, !conv_m_at2.
  split; unfold at2;
    destruct (Z.eqb m (k1 + l1) && Z.eqb n (k2 + l2))%bool;
    destruct (Z.eqb m (k1 - l1) && Z.eqb n (k2 - l2))%bool; ring.
Qed.

Lemma mode_plus (k1 k2 l1 l2 : Z) (t p : R) :
  mode (k1 + l1) (k2 + l2) t p = mode k1 k2 t p + mode l1 l2 t p.
Proof. unfold mode. rewrite !plus_IZR. ring. Qed.

Lemma mode_minus (k1 k2 l1 l2 : Z) (t p : R) :
  mode (k1 - l1) (k2 - l2) t p = mode k1 k2 t p - mode l1 l2 t p.
Proof. unfold mode. rewrite !minus_IZR. ring. Qed.

Theorem feval_fmul_fsingle (k1 k2 l1 l2 : Z) (c s c' s' t p : R) :
  feval (fmul (fsingle k1 k2 c s) (fsingle l1 l2 c' s')) t p
    = feval (fsingle k1 k2 c s) t p * feval (fsingle l1 l2 c' s') t p.
Proof.
  rewrite (feval_feq _ _ t p (fmul_fsingle k1 k2 l1 l2 c s c' s')).
  rewrite (feval_fadd _ _ _ _ t p (nbound_fsingle 0 _ _ _ _) (nbound_fsingle 0 _ _ _ _)).
  rewrite !feval_fsingle, mode_plus, mode_minus.
  set (A := mode k1 k2 t p). set (B := mode l1 l2 t p).
  rewrite cos_plus, sin_plus, cos_minus, sin_minus.
  field.
Qed.
