(** Exact quadrature of trigonometric polynomials.

    A trigonometric polynomial of degree D in an angle is a finite sum of
    cos(k x) and sin(k x) with k <= D. The equispaced rule on N points over a
    period integrates every such term exactly once N exceeds D: the constant
    term sums to its integral, and every other term sums to zero, as its
    integral does. So for these functions a finite sum of point values is the
    integral itself, with no error term and no derivative bound.

    That is what makes the resonant harmonic of the force a finite
    computation. The residual divides by the Jacobian, so it is not a
    polynomial in the angles, but the residual times a power of the Jacobian
    is, because every other factor is a finite Fourier series and the only
    operations left are sums and products. [TP1] and [TP2] are the classes in
    one and two angles, closed under the operations that build such a
    numerator, and [exact1] and [exact2] are the rules. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Quad.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Integrals of sums and multiples, over the reals                   *)

(** An equation between integrals is typed at the carrier of Coquelicot's
    module structure, which is R only after unfolding; ring and field want to
    see R itself. *)
Ltac to_R := try (match goal with |- @eq _ ?x ?y => change (@eq R x y) end).

Lemma RInt_plus_R :
  forall (f g : R -> R) a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof. intros f g a b H1 H2. exact (RInt_plus f g a b H1 H2). Qed.

Lemma RInt_scal_R :
  forall (f : R -> R) a b c, ex_RInt f a b ->
  RInt (fun x => c * f x) a b = c * RInt f a b.
Proof. intros f a b c H. exact (RInt_scal f a b c H). Qed.

(* ---------------------------------------------------------------- *)
(* One angle                                                         *)

Inductive TP1 (D : nat) : (R -> R) -> Prop :=
  | tp1_zero : TP1 D (fun _ => 0)
  | tp1_cos : forall f c k, TP1 D f -> (k <= D)%nat ->
      TP1 D (fun x => f x + c * cos (INR k * x))
  | tp1_sin : forall f c k, TP1 D f -> (k <= D)%nat ->
      TP1 D (fun x => f x + c * sin (INR k * x))
  | tp1_ext : forall f g, (forall x, f x = g x) -> TP1 D f -> TP1 D g.

Lemma TP1_mono : forall D D' f, TP1 D f -> (D <= D')%nat -> TP1 D' f.
Proof.
  intros D D' f H Hd. induction H.
  - apply tp1_zero.
  - apply tp1_cos. exact IHTP1. lia.
  - apply tp1_sin. exact IHTP1. lia.
  - apply (tp1_ext D' f g H). exact IHTP1.
Qed.

Lemma TP1_cos1 : forall D c k, (k <= D)%nat -> TP1 D (fun x => c * cos (INR k * x)).
Proof.
  intros D c k Hk. apply (tp1_ext D (fun x => 0 + c * cos (INR k * x))).
  - intros x. ring.
  - apply tp1_cos. apply tp1_zero. exact Hk.
Qed.

Lemma TP1_sin1 : forall D c k, (k <= D)%nat -> TP1 D (fun x => c * sin (INR k * x)).
Proof.
  intros D c k Hk. apply (tp1_ext D (fun x => 0 + c * sin (INR k * x))).
  - intros x. ring.
  - apply tp1_sin. apply tp1_zero. exact Hk.
Qed.

Lemma TP1_const : forall D c, TP1 D (fun _ => c).
Proof.
  intros D c. apply (tp1_ext D (fun x => c * cos (INR 0 * x))).
  - intros x. simpl. rewrite Rmult_0_l, cos_0. ring.
  - apply TP1_cos1. lia.
Qed.

Lemma TP1_add : forall D f g, TP1 D f -> TP1 D g -> TP1 D (fun x => f x + g x).
Proof.
  intros D f g Hf Hg. induction Hg.
  - apply (tp1_ext D f). intros x. ring. exact Hf.
  - apply (tp1_ext D (fun x => (f x + f0 x) + c * cos (INR k * x))).
    + intros x. ring.
    + apply tp1_cos. exact IHHg. exact H.
  - apply (tp1_ext D (fun x => (f x + f0 x) + c * sin (INR k * x))).
    + intros x. ring.
    + apply tp1_sin. exact IHHg. exact H.
  - apply (tp1_ext D (fun x => f x + f0 x)).
    + intros x. now rewrite H.
    + exact IHHg.
Qed.

Lemma TP1_scal : forall D a f, TP1 D f -> TP1 D (fun x => a * f x).
Proof.
  intros D a f Hf. induction Hf.
  - apply (tp1_ext D (fun _ => 0)). intros x. ring. apply tp1_zero.
  - apply (tp1_ext D (fun x => a * f x + (a * c) * cos (INR k * x))).
    + intros x. ring.
    + apply tp1_cos. exact IHHf. exact H.
  - apply (tp1_ext D (fun x => a * f x + (a * c) * sin (INR k * x))).
    + intros x. ring.
    + apply tp1_sin. exact IHHf. exact H.
  - apply (tp1_ext D (fun x => a * f x)).
    + intros x. now rewrite H.
    + exact IHHf.
Qed.

Lemma TP1_sub : forall D f g, TP1 D f -> TP1 D g -> TP1 D (fun x => f x - g x).
Proof.
  intros D f g Hf Hg.
  apply (tp1_ext D (fun x => f x + (-1) * g x)). intros x. ring.
  apply TP1_add. exact Hf. now apply TP1_scal.
Qed.

(** cos((k - l) x) and sin((k - l) x), whichever of k and l is larger. *)
Lemma TP1_cos_diff :
  forall D k l, (k <= D)%nat -> (l <= D)%nat ->
  TP1 D (fun x => cos (INR k * x - INR l * x)).
Proof.
  intros D k l Hk Hl.
  destruct (Nat.le_ge_cases l k) as [H|H].
  - apply (tp1_ext D (fun x => 1 * cos (INR (k - l) * x))).
    + intros x. rewrite minus_INR by exact H. rewrite Rmult_1_l.
      f_equal. ring.
    + apply TP1_cos1. lia.
  - apply (tp1_ext D (fun x => 1 * cos (INR (l - k) * x))).
    + intros x. rewrite minus_INR by exact H.
      replace (INR k * x - INR l * x) with (- ((INR l - INR k) * x)) by ring.
      rewrite cos_neg. ring.
    + apply TP1_cos1. lia.
Qed.

Lemma TP1_sin_diff :
  forall D k l, (k <= D)%nat -> (l <= D)%nat ->
  TP1 D (fun x => sin (INR k * x - INR l * x)).
Proof.
  intros D k l Hk Hl.
  destruct (Nat.le_ge_cases l k) as [H|H].
  - apply (tp1_ext D (fun x => 1 * sin (INR (k - l) * x))).
    + intros x. rewrite minus_INR by exact H. rewrite Rmult_1_l.
      f_equal. ring.
    + apply TP1_sin1. lia.
  - apply (tp1_ext D (fun x => (-1) * sin (INR (l - k) * x))).
    + intros x. rewrite minus_INR by exact H.
      replace (INR k * x - INR l * x) with (- ((INR l - INR k) * x)) by ring.
      rewrite sin_neg. ring.
    + apply TP1_sin1. lia.
Qed.

(** The four products of basis terms, by the product-to-sum formulas. *)
Lemma TP1_basis_mul :
  forall D E k l (sk sl : bool), (k <= D)%nat -> (l <= E)%nat ->
  TP1 (D + E) (fun x => (if sk then sin (INR k * x) else cos (INR k * x)) *
                        (if sl then sin (INR l * x) else cos (INR l * x))).
Proof.
  intros D E k l sk sl Hk Hl.
  assert (Hkl : (k + l <= D + E)%nat) by lia.
  assert (Hsum : forall x, INR (k + l) * x = INR k * x + INR l * x)
    by (intros x; rewrite plus_INR; ring).
  destruct sk, sl; cbv beta iota.
  - (* sin sin = (cos(a - b) - cos(a + b)) / 2 *)
    apply (tp1_ext (D + E)
             (fun x => (/2) * cos (INR k * x - INR l * x)
                       + (- / 2) * cos (INR (k + l) * x))).
    + intros x. rewrite Hsum, cos_minus, cos_plus. field.
    + apply TP1_add.
      * apply TP1_scal. apply TP1_cos_diff; lia.
      * apply TP1_cos1. exact Hkl.
  - (* sin cos = (sin(a + b) + sin(a - b)) / 2 *)
    apply (tp1_ext (D + E)
             (fun x => (/2) * sin (INR (k + l) * x)
                       + (/ 2) * sin (INR k * x - INR l * x))).
    + intros x. rewrite Hsum, sin_minus, sin_plus. field.
    + apply TP1_add.
      * apply TP1_sin1. exact Hkl.
      * apply TP1_scal. apply TP1_sin_diff; lia.
  - (* cos sin = (sin(a + b) - sin(a - b)) / 2 *)
    apply (tp1_ext (D + E)
             (fun x => (/2) * sin (INR (k + l) * x)
                       + (- / 2) * sin (INR k * x - INR l * x))).
    + intros x. rewrite Hsum, sin_minus, sin_plus. field.
    + apply TP1_add.
      * apply TP1_sin1. exact Hkl.
      * apply TP1_scal. apply TP1_sin_diff; lia.
  - (* cos cos = (cos(a + b) + cos(a - b)) / 2 *)
    apply (tp1_ext (D + E)
             (fun x => (/2) * cos (INR (k + l) * x)
                       + (/ 2) * cos (INR k * x - INR l * x))).
    + intros x. rewrite Hsum, cos_minus, cos_plus. field.
    + apply TP1_add.
      * apply TP1_cos1. exact Hkl.
      * apply TP1_scal. apply TP1_cos_diff; lia.
Qed.

(** A basis term times a polynomial. *)
Lemma TP1_basis_mul_poly :
  forall D E k (sk : bool) g, (k <= D)%nat -> TP1 E g ->
  TP1 (D + E) (fun x => (if sk then sin (INR k * x) else cos (INR k * x)) * g x).
Proof.
  intros D E k sk g Hk Hg. induction Hg.
  - apply (tp1_ext (D + E) (fun _ => 0)). intros x. ring. apply tp1_zero.
  - apply (tp1_ext (D + E)
             (fun x => (if sk then sin (INR k * x) else cos (INR k * x)) * f x
                       + c * ((if sk then sin (INR k * x) else cos (INR k * x))
                              * cos (INR k0 * x)))).
    + intros x. ring.
    + apply TP1_add. exact IHHg.
      apply TP1_scal. exact (TP1_basis_mul D E k k0 sk false Hk H).
  - apply (tp1_ext (D + E)
             (fun x => (if sk then sin (INR k * x) else cos (INR k * x)) * f x
                       + c * ((if sk then sin (INR k * x) else cos (INR k * x))
                              * sin (INR k0 * x)))).
    + intros x. ring.
    + apply TP1_add. exact IHHg.
      apply TP1_scal. exact (TP1_basis_mul D E k k0 sk true Hk H).
  - apply (tp1_ext (D + E)
             (fun x => (if sk then sin (INR k * x) else cos (INR k * x)) * f x)).
    + intros x. now rewrite H.
    + exact IHHg.
Qed.

Lemma TP1_mul : forall D E f g, TP1 D f -> TP1 E g -> TP1 (D + E) (fun x => f x * g x).
Proof.
  intros D E f g Hf Hg. induction Hf.
  - apply (tp1_ext (D + E) (fun _ => 0)). intros x. ring. apply tp1_zero.
  - apply (tp1_ext (D + E)
             (fun x => f x * g x + c * (cos (INR k * x) * g x))).
    + intros x. ring.
    + apply TP1_add. exact IHHf.
      apply TP1_scal. exact (TP1_basis_mul_poly D E k false g H Hg).
  - apply (tp1_ext (D + E)
             (fun x => f x * g x + c * (sin (INR k * x) * g x))).
    + intros x. ring.
    + apply TP1_add. exact IHHf.
      apply TP1_scal. exact (TP1_basis_mul_poly D E k true g H Hg).
  - apply (tp1_ext (D + E) (fun x => f x * g x)).
    + intros x. now rewrite H.
    + exact IHHf.
Qed.

(** An integer frequency, of either sign, with a phase. *)
Lemma INR_abs_nat : forall m, INR (Z.abs_nat m) = Rabs (IZR m).
Proof.
  intros m. rewrite INR_IZR_INZ, Nat2Z.inj_abs_nat. apply abs_IZR.
Qed.

Lemma TP1_cos_int :
  forall m c, TP1 (Z.abs_nat m) (fun x => cos (IZR m * x + c)).
Proof.
  intros m c.
  destruct (Rle_or_lt 0 (IZR m)) as [H|H].
  - apply (tp1_ext _ (fun x => 0 + cos c * cos (INR (Z.abs_nat m) * x)
                              + (- sin c) * sin (INR (Z.abs_nat m) * x))).
    + intros x. rewrite INR_abs_nat, Rabs_right by lra.
      rewrite cos_plus. ring.
    + apply tp1_sin. apply tp1_cos. apply tp1_zero. lia. lia.
  - apply (tp1_ext _ (fun x => 0 + cos c * cos (INR (Z.abs_nat m) * x)
                              + sin c * sin (INR (Z.abs_nat m) * x))).
    + intros x. rewrite INR_abs_nat, Rabs_left by lra.
      replace (IZR m * x + c) with (c - (- IZR m) * x) by ring.
      rewrite cos_minus. ring.
    + apply tp1_sin. apply tp1_cos. apply tp1_zero. lia. lia.
Qed.

Lemma TP1_sin_int :
  forall m c, TP1 (Z.abs_nat m) (fun x => sin (IZR m * x + c)).
Proof.
  intros m c.
  destruct (Rle_or_lt 0 (IZR m)) as [H|H].
  - apply (tp1_ext _ (fun x => 0 + sin c * cos (INR (Z.abs_nat m) * x)
                              + cos c * sin (INR (Z.abs_nat m) * x))).
    + intros x. rewrite INR_abs_nat, Rabs_right by lra.
      rewrite sin_plus. ring.
    + apply tp1_sin. apply tp1_cos. apply tp1_zero. lia. lia.
  - apply (tp1_ext _ (fun x => 0 + sin c * cos (INR (Z.abs_nat m) * x)
                              + (- cos c) * sin (INR (Z.abs_nat m) * x))).
    + intros x. rewrite INR_abs_nat, Rabs_left by lra.
      replace (IZR m * x + c) with (c - (- IZR m) * x) by ring.
      rewrite sin_minus. ring.
    + apply tp1_sin. apply tp1_cos. apply tp1_zero. lia. lia.
Qed.

(** Polynomials are continuous, hence integrable. *)
Lemma TP1_continuity_pt : forall D f, TP1 D f -> forall x, continuity_pt f x.
Proof.
  intros D f Hf. induction Hf; intros x.
  - apply continuity_pt_const. intros a b. reflexivity.
  - change (continuity_pt (plus_fct f (fun y => c * cos (INR k * y))) x).
    apply continuity_pt_plus. apply IHHf. reg.
  - change (continuity_pt (plus_fct f (fun y => c * sin (INR k * y))) x).
    apply continuity_pt_plus. apply IHHf. reg.
  - apply (continuity_pt_ext f g). exact H. apply IHHf.
Qed.

Lemma TP1_ex_RInt : forall D f a b, TP1 D f -> ex_RInt f a b.
Proof.
  intros D f a b Hf. apply (@ex_RInt_continuous R_CompleteNormedModule). intros z _.
  apply continuity_pt_filterlim. exact (TP1_continuity_pt D f Hf z).
Qed.

(* ---------------------------------------------------------------- *)
(* The equispaced rule on one angle                                  *)

(** N equispaced points over [a, a + 2 pi], each weighted by 2 pi / N. *)
Definition node (N : nat) (a : R) (j : nat) : R := a + 2 * PI * INR j / INR N.

Definition dsum1 (N : nat) (a : R) (f : R -> R) : R :=
  rsum (fun j => f (node N a j)) N * (2 * PI / INR N).

Lemma rsum_plus : forall (f g : nat -> R) N, rsum (fun j => f j + g j) N = rsum f N + rsum g N.
Proof. intros f g N. induction N as [|N IH]; simpl. ring. rewrite IH. ring. Qed.

Lemma rsum_scal : forall (f : nat -> R) c N, rsum (fun j => c * f j) N = c * rsum f N.
Proof. intros f c N. induction N as [|N IH]; simpl. ring. rewrite IH. ring. Qed.

Lemma rsum_ext : forall (f g : nat -> R) N, (forall j, f j = g j) -> rsum f N = rsum g N.
Proof. intros f g N H. induction N as [|N IH]; simpl. ring. rewrite IH, H. ring. Qed.

Lemma rsum_const : forall c N, rsum (fun _ => c) N = INR N * c.
Proof.
  intros c N. induction N as [|N IH]; simpl rsum. simpl. ring. rewrite IH, S_INR. ring.
Qed.

(** The telescoping sums of cosines and sines along an arithmetic run of
    angles. *)
Lemma sum_cos_arith :
  forall th ph N,
  2 * sin (ph / 2) * rsum (fun j => cos (th + INR j * ph)) N
  = sin (th + INR N * ph - ph / 2) - sin (th - ph / 2).
Proof.
  intros th ph N. induction N as [|N IH].
  - simpl. replace (th + 0 * ph - ph / 2) with (th - ph / 2) by ring. ring.
  - simpl rsum. rewrite Rmult_plus_distr_l, IH, S_INR.
    replace (th + (INR N + 1) * ph - ph / 2) with ((th + INR N * ph) + ph / 2) by field.
    replace (th + INR N * ph - ph / 2) with ((th + INR N * ph) - ph / 2) by ring.
    rewrite (sin_plus (th + INR N * ph) (ph / 2)).
    rewrite (sin_minus (th + INR N * ph) (ph / 2)). ring.
Qed.

Lemma sum_sin_arith :
  forall th ph N,
  2 * sin (ph / 2) * rsum (fun j => sin (th + INR j * ph)) N
  = cos (th - ph / 2) - cos (th + INR N * ph - ph / 2).
Proof.
  intros th ph N. induction N as [|N IH].
  - simpl. replace (th + 0 * ph - ph / 2) with (th - ph / 2) by ring. ring.
  - simpl rsum. rewrite Rmult_plus_distr_l, IH, S_INR.
    replace (th + (INR N + 1) * ph - ph / 2) with ((th + INR N * ph) + ph / 2) by field.
    replace (th + INR N * ph - ph / 2) with ((th + INR N * ph) - ph / 2) by ring.
    rewrite (cos_plus (th + INR N * ph) (ph / 2)).
    rewrite (cos_minus (th + INR N * ph) (ph / 2)). ring.
Qed.

(** A frequency strictly between 0 and N sums to zero over the N points. *)
Lemma node_arith :
  forall N a k j, (0 < N)%nat ->
  INR k * node N a j = INR k * a + INR j * (2 * PI * INR k / INR N).
Proof.
  intros N a k j HN. unfold node.
  assert (HN' : INR N <> 0) by (apply not_0_INR; lia).
  field. exact HN'.
Qed.

Lemma half_step_sin_pos :
  forall N k, (0 < k)%nat -> (k < N)%nat -> 0 < sin ((2 * PI * INR k / INR N) / 2).
Proof.
  intros N k Hk HkN.
  assert (H1 : 0 < INR k) by (apply lt_0_INR; lia).
  assert (H2 : 0 < INR N) by (apply lt_0_INR; lia).
  assert (H3 : INR k < INR N) by (apply lt_INR; lia).
  assert (HP := PI_RGT_0).
  apply sin_gt_0.
  - apply Rdiv_lt_0_compat; [|lra]. apply Rdiv_lt_0_compat; [|exact H2]. nra.
  - replace (2 * PI * INR k / INR N / 2) with (PI * (INR k / INR N)) by (field; lra).
    assert (Hq : INR k / INR N < 1).
    { unfold Rdiv. apply (Rmult_lt_reg_r (INR N)). exact H2.
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra. exact H3. }
    assert (Hq0 : 0 < INR k / INR N) by (apply Rdiv_lt_0_compat; assumption).
    nra.
Qed.

Lemma dsum_cos_zero :
  forall N a k, (0 < k)%nat -> (k < N)%nat ->
  rsum (fun j => cos (INR k * node N a j)) N = 0.
Proof.
  intros N a k Hk HkN.
  set (ph := 2 * PI * INR k / INR N).
  assert (Hs := half_step_sin_pos N k Hk HkN). fold ph in Hs.
  assert (Heq : rsum (fun j => cos (INR k * node N a j)) N
                = rsum (fun j => cos (INR k * a + INR j * ph)) N).
  { apply rsum_ext. intros j. rewrite (node_arith N a k j) by lia. reflexivity. }
  rewrite Heq.
  assert (Hsum := sum_cos_arith (INR k * a) ph N).
  assert (Hper : INR k * a + INR N * ph - ph / 2 = (INR k * a - ph / 2) + 2 * INR k * PI).
  { unfold ph. assert (INR N <> 0) by (apply not_0_INR; lia). field. exact H. }
  rewrite Hper, sin_period in Hsum.
  apply (Rmult_eq_reg_l (2 * sin (ph / 2))). rewrite Hsum. ring. lra.
Qed.

Lemma dsum_sin_zero :
  forall N a k, (0 < k)%nat -> (k < N)%nat ->
  rsum (fun j => sin (INR k * node N a j)) N = 0.
Proof.
  intros N a k Hk HkN.
  set (ph := 2 * PI * INR k / INR N).
  assert (Hs := half_step_sin_pos N k Hk HkN). fold ph in Hs.
  assert (Heq : rsum (fun j => sin (INR k * node N a j)) N
                = rsum (fun j => sin (INR k * a + INR j * ph)) N).
  { apply rsum_ext. intros j. rewrite (node_arith N a k j) by lia. reflexivity. }
  rewrite Heq.
  assert (Hsum := sum_sin_arith (INR k * a) ph N).
  assert (Hper : INR k * a + INR N * ph - ph / 2 = (INR k * a - ph / 2) + 2 * INR k * PI).
  { unfold ph. assert (INR N <> 0) by (apply not_0_INR; lia). field. exact H. }
  rewrite Hper, cos_period in Hsum.
  apply (Rmult_eq_reg_l (2 * sin (ph / 2))). rewrite Hsum. ring. lra.
Qed.

(** The integrals of the basis terms over a period. *)
Lemma RInt_cos_period :
  forall a k, (0 < k)%nat -> RInt (fun x => cos (INR k * x)) a (a + 2 * PI) = 0.
Proof.
  intros a k Hk.
  assert (Hk' : INR k <> 0) by (apply not_0_INR; lia).
  assert (HI : is_RInt (fun x => cos (INR k * x)) a (a + 2 * PI)
                 (minus (sin (INR k * (a + 2 * PI)) / INR k) (sin (INR k * a) / INR k))).
  { apply (is_RInt_derive (fun x => sin (INR k * x) / INR k)).
    - intros x _. auto_derive; try exact I; try (field; exact Hk'); try field.
    - intros x _. apply continuity_pt_filterlim. reg. }
  rewrite (is_RInt_unique _ _ _ _ HI).
  replace (INR k * (a + 2 * PI)) with (INR k * a + 2 * INR k * PI) by ring.
  rewrite sin_period. unfold minus, plus, opp; simpl. to_R. ring.
Qed.

Lemma RInt_sin_period :
  forall a k, RInt (fun x => sin (INR k * x)) a (a + 2 * PI) = 0.
Proof.
  intros a k. destruct (Nat.eq_dec k 0) as [->|Hk].
  - rewrite (RInt_ext _ (fun _ => 0)).
    + rewrite RInt_const_R. to_R. ring.
    + intros x _. simpl. rewrite Rmult_0_l. apply sin_0.
  - assert (Hk' : INR k <> 0) by (apply not_0_INR; lia).
    assert (HI : is_RInt (fun x => sin (INR k * x)) a (a + 2 * PI)
                   (minus (- cos (INR k * (a + 2 * PI)) / INR k)
                          (- cos (INR k * a) / INR k))).
    { apply (is_RInt_derive (fun x => - cos (INR k * x) / INR k)).
      - intros x _. auto_derive; try exact I; try (field; exact Hk'); try field.
      - intros x _. apply continuity_pt_filterlim. reg. }
    rewrite (is_RInt_unique _ _ _ _ HI).
    replace (INR k * (a + 2 * PI)) with (INR k * a + 2 * INR k * PI) by ring.
    rewrite cos_period. unfold minus, plus, opp; simpl. to_R. ring.
Qed.

(** The rule is exact on each basis term of frequency below N. *)
Lemma exact_cos :
  forall N a k, (k < N)%nat ->
  RInt (fun x => cos (INR k * x)) a (a + 2 * PI) = dsum1 N a (fun x => cos (INR k * x)).
Proof.
  intros N a k HkN. unfold dsum1.
  assert (HN : INR N <> 0) by (apply not_0_INR; lia).
  destruct (Nat.eq_dec k 0) as [->|Hk].
  - rewrite (RInt_ext _ (fun _ => 1)).
    + rewrite RInt_const_R.
      rewrite (rsum_ext _ (fun _ => 1)).
      * rewrite rsum_const. to_R. field. exact HN.
      * intros j. simpl. rewrite Rmult_0_l. apply cos_0.
    + intros x _. simpl. rewrite Rmult_0_l. apply cos_0.
  - rewrite RInt_cos_period by lia. rewrite dsum_cos_zero by lia. to_R. ring.
Qed.

Lemma exact_sin :
  forall N a k, (k < N)%nat ->
  RInt (fun x => sin (INR k * x)) a (a + 2 * PI) = dsum1 N a (fun x => sin (INR k * x)).
Proof.
  intros N a k HkN. unfold dsum1.
  rewrite RInt_sin_period.
  destruct (Nat.eq_dec k 0) as [->|Hk].
  - rewrite (rsum_ext _ (fun _ => 0)).
    + rewrite rsum_const. to_R. ring.
    + intros j. simpl. rewrite Rmult_0_l. apply sin_0.
  - rewrite dsum_sin_zero by lia. to_R. ring.
Qed.

(** The rule on N points integrates every polynomial of degree below N over a
    period exactly. *)
Theorem exact1 :
  forall D N a f, TP1 D f -> (D < N)%nat ->
  RInt f a (a + 2 * PI) = dsum1 N a f.
Proof.
  intros D N a f Hf HDN. induction Hf.
  - unfold dsum1. cbv beta. rewrite rsum_const, RInt_const_R. to_R. ring.
  - assert (Hex1 := TP1_ex_RInt D f a (a + 2 * PI) Hf).
    assert (Hex2 : ex_RInt (fun x => cos (INR k * x)) a (a + 2 * PI)).
    { apply (TP1_ex_RInt D). apply (tp1_ext D (fun x => 1 * cos (INR k * x))).
      intros x; ring. apply TP1_cos1. exact H. }
    assert (Hex3 : ex_RInt (fun x => c * cos (INR k * x)) a (a + 2 * PI))
      by (apply (TP1_ex_RInt D); apply TP1_cos1; exact H).
    rewrite (RInt_plus_R f (fun x => c * cos (INR k * x))) by assumption.
    rewrite (RInt_scal_R (fun x => cos (INR k * x))) by assumption.
    rewrite IHHf, (exact_cos N a k) by lia.
    unfold dsum1. cbv beta. rewrite rsum_plus, rsum_scal. to_R. ring.
  - assert (Hex1 := TP1_ex_RInt D f a (a + 2 * PI) Hf).
    assert (Hex2 : ex_RInt (fun x => sin (INR k * x)) a (a + 2 * PI)).
    { apply (TP1_ex_RInt D). apply (tp1_ext D (fun x => 1 * sin (INR k * x))).
      intros x; ring. apply TP1_sin1. exact H. }
    assert (Hex3 : ex_RInt (fun x => c * sin (INR k * x)) a (a + 2 * PI))
      by (apply (TP1_ex_RInt D); apply TP1_sin1; exact H).
    rewrite (RInt_plus_R f (fun x => c * sin (INR k * x))) by assumption.
    rewrite (RInt_scal_R (fun x => sin (INR k * x))) by assumption.
    rewrite IHHf, (exact_sin N a k) by lia.
    unfold dsum1. cbv beta. rewrite rsum_plus, rsum_scal. to_R. ring.
  - rewrite <- (RInt_ext f g) by (intros x _; apply H).
    rewrite IHHf. unfold dsum1. f_equal. apply rsum_ext. intros j. apply H.
Qed.

(* ---------------------------------------------------------------- *)
(* Two angles                                                        *)

(** Finite sums of products of a polynomial in each angle. *)
Inductive TP2 (Du Dv : nat) : (R -> R -> R) -> Prop :=
  | tp2_zero : TP2 Du Dv (fun _ _ => 0)
  | tp2_prod : forall F f g, TP2 Du Dv F -> TP1 Du f -> TP1 Dv g ->
      TP2 Du Dv (fun u v => F u v + f u * g v)
  | tp2_ext : forall F G, (forall u v, F u v = G u v) -> TP2 Du Dv F -> TP2 Du Dv G.

Lemma TP2_mono :
  forall Du Dv Du' Dv' F, TP2 Du Dv F -> (Du <= Du')%nat -> (Dv <= Dv')%nat ->
  TP2 Du' Dv' F.
Proof.
  intros Du Dv Du' Dv' F H Hu Hv. induction H.
  - apply tp2_zero.
  - apply tp2_prod. exact IHTP2. now apply (TP1_mono Du). now apply (TP1_mono Dv).
  - apply (tp2_ext Du' Dv' F G H). exact IHTP2.
Qed.

Lemma TP2_single :
  forall Du Dv f g, TP1 Du f -> TP1 Dv g -> TP2 Du Dv (fun u v => f u * g v).
Proof.
  intros Du Dv f g Hf Hg.
  apply (tp2_ext Du Dv (fun u v => 0 + f u * g v)). intros u v. ring.
  apply tp2_prod. apply tp2_zero. exact Hf. exact Hg.
Qed.

Lemma TP2_const : forall Du Dv c, TP2 Du Dv (fun _ _ => c).
Proof.
  intros Du Dv c.
  apply (tp2_ext Du Dv (fun u v => (fun _ => c) u * (fun _ => 1) v)).
  intros u v. ring.
  apply TP2_single; apply TP1_const.
Qed.

Lemma TP2_add :
  forall Du Dv F G, TP2 Du Dv F -> TP2 Du Dv G -> TP2 Du Dv (fun u v => F u v + G u v).
Proof.
  intros Du Dv F G HF HG. induction HG.
  - apply (tp2_ext Du Dv F). intros u v. ring. exact HF.
  - apply (tp2_ext Du Dv (fun u v => (F u v + F0 u v) + f u * g v)).
    + intros u v. ring.
    + apply tp2_prod; assumption.
  - apply (tp2_ext Du Dv (fun u v => F u v + F0 u v)).
    + intros u v. now rewrite H.
    + exact IHHG.
Qed.

Lemma TP2_scal : forall Du Dv a F, TP2 Du Dv F -> TP2 Du Dv (fun u v => a * F u v).
Proof.
  intros Du Dv a F HF. induction HF.
  - apply (tp2_ext Du Dv (fun _ _ => 0)). intros u v. ring. apply tp2_zero.
  - apply (tp2_ext Du Dv (fun u v => a * F u v + (fun x => a * f x) u * g v)).
    + intros u v. ring.
    + apply tp2_prod. exact IHHF. now apply TP1_scal. exact H0.
  - apply (tp2_ext Du Dv (fun u v => a * F u v)).
    + intros u v. now rewrite H.
    + exact IHHF.
Qed.

Lemma TP2_sub :
  forall Du Dv F G, TP2 Du Dv F -> TP2 Du Dv G -> TP2 Du Dv (fun u v => F u v - G u v).
Proof.
  intros Du Dv F G HF HG.
  apply (tp2_ext Du Dv (fun u v => F u v + (-1) * G u v)). intros u v. ring.
  apply TP2_add. exact HF. now apply TP2_scal.
Qed.

(** A product term times a polynomial in two angles. *)
Lemma TP2_single_mul :
  forall Du Dv Eu Ev f g G,
  TP1 Du f -> TP1 Dv g -> TP2 Eu Ev G ->
  TP2 (Du + Eu) (Dv + Ev) (fun u v => f u * g v * G u v).
Proof.
  intros Du Dv Eu Ev f g G Hf Hg HG. induction HG.
  - apply (tp2_ext _ _ (fun _ _ => 0)). intros u v. ring. apply tp2_zero.
  - apply (tp2_ext _ _ (fun u v => f u * g v * F u v
                                   + (fun x => f x * f0 x) u * (fun y => g y * g0 y) v)).
    + intros u v. ring.
    + apply tp2_prod. exact IHHG. now apply TP1_mul. now apply TP1_mul.
  - apply (tp2_ext _ _ (fun u v => f u * g v * F u v)).
    + intros u v. now rewrite H.
    + exact IHHG.
Qed.

Lemma TP2_mul :
  forall Du Dv Eu Ev F G, TP2 Du Dv F -> TP2 Eu Ev G ->
  TP2 (Du + Eu) (Dv + Ev) (fun u v => F u v * G u v).
Proof.
  intros Du Dv Eu Ev F G HF HG. induction HF.
  - apply (tp2_ext _ _ (fun _ _ => 0)). intros u v. ring. apply tp2_zero.
  - apply (tp2_ext _ _ (fun u v => F u v * G u v + f u * g v * G u v)).
    + intros u v. ring.
    + apply TP2_add. exact IHHF. now apply TP2_single_mul.
  - apply (tp2_ext _ _ (fun u v => F u v * G u v)).
    + intros u v. now rewrite H.
    + exact IHHF.
Qed.

(** The kernels cos(m u - n v) and sin(m u - n v). *)
Lemma TP2_cos_kernel :
  forall m n,
  TP2 (Z.abs_nat m) (Z.abs_nat n) (fun u v => cos (IZR m * u - IZR n * v)).
Proof.
  intros m n.
  apply (tp2_ext _ _ (fun u v => cos (IZR m * u + 0) * cos (IZR n * v + 0)
                                 + sin (IZR m * u + 0) * sin (IZR n * v + 0))).
  - intros u v. rewrite !Rplus_0_r. rewrite cos_minus. ring.
  - apply TP2_add; apply TP2_single;
      first [apply TP1_cos_int | apply TP1_sin_int].
Qed.

Lemma TP2_sin_kernel :
  forall m n,
  TP2 (Z.abs_nat m) (Z.abs_nat n) (fun u v => sin (IZR m * u - IZR n * v)).
Proof.
  intros m n.
  apply (tp2_ext _ _ (fun u v => sin (IZR m * u + 0) * cos (IZR n * v + 0)
                                 + (-1) * (cos (IZR m * u + 0) * sin (IZR n * v + 0)))).
  - intros u v. rewrite !Rplus_0_r. rewrite sin_minus. ring.
  - apply TP2_add. apply TP2_single; first [apply TP1_cos_int | apply TP1_sin_int].
    apply TP2_scal. apply TP2_single; first [apply TP1_cos_int | apply TP1_sin_int].
Qed.

(** For each fixed v a polynomial in u, and the u-integral over a period a
    polynomial in v. *)
Lemma TP2_slice : forall Du Dv F, TP2 Du Dv F -> forall v, TP1 Du (fun u => F u v).
Proof.
  intros Du Dv F HF v. induction HF.
  - apply tp1_zero.
  - apply TP1_add. exact IHHF.
    apply (tp1_ext Du (fun u => g v * f u)). intros u. ring.
    now apply TP1_scal.
  - apply (tp1_ext Du (fun u => F u v)). intros u. apply H. exact IHHF.
Qed.

Lemma TP2_inner :
  forall Du Dv F a, TP2 Du Dv F ->
  TP1 Dv (fun v => RInt (fun u => F u v) a (a + 2 * PI)).
Proof.
  intros Du Dv F a HF. induction HF.
  - apply (tp1_ext Dv (fun _ => 0)).
    + intros v. cbv beta. rewrite RInt_const_R. to_R. ring.
    + apply tp1_zero.
  - apply (tp1_ext Dv (fun v => RInt (fun u => F u v) a (a + 2 * PI)
                               + RInt f a (a + 2 * PI) * g v)).
    + intros v.
      assert (E1 := TP1_ex_RInt Du _ a (a + 2 * PI) (TP2_slice Du Dv F HF v)).
      assert (E2 := TP1_ex_RInt Du f a (a + 2 * PI) H).
      assert (E3 : ex_RInt (fun u => f u * g v) a (a + 2 * PI)).
      { apply (TP1_ex_RInt Du). apply (tp1_ext Du (fun u => g v * f u)).
        intros u; ring. now apply TP1_scal. }
      rewrite (RInt_plus_R (fun u => F u v) (fun u => f u * g v)) by assumption.
      rewrite (RInt_ext (fun u => f u * g v) (fun u => g v * f u))
        by (intros x _; to_R; ring).
      rewrite (RInt_scal_R f) by assumption. to_R. ring.
    + apply TP1_add. exact IHHF.
      apply (tp1_ext Dv (fun v => RInt f a (a + 2 * PI) * g v)). intros v. ring.
      now apply TP1_scal.
  - apply (tp1_ext Dv (fun v => RInt (fun u => F u v) a (a + 2 * PI))).
    + intros v. apply RInt_ext. intros x _. apply H.
    + exact IHHF.
Qed.

(** The double rule: N_u points in u at each of N_v points in v. *)
Definition dsum2 (Nu Nv : nat) (au av : R) (F : R -> R -> R) : R :=
  dsum1 Nv av (fun v => dsum1 Nu au (fun u => F u v)).

(** The iterated integral over the torus of a polynomial of degree below the
    point counts is the double sum, and it exists. *)
Theorem exact2 :
  forall Du Dv Nu Nv au av F, TP2 Du Dv F -> (Du < Nu)%nat -> (Dv < Nv)%nat ->
  ex_RInt (fun v => RInt (fun u => F u v) au (au + 2 * PI)) av (av + 2 * PI) /\
  RInt (fun v => RInt (fun u => F u v) au (au + 2 * PI)) av (av + 2 * PI)
  = dsum2 Nu Nv au av F.
Proof.
  intros Du Dv Nu Nv au av F HF Hu Hv.
  assert (Hin := TP2_inner Du Dv F au HF).
  split. exact (TP1_ex_RInt Dv _ av (av + 2 * PI) Hin).
  rewrite (exact1 Dv Nv av _ Hin Hv).
  unfold dsum2. unfold dsum1 at 1 2. f_equal. apply rsum_ext. intros l. cbv beta.
  exact (exact1 Du Nu au _ (TP2_slice Du Dv F HF (node Nv av l)) Hu).
Qed.
