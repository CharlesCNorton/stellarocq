(** Landreman's equilibria with iota = 2 are exact solutions of ideal MHD.

    Landreman (arXiv:2609.26742, section 2) gives, for 0 < eps < 1,
    a = sqrt(1 + eps) and b = sqrt(1 - eps), the field

      B = ((2 z x - (a/b) F y) / s, (2 z y + (b/a) F x) / s, 1 - s),
      s = x^2 / a^2 + y^2 / b^2,   F = sqrt(1 - (1 - s)^2 - 4 z^2),

    the flux label psi = (x^2 + y^2 + 4 z^2 + |B|^2 - 2 + eps^2) / 4 and the
    pressure p = p_a - 2 psi, in units with mu0 = 1. The field is the image
    A B0(A^-1 x), A = diag(a, b, 1), of an axisymmetric Solov'ev field, and
    nothing below uses more of a and b than that they are positive.

    Where the radicand of F is positive the field is smooth, and there, with
    every partial derivative the derivative of the function along that axis,
    this file proves

      [iota2_divergence]   div B = 0,
      [iota2_accel]        B . grad B = -(x, y, 4 z),
      [iota2_force]        (curl B) x B = grad p,
      [iota2_tangent]      B . grad p = 0,

    so that B and p are an ideal-MHD equilibrium whose field lines lie on the
    level sets of p, which are those of psi. *)

From Stdlib Require Import Reals Lra Psatz RNsatz.
From Coquelicot Require Import Coquelicot.

Local Open Scope R_scope.

Section Iota2.

Variables a b : R.
Hypothesis Ha : 0 < a.
Hypothesis Hb : 0 < b.

Definition sL (x y : R) : R := x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2.
Definition radL (x y z : R) : R := 1 - (1 - sL x y) ^ 2 - 4 * z ^ 2.
Definition FL (x y z : R) : R := sqrt (radL x y z).

Definition B1 (x y z : R) : R := (2 * z * x - a / b * FL x y z * y) / sL x y.
Definition B2 (x y z : R) : R := (2 * z * y + b / a * FL x y z * x) / sL x y.
Definition B3 (x y z : R) : R := 1 - sL x y.

(** Landreman's psi, with eps = (a^2 - b^2) / 2, and the pressure. *)
Definition psiL (x y z : R) : R :=
  (x ^ 2 + y ^ 2 + 4 * z ^ 2
   + (B1 x y z ^ 2 + B2 x y z ^ 2 + B3 x y z ^ 2)
   - 2 + ((a ^ 2 - b ^ 2) / 2) ^ 2) / 4.

Definition presL (pa x y z : R) : R := pa - 2 * psiL x y z.

(** Partial derivatives along the three Cartesian axes. *)
Definition pd1 (f : R -> R -> R -> R) (x y z : R) : R := Derive (fun t => f t y z) x.
Definition pd2 (f : R -> R -> R -> R) (x y z : R) : R := Derive (fun t => f x t z) y.
Definition pd3 (f : R -> R -> R -> R) (x y z : R) : R := Derive (fun t => f x y t) z.

(* ---------------------------------------------------------------- *)
(* The domain                                                        *)

Lemma a_nz : a <> 0. Proof. apply Rgt_not_eq. exact Ha. Qed.
Lemma b_nz : b <> 0. Proof. apply Rgt_not_eq. exact Hb. Qed.

Lemma sL_pos : forall x y z, 0 < radL x y z -> 0 < sL x y.
Proof.
  intros x y z H. unfold radL in H.
  assert (Hs : 0 <= sL x y).
  { unfold sL. assert (0 < a ^ 2) by (apply pow_lt; lra).
    assert (0 < b ^ 2) by (apply pow_lt; lra).
    assert (0 <= x ^ 2 / a ^ 2) by (apply Rdiv_le_0_compat; [nra | lra]).
    assert (0 <= y ^ 2 / b ^ 2) by (apply Rdiv_le_0_compat; [nra | lra]).
    lra. }
  destruct (Req_dec (sL x y) 0) as [H0 | H0].
  - rewrite H0 in H. nra.
  - lra.
Qed.

Lemma FL_pos : forall x y z, 0 < radL x y z -> 0 < FL x y z.
Proof. intros x y z H. unfold FL. apply sqrt_lt_R0. exact H. Qed.

Lemma FL_sq : forall x y z, 0 < radL x y z -> FL x y z * FL x y z = radL x y z.
Proof. intros x y z H. unfold FL. apply sqrt_sqrt. lra. Qed.

Lemma sL_rel : forall x y, sL x y * a ^ 2 * b ^ 2 = x ^ 2 * b ^ 2 + y ^ 2 * a ^ 2.
Proof.
  intros x y. unfold sL. field. split; [exact b_nz | exact a_nz].
Qed.

(* ---------------------------------------------------------------- *)
(* The partial derivatives                                           *)

Definition s1 (x : R) : R := 2 * x / a ^ 2.
Definition s2 (y : R) : R := 2 * y / b ^ 2.
Definition F1 (x y z : R) : R := (1 - sL x y) * s1 x / FL x y z.
Definition F2 (x y z : R) : R := (1 - sL x y) * s2 y / FL x y z.
Definition F3 (x y z : R) : R := - 4 * z / FL x y z.

Definition d1B1 x y z :=
  ((2 * z - a / b * F1 x y z * y) * sL x y - (2 * z * x - a / b * FL x y z * y) * s1 x)
  / sL x y ^ 2.
Definition d2B1 x y z :=
  ((- (a / b) * (F2 x y z * y + FL x y z)) * sL x y
   - (2 * z * x - a / b * FL x y z * y) * s2 y) / sL x y ^ 2.
Definition d3B1 x y z := (2 * x - a / b * F3 x y z * y) / sL x y.
Definition d1B2 x y z :=
  ((b / a * (F1 x y z * x + FL x y z)) * sL x y
   - (2 * z * y + b / a * FL x y z * x) * s1 x) / sL x y ^ 2.
Definition d2B2 x y z :=
  ((2 * z + b / a * F2 x y z * x) * sL x y - (2 * z * y + b / a * FL x y z * x) * s2 y)
  / sL x y ^ 2.
Definition d3B2 x y z := (2 * y + b / a * F3 x y z * x) / sL x y.
Definition d1B3 (x y z : R) := - s1 x.
Definition d2B3 (x y z : R) := - s2 y.
Definition d3B3 (x y z : R) : R := 0.

Lemma der_s1 : forall x y, is_derive (fun t => sL t y) x (s1 x).
Proof.
  intros x y. unfold sL, s1. auto_derive; [exact I |].
  field. exact a_nz.
Qed.

Lemma der_s2 : forall x y, is_derive (fun t => sL x t) y (s2 y).
Proof.
  intros x y. unfold sL, s2. auto_derive; [exact I |].
  field. exact b_nz.
Qed.

Lemma Der_s1 : forall x y, Derive (fun t => sL t y) x = s1 x.
Proof. intros x y. apply is_derive_unique, der_s1. Qed.

Lemma Der_s2 : forall x y, Derive (fun t => sL x t) y = s2 y.
Proof. intros x y. apply is_derive_unique, der_s2. Qed.

Ltac nzero :=
  repeat split;
  try assumption;
  try (apply Rgt_not_eq; assumption);
  try (apply Rgt_not_eq; lra);
  try exact a_nz; try exact b_nz.

(** Rewrite every radicand auto_derive writes back to [radL x y z]. *)
Ltac canon x y z :=
  repeat match goal with
  | |- context [sqrt ?A] =>
      lazymatch A with
      | radL _ _ _ => fail
      | _ => replace A with (radL x y z) by (unfold radL; ring)
      end
  end.

Ltac derB x y z H :=
  let Hs := fresh "Hs" in let HF := fresh "HF" in
  let Hs0 := fresh "Hs0" in let HF0 := fresh "HF0" in
  pose proof (sL_pos x y z H) as Hs; pose proof (FL_pos x y z H) as HF;
  assert (Hs0 : sL x y <> 0) by (apply Rgt_not_eq; exact Hs);
  assert (HF0 : sqrt (radL x y z) <> 0) by (apply Rgt_not_eq; exact HF);
  unfold B1, B2, B3, d1B1, d2B1, d3B1, d1B2, d2B2, d3B2, d1B3, d2B3, d3B3,
         F1, F2, F3, FL, radL;
  auto_derive;
  [ repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- True => exact I
    | |- sL _ _ <> 0 => exact Hs0
    | |- ex_derive (fun t => sL t _) _ => exists (s1 x); exact (der_s1 x y)
    | |- ex_derive (fun t => sL _ t) _ => exists (s2 y); exact (der_s2 x y)
    | |- 0 < ?e => replace e with (radL x y z) by (unfold radL; ring); exact H
    end
  | rewrite ?(Der_s1 x y), ?(Der_s2 x y);
    canon x y z; unfold s1, s2; field; nzero ].

Lemma der1B1 : forall x y z, 0 < radL x y z -> is_derive (fun t => B1 t y z) x (d1B1 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der2B1 : forall x y z, 0 < radL x y z -> is_derive (fun t => B1 x t z) y (d2B1 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der3B1 : forall x y z, 0 < radL x y z -> is_derive (fun t => B1 x y t) z (d3B1 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der1B2 : forall x y z, 0 < radL x y z -> is_derive (fun t => B2 t y z) x (d1B2 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der2B2 : forall x y z, 0 < radL x y z -> is_derive (fun t => B2 x t z) y (d2B2 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der3B2 : forall x y z, 0 < radL x y z -> is_derive (fun t => B2 x y t) z (d3B2 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der1B3 : forall x y z, 0 < radL x y z -> is_derive (fun t => B3 t y z) x (d1B3 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der2B3 : forall x y z, 0 < radL x y z -> is_derive (fun t => B3 x t z) y (d2B3 x y z).
Proof. intros x y z H. derB x y z H. Qed.
Lemma der3B3 : forall x y z, 0 < radL x y z -> is_derive (fun t => B3 x y t) z (d3B3 x y z).
Proof. intros x y z H. derB x y z H. Qed.

(** The partial derivatives are the formulas above. *)
Lemma pd_B : forall x y z, 0 < radL x y z ->
  pd1 B1 x y z = d1B1 x y z /\ pd2 B1 x y z = d2B1 x y z /\ pd3 B1 x y z = d3B1 x y z /\
  pd1 B2 x y z = d1B2 x y z /\ pd2 B2 x y z = d2B2 x y z /\ pd3 B2 x y z = d3B2 x y z /\
  pd1 B3 x y z = d1B3 x y z /\ pd2 B3 x y z = d2B3 x y z /\ pd3 B3 x y z = d3B3 x y z.
Proof.
  intros x y z H. unfold pd1, pd2, pd3.
  split. apply is_derive_unique, der1B1, H.
  split. apply is_derive_unique, der2B1, H.
  split. apply is_derive_unique, der3B1, H.
  split. apply is_derive_unique, der1B2, H.
  split. apply is_derive_unique, der2B2, H.
  split. apply is_derive_unique, der3B2, H.
  split. apply is_derive_unique, der1B3, H.
  split. apply is_derive_unique, der2B3, H.
  apply is_derive_unique, der3B3, H.
Qed.

(* ---------------------------------------------------------------- *)
(* The identities                                                    *)

(** a^2 b^2 s, the denominator [field] leaves once s is unfolded. *)
Lemma den_pos : forall x y, 0 < sL x y -> (x * b) ^ 2 + (y * a) ^ 2 <> 0.
Proof.
  intros x y Hs. apply Rgt_not_eq. unfold sL in Hs.
  replace ((x * b) ^ 2 + (y * a) ^ 2) with (a ^ 2 * b ^ 2 * (x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2))
    by (field; split; [exact b_nz | exact a_nz]).
  apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; apply pow_lt; lra | exact Hs].
Qed.

(** The two relations the atoms F = FL x y z and s = sL x y satisfy: F^2 is
    the radicand, and s a^2 b^2 is the polynomial x^2 b^2 + y^2 a^2. *)
Ltac atoms x y z H :=
  let HF2 := fresh "HF2" in let HS := fresh "HS" in
  let Hs := fresh "Hs" in let HF := fresh "HF" in
  pose proof (sL_pos x y z H) as Hs; pose proof (FL_pos x y z H) as HF;
  pose proof (FL_sq x y z H) as HF2; pose proof (sL_rel x y) as HS;
  unfold radL in HF2.

Theorem iota2_divergence : forall x y z, 0 < radL x y z ->
  pd1 B1 x y z + pd2 B2 x y z + pd3 B3 x y z = 0.
Proof.
  intros x y z H.
  destruct (pd_B x y z H) as (E11 & _ & _ & _ & E22 & _ & _ & _ & E33).
  rewrite E11, E22, E33.
  pose proof (sL_pos x y z H) as Hs. pose proof (FL_pos x y z H) as HF.
  assert (Sz : sL x y <> 0) by lra. assert (Fz : FL x y z <> 0) by lra.
  unfold d1B1, d2B2, d3B3, F1, F2, s1, s2.
  unfold sL in *.
  field. repeat split; try assumption; try exact a_nz; try exact b_nz.
  apply den_pos. exact Hs.
Qed.

Lemma den_pos' : forall x y, 0 < sL x y -> (a * y) ^ 2 + (b * x) ^ 2 <> 0.
Proof.
  intros x y Hs. replace ((a * y) ^ 2 + (b * x) ^ 2) with ((x * b) ^ 2 + (y * a) ^ 2)
    by ring.
  apply den_pos. exact Hs.
Qed.

Ltac nzs Hs :=
  repeat split; try assumption; try exact a_nz; try exact b_nz;
  try (apply den_pos; exact Hs); try (apply den_pos'; exact Hs).

(** Each identity is its left side less its right side equal to a cofactor
    times F^2 - radicand, which [field] checks with F an atom, and which the
    radicand then makes zero. *)
Lemma accel1 : forall x y z, 0 < radL x y z ->
  B1 x y z * d1B1 x y z + B2 x y z * d2B1 x y z + B3 x y z * d3B1 x y z = - x.
Proof.
  intros x y z H.
  pose proof (sL_pos x y z H) as Hs. pose proof (FL_pos x y z H) as HF.
  pose proof (FL_sq x y z H) as HF2.
  assert (Fz : FL x y z <> 0) by lra.
  assert (E : B1 x y z * d1B1 x y z + B2 x y z * d2B1 x y z + B3 x y z * d3B1 x y z + x
              = - a ^ 4 * b ^ 4 * x / (a ^ 2 * y ^ 2 + b ^ 2 * x ^ 2) ^ 2
                * (FL x y z * FL x y z - radL x y z)).
  { unfold B1, B2, B3, d1B1, d2B1, d3B1, F1, F2, F3, s1, s2, radL.
    unfold sL in *. field. nzs Hs. }
  rewrite HF2 in E. replace (radL x y z - radL x y z) with 0 in E by ring.
  rewrite Rmult_0_r in E. lra.
Qed.

Lemma accel2 : forall x y z, 0 < radL x y z ->
  B1 x y z * d1B2 x y z + B2 x y z * d2B2 x y z + B3 x y z * d3B2 x y z = - y.
Proof.
  intros x y z H.
  pose proof (sL_pos x y z H) as Hs. pose proof (FL_pos x y z H) as HF.
  pose proof (FL_sq x y z H) as HF2.
  assert (Fz : FL x y z <> 0) by lra.
  assert (E : B1 x y z * d1B2 x y z + B2 x y z * d2B2 x y z + B3 x y z * d3B2 x y z + y
              = - a ^ 4 * b ^ 4 * y / (a ^ 2 * y ^ 2 + b ^ 2 * x ^ 2) ^ 2
                * (FL x y z * FL x y z - radL x y z)).
  { unfold B1, B2, B3, d1B2, d2B2, d3B2, F1, F2, F3, s1, s2, radL.
    unfold sL in *. field. nzs Hs. }
  rewrite HF2 in E. replace (radL x y z - radL x y z) with 0 in E by ring.
  rewrite Rmult_0_r in E. lra.
Qed.

Lemma accel3 : forall x y z, 0 < radL x y z ->
  B1 x y z * d1B3 x y z + B2 x y z * d2B3 x y z + B3 x y z * d3B3 x y z = - (4 * z).
Proof.
  intros x y z H.
  pose proof (sL_pos x y z H) as Hs. pose proof (FL_pos x y z H) as HF.
  assert (Fz : FL x y z <> 0) by lra.
  unfold B1, B2, B3, d1B3, d2B3, d3B3, s1, s2.
  unfold sL in *. field. nzs Hs.
Qed.

(** B . grad B = -(x, y, 4 z), with every derivative the partial derivative
    of the component along its axis. *)
Theorem iota2_accel : forall x y z, 0 < radL x y z ->
  B1 x y z * pd1 B1 x y z + B2 x y z * pd2 B1 x y z + B3 x y z * pd3 B1 x y z = - x /\
  B1 x y z * pd1 B2 x y z + B2 x y z * pd2 B2 x y z + B3 x y z * pd3 B2 x y z = - y /\
  B1 x y z * pd1 B3 x y z + B2 x y z * pd2 B3 x y z + B3 x y z * pd3 B3 x y z = - (4 * z).
Proof.
  intros x y z H.
  destruct (pd_B x y z H) as (E11 & E21 & E31 & E12 & E22 & E32 & E13 & E23 & E33).
  rewrite E11, E21, E31, E12, E22, E32, E13, E23, E33.
  split; [| split]; [apply accel1 | apply accel2 | apply accel3]; exact H.
Qed.

(* ---------------------------------------------------------------- *)
(* The pressure                                                      *)

(** The gradient of p = p_a - 2 psi: with psi = (x^2 + y^2 + 4 z^2 + |B|^2
    - 2 + eps^2) / 4, its components are -(x + B . d_x B) and so on. *)
Definition gp1 x y z := - (x + (B1 x y z * d1B1 x y z + B2 x y z * d1B2 x y z
                                + B3 x y z * d1B3 x y z)).
Definition gp2 x y z := - (y + (B1 x y z * d2B1 x y z + B2 x y z * d2B2 x y z
                                + B3 x y z * d2B3 x y z)).
Definition gp3 x y z := - (4 * z + (B1 x y z * d3B1 x y z + B2 x y z * d3B2 x y z
                                    + B3 x y z * d3B3 x y z)).

Ltac derP x y z H :=
  unfold presL, psiL;
  auto_derive;
  [ repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- True => exact I
    | |- ex_derive (fun t => B1 t _ _) _ => exists (d1B1 x y z); exact (der1B1 x y z H)
    | |- ex_derive (fun t => B2 t _ _) _ => exists (d1B2 x y z); exact (der1B2 x y z H)
    | |- ex_derive (fun t => B3 t _ _) _ => exists (d1B3 x y z); exact (der1B3 x y z H)
    | |- ex_derive (fun t => B1 _ t _) _ => exists (d2B1 x y z); exact (der2B1 x y z H)
    | |- ex_derive (fun t => B2 _ t _) _ => exists (d2B2 x y z); exact (der2B2 x y z H)
    | |- ex_derive (fun t => B3 _ t _) _ => exists (d2B3 x y z); exact (der2B3 x y z H)
    | |- ex_derive (fun t => B1 _ _ t) _ => exists (d3B1 x y z); exact (der3B1 x y z H)
    | |- ex_derive (fun t => B2 _ _ t) _ => exists (d3B2 x y z); exact (der3B2 x y z H)
    | |- ex_derive (fun t => B3 _ _ t) _ => exists (d3B3 x y z); exact (der3B3 x y z H)
    end
  | destruct (pd_B x y z H) as (E11 & E21 & E31 & E12 & E22 & E32 & E13 & E23 & E33);
    unfold pd1, pd2, pd3 in *;
    rewrite ?E11, ?E21, ?E31, ?E12, ?E22, ?E32, ?E13, ?E23, ?E33;
    unfold gp1, gp2, gp3; field ].

Lemma der1P : forall pa x y z, 0 < radL x y z ->
  is_derive (fun t => presL pa t y z) x (gp1 x y z).
Proof. intros pa x y z H. derP x y z H. Qed.
Lemma der2P : forall pa x y z, 0 < radL x y z ->
  is_derive (fun t => presL pa x t z) y (gp2 x y z).
Proof. intros pa x y z H. derP x y z H. Qed.
Lemma der3P : forall pa x y z, 0 < radL x y z ->
  is_derive (fun t => presL pa x y t) z (gp3 x y z).
Proof. intros pa x y z H. derP x y z H. Qed.

(** Force balance, (curl B) x B = grad p, component by component, the curl
    and the gradient taken from the partial derivatives. *)
Theorem iota2_force : forall pa x y z, 0 < radL x y z ->
  let J1 := pd2 B3 x y z - pd3 B2 x y z in
  let J2 := pd3 B1 x y z - pd1 B3 x y z in
  let J3 := pd1 B2 x y z - pd2 B1 x y z in
  J2 * B3 x y z - J3 * B2 x y z = pd1 (presL pa) x y z /\
  J3 * B1 x y z - J1 * B3 x y z = pd2 (presL pa) x y z /\
  J1 * B2 x y z - J2 * B1 x y z = pd3 (presL pa) x y z.
Proof.
  intros pa x y z H J1 J2 J3.
  pose proof (iota2_accel x y z H) as (A1 & A2 & A3).
  assert (P1 : pd1 (presL pa) x y z = gp1 x y z)
    by (unfold pd1; apply is_derive_unique, der1P, H).
  assert (P2 : pd2 (presL pa) x y z = gp2 x y z)
    by (unfold pd2; apply is_derive_unique, der2P, H).
  assert (P3 : pd3 (presL pa) x y z = gp3 x y z)
    by (unfold pd3; apply is_derive_unique, der3P, H).
  destruct (pd_B x y z H) as (E11 & E21 & E31 & E12 & E22 & E32 & E13 & E23 & E33).
  rewrite P1, P2, P3. unfold J1, J2, J3, gp1, gp2, gp3.
  rewrite E11, E21, E31, E12, E22, E32, E13, E23, E33 in *.
  split; [| split]; nra.
Qed.

(** The field lines lie on the level sets of p = p_a - 2 psi, which are those
    of psi: B . grad p = B . ((curl B) x B) = 0. *)
Theorem iota2_tangent : forall pa x y z, 0 < radL x y z ->
  B1 x y z * pd1 (presL pa) x y z + B2 x y z * pd2 (presL pa) x y z
  + B3 x y z * pd3 (presL pa) x y z = 0.
Proof.
  intros pa x y z H.
  pose proof (iota2_force pa x y z H) as HF. cbv zeta in HF.
  destruct HF as (F1' & F2' & F3').
  rewrite <- F1', <- F2', <- F3'. ring.
Qed.

End Iota2.
