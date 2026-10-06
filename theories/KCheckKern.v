(** Interval enclosures of the coil field, over any enclosure arithmetic.

    [inR X x] says that the interval X contains the real x. Sums, products
    and differences of intervals contain the sums, products and differences
    of what they contain, and quotients and square roots do so where the real
    operation is defined ([inR_add] ... [inR_div], [inR_sqrt]). Over any
    implementation of the operations of [RI] (KFix.v), [ikern] encloses the
    field d x (x - p) / |x - p|^3 of one source once |x - p|^2 is positive
    ([ikern_correct]), and [ifield] encloses the field of a list of sources
    ([ifield_correct]). The module is a functor so that the same enclosures
    run on fixed-point intervals of any precision. *)

From Coq Require Import ZArith Reals Lra List.
From Stellarocq Require Import Hypotheses CoilSym KCheckField Invariance KFix.
Import ListNotations.
Local Open Scope R_scope.

Module KernOps (J : RI).

Definition inR (X : J.t) (x : R) : Prop := J.inR X x.

Lemma inR_add (X Y : J.t) (x y : R) : inR X x -> inR Y y -> inR (J.add X Y) (x + y).
Proof. apply J.add_ok. Qed.

Lemma inR_sub (X Y : J.t) (x y : R) : inR X x -> inR Y y -> inR (J.sub X Y) (x - y).
Proof. apply J.sub_ok. Qed.

Lemma inR_mul (X Y : J.t) (x y : R) : inR X x -> inR Y y -> inR (J.mul X Y) (x * y).
Proof. apply J.mul_ok. Qed.

Lemma inR_neg (X : J.t) (x : R) : inR X x -> inR (J.neg X) (- x).
Proof. apply J.neg_ok. Qed.

Lemma inR_abs (X : J.t) (x : R) : inR X x -> inR (J.abs X) (Rabs x).
Proof. apply J.abs_ok. Qed.

Lemma inR_div (X Y : J.t) (x y : R) : inR X x -> inR Y y -> y <> 0 -> inR (J.div X Y) (x / y).
Proof. apply J.div_ok. Qed.

Lemma inR_sqrt (X : J.t) (x : R) : inR X x -> 0 <= x -> inR (J.sqrt X) (sqrt x).
Proof. apply J.sqrt_ok. Qed.

Lemma inR_zero : inR J.zero 0.
Proof. apply J.zero_ok. Qed.

Lemma inR_q (m s : Z) : (0 <= s)%Z -> inR (J.of_q m s) (IZR m / IZR (2 ^ s)).
Proof. apply J.of_q_ok. Qed.

Lemma inR_Z (m : Z) : inR (J.of_q m 0) (IZR m).
Proof.
  pose proof (inR_q m 0 (Z.le_refl 0)) as H. simpl in H.
  replace (IZR m / 1) with (IZR m) in H by field. exact H.
Qed.

Lemma inR_nonneg (X : J.t) (x : R) : J.nonneg X = true -> inR X x -> 0 <= x.
Proof. apply J.nonneg_ok. Qed.

Lemma inR_pos (X : J.t) (x : R) : J.pos X = true -> inR X x -> 0 < x.
Proof. apply J.pos_ok. Qed.

(** X encloses a number at most the number Y encloses. *)
Definition ile (X Y : J.t) : bool := J.nonneg (J.sub Y X).

Lemma ile_correct (X Y : J.t) (x y : R) : ile X Y = true -> inR X x -> inR Y y -> x <= y.
Proof.
  unfold ile. intros H HX HY. pose proof (inR_nonneg _ _ H (inR_sub _ _ _ _ HY HX)). lra.
Qed.

(** * Triples *)

Definition i3 : Type := (J.t * J.t * J.t)%type.

Definition inR3 (X : i3) (x : vec3) : Prop :=
  let '(X1, X2, X3) := X in let '(x1, x2, x3) := x in inR X1 x1 /\ inR X2 x2 /\ inR X3 x3.

Definition iadd3 (a b : i3) : i3 :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in (J.add a1 b1, J.add a2 b2, J.add a3 b3).

Definition isub3 (a b : i3) : i3 :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in (J.sub a1 b1, J.sub a2 b2, J.sub a3 b3).

Definition idot3 (a b : i3) : J.t :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in J.add (J.add (J.mul a1 b1) (J.mul a2 b2)) (J.mul a3 b3).

Definition icross3 (a b : i3) : i3 :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in
  (J.sub (J.mul a2 b3) (J.mul a3 b2), J.sub (J.mul a3 b1) (J.mul a1 b3), J.sub (J.mul a1 b2) (J.mul a2 b1)).

Lemma inR3_add (A B : i3) (a b : vec3) : inR3 A a -> inR3 B b -> inR3 (iadd3 A B) (v3add a b).
Proof.
  destruct A as [[A1 A2] A3], B as [[B1 B2] B3], a as [[a1 a2] a3], b as [[b1 b2] b3].
  simpl. intros [H1 [H2 H3]] [G1 [G2 G3]]. repeat split; apply inR_add; assumption.
Qed.

Lemma inR3_sub (A B : i3) (a b : vec3) : inR3 A a -> inR3 B b -> inR3 (isub3 A B) (v3sub a b).
Proof.
  destruct A as [[A1 A2] A3], B as [[B1 B2] B3], a as [[a1 a2] a3], b as [[b1 b2] b3].
  simpl. intros [H1 [H2 H3]] [G1 [G2 G3]]. repeat split; apply inR_sub; assumption.
Qed.

Lemma inR_dot3 (A B : i3) (a b : vec3) : inR3 A a -> inR3 B b -> inR (idot3 A B) (dot3 a b).
Proof.
  destruct A as [[A1 A2] A3], B as [[B1 B2] B3], a as [[a1 a2] a3], b as [[b1 b2] b3].
  simpl. intros [H1 [H2 H3]] [G1 [G2 G3]].
  apply inR_add; [apply inR_add |]; apply inR_mul; assumption.
Qed.

Lemma inR3_cross (A B : i3) (a b : vec3) : inR3 A a -> inR3 B b -> inR3 (icross3 A B) (cross3r a b).
Proof.
  destruct A as [[A1 A2] A3], B as [[B1 B2] B3], a as [[a1 a2] a3], b as [[b1 b2] b3].
  simpl. intros [H1 [H2 H3]] [G1 [G2 G3]].
  repeat split; apply inR_sub; apply inR_mul; assumption.
Qed.

(** * The field of one source *)

(** The squared distance, which a check reads to show it positive. *)
Definition iqk (p x : i3) : J.t := let r := isub3 x p in idot3 r r.

(** One quotient by |r|^3 and three products. *)
Definition ikern (p d x : i3) : i3 :=
  let r := isub3 x p in
  let q := idot3 r r in
  let h := J.div (J.of_q 1 0) (J.mul q (J.sqrt q)) in
  let '(c1, c2, c3) := icross3 d r in
  (J.mul c1 h, J.mul c2 h, J.mul c3 h).

Lemma inR_iqk (P X : i3) (p x : vec3) : inR3 P p -> inR3 X x -> inR (iqk P X) (dot3 (v3sub x p) (v3sub x p)).
Proof. intros Hp Hx. unfold iqk. pose proof (inR3_sub X P x p Hx Hp) as Hr. apply inR_dot3; exact Hr. Qed.

Lemma dot3_self_nn (r : vec3) : 0 <= dot3 r r.
Proof. destruct r as [[r1 r2] r3]. simpl. nra. Qed.

Theorem ikern_correct (P D X : i3) (p d x : vec3) :
  inR3 P p -> inR3 D d -> inR3 X x -> 0 < dot3 (v3sub x p) (v3sub x p) ->
  inR3 (ikern P D X) (kern p d x).
Proof.
  intros Hp Hd Hx Hq.
  unfold ikern, kern.
  pose proof (inR3_sub X P x p Hx Hp) as Hr.
  set (r := v3sub x p) in *. set (R3 := isub3 X P) in *.
  pose proof (inR_dot3 R3 R3 r r Hr Hr) as HQ.
  set (q := dot3 r r) in *.
  assert (Hs : inR (J.sqrt (idot3 R3 R3)) (sqrt q)) by (apply inR_sqrt; [exact HQ | lra]).
  assert (Hden : inR (J.mul (idot3 R3 R3) (J.sqrt (idot3 R3 R3))) (q * sqrt q)) by (apply inR_mul; assumption).
  assert (Hq0 : q * sqrt q <> 0).
  { pose proof (sqrt_lt_R0 q Hq). apply Rgt_not_eq. apply Rmult_lt_0_compat; lra. }
  assert (Hh : inR (J.div (J.of_q 1 0) (J.mul (idot3 R3 R3) (J.sqrt (idot3 R3 R3)))) (1 / (q * sqrt q)))
    by (apply inR_div; [apply inR_Z | exact Hden | exact Hq0]).
  assert (Hsn : sqrt q <> 0 /\ q <> 0) by (split; [apply Rgt_not_eq, sqrt_lt_R0, Hq | lra]).
  pose proof (inR3_cross D R3 d r Hd Hr) as Hc.
  destruct (icross3 D R3) as [[C1 C2] C3].
  destruct (cross3r d r) as [[c1 c2] c3].
  simpl in Hc. destruct Hc as [H1 [H2 H3]].
  unfold v3scal. simpl.
  repeat split.
  - replace (/ (q * sqrt q) * c1) with (c1 * (1 / (q * sqrt q))) by (field; exact Hsn).
    apply inR_mul; assumption.
  - replace (/ (q * sqrt q) * c2) with (c2 * (1 / (q * sqrt q))) by (field; exact Hsn).
    apply inR_mul; assumption.
  - replace (/ (q * sqrt q) * c3) with (c3 * (1 / (q * sqrt q))) by (field; exact Hsn).
    apply inR_mul; assumption.
Qed.

(** * The field of a list of sources *)

Definition izero3 : i3 := (J.zero, J.zero, J.zero).

Definition ifield (srcs : list (i3 * i3)) (X : i3) : i3 :=
  fold_right (fun s acc => iadd3 (ikern (fst s) (snd s) X) acc) izero3 srcs.

(** Each interval source contains its real source, and every source lies
    away from the point. *)
Inductive srcs_in (x : vec3) : list (i3 * i3) -> list (vec3 * vec3) -> Prop :=
| srcs_in_nil : srcs_in x [] []
| srcs_in_cons (S : i3 * i3) (s : vec3 * vec3) (Ss : list (i3 * i3)) (ss : list (vec3 * vec3)) :
    inR3 (fst S) (fst s) -> inR3 (snd S) (snd s) ->
    0 < dot3 (v3sub x (fst s)) (v3sub x (fst s)) ->
    srcs_in x Ss ss -> srcs_in x (S :: Ss) (s :: ss).

Theorem ifield_correct (X : i3) (x : vec3) (Ss : list (i3 * i3)) (ss : list (vec3 * vec3)) :
  inR3 X x -> srcs_in x Ss ss -> inR3 (ifield Ss X) (rsum ss x).
Proof.
  intros Hx H. induction H as [| S s Ss ss Hp Hd Hq _ IH].
  - simpl. repeat split; exact inR_zero.
  - cbn [ifield fold_right rsum]. apply inR3_add; [apply ikern_correct; assumption | exact IH].
Qed.

(** * Cylindrical components at a point of a torus

    From enclosures of R, Z, cos phi and sin phi, the point (R cos phi,
    R sin phi, Z) and the cylindrical components of the field of a list of
    sources there. *)

Definition icyl (Rr C S Zz : J.t) : i3 := (J.mul Rr C, J.mul Rr S, Zz).

Definition iBR (B : i3) (C S : J.t) : J.t := let '(B1, B2, _) := B in J.add (J.mul B1 C) (J.mul B2 S).
Definition iBP (B : i3) (C S : J.t) : J.t := let '(B1, B2, _) := B in J.add (J.neg (J.mul B1 S)) (J.mul B2 C).
Definition iBZ (B : i3) : J.t := let '(_, _, B3) := B in B3.

Lemma inR3_cyl (Rr C S Zz : J.t) (R0 phi Z0 : R) :
  inR Rr R0 -> inR C (cos phi) -> inR S (sin phi) -> inR Zz Z0 -> inR3 (icyl Rr C S Zz) (cyl R0 phi Z0).
Proof. intros HR HC HS HZ. unfold icyl, cyl. simpl. repeat split; try apply inR_mul; assumption. Qed.

Theorem icyl_field_correct (Rr C S Zz : J.t) (R0 phi Z0 : R) (Ss : list (i3 * i3)) (ss : list (vec3 * vec3)) :
  inR Rr R0 -> inR C (cos phi) -> inR S (sin phi) -> inR Zz Z0 ->
  srcs_in (cyl R0 phi Z0) Ss ss ->
  let Bi := ifield Ss (icyl Rr C S Zz) in
  inR (iBR Bi C S) (B_R (rsum ss) R0 phi Z0) /\
  inR (iBP Bi C S) (B_phi (rsum ss) R0 phi Z0) /\
  inR (iBZ Bi) (B_Z (rsum ss) R0 phi Z0).
Proof.
  intros HR HC HS HZ Hs Bi.
  pose proof (ifield_correct (icyl Rr C S Zz) (cyl R0 phi Z0) Ss ss
                (inR3_cyl Rr C S Zz R0 phi Z0 HR HC HS HZ) Hs) as HB.
  fold Bi in HB. unfold B_R, B_phi, B_Z.
  destruct Bi as [[B1 B2] B3]. destruct (rsum ss (cyl R0 phi Z0)) as [[b1 b2] b3].
  simpl in HB |- *. destruct HB as [H1 [H2 H3]].
  repeat split.
  - apply inR_add; apply inR_mul; assumption.
  - apply inR_add; [| apply inR_mul; assumption].
    replace (- b1 * sin phi) with (- (b1 * sin phi)) by ring.
    apply inR_neg, inR_mul; assumption.
  - exact H3.
Qed.

End KernOps.
