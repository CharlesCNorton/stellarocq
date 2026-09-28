(** Enclosure arithmetic over intervals of binary64 floats.

    The module [FI] implements KFix.RI with CoqInterval's intervals over
    primitive floats: [inR X x] says that the interval X contains the real x,
    every operation is the interval operation of CoqInterval at binary64,
    and each axiom of RI follows from that operation's correctness theorem.
    [of_q m s] divides the interval of m by that of 2^s. A test of sign is
    CoqInterval's sign test, [incl X Y] is its subset test with the roles as
    RI names them, and [join] is its hull, which holds every number between
    two it holds because intervals are connected. So every check written over
    RI, the coil-field enclosures of KJet.v among them, runs on hardware
    floats. The module also exposes the cosine, the sine and pi of
    CoqInterval, with their correctness, for checks that need them. *)

From Coq Require Import ZArith Reals Lra Lia.
From Interval Require Import Float.Primitive_ops Real.Xreal Interval.Interval Interval.Float_full.
From Stellarocq Require Import KFix.
Local Open Scope R_scope.

Module FI <: RI.

Module F := PrimitiveFloat.
Module I := FloatIntervalFull F.

Definition prec : F.precision := F.PtoP 53.

Definition t : Type := I.type.
Definition inR (X : t) (x : R) : Prop := contains (I.convert X) (Xreal x).

Definition zero : t := I.zero.
Definition add (X Y : t) : t := I.add prec X Y.
Definition sub (X Y : t) : t := I.sub prec X Y.
Definition mul (X Y : t) : t := I.mul prec X Y.
Definition div (X Y : t) : t := I.div prec X Y.
Definition neg (X : t) : t := I.neg X.
Definition abs (X : t) : t := I.abs X.
Definition sqrt (X : t) : t := I.sqrt prec X.
Definition of_q (m s : Z) : t := I.div prec (I.fromZ prec m) (I.fromZ prec (2 ^ s)).
Definition nonneg (X : t) : bool := match I.sign_large X with Xgt | Xeq => true | _ => false end.
Definition pos (X : t) : bool := match I.sign_strict X with Xgt => true | _ => false end.
Definition incl (X Y : t) : bool := I.subset Y X.
Definition join (X Y : t) : t := I.join X Y.

Lemma zero_ok : inR zero 0.
Proof. unfold inR, zero. rewrite I.zero_correct. cbn. lra. Qed.

Lemma add_ok : forall X Y x y, inR X x -> inR Y y -> inR (add X Y) (x + y).
Proof. intros X Y x y HX HY. exact (I.add_correct prec X Y (Xreal x) (Xreal y) HX HY). Qed.

Lemma sub_ok : forall X Y x y, inR X x -> inR Y y -> inR (sub X Y) (x - y).
Proof. intros X Y x y HX HY. exact (I.sub_correct prec X Y (Xreal x) (Xreal y) HX HY). Qed.

Lemma mul_ok : forall X Y x y, inR X x -> inR Y y -> inR (mul X Y) (x * y).
Proof. intros X Y x y HX HY. exact (I.mul_correct prec X Y (Xreal x) (Xreal y) HX HY). Qed.

Lemma div_ok : forall X Y x y, inR X x -> inR Y y -> y <> 0 -> inR (div X Y) (x / y).
Proof.
  intros X Y x y HX HY Hy. pose proof (I.div_correct prec X Y (Xreal x) (Xreal y) HX HY) as H.
  unfold inR, div. revert H. cbn. unfold Xdiv'. generalize (is_zero_spec y). case (is_zero y); intros Hz H.
  - inversion Hz. contradiction.
  - exact H.
Qed.

Lemma neg_ok : forall X x, inR X x -> inR (neg X) (- x).
Proof. intros X x HX. exact (I.neg_correct X (Xreal x) HX). Qed.

Lemma abs_ok : forall X x, inR X x -> inR (abs X) (Rabs x).
Proof. intros X x HX. exact (I.abs_correct X (Xreal x) HX). Qed.

Lemma sqrt_ok : forall X x, inR X x -> 0 <= x -> inR (sqrt X) (R_sqrt.sqrt x).
Proof.
  intros X x HX Hx. pose proof (I.sqrt_correct prec X (Xreal x) HX) as H.
  unfold inR, sqrt. revert H. cbn. generalize (is_negative_spec x). case (is_negative x); intros Hn H.
  - inversion Hn. lra.
  - exact H.
Qed.

Lemma of_q_ok : forall m s, (0 <= s)%Z -> inR (of_q m s) (IZR m / IZR (2 ^ s)).
Proof.
  intros m s Hs. apply div_ok; [apply I.fromZ_correct | apply I.fromZ_correct |].
  apply not_0_IZR. apply Z.pow_nonzero; lia.
Qed.

Lemma nonneg_ok : forall X x, nonneg X = true -> inR X x -> 0 <= x.
Proof.
  intros X x H HX. unfold nonneg in H. pose proof (I.sign_large_correct X) as C.
  destruct (I.sign_large X); try discriminate.
  - specialize (C _ HX). injection C as C. lra.
  - destruct (C _ HX) as [_ C']. exact C'.
Qed.

Lemma pos_ok : forall X x, pos X = true -> inR X x -> 0 < x.
Proof.
  intros X x H HX. unfold pos in H. pose proof (I.sign_strict_correct X) as C.
  destruct (I.sign_strict X); try discriminate.
  destruct (C _ HX) as [_ C']. exact C'.
Qed.

Lemma incl_ok : forall X Y x, incl X Y = true -> inR Y x -> inR X x.
Proof. intros X Y x H HY. exact (I.subset_correct Y X (Xreal x) HY H). Qed.

Lemma join_ok : forall X Y x y z, inR X x -> inR Y y -> x <= z <= y -> inR (join X Y) z.
Proof.
  intros X Y x y z HX HY Hz.
  apply (contains_connected (I.convert (join X Y)) x y).
  - apply I.join_correct. left. exact HX.
  - apply I.join_correct. right. exact HY.
  - exact Hz.
Qed.

(** * Beyond RI *)

Definition cos (X : t) : t := I.cos prec X.
Definition sin (X : t) : t := I.sin prec X.
Definition pi : t := I.pi prec.

Lemma cos_ok : forall X x, inR X x -> inR (cos X) (Rtrigo_def.cos x).
Proof. intros X x HX. exact (I.cos_correct prec X (Xreal x) HX). Qed.

Lemma sin_ok : forall X x, inR X x -> inR (sin X) (Rtrigo_def.sin x).
Proof. intros X x HX. exact (I.sin_correct prec X (Xreal x) HX). Qed.

Lemma pi_ok : inR pi PI.
Proof. exact (I.pi_correct prec). Qed.

End FI.
