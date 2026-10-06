(** Enclosures of reals by intervals of fixed-point numbers.

    The checks of the KAM certificate read numbers through an enclosure
    relation [inR X x] and operations that keep it ([RI]): sums, differences,
    products, quotients by numbers away from zero, square roots of
    nonnegative numbers, absolute values, exact dyadic constants, and sign
    tests. [FX] implements it over the integers: an interval is a pair of
    integers (a, b) with a <= x 2^k <= b for a fixed number k of fractional
    bits, or the empty claim [None] when an operation cannot enclose its
    result (a quotient by an interval that meets zero, the root of one that
    reaches below zero). Products and quotients round their endpoints
    outward to the grid 2^-k. Only integer addition, multiplication,
    Euclidean division by a positive integer, shifts and the integer square
    root are used, so the extracted checks run on arbitrary-precision
    integers. *)

From Coq Require Import ZArith Reals Lra Lia.
Local Open Scope R_scope.

Module Type RI.

Parameter t : Type.
Parameter inR : t -> R -> Prop.

Parameter zero : t.
Parameter add sub mul div : t -> t -> t.
Parameter neg abs sqrt : t -> t.
Parameter of_q : Z -> Z -> t.
Parameter nonneg pos : t -> bool.

Axiom zero_ok : inR zero 0.
Axiom add_ok : forall X Y x y, inR X x -> inR Y y -> inR (add X Y) (x + y).
Axiom sub_ok : forall X Y x y, inR X x -> inR Y y -> inR (sub X Y) (x - y).
Axiom mul_ok : forall X Y x y, inR X x -> inR Y y -> inR (mul X Y) (x * y).
Axiom div_ok : forall X Y x y, inR X x -> inR Y y -> y <> 0 -> inR (div X Y) (x / y).
Axiom neg_ok : forall X x, inR X x -> inR (neg X) (- x).
Axiom abs_ok : forall X x, inR X x -> inR (abs X) (Rabs x).
Axiom sqrt_ok : forall X x, inR X x -> 0 <= x -> inR (sqrt X) (R_sqrt.sqrt x).
(** [of_q m s] encloses m / 2^s. *)
Axiom of_q_ok : forall m s, (0 <= s)%Z -> inR (of_q m s) (IZR m / IZR (2 ^ s)).
Axiom nonneg_ok : forall X x, nonneg X = true -> inR X x -> 0 <= x.
Axiom pos_ok : forall X x, pos X = true -> inR X x -> 0 < x.

(** X holds every number Y holds; the enclosure from the lower end of X to
    the upper end of Y. *)
Parameter incl : t -> t -> bool.
Parameter join : t -> t -> t.
Axiom incl_ok : forall X Y x, incl X Y = true -> inR Y x -> inR X x.
Axiom join_ok : forall X Y x y z, inR X x -> inR Y y -> x <= z <= y -> inR (join X Y) z.

End RI.

(** * Fixed-point intervals *)

Module Type Prec.
Parameter k : Z.
Axiom k_nonneg : (0 <= k)%Z.
End Prec.

(** Integer rounding helpers. *)

Lemma p2_pos (s : Z) : (0 <= s)%Z -> (0 < 2 ^ s)%Z.
Proof. intros H. apply Z.pow_pos_nonneg; lia. Qed.

Lemma IZR_p2_pos (s : Z) : (0 <= s)%Z -> 0 < IZR (2 ^ s).
Proof. intros H. apply IZR_lt. apply p2_pos, H. Qed.

(** Floor and ceiling of n / d for d > 0. *)
Definition fdiv (n d : Z) : Z := Z.div n d.
Definition cdiv (n d : Z) : Z := - Z.div (- n) d.

Lemma fdiv_le (n d : Z) : (0 < d)%Z -> IZR (fdiv n d) * IZR d <= IZR n.
Proof.
  intros Hd. unfold fdiv. rewrite <- mult_IZR. apply IZR_le.
  rewrite Z.mul_comm. apply Z.mul_div_le. exact Hd.
Qed.

Lemma cdiv_ge (n d : Z) : (0 < d)%Z -> IZR n <= IZR (cdiv n d) * IZR d.
Proof.
  intros Hd. unfold cdiv. rewrite <- mult_IZR. apply IZR_le.
  pose proof (Z.mul_div_le (- n) d Hd). lia.
Qed.

(** The four products of two intervals bound the product of their points. *)
Lemma prod_between (a b c d x y : R) :
  a <= x <= b -> c <= y <= d ->
  Rmin (Rmin (a * c) (a * d)) (Rmin (b * c) (b * d)) <= x * y <=
  Rmax (Rmax (a * c) (a * d)) (Rmax (b * c) (b * d)).
Proof.
  intros [Hax Hxb] [Hcy Hyd].
  assert (L1 : Rmin (a * y) (b * y) <= x * y <= Rmax (a * y) (b * y)).
  { destruct (Rle_or_lt 0 y) as [Hy | Hy].
    - split; [apply Rle_trans with (a * y); [apply Rmin_l | nra] | apply Rle_trans with (b * y); [nra | apply Rmax_r]].
    - split; [apply Rle_trans with (b * y); [apply Rmin_r | nra] | apply Rle_trans with (a * y); [nra | apply Rmax_l]]. }
  assert (La : Rmin (a * c) (a * d) <= a * y <= Rmax (a * c) (a * d)).
  { destruct (Rle_or_lt 0 a) as [Ha | Ha].
    - split; [apply Rle_trans with (a * c); [apply Rmin_l | nra] | apply Rle_trans with (a * d); [nra | apply Rmax_r]].
    - split; [apply Rle_trans with (a * d); [apply Rmin_r | nra] | apply Rle_trans with (a * c); [nra | apply Rmax_l]]. }
  assert (Lb : Rmin (b * c) (b * d) <= b * y <= Rmax (b * c) (b * d)).
  { destruct (Rle_or_lt 0 b) as [Hb | Hb].
    - split; [apply Rle_trans with (b * c); [apply Rmin_l | nra] | apply Rle_trans with (b * d); [nra | apply Rmax_r]].
    - split; [apply Rle_trans with (b * d); [apply Rmin_r | nra] | apply Rle_trans with (b * c); [nra | apply Rmax_l]]. }
  destruct L1 as [L1l L1u]. destruct La as [Lal Lau]. destruct Lb as [Lbl Lbu].
  split.
  - apply Rle_trans with (Rmin (a * y) (b * y)); [| exact L1l].
    apply Rmin_glb; [apply Rle_trans with (Rmin (a * c) (a * d)); [apply Rmin_l | exact Lal]
                    | apply Rle_trans with (Rmin (b * c) (b * d)); [apply Rmin_r | exact Lbl]].
  - apply Rle_trans with (Rmax (a * y) (b * y)); [exact L1u |].
    apply Rmax_lub; [apply Rle_trans with (Rmax (a * c) (a * d)); [exact Lau | apply Rmax_l]
                    | apply Rle_trans with (Rmax (b * c) (b * d)); [exact Lbu | apply Rmax_r]].
Qed.

Lemma IZR_min (a b : Z) : IZR (Z.min a b) = Rmin (IZR a) (IZR b).
Proof.
  destruct (Z.le_ge_cases a b) as [H | H].
  - rewrite Z.min_l by exact H. rewrite Rmin_left by (apply IZR_le, H). reflexivity.
  - rewrite Z.min_r by lia. rewrite Rmin_right by (apply IZR_le; lia). reflexivity.
Qed.

Lemma IZR_max (a b : Z) : IZR (Z.max a b) = Rmax (IZR a) (IZR b).
Proof.
  destruct (Z.le_ge_cases a b) as [H | H].
  - rewrite Z.max_r by exact H. rewrite Rmax_right by (apply IZR_le, H). reflexivity.
  - rewrite Z.max_l by lia. rewrite Rmax_left by (apply IZR_le; lia). reflexivity.
Qed.

Definition min4 (p q r s : Z) : Z := Z.min (Z.min p q) (Z.min r s).
Definition max4 (p q r s : Z) : Z := Z.max (Z.max p q) (Z.max r s).

Lemma IZR_min4 (p q r s : Z) : IZR (min4 p q r s) = Rmin (Rmin (IZR p) (IZR q)) (Rmin (IZR r) (IZR s)).
Proof. unfold min4. rewrite !IZR_min. reflexivity. Qed.
Lemma IZR_max4 (p q r s : Z) : IZR (max4 p q r s) = Rmax (Rmax (IZR p) (IZR q)) (Rmax (IZR r) (IZR s)).
Proof. unfold max4. rewrite !IZR_max. reflexivity. Qed.

Module FX (Pk : Prec) <: RI.

Definition k : Z := Pk.k.
Definition p2 : Z := (2 ^ k)%Z.

Lemma p2p : (0 < p2)%Z. Proof. apply p2_pos, Pk.k_nonneg. Qed.
Lemma P2 : 0 < IZR p2. Proof. apply IZR_lt, p2p. Qed.

Definition t : Type := option (Z * Z).

Definition inR (X : t) (x : R) : Prop :=
  match X with None => True | Some (a, b) => IZR a <= x * IZR p2 <= IZR b end.

Definition zero : t := Some (0%Z, 0%Z).

Definition add (X Y : t) : t :=
  match X, Y with Some (a, b), Some (c, d) => Some ((a + c)%Z, (b + d)%Z) | _, _ => None end.

Definition neg (X : t) : t := match X with Some (a, b) => Some ((- b)%Z, (- a)%Z) | None => None end.

Definition sub (X Y : t) : t := add X (neg Y).

(** Division by 2^k rounded down and up, and multiplication by 2^k, as shifts. *)
Definition shr (m : Z) : Z := Z.shiftr m k.
Definition shrc (m : Z) : Z := (- Z.shiftr (- m) k)%Z.
Definition shl (m : Z) : Z := Z.shiftl m k.

Lemma kn : (0 <= k)%Z. Proof. exact Pk.k_nonneg. Qed.

Lemma shr_eq (m : Z) : shr m = fdiv m p2.
Proof. unfold shr, fdiv, p2. apply Z.shiftr_div_pow2, kn. Qed.
Lemma shrc_eq (m : Z) : shrc m = cdiv m p2.
Proof. unfold shrc, cdiv, p2. rewrite Z.shiftr_div_pow2 by apply kn. reflexivity. Qed.
Lemma shl_eq (m : Z) : shl m = (m * p2)%Z.
Proof. unfold shl, p2. apply Z.shiftl_mul_pow2, kn. Qed.

Definition mul (X Y : t) : t :=
  match X, Y with
  | Some (a, b), Some (c, d) =>
      Some (shr (min4 (a * c) (a * d) (b * c) (b * d)), shrc (max4 (a * c) (a * d) (b * c) (b * d)))
  | _, _ => None
  end.

(** Quotient by an interval above zero: the lower end divides by the upper
    end of the divisor when it is nonnegative and by the lower end when it is
    negative, and the upper end the other way round. *)
Definition divp (a b c d : Z) : t :=
  let A := shl a in let B := shl b in
  Some (if (0 <=? a)%Z then fdiv A d else fdiv A c, if (0 <=? b)%Z then cdiv B c else cdiv B d).

Definition div (X Y : t) : t :=
  match X, Y with
  | Some (a, b), Some (c, d) =>
      if (0 <? c)%Z then divp a b c d
      else if (d <? 0)%Z then neg (divp a b (- d) (- c))
      else None
  | _, _ => None
  end.

Definition sqrt (X : t) : t :=
  match X with
  | Some (a, b) => if (0 <=? a)%Z then Some (Z.sqrt (shl a), (Z.sqrt (shl b) + 1)%Z) else None
  | None => None
  end.

Definition abs (X : t) : t :=
  match X with
  | Some (a, b) =>
      if (0 <=? a)%Z then Some (a, b) else if (b <=? 0)%Z then Some ((- b)%Z, (- a)%Z) else Some (0%Z, Z.max (- a) b)
  | None => None
  end.

Definition of_q (m s : Z) : t :=
  if (s <=? k)%Z then Some (Z.shiftl m (k - s), Z.shiftl m (k - s))
  else Some (Z.shiftr m (s - k), (- Z.shiftr (- m) (s - k))%Z).

Definition nonneg (X : t) : bool := match X with Some (a, _) => (0 <=? a)%Z | None => false end.
Definition pos (X : t) : bool := match X with Some (a, _) => (0 <? a)%Z | None => false end.

Lemma zero_ok : inR zero 0.
Proof. unfold inR, zero. rewrite Rmult_0_l. lra. Qed.

Lemma add_ok : forall X Y x y, inR X x -> inR Y y -> inR (add X Y) (x + y).
Proof.
  intros [[a b] |] [[c d] |] x y; simpl; auto.
  intros [H1 H2] [H3 H4]. rewrite !plus_IZR. lra.
Qed.

Lemma neg_ok : forall X x, inR X x -> inR (neg X) (- x).
Proof. intros [[a b] |] x; simpl; auto. intros [H1 H2]. rewrite !opp_IZR. lra. Qed.

Lemma sub_ok : forall X Y x y, inR X x -> inR Y y -> inR (sub X Y) (x - y).
Proof. intros X Y x y HX HY. unfold sub, Rminus. apply add_ok; [exact HX | apply neg_ok, HY]. Qed.

Lemma mul_ok : forall X Y x y, inR X x -> inR Y y -> inR (mul X Y) (x * y).
Proof.
  intros [[a b] |] [[c d] |] x y; simpl; auto.
  rewrite shr_eq, shrc_eq.
  intros HX HY. pose proof P2 as HP.
  pose proof (prod_between _ _ _ _ _ _ HX HY) as [L U].
  rewrite <- !mult_IZR, <- IZR_min4 in L. rewrite <- !mult_IZR, <- IZR_max4 in U.
  pose proof (fdiv_le (min4 (a * c) (a * d) (b * c) (b * d)) p2 p2p) as F.
  pose proof (cdiv_ge (max4 (a * c) (a * d) (b * c) (b * d)) p2 p2p) as C.
  replace (x * IZR p2 * (y * IZR p2)) with (x * y * IZR p2 * IZR p2) in L, U by ring.
  split.
  - apply (Rmult_le_reg_r (IZR p2)); [exact HP | lra].
  - apply (Rmult_le_reg_r (IZR p2)); [exact HP | lra].
Qed.

Lemma divp_ok (a b c d : Z) (x y : R) :
  IZR a <= x * IZR p2 <= IZR b -> IZR c <= y * IZR p2 <= IZR d -> (0 < c)%Z -> inR (divp a b c d) (x / y).
Proof.
  intros HX HY Hc. pose proof P2 as HP.
  assert (Hc' : 0 < IZR c) by (apply IZR_lt, Hc).
  assert (Hd' : 0 < IZR d) by (destruct HY; lra).
  assert (Hy : 0 < y * IZR p2) by (destruct HY; lra).
  assert (Hy0 : 0 < y) by (apply (Rmult_lt_reg_r (IZR p2)); [exact HP | lra]).
  assert (Hd : (0 < d)%Z) by (apply lt_IZR; lra).
  set (Y := y * IZR p2) in *. set (X := x * IZR p2) in *.
  (* x / y * p2 = (X p2) / Y *)
  assert (E : x / y * IZR p2 = X * IZR p2 / Y) by (unfold X, Y; field; lra).
  assert (Q : forall n m : Z, (0 < m)%Z ->
            IZR (fdiv n m) <= IZR n / IZR m /\ IZR n / IZR m <= IZR (cdiv n m)).
  { intros n m Hm. assert (Hm' : 0 < IZR m) by (apply IZR_lt, Hm).
    pose proof (fdiv_le n m Hm) as F. pose proof (cdiv_ge n m Hm) as G.
    split.
    - apply (Rmult_le_reg_r (IZR m)); [exact Hm' |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
    - apply (Rmult_le_reg_r (IZR m)); [exact Hm' |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  destruct HX as [HX1 HX2]. destruct HY as [HY1 HY2].
  unfold divp, inR. rewrite !shl_eq, E.
  split.
  - destruct (Z.leb_spec 0 a) as [Ha | Ha].
    + destruct (Q (a * p2)%Z d Hd) as [Q1 _]. rewrite mult_IZR in Q1.
      apply Rle_trans with (IZR a * IZR p2 / IZR d); [exact Q1 |].
      apply IZR_le in Ha. unfold Rdiv.
      apply Rle_trans with (IZR a * IZR p2 * / Y).
      * apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | apply Rinv_le_contravar; lra].
      * apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rmult_le_compat_r; lra].
    + destruct (Q (a * p2)%Z c Hc) as [Q1 _]. rewrite mult_IZR in Q1.
      apply Rle_trans with (IZR a * IZR p2 / IZR c); [exact Q1 |].
      apply IZR_lt in Ha. unfold Rdiv.
      apply Rle_trans with (IZR a * IZR p2 * / Y).
      * assert (IZR a * IZR p2 < 0) by nra.
        assert (/ Y <= / IZR c) by (apply Rinv_le_contravar; lra).
        pose proof (Rinv_0_lt_compat Y Hy). nra.
      * apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rmult_le_compat_r; lra].
  - destruct (Z.leb_spec 0 b) as [Hb | Hb].
    + destruct (Q (b * p2)%Z c Hc) as [_ Q2]. rewrite mult_IZR in Q2.
      apply Rle_trans with (IZR b * IZR p2 / IZR c); [| exact Q2].
      apply IZR_le in Hb. unfold Rdiv.
      apply Rle_trans with (IZR b * IZR p2 * / Y).
      * apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rmult_le_compat_r; lra].
      * apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | apply Rinv_le_contravar; lra].
    + destruct (Q (b * p2)%Z d Hd) as [_ Q2]. rewrite mult_IZR in Q2.
      apply Rle_trans with (IZR b * IZR p2 / IZR d); [| exact Q2].
      apply IZR_lt in Hb. unfold Rdiv.
      apply Rle_trans with (IZR b * IZR p2 * / Y).
      * apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rmult_le_compat_r; lra].
      * assert (IZR b * IZR p2 < 0) by nra.
        assert (/ IZR d <= / Y) by (apply Rinv_le_contravar; lra).
        pose proof (Rinv_0_lt_compat (IZR d) Hd'). nra.
Qed.

Lemma div_ok : forall X Y x y, inR X x -> inR Y y -> y <> 0 -> inR (div X Y) (x / y).
Proof.
  intros [[a b] |] [[c d] |] x y HX HY Hy; try exact I.
  unfold div.
  destruct (Z.ltb_spec 0 c) as [Hc | Hc]; [apply divp_ok; assumption |].
  destruct (Z.ltb_spec d 0) as [Hd | Hd]; [| exact I].
  replace (x / y) with (- (x / (- y))) by (field; exact Hy).
  apply neg_ok. apply divp_ok; [exact HX | | lia].
  rewrite !opp_IZR. destruct HY. lra.
Qed.

Lemma sqrt_ok : forall X x, inR X x -> 0 <= x -> inR (sqrt X) (R_sqrt.sqrt x).
Proof.
  intros [[a b] |] x; simpl; auto. intros [H1 H2] Hx.
  destruct (Z.leb_spec 0 a) as [Ha | Ha]; [| exact I].
  rewrite !shl_eq. pose proof P2 as HP.
  assert (E : R_sqrt.sqrt x * IZR p2 = R_sqrt.sqrt (x * IZR p2 * IZR p2)).
  { replace (x * IZR p2 * IZR p2) with (x * (IZR p2 * IZR p2)) by ring.
    rewrite R_sqrt.sqrt_mult_alt by lra. rewrite R_sqrt.sqrt_square by lra. reflexivity. }
  simpl. rewrite E.
  assert (HA : IZR (a * p2) <= x * IZR p2 * IZR p2) by (rewrite mult_IZR; apply Rmult_le_compat_r; lra).
  assert (HB : x * IZR p2 * IZR p2 <= IZR (b * p2)) by (rewrite mult_IZR; apply Rmult_le_compat_r; lra).
  assert (Ha2 : (0 <= a * p2)%Z) by (pose proof p2p; lia).
  assert (Hb2 : (0 <= b * p2)%Z).
  { assert (0 <= IZR (b * p2)) by (rewrite mult_IZR; apply Rmult_le_pos; [apply IZR_le in Ha; lra | lra]).
    apply le_IZR. exact H. }
  destruct (Z.sqrt_spec (a * p2) Ha2) as [Sa _].
  destruct (Z.sqrt_spec (b * p2) Hb2) as [_ Sb].
  cbv zeta in Sa, Sb.
  pose proof (Z.sqrt_nonneg (a * p2)) as N1. pose proof (Z.sqrt_nonneg (b * p2)) as N2.
  split.
  - apply Rle_trans with (R_sqrt.sqrt (IZR (a * p2))); [| apply R_sqrt.sqrt_le_1_alt, HA].
    rewrite <- (R_sqrt.sqrt_square (IZR (Z.sqrt (a * p2)))) by (apply IZR_le; exact N1).
    apply R_sqrt.sqrt_le_1_alt. rewrite <- mult_IZR. apply IZR_le. exact Sa.
  - apply Rle_trans with (R_sqrt.sqrt (IZR (b * p2))); [apply R_sqrt.sqrt_le_1_alt, HB |].
    rewrite <- (R_sqrt.sqrt_square (IZR (Z.sqrt (b * p2) + 1))) by (apply IZR_le; lia).
    apply R_sqrt.sqrt_le_1_alt. rewrite <- mult_IZR. apply IZR_le.
    rewrite Z.add_1_r. lia.
Qed.

Lemma abs_ok : forall X x, inR X x -> inR (abs X) (Rabs x).
Proof.
  intros [[a b] |] x; simpl; auto. intros [H1 H2]. pose proof P2 as HP.
  destruct (Z.leb_spec 0 a) as [Ha | Ha].
  - apply IZR_le in Ha. assert (0 <= x) by (apply (Rmult_le_reg_r (IZR p2)); lra).
    rewrite Rabs_pos_eq by lra. simpl. lra.
  - destruct (Z.leb_spec b 0) as [Hb | Hb].
    + apply IZR_le in Hb. assert (x <= 0) by (apply (Rmult_le_reg_r (IZR p2)); lra).
      rewrite Rabs_left1 by lra. simpl. rewrite !opp_IZR. lra.
    + simpl. rewrite IZR_max, opp_IZR. split.
      * apply Rmult_le_pos; [apply Rabs_pos | lra].
      * unfold Rabs. destruct (Rcase_abs x);
          [apply Rle_trans with (- IZR a); [lra | apply Rmax_l] | apply Rle_trans with (IZR b); [lra | apply Rmax_r]].
Qed.

Lemma of_q_ok : forall m s, (0 <= s)%Z -> inR (of_q m s) (IZR m / IZR (2 ^ s)).
Proof.
  intros m s Hs. unfold of_q, inR. pose proof (IZR_p2_pos s Hs) as H2s.
  assert (Hk : (0 <= k)%Z) by exact Pk.k_nonneg.
  destruct (Z.leb_spec s k) as [H | H].
  - assert (E : IZR m / IZR (2 ^ s) * IZR p2 = IZR (m * 2 ^ (k - s))).
    { unfold p2. replace k with (s + (k - s))%Z at 1 by ring.
      rewrite Z.pow_add_r by lia. rewrite !mult_IZR. field. lra. }
    rewrite Z.shiftl_mul_pow2 by lia. rewrite E. lra.
  - rewrite !Z.shiftr_div_pow2 by lia.
    change (- (- m / 2 ^ (s - k)))%Z with (cdiv m (2 ^ (s - k))).
    change (m / 2 ^ (s - k))%Z with (fdiv m (2 ^ (s - k))).
    assert (Hd : (0 < 2 ^ (s - k))%Z) by (apply p2_pos; lia).
    assert (E : IZR m / IZR (2 ^ s) * IZR p2 = IZR m / IZR (2 ^ (s - k))).
    { unfold p2. replace s with ((s - k) + k)%Z at 1 by ring.
      rewrite Z.pow_add_r by lia. rewrite mult_IZR. field.
      split; apply Rgt_not_eq, IZR_lt, p2_pos; lia. }
    rewrite E. pose proof (fdiv_le m _ Hd) as F. pose proof (cdiv_ge m _ Hd) as C.
    assert (Hd' : 0 < IZR (2 ^ (s - k))) by (apply IZR_lt, Hd).
    split.
    + apply (Rmult_le_reg_r (IZR (2 ^ (s - k)))); [exact Hd' |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
    + apply (Rmult_le_reg_r (IZR (2 ^ (s - k)))); [exact Hd' |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma nonneg_ok : forall X x, nonneg X = true -> inR X x -> 0 <= x.
Proof.
  intros [[a b] |] x; simpl; [| discriminate]. intros H [H1 _]. apply Z.leb_le in H.
  apply IZR_le in H. pose proof P2. apply (Rmult_le_reg_r (IZR p2)); lra.
Qed.

Lemma pos_ok : forall X x, pos X = true -> inR X x -> 0 < x.
Proof.
  intros [[a b] |] x; simpl; [| discriminate]. intros H [H1 _]. apply Z.ltb_lt in H.
  apply IZR_lt in H. pose proof P2. apply (Rmult_lt_reg_r (IZR p2)); lra.
Qed.

Definition incl (X Y : t) : bool :=
  match X, Y with
  | None, _ => true
  | Some (a, b), Some (c, d) => ((a <=? c)%Z && (d <=? b)%Z)%bool
  | Some _, None => false
  end.

Definition join (X Y : t) : t :=
  match X, Y with Some (a, _), Some (_, d) => Some (a, d) | _, _ => None end.

Lemma incl_ok : forall X Y x, incl X Y = true -> inR Y x -> inR X x.
Proof.
  intros [[a b] |] [[c d] |] x; simpl; auto; try discriminate.
  intros H [H1 H2]. apply andb_prop in H. destruct H as [E1 E2]. apply Z.leb_le in E1, E2.
  apply IZR_le in E1, E2. lra.
Qed.

Lemma join_ok : forall X Y x y z, inR X x -> inR Y y -> x <= z <= y -> inR (join X Y) z.
Proof.
  intros [[a b] |] [[c d] |] x y z; simpl; auto.
  intros [H1 H2] [H3 H4] [Hz1 Hz2]. pose proof P2. split.
  - apply Rle_trans with (x * IZR p2); [exact H1 | apply Rmult_le_compat_r; lra].
  - apply Rle_trans with (y * IZR p2); [apply Rmult_le_compat_r; lra | exact H4].
Qed.

End FX.
