(** Diophantine constants of noble rotation numbers, checked in rationals.

    A noble number, a continued fraction ending in ones, is a root
    w = (- b + sqrt 5) / (2 a) of a x^2 + b x + c with b^2 - 4 a c = 5, the
    discriminant of the golden mean. [quadratic_diophantine] gives the
    constant 1 / (|a| (1 + |w - w'|)), which is small when a is large. The
    same factorization gives g / |q| for every |q| >= Q0 once
    g (sqrt 5 + a / (2 Q0)) <= 1 ([dioph_large]); below Q0 a rational
    enclosure of w and a finite check over q = 1 .. Q0 - 1 give the rest
    ([small_check_sound]). [noble_diophantine] puts the two together, with
    the whole check a boolean computation on rationals ([noble_check]). *)

From Coq Require Import ZArith QArith Qround Qreals Reals Lra Lia List.
From Stellarocq Require Import Dioph.
Local Open Scope R_scope.

Lemma Q2R_inject_Z (z : Z) : Q2R (inject_Z z) = IZR z.
Proof. unfold Q2R, inject_Z. simpl. field. Qed.

(** * Five is not a square of a rational *)

Lemma sq_mod5 (x : Z) : ((x * x) mod 5 = 0)%Z -> (x mod 5 = 0)%Z.
Proof.
  intros H. rewrite Z.mul_mod in H by lia.
  assert (Hr : (0 <= x mod 5 < 5)%Z) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec (x mod 5) 0) as [E | E]; [exact E | exfalso].
  assert (Hc : (x mod 5 = 1 \/ x mod 5 = 2 \/ x mod 5 = 3 \/ x mod 5 = 4)%Z) by lia.
  destruct Hc as [C | [C | [C | C]]]; rewrite C in H; simpl in H; discriminate.
Qed.

Lemma sq5 (n : nat) : forall x q : Z, (Z.abs_nat q <= n)%nat -> (x * x = 5 * (q * q))%Z -> q = 0%Z.
Proof.
  induction n as [| n IH]; intros x q Hq H.
  - lia.
  - destruct (Z.eq_dec q 0) as [E | E]; [exact E | exfalso].
    assert (Hx5 : (x mod 5 = 0)%Z).
    { apply sq_mod5. rewrite H. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
    apply Z.mod_divide in Hx5; [| lia]. destruct Hx5 as [y Hy]. subst x.
    assert (Hq' : (q * q = 5 * (y * y))%Z) by lia.
    assert (Hq5 : (q mod 5 = 0)%Z).
    { apply sq_mod5. rewrite Hq'. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
    apply Z.mod_divide in Hq5; [| lia]. destruct Hq5 as [z Hz]. subst q.
    assert (Hy' : (y * y = 5 * (z * z))%Z) by lia.
    assert (Hz0 : z = 0%Z) by (apply (IH y z); [lia | exact Hy']).
    apply E. rewrite Hz0. ring.
Qed.

Lemma no_root5 (x q : Z) : (x * x = 5 * (q * q))%Z -> q = 0%Z.
Proof. apply (sq5 (Z.abs_nat q)). lia. Qed.

(** * The noble root *)

Section Noble.

Variables a b c : Z.
Hypothesis Ha : (0 < a)%Z.
Hypothesis Hdisc : (b * b - 4 * a * c = 5)%Z.

Definition nw : R := (- IZR b + sqrt 5) / (2 * IZR a).
Definition nw' : R := (- IZR b - sqrt 5) / (2 * IZR a).

Lemma IZR_a_pos : 0 < IZR a. Proof. apply IZR_lt. exact Ha. Qed.

Lemma sqrt5_sq : sqrt 5 * sqrt 5 = 5. Proof. apply sqrt_sqrt. lra. Qed.

Lemma sqrt5_pos : 0 < sqrt 5. Proof. apply sqrt_lt_R0. lra. Qed.

Lemma disc_R : IZR b * IZR b - 4 * IZR a * IZR c = 5.
Proof.
  replace 5 with (IZR 5) by reflexivity. rewrite <- Hdisc.
  rewrite minus_IZR, !mult_IZR. reflexivity.
Qed.

(** c from the discriminant, with 5 written as the square of its root. *)
Lemma c_R : IZR c = (IZR b * IZR b - sqrt 5 * sqrt 5) / (4 * IZR a).
Proof.
  pose proof IZR_a_pos. pose proof disc_R. rewrite sqrt5_sq.
  apply (Rmult_eq_reg_r (4 * IZR a)); [| lra].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. nra.
Qed.

Lemma nw_root : IZR a * nw ^ 2 + IZR b * nw + IZR c = 0.
Proof. pose proof IZR_a_pos. rewrite c_R. unfold nw. field. lra. Qed.

Lemma nw'_root : IZR a * nw' ^ 2 + IZR b * nw' + IZR c = 0.
Proof. pose proof IZR_a_pos. rewrite c_R. unfold nw'. field. lra. Qed.

Lemma nw_ne : nw <> nw'.
Proof.
  pose proof IZR_a_pos. pose proof sqrt5_pos. unfold nw, nw'. intros E.
  apply (Rmult_eq_compat_r (2 * IZR a)) in E.
  unfold Rdiv in E. rewrite !Rmult_assoc, Rinv_l, !Rmult_1_r in E by lra. lra.
Qed.

Lemma nw_gap : IZR a * Rabs (nw - nw') = sqrt 5.
Proof.
  pose proof IZR_a_pos. pose proof sqrt5_pos. unfold nw, nw'.
  replace ((- IZR b + sqrt 5) / (2 * IZR a) - (- IZR b - sqrt 5) / (2 * IZR a))
    with (sqrt 5 / IZR a) by (field; lra).
  rewrite Rabs_pos_eq by (apply Rlt_le, Rdiv_lt_0_compat; lra). field. lra.
Qed.

Lemma n_irr (p q : Z) : q <> 0%Z -> (a * p * p + b * p * q + c * q * q)%Z <> 0%Z.
Proof.
  intros Hq E. apply Hq. apply (no_root5 (2 * a * p + b * q)).
  assert (H4 : (4 * a * (a * p * p + b * p * q + c * q * q) = (2 * a * p + b * q) * (2 * a * p + b * q)
                 - (b * b - 4 * a * c) * (q * q))%Z) by ring.
  rewrite E, Hdisc in H4. lia.
Qed.

(** The factorization and the integer that is not zero. *)
Lemma n_factor (p q : Z) :
  IZR (a * p * p + b * p * q + c * q * q) = IZR a * (IZR p - IZR q * nw) * (IZR p - IZR q * nw').
Proof.
  pose proof IZR_a_pos.
  rewrite !plus_IZR, !mult_IZR, c_R. unfold nw, nw'.
  field. lra.
Qed.

(** Every |q| >= Q0 has |q w - p| >= g / |q|. *)
Lemma dioph_large (g Q0 : R) (p q : Z) :
  0 < g <= / 2 -> 1 <= Q0 -> g * (sqrt 5 + IZR a / (2 * Q0)) <= 1 -> Q0 <= Rabs (IZR q) ->
  g / Rabs (IZR q) <= Rabs (IZR q * nw - IZR p).
Proof.
  intros Hg HQ0 Hc Hq.
  assert (HQ : 1 <= Rabs (IZR q)) by lra.
  assert (Hq0 : q <> 0%Z) by (intros ->; rewrite Rabs_R0 in HQ; lra).
  pose proof IZR_a_pos as HA. pose proof sqrt5_pos as H5.
  apply Rmult_le_reg_l with (Rabs (IZR q)); [lra |].
  replace (Rabs (IZR q) * (g / Rabs (IZR q))) with g by (field; lra).
  destruct (Rle_lt_dec (/ 2) (Rabs (IZR q * nw - IZR p))) as [Hbig | Hsmall].
  - apply Rle_trans with (1 * / 2); [lra |]. apply Rmult_le_compat; lra.
  - assert (HN : 1 <= Rabs (IZR (a * p * p + b * p * q + c * q * q))) by (apply abs_IZR_ge_1, n_irr, Hq0).
    rewrite n_factor, !Rabs_mult, (Rabs_pos_eq (IZR a)) in HN by lra.
    replace (Rabs (IZR p - IZR q * nw)) with (Rabs (IZR q * nw - IZR p)) in HN
      by (rewrite <- Rabs_Ropp; f_equal; ring).
    assert (Hother : Rabs (IZR p - IZR q * nw') <= Rabs (IZR q) * Rabs (nw - nw') + / 2).
    { replace (IZR p - IZR q * nw') with (- (IZR q * nw - IZR p) + IZR q * (nw - nw')) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp, Rabs_mult. lra. }
    set (e := Rabs (IZR q * nw - IZR p)) in *.
    set (Q := Rabs (IZR q)) in *.
    assert (He : 0 <= e) by apply Rabs_pos.
    assert (HG : IZR a * Rabs (nw - nw') = sqrt 5) by apply nw_gap.
    (* 1 <= a e (Q |w - w'| + 1/2) = e (Q sqrt 5 + a / 2) *)
    assert (H1 : 1 <= e * (Q * sqrt 5 + IZR a / 2)).
    { apply Rle_trans with (IZR a * e * (Q * Rabs (nw - nw') + / 2)).
      - apply Rle_trans with (IZR a * e * Rabs (IZR p - IZR q * nw')); [exact HN |].
        apply Rmult_le_compat_l; [nra | exact Hother].
      - right. rewrite <- HG. field. }
    (* g Q <= Q / (Q sqrt 5 + a / 2) <= e Q *)
    assert (H2 : g * (Q * sqrt 5 + IZR a / 2) <= Q).
    { apply Rle_trans with (g * (Q * (sqrt 5 + IZR a / (2 * Q0)))).
      - apply Rmult_le_compat_l; [lra |].
        assert (IZR a / 2 <= Q * (IZR a / (2 * Q0))).
        { apply Rmult_le_reg_r with (2 * Q0); [lra |].
          replace (Q * (IZR a / (2 * Q0)) * (2 * Q0)) with (Q * IZR a) by (field; lra).
          replace (IZR a / 2 * (2 * Q0)) with (IZR a * Q0) by field. nra. }
        nra.
      - replace (g * (Q * (sqrt 5 + IZR a / (2 * Q0)))) with (Q * (g * (sqrt 5 + IZR a / (2 * Q0)))) by ring.
        apply Rle_trans with (Q * 1); [apply Rmult_le_compat_l; lra | lra]. }
    assert (HD : 0 < Q * sqrt 5 + IZR a / 2) by nra.
    nra.
Qed.

End Noble.

(** * The finite check below Q0 *)

(** At q, with w in [wl, wu], the interval [q wl, q wu] keeps g / q away from
    the integers on either side. *)
Definition small_ok (wl wu g : Q) (q : Z) : bool :=
  let lo := (inject_Z q * wl)%Q in
  let hi := (inject_Z q * wu)%Q in
  let p0 := Qfloor lo in
  (Qle_bool (g / inject_Z q) (lo - inject_Z p0) && Qle_bool (g / inject_Z q) (inject_Z p0 + 1 - hi))%bool.

Lemma small_ok_sound (wl wu g : Q) (q p : Z) (w : R) :
  (0 < q)%Z -> Q2R wl <= w <= Q2R wu -> small_ok wl wu g q = true ->
  Q2R g / IZR q <= Rabs (IZR q * w - IZR p).
Proof.
  intros Hq [Hl Hu] H. unfold small_ok in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Qle_bool_iff in H1. apply Qle_bool_iff in H2.
  apply Qle_Rle in H1. apply Qle_Rle in H2.
  assert (HqR : 0 < IZR q) by (apply IZR_lt; exact Hq).
  set (p0 := Qfloor (inject_Z q * wl)) in *.
  rewrite Q2R_minus, Q2R_mult, !Q2R_inject_Z in H1.
  rewrite Q2R_minus, Q2R_plus, Q2R_mult, !Q2R_inject_Z in H2.
  unfold Qdiv in H1, H2. rewrite Q2R_mult, Q2R_inv, Q2R_inject_Z in H1, H2
    by (intros E; apply Qeq_eqR in E; rewrite Q2R_inject_Z in E; lra).
  replace (Q2R 1) with 1 in H2 by (unfold Q2R; simpl; lra).
  assert (Hlo : IZR q * Q2R wl <= IZR q * w) by (apply Rmult_le_compat_l; lra).
  assert (Hhi : IZR q * w <= IZR q * Q2R wu) by (apply Rmult_le_compat_l; lra).
  unfold Rdiv.
  destruct (Z_le_gt_dec p p0) as [Hp | Hp].
  - apply IZR_le in Hp.
    apply Rle_trans with (IZR q * w - IZR p); [lra | apply Rle_abs].
  - assert (Hp' : IZR p0 + 1 <= IZR p) by (rewrite <- plus_IZR; apply IZR_le; lia).
    rewrite <- Rabs_Ropp. apply Rle_trans with (- (IZR q * w - IZR p)); [lra | apply Rle_abs].
Qed.

Fixpoint small_all (wl wu g : Q) (n : nat) : bool :=
  match n with
  | O => true
  | S k => (small_ok wl wu g (Z.of_nat (S k)) && small_all wl wu g k)%bool
  end.

Lemma small_all_sound (wl wu g : Q) (n : nat) (w : R) :
  Q2R wl <= w <= Q2R wu -> small_all wl wu g n = true ->
  forall q p : Z, (0 < q)%Z -> (Z.to_nat q <= n)%nat -> Q2R g / IZR q <= Rabs (IZR q * w - IZR p).
Proof.
  intros Hw. induction n as [| n IH]; intros H q p Hq Hn; [lia |].
  simpl in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Nat.eq_dec (Z.to_nat q) (S n)) as [E | E].
  - replace q with (Z.of_nat (S n)) by lia. apply (small_ok_sound wl wu); [lia | exact Hw | exact H1].
  - apply IH; [exact H2 | exact Hq | lia].
Qed.

(** * The noble check *)

(** Rational bounds s_lo <= sqrt 5 <= s_hi from their squares. *)
Lemma sqrt5_between (slo shi : Q) :
  (0 <= slo)%Q -> (slo * slo <= 5)%Q -> (5 <= shi * shi)%Q -> (0 <= shi)%Q ->
  Q2R slo <= sqrt 5 <= Q2R shi.
Proof.
  intros H0 H1 H2 H3.
  apply Qle_Rle in H0. apply Qle_Rle in H1. apply Qle_Rle in H2. apply Qle_Rle in H3.
  rewrite Q2R_mult in H1, H2. replace (Q2R 5) with 5 in H1, H2 by (unfold Q2R; simpl; lra).
  replace (Q2R 0) with 0 in H0, H3 by (unfold Q2R; simpl; lra).
  split.
  - rewrite <- (sqrt_square (Q2R slo)) by lra. apply sqrt_le_1_alt. lra.
  - rewrite <- (sqrt_square (Q2R shi)) by lra. apply sqrt_le_1_alt. lra.
Qed.

Definition nwl (a b : Z) (slo : Q) : Q := ((- inject_Z b + slo) / (2 * inject_Z a))%Q.
Definition nwu (a b : Z) (shi : Q) : Q := ((- inject_Z b + shi) / (2 * inject_Z a))%Q.

Definition noble_check (a b : Z) (slo shi g : Q) (Q0 : nat) : bool :=
  (Qle_bool 0 slo && Qle_bool (slo * slo) 5 && Qle_bool 5 (shi * shi) && Qle_bool 0 shi &&
   Qle_bool (1 # 1000000) g && Qle_bool g (1 # 2) && Qle_bool 1 (inject_Z (Z.of_nat Q0)) &&
   Qle_bool (g * (shi + inject_Z a / (2 * inject_Z (Z.of_nat Q0)))) 1 &&
   small_all (nwl a b slo) (nwu a b shi) g Q0)%bool.

Lemma noble_check_spec (a b : Z) (slo shi g : Q) (Q0 : nat) :
  noble_check a b slo shi g Q0 = true ->
  (0 <= slo)%Q /\ (slo * slo <= 5)%Q /\ (5 <= shi * shi)%Q /\ (0 <= shi)%Q /\
  ((1 # 1000000) <= g)%Q /\ (g <= 1 # 2)%Q /\ (1 <= inject_Z (Z.of_nat Q0))%Q /\
  (g * (shi + inject_Z a / (2 * inject_Z (Z.of_nat Q0))) <= 1)%Q /\
  small_all (nwl a b slo) (nwu a b shi) g Q0 = true.
Proof.
  unfold noble_check. intros H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
  apply Qle_bool_iff in H1, H2, H3, H4, H5, H6, H7, H8.
  repeat split; assumption.
Qed.

Lemma Q2R_1 : Q2R 1 = 1. Proof. unfold Q2R. simpl. lra. Qed.
Lemma Q2R_5 : Q2R 5 = 5. Proof. unfold Q2R. simpl. lra. Qed.
Lemma Q2R_0 : Q2R 0 = 0. Proof. unfold Q2R. simpl. lra. Qed.

(** A rotation number and its negative share their constants. *)
Lemma dioph_neg (w g : R) : diophantine1 (- w) g -> diophantine1 w g.
Proof.
  intros H p q Hq. pose proof (H (- p)%Z q Hq) as Hp.
  rewrite opp_IZR in Hp. replace (IZR q * - w - - IZR p) with (- (IZR q * w - IZR p)) in Hp by ring.
  rewrite Rabs_Ropp in Hp. exact Hp.
Qed.

(** k times a noble root is Diophantine against every integer, with the
    constant of [quadratic_diophantine]; the finiteness of the step's parts
    needs no more. *)
Lemma noble_scaled (a b c k : Z) :
  (0 < a)%Z -> (b * b - 4 * a * c = 5)%Z -> (0 < k)%Z ->
  diophantine1 (IZR k * nw a b)
    (/ (Rabs (IZR a) * (1 + Rabs (IZR k * nw a b - IZR k * nw' a b)))).
Proof.
  intros Ha Hd Hk.
  assert (HkR : 0 < IZR k) by (apply IZR_lt; exact Hk).
  apply (quadratic_diophantine a (b * k) (c * k * k)); [lia | | | |].
  - rewrite !mult_IZR. pose proof (nw_root a b c Ha Hd) as H. nra.
  - rewrite !mult_IZR. pose proof (nw'_root a b c Ha Hd) as H. nra.
  - pose proof (nw_ne a b Ha) as H. intros E. apply H.
    apply (Rmult_eq_reg_l (IZR k)); [exact E | lra].
  - intros p q Hq. replace (a * p * p + b * k * p * q + c * k * k * q * q)%Z
      with (a * p * p + b * p * (k * q) + c * (k * q) * (k * q))%Z by ring.
    apply (n_irr a b c Hd). lia.
Qed.

Theorem noble_diophantine (a b c : Z) (slo shi g : Q) (Q0 : nat) :
  (0 < a)%Z -> (b * b - 4 * a * c = 5)%Z -> noble_check a b slo shi g Q0 = true ->
  diophantine1 (nw a b) (Q2R g).
Proof.
  intros Ha Hd H.
  destruct (noble_check_spec a b slo shi g Q0 H) as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 HS]]]]]]]].
  destruct (sqrt5_between slo shi H1 H2 H3 H4) as [Sl Su].
  apply Qle_Rle in H5, H6, H7, H8.
  replace (Q2R (1 # 1000000)) with (/ 1000000) in H5 by (unfold Q2R; simpl; lra).
  replace (Q2R (1 # 2)) with (/ 2) in H6 by (unfold Q2R; simpl; lra).
  rewrite Q2R_1, Q2R_inject_Z in H7.
  rewrite Q2R_mult, Q2R_plus, Q2R_1 in H8. unfold Qdiv in H8.
  set (Q0R := IZR (Z.of_nat Q0)) in *.
  assert (HA : 0 < IZR a) by (apply IZR_lt; exact Ha).
  rewrite Q2R_mult, Q2R_inv, Q2R_mult, !Q2R_inject_Z in H8
    by (intros E; apply Qeq_eqR in E; rewrite Q2R_mult, Q2R_inject_Z in E;
        replace (Q2R 2) with 2 in E by (unfold Q2R; simpl; lra); unfold Q0R in *; rewrite Q2R_0 in E; lra).
  replace (Q2R 2) with 2 in H8 by (unfold Q2R; simpl; lra).
  (* the enclosure of w *)
  assert (Hw : Q2R (nwl a b slo) <= nw a b <= Q2R (nwu a b shi)).
  { unfold nwl, nwu, nw, Qdiv.
    assert (Hinv : Q2R (/ (2 * inject_Z a)) = / (2 * IZR a)).
    { rewrite Q2R_inv, Q2R_mult, Q2R_inject_Z.
      - replace (Q2R 2) with 2 by (unfold Q2R; simpl; lra). reflexivity.
      - intros E. apply Qeq_eqR in E. rewrite Q2R_mult, Q2R_inject_Z, Q2R_0 in E.
        replace (Q2R 2) with 2 in E by (unfold Q2R; simpl; lra). lra. }
    rewrite !Q2R_mult, Hinv, !Q2R_plus, Q2R_opp, Q2R_inject_Z.
    unfold Rdiv. split; apply Rmult_le_compat_r; try (apply Rlt_le, Rinv_0_lt_compat; lra); lra. }
  pose proof (small_all_sound _ _ g Q0 (nw a b) Hw HS) as Small.
  intros p q Hq.
  assert (Hg : 0 < Q2R g <= / 2) by lra.
  destruct (Rle_lt_dec Q0R (Rabs (IZR q))) as [Hbig | Hlt].
  - apply (dioph_large a b c Ha Hd (Q2R g) Q0R p q Hg H7); [| exact Hbig].
    apply Rle_trans with (Q2R g * (Q2R shi + IZR a * / (2 * Q0R))); [| exact H8].
    apply Rmult_le_compat_l; [lra |]. unfold Rdiv. lra.
  - destruct (Z_lt_le_dec 0 q) as [Hpos | Hneg].
    + assert (HqR : 0 < IZR q) by (apply IZR_lt; exact Hpos).
      rewrite Rabs_pos_eq in Hlt |- * by lra.
      apply Small; [exact Hpos |].
      apply Nat2Z.inj_le. rewrite Z2Nat.id by lia.
      apply le_IZR. unfold Q0R in Hlt. lra.
    + assert (Hq' : (q < 0)%Z) by lia.
      assert (HqR : IZR q < 0) by (apply IZR_lt; exact Hq').
      rewrite Rabs_left in Hlt |- * by lra.
      replace (Rabs (IZR q * nw a b - IZR p)) with (Rabs (IZR (- q) * nw a b - IZR (- p)))
        by (rewrite !opp_IZR, <- Rabs_Ropp; f_equal; ring).
      replace (- IZR q) with (IZR (- q)) by apply opp_IZR.
      apply Small; [lia |].
      apply Nat2Z.inj_le. rewrite Z2Nat.id by lia.
      apply le_IZR. rewrite opp_IZR. unfold Q0R in Hlt. lra.
Qed.
