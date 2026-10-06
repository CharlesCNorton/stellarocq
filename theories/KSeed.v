(** Enclosures of pi, of cos and sin of 2 pi / N and of exponentials of small
    rationals, from their series.

    pi / 4 lies between consecutive partial sums of Machin's series
    2 atan(1/3) + atan(1/7) (the standard library's [PI_2_3_7_ineq]); sin a
    and cos a lie between consecutive partial sums of their series for
    0 <= a <= pi / 2 ([sin_bound], [cos_bound]); for 0 <= x <= 1, e^x is at
    least every partial sum of its series and e^(-x) lies between
    consecutive partial sums of its alternating series ([exp_lower],
    [exp_neg_between]), so e^x is at most the inverse of the lower one
    ([exp_upper]). Over any enclosure arithmetic the partial sums are formed
    term by term ([isum_ok], [ipow_ok]) and the join of a lower and an upper
    enclosure holds the value between them ([ipi_ok], [itrig_ok],
    [iexp_pos_ok], [iexp_neg_ok]); integer powers of an enclosed exponential
    enclose the exponential of the multiple ([ipow_exp]). A seed a run was
    given serves when it holds the computed enclosure ([seed_incl]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coq Require Import Machin.
From Stellarocq Require Import KFix KCheckKern.
Import ListNotations.
Local Open Scope R_scope.

(** * Real bounds *)

Definition eterm (x : R) (i : nat) : R := / INR (fact i) * x ^ i.

Lemma exp_in_self (x : R) : exp_in x (exp x).
Proof. unfold exp. exact (proj2_sig (exist_exp x)). Qed.

Lemma exp_lower (x : R) (n : nat) : 0 <= x -> sum_f_R0 (eterm x) n <= exp x.
Proof.
  intros Hx. apply (growing_ineq (fun n => sum_f_R0 (eterm x) n)).
  - intros m. cbn [sum_f_R0]. unfold eterm.
    assert (0 < / INR (fact (S m))) by (apply Rinv_0_lt_compat, lt_0_INR, lt_O_fact).
    assert (0 <= x ^ S m) by (apply pow_le, Hx). nra.
  - exact (exp_in_self x).
Qed.

Lemma alt_eterm (x : R) (i : nat) : tg_alt (fun j => x ^ j / INR (fact j)) i = eterm (- x) i.
Proof.
  unfold tg_alt, eterm. replace (- x) with (-1 * x) by ring. rewrite Rpow_mult_distr. unfold Rdiv. ring.
Qed.

Lemma eterm_decr (x : R) : 0 <= x <= 1 -> Un_decreasing (fun j => x ^ j / INR (fact j)).
Proof.
  intros Hx n. unfold Rdiv. cbn [pow]. rewrite fact_simpl, mult_INR, Rinv_mult.
  assert (Hf : 0 < / INR (fact n)) by (apply Rinv_0_lt_compat, lt_0_INR, lt_O_fact).
  assert (Hs : 0 < / INR (S n) <= 1).
  { split; [apply Rinv_0_lt_compat, lt_0_INR; lia |].
    rewrite <- Rinv_1. apply Rinv_le_contravar; [lra |]. rewrite S_INR. pose proof (pos_INR n). lra. }
  assert (Ha : 0 <= x ^ n) by (apply pow_le; lra).
  assert (Hb : 0 <= x ^ n * / INR (fact n)) by nra.
  replace (x * x ^ n * (/ INR (S n) * / INR (fact n))) with ((x * / INR (S n)) * (x ^ n * / INR (fact n))) by ring.
  assert (Hc : x * / INR (S n) <= 1) by nra.
  assert (Hd : 0 <= x * / INR (S n)) by nra.
  nra.
Qed.

Lemma exp_neg_between (x : R) (N : nat) : 0 <= x <= 1 ->
  sum_f_R0 (eterm (- x)) (S (2 * N)) <= exp (- x) <= sum_f_R0 (eterm (- x)) (2 * N).
Proof.
  intros Hx.
  assert (E : forall n, sum_f_R0 (tg_alt (fun j => x ^ j / INR (fact j))) n = sum_f_R0 (eterm (- x)) n).
  { intros n. apply sum_eq. intros i _. apply alt_eterm. }
  rewrite <- !E. apply alternated_series_ineq.
  - exact (eterm_decr x Hx).
  - exact (cv_speed_pow_fact x).
  - intros eps He. destruct (exp_in_self (- x) eps He) as [N0 HN]. exists N0. intros n Hn.
    rewrite E. exact (HN n Hn).
Qed.

Lemma exp_upper (x : R) (N : nat) : 0 <= x <= 1 -> 0 < sum_f_R0 (eterm (- x)) (S (2 * N)) ->
  exp x <= / sum_f_R0 (eterm (- x)) (S (2 * N)).
Proof.
  intros Hx Hp. destruct (exp_neg_between x N Hx) as [A _].
  assert (E : exp x = / exp (- x)).
  { apply (Rmult_eq_reg_l (exp (- x))); [| apply Rgt_not_eq, exp_pos].
    rewrite Rinv_r by apply Rgt_not_eq, exp_pos. rewrite <- exp_plus. replace (- x + x) with 0 by ring. apply exp_0. }
  rewrite E. apply Rinv_le_contravar; assumption.
Qed.

Lemma exp_pow (y : R) (n : nat) : exp (INR n * y) = exp y ^ n.
Proof.
  induction n as [| n IH]; [simpl; rewrite Rmult_0_l; apply exp_0 |].
  rewrite S_INR. replace ((INR n + 1) * y) with (y + INR n * y) by ring. rewrite exp_plus, IH. reflexivity.
Qed.

(** An integer factorial as an integer. *)
Fixpoint Zfact (n : nat) : Z := match n with O => 1%Z | S m => (Z.of_nat (S m) * Zfact m)%Z end.

Lemma Zfact_INR (n : nat) : IZR (Zfact n) = INR (fact n).
Proof.
  induction n as [| n IH]; [reflexivity |]. cbn [Zfact]. rewrite fact_simpl, mult_INR, mult_IZR, IH.
  rewrite <- INR_IZR_INZ. reflexivity.
Qed.

Lemma pow_m1 (n : nat) : (-1) ^ n = if Nat.even n then 1 else -1.
Proof.
  induction n as [| n IH]; [reflexivity |]. cbn [pow]. rewrite IH, Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even n); simpl; ring.
Qed.

Module Seeds (J : RI).

Module KO := KernOps J.
Import KO.

Definition one : J.t := J.of_q 1 0.

(** * Series over intervals *)

Fixpoint isum (F : nat -> J.t) (n : nat) : J.t :=
  match n with O => F O | S m => J.add (isum F m) (F (S m)) end.

Lemma isum_ok (F : nat -> J.t) (f : nat -> R) (n : nat) :
  (forall i, (i <= n)%nat -> inR (F i) (f i)) -> inR (isum F n) (sum_f_R0 f n).
Proof.
  induction n as [| n IH]; intros H; [apply H; lia |].
  cbn [isum sum_f_R0]. apply inR_add; [apply IH; intros i Hi; apply H; lia | apply H; lia].
Qed.

Fixpoint ipow (X : J.t) (n : nat) : J.t := match n with O => one | S m => J.mul X (ipow X m) end.

Lemma ipow_ok (X : J.t) (x : R) (n : nat) : inR X x -> inR (ipow X n) (x ^ n).
Proof. intros H. induction n as [| n IH]; [apply inR_Z | cbn [ipow pow]; apply inR_mul; assumption]. Qed.

Definition isgn (n : nat) : J.t := if Nat.even n then one else J.of_q (-1) 0.

Lemma isgn_ok (n : nat) : inR (isgn n) ((-1) ^ n).
Proof. unfold isgn. rewrite pow_m1. destruct (Nat.even n); apply inR_Z. Qed.

Definition inat (n : nat) : J.t := J.of_q (Z.of_nat n) 0.
Lemma inat_ok (n : nat) : inR (inat n) (INR n).
Proof. unfold inat. rewrite INR_IZR_INZ. apply inR_Z. Qed.

Definition ifact (n : nat) : J.t := J.of_q (Zfact n) 0.
Lemma ifact_ok (n : nat) : inR (ifact n) (INR (fact n)).
Proof. unfold ifact. rewrite <- Zfact_INR. apply inR_Z. Qed.

Lemma inv_ok (X : J.t) (x : R) : inR X x -> x <> 0 -> inR (J.div one X) (/ x).
Proof. intros H Hx. replace (/ x) with (1 / x) by (unfold Rdiv; ring). apply inR_div; [apply inR_Z | exact H | exact Hx]. Qed.

(** * pi *)

Definition ithird : J.t := J.div one (J.of_q 3 0).
Definition iseventh : J.t := J.div one (J.of_q 7 0).

Definition ipi_term (n : nat) : J.t :=
  J.mul (isgn n) (J.add (J.mul (J.of_q 2 0) (J.div (ipow ithird (2 * n + 1)) (inat (2 * n + 1))))
                        (J.div (ipow iseventh (2 * n + 1)) (inat (2 * n + 1)))).

Lemma ipi_term_ok (n : nat) : inR (ipi_term n) (tg_alt PI_2_3_7_tg n).
Proof.
  unfold ipi_term, tg_alt, PI_2_3_7_tg, Ratan_seq.
  assert (H3 : inR ithird (/ 3)) by (apply inv_ok; [apply inR_Z | lra]).
  assert (H7 : inR iseventh (/ 7)) by (apply inv_ok; [apply inR_Z | lra]).
  assert (HN : INR (2 * n + 1) <> 0) by (apply not_0_INR; lia).
  apply inR_mul; [apply isgn_ok |]. apply inR_add; [apply inR_mul; [apply inR_Z |] |];
    apply inR_div; try apply inat_ok; try exact HN; apply ipow_ok; assumption.
Qed.

(** Machin's series to 2 N + 2 terms. *)
Definition ipi (N : nat) : J.t := J.mul (J.of_q 4 0) (J.join (isum ipi_term (S (2 * N))) (isum ipi_term (2 * N))).

Theorem ipi_ok (N : nat) : inR (ipi N) PI.
Proof.
  unfold ipi. replace PI with (4 * (PI / 4)) by field. apply inR_mul; [apply inR_Z |].
  destruct (PI_2_3_7_ineq N) as [A B].
  apply (J.join_ok _ _ _ _ _ (isum_ok ipi_term _ (S (2 * N)) (fun i _ => ipi_term_ok i))
                              (isum_ok ipi_term _ (2 * N) (fun i _ => ipi_term_ok i))). split; assumption.
Qed.

(** * cos and sin of 2 pi / N *)

Definition isin_term (A : J.t) (i : nat) : J.t := J.mul (isgn i) (J.div (ipow A (2 * i + 1)) (ifact (2 * i + 1))).
Definition icos_term (A : J.t) (i : nat) : J.t := J.mul (isgn i) (J.div (ipow A (2 * i)) (ifact (2 * i))).

Lemma isin_term_ok (A : J.t) (a : R) (i : nat) : inR A a -> inR (isin_term A i) (sin_term a i).
Proof.
  intros H. unfold isin_term, sin_term. apply inR_mul; [apply isgn_ok |].
  apply inR_div; [apply ipow_ok, H | apply ifact_ok | apply not_0_INR, fact_neq_0].
Qed.

Lemma icos_term_ok (A : J.t) (a : R) (i : nat) : inR A a -> inR (icos_term A i) (cos_term a i).
Proof.
  intros H. unfold icos_term, cos_term. apply inR_mul; [apply isgn_ok |].
  apply inR_div; [apply ipow_ok, H | apply ifact_ok | apply not_0_INR, fact_neq_0].
Qed.

Definition iang (NP N : nat) : J.t := J.div (J.mul (J.of_q 2 0) (ipi NP)) (inat N).

Lemma iang_ok (NP N : nat) : (0 < N)%nat -> inR (iang NP N) (2 * PI / INR N).
Proof.
  intros HN. unfold iang. apply inR_div; [apply inR_mul; [apply inR_Z | apply ipi_ok] | apply inat_ok |].
  apply not_0_INR. lia.
Qed.

(** cos and sin of 2 pi / N, with Machin's series to 2 NP + 2 terms and the
    trigonometric series to 2 NT + 2 terms. *)
Definition itrig (NP NT N : nat) : J.t * J.t :=
  let A := iang NP N in
  (J.join (isum (icos_term A) (2 * NT + 1)) (isum (icos_term A) (2 * (NT + 1))),
   J.join (isum (isin_term A) (2 * NT + 1)) (isum (isin_term A) (2 * (NT + 1)))).

Theorem itrig_ok (NP NT N : nat) : (4 <= N)%nat ->
  inR (fst (itrig NP NT N)) (cos (2 * PI / INR N)) /\ inR (snd (itrig NP NT N)) (sin (2 * PI / INR N)).
Proof.
  intros HN. unfold itrig. cbn [fst snd].
  pose proof (iang_ok NP N ltac:(lia)) as HA.
  assert (Ha : 0 <= 2 * PI / INR N <= PI / 2).
  { pose proof PI_RGT_0 as Hpi. assert (HN4 : 4 <= INR N) by (replace 4 with (INR 4) by (simpl; ring); apply le_INR, HN).
    split; [apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra] |].
    apply (Rmult_le_reg_r (INR N)); [lra |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  split.
  - apply (J.join_ok _ _ _ _ _ (isum_ok _ _ _ (fun i _ => icos_term_ok _ _ i HA))
                                (isum_ok _ _ _ (fun i _ => icos_term_ok _ _ i HA))).
    apply cos_bound; pose proof PI_RGT_0; lra.
  - apply (J.join_ok _ _ _ _ _ (isum_ok _ _ _ (fun i _ => isin_term_ok _ _ i HA))
                                (isum_ok _ _ _ (fun i _ => isin_term_ok _ _ i HA))).
    apply sin_bound; pose proof PI_RGT_0; lra.
Qed.

(** * Exponentials *)

Definition iexp_series (X : J.t) (n : nat) : J.t := isum (fun i => J.mul (J.div one (ifact i)) (ipow X i)) n.

Lemma iexp_series_ok (X : J.t) (x : R) (n : nat) : inR X x -> inR (iexp_series X n) (sum_f_R0 (eterm x) n).
Proof.
  intros H. apply isum_ok. intros i _. unfold eterm. apply inR_mul; [| apply ipow_ok, H].
  apply inv_ok; [apply ifact_ok | apply not_0_INR, fact_neq_0].
Qed.

(** e^x and e^(-x) for 0 <= x <= 1, with 2 NE + 2 terms. *)
Definition iexp_pos (X : J.t) (NE : nat) : J.t :=
  J.join (iexp_series X (2 * NE)) (J.div one (iexp_series (J.neg X) (S (2 * NE)))).
Definition iexp_neg (X : J.t) (NE : nat) : J.t :=
  J.join (iexp_series (J.neg X) (S (2 * NE))) (iexp_series (J.neg X) (2 * NE)).
Definition iexp_pos_flag (X : J.t) (NE : nat) : bool := J.pos (iexp_series (J.neg X) (S (2 * NE))).

Theorem iexp_pos_ok (X : J.t) (x : R) (NE : nat) : inR X x -> 0 <= x <= 1 -> iexp_pos_flag X NE = true ->
  inR (iexp_pos X NE) (exp x).
Proof.
  intros H Hx Hf. unfold iexp_pos, iexp_pos_flag in *.
  pose proof (iexp_series_ok (J.neg X) (- x) (S (2 * NE)) (inR_neg _ _ H)) as HA.
  pose proof (inR_pos _ _ Hf HA) as Hp.
  apply (J.join_ok _ _ _ _ _ (iexp_series_ok X x (2 * NE) H) (inv_ok _ _ HA ltac:(lra))).
  split; [apply exp_lower; lra | apply exp_upper; assumption].
Qed.

Theorem iexp_neg_ok (X : J.t) (x : R) (NE : nat) : inR X x -> 0 <= x <= 1 -> inR (iexp_neg X NE) (exp (- x)).
Proof.
  intros H Hx. unfold iexp_neg.
  apply (J.join_ok _ _ _ _ _ (iexp_series_ok (J.neg X) (- x) (S (2 * NE)) (inR_neg _ _ H))
                              (iexp_series_ok (J.neg X) (- x) (2 * NE) (inR_neg _ _ H))).
  exact (exp_neg_between x NE Hx).
Qed.

Theorem ipow_exp (E : J.t) (y : R) (n : nat) : inR E (exp y) -> inR (ipow E n) (exp (INR n * y)).
Proof. intros H. rewrite exp_pow. apply ipow_ok, H. Qed.

(** The rational p / q. *)
Definition iq (p q : Z) : J.t := J.div (J.of_q p 0) (J.of_q q 0).
Lemma iq_ok (p q : Z) : (0 < q)%Z -> inR (iq p q) (IZR p / IZR q).
Proof. intros Hq. unfold iq. apply inR_div; [apply inR_Z | apply inR_Z | apply Rgt_not_eq, IZR_lt, Hq]. Qed.

(** A seed a run was given serves when it holds the computed enclosure. *)
Lemma seed_incl (S C : J.t) (x : R) : J.incl S C = true -> inR C x -> inR S x.
Proof. apply J.incl_ok. Qed.

End Seeds.
