(** Matrices of Taylor models over one cell.

    A matrix of models is a list of rows ([tmat]); [tmhas] says that at a
    point of the cell each entry has the entry of a real matrix. Sums,
    products, products with interval matrices on either side, entrywise
    ranges and widened remainders keep it ([tmadd_correct], [tmm_correct],
    [tcm_correct], [tmc_correct], [tmrange_correct], [tmball_correct]).
    [tneu] is the partial sum C + E C + ... + E^k C of a Neumann series,
    built by Horner's rule; [neu_tail] bounds what it leaves out of
    (I - E)^-1 C by th^(k+1) / (1 - th) |C| when |E| <= th < 1. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Mat IMat TMEval.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The tail of a Neumann series                                      *)

(** The partial sums C, C + E C, C + E (C + E C), ... *)
Fixpoint rneu (n : nat) (E C : mat) (k : nat) : mat :=
  match k with O => C | S k' => madd C (mm n E (rneu n E C k')) end.

Lemma mnorm_msub_mm :
  forall m n p (A B C : mat), mnorm m p (msub (mm n A B) (mm n A C)) <= mnorm m n A * mnorm n p (msub B C).
Proof.
  intros m n p A B C. eapply Rle_trans; [| apply (mnorm_mm m n p A (msub B C))].
  right. apply Rle_antisym; apply fmax_mono; intros i Hi; unfold mrow; apply msum_le; intros j Hj;
    unfold msub, mm; rewrite <- msum_minus; right; f_equal; apply msum_ext; intros; ring.
Qed.

Lemma mnorm_ext :
  forall m n (A B : mat), (forall i j, (i < m)%nat -> (j < n)%nat -> A i j = B i j) -> mnorm m n A = mnorm m n B.
Proof.
  intros m n A B H. apply Rle_antisym; apply fmax_mono; intros i Hi; unfold mrow; apply msum_le;
    intros j Hj; rewrite H by assumption; lra.
Qed.

(** What the partial sum leaves out of (I - E)^-1 C. *)
Theorem neu_tail :
  forall n p (E C : mat) th k, mnorm n n E <= th -> th < 1 ->
  mnorm n p (msub (mm n (ninv n E) C) (rneu n E C k)) <= th ^ (S k) / (1 - th) * mnorm n p C.
Proof.
  intros n p E C th k HE Hth.
  set (Y := mm n (ninv n E) C).
  assert (Hth0 : 0 <= th) by (pose proof (mnorm_nonneg n n E); lra).
  (* Y = C + E Y *)
  assert (HY : forall i j, (i < n)%nat -> Y i j = C i j + mm n E Y i j).
  { intros i j Hi. unfold Y. rewrite <- (mm_assoc n E (ninv n E) C i j).
    assert (E1 : mm n (ninv n E) C i j - mm n (mm n E (ninv n E)) C i j = mm n mI C i j).
    { unfold mm at 1 2 4. rewrite <- msum_minus. apply msum_ext. intros l Hl.
      rewrite <- (neumann_right n E th HE Hth i l Hi Hl). ring. }
    rewrite (mm_mI_l n C i j Hi) in E1. lra. }
  assert (Hd : forall k, mnorm n p (msub Y (rneu n E C k)) <= th ^ (S k) * mnorm n p Y).
  { induction k0 as [|k0 IH].
    - cbn [rneu]. rewrite (mnorm_ext n p (msub Y C) (mm n E Y))
        by (intros i j Hi Hj; unfold msub; rewrite (HY i j Hi); ring).
      rewrite pow_1. eapply Rle_trans; [apply mnorm_mm|].
      apply Rmult_le_compat_r; [apply mnorm_nonneg | exact HE].
    - cbn [rneu]. rewrite (mnorm_ext n p (msub Y (madd C (mm n E (rneu n E C k0))))
                             (msub (mm n E Y) (mm n E (rneu n E C k0))))
        by (intros i j Hi Hj; unfold msub, madd; rewrite (HY i j Hi); ring).
      eapply Rle_trans; [apply mnorm_msub_mm|].
      replace (th ^ S (S k0) * mnorm n p Y) with (th * (th ^ S k0 * mnorm n p Y)) by (cbn [pow]; ring).
      apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact HE | exact IH]. }
  eapply Rle_trans; [apply Hd|].
  assert (HYn : mnorm n p Y <= / (1 - th) * mnorm n p C).
  { eapply Rle_trans; [apply mnorm_mm|]. apply Rmult_le_compat_r; [apply mnorm_nonneg|].
    exact (neumann_norm n E th HE Hth). }
  unfold Rdiv. rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply pow_le; exact Hth0 | exact HYn].
Qed.

(* ---------------------------------------------------------------- *)
(* Matrices of models                                                *)

Section TMat.

Variable prec : F.precision.
Variable d : nat.
Variable tab : tmtab.
Variable mrlo : list I.type.

Definition tmat : Type := list (list tm).
Definition tz : tm := tconst d I.zero.
Definition tget (A : tmat) (i j : nat) : tm := nth j (nth i A []) tz.
Definition ttab (m n : nat) (f : nat -> nat -> tm) : tmat :=
  map (fun i => map (fun j => f i j) (seq 0 n)) (seq 0 m).

Definition tsum (l : list tm) : tm := fold_right (tadd prec d) tz l.

Definition tmadd (m n : nat) (A B : tmat) : tmat := ttab m n (fun i j => tadd prec d (tget A i j) (tget B i j)).
Definition tmsub (m n : nat) (A B : tmat) : tmat := ttab m n (fun i j => tsub prec d (tget A i j) (tget B i j)).
Definition tmm (m n p : nat) (A B : tmat) : tmat :=
  ttab m p (fun i k => tsum (map (fun j => tmul prec d tab mrlo (tget A i j) (tget B j k)) (seq 0 n))).
(** An interval matrix on the left, and on the right. *)
Definition tcm (m n p : nat) (C : imat) (A : tmat) : tmat :=
  ttab m p (fun i k => tsum (map (fun j => tscale prec d (iget C i j) (tget A j k)) (seq 0 n))).
Definition tmc (m n p : nat) (A : tmat) (C : imat) : tmat :=
  ttab m p (fun i k => tsum (map (fun j => tscale prec d (iget C j k) (tget A i j)) (seq 0 n))).
Definition tmrange (m n : nat) (A : tmat) : imat := itab m n (fun i j => trange prec tab mrlo (tget A i j)).
(** The remainder of every entry widened by X. *)
Definition tball (X : I.type) (t : tm) : tm := TM (tpoly t) (I.add prec (trem t) X).
Definition tmball (m n : nat) (X : I.type) (A : tmat) : tmat := ttab m n (fun i j => tball X (tget A i j)).

Fixpoint tneu (n p : nat) (E C : tmat) (k : nat) : tmat :=
  match k with O => C | S k' => tmadd n p C (tmm n n p E (tneu n p E C k')) end.

Lemma tget_ttab : forall m n f i j, (i < m)%nat -> (j < n)%nat -> tget (ttab m n f) i j = f i j.
Proof.
  intros m n f i j Hi Hj. unfold tget, ttab.
  rewrite (nth_map_seq_lt (fun i => map (fun j => f i j) (seq 0 n)) m i [] Hi).
  exact (nth_map_seq_lt (fun j => f i j) n j tz Hj).
Qed.

(* Soundness at a point of the cell *)

Variables u w : R.
Hypothesis Hlo : forall k, (k < nmon d)%nat ->
  contains (I.convert (cget mrlo k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w)).
Hypothesis Htab : tab = mktab d.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.

Definition tmhas (m n : nat) (A : tmat) (M : mat) : Prop :=
  forall i j, (i < m)%nat -> (j < n)%nat -> tm_has d u w (tget A i j) (M i j).

Lemma tz_correct : tm_has d u w tz 0.
Proof. apply tconst_correct; [exact Hd | exact zero_contains]. Qed.

Lemma tsum_correct :
  forall {A : Type} (g : A -> tm) (f : A -> R) (L : list A),
  (forall x, In x L -> tm_has d u w (g x) (f x)) -> tm_has d u w (tsum (map g L)) (lsum f L).
Proof.
  intros A g f L. induction L as [|x L IH]; intros H.
  - exact tz_correct.
  - cbn [map tsum fold_right lsum]. change (fold_right (tadd prec d) tz (map g L)) with (tsum (map g L)).
    unfold lsum in IH |- *. cbn [fold_right].
    apply tadd_correct; [apply H; left; reflexivity | apply IH; intros y Hy; apply H; right; exact Hy].
Qed.

Lemma tsum_seq :
  forall (g : nat -> tm) (f : nat -> R) n,
  (forall k, (k < n)%nat -> tm_has d u w (g k) (f k)) -> tm_has d u w (tsum (map g (seq 0 n))) (msum f n).
Proof.
  intros g f n H. rewrite <- lsum_seq. apply tsum_correct.
  intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

Lemma tmadd_correct :
  forall m n A B M N, tmhas m n A M -> tmhas m n B N -> tmhas m n (tmadd m n A B) (madd M N).
Proof.
  intros m n A B M N HA HB i j Hi Hj. unfold tmadd. rewrite tget_ttab by assumption.
  apply tadd_correct; [apply HA | apply HB]; assumption.
Qed.

Lemma tmsub_correct :
  forall m n A B M N, tmhas m n A M -> tmhas m n B N -> tmhas m n (tmsub m n A B) (msub M N).
Proof.
  intros m n A B M N HA HB i j Hi Hj. unfold tmsub. rewrite tget_ttab by assumption.
  apply tsub_correct; [apply HA | apply HB]; assumption.
Qed.

Lemma tmm_correct :
  forall m n p A B M N, tmhas m n A M -> tmhas n p B N -> tmhas m p (tmm m n p A B) (mm n M N).
Proof.
  intros m n p A B M N HA HB i k Hi Hk. unfold tmm. rewrite tget_ttab by assumption.
  apply tsum_seq. intros j Hj.
  apply (tmul_correct prec d tab mrlo u w Hlo Htab Hcov Hd); [apply HA | apply HB]; assumption.
Qed.

Lemma tcm_correct :
  forall m n p C Cm A M, icont m n C Cm -> tmhas n p A M -> tmhas m p (tcm m n p C A) (mm n Cm M).
Proof.
  intros m n p C Cm A M HC HA i k Hi Hk. unfold tcm. rewrite tget_ttab by assumption.
  apply tsum_seq. intros j Hj. apply tscale_correct; [apply HC | apply HA]; assumption.
Qed.

Lemma tmc_correct :
  forall m n p A M C Cm, tmhas m n A M -> icont n p C Cm -> tmhas m p (tmc m n p A C) (mm n M Cm).
Proof.
  intros m n p A M C Cm HA HC i k Hi Hk. unfold tmc. rewrite tget_ttab by assumption.
  apply tsum_seq. intros j Hj. rewrite Rmult_comm. apply tscale_correct; [apply HC | apply HA]; assumption.
Qed.

Lemma tmrange_correct : forall m n A M, tmhas m n A M -> icont m n (tmrange m n A) M.
Proof.
  intros m n A M HA. apply itab_correct. intros i j Hi Hj.
  apply (trange_correct prec d tab mrlo u w Hlo Htab Hcov Hd). apply HA; assumption.
Qed.

Lemma tball_correct :
  forall X t x y, tm_has d u w t y -> contains (I.convert X) (Xreal (x - y)) -> tm_has d u w (tball X t) x.
Proof.
  intros X t x y [cs [r [Hc [Hr ->]]]] HX. exists cs, (r + (x - (peval (mons d) cs u w + r))).
  split; [exact Hc|]. split; [| ring].
  apply (I.add_correct prec (trem t) X (Xreal r) (Xreal _) Hr HX).
Qed.

Lemma tmball_correct :
  forall m n X A M N, tmhas m n A M ->
  (forall i j, (i < m)%nat -> (j < n)%nat -> contains (I.convert X) (Xreal (N i j - M i j))) ->
  tmhas m n (tmball m n X A) N.
Proof.
  intros m n X A M N HA HX i j Hi Hj. unfold tmball. rewrite tget_ttab by assumption.
  apply (tball_correct X _ _ (M i j)); [apply HA | apply HX]; assumption.
Qed.

Lemma tneu_correct :
  forall n p E C Em Cm, tmhas n n E Em -> tmhas n p C Cm ->
  forall k, tmhas n p (tneu n p E C k) (rneu n Em Cm k).
Proof.
  intros n p E C Em Cm HE HC k. induction k as [|k IH]; cbn [tneu rneu]; [exact HC|].
  apply tmadd_correct; [exact HC | apply tmm_correct; assumption].
Qed.

End TMat.
