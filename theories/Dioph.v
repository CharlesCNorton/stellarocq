(** Quadratic irrationals are Diophantine with exponent one.

    The KAM step divides the Fourier coefficients of the invariance error by
    the small divisors q w - p of the torus's rotation number w. A rotation
    number w is Diophantine with constant gamma and exponent one when

      |q w - p| >= gamma / |q|   for all integers p and q, q <> 0.

    [quadratic_diophantine] proves this for a root w of a x^2 + b x + c with
    integer coefficients, a <> 0 and no rational root, whose other root is w',
    with gamma = 1 / (|a| (1 + |w - w'|)): the integer a p^2 + b p q + c q^2 is
    not zero and equals a (p - q w) (p - q w'), and |p - q w'| is at most
    |q| (1 + |w - w'|) whenever |q w - p| < 1. Noble numbers, the continued
    fractions ending in ones, are such roots. *)

From Coq Require Import ZArith Reals Lra Lia.
Local Open Scope R_scope.

Definition diophantine1 (w gamma : R) : Prop :=
  forall p q : Z, q <> 0%Z -> gamma / Rabs (IZR q) <= Rabs (IZR q * w - IZR p).

Lemma abs_IZR_ge_1 (q : Z) : q <> 0%Z -> 1 <= Rabs (IZR q).
Proof.
  intros Hq. rewrite <- abs_IZR. apply IZR_le. lia.
Qed.

Theorem quadratic_diophantine (a b c : Z) (w w' : R) :
  a <> 0%Z ->
  IZR a * w ^ 2 + IZR b * w + IZR c = 0 ->
  IZR a * w' ^ 2 + IZR b * w' + IZR c = 0 ->
  w <> w' ->
  (forall p q : Z, q <> 0%Z -> (a * p * p + b * p * q + c * q * q)%Z <> 0%Z) ->
  diophantine1 w (/ (Rabs (IZR a) * (1 + Rabs (w - w')))).
Proof.
  intros Ha Hw Hw' Hne Hirr p q Hq.
  set (A := IZR a). set (P := IZR p). set (Q := IZR q).
  assert (HA : 1 <= Rabs A) by (apply abs_IZR_ge_1; exact Ha).
  assert (HQ : 1 <= Rabs Q) by (apply abs_IZR_ge_1; exact Hq).
  assert (Hd : 0 <= Rabs (w - w')) by apply Rabs_pos.
  set (G := / (Rabs A * (1 + Rabs (w - w')))).
  assert (HG : 0 < G).
  { unfold G. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
  assert (HG1 : G <= 1).
  { unfold G. rewrite <- Rinv_1. apply Rinv_le_contravar; [lra |].
    apply Rle_trans with (1 * 1); [lra |].
    apply Rmult_le_compat; lra. }
  (* the divisor as a multiple of 1 / |q| *)
  apply Rmult_le_reg_l with (Rabs Q); [lra |].
  replace (Rabs Q * (G / Rabs Q)) with G by (field; lra).
  destruct (Rle_lt_dec 1 (Rabs (Q * w - P))) as [Hbig | Hsmall].
  - (* |q w - p| >= 1 >= G, and |q| >= 1 *)
    apply Rle_trans with (1 * 1); [lra |].
    apply Rmult_le_compat; lra.
  - (* the integer a p^2 + b p q + c q^2 is not zero *)
    assert (HN : 1 <= Rabs (IZR (a * p * p + b * p * q + c * q * q))).
    { apply abs_IZR_ge_1. apply Hirr. exact Hq. }
    (* Vieta: w + w' = - b / a and w w' = c / a *)
    assert (HAz : A <> 0) by (unfold A; apply not_0_IZR; exact Ha).
    assert (Hsum : A * (w + w') = - IZR b).
    { assert (H0 : (w - w') * (A * (w + w') + IZR b) = 0).
      { unfold A in *. replace ((w - w') * (IZR a * (w + w') + IZR b))
          with ((IZR a * w ^ 2 + IZR b * w + IZR c) - (IZR a * w' ^ 2 + IZR b * w' + IZR c))
          by ring. rewrite Hw, Hw'. ring. }
      apply Rmult_integral in H0. destruct H0 as [H0 | H0]; [lra | lra]. }
    assert (Hprod : A * (w * w') = IZR c).
    { replace (A * (w * w')) with (w * (A * (w + w')) - A * w ^ 2) by ring.
      rewrite Hsum. unfold A in *. lra. }
    (* the factorization *)
    assert (Hfac : IZR (a * p * p + b * p * q + c * q * q) = A * (P - Q * w) * (P - Q * w')).
    { rewrite !plus_IZR, !mult_IZR. fold A P Q.
      replace (IZR b) with (- (A * (w + w'))) by lra.
      replace (IZR c) with (A * (w * w')) by lra.
      ring. }
    rewrite Hfac in HN.
    rewrite !Rabs_mult in HN.
    (* |p - q w'| <= |q| (1 + |w - w'|) *)
    assert (Hother : Rabs (P - Q * w') <= Rabs Q * (1 + Rabs (w - w'))).
    { replace (P - Q * w') with (- (Q * w - P) + Q * (w - w')) by ring.
      apply Rle_trans with (Rabs (- (Q * w - P)) + Rabs (Q * (w - w'))); [apply Rabs_triang |].
      rewrite Rabs_Ropp, Rabs_mult. nra. }
    assert (Hpos : 0 <= Rabs (P - Q * w)) by apply Rabs_pos.
    replace (Rabs (P - Q * w)) with (Rabs (Q * w - P)) in HN, Hpos
      by (rewrite <- Rabs_Ropp; f_equal; ring).
    (* 1 <= |a| |q w - p| |p - q w'| <= |a| |q w - p| |q| (1 + |w - w'|) *)
    assert (Hchain : 1 <= Rabs A * Rabs (Q * w - P) * (Rabs Q * (1 + Rabs (w - w')))).
    { apply Rle_trans with (Rabs A * Rabs (Q * w - P) * Rabs (P - Q * w')); [exact HN |].
      apply Rmult_le_compat_l; [| exact Hother].
      apply Rmult_le_pos; [apply Rabs_pos | exact Hpos]. }
    unfold G.
    apply Rmult_le_reg_l with (Rabs A * (1 + Rabs (w - w'))).
    { apply Rmult_lt_0_compat; lra. }
    rewrite Rinv_r by (apply Rgt_not_eq, Rmult_lt_0_compat; lra).
    replace (Rabs A * (1 + Rabs (w - w')) * (Rabs Q * Rabs (Q * w - P)))
      with (Rabs A * Rabs (Q * w - P) * (Rabs Q * (1 + Rabs (w - w')))) by ring.
    exact Hchain.
Qed.
