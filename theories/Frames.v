(** An enclosure of the inverse of a frame.

    A frame W and an approximate inverse D are dyadic matrices. [winv_encl]
    bounds |I - D W| and |I - W D| by th < 1 from their interval values, and
    returns the ball about D of radius |D| th / (1 - th); [winv_encl_sound]:
    W then has an inverse, and every inverse of W lies in the ball. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat RegResidual TMEval TMat Step Osc CellTM.

Import ListNotations.
Local Open Scope R_scope.

Section Frames.

Variable prec : F.precision.

Definition winv_encl (W D : list (list (Z * Z))) : option imat :=
  let WI := idmat prec 14 14 W in
  let DI := idmat prec 14 14 D in
  let E1 := isub prec 14 14 (iI prec 14) (imm prec 14 14 14 DI WI) in
  let E2 := isub prec 14 14 (iI prec 14) (imm prec 14 14 14 WI DI) in
  let th := iupmax prec (map (irowsum prec 14 E1) (seq 0 14) ++ map (irowsum prec 14 E2) (seq 0 14)) in
  let nD := iupmax prec (map (irowsum prec 14 DI) (seq 0 14)) in
  if inorm_le prec 14 14 E1 th && inorm_le prec 14 14 E2 th && inorm_le prec 14 14 DI nD
     && ipos (I.sub prec (I.fromZ prec 1) th) then
    Some (iball prec 14 14 DI (I.mul prec (I.div prec nD (I.sub prec (I.fromZ prec 1) th)) th))
  else None.

End Frames.

(** Conversion unfolds the wrapper before the interval computations it
    names. *)
Strategy expand [winv_encl].

Section FramesSound.

Variable prec : F.precision.

Lemma if_some_i :
  forall {A : Type} (b : bool) (x y : A), (if b then Some x else None) = Some y -> b = true /\ x = y.
Proof. intros A b x y H. destruct b; [injection H as ->; split; reflexivity | discriminate]. Qed.

Lemma iupmax_point' : forall L, exists x, contains (I.convert (iupmax prec L)) (Xreal x).
Proof. intros L. unfold iupmax. eexists. apply I.singleton_correct. Qed.

(** What a successful call has checked, with the matrices named. *)
Lemma winv_encl_checks :
  forall W D WiI, winv_encl prec W D = Some WiI ->
  let WI := idmat prec 14 14 W in
  let DI := idmat prec 14 14 D in
  let E1 := isub prec 14 14 (iI prec 14) (imm prec 14 14 14 DI WI) in
  let E2 := isub prec 14 14 (iI prec 14) (imm prec 14 14 14 WI DI) in
  let th := iupmax prec (map (irowsum prec 14 E1) (seq 0 14) ++ map (irowsum prec 14 E2) (seq 0 14)) in
  let nD := iupmax prec (map (irowsum prec 14 DI) (seq 0 14)) in
  inorm_le prec 14 14 E1 th = true /\ inorm_le prec 14 14 E2 th = true /\ inorm_le prec 14 14 DI nD = true /\
  ipos (I.sub prec (I.fromZ prec 1) th) = true /\
  WiI = iball prec 14 14 DI (I.mul prec (I.div prec nD (I.sub prec (I.fromZ prec 1) th)) th).
Proof.
  intros W D WiI H. unfold winv_encl in H. cbv zeta in H |- *.
  destruct (if_some_i _ _ _ H) as [Hc HWi]. clear H.
  apply andb_prop in Hc. destruct Hc as [Hc H4]. apply andb_prop in Hc. destruct Hc as [Hc H3].
  apply andb_prop in Hc. destruct Hc as [H1 H2].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. symmetry. exact HWi.
Qed.

Theorem winv_encl_sound :
  forall W D WiI, winv_encl prec W D = Some WiI ->
  (exists X, is_inv 14 (dmatR W) X) /\
  (forall X, is_inv 14 (dmatR W) X -> icont 14 14 WiI X).
Proof.
  intros W D WiI H. assert (HC := winv_encl_checks W D WiI H). clear H.
  set (WI := idmat prec 14 14 W) in HC. set (DI := idmat prec 14 14 D) in HC.
  set (E1 := isub prec 14 14 (iI prec 14) (imm prec 14 14 14 DI WI)) in HC.
  set (E2 := isub prec 14 14 (iI prec 14) (imm prec 14 14 14 WI DI)) in HC.
  set (th := iupmax prec (map (irowsum prec 14 E1) (seq 0 14) ++ map (irowsum prec 14 E2) (seq 0 14))) in HC.
  set (nD := iupmax prec (map (irowsum prec 14 DI) (seq 0 14))) in HC.
  destruct HC as (H1 & H2 & H3 & H4 & HWi). subst WiI.
  destruct (iupmax_point' (map (irowsum prec 14 E1) (seq 0 14) ++ map (irowsum prec 14 E2) (seq 0 14))) as [t Ht].
  fold th in Ht.
  destruct (iupmax_point' (map (irowsum prec 14 DI) (seq 0 14))) as [n Hn]. fold nD in Hn.
  assert (HW : icont 14 14 WI (dmatR W)) by apply idmat_correct.
  assert (HD : icont 14 14 DI (dmatR D)) by apply idmat_correct.
  assert (NE1 : mnorm 14 14 (msub mI (mm 14 (dmatR D) (dmatR W))) <= t).
  { apply (inorm_le_correct prec 14 14 E1 _ th t); [lia | | exact Ht | exact H1].
    apply isub_correct; [apply iI_correct | apply imm_correct; assumption]. }
  assert (NE2 : mnorm 14 14 (msub mI (mm 14 (dmatR W) (dmatR D))) <= t).
  { apply (inorm_le_correct prec 14 14 E2 _ th t); [lia | | exact Ht | exact H2].
    apply isub_correct; [apply iI_correct | apply imm_correct; assumption]. }
  assert (ND : mnorm 14 14 (dmatR D) <= n) by exact (inorm_le_correct prec 14 14 DI _ nD n ltac:(lia) HD Hn H3).
  assert (Hlt : t < 1).
  { assert (Hs1 := I.sub_correct prec (I.fromZ prec 1) th (Xreal (IZR 1)) (Xreal t) (I.fromZ_correct prec 1) Ht).
    assert (Hp := sign_pos _ (IZR 1 - t) Hs1 H4). lra. }
  assert (Ht0 : 0 <= t) by (eapply Rle_trans; [apply mnorm_nonneg | exact NE1]).
  destruct (approx_inverse 14 (dmatR W) (dmatR D) t NE1 NE2 Hlt) as [X0 [HX0l [HX0r _]]].
  split.
  - exists X0. intros i j Hi Hj. split; [apply HX0l | apply HX0r]; assumption.
  - intros X HX.
    assert (Hrad : contains (I.convert (I.mul prec (I.div prec nD (I.sub prec (I.fromZ prec 1) th)) th))
                     (Xreal (n / (1 - t) * t))).
    { assert (Hs1 := I.sub_correct prec (I.fromZ prec 1) th (Xreal (IZR 1)) (Xreal t) (I.fromZ_correct prec 1) Ht).
      change (Xsub (Xreal (IZR 1)) (Xreal t)) with (Xreal (IZR 1 - t)) in Hs1.
      assert (Hd1 := I.div_correct prec _ _ _ _ Hn Hs1). rewrite Xdiv_r in Hd1 by lra.
      exact (I.mul_correct prec _ _ _ _ Hd1 Ht). }
    apply (iball_correct prec 14 14 DI _ (dmatR D) X (n / (1 - t) * t) HD Hrad).
    (* |X - D| <= |X| |I - W D| and |X| <= |D| / (1 - t) *)
    destruct (approx_inverse 14 (dmatR W) (dmatR D) t NE1 NE2 Hlt) as [X1 [HX1l [HX1r HX1n]]].
    assert (HXX1 : forall i j, (i < 14)%nat -> (j < 14)%nat -> X i j = X1 i j).
    { intros i j Hi Hj. apply (inv_unique 14 (dmatR W)); [exact HX | | exact Hi | exact Hj].
      intros i' j' Hi' Hj'. split; [apply HX1l | apply HX1r]; assumption. }
    assert (HXn : mnorm 14 14 X <= n / (1 - t)).
    { rewrite (mnorm_ext 14 14 X X1) by exact HXX1. eapply Rle_trans; [exact HX1n|].
      unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact ND]. }
    eapply Rle_trans; [apply (inverse_near 14 (dmatR W) (dmatR D) X)|].
    + intros i j Hi Hj. exact (proj1 (HX i j Hi Hj)).
    + apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact HXn | exact NE2].
Qed.

End FramesSound.
