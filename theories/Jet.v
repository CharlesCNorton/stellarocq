(** The node data of the three-dimensional manufactured problem at a radius s
    and a step h, as expressions.

    The mapping of the collocated problem (gen/mms_colloc.py, case 3d) has, in
    the modes (0,0), (0,3), (1,-3), (1,0), (1,3) of Physics.v,

      R = 1 + p0 s + p1 s^2,  -c1,  0,  c2 sqrt s,  c1 sqrt s,
      Z = 0,                  -c1,  0,  c2 sqrt s, -c1 sqrt s,
      lambda = 0, 0, l2 sqrt s, l3 sqrt s, l4 sqrt s,

    with c1 = 0.005, c2 = 0.05, l2 = (p9 + p10) / 2, l3 = p8, l4 = (p9 - p10) / 2,
    p0, p1, p8, p9, p10 the parameters of FITTED_P, iota = 0.42 + 0.13 s, phip =
    0.035 / (2 pi), and mu0 p' = -(4 pi / 10^7) 160000; every decimal here is the
    binary64 number the example carries, an exact dyadic.

    [jet_e k] is the value of slot k of RegResidual's outer environment, an
    expression over s (slot 0) and h (slot 1): the coefficient at s, the two
    difference quotients toward s - h and s + h and their difference over h,
    lambda and iota at s -+ h/2 with their difference over h, and the roots of
    the five radii. Every quotient is written without h in a denominator, so
    the expressions stay regular as h goes to 0: for c sqrt s the quotients are
    c / (sqrt s + sqrt (s -+ h)) and their difference over h is
    -2 c / ((a + b) (b + c') (a + c')), a, b, c' the roots of s + h, s, s - h.
    [jet_values] gives what they evaluate to, [jet_rel] the relations
    RegResidual's theorems assume. *)

From Coq Require Import ZArith Reals List Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr DivDiff Force Continuum RegResidual.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The constants                                                     *)

Definition dyad (m e : Z) : R := IZR m * powerRZ 2 e.
Definition edyad (m e : Z) : expr := Emul (EfromZ m) (Epow2 e).

Lemma xeval_edyad : forall E m e, xeval E (edyad m e) = Xreal (dyad m e).
Proof. intros. reflexivity. Qed.

Definition p0 : R := dyad (-6117960975932355) (-64).
Definition p1 : R := dyad (-2380301512278831) (-68).
Definition p8 : R := dyad (-3736202182707901) (-56).
Definition p9 : R := dyad (-8443042306014537) (-58).
Definition p10 : R := dyad 3961114860168361 (-58).
Definition c2 : R := dyad 3602879701896397 (-56).
Definition c1 : R := dyad 5764607523034235 (-60).
Definition i0 : R := dyad 7566047373982433 (-54).
Definition i1 : R := dyad 1170935903116329 (-53).
Definition phe : R := dyad 1261007895663739 (-55).

Definition ep0 : expr := edyad (-6117960975932355) (-64).
Definition ep1 : expr := edyad (-2380301512278831) (-68).
Definition ep8 : expr := edyad (-3736202182707901) (-56).
Definition ep9 : expr := edyad (-8443042306014537) (-58).
Definition ep10 : expr := edyad 3961114860168361 (-58).
Definition ec2 : expr := edyad 3602879701896397 (-56).
Definition ec1 : expr := edyad 5764607523034235 (-60).
Definition ei0 : expr := edyad 7566047373982433 (-54).
Definition ei1 : expr := edyad 1170935903116329 (-53).
Definition ephe : expr := edyad 1261007895663739 (-55).

(** The amplitude of sqrt s in each mode, and lambda's. *)
Definition l2 : R := (p9 + p10) / 2.
Definition l3 : R := p8.
Definition l4 : R := (p9 - p10) / 2.

Definition phip3 : R := phe / (2 * PI).
Definition mpp3 : R := IZR 4 * PI / IZR 10000000 * IZR (-160000).

(* ---------------------------------------------------------------- *)
(* The coefficient functions                                         *)

(** The polynomial and constant parts and the sqrt amplitudes, by mode. *)
Definition polyR (k : nat) (s : R) : R :=
  match k with O => 1 + p0 * s + p1 * (s * s) | 1%nat => - c1 | _ => 0 end.
Definition ampR (k : nat) : R := match k with 3%nat => c2 | 4%nat => c1 | _ => 0 end.
Definition polyZ (k : nat) (s : R) : R := match k with 1%nat => - c1 | _ => 0 end.
Definition ampZ (k : nat) : R := match k with 3%nat => c2 | 4%nat => - c1 | _ => 0 end.
Definition ampL (k : nat) : R := match k with 2%nat => l2 | 3%nat => l3 | 4%nat => l4 | _ => 0 end.

Definition XR (k : nat) (s : R) : R := polyR k s + ampR k * sqrt s.
Definition XZ (k : nat) (s : R) : R := polyZ k s + ampZ k * sqrt s.
Definition XL (k : nat) (s : R) : R := ampL k * sqrt s.
Definition iota3 (s : R) : R := i0 + i1 * s.

(* ---------------------------------------------------------------- *)
(* The expressions                                                   *)

Definition es : expr := Evar 0.
Definition eh : expr := Evar 1.
Definition ehalf2 : expr := Ediv (EfromZ 1) (EfromZ 2).

(** The roots of s - h, s - h/2, s, s + h/2, s + h. *)
Definition eroot (i : nat) : expr :=
  match i with
  | O => Esqrt (Esub es eh)
  | 1%nat => Esqrt (Esub es (Emul ehalf2 eh))
  | 2%nat => Esqrt es
  | 3%nat => Esqrt (Eadd es (Emul ehalf2 eh))
  | _ => Esqrt (Eadd es eh)
  end.

(** The node value, the two difference quotients and the second difference
    of a coefficient p(s) + a sqrt s, p of degree at most two given by its
    value, slope and second derivative expressions. *)
Definition jx (pv : expr) (a : expr) : expr := Eadd pv (Emul a (eroot 2)).
Definition jdm (ps pss : expr) (a : expr) : expr :=
  Eadd (Esub ps (Emul (Emul ehalf2 pss) eh)) (Ediv a (Eadd (eroot 2) (eroot 0))).
Definition jdp (ps pss : expr) (a : expr) : expr :=
  Eadd (Eadd ps (Emul (Emul ehalf2 pss) eh)) (Ediv a (Eadd (eroot 4) (eroot 2))).
Definition je (pss : expr) (a : expr) : expr :=
  Esub pss
       (Ediv (Emul (EfromZ 2) a)
             (Emul (Emul (Eadd (eroot 4) (eroot 2)) (Eadd (eroot 2) (eroot 0)))
                   (Eadd (eroot 4) (eroot 0)))).

(** The polynomial parts by mode: value, slope, second derivative. *)
Definition epolyR (k : nat) : expr * expr * expr :=
  match k with
  | O => (Eadd (EfromZ 1) (Eadd (Emul ep0 es) (Emul ep1 (Emul es es))),
          Eadd ep0 (Emul (Emul (EfromZ 2) ep1) es), Emul (EfromZ 2) ep1)
  | 1%nat => (Eneg ec1, EfromZ 0, EfromZ 0)
  | _ => (EfromZ 0, EfromZ 0, EfromZ 0)
  end.
Definition eampR (k : nat) : expr :=
  match k with 3%nat => ec2 | 4%nat => ec1 | _ => EfromZ 0 end.
Definition epolyZ (k : nat) : expr * expr * expr :=
  match k with 1%nat => (Eneg ec1, EfromZ 0, EfromZ 0) | _ => (EfromZ 0, EfromZ 0, EfromZ 0) end.
Definition eampZ (k : nat) : expr :=
  match k with 3%nat => ec2 | 4%nat => Eneg ec1 | _ => EfromZ 0 end.
Definition eampL (k : nat) : expr :=
  match k with
  | 2%nat => Emul ehalf2 (Eadd ep9 ep10)
  | 3%nat => ep8
  | 4%nat => Emul ehalf2 (Esub ep9 ep10)
  | _ => EfromZ 0
  end.

Definition ephip : expr := Ediv ephe (Emul (EfromZ 2) Epi).
Definition empp : expr :=
  Emul (Ediv (Emul (EfromZ 4) Epi) (EfromZ 10000000)) (EfromZ (-160000)).

(** The four blocks of the jet of one series. *)
Definition jet4 (pe : expr * expr * expr) (a : expr) (w : nat) : expr :=
  let '(pv, ps, pss) := pe in
  match w with
  | O => jx pv a
  | 1%nat => jdm ps pss a
  | 2%nat => jdp ps pss a
  | _ => je pss a
  end.

(** Slot k of the outer environment of modes3d at the collocation angles
    (u, v), with s in slot 0 and h in slot 1; the two sources are left as the
    expressions fs and fu. *)
Definition jet_e (u v fs fu : expr) (k : nat) : expr :=
  let K := 5%nat in
  if (k =? 0)%nat then es
  else if (k =? 1)%nat then eh
  else if (k =? 2)%nat then EfromZ 0
  else if (k =? 3)%nat then u else if (k =? 4)%nat then u else if (k =? 5)%nat then EfromZ 0
  else if (k =? 6)%nat then v else if (k =? 7)%nat then v else if (k =? 8)%nat then EfromZ 0
  else if (k =? 9)%nat then ephip else if (k =? 10)%nat then ephip
  else if (k =? 11)%nat then EfromZ 0
  else if (k <? 12 + 4 * K)%nat then
    (let i := (k - 12)%nat in jet4 (epolyR (i mod K)) (eampR (i mod K)) (i / K))
  else if (k <? 12 + 8 * K)%nat then
    (let i := (k - 12 - 4 * K)%nat in jet4 (epolyZ (i mod K)) (eampZ (i mod K)) (i / K))
  else if (k <? 12 + 9 * K)%nat then
    Emul (eampL (k - 12 - 8 * K)%nat) (eroot 1)
  else if (k <? 12 + 10 * K)%nat then
    Emul (eampL (k - 12 - 9 * K)%nat) (eroot 3)
  else if (k <? 12 + 11 * K)%nat then
    Ediv (eampL (k - 12 - 10 * K)%nat) (Eadd (eroot 3) (eroot 1))
  else if (k =? 12 + 11 * K)%nat then Eadd ei0 (Emul ei1 (Esub es (Emul ehalf2 eh)))
  else if (k =? 13 + 11 * K)%nat then Eadd ei0 (Emul ei1 (Eadd es (Emul ehalf2 eh)))
  else if (k =? 14 + 11 * K)%nat then ei1
  else if (k <? 20 + 11 * K)%nat then eroot (k - 15 - 11 * K)
  else if (k =? 20 + 11 * K)%nat then eh
  else if (k =? 21 + 11 * K)%nat then empp
  else if (k =? 22 + 11 * K)%nat then fs
  else if (k =? 23 + 11 * K)%nat then fu
  else EfromZ 0.

(* ---------------------------------------------------------------- *)
(* Values                                                            *)

(** The environment of the two inputs. *)
Definition base (s h : R) : env ExtendedR := of_list [Xreal s; Xreal h].

Lemma base_s : forall s h, xeval (base s h) es = Xreal s.
Proof. intros. reflexivity. Qed.
Lemma base_h : forall s h, xeval (base s h) eh = Xreal h.
Proof. intros. reflexivity. Qed.

Definition rad (i : nat) (s h : R) : R :=
  match i with O => s - h | 1%nat => s - h / 2 | 2%nat => s | 3%nat => s + h / 2 | _ => s + h end.

Lemma xeval_half2 : forall E, xeval E ehalf2 = Xreal (1 / 2).
Proof. intros E. unfold ehalf2. cbn [xeval]. apply Xdiv_r. lra. Qed.

(** The real reading of the two inputs. *)
Definition gsh (s h : R) (k : nat) : R := match k with O => s | 1%nat => h | _ => 0 end.

Lemma base_slots :
  forall s h k, (k < 2)%nat -> eget k (base s h) Xnan = Xreal (gsh s h k).
Proof. intros s h k Hk. destruct k as [|[|k]]; [reflexivity | reflexivity | lia]. Qed.

Lemma IZR2_nz : IZR 2 <> 0.
Proof. apply not_0_IZR. lia. Qed.

Lemma eroot_val : forall s h i, xeval (base s h) (eroot i) = Xreal (sqrt (rad i s h)).
Proof.
  intros s h i.
  rewrite (xeval_rv (base s h) (gsh s h) (eroot i)).
  - f_equal. destruct i as [|[|[|[|i]]]]; unfold eroot, rad, ehalf2, es, eh; cbn [rv gsh];
      f_equal; field.
  - intros k Hk. apply base_slots.
    destruct i as [|[|[|[|i]]]]; unfold eroot, ehalf2, es, eh in Hk; cbn [occurs] in Hk;
      repeat match type of Hk with _ \/ _ => destruct Hk as [Hk|Hk] end;
      try contradiction; subst; lia.
  - destruct i as [|[|[|[|i]]]]; unfold eroot, ehalf2, es, eh; cbn [defd rv];
      repeat split; exact IZR2_nz.
Qed.

(** The jet of p(s) + a sqrt s, p = alpha + beta s + gamma s^2, without h in a
    denominator. *)
Section Identities.
Variables (al be ga A s h : R).
Hypothesis Hh : h <> 0.
Hypothesis Hs : - s < h < s.

Let X (t : R) : R := al + be * t + ga * (t * t) + A * sqrt t.

Lemma sq_rel : forall a b, 0 < a -> 0 < b -> sqrt a - sqrt b = (a - b) / (sqrt a + sqrt b).
Proof.
  intros a b Ha Hb. assert (Sa := sqrt_lt_R0 a Ha). assert (Sb := sqrt_lt_R0 b Hb).
  assert (Qa := sqrt_sqrt a (Rlt_le _ _ Ha)). assert (Qb := sqrt_sqrt b (Rlt_le _ _ Hb)).
  field_simplify_eq; [| lra]. nra.
Qed.

Lemma jid_dm :
  be + 2 * ga * s - 1 / 2 * (2 * ga) * h + A / (sqrt s + sqrt (s - h)) = (X s - X (s - h)) / h.
Proof.
  unfold X. assert (R1 := sq_rel s (s - h) ltac:(lra) ltac:(lra)).
  assert (S1 := sqrt_lt_R0 s ltac:(lra)). assert (S0 := sqrt_lt_R0 (s - h) ltac:(lra)).
  replace (s - (s - h)) with h in R1 by ring.
  replace (al + be * s + ga * (s * s) + A * sqrt s - (al + be * (s - h) + ga * ((s - h) * (s - h)) + A * sqrt (s - h)))
    with (h * (be + 2 * ga * s - ga * h) + A * (sqrt s - sqrt (s - h))) by ring.
  rewrite R1. field. repeat split; first [exact Hh | lra].
Qed.

Lemma jid_dp :
  be + 2 * ga * s + 1 / 2 * (2 * ga) * h + A / (sqrt (s + h) + sqrt s) = (X (s + h) - X s) / h.
Proof.
  unfold X. assert (R1 := sq_rel (s + h) s ltac:(lra) ltac:(lra)).
  assert (S1 := sqrt_lt_R0 s ltac:(lra)). assert (S2 := sqrt_lt_R0 (s + h) ltac:(lra)).
  replace (s + h - s) with h in R1 by ring.
  replace (al + be * (s + h) + ga * ((s + h) * (s + h)) + A * sqrt (s + h) - (al + be * s + ga * (s * s) + A * sqrt s))
    with (h * (be + 2 * ga * s + ga * h) + A * (sqrt (s + h) - sqrt s)) by ring.
  rewrite R1. field. repeat split; first [exact Hh | lra].
Qed.

Lemma jid_e :
  2 * ga - 2 * A / ((sqrt (s + h) + sqrt s) * (sqrt s + sqrt (s - h)) * (sqrt (s + h) + sqrt (s - h)))
  = ((X (s + h) - X s) / h - (X s - X (s - h)) / h) / h.
Proof.
  rewrite <- jid_dm, <- jid_dp.
  assert (S0 := sqrt_lt_R0 (s - h) ltac:(lra)). assert (S1 := sqrt_lt_R0 s ltac:(lra)).
  assert (S2 := sqrt_lt_R0 (s + h) ltac:(lra)).
  assert (R1 := sq_rel (s + h) (s - h) ltac:(lra) ltac:(lra)).
  replace (s + h - (s - h)) with (2 * h) in R1 by ring.
  set (a := sqrt (s + h)) in *. set (b := sqrt s) in *. set (c := sqrt (s - h)) in *.
  (* A / (a + b) - A / (b + c) = A (c - a) / ((a + b) (b + c)), and c - a = - 2 h / (a + c) *)
  assert (E1 : A / (a + b) - A / (b + c) = A * (c - a) / ((a + b) * (b + c))) by (field; lra).
  assert (E2 : c - a = - (2 * h / (a + c))) by lra.
  rewrite E2 in E1.
  assert (Ha : 0 < a + b) by lra. assert (Hb : 0 < b + c) by lra. assert (Hc : 0 < a + c) by lra.
  assert (E3 : A / (a + b) = A / (b + c) + A * - (2 * h / (a + c)) / ((a + b) * (b + c))) by lra.
  rewrite E3. field. repeat split; first [exact Hh | lra].
Qed.

End Identities.

Lemma Xadd_rr : forall a b, Xadd (Xreal a) (Xreal b) = Xreal (a + b).
Proof. reflexivity. Qed.
Lemma Xsub_rr : forall a b, Xsub (Xreal a) (Xreal b) = Xreal (a - b).
Proof. reflexivity. Qed.
Lemma Xmul_rr : forall a b, Xmul (Xreal a) (Xreal b) = Xreal (a * b).
Proof. reflexivity. Qed.
Lemma Xneg_r : forall a, Xneg (Xreal a) = Xreal (- a).
Proof. reflexivity. Qed.

(** The value of p(s) + A sqrt s at a radius. *)
Definition jX (al be ga A t : R) : R := al + be * t + ga * (t * t) + A * sqrt t.

(** The four components of [jet4]: the node value, the two difference
    quotients and their difference over h. *)
Lemma jet4_val :
  forall (al be ga A s h : R) (pv ps pss a : expr),
  h <> 0 -> - s < h < s ->
  xeval (base s h) pv = Xreal (al + be * s + ga * (s * s)) ->
  xeval (base s h) ps = Xreal (be + 2 * ga * s) ->
  xeval (base s h) pss = Xreal (2 * ga) ->
  xeval (base s h) a = Xreal A ->
  xeval (base s h) (jet4 (pv, ps, pss) a 0) = Xreal (jX al be ga A s) /\
  xeval (base s h) (jet4 (pv, ps, pss) a 1) = Xreal ((jX al be ga A s - jX al be ga A (s - h)) / h) /\
  xeval (base s h) (jet4 (pv, ps, pss) a 2) = Xreal ((jX al be ga A (s + h) - jX al be ga A s) / h) /\
  xeval (base s h) (jet4 (pv, ps, pss) a 3) =
    Xreal (((jX al be ga A (s + h) - jX al be ga A s) / h
            - (jX al be ga A s - jX al be ga A (s - h)) / h) / h).
Proof.
  intros al be ga A s h pv ps pss a Hh Hs Hv Hp Hq Ha.
  assert (S0 := sqrt_lt_R0 (s - h) ltac:(lra)). assert (S2 := sqrt_lt_R0 s ltac:(lra)).
  assert (S4 := sqrt_lt_R0 (s + h) ltac:(lra)).
  assert (R0 := eroot_val s h 0). assert (R2 := eroot_val s h 2). assert (R4 := eroot_val s h 4).
  cbn [rad] in R0, R2, R4.
  unfold jet4, jx, jdm, jdp, je. cbn [xeval].
  rewrite Hv, Hp, Hq, Ha, R0, R2, R4, xeval_half2, base_h.
  repeat (first [rewrite Xadd_rr | rewrite Xsub_rr | rewrite Xmul_rr]).
  split; [| split; [| split]].
  - unfold jX. reflexivity.
  - rewrite Xdiv_r by lra. rewrite Xadd_rr. f_equal. unfold jX.
    rewrite <- (jid_dm al be ga A s h Hh Hs). reflexivity.
  - rewrite Xdiv_r by lra. rewrite Xadd_rr. f_equal. unfold jX.
    rewrite <- (jid_dp al be ga A s h Hh Hs). reflexivity.
  - rewrite Xdiv_r by (apply Rmult_integral_contrapositive_currified;
                        [apply Rmult_integral_contrapositive_currified|]; lra).
    rewrite Xsub_rr. f_equal. unfold jX.
    rewrite <- (jid_e al be ga A s h Hh Hs). field. repeat split; first [exact Hh | lra].
Qed.

(** An expression over the two inputs, with nonzero divisors, has its real
    value. *)
Lemma xeval_base :
  forall s h e, (forall k, occurs k e -> (k < 2)%nat) -> defd (gsh s h) e ->
  xeval (base s h) e = Xreal (rv (gsh s h) e).
Proof.
  intros s h e Ho Hd. apply xeval_rv; [| exact Hd].
  intros k Hk. apply base_slots. exact (Ho k Hk).
Qed.

Ltac occ2 :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; cbn [occurs] in Hk;
  repeat match type of Hk with _ \/ _ => destruct Hk as [Hk|Hk] end;
  try contradiction; subst; lia.

(** Evaluate a concrete expression over the inputs and close with a field
    identity. *)
Ltac xbase :=
  rewrite xeval_base;
  [ f_equal; cbn [rv gsh]; unfold p0, p1, p8, p9, p10, c1, c2, i0, i1, dyad;
    repeat match goal with |- context [powerRZ 2 ?e] =>
      let q := fresh "q" in set (q := powerRZ 2 e) end;
    field
  | occ2
  | cbn [defd rv]; repeat split; try exact IZR2_nz ].

(** Each mode of R and Z is p(s) + A sqrt s with p of degree two, and its
    expressions evaluate to p, p', p'' and A. *)
Lemma modeR :
  forall s h k, (k < 5)%nat ->
  exists al be ga A,
    xeval (base s h) (fst (fst (epolyR k))) = Xreal (al + be * s + ga * (s * s)) /\
    xeval (base s h) (snd (fst (epolyR k))) = Xreal (be + 2 * ga * s) /\
    xeval (base s h) (snd (epolyR k)) = Xreal (2 * ga) /\
    xeval (base s h) (eampR k) = Xreal A /\
    (forall t, XR k t = jX al be ga A t).
Proof.
  intros s h k Hk.
  destruct k as [|[|[|[|[|k]]]]]; try lia; cbn [epolyR fst snd eampR];
    unfold ep0, ep1, ec1, ec2, edyad, es.
  - exists 1, p0, p1, 0.
    split; [xbase|].
    split; [xbase|].
    split; [xbase|].
    split; [xbase|].
    intros t. unfold XR, jX, polyR, ampR. ring.
  - exists (- c1), 0, 0, 0. repeat split; try xbase. intros t. unfold XR, jX, polyR, ampR. ring.
  - exists 0, 0, 0, 0. repeat split; try xbase. intros t. unfold XR, jX, polyR, ampR. ring.
  - exists 0, 0, 0, c2. repeat split; try xbase. intros t. unfold XR, jX, polyR, ampR. ring.
  - exists 0, 0, 0, c1. repeat split; try xbase. intros t. unfold XR, jX, polyR, ampR. ring.
Qed.

Lemma modeZ :
  forall s h k, (k < 5)%nat ->
  exists al be ga A,
    xeval (base s h) (fst (fst (epolyZ k))) = Xreal (al + be * s + ga * (s * s)) /\
    xeval (base s h) (snd (fst (epolyZ k))) = Xreal (be + 2 * ga * s) /\
    xeval (base s h) (snd (epolyZ k)) = Xreal (2 * ga) /\
    xeval (base s h) (eampZ k) = Xreal A /\
    (forall t, XZ k t = jX al be ga A t).
Proof.
  intros s h k Hk.
  destruct k as [|[|[|[|[|k]]]]]; try lia; cbn [epolyZ fst snd eampZ];
    unfold ec1, ec2, edyad.
  - exists 0, 0, 0, 0. repeat split; try xbase. intros t. unfold XZ, jX, polyZ, ampZ. ring.
  - exists (- c1), 0, 0, 0. repeat split; try xbase. intros t. unfold XZ, jX, polyZ, ampZ. ring.
  - exists 0, 0, 0, 0. repeat split; try xbase. intros t. unfold XZ, jX, polyZ, ampZ. ring.
  - exists 0, 0, 0, c2. repeat split; try xbase. intros t. unfold XZ, jX, polyZ, ampZ. ring.
  - exists 0, 0, 0, (- c1). repeat split; try xbase. intros t. unfold XZ, jX, polyZ, ampZ. ring.
Qed.

Lemma modeL : forall s h k, (k < 5)%nat -> xeval (base s h) (eampL k) = Xreal (ampL k).
Proof.
  intros s h k Hk.
  destruct k as [|[|[|[|[|k]]]]]; try lia; cbn [eampL ampL];
    unfold l2, l3, l4, ep8, ep9, ep10, ehalf2, edyad; xbase.
Qed.

(* ---------------------------------------------------------------- *)
(* The outer environment                                             *)

Definition ntop : nat := lm (rk0 modes3d).

Lemma ntop_val : ntop = 87%nat.
Proof. reflexivity. Qed.

Definition outer (eu ev efs efu : expr) (s h : R) : env ExtendedR :=
  of_list (map (fun k => xeval (base s h) (jet_e eu ev efs efu k)) (seq 0 ntop)).

Lemma outer_get :
  forall eu ev efs efu s h k, (k < ntop)%nat ->
  eget k (outer eu ev efs efu s h) Xnan = xeval (base s h) (jet_e eu ev efs efu k).
Proof.
  intros eu ev efs efu s h k Hk. unfold outer. rewrite eget_of_list. apply nth_map_seq0. exact Hk.
Qed.

(** Which expression each slot carries. *)
Lemma jet_slots_R :
  forall eu ev efs efu k, (k < 5)%nat ->
  jet_e eu ev efs efu (o_xR k) = jet4 (epolyR k) (eampR k) 0 /\
  jet_e eu ev efs efu (o_dmR modes3d k) = jet4 (epolyR k) (eampR k) 1 /\
  jet_e eu ev efs efu (o_dpR modes3d k) = jet4 (epolyR k) (eampR k) 2 /\
  jet_e eu ev efs efu (o_eR modes3d k) = jet4 (epolyR k) (eampR k) 3.
Proof.
  intros eu ev efs efu k Hk. destruct k as [|[|[|[|[|k]]]]]; try lia; repeat split; reflexivity.
Qed.

Lemma jet_slots_Z :
  forall eu ev efs efu k, (k < 5)%nat ->
  jet_e eu ev efs efu (o_xZ modes3d k) = jet4 (epolyZ k) (eampZ k) 0 /\
  jet_e eu ev efs efu (o_dmZ modes3d k) = jet4 (epolyZ k) (eampZ k) 1 /\
  jet_e eu ev efs efu (o_dpZ modes3d k) = jet4 (epolyZ k) (eampZ k) 2 /\
  jet_e eu ev efs efu (o_eZ modes3d k) = jet4 (epolyZ k) (eampZ k) 3.
Proof.
  intros eu ev efs efu k Hk. destruct k as [|[|[|[|[|k]]]]]; try lia; repeat split; reflexivity.
Qed.

Lemma jet_slots_L :
  forall eu ev efs efu k, (k < 5)%nat ->
  jet_e eu ev efs efu (o_Lm modes3d k) = Emul (eampL k) (eroot 1) /\
  jet_e eu ev efs efu (o_Lp modes3d k) = Emul (eampL k) (eroot 3) /\
  jet_e eu ev efs efu (o_Ldd modes3d k) = Ediv (eampL k) (Eadd (eroot 3) (eroot 1)).
Proof.
  intros eu ev efs efu k Hk. destruct k as [|[|[|[|[|k]]]]]; try lia; repeat split; reflexivity.
Qed.

Lemma jet_slots_rest :
  forall eu ev efs efu,
  jet_e eu ev efs efu 3 = eu /\ jet_e eu ev efs efu 4 = eu /\ jet_e eu ev efs efu 5 = EfromZ 0 /\
  jet_e eu ev efs efu 6 = ev /\ jet_e eu ev efs efu 7 = ev /\ jet_e eu ev efs efu 8 = EfromZ 0 /\
  jet_e eu ev efs efu 9 = ephip /\ jet_e eu ev efs efu 10 = ephip /\
  jet_e eu ev efs efu 11 = EfromZ 0 /\
  jet_e eu ev efs efu (o_im modes3d) = Eadd ei0 (Emul ei1 (Esub es (Emul ehalf2 eh))) /\
  jet_e eu ev efs efu (o_ip modes3d) = Eadd ei0 (Emul ei1 (Eadd es (Emul ehalf2 eh))) /\
  jet_e eu ev efs efu (o_idd modes3d) = ei1 /\
  (forall i, (i < 5)%nat -> jet_e eu ev efs efu (o_r modes3d i) = eroot i) /\
  jet_e eu ev efs efu (o_h modes3d) = eh /\ jet_e eu ev efs efu (o_mpp modes3d) = empp /\
  jet_e eu ev efs efu (o_fs modes3d) = efs /\ jet_e eu ev efs efu (o_fu modes3d) = efu.
Proof.
  intros eu ev efs efu. repeat split; try reflexivity.
  intros i Hi. destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity.
Qed.

(** The real values of the node data. *)
Definition dmX (X : R -> R) (s h : R) : R := (X s - X (s - h)) / h.
Definition dpX (X : R -> R) (s h : R) : R := (X (s + h) - X s) / h.
Definition eX (X : R -> R) (s h : R) : R := (dpX X s h - dmX X s h) / h.

Lemma jet_R_vals :
  forall eu ev efs efu s h k, h <> 0 -> - s < h < s -> (k < 5)%nat ->
  eget (o_xR k) (outer eu ev efs efu s h) Xnan = Xreal (XR k s) /\
  eget (o_dmR modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (dmX (XR k) s h) /\
  eget (o_dpR modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (dpX (XR k) s h) /\
  eget (o_eR modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (eX (XR k) s h).
Proof.
  intros eu ev efs efu s h k Hh Hs Hk.
  destruct (jet_slots_R eu ev efs efu k Hk) as [J0 [J1 [J2 J3]]].
  destruct (modeR s h k Hk) as [al [be [ga [A [V1 [V2 [V3 [V4 HX]]]]]]]].
  destruct (epolyR k) as [[pv ps] pss] eqn:Ep. cbn [fst snd] in V1, V2, V3.
  destruct (jet4_val al be ga A s h pv ps pss (eampR k) Hh Hs V1 V2 V3 V4) as [W0 [W1 [W2 W3]]].
  assert (Hlt : forall w, (w < 4)%nat -> (12 + 5 * w + k < ntop)%nat) by (intros; unfold ntop, lm, rk0; simpl; lia).
  rewrite !outer_get by (unfold o_xR, o_dmR, o_dpR, o_eR, rK, ntop, lm, rk0; simpl; lia).
  rewrite J0, J1, J2, J3, W0, W1, W2, W3.
  unfold eX, dpX, dmX. rewrite !HX. repeat split.
Qed.

Lemma jet_Z_vals :
  forall eu ev efs efu s h k, h <> 0 -> - s < h < s -> (k < 5)%nat ->
  eget (o_xZ modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (XZ k s) /\
  eget (o_dmZ modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (dmX (XZ k) s h) /\
  eget (o_dpZ modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (dpX (XZ k) s h) /\
  eget (o_eZ modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (eX (XZ k) s h).
Proof.
  intros eu ev efs efu s h k Hh Hs Hk.
  destruct (jet_slots_Z eu ev efs efu k Hk) as [J0 [J1 [J2 J3]]].
  destruct (modeZ s h k Hk) as [al [be [ga [A [V1 [V2 [V3 [V4 HX]]]]]]]].
  destruct (epolyZ k) as [[pv ps] pss] eqn:Ep. cbn [fst snd] in V1, V2, V3.
  destruct (jet4_val al be ga A s h pv ps pss (eampZ k) Hh Hs V1 V2 V3 V4) as [W0 [W1 [W2 W3]]].
  rewrite !outer_get by (unfold o_xZ, o_dmZ, o_dpZ, o_eZ, rK, ntop, lm, rk0; simpl; lia).
  rewrite J0, J1, J2, J3, W0, W1, W2, W3.
  unfold eX, dpX, dmX. rewrite !HX. repeat split.
Qed.

Lemma jet_L_vals :
  forall eu ev efs efu s h k, h <> 0 -> - s < h < s -> (k < 5)%nat ->
  eget (o_Lm modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (XL k (s - h / 2)) /\
  eget (o_Lp modes3d k) (outer eu ev efs efu s h) Xnan = Xreal (XL k (s + h / 2)) /\
  eget (o_Ldd modes3d k) (outer eu ev efs efu s h) Xnan =
    Xreal ((XL k (s + h / 2) - XL k (s - h / 2)) / h).
Proof.
  intros eu ev efs efu s h k Hh Hs Hk.
  destruct (jet_slots_L eu ev efs efu k Hk) as [J0 [J1 J2]].
  assert (M := modeL s h k Hk).
  assert (R1 := eroot_val s h 1). assert (R3 := eroot_val s h 3). cbn [rad] in R1, R3.
  assert (S1 := sqrt_lt_R0 (s - h / 2) ltac:(lra)). assert (S3 := sqrt_lt_R0 (s + h / 2) ltac:(lra)).
  rewrite !outer_get by (unfold o_Lm, o_Lp, o_Ldd, rK, ntop, lm, rk0; simpl; lia).
  rewrite J0, J1, J2. cbn [xeval]. rewrite M, R1, R3, Xmul_rr, Xmul_rr, Xadd_rr, Xdiv_r by lra.
  unfold XL. split; [reflexivity|]. split; [reflexivity|]. f_equal.
  assert (Q := sq_rel (s + h / 2) (s - h / 2) ltac:(lra) ltac:(lra)).
  replace (s + h / 2 - (s - h / 2)) with h in Q by field.
  replace (ampL k * sqrt (s + h / 2) - ampL k * sqrt (s - h / 2))
    with (ampL k * (sqrt (s + h / 2) - sqrt (s - h / 2))) by ring.
  rewrite Q. field. repeat split; first [exact Hh | lra].
Qed.

Lemma jet_rest_vals :
  forall eu ev efs efu u v fs fu s h, h <> 0 -> - s < h < s ->
  xeval (base s h) eu = Xreal u -> xeval (base s h) ev = Xreal v ->
  xeval (base s h) efs = Xreal fs -> xeval (base s h) efu = Xreal fu ->
  let E := outer eu ev efs efu s h in
  (eget 3 E Xnan = Xreal u /\ eget 4 E Xnan = Xreal u /\ eget 5 E Xnan = Xreal 0) /\
  (eget 6 E Xnan = Xreal v /\ eget 7 E Xnan = Xreal v /\ eget 8 E Xnan = Xreal 0) /\
  (eget 9 E Xnan = Xreal phip3 /\ eget 10 E Xnan = Xreal phip3 /\ eget 11 E Xnan = Xreal 0) /\
  (eget (o_im modes3d) E Xnan = Xreal (iota3 (s - h / 2)) /\
   eget (o_ip modes3d) E Xnan = Xreal (iota3 (s + h / 2)) /\
   eget (o_idd modes3d) E Xnan = Xreal i1) /\
  (eget (o_r modes3d 0) E Xnan = Xreal (sqrt (s - h)) /\
   eget (o_r modes3d 1) E Xnan = Xreal (sqrt (s - h / 2)) /\
   eget (o_r modes3d 2) E Xnan = Xreal (sqrt s) /\
   eget (o_r modes3d 3) E Xnan = Xreal (sqrt (s + h / 2)) /\
   eget (o_r modes3d 4) E Xnan = Xreal (sqrt (s + h))) /\
  (eget (o_h modes3d) E Xnan = Xreal h /\ eget (o_mpp modes3d) E Xnan = Xreal mpp3 /\
   eget (o_fs modes3d) E Xnan = Xreal fs /\ eget (o_fu modes3d) E Xnan = Xreal fu).
Proof.
  intros eu ev efs efu u v fs fu s h Hh Hs Hu Hv Hfs Hfu E.
  destruct (jet_slots_rest eu ev efs efu)
    as (J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & Jim & Jip & Jidd & Jr & Jh & Jm & Jfs & Jfu).
  assert (Hphi : xeval (base s h) ephip = Xreal phip3).
  { unfold ephip, ephe. cbn [xeval]. rewrite xeval_edyad, Xmul_rr.
    rewrite Xdiv_r by (assert (PI > 0) by exact PI_RGT_0; lra). reflexivity. }
  assert (Hmpp : xeval (base s h) empp = Xreal mpp3).
  { unfold empp, mpp3. cbn [xeval]. rewrite Xmul_rr.
    rewrite Xdiv_r by (apply not_0_IZR; lia). rewrite Xmul_rr. reflexivity. }
  unfold E. rewrite !outer_get by (unfold o_im, o_ip, o_idd, o_r, o_h, o_mpp, o_fs, o_fu, rK, ntop, lm, rk0;
                                  simpl; lia).
  rewrite J3, J4, J5, J6, J7, J8, J9, J10, J11, Jim, Jip, Jidd, Jh, Jm, Jfs, Jfu.
  rewrite !Jr by lia.
  rewrite !eroot_val. cbn [rad].
  repeat split; try assumption; try reflexivity.
  - unfold iota3, ei0, ei1. cbn [xeval]. rewrite !xeval_edyad, base_s, xeval_half2, base_h.
    repeat (first [rewrite Xadd_rr | rewrite Xsub_rr | rewrite Xmul_rr]). f_equal. unfold i0, i1. field.
  - unfold iota3, ei0, ei1. cbn [xeval]. rewrite !xeval_edyad, base_s, xeval_half2, base_h.
    repeat (first [rewrite Xadd_rr | rewrite Xsub_rr | rewrite Xmul_rr]). f_equal. unfold i0, i1. field.
Qed.

(* ---------------------------------------------------------------- *)
(* The residual of the exact solution                                *)

(** The two half-point jets of the exact solution at the angles (u, v). *)
Definition jm3 (u v s h : R) : jet :=
  jm modes3d u v phip3 h s (iota3 (s - h / 2))
     (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h)
     (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h)
     (fun k => XL k (s - h / 2)).
Definition jp3 (u v s h : R) : jet :=
  jp modes3d u v phip3 h s (iota3 (s + h / 2))
     (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h)
     (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h)
     (fun k => XL k (s + h / 2)).

Section Exact.

Variables (eu ev efs efu : expr) (u v fs fu s h : R).
Hypothesis Hh : h <> 0.
Hypothesis Hs : - s < h < s.
Hypothesis Hu : xeval (base s h) eu = Xreal u.
Hypothesis Hv : xeval (base s h) ev = Xreal v.
Hypothesis Hfs : xeval (base s h) efs = Xreal fs.
Hypothesis Hfu : xeval (base s h) efu = Xreal fu.

Let E := outer eu ev efs efu s h.

Lemma rK3 : forall k, (k < rK modes3d)%nat -> (k < 5)%nat.
Proof. intros k Hk. exact Hk. Qed.

Lemma exact_R :
  forall k, (k < rK modes3d)%nat ->
  eget (o_xR k) E Xnan = Xreal (XR k s) /\ eget (o_dmR modes3d k) E Xnan = Xreal (dmX (XR k) s h) /\
  eget (o_dpR modes3d k) E Xnan = Xreal (dpX (XR k) s h) /\
  eget (o_eR modes3d k) E Xnan = Xreal (eX (XR k) s h).
Proof. intros k Hk. exact (jet_R_vals eu ev efs efu s h k Hh Hs (rK3 k Hk)). Qed.

Lemma exact_Z :
  forall k, (k < rK modes3d)%nat ->
  eget (o_xZ modes3d k) E Xnan = Xreal (XZ k s) /\
  eget (o_dmZ modes3d k) E Xnan = Xreal (dmX (XZ k) s h) /\
  eget (o_dpZ modes3d k) E Xnan = Xreal (dpX (XZ k) s h) /\
  eget (o_eZ modes3d k) E Xnan = Xreal (eX (XZ k) s h).
Proof. intros k Hk. exact (jet_Z_vals eu ev efs efu s h k Hh Hs (rK3 k Hk)). Qed.

Lemma exact_L :
  forall k, (k < rK modes3d)%nat ->
  eget (o_Lm modes3d k) E Xnan = Xreal (XL k (s - h / 2)) /\
  eget (o_Lp modes3d k) E Xnan = Xreal (XL k (s + h / 2)) /\
  eget (o_Ldd modes3d k) E Xnan = Xreal ((XL k (s + h / 2) - XL k (s - h / 2)) / h).
Proof. intros k Hk. exact (jet_L_vals eu ev efs efu s h k Hh Hs (rK3 k Hk)). Qed.

Lemma exact_rel :
  (forall X k, (k < rK modes3d)%nat -> dpX X s h - dmX X s h = h * eX X s h) /\
  (forall k, (k < rK modes3d)%nat ->
     XL k (s + h / 2) - XL k (s - h / 2) = h * ((XL k (s + h / 2) - XL k (s - h / 2)) / h)) /\
  iota3 (s + h / 2) - iota3 (s - h / 2) = h * i1.
Proof.
  split; [| split].
  - intros X k _. unfold eX. field. exact Hh.
  - intros k _. field. exact Hh.
  - unfold iota3. field.
Qed.

(** The poloidal residual of the exact solution's node data, through RegResidual's
    bindings, is the forced r_u of node_residual at the outer half point. *)
Theorem exact_fu :
  f_sqrtg (jm3 u v s h) <> 0 -> f_sqrtg (jp3 u v s h) <> 0 ->
  xeval (xextend E (reg_binds modes3d)) (reg_fu modes3d) = Xreal (cres_u (jp3 u v s h) - fu).
Proof.
  intros Hm Hp.
  destruct (jet_rest_vals eu ev efs efu u v fs fu s h Hh Hs Hu Hv Hfs Hfu)
    as (H3 & H6 & H9 & Hio & Hr & Hrest).
  exact (reg_fu_ok modes3d E u v phip3 h s mpp3 fs fu (iota3 (s - h / 2)) (iota3 (s + h / 2)) i1
           (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h) (fun k => eX (XR k) s h)
           (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h) (fun k => eX (XZ k) s h)
           (fun k => XL k (s - h / 2)) (fun k => XL k (s + h / 2))
           (fun k => (XL k (s + h / 2) - XL k (s - h / 2)) / h)
           H3 H6 H9 exact_R exact_Z exact_L Hio Hr Hrest Hh ltac:(lra) ltac:(lra) reg_ok_3d Hm Hp).
Qed.

(** The radial residual: wherever it is real, the forced r_s of node_residual. *)
Theorem exact_fs :
  f_sqrtg (jm3 u v s h) <> 0 -> f_sqrtg (jp3 u v s h) <> 0 ->
  forall r, xeval (xextend E (reg_binds modes3d)) (reg_fs modes3d) = Xreal r ->
  r = node_rs (jm3 u v s h) (jp3 u v s h) (1 / h) mpp3 - fs.
Proof.
  intros Hm Hp.
  destruct (jet_rest_vals eu ev efs efu u v fs fu s h Hh Hs Hu Hv Hfs Hfu)
    as (H3 & H6 & H9 & Hio & Hr & Hrest).
  destruct exact_rel as (RX & RL & RI).
  exact (reg_fs_ok modes3d E u v phip3 h s mpp3 fs fu (iota3 (s - h / 2)) (iota3 (s + h / 2)) i1
           (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h) (fun k => eX (XR k) s h)
           (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h) (fun k => eX (XZ k) s h)
           (fun k => XL k (s - h / 2)) (fun k => XL k (s + h / 2))
           (fun k => (XL k (s + h / 2) - XL k (s - h / 2)) / h)
           H3 H6 H9 exact_R exact_Z exact_L Hio Hr Hrest Hh ltac:(lra) ltac:(lra)
           (fun k Hk => RX (XR k) k Hk) (fun k Hk => RX (XZ k) k Hk) RL RI reg_ok_3d Hm Hp).
Qed.

(** The poloidal residual needs the outer half point's Jacobian alone. *)
Theorem exact_fu_p :
  f_sqrtg (jp3 u v s h) <> 0 ->
  xeval (xextend E (reg_binds modes3d)) (reg_fu modes3d) = Xreal (cres_u (jp3 u v s h) - fu).
Proof.
  intros Hp.
  destruct (jet_rest_vals eu ev efs efu u v fs fu s h Hh Hs Hu Hv Hfs Hfu)
    as (H3 & H6 & H9 & Hio & Hr & Hrest).
  exact (reg_fu_ok_p modes3d E u v phip3 h s mpp3 fs fu (iota3 (s - h / 2)) (iota3 (s + h / 2)) i1
           (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h) (fun k => eX (XR k) s h)
           (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h) (fun k => eX (XZ k) s h)
           (fun k => XL k (s - h / 2)) (fun k => XL k (s + h / 2))
           (fun k => (XL k (s + h / 2) - XL k (s - h / 2)) / h)
           H3 H6 H9 exact_R exact_Z exact_L Hio Hr Hrest Hh ltac:(lra) ltac:(lra) reg_ok_3d Hp).
Qed.

(** A real output has nonzero Jacobians where it reads them. *)
Lemma exact_fs_nz :
  forall r, xeval (xextend E (reg_binds modes3d)) (reg_fs modes3d) = Xreal r ->
  f_sqrtg (jm3 u v s h) <> 0 /\ f_sqrtg (jp3 u v s h) <> 0.
Proof.
  destruct (jet_rest_vals eu ev efs efu u v fs fu s h Hh Hs Hu Hv Hfs Hfu)
    as (H3 & H6 & H9 & Hio & Hr & Hrest).
  exact (fs_real_nz modes3d E u v phip3 h s mpp3 fs fu (iota3 (s - h / 2)) (iota3 (s + h / 2)) i1
           (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h) (fun k => eX (XR k) s h)
           (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h) (fun k => eX (XZ k) s h)
           (fun k => XL k (s - h / 2)) (fun k => XL k (s + h / 2))
           (fun k => (XL k (s + h / 2) - XL k (s - h / 2)) / h)
           H3 H6 H9 exact_R exact_Z exact_L Hio Hr Hrest Hh ltac:(lra) ltac:(lra) reg_ok_3d).
Qed.

Lemma exact_fu_nz :
  forall r, xeval (xextend E (reg_binds modes3d)) (reg_fu modes3d) = Xreal r -> f_sqrtg (jp3 u v s h) <> 0.
Proof.
  destruct (jet_rest_vals eu ev efs efu u v fs fu s h Hh Hs Hu Hv Hfs Hfu)
    as (H3 & H6 & H9 & Hio & Hr & Hrest).
  exact (fu_real_nz modes3d E u v phip3 h s mpp3 fs fu (iota3 (s - h / 2)) (iota3 (s + h / 2)) i1
           (fun k => XR k s) (fun k => dmX (XR k) s h) (fun k => dpX (XR k) s h) (fun k => eX (XR k) s h)
           (fun k => XZ k s) (fun k => dmX (XZ k) s h) (fun k => dpX (XZ k) s h) (fun k => eX (XZ k) s h)
           (fun k => XL k (s - h / 2)) (fun k => XL k (s + h / 2))
           (fun k => (XL k (s + h / 2) - XL k (s - h / 2)) / h)
           H3 H6 H9 exact_R exact_Z exact_L Hio Hr Hrest Hh ltac:(lra) ltac:(lra) reg_ok_3d).
Qed.

End Exact.
