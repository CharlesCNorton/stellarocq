(** * The series of Physics.v and their derivatives

    Physics.v reconstructs R, Z and lambda as Fourier series whose
    coefficients are functions of the radius, and writes every derivative the
    residual reads as a series of its own ([fassemble], [flambda_terms]):
    the radial derivatives through the coefficients, the angular ones by a
    table of kernels, signs and factors m and n. This file proves that table:
    for coefficient functions with the stated radial derivatives, each series
    of the table is the partial derivative of the one it is listed as the
    derivative of ([table_s], [table_u], [table_v]). It then proves that the
    coefficients Physics.v uses have the radial derivatives it writes: the
    cubic Hermite through the half-point values and slopes ([herm_d1],
    [herm_d2]), the linear rule for an even mode of lambda ([lin_d1]) and the
    sqrt(s)-scaled rule for an odd one ([sqlin_d1]). *)

From Coq Require Import ZArith Reals List Lra.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Force.
Import ListNotations.
Local Open Scope R_scope.

(** * Sums over lists *)

Definition lsum {A : Type} (f : A -> R) (l : list A) : R := fold_right Rplus 0 (map f l).

Lemma D_lsum {A : Type} (l : list A) (f : A -> R -> R) (df : A -> R) (x : R) :
  (forall a, In a l -> is_derive (f a) x (df a)) ->
  is_derive (fun t => lsum (fun a => f a t) l) x (lsum df l).
Proof.
  induction l as [| a l IH]; intros H; unfold lsum; cbn [map fold_right].
  - apply D_const.
  - apply (D_add (f a) (fun t => fold_right Rplus 0 (map (fun a0 => f a0 t) l))).
    + apply H. left. reflexivity.
    + apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma D_ext (f g : R -> R) (x l : R) : (forall t, f t = g t) -> is_derive f x l -> is_derive g x l.
Proof. intros H. apply is_derive_ext. exact H. Qed.

Lemma D_scal (c : R) (f : R -> R) (x a : R) : is_derive f x a -> is_derive (fun t => c * f t) x (c * a).
Proof.
  intros H. pose proof (D_mul (fun _ => c) f x 0 a (D_const c x) H) as H'. cbv beta in H'.
  replace (c * a) with (0 * f x + c * a) by ring. exact H'.
Qed.

(** * A Fourier series and the table of its derivatives *)

(** One mode: its numbers and its coefficient with two radial derivatives. *)
Record term := Term { tm : Z ; tn : Z ; tc : R -> R ; tc1 : R -> R ; tc2 : R -> R }.

Definition ang (t : term) (u v : R) : R := IZR (tm t) * u - IZR (tn t) * v.

(** A cosine series (even = true) or a sine series, with the kernels and
    signs of [fassemble]: k0 the kernel of the series, k1 the other one, su
    and sv the factors of the first angular derivatives. *)
Definition k0 (even : bool) (x : R) : R := if even then cos x else sin x.
Definition k1 (even : bool) (x : R) : R := if even then sin x else cos x.
Definition su (even : bool) (t : term) : R := if even then - IZR (tm t) else IZR (tm t).
Definition sv (even : bool) (t : term) : R := if even then IZR (tn t) else - IZR (tn t).

(** The derivatives of the kernels along the two angles. *)
Lemma D_k0_u (even : bool) (t : term) (u v : R) :
  is_derive (fun x => k0 even (ang t x v)) u (su even t * k1 even (ang t u v)).
Proof. unfold k0, k1, su, ang. destruct even; cbv iota beta; auto_derive; try solve [auto]; unfold Rminus; ring. Qed.

Lemma D_k0_v (even : bool) (t : term) (u v : R) :
  is_derive (fun y => k0 even (ang t u y)) v (sv even t * k1 even (ang t u v)).
Proof. unfold k0, k1, sv, ang. destruct even; cbv iota beta; auto_derive; try solve [auto]; unfold Rminus; ring. Qed.

Lemma D_k1_u (even : bool) (t : term) (u v : R) :
  is_derive (fun x => su even t * k1 even (ang t x v)) u (- (IZR (tm t) * IZR (tm t)) * k0 even (ang t u v)).
Proof. unfold k0, k1, su, ang. destruct even; cbv iota beta; auto_derive; try solve [auto]; unfold Rminus; ring. Qed.

Lemma D_k1_v_u (even : bool) (t : term) (u v : R) :
  is_derive (fun y => su even t * k1 even (ang t u y)) v ((IZR (tm t) * IZR (tn t)) * k0 even (ang t u v)).
Proof. unfold k0, k1, su, ang. destruct even; cbv iota beta; auto_derive; try solve [auto]; unfold Rminus; ring. Qed.

Lemma D_k1_u_v (even : bool) (t : term) (u v : R) :
  is_derive (fun x => sv even t * k1 even (ang t x v)) u ((IZR (tm t) * IZR (tn t)) * k0 even (ang t u v)).
Proof. unfold k0, k1, sv, ang. destruct even; cbv iota beta; auto_derive; try solve [auto]; unfold Rminus; ring. Qed.

Lemma D_k1_v (even : bool) (t : term) (u v : R) :
  is_derive (fun y => sv even t * k1 even (ang t u y)) v (- (IZR (tn t) * IZR (tn t)) * k0 even (ang t u v)).
Proof. unfold k0, k1, sv, ang. destruct even; cbv iota beta; auto_derive; try solve [auto]; unfold Rminus; ring. Qed.

Section Table.
Variables (even : bool) (l : list term).

Definition S0 (s u v : R) := lsum (fun t => tc t s * k0 even (ang t u v)) l.
Definition S_s (s u v : R) := lsum (fun t => tc1 t s * k0 even (ang t u v)) l.
Definition S_ss (s u v : R) := lsum (fun t => tc2 t s * k0 even (ang t u v)) l.
Definition S_u (s u v : R) := lsum (fun t => su even t * (tc t s * k1 even (ang t u v))) l.
Definition S_v (s u v : R) := lsum (fun t => sv even t * (tc t s * k1 even (ang t u v))) l.
Definition S_su (s u v : R) := lsum (fun t => su even t * (tc1 t s * k1 even (ang t u v))) l.
Definition S_sv (s u v : R) := lsum (fun t => sv even t * (tc1 t s * k1 even (ang t u v))) l.
Definition S_uu (s u v : R) :=
  lsum (fun t => - (IZR (tm t) * IZR (tm t)) * (tc t s * k0 even (ang t u v))) l.
Definition S_uv (s u v : R) :=
  lsum (fun t => (IZR (tm t) * IZR (tn t)) * (tc t s * k0 even (ang t u v))) l.
Definition S_vv (s u v : R) :=
  lsum (fun t => - (IZR (tn t) * IZR (tn t)) * (tc t s * k0 even (ang t u v))) l.

(** Along the radius, for coefficients with the stated derivatives. *)
Section Radial.
Variable s0 : R.
Hypothesis Hc1 : forall t, In t l -> is_derive (tc t) s0 (tc1 t s0).
Hypothesis Hc2 : forall t, In t l -> is_derive (tc1 t) s0 (tc2 t s0).

Lemma table_s (u v : R) :
  is_derive (fun s => S0 s u v) s0 (S_s s0 u v) /\
  is_derive (fun s => S_u s u v) s0 (S_su s0 u v) /\
  is_derive (fun s => S_v s u v) s0 (S_sv s0 u v).
Proof.
  unfold S0, S_s, S_u, S_su, S_v, S_sv. refine (conj _ (conj _ _)); apply D_lsum; intros t Ht.
  - pose proof (D_mul (tc t) (fun _ => k0 even (ang t u v)) s0 _ 0 (Hc1 t Ht) (D_const _ s0)) as H.
    cbv beta in H. replace (tc1 t s0 * k0 even (ang t u v))
      with (tc1 t s0 * k0 even (ang t u v) + tc t s0 * 0) by ring. exact H.
  - apply D_scal. pose proof (D_mul (tc t) (fun _ => k1 even (ang t u v)) s0 _ 0 (Hc1 t Ht) (D_const _ s0)) as H.
    cbv beta in H. replace (tc1 t s0 * k1 even (ang t u v))
      with (tc1 t s0 * k1 even (ang t u v) + tc t s0 * 0) by ring. exact H.
  - apply D_scal. pose proof (D_mul (tc t) (fun _ => k1 even (ang t u v)) s0 _ 0 (Hc1 t Ht) (D_const _ s0)) as H.
    cbv beta in H. replace (tc1 t s0 * k1 even (ang t u v))
      with (tc1 t s0 * k1 even (ang t u v) + tc t s0 * 0) by ring. exact H.
Qed.

Lemma table_ss (u v : R) : is_derive (fun s => S_s s u v) s0 (S_ss s0 u v).
Proof.
  unfold S_s, S_ss. apply D_lsum. intros t Ht.
  pose proof (D_mul (tc1 t) (fun _ => k0 even (ang t u v)) s0 _ 0 (Hc2 t Ht) (D_const _ s0)) as H.
  cbv beta in H. replace (tc2 t s0 * k0 even (ang t u v))
    with (tc2 t s0 * k0 even (ang t u v) + tc1 t s0 * 0) by ring. exact H.
Qed.

End Radial.

(** Along the two angles. *)
Lemma table_u (s u0 v : R) :
  is_derive (fun u => S0 s u v) u0 (S_u s u0 v) /\
  is_derive (fun u => S_s s u v) u0 (S_su s u0 v) /\
  is_derive (fun u => S_u s u v) u0 (S_uu s u0 v) /\
  is_derive (fun u => S_v s u v) u0 (S_uv s u0 v).
Proof.
  unfold S0, S_s, S_u, S_su, S_v, S_uu, S_uv.
  refine (conj _ (conj _ (conj _ _))); apply D_lsum; intros t _.
  - apply (D_ext (fun x => tc t s * k0 even (ang t x v))); [intros; reflexivity |].
    replace (su even t * (tc t s * k1 even (ang t u0 v))) with (tc t s * (su even t * k1 even (ang t u0 v)))
      by ring. apply D_scal, D_k0_u.
  - replace (su even t * (tc1 t s * k1 even (ang t u0 v))) with (tc1 t s * (su even t * k1 even (ang t u0 v)))
      by ring. apply D_scal, D_k0_u.
  - apply (D_ext (fun x => tc t s * (su even t * k1 even (ang t x v))));
      [intros; ring |].
    replace (- (IZR (tm t) * IZR (tm t)) * (tc t s * k0 even (ang t u0 v)))
      with (tc t s * (- (IZR (tm t) * IZR (tm t)) * k0 even (ang t u0 v))) by ring.
    apply D_scal, D_k1_u.
  - apply (D_ext (fun x => tc t s * (sv even t * k1 even (ang t x v))));
      [intros; ring |].
    replace ((IZR (tm t) * IZR (tn t)) * (tc t s * k0 even (ang t u0 v)))
      with (tc t s * ((IZR (tm t) * IZR (tn t)) * k0 even (ang t u0 v))) by ring.
    apply D_scal, D_k1_u_v.
Qed.

Lemma table_v (s u v0 : R) :
  is_derive (fun v => S0 s u v) v0 (S_v s u v0) /\
  is_derive (fun v => S_s s u v) v0 (S_sv s u v0) /\
  is_derive (fun v => S_u s u v) v0 (S_uv s u v0) /\
  is_derive (fun v => S_v s u v) v0 (S_vv s u v0).
Proof.
  unfold S0, S_s, S_u, S_sv, S_v, S_uv, S_vv.
  refine (conj _ (conj _ (conj _ _))); apply D_lsum; intros t _.
  - replace (sv even t * (tc t s * k1 even (ang t u v0))) with (tc t s * (sv even t * k1 even (ang t u v0)))
      by ring. apply D_scal, D_k0_v.
  - replace (sv even t * (tc1 t s * k1 even (ang t u v0))) with (tc1 t s * (sv even t * k1 even (ang t u v0)))
      by ring. apply D_scal, D_k0_v.
  - apply (D_ext (fun y => tc t s * (su even t * k1 even (ang t u y))));
      [intros; ring |].
    replace ((IZR (tm t) * IZR (tn t)) * (tc t s * k0 even (ang t u v0)))
      with (tc t s * ((IZR (tm t) * IZR (tn t)) * k0 even (ang t u v0))) by ring.
    apply D_scal, D_k1_v_u.
  - apply (D_ext (fun y => tc t s * (sv even t * k1 even (ang t u y))));
      [intros; ring |].
    replace (- (IZR (tn t) * IZR (tn t)) * (tc t s * k0 even (ang t u v0)))
      with (tc t s * (- (IZR (tn t) * IZR (tn t)) * k0 even (ang t u v0))) by ring.
    apply D_scal, D_k1_v.
Qed.

End Table.

(** * The radial coefficients *)

(** The cubic Hermite through (sa, ya, da) and (sa + H, yb, db), in the
    secant-defect basis of [hermcoef_b]: t = (s - sa) / H, sec the secant,
    al and be the slope defects. *)
Section Hermite.
Variables (sa H ya da yb db : R).
Hypothesis HH : H <> 0.

Definition h_t (s : R) := (s - sa) * / H.
Definition h_sec := (yb - ya) * / H.
Definition h_al := da - h_sec.
Definition h_be := db - h_sec.

Definition herm (s : R) :=
  let t := h_t s in
  ya + t * (yb - ya) + H * ((t * (t * t) - 2 * (t * t) + t) * h_al + (t * (t * t) - t * t) * h_be).
Definition herm1 (s : R) :=
  let t := h_t s in
  h_sec + ((3 * (t * t) - 4 * t + 1) * h_al + (3 * (t * t) - 2 * t) * h_be).
Definition herm2 (s : R) :=
  let t := h_t s in
  ((6 * t - 4) * h_al + (6 * t - 2) * h_be) * / H.

Lemma herm_d1 (s : R) : is_derive herm s (herm1 s).
Proof.
  unfold herm, herm1, h_t, h_sec, h_al, h_be. auto_derive; [exact I |]. field. exact HH.
Qed.

Lemma herm_d2 (s : R) : is_derive herm1 s (herm2 s).
Proof.
  unfold herm1, herm2, h_t, h_sec, h_al, h_be. auto_derive; [exact I |]. field. exact HH.
Qed.

End Hermite.

(** The rule for lambda: linear in s for an even mode, and sqrt(s) times a
    function linear in s for an odd one, between the half points sa and
    sa + h with values ya and yb. *)
Section Linear.
Variables (sa ih ya yb : R).

Definition lin (s : R) := ya + (s - sa) * ih * (yb - ya).
Definition lin1 (s : R) := (yb - ya) * ih.

Lemma lin_d1 (s : R) : is_derive lin s (lin1 s).
Proof. unfold lin, lin1. auto_derive; [exact I | ring]. Qed.

Variables (isa isb : R).
Definition sqlin (s : R) := sqrt s * (ya * isa + (s - sa) * ih * (yb * isb - ya * isa)).
Definition sqlin1 (s : R) :=
  sqrt s * ((yb * isb - ya * isa) * ih) + sqlin s * / (2 * s).

Lemma sqlin_d1 (s : R) : 0 < s -> is_derive sqlin s (sqlin1 s).
Proof.
  intros Hs. unfold sqlin1, sqlin. auto_derive; [exact Hs |].
  pose proof (sqrt_lt_R0 s Hs) as Hq. pose proof (sqrt_sqrt s (Rlt_le _ _ Hs)) as E.
  set (q := sqrt s) in *. rewrite <- E. field. lra.
Qed.

End Linear.
