(** Rigorous quadrature over a cell of angles.

    Cell.v bounds a residual component over a cell. The same data bounds its
    integral: the value at the centre times the width of the cell, with an
    error the derivative enclosure the cell already carries controls.

    That is what a flux-surface average needs. The cells of a cell
    certificate tile the angular torus, so summing the per-cell enclosures
    encloses any angular integral of the reconstruction, and with it the
    enclosed currents, the differential volume, the field energy and the
    Mercier terms, none of which the expression language can write in closed
    form.

    [midpoint_encloses] is the per-cell statement. The bound is first order
    in the half-width, since only the first derivative is enclosed; a
    second-order form needs the second derivative, which Deriv.v can build
    by composing [deriv] with itself. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Two facts about integrals of real functions                       *)

(** The integral of a constant. *)
Lemma RInt_const_R :
  forall a b (v : R), RInt (fun _ : R => v) a b = (b - a) * v.
Proof.
  intros a b v. rewrite RInt_const.
  unfold scal, mult; simpl. unfold mult; simpl. ring.
Qed.

(** A function within K of zero on an interval has its integral within
    (b - a) K of zero. *)
Lemma RInt_le_const :
  forall (g : R -> R) a b K,
  a <= b -> ex_RInt g a b ->
  (forall x, a < x < b -> - K <= g x <= K) ->
  Rabs (RInt g a b) <= (b - a) * K.
Proof.
  intros g a b K Hab Hex H.
  assert (Hlo : RInt (fun _ : R => - K) a b <= RInt g a b).
  { apply RInt_le. exact Hab. apply ex_RInt_const. exact Hex.
    intros x Hx. apply H. exact Hx. }
  assert (Hhi : RInt g a b <= RInt (fun _ : R => K) a b).
  { apply RInt_le. exact Hab. exact Hex. apply ex_RInt_const.
    intros x Hx. apply H. exact Hx. }
  rewrite (RInt_const_R a b (- K)) in Hlo.
  rewrite (RInt_const_R a b K) in Hhi.
  replace ((b - a) * (- K)) with (- ((b - a) * K)) in Hlo by ring.
  apply Rabs_le. split; lra.
Qed.


(* ---------------------------------------------------------------- *)
(* The midpoint rule from a bound on the variation                   *)

(** The midpoint rule over a cell, given only that the function stays
    within K of its value at the centre. Both the first-order and the
    second-order bound are this lemma with a different K. *)
Lemma midpoint_generic :
  forall (phi : R -> R) c h K,
  0 <= h ->
  ex_RInt phi (c - h) (c + h) ->
  (forall t, c - h <= t <= c + h -> Rabs (phi t - phi c) <= K) ->
  Rabs (RInt phi (c - h) (c + h) - 2 * h * phi c) <= 2 * h * K.
Proof.
  intros phi c h K Hh Hex Hnear.
  assert (Hab : c - h <= c + h) by lra.
  assert (HK : 0 <= K).
  { generalize (Hnear c ltac:(lra)).
    replace (phi c - phi c) with 0 by ring. rewrite Rabs_R0. lra. }
  assert (Hlo : RInt (fun _ : R => phi c - K) (c - h) (c + h)
                <= RInt phi (c - h) (c + h)).
  { apply RInt_le. exact Hab. apply ex_RInt_const. exact Hex.
    intros x Hx. generalize (Hnear x ltac:(lra)).
    unfold Rabs. destruct (Rcase_abs (phi x - phi c)); lra. }
  assert (Hhi : RInt phi (c - h) (c + h)
                <= RInt (fun _ : R => phi c + K) (c - h) (c + h)).
  { apply RInt_le. exact Hab. exact Hex. apply ex_RInt_const.
    intros x Hx. generalize (Hnear x ltac:(lra)).
    unfold Rabs. destruct (Rcase_abs (phi x - phi c)); lra. }
  rewrite RInt_const_R in Hlo. rewrite RInt_const_R in Hhi.
  replace (c + h - (c - h)) with (2 * h) in Hlo by ring.
  replace (c + h - (c - h)) with (2 * h) in Hhi by ring.
  replace (2 * h * (phi c - K)) with (2 * h * phi c - 2 * h * K) in Hlo by ring.
  replace (2 * h * (phi c + K)) with (2 * h * phi c + 2 * h * K) in Hhi by ring.
  apply Rabs_le. split; lra.
Qed.

(** A bound on a derivative bounds the increment, for plain real
    functions. *)
Lemma mvt_bound :
  forall (phi psi : R -> R) a b K,
  (forall t, a <= t <= b -> derivable_pt_lim phi t (psi t)) ->
  (forall t, a <= t <= b -> Rabs (psi t) <= K) ->
  forall t0 t1, a <= t0 <= b -> a <= t1 <= b ->
  Rabs (phi t1 - phi t0) <= K * Rabs (t1 - t0).
Proof.
  intros phi psi a b K Hd Hb t0 t1 H0 H1.
  assert (HK : 0 <= K).
  { generalize (Hb t0 H0). generalize (Rabs_pos (psi t0)). lra. }
  assert (Hcore : forall u v, a <= u <= b -> a <= v <= b -> u < v ->
            Rabs (phi v - phi u) <= K * (v - u)).
  { intros u v Hu Hv Huv.
    destruct (MVT_cor2 phi psi u v Huv) as [z [Hz Hzin]].
    { intros s Hs. apply Hd. lra. }
    rewrite Hz, Rabs_mult.
    apply Rle_trans with (K * Rabs (v - u)).
    - apply Rmult_le_compat_r. apply Rabs_pos. apply Hb. lra.
    - rewrite (Rabs_right (v - u)) by lra. apply Rle_refl. }
  destruct (Rtotal_order t0 t1) as [Hlt|[Heq|Hgt]].
  - rewrite (Rabs_right (t1 - t0)) by lra. now apply Hcore.
  - subst t1. replace (phi t0 - phi t0) with 0 by ring.
    rewrite Rabs_R0. replace (t0 - t0) with 0 by ring.
    rewrite Rabs_R0. lra.
  - rewrite Rabs_minus_sym. rewrite (Rabs_left (t1 - t0)) by lra.
    replace (- (t1 - t0)) with (t0 - t1) by ring.
    now apply Hcore.
Qed.


Section Quadrature.

(** The environment along the parameter, the value slot, its derivative
    slot, the bound on that derivative over the cell, and the cell. *)
Variable F : R -> env ExtendedR.
Variable n nd : nat.
Variable M c h : R.

Hypothesis Hh : 0 <= h.

(** Slot nd holds the derivative of slot n along the parameter. *)
Hypothesis Hder :
  forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan).

(** Over the cell that derivative is a real number bounded by M. This is
    what [check_component] establishes by interval evaluation of the
    derivative bindings on the box. *)
Hypothesis Hbnd :
  forall t, c - h <= t <= c + h ->
  exists d, eget nd (F t) Xnan = Xreal d /\ Rabs d <= M.

(** The value slot as a real function of the parameter. *)
Definition along_real : R -> R := proj_fun 0 (slot_along F n).

(** It is differentiable wherever its derivative slot is real. *)
Lemma quad_derivable :
  forall t, c - h <= t <= c + h ->
  derivable_pt_lim along_real t (proj_val (eget nd (F t) Xnan)).
Proof.
  intros t Ht.
  destruct (Hbnd t Ht) as [d [Hd _]].
  rewrite Hd. simpl.
  specialize (Hder t). rewrite Hd in Hder.
  unfold Xderive_pt in Hder. unfold slot_along in Hder at 1.
  destruct (eget n (F t) Xnan) as [|w] eqn:Hn. contradiction.
  unfold along_real. exact (Hder 0).
Qed.

(** Hence continuous, hence integrable over the cell. *)
Lemma quad_ex_RInt : ex_RInt along_real (c - h) (c + h).
Proof.
  apply ex_RInt_Reals_1. apply continuity_implies_RiemannInt. lra.
  intros x Hx. apply derivable_continuous_pt.
  exists (proj_val (eget nd (F x) Xnan)).
  now apply quad_derivable.
Qed.

(** The value at the centre is a real number. *)
Lemma quad_centre : exists v, eget n (F c) Xnan = Xreal v.
Proof.
  destruct (Hbnd c ltac:(lra)) as [d [Hd _]].
  specialize (Hder c). rewrite Hd in Hder.
  unfold Xderive_pt in Hder. unfold slot_along in Hder.
  destruct (eget n (F c) Xnan) as [|w]. contradiction. now exists w.
Qed.

(** The midpoint rule over the cell, with the error the derivative bound
    forces: the integral exists, and it is within 2 M h^2 of the value at
    the centre times the width of the cell. Summing this over cells that
    tile the angular torus encloses a flux-surface average. *)
Theorem midpoint_encloses :
  exists v,
    eget n (F c) Xnan = Xreal v /\
    Rabs (RInt along_real (c - h) (c + h) - 2 * h * v) <= 2 * M * h * h.
Proof.
  destruct quad_centre as [v Hv].
  exists v. split. exact Hv.
  assert (Hab : c - h <= c + h) by lra.
  assert (HM : 0 <= M).
  { destruct (Hbnd c ltac:(lra)) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  assert (Hex := quad_ex_RInt).
  (* the value anywhere in the cell is within M h of the value at the centre *)
  assert (Hnear : forall t, c - h <= t <= c + h ->
            v - M * h <= along_real t <= v + M * h).
  { intros t Ht.
    destruct (bound_between_dist F n nd M (c - h) (c + h) c t Hder Hbnd
                ltac:(lra) Ht) as [w0 [w1 [H0 [H1 Hinc]]]].
    rewrite Hv in H0. injection H0 as <-.
    assert (Hw : Rabs (w1 - v) <= M * h).
    { apply Rle_trans with (M * Rabs (t - c)). exact Hinc.
      apply Rmult_le_compat_l. exact HM. apply Rabs_le. lra. }
    assert (Hw2 : - (M * h) <= w1 - v <= M * h).
    { unfold Rabs in Hw. destruct (Rcase_abs (w1 - v)); lra. }
    unfold along_real, proj_fun, slot_along. rewrite H1. simpl. lra. }
  (* so the integral lies between the two constant integrals *)
  assert (Hlo : RInt (fun _ : R => v - M * h) (c - h) (c + h)
                <= RInt along_real (c - h) (c + h)).
  { apply RInt_le. exact Hab. apply ex_RInt_const. exact Hex.
    intros x Hx. destruct (Hnear x ltac:(lra)) as [H1 _]. exact H1. }
  assert (Hhi : RInt along_real (c - h) (c + h)
                <= RInt (fun _ : R => v + M * h) (c - h) (c + h)).
  { apply RInt_le. exact Hab. exact Hex. apply ex_RInt_const.
    intros x Hx. destruct (Hnear x ltac:(lra)) as [_ H2]. exact H2. }
  rewrite RInt_const_R in Hlo. rewrite RInt_const_R in Hhi.
  replace (c + h - (c - h)) with (2 * h) in Hlo by ring.
  replace (c + h - (c - h)) with (2 * h) in Hhi by ring.
  replace (2 * h * (v - M * h)) with (2 * h * v - 2 * M * h * h) in Hlo by ring.
  replace (2 * h * (v + M * h)) with (2 * h * v + 2 * M * h * h) in Hhi by ring.
  apply Rabs_le. split; lra.
Qed.

End Quadrature.


(** An affine function integrates over a centred cell to the width times
    its value at the centre: the linear part cancels, which is what makes
    the midpoint rule second order. *)
Lemma is_RInt_affine_centred :
  forall (A L c h : R),
  is_RInt (fun t : R => A + L * (t - c)) (c - h) (c + h) (2 * h * A).
Proof.
  intros A L c h.
  assert (Hcont : forall x : R, continuous (fun t : R => A + L * (t - c)) x).
  { intros x. apply continuity_pt_filterlim. reg. }
  assert (Hder : forall x : R,
            is_derive (fun t : R => A * t + L * (/ 2 * ((t - c) * (t - c)))) x
                      (A + L * (x - c))).
  { intros x. auto_derive; try exact I; try field; try lra. }
  replace (2 * h * A)
    with ((A * (c + h) + L * (/ 2 * ((c + h - c) * (c + h - c))))
          - (A * (c - h) + L * (/ 2 * ((c - h - c) * (c - h - c))))) by field.
  apply (is_RInt_derive (fun t : R => A * t + L * (/ 2 * ((t - c) * (t - c))))).
  - intros x _. apply Hder.
  - intros x _. apply Hcont.
Qed.

Section SharpQuadrature.

(** Three slots of the same environment: a value, its derivative, and its
    second derivative, as [with_derivs2] arranges them. *)
Variable F : R -> env ExtendedR.
Variable n nd ndd : nat.
Variable M2 c h : R.

Hypothesis Hh : 0 <= h.
Hypothesis Hder1 :
  forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan).
Hypothesis Hder2 :
  forall t, Xderive_pt (slot_along F nd) (Xreal t) (eget ndd (F t) Xnan).

(** Only the second derivative has to be bounded over the cell; the value
    and the first derivative are real there as a consequence. *)
Hypothesis Hbnd2 :
  forall t, c - h <= t <= c + h ->
  exists d, eget ndd (F t) Xnan = Xreal d /\ Rabs d <= M2.

Definition sphi : R -> R := proj_fun 0 (slot_along F n).
Definition sphi' : R -> R := proj_fun 0 (slot_along F nd).

(** The first derivative slot is real over the cell. *)
Lemma sharp_d1_real :
  forall t, c - h <= t <= c + h -> eget nd (F t) Xnan = Xreal (sphi' t).
Proof.
  intros t Ht. destruct (Hbnd2 t Ht) as [d [Hd _]].
  assert (H := Hder2 t). rewrite Hd in H.
  unfold Xderive_pt in H. unfold slot_along in H at 1.
  destruct (eget nd (F t) Xnan) as [|w] eqn:Hw. contradiction.
  unfold sphi', proj_fun, slot_along. now rewrite Hw.
Qed.

(** The first derivative is differentiable, with the second derivative slot
    for derivative. *)
Lemma sharp_phi'_deriv :
  forall t, c - h <= t <= c + h ->
  derivable_pt_lim sphi' t (proj_val (eget ndd (F t) Xnan)).
Proof.
  intros t Ht.
  destruct (Hbnd2 t Ht) as [d [Hd _]].
  rewrite Hd. simpl.
  assert (H := Hder2 t). rewrite Hd in H.
  unfold Xderive_pt in H. unfold slot_along in H at 1.
  destruct (eget nd (F t) Xnan) as [|w] eqn:Hw. contradiction.
  unfold sphi'. exact (H 0).
Qed.

(** The value is differentiable, with the first derivative for derivative. *)
Lemma sharp_phi_deriv :
  forall t, c - h <= t <= c + h -> derivable_pt_lim sphi t (sphi' t).
Proof.
  intros t Ht.
  assert (Hd := sharp_d1_real t Ht).
  assert (H := Hder1 t). rewrite Hd in H.
  unfold Xderive_pt in H. unfold slot_along in H at 1.
  destruct (eget n (F t) Xnan) as [|w] eqn:Hw. contradiction.
  unfold sphi. exact (H 0).
Qed.

(** Hence the value is integrable over the cell. *)
Lemma sharp_ex_RInt : ex_RInt sphi (c - h) (c + h).
Proof.
  apply ex_RInt_Reals_1. apply continuity_implies_RiemannInt. lra.
  intros x Hx. apply derivable_continuous_pt.
  exists (sphi' x). now apply sharp_phi_deriv.
Qed.

(** The midpoint rule with the error a second-derivative bound forces: one
    order sharper in the half-width than the form that uses only the first
    derivative, because the linear part of the Taylor step integrates to
    zero over a centred cell. *)
Theorem midpoint_sharp :
  Rabs (RInt sphi (c - h) (c + h) - 2 * h * sphi c) <= 2 * M2 * h * h * h.
Proof.
  assert (Hab : c - h <= c + h) by lra.
  assert (HM : 0 <= M2).
  { destruct (Hbnd2 c ltac:(lra)) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  set (L := sphi' c).
  (* the first derivative stays within M2 h of its value at the centre *)
  assert (Hd1 : forall t, c - h <= t <= c + h -> Rabs (sphi' t - L) <= M2 * h).
  { intros t Ht.
    assert (Hb := mvt_bound sphi' (fun s => proj_val (eget ndd (F s) Xnan))
                    (c - h) (c + h) M2 sharp_phi'_deriv).
    assert (Hbb : forall s, c - h <= s <= c + h ->
              Rabs (proj_val (eget ndd (F s) Xnan)) <= M2).
    { intros s Hs. destruct (Hbnd2 s Hs) as [d [Hd Hdb]].
      rewrite Hd. simpl. exact Hdb. }
    specialize (Hb Hbb c t ltac:(lra) Ht).
    apply Rle_trans with (M2 * Rabs (t - c)). exact Hb.
    apply Rmult_le_compat_l. exact HM. apply Rabs_le. lra. }
  (* so the value stays within M2 h^2 of its affine model at the centre *)
  assert (Hpsi : forall t, c - h <= t <= c + h ->
            Rabs (sphi t - sphi c - L * (t - c)) <= M2 * h * h).
  { intros t Ht.
    assert (Hdl : forall s, c - h <= s <= c + h ->
              derivable_pt_lim (fun u : R => sphi u - L * (u - c)) s
                (sphi' s - L)).
    { intros s Hs.
      apply derivable_pt_lim_minus. now apply sharp_phi_deriv.
      apply (proj1 (is_derive_Reals _ _ _)).
      auto_derive; try exact I; try field; try lra. }
    assert (Hb := mvt_bound (fun u : R => sphi u - L * (u - c))
                    (fun s => sphi' s - L) (c - h) (c + h) (M2 * h) Hdl Hd1
                    c t ltac:(lra) Ht).
    cbv beta in Hb.
    replace (sphi t - L * (t - c) - (sphi c - L * (c - c)))
      with (sphi t - sphi c - L * (t - c)) in Hb by ring.
    apply Rle_trans with (M2 * h * Rabs (t - c)). exact Hb.
    replace (M2 * h * h) with (M2 * h * h) by ring.
    apply Rmult_le_compat_l. now apply Rmult_le_pos.
    apply Rabs_le. lra. }
  (* integrate the two affine envelopes *)
  assert (Hex := sharp_ex_RInt).
  assert (Hlo : RInt (fun t : R => (sphi c - M2 * h * h) + L * (t - c))
                  (c - h) (c + h) <= RInt sphi (c - h) (c + h)).
  { apply RInt_le. exact Hab.
    exists (2 * h * (sphi c - M2 * h * h)). apply is_RInt_affine_centred.
    exact Hex.
    intros x Hx. generalize (Hpsi x ltac:(lra)).
    unfold Rabs. destruct (Rcase_abs (sphi x - sphi c - L * (x - c))); lra. }
  assert (Hhi : RInt sphi (c - h) (c + h)
                <= RInt (fun t : R => (sphi c + M2 * h * h) + L * (t - c))
                     (c - h) (c + h)).
  { apply RInt_le. exact Hab. exact Hex.
    exists (2 * h * (sphi c + M2 * h * h)). apply is_RInt_affine_centred.
    intros x Hx. generalize (Hpsi x ltac:(lra)).
    unfold Rabs. destruct (Rcase_abs (sphi x - sphi c - L * (x - c))); lra. }
  rewrite (is_RInt_unique _ _ _ _ (is_RInt_affine_centred
             (sphi c - M2 * h * h) L c h)) in Hlo.
  rewrite (is_RInt_unique _ _ _ _ (is_RInt_affine_centred
             (sphi c + M2 * h * h) L c h)) in Hhi.
  apply Rabs_le. split; nra.
Qed.

End SharpQuadrature.



(* ---------------------------------------------------------------- *)
(* Summing the cells of a tiling                                     *)

(** The sum of the first N values of a sequence. *)
Fixpoint rsum (g : nat -> R) (N : nat) : R :=
  match N with
  | O => 0
  | S k => rsum g k + g k
  end.

(** A sum of nonnegative terms is nonnegative. *)
Lemma rsum_nonneg :
  forall g N, (forall i, 0 <= g i) -> 0 <= rsum g N.
Proof.
  intros g N Hg. induction N as [|N IH]; simpl. lra.
  generalize (Hg N). lra.
Qed.

Section Tiling.

(** A real function of the angle, and a tiling of [a, a + 2 N h] into cells
    of half-width h, cell i being centred at a + (2i+1) h. *)
Variable f : R -> R.
Variable a h : R.
Hypothesis Hh : 0 <= h.

(** Per cell: the value at its centre and the bound the midpoint rule
    carries there. This is exactly what [midpoint_encloses] delivers, so a
    cell certificate whose cells tile the angular torus supplies the whole
    hypothesis. *)
Variable v M : nat -> R.
Hypothesis HM : forall i, 0 <= M i.
Hypothesis Hcell :
  forall i,
  ex_RInt f (a + 2 * INR i * h) (a + 2 * INR (S i) * h) /\
  Rabs (RInt f (a + 2 * INR i * h) (a + 2 * INR (S i) * h) - 2 * h * v i)
  <= 2 * M i * h * h.

(** The integral over the whole tiling exists and is enclosed by the sum of
    the per-cell midpoint rules, with the errors adding. This is the flux
    surface average: the cells of a cell certificate tile the angular torus,
    so summing what the checker already proves about each of them encloses
    the average. *)
Theorem tiling_encloses :
  forall N,
  ex_RInt f a (a + 2 * INR N * h) /\
  Rabs (RInt f a (a + 2 * INR N * h) - 2 * h * rsum v N)
  <= 2 * h * h * rsum M N.
Proof.
  induction N as [|N [IHex IHb]].
  - simpl. replace (a + 2 * 0 * h) with a by ring.
    split. apply ex_RInt_point.
    assert (Hz : RInt f a a = 0) by (rewrite RInt_point; reflexivity).
    rewrite Hz. replace (0 - 2 * h * 0) with 0 by ring.
    rewrite Rabs_R0. lra.
  - destruct (Hcell N) as [Hex1 Hb1].
    assert (Hsplit : ex_RInt f a (a + 2 * INR (S N) * h)).
    { apply (ex_RInt_Chasles f a (a + 2 * INR N * h)); assumption. }
    split. exact Hsplit.
    assert (Hch : RInt f a (a + 2 * INR (S N) * h)
                  = RInt f a (a + 2 * INR N * h)
                    + RInt f (a + 2 * INR N * h) (a + 2 * INR (S N) * h)).
    { symmetry.
      replace (RInt f a (a + 2 * INR N * h)
               + RInt f (a + 2 * INR N * h) (a + 2 * INR (S N) * h))
        with (plus (RInt f a (a + 2 * INR N * h))
                   (RInt f (a + 2 * INR N * h) (a + 2 * INR (S N) * h)))
        by reflexivity.
      apply RInt_Chasles; assumption. }
    rewrite Hch.
    simpl rsum.
    replace (RInt f a (a + 2 * INR N * h)
             + RInt f (a + 2 * INR N * h) (a + 2 * INR (S N) * h)
             - 2 * h * (rsum v N + v N))
      with ((RInt f a (a + 2 * INR N * h) - 2 * h * rsum v N)
            + (RInt f (a + 2 * INR N * h) (a + 2 * INR (S N) * h)
               - 2 * h * v N)) by ring.
    eapply Rle_trans. apply Rabs_triang.
    replace (2 * h * h * (rsum M N + M N))
      with (2 * h * h * rsum M N + 2 * M N * h * h) by ring.
    now apply Rplus_le_compat.
Qed.

End Tiling.

(* ---------------------------------------------------------------- *)
(* A tiling whose cells need not be the same width                   *)

Section VarTiling.

(** [tiling_encloses] sums cells of one half-width, which is what a generator
    emits when it lays them out uniformly. A covering that refines where it
    needs to does not, and the sum a driver computes carries each cell's own
    width, so the theorem it corresponds to is this one: the cells are given
    by their breakpoints, each contributes its own width times the value at
    its centre, and the errors add.

    Nothing is assumed about how each cell's error was obtained. Substituting
    [midpoint_sharp] gives the midpoint rule, the iterated rule gives the
    two-dimensional one, and the sum is the same either way. *)

Variable f : R -> R.

(** The breakpoints, in order. Cell i is [x i, x (S i)]. *)
Variable x : nat -> R.
Hypothesis Hx : forall i, x i <= x (S i).

(** Per cell: what the rule reports and how far it can be from the integral. *)
Variable v M : nat -> R.
Hypothesis HM : forall i, 0 <= M i.
Hypothesis Hcell :
  forall i,
  ex_RInt f (x i) (x (S i)) /\
  Rabs (RInt f (x i) (x (S i)) - (x (S i) - x i) * v i) <= M i.

Theorem tiling_var_encloses :
  forall N,
  ex_RInt f (x 0%nat) (x N) /\
  Rabs (RInt f (x 0%nat) (x N)
        - rsum (fun i => (x (S i) - x i) * v i) N)
  <= rsum M N.
Proof.
  induction N as [|N [IHex IHb]].
  - split. apply ex_RInt_point.
    cbn [rsum].
    assert (Hz : RInt f (x 0%nat) (x 0%nat) = 0)
      by (rewrite RInt_point; reflexivity).
    rewrite Hz. replace (0 - 0) with 0 by ring.
    rewrite Rabs_R0. apply Rle_refl.
  - destruct (Hcell N) as [Hex1 Hb1].
    assert (Hsplit : ex_RInt f (x 0%nat) (x (S N))).
    { apply (ex_RInt_Chasles f (x 0%nat) (x N)); assumption. }
    split. exact Hsplit.
    assert (Hch : RInt f (x 0%nat) (x (S N))
                  = RInt f (x 0%nat) (x N) + RInt f (x N) (x (S N))).
    { symmetry.
      replace (RInt f (x 0%nat) (x N) + RInt f (x N) (x (S N)))
        with (plus (RInt f (x 0%nat) (x N)) (RInt f (x N) (x (S N))))
        by reflexivity.
      apply RInt_Chasles; assumption. }
    rewrite Hch. simpl rsum.
    replace (RInt f (x 0%nat) (x N) + RInt f (x N) (x (S N))
             - (rsum (fun i => (x (S i) - x i) * v i) N
                + (x (S N) - x N) * v N))
      with ((RInt f (x 0%nat) (x N)
             - rsum (fun i => (x (S i) - x i) * v i) N)
            + (RInt f (x N) (x (S N)) - (x (S N) - x N) * v N)) by ring.
    eapply Rle_trans. apply Rabs_triang.
    now apply Rplus_le_compat.
Qed.

End VarTiling.

(* ---------------------------------------------------------------- *)
(* Sums of enclosures                                                *)

(** Enclosures add: when every term of one sum is within its own bound of
    the matching term of another, the two sums are within the sum of the
    bounds. *)
Lemma rsum_triang :
  forall (F v M : nat -> R) N,
  (forall i, (i < N)%nat -> Rabs (F i - v i) <= M i) ->
  Rabs (rsum F N - rsum v N) <= rsum M N.
Proof.
  intros F v M N. induction N as [|N IH]; intros H; simpl.
  - replace (0 - 0) with 0 by ring. rewrite Rabs_R0. apply Rle_refl.
  - replace (rsum F N + F N - (rsum v N + v N))
      with ((rsum F N - rsum v N) + (F N - v N)) by ring.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

(** An integral over a run of abutting cells is the sum of the integrals
    over them, and it exists as soon as they all do. *)
Lemma rsum_chasles :
  forall (g : R -> R) (a h : R) (N : nat),
  (forall i, (i < N)%nat ->
     ex_RInt g (a + 2 * INR i * h) (a + 2 * INR (S i) * h)) ->
  ex_RInt g a (a + 2 * INR N * h) /\
  RInt g a (a + 2 * INR N * h)
  = rsum (fun i => RInt g (a + 2 * INR i * h) (a + 2 * INR (S i) * h)) N.
Proof.
  intros g a h N. induction N as [|N IH]; intros Hex.
  - simpl INR. simpl rsum.
    replace (a + 2 * 0 * h) with a by ring.
    split. apply ex_RInt_point.
    assert (Hz : RInt g a a = 0) by (rewrite RInt_point; reflexivity).
    exact Hz.
  - destruct IH as [IHex IHeq]. { intros i Hi. apply Hex. lia. }
    assert (Hlast : ex_RInt g (a + 2 * INR N * h) (a + 2 * INR (S N) * h))
      by (apply Hex; lia).
    assert (Hsplit : ex_RInt g a (a + 2 * INR (S N) * h)).
    { apply (ex_RInt_Chasles g a (a + 2 * INR N * h)); assumption. }
    split. exact Hsplit.
    replace (rsum (fun i => RInt g (a + 2 * INR i * h)
                                   (a + 2 * INR (S i) * h)) (S N))
      with (rsum (fun i => RInt g (a + 2 * INR i * h)
                                  (a + 2 * INR (S i) * h)) N
            + RInt g (a + 2 * INR N * h) (a + 2 * INR (S N) * h))
      by reflexivity.
    rewrite <- IHeq.
    replace (RInt g a (a + 2 * INR N * h)
             + RInt g (a + 2 * INR N * h) (a + 2 * INR (S N) * h))
      with (plus (RInt g a (a + 2 * INR N * h))
                 (RInt g (a + 2 * INR N * h) (a + 2 * INR (S N) * h)))
      by reflexivity.
    symmetry. apply RInt_Chasles; assumption.
Qed.

(** The integral of a finite sum of functions is the sum of their
    integrals. *)
Lemma rsum_RInt_swap :
  forall (g : nat -> R -> R) (a b : R) (N : nat),
  (forall i, (i < N)%nat -> ex_RInt (g i) a b) ->
  ex_RInt (fun v => rsum (fun i => g i v) N) a b /\
  RInt (fun v => rsum (fun i => g i v) N) a b
  = rsum (fun i => RInt (g i) a b) N.
Proof.
  intros g a b N. induction N as [|N IH]; intros Hex.
  - simpl. split. apply ex_RInt_const.
    rewrite RInt_const_R. ring.
  - destruct IH as [IHex IHeq]. { intros i Hi. apply Hex. lia. }
    assert (Hlast : ex_RInt (g N) a b) by (apply Hex; lia).
    assert (Hplus : ex_RInt (fun v => plus (rsum (fun i => g i v) N) (g N v)) a b)
      by (apply (ex_RInt_plus (fun v => rsum (fun i => g i v) N) (g N));
          assumption).
    split.
    + exact Hplus.
    + change (fun v => rsum (fun i => g i v) (S N))
        with (fun v => plus (rsum (fun i => g i v) N) (g N v)).
      replace (rsum (fun i => RInt (g i) a b) (S N))
        with (rsum (fun i => RInt (g i) a b) N + RInt (g N) a b)
        by reflexivity.
      rewrite <- IHeq.
      replace (RInt (fun v => rsum (fun i => g i v) N) a b + RInt (g N) a b)
        with (plus (RInt (fun v => rsum (fun i => g i v) N) a b)
                   (RInt (g N) a b)) by reflexivity.
      apply (RInt_plus (fun v => rsum (fun i => g i v) N) (g N)); assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* A cell with width in both angles                                  *)

Section Iterated.

(** The integrand as a function of the two angles, the inner integral as a
    function of the outer angle, the centre and half-widths of the cell, and
    a second-derivative bound in each direction. *)
Variable f : R -> R -> R.
Variable G : R -> R.
Variable cu hu cv hv Muu Mvv : R.

Hypothesis Hhu : 0 <= hu.
Hypothesis Hhv : 0 <= hv.

(** Every line of the cell carries the inner midpoint rule with the same
    bound, since the second-derivative enclosure is taken over the box and
    so does not depend on where in the cell the line sits. *)
Hypothesis Hinner :
  forall v, cv - hv <= v <= cv + hv ->
  G v = RInt (fun u => f u v) (cu - hu) (cu + hu) /\
  Rabs (G v - 2 * hu * f cu v) <= 2 * Muu * hu * hu * hu.

Hypothesis HexG : ex_RInt G (cv - hv) (cv + hv).
Hypothesis Hexc : ex_RInt (fun v => f cu v) (cv - hv) (cv + hv).

(** The outer midpoint rule on the line through the centre. *)
Hypothesis Houter :
  Rabs (RInt (fun v => f cu v) (cv - hv) (cv + hv) - 2 * hv * f cu cv)
  <= 2 * Mvv * hv * hv * hv.

(** The iterated midpoint rule over the cell. The two directions are
    separated before either is estimated, so no mixed partial derivative
    enters and the error stays second order in each half-width. *)
Theorem iterated_encloses :
  Rabs (RInt G (cv - hv) (cv + hv) - 4 * hu * hv * f cu cv)
  <= 4 * Muu * hu * hu * hu * hv + 4 * Mvv * hu * hv * hv * hv.
Proof.
  assert (Hab : cv - hv <= cv + hv) by lra.
  assert (Hc := RInt_correct _ _ _ Hexc).
  assert (Hg := RInt_correct _ _ _ HexG).
  assert (HD : is_RInt (fun v => G v - 2 * hu * f cu v) (cv - hv) (cv + hv)
                 (RInt G (cv - hv) (cv + hv)
                  - 2 * hu * RInt (fun v => f cu v) (cv - hv) (cv + hv))).
  { replace (RInt G (cv - hv) (cv + hv)
             - 2 * hu * RInt (fun v => f cu v) (cv - hv) (cv + hv))
      with (minus (RInt G (cv - hv) (cv + hv))
                  (scal (2 * hu) (RInt (fun v => f cu v) (cv - hv) (cv + hv))))
      by reflexivity.
    apply (is_RInt_minus G (fun v => scal (2 * hu) (f cu v))).
    - exact Hg.
    - apply (is_RInt_scal (fun v => f cu v)). exact Hc. }
  assert (HexD : ex_RInt (fun v => G v - 2 * hu * f cu v) (cv - hv) (cv + hv))
    by (eexists; exact HD).
  assert (HDb : Rabs (RInt (fun v => G v - 2 * hu * f cu v) (cv - hv) (cv + hv))
                <= (cv + hv - (cv - hv)) * (2 * Muu * hu * hu * hu)).
  { apply RInt_le_const. exact Hab. exact HexD.
    intros x Hx. destruct (Hinner x ltac:(lra)) as [_ Hb].
    unfold Rabs in Hb. destruct (Rcase_abs (G x - 2 * hu * f cu x)); lra. }
  rewrite (is_RInt_unique _ _ _ _ HD) in HDb.
  replace (cv + hv - (cv - hv)) with (2 * hv) in HDb by ring.
  assert (Hout : Rabs (2 * hu * (RInt (fun v => f cu v) (cv - hv) (cv + hv)
                                 - 2 * hv * f cu cv))
                 <= 2 * hu * (2 * Mvv * hv * hv * hv)).
  { rewrite Rabs_mult. rewrite (Rabs_right (2 * hu)) by lra.
    apply Rmult_le_compat_l. lra. exact Houter. }
  replace (RInt G (cv - hv) (cv + hv) - 4 * hu * hv * f cu cv)
    with ((RInt G (cv - hv) (cv + hv)
           - 2 * hu * RInt (fun v => f cu v) (cv - hv) (cv + hv))
          + 2 * hu * (RInt (fun v => f cu v) (cv - hv) (cv + hv)
                      - 2 * hv * f cu cv)) by ring.
  eapply Rle_trans. apply Rabs_triang.
  replace (4 * Muu * hu * hu * hu * hv + 4 * Mvv * hu * hv * hv * hv)
    with (2 * hv * (2 * Muu * hu * hu * hu) + 2 * hu * (2 * Mvv * hv * hv * hv))
    by ring.
  apply Rplus_le_compat. exact HDb. exact Hout.
Qed.

End Iterated.

(* ---------------------------------------------------------------- *)
(* Summing a two-dimensional tiling                                  *)

Section Tiling2.

(** The integrand over a rectangle of angles, tiled by NU by NV cells of
    half-widths hu and hv. *)
Variable f : R -> R -> R.
Variable au hu av hv : R.
Variable NU NV : nat.

(** The inner integral over u-cell i at height v. *)
Definition ucell (i : nat) (v : R) : R :=
  RInt (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu).

(** Per cell: the value the midpoint rule reports and a bound on its error,
    which [iterated_encloses] delivers. *)
Variable val err : nat -> nat -> R.

Hypothesis Hex_u :
  forall i v, (i < NU)%nat ->
  ex_RInt (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu).
Hypothesis Hex_v :
  forall i j, (i < NU)%nat -> (j < NV)%nat ->
  ex_RInt (ucell i) (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv).
Hypothesis Hcell :
  forall i j, (i < NU)%nat -> (j < NV)%nat ->
  Rabs (RInt (ucell i) (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)
        - val i j) <= err i j.

(** The integral over the whole rectangle exists and is enclosed by the sum
    of the per-cell rules, the errors adding. This is what makes a harmonic
    of the residual a statement about a surface rather than about one curve
    drawn on it. *)
Theorem tiling2_encloses :
  ex_RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
          av (av + 2 * INR NV * hv) /\
  Rabs (RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
             av (av + 2 * INR NV * hv)
        - rsum (fun j => rsum (fun i => val i j) NU) NV)
  <= rsum (fun j => rsum (fun i => err i j) NU) NV.
Proof.
  assert (Hrow : forall v, RInt (fun u => f u v) au (au + 2 * INR NU * hu)
                           = rsum (fun i => ucell i v) NU).
  { intros v.
    apply (proj2 (rsum_chasles (fun u => f u v) au hu NU
                    (fun i Hi => Hex_u i v Hi))). }
  assert (Hj : forall j, (j < NV)%nat ->
            ex_RInt (fun v => rsum (fun i => ucell i v) NU)
                    (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv) /\
            RInt (fun v => rsum (fun i => ucell i v) NU)
                 (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)
            = rsum (fun i => RInt (ucell i) (av + 2 * INR j * hv)
                                            (av + 2 * INR (S j) * hv)) NU).
  { intros j Hjn. apply rsum_RInt_swap. intros i Hi. now apply Hex_v. }
  destruct (rsum_chasles (fun v => rsum (fun i => ucell i v) NU) av hv NV
              (fun j Hjn => proj1 (Hj j Hjn))) as [HexH HeqH].
  split.
  - apply (ex_RInt_ext (fun v => rsum (fun i => ucell i v) NU)).
    + intros x _. symmetry. apply Hrow.
    + exact HexH.
  - rewrite (RInt_ext (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
                      (fun v => rsum (fun i => ucell i v) NU))
      by (intros x _; apply Hrow).
    rewrite HeqH.
    apply rsum_triang. intros j Hjn.
    rewrite (proj2 (Hj j Hjn)).
    apply rsum_triang. intros i Hi.
    now apply Hcell.
Qed.

End Tiling2.

(* ---------------------------------------------------------------- *)
(* Integrability from a Lipschitz bound                              *)

(** t held inside [a, b]. *)
Definition clamp (a b t : R) : R := Rmin b (Rmax a t).

(** The clamp lands in the interval. *)
Lemma clamp_in : forall a b t, a <= b -> a <= clamp a b t <= b.
Proof.
  intros a b t Hab. unfold clamp, Rmin, Rmax.
  repeat destruct (Rle_dec _ _); lra.
Qed.

(** Inside the interval it changes nothing. *)
Lemma clamp_id : forall a b t, a <= t <= b -> clamp a b t = t.
Proof.
  intros a b t Ht. unfold clamp, Rmin, Rmax.
  repeat destruct (Rle_dec _ _); lra.
Qed.

(** It never separates two points. *)
Lemma clamp_lip :
  forall a b x y, Rabs (clamp a b x - clamp a b y) <= Rabs (x - y).
Proof.
  intros a b x y.
  assert (H1 : x - y <= Rabs (x - y)) by apply Rle_abs.
  assert (H2 : - (x - y) <= Rabs (x - y)).
  { rewrite <- Rabs_Ropp. apply Rle_abs. }
  apply Rabs_le. unfold clamp, Rmin, Rmax.
  repeat destruct (Rle_dec _ _); split; lra.
Qed.

(** A function Lipschitz on a closed interval is integrable over it. The
    clamp turns a bound that holds only inside the interval into one that
    holds everywhere, and continuity then follows at every point, endpoints
    included. This is what supplies the integrability of the inner integral
    of an iterated rule, which no bound on a single line gives. *)
Lemma lipschitz_ex_RInt :
  forall (g : R -> R) (L a b : R),
  a <= b -> 0 <= L ->
  (forall x y, a <= x <= b -> a <= y <= b ->
     Rabs (g x - g y) <= L * Rabs (x - y)) ->
  ex_RInt g a b.
Proof.
  intros g L a b Hab HL Hlip.
  apply (ex_RInt_ext (fun t => g (clamp a b t))).
  - intros x Hx.
    rewrite Rmin_left in Hx by exact Hab.
    rewrite Rmax_right in Hx by exact Hab.
    rewrite clamp_id by lra. reflexivity.
  - apply ex_RInt_Reals_1. apply continuity_implies_RiemannInt. exact Hab.
    intros x _.
    unfold continuity_pt, continue_in, limit1_in, limit_in.
    simpl. unfold R_dist.
    intros eps Heps.
    assert (Hpos : 0 < eps / (L + 1)).
    { apply Rdiv_lt_0_compat. exact Heps. lra. }
    exists (eps / (L + 1)). split. exact Hpos.
    intros y [_ Hy].
    apply Rle_lt_trans with (L * Rabs (y - x)).
    + eapply Rle_trans.
      apply (Hlip (clamp a b y) (clamp a b x)); apply clamp_in; exact Hab.
      apply Rmult_le_compat_l. exact HL. apply clamp_lip.
    + apply Rle_lt_trans with (L * (eps / (L + 1))).
      * apply Rmult_le_compat_l. exact HL. lra.
      * assert (Hd : eps / (L + 1) * (L + 1) = eps) by (field; lra).
        nra.
Qed.

(* ---------------------------------------------------------------- *)
(* The iterated rule from the slots of a cell                        *)

Section CellLines.

(** The environment at a point of a two-dimensional cell: [E u v] is the
    slot list after the bindings, with both angle slots set. The component
    sits in slot n, its u-derivatives in ndu and nddu, its v-derivatives in
    ndv and nddv, which is how [with_derivs2] arranges them along each
    slot. *)
Variable E : R -> R -> env ExtendedR.
Variable n ndu nddu ndv nddv : nat.
Variable cu hu cv hv Muu Mvv Dv : R.

Hypothesis Hhu : 0 <= hu.
Hypothesis Hhv : 0 <= hv.

(** The component at a point of the cell. *)
Definition cellval (u v : R) : R := proj_val (eget n (E u v) Xnan).

Hypothesis HU1 : forall v t,
  Xderive_pt (slot_along (fun s => E s v) n) (Xreal t) (eget ndu (E t v) Xnan).
Hypothesis HU2 : forall v t,
  Xderive_pt (slot_along (fun s => E s v) ndu) (Xreal t) (eget nddu (E t v) Xnan).
Hypothesis HV1 : forall u t,
  Xderive_pt (slot_along (fun s => E u s) n) (Xreal t) (eget ndv (E u t) Xnan).
Hypothesis HV2 : forall u t,
  Xderive_pt (slot_along (fun s => E u s) ndv) (Xreal t) (eget nddv (E u t) Xnan).

(** The enclosures over the box: the two second derivatives and the first
    v-derivative, bounded over the whole cell rather than along one line of
    it, which is what an interval evaluation over the box gives. *)
Hypothesis HbU2 : forall u v,
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  exists d, eget nddu (E u v) Xnan = Xreal d /\ Rabs d <= Muu.
Hypothesis HbV2 : forall v, cv - hv <= v <= cv + hv ->
  exists d, eget nddv (E cu v) Xnan = Xreal d /\ Rabs d <= Mvv.
Hypothesis HbV1 : forall u v,
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  exists d, eget ndv (E u v) Xnan = Xreal d /\ Rabs d <= Dv.

(** Every u-line of the cell carries the sharp midpoint rule, with the same
    bound: the second-derivative enclosure comes from the box. *)
Lemma inner_line :
  forall v, cv - hv <= v <= cv + hv ->
  ex_RInt (fun u => cellval u v) (cu - hu) (cu + hu) /\
  Rabs (RInt (fun u => cellval u v) (cu - hu) (cu + hu)
        - 2 * hu * cellval cu v)
  <= 2 * Muu * hu * hu * hu.
Proof.
  intros v Hv. split.
  - exact (sharp_ex_RInt (fun s => E s v) n ndu nddu Muu cu hu Hhu
             (HU1 v) (HU2 v) (fun t Ht => HbU2 t v Ht Hv)).
  - exact (midpoint_sharp (fun s => E s v) n ndu nddu Muu cu hu Hhu
             (HU1 v) (HU2 v) (fun t Ht => HbU2 t v Ht Hv)).
Qed.

(** The line through the centre carries it in the other direction. *)
Lemma outer_line :
  ex_RInt (fun v => cellval cu v) (cv - hv) (cv + hv) /\
  Rabs (RInt (fun v => cellval cu v) (cv - hv) (cv + hv)
        - 2 * hv * cellval cu cv)
  <= 2 * Mvv * hv * hv * hv.
Proof.
  split.
  - exact (sharp_ex_RInt (fun s => E cu s) n ndv nddv Mvv cv hv Hhv
             (HV1 cu) (HV2 cu) HbV2).
  - exact (midpoint_sharp (fun s => E cu s) n ndv nddv Mvv cv hv Hhv
             (HV1 cu) (HV2 cu) HbV2).
Qed.

(** The bound on the first v-derivative is nonnegative. *)
Lemma cell_Dv_nonneg : 0 <= Dv.
Proof.
  destruct (HbV1 cu cv ltac:(lra) ltac:(lra)) as [d [_ Hd]].
  generalize (Rabs_pos d). lra.
Qed.

(** The inner integral is Lipschitz in the outer angle, with the constant
    the first v-derivative gives, so it is integrable over the cell. *)
Lemma inner_ex_RInt :
  ex_RInt (fun v => RInt (fun u => cellval u v) (cu - hu) (cu + hu))
          (cv - hv) (cv + hv).
Proof.
  assert (HDv := cell_Dv_nonneg).
  apply (lipschitz_ex_RInt _ (2 * hu * Dv)). lra.
  { replace (2 * hu * Dv) with ((2 * hu) * Dv) by ring.
    apply Rmult_le_pos. lra. exact HDv. }
  intros v1 v2 H1 H2.
  destruct (inner_line v1 H1) as [Hex1 _].
  destruct (inner_line v2 H2) as [Hex2 _].
  assert (HD : is_RInt (fun u => cellval u v1 - cellval u v2)
                 (cu - hu) (cu + hu)
                 (RInt (fun u => cellval u v1) (cu - hu) (cu + hu)
                  - RInt (fun u => cellval u v2) (cu - hu) (cu + hu))).
  { replace (RInt (fun u => cellval u v1) (cu - hu) (cu + hu)
             - RInt (fun u => cellval u v2) (cu - hu) (cu + hu))
      with (minus (RInt (fun u => cellval u v1) (cu - hu) (cu + hu))
                  (RInt (fun u => cellval u v2) (cu - hu) (cu + hu)))
      by reflexivity.
    apply (is_RInt_minus (fun u => cellval u v1) (fun u => cellval u v2)).
    - exact (RInt_correct _ _ _ Hex1).
    - exact (RInt_correct _ _ _ Hex2). }
  assert (HexD : ex_RInt (fun u => cellval u v1 - cellval u v2)
                   (cu - hu) (cu + hu)) by (eexists; exact HD).
  assert (Hpt : forall u, cu - hu <= u <= cu + hu ->
            Rabs (cellval u v1 - cellval u v2) <= Dv * Rabs (v1 - v2)).
  { intros u Hu.
    destruct (bound_between_dist (fun s => E u s) n ndv Dv
                (cv - hv) (cv + hv) v2 v1 (HV1 u)
                (fun t Ht => HbV1 u t Hu Ht) H2 H1)
      as [w0 [w1 [Hw0 [Hw1 Hinc]]]].
    unfold cellval. rewrite Hw0, Hw1. simpl. exact Hinc. }
  assert (Hb := RInt_le_const (fun u => cellval u v1 - cellval u v2)
                  (cu - hu) (cu + hu) (Dv * Rabs (v1 - v2))
                  ltac:(lra) HexD).
  rewrite (is_RInt_unique _ _ _ _ HD) in Hb.
  replace (cu + hu - (cu - hu)) with (2 * hu) in Hb by ring.
  replace (2 * hu * Dv * Rabs (v1 - v2))
    with (2 * hu * (Dv * Rabs (v1 - v2))) by ring.
  apply Hb.
  intros x Hx. cbv beta.
  assert (H := Hpt x ltac:(lra)).
  set (KK := Dv * Rabs (v1 - v2)) in *.
  unfold Rabs in H.
  destruct (Rcase_abs (cellval x v1 - cellval x v2)); lra.
Qed.

(** The iterated midpoint rule over a cell that has width in both angles,
    read off the slots a cell certificate already carries. Its error is
    second order in each half-width, and no mixed partial derivative
    enters. *)
Theorem cell_iterated_encloses :
  Rabs (RInt (fun v => RInt (fun u => cellval u v) (cu - hu) (cu + hu))
             (cv - hv) (cv + hv)
        - 4 * hu * hv * cellval cu cv)
  <= 4 * Muu * hu * hu * hu * hv + 4 * Mvv * hu * hv * hv * hv.
Proof.
  apply (iterated_encloses cellval
           (fun v => RInt (fun u => cellval u v) (cu - hu) (cu + hu))
           cu hu cv hv Muu Mvv Hhu Hhv).
  - intros v Hv. split. reflexivity. exact (proj2 (inner_line v Hv)).
  - exact inner_ex_RInt.
  - exact (proj1 outer_line).
  - exact (proj2 outer_line).
Qed.

End CellLines.

(* ---------------------------------------------------------------- *)
(* Cauchy-Schwarz for a weighted integral                            *)

(** A nonnegative integrand has a nonnegative integral. *)
Lemma RInt_nonneg :
  forall (h : R -> R) a b,
  a <= b -> ex_RInt h a b ->
  (forall x, a < x < b -> 0 <= h x) ->
  0 <= RInt h a b.
Proof.
  intros h a b Hab Hex Hpos.
  assert (H : RInt (fun _ : R => 0) a b <= RInt h a b).
  { apply RInt_le. exact Hab. apply ex_RInt_const. exact Hex.
    intros x Hx. apply Hpos. exact Hx. }
  rewrite RInt_const_R in H. lra.
Qed.

(** The quadratic that Cauchy-Schwarz rests on: the weighted integral of
    (f - lam g)^2 is nonnegative for every lam, and expands into the three
    integrals. *)
Lemma cs_quadratic :
  forall (f g w : R -> R) a b lam,
  a <= b ->
  ex_RInt (fun x => f x * f x * w x) a b ->
  ex_RInt (fun x => g x * g x * w x) a b ->
  ex_RInt (fun x => f x * g x * w x) a b ->
  (forall x, a < x < b -> 0 <= w x) ->
  0 <= RInt (fun x => f x * f x * w x) a b
       - 2 * lam * RInt (fun x => f x * g x * w x) a b
       + lam * lam * RInt (fun x => g x * g x * w x) a b.
Proof.
  intros f g w a b lam Hab Hff Hgg Hfg Hw.
  assert (HA := RInt_correct _ _ _ Hff).
  assert (HB := RInt_correct _ _ _ Hfg).
  assert (HC := RInt_correct _ _ _ Hgg).
  set (A := RInt (fun x => f x * f x * w x) a b) in *.
  set (B := RInt (fun x => f x * g x * w x) a b) in *.
  set (C := RInt (fun x => g x * g x * w x) a b) in *.
  assert (Hsum : is_RInt (fun x => (f x - lam * g x) * (f x - lam * g x) * w x)
                   a b (A + (- (2 * lam) * B + lam * lam * C))).
  { apply (is_RInt_ext
             (fun x => plus (f x * f x * w x)
                            (plus (scal (- (2 * lam)) (f x * g x * w x))
                                  (scal (lam * lam) (g x * g x * w x))))).
    - intros x _. unfold plus, scal; simpl. unfold mult; simpl. ring.
    - replace (A + (- (2 * lam) * B + lam * lam * C))
        with (plus A (plus (scal (- (2 * lam)) B) (scal (lam * lam) C)))
        by reflexivity.
      apply (is_RInt_plus (fun x => f x * f x * w x)
               (fun x => plus (scal (- (2 * lam)) (f x * g x * w x))
                              (scal (lam * lam) (g x * g x * w x)))).
      exact HA.
      apply (is_RInt_plus (fun x => scal (- (2 * lam)) (f x * g x * w x))
               (fun x => scal (lam * lam) (g x * g x * w x))).
      + apply (is_RInt_scal (fun x => f x * g x * w x)). exact HB.
      + apply (is_RInt_scal (fun x => g x * g x * w x)). exact HC. }
  assert (Hex : ex_RInt (fun x => (f x - lam * g x) * (f x - lam * g x) * w x)
                  a b) by (eexists; exact Hsum).
  assert (Hnn : 0 <= RInt (fun x => (f x - lam * g x) * (f x - lam * g x) * w x)
                       a b).
  { apply RInt_nonneg. exact Hab. exact Hex.
    intros x Hx. apply Rmult_le_pos.
    - assert (Hs := Rle_0_sqr (f x - lam * g x)). unfold Rsqr in Hs.
      exact Hs.
    - now apply Hw. }
  rewrite (is_RInt_unique _ _ _ _ Hsum) in Hnn.
  lra.
Qed.

(** Cauchy-Schwarz with a nonnegative weight. *)
Lemma cauchy_schwarz_pos :
  forall (f g w : R -> R) a b,
  a <= b ->
  ex_RInt (fun x => f x * f x * w x) a b ->
  ex_RInt (fun x => g x * g x * w x) a b ->
  ex_RInt (fun x => f x * g x * w x) a b ->
  (forall x, a < x < b -> 0 <= w x) ->
  RInt (fun x => f x * g x * w x) a b * RInt (fun x => f x * g x * w x) a b
  <= RInt (fun x => f x * f x * w x) a b
     * RInt (fun x => g x * g x * w x) a b.
Proof.
  intros f g w a b Hab Hff Hgg Hfg Hw.
  assert (HC : 0 <= RInt (fun x => g x * g x * w x) a b).
  { apply RInt_nonneg. exact Hab. exact Hgg.
    intros x Hx. apply Rmult_le_pos.
    - assert (Hs := Rle_0_sqr (g x)). unfold Rsqr in Hs. exact Hs.
    - now apply Hw. }
  set (A := RInt (fun x => f x * f x * w x) a b) in *.
  set (B := RInt (fun x => f x * g x * w x) a b) in *.
  set (C := RInt (fun x => g x * g x * w x) a b) in *.
  destruct (Rle_lt_or_eq_dec 0 C HC) as [Hpos|Hzero].
  - assert (H := cs_quadratic f g w a b (B / C) Hab Hff Hgg Hfg Hw).
    fold A B C in H.
    assert (Heq : A - 2 * (B / C) * B + (B / C) * (B / C) * C
                  = A - B * B / C) by (field; lra).
    rewrite Heq in H.
    assert (Hbc : B * B / C * C = B * B) by (field; lra).
    nra.
  - (* the weighted integral of g^2 vanishes, so B has to vanish too *)
    destruct (Req_dec B 0) as [HB|HB].
    + rewrite HB, <- Hzero. ring_simplify. apply Rle_refl.
    + exfalso.
      assert (H := cs_quadratic f g w a b ((A + 1) / (2 * B)) Hab Hff Hgg Hfg Hw).
      fold A B C in H.
      rewrite <- Hzero in H.
      assert (Heq : A - 2 * ((A + 1) / (2 * B)) * B
                    + (A + 1) / (2 * B) * ((A + 1) / (2 * B)) * 0 = -1)
        by (field; lra).
      rewrite Heq in H. lra.
Qed.

(** With a weight of one sign, either sign, the same inequality holds:
    negating the weight negates all three integrals, which leaves the square
    on the left and the product on the right unchanged. *)
Theorem cauchy_schwarz_weighted :
  forall (f g w : R -> R) a b,
  a <= b ->
  ex_RInt (fun x => f x * f x * w x) a b ->
  ex_RInt (fun x => g x * g x * w x) a b ->
  ex_RInt (fun x => f x * g x * w x) a b ->
  ((forall x, a < x < b -> 0 <= w x) \/ (forall x, a < x < b -> w x <= 0)) ->
  RInt (fun x => f x * g x * w x) a b * RInt (fun x => f x * g x * w x) a b
  <= RInt (fun x => f x * f x * w x) a b
     * RInt (fun x => g x * g x * w x) a b.
Proof.
  intros f g w a b Hab Hff Hgg Hfg [Hw|Hw].
  - now apply cauchy_schwarz_pos.
  - (* run the positive case on the negated weight *)
    assert (Hopp : forall (h : R -> R),
              ex_RInt (fun x => h x * w x) a b ->
              ex_RInt (fun x => h x * - w x) a b /\
              RInt (fun x => h x * - w x) a b
              = - RInt (fun x => h x * w x) a b).
    { intros h Hh.
      assert (Hc := RInt_correct _ _ _ Hh).
      assert (Hn : is_RInt (fun x => h x * - w x) a b
                     (- RInt (fun x => h x * w x) a b)).
      { apply (is_RInt_ext (fun x => opp (h x * w x))).
        - intros x _. unfold opp; simpl. ring.
        - replace (- RInt (fun x => h x * w x) a b)
            with (opp (RInt (fun x => h x * w x) a b)) by reflexivity.
          apply (is_RInt_opp (fun x => h x * w x)). exact Hc. }
      split. eexists; exact Hn.
      exact (is_RInt_unique _ _ _ _ Hn). }
    destruct (Hopp (fun x => f x * f x) Hff) as [Hff' Eff].
    destruct (Hopp (fun x => g x * g x) Hgg) as [Hgg' Egg].
    destruct (Hopp (fun x => f x * g x) Hfg) as [Hfg' Efg].
    assert (H := cauchy_schwarz_pos f g (fun x => - w x) a b Hab
                   Hff' Hgg' Hfg' (fun x Hx => ltac:(generalize (Hw x Hx); lra))).
    cbv beta in Eff, Egg, Efg, H.
    rewrite Eff, Egg, Efg in H.
    nra.
Qed.

(** The geodesic-curvature term of the Mercier criterion is never positive.

    With the weight w = gpp gf of `mercier.f90`, f = mu0 (J.B) / |B| and
    g = |B|, its three integrals are

      tjb = int f g w,  tbb = int g^2 w,  tjj = int f^2 w,

    so Dgeod = tjb^2 - tbb tjj is exactly the Cauchy-Schwarz defect and is
    nonpositive whatever the numbers, for either sign of the weight. No
    enclosure decides this: tjb^2 and tbb tjj agree to ten digits, so the
    three averages bounded separately leave the sign open however fine the
    covering. The inequality settles it once and for all. *)
Corollary mercier_geodesic_nonpositive :
  forall (f g w : R -> R) a b,
  a <= b ->
  ex_RInt (fun x => f x * f x * w x) a b ->
  ex_RInt (fun x => g x * g x * w x) a b ->
  ex_RInt (fun x => f x * g x * w x) a b ->
  ((forall x, a < x < b -> 0 <= w x) \/ (forall x, a < x < b -> w x <= 0)) ->
  RInt (fun x => f x * g x * w x) a b * RInt (fun x => f x * g x * w x) a b
  - RInt (fun x => g x * g x * w x) a b
    * RInt (fun x => f x * f x * w x) a b
  <= 0.
Proof.
  intros f g w a b Hab Hff Hgg Hfg Hw.
  assert (H := cauchy_schwarz_weighted f g w a b Hab Hff Hgg Hfg Hw).
  nra.
Qed.

(* ---------------------------------------------------------------- *)
(* Differentiating an integral in a parameter                        *)

(** A surface average is an integral over the angles of a quantity that also
    depends on the radius. Reading its radial derivative off the integral of
    the radial derivative is what the magnetic well and the shear need, and
    with them DMerc, since those are radial derivatives of averages and no
    single surface holds them.

    The step is licensed by a second derivative bounded over the box, which is
    what an interval evaluation over a cell delivers and what [with_derivs2]
    already arranges into slots. Nothing here is specific to the residual: it
    is stated for real functions of two variables and instantiated by the
    slots of a cell in the same way [cell_iterated_encloses] instantiates the
    quadrature. *)

(** Taylor with the remainder a second derivative forces. The mean value is
    taken between the two points rather than over the whole interval, so the
    slope defect is charged against the distance actually travelled and the
    remainder is quadratic in it. The uniform form, with the slope bounded
    over the whole cell, is enough for a bound but not for a derivative: it
    leaves an error linear in the step, which does not vanish beside it. *)
Lemma taylor_sharp :
  forall (g g' g'' : R -> R) (x0 r M2 : R),
  (forall t, x0 - r <= t <= x0 + r -> derivable_pt_lim g t (g' t)) ->
  (forall t, x0 - r <= t <= x0 + r -> derivable_pt_lim g' t (g'' t)) ->
  (forall t, x0 - r <= t <= x0 + r -> Rabs (g'' t) <= M2) ->
  forall t, x0 - r <= t <= x0 + r ->
  Rabs (g t - g x0 - g' x0 * (t - x0)) <= M2 * Rabs (t - x0) * Rabs (t - x0).
Proof.
  intros g g' g'' x0 r M2 Hd1 Hd2 Hb t Ht.
  assert (Hr : 0 <= r).
  { destruct Ht. lra. }
  assert (HM : 0 <= M2).
  { generalize (Hb x0 ltac:(lra)). generalize (Rabs_pos (g'' x0)). lra. }
  (* everything happens between x0 and t *)
  assert (Hsub : forall q, Rmin x0 t <= q <= Rmax x0 t -> x0 - r <= q <= x0 + r).
  { intros q Hq. unfold Rmin, Rmax in Hq.
    destruct (Rle_dec x0 t); lra. }
  assert (Hx0 : Rmin x0 t <= x0 <= Rmax x0 t).
  { unfold Rmin, Rmax. destruct (Rle_dec x0 t); lra. }
  assert (Ht' : Rmin x0 t <= t <= Rmax x0 t).
  { unfold Rmin, Rmax. destruct (Rle_dec x0 t); lra. }
  assert (Hnear : forall q, Rmin x0 t <= q <= Rmax x0 t ->
            (Rabs (q - x0) <= Rabs (t - x0))%R).
  { intros q Hq. unfold Rmin, Rmax in Hq.
    destruct (Rle_dec x0 t) as [Hle|Hgt].
    - rewrite (Rabs_right (q - x0)) by lra.
      rewrite (Rabs_right (t - x0)) by lra. lra.
    - rewrite (Rabs_left1 (q - x0)) by lra.
      rewrite (Rabs_left1 (t - x0)) by lra. lra. }
  assert (Hd : forall q, Rmin x0 t <= q <= Rmax x0 t ->
            derivable_pt_lim (fun u : R => g u - g' x0 * (u - x0)) q
              (g' q - g' x0)).
  { intros q Hq. apply derivable_pt_lim_minus. apply Hd1. now apply Hsub.
    apply (proj1 (is_derive_Reals _ _ _)).
    auto_derive; try exact I; try field; try lra. }
  assert (Hslope : forall q, Rmin x0 t <= q <= Rmax x0 t ->
            Rabs (g' q - g' x0) <= M2 * Rabs (t - x0)).
  { intros q Hq.
    assert (H2 := mvt_bound g' g'' (Rmin x0 t) (Rmax x0 t) M2
                    (fun z Hz => Hd2 z (Hsub z Hz))
                    (fun z Hz => Hb z (Hsub z Hz)) x0 q Hx0 Hq).
    apply Rle_trans with (M2 * Rabs (q - x0)). exact H2.
    apply Rmult_le_compat_l. exact HM. now apply Hnear. }
  assert (Hmv := mvt_bound (fun u : R => g u - g' x0 * (u - x0))
                   (fun q => g' q - g' x0) (Rmin x0 t) (Rmax x0 t)
                   (M2 * Rabs (t - x0)) Hd Hslope x0 t Hx0 Ht').
  cbv beta in Hmv.
  replace (g t - g' x0 * (t - x0) - (g x0 - g' x0 * (x0 - x0)))
    with (g t - g x0 - g' x0 * (t - x0)) in Hmv by ring.
  exact Hmv.
Qed.

Section DiffUnderIntegral.

(** The integrand, its derivative in the parameter, and that derivative's own
    derivative, each as a function of the parameter and the angle. *)
Variable f fs fss : R -> R -> R.
Variable a b s0 r M2 : R.

Hypothesis Hab : a <= b.
Hypothesis Hr : 0 <= r.
Hypothesis Hd1 : forall s u, s0 - r <= s <= s0 + r -> a <= u <= b ->
  derivable_pt_lim (fun t => f t u) s (fs s u).
Hypothesis Hd2 : forall s u, s0 - r <= s <= s0 + r -> a <= u <= b ->
  derivable_pt_lim (fun t => fs t u) s (fss s u).
Hypothesis Hb2 : forall s u, s0 - r <= s <= s0 + r -> a <= u <= b ->
  Rabs (fss s u) <= M2.
Hypothesis Hexf : forall s, s0 - r <= s <= s0 + r ->
  ex_RInt (fun u => f s u) a b.
Hypothesis Hexs : ex_RInt (fun u => fs s0 u) a b.

(** The average as a function of the parameter. *)
Definition avg (s : R) : R := RInt (fun u => f s u) a b.

(** Its increment is the integral of the derivative, to first order, with the
    error a second derivative forces. Integrating the pointwise Taylor step is
    all that happens; what makes it sound is that the bound is uniform in the
    angle, which is what an enclosure over the box gives. *)
Theorem avg_increment :
  forall s, s0 - r <= s <= s0 + r ->
  Rabs (avg s - avg s0 - (s - s0) * RInt (fun u => fs s0 u) a b)
  <= (b - a) * (M2 * Rabs (s - s0) * Rabs (s - s0)).
Proof.
  intros s Hs.
  assert (Hpt : forall u, a <= u <= b ->
            Rabs (f s u - f s0 u - fs s0 u * (s - s0))
            <= M2 * Rabs (s - s0) * Rabs (s - s0)).
  { intros u Hu.
    apply (taylor_sharp (fun t => f t u) (fun t => fs t u)
             (fun t => fss t u) s0 r M2).
    - intros q Hq. now apply Hd1.
    - intros q Hq. now apply Hd2.
    - intros q Hq. now apply Hb2.
    - exact Hs. }
  assert (HD : is_RInt (fun u => f s u - f s0 u - (s - s0) * fs s0 u) a b
                 (avg s - avg s0 - (s - s0) * RInt (fun u => fs s0 u) a b)).
  { unfold avg.
    replace (RInt (fun u => f s u) a b - RInt (fun u => f s0 u) a b
             - (s - s0) * RInt (fun u => fs s0 u) a b)
      with (minus (minus (RInt (fun u => f s u) a b)
                         (RInt (fun u => f s0 u) a b))
                  (scal (s - s0) (RInt (fun u => fs s0 u) a b)))
      by reflexivity.
    apply (is_RInt_minus (fun u => f s u - f s0 u)
             (fun u => scal (s - s0) (fs s0 u))).
    - apply (is_RInt_minus (fun u => f s u) (fun u => f s0 u)).
      + exact (RInt_correct _ _ _ (Hexf s Hs)).
      + exact (RInt_correct _ _ _ (Hexf s0 ltac:(lra))).
    - apply (is_RInt_scal (fun u => fs s0 u)).
      exact (RInt_correct _ _ _ Hexs). }
  assert (HexD : ex_RInt (fun u => f s u - f s0 u - (s - s0) * fs s0 u) a b)
    by (eexists; exact HD).
  assert (Hle := RInt_le_const
                   (fun u => f s u - f s0 u - (s - s0) * fs s0 u) a b
                   (M2 * Rabs (s - s0) * Rabs (s - s0)) Hab HexD).
  rewrite (is_RInt_unique _ _ _ _ HD) in Hle.
  apply Hle.
  intros x Hx. cbv beta.
  assert (H := Hpt x ltac:(lra)).
  replace (f s x - f s0 x - (s - s0) * fs s0 x)
    with (f s x - f s0 x - fs s0 x * (s - s0)) by ring.
  assert (Hup := Rle_abs (f s x - f s0 x - fs s0 x * (s - s0))).
  assert (Hlo := Rabs_maj2 (f s x - f s0 x - fs s0 x * (s - s0))).
  lra.
Qed.

(** So the average is differentiable in the parameter and its derivative is
    the integral of the derivative. This is the step that turns a certified
    enclosure of the integral of d(sqrt g)/ds into a certified enclosure of
    V'', and the same construction gives the shear from iota. Those are what
    the magnetic well and DMerc are missing, since each combines quantities
    from neighbouring surfaces that no single certificate holds. *)
Theorem diff_under_integral :
  0 < r ->
  derivable_pt_lim avg s0 (RInt (fun u => fs s0 u) a b).
Proof.
  intros Hrpos eps Heps.
  assert (HM : 0 <= M2).
  { generalize (Hb2 s0 a ltac:(lra) ltac:(lra)).
    generalize (Rabs_pos (fss s0 a)). lra. }
  set (C := (b - a) * M2).
  assert (HC : 0 <= C).
  { unfold C. apply Rmult_le_pos. lra. exact HM. }
  assert (Hpos : 0 < Rmin r (eps / (C + 1))).
  { apply Rmin_pos. exact Hrpos.
    apply Rdiv_lt_0_compat. exact Heps. lra. }
  exists (mkposreal _ Hpos).
  intros h Hh0 Hh. simpl in Hh.
  assert (Hlt : Rabs h < r)
    by (eapply Rlt_le_trans; [exact Hh|apply Rmin_l]).
  assert (Hin : s0 - r <= s0 + h <= s0 + r).
  { apply Rabs_lt_between in Hlt. lra. }
  assert (Hbnd := avg_increment (s0 + h) Hin).
  replace (s0 + h - s0) with h in Hbnd by ring.
  set (L := RInt (fun u => fs s0 u) a b) in *.
  assert (Hq : Rabs ((avg (s0 + h) - avg s0) / h - L) <= C * Rabs h).
  { replace ((avg (s0 + h) - avg s0) / h - L)
      with ((avg (s0 + h) - avg s0 - h * L) / h)
      by (field; exact Hh0).
    rewrite Rabs_div by exact Hh0.
    apply Rle_div_l. now apply Rabs_pos_lt.
    apply Rle_trans with ((b - a) * (M2 * Rabs h * Rabs h)).
    exact Hbnd. unfold C. right. ring. }
  apply Rle_lt_trans with (C * Rabs h). exact Hq.
  assert (Hsm : Rabs h < eps / (C + 1))
    by (eapply Rlt_le_trans; [exact Hh|apply Rmin_r]).
  apply Rle_lt_trans with (C * (eps / (C + 1))).
  - apply Rmult_le_compat_l. exact HC. lra.
  - assert (eps / (C + 1) * (C + 1) = eps) by (field; lra). nra.
Qed.

End DiffUnderIntegral.

(* ---------------------------------------------------------------- *)
(* A cell step charged against the derivative at its centre          *)

(** Cell.v walks from the centre of a cell charging each step against the
    derivative enclosed over the whole box. That enclosure does not see the
    cancellation the residual lives on, so it exceeds the derivative at the
    centre by a factor that only falls as the cell narrows.

    This is the same step charged against the derivative at the centre, which
    is a thin evaluation with no box in it, with the box paying only for a
    second derivative against the square of the distance. The slots are the
    ones [with_derivs2] arranges: the value, its derivative one offset up, and
    the second two offsets up. *)
Section TaylorStep.

Variable F : R -> env ExtendedR.
Variable n nd ndd : nat.
Variable M2 c h : R.

Hypothesis Hh : 0 <= h.
Hypothesis Hder1 :
  forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan).
Hypothesis Hder2 :
  forall t, Xderive_pt (slot_along F nd) (Xreal t) (eget ndd (F t) Xnan).
Hypothesis Hbnd2 :
  forall t, c - h <= t <= c + h ->
  exists d, eget ndd (F t) Xnan = Xreal d /\ Rabs d <= M2.

(** The value and its derivative at the centre are real, and the step from the
    centre is the derivative there times the distance, with a remainder the
    second derivative bounds. *)
Theorem taylor_step :
  exists v d,
    eget n (F c) Xnan = Xreal v /\
    eget nd (F c) Xnan = Xreal d /\
    forall t, c - h <= t <= c + h ->
    exists w,
      eget n (F t) Xnan = Xreal w /\
      Rabs (w - v - d * (t - c)) <= M2 * Rabs (t - c) * Rabs (t - c).
Proof.
  (* n appears in neither of these, so it is not discharged into them *)
  assert (Hd1 := sharp_d1_real F nd ndd M2 c h Hder2 Hbnd2).
  assert (Hphi := sharp_phi_deriv F n nd ndd M2 c h Hder1 Hder2 Hbnd2).
  assert (Hphi' := sharp_phi'_deriv F nd ndd M2 c h Hder2 Hbnd2).
  (* the value is real wherever its derivative is *)
  assert (Hval : forall t, c - h <= t <= c + h ->
            eget n (F t) Xnan = Xreal (sphi F n t)).
  { intros t Ht.
    assert (Hr := Hd1 t Ht).
    assert (H := Hder1 t). rewrite Hr in H.
    unfold Xderive_pt in H. unfold slot_along in H at 1.
    destruct (eget n (F t) Xnan) as [|w] eqn:Hw. contradiction.
    unfold sphi, proj_fun, slot_along. now rewrite Hw. }
  exists (sphi F n c), (sphi' F nd c).
  split. apply Hval. lra.
  split. apply Hd1. lra.
  intros t Ht.
  exists (sphi F n t). split. now apply Hval.
  apply (taylor_sharp (sphi F n) (sphi' F nd)
           (fun s => proj_val (eget ndd (F s) Xnan)) c h M2).
  - intros s Hs. now apply Hphi.
  - intros s Hs. now apply Hphi'.
  - intros s Hs. destruct (Hbnd2 s Hs) as [d [Hd Hdb]].
    rewrite Hd. simpl. exact Hdb.
  - exact Ht.
Qed.

End TaylorStep.

(** The step in one varied slot, charged against the derivative at the centre
    with the box paying only for a second derivative. *)
Lemma taylor_leg :
  forall base len binds du x n Nd qd N2 q2 (env0 : env ExtendedR) (cx : R),
  (x < base)%nat -> (0 < len)%nat ->
  well_formed base binds = true -> len = length binds ->
  (base <= n)%nat -> (n < base + len)%nat -> (0 <= du)%Z ->
  (forall k, (base <= k)%nat -> eget k env0 Xnan = Xnan) ->
  (forall k, (k < base)%nat -> exists v, eget k env0 Xnan = Xreal v) ->
  (exists d, eget (n + len)%nat (F2 base len binds x env0 cx) Xnan = Xreal d
             /\ (Rabs d <= IZR Nd * powerRZ 2%R qd)%R) ->
  (forall t, (cx - IZR du <= t <= cx + IZR du)%R ->
     exists d, eget (n + 2 * len)%nat (F2 base len binds x env0 t) Xnan = Xreal d
               /\ (Rabs d <= IZR N2 * powerRZ 2%R q2)%R) ->
  forall Mx, (cx - IZR du <= Mx <= cx + IZR du)%R ->
  exists v w,
    eget n (xextend (eset x env0 (Xreal cx)) binds) Xnan = Xreal v /\
    eget n (xextend (eset x env0 (Xreal Mx)) binds) Xnan = Xreal w /\
    (Rabs (w - v) <= IZR du * (IZR Nd * powerRZ 2%R qd)
                     + IZR N2 * powerRZ 2%R q2 * IZR du * IZR du)%R.
Proof.
  intros base len binds du x n Nd qd N2 q2 env0 cx
         Hxb Hlen0 Hwf Hlen Hbn Hnlt Hdu Hunset Hreal Hd1 Hbnd2 Mx Hin.
  assert (Hh : (0 <= IZR du)%R) by (apply IZR_le; lia).
  assert (Hinv := inv2_of base len binds x env0 Hxb Hlen0 Hwf Hlen
                    Hunset Hreal).
  destruct (deriv2_slots base len binds x env0 n Hxb Hbn Hinv)
    as [Hder1 Hder2].
  destruct (taylor_step (F2 base len binds x env0) n (n + len)%nat
              (n + 2 * len)%nat (IZR N2 * powerRZ 2%R q2) cx (IZR du)
              Hh Hder1 Hder2 Hbnd2)
    as [v [d [Hv [Hd Hstep]]]].
  destruct (Hstep Mx Hin) as [w [Hw Htay]].
  destruct Hd1 as [d0 [Hd0 Hd0b]].
  rewrite Hd0 in Hd. injection Hd as <-.
  assert (Hval : forall t, eget n (F2 base len binds x env0 t) Xnan
                   = eget n (xextend (eset x env0 (Xreal t)) binds) Xnan).
  { intros t. unfold F2.
    apply (values_with_derivs2 x base len binds _ _ base Hwf);
      try lia; try (intros k _; reflexivity). }
  rewrite Hval in Hv, Hw.
  exists v, w. split. exact Hv. split. exact Hw.
  assert (Habs : (Rabs (Mx - cx) <= IZR du)%R) by (apply Rabs_le; lra).
  assert (HN2 : (0 <= IZR N2 * powerRZ 2%R q2)%R).
  { destruct (Hbnd2 cx ltac:(lra)) as [dd [_ Hdd]].
    generalize (Rabs_pos dd). lra. }
  assert (H1 : (Rabs (d0 * (Mx - cx)) <= IZR du * (IZR Nd * powerRZ 2%R qd))%R).
  { rewrite Rabs_mult.
    apply Rle_trans with ((IZR Nd * powerRZ 2%R qd) * IZR du)%R.
    - apply Rmult_le_compat; try apply Rabs_pos. exact Hd0b. exact Habs.
    - right. ring. }
  assert (H2 : (Rabs (w - v - d0 * (Mx - cx))
                <= IZR N2 * powerRZ 2%R q2 * IZR du * IZR du)%R).
  { eapply Rle_trans. exact Htay.
    apply Rmult_le_compat.
    - apply Rmult_le_pos. exact HN2. apply Rabs_pos.
    - apply Rabs_pos.
    - apply Rmult_le_compat_l. exact HN2. exact Habs.
    - exact Habs. }
  replace (w - v)%R with ((w - v - d0 * (Mx - cx)) + d0 * (Mx - cx))%R by ring.
  eapply Rle_trans. apply Rabs_triang. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Soundness of a Taylor cell                                        *)

Section TaylorCell.

Variable slot_u slot_v : nat.
Hypothesis Huv : slot_u <> slot_v.

(** A passing Taylor check bounds the component at every real point of the
    cell, exactly as the mean-value check does. The first slot's leg is
    [taylor_leg], charged against the derivative at the centre with the box
    paying for a second derivative; the second slot keeps the mean-value step
    of [bound_between_dist], because its leg starts from a point that moves
    with the first slot. *)
Lemma component_t_correct :
  forall prec ms base len binds du dv r tb,
  length ms = base -> (slot_u < base)%nat -> (slot_v < base)%nat ->
  (0 < len)%nat -> (0 <= du)%Z -> (0 <= dv)%Z ->
  well_formed base binds = true -> len = length binds ->
  check_component_t prec base len du dv
    (iextend prec (ienv_of prec ms) binds)
    (iextend prec (ienv_of prec ms) (with_derivs2 slot_u base len binds))
    (iextend prec (box_ienv slot_u slot_v prec ms du dv)
       (with_derivs2 slot_u base len binds))
    (iextend prec (box_ienv slot_u slot_v prec ms du dv)
       (with_derivs slot_v base len binds))
    r tb = true ->
  component_t_sound slot_u slot_v ms binds du dv r tb.
Proof.
  intros prec ms base len binds du dv r tb
         Hms Hbu Hbv Hlen0 Hdu Hdv Hwf Hlen Hchk.
  unfold check_component_t in Hchk.
  destruct r; simpl in Hchk; try discriminate.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcomb].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hv_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Huu_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hu_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcentre].
  apply andb_prop in Hchk. destruct Hchk as [Hbn Hn].
  apply Nat.leb_le in Hbn. apply Nat.ltb_lt in Hn.
  assert (Hcombi := combination_t_correct prec du dv tb Hcomb).
  intros Mu Mv Hin.
  assert (HinU := proj1 Hin). assert (HinV := proj2 Hin).
  assert (Hin0 : in_cell slot_u slot_v ms du dv (IZR (nth slot_u ms 0%Z)) (IZR (nth slot_v ms 0%Z))).
  { unfold in_cell. rewrite !minus_IZR, !plus_IZR.
    generalize (IZR_le 0 du Hdu). generalize (IZR_le 0 dv Hdv). lra. }
  (* the value at the centre *)
  assert (Henv0 := iextend_correct prec binds _ _ (env_ok_fromZ prec ms)).
  destruct (check1_correct _ _ _ _ _ _ Henv0 Hcentre) as [w0 [Hw0 Hb0]].
  simpl in Hw0.
  (* the inputs of the point, which the centre of the cell is *)
  destruct (inputs_real slot_u slot_v Huv ms base (IZR (nth slot_u ms 0%Z)) (IZR (nth slot_v ms 0%Z)) Hms (conj Hbu Hbv))
    as [Hl Hr].
  rewrite (cell_env_center slot_u slot_v Huv ms base Hms (conj Hbu Hbv)) in Hl, Hr.
  (* leg one, charged against the derivative at the centre *)
  assert (Hset : eset slot_u (xenv_of ms) (Xreal (IZR (nth slot_u ms 0%Z))) = xenv_of ms)
    by (apply (xenv_of_set slot_u slot_v Huv ms base slot_u Hms Hbu)).
  assert (Hd1 : exists d,
            eget (n + len)%nat
              (F2 base len binds slot_u (xenv_of ms) (IZR (nth slot_u ms 0%Z))) Xnan
            = Xreal d
            /\ (Rabs d <= IZR (tb_Nu tb) * powerRZ 2%R (tb_qu tb))%R).
  { unfold F2. rewrite Hset.
    assert (He := iextend_correct prec (with_derivs2 slot_u base len binds)
                    _ _ (env_ok_fromZ prec ms)).
    destruct (check1_correct _ _ _ _ _ _ He Hu_chk) as [d [Hd Hb]].
    exists d. split. exact Hd. exact Hb. }
  assert (Hd2 : forall t, ((IZR (nth slot_u ms 0%Z)) - IZR du <= t <= (IZR (nth slot_u ms 0%Z)) + IZR du)%R ->
            exists d,
              eget (n + 2 * len)%nat
                (F2 base len binds slot_u (xenv_of ms) t) Xnan
              = Xreal d
              /\ (Rabs d <= IZR (tb_Nuu tb) * powerRZ 2%R (tb_quu tb))%R).
  { intros t Ht. unfold F2.
    rewrite <- (cell_env_at_v_centre slot_u slot_v Huv ms base t Hms Hbv).
    assert (Hin_t : in_cell slot_u slot_v ms du dv t (IZR (nth slot_v ms 0%Z))).
    { split.  rewrite minus_IZR, plus_IZR. exact Ht.
      exact (proj2 Hin0). }
    assert (He := iextend_correct prec (with_derivs2 slot_u base len binds)
                    _ _ (box_env_ok slot_u slot_v prec ms du dv t (IZR (nth slot_v ms 0%Z)) Hin_t)).
    destruct (check1_correct _ _ _ _ _ _ He Huu_chk) as [d [Hd Hb]].
    exists d. split. exact Hd. exact Hb. }
  assert (HinU' : ((IZR (nth slot_u ms 0%Z)) - IZR du <= Mu <= (IZR (nth slot_u ms 0%Z)) + IZR du)%R).
  { rewrite minus_IZR, plus_IZR in HinU. exact HinU. }
  destruct (taylor_leg base len binds du slot_u n
              (tb_Nu tb) (tb_qu tb) (tb_Nuu tb) (tb_quu tb) (xenv_of ms) (IZR (nth slot_u ms 0%Z))
              Hbu Hlen0 Hwf Hlen Hbn Hn Hdu Hl Hr Hd1 Hd2 Mu HinU')
    as [v1 [w1 [Hv1 [Hw1 Hleg1]]]].
  rewrite Hset in Hv1.
  rewrite Hw0 in Hv1. injection Hv1 as <-.
  (* leg two, the mean-value step in the second slot *)
  set (Fv := fun t => xextend (eset slot_v (eset slot_u (xenv_of ms) (Xreal Mu))
                                 (Xreal t))
                        (with_derivs slot_v base len binds)).
  assert (Hinv_v : inv slot_v base len Fv (base + len)).
  { destruct (inputs_real slot_u slot_v Huv ms base Mu (IZR (nth slot_v ms 0%Z)) Hms (conj Hbu Hbv))
      as [Hl2 Hr2].
    rewrite (cell_env_v slot_u slot_v Huv) in Hl2, Hr2.
    assert (Hbase := inv_base slot_v base len ltac:(lia) ltac:(lia) _ Hl2 Hr2).
    assert (Hres := inv_bindings slot_v base len ltac:(lia) ltac:(lia)
                      binds _ base Hbase Hwf ltac:(lia) ltac:(lia)).
    rewrite <- Hlen in Hres.
    refine (inv_ext slot_v base len _ Fv (base + len) _ Hres).
    intros t. unfold Fv. now rewrite eset_overwrite. }
  assert (Hdv_n := deriv_slot_of slot_u slot_v Huv slot_v base len Fv (base + len) n
                     ltac:(lia) Hbn Hinv_v).
  set (Dv := (IZR (tb_Nv tb) * powerRZ 2%R (tb_qv tb))%R).
  set (lo_v := IZR (nth slot_v ms 0%Z - dv)).
  set (hi_v := IZR (nth slot_v ms 0%Z + dv)).
  assert (Hbnd_v : forall t, (lo_v <= t <= hi_v)%R ->
            exists d, eget (n + len)%nat (Fv t) Xnan = Xreal d
                      /\ (Rabs d <= Dv)%R).
  { intros t Ht.
    assert (Hin_t : in_cell slot_u slot_v ms du dv Mu t)
      by (split; assumption).
    assert (Hd := deriv_bound_on_cell slot_u slot_v prec ms base len binds
                    du dv slot_v n _ _ Mu t Hin_t Hv_chk).
    rewrite (cell_env_v slot_u slot_v Huv) in Hd.
    exact Hd. }
  assert (Hcv : (lo_v <= (IZR (nth slot_v ms 0%Z)) <= hi_v)%R).
  { unfold lo_v, hi_v. rewrite minus_IZR, plus_IZR.
    generalize (IZR_le 0 dv Hdv). lra. }
  destruct (bound_between_dist Fv n (n + len)%nat Dv lo_v hi_v (IZR (nth slot_v ms 0%Z)) Mv
              Hdv_n Hbnd_v Hcv HinV) as [wa [wb [Hwa [Hwb Hleg2]]]].
  assert (Hval : forall t, eget n (Fv t) Xnan
                   = eget n (xextend (cell_env slot_u slot_v ms Mu t) binds)
                       Xnan).
  { intros t. unfold Fv. rewrite (cell_env_v slot_u slot_v Huv).
    apply (values_with_derivs slot_v base len binds _ _ base Hwf);
      try lia; try (intros k _; reflexivity). }
  rewrite Hval in Hwa, Hwb.
  
  rewrite (cell_env_at_v_centre slot_u slot_v Huv ms base Mu Hms Hbv) in Hwa.
  rewrite Hw1 in Hwa. injection Hwa as <-.
  exists wb. split. exact Hwb.
  (* the centre, the Taylor leg, and the mean-value leg *)
  assert (HDv : (0 <= Dv)%R).
  { destruct (Hbnd_v (IZR (nth slot_v ms 0%Z)) Hcv) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  assert (Hhalf_v : (Rabs (Mv - (IZR (nth slot_v ms 0%Z))) <= IZR dv)%R).
  {  destruct HinV as [Hl2 Hr2].
    unfold lo_v in Hl2. unfold hi_v in Hr2.
    rewrite minus_IZR in Hl2. rewrite plus_IZR in Hr2. apply Rabs_le. lra. }
  assert (Hleg2' : (Rabs (wb - w1) <= Dv * IZR dv)%R).
  { apply Rle_trans with (Dv * Rabs (Mv - (IZR (nth slot_v ms 0%Z))))%R. exact Hleg2.
    now apply Rmult_le_compat_l. }
  apply Rle_trans with
    (Rabs w0
     + (IZR du * (IZR (tb_Nu tb) * powerRZ 2%R (tb_qu tb))
        + IZR (tb_Nuu tb) * powerRZ 2%R (tb_quu tb) * IZR du * IZR du)
     + Dv * IZR dv)%R.
  - replace wb with (w0 + (w1 - w0) + (wb - w1))%R by ring.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [| exact Hleg2'].
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [apply Rle_refl | exact Hleg1].
  - unfold Dv. rewrite (Rmult_comm (IZR (tb_Nv tb) * powerRZ 2 (tb_qv tb))).
    lra.
Qed.

(** So a passing certificate bounds every component at every point of every
    cell it carries. *)
Theorem check_ccert_t_correct :
  forall c cl,
  check_ccert_t slot_u slot_v c = true ->
  In cl (tc_cells c) ->
  component_t_sound slot_u slot_v (pt_ms (tc_pt cl))
    (r_binds (residual (pt_es (tc_pt cl)) (tc_cfg c) (tc_modes c)))
    (tc_du cl) (tc_dv cl)
    (r_s (residual (pt_es (tc_pt cl)) (tc_cfg c) (tc_modes c))) (tc_s cl)
  /\ component_t_sound slot_u slot_v (pt_ms (tc_pt cl))
       (r_binds (residual (pt_es (tc_pt cl)) (tc_cfg c) (tc_modes c)))
       (tc_du cl) (tc_dv cl)
       (r_u (residual (pt_es (tc_pt cl)) (tc_cfg c) (tc_modes c))) (tc_u cl)
  /\ component_t_sound slot_u slot_v (pt_ms (tc_pt cl))
       (r_binds (residual (pt_es (tc_pt cl)) (tc_cfg c) (tc_modes c)))
       (tc_du cl) (tc_dv cl)
       (r_v (residual (pt_es (tc_pt cl)) (tc_cfg c) (tc_modes c))) (tc_v cl).
Proof.
  intros c cl Hc Hin.
  assert (Hcell : check_cell_t slot_u slot_v c cl = true).
  { unfold check_ccert_t in Hc. rewrite forallb_forall in Hc. now apply Hc. }
  unfold check_cell_t in Hcell.
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hv].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hu].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hs].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hwf].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdv].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdu].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hlen0].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hbv].
  apply andb_prop in Hcell. destruct Hcell as [Hms Hbu].
  apply Nat.eqb_eq in Hms.
  apply Nat.ltb_lt in Hbu. apply Nat.ltb_lt in Hbv.
  apply Nat.ltb_lt in Hlen0.
  apply Z.leb_le in Hdu. apply Z.leb_le in Hdv.
  repeat split;
    apply (component_t_correct (tprec_of c) _ (n_inputs_t c) _ _
             (tc_du cl) (tc_dv cl) _ _ Hms Hbu Hbv Hlen0 Hdu Hdv Hwf eq_refl);
    assumption.
Qed.

End TaylorCell.
