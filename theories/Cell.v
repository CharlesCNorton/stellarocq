(** Continuum certificates: the residual over a cell of angles.

    A cell certificate point carries, besides its center, half-widths of
    the two angle slots (in units of the slot mantissa) and bounds on the
    derivatives of each residual component with respect to those mantissas
    over the whole cell. [check_ccert] verifies the center bound, the
    derivative bounds by interval evaluation of the derivative bindings of
    Deriv.v on the box, and the mean-value combination
    eps_center + du * Du + dv * Dv <= eps_cell.

    [check_ccert_correct] states that a true verdict bounds each residual
    component at every real point of the cell, not only at its center: the
    component is a real number there and its absolute value is below
    eps_cell. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cover.

Import ListNotations.

Open Scope Z_scope.

(* ---------------------------------------------------------------- *)
(* Environments that agree on the slots an expression reads          *)

(** Two environments equal on every slot below n give an expression over
    those slots the same value. *)
Lemma xeval_agree :
  forall n e env1 env2,
  vars_below n e = true ->
  (forall k, (k < n)%nat -> eget k env1 Xnan = eget k env2 Xnan) ->
  xeval env1 e = xeval env2 e.
Proof.
  intros n e env1 env2 Hb Hagree.
  induction e; simpl in *;
    try (apply andb_prop in Hb; destruct Hb as [H1 H2]);
    try (rewrite IHe by assumption);
    try (rewrite IHe1 by assumption);
    try (rewrite IHe2 by assumption);
    try reflexivity.
  apply Hagree. now apply Nat.ltb_lt.
Qed.

(** One binding of the doubled list, exposed. *)
Lemma with_derivs_cons :
  forall x base delta n e tl,
  with_derivs x base delta ((n, e) :: tl)
  = (n, e) :: ((n + delta)%nat, deriv (dvar_of x base delta) e)
    :: with_derivs x base delta tl.
Proof. reflexivity. Qed.

(** One step of the fold that evaluates a binding list. *)
Lemma xextend_cons :
  forall env b bs,
  xextend env (b :: bs)
  = xextend (eset (fst b) env (xeval env (snd b))) bs.
Proof. reflexivity. Qed.

(** The value slots after the derivative-doubled bindings are those after
    the plain bindings. *)
Lemma values_with_derivs :
  forall x base delta bs env1 env2 next,
  well_formed next bs = true ->
  (base <= next)%nat ->
  (next + length bs <= base + delta)%nat ->
  (forall k, (k < base + delta)%nat -> eget k env1 Xnan = eget k env2 Xnan) ->
  forall k, (k < base + delta)%nat ->
  eget k (xextend env1 (with_derivs x base delta bs)) Xnan =
  eget k (xextend env2 bs) Xnan.
Proof.
  intros x base delta bs.
  induction bs as [|[n e] tl IH]; intros env1 env2 next Hwf Hbn Hlen Hagree k Hk.
  - simpl. now apply Hagree.
  - simpl in Hwf.
    apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He].
    apply Nat.eqb_eq in Hn.
    simpl length in Hlen.
    rewrite with_derivs_cons, !xextend_cons.
    cbn [fst snd].
    apply (IH _ _ (S next) Htl); try lia.
    intros j Hj.
    (* the derivative slot sits at n + delta, above every slot k asks about *)
    rewrite eget_eset_neq by lia.
    destruct (Nat.eq_dec j n) as [->|Hjn].
    + rewrite !eget_eset_eq.
      apply (xeval_agree n e env1 env2 He).
      intros i Hi. apply Hagree. lia.
    + rewrite !eget_eset_neq by exact Hjn.
      apply Hagree. lia.
Qed.

(** One binding of the tripled list, exposed. *)
Lemma with_derivs2_cons :
  forall x base delta n e tl,
  with_derivs2 x base delta ((n, e) :: tl)
  = (n, e)
    :: ((n + delta)%nat, deriv (dvar_of x base delta) e)
    :: ((n + 2 * delta)%nat,
        deriv (dvar_of x base delta) (deriv (dvar_of x base delta) e))
    :: with_derivs2 x base delta tl.
Proof. reflexivity. Qed.

(** The value slots after the bindings tripled with two derivative levels are
    those after the plain bindings, for the same reason as with one level: the
    derivative slots sit at and above base + delta, which is past every slot
    the values occupy. *)
Lemma values_with_derivs2 :
  forall x base delta bs env1 env2 next,
  well_formed next bs = true ->
  (base <= next)%nat ->
  (next + length bs <= base + delta)%nat ->
  (forall k, (k < base + delta)%nat -> eget k env1 Xnan = eget k env2 Xnan) ->
  forall k, (k < base + delta)%nat ->
  eget k (xextend env1 (with_derivs2 x base delta bs)) Xnan =
  eget k (xextend env2 bs) Xnan.
Proof.
  intros x base delta bs.
  induction bs as [|[n e] tl IH]; intros env1 env2 next Hwf Hbn Hlen Hagree k Hk.
  - simpl. now apply Hagree.
  - simpl in Hwf.
    apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hn He].
    apply Nat.eqb_eq in Hn.
    simpl length in Hlen.
    rewrite with_derivs2_cons, !xextend_cons.
    cbn [fst snd].
    apply (IH _ _ (S next) Htl); try lia.
    intros j Hj.
    (* both derivative slots sit at or above base + delta *)
    rewrite eget_eset_neq by lia.
    rewrite eget_eset_neq by lia.
    destruct (Nat.eq_dec j n) as [->|Hjn].
    + rewrite !eget_eset_eq.
      apply (xeval_agree n e env1 env2 He).
      intros i Hi. apply Hagree. lia.
    + rewrite !eget_eset_neq by exact Hjn.
      apply Hagree. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* Summing per-cell enclosures                                       *)

(** [tiling_encloses] adds the per-cell midpoint rules with [rsum], and the
    driver adds them with a loop over interval arithmetic. The two agreed by
    inspection. This is the sum itself, so the correspondence is a call
    rather than a reading: the driver hands over the list of per-cell
    contributions and gets back what the theorem sums.

    The order is the list's, and interval addition is not associative under
    rounding, so this fixes which sum is meant rather than leaving it to how
    a loop happens to accumulate. *)
Fixpoint isum (prec : F.precision) (l : list I.type) : I.type :=
  match l with
  | [] => I.zero
  | x :: tl => I.add prec x (isum prec tl)
  end.

(** Summing a list of enclosures encloses the sum of anything they enclose. *)
Lemma isum_correct :
  forall prec l (vs : list R),
  length l = length vs ->
  (forall k, (k < length l)%nat ->
     contains (I.convert (nth k l I.nai)) (Xreal (nth k vs 0%R))) ->
  contains (I.convert (isum prec l))
           (Xreal (fold_right Rplus 0%R vs)).
Proof.
  induction l as [|x tl IH]; intros vs Hlen Hc.
  - (* the empty sum is exactly zero, which the zero interval contains *)
    destruct vs; [|discriminate]. simpl. lra.
  - destruct vs as [|v vs]; [discriminate|].
    simpl. change (Xreal (v + fold_right Rplus 0%R vs))
             with (Xadd (Xreal v) (Xreal (fold_right Rplus 0%R vs))).
    apply I.add_correct.
    + exact (Hc 0%nat ltac:(simpl; lia)).
    + apply IH. now injection Hlen.
      intros k Hk. exact (Hc (S k) ltac:(simpl; lia)).
Qed.

(* ---------------------------------------------------------------- *)
(* Interval boxes                                                    *)

(** An interval containing two reals contains every real between them. *)
Lemma contains_between :
  forall xi a b x,
  contains (I.convert xi) (Xreal a) ->
  contains (I.convert xi) (Xreal b) ->
  (a <= x <= b)%R ->
  contains (I.convert xi) (Xreal x).
Proof.
  intros xi a b x Ha Hb [Hax Hxb].
  unfold contains in *.
  destruct (I.convert xi) as [|l u]. exact I.
  destruct Ha as [Hla Hau]. destruct Hb as [Hlb Hbu].
  split.
  - destruct l as [|l]. exact I. lra.
  - destruct u as [|u]. exact I. lra.
Qed.

(** The interval of the mantissas m - d .. m + d. *)
Definition slot_box (prec : F.precision) (m d : Z) : I.type :=
  I.join (I.fromZ prec (m - d)) (I.fromZ prec (m + d)).

(** It contains every real between its integer endpoints. *)
Lemma slot_box_correct :
  forall prec m d v,
  (IZR (m - d) <= v <= IZR (m + d))%R ->
  contains (I.convert (slot_box prec m d)) (Xreal v).
Proof.
  intros prec m d v Hv.
  apply (contains_between _ (IZR (m - d)) (IZR (m + d))).
  - apply I.join_correct. left. apply I.fromZ_correct.
  - apply I.join_correct. right. apply I.fromZ_correct.
  - exact Hv.
Qed.

(* ---------------------------------------------------------------- *)
(* A bound on a derivative bounds the increment                      *)

(** If along t the slot n has the slot nd for derivative, and that
    derivative is real and bounded by D on [a, b], then slot n is real at a
    and b and moves by at most D (b - a) between them. *)
Lemma bound_along :
  forall (F : R -> env ExtendedR) n nd D a b,
  (forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan)) ->
  (forall t, (a <= t <= b)%R ->
     exists d, eget nd (F t) Xnan = Xreal d /\ (Rabs d <= D)%R) ->
  (a <= b)%R ->
  exists wa wb,
    eget n (F a) Xnan = Xreal wa /\
    eget n (F b) Xnan = Xreal wb /\
    (Rabs (wb - wa) <= D * (b - a))%R.
Proof.
  intros F n nd D a b Hder Hbnd Hab.
  (* the slot is real wherever its derivative is real *)
  assert (Hreal : forall s, (a <= s <= b)%R ->
            exists w, eget n (F s) Xnan = Xreal w).
  { intros s Hs.
    destruct (Hbnd s Hs) as [d [Hd _]].
    specialize (Hder s). rewrite Hd in Hder.
    unfold Xderive_pt in Hder. unfold slot_along in Hder.
    destruct (eget n (F s) Xnan) as [|w]. contradiction. now exists w. }
  destruct (Hreal a) as [wa Hwa]. lra.
  destruct (Hreal b) as [wb Hwb]. lra.
  exists wa, wb. split. exact Hwa. split. exact Hwb.
  set (phi := proj_fun 0 (slot_along F n)).
  set (phi' := fun s => proj_val (eget nd (F s) Xnan)).
  assert (Hphi : forall s w', eget n (F s) Xnan = Xreal w' -> phi s = w').
  { intros s w' Hw'. unfold phi, proj_fun, slot_along. now rewrite Hw'. }
  assert (Hdl : forall s, (a <= s <= b)%R -> derivable_pt_lim phi s (phi' s)).
  { intros s Hs.
    destruct (Hbnd s Hs) as [d [Hd _]].
    specialize (Hder s). rewrite Hd in Hder.
    unfold Xderive_pt in Hder. unfold slot_along in Hder at 1.
    destruct (eget n (F s) Xnan) eqn:Hns. contradiction.
    unfold phi', phi. rewrite Hd. simpl. apply Hder. }
  assert (HD : (0 <= D)%R).
  { destruct (Hbnd a ltac:(lra)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt|Heq].
  - destruct (MVT_cor2 phi phi' a b Hlt) as [c [Hc Hac]].
    { intros s Hs. apply Hdl. lra. }
    rewrite (Hphi b wb Hwb), (Hphi a wa Hwa) in Hc.
    destruct (Hbnd c ltac:(lra)) as [d [Hd Hdb]].
    assert (Hpc : phi' c = d). { unfold phi'. now rewrite Hd. }
    rewrite Hpc in Hc.
    rewrite Hc.
    rewrite Rabs_mult.
    apply Rle_trans with (D * Rabs (b - a))%R.
    + apply Rmult_le_compat_r. apply Rabs_pos. exact Hdb.
    + apply Rmult_le_compat_l. exact HD.
      rewrite Rabs_right by lra. lra.
  - subst b. rewrite Hwb in Hwa. injection Hwa as <-.
    replace (wb - wb)%R with 0%R by ring. rewrite Rabs_R0.
    replace (a - a)%R with 0%R by ring. lra.
Qed.

(** The increment between two points of an interval on which the
    derivative is bounded, in either order. *)
Lemma bound_between :
  forall (F : R -> env ExtendedR) n nd D lo hi t0 t1,
  (forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan)) ->
  (forall t, (lo <= t <= hi)%R ->
     exists d, eget nd (F t) Xnan = Xreal d /\ (Rabs d <= D)%R) ->
  (lo <= t0 <= hi)%R -> (lo <= t1 <= hi)%R ->
  exists w0 w1,
    eget n (F t0) Xnan = Xreal w0 /\
    eget n (F t1) Xnan = Xreal w1 /\
    (Rabs (w1 - w0) <= D * (hi - lo))%R.
Proof.
  intros F n nd D lo hi t0 t1 Hder Hbnd Ht0 Ht1.
  assert (HD : (0 <= D)%R).
  { destruct (Hbnd t0 Ht0) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  destruct (Rle_or_lt t0 t1) as [Hle|Hlt].
  - destruct (bound_along F n nd D t0 t1 Hder) as [w0 [w1 [H0 [H1 Hinc]]]].
    + intros t Ht. apply Hbnd. lra.
    + exact Hle.
    + exists w0, w1. split. exact H0. split. exact H1.
      apply Rle_trans with (D * (t1 - t0))%R. exact Hinc.
      apply Rmult_le_compat_l. exact HD. lra.
  - destruct (bound_along F n nd D t1 t0 Hder) as [w1 [w0 [H1 [H0 Hinc]]]].
    + intros t Ht. apply Hbnd. lra.
    + lra.
    + exists w0, w1. split. exact H0. split. exact H1.
      rewrite Rabs_minus_sym.
      apply Rle_trans with (D * (t0 - t1))%R. exact Hinc.
      apply Rmult_le_compat_l. exact HD. lra.
Qed.

(** The same, charged against the distance actually travelled rather than
    the width of the interval the derivative is bounded on. The cell
    certificate walks from the centre, so it pays a half-width per angle,
    which is what the combination check adds up. *)
Lemma bound_between_dist :
  forall (F : R -> env ExtendedR) n nd D lo hi t0 t1,
  (forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan)) ->
  (forall t, (lo <= t <= hi)%R ->
     exists d, eget nd (F t) Xnan = Xreal d /\ (Rabs d <= D)%R) ->
  (lo <= t0 <= hi)%R -> (lo <= t1 <= hi)%R ->
  exists w0 w1,
    eget n (F t0) Xnan = Xreal w0 /\
    eget n (F t1) Xnan = Xreal w1 /\
    (Rabs (w1 - w0) <= D * Rabs (t1 - t0))%R.
Proof.
  intros F n nd D lo hi t0 t1 Hder Hbnd Ht0 Ht1.
  destruct (Rle_or_lt t0 t1) as [Hle|Hlt].
  - destruct (bound_along F n nd D t0 t1 Hder) as [w0 [w1 [H0 [H1 Hinc]]]].
    + intros t Ht. apply Hbnd. lra.
    + exact Hle.
    + exists w0, w1. split. exact H0. split. exact H1.
      rewrite (Rabs_right (t1 - t0)) by lra. exact Hinc.
  - destruct (bound_along F n nd D t1 t0 Hder) as [w1 [w0 [H1 [H0 Hinc]]]].
    + intros t Ht. apply Hbnd. lra.
    + lra.
    + exists w0, w1. split. exact H0. split. exact H1.
      rewrite Rabs_minus_sym.
      rewrite (Rabs_left (t1 - t0)) by lra.
      replace (- (t1 - t0))%R with (t0 - t1)%R by ring.
      exact Hinc.
Qed.

(* ---------------------------------------------------------------- *)
(* Cell certificates                                                 *)

(** The two varied slots. They are the poloidal and toroidal angle of a
    cell certificate, but nothing below depends on that: any two distinct
    input slots do, so a cell can range over a coefficient as readily as
    over an angle. *)
(* ---------------------------------------------------------------- *)
(* A cell bound charged against the derivative at the centre         *)

(** The mean-value bound charges each step against the derivative enclosed
    over the whole box. That enclosure does not see the cancellation the
    residual lives on, so it exceeds the derivative at the centre by a factor
    that only comes down as the cell narrows: measured on solovev it is five
    at the resolution a covering runs at.

    Taylor charges the step against the derivative at the centre, which is a
    thin evaluation with no box in it, and charges the box only for a second
    derivative multiplying the square of the half-width. [with_derivs2]
    already arranges value, first and second derivative into slots n, n + len
    and n + 2 len, and [inv2_bindings] already proves they hold what their
    names say.

    These are stated with every argument explicit rather than in a section, so
    that what each one needs is on its face. *)

(** The environment along the varied slot, carrying two derivative levels. *)
Definition F2 (base len : nat) (binds : list binding) (x : nat)
    (env0 : env ExtendedR) (t : R) : env ExtendedR :=
  xextend (eset x env0 (Xreal t)) (with_derivs2 x base len binds).

Lemma inv2_of :
  forall base len binds x env0,
  (x < base)%nat -> (0 < len)%nat ->
  well_formed base binds = true -> len = length binds ->
  (forall k, (base <= k)%nat -> eget k env0 Xnan = Xnan) ->
  (forall k, (k < base)%nat -> exists v, eget k env0 Xnan = Xreal v) ->
  inv2 x base len (F2 base len binds x env0) (base + len).
Proof.
  intros base len binds x env0 Hxb Hlen0 Hwf Hlen Hunset Hreal.
  assert (Hbase := inv2_base x base len Hxb Hlen0 _ Hunset Hreal).
  assert (Hres := inv2_bindings x base len Hxb Hlen0
                    binds _ base Hbase Hwf ltac:(lia) ltac:(lia)).
  rewrite <- Hlen in Hres.
  refine (inv2_ext x base len _ (F2 base len binds x env0) (base + len) _ Hres).
  intros t. unfold F2. reflexivity.
Qed.

(** A scratch slot's first and second derivatives are the slots one and two
    offsets above it. *)
Lemma deriv2_slots :
  forall base len binds x env0 n,
  (x < base)%nat -> (base <= n)%nat ->
  inv2 x base len (F2 base len binds x env0) (base + len) ->
  (forall t, Xderive_pt (slot_along (F2 base len binds x env0) n) (Xreal t)
               (eget (n + len)%nat (F2 base len binds x env0 t) Xnan))
  /\ (forall t, Xderive_pt
                 (slot_along (F2 base len binds x env0) (n + len)%nat) (Xreal t)
                 (eget (n + 2 * len)%nat (F2 base len binds x env0 t) Xnan)).
Proof.
  intros base len binds x env0 n Hxb Hn [Ha _].
  split; intros t.
  - specialize (Ha n t). unfold dvar_of in Ha.
    replace (Nat.eqb n x) with false in Ha
      by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.ltb n base) with false in Ha
      by (symmetry; apply Nat.ltb_ge; lia).
    exact Ha.
  - specialize (Ha (n + len)%nat t). unfold dvar_of in Ha.
    replace (Nat.eqb (n + len)%nat x) with false in Ha
      by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.ltb (n + len)%nat base) with false in Ha
      by (symmetry; apply Nat.ltb_ge; lia).
    replace (n + len + len)%nat with (n + 2 * len)%nat in Ha by lia.
    exact Ha.
Qed.

Section VariedSlots.

Variable slot_u slot_v : nat.
Hypothesis Huv : slot_u <> slot_v.

(** Per component: the center bound, the two derivative bounds over the
    cell (derivatives with respect to the angle mantissas), and the claimed
    bound over the cell, each N * 2^q. *)
Record cbounds := CBounds {
  cb_N0 : Z ; cb_q0 : Z ;
  cb_NDu : Z ; cb_qDu : Z ;
  cb_NDv : Z ; cb_qDv : Z ;
  cb_Nc : Z ; cb_qc : Z }.

(** One cell: a point, half-widths of the angle mantissas, and the bounds
    of the three components. *)
Record ccell := CCell {
  cc_pt : cpoint ;
  cc_du : Z ; cc_dv : Z ;
  cc_s : cbounds ; cc_u : cbounds ; cc_v : cbounds }.

(** A cell certificate. *)
Record ccert := CCert {
  cc_prec : Z ;
  cc_cfg : pconfig ;
  cc_modes : list (Z * Z) ;
  cc_cells : list ccell }.

(** Working precision of a cell certificate. *)
Definition cprec_of (c : ccert) : F.precision :=
  F.PtoP (Z.to_pos (cc_prec c)).

(** The number of input slots. *)
Definition n_inputs (c : ccert) : nat :=
  base_scratch_of (pc_lasym (cc_cfg c)) (pc_out (cc_cfg c))
    (length (cc_modes c)).

(** The box interval environment of a cell. *)
Definition box_ienv (prec : F.precision) (ms : list Z) (du dv : Z)
    : env I.type :=
  eset slot_u (eset slot_v (ienv_of prec ms) (slot_box prec (nth slot_v ms 0) dv)) (slot_box prec (nth slot_u ms 0) du).

(** The real environment of a point of the cell, with angle mantissas
    Mu and Mv. *)
Definition cell_env (ms : list Z) (Mu Mv : R) : env ExtendedR :=
  eset slot_u (eset slot_v (xenv_of ms) (Xreal Mv)) (Xreal Mu).

(** Membership of the angle mantissas in the cell. *)
Definition in_cell (ms : list Z) (du dv : Z) (Mu Mv : R) : Prop :=
  (IZR (nth slot_u ms 0%Z - du) <= Mu <= IZR (nth slot_u ms 0%Z + du))%R /\
  (IZR (nth slot_v ms 0%Z - dv) <= Mv <= IZR (nth slot_v ms 0%Z + dv))%R.

(** The box contains every point of the cell. *)
Lemma box_env_ok :
  forall prec ms du dv Mu Mv,
  in_cell ms du dv Mu Mv ->
  env_ok (box_ienv prec ms du dv) (cell_env ms Mu Mv).
Proof.
  intros prec ms du dv Mu Mv [Hu Hv].
  unfold box_ienv, cell_env.
  apply env_ok_eset.
  - apply env_ok_eset.
    + apply env_ok_fromZ.
    + now apply slot_box_correct.
  - now apply slot_box_correct.
Qed.

(** The slot of a residual component, when it is a slot reference. *)
Definition slot_of (e : expr) : option nat :=
  match e with
  | Evar n => Some n
  | _ => None
  end.

(** The mean-value combination eps_center + du Du + dv Dv <= eps_cell as
    an expression to test for nonnegativity. *)
Definition combination_e (du dv : Z) (cb : cbounds) : expr :=
  Esub (eps_e (cb_Nc cb) (cb_qc cb))
       (Eadd (eps_e (cb_N0 cb) (cb_q0 cb))
             (Eadd (Emul (EfromZ du) (eps_e (cb_NDu cb) (cb_qDu cb)))
                   (Emul (EfromZ dv) (eps_e (cb_NDv cb) (cb_qDv cb))))).

(** The checks of one component over the cell, against the environment at
    the centre and the two derivative environments over the box. The three
    do not depend on the component, so the caller builds them once. *)
Definition check_component (prec : F.precision)
    (base len : nat) (du dv : Z)
    (env0 envu envv : env I.type) (r : expr) (cb : cbounds) : bool :=
  match slot_of r with
  | None => false
  | Some n =>
      Nat.leb base n && Nat.ltb n (base + len) &&
      check1 prec env0 r (cb_N0 cb) (cb_q0 cb) &&
      check1 prec envu (Evar (n + len)) (cb_NDu cb) (cb_qDu cb) &&
      check1 prec envv (Evar (n + len)) (cb_NDv cb) (cb_qDv cb) &&
      nonneg (ieval prec eempty (combination_e du dv cb))
  end.

(* ---------------------------------------------------------------- *)
(* A cell of no width in the second angle                            *)

(** The checks of one component over a cell whose second angle has no width.
    The mean-value step there covers no distance, so no bound on that
    derivative is needed and its environment is never built. A covering of a
    three-dimensional equilibrium by curves is of this kind. *)
Definition check_component_flat (prec : F.precision)
    (base len : nat) (du : Z)
    (env0 envu : env I.type) (r : expr) (cb : cbounds) : bool :=
  match slot_of r with
  | None => false
  | Some n =>
      Nat.leb base n && Nat.ltb n (base + len) &&
      check1 prec env0 r (cb_N0 cb) (cb_q0 cb) &&
      check1 prec envu (Evar (n + len)) (cb_NDu cb) (cb_qDu cb) &&
      nonneg (ieval prec eempty (combination_e du 0 cb))
  end.

(** The checks of one cell. *)
Definition check_cell (c : ccert) (cl : ccell) : bool :=
  let prec := cprec_of c in
  let ms := pt_ms (cc_pt cl) in
  let es := pt_es (cc_pt cl) in
  let base := n_inputs c in
  let r3 := residual es (cc_cfg c) (cc_modes c) in
  let binds := r_binds r3 in
  let len := length binds in
  let box := box_ienv prec ms (cc_du cl) (cc_dv cl) in
  let env0 := iextend prec (ienv_of prec ms) binds in
  let envu := iextend prec box (with_derivs slot_u base len binds) in
  Nat.eqb (length ms) base &&
  Nat.ltb slot_u base && Nat.ltb slot_v base &&
  Nat.ltb 0 len &&
  Z.leb 0 (cc_du cl) && Z.leb 0 (cc_dv cl) &&
  well_formed base binds &&
  (if Z.eqb (cc_dv cl) 0 then
     check_component_flat prec base len (cc_du cl) env0 envu
                          (r_s r3) (cc_s cl) &&
     check_component_flat prec base len (cc_du cl) env0 envu
                          (r_u r3) (cc_u cl) &&
     check_component_flat prec base len (cc_du cl) env0 envu
                          (r_v r3) (cc_v cl)
   else
     let envv := iextend prec box (with_derivs slot_v base len binds) in
     check_component prec base len (cc_du cl) (cc_dv cl) env0 envu envv
                     (r_s r3) (cc_s cl) &&
     check_component prec base len (cc_du cl) (cc_dv cl) env0 envu envv
                     (r_u r3) (cc_u cl) &&
     check_component prec base len (cc_du cl) (cc_dv cl) env0 envu envv
                     (r_v r3) (cc_v cl)).

(** Check every cell of a certificate. *)
Definition check_ccert (c : ccert) : bool :=
  forallb (check_cell c) (cc_cells c).

(* ---------------------------------------------------------------- *)
(* Soundness of one component over its cell                          *)

(** What a passing component check means: at every point of the cell the
    component is a real number bounded by the cell bound. *)
Definition component_sound (ms : list Z) (binds : list binding)
    (du dv : Z) (r : expr) (cb : cbounds) : Prop :=
  forall Mu Mv, in_cell ms du dv Mu Mv ->
  exists w,
    xeval (xextend (cell_env ms Mu Mv) binds) r = Xreal w /\
    (Rabs w <= IZR (cb_Nc cb) * powerRZ 2%R (cb_qc cb))%R.

(** The empty environments are contained in each other. *)
Lemma env_ok_nil : env_ok (eempty : env I.type) (eempty : env ExtendedR).
Proof.
  intros n. rewrite !eget_eempty. apply I.T.J.nai_correct.
Qed.

(** A passing combination check is the real inequality it encodes. *)
Lemma combination_correct :
  forall prec du dv cb,
  nonneg (ieval prec eempty (combination_e du dv cb)) = true ->
  (IZR (cb_N0 cb) * powerRZ 2%R (cb_q0 cb)
   + IZR du * (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))
   + IZR dv * (IZR (cb_NDv cb) * powerRZ 2%R (cb_qDv cb))
   <= IZR (cb_Nc cb) * powerRZ 2%R (cb_qc cb))%R.
Proof.
  intros prec du dv cb Hchk.
  assert (Hc := ieval_correct prec eempty eempty (combination_e du dv cb) env_ok_nil).
  destruct (nonneg_correct _ _ Hc Hchk) as [d [Hd Hge]].
  unfold combination_e in Hd.
  change (xeval eempty (Esub (eps_e (cb_Nc cb) (cb_qc cb))
            (Eadd (eps_e (cb_N0 cb) (cb_q0 cb))
              (Eadd (Emul (EfromZ du) (eps_e (cb_NDu cb) (cb_qDu cb)))
                    (Emul (EfromZ dv) (eps_e (cb_NDv cb) (cb_qDv cb)))))))
    with (Xsub (xeval eempty (eps_e (cb_Nc cb) (cb_qc cb)))
            (Xadd (xeval eempty (eps_e (cb_N0 cb) (cb_q0 cb)))
              (Xadd (Xmul (Xreal (IZR du)) (xeval eempty (eps_e (cb_NDu cb) (cb_qDu cb))))
                    (Xmul (Xreal (IZR dv)) (xeval eempty (eps_e (cb_NDv cb) (cb_qDv cb)))))))
    in Hd.
  rewrite !xeval_eps_e in Hd.
  simpl in Hd.
  injection Hd as <-.
  lra.
Qed.

(** The derivative slot of a component, over the whole cell, is real and
    within its bound. *)
Lemma deriv_bound_on_cell :
  forall prec ms base len binds du dv x n N q Mu Mv,
  in_cell ms du dv Mu Mv ->
  check1 prec (iextend prec (box_ienv prec ms du dv)
                        (with_derivs x base len binds))
         (Evar (n + len)) N q = true ->
  exists d,
    eget (n + len) (xextend (cell_env ms Mu Mv) (with_derivs x base len binds)) Xnan = Xreal d /\
    (Rabs d <= IZR N * powerRZ 2%R q)%R.
Proof.
  intros prec ms base len binds du dv x n N q Mu Mv Hin Hchk.
  assert (Henv := iextend_correct prec (with_derivs x base len binds) _ _
                    (box_env_ok prec ms du dv Mu Mv Hin)).
  destruct (check1_correct _ _ _ _ _ _ Henv Hchk) as [d [Hd Hb]].
  exists d. split. exact Hd. exact Hb.
Qed.

(** The point environment with the u slot set last. *)
Lemma cell_env_v :
  forall ms Mu Mv,
  cell_env ms Mu Mv
  = eset slot_v (eset slot_u (xenv_of ms) (Xreal Mu)) (Xreal Mv).
Proof.
  intros ms Mu Mv. unfold cell_env. apply eset_comm. exact Huv.
Qed.

(** The mantissas as reals are the slots of xenv_of. *)
Lemma nth_xenv_of :
  forall ms k, (k < length ms)%nat -> eget k (xenv_of ms) Xnan = Xreal (IZR (nth k ms 0)).
Proof.
  intros ms k Hk.
  unfold xenv_of. rewrite eget_of_list.
  rewrite (nth_indep _ Xnan (Xreal (IZR 0))) by (rewrite length_map; lia).
  now rewrite (map_nth (fun z => Xreal (IZR z)) ms 0%Z k).
Qed.

(** Every input of a point is real, and nothing above them is set. *)
Lemma inputs_real :
  forall ms base Mu Mv,
  length ms = base -> (slot_u < base /\ slot_v < base)%nat ->
  (forall k, (base <= k)%nat -> eget k (cell_env ms Mu Mv) Xnan = Xnan) /\
  (forall k, (k < base)%nat ->
     exists v, eget k (cell_env ms Mu Mv) Xnan = Xreal v).
Proof.
  intros ms base Mu Mv Hlen Hb.
  unfold cell_env.
  split.
  - intros k Hk.
    rewrite eget_eset_neq by lia. rewrite eget_eset_neq by lia.
    unfold xenv_of. rewrite eget_of_list.
    apply nth_overflow. rewrite length_map. lia.
  - intros k Hk.
    destruct (Nat.eq_dec k slot_u) as [->|Hku].
    + rewrite eget_eset_eq. now exists Mu.
    + rewrite eget_eset_neq by exact Hku.
      destruct (Nat.eq_dec k slot_v) as [->|Hkv].
      * rewrite eget_eset_eq. now exists Mv.
      * rewrite eget_eset_neq by exact Hkv.
        rewrite nth_xenv_of by lia. now eexists.
Qed.

(** The center of the cell is the point itself. *)
Lemma cell_env_center :
  forall ms base,
  length ms = base -> (slot_u < base /\ slot_v < base)%nat ->
  cell_env ms (IZR (nth slot_u ms 0)) (IZR (nth slot_v ms 0)) = xenv_of ms.
Proof.
  intros ms base Hlen Hb.
  assert (Hentry : forall k, Xreal (IZR (nth k ms 0))
            = nth k (map (fun z => Xreal (IZR z)) ms) (Xreal (IZR 0))).
  { intros k. symmetry. apply (map_nth (fun z => Xreal (IZR z)) ms 0%Z k). }
  unfold cell_env, xenv_of.
  rewrite (Hentry slot_u), (Hentry slot_v).
  rewrite (eset_of_list_same _ _ slot_v (Xreal (IZR 0)))
    by (rewrite length_map; lia).
  rewrite (eset_of_list_same _ _ slot_u (Xreal (IZR 0)))
    by (rewrite length_map; lia).
  reflexivity.
Qed.

(** The derivative slot of a scratch slot n along the input slot x. *)
Lemma deriv_slot_of :
  forall x base delta F next n,
  (x < base)%nat -> (base <= n)%nat ->
  inv x base delta F next ->
  forall t, Xderive_pt (slot_along F n) (Xreal t) (eget (n + delta) (F t) Xnan).
Proof.
  intros x base delta F next n Hx Hn [Ha _] t.
  specialize (Ha n t).
  unfold dvar_of in Ha.
  replace (Nat.eqb n x) with false in Ha
    by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.ltb n base) with false in Ha
    by (symmetry; apply Nat.ltb_ge; lia).
  exact Ha.
Qed.

(** A passing component check bounds the component over the cell. *)
Lemma component_correct :
  forall prec ms base len binds du dv r cb,
  length ms = base -> (slot_u < base /\ slot_v < base)%nat -> (0 < len)%nat ->
  0 <= du -> 0 <= dv ->
  well_formed base binds = true -> len = length binds ->
  check_component prec base len du dv
    (iextend prec (ienv_of prec ms) binds)
    (iextend prec (box_ienv prec ms du dv) (with_derivs slot_u base len binds))
    (iextend prec (box_ienv prec ms du dv) (with_derivs slot_v base len binds))
    r cb = true ->
  component_sound ms binds du dv r cb.
Proof.
  intros prec ms base len binds du dv r cb Hms Hb Hlen0 Hdu Hdv Hwf Hlen Hchk.
  unfold check_component in Hchk.
  destruct r; simpl in Hchk; try discriminate.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcomb].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdv_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdu_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcenter].
  apply andb_prop in Hchk. destruct Hchk as [Hbn Hn].
  apply Nat.leb_le in Hbn. apply Nat.ltb_lt in Hn.
  assert (Hcombi := combination_correct prec du dv cb Hcomb).
  intros Mu Mv Hin.
  set (Mu0 := IZR (nth slot_u ms 0)).
  set (Mv0 := IZR (nth slot_v ms 0)).
  assert (HinU := proj1 Hin). assert (HinV := proj2 Hin).
  assert (Hin0 : in_cell ms du dv Mu0 Mv0).
  { unfold in_cell, Mu0, Mv0. rewrite !minus_IZR, !plus_IZR.
    generalize (IZR_le 0 du Hdu). generalize (IZR_le 0 dv Hdv). lra. }
  (* the center value *)
  assert (Henv0 := iextend_correct prec binds _ _ (env_ok_fromZ prec ms)).
  destruct (check1_correct _ _ _ _ _ _ Henv0 Hcenter) as [w0 [Hw0 Hb0]].
  simpl in Hw0.
  (* the u-line at v = Mv0 *)
  set (Fu := fun t => xextend (eset slot_u (eset slot_v (xenv_of ms) (Xreal Mv0)) (Xreal t))
                              (with_derivs slot_u base len binds)).
  assert (Hinv_u : inv slot_u base len Fu (base + len)).
  { destruct (inputs_real ms base Mu0 Mv0 Hms Hb) as [Hl Hr].
    unfold cell_env in Hl, Hr.
    assert (Hbase := inv_base slot_u base len ltac:(lia)
                       ltac:(lia) _ Hl Hr).
    assert (Hres := inv_bindings slot_u base len ltac:(lia)
                      ltac:(lia) binds _ base Hbase Hwf ltac:(lia)
                      ltac:(lia)).
    rewrite <- Hlen in Hres.
    (* inv_base varies the u slot on top of the centre point, which already
       set it; the outer write is the only one that survives *)
    refine (inv_ext slot_u base len _ Fu (base + len) _ Hres).
    intros t. unfold Fu. now rewrite eset_overwrite. }
  (* the v-line at u = Mu *)
  set (Fv := fun t => xextend (eset slot_v (eset slot_u (xenv_of ms) (Xreal Mu)) (Xreal t))
                              (with_derivs slot_v base len binds)).
  assert (Hinv_v : inv slot_v base len Fv (base + len)).
  { destruct (inputs_real ms base Mu Mv0 Hms Hb) as [Hl Hr].
    rewrite cell_env_v in Hl, Hr.
    assert (Hbase := inv_base slot_v base len ltac:(lia)
                       ltac:(lia) _ Hl Hr).
    assert (Hres := inv_bindings slot_v base len ltac:(lia)
                      ltac:(lia) binds _ base Hbase Hwf ltac:(lia)
                      ltac:(lia)).
    rewrite <- Hlen in Hres.
    refine (inv_ext slot_v base len _ Fv (base + len) _ Hres).
    intros t. unfold Fv. now rewrite eset_overwrite. }
  assert (Hdu_n := deriv_slot_of slot_u base len Fu (base + len) n
                     ltac:(lia) Hbn Hinv_u).
  assert (Hdv_n := deriv_slot_of slot_v base len Fv (base + len) n
                     ltac:(lia) Hbn Hinv_v).
  (* bounds on the derivative slots over the cell *)
  set (Du := (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))%R).
  set (Dv := (IZR (cb_NDv cb) * powerRZ 2%R (cb_qDv cb))%R).
  set (lo_u := IZR (nth slot_u ms 0 - du)).
  set (hi_u := IZR (nth slot_u ms 0 + du)).
  set (lo_v := IZR (nth slot_v ms 0 - dv)).
  set (hi_v := IZR (nth slot_v ms 0 + dv)).
  assert (Hbnd_u : forall t, (lo_u <= t <= hi_u)%R ->
            exists d, eget (n + len) (Fu t) Xnan = Xreal d /\ (Rabs d <= Du)%R).
  { intros t Ht.
    assert (Hin_t : in_cell ms du dv t Mv0). { split. exact Ht. exact (proj2 Hin0). }
    exact (deriv_bound_on_cell prec ms base len binds du dv slot_u n _ _ t Mv0
             Hin_t Hdu_chk). }
  assert (Hbnd_v : forall t, (lo_v <= t <= hi_v)%R ->
            exists d, eget (n + len) (Fv t) Xnan = Xreal d /\ (Rabs d <= Dv)%R).
  { intros t Ht.
    assert (Hin_t : in_cell ms du dv Mu t). { split. exact HinU. exact Ht. }
    assert (Hd := deriv_bound_on_cell prec ms base len binds du dv slot_v n _ _ Mu t
                    Hin_t Hdv_chk).
    rewrite cell_env_v in Hd. exact Hd. }
  (* along u from Mu0 to Mu, then along v from Mv0 to Mv *)
  destruct (bound_between_dist Fu n (n + len) Du lo_u hi_u Mu0 Mu Hdu_n Hbnd_u
              (proj1 Hin0) HinU) as [wu0 [wu1 [Hwu0 [Hwu1 Hinc_u]]]].
  destruct (bound_between_dist Fv n (n + len) Dv lo_v hi_v Mv0 Mv Hdv_n Hbnd_v
              (proj2 Hin0) HinV) as [wv0 [wv1 [Hwv0 [Hwv1 Hinc_v]]]].
  (* the value slots do not depend on the derivative bindings *)
  assert (Hval_u : forall t, eget n (Fu t) Xnan
                     = eget n (xextend (cell_env ms t Mv0) binds) Xnan).
  { intros t. unfold Fu, cell_env.
    apply (values_with_derivs slot_u base len binds _ _ base Hwf); try lia.
    intros k _. reflexivity. }
  assert (Hval_v : forall t, eget n (Fv t) Xnan
                     = eget n (xextend (cell_env ms Mu t) binds) Xnan).
  { intros t. unfold Fv. rewrite cell_env_v.
    apply (values_with_derivs slot_v base len binds _ _ base Hwf); try lia.
    intros k _. reflexivity. }
  rewrite Hval_u in Hwu0, Hwu1.
  rewrite Hval_v in Hwv0, Hwv1.
  unfold Mu0, Mv0 in Hwu0.
  rewrite (cell_env_center ms base Hms Hb) in Hwu0.
  rewrite Hw0 in Hwu0. injection Hwu0 as <-.
  rewrite Hwu1 in Hwv0. injection Hwv0 as <-.
  exists wv1. split. exact Hwv1.
  (* Each leg travels from the centre of the cell to a point of it, so it
     covers at most the half-width of that angle. *)
  assert (HDu : (0 <= Du)%R).
  { destruct (Hbnd_u Mu0 (proj1 Hin0)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  assert (HDv : (0 <= Dv)%R).
  { destruct (Hbnd_v Mv0 (proj2 Hin0)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  assert (Hhalf_u : (Rabs (Mu - Mu0) <= IZR du)%R).
  { unfold Mu0. destruct HinU as [Hl Hr].
    unfold lo_u in Hl. unfold hi_u in Hr.
    rewrite minus_IZR in Hl. rewrite plus_IZR in Hr.
    apply Rabs_le. lra. }
  assert (Hhalf_v : (Rabs (Mv - Mv0) <= IZR dv)%R).
  { unfold Mv0. destruct HinV as [Hl Hr].
    unfold lo_v in Hl. unfold hi_v in Hr.
    rewrite minus_IZR in Hl. rewrite plus_IZR in Hr.
    apply Rabs_le. lra. }
  assert (Hinc_u' : (Rabs (wu1 - w0) <= Du * IZR du)%R).
  { apply Rle_trans with (Du * Rabs (Mu - Mu0))%R. exact Hinc_u.
    now apply Rmult_le_compat_l. }
  assert (Hinc_v' : (Rabs (wv1 - wu1) <= Dv * IZR dv)%R).
  { apply Rle_trans with (Dv * Rabs (Mv - Mv0))%R. exact Hinc_v.
    now apply Rmult_le_compat_l. }
  (* |wv1| <= |w0| + |wu1 - w0| + |wv1 - wu1|, then the combination check *)
  apply Rle_trans with
    (Rabs w0 + Du * IZR du + Dv * IZR dv)%R.
  - replace wv1 with (w0 + (wu1 - w0) + (wv1 - wu1))%R by ring.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [| exact Hinc_v'].
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [apply Rle_refl | exact Hinc_u'].
  - unfold Du, Dv.
    apply Rle_trans with
      (IZR (cb_N0 cb) * powerRZ 2%R (cb_q0 cb)
       + IZR du * (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))
       + IZR dv * (IZR (cb_NDv cb) * powerRZ 2%R (cb_qDv cb)))%R.
    + repeat apply Rplus_le_compat; try (rewrite Rmult_comm; apply Rle_refl).
      exact Hb0.
    + exact Hcombi.
Qed.


(** It bounds the component over the cell just as the two-angle check does.
    With no width in the second angle the point is forced to the centre
    there, so the walk from the centre has one leg rather than two. *)
Lemma component_correct_flat :
  forall prec ms base len binds du r cb,
  length ms = base -> (slot_u < base /\ slot_v < base)%nat -> (0 < len)%nat ->
  0 <= du ->
  well_formed base binds = true -> len = length binds ->
  check_component_flat prec base len du
    (iextend prec (ienv_of prec ms) binds)
    (iextend prec (box_ienv prec ms du 0) (with_derivs slot_u base len binds))
    r cb = true ->
  component_sound ms binds du 0 r cb.
Proof.
  intros prec ms base len binds du r cb Hms Hb Hlen0 Hdu Hwf Hlen Hchk.
  unfold check_component_flat in Hchk.
  destruct r; simpl in Hchk; try discriminate.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcomb].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdu_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcenter].
  apply andb_prop in Hchk. destruct Hchk as [Hbn Hn].
  apply Nat.leb_le in Hbn. apply Nat.ltb_lt in Hn.
  assert (Hcombi := combination_correct prec du 0 cb Hcomb).
  intros Mu Mv Hin.
  set (Mu0 := IZR (nth slot_u ms 0)).
  set (Mv0 := IZR (nth slot_v ms 0)).
  assert (HinU := proj1 Hin).
  (* no width in the second angle leaves the point at the centre there *)
  assert (HMv : Mv = Mv0).
  { destruct Hin as [_ [Hl Hr]]. unfold Mv0.
    rewrite Z.sub_0_r in Hl. rewrite Z.add_0_r in Hr. lra. }
  assert (Hin0 : in_cell ms du 0 Mu0 Mv0).
  { unfold in_cell, Mu0, Mv0. rewrite !minus_IZR, !plus_IZR.
    generalize (IZR_le 0 du Hdu). simpl. lra. }
  assert (Henv0 := iextend_correct prec binds _ _ (env_ok_fromZ prec ms)).
  destruct (check1_correct _ _ _ _ _ _ Henv0 Hcenter) as [w0 [Hw0 Hb0]].
  simpl in Hw0.
  set (Fu := fun t => xextend (eset slot_u (eset slot_v (xenv_of ms) (Xreal Mv0)) (Xreal t))
                              (with_derivs slot_u base len binds)).
  assert (Hinv_u : inv slot_u base len Fu (base + len)).
  { destruct (inputs_real ms base Mu0 Mv0 Hms Hb) as [Hl Hr].
    unfold cell_env in Hl, Hr.
    assert (Hbase := inv_base slot_u base len ltac:(lia) ltac:(lia) _ Hl Hr).
    assert (Hres := inv_bindings slot_u base len ltac:(lia) ltac:(lia)
                      binds _ base Hbase Hwf ltac:(lia) ltac:(lia)).
    rewrite <- Hlen in Hres.
    refine (inv_ext slot_u base len _ Fu (base + len) _ Hres).
    intros t. unfold Fu. now rewrite eset_overwrite. }
  assert (Hdu_n := deriv_slot_of slot_u base len Fu (base + len) n
                     ltac:(lia) Hbn Hinv_u).
  set (Du := (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))%R).
  set (lo_u := IZR (nth slot_u ms 0 - du)).
  set (hi_u := IZR (nth slot_u ms 0 + du)).
  assert (Hbnd_u : forall t, (lo_u <= t <= hi_u)%R ->
            exists d, eget (n + len) (Fu t) Xnan = Xreal d /\ (Rabs d <= Du)%R).
  { intros t Ht.
    assert (Hin_t : in_cell ms du 0 t Mv0).
    { split. exact Ht. exact (proj2 Hin0). }
    exact (deriv_bound_on_cell prec ms base len binds du 0 slot_u n _ _ t Mv0
             Hin_t Hdu_chk). }
  destruct (bound_between_dist Fu n (n + len) Du lo_u hi_u Mu0 Mu Hdu_n Hbnd_u
              (proj1 Hin0) HinU) as [wu0 [wu1 [Hwu0 [Hwu1 Hinc_u]]]].
  assert (Hval_u : forall t, eget n (Fu t) Xnan
                     = eget n (xextend (cell_env ms t Mv0) binds) Xnan).
  { intros t. unfold Fu, cell_env.
    apply (values_with_derivs slot_u base len binds _ _ base Hwf); try lia.
    intros k _. reflexivity. }
  rewrite Hval_u in Hwu0, Hwu1.
  unfold Mu0, Mv0 in Hwu0.
  rewrite (cell_env_center ms base Hms Hb) in Hwu0.
  rewrite Hw0 in Hwu0. injection Hwu0 as <-.
  exists wu1. rewrite HMv. split. exact Hwu1.
  assert (HDu : (0 <= Du)%R).
  { destruct (Hbnd_u Mu0 (proj1 Hin0)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  assert (Hhalf_u : (Rabs (Mu - Mu0) <= IZR du)%R).
  { unfold Mu0. destruct HinU as [Hl Hr].
    unfold lo_u in Hl. unfold hi_u in Hr.
    rewrite minus_IZR in Hl. rewrite plus_IZR in Hr. apply Rabs_le. lra. }
  assert (Hinc_u' : (Rabs (wu1 - w0) <= Du * IZR du)%R).
  { apply Rle_trans with (Du * Rabs (Mu - Mu0))%R. exact Hinc_u.
    now apply Rmult_le_compat_l. }
  apply Rle_trans with (Rabs w0 + Du * IZR du)%R.
  - replace wu1 with (w0 + (wu1 - w0))%R by ring.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [apply Rle_refl | exact Hinc_u'].
  - unfold Du in *. rewrite (Rmult_comm (IZR (cb_NDu cb) * powerRZ 2 (cb_qDu cb))).
    simpl in Hcombi. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Soundness of a whole certificate                                  *)

(** A passing certificate bounds all three residual components at every
    real point of every cell it carries, not only at the cell centres. *)
Theorem check_ccert_correct :
  forall c cl,
  check_ccert c = true ->
  In cl (cc_cells c) ->
  component_sound (pt_ms (cc_pt cl))
    (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
    (cc_du cl) (cc_dv cl)
    (r_s (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))) (cc_s cl)
  /\ component_sound (pt_ms (cc_pt cl))
       (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
       (cc_du cl) (cc_dv cl)
       (r_u (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))) (cc_u cl)
  /\ component_sound (pt_ms (cc_pt cl))
       (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
       (cc_du cl) (cc_dv cl)
       (r_v (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))) (cc_v cl).
Proof.
  intros c cl Hc Hin.
  assert (Hcell : check_cell c cl = true).
  { unfold check_ccert in Hc. rewrite forallb_forall in Hc. now apply Hc. }
  unfold check_cell in Hcell.
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hcomp].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hwf].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdv].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdu].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hlen0].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hbv].
  apply andb_prop in Hcell. destruct Hcell as [Hms Hbu].
  apply Nat.eqb_eq in Hms.
  apply Nat.ltb_lt in Hbu. apply Nat.ltb_lt in Hbv.
  assert (Hb : (slot_u < n_inputs c /\ slot_v < n_inputs c)%nat)
    by (split; assumption).
  apply Nat.ltb_lt in Hlen0.
  apply Z.leb_le in Hdu. apply Z.leb_le in Hdv.
  destruct (Z.eqb (cc_dv cl) 0) eqn:Hz0.
  - apply Z.eqb_eq in Hz0.
    apply andb_prop in Hcomp. destruct Hcomp as [Hcomp Hv].
    apply andb_prop in Hcomp. destruct Hcomp as [Hs Hu].
    rewrite Hz0 in Hs, Hu, Hv |- *.
    repeat split;
      apply (component_correct_flat (cprec_of c) _ (n_inputs c) _ _
               (cc_du cl) _ _ Hms Hb Hlen0 Hdu Hwf eq_refl);
      assumption.
  - apply andb_prop in Hcomp. destruct Hcomp as [Hcomp Hv].
    apply andb_prop in Hcomp. destruct Hcomp as [Hs Hu].
    repeat split;
      apply (component_correct (cprec_of c) _ (n_inputs c) _ _
               (cc_du cl) (cc_dv cl) _ _ Hms Hb Hlen0 Hdu Hdv Hwf eq_refl);
      assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* The walk from the centre of a cell to one of its points           *)

(** From the two derivative checks alone: the component is a real number at
    the centre of the cell and at any point of it, and the two differ by at
    most the mean-value step in each angle. The upper cell bound and the
    lower one are this lemma followed by one inequality in opposite
    directions. *)
Lemma component_legs :
  forall prec ms base len binds du dv n Ndu qdu Ndv qdv Mu Mv,
  length ms = base -> (slot_u < base /\ slot_v < base)%nat -> (0 < len)%nat ->
  0 <= du -> 0 <= dv ->
  well_formed base binds = true -> len = length binds ->
  (base <= n)%nat -> (n < base + len)%nat ->
  check1 prec (iextend prec (box_ienv prec ms du dv)
                       (with_derivs slot_u base len binds))
         (Evar (n + len)) Ndu qdu = true ->
  check1 prec (iextend prec (box_ienv prec ms du dv)
                       (with_derivs slot_v base len binds))
         (Evar (n + len)) Ndv qdv = true ->
  in_cell ms du dv Mu Mv ->
  exists w0 w,
    eget n (xextend (xenv_of ms) binds) Xnan = Xreal w0 /\
    eget n (xextend (cell_env ms Mu Mv) binds) Xnan = Xreal w /\
    (Rabs (w - w0) <=
       IZR du * (IZR Ndu * powerRZ 2%R qdu)
     + IZR dv * (IZR Ndv * powerRZ 2%R qdv))%R.
Proof.
  intros prec ms base len binds du dv n Ndu qdu Ndv qdv Mu Mv
         Hms Hb Hlen0 Hdu Hdv Hwf Hlen Hbn Hn Hdu_chk Hdv_chk Hin.
  set (Mu0 := IZR (nth slot_u ms 0)).
  set (Mv0 := IZR (nth slot_v ms 0)).
  assert (HinU := proj1 Hin). assert (HinV := proj2 Hin).
  assert (Hin0 : in_cell ms du dv Mu0 Mv0).
  { unfold in_cell, Mu0, Mv0. rewrite !minus_IZR, !plus_IZR.
    generalize (IZR_le 0 du Hdu). generalize (IZR_le 0 dv Hdv). lra. }
  set (Fu := fun t => xextend (eset slot_u (eset slot_v (xenv_of ms) (Xreal Mv0)) (Xreal t))
                              (with_derivs slot_u base len binds)).
  assert (Hinv_u : inv slot_u base len Fu (base + len)).
  { destruct (inputs_real ms base Mu0 Mv0 Hms Hb) as [Hl Hr].
    unfold cell_env in Hl, Hr.
    assert (Hbase := inv_base slot_u base len ltac:(lia)
                       ltac:(lia) _ Hl Hr).
    assert (Hres := inv_bindings slot_u base len ltac:(lia)
                      ltac:(lia) binds _ base Hbase Hwf ltac:(lia) ltac:(lia)).
    rewrite <- Hlen in Hres.
    refine (inv_ext slot_u base len _ Fu (base + len) _ Hres).
    intros t. unfold Fu. now rewrite eset_overwrite. }
  set (Fv := fun t => xextend (eset slot_v (eset slot_u (xenv_of ms) (Xreal Mu)) (Xreal t))
                              (with_derivs slot_v base len binds)).
  assert (Hinv_v : inv slot_v base len Fv (base + len)).
  { destruct (inputs_real ms base Mu Mv0 Hms Hb) as [Hl Hr].
    rewrite cell_env_v in Hl, Hr.
    assert (Hbase := inv_base slot_v base len ltac:(lia)
                       ltac:(lia) _ Hl Hr).
    assert (Hres := inv_bindings slot_v base len ltac:(lia)
                      ltac:(lia) binds _ base Hbase Hwf ltac:(lia) ltac:(lia)).
    rewrite <- Hlen in Hres.
    refine (inv_ext slot_v base len _ Fv (base + len) _ Hres).
    intros t. unfold Fv. now rewrite eset_overwrite. }
  assert (Hdu_n := deriv_slot_of slot_u base len Fu (base + len) n
                     ltac:(lia) Hbn Hinv_u).
  assert (Hdv_n := deriv_slot_of slot_v base len Fv (base + len) n
                     ltac:(lia) Hbn Hinv_v).
  set (Du := (IZR Ndu * powerRZ 2%R qdu)%R).
  set (Dv := (IZR Ndv * powerRZ 2%R qdv)%R).
  set (lo_u := IZR (nth slot_u ms 0 - du)).
  set (hi_u := IZR (nth slot_u ms 0 + du)).
  set (lo_v := IZR (nth slot_v ms 0 - dv)).
  set (hi_v := IZR (nth slot_v ms 0 + dv)).
  assert (Hbnd_u : forall t, (lo_u <= t <= hi_u)%R ->
            exists d, eget (n + len) (Fu t) Xnan = Xreal d /\ (Rabs d <= Du)%R).
  { intros t Ht.
    assert (Hin_t : in_cell ms du dv t Mv0). { split. exact Ht. exact (proj2 Hin0). }
    exact (deriv_bound_on_cell prec ms base len binds du dv slot_u n _ _ t Mv0
             Hin_t Hdu_chk). }
  assert (Hbnd_v : forall t, (lo_v <= t <= hi_v)%R ->
            exists d, eget (n + len) (Fv t) Xnan = Xreal d /\ (Rabs d <= Dv)%R).
  { intros t Ht.
    assert (Hin_t : in_cell ms du dv Mu t). { split. exact HinU. exact Ht. }
    assert (Hd := deriv_bound_on_cell prec ms base len binds du dv slot_v n _ _ Mu t
                    Hin_t Hdv_chk).
    rewrite cell_env_v in Hd. exact Hd. }
  destruct (bound_between_dist Fu n (n + len) Du lo_u hi_u Mu0 Mu Hdu_n Hbnd_u
              (proj1 Hin0) HinU) as [wu0 [wu1 [Hwu0 [Hwu1 Hinc_u]]]].
  destruct (bound_between_dist Fv n (n + len) Dv lo_v hi_v Mv0 Mv Hdv_n Hbnd_v
              (proj2 Hin0) HinV) as [wv0 [wv1 [Hwv0 [Hwv1 Hinc_v]]]].
  assert (Hval_u : forall t, eget n (Fu t) Xnan
                     = eget n (xextend (cell_env ms t Mv0) binds) Xnan).
  { intros t. unfold Fu, cell_env.
    apply (values_with_derivs slot_u base len binds _ _ base Hwf);
      try lia; try (intros k _; reflexivity). }
  assert (Hval_v : forall t, eget n (Fv t) Xnan
                     = eget n (xextend (cell_env ms Mu t) binds) Xnan).
  { intros t. unfold Fv. rewrite cell_env_v.
    apply (values_with_derivs slot_v base len binds _ _ base Hwf);
      try lia; try (intros k _; reflexivity). }
  rewrite Hval_u in Hwu0, Hwu1.
  rewrite Hval_v in Hwv0, Hwv1.
  unfold Mu0, Mv0 in Hwu0.
  rewrite (cell_env_center ms base Hms Hb) in Hwu0.
  rewrite Hwu1 in Hwv0. injection Hwv0 as <-.
  exists wu0, wv1. split. exact Hwu0. split. exact Hwv1.
  assert (HDu : (0 <= Du)%R).
  { destruct (Hbnd_u Mu0 (proj1 Hin0)) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  assert (HDv : (0 <= Dv)%R).
  { destruct (Hbnd_v Mv0 (proj2 Hin0)) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  assert (Hhalf_u : (Rabs (Mu - Mu0) <= IZR du)%R).
  { unfold Mu0. destruct HinU as [Hl Hr].
    unfold lo_u in Hl. unfold hi_u in Hr.
    rewrite minus_IZR in Hl. rewrite plus_IZR in Hr. apply Rabs_le. lra. }
  assert (Hhalf_v : (Rabs (Mv - Mv0) <= IZR dv)%R).
  { unfold Mv0. destruct HinV as [Hl Hr].
    unfold lo_v in Hl. unfold hi_v in Hr.
    rewrite minus_IZR in Hl. rewrite plus_IZR in Hr. apply Rabs_le. lra. }
  assert (Hu' : (Rabs (wu1 - wu0) <= Du * IZR du)%R).
  { apply Rle_trans with (Du * Rabs (Mu - Mu0))%R. exact Hinc_u.
    now apply Rmult_le_compat_l. }
  assert (Hv' : (Rabs (wv1 - wu1) <= Dv * IZR dv)%R).
  { apply Rle_trans with (Dv * Rabs (Mv - Mv0))%R. exact Hinc_v.
    now apply Rmult_le_compat_l. }
  replace (wv1 - wu0)%R with ((wu1 - wu0) + (wv1 - wu1))%R by ring.
  eapply Rle_trans. apply Rabs_triang.
  rewrite (Rmult_comm (IZR du)), (Rmult_comm (IZR dv)).
  now apply Rplus_le_compat.
Qed.

(* ---------------------------------------------------------------- *)
(* The cell obstruction: bounded away over a continuum of angles     *)

(** The mean-value combination with the step subtracted instead of added:
    f_centre - du Du - dv Dv >= f_cell. *)
Definition combination_lower_e (du dv : Z) (cb : cbounds) : expr :=
  Esub (Esub (Esub (eps_e (cb_N0 cb) (cb_q0 cb))
                   (Emul (EfromZ du) (eps_e (cb_NDu cb) (cb_qDu cb))))
             (Emul (EfromZ dv) (eps_e (cb_NDv cb) (cb_qDv cb))))
       (eps_e (cb_Nc cb) (cb_qc cb)).

(** A passing reversed combination check is the real inequality it encodes. *)
Lemma combination_lower_correct :
  forall prec du dv cb,
  nonneg (ieval prec eempty (combination_lower_e du dv cb)) = true ->
  (IZR (cb_Nc cb) * powerRZ 2%R (cb_qc cb)
   <= IZR (cb_N0 cb) * powerRZ 2%R (cb_q0 cb)
      - IZR du * (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))
      - IZR dv * (IZR (cb_NDv cb) * powerRZ 2%R (cb_qDv cb)))%R.
Proof.
  intros prec du dv cb Hchk.
  assert (Hc := ieval_correct prec eempty eempty (combination_lower_e du dv cb) env_ok_nil).
  destruct (nonneg_correct _ _ Hc Hchk) as [d [Hd Hge]].
  unfold combination_lower_e in Hd.
  change (xeval eempty (Esub (Esub (Esub (eps_e (cb_N0 cb) (cb_q0 cb))
                    (Emul (EfromZ du) (eps_e (cb_NDu cb) (cb_qDu cb))))
                    (Emul (EfromZ dv) (eps_e (cb_NDv cb) (cb_qDv cb))))
                    (eps_e (cb_Nc cb) (cb_qc cb))))
    with (Xsub (Xsub (Xsub (xeval eempty (eps_e (cb_N0 cb) (cb_q0 cb)))
                  (Xmul (Xreal (IZR du)) (xeval eempty (eps_e (cb_NDu cb) (cb_qDu cb)))))
                  (Xmul (Xreal (IZR dv)) (xeval eempty (eps_e (cb_NDv cb) (cb_qDv cb)))))
                  (xeval eempty (eps_e (cb_Nc cb) (cb_qc cb))))
    in Hd.
  rewrite !xeval_eps_e in Hd. simpl in Hd. injection Hd as <-. lra.
Qed.

(** One component of a cell, checked for a floor instead of a ceiling. *)
Definition check_component_lower (prec : F.precision)
    (base len : nat) (du dv : Z)
    (env0 envu envv : env I.type) (r : expr) (cb : cbounds) : bool :=
  match slot_of r with
  | None => false
  | Some n =>
      Nat.leb base n && Nat.ltb n (base + len) &&
      check1_lower prec env0 r (cb_N0 cb) (cb_q0 cb) &&
      check1 prec envu (Evar (n + len)) (cb_NDu cb) (cb_qDu cb) &&
      check1 prec envv (Evar (n + len)) (cb_NDv cb) (cb_qDv cb) &&
      nonneg (ieval prec eempty (combination_lower_e du dv cb))
  end.

(** What it means: at every real point of the cell the component is a real
    number at least the cell floor, so no field of this form is in force
    balance anywhere in the cell. *)
Definition component_bounded_away (ms : list Z) (binds : list binding)
    (du dv : Z) (r : expr) (cb : cbounds) : Prop :=
  forall Mu Mv, in_cell ms du dv Mu Mv ->
  exists w,
    xeval (xextend (cell_env ms Mu Mv) binds) r = Xreal w /\
    (IZR (cb_Nc cb) * powerRZ 2%R (cb_qc cb) <= Rabs w)%R.

(** A passing reversed component check bounds the component away from zero
    over the whole cell. *)
Lemma component_lower_correct :
  forall prec ms base len binds du dv r cb,
  length ms = base -> (slot_u < base /\ slot_v < base)%nat -> (0 < len)%nat ->
  0 <= du -> 0 <= dv ->
  well_formed base binds = true -> len = length binds ->
  check_component_lower prec base len du dv
    (iextend prec (ienv_of prec ms) binds)
    (iextend prec (box_ienv prec ms du dv) (with_derivs slot_u base len binds))
    (iextend prec (box_ienv prec ms du dv) (with_derivs slot_v base len binds))
    r cb = true ->
  component_bounded_away ms binds du dv r cb.
Proof.
  intros prec ms base len binds du dv r cb Hms Hb Hlen0 Hdu Hdv Hwf Hlen Hchk.
  unfold check_component_lower in Hchk.
  destruct r; simpl in Hchk; try discriminate.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcomb].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdv_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdu_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcentre].
  apply andb_prop in Hchk. destruct Hchk as [Hbn Hn].
  apply Nat.leb_le in Hbn. apply Nat.ltb_lt in Hn.
  assert (Hcombi := combination_lower_correct prec du dv cb Hcomb).
  intros Mu Mv Hin.
  destruct (component_legs prec ms base len binds du dv n
              (cb_NDu cb) (cb_qDu cb) (cb_NDv cb) (cb_qDv cb) Mu Mv
              Hms Hb Hlen0 Hdu Hdv Hwf Hlen Hbn Hn Hdu_chk Hdv_chk Hin)
    as [w0 [w [Hw0 [Hw Hinc]]]].
  assert (Henv0 := iextend_correct prec binds _ _ (env_ok_fromZ prec ms)).
  destruct (check1_lower_correct _ _ _ _ _ _ Henv0 Hcentre) as [wc [Hwc Hb0]].
  simpl in Hwc.
  rewrite Hwc in Hw0. injection Hw0 as <-.
  exists w. split. exact Hw.
  assert (Htri : (Rabs wc - Rabs w <= Rabs (wc - w))%R) by apply Rabs_triang_inv.
  rewrite Rabs_minus_sym in Htri.
  lra.
Qed.

(** A cell is out of balance when some component is bounded away from zero
    over the whole of it. *)
Definition check_cell_lower (c : ccert) (cl : ccell) : bool :=
  let prec := cprec_of c in
  let ms := pt_ms (cc_pt cl) in
  let es := pt_es (cc_pt cl) in
  let base := n_inputs c in
  let r3 := residual es (cc_cfg c) (cc_modes c) in
  let binds := r_binds r3 in
  let len := length binds in
  let box := box_ienv prec ms (cc_du cl) (cc_dv cl) in
  let env0 := iextend prec (ienv_of prec ms) binds in
  let envu := iextend prec box (with_derivs slot_u base len binds) in
  let envv := iextend prec box (with_derivs slot_v base len binds) in
  Nat.eqb (length ms) base &&
  Nat.ltb slot_u base && Nat.ltb slot_v base &&
  Nat.ltb 0 len &&
  Z.leb 0 (cc_du cl) && Z.leb 0 (cc_dv cl) &&
  well_formed base binds &&
  (check_component_lower prec base len (cc_du cl) (cc_dv cl) env0 envu envv
                         (r_s r3) (cc_s cl) ||
   check_component_lower prec base len (cc_du cl) (cc_dv cl) env0 envu envv
                         (r_u r3) (cc_u cl) ||
   check_component_lower prec base len (cc_du cl) (cc_dv cl) env0 envu envv
                         (r_v r3) (cc_v cl)).

(** Every cell of a certificate is out of balance. *)
Definition check_ccert_lower (c : ccert) : bool :=
  forallb (check_cell_lower c) (cc_cells c).

(** A passing reversed cell verdict puts the field out of force balance at
    every real point of every cell, not only at the centres. Over cells that
    tile the angular torus that is an obstruction: no field of this form is
    in equilibrium anywhere on the covered angles. *)
Theorem check_ccert_lower_correct :
  forall c cl,
  check_ccert_lower c = true ->
  In cl (cc_cells c) ->
  component_bounded_away (pt_ms (cc_pt cl))
    (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
    (cc_du cl) (cc_dv cl)
    (r_s (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))) (cc_s cl)
  \/ component_bounded_away (pt_ms (cc_pt cl))
       (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
       (cc_du cl) (cc_dv cl)
       (r_u (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))) (cc_u cl)
  \/ component_bounded_away (pt_ms (cc_pt cl))
       (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
       (cc_du cl) (cc_dv cl)
       (r_v (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))) (cc_v cl).
Proof.
  intros c cl Hc Hin.
  assert (Hcell : check_cell_lower c cl = true).
  { unfold check_ccert_lower in Hc. rewrite forallb_forall in Hc. now apply Hc. }
  unfold check_cell_lower in Hcell.
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hcomp].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hwf].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdv].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdu].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hlen0].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hbv].
  apply andb_prop in Hcell. destruct Hcell as [Hms Hbu].
  apply Nat.eqb_eq in Hms.
  apply Nat.ltb_lt in Hbu. apply Nat.ltb_lt in Hbv.
  assert (Hb : (slot_u < n_inputs c /\ slot_v < n_inputs c)%nat)
    by (split; assumption).
  apply Nat.ltb_lt in Hlen0.
  apply Z.leb_le in Hdu. apply Z.leb_le in Hdv.
  apply orb_prop in Hcomp. destruct Hcomp as [Hcomp|Hv].
  - apply orb_prop in Hcomp. destruct Hcomp as [Hs|Hu].
    + left. apply (component_lower_correct (cprec_of c) _ (n_inputs c) _ _
                     (cc_du cl) (cc_dv cl) _ _ Hms Hb Hlen0 Hdu Hdv Hwf eq_refl Hs).
    + right; left.
      apply (component_lower_correct (cprec_of c) _ (n_inputs c) _ _
               (cc_du cl) (cc_dv cl) _ _ Hms Hb Hlen0 Hdu Hdv Hwf eq_refl Hu).
  - right; right.
    apply (component_lower_correct (cprec_of c) _ (n_inputs c) _ _
             (cc_du cl) (cc_dv cl) _ _ Hms Hb Hlen0 Hdu Hdv Hwf eq_refl Hv).
Qed.

(* ---------------------------------------------------------------- *)
(* From a list of cells to a range                                   *)

(** The interval a cell occupies in the first varied slot, as the centre and
    half-width the certificate carries. *)
Definition ucell (cl : ccell) : Z * Z :=
  (nth slot_u (pt_ms (cc_pt cl)) 0, cc_du cl).

(** A certificate whose cells cover a range of that slot bounds its first
    component at every real point of the range, and not merely at the centres
    the file lists. [Cover.covers] is a boolean over the centres and
    half-widths, so what used to be an arithmetic argument about the generator
    is decided by the checker on the same footing as the bounds themselves.

    The hypothesis on the second slot is what a covering by lines needs: every
    cell has to admit the point in that slot, which holds when the second slot
    carries a single cell spanning it, and is the case a certificate over the
    angles of one surface or over a radial cut presents. *)
Theorem check_ccert_over_range :
  forall c lo hi Mv,
  check_ccert c = true ->
  covers lo hi (map ucell (cc_cells c)) = true ->
  (forall cl, In cl (cc_cells c) ->
     (IZR (nth slot_v (pt_ms (cc_pt cl)) 0%Z - cc_dv cl) <= Mv <=
      IZR (nth slot_v (pt_ms (cc_pt cl)) 0%Z + cc_dv cl))%R) ->
  forall Mu, (IZR lo <= Mu <= IZR hi)%R ->
  exists cl, In cl (cc_cells c) /\
    exists w,
      xeval (xextend (cell_env (pt_ms (cc_pt cl)) Mu Mv)
               (r_binds (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c))))
            (r_s (residual (pt_es (cc_pt cl)) (cc_cfg c) (cc_modes c)))
      = Xreal w /\
      (Rabs w <= IZR (cb_Nc (cc_s cl)) * powerRZ 2%R (cb_qc (cc_s cl)))%R.
Proof.
  intros c lo hi Mv Hchk Hcov Hv Mu Hrange.
  destruct (covers_correct _ _ _ _ Hcov Hrange) as [cu [du [Hin Hu]]].
  apply in_map_iff in Hin. destruct Hin as [cl [Heq Hincl]].
  unfold ucell in Heq. injection Heq as Hc Hd. subst cu du.
  exists cl. split. exact Hincl.
  destruct (check_ccert_correct c cl Hchk Hincl) as [Hs _].
  apply Hs. split. exact Hu. now apply Hv.
Qed.

(** Writing a slot the value the point already gives it changes nothing. *)
Lemma xenv_of_set :
  forall ms base k,
  length ms = base -> (k < base)%nat ->
  eset k (xenv_of ms) (Xreal (IZR (nth k ms 0))) = xenv_of ms.
Proof.
  intros ms base k Hlen Hk.
  assert (Hentry : Xreal (IZR (nth k ms 0))
            = nth k (map (fun z => Xreal (IZR z)) ms) (Xreal (IZR 0))).
  { symmetry. apply (map_nth (fun z => Xreal (IZR z)) ms 0%Z k). }
  unfold xenv_of. rewrite Hentry.
  apply (eset_of_list_same _ _ k (Xreal (IZR 0))).
  rewrite length_map. lia.
Qed.

(** So a point of the cell whose second slot sits at its own value is the
    point environment with only the first slot moved. *)
Lemma cell_env_at_v_centre :
  forall ms base t,
  length ms = base -> (slot_v < base)%nat ->
  cell_env ms t (IZR (nth slot_v ms 0)) = eset slot_u (xenv_of ms) (Xreal t).
Proof.
  intros ms base t Hlen Hv. unfold cell_env.
  now rewrite (xenv_of_set ms base slot_v Hlen Hv).
Qed.

(* ---------------------------------------------------------------- *)
(* A cell checked with the derivative at its centre                  *)

(** The bounds a Taylor cell carries. The first varied slot is charged
    against its derivative at the centre, a thin evaluation, with the box
    paying only for a second derivative against the square of the half-width.
    The second slot keeps the mean-value step, because the point its leg
    starts from moves with the first slot and its derivative there is not a
    thin evaluation. *)
Record tbounds := TBounds {
  tb_N0 : Z ; tb_q0 : Z ;
  tb_Nu : Z ; tb_qu : Z ;
  tb_Nuu : Z ; tb_quu : Z ;
  tb_Nv : Z ; tb_qv : Z ;
  tb_Nc : Z ; tb_qc : Z
}.

Record tcell := TCell {
  tc_pt : cpoint ;
  tc_du : Z ; tc_dv : Z ;
  tc_s : tbounds ; tc_u : tbounds ; tc_v : tbounds
}.

Record tcert := TCert {
  tc_prec : Z ;
  tc_cfg : pconfig ;
  tc_modes : list (Z * Z) ;
  tc_cells : list tcell
}.

Definition tprec_of (c : tcert) : F.precision :=
  F.PtoP (Z.to_pos (tc_prec c)).

Definition n_inputs_t (c : tcert) : nat :=
  base_scratch_of (pc_lasym (tc_cfg c)) (pc_out (tc_cfg c))
    (length (tc_modes c)).

(** The combination a Taylor cell has to satisfy: the value at the centre,
    the first slot's step and its square, and the second slot's step. *)
Definition combination_t (du dv : Z) (tb : tbounds) : expr :=
  Esub (eps_e (tb_Nc tb) (tb_qc tb))
       (Eadd (eps_e (tb_N0 tb) (tb_q0 tb))
          (Eadd (Emul (EfromZ du) (eps_e (tb_Nu tb) (tb_qu tb)))
             (Eadd (Emul (Emul (EfromZ du) (EfromZ du))
                         (eps_e (tb_Nuu tb) (tb_quu tb)))
                   (Emul (EfromZ dv) (eps_e (tb_Nv tb) (tb_qv tb)))))).

(** env0 reads the point, envd the point with two derivative levels, and
    envb the box with two levels; envv is the second slot's derivative over
    the box, as before. *)
Definition check_component_t (prec : F.precision)
    (base len : nat) (du dv : Z)
    (env0 envd envb envv : env I.type) (r : expr) (tb : tbounds) : bool :=
  match slot_of r with
  | None => false
  | Some n =>
      Nat.leb base n && Nat.ltb n (base + len) &&
      check1 prec env0 r (tb_N0 tb) (tb_q0 tb) &&
      check1 prec envd (Evar (n + len)) (tb_Nu tb) (tb_qu tb) &&
      check1 prec envb (Evar (n + 2 * len)) (tb_Nuu tb) (tb_quu tb) &&
      check1 prec envv (Evar (n + len)) (tb_Nv tb) (tb_qv tb) &&
      nonneg (ieval prec eempty (combination_t du dv tb))
  end.

Definition check_cell_t (c : tcert) (cl : tcell) : bool :=
  let prec := tprec_of c in
  let ms := pt_ms (tc_pt cl) in
  let es := pt_es (tc_pt cl) in
  let base := n_inputs_t c in
  let r3 := residual es (tc_cfg c) (tc_modes c) in
  let binds := r_binds r3 in
  let len := length binds in
  let box := box_ienv prec ms (tc_du cl) (tc_dv cl) in
  let env0 := iextend prec (ienv_of prec ms) binds in
  let envd :=
    iextend prec (ienv_of prec ms) (with_derivs2 slot_u base len binds) in
  let envb := iextend prec box (with_derivs2 slot_u base len binds) in
  let envv := iextend prec box (with_derivs slot_v base len binds) in
  Nat.eqb (length ms) base &&
  Nat.ltb slot_u base && Nat.ltb slot_v base &&
  Nat.ltb 0 len &&
  Z.leb 0 (tc_du cl) && Z.leb 0 (tc_dv cl) &&
  well_formed base binds &&
  check_component_t prec base len (tc_du cl) (tc_dv cl)
    env0 envd envb envv (r_s r3) (tc_s cl) &&
  check_component_t prec base len (tc_du cl) (tc_dv cl)
    env0 envd envb envv (r_u r3) (tc_u cl) &&
  check_component_t prec base len (tc_du cl) (tc_dv cl)
    env0 envd envb envv (r_v r3) (tc_v cl).

Definition check_ccert_t (c : tcert) : bool :=
  forallb (check_cell_t c) (tc_cells c).

(** What a passing Taylor cell means, stated exactly as the mean-value one. *)
Definition component_t_sound (ms : list Z) (binds : list binding)
    (du dv : Z) (r : expr) (tb : tbounds) : Prop :=
  forall Mu Mv, in_cell ms du dv Mu Mv ->
  exists w,
    xeval (xextend (cell_env ms Mu Mv) binds) r = Xreal w /\
    (Rabs w <= IZR (tb_Nc tb) * powerRZ 2%R (tb_qc tb))%R.

(** A passing combination is the real inequality it encodes. *)
Lemma combination_t_correct :
  forall prec du dv tb,
  nonneg (ieval prec eempty (combination_t du dv tb)) = true ->
  (IZR (tb_N0 tb) * powerRZ 2%R (tb_q0 tb)
   + IZR du * (IZR (tb_Nu tb) * powerRZ 2%R (tb_qu tb))
   + IZR du * IZR du * (IZR (tb_Nuu tb) * powerRZ 2%R (tb_quu tb))
   + IZR dv * (IZR (tb_Nv tb) * powerRZ 2%R (tb_qv tb))
   <= IZR (tb_Nc tb) * powerRZ 2%R (tb_qc tb))%R.
Proof.
  intros prec du dv tb Hchk.
  destruct (nonneg_correct _ _
              (ieval_correct prec eempty eempty _ env_ok_nil) Hchk)
    as [d [Hd Hge]].
  unfold combination_t in Hd.
  cbn [xeval] in Hd. rewrite !xeval_eps_e in Hd.
  cbn in Hd. injection Hd as <-. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* A third varied slot                                               *)

(** A cell ranges over two slots, so a covering resolves two coordinates and
    the third is held at whatever the certificate wrote. For an axisymmetric
    equilibrium the toroidal direction costs nothing, since
    [toroidal_terms_vanish] makes its derivative the zero expression, but that
    argument sits outside the verdict. A third slot puts it inside.

    Nothing here rebuilds the walk from the centre. The two-slot walk of
    [component_legs] already moves from the centre to a point of the cell in
    the first two slots, at whatever value the third holds; one more
    mean-value leg moves the third, and the two compose. The derivative
    enclosure for that leg is taken over a box that widens all three slots,
    since the leg is travelled with the first two already moved. *)

Section ThirdSlot.

Variable slot_w : nat.
Hypothesis Hwu : slot_w <> slot_u.
Hypothesis Hwv : slot_w <> slot_v.

(** The box, widened in all three slots. *)
Definition box_ienv3 (prec : F.precision) (ms : list Z) (du dv dw : Z)
    : env I.type :=
  eset slot_u
    (eset slot_v
       (eset slot_w (ienv_of prec ms) (slot_box prec (nth slot_w ms 0) dw))
       (slot_box prec (nth slot_v ms 0) dv))
    (slot_box prec (nth slot_u ms 0) du).

(** The point environment with all three slots set. *)
Definition cell_env3 (ms : list Z) (Mu Mv Mw : R) : env ExtendedR :=
  eset slot_w (cell_env ms Mu Mv) (Xreal Mw).

Definition in_cell3 (ms : list Z) (du dv dw : Z) (Mu Mv Mw : R) : Prop :=
  in_cell ms du dv Mu Mv /\
  (IZR (nth slot_w ms 0%Z - dw) <= Mw <= IZR (nth slot_w ms 0%Z + dw))%R.

Lemma box_env_ok3 :
  forall prec ms du dv dw Mu Mv Mw,
  in_cell3 ms du dv dw Mu Mv Mw ->
  env_ok (box_ienv3 prec ms du dv dw) (cell_env3 ms Mu Mv Mw).
Proof.
  intros prec ms du dv dw Mu Mv Mw [[Hu Hv] Hw] k.
  unfold box_ienv3, cell_env3, cell_env.
  (* the two sides nest the three writes in different orders, so read each
     slot off directly rather than commuting them into line *)
  destruct (Nat.eq_dec k slot_u) as [->|Hku].
  - rewrite eget_eset_eq.
    rewrite eget_eset_neq by (apply not_eq_sym; exact Hwu).
    rewrite eget_eset_eq.
    now apply slot_box_correct.
  - rewrite (eget_eset_neq _ slot_u) by exact Hku.
    destruct (Nat.eq_dec k slot_v) as [->|Hkv].
    + rewrite eget_eset_eq.
      rewrite eget_eset_neq by (apply not_eq_sym; exact Hwv).
      rewrite eget_eset_neq by (apply not_eq_sym; exact Huv).
      rewrite eget_eset_eq.
      now apply slot_box_correct.
    + rewrite (eget_eset_neq _ slot_v) by exact Hkv.
      destruct (Nat.eq_dec k slot_w) as [->|Hkw].
      * rewrite eget_eset_eq, eget_eset_eq.
        now apply slot_box_correct.
      * rewrite (eget_eset_neq _ slot_w) by exact Hkw.
        rewrite (eget_eset_neq _ slot_w) by exact Hkw.
        rewrite (eget_eset_neq _ slot_u) by exact Hku.
        rewrite (eget_eset_neq _ slot_v) by exact Hkv.
        apply env_ok_fromZ.
Qed.

(** Writing the third slot's own value changes nothing, which is what lets the
    two-slot walk be read at that slot's centre. *)
Lemma cell_env3_centre :
  forall ms base Mu Mv,
  length ms = base -> (slot_w < base)%nat ->
  cell_env3 ms Mu Mv (IZR (nth slot_w ms 0)) = cell_env ms Mu Mv.
Proof.
  intros ms base Mu Mv Hlen Hw.
  unfold cell_env3.
  apply eset_same.
  unfold cell_env.
  rewrite find_eset_neq by exact Hwu.
  rewrite find_eset_neq by exact Hwv.
  unfold xenv_of.
  rewrite (find_of_list _ _ slot_w (Xreal (IZR 0)))
    by (rewrite length_map; lia).
  now rewrite (map_nth (fun z => Xreal (IZR z)) ms 0%Z slot_w).
Qed.

(** The checks of one component over a cell with three varied slots: the two
    the cell already had, and one more derivative bounded over the wider box. *)
Definition check_component3 (prec : F.precision)
    (base len : nat) (du dv dw : Z)
    (env0 envu envv envw : env I.type) (r : expr)
    (cb : cbounds) (Ndw qdw : Z) : bool :=
  match slot_of r with
  | None => false
  | Some n =>
      Nat.leb base n && Nat.ltb n (base + len) &&
      check1 prec env0 r (cb_N0 cb) (cb_q0 cb) &&
      check1 prec envu (Evar (n + len)) (cb_NDu cb) (cb_qDu cb) &&
      check1 prec envv (Evar (n + len)) (cb_NDv cb) (cb_qDv cb) &&
      check1 prec envw (Evar (n + len)) Ndw qdw &&
      nonneg (ieval prec eempty
                (Esub (eps_e (cb_Nc cb) (cb_qc cb))
                   (Eadd (eps_e (cb_N0 cb) (cb_q0 cb))
                      (Eadd (Emul (EfromZ du) (eps_e (cb_NDu cb) (cb_qDu cb)))
                         (Eadd (Emul (EfromZ dv) (eps_e (cb_NDv cb) (cb_qDv cb)))
                               (Emul (EfromZ dw) (eps_e Ndw qdw)))))))
  end.

(** What it means at every real point of the three-dimensional cell. *)
Definition component3_sound (ms : list Z) (binds : list binding)
    (du dv dw : Z) (r : expr) (cb : cbounds) : Prop :=
  forall Mu Mv Mw, in_cell3 ms du dv dw Mu Mv Mw ->
  exists w,
    xeval (xextend (cell_env3 ms Mu Mv Mw) binds) r = Xreal w /\
    (Rabs w <= IZR (cb_Nc cb) * powerRZ 2%R (cb_qc cb))%R.

(** A passing combination check is the real inequality it encodes, with the
    third slot's step among the terms. *)
Lemma combination3_correct :
  forall prec du dv dw cb Ndw qdw,
  nonneg (ieval prec eempty
            (Esub (eps_e (cb_Nc cb) (cb_qc cb))
               (Eadd (eps_e (cb_N0 cb) (cb_q0 cb))
                  (Eadd (Emul (EfromZ du) (eps_e (cb_NDu cb) (cb_qDu cb)))
                     (Eadd (Emul (EfromZ dv) (eps_e (cb_NDv cb) (cb_qDv cb)))
                           (Emul (EfromZ dw) (eps_e Ndw qdw))))))) = true ->
  (IZR (cb_N0 cb) * powerRZ 2%R (cb_q0 cb)
   + IZR du * (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))
   + IZR dv * (IZR (cb_NDv cb) * powerRZ 2%R (cb_qDv cb))
   + IZR dw * (IZR Ndw * powerRZ 2%R qdw)
   <= IZR (cb_Nc cb) * powerRZ 2%R (cb_qc cb))%R.
Proof.
  intros prec du dv dw cb Ndw qdw Hchk.
  destruct (nonneg_correct _ _
              (ieval_correct prec eempty eempty _ env_ok_nil) Hchk)
    as [d [Hd Hge]].
  cbn [xeval] in Hd. rewrite !xeval_eps_e in Hd.
  cbn in Hd. injection Hd as <-. lra.
Qed.

(** A passing three-slot check bounds the component at every real point of the
    cell. The first two slots are walked by [component_legs], at the value the
    third holds in the certificate; the third is one more mean-value leg from
    there, over a box wide in all three. *)
Lemma component3_correct :
  forall prec ms base len binds du dv dw r cb Ndw qdw,
  length ms = base ->
  (slot_u < base /\ slot_v < base /\ slot_w < base)%nat ->
  (0 < len)%nat ->
  0 <= du -> 0 <= dv -> 0 <= dw ->
  well_formed base binds = true -> len = length binds ->
  check_component3 prec base len du dv dw
    (iextend prec (ienv_of prec ms) binds)
    (iextend prec (box_ienv prec ms du dv) (with_derivs slot_u base len binds))
    (iextend prec (box_ienv prec ms du dv) (with_derivs slot_v base len binds))
    (iextend prec (box_ienv3 prec ms du dv dw)
       (with_derivs slot_w base len binds))
    r cb Ndw qdw = true ->
  component3_sound ms binds du dv dw r cb.
Proof.
  intros prec ms base len binds du dv dw r cb Ndw qdw
         Hms Hb Hlen0 Hdu Hdv Hdw Hwf Hlen Hchk.
  unfold check_component3 in Hchk.
  destruct r; simpl in Hchk; try discriminate.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcomb].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdw_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdv_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdu_chk].
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hcentre].
  apply andb_prop in Hchk. destruct Hchk as [Hbn Hn].
  apply Nat.leb_le in Hbn. apply Nat.ltb_lt in Hn.
  assert (Hcombi := combination3_correct prec du dv dw cb Ndw qdw Hcomb).
  destruct Hb as [Hbu [Hbv Hbw]].
  intros Mu Mv Mw [Hin Hw].
  (* the first two slots, at the value the third holds *)
  destruct (component_legs prec ms base len binds du dv n
              (cb_NDu cb) (cb_qDu cb) (cb_NDv cb) (cb_qDv cb) Mu Mv
              Hms (conj Hbu Hbv) Hlen0 Hdu Hdv Hwf Hlen Hbn Hn
              Hdu_chk Hdv_chk Hin)
    as [w0 [w1 [Hw0 [Hw1 Hinc12]]]].
  (* the centre value is bounded by the certificate's own claim *)
  assert (Henv0 := iextend_correct prec binds _ _ (env_ok_fromZ prec ms)).
  destruct (check1_correct _ _ _ _ _ _ Henv0 Hcentre) as [wc [Hwc Hb0]].
  simpl in Hwc. rewrite Hwc in Hw0. injection Hw0 as <-.
  (* the third leg, from the third slot's own value to Mw *)
  set (cw := IZR (nth slot_w ms 0)).
  set (Fw := fun t => xextend (eset slot_w (cell_env ms Mu Mv) (Xreal t))
                        (with_derivs slot_w base len binds)).
  assert (Hinv_w : inv slot_w base len Fw (base + len)).
  { destruct (inputs_real ms base Mu Mv Hms (conj Hbu Hbv)) as [Hl Hr].
    assert (Hbase := inv_base slot_w base len ltac:(lia) ltac:(lia) _ Hl Hr).
    assert (Hres := inv_bindings slot_w base len ltac:(lia) ltac:(lia)
                      binds _ base Hbase Hwf ltac:(lia) ltac:(lia)).
    rewrite <- Hlen in Hres.
    refine (inv_ext slot_w base len _ Fw (base + len) _ Hres).
    intros t. unfold Fw. reflexivity. }
  assert (Hdw_n := deriv_slot_of slot_w base len Fw (base + len) n
                     ltac:(lia) Hbn Hinv_w).
  set (Dw := (IZR Ndw * powerRZ 2%R qdw)%R).
  set (lo_w := IZR (nth slot_w ms 0 - dw)).
  set (hi_w := IZR (nth slot_w ms 0 + dw)).
  assert (Hbnd_w : forall t, (lo_w <= t <= hi_w)%R ->
            exists d, eget (n + len) (Fw t) Xnan = Xreal d /\ (Rabs d <= Dw)%R).
  { intros t Ht.
    assert (Hin3 : in_cell3 ms du dv dw Mu Mv t) by (split; assumption).
    assert (Henv := iextend_correct prec (with_derivs slot_w base len binds)
                      _ _ (box_env_ok3 prec ms du dv dw Mu Mv t Hin3)).
    destruct (check1_correct _ _ _ _ _ _ Henv Hdw_chk) as [d [Hd Hbd]].
    exists d. split. exact Hd. exact Hbd. }
  assert (Hcw : (lo_w <= cw <= hi_w)%R).
  { unfold cw, lo_w, hi_w. rewrite minus_IZR, plus_IZR.
    generalize (IZR_le 0 dw Hdw). lra. }
  destruct (bound_between_dist Fw n (n + len) Dw lo_w hi_w cw Mw
              Hdw_n Hbnd_w Hcw Hw) as [wa [wb [Hwa [Hwb Hinc3]]]].
  (* strip the derivative bindings from both ends of that leg *)
  assert (Hval : forall t, eget n (Fw t) Xnan
                   = eget n (xextend (cell_env3 ms Mu Mv t) binds) Xnan).
  { intros t. unfold Fw, cell_env3.
    apply (values_with_derivs slot_w base len binds _ _ base Hwf);
      try lia; try (intros k _; reflexivity). }
  rewrite Hval in Hwa, Hwb.
  unfold cw in Hwa. rewrite (cell_env3_centre ms base Mu Mv Hms Hbw) in Hwa.
  rewrite Hw1 in Hwa. injection Hwa as <-.
  exists wb. split. exact Hwb.
  (* the three legs and the centre, against the claim *)
  assert (HDw : (0 <= Dw)%R).
  { destruct (Hbnd_w cw Hcw) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  assert (Hhalf : (Rabs (Mw - cw) <= IZR dw)%R).
  { unfold cw. destruct Hw as [Hl Hr]. unfold lo_w in Hl. unfold hi_w in Hr.
    rewrite minus_IZR in Hl. rewrite plus_IZR in Hr. apply Rabs_le. lra. }
  assert (Hinc3' : (Rabs (wb - w1) <= Dw * IZR dw)%R).
  { apply Rle_trans with (Dw * Rabs (Mw - cw))%R. exact Hinc3.
    now apply Rmult_le_compat_l. }
  apply Rle_trans with (Rabs wc + (IZR du * (IZR (cb_NDu cb) * powerRZ 2%R (cb_qDu cb))
                                   + IZR dv * (IZR (cb_NDv cb) * powerRZ 2%R (cb_qDv cb)))
                        + Dw * IZR dw)%R.
  - replace wb with (wc + (w1 - wc) + (wb - w1))%R by ring.
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [| exact Hinc3'].
    eapply Rle_trans. apply Rabs_triang.
    apply Rplus_le_compat; [apply Rle_refl | exact Hinc12].
  - unfold Dw. rewrite (Rmult_comm (IZR Ndw * powerRZ 2 qdw)). lra.
Qed.

(* ---------------------------------------------------------------- *)
(* A certificate over three slots                                    *)

(** Per component the third slot adds one derivative bound; everything else a
    cell carries is what it carried before. *)
Record ccell3 := CCell3 {
  c3_pt : cpoint ;
  c3_du : Z ; c3_dv : Z ; c3_dw : Z ;
  c3_s : cbounds ; c3_u : cbounds ; c3_v : cbounds ;
  c3_Nws : Z ; c3_qws : Z ;
  c3_Nwu : Z ; c3_qwu : Z ;
  c3_Nwv : Z ; c3_qwv : Z
}.

Record ccert3 := CCert3 {
  c3_prec : Z ;
  c3_cfg : pconfig ;
  c3_modes : list (Z * Z) ;
  c3_cells : list ccell3
}.

Definition c3prec_of (c : ccert3) : F.precision :=
  F.PtoP (Z.to_pos (c3_prec c)).

Definition n_inputs3 (c : ccert3) : nat :=
  base_scratch_of (pc_lasym (c3_cfg c)) (pc_out (c3_cfg c))
    (length (c3_modes c)).

Definition check_cell3 (c : ccert3) (cl : ccell3) : bool :=
  let prec := c3prec_of c in
  let ms := pt_ms (c3_pt cl) in
  let es := pt_es (c3_pt cl) in
  let base := n_inputs3 c in
  let r3 := residual es (c3_cfg c) (c3_modes c) in
  let binds := r_binds r3 in
  let len := length binds in
  let box2 := box_ienv prec ms (c3_du cl) (c3_dv cl) in
  let box3 := box_ienv3 prec ms (c3_du cl) (c3_dv cl) (c3_dw cl) in
  let env0 := iextend prec (ienv_of prec ms) binds in
  let envu := iextend prec box2 (with_derivs slot_u base len binds) in
  let envv := iextend prec box2 (with_derivs slot_v base len binds) in
  let envw := iextend prec box3 (with_derivs slot_w base len binds) in
  Nat.eqb (length ms) base &&
  Nat.ltb slot_u base && Nat.ltb slot_v base && Nat.ltb slot_w base &&
  Nat.ltb 0 len &&
  Z.leb 0 (c3_du cl) && Z.leb 0 (c3_dv cl) && Z.leb 0 (c3_dw cl) &&
  well_formed base binds &&
  check_component3 prec base len (c3_du cl) (c3_dv cl) (c3_dw cl)
    env0 envu envv envw (r_s r3) (c3_s cl) (c3_Nws cl) (c3_qws cl) &&
  check_component3 prec base len (c3_du cl) (c3_dv cl) (c3_dw cl)
    env0 envu envv envw (r_u r3) (c3_u cl) (c3_Nwu cl) (c3_qwu cl) &&
  check_component3 prec base len (c3_du cl) (c3_dv cl) (c3_dw cl)
    env0 envu envv envw (r_v r3) (c3_v cl) (c3_Nwv cl) (c3_qwv cl).

Definition check_ccert3 (c : ccert3) : bool :=
  forallb (check_cell3 c) (c3_cells c).

(** A passing three-slot certificate bounds all three components at every real
    point of every cell, in all three coordinates at once. For an axisymmetric
    equilibrium the toroidal derivative is the zero expression, so its check
    passes against any bound and its step costs nothing however wide the cell:
    the covering of a cross-section becomes a covering of the volume inside the
    verdict rather than beside it. *)
Theorem check_ccert3_correct :
  forall c cl,
  check_ccert3 c = true ->
  In cl (c3_cells c) ->
  component3_sound (pt_ms (c3_pt cl))
    (r_binds (residual (pt_es (c3_pt cl)) (c3_cfg c) (c3_modes c)))
    (c3_du cl) (c3_dv cl) (c3_dw cl)
    (r_s (residual (pt_es (c3_pt cl)) (c3_cfg c) (c3_modes c))) (c3_s cl)
  /\ component3_sound (pt_ms (c3_pt cl))
       (r_binds (residual (pt_es (c3_pt cl)) (c3_cfg c) (c3_modes c)))
       (c3_du cl) (c3_dv cl) (c3_dw cl)
       (r_u (residual (pt_es (c3_pt cl)) (c3_cfg c) (c3_modes c))) (c3_u cl)
  /\ component3_sound (pt_ms (c3_pt cl))
       (r_binds (residual (pt_es (c3_pt cl)) (c3_cfg c) (c3_modes c)))
       (c3_du cl) (c3_dv cl) (c3_dw cl)
       (r_v (residual (pt_es (c3_pt cl)) (c3_cfg c) (c3_modes c))) (c3_v cl).
Proof.
  intros c cl Hc Hin.
  assert (Hcell : check_cell3 c cl = true).
  { unfold check_ccert3 in Hc. rewrite forallb_forall in Hc. now apply Hc. }
  unfold check_cell3 in Hcell.
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hv].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hu].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hs].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hwf].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdw].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdv].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hdu].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hlen0].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hbw].
  apply andb_prop in Hcell. destruct Hcell as [Hcell Hbv].
  apply andb_prop in Hcell. destruct Hcell as [Hms Hbu].
  apply Nat.eqb_eq in Hms.
  apply Nat.ltb_lt in Hbu. apply Nat.ltb_lt in Hbv. apply Nat.ltb_lt in Hbw.
  apply Nat.ltb_lt in Hlen0.
  apply Z.leb_le in Hdu. apply Z.leb_le in Hdv. apply Z.leb_le in Hdw.
  (* each component carries its own bound on the third derivative, so the
     three are discharged separately rather than by one tactic *)
  repeat split.
  - apply (component3_correct (c3prec_of c) _ (n_inputs3 c) _ _
             (c3_du cl) (c3_dv cl) (c3_dw cl) _ _ (c3_Nws cl) (c3_qws cl) Hms
             (conj Hbu (conj Hbv Hbw)) Hlen0 Hdu Hdv Hdw Hwf eq_refl Hs).
  - apply (component3_correct (c3prec_of c) _ (n_inputs3 c) _ _
             (c3_du cl) (c3_dv cl) (c3_dw cl) _ _ (c3_Nwu cl) (c3_qwu cl) Hms
             (conj Hbu (conj Hbv Hbw)) Hlen0 Hdu Hdv Hdw Hwf eq_refl Hu).
  - apply (component3_correct (c3prec_of c) _ (n_inputs3 c) _ _
             (c3_du cl) (c3_dv cl) (c3_dw cl) _ _ (c3_Nwv cl) (c3_qwv cl) Hms
             (conj Hbu (conj Hbv Hbw)) Hlen0 Hdu Hdv Hdw Hwf eq_refl Hv).
Qed.

End ThirdSlot.

End VariedSlots.
