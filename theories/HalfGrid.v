(** Second-order consistency of VMEC's half-grid scheme, and the convergence
    it gives with a stability bound.

    VMEC keeps R and Z on full-grid nodes and every field quantity on the half
    points between them. The radial residual at node j is assembled from the
    two half points around it: a quantity the residual needs at the node is
    the average of its two half-point values, and a radial derivative is
    their difference over the spacing h. Physics.v's node residual is that
    rule; its free-radius residual (full_point_b) is the same field read
    exactly, with every radial derivative a derivative of the reconstruction.

    [avg_consistent] and [dif_consistent] are the two Taylor bounds: an
    average of values h/2 either side misses the centre value by at most
    M2 h^2 / 8, and the centred difference misses the derivative by at most
    M3 h^2 / 24, M2 and M3 bounds on the second and third derivative over the
    interval. [node_consistent] carries them through the residual's products,
    so the node residual differs from the exact residual at the node by an
    explicit constant times h^2, the constant built from the derivative
    bounds of the six field quantities the residual reads.

    The half-point values the node rule averages are the reconstruction's own
    values there: the cubic Hermite of full_point_b takes value and slope at
    each knot, [hermite_knots]. So the node residual and the free-radius
    residual are two readings of one field, and [node_consistent] is the
    statement that the first converges to the second at second order.

    Consistency is half of convergence. The other half is stability: a bound
    on how far a discrete solution moves when its discrete residual changes.
    [lax] is the step from both to a residual bound of order h^2 for the
    discrete solution itself, and [lax_second_order] discharges
    Hypotheses.discretization_is_consistent from them. Stability is carried
    as a hypothesis: on the gauge-fixed quotient it is what Kantorovich.v
    calls the inverse bound, and the manufactured solutions of VMEC++ measure
    it at the resolutions they run.

    The innermost interval reads its coefficients by a linear rule between the
    two innermost nodes, since no half point lies below it. Linear
    interpolation reproduces values to second order and slopes to first,
    [axis_linear_value] and [axis_linear_slope], so near the axis the rule is
    first order in the radial derivatives, and a statement of second-order
    convergence holds on the volume outside it. *)

From Coq Require Import Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Quad Hypotheses.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Functions that vanish to some order at 0                          *)

Lemma Rabs_le_inv : forall x a, Rabs x <= a -> - a <= x <= a.
Proof.
  intros x a H. assert (H1 := Rle_abs x).
  assert (H2 : - x <= Rabs x) by (rewrite <- Rabs_Ropp; apply Rle_abs). lra.
Qed.

(** A function vanishing with its derivative at 0, whose second derivative
    is bounded by M on [0, t], is bounded by M t^2 / 2 there. *)
Lemma vanish2 :
  forall (g g' g'' : R -> R) M t,
  0 <= t ->
  (forall x, 0 <= x <= t -> derivable_pt_lim g x (g' x)) ->
  (forall x, 0 <= x <= t -> derivable_pt_lim g' x (g'' x)) ->
  g 0 = 0 -> g' 0 = 0 ->
  (forall x, 0 <= x <= t -> Rabs (g'' x) <= M) ->
  Rabs (g t) <= M * t * t / 2.
Proof.
  intros g g' g'' M t Ht Hg Hg' H0 H0' Hb.
  (* the first derivative grows at most linearly *)
  assert (Hd : forall x, 0 <= x <= t -> Rabs (g' x) <= M * x).
  { intros x Hx.
    assert (H := mvt_bound g' g'' 0 t M Hg' Hb 0 x ltac:(lra) Hx).
    rewrite H0' in H. replace (g' x - 0) with (g' x) in H by ring.
    rewrite (Rabs_right (x - 0)) in H by lra. lra. }
  destruct (Req_dec t 0) as [->|Ht0].
  - rewrite H0, Rabs_R0. lra.
  - assert (Htp : 0 < t) by lra.
    (* compare g with the parabola of the same bound, from both sides *)
    assert (Hup : g t - M * t * t / 2 <= 0).
    { destruct (MVT_cor2 (fun x => g x - M * x * x / 2) (fun x => g' x - M * x) 0 t Htp)
        as [c [Hc Hct]].
      { intros x Hx. apply derivable_pt_lim_minus. apply Hg. lra.
        apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. field. }
      cbv beta in Hc. rewrite H0 in Hc.
      assert (Hgc := Hd c ltac:(lra)). apply Rabs_le_inv in Hgc.
      replace (g t - M * t * t / 2) with (g t - M * t * t / 2 - (0 - M * 0 * 0 / 2))
        by field.
      rewrite Hc. apply Rmult_le_0_r. lra. lra. }
    assert (Hlo : - g t - M * t * t / 2 <= 0).
    { destruct (MVT_cor2 (fun x => - g x - M * x * x / 2) (fun x => - g' x - M * x) 0 t Htp)
        as [c [Hc Hct]].
      { intros x Hx. apply derivable_pt_lim_minus. apply derivable_pt_lim_opp. apply Hg. lra.
        apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. field. }
      cbv beta in Hc. rewrite H0 in Hc.
      assert (Hgc := Hd c ltac:(lra)). apply Rabs_le_inv in Hgc.
      replace (- g t - M * t * t / 2) with (- g t - M * t * t / 2 - (- 0 - M * 0 * 0 / 2))
        by field.
      rewrite Hc. apply Rmult_le_0_r. lra. lra. }
    apply Rabs_le. lra.
Qed.

(** One order more: vanishing with two derivatives at 0 and a third bounded
    by M, the function is bounded by M t^3 / 6. *)
Lemma vanish3 :
  forall (g g' g'' g''' : R -> R) M t,
  0 <= t ->
  (forall x, 0 <= x <= t -> derivable_pt_lim g x (g' x)) ->
  (forall x, 0 <= x <= t -> derivable_pt_lim g' x (g'' x)) ->
  (forall x, 0 <= x <= t -> derivable_pt_lim g'' x (g''' x)) ->
  g 0 = 0 -> g' 0 = 0 -> g'' 0 = 0 ->
  (forall x, 0 <= x <= t -> Rabs (g''' x) <= M) ->
  Rabs (g t) <= M * t * t * t / 6.
Proof.
  intros g g' g'' g''' M t Ht Hg Hg' Hg'' H0 H0' H0'' Hb.
  (* the first derivative is bounded by the quadratic, by the lemma above *)
  assert (Hd : forall x, 0 <= x <= t -> Rabs (g' x) <= M * x * x / 2).
  { intros x Hx.
    apply (vanish2 g' g'' g''' M x). lra.
    - intros y Hy. apply Hg'. lra.
    - intros y Hy. apply Hg''. lra.
    - exact H0'. - exact H0''.
    - intros y Hy. apply Hb. lra. }
  destruct (Req_dec t 0) as [->|Ht0].
  - rewrite H0, Rabs_R0. lra.
  - assert (Htp : 0 < t) by lra.
    assert (Hup : g t - M * t * t * t / 6 <= 0).
    { destruct (MVT_cor2 (fun x => g x - M * x * x * x / 6)
                         (fun x => g' x - M * x * x / 2) 0 t Htp)
        as [c [Hc Hct]].
      { intros x Hx. apply derivable_pt_lim_minus. apply Hg. lra.
        apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. field. }
      cbv beta in Hc. rewrite H0 in Hc.
      assert (Hgc := Hd c ltac:(lra)). apply Rabs_le_inv in Hgc.
      replace (g t - M * t * t * t / 6)
        with (g t - M * t * t * t / 6 - (0 - M * 0 * 0 * 0 / 6)) by field.
      rewrite Hc. apply Rmult_le_0_r. lra. lra. }
    assert (Hlo : - g t - M * t * t * t / 6 <= 0).
    { destruct (MVT_cor2 (fun x => - g x - M * x * x * x / 6)
                         (fun x => - g' x - M * x * x / 2) 0 t Htp)
        as [c [Hc Hct]].
      { intros x Hx. apply derivable_pt_lim_minus. apply derivable_pt_lim_opp. apply Hg. lra.
        apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. field. }
      cbv beta in Hc. rewrite H0 in Hc.
      assert (Hgc := Hd c ltac:(lra)). apply Rabs_le_inv in Hgc.
      replace (- g t - M * t * t * t / 6)
        with (- g t - M * t * t * t / 6 - (- 0 - M * 0 * 0 * 0 / 6)) by field.
      rewrite Hc. apply Rmult_le_0_r. lra. lra. }
    apply Rabs_le. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The half-grid rules                                               *)

(** Shifting the argument keeps a derivative, with the sign of the shift. *)
Lemma deriv_shift_plus :
  forall (f f' : R -> R) s x,
  derivable_pt_lim f (s + x) (f' (s + x)) ->
  derivable_pt_lim (fun t => f (s + t)) x (f' (s + x)).
Proof.
  intros f f' s x H.
  replace (f' (s + x)) with (f' (s + x) * 1) by ring.
  apply (derivable_pt_lim_comp (fun t => s + t) f x 1 (f' (s + x))).
  - apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. ring.
  - exact H.
Qed.

Lemma deriv_shift_minus :
  forall (f f' : R -> R) s x,
  derivable_pt_lim f (s - x) (f' (s - x)) ->
  derivable_pt_lim (fun t => f (s - t)) x (- f' (s - x)).
Proof.
  intros f f' s x H.
  replace (- f' (s - x)) with (f' (s - x) * (-1)) by ring.
  apply (derivable_pt_lim_comp (fun t => s - t) f x (-1) (f' (s - x))).
  - apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. ring.
  - exact H.
Qed.

Section Rules.

(** A quantity along the radius with three derivatives, on [s - h/2, s + h/2]. *)
Variable f f1 f2 f3 : R -> R.
Variable s h : R.
Hypothesis Hh : 0 <= h.
Hypothesis D1 : forall x, s - h / 2 <= x <= s + h / 2 -> derivable_pt_lim f x (f1 x).
Hypothesis D2 : forall x, s - h / 2 <= x <= s + h / 2 -> derivable_pt_lim f1 x (f2 x).

(** The average of the two half-point values. *)
Definition avg2 : R := (f (s - h / 2) + f (s + h / 2)) / 2.

Theorem avg_consistent :
  forall M2, (forall x, s - h / 2 <= x <= s + h / 2 -> Rabs (f2 x) <= M2) ->
  Rabs (avg2 - f s) <= M2 * h * h / 8.
Proof using Hh D1 D2.
  intros M2 HM.
  set (g := fun t => f (s + t) + f (s - t) - 2 * f s).
  set (g' := fun t => f1 (s + t) - f1 (s - t)).
  set (g'' := fun t => f2 (s + t) + f2 (s - t)).
  assert (Hv := vanish2 g g' g'' (2 * M2) (h / 2) ltac:(lra)).
  assert (Hg : forall x, 0 <= x <= h / 2 -> derivable_pt_lim g x (g' x)).
  { intros x Hx. unfold g, g'.
    replace (f1 (s + x) - f1 (s - x)) with (f1 (s + x) + - f1 (s - x) - 0) by ring.
    apply derivable_pt_lim_minus. apply derivable_pt_lim_plus.
    - apply (deriv_shift_plus f f1). apply D1. lra.
    - apply (deriv_shift_minus f f1). apply D1. lra.
    - apply derivable_pt_lim_const. }
  assert (Hg' : forall x, 0 <= x <= h / 2 -> derivable_pt_lim g' x (g'' x)).
  { intros x Hx. unfold g', g''.
    replace (f2 (s + x) + f2 (s - x)) with (f2 (s + x) - - f2 (s - x)) by ring.
    apply derivable_pt_lim_minus.
    - apply (deriv_shift_plus f1 f2). apply D2. lra.
    - apply (deriv_shift_minus f1 f2). apply D2. lra. }
  specialize (Hv Hg Hg').
  assert (Hb : forall x, 0 <= x <= h / 2 -> Rabs (g'' x) <= 2 * M2).
  { intros x Hx. unfold g''.
    eapply Rle_trans. apply Rabs_triang.
    assert (H1 := HM (s + x) ltac:(lra)). assert (H2 := HM (s - x) ltac:(lra)). lra. }
  assert (Hr := Hv ltac:(unfold g; replace (s + 0) with s by ring;
                          replace (s - 0) with s by ring; ring)
                  ltac:(unfold g'; replace (s + 0) with s by ring;
                          replace (s - 0) with s by ring; ring) Hb).
  unfold g in Hr. unfold avg2.
  replace ((f (s - h / 2) + f (s + h / 2)) / 2 - f s)
    with ((f (s + h / 2) + f (s - h / 2) - 2 * f s) / 2) by field.
  rewrite Rabs_div by lra. rewrite (Rabs_right 2) by lra.
  apply (Rmult_le_reg_r 2). lra. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  nra.
Qed.

Hypothesis D3 : forall x, s - h / 2 <= x <= s + h / 2 -> derivable_pt_lim f2 x (f3 x).

(** The centred difference of the two half-point values. *)
Definition dif2 : R := (f (s + h / 2) - f (s - h / 2)) / h.

Theorem dif_consistent :
  forall M3, 0 < h -> (forall x, s - h / 2 <= x <= s + h / 2 -> Rabs (f3 x) <= M3) ->
  Rabs (dif2 - f1 s) <= M3 * h * h / 24.
Proof using Hh D1 D2 D3.
  intros M3 Hhp HM.
  set (g := fun t => f (s + t) - f (s - t) - 2 * t * f1 s).
  set (g' := fun t => f1 (s + t) + f1 (s - t) - 2 * f1 s).
  set (g'' := fun t => f2 (s + t) - f2 (s - t)).
  set (g''' := fun t => f3 (s + t) + f3 (s - t)).
  assert (Hg : forall x, 0 <= x <= h / 2 -> derivable_pt_lim g x (g' x)).
  { intros x Hx. unfold g, g'.
    replace (f1 (s + x) + f1 (s - x) - 2 * f1 s)
      with (f1 (s + x) - - f1 (s - x) - 2 * f1 s) by ring.
    apply derivable_pt_lim_minus. apply derivable_pt_lim_minus.
    - apply (deriv_shift_plus f f1). apply D1. lra.
    - apply (deriv_shift_minus f f1). apply D1. lra.
    - apply (proj1 (is_derive_Reals _ _ _)). auto_derive; try exact I. ring. }
  assert (Hg' : forall x, 0 <= x <= h / 2 -> derivable_pt_lim g' x (g'' x)).
  { intros x Hx. unfold g', g''.
    replace (f2 (s + x) - f2 (s - x)) with (f2 (s + x) + - f2 (s - x) - 0) by ring.
    apply derivable_pt_lim_minus. apply derivable_pt_lim_plus.
    - apply (deriv_shift_plus f1 f2). apply D2. lra.
    - apply (deriv_shift_minus f1 f2). apply D2. lra.
    - apply derivable_pt_lim_const. }
  assert (Hg'' : forall x, 0 <= x <= h / 2 -> derivable_pt_lim g'' x (g''' x)).
  { intros x Hx. unfold g'', g'''.
    replace (f3 (s + x) + f3 (s - x)) with (f3 (s + x) - - f3 (s - x)) by ring.
    apply derivable_pt_lim_minus.
    - apply (deriv_shift_plus f2 f3). apply D3. lra.
    - apply (deriv_shift_minus f2 f3). apply D3. lra. }
  assert (Hb : forall x, 0 <= x <= h / 2 -> Rabs (g''' x) <= 2 * M3).
  { intros x Hx. unfold g'''.
    eapply Rle_trans. apply Rabs_triang.
    assert (H1 := HM (s + x) ltac:(lra)). assert (H2 := HM (s - x) ltac:(lra)). lra. }
  assert (Hr := vanish3 g g' g'' g''' (2 * M3) (h / 2) ltac:(lra) Hg Hg' Hg''
                  ltac:(unfold g; replace (s + 0) with s by ring;
                          replace (s - 0) with s by ring; ring)
                  ltac:(unfold g'; replace (s + 0) with s by ring;
                          replace (s - 0) with s by ring; ring)
                  ltac:(unfold g''; replace (s + 0) with s by ring;
                          replace (s - 0) with s by ring; ring) Hb).
  unfold g in Hr. unfold dif2.
  replace ((f (s + h / 2) - f (s - h / 2)) / h - f1 s)
    with ((f (s + h / 2) - f (s - h / 2) - 2 * (h / 2) * f1 s) / h) by (field; lra).
  rewrite Rabs_div by lra. rewrite (Rabs_right h) by lra.
  apply (Rmult_le_reg_r h). exact Hhp.
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  nra.
Qed.

End Rules.

(* ---------------------------------------------------------------- *)
(* The node residual                                                 *)

(** Products of approximations: if a is within ea of a0 and b within eb of
    b0, the product is within |a0| eb + |b0| ea + ea eb of a0 b0. *)
Lemma product_error :
  forall a a0 b b0 ea eb,
  Rabs (a - a0) <= ea -> Rabs (b - b0) <= eb ->
  Rabs (a * b - a0 * b0) <= Rabs a0 * eb + Rabs b0 * ea + ea * eb.
Proof.
  intros a a0 b b0 ea eb Ha Hb.
  replace (a * b - a0 * b0) with (a0 * (b - b0) + b0 * (a - a0) + (a - a0) * (b - b0))
    by ring.
  eapply Rle_trans. apply Rabs_triang.
  eapply Rle_trans. apply Rplus_le_compat_r. apply Rabs_triang.
  rewrite !Rabs_mult.
  assert (H0 : 0 <= Rabs (a - a0)) by apply Rabs_pos.
  assert (H1 : 0 <= Rabs (b - b0)) by apply Rabs_pos.
  assert (H2 := Rabs_pos a0). assert (H3 := Rabs_pos b0).
  apply Rplus_le_compat. apply Rplus_le_compat.
  - now apply Rmult_le_compat_l.
  - now apply Rmult_le_compat_l.
  - apply Rmult_le_compat; assumption.
Qed.

Section NodeResidual.

(** The six field quantities the radial residual reads, as functions of the
    radius at fixed angles, each with the derivatives the rules need:
      cBu, cBv    the contravariant components (averaged)
      cBsu, cBsv  the angular derivatives of B_s (averaged)
      cBu_, cBv_  the covariant components (differenced). *)
Variable cBu cBu1 cBu2 cBv cBv1 cBv2 : R -> R.
Variable cBsu cBsu1 cBsu2 cBsv cBsv1 cBsv2 : R -> R.
Variable cBcu cBcu1 cBcu2 cBcu3 cBcv cBcv1 cBcv2 cBcv3 : R -> R.
Variable mu0pp s h : R.

Hypothesis Hh : 0 < h.

Let I x := s - h / 2 <= x <= s + h / 2.

Hypothesis Du : forall x, I x -> derivable_pt_lim cBu x (cBu1 x) /\ derivable_pt_lim cBu1 x (cBu2 x).
Hypothesis Dv : forall x, I x -> derivable_pt_lim cBv x (cBv1 x) /\ derivable_pt_lim cBv1 x (cBv2 x).
Hypothesis Dsu : forall x, I x -> derivable_pt_lim cBsu x (cBsu1 x) /\ derivable_pt_lim cBsu1 x (cBsu2 x).
Hypothesis Dsv : forall x, I x -> derivable_pt_lim cBsv x (cBsv1 x) /\ derivable_pt_lim cBsv1 x (cBsv2 x).
Hypothesis Dcu : forall x, I x ->
  derivable_pt_lim cBcu x (cBcu1 x) /\ derivable_pt_lim cBcu1 x (cBcu2 x) /\
  derivable_pt_lim cBcu2 x (cBcu3 x).
Hypothesis Dcv : forall x, I x ->
  derivable_pt_lim cBcv x (cBcv1 x) /\ derivable_pt_lim cBcv1 x (cBcv2 x) /\
  derivable_pt_lim cBcv2 x (cBcv3 x).

(** Bounds on the derivatives the two rules charge. *)
Variable Mu Mv Msu Msv Mcu Mcv : R.
Hypothesis Bu : forall x, I x -> Rabs (cBu2 x) <= Mu.
Hypothesis Bv : forall x, I x -> Rabs (cBv2 x) <= Mv.
Hypothesis Bsu : forall x, I x -> Rabs (cBsu2 x) <= Msu.
Hypothesis Bsv : forall x, I x -> Rabs (cBsv2 x) <= Msv.
Hypothesis Bcu : forall x, I x -> Rabs (cBcu3 x) <= Mcu.
Hypothesis Bcv : forall x, I x -> Rabs (cBcv3 x) <= Mcv.

(** The node residual, from the half-point values h/2 either side, and the
    exact residual at the node. *)
Definition avgf (g : R -> R) : R := (g (s - h / 2) + g (s + h / 2)) / 2.
Definition diff (g : R -> R) : R := (g (s + h / 2) - g (s - h / 2)) / h.

Definition rs_node : R :=
  (avgf cBsv - diff cBcv) * avgf cBv - (diff cBcu - avgf cBsu) * avgf cBu - mu0pp.

Definition rs_exact : R :=
  (cBsv s - cBcv1 s) * cBv s - (cBcu1 s - cBsu s) * cBu s - mu0pp.

(** The errors of the four factors, and the constant they combine into. *)
Definition e_v : R := Mv * h * h / 8.
Definition e_u : R := Mu * h * h / 8.
Definition e_1 : R := Msv * h * h / 8 + Mcv * h * h / 24.
Definition e_2 : R := Mcu * h * h / 24 + Msu * h * h / 8.

Theorem node_consistent :
  Rabs (rs_node - rs_exact)
  <= (Rabs (cBsv s - cBcv1 s) * e_v + Rabs (cBv s) * e_1 + e_1 * e_v)
   + (Rabs (cBcu1 s - cBsu s) * e_u + Rabs (cBu s) * e_2 + e_2 * e_u).
Proof using All.
  assert (Hh0 : 0 <= h) by lra.
  (* the four factors *)
  assert (Ev : Rabs (avgf cBv - cBv s) <= e_v).
  { apply (avg_consistent cBv cBv1 cBv2 s h Hh0);
      [intros x Hx; apply (Dv x Hx) | intros x Hx; apply (Dv x Hx) | exact Bv]. }
  assert (Eu : Rabs (avgf cBu - cBu s) <= e_u).
  { apply (avg_consistent cBu cBu1 cBu2 s h Hh0);
      [intros x Hx; apply (Du x Hx) | intros x Hx; apply (Du x Hx) | exact Bu]. }
  assert (Esv : Rabs (avgf cBsv - cBsv s) <= Msv * h * h / 8).
  { apply (avg_consistent cBsv cBsv1 cBsv2 s h Hh0);
      [intros x Hx; apply (Dsv x Hx) | intros x Hx; apply (Dsv x Hx) | exact Bsv]. }
  assert (Esu : Rabs (avgf cBsu - cBsu s) <= Msu * h * h / 8).
  { apply (avg_consistent cBsu cBsu1 cBsu2 s h Hh0);
      [intros x Hx; apply (Dsu x Hx) | intros x Hx; apply (Dsu x Hx) | exact Bsu]. }
  assert (Ecv : Rabs (diff cBcv - cBcv1 s) <= Mcv * h * h / 24).
  { apply (dif_consistent cBcv cBcv1 cBcv2 cBcv3 s h Hh0);
      [intros x Hx; apply (Dcv x Hx) | intros x Hx; apply (Dcv x Hx)
      | intros x Hx; apply (Dcv x Hx) | exact Hh | exact Bcv]. }
  assert (Ecu : Rabs (diff cBcu - cBcu1 s) <= Mcu * h * h / 24).
  { apply (dif_consistent cBcu cBcu1 cBcu2 cBcu3 s h Hh0);
      [intros x Hx; apply (Dcu x Hx) | intros x Hx; apply (Dcu x Hx)
      | intros x Hx; apply (Dcu x Hx) | exact Hh | exact Bcu]. }
  assert (E1 : Rabs ((avgf cBsv - diff cBcv) - (cBsv s - cBcv1 s)) <= e_1).
  { unfold e_1.
    replace ((avgf cBsv - diff cBcv) - (cBsv s - cBcv1 s))
      with ((avgf cBsv - cBsv s) - (diff cBcv - cBcv1 s)) by ring.
    eapply Rle_trans. apply Rabs_triang. rewrite Rabs_Ropp. lra. }
  assert (E2 : Rabs ((diff cBcu - avgf cBsu) - (cBcu1 s - cBsu s)) <= e_2).
  { unfold e_2.
    replace ((diff cBcu - avgf cBsu) - (cBcu1 s - cBsu s))
      with ((diff cBcu - cBcu1 s) - (avgf cBsu - cBsu s)) by ring.
    eapply Rle_trans. apply Rabs_triang. rewrite Rabs_Ropp. lra. }
  assert (P1 := product_error _ _ _ _ _ _ E1 Ev).
  assert (P2 := product_error _ _ _ _ _ _ E2 Eu).
  unfold rs_node, rs_exact.
  replace ((avgf cBsv - diff cBcv) * avgf cBv - (diff cBcu - avgf cBsu) * avgf cBu - mu0pp
           - ((cBsv s - cBcv1 s) * cBv s - (cBcu1 s - cBsu s) * cBu s - mu0pp))
    with (((avgf cBsv - diff cBcv) * avgf cBv - (cBsv s - cBcv1 s) * cBv s)
          - ((diff cBcu - avgf cBsu) * avgf cBu - (cBcu1 s - cBsu s) * cBu s)) by ring.
  eapply Rle_trans. apply Rabs_triang. rewrite Rabs_Ropp.
  apply Rplus_le_compat; assumption.
Qed.

(** The same, as a constant times h^2 for every h up to h1: the constant
    depends on the derivative bounds and on the exact field at the node, not
    on h. *)
Definition Kc (h1 : R) : R :=
  (Rabs (cBsv s - cBcv1 s) * Mv / 8 + Rabs (cBv s) * (Msv / 8 + Mcv / 24)
   + (Msv / 8 + Mcv / 24) * (Mv / 8) * (h1 * h1))
  + (Rabs (cBcu1 s - cBsu s) * Mu / 8 + Rabs (cBu s) * (Mcu / 24 + Msu / 8)
     + (Mcu / 24 + Msu / 8) * (Mu / 8) * (h1 * h1)).

Theorem node_second_order :
  forall h1, h <= h1 -> Rabs (rs_node - rs_exact) <= Kc h1 * (h * h).
Proof using All.
  intros h1 Hh1.
  eapply Rle_trans. apply node_consistent.
  assert (HMu : 0 <= Mu) by (assert (H := Bu s ltac:(unfold I; lra));
                             assert (H' := Rabs_pos (cBu2 s)); lra).
  assert (HMv : 0 <= Mv) by (assert (H := Bv s ltac:(unfold I; lra));
                             assert (H' := Rabs_pos (cBv2 s)); lra).
  assert (HMsu : 0 <= Msu) by (assert (H := Bsu s ltac:(unfold I; lra));
                               assert (H' := Rabs_pos (cBsu2 s)); lra).
  assert (HMsv : 0 <= Msv) by (assert (H := Bsv s ltac:(unfold I; lra));
                               assert (H' := Rabs_pos (cBsv2 s)); lra).
  assert (HMcu : 0 <= Mcu) by (assert (H := Bcu s ltac:(unfold I; lra));
                               assert (H' := Rabs_pos (cBcu3 s)); lra).
  assert (HMcv : 0 <= Mcv) by (assert (H := Bcv s ltac:(unfold I; lra));
                               assert (H' := Rabs_pos (cBcv3 s)); lra).
  replace ((Rabs (cBsv s - cBcv1 s) * e_v + Rabs (cBv s) * e_1 + e_1 * e_v)
           + (Rabs (cBcu1 s - cBsu s) * e_u + Rabs (cBu s) * e_2 + e_2 * e_u))
    with (Kc h * (h * h)) by (unfold Kc, e_1, e_2, e_u, e_v; field).
  assert (Hhh : h * h <= h1 * h1) by nra.
  assert (Hq : 0 <= h * h) by nra.
  apply Rmult_le_compat_r. exact Hq.
  unfold Kc. apply Rplus_le_compat; apply Rplus_le_compat_l.
  - apply Rmult_le_compat_l. nra. exact Hhh.
  - apply Rmult_le_compat_l. nra. exact Hhh.
Qed.

End NodeResidual.

(* ---------------------------------------------------------------- *)
(* The reconstruction reproduces the half-point data                 *)

(** The cubic Hermite of full_point_b in its slope-defect form, with
    t = (s - s_a) / H, the secant S = (yb - ya) / H and the slope defects
    a = da - S and b = db - S. *)
Definition herm_val (ya yb da db H t : R) : R :=
  let S := (yb - ya) / H in
  ya + t * (yb - ya) + H * ((t * t * t - 2 * (t * t) + t) * (da - S)
                            + (t * t * t - t * t) * (db - S)).

Definition herm_slope (ya yb da db H t : R) : R :=
  let S := (yb - ya) / H in
  S + ((3 * (t * t) - 4 * t + 1) * (da - S) + (3 * (t * t) - 2 * t) * (db - S)).

(** At the two knots it takes the value and slope VMEC gives there, so the
    half-point quantities the node residual averages and differences are the
    reconstruction's own. *)
Theorem hermite_knots :
  forall ya yb da db H, H <> 0 ->
  herm_val ya yb da db H 0 = ya /\ herm_slope ya yb da db H 0 = da /\
  herm_val ya yb da db H 1 = yb /\ herm_slope ya yb da db H 1 = db.
Proof.
  intros ya yb da db H HH. unfold herm_val, herm_slope.
  repeat split; field; exact HH.
Qed.

(** The slope is the derivative of the value, in s: the reconstruction is
    continuously differentiable between the knots. *)
Theorem hermite_slope_is_derivative :
  forall ya yb da db sa H s, H <> 0 ->
  is_derive (fun x => herm_val ya yb da db H ((x - sa) / H)) s
            (herm_slope ya yb da db H ((s - sa) / H)).
Proof.
  intros ya yb da db sa H s HH. unfold herm_val, herm_slope.
  auto_derive; try exact I. field. exact HH.
Qed.

(* ---------------------------------------------------------------- *)
(* The innermost interval                                            *)

(** The linear rule between the two innermost nodes: values to second order,
    slopes to first. With |f''| <= M on [a, b], the value at a point of the
    interval misses by at most 2 M (b - a)^2 and the slope by at most
    M (b - a). *)
Theorem axis_linear_slope :
  forall (f f1 f2 : R -> R) a b M x,
  a < b -> a <= x <= b ->
  (forall y, a <= y <= b -> derivable_pt_lim f y (f1 y)) ->
  (forall y, a <= y <= b -> derivable_pt_lim f1 y (f2 y)) ->
  (forall y, a <= y <= b -> Rabs (f2 y) <= M) ->
  Rabs ((f b - f a) / (b - a) - f1 x) <= M * (b - a).
Proof.
  intros f f1 f2 a b M x Hab Hx D1 D2 HM.
  destruct (MVT_cor2 f f1 a b Hab) as [c [Hc Hcin]].
  { intros y Hy. apply D1. lra. }
  assert (Hs : (f b - f a) / (b - a) = f1 c) by (rewrite Hc; field; lra).
  rewrite Hs.
  assert (H := mvt_bound f1 f2 a b M D2 HM x c Hx ltac:(lra)).
  eapply Rle_trans. exact H.
  assert (HM0 : 0 <= M) by (assert (H0 := HM a ltac:(lra));
                            assert (H' := Rabs_pos (f2 a)); lra).
  apply Rmult_le_compat_l. exact HM0. apply Rabs_le. lra.
Qed.

Theorem axis_linear_value :
  forall (f f1 f2 : R -> R) a b M x,
  a < b -> a <= x <= b ->
  (forall y, a <= y <= b -> derivable_pt_lim f y (f1 y)) ->
  (forall y, a <= y <= b -> derivable_pt_lim f1 y (f2 y)) ->
  (forall y, a <= y <= b -> Rabs (f2 y) <= M) ->
  Rabs (f a + (x - a) * ((f b - f a) / (b - a)) - f x) <= 2 * M * (b - a) * (b - a).
Proof.
  intros f f1 f2 a b M x Hab Hx D1 D2 HM.
  assert (HM0 : 0 <= M) by (assert (H := HM a ltac:(lra)); assert (H' := Rabs_pos (f2 a)); lra).
  (* the secant slope and the slope at x both lie within M (b - a) of f1 a *)
  destruct (MVT_cor2 f f1 a b Hab) as [c [Hc Hcin]].
  { intros y Hy. apply D1. lra. }
  assert (Hs : (f b - f a) / (b - a) = f1 c) by (rewrite Hc; field; lra).
  assert (H1 : forall y, a <= y <= b -> Rabs (f1 y - f1 a) <= M * (b - a)).
  { intros y Hy. assert (H := mvt_bound f1 f2 a b M D2 HM a y ltac:(lra) Hy).
    eapply Rle_trans. exact H. apply Rmult_le_compat_l. exact HM0.
    rewrite Rabs_right by lra. lra. }
  rewrite Hs.
  destruct (Req_dec x a) as [->|Hxa].
  - replace (f a + (a - a) * f1 c - f a) with 0 by ring.
    rewrite Rabs_R0. apply Rmult_le_pos. apply Rmult_le_pos. lra. lra. lra.
  - destruct (MVT_cor2 f f1 a x ltac:(lra)) as [d [Hd Hdin]].
    { intros y Hy. apply D1. lra. }
    replace (f a + (x - a) * f1 c - f x) with ((x - a) * (f1 c - f1 d))
      by (replace (f x) with (f a + f1 d * (x - a)) by lra; ring).
    rewrite Rabs_mult, (Rabs_right (x - a)) by lra.
    assert (Hcd : Rabs (f1 c - f1 d) <= 2 * (M * (b - a))).
    { replace (f1 c - f1 d) with ((f1 c - f1 a) - (f1 d - f1 a)) by ring.
      eapply Rle_trans. apply Rabs_triang. rewrite Rabs_Ropp.
      assert (Ha := H1 c ltac:(lra)). assert (Hb := H1 d ltac:(lra)). lra. }
    apply Rle_trans with ((x - a) * (2 * (M * (b - a)))).
    + apply Rmult_le_compat_l. lra. exact Hcd.
    + assert (Hxb : x - a <= b - a) by lra.
      assert (HMb : 0 <= 2 * (M * (b - a))) by nra.
      nra.
Qed.

(* ---------------------------------------------------------------- *)
(* Consistency and stability give convergence                        *)

Section Lax.

(** A discrete solution xh at spacing h, the sampling xs of a smooth
    solution, a distance between discrete states in the norm the residual
    answers to, the discrete residual of a state, and the certified residual
    of its reconstruction. *)
Variable X : Type.
Variable dist : X -> X -> R.
Variable dres : X -> R.
Variable cres : X -> R.
Variable xh xs : X.
Variable h Cc Cr S L : R.

(** Consistency: the smooth solution, sampled, leaves a discrete residual of
    order h^2 ([node_consistent] is this for the radial residual), and its
    reconstruction a continuum residual of order h^2. *)
Hypothesis consistency : dres xs <= Cc * h * h.
Hypothesis rec_consistency : cres xs <= Cr * h * h.
(** Stability on the gauge-fixed quotient: the distance to the discrete
    solution is bounded by S times the discrete residual. *)
Hypothesis stability : dist xs xh <= S * dres xs.
(** The continuum residual moves by at most L times the distance. *)
Hypothesis lipschitz : cres xh <= cres xs + L * dist xs xh.
Hypothesis HS : 0 <= S.
Hypothesis HL : 0 <= L.

Theorem lax : cres xh <= (Cr + L * S * Cc) * h * h.
Proof using All.
  assert (H1 : dist xs xh <= S * (Cc * h * h)).
  { eapply Rle_trans. exact stability. apply Rmult_le_compat_l. exact HS. exact consistency. }
  assert (H2 : L * dist xs xh <= L * (S * (Cc * h * h))) by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

End Lax.

(** Over a family of spacings, the same hypotheses at every h below h0 give
    the second-order bound Hypotheses.discretization_is_consistent asks of
    the certified residual. *)
Theorem lax_second_order :
  forall (X : Type) (dist : X -> X -> R) (dres cres : X -> R)
         (xh xs : R -> X) (Cc Cr S L h0 : R),
  0 < h0 -> 0 <= S -> 0 <= L -> 0 < Cr + L * S * Cc ->
  (forall h, 0 < h < h0 ->
     dres (xs h) <= Cc * h * h /\ cres (xs h) <= Cr * h * h /\
     dist (xs h) (xh h) <= S * dres (xs h) /\
     cres (xh h) <= cres (xs h) + L * dist (xs h) (xh h)) ->
  discretization_is_consistent (fun h => cres (xh h)).
Proof.
  intros X dist dres cres xh xs Cc Cr S L h0 Hh0 HS HL HC Hfam.
  exists (Cr + L * S * Cc), h0. split. exact HC. split. exact Hh0.
  intros h Hh. destruct (Hfam h Hh) as [H1 [H2 [H3 H4]]].
  exact (lax X dist dres cres (xh h) (xs h) h Cc Cr S L H1 H2 H3 H4 HS HL).
Qed.
