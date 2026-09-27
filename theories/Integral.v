(** Kernel-checked surface integrals, for every state of a box.

    Quad.v proves the midpoint rule for one cell and the sum over a tiling,
    each from hypotheses about real functions, and the driver strings them
    together. Here the whole chain is one checker and one theorem: a [true]
    verdict of [check_int] proves that, for every state whose inputs lie in a
    box, the integral over a rectangle of two slots of one residual component
    exists and lies in the interval [int_total] returns.

    The rectangle is tiled by cells of equal half-widths. Each cell carries
    claimed bounds on the second derivative of the component along each slot
    and on its first derivative along the second, over the cell and over the
    whole box of states; the checker verifies them by interval evaluation of
    the derivative bindings of Deriv.v, and the cell contributes the value at
    its centre times its area, widened by the error [Quad.iterated_encloses]
    charges. The centre value is itself an interval over the box of states,
    since the state is not fixed.

    Two derivative environments are used, one along each slot, rather than one
    carrying both, so [CellLines2] restates [Quad.CellLines] for two families
    that agree on the value slot. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Quad Box.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The iterated rule from two derivative families                    *)

Section CellLines2.

Variable EU EV : R -> R -> env ExtendedR.
Variable n ndu nddu ndv nddv : nat.
Variable cu hu cv hv Muu Mvv Dv : R.

Hypothesis Hhu : 0 <= hu.
Hypothesis Hhv : 0 <= hv.

(** The two families carry the same value in the component's slot. *)
Hypothesis Hsame : forall u v, eget n (EU u v) Xnan = eget n (EV u v) Xnan.

Definition cval2 (u v : R) : R := proj_val (eget n (EU u v) Xnan).

Hypothesis HU1 : forall v t,
  Xderive_pt (slot_along (fun s => EU s v) n) (Xreal t) (eget ndu (EU t v) Xnan).
Hypothesis HU2 : forall v t,
  Xderive_pt (slot_along (fun s => EU s v) ndu) (Xreal t) (eget nddu (EU t v) Xnan).
Hypothesis HV1 : forall u t,
  Xderive_pt (slot_along (fun s => EV u s) n) (Xreal t) (eget ndv (EV u t) Xnan).
Hypothesis HV2 : forall u t,
  Xderive_pt (slot_along (fun s => EV u s) ndv) (Xreal t) (eget nddv (EV u t) Xnan).

Hypothesis HbU2 : forall u v,
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  exists d, eget nddu (EU u v) Xnan = Xreal d /\ Rabs d <= Muu.
Hypothesis HbV2 : forall v, cv - hv <= v <= cv + hv ->
  exists d, eget nddv (EV cu v) Xnan = Xreal d /\ Rabs d <= Mvv.
Hypothesis HbV1 : forall u v,
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  exists d, eget ndv (EV u v) Xnan = Xreal d /\ Rabs d <= Dv.

Lemma cval2_V : forall u v, cval2 u v = proj_val (eget n (EV u v) Xnan).
Proof. intros u v. unfold cval2. now rewrite Hsame. Qed.

Lemma inner_line2 :
  forall v, cv - hv <= v <= cv + hv ->
  ex_RInt (fun u => cval2 u v) (cu - hu) (cu + hu) /\
  Rabs (RInt (fun u => cval2 u v) (cu - hu) (cu + hu) - 2 * hu * cval2 cu v)
  <= 2 * Muu * hu * hu * hu.
Proof using All.
  intros v Hv. split.
  - exact (sharp_ex_RInt (fun s => EU s v) n ndu nddu Muu cu hu Hhu
             (HU1 v) (HU2 v) (fun t Ht => HbU2 t v Ht Hv)).
  - exact (midpoint_sharp (fun s => EU s v) n ndu nddu Muu cu hu Hhu
             (HU1 v) (HU2 v) (fun t Ht => HbU2 t v Ht Hv)).
Qed.

Lemma outer_line2 :
  ex_RInt (fun v => cval2 cu v) (cv - hv) (cv + hv) /\
  Rabs (RInt (fun v => cval2 cu v) (cv - hv) (cv + hv) - 2 * hv * cval2 cu cv)
  <= 2 * Mvv * hv * hv * hv.
Proof using All.
  assert (Hex := sharp_ex_RInt (fun s => EV cu s) n ndv nddv Mvv cv hv Hhv
                   (HV1 cu) (HV2 cu) HbV2).
  assert (Hmid := midpoint_sharp (fun s => EV cu s) n ndv nddv Mvv cv hv Hhv
                    (HV1 cu) (HV2 cu) HbV2).
  assert (Heq : forall v, cval2 cu v = sphi (fun s => EV cu s) n v).
  { intros v. rewrite cval2_V. reflexivity. }
  split.
  - apply (ex_RInt_ext (sphi (fun s => EV cu s) n)).
    + intros x _. symmetry. apply Heq.
    + exact Hex.
  - rewrite (RInt_ext (fun v => cval2 cu v) (sphi (fun s => EV cu s) n))
      by (intros x _; apply Heq).
    rewrite (Heq cv). exact Hmid.
Qed.

Lemma cell_Dv_nonneg2 : 0 <= Dv.
Proof using All.
  destruct (HbV1 cu cv ltac:(lra) ltac:(lra)) as [d [_ Hd]].
  generalize (Rabs_pos d). lra.
Qed.

Lemma inner_ex_RInt2 :
  ex_RInt (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu))
          (cv - hv) (cv + hv).
Proof using All.
  assert (HDv := cell_Dv_nonneg2).
  apply (lipschitz_ex_RInt _ (2 * hu * Dv)). lra.
  { replace (2 * hu * Dv) with ((2 * hu) * Dv) by ring.
    apply Rmult_le_pos. lra. exact HDv. }
  intros v1 v2 H1 H2.
  destruct (inner_line2 v1 H1) as [Hex1 _].
  destruct (inner_line2 v2 H2) as [Hex2 _].
  assert (HD : is_RInt (fun u => cval2 u v1 - cval2 u v2)
                 (cu - hu) (cu + hu)
                 (RInt (fun u => cval2 u v1) (cu - hu) (cu + hu)
                  - RInt (fun u => cval2 u v2) (cu - hu) (cu + hu))).
  { replace (RInt (fun u => cval2 u v1) (cu - hu) (cu + hu)
             - RInt (fun u => cval2 u v2) (cu - hu) (cu + hu))
      with (minus (RInt (fun u => cval2 u v1) (cu - hu) (cu + hu))
                  (RInt (fun u => cval2 u v2) (cu - hu) (cu + hu)))
      by reflexivity.
    apply (is_RInt_minus (fun u => cval2 u v1) (fun u => cval2 u v2)).
    - exact (RInt_correct _ _ _ Hex1).
    - exact (RInt_correct _ _ _ Hex2). }
  assert (HexD : ex_RInt (fun u => cval2 u v1 - cval2 u v2)
                   (cu - hu) (cu + hu)) by (eexists; exact HD).
  assert (Hpt : forall u, cu - hu <= u <= cu + hu ->
            Rabs (cval2 u v1 - cval2 u v2) <= Dv * Rabs (v1 - v2)).
  { intros u Hu.
    destruct (bound_between_dist (fun s => EV u s) n ndv Dv
                (cv - hv) (cv + hv) v2 v1 (HV1 u)
                (fun t Ht => HbV1 u t Hu Ht) H2 H1)
      as [w0 [w1 [Hw0 [Hw1 Hinc]]]].
    rewrite !cval2_V. rewrite Hw0, Hw1. simpl. exact Hinc. }
  assert (Hb := RInt_le_const (fun u => cval2 u v1 - cval2 u v2)
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
  destruct (Rcase_abs (cval2 x v1 - cval2 x v2)); lra.
Qed.

(** The iterated midpoint rule over one cell, from the two families, with
    the integrability of every line of the cell along the first slot. *)
Theorem cell_iterated2 :
  (forall v, cv - hv <= v <= cv + hv ->
     ex_RInt (fun u => cval2 u v) (cu - hu) (cu + hu)) /\
  ex_RInt (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu))
          (cv - hv) (cv + hv) /\
  Rabs (RInt (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu))
             (cv - hv) (cv + hv)
        - 4 * hu * hv * cval2 cu cv)
  <= 4 * Muu * hu * hu * hu * hv + 4 * Mvv * hu * hv * hv * hv.
Proof using All.
  split. { intros v Hv. exact (proj1 (inner_line2 v Hv)). }
  split. exact inner_ex_RInt2.
  apply (iterated_encloses cval2
           (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu))
           cu hu cv hv Muu Mvv Hhu Hhv).
  - intros v Hv. split. reflexivity. exact (proj2 (inner_line2 v Hv)).
  - exact inner_ex_RInt2.
  - exact (proj1 outer_line2).
  - exact (proj2 outer_line2).
Qed.

End CellLines2.

(* ---------------------------------------------------------------- *)
(* The two families of a residual component                          *)

Section SurfaceFamilies.

Variable su sv : nat.
Hypothesis Huv : su <> sv.

Variable base len : nat.
Variable binds : list binding.
Hypothesis Hsu : (su < base)%nat.
Hypothesis Hsv : (sv < base)%nat.
Hypothesis Hlen0 : (0 < len)%nat.
Hypothesis Hwf : well_formed base binds = true.
Hypothesis Hlen : len = length binds.

(** The state: every input real, nothing above the inputs set. *)
Variable X : env ExtendedR.
Hypothesis HXu : forall k, (base <= k)%nat -> eget k X Xnan = Xnan.
Hypothesis HXr : forall k, (k < base)%nat -> exists v, eget k X Xnan = Xreal v.

Variable n : nat.
Hypothesis Hbn : (base <= n)%nat.
Hypothesis Hnl : (n < base + len)%nat.

(** The point (u, v) of the surface, after the bindings. *)
Definition surf (u v : R) : env ExtendedR :=
  xextend (eset su (eset sv X (Xreal v)) (Xreal u)) binds.

(** The environment along the first slot, carrying two derivative levels,
    and the one along the second. *)
Definition EUs (u v : R) : env ExtendedR :=
  F2 base len binds su (eset sv X (Xreal v)) u.
Definition EVs (u v : R) : env ExtendedR :=
  F2 base len binds sv (eset su X (Xreal u)) v.

(** The component as a real function of the point. *)
Definition fsurf (u v : R) : R := proj_val (eget n (surf u v) Xnan).

Lemma EUs_inv2 :
  forall v, inv2 su base len (F2 base len binds su (eset sv X (Xreal v))) (base + len).
Proof using All.
  intros v.
  destruct (eset_inputs X base sv v Hsv (conj HXu HXr)) as [Hu Hr].
  exact (inv2_of base len binds su _ Hsu Hlen0 Hwf Hlen Hu Hr).
Qed.

Lemma EVs_inv2 :
  forall u, inv2 sv base len (F2 base len binds sv (eset su X (Xreal u))) (base + len).
Proof using All.
  intros u.
  destruct (eset_inputs X base su u Hsu (conj HXu HXr)) as [Hu Hr].
  exact (inv2_of base len binds sv _ Hsv Hlen0 Hwf Hlen Hu Hr).
Qed.

(** Below the derivative levels both families hold the plain bindings. *)
Lemma EUs_values :
  forall u v k, (k < base + len)%nat -> eget k (EUs u v) Xnan = eget k (surf u v) Xnan.
Proof using All.
  intros u v k Hk. unfold EUs, F2, surf.
  apply (values_with_derivs2 su base len binds _ _ base Hwf); try lia.
  intros j _. reflexivity.
Qed.

Lemma EVs_values :
  forall u v k, (k < base + len)%nat -> eget k (EVs u v) Xnan = eget k (surf u v) Xnan.
Proof using All.
  intros u v k Hk. unfold EVs, F2, surf.
  rewrite (eset_comm _ sv su) by (intros H; apply Huv; now symmetry).
  apply (values_with_derivs2 sv base len binds _ _ base Hwf); try lia.
  intros j _. reflexivity.
Qed.

Lemma surf_same : forall u v, eget n (EUs u v) Xnan = eget n (EVs u v) Xnan.
Proof using All. intros u v. now rewrite EUs_values, EVs_values. Qed.

Lemma surf_HU :
  (forall v t, Xderive_pt (slot_along (fun s => EUs s v) n) (Xreal t)
                 (eget (n + len) (EUs t v) Xnan)) /\
  (forall v t, Xderive_pt (slot_along (fun s => EUs s v) (n + len)) (Xreal t)
                 (eget (n + 2 * len) (EUs t v) Xnan)).
Proof using All.
  split; intros v t;
    destruct (deriv2_slots base len binds su (eset sv X (Xreal v)) n Hsu Hbn
                (EUs_inv2 v)) as [H1 H2].
  - exact (H1 t).
  - exact (H2 t).
Qed.

Lemma surf_HV :
  (forall u t, Xderive_pt (slot_along (fun s => EVs u s) n) (Xreal t)
                 (eget (n + len) (EVs u t) Xnan)) /\
  (forall u t, Xderive_pt (slot_along (fun s => EVs u s) (n + len)) (Xreal t)
                 (eget (n + 2 * len) (EVs u t) Xnan)).
Proof using All.
  split; intros u t;
    destruct (deriv2_slots base len binds sv (eset su X (Xreal u)) n Hsv Hbn
                (EVs_inv2 u)) as [H1 H2].
  - exact (H1 t).
  - exact (H2 t).
Qed.

Lemma cval2_fsurf :
  forall u v, cval2 EUs n u v = fsurf u v.
Proof using All.
  intros u v. unfold cval2, fsurf. now rewrite EUs_values.
Qed.

(** One cell, stated for [fsurf]: every line along the first slot is
    integrable, the cell integral exists, and it is within the iterated rule's
    error of the centre value times the area. *)
Theorem surf_cell :
  forall cu hu cv hv Muu Mvv Dv,
  0 <= hu -> 0 <= hv ->
  (forall u v, cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
     exists d, eget (n + 2 * len) (EUs u v) Xnan = Xreal d /\ Rabs d <= Muu) ->
  (forall v, cv - hv <= v <= cv + hv ->
     exists d, eget (n + 2 * len) (EVs cu v) Xnan = Xreal d /\ Rabs d <= Mvv) ->
  (forall u v, cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
     exists d, eget (n + len) (EVs u v) Xnan = Xreal d /\ Rabs d <= Dv) ->
  (forall v, cv - hv <= v <= cv + hv ->
     ex_RInt (fun u => fsurf u v) (cu - hu) (cu + hu)) /\
  ex_RInt (fun v => RInt (fun u => fsurf u v) (cu - hu) (cu + hu))
          (cv - hv) (cv + hv) /\
  Rabs (RInt (fun v => RInt (fun u => fsurf u v) (cu - hu) (cu + hu))
             (cv - hv) (cv + hv)
        - 4 * hu * hv * fsurf cu cv)
  <= 4 * Muu * hu * hu * hu * hv + 4 * Mvv * hu * hv * hv * hv.
Proof using All.
  intros cu hu cv hv Muu Mvv Dv Hhu Hhv HbU2 HbV2 HbV1.
  destruct surf_HU as [HU1 HU2]. destruct surf_HV as [HV1 HV2].
  destruct (cell_iterated2 EUs EVs n (n + len) (n + 2 * len) (n + len) (n + 2 * len)
              cu hu cv hv Muu Mvv Dv Hhu Hhv surf_same HU1 HU2 HV1 HV2
              HbU2 HbV2 HbV1) as [Hlines [Hex Hb]].
  assert (Hinner : forall v,
            RInt (fun u => cval2 EUs n u v) (cu - hu) (cu + hu)
            = RInt (fun u => fsurf u v) (cu - hu) (cu + hu)).
  { intros v. apply RInt_ext. intros x _. apply cval2_fsurf. }
  split.
  { intros v Hv. apply (ex_RInt_ext (fun u => cval2 EUs n u v)).
    - intros x _. apply cval2_fsurf.
    - exact (Hlines v Hv). }
  split.
  - apply (ex_RInt_ext (fun v => RInt (fun u => cval2 EUs n u v) (cu - hu) (cu + hu))).
    + intros x _. apply Hinner.
    + exact Hex.
  - rewrite <- (RInt_ext (fun v => RInt (fun u => cval2 EUs n u v) (cu - hu) (cu + hu)))
      by (intros x _; apply Hinner).
    rewrite <- cval2_fsurf. exact Hb.
Qed.

End SurfaceFamilies.

(* ---------------------------------------------------------------- *)
(* Summing a tiling exactly                                          *)

Lemma rsum_ext_lt :
  forall (g g' : nat -> R) N,
  (forall j, (j < N)%nat -> g j = g' j) -> rsum g N = rsum g' N.
Proof.
  intros g g' N H. induction N as [|N IH]; simpl. reflexivity.
  rewrite IH by (intros j Hj; apply H; lia). rewrite H by lia. reflexivity.
Qed.

(** The left-nested sum of Quad.v is the right fold of the same terms. *)
Lemma fold_right_Rplus_shift :
  forall (l : list R) c, fold_right Rplus c l = fold_right Rplus 0 l + c.
Proof.
  induction l as [|x l IH]; intros c; simpl. ring. rewrite IH. ring.
Qed.

Lemma fold_seq_rsum :
  forall (g : nat -> R) N, fold_right Rplus 0 (map g (seq 0 N)) = rsum g N.
Proof.
  intros g N. induction N as [|N IH]. reflexivity.
  rewrite seq_S, map_app, fold_right_app. simpl.
  rewrite fold_right_Rplus_shift, IH. ring.
Qed.

Lemma nth_map_seq :
  forall (g : nat -> R) N k, (k < N)%nat -> nth k (map g (seq 0 N)) 0 = g k.
Proof.
  intros g N k Hk.
  rewrite (nth_indep _ 0 (g O)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

(** A point of a closed interval, from the open one RInt_ext hands over. *)
Lemma interior_closed :
  forall a b x, a <= b -> Rmin a b < x < Rmax a b -> a <= x <= b.
Proof.
  intros a b x Hab Hx. rewrite Rmin_left, Rmax_right in Hx by exact Hab. lra.
Qed.

(** The integral over the whole tiling is the double sum of the cell
    integrals. Integrability along the first slot is needed only inside the
    rectangle, row by row. *)
Lemma tiling2_rows :
  forall (f : R -> R -> R) au hu av hv NU NV,
  0 <= hv ->
  (forall i j v, (i < NU)%nat -> (j < NV)%nat ->
     av + 2 * INR j * hv <= v <= av + 2 * INR (S j) * hv ->
     ex_RInt (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu)) ->
  (forall i j, (i < NU)%nat -> (j < NV)%nat ->
     ex_RInt (ucell f au hu i) (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)) ->
  ex_RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
          av (av + 2 * INR NV * hv) /\
  RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
       av (av + 2 * INR NV * hv)
  = rsum (fun j => rsum (fun i => RInt (ucell f au hu i)
                                   (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv))
                        NU) NV.
Proof.
  intros f au hu av hv NU NV Hhv Hex_u Hex_v.
  set (G := fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu)).
  assert (Hord : forall j, av + 2 * INR j * hv <= av + 2 * INR (S j) * hv).
  { intros j. rewrite S_INR. nra. }
  (* inside row j the inner integral is the sum of the cells of the row *)
  assert (Hrow : forall j v, (j < NV)%nat ->
            av + 2 * INR j * hv <= v <= av + 2 * INR (S j) * hv ->
            G v = rsum (fun i => ucell f au hu i v) NU).
  { intros j v Hj Hv. unfold G.
    apply (proj2 (rsum_chasles (fun u => f u v) au hu NU
                    (fun i Hi => Hex_u i j v Hi Hj Hv))). }
  assert (Hj : forall j, (j < NV)%nat ->
            ex_RInt G (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv) /\
            RInt G (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)
            = rsum (fun i => RInt (ucell f au hu i) (av + 2 * INR j * hv)
                                            (av + 2 * INR (S j) * hv)) NU).
  { intros j Hjn.
    destruct (rsum_RInt_swap (fun i => ucell f au hu i)
                (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv) NU
                (fun i Hi => Hex_v i j Hi Hjn)) as [Hex Heq].
    split.
    - apply (ex_RInt_ext (fun v => rsum (fun i => ucell f au hu i v) NU)).
      + intros x Hx. symmetry. apply (Hrow j x Hjn).
        exact (interior_closed _ _ _ (Hord j) Hx).
      + exact Hex.
    - rewrite (RInt_ext G (fun v => rsum (fun i => ucell f au hu i v) NU)).
      + exact Heq.
      + intros x Hx. apply (Hrow j x Hjn).
        exact (interior_closed _ _ _ (Hord j) Hx). }
  destruct (rsum_chasles G av hv NV (fun j Hjn => proj1 (Hj j Hjn))) as [HexG HeqG].
  split. exact HexG.
  change (RInt G av (av + 2 * INR NV * hv)
          = rsum (fun j => rsum (fun i => RInt (ucell f au hu i)
                                   (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv))
                                NU) NV).
  rewrite HeqG. apply rsum_ext_lt. intros j Hjn. exact (proj2 (Hj j Hjn)).
Qed.

(* ---------------------------------------------------------------- *)
(* The certificate                                                   *)

Open Scope Z_scope.

(** Per cell, the three claimed bounds: the second derivative along the
    first slot, along the second, and the first derivative along the second,
    each N * 2^q. *)
Record ibounds := IBounds {
  ib_Nuu : Z ; ib_quu : Z ;
  ib_Nvv : Z ; ib_qvv : Z ;
  ib_Ndv : Z ; ib_qdv : Z }.

Definition ib0 : ibounds := IBounds 0 0 0 0 0 0.

(** The state box, the two integration slots, the component, the first cell
    edge and the half-width along each slot, and the cells, row j running
    along the second slot and column i along the first. Cell (i, j) is
    centred at mantissas au + (2i+1) du and av + (2j+1) dv. *)
Record icert := ICert {
  ic_prec : Z ;
  ic_cfg : pconfig ;
  ic_modes : list (Z * Z) ;
  ic_es : list Z ;
  ic_ms : list Z ;
  ic_ds : list Z ;
  ic_su : nat ; ic_sv : nat ;
  ic_comp : nat ;
  ic_au : Z ; ic_du : Z ;
  ic_av : Z ; ic_dv : Z ;
  ic_rows : list (list ibounds) }.

Definition iprec_of (c : icert) : F.precision := F.PtoP (Z.to_pos (ic_prec c)).

Definition ires (c : icert) : residual3 :=
  residual (ic_es c) (ic_cfg c) (ic_modes c).

Definition ibase (c : icert) : nat :=
  base_scratch_of (pc_lasym (ic_cfg c)) (pc_out (ic_cfg c)) (length (ic_modes c)).

(** The component the certificate integrates. *)
Definition icomp (r3 : residual3) (k : nat) : expr :=
  match k with O => r_s r3 | 1%nat => r_u r3 | _ => r_v r3 end.

(** The error bound of a cell, as an expression with exact integer
    coefficients: 4 Muu du^3 dv + 4 Mvv du dv^3. *)
Definition ierr_e (du dv : Z) (b : ibounds) : expr :=
  Eadd (Emul (EfromZ (4 * du * du * du * dv)) (eps_e (ib_Nuu b) (ib_quu b)))
       (Emul (EfromZ (4 * du * dv * dv * dv)) (eps_e (ib_Nvv b) (ib_qvv b))).

(** The box environment of a cell and the one at its centre, both over the
    whole box of states. *)
Definition icell_box (prec : F.precision) (W : env I.type) (su sv : nat)
    (mu mv du dv : Z) : env I.type :=
  eset su (eset sv W (slot_box prec mv dv)) (slot_box prec mu du).

Definition icell_centre (prec : F.precision) (W : env I.type) (su sv : nat)
    (mu mv : Z) : env I.type :=
  eset su (eset sv W (I.fromZ prec mv)) (I.fromZ prec mu).

(** The derivative checks of one cell. *)
Definition check_icell (prec : F.precision) (W : env I.type) (su sv len n : nat)
    (wu wv : list binding) (mu mv du dv : Z) (b : ibounds) : bool :=
  let IB := icell_box prec W su sv mu mv du dv in
  let envu := iextend prec IB wu in
  let envv := iextend prec IB wv in
  check1 prec envu (Evar (n + 2 * len)) (ib_Nuu b) (ib_quu b) &&
  check1 prec envv (Evar (n + 2 * len)) (ib_Nvv b) (ib_qvv b) &&
  check1 prec envv (Evar (n + len)) (ib_Ndv b) (ib_qdv b).

(** What one cell contributes to the integral. *)
Definition icell_contrib (prec : F.precision) (W : env I.type) (su sv n : nat)
    (binds : list binding) (mu mv du dv : Z) (b : ibounds) : I.type :=
  let V := ieval prec (iextend prec (icell_centre prec W su sv mu mv) binds) (Evar n) in
  let E := ieval prec eempty (ierr_e du dv b) in
  I.add prec (I.mul prec (I.fromZ prec (4 * du * dv)) V) (I.join (I.neg E) E).

(** Centre mantissa of cell i along a slot. *)
Definition icentre (a d : Z) (i : nat) : Z := a + (2 * Z.of_nat i + 1) * d.

(** The cells of one row, with their column index. *)
Fixpoint row_check (prec : F.precision) (W : env I.type) (su sv len n : nat)
    (wu wv : list binding) (au du mv dv : Z) (i : nat) (row : list ibounds)
    : bool :=
  match row with
  | [] => true
  | b :: tl =>
      check_icell prec W su sv len n wu wv (icentre au du i) mv du dv b &&
      row_check prec W su sv len n wu wv au du mv dv (S i) tl
  end.

Fixpoint row_contribs (prec : F.precision) (W : env I.type) (su sv n : nat)
    (binds : list binding) (au du mv dv : Z) (i : nat) (row : list ibounds)
    : list I.type :=
  match row with
  | [] => []
  | b :: tl =>
      icell_contrib prec W su sv n binds (icentre au du i) mv du dv b
      :: row_contribs prec W su sv n binds au du mv dv (S i) tl
  end.

Fixpoint rows_check (prec : F.precision) (W : env I.type) (su sv len n : nat)
    (wu wv : list binding) (au du av dv : Z) (NU : nat) (j : nat)
    (rows : list (list ibounds)) : bool :=
  match rows with
  | [] => true
  | row :: tl =>
      Nat.eqb (length row) NU &&
      row_check prec W su sv len n wu wv au du (icentre av dv j) dv 0 row &&
      rows_check prec W su sv len n wu wv au du av dv NU (S j) tl
  end.

Fixpoint rows_contribs (prec : F.precision) (W : env I.type) (su sv n : nat)
    (binds : list binding) (au du av dv : Z) (j : nat)
    (rows : list (list ibounds)) : list I.type :=
  match rows with
  | [] => []
  | row :: tl =>
      isum prec (row_contribs prec W su sv n binds au du (icentre av dv j) dv 0 row)
      :: rows_contribs prec W su sv n binds au du av dv (S j) tl
  end.

(** The number of cells along each slot. *)
Definition inu (c : icert) : nat :=
  match ic_rows c with [] => O | row :: _ => length row end.

Definition inv_rows (c : icert) : nat := length (ic_rows c).

(** The whole check. The derivative-doubled bindings are built once. *)
Definition check_int (c : icert) : bool :=
  let prec := iprec_of c in
  let r3 := ires c in
  let binds := r_binds r3 in
  let base := ibase c in
  let len := length binds in
  let su := ic_su c in let sv := ic_sv c in
  let W := wide_ienv prec (ic_ms c) (ic_ds c) in
  match slot_of (icomp r3 (ic_comp c)) with
  | None => false
  | Some n =>
      let wu := with_derivs2 su base len binds in
      let wv := with_derivs2 sv base len binds in
      Nat.eqb (length (ic_ms c)) base &&
      negb (Nat.eqb su sv) && Nat.ltb su base && Nat.ltb sv base &&
      Nat.ltb 0 len && well_formed base binds &&
      Nat.leb base n && Nat.ltb n (base + len) &&
      Z.leb 0 (ic_du c) && Z.leb 0 (ic_dv c) &&
      rows_check prec W su sv len n wu wv (ic_au c) (ic_du c) (ic_av c) (ic_dv c)
                 (inu c) 0 (ic_rows c)
  end.

(** The enclosure of the integral a passing certificate proves. *)
Definition int_total (c : icert) : I.type :=
  let prec := iprec_of c in
  let r3 := ires c in
  let binds := r_binds r3 in
  let W := wide_ienv prec (ic_ms c) (ic_ds c) in
  match slot_of (icomp r3 (ic_comp c)) with
  | None => I.nai
  | Some n =>
      isum prec (rows_contribs prec W (ic_su c) (ic_sv c) n binds
                   (ic_au c) (ic_du c) (ic_av c) (ic_dv c) 0 (ic_rows c))
  end.

Close Scope Z_scope.

(** The integrand at a state: the component at the point (u, v) of the two
    slots, every other input taken from the state. *)
Definition int_fun (c : icert) (xs : list R) (u v : R) : R :=
  let r3 := ires c in
  match slot_of (icomp r3 (ic_comp c)) with
  | None => 0
  | Some n =>
      proj_val (eget n (xextend (eset (ic_su c) (eset (ic_sv c) (xenv_R xs) (Xreal v))
                                      (Xreal u))
                                (r_binds r3)) Xnan)
  end.

(** The integral over the tiled rectangle, in mantissa units of the two
    slots. *)
Definition int_value (c : icert) (xs : list R) : R :=
  RInt (fun v => RInt (fun u => int_fun c xs u v)
                      (IZR (ic_au c)) (IZR (ic_au c) + 2 * INR (inu c) * IZR (ic_du c)))
       (IZR (ic_av c)) (IZR (ic_av c) + 2 * INR (inv_rows c) * IZR (ic_dv c)).

Definition int_exists (c : icert) (xs : list R) : Prop :=
  ex_RInt (fun v => RInt (fun u => int_fun c xs u v)
                         (IZR (ic_au c)) (IZR (ic_au c) + 2 * INR (inu c) * IZR (ic_du c)))
          (IZR (ic_av c)) (IZR (ic_av c) + 2 * INR (inv_rows c) * IZR (ic_dv c)).

(* ---------------------------------------------------------------- *)
(* Soundness                                                         *)

(** The cell box contains every point of the cell at every state of the
    box, and the centre environment contains the centre. *)
Lemma icell_box_ok :
  forall prec W X su sv mu mv du dv u v,
  env_ok W X ->
  IZR (mu - du) <= u <= IZR (mu + du) ->
  IZR (mv - dv) <= v <= IZR (mv + dv) ->
  env_ok (icell_box prec W su sv mu mv du dv) (eset su (eset sv X (Xreal v)) (Xreal u)).
Proof.
  intros prec W X su sv mu mv du dv u v HW Hu Hv.
  unfold icell_box. apply env_ok_eset.
  - apply env_ok_eset. exact HW. now apply slot_box_correct.
  - now apply slot_box_correct.
Qed.

Lemma icell_centre_ok :
  forall prec W X su sv mu mv,
  env_ok W X ->
  env_ok (icell_centre prec W su sv mu mv)
         (eset su (eset sv X (Xreal (IZR mv))) (Xreal (IZR mu))).
Proof.
  intros prec W X su sv mu mv HW.
  unfold icell_centre. apply env_ok_eset.
  - apply env_ok_eset. exact HW. apply I.fromZ_correct.
  - apply I.fromZ_correct.
Qed.

(** The edges of cell i along a slot. *)
Lemma icentre_edges :
  forall a d i,
  IZR (icentre a d i) - IZR d = IZR a + 2 * INR i * IZR d /\
  IZR (icentre a d i) + IZR d = IZR a + 2 * INR (S i) * IZR d.
Proof.
  intros a d i. unfold icentre.
  rewrite plus_IZR, mult_IZR, plus_IZR, mult_IZR, <- INR_IZR_INZ, S_INR.
  split; ring.
Qed.

(** An error interval: the join of a bound's negation and itself contains
    every real within the bound. *)
Lemma join_neg_correct :
  forall E err e,
  contains (I.convert E) (Xreal err) -> Rabs e <= err ->
  contains (I.convert (I.join (I.neg E) E)) (Xreal e).
Proof.
  intros E err e HE He.
  apply (contains_between _ (- err) err).
  - apply I.join_correct. left.
    change (Xreal (- err)) with (Xneg (Xreal err)).
    now apply I.neg_correct.
  - apply I.join_correct. right. exact HE.
  - assert (H1 := Rle_abs e).
    assert (H2 : - e <= Rabs e) by (rewrite <- Rabs_Ropp; apply Rle_abs).
    lra.
Qed.

Lemma xeval_ierr :
  forall du dv b,
  xeval eempty (ierr_e du dv b)
  = Xreal (IZR (4 * du * du * du * dv) * (IZR (ib_Nuu b) * powerRZ 2 (ib_quu b))
           + IZR (4 * du * dv * dv * dv) * (IZR (ib_Nvv b) * powerRZ 2 (ib_qvv b))).
Proof. reflexivity. Qed.

Section CellSound.

Variable prec : F.precision.
Variable su sv base len n : nat.
Variable binds : list binding.
Variable ms ds : list Z.
Variable xs : list R.

Hypothesis Huv : su <> sv.
Hypothesis Hsu : (su < base)%nat.
Hypothesis Hsv : (sv < base)%nat.
Hypothesis Hlen0 : (0 < len)%nat.
Hypothesis Hwf : well_formed base binds = true.
Hypothesis Hlen : len = length binds.
Hypothesis Hbn : (base <= n)%nat.
Hypothesis Hnl : (n < base + len)%nat.
Hypothesis Hms : length ms = base.
Hypothesis Hin : in_box ms ds xs.

Lemma X_inputs :
  (forall k, (base <= k)%nat -> eget k (xenv_R xs) Xnan = Xnan) /\
  (forall k, (k < base)%nat -> exists v, eget k (xenv_R xs) Xnan = Xreal v).
Proof using All.
  apply xenv_R_inputs. destruct Hin as [Hl _]. lia.
Qed.

Lemma W_ok : env_ok (wide_ienv prec ms ds) (xenv_R xs).
Proof using All. now apply wide_env_ok. Qed.

(** One cell: a passing check and the contribution it reports enclose the
    integral over it, and every line of it along the first slot is
    integrable. *)
Lemma icell_sound :
  forall mu mv du dv b,
  (0 <= du)%Z -> (0 <= dv)%Z ->
  check_icell prec (wide_ienv prec ms ds) su sv len n (with_derivs2 su base len binds)
              (with_derivs2 sv base len binds) mu mv du dv b = true ->
  (forall v, IZR mv - IZR dv <= v <= IZR mv + IZR dv ->
     ex_RInt (fun u => fsurf su sv binds (xenv_R xs) n u v)
             (IZR mu - IZR du) (IZR mu + IZR du)) /\
  ex_RInt (fun v => RInt (fun u => fsurf su sv binds (xenv_R xs) n u v)
                         (IZR mu - IZR du) (IZR mu + IZR du))
          (IZR mv - IZR dv) (IZR mv + IZR dv) /\
  contains (I.convert (icell_contrib prec (wide_ienv prec ms ds) su sv n binds
                         mu mv du dv b))
           (Xreal (RInt (fun v => RInt (fun u => fsurf su sv binds (xenv_R xs) n u v)
                                       (IZR mu - IZR du) (IZR mu + IZR du))
                        (IZR mv - IZR dv) (IZR mv + IZR dv))).
Proof using All.
  intros mu mv du dv b Hdu Hdv Hchk.
  set (X := xenv_R xs).
  set (W := wide_ienv prec ms ds).
  unfold check_icell in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hdv1].
  apply andb_prop in Hchk. destruct Hchk as [Hduu Hdvv].
  destruct X_inputs as [HXu HXr].
  set (Muu := IZR (ib_Nuu b) * powerRZ 2 (ib_quu b)).
  set (Mvv := IZR (ib_Nvv b) * powerRZ 2 (ib_qvv b)).
  set (Dv := IZR (ib_Ndv b) * powerRZ 2 (ib_qdv b)).
  assert (Hhu : 0 <= IZR du) by (apply IZR_le; exact Hdu).
  assert (Hhv : 0 <= IZR dv) by (apply IZR_le; exact Hdv).
  assert (Hcell_u : forall u, IZR mu - IZR du <= u <= IZR mu + IZR du ->
            IZR (mu - du) <= u <= IZR (mu + du)).
  { intros u Hu. rewrite minus_IZR, plus_IZR. exact Hu. }
  assert (Hcell_v : forall v, IZR mv - IZR dv <= v <= IZR mv + IZR dv ->
            IZR (mv - dv) <= v <= IZR (mv + dv)).
  { intros v Hv. rewrite minus_IZR, plus_IZR. exact Hv. }
  (* the three derivative bounds over the cell, from the interval checks *)
  assert (HbU2 : forall u v, IZR mu - IZR du <= u <= IZR mu + IZR du ->
            IZR mv - IZR dv <= v <= IZR mv + IZR dv ->
            exists d, eget (n + 2 * len) (EUs su sv base len binds X u v) Xnan = Xreal d
                      /\ Rabs d <= Muu).
  { intros u v Hu Hv.
    assert (Henv := iextend_correct prec (with_derivs2 su base len binds) _ _
                      (icell_box_ok prec W X su sv mu mv du dv u v W_ok
                         (Hcell_u u Hu) (Hcell_v v Hv))).
    destruct (check1_correct _ _ _ _ _ _ Henv Hduu) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  assert (HbV : forall u v, IZR mu - IZR du <= u <= IZR mu + IZR du ->
            IZR mv - IZR dv <= v <= IZR mv + IZR dv ->
            env_ok (iextend prec (icell_box prec W su sv mu mv du dv)
                            (with_derivs2 sv base len binds))
                   (EVs su sv base len binds X u v)).
  { intros u v Hu Hv. unfold EVs, F2.
    apply iextend_correct.
    rewrite (eset_comm _ sv su) by (intros H; apply Huv; now symmetry).
    exact (icell_box_ok prec W X su sv mu mv du dv u v W_ok
             (Hcell_u u Hu) (Hcell_v v Hv)). }
  assert (HbV2 : forall v, IZR mv - IZR dv <= v <= IZR mv + IZR dv ->
            exists d, eget (n + 2 * len) (EVs su sv base len binds X (IZR mu) v) Xnan
                      = Xreal d /\ Rabs d <= Mvv).
  { intros v Hv.
    assert (Hu : IZR mu - IZR du <= IZR mu <= IZR mu + IZR du) by lra.
    destruct (check1_correct _ _ _ _ _ _ (HbV _ _ Hu Hv) Hdvv) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  assert (HbV1 : forall u v, IZR mu - IZR du <= u <= IZR mu + IZR du ->
            IZR mv - IZR dv <= v <= IZR mv + IZR dv ->
            exists d, eget (n + len) (EVs su sv base len binds X u v) Xnan = Xreal d
                      /\ Rabs d <= Dv).
  { intros u v Hu Hv.
    destruct (check1_correct _ _ _ _ _ _ (HbV _ _ Hu Hv) Hdv1) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  destruct (surf_cell su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr
              n Hbn Hnl (IZR mu) (IZR du) (IZR mv) (IZR dv) Muu Mvv Dv Hhu Hhv
              HbU2 HbV2 HbV1)
    as [Hlines [Hex Hbound]].
  split. exact Hlines.
  split. exact Hex.
  (* the contribution: area times the centre value, widened by the error *)
  unfold icell_contrib.
  set (I0 := RInt (fun v => RInt (fun u => fsurf su sv binds X n u v)
                                 (IZR mu - IZR du) (IZR mu + IZR du))
                  (IZR mv - IZR dv) (IZR mv + IZR dv)) in *.
  set (w := fsurf su sv binds X n (IZR mu) (IZR mv)) in *.
  replace I0 with (4 * IZR du * IZR dv * w + (I0 - 4 * IZR du * IZR dv * w)) by ring.
  change (Xreal (4 * IZR du * IZR dv * w + (I0 - 4 * IZR du * IZR dv * w)))
    with (Xadd (Xreal (4 * IZR du * IZR dv * w)) (Xreal (I0 - 4 * IZR du * IZR dv * w))).
  apply I.add_correct.
  - replace (4 * IZR du * IZR dv * w) with (IZR (4 * du * dv) * w)
      by (rewrite !mult_IZR; ring).
    change (Xreal (IZR (4 * du * dv) * w))
      with (Xmul (Xreal (IZR (4 * du * dv))) (Xreal w)).
    apply I.mul_correct. apply I.fromZ_correct.
    (* the centre value is enclosed by the centre environment *)
    assert (Hc := ieval_correct prec _ _ (Evar n)
                    (iextend_correct prec binds _ _
                       (icell_centre_ok prec W X su sv mu mv W_ok))).
    unfold w, fsurf, surf. apply contains_proj. exact Hc.
  - apply (join_neg_correct _
             (IZR (4 * du * du * du * dv) * (IZR (ib_Nuu b) * powerRZ 2 (ib_quu b))
              + IZR (4 * du * dv * dv * dv) * (IZR (ib_Nvv b) * powerRZ 2 (ib_qvv b)))).
    + assert (He := ieval_correct prec eempty eempty (ierr_e du dv b) env_ok_nil).
      rewrite xeval_ierr in He. exact He.
    + replace (IZR (4 * du * du * du * dv) * (IZR (ib_Nuu b) * powerRZ 2 (ib_quu b))
               + IZR (4 * du * dv * dv * dv) * (IZR (ib_Nvv b) * powerRZ 2 (ib_qvv b)))
        with (4 * Muu * IZR du * IZR du * IZR du * IZR dv
              + 4 * Mvv * IZR du * IZR dv * IZR dv * IZR dv)
        by (unfold Muu, Mvv; rewrite !mult_IZR; ring).
      exact Hbound.
Qed.

End CellSound.

(* ---------------------------------------------------------------- *)
(* The whole certificate                                             *)

Lemma row_contribs_length :
  forall prec W su sv n binds au du mv dv i row,
  length (row_contribs prec W su sv n binds au du mv dv i row) = length row.
Proof.
  intros prec W su sv n binds au du mv dv i row. revert i.
  induction row as [|b tl IH]; intros i; simpl. reflexivity. now rewrite IH.
Qed.

Lemma row_contribs_nth :
  forall prec W su sv n binds au du mv dv row i k,
  (k < length row)%nat ->
  nth k (row_contribs prec W su sv n binds au du mv dv i row) I.nai
  = icell_contrib prec W su sv n binds (icentre au du (i + k)) mv du dv
                  (nth k row ib0).
Proof.
  intros prec W su sv n binds au du mv dv row. induction row as [|b tl IH];
    intros i k Hk; simpl in Hk. lia.
  destruct k as [|k]; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH by lia. now replace (S i + k)%nat with (i + S k)%nat by lia.
Qed.

Lemma row_check_nth :
  forall prec W su sv len n wu wv au du mv dv row i,
  row_check prec W su sv len n wu wv au du mv dv i row = true ->
  forall k, (k < length row)%nat ->
  check_icell prec W su sv len n wu wv (icentre au du (i + k)) mv du dv
              (nth k row ib0) = true.
Proof.
  intros prec W su sv len n wu wv au du mv dv row. induction row as [|b tl IH];
    intros i Hchk k Hk; simpl in Hk. lia.
  simpl in Hchk. apply andb_prop in Hchk. destruct Hchk as [H1 H2].
  destruct k as [|k]; simpl.
  - now rewrite Nat.add_0_r.
  - replace (i + S k)%nat with (S i + k)%nat by lia. apply IH. exact H2. lia.
Qed.

Lemma rows_contribs_length :
  forall prec W su sv n binds au du av dv j rows,
  length (rows_contribs prec W su sv n binds au du av dv j rows) = length rows.
Proof.
  intros prec W su sv n binds au du av dv j rows. revert j.
  induction rows as [|r tl IH]; intros j; simpl. reflexivity. now rewrite IH.
Qed.

Lemma rows_contribs_nth :
  forall prec W su sv n binds au du av dv rows j k,
  (k < length rows)%nat ->
  nth k (rows_contribs prec W su sv n binds au du av dv j rows) I.nai
  = isum prec (row_contribs prec W su sv n binds au du (icentre av dv (j + k)) dv 0
                            (nth k rows [])).
Proof.
  intros prec W su sv n binds au du av dv rows. induction rows as [|r tl IH];
    intros j k Hk; simpl in Hk. lia.
  destruct k as [|k]; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH by lia. now replace (S j + k)%nat with (j + S k)%nat by lia.
Qed.

Lemma rows_check_nth :
  forall prec W su sv len n wu wv au du av dv NU rows j,
  rows_check prec W su sv len n wu wv au du av dv NU j rows = true ->
  forall k, (k < length rows)%nat ->
  length (nth k rows []) = NU /\
  row_check prec W su sv len n wu wv au du (icentre av dv (j + k)) dv 0
            (nth k rows []) = true.
Proof.
  intros prec W su sv len n wu wv au du av dv NU rows. induction rows as [|r tl IH];
    intros j Hchk k Hk; simpl in Hk. lia.
  simpl in Hchk. apply andb_prop in Hchk. destruct Hchk as [Hchk H3].
  apply andb_prop in Hchk. destruct Hchk as [H1 H2]. apply Nat.eqb_eq in H1.
  destruct k as [|k]; simpl.
  - rewrite Nat.add_0_r. now split.
  - replace (j + S k)%nat with (S j + k)%nat by lia. apply IH. exact H3. lia.
Qed.

(** A passing certificate encloses the integral over the tiled rectangle, at
    every state of the box. *)
Theorem check_int_correct :
  forall c, check_int c = true ->
  forall xs, in_box (ic_ms c) (ic_ds c) xs ->
  int_exists c xs /\ contains (I.convert (int_total c)) (Xreal (int_value c xs)).
Proof.
  intros c Hchk xs Hin.
  unfold check_int in Hchk.
  unfold int_exists, int_value, int_total, int_fun.
  cbv zeta in Hchk |- *.
  revert Hchk.
  destruct (slot_of (icomp (ires c) (ic_comp c))) as [n|] eqn:Hn;
    intros Hchk; [|discriminate].
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
         end.
  match goal with H : Nat.eqb (length (ic_ms c)) _ = true |- _ =>
    apply Nat.eqb_eq in H; rename H into Hms end.
  match goal with H : negb (Nat.eqb (ic_su c) (ic_sv c)) = true |- _ =>
    apply negb_true_iff, Nat.eqb_neq in H; rename H into Huv end.
  match goal with H : Nat.ltb (ic_su c) _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hsu end.
  match goal with H : Nat.ltb (ic_sv c) _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hsv end.
  match goal with H : Nat.ltb 0 _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hlen0 end.
  match goal with H : well_formed _ _ = true |- _ => rename H into Hwf end.
  match goal with H : Nat.leb _ n = true |- _ =>
    apply Nat.leb_le in H; rename H into Hbn end.
  match goal with H : Nat.ltb n _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hnl end.
  match goal with H : Z.leb 0 (ic_du c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdu end.
  match goal with H : Z.leb 0 (ic_dv c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdv end.
  match goal with H : rows_check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = true |- _ =>
    rename H into Hrows end.
  set (prec := iprec_of c) in *.
  set (binds := r_binds (ires c)) in *.
  set (base := ibase c) in *.
  set (len := length binds) in *.
  set (W := wide_ienv prec (ic_ms c) (ic_ds c)) in *.
  set (f := fsurf (ic_su c) (ic_sv c) binds (xenv_R xs) n).
  set (au := IZR (ic_au c)). set (hu := IZR (ic_du c)).
  set (av := IZR (ic_av c)). set (hv := IZR (ic_dv c)).
  set (NU := inu c). set (NV := inv_rows c).
  enough (Hgoal :
    ex_RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
            av (av + 2 * INR NV * hv) /\
    contains (I.convert (isum prec (rows_contribs prec W (ic_su c) (ic_sv c) n binds
                                      (ic_au c) (ic_du c) (ic_av c) (ic_dv c) 0
                                      (ic_rows c))))
             (Xreal (RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu))
                          av (av + 2 * INR NV * hv)))) by exact Hgoal.
  assert (Hhv : 0 <= hv) by (unfold hv; apply IZR_le; exact Hdv).
  (* every cell of the tiling carries its enclosure *)
  assert (Hcell : forall i j, (i < NU)%nat -> (j < NV)%nat ->
            (forall v, av + 2 * INR j * hv <= v <= av + 2 * INR (S j) * hv ->
               ex_RInt (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu)) /\
            ex_RInt (ucell f au hu i) (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv) /\
            contains (I.convert
                        (icell_contrib prec W (ic_su c) (ic_sv c) n binds
                           (icentre (ic_au c) (ic_du c) i)
                           (icentre (ic_av c) (ic_dv c) j) (ic_du c) (ic_dv c)
                           (nth i (nth j (ic_rows c) []) ib0)))
                     (Xreal (RInt (ucell f au hu i)
                                  (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)))).
  { intros i j Hi Hj.
    destruct (rows_check_nth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrows j Hj) as [Hrl Hrow].
    rewrite Nat.add_0_l in Hrow.
    assert (Hi' : (i < length (nth j (ic_rows c) []))%nat) by (rewrite Hrl; exact Hi).
    assert (Hck := row_check_nth _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrow i Hi').
    rewrite Nat.add_0_l in Hck.
    destruct (icentre_edges (ic_au c) (ic_du c) i) as [Hul Huh].
    destruct (icentre_edges (ic_av c) (ic_dv c) j) as [Hvl Hvh].
    destruct (icell_sound prec (ic_su c) (ic_sv c) base len n binds (ic_ms c) (ic_ds c) xs
                Huv Hsu Hsv Hlen0 Hwf eq_refl Hbn Hnl Hms Hin
                (icentre (ic_au c) (ic_du c) i) (icentre (ic_av c) (ic_dv c) j)
                (ic_du c) (ic_dv c) _ Hdu Hdv Hck) as [Hlines [Hex Hcon]].
    rewrite Hul, Huh in Hlines, Hex, Hcon.
    rewrite Hvl, Hvh in Hlines, Hex, Hcon.
    split; [|split].
    - exact Hlines.
    - exact Hex.
    - exact Hcon. }
  destruct (tiling2_rows f au hu av hv NU NV Hhv
              (fun i j v Hi Hj Hv => proj1 (Hcell i j Hi Hj) v Hv)
              (fun i j Hi Hj => proj1 (proj2 (Hcell i j Hi Hj)))) as [Hext Heqt].
  split. exact Hext.
  rewrite Heqt.
  (* the nested isum encloses the nested sum *)
  rewrite <- fold_seq_rsum.
  assert (Hlr : length (rows_contribs prec W (ic_su c) (ic_sv c) n binds
                          (ic_au c) (ic_du c) (ic_av c) (ic_dv c) 0 (ic_rows c))
                = length (map (fun j => rsum (fun i => RInt (ucell f au hu i)
                                   (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)) NU)
                              (seq 0 NV))).
  { rewrite rows_contribs_length, length_map, length_seq. reflexivity. }
  apply (isum_correct prec _ _ Hlr).
  intros k Hk.
  rewrite rows_contribs_length in Hk.
  rewrite rows_contribs_nth by exact Hk.
  rewrite nth_map_seq by exact Hk.
  rewrite Nat.add_0_l.
  destruct (rows_check_nth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrows k Hk) as [Hrl _].
  rewrite <- fold_seq_rsum.
  assert (Hlc : length (row_contribs prec W (ic_su c) (ic_sv c) n binds
                          (ic_au c) (ic_du c) (icentre (ic_av c) (ic_dv c) k)
                          (ic_dv c) 0 (nth k (ic_rows c) []))
                = length (map (fun i => RInt (ucell f au hu i)
                                   (av + 2 * INR k * hv) (av + 2 * INR (S k) * hv))
                              (seq 0 NU))).
  { rewrite row_contribs_length, length_map, length_seq. exact Hrl. }
  apply (isum_correct prec _ _ Hlc).
  intros i Hi.
  rewrite row_contribs_length, Hrl in Hi.
  rewrite row_contribs_nth by (rewrite Hrl; exact Hi).
  rewrite nth_map_seq by exact Hi.
  rewrite Nat.add_0_l.
  exact (proj2 (proj2 (Hcell i k Hi Hk))).
Qed.
