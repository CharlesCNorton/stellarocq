(** Integrals over a tiling, computed and checked inside the development.

    Quad.v proves the midpoint rule over one cell from bounds on second
    derivatives ([midpoint_sharp], [cell_iterated_encloses]) and sums cells
    ([tiling_var_encloses], [tiling2_encloses]). Here the checker computes the
    whole integral itself from a node of a certificate: it lays out the cells,
    encloses the second derivatives of the three components over each cell,
    reads a bound off each enclosure and checks it there, evaluates the
    components at each centre, and adds value and error with [Cell.isum].
    [integ2_correct] and [integ1_correct] state that the interval it returns
    for each component contains the integral of that component over the
    rectangle, or over the run of cells of one plane, scaled from the mantissa
    units of the angle slots to the units of their exponents.
    [integ2_torus_correct] states the same for the integral over exactly one
    period of both angles, [0, 2 pi], from a lattice that starts at 0 and
    reaches past it: the two strips the lattice adds are bounded through the
    component's enclosures over the cells of its last column and last row
    ([torus_strips]), so the period needs no dyadic endpoint.

    The component is a function of the two angle mantissas with every other
    input slot at the node's value, [cellf]; the tiling is the checker's own,
    so no covering or partition of cells has to be believed. *)

From Coq Require Import ZArith Reals List Bool Lia Lra FunctionalExtensionality.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Interval Require Float.Basic.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Quad.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The midpoint rule over a cell from two derivative environments    *)

(** [Quad.cell_iterated_encloses] reads both angular derivatives from one
    environment. The slots [with_derivs2] builds along each angle sit at the
    same offsets, so the two directions are read from two environments that
    agree on the component. *)
Section CellLines2.

Variable EU EV : R -> R -> env ExtendedR.
Variable n nu nuu nv nvv : nat.
Variable cu hu cv hv Muu Mvv Dv : R.

Hypothesis Hhu : 0 <= hu.
Hypothesis Hhv : 0 <= hv.
Hypothesis Hsame : forall u v, eget n (EU u v) Xnan = eget n (EV u v) Xnan.

Hypothesis HU1 : forall v t,
  Xderive_pt (slot_along (fun s => EU s v) n) (Xreal t) (eget nu (EU t v) Xnan).
Hypothesis HU2 : forall v t,
  Xderive_pt (slot_along (fun s => EU s v) nu) (Xreal t) (eget nuu (EU t v) Xnan).
Hypothesis HV1 : forall u t,
  Xderive_pt (slot_along (fun s => EV u s) n) (Xreal t) (eget nv (EV u t) Xnan).
Hypothesis HV2 : forall u t,
  Xderive_pt (slot_along (fun s => EV u s) nv) (Xreal t) (eget nvv (EV u t) Xnan).

Hypothesis HbU2 : forall u v,
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  exists d, eget nuu (EU u v) Xnan = Xreal d /\ Rabs d <= Muu.
Hypothesis HbV2 : forall v, cv - hv <= v <= cv + hv ->
  exists d, eget nvv (EV cu v) Xnan = Xreal d /\ Rabs d <= Mvv.
Hypothesis HbV1 : forall u v,
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  exists d, eget nv (EV u v) Xnan = Xreal d /\ Rabs d <= Dv.

Definition cval2 (u v : R) : R := proj_val (eget n (EU u v) Xnan).

Lemma cval2_ev : forall u v, cval2 u v = proj_val (eget n (EV u v) Xnan).
Proof. intros u v. unfold cval2. now rewrite Hsame. Qed.

Lemma inner_line2 :
  forall v, cv - hv <= v <= cv + hv ->
  ex_RInt (fun u => cval2 u v) (cu - hu) (cu + hu) /\
  Rabs (RInt (fun u => cval2 u v) (cu - hu) (cu + hu) - 2 * hu * cval2 cu v)
  <= 2 * Muu * hu * hu * hu.
Proof.
  intros v Hv. split.
  - exact (sharp_ex_RInt (fun s => EU s v) n nu nuu Muu cu hu Hhu
             (HU1 v) (HU2 v) (fun t Ht => HbU2 t v Ht Hv)).
  - exact (midpoint_sharp (fun s => EU s v) n nu nuu Muu cu hu Hhu
             (HU1 v) (HU2 v) (fun t Ht => HbU2 t v Ht Hv)).
Qed.

Lemma outer_line2 :
  ex_RInt (fun v => cval2 cu v) (cv - hv) (cv + hv) /\
  Rabs (RInt (fun v => cval2 cu v) (cv - hv) (cv + hv) - 2 * hv * cval2 cu cv)
  <= 2 * Mvv * hv * hv * hv.
Proof.
  pose proof (sharp_ex_RInt (fun s => EV cu s) n nv nvv Mvv cv hv Hhv (HV1 cu) (HV2 cu) HbV2) as Hex.
  pose proof (midpoint_sharp (fun s => EV cu s) n nv nvv Mvv cv hv Hhv (HV1 cu) (HV2 cu) HbV2) as Hmid.
  assert (Hpt : forall v, cval2 cu v = sphi (fun s => EV cu s) n v).
  { intros v. rewrite cval2_ev. reflexivity. }
  split.
  - apply (ex_RInt_ext (sphi (fun s => EV cu s) n)); [intros x _; symmetry; apply Hpt | exact Hex].
  - rewrite (RInt_ext (fun v => cval2 cu v) (sphi (fun s => EV cu s) n)) by (intros x _; apply Hpt).
    rewrite (Hpt cv). exact Hmid.
Qed.

Lemma cell2_Dv_nonneg : 0 <= Dv.
Proof.
  destruct (HbV1 cu cv ltac:(lra) ltac:(lra)) as [d [_ Hd]].
  generalize (Rabs_pos d). lra.
Qed.

Lemma inner_ex_RInt2 :
  ex_RInt (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu)) (cv - hv) (cv + hv).
Proof.
  assert (HDv := cell2_Dv_nonneg).
  apply (lipschitz_ex_RInt _ (2 * hu * Dv)). lra.
  { apply Rmult_le_pos; [lra | exact HDv]. }
  intros v1 v2 H1 H2.
  destruct (inner_line2 v1 H1) as [Hex1 _].
  destruct (inner_line2 v2 H2) as [Hex2 _].
  assert (HD : is_RInt (fun u => cval2 u v1 - cval2 u v2) (cu - hu) (cu + hu)
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
  assert (HexD : ex_RInt (fun u => cval2 u v1 - cval2 u v2) (cu - hu) (cu + hu))
    by (eexists; exact HD).
  assert (Hpt : forall u, cu - hu <= u <= cu + hu ->
            Rabs (cval2 u v1 - cval2 u v2) <= Dv * Rabs (v1 - v2)).
  { intros u Hu.
    destruct (bound_between_dist (fun s => EV u s) n nv Dv (cv - hv) (cv + hv) v2 v1 (HV1 u)
                (fun t Ht => HbV1 u t Hu Ht) H2 H1) as [w0 [w1 [Hw0 [Hw1 Hinc]]]].
    rewrite !cval2_ev. rewrite Hw0, Hw1. simpl. exact Hinc. }
  assert (Hb := RInt_le_const (fun u => cval2 u v1 - cval2 u v2) (cu - hu) (cu + hu)
                  (Dv * Rabs (v1 - v2)) ltac:(lra) HexD).
  rewrite (is_RInt_unique _ _ _ _ HD) in Hb.
  replace (cu + hu - (cu - hu)) with (2 * hu) in Hb by ring.
  replace (2 * hu * Dv * Rabs (v1 - v2)) with (2 * hu * (Dv * Rabs (v1 - v2))) by ring.
  apply Hb.
  intros x Hx. cbv beta.
  assert (H := Hpt x ltac:(lra)).
  set (KK := Dv * Rabs (v1 - v2)) in *.
  unfold Rabs in H. destruct (Rcase_abs (cval2 x v1 - cval2 x v2)); lra.
Qed.

(** The same over any part [a', b'] of the cell's first range, which is what
    a period ending inside the last cell of a lattice needs. *)
Lemma inner_ex_RInt2_sub :
  forall a' b', cu - hu <= a' <= b' -> b' <= cu + hu ->
  ex_RInt (fun v => RInt (fun u => cval2 u v) a' b') (cv - hv) (cv + hv).
Proof.
  intros a' b' Ha Hb.
  assert (HDv := cell2_Dv_nonneg).
  assert (Hsub : forall v, cv - hv <= v <= cv + hv -> ex_RInt (fun u => cval2 u v) a' b').
  { intros v Hv. destruct (inner_line2 v Hv) as [Hex _].
    apply (ex_RInt_Chasles_2 (V := R_CompleteNormedModule) (fun u => cval2 u v) (cu - hu) a' b');
      [lra |].
    apply (ex_RInt_Chasles_1 (V := R_CompleteNormedModule) (fun u => cval2 u v) (cu - hu) b' (cu + hu));
      [lra | exact Hex]. }
  apply (lipschitz_ex_RInt _ ((b' - a') * Dv)). lra.
  { apply Rmult_le_pos; [lra | exact HDv]. }
  intros v1 v2 H1 H2.
  pose proof (Hsub v1 H1) as Hex1. pose proof (Hsub v2 H2) as Hex2.
  assert (HD : is_RInt (fun u => cval2 u v1 - cval2 u v2) a' b'
                 (RInt (fun u => cval2 u v1) a' b' - RInt (fun u => cval2 u v2) a' b')).
  { replace (RInt (fun u => cval2 u v1) a' b' - RInt (fun u => cval2 u v2) a' b')
      with (minus (RInt (fun u => cval2 u v1) a' b') (RInt (fun u => cval2 u v2) a' b'))
      by reflexivity.
    apply (is_RInt_minus (fun u => cval2 u v1) (fun u => cval2 u v2)).
    - exact (RInt_correct _ _ _ Hex1).
    - exact (RInt_correct _ _ _ Hex2). }
  assert (HexD : ex_RInt (fun u => cval2 u v1 - cval2 u v2) a' b') by (eexists; exact HD).
  assert (Hpt : forall u, a' <= u <= b' ->
            Rabs (cval2 u v1 - cval2 u v2) <= Dv * Rabs (v1 - v2)).
  { intros u Hu.
    destruct (bound_between_dist (fun s => EV u s) n nv Dv (cv - hv) (cv + hv) v2 v1 (HV1 u)
                (fun t Ht => HbV1 u t ltac:(lra) Ht) H2 H1) as [w0 [w1 [Hw0 [Hw1 Hinc]]]].
    rewrite !cval2_ev. rewrite Hw0, Hw1. simpl. exact Hinc. }
  assert (Hb' := RInt_le_const (fun u => cval2 u v1 - cval2 u v2) a' b'
                   (Dv * Rabs (v1 - v2)) ltac:(lra) HexD).
  rewrite (is_RInt_unique _ _ _ _ HD) in Hb'.
  replace ((b' - a') * Dv * Rabs (v1 - v2)) with ((b' - a') * (Dv * Rabs (v1 - v2))) by ring.
  apply Hb'.
  intros x Hx. cbv beta.
  assert (H := Hpt x ltac:(lra)).
  set (KK := Dv * Rabs (v1 - v2)) in *.
  unfold Rabs in H. destruct (Rcase_abs (cval2 x v1 - cval2 x v2)); lra.
Qed.

Theorem cell2_encloses :
  Rabs (RInt (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu)) (cv - hv) (cv + hv)
        - 4 * hu * hv * cval2 cu cv)
  <= 4 * Muu * hu * hu * hu * hv + 4 * Mvv * hu * hv * hv * hv.
Proof.
  apply (iterated_encloses cval2 (fun v => RInt (fun u => cval2 u v) (cu - hu) (cu + hu))
           cu hu cv hv Muu Mvv Hhu Hhv).
  - intros v Hv. split. reflexivity. exact (proj2 (inner_line2 v Hv)).
  - exact inner_ex_RInt2.
  - exact (proj1 outer_line2).
  - exact (proj2 outer_line2).
Qed.

End CellLines2.

(* ---------------------------------------------------------------- *)
(* One cell of a certificate                                         *)

Section Cells.

Variable slot_u slot_v : nat.
Hypothesis Huv : slot_u <> slot_v.

(** The component at the angle mantissas u and v, every other input at the
    node's value. *)
Definition cellf (binds : list binding) (n : nat) (ms : list Z) (u v : R) : R :=
  proj_val (eget n (xextend (cell_env slot_u slot_v ms u v) binds) Xnan).

(** The environments of the two derivative directions: the derivatives along
    the first angle at a fixed second angle, and the other way round. *)
Definition EUf (base len : nat) (binds : list binding) (ms : list Z) (u v : R) : env ExtendedR :=
  F2 base len binds slot_u (eset slot_v (xenv_of ms) (Xreal v)) u.
Definition EVf (base len : nat) (binds : list binding) (ms : list Z) (u v : R) : env ExtendedR :=
  F2 base len binds slot_v (eset slot_u (xenv_of ms) (Xreal u)) v.

(** The interval environments over a cell centred at (cu, cv), in the two
    nestings the derivative environments use. *)
Definition box_uv (prec : F.precision) (ms : list Z) (cu du cv dv : Z) : env I.type :=
  eset slot_u (eset slot_v (ienv_of prec ms) (slot_box prec cv dv)) (slot_box prec cu du).
Definition box_vu (prec : F.precision) (ms : list Z) (cu du cv dv : Z) : env I.type :=
  eset slot_v (eset slot_u (ienv_of prec ms) (slot_box prec cu du)) (slot_box prec cv dv).

Lemma box_uv_ok :
  forall prec ms cu du cv dv u v,
  (IZR (cu - du) <= u <= IZR (cu + du)) -> (IZR (cv - dv) <= v <= IZR (cv + dv)) ->
  env_ok (box_uv prec ms cu du cv dv) (eset slot_u (eset slot_v (xenv_of ms) (Xreal v)) (Xreal u)).
Proof.
  intros prec ms cu du cv dv u v Hu Hv. unfold box_uv.
  apply env_ok_eset; [apply env_ok_eset; [apply env_ok_fromZ | now apply slot_box_correct] |].
  now apply slot_box_correct.
Qed.

Lemma box_vu_ok :
  forall prec ms cu du cv dv u v,
  (IZR (cu - du) <= u <= IZR (cu + du)) -> (IZR (cv - dv) <= v <= IZR (cv + dv)) ->
  env_ok (box_vu prec ms cu du cv dv) (eset slot_v (eset slot_u (xenv_of ms) (Xreal u)) (Xreal v)).
Proof.
  intros prec ms cu du cv dv u v Hu Hv. unfold box_vu.
  apply env_ok_eset; [apply env_ok_eset; [apply env_ok_fromZ | now apply slot_box_correct] |].
  now apply slot_box_correct.
Qed.

(** One angle set and the rest at the node: nothing above the inputs is set
    and every input is real. *)
Lemma set1_facts :
  forall ms base x a, length ms = base -> (x < base)%nat ->
  (forall k, (base <= k)%nat -> eget k (eset x (xenv_of ms) (Xreal a)) Xnan = Xnan) /\
  (forall k, (k < base)%nat -> exists r, eget k (eset x (xenv_of ms) (Xreal a)) Xnan = Xreal r).
Proof.
  intros ms base x a Hlen Hx. split.
  - intros k Hk. rewrite eget_eset_neq by lia. unfold xenv_of. rewrite eget_of_list.
    apply nth_overflow. rewrite length_map. lia.
  - intros k Hk. destruct (Nat.eq_dec k x) as [-> | Hkx].
    + rewrite eget_eset_eq. now exists a.
    + rewrite eget_eset_neq by exact Hkx. rewrite (nth_xenv_of slot_u slot_v) by lia. now eexists.
Qed.

Section Node.

Variables (base len : nat) (binds : list binding) (ms : list Z) (n : nat).
Hypothesis Hms : length ms = base.
Hypothesis Hbu : (slot_u < base)%nat.
Hypothesis Hbv : (slot_v < base)%nat.
Hypothesis Hlen0 : (0 < len)%nat.
Hypothesis Hwf : well_formed base binds = true.
Hypothesis Hlen : len = length binds.
Hypothesis Hbn : (base <= n)%nat.
Hypothesis Hnl : (n < base + len)%nat.

Lemma EU_derivs :
  (forall v t, Xderive_pt (slot_along (fun s => EUf base len binds ms s v) n) (Xreal t)
                 (eget (n + len) (EUf base len binds ms t v) Xnan)) /\
  (forall v t, Xderive_pt (slot_along (fun s => EUf base len binds ms s v) (n + len)) (Xreal t)
                 (eget (n + 2 * len) (EUf base len binds ms t v) Xnan)).
Proof.
  split; intros v t;
    destruct (set1_facts ms base slot_v v Hms Hbv) as [Hun Hre];
    pose proof (inv2_of base len binds slot_u _ Hbu Hlen0 Hwf Hlen Hun Hre) as Hinv;
    destruct (deriv2_slots base len binds slot_u _ n Hbu Hbn Hinv) as [H1 H2].
  - exact (H1 t).
  - exact (H2 t).
Qed.

Lemma EV_derivs :
  (forall u t, Xderive_pt (slot_along (fun s => EVf base len binds ms u s) n) (Xreal t)
                 (eget (n + len) (EVf base len binds ms u t) Xnan)) /\
  (forall u t, Xderive_pt (slot_along (fun s => EVf base len binds ms u s) (n + len)) (Xreal t)
                 (eget (n + 2 * len) (EVf base len binds ms u t) Xnan)).
Proof.
  split; intros u t;
    destruct (set1_facts ms base slot_u u Hms Hbu) as [Hun Hre];
    pose proof (inv2_of base len binds slot_v _ Hbv Hlen0 Hwf Hlen Hun Hre) as Hinv;
    destruct (deriv2_slots base len binds slot_v _ n Hbv Hbn Hinv) as [H1 H2].
  - exact (H1 t).
  - exact (H2 t).
Qed.

(** Both derivative environments carry the component itself at its slot. *)
Lemma EU_value : forall u v,
  eget n (EUf base len binds ms u v) Xnan = eget n (xextend (cell_env slot_u slot_v ms u v) binds) Xnan.
Proof.
  intros u v. unfold EUf, F2.
  apply (values_with_derivs2 slot_u base len binds _ _ base Hwf); try lia.
  intros k _. reflexivity.
Qed.

Lemma EV_value : forall u v,
  eget n (EVf base len binds ms u v) Xnan = eget n (xextend (cell_env slot_u slot_v ms u v) binds) Xnan.
Proof.
  intros u v. unfold EVf, F2.
  apply (values_with_derivs2 slot_v base len binds _ _ base Hwf); try lia.
  intros k _. unfold cell_env.
  destruct (Nat.eq_dec k slot_u) as [-> | Hku].
  - rewrite eget_eset_neq by exact Huv. rewrite !eget_eset_eq. reflexivity.
  - destruct (Nat.eq_dec k slot_v) as [-> | Hkv].
    + rewrite eget_eset_eq. rewrite eget_eset_neq by (intros E; apply Huv; now symmetry).
      rewrite eget_eset_eq. reflexivity.
    + rewrite !eget_eset_neq by assumption. reflexivity.
Qed.

Lemma cellf_EU : forall u v, cellf binds n ms u v = cval2 (EUf base len binds ms) n u v.
Proof. intros u v. unfold cellf, cval2. now rewrite EU_value. Qed.

(** The bounds on the second derivatives over the box and on the first
    derivative along the second angle, checked. *)
Definition checks2 (prec : F.precision) (cu hu cv hv Nuu quu Nvv qvv Nd qd : Z) : bool :=
  check1 prec (iextend prec (box_uv prec ms cu hu cv hv) (with_derivs2 slot_u base len binds))
    (Evar (n + 2 * len)) Nuu quu &&
  check1 prec (iextend prec (box_vu prec ms cu hu cv hv) (with_derivs2 slot_v base len binds))
    (Evar (n + 2 * len)) Nvv qvv &&
  check1 prec (iextend prec (box_vu prec ms cu hu cv hv) (with_derivs2 slot_v base len binds))
    (Evar (n + len)) Nd qd.

Theorem cell2_cert :
  forall prec cu hu cv hv Nuu quu Nvv qvv Nd qd,
  (0 <= hu)%Z -> (0 <= hv)%Z ->
  checks2 prec cu hu cv hv Nuu quu Nvv qvv Nd qd = true ->
  let f := cellf binds n ms in
  (forall v, IZR cv - IZR hv <= v <= IZR cv + IZR hv ->
     ex_RInt (fun u => f u v) (IZR cu - IZR hu) (IZR cu + IZR hu)) /\
  ex_RInt (fun v => RInt (fun u => f u v) (IZR cu - IZR hu) (IZR cu + IZR hu))
          (IZR cv - IZR hv) (IZR cv + IZR hv) /\
  Rabs (RInt (fun v => RInt (fun u => f u v) (IZR cu - IZR hu) (IZR cu + IZR hu))
             (IZR cv - IZR hv) (IZR cv + IZR hv)
        - 4 * IZR hu * IZR hv * f (IZR cu) (IZR cv))
  <= 4 * (IZR Nuu * powerRZ 2 quu) * IZR hu * IZR hu * IZR hu * IZR hv
     + 4 * (IZR Nvv * powerRZ 2 qvv) * IZR hu * IZR hv * IZR hv * IZR hv.
Proof.
  intros prec cu hu cv hv Nuu quu Nvv qvv Nd qd Hhu Hhv Hc f.
  unfold checks2 in Hc. apply andb_prop in Hc. destruct Hc as [Hc Hd].
  apply andb_prop in Hc. destruct Hc as [Huu Hvv].
  assert (Hhu' : 0 <= IZR hu) by (apply IZR_le; exact Hhu).
  assert (Hhv' : 0 <= IZR hv) by (apply IZR_le; exact Hhv).
  destruct EU_derivs as [HU1 HU2]. destruct EV_derivs as [HV1 HV2].
  assert (HbU2 : forall u v, IZR cu - IZR hu <= u <= IZR cu + IZR hu ->
            IZR cv - IZR hv <= v <= IZR cv + IZR hv ->
            exists d, eget (n + 2 * len) (EUf base len binds ms u v) Xnan = Xreal d /\
                      Rabs d <= IZR Nuu * powerRZ 2 quu).
  { intros u v Hu Hv.
    assert (Henv := iextend_correct prec (with_derivs2 slot_u base len binds) _ _
                      (box_uv_ok prec ms cu hu cv hv u v
                         ltac:(rewrite minus_IZR, plus_IZR; lra) ltac:(rewrite minus_IZR, plus_IZR; lra))).
    destruct (check1_correct _ _ _ _ _ _ Henv Huu) as [x [Hx Hb]].
    exists x. split; [exact Hx | exact Hb]. }
  assert (HbV2 : forall v, IZR cv - IZR hv <= v <= IZR cv + IZR hv ->
            exists d, eget (n + 2 * len) (EVf base len binds ms (IZR cu) v) Xnan = Xreal d /\
                      Rabs d <= IZR Nvv * powerRZ 2 qvv).
  { intros v Hv.
    assert (Henv := iextend_correct prec (with_derivs2 slot_v base len binds) _ _
                      (box_vu_ok prec ms cu hu cv hv (IZR cu) v
                         ltac:(rewrite minus_IZR, plus_IZR; lra) ltac:(rewrite minus_IZR, plus_IZR; lra))).
    destruct (check1_correct _ _ _ _ _ _ Henv Hvv) as [x [Hx Hb]].
    exists x. split; [exact Hx | exact Hb]. }
  assert (HbV1 : forall u v, IZR cu - IZR hu <= u <= IZR cu + IZR hu ->
            IZR cv - IZR hv <= v <= IZR cv + IZR hv ->
            exists d, eget (n + len) (EVf base len binds ms u v) Xnan = Xreal d /\
                      Rabs d <= IZR Nd * powerRZ 2 qd).
  { intros u v Hu Hv.
    assert (Henv := iextend_correct prec (with_derivs2 slot_v base len binds) _ _
                      (box_vu_ok prec ms cu hu cv hv u v
                         ltac:(rewrite minus_IZR, plus_IZR; lra) ltac:(rewrite minus_IZR, plus_IZR; lra))).
    destruct (check1_correct _ _ _ _ _ _ Henv Hd) as [x [Hx Hb]].
    exists x. split; [exact Hx | exact Hb]. }
  assert (Hsame : forall u v, eget n (EUf base len binds ms u v) Xnan = eget n (EVf base len binds ms u v) Xnan).
  { intros u v. now rewrite EU_value, EV_value. }
  assert (Ef : f = cval2 (EUf base len binds ms) n).
  { unfold f. apply functional_extensionality. intros u.
    apply functional_extensionality. intros v. apply cellf_EU. }
  rewrite Ef.
  split; [| split].
  - intros v Hv.
    exact (proj1 (inner_line2 (EUf base len binds ms) n (n + len) (n + 2 * len)
                    (IZR cu) (IZR hu) (IZR cv) (IZR hv) _ Hhu' HU1 HU2 HbU2 v Hv)).
  - exact (inner_ex_RInt2 (EUf base len binds ms) (EVf base len binds ms) n (n + len) (n + 2 * len)
             (n + len) (IZR cu) (IZR hu) (IZR cv) (IZR hv) _ _
             Hhu' Hhv' Hsame HU1 HU2 HV1 HbU2 HbV1).
  - exact (cell2_encloses (EUf base len binds ms) (EVf base len binds ms) n (n + len) (n + 2 * len)
             (n + len) (n + 2 * len) (IZR cu) (IZR hu) (IZR cv) (IZR hv) _ _ _
             Hhu' Hhv' Hsame HU1 HU2 HV1 HV2 HbU2 HbV2 HbV1).
Qed.

(** The inner integral over any part of a cell's first range is integrable
    over the cell's second range. *)
Theorem cell2_sub :
  forall prec cu hu cv hv Nuu quu Nvv qvv Nd qd a' b',
  (0 <= hu)%Z -> (0 <= hv)%Z ->
  checks2 prec cu hu cv hv Nuu quu Nvv qvv Nd qd = true ->
  IZR cu - IZR hu <= a' <= b' -> b' <= IZR cu + IZR hu ->
  let f := cellf binds n ms in
  ex_RInt (fun v => RInt (fun u => f u v) a' b') (IZR cv - IZR hv) (IZR cv + IZR hv).
Proof.
  intros prec cu hu cv hv Nuu quu Nvv qvv Nd qd a' b' Hhu Hhv Hc Ha Hb f.
  unfold checks2 in Hc. apply andb_prop in Hc. destruct Hc as [Hc Hd].
  apply andb_prop in Hc. destruct Hc as [Huu _].
  assert (Hhu' : 0 <= IZR hu) by (apply IZR_le; exact Hhu).
  assert (Hhv' : 0 <= IZR hv) by (apply IZR_le; exact Hhv).
  destruct EU_derivs as [HU1 HU2]. destruct EV_derivs as [HV1 _].
  assert (HbU2 : forall u v, IZR cu - IZR hu <= u <= IZR cu + IZR hu ->
            IZR cv - IZR hv <= v <= IZR cv + IZR hv ->
            exists d, eget (n + 2 * len) (EUf base len binds ms u v) Xnan = Xreal d /\
                      Rabs d <= IZR Nuu * powerRZ 2 quu).
  { intros u v Hu Hv.
    assert (Henv := iextend_correct prec (with_derivs2 slot_u base len binds) _ _
                      (box_uv_ok prec ms cu hu cv hv u v
                         ltac:(rewrite minus_IZR, plus_IZR; lra) ltac:(rewrite minus_IZR, plus_IZR; lra))).
    destruct (check1_correct _ _ _ _ _ _ Henv Huu) as [x [Hx Hbx]].
    exists x. split; [exact Hx | exact Hbx]. }
  assert (HbV1 : forall u v, IZR cu - IZR hu <= u <= IZR cu + IZR hu ->
            IZR cv - IZR hv <= v <= IZR cv + IZR hv ->
            exists d, eget (n + len) (EVf base len binds ms u v) Xnan = Xreal d /\
                      Rabs d <= IZR Nd * powerRZ 2 qd).
  { intros u v Hu Hv.
    assert (Henv := iextend_correct prec (with_derivs2 slot_v base len binds) _ _
                      (box_vu_ok prec ms cu hu cv hv u v
                         ltac:(rewrite minus_IZR, plus_IZR; lra) ltac:(rewrite minus_IZR, plus_IZR; lra))).
    destruct (check1_correct _ _ _ _ _ _ Henv Hd) as [x [Hx Hbx]].
    exists x. split; [exact Hx | exact Hbx]. }
  assert (Hsame : forall u v, eget n (EUf base len binds ms u v) Xnan = eget n (EVf base len binds ms u v) Xnan).
  { intros u v. now rewrite EU_value, EV_value. }
  assert (Ef : f = cval2 (EUf base len binds ms) n).
  { unfold f. apply functional_extensionality. intros u.
    apply functional_extensionality. intros v. apply cellf_EU. }
  rewrite Ef.
  exact (inner_ex_RInt2_sub (EUf base len binds ms) (EVf base len binds ms) n (n + len) (n + 2 * len)
           (n + len) (IZR cu) (IZR hu) (IZR cv) (IZR hv) _ _
           Hhu' Hhv' Hsame HU1 HU2 HV1 HbU2 HbV1 a' b' Ha Hb).
Qed.

(** A bound on the component over a whole cell, read off its enclosure
    there. *)
Lemma box_bound :
  forall prec cu hu cv hv N q u v,
  check1 prec (iextend prec (box_uv prec ms cu hu cv hv) binds) (Evar n) N q = true ->
  IZR (cu - hu) <= u <= IZR (cu + hu) -> IZR (cv - hv) <= v <= IZR (cv + hv) ->
  Rabs (cellf binds n ms u v) <= IZR N * powerRZ 2 q.
Proof.
  intros prec cu hu cv hv N q u v Hc Hu Hv.
  assert (Henv := iextend_correct prec binds _ _ (box_uv_ok prec ms cu hu cv hv u v Hu Hv)).
  destruct (check1_correct _ _ _ _ _ _ Henv Hc) as [x [Hx Hb]].
  change (xeval (xextend (eset slot_u (eset slot_v (xenv_of ms) (Xreal v)) (Xreal u)) binds) (Evar n))
    with (eget n (xextend (cell_env slot_u slot_v ms u v) binds) Xnan) in Hx.
  unfold cellf. rewrite Hx. exact Hb.
Qed.

(** One cell of a curve at a fixed second angle: the claimed bound on the
    second derivative along the first angle over the cell, checked. *)
Definition checks1 (prec : F.precision) (cu hu cv Nuu quu : Z) : bool :=
  check1 prec (iextend prec (box_uv prec ms cu hu cv 0) (with_derivs2 slot_u base len binds))
    (Evar (n + 2 * len)) Nuu quu.

Theorem cell1_cert :
  forall prec cu hu cv Nuu quu,
  (0 <= hu)%Z -> checks1 prec cu hu cv Nuu quu = true ->
  let f := fun u => cellf binds n ms u (IZR cv) in
  ex_RInt f (IZR cu - IZR hu) (IZR cu + IZR hu) /\
  Rabs (RInt f (IZR cu - IZR hu) (IZR cu + IZR hu) - 2 * IZR hu * f (IZR cu))
  <= 2 * (IZR Nuu * powerRZ 2 quu) * IZR hu * IZR hu * IZR hu.
Proof.
  intros prec cu hu cv Nuu quu Hhu Hc f.
  assert (Hhu' : 0 <= IZR hu) by (apply IZR_le; exact Hhu).
  destruct EU_derivs as [HU1 HU2].
  assert (Hb : forall t, IZR cu - IZR hu <= t <= IZR cu + IZR hu ->
            exists d, eget (n + 2 * len) (EUf base len binds ms t (IZR cv)) Xnan = Xreal d /\
                      Rabs d <= IZR Nuu * powerRZ 2 quu).
  { intros t Ht.
    assert (Henv := iextend_correct prec (with_derivs2 slot_u base len binds) _ _
                      (box_uv_ok prec ms cu hu cv 0 t (IZR cv)
                         ltac:(rewrite minus_IZR, plus_IZR; lra)
                         ltac:(rewrite Z.sub_0_r, Z.add_0_r; lra))).
    destruct (check1_correct _ _ _ _ _ _ Henv Hc) as [x [Hx Hbx]].
    exists x. split; [exact Hx | exact Hbx]. }
  assert (Ef : f = sphi (fun s => EUf base len binds ms s (IZR cv)) n).
  { unfold f. apply functional_extensionality. intros u. rewrite cellf_EU. reflexivity. }
  rewrite Ef. split.
  - exact (sharp_ex_RInt _ n (n + len) (n + 2 * len) _ (IZR cu) (IZR hu) Hhu' (HU1 (IZR cv)) (HU2 (IZR cv)) Hb).
  - exact (midpoint_sharp _ n (n + len) (n + 2 * len) _ (IZR cu) (IZR hu) Hhu' (HU1 (IZR cv)) (HU2 (IZR cv)) Hb).
Qed.

(** An interval that contains an extended real contains the real it
    projects to. *)
Lemma contains_proj : forall X x, contains X x -> contains X (Xreal (proj_val x)).
Proof. intros [| l u] [| y] H; simpl in *; auto; contradiction. Qed.

(** The component at the centre of a cell, enclosed. *)
Lemma centre_val :
  forall prec cu cv,
  contains (I.convert (ieval prec (iextend prec (box_uv prec ms cu 0 cv 0) binds) (Evar n)))
           (Xreal (cellf binds n ms (IZR cu) (IZR cv))).
Proof.
  intros prec cu cv.
  assert (Henv := iextend_correct prec binds _ _
                    (box_uv_ok prec ms cu 0 cv 0 (IZR cu) (IZR cv)
                       ltac:(rewrite Z.sub_0_r, Z.add_0_r; lra)
                       ltac:(rewrite Z.sub_0_r, Z.add_0_r; lra))).
  pose proof (ieval_correct prec _ _ (Evar n) Henv) as H. simpl in H.
  unfold cellf. apply contains_proj. exact H.
Qed.

End Node.

End Cells.

(* ---------------------------------------------------------------- *)
(* Sums                                                              *)

Lemma isum_map :
  forall prec (A : Type) (xs : list A) (fI : A -> I.type) (fR : A -> R),
  (forall a, In a xs -> contains (I.convert (fI a)) (Xreal (fR a))) ->
  contains (I.convert (isum prec (map fI xs))) (Xreal (fold_right Rplus 0 (map fR xs))).
Proof.
  intros prec A xs fI fR H. induction xs as [| a xs IH]; simpl.
  - lra.
  - change (Xreal (fR a + fold_right Rplus 0 (map fR xs)))
      with (Xadd (Xreal (fR a)) (Xreal (fold_right Rplus 0 (map fR xs)))).
    apply I.add_correct.
    + apply H. left. reflexivity.
    + apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma fold_plus_init : forall l c, fold_right Rplus c l = fold_right Rplus 0 l + c.
Proof. induction l as [| x l IH]; intros c; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fold_map_seq : forall (g : nat -> R) N, fold_right Rplus 0 (map g (seq 0 N)) = rsum g N.
Proof.
  intros g N. induction N as [| N IH]; [reflexivity |].
  rewrite seq_S, map_app, fold_right_app. simpl. rewrite fold_plus_init, IH. ring.
Qed.

(** The cells of an NU by NV lattice, row by row of the second angle. *)
Definition grid (NU NV : nat) : list (nat * nat) :=
  flat_map (fun j => map (fun i => (i, j)) (seq 0 NU)) (seq 0 NV).

Lemma fold_grid :
  forall (g : nat * nat -> R) NU NV,
  fold_right Rplus 0 (map g (grid NU NV)) = rsum (fun j => rsum (fun i => g (i, j)) NU) NV.
Proof.
  intros g NU NV. unfold grid. induction NV as [| NV IH]; [reflexivity |].
  rewrite seq_S, flat_map_app, map_app, fold_right_app. simpl. rewrite app_nil_r.
  rewrite fold_plus_init, IH, map_map, fold_map_seq. reflexivity.
Qed.

Lemma in_grid : forall NU NV i j, (i < NU)%nat -> (j < NV)%nat -> In (i, j) (grid NU NV).
Proof.
  intros NU NV i j Hi Hj. unfold grid. apply in_flat_map. exists j.
  split; [apply in_seq; lia |]. apply in_map_iff. exists i. split; [reflexivity | apply in_seq; lia].
Qed.

Lemma grid_in : forall NU NV i j, In (i, j) (grid NU NV) -> (i < NU)%nat /\ (j < NV)%nat.
Proof.
  intros NU NV i j H. unfold grid in H. apply in_flat_map in H. destruct H as [j' [Hj' H]].
  apply in_map_iff in H. destruct H as [i' [E Hi']]. injection E as <- <-.
  apply in_seq in Hj'. apply in_seq in Hi'. lia.
Qed.

(** The centre of cell i of a lattice from a with half-width h. *)
Definition ctr (a h : Z) (i : nat) : Z := a + (2 * Z.of_nat i + 1) * h.

Lemma ctr_lo : forall a h i, IZR (ctr a h i) - IZR h = IZR a + 2 * INR i * IZR h.
Proof. intros a h i. unfold ctr. rewrite plus_IZR, mult_IZR, plus_IZR, mult_IZR, <- INR_IZR_INZ. ring. Qed.

Lemma ctr_hi : forall a h i, IZR (ctr a h i) + IZR h = IZR a + 2 * INR (S i) * IZR h.
Proof. intros a h i. unfold ctr. rewrite plus_IZR, mult_IZR, plus_IZR, mult_IZR, <- INR_IZR_INZ, S_INR. ring. Qed.

(** A point of a lattice's range lies in one of its cells. *)
Lemma find_cell :
  forall a h N x, (0 < N)%nat -> 0 <= h -> a <= x <= a + 2 * INR N * h ->
  exists j, (j < N)%nat /\ a + 2 * INR j * h <= x <= a + 2 * INR (S j) * h.
Proof.
  intros a h N x HN Hh. induction N as [| m IH]; [lia |]. intros Hx.
  destruct (Nat.eq_dec m 0) as [-> | Hm].
  - exists 0%nat. split; [lia |]. simpl INR in *. lra.
  - destruct (Rle_dec x (a + 2 * INR m * h)) as [Hle | Hgt].
    + assert (H0 : a <= a + 2 * INR m * h) by (pose proof (pos_INR m); nra).
      destruct (IH ltac:(lia) ltac:(lra)) as [j [Hj Hjx]]. exists j. split; [lia | exact Hjx].
    + exists m. split; [lia | lra].
Qed.

(** The enclosure of an integral from the sum of the rules S and the sum of
    their errors E, in mantissa units, scaled by 2^k. *)
Definition widen (prec : F.precision) (S E : I.type) (k : Z) : I.type :=
  I.mul prec (I.add prec S (I.join (I.neg E) E)) (ieval prec eempty (Epow2 k)).

(** A sum s with error at most e encloses the integral I, widened by the
    error and scaled by 2^k. *)
Lemma widen_scale :
  forall prec S E (s e Iv : R) k,
  contains (I.convert S) (Xreal s) -> contains (I.convert E) (Xreal e) -> Rabs (Iv - s) <= e ->
  contains (I.convert (widen prec S E k)) (Xreal (Iv * powerRZ 2 k)).
Proof.
  intros prec S E s e Iv k HS HE Hb. unfold widen.
  assert (HJ : contains (I.convert (I.join (I.neg E) E)) (Xreal (Iv - s))).
  { apply (contains_between _ (- e) e).
    - apply I.join_correct. left. change (Xreal (- e)) with (Xneg (Xreal e)). now apply I.neg_correct.
    - apply I.join_correct. right. exact HE.
    - unfold Rabs in Hb. destruct (Rcase_abs (Iv - s)); lra. }
  assert (HA : contains (I.convert (I.add prec S (I.join (I.neg E) E))) (Xreal Iv)).
  { replace Iv with (s + (Iv - s)) by ring.
    change (Xreal (s + (Iv - s))) with (Xadd (Xreal s) (Xreal (Iv - s))).
    now apply I.add_correct. }
  assert (HP : contains (I.convert (ieval prec eempty (Epow2 k))) (Xreal (powerRZ 2 k))).
  { exact (ieval_correct prec eempty eempty (Epow2 k) env_ok_nil). }
  change (Xreal (Iv * powerRZ 2 k)) with (Xmul (Xreal Iv) (Xreal (powerRZ 2 k))).
  now apply I.mul_correct.
Qed.

(* ---------------------------------------------------------------- *)
(* One period inside a lattice                                       *)

Lemma abs_between : forall x K, Rabs x <= K -> - K <= x <= K.
Proof. intros x K H. unfold Rabs in H. destruct (Rcase_abs x); lra. Qed.

Lemma rsum_abs :
  forall (F M : nat -> R) N,
  (forall i, (i < N)%nat -> Rabs (F i) <= M i) -> Rabs (rsum F N) <= rsum M N.
Proof.
  intros F M N H.
  assert (Z0 : forall K, rsum (fun _ => 0) K = 0).
  { induction K as [| K IH]; simpl; [reflexivity | rewrite IH; ring]. }
  replace (rsum F N) with (rsum F N - rsum (fun _ => 0) N) by (rewrite Z0; ring).
  apply rsum_triang. intros i Hi. rewrite Rminus_0_r. now apply H.
Qed.

Lemma rsum_scal :
  forall (c : R) (M : nat -> R) N, rsum (fun i => c * M i) N = c * rsum M N.
Proof. intros c M N. induction N as [| N IH]; simpl; [ring | rewrite IH; ring]. Qed.

(** A lattice of NU by NV cells from (au, av) reaches past one period of each
    angle, Pu and Pv, when each period ends inside the last cell of its row.
    The integral over the period is then the integral over the lattice less
    two strips: the part of the first angle beyond its period, over the whole
    second range, and the part of the second angle beyond its period, over the
    first angle's period. Bounds on the integrand over the last column of
    cells and over the last row bound the two. *)
Section Strips.

Variable f : R -> R -> R.
Variables au hu av hv Pu Pv : R.
Variables NU NV : nat.
Variables Mcol Mrow : nat -> R.

Hypothesis HNU : (0 < NU)%nat.
Hypothesis HNV : (0 < NV)%nat.
Hypothesis Hhu : 0 <= hu.
Hypothesis Hhv : 0 <= hv.
Hypothesis HPu : 2 * INR (pred NU) * hu <= Pu <= 2 * INR NU * hu.
Hypothesis HPv : 2 * INR (pred NV) * hv <= Pv <= 2 * INR NV * hv.

Hypothesis Hex_u :
  forall i v, (i < NU)%nat -> av <= v <= av + 2 * INR NV * hv ->
  ex_RInt (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu).
Hypothesis HexI :
  ex_RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu)) av (av + 2 * INR NV * hv).
Hypothesis Hex_h :
  forall j, (j < NV)%nat ->
  ex_RInt (fun v => RInt (fun u => f u v) (au + Pu) (au + 2 * INR NU * hu))
          (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv).
Hypothesis Hcol :
  forall j u v, (j < NV)%nat ->
  au + 2 * INR (pred NU) * hu <= u <= au + 2 * INR NU * hu ->
  av + 2 * INR j * hv <= v <= av + 2 * INR (S j) * hv ->
  Rabs (f u v) <= Mcol j.
Hypothesis Hrow :
  forall i u v, (i < NU)%nat ->
  au + 2 * INR i * hu <= u <= au + 2 * INR (S i) * hu ->
  av + 2 * INR (pred NV) * hv <= v <= av + 2 * INR NV * hv ->
  Rabs (f u v) <= Mrow i.

Theorem torus_strips :
  ex_RInt (fun v => RInt (fun u => f u v) au (au + Pu)) av (av + Pv) /\
  Rabs (RInt (fun v => RInt (fun u => f u v) au (au + Pu)) av (av + Pv)
        - RInt (fun v => RInt (fun u => f u v) au (au + 2 * INR NU * hu)) av (av + 2 * INR NV * hv))
  <= (2 * INR NU * hu - Pu) * (2 * hv) * rsum Mcol NV
     + (2 * INR NV * hv - Pv) * (2 * hu * rsum Mrow NU + (2 * INR NU * hu - Pu) * Mcol (pred NV)).
Proof.
  assert (HSU : S (pred NU) = NU) by lia.
  assert (HSV : S (pred NV) = NV) by lia.
  assert (Hpu0 := pos_INR (pred NU)). assert (Hpv0 := pos_INR (pred NV)).
  set (Lu := au + 2 * INR NU * hu) in *. set (Lv := av + 2 * INR NV * hv) in *.
  set (U := au + Pu) in *. set (V := av + Pv) in *.
  set (I := fun v => RInt (fun u => f u v) au Lu) in *.
  set (g := fun v => RInt (fun u => f u v) au U) in *.
  set (h := fun v => RInt (fun u => f u v) U Lu) in *.
  assert (HaU : au <= U <= Lu) by (unfold U, Lu; nra).
  assert (HaV : av <= V <= Lv) by (unfold V, Lv; nra).
  assert (HUl : au + 2 * INR (pred NU) * hu <= U) by (unfold U; lra).
  assert (HVl : av + 2 * INR (pred NV) * hv <= V) by (unfold V; lra).
  (* every line across the lattice, and its two parts *)
  assert (Hline : forall v, av <= v <= Lv ->
            ex_RInt (fun u => f u v) au Lu /\
            I v = rsum (fun i => RInt (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu)) NU).
  { intros v Hv. exact (rsum_chasles (fun u => f u v) au hu NU (fun i Hi => Hex_u i v Hi Hv)). }
  assert (Hsplit : forall v, av <= v <= Lv ->
            ex_RInt (fun u => f u v) au U /\ ex_RInt (fun u => f u v) U Lu /\ I v = g v + h v).
  { intros v Hv. destruct (Hline v Hv) as [Hex _].
    assert (H1 : ex_RInt (fun u => f u v) au U)
      by (apply (ex_RInt_Chasles_1 (V := R_CompleteNormedModule) (fun u => f u v) au U Lu);
          [lra | exact Hex]).
    assert (H2 : ex_RInt (fun u => f u v) U Lu)
      by (apply (ex_RInt_Chasles_2 (V := R_CompleteNormedModule) (fun u => f u v) au U Lu);
          [lra | exact Hex]).
    split; [exact H1 | split; [exact H2 |]].
    unfold I, g, h.
    replace (RInt (fun u => f u v) au U + RInt (fun u => f u v) U Lu)
      with (plus (RInt (fun u => f u v) au U) (RInt (fun u => f u v) U Lu)) by reflexivity.
    symmetry. apply RInt_Chasles; assumption. }
  assert (HI : forall v, av <= v <= Lv -> I v = g v + h v)
    by (intros v Hv; exact (proj2 (proj2 (Hsplit v Hv)))).
  (* the strip beyond the first period, row by row *)
  assert (Hh : ex_RInt h av Lv /\
               RInt h av Lv = rsum (fun j => RInt h (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv)) NV)
    by exact (rsum_chasles h av hv NV Hex_h).
  assert (Hg : ex_RInt g av Lv).
  { apply (ex_RInt_ext (V := R_CompleteNormedModule) (fun v => I v - h v)).
    - intros x Hx. rewrite Rmin_left, Rmax_right in Hx by lra.
      change (I x - h x = g x). rewrite (HI x ltac:(lra)). ring.
    - exact (ex_RInt_minus (V := R_CompleteNormedModule) I h av Lv HexI (proj1 Hh)). }
  assert (HgV : ex_RInt g av V)
    by (apply (ex_RInt_Chasles_1 (V := R_CompleteNormedModule) g av V Lv); [lra | exact Hg]).
  assert (HgR : ex_RInt g V Lv)
    by (apply (ex_RInt_Chasles_2 (V := R_CompleteNormedModule) g av V Lv); [lra | exact Hg]).
  split; [exact HgV |].
  (* the lattice integral in pieces *)
  assert (HIeq : @eq R (RInt I av Lv) (RInt g av V + RInt g V Lv + RInt h av Lv)).
  { assert (E1 : RInt I av Lv = RInt (fun v => g v + h v) av Lv).
    { apply (RInt_ext (V := R_CompleteNormedModule)).
      intros x Hx. rewrite Rmin_left, Rmax_right in Hx by lra. exact (HI x ltac:(lra)). }
    assert (E2 : RInt (fun v => g v + h v) av Lv = RInt g av Lv + RInt h av Lv)
      by exact (RInt_plus (V := R_CompleteNormedModule) g h av Lv Hg (proj1 Hh)).
    assert (E3 : RInt g av V + RInt g V Lv = RInt g av Lv)
      by exact (RInt_Chasles (V := R_CompleteNormedModule) g av V Lv HgV HgR).
    rewrite E1, E2, <- E3. ring. }
  (* h on each row of cells *)
  assert (Hhb : forall j v, (j < NV)%nat -> av + 2 * INR j * hv <= v <= av + 2 * INR (S j) * hv ->
            Rabs (h v) <= (Lu - U) * Mcol j).
  { intros j v Hj Hv.
    assert (Hv' : av <= v <= Lv).
    { unfold Lv. assert (INR (S j) <= INR NV) by (apply le_INR; lia). pose proof (pos_INR j). split; nra. }
    destruct (Hsplit v Hv') as [_ [Hex2 _]].
    unfold h. apply RInt_le_const; [lra | exact Hex2 |].
    intros x Hx. apply abs_between. apply (Hcol j x v Hj); [lra | exact Hv]. }
  assert (HhI : Rabs (RInt h av Lv) <= (Lu - U) * (2 * hv) * rsum Mcol NV).
  { rewrite (proj2 Hh).
    apply (Rle_trans _ (rsum (fun j => 2 * hv * (Lu - U) * Mcol j) NV)).
    - apply rsum_abs. intros j Hj.
      assert (Hr : av + 2 * INR j * hv <= av + 2 * INR (S j) * hv) by (rewrite S_INR; nra).
      pose proof (RInt_le_const h (av + 2 * INR j * hv) (av + 2 * INR (S j) * hv) ((Lu - U) * Mcol j)
                    Hr (Hex_h j Hj)) as Hb.
      replace (2 * hv * (Lu - U) * Mcol j)
        with ((av + 2 * INR (S j) * hv - (av + 2 * INR j * hv)) * ((Lu - U) * Mcol j))
        by (rewrite S_INR; ring).
      apply Hb. intros x Hx. apply abs_between. apply (Hhb j x Hj). lra.
    - rewrite rsum_scal. apply Req_le. ring. }
  (* g beyond the second period, in the last row of cells *)
  assert (Hgb : forall v, V <= v <= Lv ->
            Rabs (g v) <= 2 * hu * rsum Mrow NU + (Lu - U) * Mcol (pred NV)).
  { intros v Hv.
    assert (Hv' : av <= v <= Lv) by lra.
    assert (Hlast : av + 2 * INR (pred NV) * hv <= v <= av + 2 * INR (S (pred NV)) * hv).
    { rewrite HSV. fold Lv. lra. }
    destruct (Hline v Hv') as [_ HIr].
    assert (HgI : @eq R (g v) (I v - h v)).
    { rewrite (HI v Hv'). unfold Rminus. rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r. reflexivity. }
    rewrite HgI.
    apply (Rle_trans _ (Rabs (I v) + Rabs (h v))).
    { unfold Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    apply Rplus_le_compat.
    - rewrite HIr.
      apply (Rle_trans _ (rsum (fun i => 2 * hu * Mrow i) NU)).
      + apply rsum_abs. intros i Hi.
        assert (Hr : au + 2 * INR i * hu <= au + 2 * INR (S i) * hu) by (rewrite S_INR; nra).
        pose proof (RInt_le_const (fun u => f u v) (au + 2 * INR i * hu) (au + 2 * INR (S i) * hu) (Mrow i)
                      Hr (Hex_u i v Hi Hv')) as Hb.
        replace (2 * hu * Mrow i) with ((au + 2 * INR (S i) * hu - (au + 2 * INR i * hu)) * Mrow i)
          by (rewrite S_INR; ring).
        apply Hb. intros x Hx. apply abs_between. apply (Hrow i x v Hi); lra.
      + rewrite rsum_scal. lra.
    - exact (Hhb (pred NV) v ltac:(lia) Hlast). }
  assert (HgR' : Rabs (RInt g V Lv) <= (Lv - V) * (2 * hu * rsum Mrow NU + (Lu - U) * Mcol (pred NV))).
  { apply RInt_le_const; [lra | exact HgR |]. intros x Hx. apply abs_between. apply Hgb. lra. }
  replace (RInt g av V - RInt I av Lv) with (- (RInt g V Lv + RInt h av Lv)) by (rewrite HIeq; ring).
  rewrite Rabs_Ropp.
  eapply Rle_trans; [apply Rabs_triang |].
  replace (2 * INR NU * hu - Pu) with (Lu - U) by (unfold Lu, U; ring).
  replace (2 * INR NV * hv - Pv) with (Lv - V) by (unfold Lv, V; ring).
  lra.
Qed.

End Strips.

(* ---------------------------------------------------------------- *)
(* A bound read off an enclosure                                     *)

(** A first guess at N 2^q above every magnitude an enclosure admits: its
    upper end as a float, with a margin for the rounding of N 2^q in the
    interval arithmetic. Below 2^-900 the guess is 2^-900, where the power of
    two is still a normal float; an unbounded enclosure gives none. *)
Definition start_of (X : I.type) : option (Z * Z) :=
  match F.toF (I.upper (I.abs X)) with
  | Basic.Fnan => None
  | Basic.Fzero => Some (1%Z, (-900)%Z)
  | Basic.Float _ m e =>
      if (e + 53 <? -900)%Z then Some (1%Z, (-900)%Z)
      else Some ((Zpos m + Zpos m / 1073741824 + 4)%Z, e)
  end.

(** The guess, grown until the test accepts it. *)
Fixpoint grow (fuel : nat) (ok : Z -> Z -> bool) (N q : Z) : option (Z * Z) :=
  match fuel with
  | O => None
  | S f => if ok N q then Some (N, q) else grow f ok (N + N / 4096 + 1)%Z q
  end.

Lemma grow_ok :
  forall fuel ok N q r, grow fuel ok N q = Some r -> ok (fst r) (snd r) = true.
Proof.
  induction fuel as [| f IH]; intros ok N q r H; [discriminate |].
  simpl in H. destruct (ok N q) eqn:Hok.
  - injection H as <-. exact Hok.
  - exact (IH _ _ _ _ H).
Qed.

(** A bound N 2^q on the magnitude of e over the environment that [check1]
    accepts. How it is found carries no weight: what is returned passed the
    check. *)
Definition claim_of (prec : F.precision) (ie : env I.type) (e : expr) : option (Z * Z) :=
  match start_of (ieval prec ie e) with
  | None => None
  | Some Nq => grow 64 (check1 prec ie e) (fst Nq) (snd Nq)
  end.

Lemma claim_of_ok :
  forall prec ie e r, claim_of prec ie e = Some r -> check1 prec ie e (fst r) (snd r) = true.
Proof.
  intros prec ie e r H. unfold claim_of in H.
  destruct (start_of (ieval prec ie e)) as [Nq |]; [| discriminate].
  exact (grow_ok _ _ _ _ _ H).
Qed.

(* ---------------------------------------------------------------- *)
(* Lists                                                             *)

(** Every entry, when every entry is there. *)
Fixpoint all_some {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | o :: tl =>
      match o, all_some tl with
      | Some a, Some r => Some (a :: r)
      | _, _ => None
      end
  end.

Lemma all_some_nth :
  forall (A : Type) (l : list (option A)) r, all_some l = Some r ->
  forall k d, (k < length l)%nat -> nth k l None = Some (nth k r d).
Proof.
  intros A l. induction l as [| o tl IH]; intros r H k d Hk; simpl in Hk; [lia |].
  simpl in H. destruct o as [a |]; [| discriminate].
  destruct (all_some tl) as [r' |] eqn:Ht; [| discriminate].
  injection H as <-.
  destruct k as [| k]; [reflexivity |].
  simpl. apply (IH r' eq_refl k d). lia.
Qed.

Definition is_some {A : Type} (o : option A) : bool :=
  match o with Some _ => true | None => false end.

Lemma nth_map_lt :
  forall (A B : Type) (f : A -> B) l k da db, (k < length l)%nat ->
  nth k (map f l) db = f (nth k l da).
Proof.
  intros A B f l k da db Hk.
  rewrite (nth_indep (map f l) db (f da)) by (rewrite length_map; exact Hk).
  apply map_nth.
Qed.

Lemma nth_seq_map :
  forall (A : Type) (f : nat -> A) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk.
  rewrite (nth_map_lt _ _ f (seq 0 n) k 0%nat d) by (rewrite length_seq; exact Hk).
  rewrite seq_nth by exact Hk. reflexivity.
Qed.

Lemma forallb_map_in :
  forall (A B : Type) (p : B -> bool) (g : A -> B) l x,
  forallb p (map g l) = true -> In x l -> p (g x) = true.
Proof.
  intros A B p g l x H Hx. rewrite forallb_forall in H. apply H. apply in_map. exact Hx.
Qed.

Lemma combine_map :
  forall (A B : Type) (g : A -> B) l, combine l (map g l) = map (fun x => (x, g x)) l.
Proof.
  intros A B g l. induction l as [| x l IH]; [reflexivity |]. simpl. rewrite IH. reflexivity.
Qed.

Lemma last_map_d :
  forall (A B : Type) (f : A -> B) l d, last (map f l) (f d) = f (last l d).
Proof.
  intros A B f l d. induction l as [| y l IH]; [reflexivity |].
  destruct l as [| z l']; [reflexivity |].
  exact IH.
Qed.

(* ---------------------------------------------------------------- *)
(* The integrators                                                   *)

Section Integrators.

Variable slot_u slot_v : nat.

(** The bounds on one cell of a surface integral: on the two second
    derivatives over the cell and on the first derivative along the second
    angle. *)
Record claim2 := Claim2 { k2_Nuu : Z ; k2_quu : Z ; k2_Nvv : Z ; k2_qvv : Z ; k2_Nd : Z ; k2_qd : Z }.

Definition claim0 : claim2 := Claim2 0 0 0 0 0 0.

(** One cell of a curve: its centre and half-width along the first angle, and
    the bound on the second derivative over it. *)
Record claim1 := Claim1 { k1_c : Z ; k1_h : Z ; k1_Nuu : Z ; k1_quu : Z }.

Definition lo1 (c : claim1) : Z := k1_c c - k1_h c.
Definition hi1 (c : claim1) : Z := k1_c c + k1_h c.

(** Consecutive cells of a run share their end. *)
Fixpoint abut (l : list claim1) : bool :=
  match l with
  | c :: tl => match tl with d :: _ => (hi1 c =? lo1 d) && abut tl | [] => true end
  | [] => true
  end.

(** The component a certificate names: 0 the radial one, 1 and 2 the two
    angular ones. *)
Definition comp_of (r3 : residual3) (comp : nat) : expr := nth comp [r_s r3; r_u r3; r_v r3] (r_s r3).

(** The slots of the three components, when each is a slot reference. *)
Definition slots3 (r3 : residual3) : option (list nat) :=
  match slot_of (r_s r3), slot_of (r_u r3), slot_of (r_v r3) with
  | Some a, Some b, Some c => Some [a; b; c]
  | _, _, _ => None
  end.

Lemma slots3_comp :
  forall r3 ns, slots3 r3 = Some ns ->
  length ns = 3%nat /\ forall c, (c < 3)%nat -> slot_of (comp_of r3 c) = Some (nth c ns 0%nat).
Proof.
  intros r3 ns H. unfold slots3 in H.
  destruct (slot_of (r_s r3)) as [a |] eqn:Ha; [| discriminate].
  destruct (slot_of (r_u r3)) as [b |] eqn:Hb; [| discriminate].
  destruct (slot_of (r_v r3)) as [c |] eqn:Hc; [| discriminate].
  injection H as <-. split; [reflexivity |].
  intros k Hk. destruct k as [| [| [| k]]]; [exact Ha | exact Hb | exact Hc | lia].
Qed.

(** What the node must satisfy for the cells to be read off it. *)
Definition node_ok (ms : list Z) (base len : nat) (binds : list binding) (n : nat) : bool :=
  Nat.eqb (length ms) base && Nat.ltb slot_u base && Nat.ltb slot_v base && Nat.ltb 0 len &&
  well_formed base binds && Nat.leb base n && Nat.ltb n (base + len).

Lemma node_ok_facts :
  forall ms base len binds n, node_ok ms base len binds n = true ->
  length ms = base /\ (slot_u < base)%nat /\ (slot_v < base)%nat /\ (0 < len)%nat /\
  well_formed base binds = true /\ (base <= n)%nat /\ (n < base + len)%nat.
Proof.
  intros ms base len binds n H. unfold node_ok in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
  apply Nat.eqb_eq in H1. apply Nat.ltb_lt in H2, H3, H4, H7. apply Nat.leb_le in H6.
  repeat split; assumption.
Qed.

Definition err2_e (hu hv : Z) (c : claim2) : expr :=
  Eadd (Emul (EfromZ (4 * hu * hu * hu * hv)) (eps_e (k2_Nuu c) (k2_quu c)))
       (Emul (EfromZ (4 * hu * hv * hv * hv)) (eps_e (k2_Nvv c) (k2_qvv c))).

(** The value of each component at the centre of a cell, weighted. *)
Definition cell_vals (prec : F.precision) (ms : list Z) (binds : list binding) (ns : list nat)
    (w cu cv : Z) : list I.type :=
  let envc := iextend prec (box_uv slot_u slot_v prec ms cu 0 cv 0) binds in
  map (fun n => I.mul prec (I.fromZ prec w) (ieval prec envc (Evar n))) ns.

Lemma cell_vals_nth :
  forall prec ms binds ns w cu cv c, (c < length ns)%nat ->
  nth c (cell_vals prec ms binds ns w cu cv) I.nai =
  I.mul prec (I.fromZ prec w)
    (ieval prec (iextend prec (box_uv slot_u slot_v prec ms cu 0 cv 0) binds) (Evar (nth c ns 0%nat))).
Proof.
  intros prec ms binds ns w cu cv c Hc. unfold cell_vals. cbv zeta.
  exact (nth_map_lt _ _ _ ns c 0%nat I.nai Hc).
Qed.

(* ---------------------------------------------------------------- *)
(* The surface integral                                              *)

(** The bounds on the two second derivatives over a cell and on the first
    derivative along the second angle, read off the enclosures and checked
    there, for each component; none when an enclosure yields no bound. *)
Definition cell2_claims (prec : F.precision) (ms : list Z) (len : nat) (wu wv : list binding)
    (ns : list nat) (cu hu cv hv : Z) : option (list claim2) :=
  let envu := iextend prec (box_uv slot_u slot_v prec ms cu hu cv hv) wu in
  let envv := iextend prec (box_vu slot_u slot_v prec ms cu hu cv hv) wv in
  all_some (map (fun n =>
    match claim_of prec envu (Evar (n + 2 * len)), claim_of prec envv (Evar (n + 2 * len)),
          claim_of prec envv (Evar (n + len)) with
    | Some a, Some b, Some c => Some (Claim2 (fst a) (snd a) (fst b) (snd b) (fst c) (snd c))
    | _, _, _ => None
    end) ns).

Lemma cell2_claims_ok :
  forall prec ms base len binds ns cu hu cv hv cs,
  cell2_claims prec ms len (with_derivs2 slot_u base len binds) (with_derivs2 slot_v base len binds)
    ns cu hu cv hv = Some cs ->
  forall k, (k < length ns)%nat ->
  checks2 slot_u slot_v base len binds ms (nth k ns 0%nat) prec cu hu cv hv
    (k2_Nuu (nth k cs claim0)) (k2_quu (nth k cs claim0)) (k2_Nvv (nth k cs claim0))
    (k2_qvv (nth k cs claim0)) (k2_Nd (nth k cs claim0)) (k2_qd (nth k cs claim0)) = true.
Proof.
  intros prec ms base len binds ns cu hu cv hv cs H k Hk.
  unfold cell2_claims in H. cbv zeta in H.
  pose proof (all_some_nth _ _ _ H k claim0 ltac:(rewrite length_map; exact Hk)) as Hn.
  rewrite (nth_map_lt _ _ _ ns k 0%nat None Hk) in Hn. cbv beta in Hn.
  destruct (claim_of prec (iextend prec (box_uv slot_u slot_v prec ms cu hu cv hv)
              (with_derivs2 slot_u base len binds)) (Evar (nth k ns 0%nat + 2 * len)))
    as [a |] eqn:Ha; [| discriminate].
  destruct (claim_of prec (iextend prec (box_vu slot_u slot_v prec ms cu hu cv hv)
              (with_derivs2 slot_v base len binds)) (Evar (nth k ns 0%nat + 2 * len)))
    as [b |] eqn:Hb; [| discriminate].
  destruct (claim_of prec (iextend prec (box_vu slot_u slot_v prec ms cu hu cv hv)
              (with_derivs2 slot_v base len binds)) (Evar (nth k ns 0%nat + len)))
    as [c |] eqn:Hc; [| discriminate].
  injection Hn as Hn. rewrite <- Hn. cbn [k2_Nuu k2_quu k2_Nvv k2_qvv k2_Nd k2_qd].
  unfold checks2.
  rewrite (claim_of_ok _ _ _ _ Ha), (claim_of_ok _ _ _ _ Hb), (claim_of_ok _ _ _ _ Hc).
  reflexivity.
Qed.

(** The error of component c over a cell, from the bounds read off it. *)
Definition err2 (prec : F.precision) (hu hv : Z) (c : nat) (o : option (list claim2)) : I.type :=
  match o with
  | Some cs => ieval prec eempty (err2_e hu hv (nth c cs claim0))
  | None => I.nai
  end.

(** The integral of each component over the rectangle [au, au + 2 NU hu] x
    [av, av + 2 NV hv] of angle mantissas, scaled by 2^k for the exponents of
    the two slots, beside the scaled sum of the errors of its cells; none when
    a check fails. *)
Definition integ2 (prec : F.precision) (es ms : list Z) (cfg : pconfig) (modes : list (Z * Z))
    (au hu : Z) (NU : nat) (av hv : Z) (NV : nat) : option (list (I.type * I.type)) :=
  if Nat.eqb slot_u slot_v then None else
  let r3 := residual es cfg modes in
  let binds := r_binds r3 in
  let len := length binds in
  let base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes) in
  match slots3 r3 with
  | None => None
  | Some ns =>
      if forallb (node_ok ms base len binds) ns && Z.leb 0 hu && Z.leb 0 hv &&
         Nat.ltb 0 NU && Nat.ltb 0 NV then
        let wu := with_derivs2 slot_u base len binds in
        let wv := with_derivs2 slot_v base len binds in
        let cls := map (fun ij => cell2_claims prec ms len wu wv ns
                                    (ctr au hu (fst ij)) hu (ctr av hv (snd ij)) hv) (grid NU NV) in
        if forallb is_some cls then
          let vals := map (fun ij => cell_vals prec ms binds ns (4 * hu * hv)
                                       (ctr au hu (fst ij)) (ctr av hv (snd ij))) (grid NU NV) in
          let k := (nth slot_u es 0 + nth slot_v es 0)%Z in
          Some (map (fun c =>
                  let E := isum prec (map (err2 prec hu hv c) cls) in
                  (widen prec (isum prec (map (fun l => nth c l I.nai) vals)) E k,
                   I.mul prec E (ieval prec eempty (Epow2 k))))
                (seq 0 (length ns)))
        else None
      else None
  end.

(** The error bound of one cell of a surface integral, as a real. *)
Definition err2r (hu hv : Z) (c : claim2) : R :=
  4 * (IZR (k2_Nuu c) * powerRZ 2 (k2_quu c)) * IZR hu * IZR hu * IZR hu * IZR hv
  + 4 * (IZR (k2_Nvv c) * powerRZ 2 (k2_qvv c)) * IZR hu * IZR hv * IZR hv * IZR hv.

(** One component over a lattice whose cells pass the checks: every line
    across a cell is integrable, the iterated integral over the lattice exists,
    and it lies within the summed cell errors of the summed midpoint rules. *)
Lemma integ2_lattice :
  forall (Huv : slot_u <> slot_v) prec es ms cfg modes au hu NU av hv NV n
         (cl : nat * nat -> claim2),
  let r3 := residual es cfg modes in
  let binds := r_binds r3 in
  let len := length binds in
  let base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes) in
  node_ok ms base len binds n = true -> (0 <= hu)%Z -> (0 <= hv)%Z -> (0 < NU)%nat -> (0 < NV)%nat ->
  (forall i j, (i < NU)%nat -> (j < NV)%nat ->
     checks2 slot_u slot_v base len binds ms n prec (ctr au hu i) hu (ctr av hv j) hv
       (k2_Nuu (cl (i, j))) (k2_quu (cl (i, j))) (k2_Nvv (cl (i, j))) (k2_qvv (cl (i, j)))
       (k2_Nd (cl (i, j))) (k2_qd (cl (i, j))) = true) ->
  let f := cellf slot_u slot_v binds n ms in
  let bu := IZR au + 2 * INR NU * IZR hu in
  let bv := IZR av + 2 * INR NV * IZR hv in
  (forall i v, (i < NU)%nat -> IZR av <= v <= bv ->
     ex_RInt (fun u => f u v) (IZR au + 2 * INR i * IZR hu) (IZR au + 2 * INR (S i) * IZR hu)) /\
  ex_RInt (fun v => RInt (fun u => f u v) (IZR au) bu) (IZR av) bv /\
  Rabs (RInt (fun v => RInt (fun u => f u v) (IZR au) bu) (IZR av) bv
        - rsum (fun j => rsum (fun i => 4 * IZR hu * IZR hv * f (IZR (ctr au hu i)) (IZR (ctr av hv j)))
                              NU) NV)
  <= rsum (fun j => rsum (fun i => err2r hu hv (cl (i, j))) NU) NV.
Proof.
  intros Huv prec es ms cfg modes au hu NU av hv NV n cl r3 binds len base
         Hnode Hhu Hhv HNU HNV Hchk f bu bv.
  destruct (node_ok_facts ms base len binds n Hnode) as (Hms & Hbu & Hbv & Hlen0 & Hwf & Hbn & Hnl).
  assert (Hhu' : 0 <= IZR hu) by (apply IZR_le; exact Hhu).
  assert (Hhv' : 0 <= IZR hv) by (apply IZR_le; exact Hhv).
  assert (Hcell : forall i j, (i < NU)%nat -> (j < NV)%nat ->
            let c := cl (i, j) in
            (forall v, IZR (ctr av hv j) - IZR hv <= v <= IZR (ctr av hv j) + IZR hv ->
               ex_RInt (fun u => f u v) (IZR (ctr au hu i) - IZR hu) (IZR (ctr au hu i) + IZR hu)) /\
            ex_RInt (fun v => RInt (fun u => f u v) (IZR (ctr au hu i) - IZR hu) (IZR (ctr au hu i) + IZR hu))
                    (IZR (ctr av hv j) - IZR hv) (IZR (ctr av hv j) + IZR hv) /\
            Rabs (RInt (fun v => RInt (fun u => f u v) (IZR (ctr au hu i) - IZR hu) (IZR (ctr au hu i) + IZR hu))
                       (IZR (ctr av hv j) - IZR hv) (IZR (ctr av hv j) + IZR hv)
                  - 4 * IZR hu * IZR hv * f (IZR (ctr au hu i)) (IZR (ctr av hv j)))
            <= 4 * (IZR (k2_Nuu c) * powerRZ 2 (k2_quu c)) * IZR hu * IZR hu * IZR hu * IZR hv
               + 4 * (IZR (k2_Nvv c) * powerRZ 2 (k2_qvv c)) * IZR hu * IZR hv * IZR hv * IZR hv).
  { intros i j Hi Hj c.
    exact (cell2_cert slot_u slot_v Huv base len binds ms n Hms Hbu Hbv Hlen0 Hwf eq_refl Hbn Hnl prec
             (ctr au hu i) hu (ctr av hv j) hv _ _ _ _ _ _ Hhu Hhv (Hchk i j Hi Hj)). }
  assert (Hab : IZR av <= bv) by (unfold bv; pose proof (pos_INR NV); nra).
  (* the v-cells lie in the range *)
  assert (Hvin : forall j v, (j < NV)%nat ->
            IZR av + 2 * INR j * IZR hv <= v <= IZR av + 2 * INR (S j) * IZR hv -> IZR av <= v <= bv).
  { intros j v Hj Hv. unfold bv. assert (INR (S j) <= INR NV) by (apply le_INR; lia).
    pose proof (pos_INR j). split; nra. }
  (* every line of every u-cell, inside the range *)
  assert (Hlines : forall i v, (i < NU)%nat -> IZR av <= v <= bv ->
            ex_RInt (fun u => f u v) (IZR au + 2 * INR i * IZR hu) (IZR au + 2 * INR (S i) * IZR hu)).
  { intros i v Hi Hv.
    destruct (find_cell (IZR av) (IZR hv) NV v HNV Hhv' Hv) as [j [Hj Hjv]].
    destruct (Hcell i j Hi Hj) as [H1 _].
    rewrite !ctr_lo, !ctr_hi in H1.
    exact (H1 v Hjv). }
  set (f' := fun u v => f u (clamp (IZR av) bv v)).
  assert (Hf' : forall u v, IZR av <= v <= bv -> f' u v = f u v).
  { intros u v Hv. unfold f'. rewrite clamp_id by exact Hv. reflexivity. }
  set (val := fun i j => 4 * IZR hu * IZR hv * f (IZR (ctr au hu i)) (IZR (ctr av hv j))).
  set (err := fun i j => err2r hu hv (cl (i, j))).
  destruct (tiling2_encloses f' (IZR au) (IZR hu) (IZR av) (IZR hv) NU NV val err) as [Hex Hbnd].
  - (* every line of every u-cell is integrable *)
    intros i v Hi.
    set (v' := clamp (IZR av) bv v).
    assert (Hv' : IZR av <= v' <= bv) by (apply clamp_in; exact Hab).
    exact (Hlines i v' Hi Hv').
  - (* the inner integral over a u-cell is integrable over every v-cell *)
    intros i j Hi Hj.
    destruct (Hcell i j Hi Hj) as [_ [H2 _]].
    rewrite !ctr_lo, !ctr_hi in H2.
    apply (ex_RInt_ext (fun v => RInt (fun u => f u v) (IZR au + 2 * INR i * IZR hu)
                                  (IZR au + 2 * INR (S i) * IZR hu))); [| exact H2].
    intros x Hx. unfold ucell.
    assert (Hr : IZR av + 2 * INR j * IZR hv <= IZR av + 2 * INR (S j) * IZR hv)
      by (rewrite S_INR; lra).
    rewrite Rmin_left, Rmax_right in Hx by exact Hr.
    apply RInt_ext. intros u _. symmetry. apply Hf'. apply (Hvin j x Hj). lra.
  - (* each cell is enclosed *)
    intros i j Hi Hj.
    destruct (Hcell i j Hi Hj) as [_ [_ H3]].
    rewrite !ctr_lo, !ctr_hi in H3.
    assert (Hr : IZR av + 2 * INR j * IZR hv <= IZR av + 2 * INR (S j) * IZR hv)
      by (rewrite S_INR; lra).
    rewrite (RInt_ext (ucell f' (IZR au) (IZR hu) i)
               (fun v => RInt (fun u => f u v) (IZR au + 2 * INR i * IZR hu) (IZR au + 2 * INR (S i) * IZR hu))).
    + exact H3.
    + intros x Hx. rewrite Rmin_left, Rmax_right in Hx by exact Hr. unfold ucell.
      apply RInt_ext. intros u _. apply Hf'. apply (Hvin j x Hj). lra.
  - (* the whole rectangle *)
    assert (Heq : forall v, Rmin (IZR av) bv < v < Rmax (IZR av) bv ->
              RInt (fun u => f' u v) (IZR au) bu = RInt (fun u => f u v) (IZR au) bu).
    { intros v Hv. rewrite Rmin_left, Rmax_right in Hv by exact Hab.
      apply RInt_ext. intros u _. apply Hf'. lra. }
    fold bv in Hex, Hbnd. fold bu in Hex, Hbnd.
    split; [exact Hlines | split].
    + apply (ex_RInt_ext (fun v => RInt (fun u => f' u v) (IZR au) bu)); [| exact Hex].
      intros v Hv. apply Heq. exact Hv.
    + rewrite (RInt_ext (fun v => RInt (fun u => f u v) (IZR au) bu)
                        (fun v => RInt (fun u => f' u v) (IZR au) bu)) by (intros v Hv; symmetry; apply Heq; exact Hv).
      exact Hbnd.
Qed.

(** The summed midpoint values of a lattice, enclosed. *)
Lemma lattice_vals :
  forall prec ms binds n au hu NU av hv NV,
  contains (I.convert (isum prec (map (fun ij => I.mul prec (I.fromZ prec (4 * hu * hv))
      (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (ctr au hu (fst ij)) 0
                                  (ctr av hv (snd ij)) 0) binds) (Evar n))) (grid NU NV))))
    (Xreal (rsum (fun j => rsum (fun i => 4 * IZR hu * IZR hv
              * cellf slot_u slot_v binds n ms (IZR (ctr au hu i)) (IZR (ctr av hv j))) NU) NV)).
Proof.
  intros prec ms binds n au hu NU av hv NV.
  set (val := fun i j => 4 * IZR hu * IZR hv
                * cellf slot_u slot_v binds n ms (IZR (ctr au hu i)) (IZR (ctr av hv j))).
  change (rsum (fun j => rsum (fun i => 4 * IZR hu * IZR hv
            * cellf slot_u slot_v binds n ms (IZR (ctr au hu i)) (IZR (ctr av hv j))) NU) NV)
    with (rsum (fun j => rsum (fun i => val i j) NU) NV).
  rewrite <- (fold_grid (fun ij => val (fst ij) (snd ij))).
  apply isum_map. intros [i j] Hin. cbv beta. cbn [fst snd].
  unfold val.
  replace (4 * IZR hu * IZR hv * cellf slot_u slot_v binds n ms (IZR (ctr au hu i)) (IZR (ctr av hv j)))
    with (IZR (4 * hu * hv) * cellf slot_u slot_v binds n ms (IZR (ctr au hu i)) (IZR (ctr av hv j)))
    by (rewrite !mult_IZR; ring).
  exact (I.mul_correct prec _ _ (Xreal (IZR (4 * hu * hv)))
           (Xreal (cellf slot_u slot_v binds n ms (IZR (ctr au hu i)) (IZR (ctr av hv j))))
           (I.fromZ_correct prec (4 * hu * hv))
           (centre_val slot_u slot_v binds ms n prec (ctr au hu i) (ctr av hv j))).
Qed.

(** The summed cell errors of a lattice, enclosed. *)
Lemma lattice_errs :
  forall prec hu NU hv NV (cl : nat * nat -> claim2),
  contains (I.convert (isum prec (map (fun ij => ieval prec eempty (err2_e hu hv (cl ij))) (grid NU NV))))
    (Xreal (rsum (fun j => rsum (fun i => err2r hu hv (cl (i, j))) NU) NV)).
Proof.
  intros prec hu NU hv NV cl.
  set (err := fun i j => err2r hu hv (cl (i, j))).
  change (rsum (fun j => rsum (fun i => err2r hu hv (cl (i, j))) NU) NV)
    with (rsum (fun j => rsum (fun i => err i j) NU) NV).
  rewrite <- (fold_grid (fun ij => err (fst ij) (snd ij))).
  apply isum_map. intros [i j] Hin. cbn [fst snd].
  assert (Hev := ieval_correct prec eempty eempty (err2_e hu hv (cl (i, j))) env_ok_nil).
  unfold err2_e, eps_e, epow2 in Hev. simpl in Hev.
  unfold err, err2r.
  replace (4 * (IZR (k2_Nuu (cl (i, j))) * powerRZ 2 (k2_quu (cl (i, j)))) * IZR hu * IZR hu * IZR hu * IZR hv
           + 4 * (IZR (k2_Nvv (cl (i, j))) * powerRZ 2 (k2_qvv (cl (i, j)))) * IZR hu * IZR hv * IZR hv * IZR hv)
    with (IZR (4 * hu * hu * hu * hv) * (IZR (k2_Nuu (cl (i, j))) * powerRZ 2 (k2_quu (cl (i, j))))
          + IZR (4 * hu * hv * hv * hv) * (IZR (k2_Nvv (cl (i, j))) * powerRZ 2 (k2_qvv (cl (i, j)))))
    by (rewrite !mult_IZR; ring).
  exact Hev.
Qed.

(** One component, from bounds on its cells that pass the checks. *)
Lemma integ2_core :
  forall (Huv : slot_u <> slot_v) prec es ms cfg modes au hu NU av hv NV n
         (cl : nat * nat -> claim2) q,
  let r3 := residual es cfg modes in
  let binds := r_binds r3 in
  let len := length binds in
  let base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes) in
  node_ok ms base len binds n = true -> (0 <= hu)%Z -> (0 <= hv)%Z -> (0 < NU)%nat -> (0 < NV)%nat ->
  (forall i j, (i < NU)%nat -> (j < NV)%nat ->
     checks2 slot_u slot_v base len binds ms n prec (ctr au hu i) hu (ctr av hv j) hv
       (k2_Nuu (cl (i, j))) (k2_quu (cl (i, j))) (k2_Nvv (cl (i, j))) (k2_qvv (cl (i, j)))
       (k2_Nd (cl (i, j))) (k2_qd (cl (i, j))) = true) ->
  let f := cellf slot_u slot_v binds n ms in
  let bu := IZR au + 2 * INR NU * IZR hu in
  let bv := IZR av + 2 * INR NV * IZR hv in
  ex_RInt (fun v => RInt (fun u => f u v) (IZR au) bu) (IZR av) bv /\
  contains (I.convert (widen prec
      (isum prec (map (fun ij => I.mul prec (I.fromZ prec (4 * hu * hv))
         (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (ctr au hu (fst ij)) 0
                                     (ctr av hv (snd ij)) 0) binds) (Evar n))) (grid NU NV)))
      (isum prec (map (fun ij => ieval prec eempty (err2_e hu hv (cl ij))) (grid NU NV))) q))
    (Xreal (RInt (fun v => RInt (fun u => f u v) (IZR au) bu) (IZR av) bv * powerRZ 2 q)).
Proof.
  intros Huv prec es ms cfg modes au hu NU av hv NV n cl q r3 binds len base
         Hnode Hhu Hhv HNU HNV Hchk f bu bv.
  destruct (integ2_lattice Huv prec es ms cfg modes au hu NU av hv NV n cl Hnode Hhu Hhv HNU HNV Hchk)
    as [_ [Hex Hbnd]].
  split; [exact Hex |].
  apply (widen_scale prec _ _ _ _ _ _
           (lattice_vals prec ms binds n au hu NU av hv NV)
           (lattice_errs prec hu NU hv NV cl) Hbnd).
Qed.

Theorem integ2_correct :
  forall prec es ms cfg modes au hu NU av hv NV Os,
  integ2 prec es ms cfg modes au hu NU av hv NV = Some Os ->
  let r3 := residual es cfg modes in
  forall c, (c < 3)%nat ->
  exists n, slot_of (comp_of r3 c) = Some n /\
  let f := cellf slot_u slot_v (r_binds r3) n ms in
  let bu := IZR au + 2 * INR NU * IZR hu in
  let bv := IZR av + 2 * INR NV * IZR hv in
  ex_RInt (fun v => RInt (fun u => f u v) (IZR au) bu) (IZR av) bv /\
  contains (I.convert (fst (nth c Os (I.nai, I.nai))))
    (Xreal (RInt (fun v => RInt (fun u => f u v) (IZR au) bu) (IZR av) bv
            * powerRZ 2 (nth slot_u es 0%Z + nth slot_v es 0%Z))).
Proof.
  intros prec es ms cfg modes au hu NU av hv NV Os Hi r3 c Hc.
  unfold integ2 in Hi.
  destruct (Nat.eqb slot_u slot_v) eqn:Heq; [discriminate |].
  apply Nat.eqb_neq in Heq.
  cbv zeta in Hi. fold r3 in Hi.
  set (binds := r_binds r3) in *. set (len := length binds) in *.
  set (base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes)) in *.
  destruct (slots3 r3) as [ns |] eqn:Hns; [| discriminate].
  destruct (slots3_comp r3 ns Hns) as [Hlen3 Hslot].
  exists (nth c ns 0%nat). split; [exact (Hslot c Hc) |].
  destruct (forallb (node_ok ms base len binds) ns && (0 <=? hu)%Z && (0 <=? hv)%Z &&
            (0 <? NU)%nat && (0 <? NV)%nat) eqn:Hc1; [| discriminate].
  set (g := fun ij : nat * nat =>
              cell2_claims prec ms len (with_derivs2 slot_u base len binds)
                (with_derivs2 slot_v base len binds) ns (ctr au hu (fst ij)) hu (ctr av hv (snd ij)) hv) in *.
  destruct (forallb is_some (map g (grid NU NV))) eqn:Hc2; [| discriminate].
  (* injection would normalize the terms, so the equation is read off with
     beta and iota alone *)
  apply (f_equal (fun o => match o with Some x => x | None => Os end)) in Hi.
  cbv beta iota in Hi. subst Os.
  repeat rewrite andb_true_iff in Hc1. destruct Hc1 as [[[[Hnodes Hhu] Hhv] HNU] HNV].
  apply Z.leb_le in Hhu. apply Z.leb_le in Hhv. apply Nat.ltb_lt in HNU. apply Nat.ltb_lt in HNV.
  assert (Hcn : (c < length ns)%nat) by lia.
  rewrite (nth_seq_map _ _ (length ns) c (I.nai, I.nai) Hcn). cbv beta. cbn [fst].
  set (cl := fun ij => match g ij with Some cs => nth c cs claim0 | None => claim0 end).
  assert (HS : map (fun l => nth c l I.nai)
                 (map (fun ij => cell_vals prec ms binds ns (4 * hu * hv)
                                   (ctr au hu (fst ij)) (ctr av hv (snd ij))) (grid NU NV))
             = map (fun ij => I.mul prec (I.fromZ prec (4 * hu * hv))
                 (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (ctr au hu (fst ij)) 0
                                             (ctr av hv (snd ij)) 0) binds) (Evar (nth c ns 0%nat))))
                 (grid NU NV)).
  { rewrite map_map. apply map_ext. intros ij. apply cell_vals_nth. exact Hcn. }
  assert (HE : map (err2 prec hu hv c) (map g (grid NU NV))
             = map (fun ij => ieval prec eempty (err2_e hu hv (cl ij))) (grid NU NV)).
  { rewrite map_map. apply map_ext_in. intros ij Hij.
    pose proof (forallb_map_in _ _ is_some g _ _ Hc2 Hij) as Hs.
    unfold cl, err2. destruct (g ij) as [cs |]; [reflexivity | discriminate]. }
  rewrite HS, HE.
  pose proof (integ2_core Heq prec es ms cfg modes au hu NU av hv NV (nth c ns 0%nat) cl
                (nth slot_u es 0%Z + nth slot_v es 0%Z)) as Hcore.
  cbv zeta in Hcore. cbv zeta.
  apply Hcore.
  - apply (proj1 (forallb_forall _ _) Hnodes). apply nth_In. exact Hcn.
  - exact Hhu.
  - exact Hhv.
  - exact HNU.
  - exact HNV.
  - intros i j Hi Hj.
    assert (Hin := in_grid NU NV i j Hi Hj).
    pose proof (forallb_map_in _ _ is_some g _ _ Hc2 Hin) as Hs.
    unfold cl. destruct (g (i, j)) as [cs |] eqn:Hcs; [| discriminate].
    exact (cell2_claims_ok prec ms base len binds ns _ _ _ _ cs Hcs c Hcn).
Qed.

(* ---------------------------------------------------------------- *)
(* The integral over one period of both angles                      *)

(** One period of an angle, 2 pi, in the mantissa units of a slot with
    exponent e. *)
Definition period (e : Z) : R := 2 * PI * powerRZ 2 (- e).

Definition period_e (e : Z) : expr := Emul (Emul (EfromZ 2) Epi) (Epow2 (- e)).

(** How far a lattice of N cells of half-width h from 0 reaches past one
    period, and how far the period reaches into the lattice's last cell. *)
Definition excess_e (N : nat) (h e : Z) : expr :=
  Esub (EfromZ (2 * Z.of_nat N * h)) (period_e e).
Definition reach_e (N : nat) (h e : Z) : expr :=
  Esub (period_e e) (EfromZ (2 * Z.of_nat (pred N) * h)).

Lemma xeval_period_e : forall env e, xeval env (period_e e) = Xreal (period e).
Proof. intros env e. reflexivity. Qed.

Lemma xeval_excess_e :
  forall env N h e, xeval env (excess_e N h e) = Xreal (2 * INR N * IZR h - period e).
Proof.
  intros env N h e.
  replace (2 * INR N * IZR h) with (IZR (2 * Z.of_nat N * h))
    by (rewrite !mult_IZR, <- INR_IZR_INZ; reflexivity).
  reflexivity.
Qed.

Lemma xeval_reach_e :
  forall env N h e, xeval env (reach_e N h e) = Xreal (period e - 2 * INR (pred N) * IZR h).
Proof.
  intros env N h e.
  replace (2 * INR (pred N) * IZR h) with (IZR (2 * Z.of_nat (pred N) * h))
    by (rewrite !mult_IZR, <- INR_IZR_INZ; reflexivity).
  reflexivity.
Qed.

(** A bound on each component over one cell, read off the enclosure of its
    value there and checked. *)
Definition vbounds (prec : F.precision) (ms : list Z) (binds : list binding) (ns : list nat)
    (cu hu cv hv : Z) : option (list (Z * Z)) :=
  let env := iextend prec (box_uv slot_u slot_v prec ms cu hu cv hv) binds in
  all_some (map (fun n => claim_of prec env (Evar n)) ns).

Lemma vbounds_ok :
  forall prec ms binds ns cu hu cv hv l,
  vbounds prec ms binds ns cu hu cv hv = Some l ->
  forall k, (k < length ns)%nat ->
  check1 prec (iextend prec (box_uv slot_u slot_v prec ms cu hu cv hv) binds) (Evar (nth k ns 0%nat))
    (fst (nth k l (0%Z, 0%Z))) (snd (nth k l (0%Z, 0%Z))) = true.
Proof.
  intros prec ms binds ns cu hu cv hv l H k Hk.
  unfold vbounds in H. cbv zeta in H.
  pose proof (all_some_nth _ _ _ H k (0%Z, 0%Z) ltac:(rewrite length_map; exact Hk)) as Hn.
  rewrite (nth_map_lt _ _ _ ns k 0%nat None Hk) in Hn.
  exact (claim_of_ok _ _ _ _ Hn).
Qed.

(** The bound of component c on a cell, as an expression and as a real. *)
Definition vb_e (c : nat) (o : option (list (Z * Z))) : expr :=
  match o with
  | Some l => eps_e (fst (nth c l (0%Z, 0%Z))) (snd (nth c l (0%Z, 0%Z)))
  | None => EfromZ 0
  end.

Definition vb_r (c : nat) (o : option (list (Z * Z))) : R :=
  match o with
  | Some l => IZR (fst (nth c l (0%Z, 0%Z))) * powerRZ 2 (snd (nth c l (0%Z, 0%Z)))
  | None => 0
  end.

Lemma xeval_vb_e : forall env c o, xeval env (vb_e c o) = Xreal (vb_r c o).
Proof. intros env c [l |]; reflexivity. Qed.

Definition esum_e (l : list expr) : expr := fold_right Eadd (EfromZ 0) l.

Lemma xeval_esum_vb :
  forall env c l, xeval env (esum_e (map (vb_e c) l)) = Xreal (fold_right Rplus 0 (map (vb_r c) l)).
Proof.
  intros env c l. induction l as [| o l IH]; [reflexivity |].
  change (xeval env (esum_e (map (vb_e c) (o :: l))))
    with (Xadd (xeval env (vb_e c o)) (xeval env (esum_e (map (vb_e c) l)))).
  rewrite IH, xeval_vb_e. reflexivity.
Qed.

(** The two strips the lattice adds to the period, bounded through the last
    column of cells and the last row. *)
Definition strips_e (c : nat) (cols rows : list (option (list (Z * Z)))) (NU : nat) (hu eu : Z)
    (NV : nat) (hv ev : Z) : expr :=
  Eadd (Emul (Emul (excess_e NU hu eu) (EfromZ (2 * hv))) (esum_e (map (vb_e c) cols)))
       (Emul (excess_e NV hv ev)
             (Eadd (Emul (EfromZ (2 * hu)) (esum_e (map (vb_e c) rows)))
                   (Emul (excess_e NU hu eu) (vb_e c (nth (pred NV) cols None))))).

Lemma xeval_strips_e :
  forall env c cols rows NU hu eu NV hv ev,
  xeval env (strips_e c cols rows NU hu eu NV hv ev) =
  Xreal ((2 * INR NU * IZR hu - period eu) * (2 * IZR hv) * fold_right Rplus 0 (map (vb_r c) cols)
         + (2 * INR NV * IZR hv - period ev)
           * (2 * IZR hu * fold_right Rplus 0 (map (vb_r c) rows)
              + (2 * INR NU * IZR hu - period eu) * vb_r c (nth (pred NV) cols None))).
Proof.
  intros env c cols rows NU hu eu NV hv ev.
  change (xeval env (strips_e c cols rows NU hu eu NV hv ev))
    with (Xadd (Xmul (Xmul (xeval env (excess_e NU hu eu)) (Xreal (IZR (2 * hv))))
                     (xeval env (esum_e (map (vb_e c) cols))))
               (Xmul (xeval env (excess_e NV hv ev))
                     (Xadd (Xmul (Xreal (IZR (2 * hu))) (xeval env (esum_e (map (vb_e c) rows))))
                           (Xmul (xeval env (excess_e NU hu eu))
                                 (xeval env (vb_e c (nth (pred NV) cols None))))))).
  rewrite !xeval_excess_e, !xeval_esum_vb, xeval_vb_e, !mult_IZR.
  reflexivity.
Qed.

(** The integral of each component over one period of both angles, [0, 2 pi]
    in each, for a lattice of cells from 0 that reaches past both periods:
    the lattice's enclosure widened by the two strips it adds. *)
Definition integ2_torus (prec : F.precision) (es ms : list Z) (cfg : pconfig) (modes : list (Z * Z))
    (hu : Z) (NU : nat) (hv : Z) (NV : nat) : option (list (I.type * I.type)) :=
  if Nat.eqb slot_u slot_v then None else
  let r3 := residual es cfg modes in
  let binds := r_binds r3 in
  let len := length binds in
  let base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes) in
  let eu := nth slot_u es 0%Z in
  let ev := nth slot_v es 0%Z in
  match slots3 r3 with
  | None => None
  | Some ns =>
      if forallb (node_ok ms base len binds) ns && Z.leb 0 hu && Z.leb 0 hv &&
         Nat.ltb 0 NU && Nat.ltb 0 NV &&
         nonneg (ieval prec eempty (excess_e NU hu eu)) && nonneg (ieval prec eempty (reach_e NU hu eu)) &&
         nonneg (ieval prec eempty (excess_e NV hv ev)) && nonneg (ieval prec eempty (reach_e NV hv ev)) then
        let wu := with_derivs2 slot_u base len binds in
        let wv := with_derivs2 slot_v base len binds in
        let cls := map (fun ij => cell2_claims prec ms len wu wv ns
                                    (ctr 0 hu (fst ij)) hu (ctr 0 hv (snd ij)) hv) (grid NU NV) in
        let cols := map (fun j => vbounds prec ms binds ns (ctr 0 hu (pred NU)) hu (ctr 0 hv j) hv)
                        (seq 0 NV) in
        let rows := map (fun i => vbounds prec ms binds ns (ctr 0 hu i) hu (ctr 0 hv (pred NV)) hv)
                        (seq 0 NU) in
        if forallb is_some cls && forallb is_some cols && forallb is_some rows then
          let vals := map (fun ij => cell_vals prec ms binds ns (4 * hu * hv)
                                       (ctr 0 hu (fst ij)) (ctr 0 hv (snd ij))) (grid NU NV) in
          let k := (eu + ev)%Z in
          Some (map (fun c =>
                  let E := I.add prec (isum prec (map (err2 prec hu hv c) cls))
                                 (ieval prec eempty (strips_e c cols rows NU hu eu NV hv ev)) in
                  (widen prec (isum prec (map (fun l => nth c l I.nai) vals)) E k,
                   I.mul prec E (ieval prec eempty (Epow2 k))))
                (seq 0 (length ns)))
        else None
      else None
  end.

Theorem integ2_torus_correct :
  forall prec es ms cfg modes hu NU hv NV Os,
  integ2_torus prec es ms cfg modes hu NU hv NV = Some Os ->
  let r3 := residual es cfg modes in
  forall c, (c < 3)%nat ->
  exists n, slot_of (comp_of r3 c) = Some n /\
  let f := cellf slot_u slot_v (r_binds r3) n ms in
  let pu := period (nth slot_u es 0%Z) in
  let pv := period (nth slot_v es 0%Z) in
  ex_RInt (fun v => RInt (fun u => f u v) 0 pu) 0 pv /\
  contains (I.convert (fst (nth c Os (I.nai, I.nai))))
    (Xreal (RInt (fun v => RInt (fun u => f u v) 0 pu) 0 pv
            * powerRZ 2 (nth slot_u es 0%Z + nth slot_v es 0%Z))).
Proof.
  intros prec es ms cfg modes hu NU hv NV Os Hi r3 c Hc.
  unfold integ2_torus in Hi.
  destruct (Nat.eqb slot_u slot_v) eqn:Heq; [discriminate |].
  apply Nat.eqb_neq in Heq.
  cbv zeta in Hi. fold r3 in Hi.
  set (binds := r_binds r3) in *. set (len := length binds) in *.
  set (base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes)) in *.
  set (eu := nth slot_u es 0%Z) in *. set (ev := nth slot_v es 0%Z) in *.
  destruct (slots3 r3) as [ns |] eqn:Hns; [| discriminate].
  destruct (slots3_comp r3 ns Hns) as [Hlen3 Hslot].
  exists (nth c ns 0%nat). split; [exact (Hslot c Hc) |].
  destruct (forallb (node_ok ms base len binds) ns && (0 <=? hu)%Z && (0 <=? hv)%Z &&
            (0 <? NU)%nat && (0 <? NV)%nat &&
            nonneg (ieval prec eempty (excess_e NU hu eu)) && nonneg (ieval prec eempty (reach_e NU hu eu)) &&
            nonneg (ieval prec eempty (excess_e NV hv ev)) && nonneg (ieval prec eempty (reach_e NV hv ev)))
    eqn:Hc1; [| discriminate].
  set (g := fun ij : nat * nat =>
              cell2_claims prec ms len (with_derivs2 slot_u base len binds)
                (with_derivs2 slot_v base len binds) ns (ctr 0 hu (fst ij)) hu (ctr 0 hv (snd ij)) hv) in *.
  set (colf := fun j => vbounds prec ms binds ns (ctr 0 hu (pred NU)) hu (ctr 0 hv j) hv) in *.
  set (rowf := fun i => vbounds prec ms binds ns (ctr 0 hu i) hu (ctr 0 hv (pred NV)) hv) in *.
  destruct (forallb is_some (map g (grid NU NV)) && forallb is_some (map colf (seq 0 NV)) &&
            forallb is_some (map rowf (seq 0 NU))) eqn:Hc2; [| discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => Os end)) in Hi.
  cbv beta iota in Hi. subst Os.
  repeat rewrite andb_true_iff in Hc1.
  destruct Hc1 as [[[[[[[[Hnodes Hhu] Hhv] HNU] HNV] Hxu] Hru] Hxv] Hrv].
  apply Z.leb_le in Hhu. apply Z.leb_le in Hhv. apply Nat.ltb_lt in HNU. apply Nat.ltb_lt in HNV.
  repeat rewrite andb_true_iff in Hc2. destruct Hc2 as [[Hcls Hcols] Hrows].
  assert (Hcn : (c < length ns)%nat) by lia.
  rewrite (nth_seq_map _ _ (length ns) c (I.nai, I.nai) Hcn). cbv beta. cbn [fst].
  set (n := nth c ns 0%nat) in *.
  set (cl := fun ij => match g ij with Some cs => nth c cs claim0 | None => claim0 end).
  assert (HS : map (fun l => nth c l I.nai)
                 (map (fun ij => cell_vals prec ms binds ns (4 * hu * hv)
                                   (ctr 0 hu (fst ij)) (ctr 0 hv (snd ij))) (grid NU NV))
             = map (fun ij => I.mul prec (I.fromZ prec (4 * hu * hv))
                 (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (ctr 0 hu (fst ij)) 0
                                             (ctr 0 hv (snd ij)) 0) binds) (Evar n)))
                 (grid NU NV)).
  { rewrite map_map. apply map_ext. intros ij. apply cell_vals_nth. exact Hcn. }
  assert (HE : map (err2 prec hu hv c) (map g (grid NU NV))
             = map (fun ij => ieval prec eempty (err2_e hu hv (cl ij))) (grid NU NV)).
  { rewrite map_map. apply map_ext_in. intros ij Hij.
    pose proof (forallb_map_in _ _ is_some g _ _ Hcls Hij) as Hs.
    unfold cl, err2. destruct (g ij) as [cs |]; [reflexivity | discriminate]. }
  rewrite HS, HE.
  (* every cell passes its checks *)
  assert (Hchk : forall i j, (i < NU)%nat -> (j < NV)%nat ->
            checks2 slot_u slot_v base len binds ms n prec (ctr 0 hu i) hu (ctr 0 hv j) hv
              (k2_Nuu (cl (i, j))) (k2_quu (cl (i, j))) (k2_Nvv (cl (i, j))) (k2_qvv (cl (i, j)))
              (k2_Nd (cl (i, j))) (k2_qd (cl (i, j))) = true).
  { intros i j Hi Hj.
    assert (Hin := in_grid NU NV i j Hi Hj).
    pose proof (forallb_map_in _ _ is_some g _ _ Hcls Hin) as Hs.
    unfold cl. destruct (g (i, j)) as [cs |] eqn:Hcs; [| discriminate].
    exact (cell2_claims_ok prec ms base len binds ns _ _ _ _ cs Hcs c Hcn). }
  assert (Hnode : node_ok ms base len binds n = true)
    by (apply (proj1 (forallb_forall _ _) Hnodes); apply nth_In; exact Hcn).
  destruct (node_ok_facts ms base len binds n Hnode) as (Hms & Hbu & Hbv & Hlen0 & Hwf & Hbn & Hnl).
  assert (Hhu' : 0 <= IZR hu) by (apply IZR_le; exact Hhu).
  assert (Hhv' : 0 <= IZR hv) by (apply IZR_le; exact Hhv).
  assert (HSU : S (pred NU) = NU) by lia.
  assert (HSV : S (pred NV) = NV) by lia.
  (* the lattice *)
  destruct (integ2_lattice Heq prec es ms cfg modes 0 hu NU 0 hv NV n cl Hnode Hhu Hhv HNU HNV Hchk)
    as [Hlines [HexL HbL]].
  cbv zeta in Hlines, HexL, HbL.
  set (f := cellf slot_u slot_v binds n ms) in *.
  (* the lattice reaches past both periods, which end inside its last cells *)
  destruct (nonneg_correct _ _ (ieval_correct prec eempty eempty (excess_e NU hu eu) env_ok_nil) Hxu)
    as [xu [Exu Hxu0]].
  destruct (nonneg_correct _ _ (ieval_correct prec eempty eempty (reach_e NU hu eu) env_ok_nil) Hru)
    as [ru [Eru Hru0]].
  destruct (nonneg_correct _ _ (ieval_correct prec eempty eempty (excess_e NV hv ev) env_ok_nil) Hxv)
    as [xv [Exv Hxv0]].
  destruct (nonneg_correct _ _ (ieval_correct prec eempty eempty (reach_e NV hv ev) env_ok_nil) Hrv)
    as [rv [Erv Hrv0]].
  rewrite xeval_excess_e in Exu, Exv. rewrite xeval_reach_e in Eru, Erv.
  injection Exu as Exu. injection Eru as Eru. injection Exv as Exv. injection Erv as Erv.
  assert (HPu : 2 * INR (pred NU) * IZR hu <= period eu <= 2 * INR NU * IZR hu) by lra.
  assert (HPv : 2 * INR (pred NV) * IZR hv <= period ev <= 2 * INR NV * IZR hv) by lra.
  (* the cells of the last column and of the last row *)
  assert (Hcol : forall j u v, (j < NV)%nat ->
            0 + 2 * INR (pred NU) * IZR hu <= u <= 0 + 2 * INR NU * IZR hu ->
            0 + 2 * INR j * IZR hv <= v <= 0 + 2 * INR (S j) * IZR hv ->
            Rabs (f u v) <= vb_r c (colf j)).
  { intros j u v Hj Hu Hv.
    assert (Hs : is_some (colf j) = true)
      by (apply (forallb_map_in _ _ is_some colf (seq 0 NV) j Hcols); apply in_seq; lia).
    destruct (colf j) as [l |] eqn:Hl; [| discriminate].
    cbn [vb_r].
    apply (box_bound slot_u slot_v binds ms n prec (ctr 0 hu (pred NU)) hu (ctr 0 hv j) hv).
    - exact (vbounds_ok prec ms binds ns _ _ _ _ l Hl c Hcn).
    - rewrite minus_IZR, plus_IZR, ctr_lo, ctr_hi, HSU. exact Hu.
    - rewrite minus_IZR, plus_IZR, ctr_lo, ctr_hi. exact Hv. }
  assert (Hrow : forall i u v, (i < NU)%nat ->
            0 + 2 * INR i * IZR hu <= u <= 0 + 2 * INR (S i) * IZR hu ->
            0 + 2 * INR (pred NV) * IZR hv <= v <= 0 + 2 * INR NV * IZR hv ->
            Rabs (f u v) <= vb_r c (rowf i)).
  { intros i u v Hi Hu Hv.
    assert (Hs : is_some (rowf i) = true)
      by (apply (forallb_map_in _ _ is_some rowf (seq 0 NU) i Hrows); apply in_seq; lia).
    destruct (rowf i) as [l |] eqn:Hl; [| discriminate].
    cbn [vb_r].
    apply (box_bound slot_u slot_v binds ms n prec (ctr 0 hu i) hu (ctr 0 hv (pred NV)) hv).
    - exact (vbounds_ok prec ms binds ns _ _ _ _ l Hl c Hcn).
    - rewrite minus_IZR, plus_IZR, ctr_lo, ctr_hi. exact Hu.
    - rewrite minus_IZR, plus_IZR, ctr_lo, ctr_hi, HSV. exact Hv. }
  (* the strip beyond the first period is integrable over each cell of the
     last column *)
  assert (Hex_h : forall j, (j < NV)%nat ->
            ex_RInt (fun v => RInt (fun u => f u v) (0 + period eu) (0 + 2 * INR NU * IZR hu))
                    (0 + 2 * INR j * IZR hv) (0 + 2 * INR (S j) * IZR hv)).
  { intros j Hj.
    assert (Hlo' : IZR (ctr 0 hu (pred NU)) - IZR hu <= 0 + period eu <= 0 + 2 * INR NU * IZR hu)
      by (rewrite ctr_lo; lra).
    assert (Hhi' : 0 + 2 * INR NU * IZR hu <= IZR (ctr 0 hu (pred NU)) + IZR hu)
      by (rewrite ctr_hi, HSU; lra).
    pose proof (cell2_sub slot_u slot_v Heq base len binds ms n Hms Hbu Hbv Hlen0 Hwf eq_refl Hbn Hnl
                  prec (ctr 0 hu (pred NU)) hu (ctr 0 hv j) hv _ _ _ _ _ _
                  (0 + period eu) (0 + 2 * INR NU * IZR hu) Hhu Hhv
                  (Hchk (pred NU) j ltac:(lia) Hj) Hlo' Hhi') as H.
    cbv zeta in H. rewrite ctr_lo, ctr_hi in H. exact H. }
  destruct (torus_strips f 0 (IZR hu) 0 (IZR hv) (period eu) (period ev) NU NV
              (fun j => vb_r c (colf j)) (fun i => vb_r c (rowf i))
              HNU HNV Hhu' Hhv' HPu HPv Hlines HexL Hex_h Hcol Hrow) as [HexT HbT].
  rewrite !Rplus_0_l in HexT. rewrite !Rplus_0_l in HbT. rewrite !Rplus_0_l in HbL.
  split; [exact HexT |].
  (* the strips' bound is the checker's *)
  assert (HEs : contains (I.convert (ieval prec eempty
                   (strips_e c (map colf (seq 0 NV)) (map rowf (seq 0 NU)) NU hu eu NV hv ev)))
                  (Xreal ((2 * INR NU * IZR hu - period eu) * (2 * IZR hv) * rsum (fun j => vb_r c (colf j)) NV
                          + (2 * INR NV * IZR hv - period ev)
                            * (2 * IZR hu * rsum (fun i => vb_r c (rowf i)) NU
                               + (2 * INR NU * IZR hu - period eu) * vb_r c (colf (pred NV)))))).
  { pose proof (ieval_correct prec eempty eempty
                  (strips_e c (map colf (seq 0 NV)) (map rowf (seq 0 NU)) NU hu eu NV hv ev) env_ok_nil) as H.
    rewrite xeval_strips_e, !map_map, !fold_map_seq in H.
    rewrite (nth_seq_map _ colf NV (pred NV) None ltac:(lia)) in H.
    exact H. }
  apply (widen_scale prec _ _ _ _ _ _ (lattice_vals prec ms binds n 0 hu NU 0 hv NV)
           (I.add_correct prec _ _ _ _ (lattice_errs prec hu NU hv NV cl) HEs)).
  cbv beta.
  match goal with
  | |- Rabs (?T - ?s) <= ?e1 + ?e2 =>
      match type of HbT with
      | Rabs (?T' - ?L) <= _ =>
          replace (T - s) with ((T - L) + (L - s)) by ring
      end
  end.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite Rplus_comm. apply Rplus_le_compat; [exact HbL | exact HbT].
Qed.

(* ---------------------------------------------------------------- *)
(* The integral along a curve                                        *)

(** The bound on the second derivative along the first angle over a cell of a
    curve, read off the enclosure and checked there, for each component. *)
Definition cell1_claims (prec : F.precision) (ms : list Z) (len : nat) (wu : list binding)
    (ns : list nat) (c h cv : Z) : option (list (Z * Z)) :=
  let envu := iextend prec (box_uv slot_u slot_v prec ms c h cv 0) wu in
  all_some (map (fun n => claim_of prec envu (Evar (n + 2 * len))) ns).

Lemma cell1_claims_ok :
  forall prec ms base len binds ns c h cv bs,
  cell1_claims prec ms len (with_derivs2 slot_u base len binds) ns c h cv = Some bs ->
  forall k, (k < length ns)%nat ->
  checks1 slot_u slot_v base len binds ms (nth k ns 0%nat) prec c h cv
    (fst (nth k bs (0%Z, 0%Z))) (snd (nth k bs (0%Z, 0%Z))) = true.
Proof.
  intros prec ms base len binds ns c h cv bs H k Hk.
  unfold cell1_claims in H. cbv zeta in H.
  pose proof (all_some_nth _ _ _ H k (0%Z, 0%Z) ltac:(rewrite length_map; exact Hk)) as Hn.
  rewrite (nth_map_lt _ _ _ ns k 0%nat None Hk) in Hn.
  unfold checks1. exact (claim_of_ok _ _ _ _ Hn).
Qed.

(** A cell of a run with the bound of component c on it. *)
Definition k1_of (c : nat) (ch : Z * Z) (o : option (list (Z * Z))) : claim1 :=
  let b := match o with Some bs => nth c bs (0%Z, 0%Z) | None => (0%Z, 0%Z) end in
  Claim1 (fst ch) (snd ch) (fst b) (snd b).

Definition err1 (prec : F.precision) (k : claim1) : I.type :=
  ieval prec eempty (Emul (EfromZ (2 * k1_h k * k1_h k * k1_h k)) (eps_e (k1_Nuu k) (k1_quu k))).

(** Consecutive cells, given as centre and half-width, share their end. *)
Fixpoint abut2 (l : list (Z * Z)) : bool :=
  match l with
  | a :: tl =>
      match tl with
      | b :: _ => (fst a + snd a =? fst b - snd b)%Z && abut2 tl
      | [] => true
      end
  | [] => true
  end.

Lemma abut_k1 :
  forall c (g : Z * Z -> option (list (Z * Z))) cells,
  abut (map (fun ch => k1_of c ch (g ch)) cells) = abut2 cells.
Proof.
  intros c g cells. induction cells as [| a tl IH]; [reflexivity |].
  destruct tl as [| b tl']; [reflexivity |].
  change (abut (k1_of c a (g a) :: map (fun ch => k1_of c ch (g ch)) (b :: tl'))
          = ((fst a + snd a =? fst b - snd b)%Z && abut2 (b :: tl'))%bool).
  rewrite <- IH. reflexivity.
Qed.

(** The integral of each component along a run of abutting cells at the
    second angle cv, scaled by 2^k for the exponent of the first slot, beside
    the scaled sum of the errors of its cells; none when a check fails. *)
Definition integ1 (prec : F.precision) (es ms : list Z) (cfg : pconfig) (modes : list (Z * Z))
    (cv : Z) (cells : list (Z * Z)) : option (list (I.type * I.type)) :=
  if Nat.eqb slot_u slot_v then None else
  let r3 := residual es cfg modes in
  let binds := r_binds r3 in
  let len := length binds in
  let base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes) in
  match slots3 r3, cells with
  | None, _ => None
  | _, [] => None
  | Some ns, _ :: _ =>
      if forallb (node_ok ms base len binds) ns && abut2 cells &&
         forallb (fun ch => Z.leb 0 (snd ch)) cells then
        let wu := with_derivs2 slot_u base len binds in
        let cls := map (fun ch => cell1_claims prec ms len wu ns (fst ch) (snd ch) cv) cells in
        if forallb is_some cls then
          let vals := map (fun ch => cell_vals prec ms binds ns (2 * snd ch) (fst ch) cv) cells in
          let k := nth slot_u es 0%Z in
          Some (map (fun c =>
                  let E := isum prec (map (fun p => err1 prec (k1_of c (fst p) (snd p)))
                                        (combine cells cls)) in
                  (widen prec (isum prec (map (fun l => nth c l I.nai) vals)) E k,
                   I.mul prec E (ieval prec eempty (Epow2 k))))
                (seq 0 (length ns)))
        else None
      else None
  end.

(** A run of abutting cells, each enclosed, encloses the integral over the run. *)
Lemma run_encloses :
  forall (f : R -> R) (vI eI : claim1 -> R) (l : list claim1) c0 z,
  abut (c0 :: l) = true ->
  (forall c, In c (c0 :: l) ->
     ex_RInt f (IZR (lo1 c)) (IZR (hi1 c)) /\ Rabs (RInt f (IZR (lo1 c)) (IZR (hi1 c)) - vI c) <= eI c) ->
  ex_RInt f (IZR (lo1 c0)) (IZR (hi1 (last (c0 :: l) z))) /\
  Rabs (RInt f (IZR (lo1 c0)) (IZR (hi1 (last (c0 :: l) z))) - fold_right Rplus 0 (map vI (c0 :: l)))
  <= fold_right Rplus 0 (map eI (c0 :: l)).
Proof.
  intros f vI eI l. induction l as [| d l IH]; intros c0 z Hab Hc.
  - destruct (Hc c0 (or_introl eq_refl)) as [Hex Hb]. cbn [last map fold_right].
    split; [exact Hex |]. replace (vI c0 + 0) with (vI c0) by ring. replace (eI c0 + 0) with (eI c0) by ring.
    exact Hb.
  - cbn [abut] in Hab. apply andb_prop in Hab. destruct Hab as [Hcd Hab]. apply Z.eqb_eq in Hcd.
    destruct (Hc c0 (or_introl eq_refl)) as [Hex0 Hb0].
    destruct (IH d z Hab (fun c Hin => Hc c (or_intror Hin))) as [Hex1 Hb1].
    assert (Hlast : last (c0 :: d :: l) z = last (d :: l) z) by reflexivity.
    rewrite Hlast. rewrite <- Hcd in Hex1, Hb1.
    assert (Hsplit : ex_RInt f (IZR (lo1 c0)) (IZR (hi1 (last (d :: l) z))))
      by (apply (ex_RInt_Chasles f _ (IZR (hi1 c0))); assumption).
    split; [exact Hsplit |].
    assert (Hch : RInt f (IZR (lo1 c0)) (IZR (hi1 (last (d :: l) z)))
                  = RInt f (IZR (lo1 c0)) (IZR (hi1 c0)) + RInt f (IZR (hi1 c0)) (IZR (hi1 (last (d :: l) z)))).
    { symmetry.
      replace (RInt f (IZR (lo1 c0)) (IZR (hi1 c0)) + RInt f (IZR (hi1 c0)) (IZR (hi1 (last (d :: l) z))))
        with (plus (RInt f (IZR (lo1 c0)) (IZR (hi1 c0))) (RInt f (IZR (hi1 c0)) (IZR (hi1 (last (d :: l) z)))))
        by reflexivity.
      apply RInt_Chasles; assumption. }
    rewrite Hch. cbn [map fold_right] in *.
    replace (RInt f (IZR (lo1 c0)) (IZR (hi1 c0)) + RInt f (IZR (hi1 c0)) (IZR (hi1 (last (d :: l) z)))
             - (vI c0 + (vI d + fold_right Rplus 0 (map vI l))))
      with ((RInt f (IZR (lo1 c0)) (IZR (hi1 c0)) - vI c0)
            + (RInt f (IZR (hi1 c0)) (IZR (hi1 (last (d :: l) z))) - (vI d + fold_right Rplus 0 (map vI l))))
      by ring.
    eapply Rle_trans; [apply Rabs_triang |]. lra.
Qed.

(** One component, from bounds on the cells of a run that pass the checks. *)
Lemma integ1_core :
  forall (Huv : slot_u <> slot_v) prec es ms cfg modes n cv (k0 : claim1) (l : list claim1) q,
  let r3 := residual es cfg modes in
  let binds := r_binds r3 in
  let len := length binds in
  let base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes) in
  node_ok ms base len binds n = true -> abut (k0 :: l) = true ->
  (forall k, In k (k0 :: l) -> (0 <= k1_h k)%Z /\
     checks1 slot_u slot_v base len binds ms n prec (k1_c k) (k1_h k) cv (k1_Nuu k) (k1_quu k) = true) ->
  let f := fun u => cellf slot_u slot_v binds n ms u (IZR cv) in
  let a := IZR (lo1 k0) in
  let b := IZR (hi1 (last (k0 :: l) k0)) in
  ex_RInt f a b /\
  contains (I.convert (widen prec
      (isum prec (map (fun k => I.mul prec (I.fromZ prec (2 * k1_h k))
          (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (k1_c k) 0 cv 0) binds) (Evar n)))
          (k0 :: l)))
      (isum prec (map (err1 prec) (k0 :: l))) q))
    (Xreal (RInt f a b * powerRZ 2 q)).
Proof.
  intros Huv prec es ms cfg modes n cv k0 l q r3 binds len base Hnode Hab Hall f a b.
  destruct (node_ok_facts ms base len binds n Hnode) as (Hms & Hbu & Hbv & Hlen0 & Hwf & Hbn & Hnl).
  set (vI := fun c => 2 * IZR (k1_h c) * f (IZR (k1_c c))).
  set (eI := fun c => 2 * (IZR (k1_Nuu c) * powerRZ 2 (k1_quu c)) * IZR (k1_h c) * IZR (k1_h c) * IZR (k1_h c)).
  assert (Hcells : forall c, In c (k0 :: l) ->
            ex_RInt f (IZR (lo1 c)) (IZR (hi1 c)) /\ Rabs (RInt f (IZR (lo1 c)) (IZR (hi1 c)) - vI c) <= eI c).
  { intros c Hin. destruct (Hall c Hin) as [Hh Hck].
    pose proof (cell1_cert slot_u slot_v Huv base len binds ms n Hms Hbu Hbv Hlen0 Hwf eq_refl Hbn Hnl prec
                  (k1_c c) (k1_h c) cv (k1_Nuu c) (k1_quu c) Hh Hck) as H.
    cbv zeta in H. unfold lo1, hi1. rewrite minus_IZR, plus_IZR. exact H. }
  destruct (run_encloses f vI eI l k0 k0 Hab Hcells) as [Hex Hb].
  split; [exact Hex |].
  assert (HS : contains (I.convert (isum prec (map (fun k =>
                   I.mul prec (I.fromZ prec (2 * k1_h k))
                     (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (k1_c k) 0 cv 0) binds) (Evar n)))
                   (k0 :: l)))) (Xreal (fold_right Rplus 0 (map vI (k0 :: l))))).
  { apply isum_map. intros c Hin. cbv beta.
    unfold vI. replace (2 * IZR (k1_h c) * f (IZR (k1_c c))) with (IZR (2 * k1_h c) * f (IZR (k1_c c)))
      by (rewrite mult_IZR; ring).
    exact (I.mul_correct prec _ _ (Xreal (IZR (2 * k1_h c))) (Xreal (f (IZR (k1_c c))))
             (I.fromZ_correct prec (2 * k1_h c))
             (centre_val slot_u slot_v binds ms n prec (k1_c c) cv)). }
  assert (HE : contains (I.convert (isum prec (map (err1 prec) (k0 :: l))))
                 (Xreal (fold_right Rplus 0 (map eI (k0 :: l))))).
  { apply isum_map. intros c Hin. unfold err1.
    assert (Hev := ieval_correct prec eempty eempty
                     (Emul (EfromZ (2 * k1_h c * k1_h c * k1_h c)) (eps_e (k1_Nuu c) (k1_quu c))) env_ok_nil).
    unfold eps_e, epow2 in Hev. simpl in Hev. unfold eI.
    replace (2 * (IZR (k1_Nuu c) * powerRZ 2 (k1_quu c)) * IZR (k1_h c) * IZR (k1_h c) * IZR (k1_h c))
      with (IZR (2 * k1_h c * k1_h c * k1_h c) * (IZR (k1_Nuu c) * powerRZ 2 (k1_quu c)))
      by (rewrite !mult_IZR; ring).
    exact Hev. }
  exact (widen_scale prec _ _ _ _ _ q HS HE Hb).
Qed.

Theorem integ1_correct :
  forall prec es ms cfg modes cv cells Os,
  integ1 prec es ms cfg modes cv cells = Some Os ->
  let r3 := residual es cfg modes in
  forall c, (c < 3)%nat ->
  exists n ch0 l, slot_of (comp_of r3 c) = Some n /\ cells = ch0 :: l /\
  let f := fun u => cellf slot_u slot_v (r_binds r3) n ms u (IZR cv) in
  let a := IZR (fst ch0 - snd ch0) in
  let b := IZR (fst (last cells ch0) + snd (last cells ch0)) in
  ex_RInt f a b /\
  contains (I.convert (fst (nth c Os (I.nai, I.nai))))
    (Xreal (RInt f a b * powerRZ 2 (nth slot_u es 0%Z))).
Proof.
  intros prec es ms cfg modes cv cells Os Hi r3 c Hc.
  unfold integ1 in Hi.
  destruct (Nat.eqb slot_u slot_v) eqn:Heq; [discriminate |].
  apply Nat.eqb_neq in Heq.
  cbv zeta in Hi. fold r3 in Hi.
  set (binds := r_binds r3) in *. set (len := length binds) in *.
  set (base := base_scratch_of (pc_lasym cfg) (pc_out cfg) (length modes)) in *.
  destruct (slots3 r3) as [ns |] eqn:Hns; [| discriminate].
  destruct cells as [| ch0 l]; [discriminate |].
  destruct (slots3_comp r3 ns Hns) as [Hlen3 Hslot].
  exists (nth c ns 0%nat), ch0, l. split; [exact (Hslot c Hc) |]. split; [reflexivity |].
  destruct (forallb (node_ok ms base len binds) ns && abut2 (ch0 :: l) &&
            forallb (fun ch => (0 <=? snd ch)%Z) (ch0 :: l)) eqn:Hc1; [| discriminate].
  set (g := fun ch : Z * Z =>
              cell1_claims prec ms len (with_derivs2 slot_u base len binds) ns (fst ch) (snd ch) cv) in *.
  destruct (forallb is_some (map g (ch0 :: l))) eqn:Hc2; [| discriminate].
  (* injection would normalize the terms, so the equation is read off with
     beta and iota alone *)
  apply (f_equal (fun o => match o with Some x => x | None => Os end)) in Hi.
  cbv beta iota in Hi. subst Os.
  repeat rewrite andb_true_iff in Hc1. destruct Hc1 as [[Hnodes Habut] Hpos].
  assert (Hcn : (c < length ns)%nat) by lia.
  rewrite (nth_seq_map _ _ (length ns) c (I.nai, I.nai) Hcn). cbv beta. cbn [fst].
  set (K := fun ch => k1_of c ch (g ch)).
  assert (HS : map (fun l0 => nth c l0 I.nai)
                 (map (fun ch => cell_vals prec ms binds ns (2 * snd ch) (fst ch) cv) (ch0 :: l))
             = map (fun k => I.mul prec (I.fromZ prec (2 * k1_h k))
                 (ieval prec (iextend prec (box_uv slot_u slot_v prec ms (k1_c k) 0 cv 0) binds)
                    (Evar (nth c ns 0%nat)))) (map K (ch0 :: l))).
  { rewrite !map_map. apply map_ext. intros ch. rewrite cell_vals_nth by exact Hcn. reflexivity. }
  assert (HE : map (fun p => err1 prec (k1_of c (fst p) (snd p))) (combine (ch0 :: l) (map g (ch0 :: l)))
             = map (err1 prec) (map K (ch0 :: l))).
  { rewrite combine_map, !map_map. reflexivity. }
  assert (Hlast : (fst (last (ch0 :: l) ch0) + snd (last (ch0 :: l) ch0))%Z
                  = hi1 (last (map K (ch0 :: l)) (K ch0))).
  { rewrite (last_map_d _ _ K (ch0 :: l) ch0). reflexivity. }
  rewrite HS, HE. cbv zeta. rewrite Hlast.
  pose proof (integ1_core Heq prec es ms cfg modes (nth c ns 0%nat) cv (K ch0) (map K l)
                (nth slot_u es 0%Z)) as Hcore.
  cbv zeta in Hcore.
  apply Hcore.
  - apply (proj1 (forallb_forall _ _) Hnodes). apply nth_In. exact Hcn.
  - change (abut (map K (ch0 :: l)) = true). unfold K. rewrite abut_k1. exact Habut.
  - intros k Hk. change (In k (map K (ch0 :: l))) in Hk.
    apply in_map_iff in Hk. destruct Hk as [ch [<- Hch]].
    split.
    + apply (proj1 (forallb_forall _ _) Hpos) in Hch. apply Z.leb_le in Hch. exact Hch.
    + pose proof (forallb_map_in _ _ is_some g _ _ Hc2 Hch) as Hs.
      unfold K, k1_of. destruct (g ch) as [bs |] eqn:Hg; [| discriminate].
      exact (cell1_claims_ok prec ms base len binds ns _ _ _ bs Hg c Hcn).
Qed.

End Integrators.
