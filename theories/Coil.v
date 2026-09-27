(** An invariant torus of a coil field, from a certified bound on how far a
    trigonometric torus is from being invariant.

    A certificate of Physics.RCoil carries a torus as a finite Fourier series
    in two angles and a coil set as the source points of the trapezoidal
    Biot-Savart rule. [coil_torus] and [coil_field] are those two objects as
    real functions of a state, read from the same slots, and [coil_sine] is
    the component the certificate bounds, the sine of the angle between the
    field and the torus as Physics.v writes it, at angles in radians.

    Two certificates bound it. A covering of the whole torus by Taylor cells
    (BoxCell.bt_surface) gives [coil_sine_bound]: the sine is at most the
    largest cell bound at every point. Point certificates at the points of a
    grid (BoxCell.check_bpcert_correct) give [coil_grid_bound]: the sine is at
    most the largest point bound at every point of the grid.

    The step from there to an invariant torus is the a posteriori KAM theorem,
    carried as the hypothesis [Hypotheses.kam_nearby], or
    [Hypotheses.kam_from_points] for a grid, and [coil_torus_nearby] and
    [coil_torus_from_grid] are the conclusions under it: an invariant torus of
    the coil field lies within the distance the hypothesis names of the
    certified one. *)

From Coq Require Import ZArith Reals List Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Checker Hypotheses Box Integral BoxCell.

Import ListNotations.
Local Open Scope R_scope.

(** A sum over 0 .. n - 1. *)
Fixpoint csum (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => csum f k + f k end.

Section Objects.

(** The modes, the slot exponents and a state (mantissas), as a certificate
    lays them out. *)
Variable lasym : bool.
Variable modes : list (Z * Z).
Variable es : list Z.
Variable xs : list R.

(** The value of slot k of the state: its mantissa times its power of two. *)
Definition sval (k : nat) : R := nth k xs 0 * powerRZ 2 (nth k es 0%Z).

Let K := length modes.
Let mode_m (k : nat) : R := IZR (fst (nth k modes (0%Z, 0%Z))).
Let mode_n (k : nat) : R := IZR (snd (nth k modes (0%Z, 0%Z))).

(** The torus: R cos(m u - n v) and Z sin(m u - n v) over the modes, from the
    first node row of the R and Z blocks, at the geometric toroidal angle v. *)
Definition coil_torus (u v : R) : vec3 :=
  let Rt := csum (fun k => sval (base_R K + k) * cos (mode_m k * u - mode_n k * v)) K in
  let Zt := csum (fun k => sval (base_Z K + k) * sin (mode_m k * u - mode_n k * v)) K in
  (Rt * cos v, Rt * sin v, Zt).

(** The field: over the source points of the block after the state, the
    weighted tangent crossed with (x - point), over |x - point|^3. *)
Definition coil_field (P : nat) (x : vec3) : vec3 :=
  let b := base_W lasym K in
  let p j : vec3 := (sval (b + 6 * j), sval (b + 6 * j + 1), sval (b + 6 * j + 2)) in
  let d j : vec3 := (sval (b + 6 * j + 3), sval (b + 6 * j + 4), sval (b + 6 * j + 5)) in
  let r j : vec3 :=
    let '(x1, x2, x3) := x in let '(p1, p2, p3) := p j in (x1 - p1, x2 - p2, x3 - p3) in
  let term j : vec3 :=
    let q := dot3 (r j) (r j) in
    let '(c1, c2, c3) := cross3r (d j) (r j) in
    (c1 / (q * sqrt q), c2 / (q * sqrt q), c3 / (q * sqrt q)) in
  (csum (fun j => coord1 (term j)) P,
   csum (fun j => coord2 (term j)) P,
   csum (fun j => coord3 (term j)) P).

End Objects.

(** The component a certificate bounds, at the angles U and V in radians. *)
Definition coil_sine (su sv : nat) (es : list Z) (r3 : residual3) (comp : nat)
    (xs : list R) (U V : R) : R :=
  proj_val
    (xeval (surf su sv (r_binds r3) (xenv_R xs)
                 (U / powerRZ 2 (nth su es 0%Z)) (V / powerRZ 2 (nth sv es 0%Z)))
           (icomp r3 comp)).

(* ---------------------------------------------------------------- *)
(* The covering                                                      *)

Definition bt_sine (c : btcert) : list R -> R -> R -> R :=
  coil_sine (btc_su c) (btc_sv c) (btc_es c) (btres c) (btc_comp c).

(** Over a grid of cells that spans both angles over a full turn, the sine is
    at most the largest cell bound at every point of the torus and every state
    of the box. *)
Theorem coil_sine_bound :
  forall c au av nu nv,
  check_btcert c = true -> bt_tiles c au av nu nv = true ->
  bt_period c au av nu nv 1 = true ->
  forall xs, in_box (btc_ms c) (btc_ds c) xs ->
  forall U V, 0 <= U <= 2 * PI -> 0 <= V <= 2 * PI ->
  Rabs (bt_sine c xs U V) <= btsup c.
Proof.
  intros c au av nu nv Hc Ht Hp xs Hin U V HU HV.
  assert (HV1 : 0 <= V <= 2 * PI / IZR 1).
  { replace (2 * PI / IZR 1) with (2 * PI) by (simpl; field). exact HV. }
  destruct (bt_surface c au av nu nv 1 Hc Ht Hp xs Hin U V HU HV1) as [w [Hw Hb]].
  unfold bt_sine, coil_sine. rewrite Hw. exact Hb.
Qed.

(** Under the KAM hypothesis with the certified bound, an invariant torus of
    the coil field lies within delta of the certified torus. *)
Theorem coil_torus_nearby :
  forall c au av nu nv P delta,
  check_btcert c = true -> bt_tiles c au av nu nv = true ->
  bt_period c au av nu nv 1 = true ->
  forall xs, in_box (btc_ms c) (btc_ds c) xs ->
  let lasym := pc_lasym (btc_cfg c) in
  kam_nearby (coil_field lasym (btc_modes c) (btc_es c) xs P)
             (coil_torus (btc_modes c) (btc_es c) xs) (bt_sine c xs) (btsup c) delta ->
  exists T', invariant_torus (coil_field lasym (btc_modes c) (btc_es c) xs P) T' /\
             forall u v, dist3 (T' u v) (coil_torus (btc_modes c) (btc_es c) xs u v) <= delta.
Proof.
  intros c au av nu nv P delta Hc Ht Hp xs Hin lasym Hk.
  apply Hk. intros u v Hu Hv.
  exact (coil_sine_bound c au av nu nv Hc Ht Hp xs Hin u v Hu Hv).
Qed.

(* ---------------------------------------------------------------- *)
(* The grid                                                          *)

Definition bp_sine (c : bpcert) : list R -> R -> R -> R :=
  coil_sine (bpc_su c) (bpc_sv c) (bpc_es c) (bpres c) (bpc_comp c).

(** The listed points in radians, and the largest bound claimed at them. *)
Definition grid_angles (c : bpcert) : list (R * R) :=
  map (fun p => (IZR (bp_mu p) * powerRZ 2 (nth (bpc_su c) (bpc_es c) 0%Z),
                 IZR (bp_mv p) * powerRZ 2 (nth (bpc_sv c) (bpc_es c) 0%Z)))
      (bpc_pts c).

Definition bpsup (c : bpcert) : R :=
  fold_right Rmax 0 (map (fun p => IZR (bp_N p) * powerRZ 2 (bp_q p)) (bpc_pts c)).

Lemma fold_Rmax_ge' : forall l x, In x l -> x <= fold_right Rmax 0 l.
Proof.
  induction l as [|a l IH]; intros x Hx; simpl in Hx |- *. contradiction.
  destruct Hx as [<-|Hx]. apply Rmax_l.
  eapply Rle_trans. apply IH, Hx. apply Rmax_r.
Qed.

Lemma scale_back : forall m e, IZR m * powerRZ 2 e / powerRZ 2 e = IZR m.
Proof.
  intros m e. assert (H : 0 < powerRZ 2 e) by (apply powerRZ_lt; lra).
  field. lra.
Qed.

(** A certificate whose every point claims a ceiling bounds the sine at every
    listed point, at every state of the box, by the largest ceiling. *)
Theorem coil_grid_bound :
  forall c, check_bpcert c = true ->
  List.Forall (fun p => bp_mode p = 0%Z) (bpc_pts c) ->
  forall xs, in_box (bpc_ms c) (bpc_ds c) xs ->
  forall q, In q (grid_angles c) -> Rabs (bp_sine c xs (fst q) (snd q)) <= bpsup c.
Proof.
  intros c Hc Hm xs Hin q Hq.
  unfold grid_angles in Hq. apply in_map_iff in Hq. destruct Hq as [p [<- Hp]].
  assert (Hs := proj1 (List.Forall_forall _ _) (check_bpcert_correct c Hc) p Hp xs Hin).
  assert (Hp0 := proj1 (List.Forall_forall _ _) Hm p Hp).
  destruct Hs as [w [Hw Hb]].
  unfold bp_sine, coil_sine. simpl fst. simpl snd.
  rewrite !scale_back. rewrite Hw. simpl proj_val.
  unfold bpt_claim in Hb. rewrite Hp0 in Hb. simpl in Hb.
  eapply Rle_trans. exact Hb.
  apply fold_Rmax_ge'. apply in_map_iff. exists p. split. reflexivity. exact Hp.
Qed.

(** Under the KAM hypothesis for a grid, with the grid filling the torus to
    within h, an invariant torus of the coil field lies within delta of the
    certified torus. *)
Theorem coil_torus_from_grid :
  forall c P h delta,
  check_bpcert c = true ->
  List.Forall (fun p => bp_mode p = 0%Z) (bpc_pts c) ->
  forall xs, in_box (bpc_ms c) (bpc_ds c) xs ->
  (forall u v, 0 <= u <= 2 * PI -> 0 <= v <= 2 * PI ->
     exists p, In p (grid_angles c) /\ Rabs (u - fst p) <= h /\ Rabs (v - snd p) <= h) ->
  let lasym := pc_lasym (bpc_cfg c) in
  kam_from_points (coil_field lasym (bpc_modes c) (bpc_es c) xs P)
                  (coil_torus (bpc_modes c) (bpc_es c) xs) (bp_sine c xs)
                  (grid_angles c) h (bpsup c) delta ->
  exists T', invariant_torus (coil_field lasym (bpc_modes c) (bpc_es c) xs P) T' /\
             forall u v, dist3 (T' u v) (coil_torus (bpc_modes c) (bpc_es c) xs u v) <= delta.
Proof.
  intros c P h delta Hc Hm xs Hin Hfill lasym Hk.
  apply Hk. exact Hfill.
  intros q Hq. exact (coil_grid_bound c Hc Hm xs Hin q Hq).
Qed.
