(** Cells that cover a rectangle, decided in integers.

    [Cover.covers] decides that intervals of one coordinate cover a range. A
    verdict over two coordinates, the radius and an angle or two angles,
    speaks about the rectangle its cells span only if every point of that
    rectangle lies in one of them, and the projections on the two axes do not
    decide that: cells can cover each axis and leave a hole. [cover2] decides
    it column by column. The cells are gathered into runs of one extent in the
    first coordinate; the extents of the runs have to cover the range of the
    first coordinate, and the cells of each run the range of the second. The
    order of the cells is the caller's, who lists the cells of a column
    together and everything in ascending order: an order that does not do
    that makes the check fail, never pass.

    A cell with no width in one coordinate lies on a line of it, and a verdict
    over such cells speaks about the lines: [cover_lines] gathers the cells by
    their line and decides that each line is covered along the other
    coordinate.

    A cell's extent in a coordinate is its centre mantissa m, the exponent e of
    that coordinate and its half-width d in units of 2^e. The checks compare
    extents at the finest exponent of the list, where every end is an integer,
    and [cells_cover_rect] and [cells_cover_lines] state the result in the
    mantissa units of each cell, the terms [Cell.in_cell] reads. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Stellarocq Require Import Checker Cover Cell.

Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- *)
(* Extents at a common exponent                                      *)

Record ext := Ext { x_m : Z ; x_e : Z ; x_d : Z }.

(** The finest exponent of a list, starting from e. *)
Definition emin (l : list ext) (e : Z) : Z := fold_right (fun x a => Z.min (x_e x) a) e l.

Lemma emin_le : forall l e x, In x l -> emin l e <= x_e x.
Proof.
  induction l as [|y l IH]; intros e x H; [destruct H |].
  simpl. destruct H as [-> | H]; [lia |]. specialize (IH e x H). lia.
Qed.

(** Centre, half-width and ends of an extent in units of 2^f. *)
Definition mid_at (f : Z) (x : ext) : Z := x_m x * 2 ^ (x_e x - f).
Definition half_at (f : Z) (x : ext) : Z := x_d x * 2 ^ (x_e x - f).
Definition lo_at (f : Z) (x : ext) : Z := mid_at f x - half_at f x.
Definition hi_at (f : Z) (x : ext) : Z := mid_at f x + half_at f x.

Definition span_lo (f : Z) (l : list ext) (z : Z) : Z := fold_right (fun x a => Z.min (lo_at f x) a) z l.
Definition span_hi (f : Z) (l : list ext) (z : Z) : Z := fold_right (fun x a => Z.max (hi_at f x) a) z l.

(** The exponents and the rectangle of a list of cells. *)
Definition fu_of (cs : list (ext * ext)) : Z :=
  match cs with [] => 0 | p :: _ => emin (map fst cs) (x_e (fst p)) end.
Definition fv_of (cs : list (ext * ext)) : Z :=
  match cs with [] => 0 | p :: _ => emin (map snd cs) (x_e (snd p)) end.
Definition ulo_of (cs : list (ext * ext)) : Z :=
  match cs with [] => 0 | p :: _ => span_lo (fu_of cs) (map fst cs) (lo_at (fu_of cs) (fst p)) end.
Definition uhi_of (cs : list (ext * ext)) : Z :=
  match cs with [] => 0 | p :: _ => span_hi (fu_of cs) (map fst cs) (hi_at (fu_of cs) (fst p)) end.
Definition vlo_of (cs : list (ext * ext)) : Z :=
  match cs with [] => 0 | p :: _ => span_lo (fv_of cs) (map snd cs) (lo_at (fv_of cs) (snd p)) end.
Definition vhi_of (cs : list (ext * ext)) : Z :=
  match cs with [] => 0 | p :: _ => span_hi (fv_of cs) (map snd cs) (hi_at (fv_of cs) (snd p)) end.

Lemma fu_of_le : forall cs p, In p cs -> fu_of cs <= x_e (fst p).
Proof.
  intros [| q cs] p H; [destruct H |]. unfold fu_of.
  apply emin_le. apply in_map. exact H.
Qed.

Lemma fv_of_le : forall cs p, In p cs -> fv_of cs <= x_e (snd p).
Proof.
  intros [| q cs] p H; [destruct H |]. unfold fv_of.
  apply emin_le. apply in_map. exact H.
Qed.

(* ---------------------------------------------------------------- *)
(* Runs of one key                                                   *)

(** Consecutive entries of one key, gathered under it. *)
Fixpoint runs {K V : Type} (eqk : K -> K -> bool) (l : list (K * V)) : list (K * list V) :=
  match l with
  | [] => []
  | (k, v) :: tl =>
      match runs eqk tl with
      | (k', vs) :: rest =>
          if eqk k k' then (k, v :: vs) :: rest else (k, [v]) :: (k', vs) :: rest
      | [] => [(k, [v])]
      end
  end.

Section Runs.

Variables (K V : Type) (eqk : K -> K -> bool).
Hypothesis Heqk : forall a b, eqk a b = true -> a = b.

(** An entry of a run is an entry of the list, under the run's key. *)
Lemma runs_sound :
  forall (l : list (K * V)) (k : K) (vs : list V) (v : V),
  In (k, vs) (runs eqk l) -> In v vs -> In (k, v) l.
Proof.
  induction l as [| [k0 v0] tl IH]; intros k vs v Hr Hv; [destruct Hr |].
  simpl in Hr. destruct (runs eqk tl) as [| [k' vs'] rest] eqn:Ht.
  - destruct Hr as [Hr | []]. injection Hr as <- <-.
    destruct Hv as [<- | []]. left. reflexivity.
  - destruct (eqk k0 k') eqn:Hk.
    + apply Heqk in Hk. subst k'. destruct Hr as [Hr | Hr].
      * injection Hr as <- <-. destruct Hv as [<- | Hv]; [left; reflexivity |].
        right. apply (IH k0 vs'); [left; reflexivity | exact Hv].
      * right. apply (IH k vs); [right; exact Hr | exact Hv].
    + destruct Hr as [Hr | Hr].
      * injection Hr as <- <-. destruct Hv as [<- | []]. left. reflexivity.
      * right. apply (IH k vs); [exact Hr | exact Hv].
Qed.

(** An entry of the list lies in a run of its key. *)
Lemma runs_complete :
  forall (l : list (K * V)) (k : K) (v : V),
  In (k, v) l -> exists vs, In (k, vs) (runs eqk l) /\ In v vs.
Proof.
  induction l as [| [k0 v0] tl IH]; intros k v H; [destruct H |].
  simpl. destruct H as [H | H].
  - injection H as <- <-.
    destruct (runs eqk tl) as [| [k' vs'] rest].
    + exists [v0]. split; left; reflexivity.
    + destruct (eqk k0 k').
      * exists (v0 :: vs'). split; left; reflexivity.
      * exists [v0]. split; left; reflexivity.
  - destruct (IH k v H) as [vs [Hr Hv]].
    destruct (runs eqk tl) as [| [k' vs'] rest] eqn:Ht; [destruct Hr |].
    destruct (eqk k0 k') eqn:Hk.
    + apply Heqk in Hk. subst k'. destruct Hr as [Hr | Hr].
      * injection Hr as Hk0 Hvs. subst k vs'.
        exists (v0 :: vs). split; [left; reflexivity | right; exact Hv].
      * exists vs. split; [right; exact Hr | exact Hv].
    + exists vs. split; [right; exact Hr | exact Hv].
Qed.

End Runs.

(* ---------------------------------------------------------------- *)
(* The rectangle, column by column                                   *)

(** Both extents of every cell at the finest exponents, as centre and
    half-width. *)
Definition prep_rect (fu fv : Z) (cs : list (ext * ext)) : list ((Z * Z) * (Z * Z)) :=
  map (fun p => ((mid_at fu (fst p), half_at fu (fst p)), (mid_at fv (snd p), half_at fv (snd p)))) cs.

Lemma prep_rect_in :
  forall fu fv cs c d c' d', In ((c, d), (c', d')) (prep_rect fu fv cs) ->
  exists p, In p cs /\
    lo_at fu (fst p) = c - d /\ hi_at fu (fst p) = c + d /\
    lo_at fv (snd p) = c' - d' /\ hi_at fv (snd p) = c' + d'.
Proof.
  intros fu fv cs c d c' d' H. unfold prep_rect in H.
  apply in_map_iff in H. destruct H as [p [Hp Hin]].
  injection Hp as Hmu Hhu Hmv Hhv.
  exists p. unfold lo_at, hi_at. rewrite Hmu, Hhu, Hmv, Hhv. repeat split; exact Hin || reflexivity.
Qed.

Definition pair_eqb (a b : Z * Z) : bool := (fst a =? fst b) && (snd a =? snd b).

Lemma pair_eqb_eq : forall a b, pair_eqb a b = true -> a = b.
Proof.
  intros [a1 a2] [b1 b2] H. unfold pair_eqb in H. simpl in H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

(** The cells cover the rectangle they span: the runs of one extent in the
    first coordinate cover its range, and the cells of each run the range of
    the second. *)
Definition cover2 (cs : list (ext * ext)) : bool :=
  match cs with
  | [] => false
  | _ :: _ =>
      let fu := fu_of cs in
      let fv := fv_of cs in
      let vlo := vlo_of cs in
      let vhi := vhi_of cs in
      let rs := runs pair_eqb (prep_rect fu fv cs) in
      covers (ulo_of cs) (uhi_of cs) (map fst rs) &&
      forallb (fun r => covers vlo vhi (snd r)) rs
  end.

Theorem cover2_correct :
  forall cs, cover2 cs = true ->
  forall x y : R,
  (IZR (ulo_of cs) <= x <= IZR (uhi_of cs))%R -> (IZR (vlo_of cs) <= y <= IZR (vhi_of cs))%R ->
  exists p, In p cs /\
    (IZR (lo_at (fu_of cs) (fst p)) <= x <= IZR (hi_at (fu_of cs) (fst p)))%R /\
    (IZR (lo_at (fv_of cs) (snd p)) <= y <= IZR (hi_at (fv_of cs) (snd p)))%R.
Proof.
  intros cs Hc x y Hx Hy. unfold cover2 in Hc.
  destruct cs as [| q cs']; [discriminate |]. cbv beta iota zeta in Hc.
  set (cs := q :: cs') in *.
  apply andb_prop in Hc. destruct Hc as [Hu Hv].
  rewrite forallb_forall in Hv.
  destruct (covers_correct _ _ _ x Hu Hx) as [c [d [Hin Hcd]]].
  apply in_map_iff in Hin. destruct Hin as [[k vs] [Hk Hr]]. simpl in Hk. subst k.
  destruct (covers_correct _ _ _ y (Hv _ Hr) Hy) as [c' [d' [Hin' Hcd']]].
  simpl in Hin'.
  pose proof (runs_sound _ _ pair_eqb pair_eqb_eq _ _ _ _ Hr Hin') as Hp.
  destruct (prep_rect_in _ _ _ _ _ _ _ Hp) as [p [Hp' [E1 [E2 [E3 E4]]]]].
  exists p. split; [exact Hp' |]. rewrite E1, E2, E3, E4. split; assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Lines                                                             *)

(** Every cell's line, its centre in the second coordinate, with its extent
    in the first. *)
Definition prep_lines (fu fv : Z) (cs : list (ext * ext)) : list (Z * (Z * Z)) :=
  map (fun p => (mid_at fv (snd p), (mid_at fu (fst p), half_at fu (fst p)))) cs.

Lemma prep_lines_in :
  forall fu fv cs k c d, In (k, (c, d)) (prep_lines fu fv cs) ->
  exists p, In p cs /\ mid_at fv (snd p) = k /\
    lo_at fu (fst p) = c - d /\ hi_at fu (fst p) = c + d.
Proof.
  intros fu fv cs k c d H. unfold prep_lines in H.
  apply in_map_iff in H. destruct H as [p [Hp Hin]].
  injection Hp as Hk Hm Hh.
  exists p. unfold lo_at, hi_at. rewrite Hm, Hh. repeat split; exact Hin || exact Hk || reflexivity.
Qed.

(** Every line the cells lie on is covered over the range of the first
    coordinate by the run of cells on it. *)
Definition cover_lines (cs : list (ext * ext)) : bool :=
  match cs with
  | [] => false
  | _ :: _ =>
      let ulo := ulo_of cs in
      let uhi := uhi_of cs in
      forallb (fun r => covers ulo uhi (snd r)) (runs Z.eqb (prep_lines (fu_of cs) (fv_of cs) cs))
  end.

Theorem cover_lines_correct :
  forall cs, cover_lines cs = true ->
  forall p0, In p0 cs -> forall x : R, (IZR (ulo_of cs) <= x <= IZR (uhi_of cs))%R ->
  exists p, In p cs /\ mid_at (fv_of cs) (snd p) = mid_at (fv_of cs) (snd p0) /\
    (IZR (lo_at (fu_of cs) (fst p)) <= x <= IZR (hi_at (fu_of cs) (fst p)))%R.
Proof.
  intros cs Hc p0 Hp0 x Hx. unfold cover_lines in Hc.
  destruct cs as [| q cs']; [discriminate |]. cbv beta iota zeta in Hc.
  set (cs := q :: cs') in *.
  rewrite forallb_forall in Hc.
  assert (Heq : forall a b, (a =? b) = true -> a = b) by (intros a b H; apply Z.eqb_eq; exact H).
  assert (Hin0 : In (mid_at (fv_of cs) (snd p0), (mid_at (fu_of cs) (fst p0), half_at (fu_of cs) (fst p0)))
                    (prep_lines (fu_of cs) (fv_of cs) cs)).
  { unfold prep_lines. apply in_map_iff. exists p0. split; [reflexivity | exact Hp0]. }
  destruct (runs_complete _ _ Z.eqb Heq _ _ _ Hin0) as [vs [Hr Hv]].
  destruct (covers_correct _ _ _ x (Hc _ Hr) Hx) as [c [d [Hin Hcd]]]. simpl in Hin.
  pose proof (runs_sound _ _ Z.eqb Heq _ _ _ _ Hr Hin) as Hp.
  destruct (prep_lines_in _ _ _ _ _ _ Hp) as [p [Hp' [Ek [E1 E2]]]].
  exists p. split; [exact Hp' |]. split; [exact Ek |].
  rewrite E1, E2. exact Hcd.
Qed.

(* ---------------------------------------------------------------- *)
(* The cells of a certificate                                        *)

(** The extent of a cell in a slot: the slot's mantissa and exponent at the
    cell's point, and the half-width the cell carries for it. *)
Definition cell_ext (slot : nat) (w : Z) (cl : ccell) : ext :=
  Ext (nth slot (pt_ms (cc_pt cl)) 0) (nth slot (pt_es (cc_pt cl)) 0) w.

Definition cell_exts (xu xv : nat) (cl : ccell) : ext * ext :=
  (cell_ext xu (cc_du cl) cl, cell_ext xv (cc_dv cl) cl).

(** An end at the common exponent f, read in the mantissa units of the extent. *)
Lemma at_scale :
  forall (f : Z) (x : ext) (X : R), f <= x_e x ->
  (IZR (lo_at f x) <= X <= IZR (hi_at f x))%R ->
  (IZR (x_m x - x_d x) <= X / IZR (2 ^ (x_e x - f)) <= IZR (x_m x + x_d x))%R.
Proof.
  intros f x X Hf HX.
  assert (Hp : (0 < IZR (2 ^ (x_e x - f)))%R) by (apply IZR_lt; apply Z.pow_pos_nonneg; lia).
  unfold lo_at, hi_at, mid_at, half_at in HX. rewrite !minus_IZR, !plus_IZR, !mult_IZR in HX.
  rewrite minus_IZR, plus_IZR. split.
  - apply (Rmult_le_reg_r (IZR (2 ^ (x_e x - f)))); [exact Hp |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
  - apply (Rmult_le_reg_r (IZR (2 ^ (x_e x - f)))); [exact Hp |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

(** Every point of the rectangle the cells span lies in one of them: with
    x and y read at the finest exponents fu and fv, the cell's own mantissa
    coordinates of the point satisfy [Cell.in_cell]. *)
Theorem cells_cover_rect :
  forall xu xv (cells : list ccell),
  let cs := map (cell_exts xu xv) cells in
  cover2 cs = true ->
  forall x y : R,
  (IZR (ulo_of cs) <= x <= IZR (uhi_of cs))%R -> (IZR (vlo_of cs) <= y <= IZR (vhi_of cs))%R ->
  exists cl, In cl cells /\
    in_cell xu xv (pt_ms (cc_pt cl)) (cc_du cl) (cc_dv cl)
      (x / IZR (2 ^ (nth xu (pt_es (cc_pt cl)) 0 - fu_of cs)))
      (y / IZR (2 ^ (nth xv (pt_es (cc_pt cl)) 0 - fv_of cs))).
Proof.
  intros xu xv cells cs Hc x y Hx Hy.
  destruct (cover2_correct cs Hc x y Hx Hy) as [p [Hin [Hpx Hpy]]].
  unfold cs in Hin. apply in_map_iff in Hin. destruct Hin as [cl [Hp Hcl]].
  assert (Hin : In p cs) by (unfold cs; rewrite <- Hp; apply in_map; exact Hcl).
  pose proof (fu_of_le cs p Hin) as Hfu. pose proof (fv_of_le cs p Hin) as Hfv.
  exists cl. split; [exact Hcl |]. subst p. unfold in_cell. split.
  - exact (at_scale _ (cell_ext xu (cc_du cl) cl) x Hfu Hpx).
  - exact (at_scale _ (cell_ext xv (cc_dv cl) cl) y Hfv Hpy).
Qed.

(** With no width in the second slot, every line the cells lie on is covered
    in the first: a point of the range on the line of any cell lies in a cell
    on that line. *)
Theorem cells_cover_lines :
  forall xu xv (cells : list ccell),
  let cs := map (cell_exts xu xv) cells in
  cover_lines cs = true ->
  forall cl0, In cl0 cells -> forall x : R, (IZR (ulo_of cs) <= x <= IZR (uhi_of cs))%R ->
  exists cl, In cl cells /\
    mid_at (fv_of cs) (cell_ext xv (cc_dv cl) cl) = mid_at (fv_of cs) (cell_ext xv (cc_dv cl0) cl0) /\
    (IZR (nth xu (pt_ms (cc_pt cl)) 0%Z - cc_du cl)
       <= x / IZR (2 ^ (nth xu (pt_es (cc_pt cl)) 0%Z - fu_of cs))
       <= IZR (nth xu (pt_ms (cc_pt cl)) 0%Z + cc_du cl))%R.
Proof.
  intros xu xv cells cs Hc cl0 Hcl0 x Hx.
  assert (Hin0 : In (cell_exts xu xv cl0) cs) by (unfold cs; apply in_map; exact Hcl0).
  destruct (cover_lines_correct cs Hc _ Hin0 x Hx) as [p [Hin [Hline Hpx]]].
  unfold cs in Hin. apply in_map_iff in Hin. destruct Hin as [cl [Hp Hcl]].
  assert (Hinp : In p cs) by (unfold cs; rewrite <- Hp; apply in_map; exact Hcl).
  pose proof (fu_of_le cs p Hinp) as Hfu.
  exists cl. split; [exact Hcl |]. subst p. split; [exact Hline |].
  exact (at_scale _ (cell_ext xu (cc_du cl) cl) x Hfu Hpx).
Qed.

(** The same with the slots exchanged: with no width in the first slot, every
    line the cells lie on is covered in the second. *)
Definition cell_exts_vu (xu xv : nat) (cl : ccell) : ext * ext :=
  (cell_ext xv (cc_dv cl) cl, cell_ext xu (cc_du cl) cl).

Theorem cells_cover_lines_vu :
  forall xu xv (cells : list ccell),
  let cs := map (cell_exts_vu xu xv) cells in
  cover_lines cs = true ->
  forall cl0, In cl0 cells -> forall y : R, (IZR (ulo_of cs) <= y <= IZR (uhi_of cs))%R ->
  exists cl, In cl cells /\
    mid_at (fv_of cs) (cell_ext xu (cc_du cl) cl) = mid_at (fv_of cs) (cell_ext xu (cc_du cl0) cl0) /\
    (IZR (nth xv (pt_ms (cc_pt cl)) 0%Z - cc_dv cl)
       <= y / IZR (2 ^ (nth xv (pt_es (cc_pt cl)) 0%Z - fu_of cs))
       <= IZR (nth xv (pt_ms (cc_pt cl)) 0%Z + cc_dv cl))%R.
Proof.
  intros xu xv cells cs Hc cl0 Hcl0 y Hy.
  assert (Hin0 : In (cell_exts_vu xu xv cl0) cs) by (unfold cs; apply in_map; exact Hcl0).
  destruct (cover_lines_correct cs Hc _ Hin0 y Hy) as [p [Hin [Hline Hpy]]].
  unfold cs in Hin. apply in_map_iff in Hin. destruct Hin as [cl [Hp Hcl]].
  assert (Hinp : In p cs) by (unfold cs; rewrite <- Hp; apply in_map; exact Hcl).
  pose proof (fu_of_le cs p Hinp) as Hfu.
  exists cl. split; [exact Hcl |]. subst p. split; [exact Hline |].
  exact (at_scale _ (cell_ext xv (cc_dv cl) cl) y Hfu Hpy).
Qed.
