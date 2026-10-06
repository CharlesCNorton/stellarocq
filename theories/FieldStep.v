(** A priori enclosures of the solutions of a planar equation over a step.

    The field-line equations with the toroidal angle as time are
    R' = FR (R, phi, Z), Z' = FZ (R, phi, Z). Let a solution start at phi = a
    in the box [xl, xh] x [zl, zh], let FR and FZ lie in [fl, fh] and
    [gl, gh] over a box [bl, bh] x [cl, ch] and the angles [a, a + h], and
    let the box grown by h times those bounds lie inside that box strictly.
    Then the solution stays inside it over the whole step and at every angle
    of the step lies in the box grown by the angle travelled
    ([step_enclosure]): were it to leave, it would do so at a first angle,
    where the mean value theorem, applied up to that angle, puts it strictly
    inside. No existence or uniqueness of solutions is used, so the
    enclosure holds for every solution through the initial box, and a chain
    of steps encloses every solution over an interval of angles
    ([chain_enclosure]). *)

From Coq Require Import Reals Lra List Classical.
From Coquelicot Require Import Coquelicot.
Import ListNotations.
Local Open Scope R_scope.

(** A continuous function inside an open interval stays inside near the point. *)
Lemma cont_nbhd (f : R -> R) (x lo hi : R) :
  continuity_pt f x -> lo < f x < hi -> exists d, 0 < d /\ forall y, Rabs (y - x) < d -> lo < f y < hi.
Proof.
  intros Hc Hf.
  assert (He : Rmin (f x - lo) (hi - f x) > 0) by (apply Rmin_pos; lra).
  destruct (Hc _ He) as [d [Hd Hy]].
  exists d. split; [lra |]. intros y Hyx.
  destruct (Req_dec y x) as [E | E]; [subst; exact Hf |].
  assert (Hyd : D_x no_cond x y /\ R_dist y x < d).
  { split; [split; [exact I | intros E'; apply E; symmetry; exact E'] | exact Hyx]. }
  specialize (Hy y Hyd). simpl in Hy. unfold R_dist in Hy.
  pose proof (Rmin_l (f x - lo) (hi - f x)). pose proof (Rmin_r (f x - lo) (hi - f x)).
  apply Rabs_def2 in Hy. lra.
Qed.

Lemma derive_cont (f : R -> R) (x l : R) : is_derive f x l -> continuity_pt f x.
Proof.
  intros H. apply derivable_continuous_pt. exists l. apply is_derive_Reals, H.
Qed.

(** The increment over [a, u] of a function whose derivative lies in [m, M]
    on the open interval. *)
Lemma incr_bounds (f : R -> R) (df : R -> R) (a u m M : R) :
  a < u -> (forall c, a <= c <= u -> is_derive f c (df c)) ->
  (forall c, a < c < u -> m <= df c <= M) ->
  f a + (u - a) * m <= f u <= f a + (u - a) * M.
Proof.
  intros Hau Hd Hb.
  destruct (MVT_cor2 f df a u Hau) as [c [Hc Hac]].
  { intros c Hc. apply is_derive_Reals, Hd, Hc. }
  specialize (Hb c Hac). nra.
Qed.

Section Step.

Variables (FR FZ : R -> R -> R -> R) (r z : R -> R) (a h : R).
Variables (xl xh zl zh bl bh cl ch fl fh gl gh : R).
Hypothesis Hsol : forall s, a <= s <= a + h ->
  is_derive r s (FR (r s) s (z s)) /\ is_derive z s (FZ (r s) s (z s)).
Hypothesis HX : (xl <= r a <= xh) /\ (zl <= z a <= zh).
Hypothesis HF : forall R0 s Z0, bl <= R0 <= bh -> a <= s <= a + h -> cl <= Z0 <= ch ->
  (fl <= FR R0 s Z0 <= fh) /\ (gl <= FZ R0 s Z0 <= gh).
Hypothesis HB : bl < xl + h * Rmin 0 fl /\ xh + h * Rmax 0 fh < bh /\
                cl < zl + h * Rmin 0 gl /\ zh + h * Rmax 0 gh < ch.

Definition inB (s : R) : Prop := (bl < r s < bh) /\ (cl < z s < ch).

Definition grown (u : R) : Prop :=
  (xl + (u - a) * fl <= r u <= xh + (u - a) * fh) /\ (zl + (u - a) * gl <= z u <= zh + (u - a) * gh).

(** Inside the box up to u, the solution at u lies in the grown box. *)
Lemma grown_of_inside (u : R) : a <= u <= a + h -> (forall v, a <= v < u -> inB v) -> grown u.
Proof.
  intros Hu Hin. destruct (Req_dec u a) as [E | E].
  - subst u. unfold grown. replace (a - a) with 0 by ring. destruct HX. lra.
  - assert (Hau : a < u) by lra.
    assert (Hd : forall c, a <= c <= u -> is_derive r c (FR (r c) c (z c)) /\ is_derive z c (FZ (r c) c (z c)))
      by (intros c Hc; apply Hsol; lra).
    assert (Hb : forall c, a < c < u -> (fl <= FR (r c) c (z c) <= fh) /\ (gl <= FZ (r c) c (z c) <= gh)).
    { intros c Hc. destruct (Hin c ltac:(lra)) as [H1 H2]. apply HF; lra. }
    pose proof (incr_bounds r (fun c => FR (r c) c (z c)) a u fl fh Hau
                  (fun c Hc => proj1 (Hd c Hc)) (fun c Hc => proj1 (Hb c Hc))) as I1.
    pose proof (incr_bounds z (fun c => FZ (r c) c (z c)) a u gl gh Hau
                  (fun c Hc => proj2 (Hd c Hc)) (fun c Hc => proj2 (Hb c Hc))) as I2.
    destruct HX as [X1 X2]. unfold grown.
    assert (0 < u - a) by lra.
    split; split; nra.
Qed.

(** The grown box lies strictly inside the box. *)
Lemma inside_of_grown (u : R) : a <= u <= a + h -> grown u -> inB u.
Proof.
  intros Hu [[G1 G2] [G3 G4]]. destruct HB as [B1 [B2 [B3 B4]]].
  assert (Hm : forall f, h * Rmin 0 f <= (u - a) * f).
  { intros f. destruct (Rle_dec 0 f) as [Hf | Hf].
    - rewrite Rmin_left by lra. nra.
    - rewrite Rmin_right by lra. nra. }
  assert (HM : forall f, (u - a) * f <= h * Rmax 0 f).
  { intros f. destruct (Rle_dec 0 f) as [Hf | Hf].
    - rewrite Rmax_right by lra. nra.
    - rewrite Rmax_left by lra. nra. }
  pose proof (Hm fl). pose proof (HM fh). pose proof (Hm gl). pose proof (HM gh).
  unfold inB. lra.
Qed.

Theorem step_inside (s : R) : a <= s <= a + h -> inB s.
Proof.
  intros Hs.
  destruct (classic (inB s)) as [H | H]; [exact H |]. exfalso.
  set (E := fun y => a <= - y <= s /\ ~ inB (- y)).
  assert (Hbound : bound E) by (exists (- a); intros y [Hy _]; lra).
  assert (Hne : exists y, E y).
  { exists (- s). unfold E. rewrite Ropp_involutive. split; [lra | exact H]. }
  destruct (completeness E Hbound Hne) as [m [Hub Hleast]].
  set (t := - m).
  assert (Hlow : forall u, a <= u <= s -> ~ inB u -> t <= u).
  { intros u Hu Hn. assert (Eu : E (- u)) by (unfold E; rewrite Ropp_involutive; auto).
    specialize (Hub _ Eu). unfold t. lra. }
  assert (Hta : a <= t).
  { assert (m <= - a) by (apply Hleast; intros y [Hy _]; lra). unfold t. lra. }
  assert (Hts : t <= s).
  { assert (Es : E (- s)) by (unfold E; rewrite Ropp_involutive; split; [lra | exact H]).
    specialize (Hub _ Es). unfold t. lra. }
  assert (Hbefore : forall v, a <= v < t -> inB v).
  { intros v Hv. destruct (classic (inB v)) as [Hi | Hn]; [exact Hi |].
    exfalso. specialize (Hlow v ltac:(lra) Hn). lra. }
  pose proof (inside_of_grown t ltac:(lra) (grown_of_inside t ltac:(lra) Hbefore)) as [Hr Hz].
  destruct (Hsol t ltac:(lra)) as [Dr Dz].
  destruct (cont_nbhd r t bl bh (derive_cont _ _ _ Dr) Hr) as [d1 [Hd1 N1]].
  destruct (cont_nbhd z t cl ch (derive_cont _ _ _ Dz) Hz) as [d2 [Hd2 N2]].
  assert (Hd : 0 < Rmin d1 d2) by (apply Rmin_pos; lra).
  assert (Hnear : forall u, Rabs (u - t) < Rmin d1 d2 -> inB u).
  { intros u Hu. pose proof (Rmin_l d1 d2). pose proof (Rmin_r d1 d2).
    split; [apply N1 | apply N2]; lra. }
  assert (Hup : is_upper_bound E (- (t + Rmin d1 d2))).
  { intros y [Hy Hn]. specialize (Hlow (- y) Hy Hn).
    destruct (Rlt_dec (- y) (t + Rmin d1 d2)) as [Hlt | Hge].
    - exfalso. apply Hn, Hnear. apply Rabs_def1; lra.
    - apply Rnot_lt_le in Hge. lra. }
  specialize (Hleast _ Hup). unfold t in *. lra.
Qed.

Theorem step_enclosure (s : R) : a <= s <= a + h -> grown s.
Proof.
  intros Hs. apply grown_of_inside; [exact Hs |].
  intros v Hv. apply step_inside. lra.
Qed.

End Step.

(** * Chains of steps *)

(** One step of a chain: its length and the a priori box with the bounds of
    the two components over it. *)
Record step := mkstep { st_h : R ; st_bl : R ; st_bh : R ; st_cl : R ; st_ch : R ;
                        st_fl : R ; st_fh : R ; st_gl : R ; st_gh : R }.

(** The box at the end of a step from the box (xl, xh, zl, zh). *)
Definition next_box (st : step) (X : R * R * R * R) : R * R * R * R :=
  let '(xl, xh, zl, zh) := X in
  (xl + st_h st * st_fl st, xh + st_h st * st_fh st, zl + st_h st * st_gl st, zh + st_h st * st_gh st).

Definition inbox (X : R * R * R * R) (R0 Z0 : R) : Prop :=
  let '(xl, xh, zl, zh) := X in (xl <= R0 <= xh) /\ (zl <= Z0 <= zh).

(** What a step asks of the components and of its boxes. *)
Definition step_ok (FR FZ : R -> R -> R -> R) (a : R) (X : R * R * R * R) (st : step) : Prop :=
  let '(xl, xh, zl, zh) := X in
  0 <= st_h st /\
  (forall R0 s Z0, st_bl st <= R0 <= st_bh st -> a <= s <= a + st_h st -> st_cl st <= Z0 <= st_ch st ->
     (st_fl st <= FR R0 s Z0 <= st_fh st) /\ (st_gl st <= FZ R0 s Z0 <= st_gh st)) /\
  st_bl st < xl + st_h st * Rmin 0 (st_fl st) /\ xh + st_h st * Rmax 0 (st_fh st) < st_bh st /\
  st_cl st < zl + st_h st * Rmin 0 (st_gl st) /\ zh + st_h st * Rmax 0 (st_gh st) < st_ch st.

Fixpoint chain_ok (FR FZ : R -> R -> R -> R) (a : R) (X : R * R * R * R) (sts : list step) : Prop :=
  match sts with
  | [] => True
  | st :: rest => step_ok FR FZ a X st /\ chain_ok FR FZ (a + st_h st) (next_box st X) rest
  end.

Fixpoint chain_end (a : R) (X : R * R * R * R) (sts : list step) : R * (R * R * R * R) :=
  match sts with
  | [] => (a, X)
  | st :: rest => chain_end (a + st_h st) (next_box st X) rest
  end.

Fixpoint chain_len (sts : list step) : R :=
  match sts with
  | [] => 0
  | st :: rest => st_h st + chain_len rest
  end.

Lemma chain_len_nonneg (FR FZ : R -> R -> R -> R) (a : R) (X : R * R * R * R) (sts : list step) :
  chain_ok FR FZ a X sts -> 0 <= chain_len sts.
Proof.
  revert a X. induction sts as [| st rest IH]; intros a X H; simpl; [lra |].
  destruct H as [H1 H2]. destruct X as [[[xl xh] zl] zh]. destruct H1 as [Hh _].
  pose proof (IH _ _ H2). lra.
Qed.

Theorem chain_enclosure (FR FZ : R -> R -> R -> R) (r z : R -> R) (sts : list step) :
  forall (a : R) (X : R * R * R * R),
  chain_ok FR FZ a X sts ->
  (forall s, a <= s <= a + chain_len sts ->
     is_derive r s (FR (r s) s (z s)) /\ is_derive z s (FZ (r s) s (z s))) ->
  inbox X (r a) (z a) ->
  let '(e, Y) := chain_end a X sts in inbox Y (r e) (z e).
Proof.
  induction sts as [| st rest IH]; intros a X Hc Hs HX; simpl; [exact HX |].
  destruct Hc as [Hst Hrest].
  pose proof (chain_len_nonneg _ _ _ _ _ Hrest) as Hlen.
  destruct X as [[[xl xh] zl] zh].
  destruct Hst as [Hh [HF [B1 [B2 [B3 B4]]]]].
  apply IH; [exact Hrest | |].
  - intros s Hs'. apply Hs. simpl. lra.
  - pose proof (step_enclosure FR FZ r z a (st_h st) xl xh zl zh (st_bl st) (st_bh st) (st_cl st) (st_ch st)
                  (st_fl st) (st_fh st) (st_gl st) (st_gh st)
                  (fun s Hs' => Hs s ltac:(simpl; lra)) HX HF (conj B1 (conj B2 (conj B3 B4)))
                  (a + st_h st) ltac:(lra)) as G.
    unfold grown in G. replace (a + st_h st - a) with (st_h st) in G by ring.
    unfold next_box, inbox. exact G.
Qed.
