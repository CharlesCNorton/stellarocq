(** Existence of a zero of an expression system, from an interval Newton test.

    A system is a list of bindings over input slots, the first n of which are
    unknowns, with n output slots. A certificate names a centre c, a radius r
    in mantissa units, an approximate inverse A of the Jacobian at the centre,
    an approximate inverse B of A, and a contraction constant K below one.
    [check_newton] evaluates the outputs at the centre, encloses every
    Jacobian entry over the box |x - c| <= r by the doubled bindings of
    Deriv.v along each unknown, and tests three row-sum bounds in interval
    arithmetic: the rows of I - A J over the box and of I - B A sum below K
    in absolute value, and |A F(c)| + K r <= r.

    [newton_correct] states what a passing test proves: the map x - A F(x)
    contracts the box into itself, so by [Kantorovich.contraction_fixed_point]
    it has a fixed point there, the bound on I - B A makes that fixed point a
    zero of F, and the contraction makes it the only zero in the box. The Jacobian enters
    through the mean value theorem one coordinate at a time, which is why the
    per-entry enclosures suffice: the increment of an output between two
    points of the box is a sum of products of enclosed derivatives and
    coordinate differences. *)

From Coq Require Import ZArith Reals List Bool Lia Lra Eqdep_dec.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Kantorovich.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Finite sums                                                       *)

Fixpoint sumn (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => sumn f k + f k end.

Lemma sumn_ext :
  forall f g n, (forall k, (k < n)%nat -> f k = g k) -> sumn f n = sumn g n.
Proof.
  intros f g n H. induction n as [|n IH]; simpl. reflexivity.
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumn_zero : forall n, sumn (fun _ => 0) n = 0.
Proof. induction n; simpl; lra. Qed.

Lemma sumn_plus :
  forall f g n, sumn (fun k => f k + g k) n = sumn f n + sumn g n.
Proof. intros f g n. induction n; simpl; lra. Qed.

Lemma sumn_minus :
  forall f g n, sumn (fun k => f k - g k) n = sumn f n - sumn g n.
Proof. intros f g n. induction n; simpl; lra. Qed.

Lemma sumn_scal : forall c f n, sumn (fun k => c * f k) n = c * sumn f n.
Proof. intros c f n. induction n; simpl; lra. Qed.

Lemma sumn_swap :
  forall (f : nat -> nat -> R) n m,
  sumn (fun i => sumn (fun j => f i j) m) n
  = sumn (fun j => sumn (fun i => f i j) n) m.
Proof.
  intros f n m. induction n as [|n IH]; simpl.
  - rewrite sumn_zero. reflexivity.
  - rewrite IH. rewrite <- sumn_plus. reflexivity.
Qed.

Lemma sumn_abs :
  forall f n, Rabs (sumn f n) <= sumn (fun k => Rabs (f k)) n.
Proof.
  intros f n. induction n as [|n IH]; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans. apply Rabs_triang. lra.
Qed.

Lemma sumn_le :
  forall f g n, (forall k, (k < n)%nat -> f k <= g k) -> sumn f n <= sumn g n.
Proof.
  intros f g n H. induction n as [|n IH]; simpl. lra.
  assert (sumn f n <= sumn g n) by (apply IH; intros; apply H; lia).
  assert (f n <= g n) by (apply H; lia). lra.
Qed.

Lemma sumn_nonneg :
  forall f n, (forall k, (k < n)%nat -> 0 <= f k) -> 0 <= sumn f n.
Proof.
  intros f n H. rewrite <- (sumn_zero n). apply sumn_le. intros. now apply H.
Qed.

Lemma fold_Rplus_shift :
  forall (l : list R) a0, fold_right Rplus a0 l = fold_right Rplus 0 l + a0.
Proof. induction l; intros a0; simpl. lra. rewrite IHl. lra. Qed.

Lemma sumn_fold :
  forall (f : nat -> R) n, fold_right Rplus 0 (map f (seq 0 n)) = sumn f n.
Proof.
  intros f n. induction n as [|n IH]. reflexivity.
  rewrite seq_S, map_app, fold_right_app. cbn [map fold_right Nat.add].
  rewrite fold_Rplus_shift, IH. simpl. lra.
Qed.

(** A sum of products against a vector, bounded by the sum of absolute
    values times the largest coordinate. *)
Lemma sumn_prod_bound :
  forall (g v : nat -> R) n M,
  (forall j, (j < n)%nat -> Rabs (v j) <= M) ->
  Rabs (sumn (fun j => g j * v j) n) <= sumn (fun j => Rabs (g j)) n * M.
Proof.
  intros g v n M Hv.
  eapply Rle_trans. apply sumn_abs.
  rewrite Rmult_comm. rewrite <- sumn_scal.
  apply sumn_le. intros j Hj. rewrite Rabs_mult, (Rmult_comm M).
  apply Rmult_le_compat_l. apply Rabs_pos. now apply Hv.
Qed.

Lemma nth_map_in :
  forall (A B : Type) (f : A -> B) (l : list A) k (d : A) (d' : B),
  (k < length l)%nat -> nth k (map f l) d' = f (nth k l d).
Proof.
  intros A B f l k d d' Hk.
  rewrite (nth_indep _ d' (f d)) by (rewrite length_map; lia).
  apply map_nth.
Qed.

Lemma nth_map_seq :
  forall (f : nat -> R) n i, (i < n)%nat -> nth i (map f (seq 0 n)) 0 = f i.
Proof.
  intros f n i Hi.
  rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* Vectors in the max norm                                           *)

Definition vsub (a b : list R) : list R :=
  map (fun p => fst p - snd p) (combine a b).

Lemma length_vsub :
  forall a b, length a = length b -> length (vsub a b) = length a.
Proof.
  intros a b H. unfold vsub. rewrite length_map, length_combine. lia.
Qed.

Lemma nth_vsub :
  forall a b k, length a = length b -> (k < length a)%nat ->
  nth k (vsub a b) 0 = nth k a 0 - nth k b 0.
Proof.
  intros a b k Hl Hk. unfold vsub.
  rewrite (nth_map_in _ _ _ _ _ (0, 0)) by (rewrite length_combine; lia).
  rewrite combine_nth by exact Hl. reflexivity.
Qed.

Fixpoint vmax (l : list R) : R :=
  match l with [] => 0 | x :: t => Rmax (Rabs x) (vmax t) end.

Lemma vmax_nonneg : forall l, 0 <= vmax l.
Proof.
  induction l as [|x t IH]; simpl. lra.
  eapply Rle_trans. apply IH. apply Rmax_r.
Qed.

Lemma vmax_nth : forall l k, Rabs (nth k l 0) <= vmax l.
Proof.
  induction l as [|x t IH]; intros k; simpl.
  - destruct k; rewrite Rabs_R0; lra.
  - destruct k. apply Rmax_l. eapply Rle_trans. apply IH. apply Rmax_r.
Qed.

Lemma vmax_le :
  forall l K, 0 <= K ->
  (forall k, (k < length l)%nat -> Rabs (nth k l 0) <= K) -> vmax l <= K.
Proof.
  induction l as [|x t IH]; intros K HK H; simpl. exact HK.
  apply Rmax_lub. apply (H 0%nat). simpl. lia.
  apply IH. exact HK. intros k Hk. apply (H (S k)). simpl. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The complete metric space of vectors of one length                *)

Section Metric.

Variable n : nat.

Definition vec := { l : list R | length l = n }.

Definition vd (x y : vec) : R := vmax (vsub (proj1_sig x) (proj1_sig y)).

Lemma vec_eq :
  forall (a b : list R) (Ha : length a = n) (Hb : length b = n),
  a = b -> exist (fun l : list R => length l = n) a Ha = exist _ b Hb.
Proof.
  intros a b Ha Hb E. subst b. f_equal. apply UIP_dec. apply Nat.eq_dec.
Qed.

Lemma vd_nonneg : forall x y, 0 <= vd x y.
Proof. intros x y. apply vmax_nonneg. Qed.

Lemma vd_refl : forall x, vd x x = 0.
Proof.
  intros [a Ha]. unfold vd. simpl.
  apply Rle_antisym.
  - apply vmax_le. lra. intros k Hk.
    rewrite length_vsub in Hk by reflexivity.
    rewrite nth_vsub by (auto; lia). rewrite Rminus_diag_eq by reflexivity.
    rewrite Rabs_R0. lra.
  - apply vmax_nonneg.
Qed.

Lemma vd_eq : forall x y, vd x y = 0 -> x = y.
Proof.
  intros [a Ha] [b Hb] H. unfold vd in H. simpl in H.
  apply vec_eq.
  apply (nth_ext _ _ 0 0). lia.
  intros k Hk.
  assert (Hab := vmax_nth (vsub a b) k). rewrite H in Hab.
  rewrite nth_vsub in Hab by lia.
  generalize (Rabs_pos (nth k a 0 - nth k b 0)). intros.
  assert (Hz : Rabs (nth k a 0 - nth k b 0) = 0) by lra.
  destruct (Req_dec (nth k a 0 - nth k b 0) 0) as [Hd|Hd]. lra.
  exfalso. generalize (Rabs_pos_lt _ Hd). lra.
Qed.

Lemma vd_sym : forall x y, vd x y = vd y x.
Proof.
  intros [a Ha] [b Hb]. unfold vd. simpl.
  assert (Hle : forall u v : list R, length u = n -> length v = n ->
            vmax (vsub u v) <= vmax (vsub v u)).
  { intros u v Hu Hv. apply vmax_le. apply vmax_nonneg.
    intros k Hk. rewrite length_vsub in Hk by lia.
    rewrite nth_vsub by lia.
    rewrite Rabs_minus_sym.
    rewrite <- (nth_vsub v u k) by lia. apply vmax_nth. }
  apply Rle_antisym; apply Hle; assumption.
Qed.

Lemma vd_tri : forall x y z, vd x z <= vd x y + vd y z.
Proof.
  intros [a Ha] [b Hb] [c Hc]. unfold vd. simpl.
  apply vmax_le.
  { generalize (vmax_nonneg (vsub a b)) (vmax_nonneg (vsub b c)). lra. }
  intros k Hk. rewrite length_vsub in Hk by lia.
  rewrite nth_vsub by lia.
  replace (nth k a 0 - nth k c 0)
    with ((nth k a 0 - nth k b 0) + (nth k b 0 - nth k c 0)) by ring.
  eapply Rle_trans. apply Rabs_triang.
  apply Rplus_le_compat.
  - rewrite <- (nth_vsub a b k) by lia. apply vmax_nth.
  - rewrite <- (nth_vsub b c k) by lia. apply vmax_nth.
Qed.

(** The limit of a Cauchy sequence in a closed ball stays in it. *)
Lemma vec_complete :
  forall (x0 : vec) (r : R) (u : nat -> vec),
  (forall k, vd x0 (u k) <= r) ->
  (forall eps, 0 < eps ->
     exists N, forall m k, (N <= m)%nat -> (N <= k)%nat -> vd (u m) (u k) < eps) ->
  exists x, vd x0 x <= r /\
    forall eps, 0 < eps -> exists N, forall k, (N <= k)%nat -> vd x (u k) < eps.
Proof.
  intros x0 r u Hball Hcauchy.
  set (c := fun i k => nth i (proj1_sig (u k)) 0).
  (* each coordinate is a Cauchy sequence of reals *)
  assert (Hcau : forall i, (i < n)%nat -> Cauchy_crit (c i)).
  { intros i Hi eps Heps.
    destruct (Hcauchy eps Heps) as [N HN].
    exists N. intros m k Hm Hk.
    unfold Rdist, c.
    destruct (u m) as [um Hum] eqn:Em. destruct (u k) as [uk Huk] eqn:Ek.
    simpl.
    apply Rle_lt_trans with (vd (u m) (u k)).
    - rewrite Em, Ek. unfold vd. simpl.
      rewrite <- (nth_vsub um uk i) by lia. apply vmax_nth.
    - now apply HN. }
  set (lim := fun i => match lt_dec i n with
                       | left H => proj1_sig (R_complete (c i) (Hcau i H))
                       | right _ => 0 end).
  assert (Hlim : forall i, (i < n)%nat -> Un_cv (c i) (lim i)).
  { intros i Hi. unfold lim. destruct (lt_dec i n) as [H|H]. 2: lia.
    exact (proj2_sig (R_complete (c i) (Hcau i H))). }
  assert (HL : length (map lim (seq 0 n)) = n)
    by (rewrite length_map, length_seq; reflexivity).
  exists (exist _ (map lim (seq 0 n)) HL).
  destruct x0 as [a Ha].
  split.
  - (* the limit stays within r of the centre *)
    unfold vd. simpl.
    apply vmax_le.
    { generalize (Hball 0%nat). unfold vd. simpl.
      generalize (vmax_nonneg (vsub a (proj1_sig (u 0%nat)))). lra. }
    intros i Hi. rewrite length_vsub in Hi by lia.
    rewrite nth_vsub by lia. rewrite nth_map_seq by lia.
    destruct (Rle_lt_dec (Rabs (nth i a 0 - lim i)) r) as [Hok|Hbad]. exact Hok.
    exfalso.
    set (eps := Rabs (nth i a 0 - lim i) - r).
    destruct (Hlim i ltac:(lia) eps ltac:(unfold eps; lra)) as [N HN].
    specialize (HN N (Nat.le_refl N)). unfold Rdist, c in HN.
    assert (Hk := Hball N). unfold vd in Hk.
    destruct (u N) as [uN HuN]. simpl in Hk, HN.
    assert (Hi' : Rabs (nth i a 0 - nth i uN 0) <= r).
    { rewrite <- (nth_vsub a uN i) by lia.
      eapply Rle_trans. apply vmax_nth. exact Hk. }
    assert (Rabs (nth i a 0 - lim i)
            <= Rabs (nth i a 0 - nth i uN 0) + Rabs (nth i uN 0 - lim i)).
    { replace (nth i a 0 - lim i)
        with ((nth i a 0 - nth i uN 0) + (nth i uN 0 - lim i)) by ring.
      apply Rabs_triang. }
    unfold eps in HN. lra.
  - (* and the sequence converges to it *)
    intros eps Heps.
    assert (Hall : forall m, (m <= n)%nat -> exists N, forall i, (i < m)%nat ->
              forall k, (N <= k)%nat -> Rabs (lim i - c i k) < eps / 2).
    { intros m. induction m as [|m IH]; intros Hm.
      - exists 0%nat. intros i Hi. lia.
      - destruct (IH ltac:(lia)) as [N1 H1].
        destruct (Hlim m ltac:(lia) (eps / 2) ltac:(lra)) as [N2 H2].
        exists (Nat.max N1 N2). intros i Hi k Hk.
        destruct (Nat.eq_dec i m) as [->|Hne].
        + specialize (H2 k ltac:(lia)). unfold Rdist in H2.
          rewrite Rabs_minus_sym. exact H2.
        + apply H1. lia. lia. }
    destruct (Hall n (Nat.le_refl n)) as [N HN].
    exists N. intros k Hk. destruct (u k) as [uk Huk] eqn:Ek.
    unfold vd. simpl.
    apply Rle_lt_trans with (eps / 2). 2: lra.
    apply vmax_le. lra.
    intros i Hi. rewrite length_vsub in Hi by lia. rewrite HL in Hi.
    rewrite nth_vsub by lia. rewrite nth_map_seq by lia.
    left. specialize (HN i Hi k Hk). unfold c in HN. rewrite Ek in HN.
    simpl in HN. exact HN.
Qed.

End Metric.

(* ---------------------------------------------------------------- *)
(* Environments of a point of the box                                *)

(** The real environment of a list of reals. *)
Definition xenv_R (l : list R) : env ExtendedR := of_list (map Xreal l).

Lemma eget_xenv_R :
  forall l k, (k < length l)%nat -> eget k (xenv_R l) Xnan = Xreal (nth k l 0).
Proof.
  intros l k Hk. unfold xenv_R. rewrite eget_of_list.
  now rewrite (nth_map_in _ _ _ _ _ 0) by lia.
Qed.

Lemma eget_xenv_R_over :
  forall l k, (length l <= k)%nat -> eget k (xenv_R l) Xnan = Xnan.
Proof.
  intros l k Hk. unfold xenv_R. rewrite eget_of_list.
  apply nth_overflow. rewrite length_map. lia.
Qed.

Lemma eget_ienv_of :
  forall prec (c : list Z) k, (k < length c)%nat ->
  eget k (ienv_of prec c) I.nai = I.fromZ prec (nth k c 0%Z).
Proof.
  intros prec c k Hk. unfold ienv_of. rewrite eget_of_list.
  now rewrite (nth_map_in _ _ _ _ _ 0%Z) by lia.
Qed.

Lemma eget_ienv_of_over :
  forall prec (c : list Z) k, (length c <= k)%nat ->
  eget k (ienv_of prec c) I.nai = I.nai.
Proof.
  intros prec c k Hk. unfold ienv_of. rewrite eget_of_list.
  apply nth_overflow. rewrite length_map. lia.
Qed.

(** What the environment of a point of the box looks like: the unknowns
    carry the point's coordinates, the parameters the centre's, and nothing
    above the inputs is set. *)
Definition point_spec (c : list Z) (n base : nat) (f : nat -> R)
    (e : env ExtendedR) : Prop :=
  (forall i, (i < n)%nat -> eget i e Xnan = Xreal (f i)) /\
  (forall i, (n <= i)%nat -> (i < base)%nat ->
     eget i e Xnan = Xreal (IZR (nth i c 0%Z))) /\
  (forall i, (base <= i)%nat -> eget i e Xnan = Xnan).

Definition in_boxf (c : list Z) (r : Z) (n : nat) (f : nat -> R) : Prop :=
  forall i, (i < n)%nat ->
  IZR (nth i c 0%Z - r) <= f i <= IZR (nth i c 0%Z + r).

(** The interval environment of the box. *)
Fixpoint boxn (prec : F.precision) (c : list Z) (r : Z) (k : nat)
    (e : env I.type) : env I.type :=
  match k with
  | O => e
  | S k' => boxn prec c r k' (eset k' e (slot_box prec (nth k' c 0%Z) r))
  end.

Lemma eget_boxn_out :
  forall prec c r k e i, (k <= i)%nat ->
  eget i (boxn prec c r k e) I.nai = eget i e I.nai.
Proof.
  intros prec c r k. induction k as [|k IH]; intros e i Hi; simpl.
  reflexivity.
  rewrite IH by lia. apply eget_eset_neq. lia.
Qed.

Lemma eget_boxn_in :
  forall prec c r k e i, (i < k)%nat ->
  eget i (boxn prec c r k e) I.nai = slot_box prec (nth i c 0%Z) r.
Proof.
  intros prec c r k. induction k as [|k IH]; intros e i Hi. lia.
  simpl. destruct (Nat.eq_dec i k) as [->|Hne].
  - rewrite eget_boxn_out by lia. apply eget_eset_eq.
  - apply IH. lia.
Qed.

Lemma box_env_ok :
  forall prec c r n f e,
  (n <= length c)%nat ->
  in_boxf c r n f ->
  point_spec c n (length c) f e ->
  env_ok (boxn prec c r n (ienv_of prec c)) e.
Proof.
  intros prec c r n f e Hn Hbox [Hu [Hp Hz]] i.
  destruct (lt_dec i n) as [Hi|Hi].
  - rewrite eget_boxn_in by exact Hi. rewrite Hu by exact Hi.
    apply slot_box_correct. now apply Hbox.
  - rewrite eget_boxn_out by lia.
    destruct (lt_dec i (length c)) as [Hc|Hc].
    + rewrite eget_ienv_of by exact Hc. rewrite Hp by lia.
      apply I.fromZ_correct.
    + rewrite eget_ienv_of_over by lia. rewrite Hz by lia.
      rewrite I.nai_correct. exact I.
Qed.

(** The environment of a list of unknowns beside the centre's parameters. *)
Definition E (c : list Z) (n : nat) (p : list R) : env ExtendedR :=
  xenv_R (p ++ map IZR (skipn n c)).

Lemma E_spec :
  forall c n p, length p = n -> (n <= length c)%nat ->
  point_spec c n (length c) (fun i => nth i p 0) (E c n p).
Proof.
  intros c n p Hp Hn.
  assert (Hlen : length (p ++ map IZR (skipn n c)) = length c).
  { rewrite length_app, length_map, length_skipn. lia. }
  unfold E. split; [|split].
  - intros i Hi. rewrite eget_xenv_R by lia. rewrite app_nth1 by lia. reflexivity.
  - intros i Hi Hc. rewrite eget_xenv_R by lia.
    rewrite app_nth2 by lia.
    rewrite (nth_map_in _ _ _ _ _ 0%Z) by (rewrite length_skipn; lia).
    rewrite nth_skipn.
    replace (n + (i - length p))%nat with i by lia. reflexivity.
  - intros i Hi. apply eget_xenv_R_over. lia.
Qed.

(** The centre's own environment is the one the checker builds from the
    mantissas. *)
Lemma E_centre :
  forall c n, (n <= length c)%nat ->
  E c n (map IZR (firstn n c)) = xenv_of c.
Proof.
  intros c n Hn. unfold E, xenv_R, xenv_of.
  rewrite <- map_app, firstn_skipn, map_map. reflexivity.
Qed.

(** Writing one unknown of a point environment gives the environment of the
    moved point. *)
Lemma point_spec_eset :
  forall c n base f e j t, (j < n)%nat -> (n <= base)%nat ->
  point_spec c n base f e ->
  point_spec c n base (fun i => if Nat.eqb i j then t else f i)
    (eset j e (Xreal t)).
Proof.
  intros c n base f e j t Hj Hnb [Hu [Hp Hz]]. split; [|split].
  - intros i Hi. destruct (Nat.eq_dec i j) as [->|Hne].
    + rewrite Nat.eqb_refl. apply eget_eset_eq.
    + rewrite (proj2 (Nat.eqb_neq i j) Hne). rewrite eget_eset_neq by exact Hne.
      now apply Hu.
  - intros i Hi Hb. rewrite eget_eset_neq by lia. now apply Hp.
  - intros i Hi. rewrite eget_eset_neq by lia. now apply Hz.
Qed.

(** Two environments of the same point agree everywhere. *)
Lemma point_spec_agree :
  forall c n base f e1 e2,
  point_spec c n base f e1 -> point_spec c n base f e2 ->
  forall k, eget k e1 Xnan = eget k e2 Xnan.
Proof.
  intros c n base f e1 e2 [A1 [B1 C1]] [A2 [B2 C2]] k.
  destruct (lt_dec k n). now rewrite A1, A2.
  destruct (lt_dec k base). now rewrite B1, B2 by lia.
  now rewrite C1, C2 by lia.
Qed.

(** So do the value slots after the bindings, doubled or not. *)
Lemma values_agree :
  forall x base len binds e1 e2,
  well_formed base binds = true -> len = length binds ->
  (forall k, eget k e1 Xnan = eget k e2 Xnan) ->
  forall k, (k < base + len)%nat ->
  eget k (xextend e1 (with_derivs x base len binds)) Xnan
  = eget k (xextend e2 binds) Xnan.
Proof.
  intros x base len binds e1 e2 Hwf Hlen Hag k Hk.
  apply (values_with_derivs x base len binds e1 e2 base Hwf); try lia.
  intros i _. apply Hag.
Qed.

(* ---------------------------------------------------------------- *)
(* The mean value theorem with an enclosed derivative                *)

(** Along a slot whose derivative slot is real and enclosed by D between a
    and b, the value slot is real at both ends and its increment is an
    enclosed derivative times the distance. *)
Lemma increment_along :
  forall (F : R -> env ExtendedR) n nd (D : I.type) a b,
  (forall t, Xderive_pt (slot_along F n) (Xreal t) (eget nd (F t) Xnan)) ->
  (forall t, Rmin a b <= t <= Rmax a b ->
     exists d, eget nd (F t) Xnan = Xreal d /\ contains (I.convert D) (Xreal d)) ->
  exists wa wb d,
    eget n (F a) Xnan = Xreal wa /\ eget n (F b) Xnan = Xreal wb /\
    contains (I.convert D) (Xreal d) /\ wb - wa = d * (b - a).
Proof.
  intros F n nd D a b Hder Hbnd.
  assert (Hreal : forall s, Rmin a b <= s <= Rmax a b ->
            exists w, eget n (F s) Xnan = Xreal w).
  { intros s Hs. destruct (Hbnd s Hs) as [d [Hd _]].
    specialize (Hder s). rewrite Hd in Hder.
    unfold Xderive_pt in Hder. unfold slot_along in Hder.
    destruct (eget n (F s) Xnan) as [|w]. contradiction. now exists w. }
  assert (Hab : Rmin a b <= a <= Rmax a b).
  { split. apply Rmin_l. apply Rmax_l. }
  assert (Hbb : Rmin a b <= b <= Rmax a b).
  { split. apply Rmin_r. apply Rmax_r. }
  destruct (Hreal a Hab) as [wa Hwa]. destruct (Hreal b Hbb) as [wb Hwb].
  set (phi := proj_fun 0 (slot_along F n)).
  set (phi' := fun s => proj_val (eget nd (F s) Xnan)).
  assert (Hphi : forall s w', eget n (F s) Xnan = Xreal w' -> phi s = w').
  { intros s w' Hw'. unfold phi, proj_fun, slot_along. now rewrite Hw'. }
  assert (Hdl : forall s, Rmin a b <= s <= Rmax a b ->
            derivable_pt_lim phi s (phi' s)).
  { intros s Hs. destruct (Hbnd s Hs) as [d [Hd _]].
    specialize (Hder s). rewrite Hd in Hder.
    unfold Xderive_pt in Hder. unfold slot_along in Hder at 1.
    destruct (eget n (F s) Xnan) eqn:Hns. contradiction.
    unfold phi', phi. rewrite Hd. simpl. apply Hder. }
  destruct (Rtotal_order a b) as [Hlt|[Heq|Hgt]].
  - rewrite Rmin_left in * by lra. rewrite Rmax_right in * by lra.
    destruct (MVT_cor2 phi phi' a b Hlt) as [z [Hz Hzin]].
    { intros s Hs. apply Hdl. lra. }
    destruct (Hbnd z ltac:(lra)) as [d [Hd Hdc]].
    exists wa, wb, d. split. exact Hwa. split. exact Hwb. split. exact Hdc.
    rewrite (Hphi a wa Hwa), (Hphi b wb Hwb) in Hz.
    unfold phi' in Hz. rewrite Hd in Hz. simpl in Hz. exact Hz.
  - subst b. destruct (Hbnd a Hab) as [d [Hd Hdc]].
    exists wa, wb, d. split. exact Hwa. split. exact Hwb. split. exact Hdc.
    rewrite Hwa in Hwb. injection Hwb as <-. ring.
  - rewrite Rmin_right in * by lra. rewrite Rmax_left in * by lra.
    destruct (MVT_cor2 phi phi' b a Hgt) as [z [Hz Hzin]].
    { intros s Hs. apply Hdl. lra. }
    destruct (Hbnd z ltac:(lra)) as [d [Hd Hdc]].
    exists wa, wb, d. split. exact Hwa. split. exact Hwb. split. exact Hdc.
    rewrite (Hphi a wa Hwa), (Hphi b wb Hwb) in Hz.
    unfold phi' in Hz. rewrite Hd in Hz. simpl in Hz. lra.
Qed.

(** The derivative slot of a scratch slot along an input slot. *)
Lemma deriv_slot :
  forall x base delta F next n,
  (x < base)%nat -> (base <= n)%nat ->
  inv x base delta F next ->
  forall t, Xderive_pt (slot_along F n) (Xreal t) (eget (n + delta) (F t) Xnan).
Proof.
  intros x base delta F next n Hx Hn [Ha _] t.
  specialize (Ha n t). unfold dvar_of in Ha.
  replace (Nat.eqb n x) with false in Ha by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.ltb n base) with false in Ha by (symmetry; apply Nat.ltb_ge; lia).
  exact Ha.
Qed.

(* ---------------------------------------------------------------- *)
(* The system and its check                                          *)

Record system := System {
  sy_prec : Z ;
  sy_n : nat ;
  sy_centre : list Z ;
  sy_r : Z ;
  sy_binds : list binding ;
  sy_out : list nat ;
  sy_A : list (list (Z * Z)) ;
  sy_B : list (list (Z * Z)) ;
  sy_KN : Z ; sy_Kq : Z ;
  sy_MN : Z ; sy_Mq : Z
}.

Definition sprec (s : system) : F.precision := F.PtoP (Z.to_pos (sy_prec s)).
Definition sbase (s : system) : nat := length (sy_centre s).
Definition slen (s : system) : nat := length (sy_binds s).

(** A dyadic entry m 2^e, enclosed and as a real. *)
Definition dyad (prec : F.precision) (me : Z * Z) : I.type :=
  ieval prec eempty (eps_e (fst me) (snd me)).
Definition dyadR (me : Z * Z) : R := IZR (fst me) * powerRZ 2 (snd me).

Lemma dyad_correct :
  forall prec me, contains (I.convert (dyad prec me)) (Xreal (dyadR me)).
Proof.
  intros prec me. unfold dyad, dyadR.
  assert (H := ieval_correct prec eempty eempty (eps_e (fst me) (snd me)) env_ok_nil).
  rewrite xeval_eps_e in H. exact H.
Qed.

Definition entry (M : list (list (Z * Z))) (i k : nat) : Z * Z :=
  nth k (nth i M []) (0%Z, 0%Z).

Definition oslot (s : system) (k : nat) : nat := nth k (sy_out s) 0%nat.
Definition Kiv (s : system) : I.type := dyad (sprec s) (sy_KN s, sy_Kq s).
Definition KR (s : system) : R := dyadR (sy_KN s, sy_Kq s).
Definition Riv (s : system) : I.type := I.fromZ (sprec s) (sy_r s).
Definition box (s : system) : env I.type :=
  boxn (sprec s) (sy_centre s) (sy_r s) (sy_n s) (ienv_of (sprec s) (sy_centre s)).
Definition colenv (s : system) (j : nat) : env I.type :=
  iextend (sprec s) (box s) (with_derivs j (sbase s) (slen s) (sy_binds s)).
Definition J (s : system) (k j : nat) : I.type :=
  ieval (sprec s) (colenv s j) (Evar (oslot s k + slen s)).
Definition Aiv (s : system) (i k : nat) : I.type := dyad (sprec s) (entry (sy_A s) i k).
Definition AR (s : system) (i k : nat) : R := dyadR (entry (sy_A s) i k).
Definition Biv (s : system) (i k : nat) : I.type := dyad (sprec s) (entry (sy_B s) i k).
Definition BR (s : system) (i k : nat) : R := dyadR (entry (sy_B s) i k).
Definition Miv (s : system) : I.type := dyad (sprec s) (sy_MN s, sy_Mq s).
Definition delta (i j : nat) : Z := if Nat.eqb i j then 1%Z else 0%Z.

(** The Jacobian, tabulated: one environment per unknown, read once for
    every output. [J] is what an entry means and [Jtab] is what the check
    computes; [Jtab_spec] says they agree. Written as a table so that the
    extracted code builds each column's environment once rather than once
    per entry it reads from it. *)
Definition colvals (s : system) (j : nat) : list I.type :=
  let env := colenv s j in
  map (fun k => ieval (sprec s) env (Evar (oslot s k + slen s))) (seq 0 (sy_n s)).
Definition Jtab (s : system) : list (list I.type) := map (colvals s) (seq 0 (sy_n s)).
Definition Jt (jt : list (list I.type)) (k j : nat) : I.type :=
  nth k (nth j jt []) I.nai.

Definition Giv (jt : list (list I.type)) (s : system) (i j : nat) : I.type :=
  I.sub (sprec s) (I.fromZ (sprec s) (delta i j))
    (isum (sprec s) (map (fun k => I.mul (sprec s) (Aiv s i k) (Jt jt k j))
                         (seq 0 (sy_n s)))).
Definition Hiv (s : system) (i j : nat) : I.type :=
  I.sub (sprec s) (I.fromZ (sprec s) (delta i j))
    (isum (sprec s) (map (fun k => I.mul (sprec s) (Biv s i k) (Aiv s k j))
                         (seq 0 (sy_n s)))).
Definition rowsum (s : system) (Mi : nat -> I.type) : I.type :=
  isum (sprec s) (map (fun j => I.abs (Mi j)) (seq 0 (sy_n s))).
Definition centre_env (s : system) : env I.type :=
  iextend (sprec s) (ienv_of (sprec s) (sy_centre s)) (sy_binds s).
Definition Fc (s : system) (k : nat) : I.type :=
  ieval (sprec s) (centre_env s) (Evar (oslot s k)).

(** The outputs at the centre, tabulated the same way. *)
Definition Fctab (s : system) : list I.type :=
  let env := centre_env s in
  map (fun k => ieval (sprec s) env (Evar (oslot s k))) (seq 0 (sy_n s)).
Definition Ft (ft : list I.type) (k : nat) : I.type := nth k ft I.nai.

Definition Viv (ft : list I.type) (s : system) (i : nat) : I.type :=
  isum (sprec s) (map (fun k => I.mul (sprec s) (Aiv s i k) (Ft ft k))
                      (seq 0 (sy_n s))).

(** The Jacobian entry is a real number when its enclosure sits below the
    claimed bound M, since an enclosure of a NaN is unbounded. *)
Definition entry_ok (s : system) (xi : I.type) : bool :=
  nonneg (I.sub (sprec s) (Miv s) (I.abs xi)).

Definition check_newton (s : system) : bool :=
  let prec := sprec s in
  let n := sy_n s in
  let base := sbase s in
  let len := slen s in
  let jt := Jtab s in
  let ft := Fctab s in
  Nat.leb n base && Nat.ltb 0 len && well_formed base (sy_binds s) &&
  Nat.eqb (length (sy_out s)) n &&
  forallb (fun o => Nat.leb base o && Nat.ltb o (base + len)) (sy_out s) &&
  Z.leb 0 (sy_r s) &&
  nonneg (Kiv s) &&
  nonneg (ieval prec eempty
            (Esub (Esub e1 (eps_e (sy_KN s) (sy_Kq s))) (epow2 (-20)))) &&
  forallb (fun j => forallb (fun k => entry_ok s (Jt jt k j)) (seq 0 n)) (seq 0 n) &&
  forallb (fun i => nonneg (I.sub prec (Kiv s) (rowsum s (Giv jt s i)))) (seq 0 n) &&
  forallb (fun i => nonneg (I.sub prec (Kiv s) (rowsum s (Hiv s i)))) (seq 0 n) &&
  forallb (fun i =>
             nonneg (I.sub prec (Riv s)
                       (I.add prec (I.abs (Viv ft s i))
                              (I.mul prec (Kiv s) (Riv s)))))
          (seq 0 n).

Lemma Jtab_spec :
  forall s k j, (k < sy_n s)%nat -> (j < sy_n s)%nat -> Jt (Jtab s) k j = J s k j.
Proof.
  intros s k j Hk Hj. unfold Jt, Jtab, colvals, J.
  rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbv zeta.
  rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. reflexivity.
Qed.

Lemma Fctab_spec :
  forall s k, (k < sy_n s)%nat -> Ft (Fctab s) k = Fc s k.
Proof.
  intros s k Hk. unfold Ft, Fctab, Fc. cbv zeta.
  rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* What the outputs mean                                             *)

(** Output k at an environment, and the map the fixed point is sought of. *)
Definition Fx (s : system) (e : env ExtendedR) (k : nat) : ExtendedR :=
  xeval (xextend e (sy_binds s)) (Evar (oslot s k)).

Definition Freal (s : system) (p : list R) : nat -> R :=
  fun k => proj_val (Fx s (E (sy_centre s) (sy_n s) p) k).

Definition Gmap (s : system) (p : list R) : list R :=
  vsub p (map (fun i => sumn (fun k => AR s i k * Freal s p k) (sy_n s))
              (seq 0 (sy_n s))).

Definition in_box (s : system) (p : list R) : Prop :=
  length p = sy_n s /\ in_boxf (sy_centre s) (sy_r s) (sy_n s) (fun i => nth i p 0).

(* ---------------------------------------------------------------- *)
(* Facts about sums and containment used by the assembly            *)

Lemma sumn_kron :
  forall (v : nat -> R) n i, (i < n)%nat ->
  sumn (fun j => IZR (delta i j) * v j) n = v i.
Proof.
  intros v n i Hi. induction n as [|n IH]. lia.
  simpl. destruct (Nat.eq_dec i n) as [->|Hne].
  - rewrite (sumn_ext _ (fun _ => 0)).
    + rewrite sumn_zero. unfold delta. rewrite Nat.eqb_refl. simpl. ring.
    + intros k Hk. unfold delta. rewrite (proj2 (Nat.eqb_neq n k)) by lia. simpl. ring.
  - rewrite IH by lia. unfold delta. rewrite (proj2 (Nat.eqb_neq i n)) by lia.
    simpl. ring.
Qed.

Lemma in_seq_lt : forall n k, (k < n)%nat -> In k (seq 0 n).
Proof. intros. apply in_seq. lia. Qed.

(** A sum of enclosures over the modes contains the sum of the reals. *)
Lemma isum_seq_correct :
  forall prec (fi : nat -> I.type) (fr : nat -> R) n,
  (forall k, (k < n)%nat -> contains (I.convert (fi k)) (Xreal (fr k))) ->
  contains (I.convert (isum prec (map fi (seq 0 n)))) (Xreal (sumn fr n)).
Proof.
  intros prec fi fr n H.
  rewrite <- sumn_fold.
  apply isum_correct.
  - rewrite !length_map. reflexivity.
  - intros k Hk. rewrite length_map, length_seq in Hk.
    rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
    rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
    rewrite seq_nth by lia. apply H. lia.
Qed.

Lemma Xabs_real : forall x, Xabs (Xreal x) = Xreal (Rabs x).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* Reading the check                                                 *)

Section Check.

Variable s : system.
Hypothesis Hchk : check_newton s = true.

Notation prec := (sprec s).
Notation n := (sy_n s).
Notation base := (sbase s).
Notation len := (slen s).
Notation c := (sy_centre s).
Notation r := (sy_r s).
Notation binds := (sy_binds s).

Lemma chk_all :
  (n <= base)%nat /\ (0 < len)%nat /\ well_formed base binds = true /\
  length (sy_out s) = n /\
  (forall k, (k < n)%nat ->
     (base <= oslot s k)%nat /\ (oslot s k < base + len)%nat) /\
  (0 <= r)%Z /\ nonneg (Kiv s) = true /\
  nonneg (ieval prec eempty
            (Esub (Esub e1 (eps_e (sy_KN s) (sy_Kq s))) (epow2 (-20)))) = true /\
  (forall j k, (j < n)%nat -> (k < n)%nat ->
     entry_ok s (Jt (Jtab s) k j) = true) /\
  (forall i, (i < n)%nat ->
     nonneg (I.sub prec (Kiv s) (rowsum s (Giv (Jtab s) s i))) = true) /\
  (forall i, (i < n)%nat ->
     nonneg (I.sub prec (Kiv s) (rowsum s (Hiv s i))) = true) /\
  (forall i, (i < n)%nat ->
     nonneg (I.sub prec (Riv s)
               (I.add prec (I.abs (Viv (Fctab s) s i)) (I.mul prec (Kiv s) (Riv s)))) = true).
Proof.
  unfold check_newton in Hchk. cbv zeta in Hchk.
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as [[[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11] H12].
  apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. apply Nat.eqb_eq in H4.
  rewrite forallb_forall in H5, H9, H10, H11, H12. apply Z.leb_le in H6.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 (conj H7 (conj H8
            (conj _ (conj _ (conj _ _))))))))))).
  - intros k Hk.
    specialize (H5 (oslot s k) ltac:(unfold oslot; apply nth_In; lia)).
    apply andb_true_iff in H5. destruct H5 as [Ha Hb].
    apply Nat.leb_le in Ha. apply Nat.ltb_lt in Hb. split; lia.
  - intros j k Hj Hk. specialize (H9 j (in_seq_lt _ _ Hj)).
    rewrite forallb_forall in H9. apply H9. now apply in_seq_lt.
  - intros i Hi. apply H10. now apply in_seq_lt.
  - intros i Hi. apply H11. now apply in_seq_lt.
  - intros i Hi. apply H12. now apply in_seq_lt.
Qed.

Lemma c_nb : (n <= base)%nat.
Proof. destruct chk_all as (H & _). exact H. Qed.
Lemma c_len : (0 < len)%nat.
Proof. destruct chk_all as (_ & H & _). exact H. Qed.
Lemma c_wf : well_formed base binds = true.
Proof. destruct chk_all as (_ & _ & H & _). exact H. Qed.
Lemma c_out : forall k, (k < n)%nat ->
  (base <= oslot s k)%nat /\ (oslot s k < base + len)%nat.
Proof. destruct chk_all as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma c_r : (0 <= r)%Z.
Proof. destruct chk_all as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma c_jac : forall j k, (j < n)%nat -> (k < n)%nat ->
  entry_ok s (Jt (Jtab s) k j) = true.
Proof. destruct chk_all as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma c_rowG : forall i, (i < n)%nat ->
  nonneg (I.sub prec (Kiv s) (rowsum s (Giv (Jtab s) s i))) = true.
Proof. destruct chk_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma c_rowH : forall i, (i < n)%nat ->
  nonneg (I.sub prec (Kiv s) (rowsum s (Hiv s i))) = true.
Proof. destruct chk_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma c_first : forall i, (i < n)%nat ->
  nonneg (I.sub prec (Riv s)
            (I.add prec (I.abs (Viv (Fctab s) s i)) (I.mul prec (Kiv s) (Riv s)))) = true.
Proof. destruct chk_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma K_nonneg : 0 <= KR s.
Proof.
  destruct chk_all as (_ & _ & _ & _ & _ & _ & H & _).
  destruct (nonneg_correct _ _ (dyad_correct prec (sy_KN s, sy_Kq s)) H)
    as [d [Hd Hge]].
  unfold KR. injection Hd as <-. exact Hge.
Qed.

Lemma K_lt_one : KR s < 1.
Proof.
  destruct chk_all as (_ & _ & _ & _ & _ & _ & _ & H & _).
  assert (Hc := ieval_correct prec eempty eempty
                  (Esub (Esub e1 (eps_e (sy_KN s) (sy_Kq s))) (epow2 (-20)))
                  env_ok_nil).
  destruct (nonneg_correct _ _ Hc H) as [d [Hd Hge]].
  cbn [xeval] in Hd. rewrite xeval_eps_e in Hd. unfold e1 in Hd. cbn in Hd.
  injection Hd as Hd. unfold KR, dyadR. simpl fst. simpl snd.
  assert (0 < powerRZ 2 (-20)) by (apply powerRZ_lt; lra).
  lra.
Qed.

Lemma r_nonneg : 0 <= IZR r.
Proof. apply IZR_le. exact c_r. Qed.

(* ---------------------------------------------------------------- *)
(* One coordinate at a time                                          *)

(** The doubled environment along unknown j from a point environment. *)
Definition Fu (e : env ExtendedR) (j : nat) (t : R) : env ExtendedR :=
  xextend (eset j e (Xreal t)) (with_derivs j base len binds).

Lemma in_boxf_eset :
  forall f j t, in_boxf c r n f -> (j < n)%nat ->
  IZR (nth j c 0%Z - r) <= t <= IZR (nth j c 0%Z + r) ->
  in_boxf c r n (fun i => if Nat.eqb i j then t else f i).
Proof.
  intros f j t Hf Hj Ht i Hi. destruct (Nat.eqb i j) eqn:E.
  - apply Nat.eqb_eq in E. subst i. exact Ht.
  - now apply Hf.
Qed.

(** Every Jacobian entry is a real number enclosed by J, at every point of
    the box. *)
Lemma jac_entry :
  forall f e j k t,
  (j < n)%nat -> (k < n)%nat ->
  in_boxf c r n f -> point_spec c n base f e ->
  IZR (nth j c 0%Z - r) <= t <= IZR (nth j c 0%Z + r) ->
  exists d, eget (oslot s k + len) (Fu e j t) Xnan = Xreal d /\
            contains (I.convert (J s k j)) (Xreal d).
Proof.
  intros f e j k t Hj Hk Hf He Ht.
  assert (Hok : env_ok (box s) (eset j e (Xreal t))).
  { apply (box_env_ok prec c r n (fun i => if Nat.eqb i j then t else f i)).
    - exact c_nb.
    - now apply in_boxf_eset.
    - apply point_spec_eset. exact Hj. exact c_nb. exact He. }
  assert (Henv := iextend_correct prec (with_derivs j base len binds) _ _ Hok).
  assert (Hc := ieval_correct prec _ _ (Evar (oslot s k + len)) Henv).
  cbn [xeval] in Hc.
  change (xextend (eset j e (Xreal t)) (with_derivs j base len binds))
    with (Fu e j t) in Hc.
  change (ieval prec (iextend prec (box s) (with_derivs j base len binds))
            (Evar (oslot s k + len))) with (J s k j) in Hc.
  (* the entry's enclosure sits below M, so the value it encloses is real *)
  assert (Hm := c_jac j k Hj Hk). unfold entry_ok in Hm.
  rewrite Jtab_spec in Hm by assumption.
  assert (Hc2 : contains (I.convert (I.sub prec (Miv s) (I.abs (J s k j))))
                  (Xsub (Xreal (dyadR (sy_MN s, sy_Mq s)))
                        (Xabs (eget (oslot s k + len) (Fu e j t) Xnan)))).
  { apply I.sub_correct. apply dyad_correct. apply I.abs_correct. exact Hc. }
  destruct (nonneg_correct _ _ Hc2 Hm) as [d0 [Hd0 _]].
  destruct (eget (oslot s k + len) (Fu e j t) Xnan) as [|d] eqn:Hd.
  { simpl in Hd0. discriminate. }
  exists d. split. reflexivity. exact Hc.
Qed.

(** The derivative slot of an output along unknown j. *)
Lemma output_deriv :
  forall f e j k,
  (j < n)%nat -> (k < n)%nat -> point_spec c n base f e ->
  forall t, Xderive_pt (slot_along (Fu e j) (oslot s k)) (Xreal t)
                       (eget (oslot s k + len) (Fu e j t) Xnan).
Proof.
  intros f e j k Hj Hk [Hu [Hp Hz]].
  assert (Hbase : inv j base len (fun t => eset j e (Xreal t)) base).
  { apply inv_base. generalize c_nb; lia. exact c_len.
    - intros i Hi. now apply Hz.
    - intros i Hi. destruct (lt_dec i n) as [H|H].
      + exists (f i). now apply Hu.
      + exists (IZR (nth i c 0%Z)). apply Hp; lia. }
  assert (Hres := inv_bindings j base len ltac:(generalize c_nb; lia) c_len binds
                    _ base Hbase c_wf (Nat.le_refl base)
                    ltac:(unfold slen; lia)).
  apply (deriv_slot j base len _ (base + length binds) (oslot s k)).
  generalize c_nb; lia. apply c_out. exact Hk. exact Hres.
Qed.

(** The value slot of the doubled environment is the output at the moved
    point. *)
Lemma output_value :
  forall e e' j k t,
  (j < n)%nat -> (k < n)%nat ->
  (forall i, eget i (eset j e (Xreal t)) Xnan = eget i e' Xnan) ->
  eget (oslot s k) (Fu e j t) Xnan = Fx s e' k.
Proof.
  intros e e' j k t Hj Hk Hag.
  unfold Fu, Fx. cbn [xeval].
  apply (values_agree j base len binds _ _ c_wf eq_refl Hag).
  destruct (c_out k Hk). lia.
Qed.

Lemma plain_agree :
  forall e1 e2,
  (forall i, eget i e1 Xnan = eget i e2 Xnan) ->
  forall k, (k < n)%nat -> Fx s e1 k = Fx s e2 k.
Proof.
  intros e1 e2 Hag k Hk. unfold Fx. cbn [xeval].
  rewrite <- (values_agree 0 base len binds e1 e1 c_wf eq_refl (fun _ => eq_refl))
    by (destruct (c_out k Hk); lia).
  apply (values_agree 0 base len binds e1 e2 c_wf eq_refl Hag).
  destruct (c_out k Hk). lia.
Qed.

Lemma point_spec_ext :
  forall f g e, (forall i, (i < n)%nat -> f i = g i) ->
  point_spec c n base f e -> point_spec c n base g e.
Proof.
  intros f g e Hfg [Hu [Hp Hz]]. split; [|split]; try assumption.
  intros i Hi. rewrite Hu by exact Hi. now rewrite Hfg.
Qed.

(** The increment of an output between two points of the box that differ
    in one unknown. *)
Lemma step_one :
  forall f e j k a b,
  (j < n)%nat -> (k < n)%nat ->
  in_boxf c r n f -> point_spec c n base f e ->
  IZR (nth j c 0%Z - r) <= a <= IZR (nth j c 0%Z + r) ->
  IZR (nth j c 0%Z - r) <= b <= IZR (nth j c 0%Z + r) ->
  exists wa wb d,
    eget (oslot s k) (Fu e j a) Xnan = Xreal wa /\
    eget (oslot s k) (Fu e j b) Xnan = Xreal wb /\
    contains (I.convert (J s k j)) (Xreal d) /\
    wb - wa = d * (b - a).
Proof.
  intros f e j k a b Hj Hk Hf He Ha Hb.
  apply (increment_along (Fu e j) (oslot s k) (oslot s k + len) (J s k j) a b).
  - apply (output_deriv f e j k Hj Hk He).
  - intros t Ht.
    apply (jac_entry f e j k t Hj Hk Hf He).
    unfold Rmin, Rmax in Ht. destruct (Rle_dec a b); lra.
Qed.

(** The output is a real number at every point of the box. *)
Lemma real_at :
  forall p, in_box s p -> forall k, (k < n)%nat ->
  exists v, Fx s (E c n p) k = Xreal v.
Proof.
  intros p [Hlen Hbox] k Hk.
  assert (Hn : (0 < n)%nat) by lia.
  assert (Hspec := E_spec c n p Hlen c_nb).
  destruct (step_one _ _ 0 k (nth 0 p 0) (nth 0 p 0) Hn Hk Hbox Hspec
              (Hbox 0%nat Hn) (Hbox 0%nat Hn)) as [wa [_ [_ [Hwa _]]]].
  exists wa. rewrite <- Hwa.
  symmetry. apply (output_value _ _ 0 k _ Hn Hk).
  intros i. destruct (Nat.eq_dec i 0) as [->|Hne].
  - rewrite eget_eset_eq. destruct Hspec as [Hu _]. symmetry. now apply Hu.
  - now rewrite eget_eset_neq.
Qed.

(** The coordinates of the walk from y to x. *)
Definition walk (x y : list R) (m : nat) : list R :=
  map (fun i => if Nat.ltb i m then nth i x 0 else nth i y 0) (seq 0 n).

Lemma walk_box :
  forall x y m, in_box s x -> in_box s y -> in_box s (walk x y m).
Proof.
  intros x y m [Hx Hbx] [Hy Hby]. split.
  - unfold walk. rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold walk. rewrite nth_map_seq by exact Hi.
    destruct (Nat.ltb i m). now apply Hbx. now apply Hby.
Qed.

(** Along the walk the increment is a sum of enclosed derivatives times
    coordinate differences. *)
Lemma telescope :
  forall x y k, in_box s x -> in_box s y -> (k < n)%nat ->
  exists D : nat -> R,
    (forall j, (j < n)%nat -> contains (I.convert (J s k j)) (Xreal (D j))) /\
    exists vx vy,
      Fx s (E c n x) k = Xreal vx /\ Fx s (E c n y) k = Xreal vy /\
      vx - vy = sumn (fun j => D j * (nth j x 0 - nth j y 0)) n.
Proof.
  intros x y k Hx Hy Hk.
  assert (Hn : (0 < n)%nat) by lia.
  assert (Hwalk : forall m, (m <= n)%nat ->
    exists D : nat -> R,
      (forall j, (j < m)%nat -> contains (I.convert (J s k j)) (Xreal (D j))) /\
      exists v0 vm,
        Fx s (E c n (walk x y 0)) k = Xreal v0 /\
        Fx s (E c n (walk x y m)) k = Xreal vm /\
        vm - v0 = sumn (fun j => D j * (nth j x 0 - nth j y 0)) m).
  { intros m. induction m as [|m IH]; intros Hm.
    - destruct (real_at _ (walk_box x y 0 Hx Hy) k Hk) as [v0 Hv0].
      exists (fun _ => 0). split. intros j Hj. lia.
      exists v0, v0. split. exact Hv0. split. exact Hv0. simpl. ring.
    - destruct (IH ltac:(lia)) as [D [HD [v0 [vm [Hv0 [Hvm Hsum]]]]]].
      set (e := E c n (walk x y m)).
      assert (Hbm := walk_box x y m Hx Hy).
      assert (Hspec : point_spec c n base (fun i => nth i (walk x y m) 0) e).
      { apply E_spec. apply Hbm. exact c_nb. }
      destruct Hx as [Hlx Hbx]. destruct Hy as [Hly Hby].
      destruct (step_one _ e m k (nth m y 0) (nth m x 0) ltac:(lia) Hk (proj2 Hbm)
                  Hspec (Hby m ltac:(lia)) (Hbx m ltac:(lia)))
        as [wa [wb [d [Hwa [Hwb [Hd Hinc]]]]]].
      (* the two ends of the step are the two walks *)
      assert (Ha : eget (oslot s k) (Fu e m (nth m y 0)) Xnan = Fx s e k).
      { apply (output_value e e m k _ ltac:(lia) Hk).
        intros i. destruct (Nat.eq_dec i m) as [->|Hne].
        - rewrite eget_eset_eq. destruct Hspec as [Hu _]. rewrite Hu by lia.
          unfold walk. rewrite nth_map_seq by lia.
          rewrite (proj2 (Nat.ltb_ge m m)) by lia. reflexivity.
        - now rewrite eget_eset_neq. }
      assert (Hb : eget (oslot s k) (Fu e m (nth m x 0)) Xnan
                   = Fx s (E c n (walk x y (S m))) k).
      { apply (output_value e _ m k _ ltac:(lia) Hk).
        intros i.
        assert (Hspec' := E_spec c n (walk x y (S m))
                            (proj1 (walk_box x y (S m) (conj Hlx Hbx) (conj Hly Hby)))
                            c_nb).
        assert (Hset := point_spec_eset c n base _ e m (nth m x 0) ltac:(lia) c_nb Hspec).
        apply (point_spec_agree c n base
                 (fun i => if Nat.eqb i m then nth m x 0 else nth i (walk x y m) 0)
                 _ _ Hset).
        apply (point_spec_ext (fun i => nth i (walk x y (S m)) 0)).
        2: exact Hspec'.
        intros i0 Hi0. unfold walk. rewrite !nth_map_seq by lia.
        destruct (Nat.eq_dec i0 m) as [->|Hne].
        - rewrite Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt m (S m))) by lia. reflexivity.
        - rewrite (proj2 (Nat.eqb_neq i0 m) Hne).
          destruct (Nat.ltb i0 m) eqn:Elt.
          + apply Nat.ltb_lt in Elt. rewrite (proj2 (Nat.ltb_lt i0 (S m))) by lia. reflexivity.
          + apply Nat.ltb_ge in Elt. rewrite (proj2 (Nat.ltb_ge i0 (S m))) by lia. reflexivity. }
      rewrite Ha in Hwa. rewrite Hb in Hwb.
      fold e in Hvm. rewrite Hvm in Hwa. injection Hwa as <-.
      exists (fun j => if Nat.eqb j m then d else D j). split.
      { intros j Hj. destruct (Nat.eq_dec j m) as [->|Hne].
        - rewrite Nat.eqb_refl. exact Hd.
        - rewrite (proj2 (Nat.eqb_neq j m) Hne). apply HD. lia. }
      exists v0, wb. split. exact Hv0. split. exact Hwb.
      simpl. rewrite Nat.eqb_refl.
      rewrite (sumn_ext (fun j => (if Nat.eqb j m then d else D j) * (nth j x 0 - nth j y 0))
                        (fun j => D j * (nth j x 0 - nth j y 0))).
      + lra.
      + intros j Hj. rewrite (proj2 (Nat.eqb_neq j m)) by lia. reflexivity. }
  destruct (Hwalk n (Nat.le_refl n)) as [D [HD [v0 [vn [Hv0 [Hvn Hsum]]]]]].
  exists D. split. exact HD.
  exists vn, v0. split; [|split].
  - rewrite <- Hvn. apply plain_agree; try exact Hk.
    apply (point_spec_agree c n base (fun i => nth i x 0)).
    + apply E_spec. apply Hx. exact c_nb.
    + apply (point_spec_ext (fun i => nth i (walk x y n) 0)).
      * intros i Hi. unfold walk. rewrite nth_map_seq by lia.
        rewrite (proj2 (Nat.ltb_lt i n)) by lia. reflexivity.
      * apply E_spec. apply walk_box; assumption. exact c_nb.
  - rewrite <- Hv0. apply plain_agree; try exact Hk.
    apply (point_spec_agree c n base (fun i => nth i y 0)).
    + apply E_spec. apply Hy. exact c_nb.
    + apply (point_spec_ext (fun i => nth i (walk x y 0) 0)).
      * intros i Hi. unfold walk. rewrite nth_map_seq by lia. reflexivity.
      * apply E_spec. apply walk_box; assumption. exact c_nb.
  - exact Hsum.
Qed.

(** The same for every output at once. *)
Lemma telescope_all :
  forall x y, in_box s x -> in_box s y ->
  exists D : nat -> nat -> R,
    (forall k j, (k < n)%nat -> (j < n)%nat ->
       contains (I.convert (J s k j)) (Xreal (D k j))) /\
    (forall k, (k < n)%nat ->
       Freal s x k - Freal s y k
       = sumn (fun j => D k j * (nth j x 0 - nth j y 0)) n).
Proof.
  intros x y Hx Hy.
  assert (H : forall m, (m <= n)%nat ->
    exists D : nat -> nat -> R,
      (forall k j, (k < m)%nat -> (j < n)%nat ->
         contains (I.convert (J s k j)) (Xreal (D k j))) /\
      (forall k, (k < m)%nat ->
         Freal s x k - Freal s y k
         = sumn (fun j => D k j * (nth j x 0 - nth j y 0)) n)).
  { intros m. induction m as [|m IH]; intros Hm.
    - exists (fun _ _ => 0). split; intros; lia.
    - destruct (IH ltac:(lia)) as [D [HD Hval]].
      destruct (telescope x y m Hx Hy ltac:(lia)) as [Dm [HDm [vx [vy [Hvx [Hvy Hs]]]]]].
      exists (fun k j => if Nat.eqb k m then Dm j else D k j). split.
      + intros k j Hk Hj. destruct (Nat.eq_dec k m) as [->|Hne].
        * rewrite Nat.eqb_refl. now apply HDm.
        * rewrite (proj2 (Nat.eqb_neq k m) Hne). apply HD; lia.
      + intros k Hk. destruct (Nat.eq_dec k m) as [->|Hne].
        * rewrite Nat.eqb_refl. unfold Freal. rewrite Hvx, Hvy. simpl. exact Hs.
        * rewrite (proj2 (Nat.eqb_neq k m) Hne). apply Hval. lia. }
  destruct (H n (Nat.le_refl n)) as [D HD]. exists D. exact HD.
Qed.

(* ---------------------------------------------------------------- *)
(* The contraction                                                   *)

Lemma length_Gmap : forall p, length p = n -> length (Gmap s p) = n.
Proof.
  intros p Hp. unfold Gmap. rewrite length_vsub.
  exact Hp. rewrite Hp, length_map, length_seq. reflexivity.
Qed.

Lemma nth_Gmap :
  forall p i, length p = n -> (i < n)%nat ->
  nth i (Gmap s p) 0 = nth i p 0 - sumn (fun k => AR s i k * Freal s p k) n.
Proof.
  intros p i Hp Hi. unfold Gmap.
  rewrite nth_vsub by (rewrite ?length_map, ?length_seq; lia).
  rewrite nth_map_seq by exact Hi. reflexivity.
Qed.

(** A row of I - A J contains the real row built from any enclosed
    derivatives. *)
Lemma G_contains :
  forall (D : nat -> nat -> R) i j,
  (i < n)%nat -> (j < n)%nat ->
  (forall k, (k < n)%nat -> contains (I.convert (J s k j)) (Xreal (D k j))) ->
  contains (I.convert (Giv (Jtab s) s i j))
    (Xreal (IZR (delta i j) - sumn (fun k => AR s i k * D k j) n)).
Proof.
  intros D i j Hi Hj HD. unfold Giv.
  change (Xreal (IZR (delta i j) - sumn (fun k => AR s i k * D k j) n))
    with (Xsub (Xreal (IZR (delta i j))) (Xreal (sumn (fun k => AR s i k * D k j) n))).
  apply I.sub_correct. apply I.fromZ_correct.
  apply isum_seq_correct. intros k Hk.
  change (Xreal (AR s i k * D k j)) with (Xmul (Xreal (AR s i k)) (Xreal (D k j))).
  apply I.mul_correct. apply dyad_correct.
  rewrite Jtab_spec by assumption. now apply HD.
Qed.

Lemma H_contains :
  forall i j, (i < n)%nat -> (j < n)%nat ->
  contains (I.convert (Hiv s i j))
    (Xreal (IZR (delta i j) - sumn (fun k => BR s i k * AR s k j) n)).
Proof.
  intros i j Hi Hj. unfold Hiv.
  change (Xreal (IZR (delta i j) - sumn (fun k => BR s i k * AR s k j) n))
    with (Xsub (Xreal (IZR (delta i j))) (Xreal (sumn (fun k => BR s i k * AR s k j) n))).
  apply I.sub_correct. apply I.fromZ_correct.
  apply isum_seq_correct. intros k Hk.
  change (Xreal (BR s i k * AR s k j)) with (Xmul (Xreal (BR s i k)) (Xreal (AR s k j))).
  apply I.mul_correct; apply dyad_correct.
Qed.

(** A row whose entries are enclosed and whose row sum passed the check
    sums below K in absolute value. *)
Lemma row_bound :
  forall (Mi : nat -> I.type) (g : nat -> R),
  (forall j, (j < n)%nat -> contains (I.convert (Mi j)) (Xreal (g j))) ->
  nonneg (I.sub prec (Kiv s) (rowsum s Mi)) = true ->
  sumn (fun j => Rabs (g j)) n <= KR s.
Proof.
  intros Mi g Hg Hchk'.
  assert (Hrow : contains (I.convert (rowsum s Mi)) (Xreal (sumn (fun j => Rabs (g j)) n))).
  { unfold rowsum. apply isum_seq_correct. intros j Hj.
    rewrite <- Xabs_real. apply I.abs_correct. now apply Hg. }
  assert (Hc := I.sub_correct prec _ _ _ _ (dyad_correct prec (sy_KN s, sy_Kq s)) Hrow).
  destruct (nonneg_correct _ _ Hc Hchk') as [d [Hd Hge]].
  cbn in Hd. injection Hd as Hd. unfold KR. lra.
Qed.

Lemma contraction :
  forall x y, in_box s x -> in_box s y ->
  vmax (vsub (Gmap s x) (Gmap s y)) <= KR s * vmax (vsub x y).
Proof.
  intros x y Hx Hy.
  destruct (telescope_all x y Hx Hy) as [D [HD Hval]].
  assert (Hlx : length x = n) by apply Hx.
  assert (Hly : length y = n) by apply Hy.
  set (M := vmax (vsub x y)).
  assert (HM : forall j, (j < n)%nat -> Rabs (nth j x 0 - nth j y 0) <= M).
  { intros j Hj. unfold M. rewrite <- (nth_vsub x y j) by lia. apply vmax_nth. }
  apply vmax_le.
  { apply Rmult_le_pos. apply K_nonneg. apply vmax_nonneg. }
  intros i Hi.
  rewrite length_vsub in Hi by (rewrite !length_Gmap; lia).
  rewrite length_Gmap in Hi by exact Hlx.
  rewrite nth_vsub by (rewrite !length_Gmap; lia).
  rewrite !nth_Gmap by lia.
  (* the row as a sum against the coordinate differences *)
  set (g := fun j => IZR (delta i j) - sumn (fun k => AR s i k * D k j) n).
  assert (Hrow : nth i x 0 - sumn (fun k => AR s i k * Freal s x k) n
                 - (nth i y 0 - sumn (fun k => AR s i k * Freal s y k) n)
                 = sumn (fun j => g j * (nth j x 0 - nth j y 0)) n).
  { unfold g.
    rewrite (sumn_ext (fun j => (IZR (delta i j) - sumn (fun k => AR s i k * D k j) n)
                                * (nth j x 0 - nth j y 0))
                      (fun j => IZR (delta i j) * (nth j x 0 - nth j y 0)
                                - sumn (fun k => AR s i k * (D k j * (nth j x 0 - nth j y 0))) n)).
    2: { intros j Hj.
         rewrite (sumn_ext (fun k => AR s i k * (D k j * (nth j x 0 - nth j y 0)))
                           (fun k => (nth j x 0 - nth j y 0) * (AR s i k * D k j)))
           by (intros; ring).
         rewrite sumn_scal. ring. }
    rewrite sumn_minus. rewrite sumn_kron by exact Hi.
    rewrite sumn_swap.
    rewrite (sumn_ext (fun k => sumn (fun j => AR s i k * (D k j * (nth j x 0 - nth j y 0))) n)
                      (fun k => AR s i k * (Freal s x k - Freal s y k))).
    2: { intros k Hk. rewrite sumn_scal. rewrite (Hval k Hk). reflexivity. }
    rewrite (sumn_ext (fun k => AR s i k * (Freal s x k - Freal s y k))
                      (fun k => AR s i k * Freal s x k - AR s i k * Freal s y k))
      by (intros; ring).
    rewrite sumn_minus. ring. }
  rewrite Hrow.
  eapply Rle_trans. apply (sumn_prod_bound g _ n M HM).
  apply Rmult_le_compat_r. apply vmax_nonneg.
  apply (row_bound (Giv (Jtab s) s i) g).
  - intros j Hj. apply G_contains; try assumption. intros k Hk. now apply HD.
  - now apply c_rowG.
Qed.

(* ---------------------------------------------------------------- *)
(* The first step, from the centre                                   *)

Definition x0 : list R := map IZR (firstn n c).

Lemma length_x0 : length x0 = n.
Proof. unfold x0. rewrite length_map, length_firstn. generalize c_nb. unfold sbase. lia. Qed.

Lemma nth_x0 : forall i, (i < n)%nat -> nth i x0 0 = IZR (nth i c 0%Z).
Proof.
  intros i Hi. unfold x0.
  rewrite (nth_map_in _ _ _ _ _ 0%Z)
    by (rewrite length_firstn; generalize c_nb; unfold sbase; lia).
  rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt i n) Hi). reflexivity.
Qed.

Lemma x0_box : in_box s x0.
Proof.
  split. exact length_x0.
  intros i Hi. rewrite nth_x0 by exact Hi. rewrite minus_IZR, plus_IZR.
  generalize r_nonneg. lra.
Qed.

Lemma first_step :
  vmax (vsub x0 (Gmap s x0)) <= (1 - KR s) * IZR r.
Proof.
  assert (HE : E c n x0 = xenv_of c) by (apply E_centre; exact c_nb).
  apply vmax_le.
  { apply Rmult_le_pos. generalize K_lt_one. lra. exact r_nonneg. }
  intros i Hi.
  rewrite length_vsub in Hi by (rewrite length_Gmap; apply length_x0).
  rewrite length_x0 in Hi.
  assert (HG : length (Gmap s x0) = n) by (apply length_Gmap; exact length_x0).
  rewrite nth_vsub by (rewrite ?HG, ?length_x0; lia).
  rewrite nth_Gmap by (try exact length_x0; lia).
  replace (nth i x0 0 - (nth i x0 0 - sumn (fun k => AR s i k * Freal s x0 k) n))
    with (sumn (fun k => AR s i k * Freal s x0 k) n) by ring.
  (* the outputs at the centre, contained in the thin evaluation *)
  assert (HF : forall k, (k < n)%nat ->
            contains (I.convert (Fc s k)) (Xreal (Freal s x0 k))).
  { intros k Hk. unfold Freal. rewrite HE.
    destruct (real_at x0 x0_box k Hk) as [v Hv]. rewrite HE in Hv.
    rewrite Hv. simpl.
    assert (Henv := iextend_correct prec binds _ _ (env_ok_fromZ prec c)).
    assert (H := ieval_correct prec _ _ (Evar (oslot s k)) Henv).
    unfold Fx in Hv. rewrite Hv in H. exact H. }
  assert (HV : contains (I.convert (Viv (Fctab s) s i))
                 (Xreal (sumn (fun k => AR s i k * Freal s x0 k) n))).
  { unfold Viv. apply isum_seq_correct. intros k Hk.
    change (Xreal (AR s i k * Freal s x0 k))
      with (Xmul (Xreal (AR s i k)) (Xreal (Freal s x0 k))).
    apply I.mul_correct. apply dyad_correct.
    rewrite Fctab_spec by assumption. now apply HF. }
  set (v := sumn (fun k => AR s i k * Freal s x0 k) n) in *.
  assert (Hc : contains (I.convert (I.sub prec (Riv s)
                           (I.add prec (I.abs (Viv (Fctab s) s i)) (I.mul prec (Kiv s) (Riv s)))))
                        (Xreal (IZR r - (Rabs v + KR s * IZR r)))).
  { change (Xreal (IZR r - (Rabs v + KR s * IZR r)))
      with (Xsub (Xreal (IZR r)) (Xadd (Xreal (Rabs v)) (Xmul (Xreal (KR s)) (Xreal (IZR r))))).
    apply I.sub_correct. apply I.fromZ_correct.
    apply I.add_correct.
    - rewrite <- Xabs_real. apply I.abs_correct. exact HV.
    - apply I.mul_correct. apply dyad_correct. apply I.fromZ_correct. }
  destruct (nonneg_correct _ _ Hc (c_first i Hi)) as [d [Hd Hge]].
  injection Hd as Hd. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The theorem                                                       *)

Definition X := vec n.
Definition xv0 : X := exist _ x0 length_x0.
Definition Gv (v : X) : X :=
  exist _ (Gmap s (proj1_sig v)) (length_Gmap _ (proj2_sig v)).

Lemma box_iff : forall v : X, vd n xv0 v <= IZR r <-> in_box s (proj1_sig v).
Proof.
  intros [p Hp]. unfold vd, xv0, in_box. simpl. split.
  - intros H. split. exact Hp.
    intros i Hi.
    assert (Hi' : Rabs (nth i x0 0 - nth i p 0) <= IZR r).
    { rewrite <- (nth_vsub x0 p i) by (rewrite ?length_x0; lia).
      eapply Rle_trans. apply vmax_nth. exact H. }
    rewrite nth_x0 in Hi' by exact Hi. rewrite minus_IZR, plus_IZR.
    unfold Rabs in Hi'. destruct (Rcase_abs (IZR (nth i c 0%Z) - nth i p 0)); lra.
  - intros [_ Hb]. apply vmax_le. exact r_nonneg.
    intros i Hi. rewrite length_vsub in Hi by (rewrite length_x0; lia).
    rewrite length_x0 in Hi.
    rewrite nth_vsub by (rewrite ?length_x0; lia). rewrite nth_x0 by exact Hi.
    specialize (Hb i Hi). rewrite minus_IZR, plus_IZR in Hb.
    apply Rabs_le. lra.
Qed.

Theorem newton_correct :
  exists x : list R,
    in_box s x /\
    (forall k, (k < n)%nat -> Fx s (E c n x) k = Xreal 0) /\
    (forall y, in_box s y ->
       (forall k, (k < n)%nat -> Fx s (E c n y) k = Xreal 0) -> y = x).
Proof.
  assert (Hcontract : forall x y : X,
            vd n xv0 x <= IZR r -> vd n xv0 y <= IZR r ->
            vd n (Gv x) (Gv y) <= KR s * vd n x y).
  { intros x y Hx Hy. apply box_iff in Hx. apply box_iff in Hy.
    unfold vd, Gv. simpl. now apply contraction. }
  assert (Hsmall : vd n xv0 (Gv xv0) <= (1 - KR s) * IZR r).
  { unfold vd, Gv, xv0. simpl. exact first_step. }
  destruct (contraction_fixed_point X (vd n) (vd_nonneg n) (vd_refl n) (vd_eq n)
              (vd_sym n) (vd_tri n) Gv xv0 (KR s) (IZR r) K_nonneg K_lt_one
              r_nonneg Hcontract Hsmall (vec_complete n xv0 (IZR r)))
    as [xs [Hxs Hfix]].
  destruct xs as [x Hx].
  assert (Hbox : in_box s x) by (apply (box_iff (exist _ x Hx)); exact Hxs).
  assert (HG : Gmap s x = x) by (exact (f_equal (@proj1_sig _ _) Hfix)).
  (* the fixed point makes A F(x) vanish *)
  assert (HAF : forall i, (i < n)%nat -> sumn (fun k => AR s i k * Freal s x k) n = 0).
  { intros i Hi.
    assert (H := f_equal (fun l => nth i l 0) HG). simpl in H.
    rewrite nth_Gmap in H by lia. lra. }
  (* and B's approximate inverse of A makes F(x) vanish *)
  assert (HF : forall k, (k < n)%nat -> Freal s x k = 0).
  { set (Fl := map (Freal s x) (seq 0 n)).
    assert (HFl : forall k, (k < n)%nat -> nth k Fl 0 = Freal s x k)
      by (intros k Hk; unfold Fl; now rewrite nth_map_seq).
    assert (Hrow : forall j, (j < n)%nat ->
              Freal s x j
              = sumn (fun i => (IZR (delta j i) - sumn (fun k => BR s j k * AR s k i) n)
                               * Freal s x i) n).
    { intros j Hj.
      rewrite (sumn_ext _ (fun i => IZR (delta j i) * Freal s x i
                                    - sumn (fun k => BR s j k * (AR s k i * Freal s x i)) n)).
      2: { intros i Hi.
           rewrite (sumn_ext (fun k => BR s j k * (AR s k i * Freal s x i))
                             (fun k => Freal s x i * (BR s j k * AR s k i))) by (intros; ring).
           rewrite sumn_scal. ring. }
      rewrite sumn_minus, sumn_kron by exact Hj.
      rewrite sumn_swap.
      rewrite (sumn_ext (fun k => sumn (fun i => BR s j k * (AR s k i * Freal s x i)) n)
                        (fun _ => 0)).
      rewrite sumn_zero. ring.
      intros k Hk. rewrite sumn_scal. rewrite HAF by exact Hk. ring. }
    assert (Hbnd : vmax Fl <= KR s * vmax Fl).
    { apply vmax_le. apply Rmult_le_pos. apply K_nonneg. apply vmax_nonneg.
      intros j Hj. unfold Fl in Hj. rewrite length_map, length_seq in Hj.
      rewrite HFl by exact Hj. rewrite Hrow by exact Hj.
      eapply Rle_trans.
      apply (sumn_prod_bound _ (Freal s x) n (vmax Fl)).
      { intros i Hi. rewrite <- HFl by exact Hi. apply vmax_nth. }
      apply Rmult_le_compat_r. apply vmax_nonneg.
      apply (row_bound (Hiv s j)).
      - intros i Hi. apply H_contains; assumption.
      - now apply c_rowH. }
    assert (Hz : vmax Fl = 0).
    { generalize (vmax_nonneg Fl) K_lt_one. intros. nra. }
    intros k Hk.
    assert (Hk' := vmax_nth Fl k). rewrite Hz, HFl in Hk' by exact Hk.
    generalize (Rabs_pos (Freal s x k)). intros.
    destruct (Req_dec (Freal s x k) 0) as [Hd|Hd]. exact Hd.
    exfalso. generalize (Rabs_pos_lt _ Hd). lra. }
  exists x. split. exact Hbox. split.
  - intros k Hk. destruct (real_at x Hbox k Hk) as [v Hv].
    rewrite Hv. f_equal. specialize (HF k Hk). unfold Freal in HF.
    rewrite Hv in HF. exact HF.
  - intros y Hy Hzero.
    assert (Hly : length y = n) by apply Hy.
    assert (HGy : Gmap s y = y).
    { apply (nth_ext _ _ 0 0). rewrite length_Gmap; lia.
      intros i Hi. rewrite length_Gmap in Hi by exact Hly.
      rewrite nth_Gmap by lia.
      rewrite (sumn_ext _ (fun _ => 0)). rewrite sumn_zero. ring.
      intros k Hk. unfold Freal. rewrite Hzero by exact Hk. simpl. ring. }
    set (yv := exist (fun l : list R => length l = n) y Hly).
    assert (Hyv : Gv yv = yv).
    { unfold Gv, yv. apply vec_eq. exact HGy. }
    assert (Hd : vd n (exist _ x Hx) yv <= KR s * vd n (exist _ x Hx) yv).
    { rewrite <- Hfix at 1. rewrite <- Hyv at 1.
      apply Hcontract. exact Hxs. apply box_iff. exact Hy. }
    assert (Hd0 : vd n (exist _ x Hx) yv = 0).
    { generalize (vd_nonneg n (exist _ x Hx) yv) K_lt_one. intros. nra. }
    apply vd_eq in Hd0. injection Hd0 as Hd0. now symmetry.
Qed.

End Check.

(* ---------------------------------------------------------------- *)
(* A system to run the check on                                      *)

(** The unit circle meets the diagonal: x^2 + y^2 - 1 = 0 and x - y = 0,
    the unknowns being the mantissas of slots 0 and 1 against the exponents
    given. The bindings are well formed from base 2. *)
Definition circle_binds (exps : list Z) : list binding :=
  [ (2%nat, Emul (evar exps 0) (evar exps 0)) ;
    (3%nat, Emul (evar exps 1) (evar exps 1)) ;
    (4%nat, Esub (Eadd (Evar 2) (Evar 3)) e1) ;
    (5%nat, Esub (evar exps 0) (evar exps 1)) ].

Definition circle_out : list nat := [4%nat; 5%nat].
