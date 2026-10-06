(** A second-order bound from coordinate derivatives on a box.

    For a function F of the coordinates y_0 .. y_(n-1) whose derivative along
    coordinate i is g_i, and whose g_i have derivatives along coordinate l
    bounded by K_il, everywhere on a box, the change of F between two points
    of the box less the gradient at a third point applied to the step obeys
    [taylor2]:

      |F(y) - F(y') - sum_i g_i(c) (y_i - y'_i)|
        <= sum_i sum_l K_il max(|y_l - c_l|, |y'_l - c_l|) |y_i - y'_i|.

    The proof crosses from y' to y one coordinate at a time with the mean
    value theorem, and bounds each partial at its intermediate point against
    the partial at c the same way ([grad_osc]). No derivative is taken in
    two coordinates at once. *)

From Coq Require Import Reals Lra Lia FunctionalExtensionality.
From Stellarocq Require Import Mat.

Local Open Scope R_scope.

Definition upd (y : nat -> R) (i : nat) (t : R) : nat -> R := fun j => if Nat.eqb j i then t else y j.

Lemma upd_upd : forall y i a b, upd (upd y i a) i b = upd y i b.
Proof.
  intros y i a b. apply functional_extensionality. intros j. unfold upd.
  destruct (Nat.eqb j i); reflexivity.
Qed.

Lemma upd_same : forall y i, upd y i (y i) = y.
Proof.
  intros y i. apply functional_extensionality. intros j. unfold upd.
  destruct (Nat.eqb_spec j i) as [->|]; reflexivity.
Qed.

(** The mean value theorem in either direction. *)
Lemma mvt_between :
  forall (f f' : R -> R) a b, (forall c, Rmin a b <= c <= Rmax a b -> derivable_pt_lim f c (f' c)) ->
  exists c, Rmin a b <= c <= Rmax a b /\ f b - f a = f' c * (b - a).
Proof.
  intros f f' a b Hd.
  destruct (Rtotal_order a b) as [Hab|[Hab|Hab]].
  - destruct (MVT_cor2 f f' a b Hab) as [c [Ec Hc]].
    + intros c Hc. apply Hd. rewrite Rmin_left, Rmax_right by lra. exact Hc.
    + exists c. rewrite Rmin_left, Rmax_right by lra. split; [lra | exact Ec].
  - subst b. exists a. rewrite Rmin_left, Rmax_left by lra. split; [lra | ring].
  - destruct (MVT_cor2 f f' b a Hab) as [c [Ec Hc]].
    + intros c Hc. apply Hd. rewrite Rmin_right, Rmax_left by lra. exact Hc.
    + exists c. rewrite Rmin_right, Rmax_left by lra. split; [lra|]. lra.
Qed.

(** A point between two others is no farther from a third than both. *)
Lemma between_dist :
  forall a b t c, Rmin a b <= t <= Rmax a b -> Rabs (t - c) <= Rmax (Rabs (a - c)) (Rabs (b - c)).
Proof.
  intros a b t c Ht.
  assert (Ha := Rle_abs (a - c)). assert (Ha' := Rle_abs (- (a - c))). rewrite Rabs_Ropp in Ha'.
  assert (Hb := Rle_abs (b - c)). assert (Hb' := Rle_abs (- (b - c))). rewrite Rabs_Ropp in Hb'.
  assert (M1 := Rmax_l (Rabs (a - c)) (Rabs (b - c))). assert (M2 := Rmax_r (Rabs (a - c)) (Rabs (b - c))).
  apply Rabs_le. unfold Rmin, Rmax in Ht. destruct (Rle_dec a b); split; lra.
Qed.

Section Taylor.

Variable n : nat.
Variables lo hi : nat -> R.

Definition inbox (y : nat -> R) : Prop := forall i, (i < n)%nat -> lo i <= y i <= hi i.

Variable F : (nat -> R) -> R.
Variable g : nat -> (nat -> R) -> R.
Variable Dg : nat -> nat -> (nat -> R) -> R.
Variable K : nat -> nat -> R.

Hypothesis HF : forall y, inbox y -> forall i, (i < n)%nat ->
  derivable_pt_lim (fun t => F (upd y i t)) (y i) (g i y).
Hypothesis Hg : forall y, inbox y -> forall i l, (i < n)%nat -> (l < n)%nat ->
  derivable_pt_lim (fun t => g i (upd y l t)) (y l) (Dg i l y).
Hypothesis HK : forall y, inbox y -> forall i l, (i < n)%nat -> (l < n)%nat -> Rabs (Dg i l y) <= K i l.

Lemma inbox_upd :
  forall y i t, inbox y -> (i < n)%nat -> lo i <= t <= hi i -> inbox (upd y i t).
Proof.
  intros y i t Hy Hi Ht j Hj. unfold upd. destruct (Nat.eqb_spec j i) as [->|]; [exact Ht | apply Hy; exact Hj].
Qed.

Lemma between_box :
  forall a b t i, lo i <= a <= hi i -> lo i <= b <= hi i -> Rmin a b <= t <= Rmax a b -> lo i <= t <= hi i.
Proof. intros a b t i Ha Hb Ht. unfold Rmin, Rmax in Ht. destruct (Rle_dec a b); lra. Qed.

(** Along one coordinate, F changes by a partial at a point between. *)
Lemma mvt_coord :
  forall (D : nat -> (nat -> R) -> R) (G : (nat -> R) -> R) y i t,
  (forall z, inbox z -> derivable_pt_lim (fun u => G (upd z i u)) (z i) (D i z)) ->
  inbox y -> (i < n)%nat -> lo i <= t <= hi i ->
  exists c, Rmin (y i) t <= c <= Rmax (y i) t /\ G (upd y i t) - G y = D i (upd y i c) * (t - y i).
Proof.
  intros D G y i t HD Hy Hi Ht.
  destruct (mvt_between (fun u => G (upd y i u)) (fun u => D i (upd y i u)) (y i) t) as [c [Hc Ec]].
  - intros c Hc. assert (Hb : inbox (upd y i c)) by (apply inbox_upd; [exact Hy | exact Hi | eapply between_box; [apply Hy; exact Hi | exact Ht | exact Hc]]).
    assert (H := HD (upd y i c) Hb).
    assert (Ez : upd y i c i = c) by (unfold upd; rewrite Nat.eqb_refl; reflexivity). rewrite Ez in H.
    rewrite (functional_extensionality (fun u => G (upd (upd y i c) i u)) (fun u => G (upd y i u))) in H
      by (intros u; rewrite upd_upd; reflexivity).
    exact H.
  - exists c. split; [exact Hc|]. cbv beta in Ec. rewrite upd_same in Ec. exact Ec.
Qed.

(** The path from c to y that takes the first k coordinates from y. *)
Definition path (c y : nat -> R) (k : nat) : nat -> R := fun j => if Nat.ltb j k then y j else c j.

Lemma path_box : forall c y k, inbox c -> inbox y -> inbox (path c y k).
Proof.
  intros c y k Hc Hy j Hj. unfold path. destruct (Nat.ltb j k); [apply Hy | apply Hc]; exact Hj.
Qed.

Lemma path_step : forall c y k, path c y (S k) = upd (path c y k) k (y k).
Proof.
  intros c y k. apply functional_extensionality. intros j. unfold path, upd.
  destruct (Nat.eqb_spec j k) as [->|Hne].
  - rewrite (proj2 (Nat.ltb_lt k (S k)) ltac:(lia)). reflexivity.
  - destruct (Nat.ltb_spec j (S k)); destruct (Nat.ltb_spec j k); try reflexivity; lia.
Qed.

Lemma path_k : forall c y k, path c y k k = c k.
Proof. intros c y k. unfold path. rewrite Nat.ltb_irrefl. reflexivity. Qed.

Lemma path_0 : forall c y, path c y 0 = c.
Proof. intros c y. apply functional_extensionality. intros j. reflexivity. Qed.

Lemma path_n : forall c y, (forall j, (n <= j)%nat -> y j = c j) -> path c y n = y.
Proof.
  intros c y H. apply functional_extensionality. intros j. unfold path.
  destruct (Nat.ltb_spec j n); [reflexivity | symmetry; apply H; lia].
Qed.

(** A sum of the steps of a path. *)
Lemma telescope :
  forall (G : (nat -> R) -> R) c y k, G (path c y k) - G c = msum (fun l => G (path c y (S l)) - G (path c y l)) k.
Proof.
  intros G c y k. induction k as [|k IH]; cbn [msum].
  - rewrite path_0. ring.
  - rewrite <- IH. ring.
Qed.

(** A partial at y against the same partial at c. *)
Lemma grad_osc :
  forall i y c, (i < n)%nat -> inbox y -> inbox c -> (forall j, (n <= j)%nat -> y j = c j) ->
  Rabs (g i y - g i c) <= msum (fun l => K i l * Rabs (y l - c l)) n.
Proof.
  intros i y c Hi Hy Hc Hyc.
  rewrite <- (path_n c y Hyc) at 1. rewrite telescope.
  eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros l Hl.
  rewrite path_step.
  destruct (mvt_coord (fun l z => Dg i l z) (g i) (path c y l) l (y l)
              (fun z Hz => Hg z Hz i l Hi Hl) (path_box c y l Hc Hy) Hl (Hy l Hl)) as [t [Ht Et]].
  rewrite Et, path_k, Rabs_mult.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  apply HK; [| exact Hi | exact Hl]. apply inbox_upd; [apply path_box; assumption | exact Hl |].
  eapply between_box; [| apply Hy; exact Hl | exact Ht]. rewrite path_k. apply Hc. exact Hl.
Qed.

(** The second-order bound. *)
Theorem taylor2 :
  forall y y' c, inbox y -> inbox y' -> inbox c ->
  (forall j, (n <= j)%nat -> y j = c j) -> (forall j, (n <= j)%nat -> y' j = c j) ->
  Rabs (F y - F y' - msum (fun i => g i c * (y i - y' i)) n)
  <= msum (fun i => msum (fun l => K i l * Rmax (Rabs (y l - c l)) (Rabs (y' l - c l))) n * Rabs (y i - y' i)) n.
Proof.
  intros y y' c Hy Hy' Hc Hyc Hy'c.
  assert (Hyy' : forall j, (n <= j)%nat -> y j = y' j) by (intros j Hj; rewrite Hyc, Hy'c by exact Hj; reflexivity).
  rewrite <- (path_n y' y Hyy') at 1. rewrite telescope.
  rewrite <- msum_minus. eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros i Hi.
  rewrite path_step.
  destruct (mvt_coord (fun i z => g i z) F (path y' y i) i (y i)
              (fun z Hz => HF z Hz i Hi) (path_box y' y i Hy' Hy) Hi (Hy i Hi)) as [t [Ht Et]].
  rewrite Et, path_k.
  set (z := upd (path y' y i) i t).
  assert (Hz : inbox z).
  { apply inbox_upd; [apply path_box; assumption | exact Hi |].
    eapply between_box; [| apply Hy; exact Hi | exact Ht]. rewrite path_k. apply Hy'. exact Hi. }
  replace (g i z * (y i - y' i) - g i c * (y i - y' i)) with ((g i z - g i c) * (y i - y' i)) by ring.
  rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos|].
  eapply Rle_trans; [apply grad_osc; [exact Hi | exact Hz | exact Hc |]|].
  - intros j Hj. unfold z, upd, path. replace (Nat.eqb j i) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.ltb j i) with false by (symmetry; apply Nat.ltb_ge; lia). apply Hy'c. exact Hj.
  - apply msum_le. intros l Hl. apply Rmult_le_compat_l.
    + eapply Rle_trans; [apply Rabs_pos | apply (HK c Hc i l Hi Hl)].
    + destruct (Nat.eq_dec l i) as [->|Hne].
      * assert (Ez : z i = t) by (unfold z, upd; rewrite Nat.eqb_refl; reflexivity). rewrite Ez.
        rewrite path_k in Ht. rewrite Rmax_comm. apply between_dist. exact Ht.
      * assert (Ez : z l = path y' y i l) by (unfold z, upd; rewrite (proj2 (Nat.eqb_neq l i) Hne); reflexivity).
        rewrite Ez. unfold path. destruct (Nat.ltb l i); [apply Rmax_l | apply Rmax_r].
Qed.

End Taylor.

(** The first-order bound for any function with bounded coordinate
    derivatives on the box. *)
Section Osc1.

Variable n : nat.
Variables lo hi : nat -> R.
Variable G : (nat -> R) -> R.
Variable DG : nat -> (nat -> R) -> R.
Variable KG : nat -> R.

Hypothesis HG : forall y, inbox n lo hi y -> forall l, (l < n)%nat ->
  derivable_pt_lim (fun t => G (upd y l t)) (y l) (DG l y).
Hypothesis HKG : forall y, inbox n lo hi y -> forall l, (l < n)%nat -> Rabs (DG l y) <= KG l.

Theorem osc1 :
  forall y c, inbox n lo hi y -> inbox n lo hi c -> (forall j, (n <= j)%nat -> y j = c j) ->
  Rabs (G y - G c) <= msum (fun l => KG l * Rabs (y l - c l)) n.
Proof.
  intros y c Hy Hc Hyc.
  rewrite <- (path_n n c y Hyc) at 1. rewrite telescope.
  eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros l Hl.
  rewrite path_step.
  destruct (mvt_coord n lo hi DG G (path c y l) l (y l) (fun z Hz => HG z Hz l Hl)
              (path_box n lo hi c y l Hc Hy) Hl (Hy l Hl)) as [t [Ht Et]].
  rewrite Et, path_k, Rabs_mult.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  apply HKG; [| exact Hl]. apply inbox_upd; [apply path_box; assumption | exact Hl |].
  eapply between_box; [| apply Hy; exact Hl | exact Ht]. rewrite path_k. apply Hc. exact Hl.
Qed.

End Osc1.
