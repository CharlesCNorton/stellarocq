(** The contraction mapping theorem for a distance that reads finitely many
    coordinates.

    [pseudo_fixed_point]: Kantorovich's iteration without its hypothesis
    d x y = 0 -> x = y gives a point of the ball at distance zero from its
    image. [coords_complete]: a distance on families of vectors that bounds,
    and is bounded by, the coordinates of a finite list makes the closed
    ball complete; the limit is taken coordinate by coordinate. *)

From Coq Require Import Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Mat Kantorovich.

Local Open Scope R_scope.

Section Pseudo.

Variable X : Type.
Variable d : X -> X -> R.
Hypothesis d_nonneg : forall x y, 0 <= d x y.
Hypothesis d_refl : forall x, d x x = 0.
Hypothesis d_sym : forall x y, d x y = d y x.
Hypothesis d_tri : forall x y z, d x z <= d x y + d y z.
Variable G : X -> X.
Variable x0 : X.
Variables k r : R.
Hypothesis Hk0 : 0 <= k.
Hypothesis Hk1 : k < 1.
Hypothesis Hr : 0 <= r.
Hypothesis Hcontract : forall x y, d x0 x <= r -> d x0 y <= r -> d (G x) (G y) <= k * d x y.
Hypothesis Hsmall : d x0 (G x0) <= (1 - k) * r.
Hypothesis Hcomplete :
  forall u : nat -> X,
  (forall n, d x0 (u n) <= r) ->
  (forall eps, 0 < eps -> exists N, forall m n, (N <= m)%nat -> (N <= n)%nat -> d (u m) (u n) < eps) ->
  exists x, d x0 x <= r /\ forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> d x (u n) < eps.

Theorem pseudo_fixed_point : exists x, d x0 x <= r /\ d (G x) x = 0.
Proof.
  destruct (Hcomplete (iter X G x0) (iter_in_ball X d d_refl d_tri G x0 k r Hk0 Hr Hcontract Hsmall)
              (iter_cauchy X d d_nonneg d_refl d_sym d_tri G x0 k r Hk0 Hk1 Hr Hcontract Hsmall)) as [x [Hx Hlim]].
  exists x. split; [exact Hx|].
  assert (Hall : forall eps, 0 < eps -> d (G x) x < eps).
  { intros eps Heps.
    set (e2 := eps / 2 / (k + 1)).
    assert (He2 : 0 < e2) by (unfold e2; apply Rdiv_lt_0_compat; lra).
    destruct (Hlim e2 He2) as [N1 H1].
    destruct (Hlim (eps / 2) ltac:(lra)) as [N2 H2].
    set (n := Nat.max N1 N2).
    assert (Hn1 : (N1 <= n)%nat) by (unfold n; lia).
    assert (Hn2 : (N2 <= S n)%nat) by (unfold n; lia).
    apply Rle_lt_trans with (d (G x) (G (iter X G x0 n)) + d (G (iter X G x0 n)) x); [apply d_tri|].
    assert (Hc : d (G x) (G (iter X G x0 n)) <= k * d x (iter X G x0 n)).
    { apply Hcontract; [exact Hx | apply (iter_in_ball X d d_refl d_tri G x0 k r Hk0 Hr Hcontract Hsmall)]. }
    assert (Hx1 : d x (iter X G x0 n) < e2) by (apply H1; lia).
    assert (Hx2 : d x (iter X G x0 (S n)) < eps / 2) by (apply H2; lia).
    change (G (iter X G x0 n)) with (iter X G x0 (S n)) in *.
    rewrite (d_sym (iter X G x0 (S n)) x).
    assert (Hke2 : k * d x (iter X G x0 n) <= k * e2) by (apply Rmult_le_compat_l; lra).
    assert (He2b : k * e2 < eps / 2).
    { unfold e2. apply Rlt_le_trans with ((k + 1) * (eps / 2 / (k + 1))).
      - apply Rmult_lt_compat_r; [exact He2 | lra].
      - right. field. lra. }
    lra. }
  destruct (Rle_lt_or_eq_dec 0 (d (G x) x) (d_nonneg _ _)) as [Hlt|Heq].
  - exfalso. specialize (Hall (d (G x) x) Hlt). lra.
  - now symmetry.
Qed.

End Pseudo.

Section Coords.

(** The coordinates the distance reads, and two constants comparing it with them. *)
Variable L : list (nat * nat).
Variable d : (nat -> vec) -> (nat -> vec) -> R.
Variables A B : R.
Hypothesis HA0 : 0 <= A.
Hypothesis HB0 : 0 <= B.
Hypothesis HA : forall x y p, In p L -> Rabs (x (fst p) (snd p) - y (fst p) (snd p)) <= A * d x y.
Hypothesis HB : forall x y e, 0 <= e ->
  (forall p, In p L -> Rabs (x (fst p) (snd p) - y (fst p) (snd p)) <= e) -> d x y <= B * e.
Hypothesis d_sym : forall x y, d x y = d y x.
Hypothesis d_tri : forall x y z, d x z <= d x y + d y z.

Definition lim_of (u : nat -> nat -> vec) : nat -> vec := fun j c => real (Lim_seq (fun n => u n j c)).

Lemma coord_lim :
  forall u : nat -> nat -> vec,
  (forall eps, 0 < eps -> exists N, forall m n, (N <= m)%nat -> (N <= n)%nat -> d (u m) (u n) < eps) ->
  forall p, In p L -> is_lim_seq (fun n => u n (fst p) (snd p)) (lim_of u (fst p) (snd p)).
Proof.
  intros u Hc p Hp. unfold lim_of. apply Lim_seq_correct'.
  apply ex_lim_seq_cauchy_corr. intros eps.
  destruct (Hc (eps / (A + 1)) ltac:(apply Rdiv_lt_0_compat; [apply cond_pos | lra])) as [N HN].
  exists N. intros n m Hn Hm.
  eapply Rle_lt_trans; [apply (HA (u n) (u m) p Hp)|].
  assert (H := HN n m Hn Hm). assert (He : 0 < eps) by apply cond_pos.
  destruct (Rle_lt_dec (d (u n) (u m)) 0) as [Hle|Hlt].
  - assert (A * d (u n) (u m) <= 0) by nra. lra.
  - apply Rle_lt_trans with ((A + 1) * d (u n) (u m)); [nra|].
    apply Rlt_le_trans with ((A + 1) * (eps / (A + 1))); [apply Rmult_lt_compat_l; lra | right; field; lra].
Qed.

(** A finite family of convergent sequences is close together after one N. *)
Lemma lims_uniform :
  forall (u : nat -> nat -> vec) (x : nat -> vec) e, 0 < e ->
  (forall p, In p L -> is_lim_seq (fun n => u n (fst p) (snd p)) (x (fst p) (snd p))) ->
  exists N, forall n, (N <= n)%nat -> forall p, In p L -> Rabs (x (fst p) (snd p) - u n (fst p) (snd p)) <= e.
Proof.
  intros u x e He Hl.
  assert (Gen : forall L', (forall p, In p L' -> In p L) ->
            exists N, forall n, (N <= n)%nat -> forall p, In p L' -> Rabs (x (fst p) (snd p) - u n (fst p) (snd p)) <= e).
  { induction L' as [|a L' IH]; intros Hsub.
    - exists 0%nat. intros n _ p Hp. destruct Hp.
    - destruct (IH (fun p Hp => Hsub p (or_intror Hp))) as [N1 HN1].
      assert (Ha := Hl a (Hsub a (or_introl eq_refl))).
      assert (Ha' := proj1 (is_lim_seq_Reals _ _) Ha). destruct (Ha' e He) as [N2 HN2].
      exists (Nat.max N1 N2). intros n Hn p [<-|Hp].
      + assert (H := HN2 n ltac:(lia)). unfold R_dist in H. rewrite Rabs_minus_sym. lra.
      + apply HN1; [lia | exact Hp]. }
  exact (Gen L (fun p Hp => Hp)).
Qed.

Theorem coords_complete :
  forall (x0 : nat -> vec) r (u : nat -> nat -> vec),
  (forall n, d x0 (u n) <= r) ->
  (forall eps, 0 < eps -> exists N, forall m n, (N <= m)%nat -> (N <= n)%nat -> d (u m) (u n) < eps) ->
  exists x, d x0 x <= r /\ forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> d x (u n) < eps.
Proof.
  intros x0 r u Hball Hc.
  assert (Hl := coord_lim u Hc).
  assert (Hconv : forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> d (lim_of u) (u n) < eps).
  { intros eps Heps.
    destruct (lims_uniform u (lim_of u) (eps / (B + 1)) ltac:(apply Rdiv_lt_0_compat; lra) Hl) as [N HN].
    exists N. intros n Hn.
    eapply Rle_lt_trans; [apply (HB (lim_of u) (u n) (eps / (B + 1))); [left; apply Rdiv_lt_0_compat; lra | exact (HN n Hn)]|].
    apply Rlt_le_trans with ((B + 1) * (eps / (B + 1))).
    - apply Rmult_lt_compat_r; [apply Rdiv_lt_0_compat; lra | lra].
    - right. field. lra. }
  exists (lim_of u). split; [| exact Hconv].
  apply Rnot_lt_le. intros Hgt.
  destruct (Hconv (d x0 (lim_of u) - r) ltac:(lra)) as [N HN].
  assert (H1 := d_tri x0 (u N) (lim_of u)). assert (H2 := Hball N). assert (H3 := HN N (le_n N)).
  rewrite d_sym in H3. lra.
Qed.

End Coords.
