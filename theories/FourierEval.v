(** The function a coefficient family carries, and its derivatives.

    [feval u t p] is the sum over Z x Z of a_mn cos(m t + n p) + b_mn sin(m t +
    n p). A bound |u|_0 <= M makes the sum absolutely convergent and at most M
    in absolute value ([feval_bound]). A bound on a strip of positive width
    makes the partial sums converge uniformly together with their derivatives
    in t and in p, and then [dt u] and [dp u] carry the partial derivatives of
    the function [u] carries ([feval_dt], [feval_dp]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum.
Local Open Scope R_scope.

Definition mode (m n : Z) (t p : R) : R := IZR m * t + IZR n * p.

Definition term (u : fser) (t p : R) (m n : Z) : R :=
  fc u m n * cos (mode m n t p) + fs u m n * sin (mode m n t p).

Definition feval (u : fser) (t p : R) : R := zz_sum (term u t p).

Lemma wt_0 (m n : Z) : wt 0 m n = 1.
Proof. unfold wt. rewrite Rmult_0_l. apply exp_0. Qed.

Lemma term_abs (u : fser) (t p : R) (m n : Z) : Rabs (term u t p m n) <= nterm 0 u m n.
Proof.
  unfold term, nterm. rewrite wt_0, Rmult_1_r.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite !Rabs_mult.
  pose proof (COS_bound (mode m n t p)) as Hc. pose proof (SIN_bound (mode m n t p)) as Hs.
  assert (Rabs (cos (mode m n t p)) <= 1) by (apply Rabs_le; lra).
  assert (Rabs (sin (mode m n t p)) <= 1) by (apply Rabs_le; lra).
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)).
  pose proof (Rabs_pos (cos (mode m n t p))). pose proof (Rabs_pos (sin (mode m n t p))).
  nra.
Qed.

(** Partial sums of a family dominated by h move by no more than those of h. *)
Lemma layer_dom (g h : Z -> Z -> R) (N : nat) :
  (forall m n, Rabs (g m n) <= h m n) -> Rabs (layer g N) <= layer h N.
Proof.
  intros H. eapply Rle_trans; [apply layer_abs |].
  unfold layer, absf. cbv zeta.
  apply Rplus_le_compat; [apply Rplus_le_compat |].
  - apply zsum_le. intros n. apply H.
  - apply zsum_le. intros n. apply H.
  - apply zsum_le. intros m. apply Rplus_le_compat; apply H.
Qed.

Lemma sqsum_diff_dom (g h : Z -> Z -> R) (N k : nat) :
  (forall m n, Rabs (g m n) <= h m n) ->
  Rabs (sqsum g (N + k) - sqsum g N) <= sqsum h (N + k) - sqsum h N.
Proof.
  intros H. induction k as [| k IH].
  - rewrite Nat.add_0_r. unfold Rminus. rewrite !Rplus_opp_r, Rabs_R0. lra.
  - replace (N + S k)%nat with (S (N + k)) by lia.
    rewrite !sqsum_S.
    replace (sqsum g (N + k) + layer g (N + k) - sqsum g N)
      with ((sqsum g (N + k) - sqsum g N) + layer g (N + k)) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    pose proof (layer_dom g h (N + k) H). lra.
Qed.

Lemma nterm_absf (u : fser) (m n : Z) : absf (nterm 0 u) m n = nterm 0 u m n.
Proof. unfold absf. apply Rabs_pos_eq, nterm_nonneg. Qed.

Lemma summable_of_nbound (u : fser) (M t p : R) :
  nbound 0 M u -> abs_summable (term u t p) M.
Proof.
  intros H N. eapply Rle_trans; [| apply (H N)].
  apply sqsum_le. intros m n. apply term_abs.
Qed.

Theorem feval_bound (u : fser) (M t p : R) :
  nbound 0 M u -> Rabs (feval u t p) <= M.
Proof. intros H. apply (zz_sum_bound _ M), summable_of_nbound, H. Qed.

(** * Uniform convergence of the partial sums *)

Lemma nbound_cv (u : fser) (M : R) :
  nbound 0 M u -> ex_finite_lim_seq (fun N => sqsum (nterm 0 u) N).
Proof.
  intros H. apply ex_finite_lim_seq_incr with M.
  - intros N. rewrite sqsum_S.
    assert (0 <= layer (nterm 0 u) N).
    { apply Rle_trans with (Rabs (layer (nterm 0 u) N)); [apply Rabs_pos |].
      apply layer_dom. intros m n.
      rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
    lra.
  - exact H.
Qed.

(** |partial sum N - sum| <= (sum of the norm terms) - (their partial sum N). *)
Lemma feval_tail (u : fser) (M t p : R) (N : nat) :
  nbound 0 M u ->
  Rabs (sqsum (term u t p) N - feval u t p)
    <= real (Lim_seq (fun N' => sqsum (nterm 0 u) N')) - sqsum (nterm 0 u) N.
Proof.
  intros H.
  destruct (nbound_cv u M H) as [A HA].
  rewrite (is_lim_seq_unique _ _ HA). simpl.
  pose proof (zz_sum_is_lim (term u t p) M (summable_of_nbound u M t p H)) as HS.
  fold (feval u t p) in HS.
  (* |S_N - S_(N+k)| <= A_(N+k) - A_N, and pass to the limit in k *)
  assert (Hk : forall k, Rabs (sqsum (term u t p) N - sqsum (term u t p) (N + k))
                        <= sqsum (nterm 0 u) (N + k) - sqsum (nterm 0 u) N).
  { intros k. rewrite Rabs_minus_sym. apply sqsum_diff_dom. intros m n. apply term_abs. }
  assert (HSk : is_lim_seq (fun k => sqsum (term u t p) (N + k)) (feval u t p)).
  { apply (is_lim_seq_incr_n (fun N' => sqsum (term u t p) N') N) in HS.
    eapply is_lim_seq_ext; [| exact HS]. intros k. simpl. rewrite Nat.add_comm. reflexivity. }
  assert (HAk : is_lim_seq (fun k => sqsum (nterm 0 u) (N + k)) A).
  { apply (is_lim_seq_incr_n (fun N' => sqsum (nterm 0 u) N') N) in HA.
    eapply is_lim_seq_ext; [| exact HA]. intros k. simpl. rewrite Nat.add_comm. reflexivity. }
  apply (is_lim_seq_le
           (fun k => Rabs (sqsum (term u t p) N - sqsum (term u t p) (N + k)))
           (fun k => sqsum (nterm 0 u) (N + k) - sqsum (nterm 0 u) N)
           (Rabs (sqsum (term u t p) N - feval u t p))
           (A - sqsum (nterm 0 u) N)).
  - exact Hk.
  - apply (is_lim_seq_abs (fun k => sqsum (term u t p) N - sqsum (term u t p) (N + k))
                          (sqsum (term u t p) N - feval u t p)).
    apply is_lim_seq_minus'; [apply is_lim_seq_const | exact HSk].
  - apply is_lim_seq_minus'; [exact HAk | apply is_lim_seq_const].
Qed.

Lemma feval_cvu (u : fser) (M p : R) :
  nbound 0 M u ->
  CVU_dom (fun N t => sqsum (term u t p) N) (fun _ => True).
Proof.
  intros H eps.
  destruct (nbound_cv u M H) as [A HA].
  pose proof HA as HA'.
  apply is_lim_seq_spec in HA'.
  destruct (HA' eps) as [N0 HN0].
  exists N0. intros N HN t _.
  pose proof (feval_tail u M t p N H) as Ht.
  unfold feval, zz_sum in Ht.
  rewrite (is_lim_seq_unique _ _ HA) in Ht. simpl in Ht.
  specialize (HN0 N HN).
  apply Rle_lt_trans with (A - sqsum (nterm 0 u) N); [exact Ht |].
  rewrite Rabs_minus_sym in HN0.
  pose proof (Rle_abs (A - sqsum (nterm 0 u) N)). lra.
Qed.

(** * Derivatives of the partial sums *)

Lemma is_derive_zsum (f : Z -> R -> R) (f' : Z -> R -> R) (x : R) (N : nat) :
  (forall m, is_derive (f m) x (f' m x)) ->
  is_derive (fun y => zsum (fun m => f m y) N) x (zsum (fun m => f' m x) N).
Proof.
  intros H. induction N as [| N IH].
  - rewrite zsum_0. eapply is_derive_ext; [| apply H]. intros y. rewrite zsum_0. reflexivity.
  - eapply is_derive_ext.
    { intros y. rewrite zsum_S. reflexivity. }
    rewrite zsum_S.
    apply (is_derive_plus (fun y => zsum (fun m => f m y) N)
                          (fun y => f (Z.of_nat (S N)) y + f (- Z.of_nat (S N))%Z y)).
    + exact IH.
    + apply (is_derive_plus (f (Z.of_nat (S N))) (f (- Z.of_nat (S N))%Z)); apply H.
Qed.

Lemma is_derive_sqsum (g : Z -> Z -> R -> R) (g' : Z -> Z -> R -> R) (x : R) (N : nat) :
  (forall m n, is_derive (g m n) x (g' m n x)) ->
  is_derive (fun y => sqsum (fun m n => g m n y) N) x (sqsum (fun m n => g' m n x) N).
Proof.
  intros H. unfold sqsum.
  apply (is_derive_zsum (fun m y => zsum (fun n => g m n y) N)
                        (fun m y => zsum (fun n => g' m n y) N)).
  intros m. apply (is_derive_zsum (fun n y => g m n y) (fun n y => g' m n y)). intros n. apply H.
Qed.

Lemma is_derive_term_t (u : fser) (p t : R) (m n : Z) :
  is_derive (fun y => term u y p m n) t (term (dt u) t p m n).
Proof.
  unfold term, mode. simpl.
  auto_derive; [exact I |]. ring.
Qed.

Lemma is_derive_term_p (u : fser) (t p : R) (m n : Z) :
  is_derive (fun y => term u t y m n) p (term (dp u) t p m n).
Proof.
  unfold term, mode. simpl.
  auto_derive; [exact I |]. ring.
Qed.

Lemma continuity_of_derive (f : R -> R) (f' : R -> R) :
  (forall x, is_derive f x (f' x)) ->
  (forall x, ex_derive f' x) -> forall x, continuity_pt (Derive f) x.
Proof.
  intros Hf Hf' x.
  apply continuity_pt_ext with f'.
  { intros y. symmetry. apply is_derive_unique, Hf. }
  apply continuity_pt_filterlim.
  apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
  apply Hf'.
Qed.

(** * The derivatives of the function *)

Theorem feval_dt (rho M : R) (u : fser) (p t : R) :
  0 < rho -> nbound rho M u ->
  is_derive (fun y => feval u y p) t (feval (dt u) t p).
Proof.
  intros Hr H.
  assert (H0 : nbound 0 M u) by (apply (nbound_mono rho); [lra | exact H]).
  assert (Hd : nbound 0 (/ (exp 1 * rho) * M) (dt u)).
  { replace 0 with (rho - rho) by ring. apply nbound_dt; assumption. }
  set (fn := fun N y => sqsum (term u y p) N).
  assert (Hder : forall N y, is_derive (fn N) y (sqsum (term (dt u) y p) N)).
  { intros N y. unfold fn.
    apply (is_derive_sqsum (fun m n y => term u y p m n) (fun m n y => term (dt u) y p m n)).
    intros m n. apply is_derive_term_t. }
  assert (HD : forall N y, Derive (fn N) y = sqsum (term (dt u) y p) N).
  { intros N y. apply is_derive_unique, Hder. }
  pose proof (CVU_Derive fn (fun _ => True) open_true
                ltac:(intros a b _ _ c _; exact I)
                (feval_cvu u M p H0)
                ltac:(intros N y _; eexists; apply Hder)) as HC.
  assert (Hcont : forall N y, True -> continuity_pt (Derive (fn N)) y).
  { intros N y _.
    apply (continuity_of_derive (fn N) (fun y => sqsum (term (dt u) y p) N)).
    - intros z. apply Hder.
    - intros z. eexists.
      apply (is_derive_sqsum (fun m n y => term (dt u) y p m n)
                             (fun m n y => term (dt (dt u)) y p m n)).
      intros m n. apply is_derive_term_t. }
  specialize (HC Hcont).
  assert (Hcvu' : CVU_dom (fun N y => Derive (fn N) y) (fun _ => True)).
  { intros eps. destruct (feval_cvu (dt u) _ p Hd eps) as [N0 HN0].
    exists N0. intros N HN y Hy.
    rewrite (Lim_seq_ext (fun n0 => Derive (fn n0) y) (fun n0 => sqsum (term (dt u) y p) n0))
      by (intros; apply HD).
    rewrite HD. apply HN0; assumption. }
  specialize (HC Hcvu' t I).
  rewrite (Lim_seq_ext (fun n0 => Derive (fn n0) t) (fun n0 => sqsum (term (dt u) t p) n0))
    in HC by (intros; apply HD).
  exact HC.
Qed.

Theorem feval_dp (rho M : R) (u : fser) (t p : R) :
  0 < rho -> nbound rho M u ->
  is_derive (fun y => feval u t y) p (feval (dp u) t p).
Proof.
  intros Hr H.
  assert (H0 : nbound 0 M u) by (apply (nbound_mono rho); [lra | exact H]).
  assert (Hd : nbound 0 (/ (exp 1 * rho) * M) (dp u)).
  { replace 0 with (rho - rho) by ring. apply nbound_dp; assumption. }
  (* the same argument with the roles of t and p exchanged *)
  set (fn := fun N y => sqsum (term u t y) N).
  assert (Hder : forall N y, is_derive (fn N) y (sqsum (term (dp u) t y) N)).
  { intros N y. unfold fn.
    apply (is_derive_sqsum (fun m n y => term u t y m n) (fun m n y => term (dp u) t y m n)).
    intros m n. apply is_derive_term_p. }
  assert (HD : forall N y, Derive (fn N) y = sqsum (term (dp u) t y) N).
  { intros N y. apply is_derive_unique, Hder. }
  assert (Hcvu : forall v K, nbound 0 K v ->
            CVU_dom (fun N y => sqsum (term v t y) N) (fun _ => True)).
  { intros v K Hv eps.
    destruct (nbound_cv v K Hv) as [A HA].
    pose proof HA as HA'. apply is_lim_seq_spec in HA'.
    destruct (HA' eps) as [N0 HN0].
    exists N0. intros N HN y _.
    pose proof (feval_tail v K t y N Hv) as Ht.
    unfold feval, zz_sum in Ht.
    rewrite (is_lim_seq_unique _ _ HA) in Ht. simpl in Ht.
    specialize (HN0 N HN).
    apply Rle_lt_trans with (A - sqsum (nterm 0 v) N); [exact Ht |].
    rewrite Rabs_minus_sym in HN0.
    pose proof (Rle_abs (A - sqsum (nterm 0 v) N)). lra. }
  pose proof (CVU_Derive fn (fun _ => True) open_true
                ltac:(intros a b _ _ c _; exact I)
                (Hcvu u M H0)
                ltac:(intros N y _; eexists; apply Hder)) as HC.
  assert (Hcont : forall N y, True -> continuity_pt (Derive (fn N)) y).
  { intros N y _.
    apply (continuity_of_derive (fn N) (fun y => sqsum (term (dp u) t y) N)).
    - intros z. apply Hder.
    - intros z. eexists.
      apply (is_derive_sqsum (fun m n y => term (dp u) t y m n)
                             (fun m n y => term (dp (dp u)) t y m n)).
      intros m n. apply is_derive_term_p. }
  specialize (HC Hcont).
  assert (Hcvu' : CVU_dom (fun N y => Derive (fn N) y) (fun _ => True)).
  { intros eps. destruct (Hcvu (dp u) _ Hd eps) as [N0 HN0].
    exists N0. intros N HN y Hy.
    rewrite (Lim_seq_ext (fun n0 => Derive (fn n0) y) (fun n0 => sqsum (term (dp u) t y) n0))
      by (intros; apply HD).
    rewrite HD. apply HN0; assumption. }
  specialize (HC Hcvu' p I).
  rewrite (Lim_seq_ext (fun n0 => Derive (fn n0) p) (fun n0 => sqsum (term (dp u) t p) n0))
    in HC by (intros; apply HD).
  exact HC.
Qed.
