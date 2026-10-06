(** Matrices over the reals, with the infinity norm.

    Vectors are functions from indices to reals and matrices functions of a
    row and a column index; a dimension is passed wherever a sum or a maximum
    over indices is taken. [mnorm] is the largest row sum of moduli, the norm
    induced by [vnorm], the largest modulus ([mv_bound], [mnorm_mm]).

    One step x |-> (I + h A) x grows the norm by at most 1 + h mu(A), with
    mu(A) the largest diagonal entry plus the moduli of its row off the
    diagonal ([step_up]), and shrinks it by at least 1 - h mu(-A)
    ([step_down]); these are the forward and backward one-step bounds of the
    recursions of the stability argument. [neumann] gives the inverse of
    I - E for ||E|| < 1 as the sum of the powers of E, with ||(I - E)^-1|| at
    most 1 / (1 - ||E||). *)

From Coq Require Import Reals Lra Lia.
From Coquelicot Require Import Coquelicot.

Local Open Scope R_scope.

Definition vec := nat -> R.
Definition mat := nat -> nat -> R.

(* ---------------------------------------------------------------- *)
(* Finite sums and maxima                                            *)

Fixpoint msum (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => msum f k + f k end.

Fixpoint fmax (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => Rmax (fmax f k) (f k) end.

Lemma msum_ext : forall f g n, (forall i, (i < n)%nat -> f i = g i) -> msum f n = msum g n.
Proof.
  intros f g n H. induction n as [|n IH]; simpl; [reflexivity|].
  rewrite IH by (intros i Hi; apply H; lia). rewrite (H n) by lia. reflexivity.
Qed.

Lemma msum_plus : forall f g n, msum (fun i => f i + g i) n = msum f n + msum g n.
Proof. intros f g n. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma msum_minus : forall f g n, msum (fun i => f i - g i) n = msum f n - msum g n.
Proof. intros f g n. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma msum_scal : forall c f n, msum (fun i => c * f i) n = c * msum f n.
Proof. intros c f n. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma msum_scal_r : forall c f n, msum (fun i => f i * c) n = msum f n * c.
Proof. intros c f n. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma msum_zero : forall n, msum (fun _ => 0) n = 0.
Proof. intros n. induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH. ring. Qed.

Lemma msum_le :
  forall f g n, (forall i, (i < n)%nat -> f i <= g i) -> msum f n <= msum g n.
Proof.
  intros f g n H. induction n as [|n IH]; simpl; [lra|].
  assert (H1 := H n ltac:(lia)). assert (H2 : msum f n <= msum g n) by (apply IH; intros; apply H; lia).
  lra.
Qed.

Lemma msum_nonneg : forall f n, (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= msum f n.
Proof.
  intros f n H. rewrite <- (msum_zero n). apply msum_le. exact H.
Qed.

Lemma msum_abs : forall f n, Rabs (msum f n) <= msum (fun i => Rabs (f i)) n.
Proof.
  intros f n. induction n as [|n IH]; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma msum_swap :
  forall (f : nat -> nat -> R) m n,
  msum (fun i => msum (fun j => f i j) n) m = msum (fun j => msum (fun i => f i j) m) n.
Proof.
  intros f m. induction m as [|m IH]; intros n; simpl.
  - symmetry. apply msum_zero.
  - rewrite IH. rewrite <- msum_plus. reflexivity.
Qed.

(** The term at one index, when the others vanish. *)
Lemma msum_single :
  forall f n k, (k < n)%nat -> (forall i, (i < n)%nat -> i <> k -> f i = 0) -> msum f n = f k.
Proof.
  intros f n. induction n as [|n IH]; intros k Hk H; [lia|]. simpl.
  destruct (Nat.eq_dec k n) as [->|Hkn].
  - rewrite (msum_ext f (fun _ => 0)) by (intros i Hi; apply H; lia).
    rewrite msum_zero. ring.
  - rewrite (IH k) by (lia || (intros i Hi Hik; apply H; [lia | exact Hik])).
    rewrite (H n) by lia. ring.
Qed.

Lemma msum_ge :
  forall f n j, (forall i, (i < n)%nat -> 0 <= f i) -> (j < n)%nat -> f j <= msum f n.
Proof.
  intros f n. induction n as [|n IH]; intros j Hf Hj; [lia|]. simpl.
  destruct (Nat.eq_dec j n) as [->|Hjn].
  - assert (0 <= msum f n) by (apply msum_nonneg; intros i Hi; apply Hf; lia). lra.
  - assert (f j <= msum f n) by (apply IH; [intros i Hi; apply Hf; lia | lia]).
    assert (0 <= f n) by (apply Hf; lia). lra.
Qed.

Lemma fmax_nonneg : forall f n, 0 <= fmax f n.
Proof.
  intros f n. induction n as [|n IH]; simpl; [lra|].
  eapply Rle_trans; [exact IH | apply Rmax_l].
Qed.

Lemma fmax_ge : forall f n i, (i < n)%nat -> f i <= fmax f n.
Proof.
  intros f n. induction n as [|n IH]; intros i Hi; [lia|]. simpl.
  destruct (Nat.eq_dec i n) as [->|Hin].
  - apply Rmax_r.
  - eapply Rle_trans; [apply IH; lia | apply Rmax_l].
Qed.

Lemma fmax_le : forall f n c, 0 <= c -> (forall i, (i < n)%nat -> f i <= c) -> fmax f n <= c.
Proof.
  intros f n c Hc H. induction n as [|n IH]; simpl; [exact Hc|].
  apply Rmax_lub; [apply IH; intros; apply H; lia | apply H; lia].
Qed.

Lemma fmax_attained :
  forall f n, (0 < n)%nat -> (forall i, 0 <= f i) -> exists i, (i < n)%nat /\ f i = fmax f n.
Proof.
  intros f n. induction n as [|k IH]; intros Hn Hf; [lia|].
  change (fmax f (S k)) with (Rmax (fmax f k) (f k)).
  destruct k as [|k'].
  - exists 0%nat. split; [lia|]. simpl fmax. rewrite Rmax_right by apply Hf. reflexivity.
  - destruct (IH ltac:(lia) Hf) as [i [Hi Hfi]].
    destruct (Rle_dec (fmax f (S k')) (f (S k'))) as [Hle|Hgt].
    + exists (S k'). split; [lia|]. rewrite Rmax_right by exact Hle. reflexivity.
    + exists i. split; [lia|]. rewrite Rmax_left by lra. exact Hfi.
Qed.

Lemma fmax_mono :
  forall f g n, (forall i, (i < n)%nat -> f i <= g i) -> fmax f n <= fmax g n.
Proof.
  intros f g n H. apply fmax_le; [apply fmax_nonneg|].
  intros i Hi. eapply Rle_trans; [apply H; exact Hi | apply fmax_ge; exact Hi].
Qed.

(* ---------------------------------------------------------------- *)
(* Norms and products                                                *)

Definition vnorm (n : nat) (x : vec) : R := fmax (fun i => Rabs (x i)) n.
Definition mrow (n : nat) (A : mat) (i : nat) : R := msum (fun j => Rabs (A i j)) n.
Definition mnorm (m n : nat) (A : mat) : R := fmax (mrow n A) m.

Definition mv (n : nat) (A : mat) (x : vec) : vec := fun i => msum (fun j => A i j * x j) n.
Definition mm (n : nat) (A B : mat) : mat := fun i k => msum (fun j => A i j * B j k) n.
Definition mI : mat := fun i k => if Nat.eqb i k then 1 else 0.
Definition madd (A B : mat) : mat := fun i k => A i k + B i k.
Definition msub (A B : mat) : mat := fun i k => A i k - B i k.
Definition mscal (c : R) (A : mat) : mat := fun i k => c * A i k.

Lemma vnorm_nonneg : forall n x, 0 <= vnorm n x.
Proof. intros. apply fmax_nonneg. Qed.

Lemma vnorm_ge : forall n x i, (i < n)%nat -> Rabs (x i) <= vnorm n x.
Proof. intros n x i Hi. exact (fmax_ge (fun i => Rabs (x i)) n i Hi). Qed.

Lemma vnorm_le : forall n x c, 0 <= c -> (forall i, (i < n)%nat -> Rabs (x i) <= c) -> vnorm n x <= c.
Proof. intros n x c Hc H. exact (fmax_le _ n c Hc H). Qed.

Lemma mnorm_nonneg : forall m n A, 0 <= mnorm m n A.
Proof. intros. apply fmax_nonneg. Qed.

Lemma mrow_le_mnorm : forall m n A i, (i < m)%nat -> mrow n A i <= mnorm m n A.
Proof. intros m n A i Hi. exact (fmax_ge (mrow n A) m i Hi). Qed.

Lemma mv_bound : forall m n A x, vnorm m (mv n A x) <= mnorm m n A * vnorm n x.
Proof.
  intros m n A x. apply vnorm_le.
  - apply Rmult_le_pos; [apply mnorm_nonneg | apply vnorm_nonneg].
  - intros i Hi. unfold mv. eapply Rle_trans; [apply msum_abs|].
    eapply Rle_trans with (msum (fun j => Rabs (A i j) * vnorm n x) n).
    + apply msum_le. intros j Hj. rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos|].
      apply vnorm_ge. exact Hj.
    + rewrite msum_scal_r. apply Rmult_le_compat_r; [apply vnorm_nonneg|].
      exact (mrow_le_mnorm m n A i Hi).
Qed.

Lemma mv_mm : forall n A B x i, mv n (mm n A B) x i = mv n A (mv n B x) i.
Proof.
  intros n A B x i. unfold mv, mm.
  rewrite (msum_ext (fun j => msum (fun k => A i k * B k j) n * x j)
                    (fun j => msum (fun k => A i k * B k j * x j) n))
    by (intros j Hj; rewrite <- msum_scal_r; reflexivity).
  rewrite msum_swap. apply msum_ext. intros k Hk.
  rewrite <- msum_scal. apply msum_ext. intros j Hj. ring.
Qed.

Lemma mm_assoc : forall n A B C i k, mm n (mm n A B) C i k = mm n A (mm n B C) i k.
Proof.
  intros n A B C i k. unfold mm.
  rewrite (msum_ext (fun j => msum (fun l => A i l * B l j) n * C j k)
                    (fun j => msum (fun l => A i l * B l j * C j k) n))
    by (intros j Hj; rewrite <- msum_scal_r; reflexivity).
  rewrite msum_swap. apply msum_ext. intros l Hl.
  rewrite <- msum_scal. apply msum_ext. intros j Hj. ring.
Qed.

Lemma mnorm_mm : forall m n p A B, mnorm m p (mm n A B) <= mnorm m n A * mnorm n p B.
Proof.
  intros m n p A B. apply fmax_le.
  - apply Rmult_le_pos; apply mnorm_nonneg.
  - intros i Hi. unfold mrow, mm.
    eapply Rle_trans with (msum (fun k => msum (fun j => Rabs (A i j) * Rabs (B j k)) n) p).
    + apply msum_le. intros k Hk. eapply Rle_trans; [apply msum_abs|].
      apply msum_le. intros j Hj. rewrite Rabs_mult. lra.
    + rewrite msum_swap.
      eapply Rle_trans with (msum (fun j => Rabs (A i j) * mnorm n p B) n).
      * apply msum_le. intros j Hj. rewrite msum_scal.
        apply Rmult_le_compat_l; [apply Rabs_pos|]. exact (mrow_le_mnorm n p B j Hj).
      * rewrite msum_scal_r. apply Rmult_le_compat_r; [apply mnorm_nonneg|].
        exact (mrow_le_mnorm m n A i Hi).
Qed.

Lemma mv_mI : forall n x i, (i < n)%nat -> mv n mI x i = x i.
Proof.
  intros n x i Hi. unfold mv, mI.
  rewrite (msum_single _ n i Hi).
  - rewrite Nat.eqb_refl. ring.
  - intros j Hj Hji. destruct (Nat.eqb_spec i j) as [->|]; [lia | ring].
Qed.

Lemma mm_mI_l : forall n A i k, (i < n)%nat -> mm n mI A i k = A i k.
Proof.
  intros n A i k Hi. unfold mm, mI.
  rewrite (msum_single _ n i Hi).
  - rewrite Nat.eqb_refl. ring.
  - intros j Hj Hji. destruct (Nat.eqb_spec i j) as [->|]; [lia | ring].
Qed.

Lemma mm_mI_r : forall n A i k, (k < n)%nat -> mm n A mI i k = A i k.
Proof.
  intros n A i k Hk. unfold mm, mI.
  rewrite (msum_single _ n k Hk).
  - rewrite Nat.eqb_refl. ring.
  - intros j Hj Hjk. destruct (Nat.eqb_spec j k) as [->|]; [lia | ring].
Qed.

(* ---------------------------------------------------------------- *)
(* One step of a recursion                                           *)

(** The logarithmic norm in the infinity norm, clipped below at 0. *)
Definition lognorm (n : nat) (A : mat) : R :=
  fmax (fun i => A i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n) n.

Lemma msum_split_diag :
  forall n (f : nat -> R) i, (i < n)%nat ->
  msum f n = f i + msum (fun j => if Nat.eqb j i then 0 else f j) n.
Proof.
  intros n f i Hi.
  assert (E : msum f n = msum (fun j => (if Nat.eqb j i then f j else 0)
                                       + (if Nat.eqb j i then 0 else f j)) n).
  { apply msum_ext. intros j Hj. destruct (Nat.eqb j i); ring. }
  rewrite E, msum_plus. f_equal.
  rewrite (msum_single (fun j => if Nat.eqb j i then f j else 0) n i Hi).
  - rewrite Nat.eqb_refl. reflexivity.
  - intros j Hj Hji. destruct (Nat.eqb_spec j i); [contradiction | reflexivity].
Qed.

Theorem step_up :
  forall n (A : mat) h x, 0 <= h -> (forall i, (i < n)%nat -> 0 <= 1 + h * A i i) ->
  vnorm n (fun i => x i + h * mv n A x i) <= (1 + h * lognorm n A) * vnorm n x.
Proof.
  intros n A h x Hh Hd. apply vnorm_le.
  - apply Rmult_le_pos; [| apply vnorm_nonneg].
    assert (0 <= lognorm n A) by apply fmax_nonneg. nra.
  - intros i Hi. unfold mv.
    rewrite (msum_split_diag n _ i Hi).
    set (off := msum (fun j => if Nat.eqb j i then 0 else A i j * x j) n).
    replace (x i + h * (A i i * x i + off)) with ((1 + h * A i i) * x i + h * off) by ring.
    assert (Hoff : Rabs off <= msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n * vnorm n x).
    { unfold off. eapply Rle_trans; [apply msum_abs|]. rewrite <- msum_scal_r.
      apply msum_le. intros j Hj. destruct (Nat.eqb j i).
      - rewrite Rabs_R0. lra.
      - rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | apply vnorm_ge; exact Hj]. }
    assert (Hxi := vnorm_ge n x i Hi).
    assert (Hl := fmax_ge (fun i => A i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n)
                          n i Hi).
    fold (lognorm n A) in Hl. cbv beta in Hl.
    assert (Hdi := Hd i Hi).
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_mult, (Rabs_right (1 + h * A i i)) by lra.
    rewrite Rabs_mult, (Rabs_right h) by lra.
    assert (Hn := vnorm_nonneg n x).
    assert (H1 : (1 + h * A i i) * Rabs (x i) <= (1 + h * A i i) * vnorm n x)
      by (apply Rmult_le_compat_l; lra).
    assert (H2 : h * Rabs off <= h * (msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n * vnorm n x))
      by (apply Rmult_le_compat_l; lra).
    assert (H3 : h * (A i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n) * vnorm n x
                 <= h * lognorm n A * vnorm n x).
    { apply Rmult_le_compat_r; [exact Hn|]. apply Rmult_le_compat_l; lra. }
    nra.
Qed.

(** The same as a bound on the matrix I + h A. *)
Theorem mnorm_step :
  forall n (A : mat) h, 0 <= h -> (forall i, (i < n)%nat -> 0 <= 1 + h * A i i) ->
  mnorm n n (fun i j => mI i j + h * A i j) <= 1 + h * lognorm n A.
Proof.
  intros n A h Hh Hd.
  assert (Hl0 : 0 <= lognorm n A) by apply fmax_nonneg.
  apply fmax_le; [nra|]. intros i Hi. unfold mrow.
  rewrite (msum_split_diag n _ i Hi). unfold mI at 1. rewrite Nat.eqb_refl.
  rewrite (msum_ext _ (fun j => if Nat.eqb j i then 0 else h * Rabs (A i j))).
  2: { intros j Hj. destruct (Nat.eqb_spec j i) as [->|Hji]; [reflexivity|].
       unfold mI. replace (Nat.eqb i j) with false by (symmetry; apply Nat.eqb_neq; lia).
       rewrite Rplus_0_l, Rabs_mult, (Rabs_right h) by lra. reflexivity. }
  rewrite Rabs_right by (specialize (Hd i Hi); lra).
  rewrite (msum_ext _ (fun j => h * (if Nat.eqb j i then 0 else Rabs (A i j))))
    by (intros j _; destruct (Nat.eqb j i); ring).
  rewrite msum_scal.
  assert (Hl := fmax_ge (fun i => A i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n) n i Hi).
  fold (lognorm n A) in Hl. cbv beta in Hl.
  assert (h * (A i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) n) <= h * lognorm n A)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** The backward bound: (I + h A) x is at least (1 - h mu(-A)) times x. *)
Theorem step_down :
  forall n (A : mat) h x, 0 <= h ->
  (1 - h * lognorm n (fun i j => - A i j)) * vnorm n x
  <= vnorm n (fun i => x i + h * mv n A x i).
Proof.
  intros n A h x Hh.
  destruct n as [|n].
  - unfold vnorm. simpl. lra.
  - (* the index where x attains its norm *)
    destruct (fmax_attained (fun i => Rabs (x i)) (S n) ltac:(lia) (fun i => Rabs_pos (x i)))
      as [i [Hi Hxi]].
    fold (vnorm (S n) x) in Hxi.
    rewrite <- Hxi.
    eapply Rle_trans; [| apply (vnorm_ge (S n) _ i Hi)].
    unfold mv. rewrite (msum_split_diag (S n) _ i Hi).
    set (off := msum (fun j => if Nat.eqb j i then 0 else A i j * x j) (S n)).
    replace (x i + h * (A i i * x i + off)) with ((1 + h * A i i) * x i + h * off) by ring.
    set (r := msum (fun j => if Nat.eqb j i then 0 else Rabs (A i j)) (S n)).
    assert (Hoff : Rabs off <= r * Rabs (x i)).
    { unfold off, r. rewrite Hxi. eapply Rle_trans; [apply msum_abs|]. rewrite <- msum_scal_r.
      apply msum_le. intros j Hj. destruct (Nat.eqb j i).
      - rewrite Rabs_R0. lra.
      - rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | apply vnorm_ge; exact Hj]. }
    assert (Hl := fmax_ge (fun i => - A i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (- A i j)) (S n))
                          (S n) i Hi).
    fold (lognorm (S n) (fun i j => - A i j)) in Hl. cbv beta in Hl.
    assert (Hr : msum (fun j => if Nat.eqb j i then 0 else Rabs (- A i j)) (S n) = r).
    { unfold r. apply msum_ext. intros j Hj. destruct (Nat.eqb j i); [reflexivity|]. apply Rabs_Ropp. }
    rewrite Hr in Hl.
    set (mu := lognorm (S n) (fun i j => - A i j)) in *.
    (* |(1 + h a) x + h off| >= (1 + h a) |x| - h |off| when 1 + h a >= 0, and >= -(...) otherwise *)
    assert (Hx0 := Rabs_pos (x i)).
    assert (Hmu0 : 0 <= mu) by apply fmax_nonneg.
    destruct (Rle_dec 0 (1 + h * A i i)) as [Hpos|Hneg].
    + assert (Rabs ((1 + h * A i i) * x i + h * off) >= (1 + h * A i i) * Rabs (x i) - h * Rabs off).
      { assert (H1 := Rabs_triang ((1 + h * A i i) * x i + h * off) (- (h * off))).
        replace ((1 + h * A i i) * x i + h * off + - (h * off)) with ((1 + h * A i i) * x i) in H1 by ring.
        rewrite Rabs_mult, (Rabs_right (1 + h * A i i)) in H1 by lra.
        rewrite Rabs_Ropp, Rabs_mult, (Rabs_right h) in H1 by lra. lra. }
      assert (h * Rabs off <= h * (r * Rabs (x i))) by (apply Rmult_le_compat_l; lra).
      assert (h * (- A i i + r) * Rabs (x i) <= h * mu * Rabs (x i)).
      { apply Rmult_le_compat_r; [exact Hx0|]. apply Rmult_le_compat_l; lra. }
      nra.
    + (* 1 + h a < 0: then 1 - h mu < 0 and the bound is trivial *)
      assert (h * (- A i i + r) >= 0 + 1) by (assert (0 <= r) by (unfold r; apply msum_nonneg; intros j Hj; destruct (Nat.eqb j i); [lra | apply Rabs_pos]); nra).
      assert (1 - h * mu <= 0).
      { assert (h * (- A i i + r) <= h * mu) by (apply Rmult_le_compat_l; lra). lra. }
      assert ((1 - h * mu) * Rabs (x i) <= 0) by nra.
      assert (0 <= Rabs ((1 + h * A i i) * x i + h * off)) by apply Rabs_pos. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The inverse of I - E                                              *)

Lemma mm_ext :
  forall n A A' B B' i k,
  (forall l, (l < n)%nat -> A i l = A' i l) -> (forall l, (l < n)%nat -> B l k = B' l k) ->
  mm n A B i k = mm n A' B' i k.
Proof.
  intros n A A' B B' i k HA HB. unfold mm. apply msum_ext. intros l Hl. rewrite HA, HB by exact Hl.
  reflexivity.
Qed.

Lemma ex_series_Rplus (a b : nat -> R) :
  ex_series a -> ex_series b -> ex_series (fun k => a k + b k).
Proof.
  intros Ha Hb.
  apply (@ex_series_ext R_AbsRing R_NormedModule (fun k => @plus R_NormedModule (a k) (b k)));
    [intros; reflexivity|].
  apply (@ex_series_plus R_AbsRing R_NormedModule); assumption.
Qed.

Lemma ex_series_Rmult_l (c : R) (a : nat -> R) : ex_series a -> ex_series (fun k => c * a k).
Proof.
  intros Ha.
  apply (@ex_series_ext R_AbsRing R_NormedModule (fun k => @scal R_AbsRing R_NormedModule c (a k)));
    [intros; reflexivity|].
  apply (@ex_series_scal_l R_AbsRing R_NormedModule); assumption.
Qed.

(** A finite sum of convergent series is the series of the finite sums. *)
Lemma msum_series :
  forall (f : nat -> nat -> R) m, (forall l, (l < m)%nat -> ex_series (f l)) ->
  ex_series (fun k => msum (fun l => f l k) m) /\
  msum (fun l => Series (f l)) m = Series (fun k => msum (fun l => f l k) m).
Proof.
  intros f m. induction m as [|m IH]; intros Hex; simpl.
  - assert (Hg : Rabs (/ 2) < 1) by (rewrite Rabs_right; lra).
    split.
    + apply (@ex_series_le R_AbsRing R_CompleteNormedModule _ (fun k => (/ 2) ^ k));
        [| apply ex_series_geom; exact Hg].
      intros k. change (norm (0 : R)) with (Rabs 0). rewrite Rabs_R0. apply pow_le. lra.
    + symmetry. rewrite (Series_ext (fun _ => 0) (fun _ => 0 * 1)) by (intros; ring).
      rewrite Series_scal_l. ring.
  - destruct (IH (fun l Hl => Hex l ltac:(lia))) as [Hm Em].
    assert (Hl := Hex m ltac:(lia)).
    split.
    + apply ex_series_Rplus; assumption.
    + rewrite Em, Series_plus by assumption. reflexivity.
Qed.

Section Neumann.

Variable n : nat.
Variable E : mat.
Variable th : R.
Hypothesis Hth : mnorm n n E <= th.
Hypothesis Hth1 : th < 1.

Fixpoint mpow (k : nat) : mat :=
  match k with O => mI | S k' => mm n E (mpow k') end.

Lemma th_nonneg : 0 <= th.
Proof. pose proof (mnorm_nonneg n n E). lra. Qed.

Lemma mnorm_mI : mnorm n n mI <= 1.
Proof.
  apply fmax_le; [lra|]. intros i Hi. unfold mrow, mI.
  rewrite (msum_single _ n i Hi).
  - rewrite Nat.eqb_refl, Rabs_R1. lra.
  - intros j Hj Hji. destruct (Nat.eqb_spec i j) as [->|]; [lia | apply Rabs_R0].
Qed.

Lemma mnorm_mpow : forall k, mnorm n n (mpow k) <= th ^ k.
Proof.
  induction k as [|k IH]; simpl.
  - apply mnorm_mI.
  - eapply Rle_trans; [apply mnorm_mm|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hth | exact IH].
Qed.

Lemma mrow_mpow : forall k i, (i < n)%nat -> mrow n (mpow k) i <= th ^ k.
Proof. intros k i Hi. eapply Rle_trans; [apply (mrow_le_mnorm n n _ i Hi) | apply mnorm_mpow]. Qed.

Lemma mpow_entry : forall k i j, (i < n)%nat -> (j < n)%nat -> Rabs (mpow k i j) <= th ^ k.
Proof.
  intros k i j Hi Hj. eapply Rle_trans; [| apply (mrow_mpow k i Hi)].
  unfold mrow. apply (msum_ge (fun j => Rabs (mpow k i j)) n j); [intros; apply Rabs_pos | exact Hj].
Qed.

(** E^(k+1) = E^k E on the indices below n. *)
Lemma mpow_succ_r :
  forall k i j, (i < n)%nat -> (j < n)%nat -> mpow (S k) i j = mm n (mpow k) E i j.
Proof.
  induction k as [|k IH]; intros i j Hi Hj.
  - cbn [mpow]. rewrite mm_mI_r by exact Hj. rewrite mm_mI_l by exact Hi. reflexivity.
  - change (mpow (S (S k)) i j) with (mm n E (mpow (S k)) i j).
    rewrite (mm_ext n E E (mpow (S k)) (mm n (mpow k) E) i j)
      by (intros l Hl; first [reflexivity | apply IH; assumption]).
    rewrite <- mm_assoc. reflexivity.
Qed.

Lemma th_abs : Rabs th < 1.
Proof. rewrite Rabs_right by (pose proof th_nonneg; lra). exact Hth1. Qed.

Lemma ex_mpow : forall i j, (i < n)%nat -> (j < n)%nat -> ex_series (fun k => mpow k i j).
Proof.
  intros i j Hi Hj. apply ex_series_Rabs.
  apply (@ex_series_le R_AbsRing R_CompleteNormedModule _ (fun k => th ^ k));
    [| apply ex_series_geom, th_abs].
  intros k. change (norm (Rabs (mpow k i j))) with (Rabs (Rabs (mpow k i j))).
  rewrite Rabs_Rabsolu. exact (mpow_entry k i j Hi Hj).
Qed.

Definition ninv : mat := fun i j => Series (fun k => mpow k i j).

Lemma mm_E_ninv :
  forall i j, (i < n)%nat -> (j < n)%nat -> mm n E ninv i j = Series (fun k => mpow (S k) i j).
Proof.
  intros i j Hi Hj. unfold mm, ninv.
  rewrite (msum_ext _ (fun l => Series (fun k => E i l * mpow k l j)))
    by (intros l Hl; rewrite Series_scal_l; reflexivity).
  destruct (msum_series (fun l k => E i l * mpow k l j) n) as [_ Es].
  { intros l Hl. apply ex_series_Rmult_l. apply ex_mpow; assumption. }
  rewrite Es. reflexivity.
Qed.

Lemma mm_ninv_E :
  forall i j, (i < n)%nat -> (j < n)%nat -> mm n ninv E i j = Series (fun k => mpow (S k) i j).
Proof.
  intros i j Hi Hj. unfold mm, ninv.
  rewrite (msum_ext _ (fun l => Series (fun k => mpow k i l * E l j)))
    by (intros l Hl; rewrite Series_scal_r; reflexivity).
  destruct (msum_series (fun l k => mpow k i l * E l j) n) as [_ Es].
  { intros l Hl. apply ex_series_scal_r. apply ex_mpow; assumption. }
  rewrite Es. apply Series_ext. intros k. rewrite mpow_succ_r by assumption. reflexivity.
Qed.

(** (I - E) S = I and S (I - E) = I on the indices below n. *)
Theorem neumann_right :
  forall i j, (i < n)%nat -> (j < n)%nat -> ninv i j - mm n E ninv i j = mI i j.
Proof.
  intros i j Hi Hj. rewrite mm_E_ninv by assumption. unfold ninv.
  rewrite (Series_incr_1 (fun k => mpow k i j)) by (apply ex_mpow; assumption).
  cbn [mpow]. ring.
Qed.

Theorem neumann_left :
  forall i j, (i < n)%nat -> (j < n)%nat -> ninv i j - mm n ninv E i j = mI i j.
Proof.
  intros i j Hi Hj. rewrite mm_ninv_E by assumption. unfold ninv.
  rewrite (Series_incr_1 (fun k => mpow k i j)) by (apply ex_mpow; assumption).
  cbn [mpow]. ring.
Qed.

Theorem neumann_norm : mnorm n n ninv <= / (1 - th).
Proof.
  assert (Hpos : 0 < / (1 - th)) by (apply Rinv_0_lt_compat; lra).
  apply fmax_le; [lra|]. intros i Hi. unfold mrow, ninv.
  eapply Rle_trans with (msum (fun j => Series (fun k => Rabs (mpow k i j))) n).
  - apply msum_le. intros j Hj. apply Series_Rabs.
    apply (@ex_series_le R_AbsRing R_CompleteNormedModule _ (fun k => th ^ k));
      [| apply ex_series_geom, th_abs].
    intros k. change (norm (Rabs (mpow k i j))) with (Rabs (Rabs (mpow k i j))).
    rewrite Rabs_Rabsolu. exact (mpow_entry k i j Hi Hj).
  - destruct (msum_series (fun j k => Rabs (mpow k i j)) n) as [Hex Es].
    { intros j Hj.
      apply (@ex_series_le R_AbsRing R_CompleteNormedModule _ (fun k => th ^ k));
        [| apply ex_series_geom, th_abs].
      intros k. change (norm (Rabs (mpow k i j))) with (Rabs (Rabs (mpow k i j))).
      rewrite Rabs_Rabsolu. exact (mpow_entry k i j Hi Hj). }
    rewrite Es. rewrite <- (Series_geom th th_abs).
    apply Series_le; [| apply ex_series_geom, th_abs].
    intros k. split.
    + apply msum_nonneg. intros; apply Rabs_pos.
    + exact (mrow_mpow k i Hi).
Qed.

End Neumann.

(** A matrix with an approximate inverse R on both sides has an inverse,
    within ||R|| / (1 - theta) in norm. *)
Theorem approx_inverse :
  forall n (M R : mat) th,
  mnorm n n (msub mI (mm n R M)) <= th -> mnorm n n (msub mI (mm n M R)) <= th -> th < 1 ->
  exists X : mat,
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j) /\
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n M X i j = mI i j) /\
    mnorm n n X <= mnorm n n R / (1 - th).
Proof.
  intros n M R th HL HR Hth.
  set (EL := msub mI (mm n R M)). set (ER := msub mI (mm n M R)).
  set (SL := ninv n EL). set (SR := ninv n ER).
  (* the left inverse SL R and the right inverse R SR *)
  assert (Left : forall i j, (i < n)%nat -> (j < n)%nat -> mm n (mm n SL R) M i j = mI i j).
  { intros i j Hi Hj. rewrite mm_assoc.
    rewrite (mm_ext n SL SL (mm n R M) (msub mI EL) i j)
      by (intros l Hl; first [reflexivity | unfold EL, msub; ring]).
    unfold mm at 1. unfold msub.
    rewrite (msum_ext _ (fun l => SL i l * mI l j - SL i l * EL l j))
      by (intros l Hl; ring).
    rewrite msum_minus. fold (mm n SL mI i j). fold (mm n SL EL i j).
    rewrite mm_mI_r by exact Hj. apply neumann_left with th; [exact HL | exact Hth | exact Hi | exact Hj]. }
  assert (Right : forall i j, (i < n)%nat -> (j < n)%nat -> mm n M (mm n R SR) i j = mI i j).
  { intros i j Hi Hj. rewrite <- mm_assoc.
    rewrite (mm_ext n (mm n M R) (msub mI ER) SR SR i j)
      by (intros l Hl; first [reflexivity | unfold ER, msub; ring]).
    unfold mm at 1. unfold msub.
    rewrite (msum_ext _ (fun l => mI i l * SR l j - ER i l * SR l j))
      by (intros l Hl; ring).
    rewrite msum_minus. fold (mm n mI SR i j). fold (mm n ER SR i j).
    rewrite mm_mI_l by exact Hi. apply neumann_right with th; [exact HR | exact Hth | exact Hi | exact Hj]. }
  (* the two coincide *)
  assert (Same : forall i j, (i < n)%nat -> (j < n)%nat -> mm n SL R i j = mm n R SR i j).
  { intros i j Hi Hj.
    assert (A1 : mm n (mm n (mm n SL R) M) (mm n R SR) i j = mm n (mm n SL R) (mm n M (mm n R SR)) i j)
      by apply mm_assoc.
    rewrite (mm_ext n (mm n (mm n SL R) M) mI (mm n R SR) (mm n R SR) i j) in A1
      by (intros l Hl; first [reflexivity | apply Left; assumption]).
    rewrite (mm_ext n (mm n SL R) (mm n SL R) (mm n M (mm n R SR)) mI i j) in A1
      by (intros l Hl; first [reflexivity | apply Right; assumption]).
    rewrite mm_mI_l in A1 by exact Hi. rewrite mm_mI_r in A1 by exact Hj. symmetry. exact A1. }
  exists (mm n SL R). split; [exact Left|]. split.
  - intros i j Hi Hj. rewrite (mm_ext n M M (mm n SL R) (mm n R SR) i j)
      by (intros l Hl; first [reflexivity | apply Same; assumption]).
    apply Right; assumption.
  - eapply Rle_trans; [apply mnorm_mm|].
    assert (HS := neumann_norm n EL th HL Hth). assert (HR0 := mnorm_nonneg n n R).
    replace (mnorm n n R / (1 - th)) with (/ (1 - th) * mnorm n n R) by (field; lra).
    apply Rmult_le_compat_r; [exact HR0 | exact HS].
Qed.
