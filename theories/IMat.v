(** Interval matrices.

    An interval matrix is a list of rows of CoqInterval intervals, and
    [icont m n A M] says that every entry of the real m x n matrix M lies in
    the corresponding entry of A. An entry outside the lists reads as the
    interval of everything, so no statement here needs the lists to have a
    shape. The operations are the entrywise sum and difference, the product
    ([imm_correct]), the identity and dyadic point matrices, and three
    checks: an upper bound on the infinity norm ([inorm_le_correct]), an
    upper bound on the logarithmic norm of Mat.v ([ilognorm_le_correct]), and
    the inverse of a matrix from an approximate inverse R, which exists, is
    two-sided, and lies within theta ||R|| / (1 - theta) of R in norm
    ([iinverse_correct]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat.

Import ListNotations.
Local Open Scope R_scope.

Definition imat : Type := list (list I.type).

Definition iget (A : imat) (i j : nat) : I.type := nth j (nth i A []) I.nai.

Definition icont (m n : nat) (A : imat) (M : mat) : Prop :=
  forall i j, (i < m)%nat -> (j < n)%nat -> contains (I.convert (iget A i j)) (Xreal (M i j)).

Lemma msum_sumn : forall f n, msum f n = sumn f n.
Proof. intros f n. induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma isum_msum :
  forall prec (fi : nat -> I.type) (fr : nat -> R) n,
  (forall k, (k < n)%nat -> contains (I.convert (fi k)) (Xreal (fr k))) ->
  contains (I.convert (isum prec (map fi (seq 0 n)))) (Xreal (msum fr n)).
Proof. intros prec fi fr n H. rewrite msum_sumn. apply isum_seq_correct. exact H. Qed.

Lemma nth_map_seq_lt :
  forall {A : Type} (f : nat -> A) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; exact Hk).
  rewrite seq_nth by exact Hk. reflexivity.
Qed.

(** A matrix given by a function of its indices, tabulated. *)
Definition itab (m n : nat) (f : nat -> nat -> I.type) : imat :=
  map (fun i => map (fun j => f i j) (seq 0 n)) (seq 0 m).

Lemma iget_itab :
  forall m n f i j, (i < m)%nat -> (j < n)%nat -> iget (itab m n f) i j = f i j.
Proof.
  intros m n f i j Hi Hj. unfold iget, itab.
  rewrite (nth_map_seq_lt _ m i [] Hi). apply nth_map_seq_lt. exact Hj.
Qed.

Lemma itab_correct :
  forall m n f (M : mat),
  (forall i j, (i < m)%nat -> (j < n)%nat -> contains (I.convert (f i j)) (Xreal (M i j))) ->
  icont m n (itab m n f) M.
Proof. intros m n f M H i j Hi Hj. rewrite iget_itab by assumption. apply H; assumption. Qed.

(* ---------------------------------------------------------------- *)
(* Sums, differences, products                                       *)

Definition iadd (prec : F.precision) (m n : nat) (A B : imat) : imat :=
  itab m n (fun i j => I.add prec (iget A i j) (iget B i j)).
Definition isub (prec : F.precision) (m n : nat) (A B : imat) : imat :=
  itab m n (fun i j => I.sub prec (iget A i j) (iget B i j)).
Definition imm (prec : F.precision) (m n p : nat) (A B : imat) : imat :=
  itab m p (fun i k => isum prec (map (fun j => I.mul prec (iget A i j) (iget B j k)) (seq 0 n))).

Lemma iadd_correct :
  forall prec m n A B M N, icont m n A M -> icont m n B N -> icont m n (iadd prec m n A B) (madd M N).
Proof.
  intros prec m n A B M N HA HB. apply itab_correct. intros i j Hi Hj.
  exact (I.add_correct prec _ _ (Xreal (M i j)) (Xreal (N i j)) (HA i j Hi Hj) (HB i j Hi Hj)).
Qed.

Lemma isub_correct :
  forall prec m n A B M N, icont m n A M -> icont m n B N -> icont m n (isub prec m n A B) (msub M N).
Proof.
  intros prec m n A B M N HA HB. apply itab_correct. intros i j Hi Hj.
  exact (I.sub_correct prec _ _ (Xreal (M i j)) (Xreal (N i j)) (HA i j Hi Hj) (HB i j Hi Hj)).
Qed.

Lemma imm_correct :
  forall prec m n p A B M N,
  icont m n A M -> icont n p B N -> icont m p (imm prec m n p A B) (mm n M N).
Proof.
  intros prec m n p A B M N HA HB. apply itab_correct. intros i k Hi Hk. unfold mm.
  apply isum_msum. intros j Hj.
  exact (I.mul_correct prec _ _ (Xreal (M i j)) (Xreal (N j k)) (HA i j Hi Hj) (HB j k Hj Hk)).
Qed.

(** The identity, exactly. *)
Definition iI (prec : F.precision) (n : nat) : imat :=
  itab n n (fun i j => I.fromZ prec (if Nat.eqb i j then 1%Z else 0%Z)).

Lemma iI_correct : forall prec n, icont n n (iI prec n) mI.
Proof.
  intros prec n. apply itab_correct. intros i j Hi Hj. unfold mI.
  destruct (Nat.eqb i j); apply I.fromZ_correct.
Qed.

(** A matrix of dyadic numbers m 2^e, enclosed, and its real value. *)
Definition dentry (D : list (list (Z * Z))) (i j : nat) : Z * Z := nth j (nth i D []) (0%Z, 0%Z).
Definition idmat (prec : F.precision) (m n : nat) (D : list (list (Z * Z))) : imat :=
  itab m n (fun i j => dyad prec (dentry D i j)).
Definition dmatR (D : list (list (Z * Z))) : mat := fun i j => dyadR (dentry D i j).

Lemma idmat_correct : forall prec m n D, icont m n (idmat prec m n D) (dmatR D).
Proof. intros prec m n D. apply itab_correct. intros i j _ _. apply dyad_correct. Qed.

(* ---------------------------------------------------------------- *)
(* Norm bounds                                                       *)

(** The sum of the moduli of row i. *)
Definition irowsum (prec : F.precision) (n : nat) (A : imat) (i : nat) : I.type :=
  isum prec (map (fun j => I.abs (iget A i j)) (seq 0 n)).

Lemma irowsum_correct :
  forall prec m n A M i, icont m n A M -> (i < m)%nat ->
  contains (I.convert (irowsum prec n A i)) (Xreal (mrow n M i)).
Proof.
  intros prec m n A M i HA Hi. unfold irowsum, mrow. apply isum_msum. intros j Hj.
  rewrite <- Xabs_real. apply I.abs_correct. apply HA; assumption.
Qed.

(** Every row sum below b. *)
Definition inorm_le (prec : F.precision) (m n : nat) (A : imat) (b : I.type) : bool :=
  forallb (fun i => nonneg (I.sub prec b (irowsum prec n A i))) (seq 0 m).

Lemma inorm_le_rows :
  forall prec m n A M b beta, icont m n A M -> contains (I.convert b) (Xreal beta) ->
  inorm_le prec m n A b = true -> forall i, (i < m)%nat -> mrow n M i <= beta.
Proof.
  intros prec m n A M b beta HA Hb Hc i Hi. unfold inorm_le in Hc. rewrite forallb_forall in Hc.
  specialize (Hc i (in_seq_lt _ _ Hi)).
  assert (H := I.sub_correct prec _ _ _ _ Hb (irowsum_correct prec m n A M i HA Hi)).
  destruct (nonneg_correct _ _ H Hc) as [d [Hd Hge]]. cbn in Hd. injection Hd as Hd. lra.
Qed.

Theorem inorm_le_correct :
  forall prec m n A M b beta, (0 < m)%nat -> icont m n A M -> contains (I.convert b) (Xreal beta) ->
  inorm_le prec m n A b = true -> mnorm m n M <= beta.
Proof.
  intros prec m n A M b beta Hm HA Hb Hc.
  assert (Hrows := inorm_le_rows prec m n A M b beta HA Hb Hc).
  assert (H0 : 0 <= beta).
  { eapply Rle_trans; [| apply (Hrows 0%nat Hm)]. unfold mrow. apply msum_nonneg. intros; apply Rabs_pos. }
  apply fmax_le; [exact H0|]. exact Hrows.
Qed.

(** The diagonal entry plus the moduli off the diagonal, row i. *)
Definition ilogrow (prec : F.precision) (n : nat) (A : imat) (i : nat) : I.type :=
  I.add prec (iget A i i)
    (isum prec (map (fun j => if Nat.eqb j i then I.zero else I.abs (iget A i j)) (seq 0 n))).

Definition ilognorm_le (prec : F.precision) (n : nat) (A : imat) (b : I.type) : bool :=
  nonneg b && forallb (fun i => nonneg (I.sub prec b (ilogrow prec n A i))) (seq 0 n).

Theorem ilognorm_le_correct :
  forall prec n A M b beta, icont n n A M -> contains (I.convert b) (Xreal beta) ->
  ilognorm_le prec n A b = true -> lognorm n M <= beta.
Proof.
  intros prec n A M b beta HA Hb Hc. unfold ilognorm_le in Hc. apply andb_true_iff in Hc.
  destruct Hc as [H0 Hc]. rewrite forallb_forall in Hc.
  destruct (nonneg_correct _ _ Hb H0) as [d [Hd Hge]]. injection Hd as <-.
  apply fmax_le; [exact Hge|]. intros i Hi.
  specialize (Hc i (in_seq_lt _ _ Hi)).
  assert (Hrow : contains (I.convert (ilogrow prec n A i))
                   (Xreal (M i i + msum (fun j => if Nat.eqb j i then 0 else Rabs (M i j)) n))).
  { unfold ilogrow. apply (I.add_correct prec _ _ (Xreal (M i i)) (Xreal _)); [apply HA; assumption|].
    apply isum_msum. intros j Hj. destruct (Nat.eqb j i).
    - rewrite I.zero_correct. cbn. lra.
    - rewrite <- Xabs_real. apply I.abs_correct. apply HA; assumption. }
  assert (H := I.sub_correct prec _ _ _ _ Hb Hrow).
  destruct (nonneg_correct _ _ H Hc) as [e [He Hge']]. cbn in He. injection He as He. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Inverses from approximate inverses                                *)

(** ||X - R|| <= ||X|| ||I - M R|| for a left inverse X of M. *)
Lemma inverse_near :
  forall n (M R X : mat),
  (forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j) ->
  mnorm n n (msub X R) <= mnorm n n X * mnorm n n (msub mI (mm n M R)).
Proof.
  intros n M R X HX.
  assert (E : forall i j, (i < n)%nat -> (j < n)%nat ->
              msub X R i j = mm n X (msub mI (mm n M R)) i j).
  { intros i j Hi Hj. unfold msub at 2. unfold mm at 1.
    rewrite (msum_ext _ (fun l => X i l * mI l j - X i l * mm n M R l j)) by (intros; ring).
    rewrite msum_minus. fold (mm n X mI i j). fold (mm n X (mm n M R) i j).
    rewrite mm_mI_r by exact Hj. rewrite <- mm_assoc.
    rewrite (mm_ext n (mm n X M) mI R R i j) by (intros l Hl; first [reflexivity | apply HX; assumption]).
    rewrite mm_mI_l by exact Hi. unfold msub. reflexivity. }
  eapply Rle_trans; [| apply mnorm_mm].
  apply fmax_mono. intros i Hi. unfold mrow. apply msum_le. intros j Hj. rewrite E by assumption. lra.
Qed.

(** The check: the rows of I - R M and of I - M R sum below theta, and theta
    is below one; M is enclosed by MI and R is the dyadic matrix D. *)
Definition iinverse_ok (prec : F.precision) (n : nat) (MI : imat) (D : list (list (Z * Z)))
    (th : I.type) : bool :=
  let RI := idmat prec n n D in
  inorm_le prec n n (isub prec n n (iI prec n) (imm prec n n n RI MI)) th &&
  inorm_le prec n n (isub prec n n (iI prec n) (imm prec n n n MI RI)) th &&
  nonneg (I.sub prec (I.fromZ prec 1) th) && negb (nonneg (I.sub prec th (I.fromZ prec 1))).

Theorem iinverse_correct :
  forall prec n MI D th M theta,
  (0 < n)%nat -> icont n n MI M -> contains (I.convert th) (Xreal theta) ->
  iinverse_ok prec n MI D th = true -> theta < 1 ->
  exists X : mat,
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j) /\
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n M X i j = mI i j) /\
    mnorm n n X <= mnorm n n (dmatR D) / (1 - theta) /\
    mnorm n n (msub X (dmatR D)) <= mnorm n n (dmatR D) / (1 - theta) * theta.
Proof.
  intros prec n MI D th M theta Hn HM Hth Hc Hlt.
  unfold iinverse_ok in Hc. cbv zeta in Hc.
  apply andb_true_iff in Hc. destruct Hc as [Hc _].
  apply andb_true_iff in Hc. destruct Hc as [Hc _].
  apply andb_true_iff in Hc. destruct Hc as [HL HR].
  set (R := dmatR D).
  assert (HRI := idmat_correct prec n n D).
  assert (HL' : mnorm n n (msub mI (mm n R M)) <= theta).
  { refine (inorm_le_correct prec n n _ _ th theta Hn _ Hth HL).
    apply isub_correct; [apply iI_correct | apply imm_correct; assumption]. }
  assert (HR' : mnorm n n (msub mI (mm n M R)) <= theta).
  { refine (inorm_le_correct prec n n _ _ th theta Hn _ Hth HR).
    apply isub_correct; [apply iI_correct | apply imm_correct; assumption]. }
  destruct (approx_inverse n M R theta HL' HR' Hlt) as [X [HX1 [HX2 HX3]]].
  exists X. split; [exact HX1|]. split; [exact HX2|]. split; [exact HX3|].
  eapply Rle_trans; [apply (inverse_near n M R X HX1)|].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact HX3 | exact HR'].
Qed.

(** An entry of a matrix is at most its norm in modulus. *)
Lemma entry_le_mnorm :
  forall m n (A : mat) i j, (i < m)%nat -> (j < n)%nat -> Rabs (A i j) <= mnorm m n A.
Proof.
  intros m n A i j Hi Hj. eapply Rle_trans; [| apply (mrow_le_mnorm m n A i Hi)].
  unfold mrow. apply (msum_ge (fun j => Rabs (A i j)) n j); [intros; apply Rabs_pos | exact Hj].
Qed.

(** The ball of radius r about a matrix, as an interval matrix. *)
Definition iball (prec : F.precision) (m n : nat) (C : imat) (r : I.type) : imat :=
  itab m n (fun i j => I.add prec (iget C i j) (I.join (I.neg r) r)).

Lemma abs_le_both : forall x a, Rabs x <= a -> - a <= x <= a.
Proof.
  intros x a H. assert (H1 := Rle_abs x).
  assert (H2 : - x <= Rabs x) by (rewrite <- Rabs_Ropp; apply Rle_abs). lra.
Qed.

(** The interval from -r to r holds every real of modulus at most rho. *)
Lemma isym_correct :
  forall r rho x, contains (I.convert r) (Xreal rho) -> Rabs x <= rho ->
  contains (I.convert (I.join (I.neg r) r)) (Xreal x).
Proof.
  intros r rho x Hr Hx. apply abs_le_both in Hx.
  apply (contains_connected (I.convert (I.join (I.neg r) r)) (- rho) rho).
  - apply I.join_correct. left. exact (I.neg_correct r (Xreal rho) Hr).
  - apply I.join_correct. right. exact Hr.
  - exact Hx.
Qed.

Lemma iball_correct :
  forall prec m n C r (Cm X : mat) rho,
  icont m n C Cm -> contains (I.convert r) (Xreal rho) -> mnorm m n (msub X Cm) <= rho ->
  icont m n (iball prec m n C r) X.
Proof.
  intros prec m n C r Cm X rho HC Hr Hn. apply itab_correct. intros i j Hi Hj.
  replace (X i j) with (Cm i j + (X i j - Cm i j)) by ring.
  apply (I.add_correct prec _ _ (Xreal (Cm i j)) (Xreal (X i j - Cm i j))); [apply HC; assumption|].
  apply (isym_correct r rho); [exact Hr|].
  eapply Rle_trans; [exact (entry_le_mnorm m n (msub X Cm) i j Hi Hj) | exact Hn].
Qed.
