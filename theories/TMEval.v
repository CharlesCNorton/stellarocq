(** Taylor models in two variables, and the evaluation of binding lists in
    them.

    A cell is a box of points s = sc + u, h = hc + w with u in U and w in W. A
    Taylor model of degree d is a polynomial in u and w of total degree at most
    d, with interval coefficients, and an interval remainder; it holds a real
    x at the point (u, w) when x is the polynomial at some choice of the
    coefficients in their intervals plus some element of the remainder
    ([tm_has]). Sums, scalings and products act on the coefficients; the pairs
    of coefficients that meet in each monomial of degree at most d of a
    product are tabulated once ([mktab]), and the terms of higher degree go to
    the remainder as the products A_i B_j, i + j > d, of enclosures of the
    homogeneous parts of the two factors over the cell. A reciprocal is the
    geometric series in q = x / b0 - 1 about a point b0 of the constant term,
    with the exact tail (-q)^(d+1) / (1 + q); a square root is two Newton
    steps y' = (y + x / y) / 2 from sqrt b0, whose error after each step is
    exactly (y - sqrt x)^2 / (2 y). [tmextend] evaluates a binding list in
    these models, and [tmextend_correct] states that every slot holds, at
    every point of the cell, the value the list gives it there. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Mat IMat.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Sums over lists                                                   *)

Definition lsum {A : Type} (g : A -> R) (L : list A) : R := fold_right (fun x acc => g x + acc) 0 L.

Lemma lsum_nil : forall A (g : A -> R), lsum g [] = 0.
Proof. reflexivity. Qed.

Lemma lsum_cons : forall A (g : A -> R) x L, lsum g (x :: L) = g x + lsum g L.
Proof. reflexivity. Qed.

Lemma lsum_app : forall A (g : A -> R) L1 L2, lsum g (L1 ++ L2) = lsum g L1 + lsum g L2.
Proof.
  intros A g L1 L2. induction L1 as [|x L1 IH]; cbn [app]; [rewrite lsum_nil; ring|].
  rewrite !lsum_cons, IH. ring.
Qed.

Lemma lsum_ext : forall A (g h : A -> R) L, (forall x, In x L -> g x = h x) -> lsum g L = lsum h L.
Proof.
  intros A g h L H. induction L as [|x L IH]; [reflexivity|]. rewrite !lsum_cons.
  rewrite H by (left; reflexivity). rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma lsum_scal : forall A c (g : A -> R) L, lsum (fun x => c * g x) L = c * lsum g L.
Proof. intros A c g L. induction L as [|x L IH]; [simpl; ring|]. rewrite !lsum_cons, IH. ring. Qed.

Lemma lsum_scal_r : forall A c (g : A -> R) L, lsum (fun x => g x * c) L = lsum g L * c.
Proof. intros A c g L. induction L as [|x L IH]; [simpl; ring|]. rewrite !lsum_cons, IH. ring. Qed.

Lemma lsum_plus : forall A (g h : A -> R) L, lsum (fun x => g x + h x) L = lsum g L + lsum h L.
Proof. intros A g h L. induction L as [|x L IH]; [simpl; ring|]. rewrite !lsum_cons, IH. ring. Qed.

Lemma lsum_zero : forall A (L : list A), lsum (fun _ => 0) L = 0.
Proof. intros A L. induction L as [|x L IH]; [reflexivity|]. rewrite lsum_cons, IH. ring. Qed.

Lemma lsum_map : forall A B (f : A -> B) (g : B -> R) L, lsum g (map f L) = lsum (fun x => g (f x)) L.
Proof. intros A B f g L. induction L as [|x L IH]; [reflexivity|]. simpl map. rewrite !lsum_cons, IH. reflexivity. Qed.

Lemma lsum_flat_map :
  forall A B (f : A -> list B) (g : B -> R) L, lsum g (flat_map f L) = lsum (fun x => lsum g (f x)) L.
Proof.
  intros A B f g L. induction L as [|x L IH]; [reflexivity|]. simpl flat_map. rewrite lsum_app, lsum_cons, IH.
  reflexivity.
Qed.

Lemma lsum_seq : forall (g : nat -> R) n, lsum g (seq 0 n) = msum g n.
Proof.
  intros g n. induction n as [|n IH]; [reflexivity|]. rewrite seq_S, lsum_app, IH. simpl. unfold lsum. simpl. ring.
Qed.

Lemma lsum_prod_gen :
  forall A B (g : A * B -> R) L1 L2,
  lsum g (list_prod L1 L2) = lsum (fun i => lsum (fun j => g (i, j)) L2) L1.
Proof.
  intros A B g L1 L2. induction L1 as [|x L1 IH]; [reflexivity|].
  cbn [list_prod]. rewrite lsum_app, lsum_cons, IH, lsum_map. reflexivity.
Qed.

Lemma lsum_prod :
  forall (g : nat * nat -> R) n m,
  lsum g (list_prod (seq 0 n) (seq 0 m)) = msum (fun i => msum (fun j => g (i, j)) m) n.
Proof.
  intros g n m. rewrite lsum_prod_gen, <- lsum_seq. apply lsum_ext. intros i _.
  rewrite <- lsum_seq. reflexivity.
Qed.

(** Exactly one element of a duplicate-free list carries c. *)
Lemma lsum_single_nat :
  forall (T : list nat) k c, NoDup T -> In k T -> lsum (fun t => if Nat.eqb k t then c else 0) T = c.
Proof.
  intros T k c Hnd. induction Hnd as [|t T Hnin Hnd IH]; intros Hin; [destruct Hin|].
  rewrite lsum_cons. destruct (Nat.eqb_spec k t) as [->|Hne].
  - rewrite (lsum_ext _ _ (fun _ => 0)); [rewrite lsum_zero; ring|].
    intros x Hx. destruct (Nat.eqb_spec t x) as [->|]; [contradiction | reflexivity].
  - destruct Hin as [->|Hin]; [contradiction|]. rewrite IH by exact Hin. ring.
Qed.

(** A sum regrouped by a key that takes values in a duplicate-free list. *)
Lemma lsum_partition :
  forall (A : Type) (key : A -> nat) (g : A -> R) (L : list A) (T : list nat),
  NoDup T -> (forall x, In x L -> In (key x) T) ->
  lsum g L = lsum (fun t => lsum g (filter (fun x => Nat.eqb (key x) t) L)) T.
Proof.
  intros A key g L T Hnd. induction L as [|x L IH]; intros Hk.
  - rewrite lsum_nil. symmetry.
    rewrite (lsum_ext _ (fun t => lsum g (filter (fun x => Nat.eqb (key x) t) [])) (fun _ => 0) T)
      by (intros; reflexivity).
    apply lsum_zero.
  - rewrite lsum_cons, IH by (intros y Hy; apply Hk; right; exact Hy).
    transitivity (lsum (fun t => (if Nat.eqb (key x) t then g x else 0)
                                 + lsum g (filter (fun y => Nat.eqb (key y) t) L)) T).
    + rewrite lsum_plus. rewrite (lsum_single_nat T (key x) (g x) Hnd (Hk x (or_introl eq_refl))). reflexivity.
    + apply lsum_ext. intros t _. simpl filter. destruct (Nat.eqb (key x) t); rewrite ?lsum_cons; ring.
Qed.

Lemma lsum_filter :
  forall A (p : A -> bool) (g : A -> R) L, lsum g (filter p L) = lsum (fun x => if p x then g x else 0) L.
Proof.
  intros A p g L. induction L as [|x L IH]; [reflexivity|]. cbn [filter]. rewrite lsum_cons.
  destruct (p x); [rewrite lsum_cons, IH; reflexivity | rewrite IH; ring].
Qed.

(** A sum regrouped by a key, the summand reading its own class. *)
Lemma lsum_regroup :
  forall (A : Type) (key : A -> nat) (phi : A -> nat -> R) (L : list A) (T : list nat),
  NoDup T -> (forall x, In x L -> In (key x) T) ->
  lsum (fun x => phi x (key x)) L = lsum (fun t => lsum (fun x => phi x t) (filter (fun x => Nat.eqb (key x) t) L)) T.
Proof.
  intros A key phi L T Hnd Hk. rewrite (lsum_partition A key (fun x => phi x (key x)) L T Hnd Hk).
  apply lsum_ext. intros t _. apply lsum_ext. intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
  apply Nat.eqb_eq in Hx. rewrite Hx. reflexivity.
Qed.

Lemma lsum_swap :
  forall A B (F : A -> B -> R) (L1 : list A) (L2 : list B),
  lsum (fun x => lsum (fun y => F x y) L2) L1 = lsum (fun y => lsum (fun x => F x y) L1) L2.
Proof.
  intros A B F L1 L2. induction L1 as [|x L1 IH].
  - rewrite lsum_nil. symmetry. rewrite (lsum_ext _ _ (fun _ => 0)) by (intros; reflexivity). apply lsum_zero.
  - rewrite lsum_cons, IH. rewrite <- lsum_plus. apply lsum_ext. intros y _. rewrite lsum_cons. reflexivity.
Qed.

Lemma lsum_mult :
  forall A B (f : A -> R) (g : B -> R) L1 L2, lsum f L1 * lsum g L2 = lsum (fun x => lsum (fun y => f x * g y) L2) L1.
Proof.
  intros A B f g L1 L2. rewrite <- lsum_scal_r. apply lsum_ext. intros x _. rewrite lsum_scal. reflexivity.
Qed.

(** Interval sums of a mapped list. *)
Lemma isum_map :
  forall prec A (L : list A) (f : A -> I.type) (g : A -> R),
  (forall x, In x L -> contains (I.convert (f x)) (Xreal (g x))) ->
  contains (I.convert (isum prec (map f L))) (Xreal (lsum g L)).
Proof.
  intros prec A L f g H. induction L as [|x L IH].
  - cbn [map isum]. rewrite lsum_nil, I.zero_correct. cbn. lra.
  - cbn [map isum]. rewrite lsum_cons.
    apply (I.add_correct prec _ _ (Xreal (g x)) (Xreal (lsum g L))).
    + apply H. left. reflexivity.
    + apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* ---------------------------------------------------------------- *)
(* Monomials and the product table                                   *)

(** The monomials u^i w^j of total degree at most d. *)
Definition mons (d : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq 0 (S d - i))) (seq 0 (S d)).

Definition madd2 (a b : nat * nat) : nat * nat := (fst a + fst b, snd a + snd b)%nat.
Definition meqb (a b : nat * nat) : bool := Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Lemma meqb_eq : forall a b, meqb a b = true -> a = b.
Proof.
  intros [a1 a2] [b1 b2] H. unfold meqb in H. cbn in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. subst. reflexivity.
Qed.

Fixpoint findi (m : nat * nat) (L : list (nat * nat)) (i : nat) : option nat :=
  match L with
  | [] => None
  | x :: L' => if meqb x m then Some i else findi m L' (S i)
  end.

Lemma findi_spec :
  forall m L i t, findi m L i = Some t -> (i <= t)%nat /\ (t - i < length L)%nat /\ nth (t - i) L (0%nat, 0%nat) = m.
Proof.
  intros m L. induction L as [|x L IH]; intros i t H; [discriminate|].
  simpl in H. destruct (meqb x m) eqn:Hx.
  - injection H as <-. rewrite Nat.sub_diag. split; [lia|]. split; [simpl; lia|]. simpl. exact (meqb_eq _ _ Hx).
  - destruct (IH (S i) t H) as [H1 [H2 H3]]. split; [lia|].
    replace (t - i)%nat with (S (t - S i)) by lia. split; [simpl; lia|]. exact H3.
Qed.

Definition allpairs (n : nat) : list (nat * nat) := list_prod (seq 0 n) (seq 0 n).

(** The degree of the monomial of a coefficient index, and the pairs of
    indices whose product has degree at most d. *)
Definition mdeg (d k : nat) : nat := let m := nth k (mons d) (0%nat, 0%nat) in (fst m + snd m)%nat.

Definition lowpairs (d : nat) : list (nat * nat) :=
  filter (fun kk => Nat.leb (mdeg d (fst kk) + mdeg d (snd kk)) d) (allpairs (length (mons d))).

(** The monomial a pair of coefficient indices of the product lands on. *)
Definition tidx (d : nat) (kk : nat * nat) : nat :=
  match findi (madd2 (nth (fst kk) (mons d) (0%nat, 0%nat)) (nth (snd kk) (mons d) (0%nat, 0%nat))) (mons d) 0 with
  | Some t => t
  | None => length (mons d)
  end.

(** For each monomial, the pairs landing on it; for each degree, the
    coefficient indices of that degree. *)
Record tmtab : Type := TMTab { tlow : list (list (nat * nat)); tdeg : list (list nat) }.

Definition mktab (d : nat) : tmtab :=
  let n := length (mons d) in
  TMTab (map (fun t => filter (fun kk => Nat.eqb (tidx d kk) t) (lowpairs d)) (seq 0 n))
        (map (fun i => filter (fun k => Nat.eqb (mdeg d k) i) (seq 0 n)) (seq 0 (S d))).

(** Every low pair lands on a monomial of the list, and every monomial has
    degree at most d. *)
Definition covered (d : nat) : bool :=
  forallb (fun kk => Nat.ltb (tidx d kk) (length (mons d))) (lowpairs d) &&
  forallb (fun k => Nat.leb (mdeg d k) d) (seq 0 (length (mons d))).

Lemma covered3 : covered 3 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* Real polynomials                                                  *)

Definition mval (m : nat * nat) (u w : R) : R := u ^ fst m * w ^ snd m.

Lemma mval_add : forall a b u w, mval (madd2 a b) u w = mval a u w * mval b u w.
Proof. intros [a1 a2] [b1 b2] u w. unfold mval, madd2. cbn. rewrite !pow_add. ring. Qed.

Definition peval (ms : list (nat * nat)) (cs : list R) (u w : R) : R :=
  msum (fun k => nth k cs 0 * mval (nth k ms (0%nat, 0%nat)) u w) (length ms).

Lemma msum_mult : forall f g n, msum f n * msum g n = msum (fun i => msum (fun j => f i * g j) n) n.
Proof.
  intros f g n. rewrite <- msum_scal_r. apply msum_ext. intros i _. rewrite msum_scal. reflexivity.
Qed.

(** The homogeneous part of degree i of a polynomial. *)
Definition hom (d : nat) (cs : list R) (u w : R) (i : nat) : R :=
  lsum (fun k => nth k cs 0 * mval (nth k (mons d) (0%nat, 0%nat)) u w)
       (filter (fun k => Nat.eqb (mdeg d k) i) (seq 0 (length (mons d)))).

Lemma covered_deg : forall d, covered d = true -> forall k, (k < length (mons d))%nat -> (mdeg d k <= d)%nat.
Proof.
  intros d Hc k Hk. unfold covered in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
  rewrite forallb_forall in Hc. apply Nat.leb_le. apply Hc. apply in_seq. lia.
Qed.

Lemma covered_low :
  forall d, covered d = true -> forall kk, In kk (lowpairs d) -> (tidx d kk < length (mons d))%nat.
Proof.
  intros d Hc kk Hk. unfold covered in Hc. apply andb_prop in Hc. destruct Hc as [Hc _].
  rewrite forallb_forall in Hc. apply Nat.ltb_lt. apply Hc. exact Hk.
Qed.

Lemma peval_hom :
  forall d cs u w, covered d = true -> peval (mons d) cs u w = lsum (hom d cs u w) (seq 0 (S d)).
Proof.
  intros d cs u w Hc. unfold peval, hom. rewrite <- lsum_seq.
  apply lsum_partition; [apply seq_NoDup|].
  intros k Hk. apply in_seq in Hk. apply in_seq. assert (H := covered_deg d Hc k ltac:(lia)). lia.
Qed.

(** The degree pairs (i, j) of the product above degree d. *)
Definition hipairs (d : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (filter (fun j => Nat.ltb d (i + j)) (seq 0 (S d)))) (seq 0 (S d)).

Lemma lsum_if_out :
  forall A (c : bool) (F : A -> R) L, (if c then lsum F L else 0) = lsum (fun x => if c then F x else 0) L.
Proof. intros A c F L. destruct c; [reflexivity|]. symmetry. apply lsum_zero. Qed.

(** The product of two polynomials: the monomials of degree at most d with
    the coefficients the table collects, and the products of homogeneous
    parts above degree d. *)
Lemma peval_mul :
  forall d (a b : list R) u w,
  covered d = true ->
  let n := length (mons d) in
  let cf := fun t => lsum (fun kk => nth (fst kk) a 0 * nth (snd kk) b 0)
                          (filter (fun kk => Nat.eqb (tidx d kk) t) (lowpairs d)) in
  peval (mons d) a u w * peval (mons d) b u w
  = msum (fun t => cf t * mval (nth t (mons d) (0%nat, 0%nat)) u w) n
    + lsum (fun ij => hom d a u w (fst ij) * hom d b u w (snd ij)) (hipairs d).
Proof.
  intros d a b u w Hcov n cf.
  set (D := seq 0 (S d)).
  set (mv := fun k => mval (nth k (mons d) (0%nat, 0%nat)) u w).
  set (f := fun k => nth k a 0 * mv k).
  set (g := fun k => nth k b 0 * mv k).
  set (cls := fun i => filter (fun k => Nat.eqb (mdeg d k) i) (seq 0 n)).
  assert (HD : NoDup D) by apply seq_NoDup.
  assert (HkD : forall k, In k (seq 0 n) -> In (mdeg d k) D).
  { intros k Hk. apply in_seq in Hk. apply in_seq. assert (H := covered_deg d Hcov k ltac:(lia)). lia. }
  rewrite !peval_hom by exact Hcov. fold D. rewrite lsum_mult.
  transitivity (lsum (fun i => lsum (fun j => if Nat.leb (i + j) d then hom d a u w i * hom d b u w j else 0) D) D
                + lsum (fun i => lsum (fun j => if Nat.ltb d (i + j) then hom d a u w i * hom d b u w j else 0) D) D).
  { rewrite <- lsum_plus. apply lsum_ext. intros i _. rewrite <- lsum_plus. apply lsum_ext. intros j _.
    destruct (Nat.leb_spec (i + j) d); destruct (Nat.ltb_spec d (i + j)); try lia; ring. }
  f_equal.
  - (* the low part: regroup by degree classes, then by the monomial of the product *)
    transitivity (lsum (fun i => lsum (fun k1 => lsum (fun j => lsum (fun k2 => if Nat.leb (i + j) d then f k1 * g k2 else 0)
                                                                    (cls j)) D) (cls i)) D).
    { apply lsum_ext. intros i _.
      transitivity (lsum (fun j => lsum (fun k1 => lsum (fun k2 => if Nat.leb (i + j) d then f k1 * g k2 else 0) (cls j)) (cls i)) D).
      - apply lsum_ext. intros j _. unfold hom.
        rewrite lsum_mult, lsum_if_out. apply lsum_ext. intros k1 _. rewrite lsum_if_out. reflexivity.
      - apply lsum_swap. }
    transitivity (lsum (fun i => lsum (fun k1 => lsum (fun k2 => if Nat.leb (i + mdeg d k2) d then f k1 * g k2 else 0)
                                                     (seq 0 n)) (cls i)) D).
    { apply lsum_ext. intros i _. apply lsum_ext. intros k1 _. symmetry.
      apply (lsum_regroup nat (mdeg d) (fun k2 j => if Nat.leb (i + j) d then f k1 * g k2 else 0) (seq 0 n) D HD HkD). }
    transitivity (lsum (fun k1 => lsum (fun k2 => if Nat.leb (mdeg d k1 + mdeg d k2) d then f k1 * g k2 else 0)
                                       (seq 0 n)) (seq 0 n)).
    { symmetry. apply (lsum_regroup nat (mdeg d)
                         (fun k1 i => lsum (fun k2 => if Nat.leb (i + mdeg d k2) d then f k1 * g k2 else 0) (seq 0 n))
                         (seq 0 n) D HD HkD). }
    set (F := fun kk : nat * nat => f (fst kk) * g (snd kk)).
    transitivity (lsum F (lowpairs d)).
    { unfold lowpairs, allpairs. fold n. rewrite lsum_filter, lsum_prod_gen. reflexivity. }
    assert (Hk : forall kk, In kk (lowpairs d) -> In (tidx d kk) (seq 0 n)).
    { intros kk Hkk. apply in_seq. assert (H := covered_low d Hcov kk Hkk). fold n in H. lia. }
    rewrite (lsum_partition _ (tidx d) F (lowpairs d) (seq 0 n) (seq_NoDup _ _) Hk).
    rewrite lsum_seq. apply msum_ext. intros t Ht.
    unfold cf. rewrite <- lsum_scal_r. apply lsum_ext. intros kk Hkk.
    apply filter_In in Hkk. destruct Hkk as [_ Hkk]. apply Nat.eqb_eq in Hkk.
    unfold F, f, g, mv. unfold tidx in Hkk.
    destruct (findi _ (mons d) 0) eqn:Hf; [| fold n in Hkk; lia].
    subst. destruct (findi_spec _ _ _ _ Hf) as [_ [_ Hm]]. rewrite Nat.sub_0_r in Hm.
    rewrite Hm, mval_add. ring.
  - (* the high part *)
    unfold hipairs. rewrite lsum_flat_map. apply lsum_ext. intros i _.
    rewrite lsum_map, lsum_filter. reflexivity.
Qed.

Lemma mons_head :
  forall d, mons d = map (fun j => (0%nat, j)) (seq 0 (S d))
                     ++ flat_map (fun i => map (fun j => (i, j)) (seq 0 (S d - i))) (seq 1 d).
Proof. intros d. unfold mons. cbn [seq flat_map]. reflexivity. Qed.

Lemma mons_nth0 : forall d, nth 0 (mons d) (0%nat, 0%nat) = (0%nat, 0%nat).
Proof. intros d. rewrite mons_head. reflexivity. Qed.

Lemma mons_nth1 : forall d, (1 <= d)%nat -> nth 1 (mons d) (0%nat, 0%nat) = (0%nat, 1%nat).
Proof. intros d Hd. destruct d as [|d]; [lia|]. rewrite mons_head. reflexivity. Qed.

Lemma mons_nthSd : forall d, (1 <= d)%nat -> nth (S d) (mons d) (0%nat, 0%nat) = (1%nat, 0%nat).
Proof.
  intros d Hd. rewrite mons_head. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq, Nat.sub_diag. destruct d as [|d]; [lia|]. reflexivity.
Qed.

Lemma mons_length : forall d, (S d <= length (mons d))%nat.
Proof. intros d. rewrite mons_head, length_app, length_map, length_seq. lia. Qed.

(* ---------------------------------------------------------------- *)
(* Taylor models                                                     *)

Section TM.

Variable prec : F.precision.
Variable d : nat.
Variable tab : tmtab.
(** Enclosures over the cell of the monomials of degree at most d. *)
Variable mrlo : list I.type.

Definition nmon : nat := length (mons d).
Definition cget (p : list I.type) (k : nat) : I.type := nth k p I.zero.

Record tm : Type := TM { tpoly : list I.type; trem : I.type }.

Definition ptab' (f : nat -> I.type) : list I.type := map f (seq 0 nmon).

(** Enclosures of the homogeneous parts of degree 0 .. d over the cell, and
    of the whole polynomial. *)
Definition hranges (p : list I.type) : list I.type :=
  map (fun cls => isum prec (map (fun k => I.mul prec (cget p k) (cget mrlo k)) cls)) (tdeg tab).
Definition prange (p : list I.type) : I.type := isum prec (hranges p).
Definition trange (t : tm) : I.type := I.add prec (prange (tpoly t)) (trem t).

Definition one : I.type := I.fromZ prec 1.

Definition tconst (X : I.type) : tm := TM (ptab' (fun k => if Nat.eqb k 0 then X else I.zero)) I.zero.
Definition tvar_u (C : I.type) : tm :=
  TM (ptab' (fun k => if Nat.eqb k 0 then C else if Nat.eqb k (S d) then one else I.zero)) I.zero.
Definition tvar_w (C : I.type) : tm :=
  TM (ptab' (fun k => if Nat.eqb k 0 then C else if Nat.eqb k 1 then one else I.zero)) I.zero.

Definition tadd (a b : tm) : tm :=
  TM (ptab' (fun k => I.add prec (cget (tpoly a) k) (cget (tpoly b) k))) (I.add prec (trem a) (trem b)).
Definition tsub (a b : tm) : tm :=
  TM (ptab' (fun k => I.sub prec (cget (tpoly a) k) (cget (tpoly b) k))) (I.sub prec (trem a) (trem b)).
Definition tneg (a : tm) : tm := TM (ptab' (fun k => I.neg (cget (tpoly a) k))) (I.neg (trem a)).
Definition tscale (X : I.type) (a : tm) : tm :=
  TM (ptab' (fun k => I.mul prec X (cget (tpoly a) k))) (I.mul prec X (trem a)).

(** The sum of the products of the coefficient pairs of a table entry. *)
Definition pconv (pa pb : list I.type) (pl : list (nat * nat)) : I.type :=
  isum prec (map (fun kk => I.mul prec (cget pa (fst kk)) (cget pb (snd kk))) pl).

Definition tmul (a b : tm) : tm :=
  let pa := tpoly a in let pb := tpoly b in
  let ha := hranges pa in let hb := hranges pb in
  TM (map (pconv pa pb) (tlow tab))
     (isum prec [isum prec (map (fun ij => I.mul prec (nth (fst ij) ha I.zero) (nth (snd ij) hb I.zero)) (hipairs d));
                 I.mul prec (trem a) (isum prec hb); I.mul prec (isum prec ha) (trem b);
                 I.mul prec (trem a) (trem b)]).

(** sum_{j <= n} (-q)^j, by Horner. *)
Fixpoint tgeom (q : tm) (n : nat) : tm :=
  match n with O => tconst one | S n' => tsub (tconst one) (tmul q (tgeom q n')) end.

Fixpoint ipow (X : I.type) (n : nat) : I.type :=
  match n with O => one | S n' => I.mul prec X (ipow X n') end.

Definition ipos (X : I.type) : bool := match I.sign_strict X with Xgt => true | _ => false end.
Definition inz (X : I.type) : bool := match I.sign_strict X with Xgt | Xlt => true | _ => false end.

(** A point of the constant term. *)
Definition tmid (a : tm) : I.type := I.singleton (I.midpoint (cget (tpoly a) 0)).

Definition trecip (a : tm) : option tm :=
  let B0 := tmid a in
  let iB0 := I.inv prec B0 in
  let q := tscale iB0 (tsub a (tconst B0)) in
  let Q := trange q in
  let oq := I.add prec one Q in
  if inz B0 && inz oq then
    Some (tscale iB0 (tadd (tgeom q d) (tconst (I.div prec (ipow (I.neg Q) (S d)) oq))))
  else None.

Definition tdiv (a b : tm) : option tm := option_map (tmul a) (trecip b).

Definition two : I.type := I.fromZ prec 2.
Definition half : I.type := I.div prec one two.

(** Two Newton steps for the square root. *)
Definition tsqrt (a : tm) : option tm :=
  let B0 := tmid a in
  let Xr := trange a in
  if ipos Xr && ipos B0 then
    let S0 := I.sqrt prec B0 in
    let E0 := I.sub prec S0 (I.sqrt prec Xr) in
    let y1 := tscale half (tadd (tconst S0) (tmul a (tconst (I.inv prec S0)))) in
    let E1 := I.div prec (I.sqr prec E0) (I.mul prec two S0) in
    match trecip y1 with
    | None => None
    | Some r1 =>
        let y2 := tscale half (tadd y1 (tmul a r1)) in
        let E2 := I.div prec (I.sqr prec E1) (I.mul prec two (trange y1)) in
        Some (tsub y2 (tconst E2))
    end
  else None.

(** A function of one argument, through the range of the model. *)
Definition tfun (f : I.type -> I.type) (a : tm) : tm := tconst (f (trange a)).

Definition otm : Type := option tm.

Definition olift2 (f : tm -> tm -> tm) (a b : otm) : otm :=
  match a, b with Some x, Some y => Some (f x y) | _, _ => None end.

Fixpoint tmeval (tenv : env otm) (e : expr) : otm :=
  match e with
  | Evar n     => eget n tenv None
  | EfromZ z   => Some (tconst (I.fromZ prec z))
  | Epi        => Some (tconst (I.pi prec))
  | Eneg a     => option_map tneg (tmeval tenv a)
  | Eadd a b   => olift2 tadd (tmeval tenv a) (tmeval tenv b)
  | Esub a b   => olift2 tsub (tmeval tenv a) (tmeval tenv b)
  | Emul a b   => olift2 tmul (tmeval tenv a) (tmeval tenv b)
  | Ediv a b   => match tmeval tenv a, tmeval tenv b with
                  | Some x, Some y => tdiv x y
                  | _, _ => None
                  end
  | Esqrt a    => match tmeval tenv a with Some x => tsqrt x | None => None end
  | Esin a     => option_map (tfun (I.sin prec)) (tmeval tenv a)
  | Ecos a     => option_map (tfun (I.cos prec)) (tmeval tenv a)
  | Eexp a     => option_map (tfun (I.exp prec)) (tmeval tenv a)
  | Eatan a    => option_map (tfun (I.atan prec)) (tmeval tenv a)
  | Epow2 z    => Some (tconst (I.power_int prec (I.fromZ prec 2) z))
  end.

Definition tmextend (tenv : env otm) (bs : list binding) : env otm :=
  fold_left (fun e b => eset (fst b) e (tmeval e (snd b))) bs tenv.

(* ---------------------------------------------------------------- *)
(* Soundness at a point of the cell                                  *)

Variables u w : R.
Hypothesis Hlo : forall k, (k < nmon)%nat ->
  contains (I.convert (cget mrlo k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w)).
Hypothesis Htab : tab = mktab d.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.

Definition ccont (p : list I.type) (cs : list R) : Prop :=
  length cs = nmon /\ forall k, (k < nmon)%nat -> contains (I.convert (cget p k)) (Xreal (nth k cs 0)).

Definition tm_has (t : tm) (x : R) : Prop :=
  exists cs r, ccont (tpoly t) cs /\ contains (I.convert (trem t)) (Xreal r) /\
               x = peval (mons d) cs u w + r.

Lemma cget_ptab : forall f k, (k < nmon)%nat -> cget (ptab' f) k = f k.
Proof. intros f k Hk. unfold cget, ptab'. apply nth_map_seq_lt. exact Hk. Qed.

Lemma nth_map_seq0 : forall (f : nat -> R) n k, (k < n)%nat -> nth k (map f (seq 0 n)) 0 = f k.
Proof. intros f n k Hk. apply nth_map_seq_lt. exact Hk. Qed.

Lemma ccont_build :
  forall p (f : nat -> R), (forall k, (k < nmon)%nat -> contains (I.convert (cget p k)) (Xreal (f k))) ->
  ccont p (map f (seq 0 nmon)).
Proof.
  intros p f H. split; [rewrite length_map, length_seq; reflexivity|].
  intros k Hk. rewrite nth_map_seq0 by exact Hk. apply H. exact Hk.
Qed.

Lemma peval_build :
  forall (f : nat -> R), peval (mons d) (map f (seq 0 nmon)) u w
                         = msum (fun k => f k * mval (nth k (mons d) (0%nat, 0%nat)) u w) nmon.
Proof. intros f. unfold peval. apply msum_ext. intros k Hk. rewrite nth_map_seq0 by exact Hk. reflexivity. Qed.

Lemma hranges_eq :
  forall p, hranges p = map (fun i => isum prec (map (fun k => I.mul prec (cget p k) (cget mrlo k))
                                                   (filter (fun k => Nat.eqb (mdeg d k) i) (seq 0 nmon))))
                            (seq 0 (S d)).
Proof. intros p. unfold hranges. rewrite Htab. unfold mktab. cbn [tdeg]. rewrite map_map. reflexivity. Qed.

Lemma hom_contains :
  forall p cs i, ccont p cs ->
  contains (I.convert (isum prec (map (fun k => I.mul prec (cget p k) (cget mrlo k))
                                      (filter (fun k => Nat.eqb (mdeg d k) i) (seq 0 nmon)))))
           (Xreal (hom d cs u w i)).
Proof.
  intros p cs i [Hl Hc]. unfold hom. fold nmon. apply isum_map. intros k Hk.
  apply filter_In in Hk. destruct Hk as [Hk _]. apply in_seq in Hk.
  apply (I.mul_correct prec _ _ (Xreal (nth k cs 0)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w))).
  - apply Hc. lia.
  - apply Hlo. lia.
Qed.

Lemma hranges_correct :
  forall p cs i, ccont p cs -> (i <= d)%nat -> contains (I.convert (nth i (hranges p) I.zero)) (Xreal (hom d cs u w i)).
Proof.
  intros p cs i Hc Hi. rewrite hranges_eq, nth_map_seq_lt by lia. apply hom_contains. exact Hc.
Qed.

Lemma prange_correct : forall p cs, ccont p cs -> contains (I.convert (prange p)) (Xreal (peval (mons d) cs u w)).
Proof.
  intros p cs Hc. unfold prange. rewrite hranges_eq, peval_hom by exact Hcov.
  apply isum_map. intros i _. apply hom_contains. exact Hc.
Qed.

Lemma trange_correct : forall t x, tm_has t x -> contains (I.convert (trange t)) (Xreal x).
Proof.
  intros t x [cs [r [Hc [Hr ->]]]]. unfold trange.
  apply (I.add_correct prec _ _ (Xreal (peval (mons d) cs u w)) (Xreal r)); [apply prange_correct; exact Hc | exact Hr].
Qed.

Lemma zero_contains : contains (I.convert I.zero) (Xreal 0).
Proof. rewrite I.zero_correct. cbn. lra. Qed.

Lemma one_correct : contains (I.convert one) (Xreal 1).
Proof. exact (I.fromZ_correct prec 1). Qed.

Lemma mval00 : forall u' w', mval (0%nat, 0%nat) u' w' = 1.
Proof. intros. unfold mval. cbn. ring. Qed.

Lemma tconst_correct : forall X x, contains (I.convert X) (Xreal x) -> tm_has (tconst X) x.
Proof.
  intros X x Hx. exists (map (fun k => if Nat.eqb k 0 then x else 0) (seq 0 nmon)), 0.
  split; [apply ccont_build; intros k Hk; unfold tconst; cbn [tpoly]; rewrite cget_ptab by exact Hk;
          destruct (Nat.eqb k 0); [exact Hx | exact zero_contains]|].
  split; [exact zero_contains|].
  rewrite peval_build.
  assert (Hn : (0 < nmon)%nat) by (unfold nmon; assert (H := mons_length d); lia).
  rewrite (msum_single _ nmon 0 Hn).
  - cbn [Nat.eqb]. rewrite mons_nth0, mval00. ring.
  - intros k Hk Hk0. destruct (Nat.eqb_spec k 0); [contradiction | ring].
Qed.

Lemma tvar_u_correct : forall C c, contains (I.convert C) (Xreal c) -> tm_has (tvar_u C) (c + u).
Proof.
  intros C c Hc.
  exists (map (fun k => if Nat.eqb k 0 then c else if Nat.eqb k (S d) then 1 else 0) (seq 0 nmon)), 0.
  split.
  { apply ccont_build. intros k Hk. unfold tvar_u. cbn [tpoly]. rewrite cget_ptab by exact Hk.
    destruct (Nat.eqb k 0); [exact Hc|]. destruct (Nat.eqb k (S d)); [exact one_correct | exact zero_contains]. }
  split; [exact zero_contains|].
  rewrite peval_build.
  assert (HS : (S d < nmon)%nat).
  { unfold nmon. rewrite mons_head, length_app, length_map, length_seq.
    destruct d as [|d']; [lia|]. cbn [seq flat_map]. rewrite length_app, length_map, length_seq. lia. }
  rewrite (msum_ext _ (fun k => (if Nat.eqb k 0 then c else 0) + (if Nat.eqb k (S d) then u else 0))).
  - rewrite msum_plus. rewrite (msum_single _ nmon 0 ltac:(lia)), (msum_single _ nmon (S d) HS).
    + rewrite !Nat.eqb_refl. ring.
    + intros k Hk Hne. destruct (Nat.eqb_spec k (S d)); [contradiction | reflexivity].
    + intros k Hk Hne. destruct (Nat.eqb_spec k 0); [contradiction | reflexivity].
  - intros k Hk. destruct (Nat.eqb_spec k 0) as [->|H0].
    + rewrite mons_nth0, mval00. cbn [Nat.eqb]. ring.
    + destruct (Nat.eqb_spec k (S d)) as [->|HS'].
      * rewrite mons_nthSd by exact Hd. unfold mval. cbn. ring.
      * ring.
Qed.

Lemma tvar_w_correct : forall C c, contains (I.convert C) (Xreal c) -> tm_has (tvar_w C) (c + w).
Proof.
  intros C c Hc.
  exists (map (fun k => if Nat.eqb k 0 then c else if Nat.eqb k 1 then 1 else 0) (seq 0 nmon)), 0.
  split.
  { apply ccont_build. intros k Hk. unfold tvar_w. cbn [tpoly]. rewrite cget_ptab by exact Hk.
    destruct (Nat.eqb k 0); [exact Hc|]. destruct (Nat.eqb k 1); [exact one_correct | exact zero_contains]. }
  split; [exact zero_contains|].
  rewrite peval_build.
  assert (H1 : (1 < nmon)%nat) by (unfold nmon; assert (H := mons_length d); lia).
  rewrite (msum_ext _ (fun k => (if Nat.eqb k 0 then c else 0) + (if Nat.eqb k 1 then w else 0))).
  - rewrite msum_plus. rewrite (msum_single _ nmon 0 ltac:(lia)), (msum_single _ nmon 1 H1).
    + cbn [Nat.eqb]. ring.
    + intros k Hk Hne. destruct (Nat.eqb_spec k 1); [contradiction | reflexivity].
    + intros k Hk Hne. destruct (Nat.eqb_spec k 0); [contradiction | reflexivity].
  - intros k Hk. destruct (Nat.eqb_spec k 0) as [->|H0].
    + rewrite mons_nth0, mval00. cbn [Nat.eqb]. ring.
    + destruct (Nat.eqb_spec k 1) as [->|H1'].
      * rewrite mons_nth1 by exact Hd. unfold mval. cbn. ring.
      * ring.
Qed.

(** Linear operations act on the coefficients. *)
Lemma tlin_correct :
  forall (op : I.type -> I.type -> I.type) (rop : R -> R -> R) a b x y,
  (forall X Y p q, contains (I.convert X) (Xreal p) -> contains (I.convert Y) (Xreal q) ->
     contains (I.convert (op X Y)) (Xreal (rop p q))) ->
  (forall p q r s, rop (p + q) (r + s) = rop p r + rop q s) ->
  (forall (f g : nat -> R) n, msum (fun k => rop (f k) (g k)) n = rop (msum f n) (msum g n)) ->
  (forall p q m, rop p q * m = rop (p * m) (q * m)) ->
  tm_has a x -> tm_has b y ->
  tm_has (TM (ptab' (fun k => op (cget (tpoly a) k) (cget (tpoly b) k))) (op (trem a) (trem b))) (rop x y).
Proof.
  intros op rop a b x y Hop Hadd Hsum Hmul [ca [ra [[Hla Hca] [Hra ->]]]] [cb [rb [[Hlb Hcb] [Hrb ->]]]].
  exists (map (fun k => rop (nth k ca 0) (nth k cb 0)) (seq 0 nmon)), (rop ra rb).
  split; [apply ccont_build; intros k Hk; cbn [tpoly]; rewrite cget_ptab by exact Hk; apply Hop;
          [apply Hca | apply Hcb]; exact Hk|].
  split; [apply Hop; assumption|].
  rewrite Hadd. f_equal. rewrite peval_build. unfold peval. fold nmon.
  rewrite <- Hsum. apply msum_ext. intros k _. rewrite Hmul. reflexivity.
Qed.

Lemma tadd_correct : forall a b x y, tm_has a x -> tm_has b y -> tm_has (tadd a b) (x + y).
Proof.
  intros a b x y Ha Hb. unfold tadd.
  apply (tlin_correct (I.add prec) Rplus); try assumption.
  - intros X Y p q Hp Hq. exact (I.add_correct prec _ _ (Xreal p) (Xreal q) Hp Hq).
  - intros; ring.
  - intros f g n. apply msum_plus.
  - intros; ring.
Qed.

Lemma tsub_correct : forall a b x y, tm_has a x -> tm_has b y -> tm_has (tsub a b) (x - y).
Proof.
  intros a b x y Ha Hb. unfold tsub.
  apply (tlin_correct (I.sub prec) Rminus); try assumption.
  - intros X Y p q Hp Hq. exact (I.sub_correct prec _ _ (Xreal p) (Xreal q) Hp Hq).
  - intros; ring.
  - intros f g n. apply msum_minus.
  - intros; ring.
Qed.

Lemma tneg_correct : forall a x, tm_has a x -> tm_has (tneg a) (- x).
Proof.
  intros a x [ca [ra [[Hla Hca] [Hra ->]]]].
  exists (map (fun k => - nth k ca 0) (seq 0 nmon)), (- ra).
  split; [apply ccont_build; intros k Hk; unfold tneg; cbn [tpoly]; rewrite cget_ptab by exact Hk;
          exact (I.neg_correct _ (Xreal (nth k ca 0)) (Hca k Hk))|].
  split; [exact (I.neg_correct _ (Xreal ra) Hra)|].
  rewrite peval_build. unfold peval. fold nmon.
  rewrite (msum_ext (fun k => - nth k ca 0 * mval (nth k (mons d) (0%nat, 0%nat)) u w)
                    (fun k => -1 * (nth k ca 0 * mval (nth k (mons d) (0%nat, 0%nat)) u w))) by (intros; ring).
  rewrite msum_scal. ring.
Qed.

Lemma tscale_correct : forall X c a x, contains (I.convert X) (Xreal c) -> tm_has a x -> tm_has (tscale X a) (c * x).
Proof.
  intros X c a x Hc [ca [ra [[Hla Hca] [Hra ->]]]].
  exists (map (fun k => c * nth k ca 0) (seq 0 nmon)), (c * ra).
  split; [apply ccont_build; intros k Hk; unfold tscale; cbn [tpoly]; rewrite cget_ptab by exact Hk;
          exact (I.mul_correct prec _ _ (Xreal c) (Xreal (nth k ca 0)) Hc (Hca k Hk))|].
  split; [exact (I.mul_correct prec _ _ (Xreal c) (Xreal ra) Hc Hra)|].
  rewrite peval_build. unfold peval. fold nmon.
  rewrite (msum_ext (fun k => c * nth k ca 0 * mval (nth k (mons d) (0%nat, 0%nat)) u w)
                    (fun k => c * (nth k ca 0 * mval (nth k (mons d) (0%nat, 0%nat)) u w))) by (intros; ring).
  rewrite msum_scal. ring.
Qed.

(* Products *)

Lemma nth_map_seq_off :
  forall {A : Type} (f : nat -> A) s m k (dflt : A), (k < m)%nat -> nth k (map f (seq s m)) dflt = f (s + k)%nat.
Proof.
  intros A f s m k dflt Hk. rewrite (nth_indep _ dflt (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

Lemma lsum_seq_shift : forall (g : nat -> R) s m, lsum g (seq s m) = msum (fun k => g (s + k)%nat) m.
Proof.
  intros g s m. induction m as [|m IH]; [reflexivity|].
  rewrite seq_S, lsum_app, IH. cbn [msum]. rewrite lsum_cons, lsum_nil. ring.
Qed.

Lemma in_allpairs : forall n kk, In kk (allpairs n) -> (fst kk < n)%nat /\ (snd kk < n)%nat.
Proof.
  intros n [k1 k2] H. unfold allpairs in H. apply in_prod_iff in H. destruct H as [H1 H2].
  apply in_seq in H1, H2. cbn. lia.
Qed.

Lemma pconv_correct :
  forall pa pb ca cb pl, ccont pa ca -> ccont pb cb -> (forall kk, In kk pl -> In kk (allpairs nmon)) ->
  contains (I.convert (pconv pa pb pl)) (Xreal (lsum (fun kk => nth (fst kk) ca 0 * nth (snd kk) cb 0) pl)).
Proof.
  intros pa pb ca cb pl [_ Ha] [_ Hb] Hpl. unfold pconv. apply isum_map. intros kk Hkk.
  destruct (in_allpairs _ _ (Hpl kk Hkk)) as [H1 H2].
  exact (I.mul_correct prec _ _ (Xreal (nth (fst kk) ca 0)) (Xreal (nth (snd kk) cb 0)) (Ha _ H1) (Hb _ H2)).
Qed.

Lemma hipairs_in : forall ij, In ij (hipairs d) -> (fst ij <= d)%nat /\ (snd ij <= d)%nat.
Proof.
  intros [i j] H. unfold hipairs in H. apply in_flat_map in H. destruct H as [i' [Hi' H]].
  apply in_map_iff in H. destruct H as [j' [He Hj']]. injection He as <- <-.
  apply filter_In in Hj'. destruct Hj' as [Hj' _]. apply in_seq in Hi', Hj'. cbn. lia.
Qed.

Lemma tmul_correct : forall a b x y, tm_has a x -> tm_has b y -> tm_has (tmul a b) (x * y).
Proof.
  intros a b x y [ca [ra [[Hla Hca] [Hra ->]]]] [cb [rb [[Hlb Hcb] [Hrb ->]]]].
  set (n := nmon).
  set (tbl := fun t => filter (fun kk => Nat.eqb (tidx d kk) t) (lowpairs d)).
  set (cf := fun t => lsum (fun kk => nth (fst kk) ca 0 * nth (snd kk) cb 0) (tbl t)).
  set (Hi := lsum (fun ij => hom d ca u w (fst ij) * hom d cb u w (snd ij)) (hipairs d)).
  assert (Hpm : peval (mons d) ca u w * peval (mons d) cb u w
                = msum (fun t => cf t * mval (nth t (mons d) (0%nat, 0%nat)) u w) n + Hi)
    by exact (peval_mul d ca cb u w Hcov).
  set (Pa := peval (mons d) ca u w) in *. set (Pb := peval (mons d) cb u w) in *.
  assert (Htbl : forall t kk, In kk (tbl t) -> In kk (allpairs nmon)).
  { intros t kk Hkk. unfold tbl in Hkk. apply filter_In in Hkk. destruct Hkk as [Hkk _].
    unfold lowpairs in Hkk. apply filter_In in Hkk. exact (proj1 Hkk). }
  assert (Hlow : tlow tab = map tbl (seq 0 n)) by (rewrite Htab; reflexivity).
  assert (Hcc : ccont (tpoly a) ca /\ ccont (tpoly b) cb) by (split; split; assumption).
  destruct Hcc as [Hcca Hccb].
  exists (map cf (seq 0 n)), (Hi + ra * Pb + Pa * rb + ra * rb).
  split; [|split].
  - apply ccont_build. intros k Hk. unfold tmul, cget. cbn [tpoly].
    rewrite Hlow, map_map. rewrite nth_map_seq_lt by exact Hk.
    apply pconv_correct; [exact Hcca | exact Hccb | apply Htbl].
  - unfold tmul. cbn [trem].
    replace (Hi + ra * Pb + Pa * rb + ra * rb) with (fold_right Rplus 0 [Hi; ra * Pb; Pa * rb; ra * rb]) by (cbn; ring).
    apply isum_correct; [reflexivity|]. intros k Hk. cbn [length] in Hk.
    destruct k as [|[|[|[|k]]]]; cbn [nth]; try lia.
    + unfold Hi. apply isum_map. intros ij Hij. destruct (hipairs_in ij Hij) as [Hi1 Hi2].
      apply (I.mul_correct prec _ _ (Xreal (hom d ca u w (fst ij))) (Xreal (hom d cb u w (snd ij)))).
      * apply hranges_correct; assumption.
      * apply hranges_correct; assumption.
    + apply (I.mul_correct prec _ _ (Xreal ra) (Xreal Pb)); [exact Hra|].
      fold (prange (tpoly b)). apply prange_correct. exact Hccb.
    + apply (I.mul_correct prec _ _ (Xreal Pa) (Xreal rb)); [|exact Hrb].
      fold (prange (tpoly a)). apply prange_correct. exact Hcca.
    + exact (I.mul_correct prec _ _ (Xreal ra) (Xreal rb) Hra Hrb).
  - rewrite peval_build. fold n.
    replace ((Pa + ra) * (Pb + rb)) with (Pa * Pb + ra * Pb + Pa * rb + ra * rb) by ring.
    rewrite Hpm. ring.
Qed.

(* The geometric sum and the reciprocal *)

Fixpoint rgeom (q : R) (n : nat) : R := match n with O => 1 | S n' => 1 - q * rgeom q n' end.

Lemma rgeom_id : forall q n, (1 + q) * rgeom q n = 1 - (- q) ^ (S n).
Proof.
  intros q n. induction n as [|n IH]; cbn [rgeom pow]; [ring|].
  replace ((1 + q) * (1 - q * rgeom q n)) with ((1 + q) - q * ((1 + q) * rgeom q n)) by ring.
  rewrite IH. cbn [pow]. ring.
Qed.

Lemma tgeom_correct : forall q x n, tm_has q x -> tm_has (tgeom q n) (rgeom x n).
Proof.
  intros q x n Hq. induction n as [|n IH]; cbn [tgeom rgeom].
  - apply tconst_correct. exact one_correct.
  - apply tsub_correct; [apply tconst_correct; exact one_correct | apply tmul_correct; assumption].
Qed.

Lemma ipow_correct : forall X x n, contains (I.convert X) (Xreal x) -> contains (I.convert (ipow X n)) (Xreal (x ^ n)).
Proof.
  intros X x n Hx. induction n as [|n IH]; cbn [ipow pow]; [exact one_correct|].
  exact (I.mul_correct prec _ _ (Xreal x) (Xreal (x ^ n)) Hx IH).
Qed.

Lemma sign_nz : forall X x, contains (I.convert X) (Xreal x) -> inz X = true -> x <> 0.
Proof.
  intros X x Hx H. unfold inz in H. assert (Hs := I.sign_strict_correct X).
  destruct (I.sign_strict X); try discriminate.
  - destruct (Hs _ Hx) as [_ Hlt]. cbn in Hlt. lra.
  - destruct (Hs _ Hx) as [_ Hgt]. cbn in Hgt. lra.
Qed.

Lemma sign_pos : forall X x, contains (I.convert X) (Xreal x) -> ipos X = true -> 0 < x.
Proof.
  intros X x Hx H. unfold ipos in H. assert (Hs := I.sign_strict_correct X).
  destruct (I.sign_strict X); try discriminate. destruct (Hs _ Hx) as [_ Hgt]. cbn in Hgt. exact Hgt.
Qed.

Lemma inv_contains : forall X x, contains (I.convert X) (Xreal x) -> x <> 0 -> contains (I.convert (I.inv prec X)) (Xreal (/ x)).
Proof.
  intros X x Hx Hnz. assert (H := I.inv_correct prec X (Xreal x) Hx).
  cbn [Xbind] in H. unfold Xinv' in H. destruct (is_zero_spec x) as [Hz|Hz]; [contradiction | exact H].
Qed.

Lemma div_contains :
  forall X Y x y, contains (I.convert X) (Xreal x) -> contains (I.convert Y) (Xreal y) -> y <> 0 ->
  contains (I.convert (I.div prec X Y)) (Xreal (x / y)).
Proof.
  intros X Y x y Hx Hy Hnz. assert (H := I.div_correct prec X Y (Xreal x) (Xreal y) Hx Hy).
  cbn [Xbind2] in H. unfold Xdiv' in H. destruct (is_zero_spec y) as [Hz|Hz]; [contradiction | exact H].
Qed.

Lemma tmid_point : forall a, exists b0, contains (I.convert (tmid a)) (Xreal b0).
Proof.
  intros a. unfold tmid. exists (proj_val (I.convert_bound (I.midpoint (cget (tpoly a) 0)))).
  apply I.singleton_correct.
Qed.

Lemma trecip_correct : forall a x t, tm_has a x -> trecip a = Some t -> x <> 0 /\ tm_has t (/ x).
Proof.
  intros a x t Ha Ht. unfold trecip in Ht.
  destruct (tmid_point a) as [b0 Hb0].
  set (B0 := tmid a) in *. set (iB0 := I.inv prec B0) in *.
  set (qt := tscale iB0 (tsub a (tconst B0))) in *. set (Q := trange qt) in *.
  set (oq := I.add prec one Q) in *.
  destruct (inz B0 && inz oq) eqn:Hc; [|discriminate]. injection Ht as <-.
  apply andb_prop in Hc. destruct Hc as [HB HQ].
  assert (Hb0nz : b0 <> 0) by exact (sign_nz _ _ Hb0 HB).
  assert (HiB : contains (I.convert iB0) (Xreal (/ b0))) by exact (inv_contains _ _ Hb0 Hb0nz).
  set (qv := / b0 * (x - b0)).
  assert (Hq : tm_has qt qv).
  { apply tscale_correct; [exact HiB|]. apply tsub_correct; [exact Ha | apply tconst_correct; exact Hb0]. }
  assert (HQv : contains (I.convert Q) (Xreal qv)) by exact (trange_correct _ _ Hq).
  assert (Hoq : contains (I.convert oq) (Xreal (1 + qv))) by exact (I.add_correct prec _ _ (Xreal 1) (Xreal qv) one_correct HQv).
  assert (Hoqnz : 1 + qv <> 0) by exact (sign_nz _ _ Hoq HQ).
  assert (Hx : x = b0 * (1 + qv)) by (unfold qv; field; exact Hb0nz).
  assert (Hxnz : x <> 0) by (rewrite Hx; apply Rmult_integral_contrapositive; split; assumption).
  split; [exact Hxnz|].
  assert (Hid : / x = / b0 * (rgeom qv d + (- qv) ^ (S d) / (1 + qv))).
  { assert (H := rgeom_id qv d).
    assert (HG : rgeom qv d + (- qv) ^ (S d) / (1 + qv) = / (1 + qv)).
    { apply (Rmult_eq_reg_l (1 + qv)); [|exact Hoqnz].
      rewrite Rmult_plus_distr_l, H. field. exact Hoqnz. }
    rewrite HG, Hx, Rinv_mult. reflexivity. }
  rewrite Hid. apply tscale_correct; [exact HiB|]. apply tadd_correct; [apply tgeom_correct; exact Hq|].
  apply tconst_correct. apply div_contains; [| exact Hoq | exact Hoqnz].
  exact (ipow_correct (I.neg Q) (- qv) (S d) (I.neg_correct _ (Xreal qv) HQv)).
Qed.

(* The square root *)

Lemma sqrt_contains :
  forall X x, contains (I.convert X) (Xreal x) -> 0 <= x -> contains (I.convert (I.sqrt prec X)) (Xreal (sqrt x)).
Proof.
  intros X x Hx Hpos. assert (H := I.sqrt_correct prec X (Xreal x) Hx).
  cbn [Xbind] in H. unfold Xsqrt' in H. destruct (is_negative_spec x) as [Hn|Hn]; [lra | exact H].
Qed.

Lemma sqr_contains : forall X x, contains (I.convert X) (Xreal x) -> contains (I.convert (I.sqr prec X)) (Xreal (x * x)).
Proof. intros X x Hx. exact (I.sqr_correct prec X (Xreal x) Hx). Qed.

Lemma two_correct : contains (I.convert two) (Xreal 2).
Proof. exact (I.fromZ_correct prec 2). Qed.

Lemma half_correct : contains (I.convert half) (Xreal (/ 2)).
Proof.
  unfold half. replace (/ 2) with (1 / 2) by field. apply div_contains; [exact one_correct | exact two_correct | lra].
Qed.

(** One Newton step: y' - sqrt x = (y - sqrt x)^2 / (2 y). *)
Lemma newton_err : forall x y, 0 <= x -> y <> 0 -> / 2 * (y + x * / y) - sqrt x = (y - sqrt x) * (y - sqrt x) / (2 * y).
Proof.
  intros x y Hx Hy.
  replace (x * / y) with (sqrt x * sqrt x * / y) by (rewrite sqrt_sqrt by exact Hx; reflexivity).
  field. exact Hy.
Qed.

Lemma tsqrt_correct : forall a x t, tm_has a x -> tsqrt a = Some t -> 0 < x /\ tm_has t (sqrt x).
Proof.
  intros a x t Ha Ht. unfold tsqrt in Ht.
  destruct (tmid_point a) as [b0 Hb0].
  set (B0 := tmid a) in *. set (Xr := trange a) in *.
  destruct (ipos Xr && ipos B0) eqn:Hc; [|discriminate]. apply andb_prop in Hc. destruct Hc as [HX HB].
  assert (Hxpos : 0 < x) by exact (sign_pos _ _ (trange_correct _ _ Ha) HX).
  assert (Hb0pos : 0 < b0) by exact (sign_pos _ _ Hb0 HB).
  set (y0 := sqrt b0).
  assert (Hy0 : 0 < y0) by (apply sqrt_lt_R0; exact Hb0pos).
  set (S0 := I.sqrt prec B0) in *.
  assert (HS0 : contains (I.convert S0) (Xreal y0)) by (apply sqrt_contains; [exact Hb0 | lra]).
  set (E0 := I.sub prec S0 (I.sqrt prec Xr)) in *.
  assert (HE0 : contains (I.convert E0) (Xreal (y0 - sqrt x))).
  { apply (I.sub_correct prec _ _ (Xreal y0) (Xreal (sqrt x))); [exact HS0|].
    apply sqrt_contains; [exact (trange_correct _ _ Ha) | lra]. }
  set (y1v := / 2 * (y0 + x * / y0)).
  set (y1 := tscale half (tadd (tconst S0) (tmul a (tconst (I.inv prec S0))))) in *.
  assert (Hy1 : tm_has y1 y1v).
  { apply tscale_correct; [exact half_correct|]. apply tadd_correct; [apply tconst_correct; exact HS0|].
    apply tmul_correct; [exact Ha|]. apply tconst_correct. apply inv_contains; [exact HS0 | lra]. }
  set (E1 := I.div prec (I.sqr prec E0) (I.mul prec two S0)) in *.
  assert (HE1 : contains (I.convert E1) (Xreal (y1v - sqrt x))).
  { unfold y1v. rewrite newton_err by lra. apply div_contains; [apply sqr_contains; exact HE0| |lra].
    exact (I.mul_correct prec _ _ (Xreal 2) (Xreal y0) two_correct HS0). }
  destruct (trecip y1) as [r1|] eqn:Hr; [|discriminate]. injection Ht as <-.
  destruct (trecip_correct y1 y1v r1 Hy1 Hr) as [Hy1nz Hr1].
  set (y2v := / 2 * (y1v + x * / y1v)).
  assert (Hy2 : tm_has (tscale half (tadd y1 (tmul a r1))) y2v).
  { apply tscale_correct; [exact half_correct|]. apply tadd_correct; [exact Hy1|]. apply tmul_correct; assumption. }
  assert (HE2 : contains (I.convert (I.div prec (I.sqr prec E1) (I.mul prec two (trange y1)))) (Xreal (y2v - sqrt x))).
  { unfold y2v. rewrite newton_err by lra. apply div_contains; [apply sqr_contains; exact HE1| |lra].
    exact (I.mul_correct prec _ _ (Xreal 2) (Xreal y1v) two_correct (trange_correct _ _ Hy1)). }
  split; [exact Hxpos|].
  replace (sqrt x) with (y2v - (y2v - sqrt x)) by ring.
  apply tsub_correct; [exact Hy2 | apply tconst_correct; exact HE2].
Qed.

(* Evaluation *)

Definition otm_has (o : otm) (v : ExtendedR) : Prop :=
  match o with None => True | Some t => exists x, v = Xreal x /\ tm_has t x end.

Definition tenv_ok (te : env otm) (E : env ExtendedR) : Prop :=
  forall n, otm_has (eget n te None) (eget n E Xnan).

Lemma tfun_correct :
  forall (fi : I.type -> I.type) (fx : ExtendedR -> ExtendedR) (fr : R -> R) a x,
  (forall X v, contains (I.convert X) v -> contains (I.convert (fi X)) (fx v)) ->
  (forall r, fx (Xreal r) = Xreal (fr r)) ->
  tm_has a x -> tm_has (tfun fi a) (fr x).
Proof.
  intros fi fx fr a x Hext Hval Ha. unfold tfun. apply tconst_correct. rewrite <- Hval.
  apply Hext. exact (trange_correct _ _ Ha).
Qed.

Lemma tmeval_correct : forall te E e, tenv_ok te E -> otm_has (tmeval te e) (xeval E e).
Proof.
  intros te E e Hte. induction e; cbn [tmeval xeval].
  - apply Hte.
  - exists (IZR z). split; [reflexivity|]. apply tconst_correct. apply I.fromZ_correct.
  - exists PI. split; [reflexivity|]. apply tconst_correct. apply I.pi_correct.
  - destruct (tmeval te e) as [t|]; [|exact I]. destruct IHe as [x [-> Hx]].
    exists (- x). split; [reflexivity | apply tneg_correct; exact Hx].
  - destruct (tmeval te e1) as [t1|]; [|exact I]. destruct (tmeval te e2) as [t2|]; [|exact I].
    destruct IHe1 as [x [-> Hx]]. destruct IHe2 as [y [-> Hy]].
    exists (x + y). split; [reflexivity | apply tadd_correct; assumption].
  - destruct (tmeval te e1) as [t1|]; [|exact I]. destruct (tmeval te e2) as [t2|]; [|exact I].
    destruct IHe1 as [x [-> Hx]]. destruct IHe2 as [y [-> Hy]].
    exists (x - y). split; [reflexivity | apply tsub_correct; assumption].
  - destruct (tmeval te e1) as [t1|]; [|exact I]. destruct (tmeval te e2) as [t2|]; [|exact I].
    destruct IHe1 as [x [-> Hx]]. destruct IHe2 as [y [-> Hy]].
    exists (x * y). split; [reflexivity | apply tmul_correct; assumption].
  - destruct (tmeval te e1) as [t1|]; [|exact I]. destruct (tmeval te e2) as [t2|]; [|exact I].
    destruct IHe1 as [x [-> Hx]]. destruct IHe2 as [y [-> Hy]].
    unfold tdiv. destruct (trecip t2) as [r|] eqn:Hr; [|exact I]. cbn [option_map].
    destruct (trecip_correct t2 y r Hy Hr) as [Hynz Hry].
    exists (x / y). split.
    + cbn [Xbind2]. unfold Xdiv'. destruct (is_zero_spec y) as [Hz|Hz]; [contradiction | reflexivity].
    + unfold Rdiv. apply tmul_correct; assumption.
  - destruct (tmeval te e) as [t1|]; [|exact I]. destruct IHe as [x [-> Hx]].
    destruct (tsqrt t1) as [t|] eqn:Ht; [|exact I].
    destruct (tsqrt_correct t1 x t Hx Ht) as [Hxpos Hs].
    exists (sqrt x). split; [|exact Hs].
    cbn [Xbind]. unfold Xsqrt'. destruct (is_negative_spec x) as [Hn|Hn]; [lra | reflexivity].
  - destruct (tmeval te e) as [t|]; [|exact I]. destruct IHe as [x [-> Hx]].
    exists (sin x). split; [reflexivity|].
    exact (tfun_correct (I.sin prec) Xsin sin t x (I.sin_correct prec) (fun r => eq_refl) Hx).
  - destruct (tmeval te e) as [t|]; [|exact I]. destruct IHe as [x [-> Hx]].
    exists (cos x). split; [reflexivity|].
    exact (tfun_correct (I.cos prec) Xcos cos t x (I.cos_correct prec) (fun r => eq_refl) Hx).
  - destruct (tmeval te e) as [t|]; [|exact I]. destruct IHe as [x [-> Hx]].
    exists (exp x). split; [reflexivity|].
    exact (tfun_correct (I.exp prec) Xexp exp t x (I.exp_correct prec) (fun r => eq_refl) Hx).
  - destruct (tmeval te e) as [t|]; [|exact I]. destruct IHe as [x [-> Hx]].
    exists (atan x). split; [reflexivity|].
    exact (tfun_correct (I.atan prec) Xatan atan t x (I.atan_correct prec) (fun r => eq_refl) Hx).
  - exists (powerRZ 2 z). split; [reflexivity|]. apply tconst_correct.
    assert (Hc : contains (I.convert (I.fromZ prec 2)) (Xreal (IZR 2))) by apply I.fromZ_correct.
    assert (H := I.power_int_correct prec z _ _ Hc).
    unfold Xpower_int, Xpower_int' in H.
    destruct z as [|q|q]; cbv beta iota delta [Xbind] in H; try exact H.
    revert H. generalize (is_zero_spec 2%R). case (is_zero 2%R).
    + intros Hz0 H. exfalso. inversion Hz0 as [Heq|Hne]. lra.
    + intros Hz0 H. exact H.
Qed.

Lemma tenv_ok_eset :
  forall te E n o v, tenv_ok te E -> otm_has o v -> tenv_ok (eset n te o) (eset n E v).
Proof.
  intros te E n o v Hte Hv k. destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite !eget_eset_eq. exact Hv.
  - rewrite !eget_eset_neq by exact Hne. apply Hte.
Qed.

Theorem tmextend_correct : forall bs te E, tenv_ok te E -> tenv_ok (tmextend te bs) (xextend E bs).
Proof.
  induction bs as [|[n e] bs IH]; intros te E Hte; [exact Hte|].
  cbn [tmextend xextend fold_left]. apply IH. apply tenv_ok_eset; [exact Hte|]. apply tmeval_correct. exact Hte.
Qed.

End TM.
