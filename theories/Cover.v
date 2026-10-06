(** Cells cover a range, checked rather than asserted.

    Cell.v certifies each cell of a list on its own, so a passing certificate
    proves a conjunction over the cells it happens to carry. That those cells
    leave no gap, and so that their union is an interval rather than a scatter
    of rectangles, is a property of the list and not of any one cell. It was
    an arithmetic argument about the generator that wrote the file. Here it is
    a boolean the checker evaluates, so a certificate claiming to cover a range
    it does not cover is rejected on the same footing as one whose bounds are
    too small.

    A cell is carried as its centre and half-width in mantissa units, which is
    what the certificate stores and what [Cell.in_cell] reads. The check is
    integer arithmetic throughout; reals appear only in the conclusion.

    The condition is a chain: the first cell reaches the start of the range,
    each later cell begins at or before the running frontier, and the frontier
    ends at or past the end of the range. Tracking a frontier rather than a
    remaining interval is what keeps the shared endpoint of two abutting cells
    covered, since that point belongs to both. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.

Import ListNotations.

Open Scope Z_scope.

(** The cells of cs, added to what is already covered up to frontier, reach
    hi. *)
Fixpoint chain (frontier hi : Z) (cs : list (Z * Z)) : bool :=
  match cs with
  | [] => Z.leb hi frontier
  | (c, d) :: tl =>
      Z.leb (c - d) frontier && chain (Z.max frontier (c + d)) hi tl
  end.

(** The cells cover [lo, hi]. *)
Definition covers (lo hi : Z) (cs : list (Z * Z)) : bool :=
  match cs with
  | [] => Z.ltb hi lo
  | (c, d) :: tl => Z.leb (c - d) lo && chain (c + d) hi tl
  end.

(** Anything at or below the frontier is already accounted for; anything above
    it and below hi lies in one of the cells. *)
Lemma chain_correct :
  forall cs frontier hi (M : R),
  chain frontier hi cs = true ->
  (M <= IZR hi)%R ->
  (M <= IZR frontier)%R \/
  exists c d, In (c, d) cs /\ (IZR (c - d) <= M <= IZR (c + d))%R.
Proof.
  induction cs as [|[c d] tl IH]; intros f hi M Hch Hhi; simpl in Hch.
  - apply Z.leb_le in Hch. left.
    apply Rle_trans with (IZR hi). exact Hhi. now apply IZR_le.
  - apply andb_prop in Hch. destruct Hch as [Hreach Hrest].
    apply Z.leb_le in Hreach.
    destruct (IH _ _ M Hrest Hhi) as [Hle|[c' [d' [Hin Hb]]]].
    + (* at or below the new frontier, which is the larger of the two *)
      destruct (Rle_dec M (IZR f)) as [Hf|Hf]. now left.
      apply Rnot_le_lt in Hf.
      (* above the old frontier, so the larger of the two is this cell's end *)
      assert (Hcd : (M <= IZR (c + d))%R).
      { destruct (Z.max_spec f (c + d)) as [[Hlt Heq]|[Hge Heq]];
          rewrite Heq in Hle; [exact Hle | lra]. }
      right. exists c, d. split. now left. split.
      * apply Rle_trans with (IZR f). now apply IZR_le. lra.
      * exact Hcd.
    + right. exists c', d'. split. now right. exact Hb.
Qed.

(** What a passing check means: every real of the range, not merely every
    integer of it, lies in one of the cells. *)
Lemma covers_correct :
  forall cs lo hi (M : R),
  covers lo hi cs = true ->
  (IZR lo <= M <= IZR hi)%R ->
  exists c d, In (c, d) cs /\ (IZR (c - d) <= M <= IZR (c + d))%R.
Proof.
  intros [|[c d] tl] lo hi M Hcov [Hlo Hhi]; unfold covers in Hcov.
  - apply Z.ltb_lt in Hcov.
    assert (lo <= hi) by (apply le_IZR; lra). lia.
  - apply andb_prop in Hcov. destruct Hcov as [Hreach Hrest].
    apply Z.leb_le in Hreach.
    destruct (chain_correct tl (c + d) hi M Hrest Hhi) as [Hle|[c' [d' [Hin Hb]]]].
    + exists c, d. split. now left. split.
      * apply Rle_trans with (IZR lo). now apply IZR_le. exact Hlo.
      * exact Hle.
    + exists c', d'. split. now right. exact Hb.
Qed.

(* ---------------------------------------------------------------- *)
(* Coverings that meet                                               *)

(** The plasma is covered by more than one certificate: the innermost
    interval and the outermost are reconstructed differently from the rest, so
    they are different files. Each carries its own range, and what a reader
    wants is the union. That is a fact about the two lists rather than about
    either, and it is this one: coverings that meet concatenate.

    Walking from a frontier that is further along can only help, which is what
    makes the concatenation work: the first list leaves the frontier at or past
    where the second starts. *)
Lemma chain_mono :
  forall cs f f' hi,
  f <= f' -> chain f hi cs = true -> chain f' hi cs = true.
Proof.
  induction cs as [|[c d] tl IH]; intros f f' hi Hff Hch; simpl in *.
  - apply Z.leb_le in Hch. apply Z.leb_le. lia.
  - apply andb_prop in Hch. destruct Hch as [Hreach Hrest].
    apply Z.leb_le in Hreach.
    apply andb_true_intro. split.
    + apply Z.leb_le. lia.
    + apply (IH (Z.max f (c + d))). lia. exact Hrest.
Qed.

Lemma chain_app :
  forall l1 l2 f m hi,
  chain f m l1 = true -> chain m hi l2 = true ->
  chain f hi (l1 ++ l2) = true.
Proof.
  induction l1 as [|[c d] tl IH]; intros l2 f m hi H1 H2; simpl in *.
  - apply Z.leb_le in H1. apply (chain_mono l2 m f hi). lia. exact H2.
  - apply andb_prop in H1. destruct H1 as [Hreach Hrest].
    apply andb_true_intro. split. exact Hreach.
    apply (IH l2 _ m). exact Hrest. exact H2.
Qed.

(** A covering claims more of the range than it needs to when the range
    shrinks from the left. *)
Lemma covers_lo_mono :
  forall cs lo lo' hi,
  lo <= lo' -> covers lo hi cs = true -> covers lo' hi cs = true.
Proof.
  intros [|[c d] tl] lo lo' hi Hlo Hcov; unfold covers in *.
  - apply Z.ltb_lt in Hcov. apply Z.ltb_lt. lia.
  - apply andb_prop in Hcov. destruct Hcov as [Hreach Hrest].
    apply Z.leb_le in Hreach.
    apply andb_true_intro. split. apply Z.leb_le. lia. exact Hrest.
Qed.

(** Two coverings that meet cover the whole range between them. So the
    certificates of the innermost interval, the body and the outermost one are
    a covering of the plasma, and that is a theorem rather than a remark about
    three files. *)
Theorem covers_app :
  forall l1 l2 a b c,
  covers a b l1 = true -> covers b c l2 = true ->
  covers a c (l1 ++ l2) = true.
Proof.
  intros [|[x d] tl] l2 a b c H1 H2; unfold covers in H1.
  - apply Z.ltb_lt in H1. simpl.
    apply (covers_lo_mono l2 b a c). lia. exact H2.
  - apply andb_prop in H1. destruct H1 as [Hreach Hrest].
    simpl. unfold covers. apply andb_true_intro. split. exact Hreach.
    apply (chain_app tl l2 (x + d) b c). exact Hrest.
    (* the second covering walks from its own first cell, and its frontier
       starts no earlier than b *)
    destruct l2 as [|[y e] tl2]; unfold covers in H2.
    + apply Z.ltb_lt in H2. simpl. apply Z.leb_le. lia.
    + apply andb_prop in H2. destruct H2 as [Hy Hrest2].
      apply Z.leb_le in Hy. simpl.
      apply andb_true_intro. split. apply Z.leb_le. lia.
      apply (chain_mono tl2 (y + e)). lia. exact Hrest2.
Qed.

(* ---------------------------------------------------------------- *)
(* The tiling a generator emits                                      *)

(** Cell i centred at a + (2i+1) d with half-width d. Consecutive cells share
    an endpoint exactly, because the centres and the half-width are integers
    in mantissa units and nothing is rounded between choosing them and writing
    them down. *)
Fixpoint tiling (a d : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => []
  | S k => (a + d, d) :: tiling (a + 2 * d) d k
  end.

Lemma chain_tiling :
  forall n a d f, a <= f ->
  chain f (a + 2 * d * Z.of_nat n) (tiling a d n) = true.
Proof.
  induction n as [|n IH]; intros a d f Haf.
  - cbn [tiling chain]. apply Z.leb_le. simpl Z.of_nat. lia.
  - replace (a + 2 * d * Z.of_nat (S n))
      with ((a + 2 * d) + 2 * d * Z.of_nat n)
      by (rewrite Nat2Z.inj_succ; ring).
    cbn [tiling chain].
    apply andb_true_intro. split.
    + apply Z.leb_le. lia.
    + replace (a + d + d) with (a + 2 * d) by ring.
      apply IH. apply Z.le_max_r.
Qed.

(** So a run of n such cells covers exactly the range it is meant to. *)
Lemma tiling_covers :
  forall n a d, (0 < n)%nat ->
  covers a (a + 2 * d * Z.of_nat n) (tiling a d n) = true.
Proof.
  intros [|n] a d Hn. lia.
  replace (a + 2 * d * Z.of_nat (S n))
    with ((a + 2 * d) + 2 * d * Z.of_nat n)
    by (rewrite Nat2Z.inj_succ; ring).
  cbn [tiling covers].
  apply andb_true_intro. split.
  - apply Z.leb_le. lia.
  - replace (a + d + d) with (a + 2 * d) by ring.
    apply chain_tiling. lia.
Qed.
