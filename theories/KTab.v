(** Tables of cosines, sines and exponentials from a few enclosed seeds.

    Given enclosures of cos phi and sin phi, repeated rotation encloses
    cos(a + j phi) and sin(a + j phi) for j = 0 .. n - 1 ([powl_ok]); from
    phi = 2 pi / N this lists the cosines and sines at the points of a grid
    of N angles, and a mode k reads its step at k mod N ([step_ok]), so each
    row of cos(k 2 pi a / N) comes from one rotation ([krow_ok]). The
    symmetric tables over the modes of [zrange] reuse each |k| for k and -k
    ([ztab_ok]). Powers of an enclosed exponential list e^(j x) the same way
    ([epow_ok], [zexp_ok]). Everything is over the enclosures of [RI], so a
    table carries the rounding of the recurrence and nothing else. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Stellarocq Require Import KAMScalar FourierDFT KFix KCheckKern KEngine.
Import ListNotations.
Local Open Scope R_scope.

Lemma cos_add_2piz (x : R) (j : Z) : cos (x + 2 * PI * IZR j) = cos x.
Proof. rewrite cos_plus, cos_2piz, sin_2piz. ring. Qed.

Lemma sin_add_2piz (x : R) (j : Z) : sin (x + 2 * PI * IZR j) = sin x.
Proof. rewrite sin_plus, cos_2piz, sin_2piz. ring. Qed.

(** k 2 pi a / N differs from (k mod N) 2 pi a / N by a multiple of 2 pi. *)
Lemma angle_mod (N : nat) (k : Z) (a : nat) : (0 < N)%nat ->
  IZR k * gpt N a = IZR (k mod Z.of_nat N) * gpt N a + 2 * PI * IZR (k / Z.of_nat N * Z.of_nat a).
Proof.
  intros HN. unfold gpt.
  assert (HN' : INR N <> 0) by (apply not_0_INR; lia).
  rewrite (Z_div_mod_eq_full k (Z.of_nat N)) at 1.
  rewrite plus_IZR, !mult_IZR, <- !INR_IZR_INZ. field. exact HN'.
Qed.

Module Tab (J : RI).

Module E := Engine J.
Import E E.KO.

Definition pinR (X : J.t * J.t) (x : R * R) : Prop := inR (fst X) (fst x) /\ inR (snd X) (snd x).

(** One rotation by the step (c, s). *)
Definition rot (st x : J.t * J.t) : J.t * J.t :=
  (J.sub (J.mul (fst x) (fst st)) (J.mul (snd x) (snd st)), J.add (J.mul (snd x) (fst st)) (J.mul (fst x) (snd st))).

Lemma rot_ok (st x : J.t * J.t) (phi a : R) :
  pinR st (cos phi, sin phi) -> pinR x (cos a, sin a) -> pinR (rot st x) (cos (a + phi), sin (a + phi)).
Proof.
  intros [H1 H2] [G1 G2]. cbn [fst snd] in *. unfold pinR, rot. cbn [fst snd].
  rewrite cos_plus, sin_plus. split.
  - apply inR_sub; apply inR_mul; assumption.
  - replace (sin a * cos phi + cos a * sin phi) with (sin a * cos phi + cos a * sin phi) by ring.
    apply inR_add; apply inR_mul; assumption.
Qed.

(** x, x st, x st^2, ... *)
Fixpoint powl (st x : J.t * J.t) (n : nat) : list (J.t * J.t) :=
  match n with O => [] | S n' => x :: powl st (rot st x) n' end.

Theorem powl_ok (st x : J.t * J.t) (phi a : R) (n : nat) :
  pinR st (cos phi, sin phi) -> pinR x (cos a, sin a) ->
  Forall2 pinR (powl st x n) (map (fun j => (cos (a + INR j * phi), sin (a + INR j * phi))) (seq 0 n)).
Proof.
  intros Hs. revert x a. induction n as [| n IH]; intros x a Hx; [constructor |].
  cbn [powl seq map]. constructor.
  - rewrite Rmult_0_l, Rplus_0_r. exact Hx.
  - rewrite <- seq_shift, map_map.
    replace (map (fun j => (cos (a + INR (S j) * phi), sin (a + INR (S j) * phi))) (seq 0 n))
      with (map (fun j => (cos ((a + phi) + INR j * phi), sin ((a + phi) + INR j * phi))) (seq 0 n)).
    + apply IH. apply rot_ok; assumption.
    + apply map_ext. intros j. rewrite S_INR. f_equal; f_equal; ring.
Qed.

Definition one2 : J.t * J.t := (J.of_q 1 0, J.zero).

Lemma one2_ok : pinR one2 (cos 0, sin 0).
Proof. rewrite cos_0, sin_0. split; [apply inR_Z | apply inR_zero]. Qed.

(** The base table of a grid of N angles from enclosures of cos(2 pi / N) and
    sin(2 pi / N). *)
Definition base (seed : J.t * J.t) (N : nat) : list (J.t * J.t) := powl seed one2 N.

Lemma gpt_step (N j : nat) : (0 < N)%nat -> 0 + INR j * (2 * PI / INR N) = gpt N j.
Proof. intros HN. unfold gpt. assert (INR N <> 0) by (apply not_0_INR; lia). field. assumption. Qed.

Lemma base_ok (seed : J.t * J.t) (N : nat) : (0 < N)%nat ->
  pinR seed (cos (2 * PI / INR N), sin (2 * PI / INR N)) ->
  Forall2 pinR (base seed N) (map (fun j => (cos (gpt N j), sin (gpt N j))) (seq 0 N)).
Proof.
  intros HN Hs. unfold base.
  pose proof (powl_ok seed one2 (2 * PI / INR N) 0 N Hs one2_ok) as H.
  replace (map (fun j => (cos (gpt N j), sin (gpt N j))) (seq 0 N))
    with (map (fun j => (cos (0 + INR j * (2 * PI / INR N)), sin (0 + INR j * (2 * PI / INR N)))) (seq 0 N));
    [exact H |].
  apply map_ext_in. intros j _. rewrite gpt_step by exact HN. reflexivity.
Qed.

Lemma nth_map_seq {A : Type} (f : nat -> A) (n j : nat) (d : A) : (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros H. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma forall2_nth {A B : Type} (Rel : A -> B -> Prop) (l1 : list A) (l2 : list B) (d1 : A) (d2 : B) (j : nat) :
  Forall2 Rel l1 l2 -> (j < length l2)%nat -> Rel (nth j l1 d1) (nth j l2 d2).
Proof.
  intros H. revert j. induction H as [| x y l1 l2 Hxy _ IH]; intros j Hj; [simpl in Hj; lia |].
  destruct j as [| j]; [exact Hxy |]. simpl. apply IH. simpl in Hj. lia.
Qed.

(** The step of mode k on a grid of N angles, read from the base table. *)
Definition step (B : list (J.t * J.t)) (N : nat) (k : Z) : J.t * J.t :=
  nth (Z.to_nat (k mod Z.of_nat N)) B one2.

Lemma step_ok (seed : J.t * J.t) (N : nat) (k : Z) : (0 < N)%nat ->
  pinR seed (cos (2 * PI / INR N), sin (2 * PI / INR N)) ->
  pinR (step (base seed N) N k) (cos (IZR k * gpt N 1), sin (IZR k * gpt N 1)).
Proof.
  intros HN Hs. pose proof (base_ok seed N HN Hs) as HB.
  assert (Hm : (0 <= k mod Z.of_nat N < Z.of_nat N)%Z) by (apply Z.mod_pos_bound; lia).
  set (j := Z.to_nat (k mod Z.of_nat N)).
  assert (Hj : (j < N)%nat) by (unfold j; lia).
  pose proof (forall2_nth pinR _ _ one2 (0, 0) j HB) as H.
  rewrite length_map, length_seq in H. specialize (H Hj).
  rewrite nth_map_seq in H by exact Hj.
  unfold step. fold j.
  rewrite (angle_mod N k 1 HN), cos_add_2piz, sin_add_2piz.
  replace (IZR (k mod Z.of_nat N) * gpt N 1) with (gpt N j); [exact H |].
  unfold gpt, j. rewrite INR_IZR_INZ, Z2Nat.id by lia.
  assert (INR N <> 0) by (apply not_0_INR; lia). simpl. field. assumption.
Qed.

(** The row cos(k 2 pi a / N), a = 0 .. n - 1. *)
Definition krow (B : list (J.t * J.t)) (N : nat) (k : Z) (n : nat) : list (J.t * J.t) :=
  powl (step B N k) one2 n.

Theorem krow_ok (seed : J.t * J.t) (N : nat) (k : Z) (n : nat) : (0 < N)%nat ->
  pinR seed (cos (2 * PI / INR N), sin (2 * PI / INR N)) ->
  Forall2 (fun CS a => inR (fst CS) (cos (IZR k * gpt N a)) /\ inR (snd CS) (sin (IZR k * gpt N a)))
          (krow (base seed N) N k n) (seq 0 n).
Proof.
  intros HN Hs. unfold krow.
  pose proof (powl_ok (step (base seed N) N k) one2 (IZR k * gpt N 1) 0 n (step_ok seed N k HN Hs) one2_ok) as H.
  apply forall2_map_r' in H. eapply Forall2_impl; [| exact H]. intros CS a [H1 H2]. cbn [fst snd] in H1, H2.
  replace (IZR k * gpt N a) with (0 + INR a * (IZR k * gpt N 1)); [split; assumption |].
  unfold gpt. assert (INR N <> 0) by (apply not_0_INR; lia). simpl. field. assumption.
Qed.

(** The same row read from the base table at k a mod N, entry by entry. A
    rotation widens an enclosure by up to |cos| + |sin| of its step, so rows
    of large modes are read from the base table, whose entries carry the
    widening of small steps only. *)
Definition krowi (B : list (J.t * J.t)) (N : nat) (k : Z) (n : nat) : list (J.t * J.t) :=
  map (fun a => step B N (k * Z.of_nat a)) (seq 0 n).

Theorem krowi_ok (seed : J.t * J.t) (N : nat) (k : Z) (n : nat) : (0 < N)%nat ->
  pinR seed (cos (2 * PI / INR N), sin (2 * PI / INR N)) ->
  Forall2 (fun CS a => inR (fst CS) (cos (IZR k * gpt N a)) /\ inR (snd CS) (sin (IZR k * gpt N a)))
          (krowi (base seed N) N k n) (seq 0 n).
Proof.
  intros HN Hs. unfold krowi. generalize (seq 0 n). intros as_.
  induction as_ as [| a as_ IH]; [constructor |]. cbn [map]. constructor; [| exact IH].
  destruct (step_ok seed N (k * Z.of_nat a) HN Hs) as [C S].
  replace (IZR k * gpt N a) with (IZR (k * Z.of_nat a) * gpt N 1); [split; assumption |].
  unfold gpt. rewrite mult_IZR, <- INR_IZR_INZ. assert (INR N <> 0) by (apply not_0_INR; lia).
  change (INR 1) with 1. field. assumption.
Qed.

(** * Tables over the modes of a box *)

(** From the list e^(i j phi), j = 0 .. K, the table over zrange K: the pair at
    j for the mode j and its conjugate for -j. *)
Fixpoint zfold (pos : list (J.t * J.t)) (K : nat) : list (J.t * J.t) :=
  match K with
  | O => [nth 0 pos one2]
  | S K' => let x := nth (S K') pos one2 in x :: (fst x, J.neg (snd x)) :: zfold pos K'
  end.

Lemma zfold_ok (pos : list (J.t * J.t)) (phi : R) (K : nat) :
  (forall j, (j <= K)%nat -> pinR (nth j pos one2) (cos (INR j * phi), sin (INR j * phi))) ->
  Forall2 (fun CS k => inR (fst CS) (cos (IZR k * phi)) /\ inR (snd CS) (sin (IZR k * phi))) (zfold pos K) (zrange K).
Proof.
  induction K as [| K IH]; intros Hj.
  - cbn [zfold zrange]. constructor; [| constructor].
    destruct (Hj 0%nat (le_n 0)) as [A B]. cbn [fst snd] in A, B. simpl in A, B |- *.
    rewrite Rmult_0_l in A, B |- *. split; assumption.
  - cbn [zfold zrange].
    destruct (Hj (S K) (le_n _)) as [A B]. cbn [fst snd] in A, B.
    rewrite INR_IZR_INZ in A, B.
    constructor; [split; assumption |]. constructor.
    + cbn [fst snd]. rewrite opp_IZR, Ropp_mult_distr_l_reverse, cos_neg, sin_neg.
      split; [exact A | apply inR_neg, B].
    + apply IH. intros j Hjk. apply Hj. lia.
Qed.

Definition ztab (st : J.t * J.t) (K : nat) : list (J.t * J.t) := zfold (powl st one2 (S K)) K.

Theorem ztab_ok (st : J.t * J.t) (phi : R) (K : nat) :
  pinR st (cos phi, sin phi) ->
  Forall2 (fun CS k => inR (fst CS) (cos (IZR k * phi)) /\ inR (snd CS) (sin (IZR k * phi))) (ztab st K) (zrange K).
Proof.
  intros Hs. unfold ztab. apply zfold_ok.
  pose proof (powl_ok st one2 phi 0 (S K) Hs one2_ok) as H.
  intros j Hj.
  pose proof (forall2_nth pinR _ _ one2 (0, 0) j H) as G.
  rewrite length_map, length_seq in G. assert (Hl : (j < S K)%nat) by lia. specialize (G Hl).
  rewrite nth_map_seq in G by exact Hl.
  rewrite !Rplus_0_l in G. exact G.
Qed.

(** * Exponentials *)

(** e^y, e^(y + x), e^(y + 2 x), ... *)
Fixpoint spow (E X : J.t) (n : nat) : list J.t :=
  match n with O => [] | S n' => X :: spow E (J.mul X E) n' end.

Theorem spow_ok (E X : J.t) (x y : R) (n : nat) : inR E (exp x) -> inR X (exp y) ->
  Forall2 inR (spow E X n) (map (fun j => exp (y + INR j * x)) (seq 0 n)).
Proof.
  intros HE. revert X y. induction n as [| n IH]; intros X y HX; [constructor |].
  cbn [spow seq map]. constructor.
  - rewrite Rmult_0_l, Rplus_0_r. exact HX.
  - rewrite <- seq_shift, map_map.
    replace (map (fun j => exp (y + INR (S j) * x)) (seq 0 n)) with (map (fun j => exp ((y + x) + INR j * x)) (seq 0 n)).
    + apply IH. rewrite exp_plus. apply inR_mul; assumption.
    + apply map_ext. intros j. rewrite S_INR. f_equal. ring.
Qed.

(** The table over zrange K of e^(y + x |k|). *)
Fixpoint zfold1 (pos : list J.t) (K : nat) : list J.t :=
  match K with O => [nth 0 pos J.zero] | S K' => let v := nth (S K') pos J.zero in v :: v :: zfold1 pos K' end.

Definition zexp (E X : J.t) (K : nat) : list J.t := zfold1 (spow E X (S K)) K.

Theorem zexp_ok (E X : J.t) (x y : R) (K : nat) : inR E (exp x) -> inR X (exp y) ->
  Forall2 (fun V k => inR V (exp (y + x * Rabs (IZR k)))) (zexp E X K) (zrange K).
Proof.
  intros HE HX. unfold zexp.
  pose proof (spow_ok E X x y (S K) HE HX) as H.
  assert (Hj : forall j, (j <= K)%nat -> inR (nth j (spow E X (S K)) J.zero) (exp (y + INR j * x))).
  { intros j Hj. pose proof (forall2_nth inR _ _ J.zero 0 j H) as G.
    rewrite length_map, length_seq in G. assert (Hl : (j < S K)%nat) by lia. specialize (G Hl).
    rewrite nth_map_seq in G by exact Hl. exact G. }
  clear H. generalize (spow E X (S K)) Hj. clear Hj. intros pos Hj.
  induction K as [| K IH].
  - cbn [zfold1 zrange]. constructor; [| constructor].
    simpl. rewrite Rabs_R0, Rmult_0_r. specialize (Hj 0%nat (le_n 0)). simpl in Hj. rewrite Rmult_0_l in Hj. exact Hj.
  - cbn [zfold1 zrange]. specialize (IH (fun j Hjk => Hj j ltac:(lia))).
    pose proof (Hj (S K) (le_n _)) as HS.
    assert (E1 : exp (y + INR (S K) * x) = exp (y + x * Rabs (IZR (Z.of_nat (S K))))).
    { rewrite Rabs_pos_eq by (apply IZR_le; lia). rewrite <- INR_IZR_INZ. f_equal. ring. }
    assert (E2 : exp (y + INR (S K) * x) = exp (y + x * Rabs (IZR (- Z.of_nat (S K))))).
    { rewrite opp_IZR, Rabs_Ropp, Rabs_pos_eq by (apply IZR_le; lia). rewrite <- INR_IZR_INZ. f_equal. ring. }
    constructor; [rewrite <- E1; exact HS |]. constructor; [rewrite <- E2; exact HS | exact IH].
Qed.

(** The table over zrange K of e^(y + x (K - |k|)), from the powers listed
    downward from |k| = K, so that a decaying exponential starts from its
    largest entry. *)
Fixpoint zfold1r (pos : list J.t) (K j : nat) : list J.t :=
  match j with
  | O => [nth K pos J.zero]
  | S j' => let v := nth (K - S j') pos J.zero in v :: v :: zfold1r pos K j'
  end.

Definition zexp_rev (E X : J.t) (K : nat) : list J.t := zfold1r (spow E X (S K)) K K.

Theorem zexp_rev_ok (E X : J.t) (x y : R) (K : nat) : inR E (exp x) -> inR X (exp y) ->
  Forall2 (fun V k => inR V (exp (y + x * (INR K - Rabs (IZR k))))) (zexp_rev E X K) (zrange K).
Proof.
  intros HE HX. unfold zexp_rev.
  pose proof (spow_ok E X x y (S K) HE HX) as H.
  assert (Hj : forall i, (i <= K)%nat -> inR (nth i (spow E X (S K)) J.zero) (exp (y + INR i * x))).
  { intros i Hi. pose proof (forall2_nth inR _ _ J.zero 0 i H) as G.
    rewrite length_map, length_seq in G. assert (Hl : (i < S K)%nat) by lia. specialize (G Hl).
    rewrite nth_map_seq in G by exact Hl. exact G. }
  clear H. generalize (spow E X (S K)) Hj. clear Hj. intros pos Hj.
  assert (Gen : forall j, (j <= K)%nat ->
            Forall2 (fun V k => inR V (exp (y + x * (INR K - Rabs (IZR k))))) (zfold1r pos K j) (zrange j)).
  { induction j as [| j IH]; intros HjK.
    - cbn [zfold1r zrange]. constructor; [| constructor].
      simpl. rewrite Rabs_R0, Rminus_0_r. specialize (Hj K (le_n K)).
      replace (y + x * INR K) with (y + INR K * x) by ring. exact Hj.
    - cbn [zfold1r zrange]. specialize (IH ltac:(lia)).
      pose proof (Hj (K - S j)%nat ltac:(lia)) as HS.
      assert (E1 : exp (y + INR (K - S j) * x) = exp (y + x * (INR K - Rabs (IZR (Z.of_nat (S j)))))).
      { rewrite Rabs_pos_eq by (apply IZR_le; lia). rewrite <- INR_IZR_INZ, minus_INR by lia. f_equal. ring. }
      assert (E2 : exp (y + INR (K - S j) * x) = exp (y + x * (INR K - Rabs (IZR (- Z.of_nat (S j)))))).
      { rewrite opp_IZR, Rabs_Ropp, Rabs_pos_eq by (apply IZR_le; lia). rewrite <- INR_IZR_INZ, minus_INR by lia.
        f_equal. ring. }
      constructor; [rewrite <- E1; exact HS |]. constructor; [rewrite <- E2; exact HS | exact IH]. }
  exact (Gen K (le_n K)).
Qed.

End Tab.
