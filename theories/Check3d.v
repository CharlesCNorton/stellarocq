(** The assembly stage of the three-dimensional stability check: what it
    computes from the cells' ranges, and what each computation encloses.

    For the range Rc of W N W^-1 over a reference step: the reference matrix
    Nref, the midpoints of Rc; om and nu, bounds on the row sums of |Rc - Nref|
    and of |Rc|; the reference step G = I + 2^-16 Nref and a bound q on its
    norm; and l, a bound on 2^-16 om + e^(2^-16 nu) - 1 - 2^-16 nu
    ([cell_ok_sound]). For the steps of a segment: an enclosure of the product
    of their reference steps ([iprod_cont]), and delta, a bound on
    sum_i (prod_{j > i} q_j) l_i (prod_{j < i} (q_j + l_j)) ([delta_ok_sound]),
    the distance Assemble.seg_bound gives between every level's propagator over
    the segment and that product. The sum is prod_j (q_j + l_j) - prod_j q_j
    ([rdelta_prod]), which the check evaluates. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat Shoot Recur CFMS Step NBound TMEval TMat Osc
  CellTM Assemble.

Import ListNotations.
Local Open Scope R_scope.

(** The real value of an interval's midpoint, which a nonempty interval holds. *)
Definition rmid (X : I.type) : R := proj_val (I.F.toX (I.midpoint X)).

Lemma rmid_in : forall X x, contains (I.convert X) (Xreal x) -> contains (I.convert X) (Xreal (rmid X)).
Proof.
  intros X x Hx. assert (Hne : not_empty (I.convert X)) by (exists x; exact Hx).
  destruct (I.midpoint_correct X Hne) as [E C]. unfold rmid. rewrite <- E. exact C.
Qed.

(* ---------------------------------------------------------------- *)
(* The computations                                                  *)

Section Defs.

Variable prec : F.precision.

Definition ione : I.type := I.fromZ prec 1.
Definition ihr : I.type := Newton.dyad prec (1%Z, (-16)%Z).

Definition nref (Rc : imat) : imat := itab 14 14 (fun r c => I.singleton (I.midpoint (iget Rc r c))).
Definition iom (Rc : imat) : I.type := iupmax prec (map (irowsum prec 14 (isub prec 14 14 Rc (nref Rc))) (seq 0 14)).
Definition inu (Rc : imat) : I.type := iupmax prec (map (irowsum prec 14 Rc) (seq 0 14)).
Definition igs (Rc : imat) : imat :=
  let N := nref Rc in let H := ihr in
  itab 14 14 (fun r c => I.add prec (I.fromZ prec (if Nat.eqb r c then 1%Z else 0%Z)) (I.mul prec H (iget N r c))).
Definition iq (Rc : imat) : I.type := iupmax prec (map (irowsum prec 14 (igs Rc)) (seq 0 14)).
Definition iexpr (om nu : I.type) : I.type :=
  I.add prec (I.mul prec ihr om) (I.sub prec (I.sub prec (I.exp prec (I.mul prec ihr nu)) ione) (I.mul prec ihr nu)).
Definition il (Rc : imat) : I.type := iupmax prec [iexpr (iom Rc) (inu Rc)].

Definition cell_ok (Rc : imat) : bool :=
  inorm_le prec 14 14 (isub prec 14 14 Rc (nref Rc)) (iom Rc) && inorm_le prec 14 14 Rc (inu Rc) &&
  inorm_le prec 14 14 (igs Rc) (iq Rc) && nonneg (I.sub prec (il Rc) (iexpr (iom Rc) (inu Rc))).

(** The product of a list, its last element leftmost, in the order of
    Shoot.gprodf. *)
Definition iprodl (L : list I.type) : I.type := fold_left (fun acc x => I.mul prec x acc) L ione.

(** For the steps Rs 0 .. Rs (nb - 1) of a segment:
    prod (q_j + l_j) - prod q_j. *)
Definition idelta (Rs : nat -> imat) (nb : nat) : I.type :=
  I.sub prec (iprodl (map (fun j => I.add prec (iq (Rs j)) (il (Rs j))) (seq 0 nb)))
             (iprodl (map (fun j => iq (Rs j)) (seq 0 nb))).
Definition delta_of (Rs : nat -> imat) (nb : nat) : I.type := iupmax prec [idelta Rs nb].
Definition delta_ok (Rs : nat -> imat) (nb : nat) : bool := nonneg (I.sub prec (delta_of Rs nb) (idelta Rs nb)).

(** The product of the reference steps G_{nb-1} ... G_0. *)
Definition iprod (Rs : nat -> imat) (nb : nat) : imat :=
  fold_left (fun acc i => imm prec 14 14 14 (igs (Rs i)) acc) (seq 0 nb) (iI prec 14).

End Defs.

(** Conversion unfolds these before the interval operations they call. *)
Strategy expand [nref iom inu igs iq iexpr il cell_ok iprodl idelta delta_of delta_ok iprod].

(* ---------------------------------------------------------------- *)
(* What they enclose                                                 *)

Definition hr : R := dyadR (1%Z, (-16)%Z).

Section Sound.

Variable prec : F.precision.

Lemma iupmax_in : forall L, contains (I.convert (iupmax prec L)) (Xreal (rmid (iupmax prec L))).
Proof. intros L. apply (rmid_in _ _ (I.singleton_correct _)). Qed.

Definition rnref (Rc : imat) : mat := fun r c => rmid (iget Rc r c).
Definition om (Rc : imat) : R := rmid (iom prec Rc).
Definition nu (Rc : imat) : R := rmid (inu prec Rc).
Definition qq (Rc : imat) : R := rmid (iq prec Rc).
Definition ll (Rc : imat) : R := rmid (il prec Rc).
Definition gref (Rc : imat) : mat := fun r c => mI r c + hr * rnref Rc r c.

Lemma nref_cont : forall Rc, icont 14 14 (nref Rc) (rnref Rc).
Proof. intros Rc. apply itab_correct. intros r c _ _. unfold rnref, rmid. apply I.singleton_correct. Qed.

Lemma igs_cont : forall Rc, icont 14 14 (igs prec Rc) (gref Rc).
Proof.
  intros Rc. unfold igs. cbv zeta. apply itab_correct. intros r c Hr Hc. unfold gref.
  apply (I.add_correct prec _ _ (Xreal (mI r c)) (Xreal (hr * rnref Rc r c))).
  - unfold mI. destruct (Nat.eqb r c); apply I.fromZ_correct.
  - apply (I.mul_correct prec _ _ (Xreal hr) (Xreal (rnref Rc r c))); [apply dyad_correct | apply nref_cont; assumption].
Qed.

Lemma iexpr_cont :
  forall X Y x y, contains (I.convert X) (Xreal x) -> contains (I.convert Y) (Xreal y) ->
  contains (I.convert (iexpr prec X Y)) (Xreal (hr * x + (exp (hr * y) - 1 - hr * y))).
Proof.
  intros X Y x y HX HY. unfold iexpr.
  assert (Hh : contains (I.convert (ihr prec)) (Xreal hr)) by apply dyad_correct.
  assert (H1 := I.mul_correct prec _ _ _ _ Hh HX).
  assert (H2 := I.mul_correct prec _ _ _ _ Hh HY).
  assert (H3 := I.exp_correct prec _ _ H2).
  assert (H4 := I.sub_correct prec _ _ _ _ H3 (I.fromZ_correct prec 1)).
  assert (H5 := I.sub_correct prec _ _ _ _ H4 H2).
  exact (I.add_correct prec _ _ _ _ H1 H5).
Qed.

Theorem cell_ok_sound :
  forall Rc, cell_ok prec Rc = true ->
  (forall A, icont 14 14 Rc A -> mnorm 14 14 (msub A (rnref Rc)) <= om Rc /\ mnorm 14 14 A <= nu Rc) /\
  mnorm 14 14 (gref Rc) <= qq Rc /\
  hr * om Rc + (exp (hr * nu Rc) - 1 - hr * nu Rc) <= ll Rc.
Proof.
  intros Rc H. unfold cell_ok in H.
  apply andb_prop in H. destruct H as [H H4]. apply andb_prop in H. destruct H as [H H3].
  apply andb_prop in H. destruct H as [H1 H2].
  split; [| split].
  - intros A HA. split.
    + apply (inorm_le_correct prec 14 14 (isub prec 14 14 Rc (nref Rc)) (msub A (rnref Rc)) (iom prec Rc) (om Rc));
        [lia | | apply iupmax_in | exact H1].
      apply isub_correct; [exact HA | apply nref_cont].
    + exact (inorm_le_correct prec 14 14 Rc A (inu prec Rc) (nu Rc) ltac:(lia) HA (iupmax_in _) H2).
  - exact (inorm_le_correct prec 14 14 (igs prec Rc) (gref Rc) (iq prec Rc) (qq Rc) ltac:(lia) (igs_cont Rc)
             (iupmax_in _) H3).
  - assert (Hom : contains (I.convert (iom prec Rc)) (Xreal (om Rc))) by apply iupmax_in.
    assert (Hnu : contains (I.convert (inu prec Rc)) (Xreal (nu Rc))) by apply iupmax_in.
    assert (Hl : contains (I.convert (il prec Rc)) (Xreal (ll Rc))) by apply iupmax_in.
    assert (Hs := I.sub_correct prec _ _ _ _ Hl (iexpr_cont _ _ _ _ Hom Hnu)).
    destruct (nonneg_correct _ _ Hs H4) as [r [Er Hr]]. injection Er as <-. lra.
Qed.

Lemma fold_seq_S :
  forall {A : Type} (f : A -> nat -> A) n x, fold_left f (seq 0 (S n)) x = f (fold_left f (seq 0 n) x) n.
Proof. intros A f n x. rewrite seq_S, fold_left_app. reflexivity. Qed.

Lemma iprodl_cont :
  forall g (gr : nat -> R) n, (forall j, contains (I.convert (g j)) (Xreal (gr j))) ->
  contains (I.convert (iprodl prec (map g (seq 0 n)))) (Xreal (gprodf gr 0 n)).
Proof.
  intros g gr n Hg. induction n as [|n IH].
  - apply I.fromZ_correct.
  - unfold iprodl in *. rewrite seq_S, map_app, fold_left_app. cbn [map fold_left gprodf].
    rewrite Nat.add_0_l. apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); [apply Hg | exact IH].
Qed.

Definition rdelta (Rs : nat -> imat) (nb : nat) : R :=
  msum (fun i => gprodf (fun j => qq (Rs j)) (S i) (nb - S i) * ll (Rs i) * gprodf (fun j => qq (Rs j) + ll (Rs j)) 0 i) nb.

(** The sum telescopes. *)
Lemma telescope_prod :
  forall (q l : nat -> R) n,
  msum (fun i => gprodf q (S i) (n - S i) * l i * gprodf (fun j => q j + l j) 0 i) n
  = gprodf (fun j => q j + l j) 0 n - gprodf q 0 n.
Proof.
  intros q l n. induction n as [|n IH]; [cbn; ring|].
  cbn [msum]. rewrite (msum_ext _ (fun i => q n * (gprodf q (S i) (n - S i) * l i * gprodf (fun j => q j + l j) 0 i))).
  2: { intros i Hi. replace (S n - S i)%nat with (S (n - S i)) by lia. cbn [gprodf].
       replace (S i + (n - S i))%nat with n by lia. ring. }
  rewrite msum_scal, IH. replace (S n - S n)%nat with O by lia. cbn [gprodf]. rewrite !Nat.add_0_l. ring.
Qed.

Lemma rdelta_prod :
  forall Rs nb, rdelta Rs nb = gprodf (fun j => qq (Rs j) + ll (Rs j)) 0 nb - gprodf (fun j => qq (Rs j)) 0 nb.
Proof. intros Rs nb. unfold rdelta. apply telescope_prod. Qed.

Lemma idelta_cont : forall Rs nb, contains (I.convert (idelta prec Rs nb)) (Xreal (rdelta Rs nb)).
Proof.
  intros Rs nb. rewrite rdelta_prod. unfold idelta.
  apply (I.sub_correct prec _ _ (Xreal _) (Xreal _)); apply iprodl_cont; intros j.
  - apply (I.add_correct prec _ _ (Xreal _) (Xreal _)); apply iupmax_in.
  - apply iupmax_in.
Qed.

Lemma delta_ok_sound : forall Rs nb, delta_ok prec Rs nb = true -> rdelta Rs nb <= rmid (delta_of prec Rs nb).
Proof.
  intros Rs nb H. unfold delta_ok in H.
  assert (Hd : contains (I.convert (delta_of prec Rs nb)) (Xreal (rmid (delta_of prec Rs nb)))) by apply iupmax_in.
  assert (Hs := I.sub_correct prec _ _ _ _ Hd (idelta_cont Rs nb)).
  destruct (nonneg_correct _ _ Hs H) as [r [Er Hr]]. injection Er as <-. lra.
Qed.

Lemma iprod_cont : forall Rs nb, icont 14 14 (iprod prec Rs nb) (mprod 14 (fun i => gref (Rs i)) 0 nb).
Proof.
  intros Rs nb. induction nb as [|nb IH].
  - apply iI_correct.
  - unfold iprod in *. rewrite fold_seq_S. cbn [mprod]. rewrite Nat.add_0_l.
    apply imm_correct; [apply igs_cont | exact IH].
Qed.

End Sound.
