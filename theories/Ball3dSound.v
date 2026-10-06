(** What the ball and consistency checks of Ball3d state.

    For a collocation point's residual tail evaluated over an environment of
    its 87 input slots: the adjoint slot of input i is the derivative of the
    output along that input ([adj_partial], AdjointSound with no prefix), and
    the forward tangent of a slot along input l is its derivative along l
    ([tan_partial], DerivSeq). The facts are proved for any flattened list
    and its adjoints with the properties [tail_ok] decides, and [tail_ok]
    holds of the radial and the poloidal tails. *)

From Coq Require Import ZArith Reals List Bool Lia Lra FunctionalExtensionality.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Newton TMEval LinCheck DerivSeq Adjoint AdjointSound
  CellTM QDiff Check3d Jet Ball3d Taylor.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Real functions                                                    *)

Lemma dpl_ext :
  forall f g x l, (forall t, f t = g t) -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros f g x l H D eps Heps. destruct (D eps Heps) as [del Hdel]. exists del.
  intros t Ht Htd. rewrite <- !H. apply Hdel; assumption.
Qed.

Lemma dpl_const : forall (c x : R), derivable_pt_lim (fun _ => c) x 0.
Proof.
  intros c x eps Heps. exists (mkposreal 1 Rlt_0_1). intros t Ht _.
  replace ((c - c) / t - 0) with 0 by (field; exact Ht). rewrite Rabs_R0. exact Heps.
Qed.

Lemma Xderive_real :
  forall f t0 d y, f (Xreal t0) = Xreal y -> Xderive_pt f (Xreal t0) (Xreal d) ->
  derivable_pt_lim (fun t => xr (f (Xreal t))) t0 d.
Proof.
  intros f t0 d y Hy HD. unfold Xderive_pt in HD. rewrite Hy in HD. specialize (HD 0).
  apply (dpl_ext _ _ _ _ (fun t => eq_refl) HD).
Qed.

Lemma ks40_lt : forall k, In k ks40 -> (k < 87)%nat.
Proof. intros k Hk. unfold ks40 in Hk. apply in_seq in Hk. lia. Qed.

Lemma ks40_nth : forall i, (i < 40)%nat -> nth i ks40 0%nat = (12 + i)%nat.
Proof. intros i Hi. unfold ks40. rewrite seq_nth by exact Hi. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* A flattened list and its adjoints                                 *)

Section Tail.

Variables (ab0 : list binding) (top0 o0 : nat).
Hypothesis Hwf0 : well_formed 87 ab0 = true.
Hypothesis Hs0 : forallb (fun b => single (snd b)) ab0 = true.
Hypothesis Htop0 : top0 = (87 + length ab0)%nat.
Hypothesis Ho0 : (87 <= o0 < top0)%nat.
Hypothesis Hwft0 : well_formed 87 (ab0 ++ adj_binds 87 top0 o0 ab0 ks40) = true.
Hypothesis Hin0 : forall i, (i < 40)%nat -> (in_slot 87 top0 o0 i < 87 + length (ab0 ++ adj_binds 87 top0 o0 ab0 ks40))%nat.

Let tl0 : list binding := ab0 ++ adj_binds 87 top0 o0 ab0 ks40.

(** The inputs real, the slots from 87 unset, every slot of the tail real. *)
Definition tail_env (E0 : env ExtendedR) : Prop :=
  (forall k, (87 <= k)%nat -> eget k E0 Xnan = Xnan) /\
  (forall k, (k < 87)%nat -> exists x, eget k E0 Xnan = Xreal x) /\
  (forall k, (87 <= k < 87 + length tl0)%nat -> exists x, eget k (xextend E0 tl0) Xnan = Xreal x).

Lemma wf_adj : well_formed (87 + length ab0) (adj_binds 87 top0 o0 ab0 ks40) = true.
Proof. assert (H := Hwft0). rewrite DivDiff.well_formed_app in H. apply andb_prop in H. exact (proj2 H). Qed.

Lemma tail_low :
  forall E k, (k < 87 + length ab0)%nat -> eget k (xextend E tl0) Xnan = eget k (xextend E ab0) Xnan.
Proof.
  intros E k Hk. unfold tl0. rewrite xextend_app.
  apply (eget_above _ _ (87 + length ab0)); [exact wf_adj | exact Hk].
Qed.

Lemma len_ab_tl : (length ab0 <= length tl0)%nat.
Proof. unfold tl0. rewrite length_app. lia. Qed.

Lemma in_slot_lt : forall i, (i < 40)%nat -> (87 <= in_slot 87 top0 o0 i < 87 + length tl0)%nat.
Proof. intros i Hi. split; [unfold in_slot; lia | exact (Hin0 i Hi)]. Qed.

(** The adjoint slot of input 12 + i is the derivative of the output along it. *)
Lemma adj_partial :
  forall E0, tail_env E0 -> forall i, (i < 40)%nat ->
  derivable_pt_lim (fun t => xr (eget o0 (xextend (eset (12 + i) E0 (Xreal t)) tl0) Xnan))
                   (xr (eget (12 + i) E0 Xnan))
                   (xr (eget (in_slot 87 top0 o0 i) (xextend E0 tl0) Xnan)).
Proof.
  intros E0 [Hun [Hin Hre]] i Hi.
  assert (Hwfa : well_formed 87 ([] ++ ab0 ++ adj_binds 87 (87 + length ab0) o0 ab0 ks40) = true).
  { cbn [app]. rewrite <- Htop0. exact Hwft0. }
  assert (Ho' : (87 <= o0 < 87 + length ab0)%nat) by lia.
  assert (Hreal : forall j, (j < 87 + length ab0)%nat -> exists x, eget j (xextend E0 ([] ++ ab0)) Xnan = Xreal x).
  { intros j Hj. cbn [app]. destruct (Nat.lt_ge_cases j 87) as [Hj0|Hj0].
    - rewrite (eget_above _ _ 87) by assumption. apply Hin. exact Hj0.
    - rewrite <- tail_low by exact Hj. apply Hre. assert (H := len_ab_tl). lia. }
  destruct (Hin (12 + i)%nat ltac:(lia)) as [t0 Ht0].
  assert (HD := adj_input 87 87 (length ab0) o0 (12 + i) [] ab0 ks40 E0 eq_refl eq_refl Hwf0 eq_refl Hs0
                  Ho' ltac:(lia) ks40_lt Hwfa Hreal ltac:(intros k Hk; lia) eq_refl i
                  ltac:(unfold ks40; rewrite length_seq; exact Hi) ltac:(rewrite ks40_nth by exact Hi; reflexivity)
                  t0 Hun Hin Ht0).
  cbn [app] in HD. rewrite <- Htop0 in HD. fold tl0 in HD.
  assert (Hy : exists y, slot_along (fun t => xextend (eset (12 + i) E0 (Xreal t)) ab0) o0 (Xreal t0) = Xreal y).
  { cbn [slot_along]. rewrite (env_agree ab0 _ E0).
    - rewrite <- tail_low by lia. apply Hre. assert (H := len_ab_tl). lia.
    - intros k. destruct (Nat.eq_dec k (12 + i)) as [->|Hne].
      + rewrite eget_eset_eq. symmetry. exact Ht0.
      + apply eget_eset_neq. exact Hne. }
  destruct Hy as [y Hy].
  destruct (Hre (in_slot 87 top0 o0 i) (in_slot_lt i Hi)) as [g Hg].
  rewrite Hg in HD. rewrite Ht0, Hg. cbn [xr].
  assert (HX := Xderive_real _ t0 _ y Hy HD).
  eapply dpl_ext; [| exact HX]. intros t. cbn [slot_along]. rewrite <- tail_low by lia. reflexivity.
Qed.

(** The forward tangent along input l of a slot of the tail is its
    derivative along l. *)
Lemma tan_partial :
  forall E0, tail_env E0 -> forall l g, (l < 87)%nat -> (87 <= g < 87 + length tl0)%nat ->
  (exists y, eget (g + length tl0) (xextend E0 (with_dseq l 87 (length tl0) tl0)) Xnan = Xreal y) ->
  derivable_pt_lim (fun t => xr (eget g (xextend (eset l E0 (Xreal t)) tl0) Xnan))
                   (xr (eget l E0 Xnan))
                   (xr (eget (g + length tl0) (xextend E0 (with_dseq l 87 (length tl0) tl0)) Xnan)).
Proof.
  intros E0 [Hun [Hin Hre]] l g Hl Hg [y Hy].
  remember (length tl0) as n eqn:En.
  assert (Hn : (0 < n)%nat) by lia.
  destruct (Hin l Hl) as [t0 Ht0].
  assert (HS := sinv_base l 87 n Hl Hn E0 Hun Hin).
  destruct (dseq_correct l 87 n Hl Hn tl0 (fun t => eset l E0 (Xreal t)) Hwft0 (eq_sym En) HS) as [_ HD].
  specialize (HD (g - 87)%nat t0 ltac:(lia)).
  replace (87 + (g - 87))%nat with g in HD by lia.
  replace (87 + n + (g - 87))%nat with (g + n)%nat in HD by lia.
  assert (HE : forall k, eget k (eset l E0 (Xreal t0)) Xnan = eget k E0 Xnan).
  { intros k. destruct (Nat.eq_dec k l) as [->|Hne]; [rewrite eget_eset_eq; symmetry; exact Ht0 | apply eget_eset_neq; exact Hne]. }
  rewrite (env_agree _ _ E0 HE) in HD. rewrite Hy in HD.
  assert (Hwfd : well_formed (87 + n) (dbinds l 87 n tl0) = true) by exact (dbinds_wf l 87 n Hl Hn tl0 87 Hwft0 (le_n 87)).
  assert (Hlow : forall E, eget g (xextend E (with_dseq l 87 n tl0)) Xnan = eget g (xextend E tl0) Xnan).
  { intros E. unfold with_dseq. rewrite xextend_app. apply (eget_above _ _ (87 + n)); [exact Hwfd | lia]. }
  destruct (Hre g Hg) as [x Hx].
  assert (Hv : slot_along (fun t => xextend (eset l E0 (Xreal t)) (with_dseq l 87 n tl0)) g (Xreal t0) = Xreal x).
  { cbn [slot_along]. rewrite (env_agree _ _ E0 HE), Hlow. exact Hx. }
  rewrite Ht0, Hy. cbn [xr].
  assert (HX := Xderive_real _ t0 _ x Hv HD).
  eapply dpl_ext; [| exact HX]. intros t. cbn [slot_along]. rewrite Hlow. reflexivity.
Qed.

End Tail.

(* ---------------------------------------------------------------- *)
(* The radial and poloidal tails                                     *)

Lemma tl_split : forall r, tl r = ab r ++ adj_binds 87 (ttop r) (tout r) (ab r) ks40.
Proof. intros r. reflexivity. Qed.

(** The properties of the tails, decided with the flattening computed once. *)
Definition tail_ok_of (a : list binding * env nat * nat) : bool :=
  let A := fst (fst a) in let tp := snd a in let o := rget (snd (fst a)) rtop3 in
  let T := A ++ adj_binds 87 tp o A ks40 in let n := length T in
  well_formed 87 A && forallb (fun b => single (snd b)) A &&
  Nat.eqb tp (87 + length A) && Nat.leb 87 o && Nat.ltb o tp &&
  well_formed 87 T && forallb (fun i => Nat.ltb (in_slot 87 tp o i) (87 + n)) (seq 0 40).

Definition tail_ok (r : bool) : bool := tail_ok_of (anfs r).

Lemma tail_ok_true : forall r, tail_ok r = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma tail_facts :
  forall r, well_formed 87 (ab r) = true /\ forallb (fun b => single (snd b)) (ab r) = true /\
            ttop r = (87 + length (ab r))%nat /\ (87 <= tout r < ttop r)%nat /\
            well_formed 87 (ab r ++ adj_binds 87 (ttop r) (tout r) (ab r) ks40) = true /\
            (forall i, (i < 40)%nat ->
               (in_slot 87 (ttop r) (tout r) i < 87 + length (ab r ++ adj_binds 87 (ttop r) (tout r) (ab r) ks40))%nat).
Proof.
  intros r. assert (H := tail_ok_true r). unfold tail_ok, tail_ok_of in H. cbv zeta in H.
  fold (ab r) (ttop r) (tout r) in H.
  apply andb_prop in H. destruct H as [H H7]. apply andb_prop in H. destruct H as [H H6].
  apply andb_prop in H. destruct H as [H H5]. apply andb_prop in H. destruct H as [H H4].
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  split; [exact H1|]. split; [exact H2|]. split; [apply Nat.eqb_eq; exact H3|].
  split; [split; [apply Nat.leb_le; exact H4 | apply Nat.ltb_lt; exact H5]|]. split; [exact H6|].
  intros i Hi. rewrite forallb_forall in H7. apply Nat.ltb_lt. apply H7. apply in_seq. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The interval checks                                               *)

Lemma contains_nan_any : forall X v, contains (I.convert X) Xnan -> contains (I.convert X) v.
Proof. intros X v H. apply contains_Xnan in H. rewrite H. exact I. Qed.

Section Checks.

Variable prec : F.precision.

Lemma rb_sound :
  forall X x, contains (I.convert X) x -> rb prec X = true ->
  exists y, x = Xreal y /\ Rabs y <= rmid (ibound prec X).
Proof.
  intros X x Hx H. unfold rb in H. cbv zeta in H. apply andb_prop in H. destruct H as [N1 N2].
  assert (HB := iupmax_in prec [I.abs X]). fold (ibound prec X) in HB.
  destruct (nonneg_correct _ _ (I.sub_correct prec _ _ _ _ HB Hx) N1) as [r1 [E1 H1]].
  destruct x as [|y]; [discriminate E1|].
  injection E1 as E1.
  destruct (nonneg_correct _ _ (I.add_correct prec _ _ _ _ Hx HB) N2) as [r2 [E2 H2]].
  injection E2 as E2.
  exists y. split; [reflexivity|]. apply Rabs_le. lra.
Qed.

Lemma le_bound_sound : forall K B b, contains (I.convert B) (Xreal b) -> le_bound prec K B = true -> b <= dyadR K.
Proof.
  intros K B b HB H. unfold le_bound in H.
  destruct (nonneg_correct _ _ (I.sub_correct prec _ _ _ _ (dyad_correct prec K) HB) H) as [r1 [E1 H1]].
  injection E1 as E1. lra.
Qed.

Lemma ival_contains :
  forall lo hi x, dyadR lo <= x <= dyadR hi -> contains (I.convert (ival prec lo hi)) (Xreal x).
Proof.
  intros lo hi x Hx. unfold ival.
  apply (contains_connected _ (dyadR lo) (dyadR hi)); [| | exact Hx].
  - apply I.join_correct. left. apply dyad_correct.
  - apply I.join_correct. right. apply dyad_correct.
Qed.

Lemma sym_contains : forall rr z, Rabs z <= dyadR rr -> contains (I.convert (sym prec rr)) (Xreal z).
Proof.
  intros rr z Hz. unfold sym.
  assert (H1 := Rle_abs z). assert (H2 := Rle_abs (- z)). rewrite Rabs_Ropp in H2.
  apply (contains_connected _ (- dyadR rr) (dyadR rr)); [| | lra].
  - apply I.join_correct. left. exact (I.neg_correct _ (Xreal _) (dyad_correct prec rr)).
  - apply I.join_correct. right. apply dyad_correct.
Qed.

End Checks.

(* ---------------------------------------------------------------- *)
(* The box of a cell                                                 *)

(** The exact jet of point kp, and the jet with the 27 unknown slots moved by z. *)
Definition Ex (r : bool) (kp : nat) (s h : R) : env ExtendedR :=
  xextend (pin s h 0) (jet_layer (fst (pt r kp)) (snd (pt r kp)) 0).

Definition Ez (r : bool) (kp : nat) (s h : R) (z : nat -> R) : env ExtendedR :=
  fold_left (fun E pc => let k := uslot (fst pc) (snd pc) in eset k E (Xreal (xr (eget k E Xnan) + z k))) xdpc (Ex r kp s h).

Definition rad (rx rd : Z * Z) (pc : nat * nat) : R := if Nat.eqb (fst pc) 0 then dyadR rx else dyadR rd.

Lemma uslot_lt : forall pc, In pc xdpc -> (12 <= uslot (fst pc) (snd pc) < 52)%nat.
Proof.
  intros [p c] Hpc. unfold xdpc in Hpc. apply in_prod_iff in Hpc. destruct Hpc as [Hp Hc].
  apply in_seq in Hp. apply in_seq in Hc. cbn [fst snd]. unfold uslot.
  destruct (Nat.ltb_spec c 5); lia.
Qed.

Lemma fold_eset_other :
  forall (sl : nat * nat -> nat) (L : list (nat * nat)) (f : env ExtendedR -> nat * nat -> ExtendedR) E k,
  (forall pc, In pc L -> sl pc <> k) ->
  eget k (fold_left (fun E pc => eset (sl pc) E (f E pc)) L E) Xnan = eget k E Xnan.
Proof.
  intros sl L. induction L as [|pc L IH]; intros f E k H; [reflexivity|].
  change (fold_left (fun E pc => eset (sl pc) E (f E pc)) (pc :: L) E)
    with (fold_left (fun E pc => eset (sl pc) E (f E pc)) L (eset (sl pc) E (f E pc))).
  rewrite IH by (intros; apply H; right; assumption).
  apply eget_eset_neq. intros Heq. apply (H pc (or_introl eq_refl)). symmetry. exact Heq.
Qed.

Lemma jet_layer_slots : forall u v k, In k (map fst (jet_layer u v 0)) -> (3 <= k < 87)%nat.
Proof.
  intros u v k Hk. unfold jet_layer in Hk. rewrite map_map in Hk. apply in_map_iff in Hk.
  destruct Hk as [i [Ei Hi]]. apply in_seq in Hi. cbn [fst] in Ei. rewrite ntop_val in Hi. lia.
Qed.

Lemma Ez_high : forall r kp s h z k, (87 <= k)%nat -> eget k (Ez r kp s h z) Xnan = Xnan.
Proof.
  intros r kp s h z k Hk. unfold Ez.
  rewrite (fold_eset_other (fun pc => uslot (fst pc) (snd pc)) xdpc
             (fun E pc => Xreal (xr (eget (uslot (fst pc) (snd pc)) E Xnan) + z (uslot (fst pc) (snd pc)))))
    by (intros pc Hpc; assert (H := uslot_lt pc Hpc); lia).
  unfold Ex. rewrite eget_xextend_notin by (intros Hin; apply jet_layer_slots in Hin; lia).
  unfold pin. rewrite !eget_eset_neq by lia. apply eget_eempty.
Qed.

Section Box.

Variable prec : F.precision.
Variables (r : bool) (kp c : nat) (rx rd hhi : Z * Z).

Lemma box_env_ok :
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  env_ok (box_env prec (ival prec (clo c) (chi c)) (ival prec (0%Z, 0%Z) hhi)) (pin s h 0).
Proof.
  intros s h Hs Hh k. unfold box_env, pin.
  destruct (Nat.eq_dec k 2) as [->|H2]; [rewrite !eget_eset_eq; apply I.fromZ_correct|].
  rewrite !(eget_eset_neq _ 2) by exact H2.
  destruct (Nat.eq_dec k 1) as [->|H1].
  - rewrite !eget_eset_eq. apply ival_contains. replace (dyadR (0%Z, 0%Z)) with 0 by (unfold dyadR; cbn; ring). exact Hh.
  - rewrite !(eget_eset_neq _ 1) by exact H1. destruct (Nat.eq_dec k 0) as [->|H0].
    + rewrite !eget_eset_eq. apply ival_contains. exact Hs.
    + rewrite !(eget_eset_neq _ 0) by exact H0. rewrite !eget_eempty. rewrite I.nai_correct. exact I.
Qed.

(** Stated over an abstract slot function and radius: with the concrete
    slots in the statement, the kernel's check of the proof takes minutes. *)
Lemma widen_fold_gen :
  forall (sl : nat * nat -> nat) (sr : nat * nat -> I.type) L J E (z : nat -> R),
  (forall pc, In pc L -> contains (I.convert (sr pc)) (Xreal (z (sl pc)))) ->
  env_ok J E ->
  env_ok (fold_left (fun J pc => eset (sl pc) J (I.add prec (eget (sl pc) J I.nai) (sr pc))) L J)
         (fold_left (fun E pc => eset (sl pc) E (Xreal (xr (eget (sl pc) E Xnan) + z (sl pc)))) L E).
Proof.
  intros sl sr. induction L as [|pc L IH]; intros J E z Hz HJ; [exact HJ|].
  cbn [fold_left]. apply IH; [intros; apply Hz; right; assumption|].
  apply env_ok_eset; [exact HJ|].
  assert (HA := I.add_correct prec _ _ _ _ (HJ (sl pc)) (Hz pc (or_introl eq_refl))). revert HA.
  destruct (eget (sl pc) E Xnan) as [|a]; intros HA.
  - apply contains_nan_any. exact HA.
  - exact HA.
Qed.

Lemma ball_box :
  forall s h z, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  (forall pc, In pc xdpc -> Rabs (z (uslot (fst pc) (snd pc))) <= rad rx rd pc) ->
  env_ok (widen prec (jetbox prec (fst (pt r kp)) (snd (pt r kp)) (clo c) (chi c) hhi) rx rd) (Ez r kp s h z).
Proof.
  intros s h z Hs Hh Hz. unfold widen, Ez, jetbox, Ex.
  apply (widen_fold_gen (fun pc => uslot (fst pc) (snd pc)) (fun pc => sym prec (if Nat.eqb (fst pc) 0 then rx else rd))).
  - intros pc Hpc. apply sym_contains. assert (H := Hz pc Hpc). unfold rad in H.
    destruct (Nat.eqb (fst pc) 0); exact H.
  - apply iextend_correct. apply box_env_ok; assumption.
Qed.

(** What a passing check of the cell states at every point of its box: the
    tail is real there, and every tangent of an adjoint slot along a moved
    unknown is real and within K. *)
Theorem ball_sound :
  forall K, ball_cell_ok prec K rx rd hhi r (dtails r) kp c = true ->
  forall s h z, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  (forall pc, In pc xdpc -> Rabs (z (uslot (fst pc) (snd pc))) <= rad rx rd pc) ->
  tail_env (ab r) (ttop r) (tout r) (Ez r kp s h z) /\
  (forall l g, In l xdslots -> In g (gslots r) ->
     exists y, eget (g + length (tl r)) (xextend (Ez r kp s h z) (with_dseq l 87 (length (tl r)) (tl r))) Xnan = Xreal y /\
               Rabs y <= dyadR K).
Proof.
  intros K Hok s h z Hs Hh Hz.
  assert (HE := ball_box s h z Hs Hh Hz).
  remember (widen prec (jetbox prec (fst (pt r kp)) (snd (pt r kp)) (clo c) (chi c) hhi) rx rd) as E eqn:EE.
  unfold ball_cell_ok in Hok. cbv zeta in Hok. apply andb_prop in Hok. destruct Hok as [_ Hok].
  rewrite <- EE in Hok.
  destruct (ball_tab prec r (dtails r) E) as [T|] eqn:HT; [| discriminate].
  unfold ball_tab in HT. cbv zeta in HT.
  destruct (forallb (fun k => rb prec (eget k E I.nai)) (seq 0 87) &&
            forallb (fun k => rb prec (eget k (iextend prec E (tl r)) I.nai)) (seq 87 (length (tl r)))) eqn:H12;
    [| discriminate].
  apply andb_prop in H12. destruct H12 as [H1 H2]. rewrite forallb_forall in H1, H2.
  remember (map (fun bs => map (fun g => eget (g + length (tl r)) (iextend prec E bs) I.nai) (gslots r)) (dtails r))
    as T0 eqn:ET0.
  destruct (forallb (forallb (rb prec)) T0) eqn:H3; [| discriminate].
  injection HT as HT. rewrite forallb_forall in H3. rewrite <- HT, forallb_forall in Hok.
  split.
  - split; [| split].
    + intros k Hk. apply Ez_high. exact Hk.
    + intros k Hk. destruct (rb_sound prec _ _ (HE k) (H1 k ltac:(apply in_seq; lia))) as [y [Ey _]]. exists y. exact Ey.
    + intros k Hk. assert (HF := iextend_correct prec (tl r) E (Ez r kp s h z) HE k).
      rewrite <- tl_split in Hk.
      destruct (rb_sound prec _ _ HF (H2 k ltac:(apply in_seq; lia))) as [y [Ey _]]. exists y.
      rewrite <- tl_split. exact Ey.
  - intros l g Hl Hg.
    set (bs := with_dseq l 87 (length (tl r)) (tl r)).
    set (X := eget (g + length (tl r)) (iextend prec E bs) I.nai).
    set (row := map (fun g => eget (g + length (tl r)) (iextend prec E bs) I.nai) (gslots r)).
    assert (Hrow : In row T0).
    { rewrite ET0. unfold row. apply (in_map (fun bs => map (fun g => eget (g + length (tl r)) (iextend prec E bs) I.nai) (gslots r))).
      unfold bs, dtails. apply (in_map (fun l => with_dseq l 87 (length (tl r)) (tl r))). exact Hl. }
    assert (HX : In X row) by (unfold row, X; apply (in_map (fun g => eget (g + length (tl r)) (iextend prec E bs) I.nai)); exact Hg).
    assert (Hrb := H3 row Hrow). rewrite forallb_forall in Hrb.
    assert (HF := iextend_correct prec bs E (Ez r kp s h z) HE (g + length (tl r))%nat).
    destruct (rb_sound prec _ _ HF (Hrb X HX)) as [y [Ey Hy]].
    exists y. split; [exact Ey|].
    assert (Hrow' : In (map (ibound prec) row) (map (map (ibound prec)) T0)) by (apply in_map; exact Hrow).
    assert (Hk := Hok _ Hrow'). rewrite forallb_forall in Hk.
    assert (Hb := Hk (ibound prec X) (in_map _ _ _ HX)).
    assert (HB := le_bound_sound prec K _ _ (iupmax_in prec [I.abs X]) Hb).
    eapply Rle_trans; [exact Hy | exact HB].
Qed.

(** The exact jet's inputs are real over the cell. *)
Theorem jet_real :
  forall K, ball_cell_ok prec K rx rd hhi r (dtails r) kp c = true ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  forall k, (k < 87)%nat -> exists x, eget k (Ex r kp s h) Xnan = Xreal x.
Proof.
  intros K Hok s h Hs Hh k Hk. unfold ball_cell_ok in Hok. cbv zeta in Hok.
  apply andb_prop in Hok. destruct Hok as [H0 _]. rewrite forallb_forall in H0.
  assert (HJ : env_ok (jetbox prec (fst (pt r kp)) (snd (pt r kp)) (clo c) (chi c) hhi) (Ex r kp s h)).
  { unfold jetbox, Ex. apply iextend_correct. apply box_env_ok; assumption. }
  destruct (rb_sound prec _ _ (HJ k) (H0 k ltac:(apply in_seq; lia))) as [y [Ey _]]. exists y. exact Ey.
Qed.

End Box.
