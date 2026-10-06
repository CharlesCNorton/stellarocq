(** What the cell function's ranges enclose.

    At every point (sc + u, hc + w) of a cell, |u| <= a, |w| <= b, each block
    model of [cell_blocks] has the block's real value there ([blocks_sound]):
    the poloidal points' adjoint slots through TMEval.tmextend_correct, and
    the radial points' at s, at s + h and their divided difference through
    QDiff.QL_sound. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Cell Newton Mat IMat DerivSeq RegResidual Jet LinCheck
  TMEval TMat QDiff Recur Step Osc CellTM.

Import ListNotations.
Local Open Scope R_scope.

(** Conversion takes projections of explicit tuples before it reads an
    environment, so that no evaluation of a list is started. *)
#[local] Strategy expand [fst snd].
#[local] Strategy 1000 [eget tmextend xextend].

(** A bind that succeeds, read without reducing its argument: the cell's
    option values are never evaluated in a conversion. *)
Lemma obind_some :
  forall {A B : Type} (o : option A) (f : A -> option B) y,
  obind o f = Some y -> exists x, o = Some x /\ f x = Some y.
Proof. intros A B o f y H. destruct o as [x|]; [exists x; split; [reflexivity | exact H] | discriminate]. Qed.

Lemma forallb_nth_true :
  forall {A : Type} (f : A -> bool) (L : list A) k dflt, forallb f L = true -> (k < length L)%nat -> f (nth k L dflt) = true.
Proof.
  intros A f L k dflt H Hk. rewrite forallb_forall in H. apply H. apply nth_In. exact Hk.
Qed.

Section Sound.

Variable prec : F.precision.
Variable d : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.

Let tab : tmtab := mktab d.

(* ---------------------------------------------------------------- *)
(* The inputs                                                        *)

Lemma mrlo_ok :
  forall U W u w, contains (I.convert U) (Xreal u) -> contains (I.convert W) (Xreal w) ->
  forall k, (k < nmon d)%nat ->
  contains (I.convert (cget (mrlo_of prec d U W) k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w)).
Proof.
  intros U W u w HU HW k Hk. unfold cget.
  set (f := fun m : nat * nat => I.mul prec (ipow prec U (fst m)) (ipow prec W (snd m))).
  change (mrlo_of prec d U W) with (map f (mons d)).
  rewrite (nth_indep (map f (mons d)) I.zero (f (0%nat, 0%nat))) by (rewrite length_map; exact Hk).
  rewrite map_nth. unfold f, mval.
  apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); apply ipow_correct; assumption.
Qed.

Lemma cell_mrlo_ok :
  forall a b u w, Rabs u <= dyadR a -> Rabs w <= dyadR b ->
  forall k, (k < nmon d)%nat ->
  contains (I.convert (cget (cell_mrlo prec d a b) k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w)).
Proof.
  intros a b u w Ha Hb. unfold cell_mrlo. apply mrlo_ok.
  - apply (isym_correct _ (dyadR a)); [apply dyad_correct | exact Ha].
  - apply (isym_correct _ (dyadR b)); [apply dyad_correct | exact Hb].
Qed.

Lemma tenv_p_ok :
  forall u w ts th s h, tm_has d u w ts s -> tm_has d u w th h ->
  tenv_ok d u w (tenv_p d ts th) (pin s h 0).
Proof.
  intros u w ts th s h Hs Hh n. unfold tenv_p, pin.
  destruct (Nat.eq_dec n 2) as [->|N2].
  { rewrite !eget_eset_eq. cbn [otm_has]. exists 0. split; [reflexivity|].
    apply tconst_correct; [exact Hd | exact zero_contains]. }
  rewrite !(eget_eset_neq _ 2 n) by exact N2.
  destruct (Nat.eq_dec n 1) as [->|N1].
  { rewrite !eget_eset_eq. cbn [otm_has]. exists h. split; [reflexivity | exact Hh]. }
  rewrite !(eget_eset_neq _ 1 n) by exact N1.
  destruct (Nat.eq_dec n 0) as [->|N0].
  { rewrite !eget_eset_eq. cbn [otm_has]. exists s. split; [reflexivity | exact Hs]. }
  rewrite !(eget_eset_neq _ 0 n) by exact N0. rewrite eget_eempty. exact I.
Qed.

Lemma tenv_q_ok :
  forall u w ts tsh th s h, tm_has d u w ts s -> tm_has d u w tsh (s + h) -> tm_has d u w th h ->
  tenv_ok d u w (tenv_q prec d ts tsh th) (qin s h 0).
Proof.
  intros u w ts tsh th s h Hs Hsh Hh n. unfold tenv_q, qin. rewrite eget_of_list.
  assert (Z0 : tm_has d u w (tconst d I.zero) 0) by (apply tconst_correct; [exact Hd | exact zero_contains]).
  assert (Z1 : tm_has d u w (tconst d (I.fromZ prec 1)) 1) by (apply tconst_correct; [exact Hd | apply I.fromZ_correct]).
  destruct (Nat.lt_ge_cases n 9) as [Hn|Hn].
  - destruct n as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; try lia;
      rewrite ?eget_eset_neq by lia; rewrite eget_eset_eq; cbn [nth otm_has];
      first [exists 0; split; [reflexivity | exact Z0]
            | exists 1; split; [reflexivity | exact Z1]
            | exists s; split; [reflexivity | exact Hs]
            | exists (s + h); split; [reflexivity | exact Hsh]
            | exists h; split; [reflexivity | exact Hh]].
  - rewrite !eget_eset_neq by lia. rewrite eget_eempty. exact I.
Qed.

(* ---------------------------------------------------------------- *)
(* The blocks                                                        *)

Lemma out_sound :
  forall mrlo u w,
  (forall k, (k < nmon d)%nat -> contains (I.convert (cget mrlo k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w))) ->
  forall te E L k t,
  tenv_ok d u w te E -> eget k (tmextend prec d tab mrlo te L) None = Some t ->
  exists x, eget k (xextend E L) Xnan = Xreal x /\ tm_has d u w t x.
Proof.
  intros mrlo u w Hlo te E L k t Hte Ht.
  assert (H := tmextend_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd L te E Hte k).
  rewrite Ht in H. exact H.
Qed.

Lemma ofull_tab :
  forall np (g : nat -> nat -> otm) T,
  ofull d (map (fun i => map (fun j => g i j) (seq 0 9)) (seq 0 np)) = Some T ->
  forall i j, (i < np)%nat -> (j < 9)%nat -> g i j = Some (tget d T i j).
Proof.
  intros np g T H i j Hi Hj. unfold ofull in H.
  destruct (forallb (forallb osome) (map (fun i => map (fun j => g i j) (seq 0 9)) (seq 0 np))) eqn:Hall;
    [|discriminate].
  assert (HT : T = map (map (oval d)) (map (fun i => map (fun j => g i j) (seq 0 9)) (seq 0 np))) by congruence.
  subst T. unfold tget.
  rewrite (nth_indep _ [] (map (oval d) [])) by (rewrite !length_map, length_seq; exact Hi).
  rewrite map_nth, nth_map_seq_lt by exact Hi.
  rewrite (nth_indep _ (tz d) (oval d None)) by (rewrite !length_map, length_seq; exact Hj).
  rewrite map_nth, nth_map_seq_lt by exact Hj. cbv beta.
  rewrite forallb_forall in Hall.
  assert (Hrow : forallb osome (map (fun j => g i j) (seq 0 9)) = true).
  { apply Hall. apply (in_map (fun i0 => map (fun j0 => g i0 j0) (seq 0 9)) (seq 0 np) i). apply in_seq. lia. }
  rewrite forallb_forall in Hrow.
  assert (Hij : osome (g i j) = true).
  { apply Hrow. apply (in_map (fun j0 => g i j0) (seq 0 9) j). apply in_seq. lia. }
  unfold oval. destruct (g i j); [reflexivity | discriminate].
Qed.

(** A block of the radial lists, entry by entry. *)
Lemma rblk_tab :
  forall mrlo te f part,
  rblk (renvs prec d tab mrlo te) f part
  = map (fun i => map (fun j => eget (f (aslot_in true part j)) (tmextend prec d tab mrlo te (qlist i)) None)
                      (seq 0 9)) (seq 0 5).
Proof.
  intros mrlo te f part. unfold rblk. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  apply map_ext. intros j. unfold renvs. rewrite nth_map_seq_lt by lia. reflexivity.
Qed.

Lemma pblk_tab :
  forall mrlo te part,
  pblk (penvs prec d tab mrlo te) part
  = map (fun i => map (fun j => eget (aslot_in false part j) (tmextend prec d tab mrlo te (plist false i)) None)
                      (seq 0 9)) (seq 0 4).
Proof.
  intros mrlo te part. unfold pblk. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  apply map_ext. intros j. unfold penvs. rewrite nth_map_seq_lt by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* At a point of the cell                                            *)

(** The radial lists are well formed, and the adjoint slots lie inside
    them. *)
Hypothesis Hwf_r : forall kp, (kp < 5)%nat -> Deriv.well_formed 3 (plist true kp) = true.
Hypothesis Hin_r : forall kp part c, (kp < 5)%nat -> (part < 4)%nat -> (c < 9)%nat ->
  (3 <= aslot_in true part c < 3 + length (plist true kp))%nat.

Section Point.

Variables mrlo : list I.type.
Variables u w : R.
Hypothesis Hlo : forall k, (k < nmon d)%nat ->
  contains (I.convert (cget mrlo k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w)).
Variables ts th : tm.
Variables s h : R.
Hypothesis Hs : tm_has d u w ts s.
Hypothesis Hh : tm_has d u w th h.

Lemma Hsh : tm_has d u w (tadd prec d ts th) (s + h).
Proof. apply tadd_correct; assumption. Qed.

(** A poloidal entry: the partial at (s, h). *)
Lemma pol_entry :
  forall kp part c t,
  eget (aslot_in false part c) (tmextend prec d tab mrlo (tenv_p d ts th) (plist false kp)) None = Some t ->
  tm_has d u w t (pval false kp part c s h).
Proof.
  intros kp part c t Ht.
  destruct (out_sound mrlo u w Hlo _ (pin s h 0) _ _ _ (tenv_p_ok u w ts th s h Hs Hh) Ht) as [x [Hx Hxt]].
  unfold pval. rewrite Hx. exact Hxt.
Qed.

(** A radial entry: the partial at s, at s + h, and their difference over h,
    from the three layers of the tripled list. *)
Lemma rad_entry :
  forall kp part c, (kp < 5)%nat -> (part < 4)%nat -> (c < 9)%nat ->
  let F := tmextend prec d tab mrlo (tenv_q prec d ts (tadd prec d ts th) th) (qlist kp) in
  (forall t, eget (lm (aslot_in true part c)) F None = Some t -> tm_has d u w t (pval true kp part c s h)) /\
  (forall t, eget (lp (aslot_in true part c)) F None = Some t -> tm_has d u w t (pval true kp part c (s + h) h)) /\
  (forall tm tp t, eget (lm (aslot_in true part c)) F None = Some tm ->
     eget (lp (aslot_in true part c)) F None = Some tp ->
     eget (ld (aslot_in true part c)) F None = Some t -> 0 < h ->
     tm_has d u w t ((pval true kp part c (s + h) h - pval true kp part c s h) / h)).
Proof.
  intros kp part c Hkp Hpart Hc F.
  set (n := aslot_in true part c).
  assert (Hwf := Hwf_r kp Hkp).
  assert (Hn : (3 <= n < 3 + length (plist true kp))%nat) by exact (Hin_r kp part c Hkp Hpart Hc).
  assert (Hte := tenv_q_ok u w ts (tadd prec d ts th) th s h Hs Hsh Hh).
  destruct (QL_sound (plist true kp) Hwf s h 0 n Hn) as [Qm [Qp Qd]].
  set (Q := QL_with (fxenv q_in (plist true kp)) (plist true kp)) in Qm, Qp, Qd.
  assert (Em : forall x, eget (lm n) (xextend (qin s h 0) Q) Xnan = Xreal x -> pval true kp part c s h = x).
  { intros x Hx. unfold pval. fold n. rewrite <- Qm, Hx. reflexivity. }
  assert (Ep : forall x, eget (lp n) (xextend (qin s h 0) Q) Xnan = Xreal x -> pval true kp part c (s + h) h = x).
  { intros x Hx. unfold pval. fold n. rewrite <- Qp, Hx. reflexivity. }
  split; [| split].
  - intros t Ht. destruct (out_sound mrlo u w Hlo _ _ _ _ t Hte Ht) as [x [Hx Hxt]].
    unfold qlist in Hx. fold Q in Hx. rewrite (Em x Hx). exact Hxt.
  - intros t Ht. destruct (out_sound mrlo u w Hlo _ _ _ _ t Hte Ht) as [x [Hx Hxt]].
    unfold qlist in Hx. fold Q in Hx. rewrite (Ep x Hx). exact Hxt.
  - intros tm tp t Htm Htp Ht Hpos.
    destruct (out_sound mrlo u w Hlo _ _ _ _ tm Hte Htm) as [xm [Hxm _]].
    destruct (out_sound mrlo u w Hlo _ _ _ _ tp Hte Htp) as [xp [Hxp _]].
    destruct (out_sound mrlo u w Hlo _ _ _ _ t Hte Ht) as [xd [Hxd Hxdt]].
    unfold qlist in Hxm, Hxp, Hxd. fold Q in Hxm, Hxp, Hxd.
    assert (Hrel := Qd xm xp xd Hxm Hxp Hxd).
    rewrite (Em xm Hxm), (Ep xp Hxp).
    replace ((xp - xm) / h) with xd by (rewrite Hrel; field; lra). exact Hxdt.
Qed.

(** The eight block models come out of eight full tables. *)
Lemma blocks_of_eqs :
  forall Fs Gs B, blocks_of d Fs Gs = Some B ->
  ofull d (rblk Fs lm 0) = Some (b_Rx B) /\
  ofull d (rblk Fs lm 2) = Some (b_Rdp B) /\
  ofull d (rblk Fs lp 1) = Some (b_Rdm' B) /\
  ofull d (pblk Gs 0) = Some (b_Ux B) /\
  ofull d (pblk Gs 2) = Some (b_Up B) /\
  ofull d (rblk Fs lm 3) = Some (b_Re B) /\
  ofull d (rblk Fs lp 3) = Some (b_Rep B) /\
  ofull d (rblk Fs ld 3) = Some (b_DD B).
Proof.
  intros Fs Gs B HB. unfold blocks_of in HB.
  destruct (obind_some _ _ _ HB) as [Rx [E1 H1]]. clear HB.
  destruct (obind_some _ _ _ H1) as [Rdp [E2 H2]]. clear H1.
  destruct (obind_some _ _ _ H2) as [Rdm' [E3 H3]]. clear H2.
  destruct (obind_some _ _ _ H3) as [Ux [E4 H4]]. clear H3.
  destruct (obind_some _ _ _ H4) as [Up [E5' H5]]. clear H4.
  destruct (obind_some _ _ _ H5) as [Re [E6 H6]]. clear H5.
  destruct (obind_some _ _ _ H6) as [Rep [E7 H7]]. clear H6.
  destruct (obind_some _ _ _ H7) as [DD [E8 H8]]. clear H7.
  injection H8 as <-. cbn [b_Rx b_Rdp b_Rdm' b_Ux b_Up b_Re b_Rep b_DD].
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  split; [exact E5'|]. split; [exact E6|]. split; [exact E7|]. exact E8.
Qed.

Let F' (kp : nat) : env otm := tmextend prec d tab mrlo (tenv_q prec d ts (tadd prec d ts th) th) (qlist kp).

(** A radial block through layer f, entry by entry. *)
Lemma rad_block :
  forall f part T, (part < 4)%nat ->
  ofull d (rblk (renvs prec d tab mrlo (tenv_q prec d ts (tadd prec d ts th) th)) f part) = Some T ->
  forall i c, (i < 5)%nat -> (c < 9)%nat -> eget (f (aslot_in true part c)) (F' i) None = Some (tget d T i c).
Proof.
  intros f part T Hp HT i c Hi Hc. rewrite rblk_tab in HT.
  exact (ofull_tab 5 (fun i j => eget (f (aslot_in true part j)) (F' i) None) T HT i c Hi Hc).
Qed.

(** Every block model has the block at the point. *)
Theorem blocks_sound :
  forall B, cell_blocks prec d tab mrlo ts th = Some B ->
  tmhas d u w 5 9 (b_Rx B) (fun i c => pval true i 0 c s h) /\
  tmhas d u w 5 9 (b_Rdp B) (fun i c => pval true i 2 c s h) /\
  tmhas d u w 5 9 (b_Rdm' B) (fun i c => pval true i 1 c (s + h) h) /\
  tmhas d u w 4 9 (b_Ux B) (fun i c => pval false i 0 c s h) /\
  tmhas d u w 4 9 (b_Up B) (fun i c => pval false i 2 c s h) /\
  tmhas d u w 5 9 (b_Re B) (fun i c => pval true i 3 c s h) /\
  tmhas d u w 5 9 (b_Rep B) (fun i c => pval true i 3 c (s + h) h) /\
  (0 < h -> tmhas d u w 5 9 (b_DD B) (fun i c => (pval true i 3 c (s + h) h - pval true i 3 c s h) / h)).
Proof.
  intros B HB. unfold cell_blocks in HB.
  destruct (blocks_of_eqs _ _ B HB) as (E1 & E2 & E3 & E4 & E5' & E6 & E7 & E8).
  assert (P0 : forall part T, (part < 4)%nat ->
            ofull d (pblk (penvs prec d tab mrlo (tenv_p d ts th)) part) = Some T ->
            tmhas d u w 4 9 T (fun i c => pval false i part c s h)).
  { intros part T Hp HT i c Hi Hc. rewrite pblk_tab in HT.
    assert (Hg := ofull_tab 4 (fun i j => eget (aslot_in false part j)
                    (tmextend prec d tab mrlo (tenv_p d ts th) (plist false i)) None) T HT i c Hi Hc).
    exact (pol_entry i part c _ Hg). }
  split; [intros i c Hi Hc; exact (proj1 (rad_entry i 0 c Hi ltac:(lia) Hc) _ (rad_block lm 0 _ ltac:(lia) E1 i c Hi Hc))|].
  split; [intros i c Hi Hc; exact (proj1 (rad_entry i 2 c Hi ltac:(lia) Hc) _ (rad_block lm 2 _ ltac:(lia) E2 i c Hi Hc))|].
  split; [intros i c Hi Hc;
          exact (proj1 (proj2 (rad_entry i 1 c Hi ltac:(lia) Hc)) _ (rad_block lp 1 _ ltac:(lia) E3 i c Hi Hc))|].
  split; [exact (P0 0%nat _ ltac:(lia) E4)|].
  split; [exact (P0 2%nat _ ltac:(lia) E5')|].
  split; [intros i c Hi Hc; exact (proj1 (rad_entry i 3 c Hi ltac:(lia) Hc) _ (rad_block lm 3 _ ltac:(lia) E6 i c Hi Hc))|].
  split; [intros i c Hi Hc;
          exact (proj1 (proj2 (rad_entry i 3 c Hi ltac:(lia) Hc)) _ (rad_block lp 3 _ ltac:(lia) E7 i c Hi Hc))|].
  intros Hpos i c Hi Hc.
  exact (proj2 (proj2 (rad_entry i 3 c Hi ltac:(lia) Hc)) _ _ _
           (rad_block lm 3 _ ltac:(lia) E6 i c Hi Hc) (rad_block lp 3 _ ltac:(lia) E7 i c Hi Hc)
           (rad_block ld 3 _ ltac:(lia) E8 i c Hi Hc) Hpos).
Qed.

End Point.

End Sound.
