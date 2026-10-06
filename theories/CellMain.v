(** The cell function's verdicts.

    [cell_range_sound]: when [cell_range] returns ranges R for the cell
    s in sc +- a, h in hc +- b and a frame W whose inverse WiI encloses, then
    at every point of the cell with h > 0 the matrix M = [Pp; Up] is
    invertible and R encloses W N W^-1 entrywise. [start_range_sound]: when
    [start_range] returns ranges R for the steps h in hc +- b, R encloses the
    start rows [Pm(1/4 + h, h), -h I] (I + h N(1/4, h)) W^-1 at every such
    h > 0. The adjoint lists of the radial points are well formed and hold
    the slots the cell reads ([plist_r_wf], [aslot_r_in]), each checked
    once by computation. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Cell Newton Mat IMat DerivSeq RegResidual Jet LinCheck
  TMEval TMat QDiff Recur Step Osc CellTM CellSound CellN.

Import ListNotations.
Local Open Scope R_scope.

#[local] Strategy expand [fst snd].
#[local] Strategy 1000 [eget tmextend xextend].

(* ---------------------------------------------------------------- *)
(* The lists are well formed                                         *)

Lemma plists_r_wf : forallb (fun kp => Deriv.well_formed 3 (plist true kp)) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plist_r_wf : forall kp, (kp < 5)%nat -> Deriv.well_formed 3 (plist true kp) = true.
Proof.
  intros kp Hkp. assert (H := plists_r_wf). rewrite forallb_forall in H.
  exact (H kp ltac:(apply in_seq; lia)).
Qed.

Lemma aslots_r_in :
  forallb (fun kp => forallb (fun pc => let n := aslot_in true (fst pc) (snd pc) in
                                        Nat.leb 3 n && Nat.ltb n (3 + length (plist true kp)))
                             (list_prod (seq 0 4) (seq 0 9))) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma aslot_r_in :
  forall kp part c, (kp < 5)%nat -> (part < 4)%nat -> (c < 9)%nat ->
  (3 <= aslot_in true part c < 3 + length (plist true kp))%nat.
Proof.
  intros kp part c Hkp Hp Hc.
  assert (H := aslots_r_in). rewrite forallb_forall in H.
  specialize (H kp ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  specialize (H (part, c) ltac:(apply in_prod; apply in_seq; lia)). cbn [fst snd] in H.
  apply andb_prop in H. destruct H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The verdicts                                                      *)

Section Main.

Variable prec : F.precision.
Variable d : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.

Let tab : tmtab := mktab d.

(** What a successful cell computation carries at each point of its cell. *)
Lemma cell_core_sound :
  forall sc hc a b kn mrlo th NT B,
  cell_core prec d tab sc hc a b kn = Some (mrlo, th, NT, B) ->
  forall u w, Rabs u <= dyadR a -> Rabs w <= dyadR b -> 0 < dyadR hc + w ->
  let s := dyadR sc + u in let h := dyadR hc + w in
  (forall k, (k < nmon d)%nat ->
     contains (I.convert (cget mrlo k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w))) /\
  tm_has d u w th h /\
  (exists X, is_inv 9 (mstack (bPp s h) (bUp s h)) X) /\
  tmhas d u w 14 14 NT (bN s h) /\
  tmhas d u w 5 9 (b_Rep B) (fun i c => pval true i 3 c (s + h) h) /\
  tmhas d u w 5 9 (b_Rdm' B) (fun i c => pval true i 1 c (s + h) h).
Proof.
  intros sc hc a b kn mrlo th NT B HC u w Ha Hb Hpos s h.
  unfold cell_core in HC.
  destruct (obind_some _ _ _ HC) as [B0 [HB0 H1]]. clear HC.
  destruct (obind_some _ _ _ H1) as [N0 [HN0 H2]]. clear H1.
  injection H2 as Em Et EN EB. subst mrlo th NT B.
  set (mrlo := cell_mrlo prec d a b) in *.
  set (th := tvar_w prec d (Newton.dyad prec hc)) in *.
  set (ts := tvar_u prec d (Newton.dyad prec sc)) in *.
  assert (Hlo := cell_mrlo_ok prec d a b u w Ha Hb).
  fold mrlo in Hlo.
  assert (Hs : tm_has d u w ts s)
    by exact (tvar_u_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd _ _ (dyad_correct prec sc)).
  assert (Hh : tm_has d u w th h) by exact (tvar_w_correct prec d u w Hd _ _ (dyad_correct prec hc)).
  destruct (blocks_sound prec d Hcov Hd plist_r_wf aslot_r_in mrlo u w Hlo ts th s h Hs Hh B0 HB0)
    as (HRx & HRdp & HRdm & HUx & HUp & HRe & HRep & HDD).
  destruct (t_N_sound prec d Hcov Hd mrlo u w Hlo th s h Hh Hpos B0 HRx HRdp HRdm HUx HUp HRe (HDD Hpos) kn N0 HN0)
    as [Hinv HN].
  split; [exact Hlo|]. split; [exact Hh|]. split; [exact Hinv|]. split; [exact HN|]. split; [exact HRep | exact HRdm].
Qed.

Theorem cell_range_sound :
  forall sc hc a b kn W WiI RW (Wi : mat),
  cell_range prec d tab sc hc a b kn W WiI = Some RW -> icont 14 14 WiI Wi ->
  forall u w, Rabs u <= dyadR a -> Rabs w <= dyadR b -> 0 < dyadR hc + w ->
  (exists X, is_inv 9 (mstack (bPp (dyadR sc + u) (dyadR hc + w)) (bUp (dyadR sc + u) (dyadR hc + w))) X) /\
  icont 14 14 RW (mm 14 (mm 14 (dmatR W) (bN (dyadR sc + u) (dyadR hc + w))) Wi).
Proof.
  intros sc hc a b kn W WiI RW Wi HR HWi u w Ha Hb Hpos.
  unfold cell_range in HR.
  destruct (obind_some _ _ _ HR) as [[[[mrlo th] NT] B] [HC H1]]. clear HR.
  cbv beta iota in H1. injection H1 as <-.
  destruct (cell_core_sound sc hc a b kn mrlo th NT B HC u w Ha Hb Hpos)
    as (Hlo & Hh & Hinv & HN & _ & _).
  split; [exact Hinv|].
  apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd).
  apply (tmc_correct prec d u w Hd); [| exact HWi].
  apply (tcm_correct prec d u w Hd); [apply idmat_correct | exact HN].
Qed.

(** The ranges of the parts of the cell's s-interval: at every point of
    part q, range q encloses W N W^-1. *)
Theorem cell_ranges_sound :
  forall sc hc a b kn p W WiI RR (Wi : mat),
  cell_ranges prec d tab sc hc a b kn p W WiI = Some RR -> icont 14 14 WiI Wi ->
  forall q u w, (q < 2 ^ p)%nat ->
  Rabs (u - dyadR (ucen a p q)) <= dyadR (urad a p) ->
  Rabs u <= dyadR a -> Rabs w <= dyadR b -> 0 < dyadR hc + w ->
  (exists X, is_inv 9 (mstack (bPp (dyadR sc + u) (dyadR hc + w)) (bUp (dyadR sc + u) (dyadR hc + w))) X) /\
  icont 14 14 (nth q RR []) (mm 14 (mm 14 (dmatR W) (bN (dyadR sc + u) (dyadR hc + w))) Wi).
Proof.
  intros sc hc a b kn p W WiI RR Wi HR HWi q u w Hq Hsub Ha Hb Hpos.
  unfold cell_ranges in HR.
  destruct (obind_some _ _ _ HR) as [[[[mrlo th] NT] B] [HC H1]]. clear HR.
  cbv beta iota in H1. injection H1 as <-.
  destruct (cell_core_sound sc hc a b kn mrlo th NT B HC u w Ha Hb Hpos)
    as (Hlo & Hh & Hinv & HN & _ & _).
  split; [exact Hinv|].
  rewrite nth_map_seq_lt by exact Hq.
  assert (Hlo' : forall k, (k < nmon d)%nat ->
            contains (I.convert (cget (sub_mrlo prec d a b p q) k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w))).
  { unfold sub_mrlo. apply mrlo_ok.
    - replace u with (dyadR (ucen a p q) + (u - dyadR (ucen a p q))) by ring.
      apply (I.add_correct prec _ _ (Xreal _) (Xreal _)); [apply dyad_correct|].
      apply (isym_correct _ (dyadR (urad a p))); [apply dyad_correct | exact Hsub].
    - apply (isym_correct _ (dyadR b)); [apply dyad_correct | exact Hb]. }
  apply (tmrange_correct prec d tab (sub_mrlo prec d a b p q) u w Hlo' eq_refl Hcov Hd).
  apply (tmc_correct prec d u w Hd); [| exact HWi].
  apply (tcm_correct prec d u w Hd); [apply idmat_correct | exact HN].
Qed.

Lemma le_dy_sound : forall K X x, contains (I.convert X) (Xreal x) -> le_dy prec K X = true -> x <= dyadR K.
Proof.
  intros K X x HX H. unfold le_dy in H.
  destruct (nonneg_correct _ _ (I.sub_correct prec _ _ _ _ (dyad_correct prec K) HX) H) as [r1 [E1 H1]].
  injection E1 as E1. lra.
Qed.

(** [cell_ranges2] returns what [cell_ranges] returns, and at every point
    of the cell with h > 0 it bounds |M^-1|, |M| and |Q| by BM, BMM and BQ. *)
Theorem cell_ranges2_sound :
  forall sc hc a b kn p W WiI BM BMM BQ RR,
  cell_ranges2 prec d tab sc hc a b kn p W WiI BM BMM BQ = Some RR ->
  cell_ranges prec d tab sc hc a b kn p W WiI = Some RR /\
  (forall u w, Rabs u <= dyadR a -> Rabs w <= dyadR b -> 0 < dyadR hc + w ->
   mnorm 9 9 (Mi (bPp (dyadR sc + u) (dyadR hc + w)) (bUp (dyadR sc + u) (dyadR hc + w))) <= dyadR BM /\
   mnorm 9 9 (mstack (bPp (dyadR sc + u) (dyadR hc + w)) (bUp (dyadR sc + u) (dyadR hc + w))) <= dyadR BMM /\
   mnorm 5 9 (Qm (dyadR hc + w) (bPp (dyadR sc + u) (dyadR hc + w))
                 (bPm (dyadR sc + u + (dyadR hc + w)) (dyadR hc + w))) <= dyadR BQ).
Proof.
  intros sc hc a b kn p W WiI BM BMM BQ RR HR.
  unfold cell_ranges2 in HR.
  destruct (obind_some _ _ _ HR) as [[[[mrlo th] NT] B] [HC H1]]. clear HR.
  cbv beta iota in H1.
  destruct (obind_some _ _ _ H1) as [[[bMi bM] bQ] [HB H2]]. clear H1.
  cbv beta iota zeta in H2.
  destruct (if_some _ _ _ H2) as [Hle HRR]. clear H2.
  split.
  - unfold cell_ranges. rewrite HC. cbn [obind]. f_equal. exact HRR.
  - intros u w Ha Hb Hpos.
    unfold cell_core in HC.
    destruct (obind_some _ _ _ HC) as [B0 [HB0 H1]]. clear HC.
    destruct (obind_some _ _ _ H1) as [N0 [HN0 H2]]. clear H1.
    injection H2 as Em Et EN EB. subst mrlo th NT B.
    set (mrlo := cell_mrlo prec d a b) in *.
    set (th := tvar_w prec d (Newton.dyad prec hc)) in *.
    set (ts := tvar_u prec d (Newton.dyad prec sc)) in *.
    assert (Hlo := cell_mrlo_ok prec d a b u w Ha Hb). fold mrlo in Hlo.
    assert (Hs : tm_has d u w ts (dyadR sc + u))
      by exact (tvar_u_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd _ _ (dyad_correct prec sc)).
    assert (Hh : tm_has d u w th (dyadR hc + w)) by exact (tvar_w_correct prec d u w Hd _ _ (dyad_correct prec hc)).
    destruct (blocks_sound prec d Hcov Hd plist_r_wf aslot_r_in mrlo u w Hlo ts th _ _ Hs Hh B0 HB0)
      as (HRx & HRdp & HRdm & HUx & HUp & HRe & HRep & HDD).
    destruct (t_Mb_sound prec d Hcov Hd mrlo u w Hlo th _ _ Hh Hpos B0 HRdp HRdm HUp HRe (HDD Hpos) bMi bM bQ HB)
      as [[x1 [Hx1 N1]] [[x2 [Hx2 N2]] [x3 [Hx3 N3]]]].
    apply andb_prop in Hle. destruct Hle as [Hle H3]. apply andb_prop in Hle. destruct Hle as [H1 H2].
    split; [| split].
    + eapply Rle_trans; [exact N1 | exact (le_dy_sound _ _ _ Hx1 H1)].
    + eapply Rle_trans; [exact N2 | exact (le_dy_sound _ _ _ Hx2 H2)].
    + eapply Rle_trans; [exact N3 | exact (le_dy_sound _ _ _ Hx3 H3)].
Qed.

Lemma dyad_quarter : dyadR (1%Z, (-2)%Z) = / 4.
Proof. unfold dyadR. cbn [fst snd]. simpl. field. Qed.

Theorem start_range_sound :
  forall hc b kn WiI RS (Wi : mat),
  start_range prec d tab hc b kn WiI = Some RS -> icont 14 14 WiI Wi ->
  forall w, Rabs w <= dyadR b -> 0 < dyadR hc + w ->
  icont 5 14 RS (mm 14 (bCs (/ 4) (dyadR hc + w)) Wi).
Proof.
  intros hc b kn WiI RS Wi HR HWi w Hb Hpos.
  unfold start_range in HR.
  destruct (obind_some _ _ _ HR) as [[[[mrlo th] NT] B] [HC H1]]. clear HR.
  cbv beta iota in H1. injection H1 as <-.
  assert (Ha : Rabs 0 <= dyadR (0%Z, 0%Z)) by (rewrite Rabs_R0; unfold dyadR; cbn [fst snd]; lra).
  destruct (cell_core_sound _ hc _ b kn mrlo th NT B HC 0 w Ha Hb Hpos) as (Hlo & Hh & _ & HN & HRep & HRdm).
  rewrite dyad_quarter, Rplus_0_r in HN, HRep, HRdm.
  set (h := dyadR hc + w) in *.
  apply (tmrange_correct prec d tab mrlo 0 w Hlo eq_refl Hcov Hd).
  apply (tmc_correct prec d 0 w Hd); [| exact HWi].
  unfold bCs. apply (tmm_correct prec d tab mrlo 0 w Hlo eq_refl Hcov Hd).
  - intros i c Hi Hc. unfold t_C. rewrite tget_ttab by assumption. unfold bC, bPm.
    destruct (Nat.ltb_spec c 9) as [H9|H9].
    + apply tsub_correct; [apply HRep; assumption|].
      apply (tmul_correct prec d tab mrlo 0 w Hlo eq_refl Hcov Hd); [exact Hh | apply HRdm; assumption].
    + destruct (Nat.eqb (c - 9) i).
      * apply tneg_correct. exact Hh.
      * apply tz_correct. exact Hd.
  - intros i c Hi Hc. unfold t_Psi. rewrite tget_ttab by assumption.
    apply tadd_correct.
    + apply (tId_sound prec d Hd 0 w 14); assumption.
    + apply (tmul_correct prec d tab mrlo 0 w Hlo eq_refl Hcov Hd); [exact Hh | apply HN; assumption].
Qed.

End Main.
