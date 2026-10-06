(** What the cell function's step matrix encloses.

    At a point of the cell with h > 0, given models of the blocks
    ([CellSound.blocks_sound]), [t_N_sound]: M = [Pp; Up] is invertible, and
    the model of N has N = Step.Nmat at the point. The preconditioned matrix
    I - P M and I - M P are within th0 < 1 of zero by their ranges, so M has
    an inverse (Mat.approx_inverse) equal to (I - E)^-1 P; the Neumann sum
    with its tail (TMat.neu_tail) has M^-1 [SV E5], whose rows are N's first
    nine, and Q M^-1 [SV E5] less [Sx 0] gives the last five. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Cell Newton Mat IMat DerivSeq RegResidual Jet LinCheck
  TMEval TMat QDiff Recur Step Osc CellTM CellSound.

Import ListNotations.
Local Open Scope R_scope.

#[local] Strategy expand [fst snd].
#[local] Strategy 1000 [eget tmextend xextend].

Lemma if_some :
  forall {A : Type} (b : bool) (x y : A), (if b then Some x else None) = Some y -> b = true /\ x = y.
Proof. intros A b x y H. destruct b; [injection H as ->; split; reflexivity | discriminate]. Qed.

Lemma triple_eq :
  forall {A B C : Type} (a a' : A) (b b' : B) (c c' : C), (a, b, c) = (a', b', c') -> a = a' /\ b = b' /\ c = c'.
Proof. intros A B C a a' b b' c c' H. injection H as -> -> ->. split; [| split]; reflexivity. Qed.

Section N.

Variable prec : F.precision.
Variable d : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Let tab : tmtab := mktab d.

Variables mrlo : list I.type.
Variables u w : R.
Hypothesis Hlo : forall k, (k < nmon d)%nat ->
  contains (I.convert (cget mrlo k)) (Xreal (mval (nth k (mons d) (0%nat, 0%nat)) u w)).
Variables th : tm.
Variables s h : R.
Hypothesis Hh : tm_has d u w th h.
Hypothesis Hpos : 0 < h.
Variable B : blocks.
Hypothesis HRx : tmhas d u w 5 9 (b_Rx B) (fun i c => pval true i 0 c s h).
Hypothesis HRdp : tmhas d u w 5 9 (b_Rdp B) (fun i c => pval true i 2 c s h).
Hypothesis HRdm : tmhas d u w 5 9 (b_Rdm' B) (fun i c => pval true i 1 c (s + h) h).
Hypothesis HUx : tmhas d u w 4 9 (b_Ux B) (fun i c => pval false i 0 c s h).
Hypothesis HUp : tmhas d u w 4 9 (b_Up B) (fun i c => pval false i 2 c s h).
Hypothesis HRe : tmhas d u w 5 9 (b_Re B) (fun i c => pval true i 3 c s h).
Hypothesis HDD : tmhas d u w 5 9 (b_DD B) (fun i c => (pval true i 3 c (s + h) h - pval true i 3 c s h) / h).

Let tmul' := tmul_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd.

(* ---------------------------------------------------------------- *)
(* The assembled blocks                                              *)

Definition rM : mat := mstack (bPp s h) (bUp s h).
Definition rSVE : mat := fun i c => if Nat.ltb c 9 then SV h (bSx s h) (bV s h) i c else E5 i (c - 9)%nat.
Definition rQ : mat := Qm h (bPp s h) (bPm (s + h) h).

Lemma tPp_sound : tmhas d u w 5 9 (t_Pp prec d tab mrlo th B) (bPp s h).
Proof.
  intros i c Hi Hc. unfold t_Pp. rewrite tget_ttab by assumption. unfold bPp.
  apply tadd_correct; [apply HRe; assumption|]. apply tmul'; [exact Hh | apply HRdp; assumption].
Qed.

Lemma tQ_sound : tmhas d u w 5 9 (t_Q prec d B) rQ.
Proof.
  intros i c Hi Hc. unfold t_Q. rewrite tget_ttab by assumption.
  replace (rQ i c) with ((pval true i 3 c (s + h) h - pval true i 3 c s h) / h
                         - pval true i 1 c (s + h) h - pval true i 2 c s h)
    by (unfold rQ, Qm, bPm, bPp; field; lra).
  apply tsub_correct; [apply tsub_correct|]; [apply HDD | apply HRdm | apply HRdp]; assumption.
Qed.

Lemma tM_sound : tmhas d u w 9 9 (t_M prec d tab mrlo th B) rM.
Proof.
  intros i c Hi Hc. unfold t_M, rM, mstack. rewrite tget_ttab by assumption.
  destruct (Nat.ltb_spec i 5) as [H5|H5].
  - apply tPp_sound; assumption.
  - unfold bUp. apply HUp; lia.
Qed.

Lemma tSVE_sound : tmhas d u w 9 14 (t_SVE prec d tab mrlo th B) rSVE.
Proof.
  intros i c Hi Hc. unfold t_SVE, rSVE. rewrite tget_ttab by assumption.
  destruct (Nat.ltb_spec c 9) as [H9|H9].
  - unfold SV, mstack. destruct (Nat.ltb_spec i 5) as [H5|H5].
    + apply tneg_correct. apply tmul'; [exact Hh | apply HRx; assumption].
    + apply tneg_correct. unfold bV. apply HUx; lia.
  - unfold E5, mI. destruct (Nat.ltb_spec i 5) as [H5|H5]; cbn [andb].
    + destruct (Nat.eqb_spec (c - 9) i) as [E|E].
      * rewrite E, Nat.eqb_refl. apply tconst_correct; [exact Hd | apply I.fromZ_correct].
      * replace (Nat.eqb i (c - 9)) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply tz_correct. exact Hd.
    + apply tz_correct. exact Hd.
Qed.

Lemma tId_sound : forall n, tmhas d u w n n (t_Id prec d n) mI.
Proof.
  intros n i c Hi Hc. unfold t_Id. rewrite tget_ttab by assumption.
  apply tconst_correct; [exact Hd|]. unfold mI. destruct (Nat.eqb i c); apply I.fromZ_correct.
Qed.

Definition rP (M : tmat) : mat :=
  fun i c => proj_val (I.convert_bound
    (fget (finv 9 (map (fun i => map (fun c => I.midpoint (cget (tpoly (tget d M i c)) 0)) (seq 0 9)) (seq 0 9))) i c)).

Lemma tP_cont : forall M, icont 9 9 (t_P d M) (rP M).
Proof. intros M. unfold t_P. apply itab_correct. intros i c _ _. apply I.singleton_correct. Qed.

Lemma iupmax_point : forall L, exists x, contains (I.convert (iupmax prec L)) (Xreal x).
Proof. intros L. unfold iupmax. eexists. apply I.singleton_correct. Qed.

(* ---------------------------------------------------------------- *)
(* The step matrix                                                   *)

Theorem t_N_sound :
  forall kn NT, t_N prec d tab mrlo th B kn = Some NT ->
  (exists X, is_inv 9 rM X) /\ tmhas d u w 14 14 NT (bN s h).
Proof.
  intros kn NT HN. unfold t_N in HN.
  set (M := t_M prec d tab mrlo th B) in HN.
  set (PI := t_P d M) in HN.
  set (E := tmsub prec d 9 9 (t_Id prec d 9) (tcm prec d 9 9 9 PI M)) in HN.
  set (E' := tmsub prec d 9 9 (t_Id prec d 9) (tmc prec d 9 9 9 M PI)) in HN.
  set (RE := tmrange prec d tab mrlo 9 9 E) in HN.
  set (RE' := tmrange prec d tab mrlo 9 9 E') in HN.
  set (th0 := iupmax prec (map (irowsum prec 9 RE) (seq 0 9) ++ map (irowsum prec 9 RE') (seq 0 9))) in HN.
  set (C := tcm prec d 9 9 14 PI (t_SVE prec d tab mrlo th B)) in HN.
  set (RC := tmrange prec d tab mrlo 9 14 C) in HN.
  set (gam := iupmax prec (map (irowsum prec 14 RC) (seq 0 9))) in HN.
  destruct (if_some _ _ _ HN) as [Hc HNT]. clear HN. subst NT.
  apply andb_prop in Hc. destruct Hc as [Hc H4]. apply andb_prop in Hc. destruct Hc as [Hc H3].
  apply andb_prop in Hc. destruct Hc as [H1 H2].
  destruct (iupmax_point (map (irowsum prec 9 RE) (seq 0 9) ++ map (irowsum prec 9 RE') (seq 0 9))) as [th1 Hth1].
  fold th0 in Hth1.
  destruct (iupmax_point (map (irowsum prec 14 RC) (seq 0 9))) as [g1 Hg1]. fold gam in Hg1.
  (* the real matrices *)
  set (P := rP M).
  set (Er := msub mI (mm 9 P rM)).
  set (Er' := msub mI (mm 9 rM P)).
  set (Cr := mm 9 P rSVE).
  assert (HP : icont 9 9 PI P) by apply tP_cont.
  assert (HE : tmhas d u w 9 9 E Er).
  { apply tmsub_correct; [apply tId_sound | apply (tcm_correct prec d u w Hd); [exact HP | apply tM_sound]]. }
  assert (HE' : tmhas d u w 9 9 E' Er').
  { apply tmsub_correct; [apply tId_sound | apply (tmc_correct prec d u w Hd); [apply tM_sound | exact HP]]. }
  assert (HC : tmhas d u w 9 14 C Cr) by (apply (tcm_correct prec d u w Hd); [exact HP | apply tSVE_sound]).
  assert (NE : mnorm 9 9 Er <= th1).
  { apply (inorm_le_correct prec 9 9 RE Er th0 th1); [lia | | exact Hth1 | exact H1].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd). exact HE. }
  assert (NE' : mnorm 9 9 Er' <= th1).
  { apply (inorm_le_correct prec 9 9 RE' Er' th0 th1); [lia | | exact Hth1 | exact H2].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd). exact HE'. }
  assert (NC : mnorm 9 14 Cr <= g1).
  { apply (inorm_le_correct prec 9 14 RC Cr gam g1); [lia | | exact Hg1 | exact H3].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd). exact HC. }
  assert (Hlt : th1 < 1).
  { assert (Hs1 := I.sub_correct prec (I.fromZ prec 1) th0 (Xreal (IZR 1)) (Xreal th1) (I.fromZ_correct prec 1) Hth1).
    assert (Hp := sign_pos _ (IZR 1 - th1) Hs1 H4). lra. }
  assert (Hth0 : 0 <= th1) by (eapply Rle_trans; [apply mnorm_nonneg | exact NE]).
  (* M is invertible *)
  destruct (approx_inverse 9 rM P th1 NE NE' Hlt) as [X [HXl [HXr _]]].
  assert (HinvX : is_inv 9 rM X) by (intros i j Hi Hj; split; [apply HXl | apply HXr]; assumption).
  split; [exists X; exact HinvX|].
  (* (I - E)^-1 P is that inverse *)
  set (L := mm 9 (ninv 9 Er) P).
  assert (HLM : forall i j, (i < 9)%nat -> (j < 9)%nat -> mm 9 L rM i j = mI i j).
  { intros i j Hi Hj. unfold L. rewrite mm_assoc.
    rewrite (mm_ext 9 (ninv 9 Er) (ninv 9 Er) (mm 9 P rM) (msub mI Er) i j).
    - exact (ninv_left 9 Er th1 NE Hlt i j Hi Hj).
    - intros; reflexivity.
    - intros l Hl. unfold Er, msub. ring. }
  assert (HLX : forall i j, (i < 9)%nat -> (j < 9)%nat -> L i j = X i j).
  { intros i j Hi Hj.
    assert (A := mm_assoc 9 L rM X i j).
    rewrite (mm_ext 9 (mm 9 L rM) mI X X i j) in A by (intros l Hl; first [apply HLM; assumption | reflexivity]).
    rewrite (mm_ext 9 L L (mm 9 rM X) mI i j) in A by (intros l Hl; first [reflexivity | apply HXr; assumption]).
    rewrite mm_mI_l in A by exact Hi. rewrite mm_mI_r in A by exact Hj. lra. }
  assert (HMi : forall i j, (i < 9)%nat -> (j < 9)%nat -> Mi (bPp s h) (bUp s h) i j = L i j).
  { intros i j Hi Hj. unfold Mi, Mst. fold rM. rewrite (minv_spec 9 rM X HinvX i j Hi Hj). symmetry. apply HLX; assumption. }
  (* the Neumann sum with its tail *)
  set (Yr := mm 9 (ninv 9 Er) Cr).
  set (tau := I.mul prec (I.div prec (ipow prec th0 (S kn)) (I.sub prec (I.fromZ prec 1) th0)) gam).
  assert (Htau : contains (I.convert tau) (Xreal (th1 ^ S kn / (1 - th1) * g1))).
  { unfold tau.
    assert (Hs1 := I.sub_correct prec (I.fromZ prec 1) th0 (Xreal (IZR 1)) (Xreal th1) (I.fromZ_correct prec 1) Hth1).
    assert (Hd1 := I.div_correct prec _ _ _ _ (ipow_correct prec th0 th1 (S kn) Hth1) Hs1).
    change (Xsub (Xreal (IZR 1)) (Xreal th1)) with (Xreal (IZR 1 - th1)) in Hd1. rewrite Xdiv_r in Hd1 by lra.
    exact (I.mul_correct prec _ _ _ _ Hd1 Hg1). }
  assert (HY : tmhas d u w 9 14 (tmball prec d 9 14 (I.join (I.neg tau) tau) (tneu prec d tab mrlo 9 14 E C kn)) Yr).
  { apply (tmball_correct prec d u w 9 14 _ _ (rneu 9 Er Cr kn) Yr).
    - exact (tneu_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd 9 14 E C Er Cr HE HC kn).
    - intros i j Hi Hj. apply (isym_correct _ (th1 ^ S kn / (1 - th1) * g1)); [exact Htau|].
      eapply Rle_trans; [apply (entry_le_mnorm 9 14 (msub Yr (rneu 9 Er Cr kn)) i j Hi Hj)|].
      eapply Rle_trans; [apply (neu_tail 9 14 Er Cr th1 kn NE Hlt)|].
      apply Rmult_le_compat_l; [| exact NC].
      unfold Rdiv. apply Rmult_le_pos; [apply pow_le; exact Hth0 | left; apply Rinv_0_lt_compat; lra]. }
  (* that sum is M^-1 [SV E5] *)
  assert (HYM : forall i c, (i < 9)%nat -> (c < 14)%nat -> Yr i c = mm 9 (Mi (bPp s h) (bUp s h)) rSVE i c).
  { intros i c Hi Hc. unfold Yr, Cr. rewrite <- mm_assoc. fold L.
    apply mm_ext; [intros l Hl; symmetry; apply HMi; assumption | intros; reflexivity]. }
  set (Y := tmball prec d 9 14 (I.join (I.neg tau) tau) (tneu prec d tab mrlo 9 14 E C kn)) in HY |- *.
  assert (HQY : tmhas d u w 5 14 (tmm prec d tab mrlo 5 9 14 (t_Q prec d B) Y) (mm 9 rQ Yr))
    by exact (tmm_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd 5 9 14 _ _ _ _ tQ_sound HY).
  (* the rows of N *)
  intros i c Hi Hc. rewrite tget_ttab by assumption. cbv beta.
  set (Mi0 := Mi (bPp s h) (bUp s h)).
  set (SV0 := SV h (bSx s h) (bV s h)).
  assert (HSV : forall l, (c < 9)%nat -> mm 9 Mi0 rSVE l c = mm 9 Mi0 SV0 l c).
  { intros l Hc9. unfold mm, rSVE. apply msum_ext. intros m Hm. destruct (Nat.ltb_spec c 9); [reflexivity | lia]. }
  assert (HE5 : forall l, (9 <= c)%nat -> mm 9 Mi0 rSVE l c = mm 9 Mi0 E5 l (c - 9)%nat).
  { intros l Hc9. unfold mm, rSVE. apply msum_ext. intros m Hm. destruct (Nat.ltb_spec c 9); [lia | reflexivity]. }
  unfold bN, Nmat.
  destruct (Nat.ltb_spec i 9) as [H9|H9].
  - assert (HYi := HY i c H9 Hc). rewrite (HYM i c H9 Hc) in HYi. fold Mi0 in HYi.
    destruct (Nat.ltb_spec c 9) as [Hc9|Hc9].
    + unfold Nxx. fold Mi0 SV0. rewrite <- (HSV i Hc9). exact HYi.
    + unfold Nxp. fold Mi0. rewrite <- (HE5 i Hc9). exact HYi.
  - set (r := (i - 9)%nat).
    assert (Hr : (r < 5)%nat) by (unfold r; lia).
    assert (HQ : mm 9 rQ Yr r c = mm 9 rQ (mm 9 Mi0 rSVE) r c)
      by (apply mm_ext; [intros; reflexivity | intros l Hl; apply HYM; assumption]).
    assert (HQYi := HQY r c Hr Hc). rewrite HQ in HQYi.
    destruct (Nat.ltb_spec c 9) as [Hc9|Hc9].
    + unfold Npx. fold Mi0 SV0.
      replace (- bSx s h r c + mm 9 (Qm h (bPp s h) (bPm (s + h) h)) (mm 9 Mi0 SV0) r c)
        with (mm 9 rQ (mm 9 Mi0 rSVE) r c - pval true r 0 c s h).
      * apply tsub_correct; [exact HQYi | apply HRx; assumption].
      * unfold rQ, bSx. rewrite (mm_ext 9 (Qm h (bPp s h) (bPm (s + h) h)) (Qm h (bPp s h) (bPm (s + h) h))
                                   (mm 9 Mi0 rSVE) (mm 9 Mi0 SV0) r c)
          by (intros l Hl; first [reflexivity | apply HSV; exact Hc9]).
        ring.
    + unfold Npp. fold Mi0.
      replace (mm 9 (Qm h (bPp s h) (bPm (s + h) h)) (mm 9 Mi0 E5) r (c - 9)%nat) with (mm 9 rQ (mm 9 Mi0 rSVE) r c).
      * exact HQYi.
      * unfold rQ. unfold mm at 1 3. apply msum_ext. intros l Hl. rewrite (HE5 l Hc9). reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* Bounds on M^-1, M and Q                                           *)

Theorem t_Mb_sound :
  forall bMi bM bQ, t_Mb prec d tab mrlo th B = Some (bMi, bM, bQ) ->
  (exists x, contains (I.convert bMi) (Xreal x) /\ mnorm 9 9 (Mi (bPp s h) (bUp s h)) <= x) /\
  (exists x, contains (I.convert bM) (Xreal x) /\ mnorm 9 9 rM <= x) /\
  (exists x, contains (I.convert bQ) (Xreal x) /\ mnorm 5 9 rQ <= x).
Proof.
  intros bMi bM bQ HT. unfold t_Mb in HT.
  set (M := t_M prec d tab mrlo th B) in HT.
  set (PI := t_P d M) in HT.
  set (RE := tmrange prec d tab mrlo 9 9 (tmsub prec d 9 9 (t_Id prec d 9) (tcm prec d 9 9 9 PI M))) in HT.
  set (RE' := tmrange prec d tab mrlo 9 9 (tmsub prec d 9 9 (t_Id prec d 9) (tmc prec d 9 9 9 M PI))) in HT.
  set (th0 := iupmax prec (map (irowsum prec 9 RE) (seq 0 9) ++ map (irowsum prec 9 RE') (seq 0 9))) in HT.
  set (nP := iupmax prec (map (irowsum prec 9 PI) (seq 0 9))) in HT.
  set (RM := tmrange prec d tab mrlo 9 9 M) in HT.
  set (nM := iupmax prec (map (irowsum prec 9 RM) (seq 0 9))) in HT.
  set (RQ := tmrange prec d tab mrlo 5 9 (t_Q prec d B)) in HT.
  set (nQ := iupmax prec (map (irowsum prec 9 RQ) (seq 0 5))) in HT.
  destruct (if_some _ _ _ HT) as [Hc HE]. clear HT.
  destruct (triple_eq _ _ _ _ _ _ HE) as [E1 [E2 E3]]. clear HE. subst bMi bM bQ.
  apply andb_prop in Hc. destruct Hc as [Hc H6]. apply andb_prop in Hc. destruct Hc as [Hc H5].
  apply andb_prop in Hc. destruct Hc as [Hc H4]. apply andb_prop in Hc. destruct Hc as [Hc H3].
  apply andb_prop in Hc. destruct Hc as [H1 H2].
  destruct (iupmax_point (map (irowsum prec 9 RE) (seq 0 9) ++ map (irowsum prec 9 RE') (seq 0 9))) as [th1 Hth1].
  fold th0 in Hth1.
  destruct (iupmax_point (map (irowsum prec 9 PI) (seq 0 9))) as [p1 Hp1]. fold nP in Hp1.
  destruct (iupmax_point (map (irowsum prec 9 RM) (seq 0 9))) as [m1 Hm1]. fold nM in Hm1.
  destruct (iupmax_point (map (irowsum prec 9 RQ) (seq 0 5))) as [q1 Hq1]. fold nQ in Hq1.
  set (P := rP M).
  assert (HP : icont 9 9 PI P) by apply tP_cont.
  assert (HM := tM_sound). fold M in HM.
  assert (NE : mnorm 9 9 (msub mI (mm 9 P rM)) <= th1).
  { apply (inorm_le_correct prec 9 9 RE _ th0 th1); [lia | | exact Hth1 | exact H1].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd).
    apply tmsub_correct; [apply tId_sound | apply (tcm_correct prec d u w Hd); [exact HP | exact HM]]. }
  assert (NE' : mnorm 9 9 (msub mI (mm 9 rM P)) <= th1).
  { apply (inorm_le_correct prec 9 9 RE' _ th0 th1); [lia | | exact Hth1 | exact H2].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd).
    apply tmsub_correct; [apply tId_sound | apply (tmc_correct prec d u w Hd); [exact HM | exact HP]]. }
  assert (Hlt : th1 < 1).
  { assert (Hs1 := I.sub_correct prec (I.fromZ prec 1) th0 (Xreal (IZR 1)) (Xreal th1) (I.fromZ_correct prec 1) Hth1).
    assert (Hp := sign_pos _ (IZR 1 - th1) Hs1 H3). lra. }
  assert (NP : mnorm 9 9 P <= p1) by exact (inorm_le_correct prec 9 9 PI P nP p1 ltac:(lia) HP Hp1 H4).
  split; [| split].
  - destruct (approx_inverse 9 rM P th1 NE NE' Hlt) as [X [HXl [HXr HXn]]].
    assert (HinvX : is_inv 9 rM X) by (intros i j Hi Hj; split; [apply HXl | apply HXr]; assumption).
    exists (p1 / (1 - th1)). split.
    + assert (Hs1 := I.sub_correct prec (I.fromZ prec 1) th0 (Xreal (IZR 1)) (Xreal th1) (I.fromZ_correct prec 1) Hth1).
      assert (Hdv := I.div_correct prec _ _ _ _ Hp1 Hs1).
      change (Xsub (Xreal (IZR 1)) (Xreal th1)) with (Xreal (IZR 1 - th1)) in Hdv.
      rewrite Xdiv_r in Hdv by lra. exact Hdv.
    + rewrite (mnorm_ext 9 9 (Mi (bPp s h) (bUp s h)) X).
      * eapply Rle_trans; [exact HXn|]. apply Rmult_le_compat_r; [| exact NP].
        left. apply Rinv_0_lt_compat. lra.
      * intros i j Hi Hj. unfold Mi, Mst. fold rM. exact (minv_spec 9 rM X HinvX i j Hi Hj).
  - exists m1. split; [exact Hm1|].
    apply (inorm_le_correct prec 9 9 RM rM nM m1 ltac:(lia)); [| exact Hm1 | exact H5].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd). exact HM.
  - exists q1. split; [exact Hq1|].
    apply (inorm_le_correct prec 5 9 RQ rQ nQ q1 ltac:(lia)); [| exact Hq1 | exact H6].
    apply (tmrange_correct prec d tab mrlo u w Hlo eq_refl Hcov Hd). exact tQ_sound.
Qed.

End N.
