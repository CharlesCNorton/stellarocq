(** The step matrices of every level h = 2^-K, K >= 16, against the cells.

    Level K has the rows j = 2^(K-2) .. 2^K of the collocated problem, s = j h;
    segment k of the check is the rows cutK K k .. cutK K (k+1), s from
    1/4 + k/16 to 1/4 + (k+1)/16, and splits into 4096 reference steps of
    fK K = 2^(K-16) rows each. The Taylor-model cells of the check are 256 per
    segment, s-intervals of width 2^-12 with h in [0, 2^-16], and reference
    step i is part i mod 16 of cell i / 16 ([cell_point]: every row's (s, h)
    lies in its part). A frame is rescaled by 2^e, its inverse by 2^-e, which
    leaves W N W^-1 unchanged ([scale_conj]). [seg_level]: when the steps'
    ranges pass their checks, the propagator of every level over the segment,
    in the frame's coordinates, lies within the segment's delta of the
    product of the reference steps. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat TMEval TMat Shoot Recur CFMS Step NBound Osc
  CellTM CellSound CellN CellMain Frames Assemble Check3d.

Local Open Scope R_scope.

Definition hK (K : nat) : R := / 2 ^ K.
Definition fK (K : nat) : nat := (2 ^ (K - 16))%nat.
Definition cutK (K k : nat) : nat := (2 ^ (K - 2) + k * (4096 * fK K))%nat.
Definition PsiK (K : nat) (j : nat) : mat := fun r c => mI r c + hK K * bN (INR j * hK K) (hK K) r c.

(** Cell (k, j): s in sc +- 2^-13 and h in 2^-17 +- 2^-17. *)
Definition csc (k j : nat) : Z * Z := (Z.of_nat (2048 + 512 * k + 2 * j + 1), (-13)%Z).
Definition chalf : Z * Z := (1%Z, (-13)%Z).
Definition chh : Z * Z := (1%Z, (-17)%Z).

(* ---------------------------------------------------------------- *)
(* Arithmetic of the levels                                          *)

Lemma pow2_pos : forall n, 0 < 2 ^ n.
Proof. intros n. apply pow_lt. lra. Qed.

Lemma hK_pos : forall K, 0 < hK K.
Proof. intros K. unfold hK. apply Rinv_0_lt_compat. apply pow2_pos. Qed.

Lemma pow_split : forall K n, (n <= K)%nat -> 2 ^ K = 2 ^ (K - n) * 2 ^ n.
Proof. intros K n H. rewrite <- pow_add. f_equal. lia. Qed.

Lemma INR_pow2 : forall n, INR (2 ^ n) = 2 ^ n.
Proof. intros n. rewrite pow_INR. reflexivity. Qed.

Lemma pow_ratio : forall K n, (n <= K)%nat -> INR (2 ^ (K - n)) * hK K = / 2 ^ n.
Proof.
  intros K n H. rewrite INR_pow2. unfold hK. rewrite (pow_split K n H).
  assert (H1 := pow2_pos (K - n)). assert (H2 := pow2_pos n). field. lra.
Qed.

Lemma fK_pos : forall K, (0 < fK K)%nat.
Proof. intros K. unfold fK. apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. Qed.

Lemma fK_h : forall K, (16 <= K)%nat -> INR (fK K) * hK K = / 65536.
Proof. intros K H. unfold fK. rewrite pow_ratio by exact H. cbn. lra. Qed.

Lemma cutK_s :
  forall K k i t, (16 <= K)%nat ->
  INR (cutK K k + i * fK K + t) * hK K = / 4 + INR k / 16 + INR i / 65536 + INR t * hK K.
Proof.
  intros K k i t HK. unfold cutK. rewrite !plus_INR, !mult_INR.
  assert (E1 : INR (2 ^ (K - 2)) * hK K = / 4) by (rewrite pow_ratio by lia; cbn; lra).
  assert (E2 := fK_h K HK).
  replace ((INR (2 ^ (K - 2)) + INR k * (INR 4096 * INR (fK K)) + INR i * INR (fK K) + INR t) * hK K)
    with (INR (2 ^ (K - 2)) * hK K + INR k * INR 4096 * (INR (fK K) * hK K) + INR i * (INR (fK K) * hK K) + INR t * hK K)
    by ring.
  rewrite E1, E2. replace (INR 4096) with 4096 by (cbn; ring). field.
Qed.

Lemma pRZ13 : powerRZ 2 (-13) = / 8192.
Proof. change (powerRZ 2 (-13)) with (/ 2 ^ 13). f_equal. cbn. ring. Qed.

Lemma pRZ16 : powerRZ 2 (-16) = / 65536.
Proof. change (powerRZ 2 (-16)) with (/ 2 ^ 16). f_equal. cbn. ring. Qed.

Lemma pRZ17 : powerRZ 2 (-17) = / 131072.
Proof. change (powerRZ 2 (-17)) with (/ 2 ^ 17). f_equal. cbn. ring. Qed.

Lemma dyadR_csc : forall k i, dyadR (csc k i) = / 4 + INR k / 16 + INR i / 4096 + / 8192.
Proof.
  intros k i. unfold dyadR, csc. cbn [fst snd]. rewrite <- INR_IZR_INZ.
  rewrite !plus_INR, !mult_INR, pRZ13.
  replace (INR 2048) with 2048 by (cbn; ring). replace (INR 512) with 512 by (cbn; ring).
  replace (INR 2) with 2 by (cbn; ring). replace (INR 1) with 1 by (cbn; ring). field.
Qed.

Lemma dyadR_chalf : dyadR chalf = / 8192.
Proof. unfold dyadR, chalf. cbn [fst snd]. rewrite pRZ13. cbn. lra. Qed.

Lemma dyadR_chh : dyadR chh = / 131072.
Proof. unfold dyadR, chh. cbn [fst snd]. rewrite pRZ17. cbn. lra. Qed.

Lemma dyadR_urad : dyadR (urad chalf 4) = / 131072.
Proof. unfold dyadR, urad, chalf. cbn [fst snd]. replace (-13 - Z.of_nat 4)%Z with (-17)%Z by reflexivity.
  rewrite pRZ17. cbn. lra. Qed.

Lemma dyadR_ucen : forall q, dyadR (ucen chalf 4 q) = (2 * INR q - 15) / 131072.
Proof.
  intros q. unfold dyadR, ucen, chalf. cbn [fst snd].
  replace (-13 - Z.of_nat 4)%Z with (-17)%Z by reflexivity. rewrite pRZ17.
  replace (2 ^ Z.of_nat 4)%Z with 16%Z by reflexivity.
  rewrite Z.mul_1_l, minus_IZR, plus_IZR, mult_IZR, <- INR_IZR_INZ. cbn [IZR IPR IPR_2]. field.
Qed.

Lemma hK_le : forall K, (16 <= K)%nat -> hK K <= / 65536.
Proof.
  intros K H. rewrite <- (fK_h K H). assert (Hf := fK_pos K). apply lt_INR in Hf. cbn in Hf.
  assert (Hh := hK_pos K). rewrite <- (Rmult_1_l (hK K)) at 1. apply Rmult_le_compat_r; [lra|].
  apply (le_INR 1). apply fK_pos.
Qed.

(** Every row of reference step i lies in part i mod 16 of cell i / 16. *)
Lemma cell_point :
  forall K k i t, (16 <= K)%nat -> (i < 4096)%nat -> (t < fK K)%nat ->
  let u := INR (cutK K k + i * fK K + t) * hK K - dyadR (csc k (i / 16)) in
  Rabs (u - dyadR (ucen chalf 4 (i mod 16))) <= dyadR (urad chalf 4) /\ Rabs u <= dyadR chalf /\
  Rabs (hK K - dyadR chh) <= dyadR chh /\ 0 < dyadR chh + (hK K - dyadR chh).
Proof.
  intros K k i t HK Hi Ht u. unfold u. rewrite cutK_s by exact HK.
  rewrite dyadR_csc, dyadR_chalf, dyadR_chh, dyadR_urad, dyadR_ucen.
  assert (Hh := hK_pos K). assert (Hle := hK_le K HK).
  assert (Htf : INR t * hK K <= / 65536 - hK K).
  { rewrite <- (fK_h K HK). assert (Ht' : (t + 1 <= fK K)%nat) by lia. apply le_INR in Ht'. rewrite plus_INR in Ht'.
    cbn in Ht'. nra. }
  assert (Ht0 : 0 <= INR t * hK K) by (apply Rmult_le_pos; [apply pos_INR | lra]).
  assert (Hdm : INR i = 16 * INR (i / 16) + INR (i mod 16)).
  { rewrite (Nat.div_mod_eq i 16) at 1. rewrite plus_INR, mult_INR. cbn. ring. }
  assert (Hq : INR (i mod 16) <= 15).
  { assert (H := Nat.mod_upper_bound i 16 ltac:(lia)).
    replace 15 with (INR 15) by (cbn; ring). apply le_INR. lia. }
  assert (Hq0 := pos_INR (i mod 16)).
  rewrite Hdm. split; [| split; [| split]].
  - apply Rabs_le. split; lra.
  - apply Rabs_le. split; lra.
  - apply Rabs_le. split; lra.
  - lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Frames rescaled by powers of two                                  *)

Definition scale (e : Z) (A : mat) : mat := fun r c => powerRZ 2 e * A r c.

Lemma powerRZ_inv2 : forall e, powerRZ 2 e * powerRZ 2 (- e) = 1.
Proof.
  intros e. rewrite <- powerRZ_add by lra. replace (e + - e)%Z with 0%Z by lia. reflexivity.
Qed.

Lemma mm_scale_l : forall n e A B i j, mm n (scale e A) B i j = powerRZ 2 e * mm n A B i j.
Proof. intros. unfold mm, scale. rewrite <- msum_scal. apply msum_ext. intros; ring. Qed.

Lemma mm_scale_r : forall n e A B i j, mm n A (scale e B) i j = powerRZ 2 e * mm n A B i j.
Proof. intros. unfold mm, scale. rewrite <- msum_scal. apply msum_ext. intros; ring. Qed.

Lemma scale_inv : forall e W X, is_inv 14 W X -> is_inv 14 (scale e W) (scale (- e) X).
Proof.
  intros e W X HX i j Hi Hj. destruct (HX i j Hi Hj) as [H1 H2].
  assert (P := powerRZ_inv2 e).
  split.
  - rewrite mm_scale_l, mm_scale_r, H1. rewrite <- Rmult_assoc, (Rmult_comm (powerRZ 2 (- e)) (powerRZ 2 e)), P. ring.
  - rewrite mm_scale_l, mm_scale_r, H2. rewrite <- Rmult_assoc, P. ring.
Qed.

Lemma scale_conj :
  forall e W X N i j, mm 14 (mm 14 (scale e W) N) (scale (- e) X) i j = mm 14 (mm 14 W N) X i j.
Proof.
  intros e W X N i j. rewrite mm_scale_r.
  rewrite (mm_ext 14 (mm 14 (scale e W) N) (fun i k => powerRZ 2 e * mm 14 W N i k) X X i j)
    by (intros; first [apply mm_scale_l | reflexivity]).
  unfold mm at 1. rewrite (msum_ext _ (fun l => powerRZ 2 e * (mm 14 W N i l * X l j))) by (intros; ring).
  rewrite msum_scal. fold (mm 14 (mm 14 W N) X i j).
  rewrite <- Rmult_assoc, (Rmult_comm (powerRZ 2 (- e))), powerRZ_inv2. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* A segment of every level                                          *)

Section Seg.

Variable prec : F.precision.
Variable d : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable kn : nat.
Variables Wd Dd : list (list (Z * Z)).
Variable WiI : imat.
Variable e : Z.
Variable k : nat.
Variable Rs : nat -> imat.
Hypothesis HWiI : winv_encl prec Wd Dd = Some WiI.
Hypothesis Hcells : forall j, (j < 256)%nat ->
  cell_ranges prec d (mktab d) (csc k j) chh chalf chh kn 4 Wd WiI = Some (map (fun q => Rs (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hok : forall i, (i < 4096)%nat -> cell_ok prec (Rs i) = true.
Hypothesis Hdel : delta_ok prec Rs 4096 = true.
Variable X : mat.
Hypothesis HX : is_inv 14 (dmatR Wd) X.

Let W' : mat := scale e (dmatR Wd).
Let Wi' : mat := scale (- e) X.

Lemma HXcont : icont 14 14 WiI X.
Proof. exact (proj2 (winv_encl_sound prec Wd Dd WiI HWiI) X HX). Qed.

(** The step matrix in the frame's coordinates. *)
Definition Aseg (K : nat) (j : nat) : mat := mm 14 (mm 14 W' (bN (INR j * hK K) (hK K))) Wi'.

Lemma Aseg_cell :
  forall K i t, (16 <= K)%nat -> (i < 4096)%nat -> (t < fK K)%nat ->
  icont 14 14 (Rs i) (Aseg K (cutK K k + i * fK K + t)%nat).
Proof.
  intros K i t HK Hi Ht.
  destruct (cell_point K k i t HK Hi Ht) as [Hsub [Hu [Hw Hp]]].
  assert (Hj : (i / 16 < 256)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hq : (i mod 16 < 2 ^ 4)%nat) by (change (2 ^ 4)%nat with 16%nat; apply Nat.mod_upper_bound; lia).
  destruct (cell_ranges_sound prec d Hcov Hd (csc k (i / 16)) chh chalf chh kn 4 Wd WiI _ X (Hcells _ Hj) HXcont
              (i mod 16) _ _ Hq Hsub Hu Hw Hp) as [_ Hc].
  rewrite nth_map_seq_lt in Hc by (apply Nat.mod_upper_bound; lia).
  rewrite <- (Nat.div_mod_eq i 16) in Hc.
  replace (dyadR (csc k (i / 16)) + (INR (cutK K k + i * fK K + t) * hK K - dyadR (csc k (i / 16))))
    with (INR (cutK K k + i * fK K + t) * hK K) in Hc by ring.
  replace (dyadR chh + (hK K - dyadR chh)) with (hK K) in Hc by ring.
  intros r c Hr Hc'. unfold Aseg, W', Wi'. rewrite scale_conj. apply Hc; assumption.
Qed.

Lemma gstep_gref :
  forall K i, (16 <= K)%nat -> meq 14 (gstep (fun i => rnref (Rs i)) (hK K) (fK K) i) (gref (Rs i)).
Proof.
  intros K i HK r c _ _. unfold gstep, gref. rewrite (fK_h K HK). unfold hr, dyadR. cbn [fst snd].
  rewrite pRZ16. ring.
Qed.

Theorem seg_level :
  forall K, (16 <= K)%nat ->
  mnorm 14 14 (msub (mm 14 (mm 14 W' (mprod 14 (PsiK K) (cutK K k) (4096 * fK K))) Wi')
                    (mprod 14 (fun i => gref (Rs i)) 0 4096))
  <= rmid (delta_of prec Rs 4096).
Proof.
  intros K HK.
  assert (HW : forall i j, (i < 14)%nat -> (j < 14)%nat -> mm 14 W' Wi' i j = mI i j /\ mm 14 Wi' W' i j = mI i j).
  { intros i j Hi Hj. destruct (scale_inv e (dmatR Wd) X HX i j Hi Hj) as [H1 H2]. split; [exact H2 | exact H1]. }
  (* the propagator in coordinates is the product of the steps I + h A_j *)
  assert (Hm : meq 14 (mm 14 (mm 14 W' (mprod 14 (PsiK K) (cutK K k) (4096 * fK K))) Wi')
                      (mprod 14 (fstep (Aseg K) (hK K)) (cutK K k) (4096 * fK K))).
  { eapply meq_trans; [apply meq_sym; apply mprod_conj; intros i j Hi Hj; apply HW; assumption|].
    apply mprod_ext. intros i Hi. unfold PsiK, fstep, Aseg.
    apply (conj_step 14 W' Wi'). intros i' j' Hi' Hj'. apply HW; assumption. }
  rewrite (mnorm_meq 14 _ (msub (mprod 14 (fstep (Aseg K) (hK K)) (cutK K k) (4096 * fK K))
                               (mprod 14 (gstep (fun i => rnref (Rs i)) (hK K) (fK K)) 0 4096))).
  2: { intros r c Hr Hc. unfold msub. rewrite (Hm r c Hr Hc).
       assert (Hg : meq 14 (mprod 14 (fun i => gref (Rs i)) 0 4096)
                           (mprod 14 (gstep (fun i => rnref (Rs i)) (hK K) (fK K)) 0 4096)).
       { apply mprod_ext. intros i _. apply meq_sym. apply gstep_gref. exact HK. }
       rewrite (Hg r c Hr Hc). reflexivity. }
  eapply Rle_trans; [| apply (delta_ok_sound prec Rs 4096 Hdel)].
  apply (seg_bound (Aseg K) (fun i => rnref (Rs i)) (hK K) (cutK K k) (fK K) 4096
           (fun i => om prec (Rs i)) (fun i => nu prec (Rs i)) (fun i => qq prec (Rs i)) (fun i => ll prec (Rs i))).
  - left. apply hK_pos.
  - apply fK_pos.
  - intros i t Hi Ht. exact (proj1 (proj1 (cell_ok_sound prec (Rs i) (Hok i Hi)) _ (Aseg_cell K i t HK Hi Ht))).
  - intros i t Hi Ht. exact (proj2 (proj1 (cell_ok_sound prec (Rs i) (Hok i Hi)) _ (Aseg_cell K i t HK Hi Ht))).
  - intros i Hi. rewrite (mnorm_meq 14 _ _ (gstep_gref K i HK)).
    exact (proj1 (proj2 (cell_ok_sound prec (Rs i) (Hok i Hi)))).
  - intros i Hi. rewrite (fK_h K HK).
    assert (E : / 65536 = hr) by (unfold hr, dyadR; cbn [fst snd]; rewrite pRZ16; ring).
    rewrite E. exact (proj2 (proj2 (cell_ok_sound prec (Rs i) (Hok i Hi)))).
Qed.

End Seg.
