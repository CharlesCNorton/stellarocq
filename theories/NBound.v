(** How far N moves between two points, from how far its ingredients move.

    N of Step.v is built from the inverse Mi of M = [Pp; Up], the matrix
    SV = [-h Sx; -V], Sx and Q by products and sums. At two points, with the
    ingredients bounded in norm and their differences bounded, [N_diff]
    bounds the difference of the two N in the infinity norm, without
    differentiating the inverse: Mi - Mi' = Mi (M' - M) Mi' ([inv_diff]).
    [defect_bound] turns bounds on N at three points into the bound on the
    local defect Psi(s, h) - Psi(s + h/2, h/2) Psi(s, h/2) that Levels.v asks
    for. *)

From Coq Require Import Reals Lra Lia.
From Stellarocq Require Import Mat Shoot Recur CFMS Step.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Norms of rectangular products and sums                            *)

Lemma mnorm_msub_le : forall m n A B, mnorm m n (msub A B) <= mnorm m n A + mnorm m n B.
Proof.
  intros m n A B. apply fmax_le; [apply Rplus_le_le_0_compat; apply mnorm_nonneg|].
  intros i Hi. unfold mrow, msub.
  eapply Rle_trans; [| apply Rplus_le_compat; apply mrow_le_mnorm; exact Hi]. unfold mrow.
  rewrite <- msum_plus. apply msum_le. intros j Hj. unfold Rminus. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp. lra.
Qed.

Lemma mnorm_madd_le : forall m n A B, mnorm m n (madd A B) <= mnorm m n A + mnorm m n B.
Proof.
  intros m n A B. apply fmax_le; [apply Rplus_le_le_0_compat; apply mnorm_nonneg|].
  intros i Hi. unfold mrow, madd.
  eapply Rle_trans; [| apply Rplus_le_compat; apply mrow_le_mnorm; exact Hi]. unfold mrow.
  rewrite <- msum_plus. apply msum_le. intros j Hj. apply Rabs_triang.
Qed.

Lemma mnorm_ext :
  forall m n A B, (forall i j, (i < m)%nat -> (j < n)%nat -> A i j = B i j) -> mnorm m n A = mnorm m n B.
Proof.
  intros m n A B H. unfold mnorm. apply Rle_antisym; apply fmax_mono; intros i Hi; unfold mrow;
    apply msum_le; intros j Hj; rewrite H by assumption; lra.
Qed.

(** The difference of two products. *)
Lemma mm_diff :
  forall m k n A A' B B',
  mnorm m n (msub (mm k A B) (mm k A' B'))
  <= mnorm m k (msub A A') * mnorm k n B + mnorm m k A' * mnorm k n (msub B B').
Proof.
  intros m k n A A' B B'.
  rewrite (mnorm_ext m n (msub (mm k A B) (mm k A' B')) (madd (mm k (msub A A') B) (mm k A' (msub B B')))).
  - eapply Rle_trans; [apply mnorm_madd_le|]. apply Rplus_le_compat; apply mnorm_mm.
  - intros i j _ _. unfold msub, madd, mm. cbv beta. rewrite <- msum_minus, <- msum_plus.
    apply msum_ext. intros; ring.
Qed.

(** The difference of two inverses. *)
Lemma inv_diff :
  forall n M M' X X', is_inv n M X -> is_inv n M' X' ->
  mnorm n n (msub X X') <= mnorm n n X * mnorm n n (msub M' M) * mnorm n n X'.
Proof.
  intros n M M' X X' HX HX'.
  rewrite (mnorm_ext n n (msub X X') (mm n X (mm n (msub M' M) X'))).
  - eapply Rle_trans; [apply mnorm_mm|]. rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply mnorm_nonneg|].
    apply mnorm_mm.
  - intros i j Hi Hj.
    (* X (M' - M) X' = X M' X' - X M X' = X - X' *)
    assert (A : mm n X (mm n (msub M' M) X') i j = mm n X (mm n M' X') i j - mm n X (mm n M X') i j).
    { unfold mm, msub. cbv beta. rewrite <- msum_minus. apply msum_ext. intros l Hl.
      rewrite (msum_ext (fun k => (M' l k - M l k) * X' k j) (fun k => M' l k * X' k j - M l k * X' k j))
        by (intros; ring).
      rewrite msum_minus. ring. }
    rewrite A.
    rewrite (mm_ext n X X (mm n M' X') mI i j) by (intros l Hl; first [reflexivity | apply (HX' l j Hl Hj)]).
    rewrite mm_mI_r by exact Hj.
    rewrite <- mm_assoc.
    rewrite (mm_ext n (mm n X M) mI X' X' i j) by (intros l Hl; first [apply (HX i l Hi Hl) | reflexivity]).
    rewrite mm_mI_l by exact Hi. unfold msub. reflexivity.
Qed.

Lemma mnorm_scal_nonneg :
  forall m n a A, 0 <= a -> mnorm m n (fun i j => a * A i j) = a * mnorm m n A.
Proof.
  intros m n a A Ha. unfold mnorm, mrow. induction m as [|m IH]; cbn [fmax]; [ring|].
  rewrite IH. rewrite (msum_ext _ (fun j => a * Rabs (A m j))) by (intros; rewrite Rabs_mult, Rabs_right by lra; reflexivity).
  rewrite msum_scal. rewrite RmaxRmult by exact Ha. reflexivity.
Qed.

Lemma mnorm_scal_abs : forall m n a A, mnorm m n (fun i j => a * A i j) = Rabs a * mnorm m n A.
Proof.
  intros m n a A. unfold mnorm, mrow. induction m as [|m IH]; cbn [fmax]; [ring|].
  rewrite IH. rewrite (msum_ext _ (fun j => Rabs a * Rabs (A m j))) by (intros; rewrite Rabs_mult; reflexivity).
  rewrite msum_scal. rewrite RmaxRmult by apply Rabs_pos. reflexivity.
Qed.

Lemma mnorm_neg_r : forall m n A, mnorm m n (fun i j => - A i j) = mnorm m n A.
Proof.
  intros m n A. unfold mnorm, mrow. apply Rle_antisym; apply fmax_mono; intros i Hi; apply msum_le;
    intros j Hj; rewrite Rabs_Ropp; lra.
Qed.

Lemma mnorm_E5 : mnorm 9 5 E5 <= 1.
Proof.
  apply fmax_le; [lra|]. intros i Hi. unfold mrow, E5. destruct (Nat.ltb_spec i 5) as [H5|H5].
  - rewrite (msum_single _ 5 i H5).
    + unfold mI. rewrite Nat.eqb_refl, Rabs_R1. lra.
    + intros j Hj Hji. unfold mI. destruct (Nat.eqb_spec i j) as [->|]; [contradiction | apply Rabs_R0].
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; apply Rabs_R0). rewrite msum_zero. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The local defect                                                  *)

(** Psi = I + h N at the step h against two steps of h/2. *)
Theorem defect_bound :
  forall n (N1 N2 N3 : mat) h a b c,
  0 <= h ->
  mnorm n n (msub N1 N2) <= a -> mnorm n n (msub N1 N3) <= b ->
  mnorm n n N2 <= c -> mnorm n n N3 <= c ->
  mnorm n n (msub (fun i j => mI i j + h * N1 i j)
                  (mm n (fun i j => mI i j + h / 2 * N2 i j) (fun i j => mI i j + h / 2 * N3 i j)))
  <= h * ((a + b) / 2) + h * h / 4 * (c * c).
Proof.
  intros n N1 N2 N3 h a b c Hh H12 H13 H2 H3.
  assert (Hc : 0 <= c) by (eapply Rle_trans; [apply mnorm_nonneg | exact H2]).
  (* the defect is h (N1 - N2/2 - N3/2) - h^2/4 N2 N3 *)
  rewrite (mnorm_ext n n _ (madd (fun i j => h / 2 * msub N1 N2 i j + h / 2 * msub N1 N3 i j)
                                 (fun i j => - (h * h / 4 * mm n N2 N3 i j)))).
  - eapply Rle_trans; [apply mnorm_madd_le|]. apply Rplus_le_compat.
    + eapply Rle_trans; [apply (mnorm_madd_le n n (fun i j => h / 2 * msub N1 N2 i j) (fun i j => h / 2 * msub N1 N3 i j))|].
      rewrite !(mnorm_scal_nonneg n n (h / 2)) by lra.
      replace (h * ((a + b) / 2)) with (h / 2 * a + h / 2 * b) by field.
      apply Rplus_le_compat; apply Rmult_le_compat_l; lra.
    + rewrite (mnorm_neg_r n n), (mnorm_scal_nonneg n n (h * h / 4)) by nra.
      apply Rmult_le_compat_l; [nra|].
      eapply Rle_trans; [apply mnorm_mm|]. apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact H2 | exact H3].
  - intros i j Hi Hj. unfold msub, madd, mm. cbv beta.
    rewrite (msum_ext (fun k => (mI i k + h / 2 * N2 i k) * (mI k j + h / 2 * N3 k j))
                      (fun k => mI i k * mI k j + h / 2 * (mI i k * N3 k j) + h / 2 * (N2 i k * mI k j)
                                + h * h / 4 * (N2 i k * N3 k j))) by (intros; cbv beta; field).
    rewrite !msum_plus, !msum_scal.
    fold (mm n mI mI i j). fold (mm n mI N3 i j). fold (mm n N2 mI i j). fold (mm n N2 N3 i j).
    rewrite mm_mI_l by exact Hi. rewrite mm_mI_l by exact Hi. rewrite mm_mI_r by exact Hj. field.
Qed.

(* ---------------------------------------------------------------- *)
(* Norms of the blocks of N                                          *)

Lemma mnorm_mstack :
  forall A B, mnorm 9 9 (mstack A B) <= mnorm 5 9 A + mnorm 4 9 B.
Proof.
  intros A B. apply fmax_le; [apply Rplus_le_le_0_compat; apply mnorm_nonneg|].
  intros i Hi. unfold mrow, mstack. destruct (Nat.ltb_spec i 5) as [H5|H5].
  - assert (H := mrow_le_mnorm 5 9 A i H5). unfold mrow in H. assert (0 <= mnorm 4 9 B) by apply mnorm_nonneg. lra.
  - assert (H := mrow_le_mnorm 4 9 B (i - 5) ltac:(lia)). unfold mrow in H.
    assert (0 <= mnorm 5 9 A) by apply mnorm_nonneg. lra.
Qed.

Lemma msub_mstack :
  forall A B A' B' i k, msub (mstack A B) (mstack A' B') i k = mstack (msub A A') (msub B B') i k.
Proof. intros A B A' B' i k. unfold msub, mstack. destruct (Nat.ltb i 5); reflexivity. Qed.

(** The 14 x 14 norm of N from the norms of its four blocks. *)
Lemma mnorm_Nblocks :
  forall (A : mat) (B : mat) (C : mat) (D : mat) a b c d,
  mnorm 9 9 A <= a -> mnorm 9 5 B <= b -> mnorm 5 9 C <= c -> mnorm 5 5 D <= d ->
  mnorm 14 14 (fun i k => if Nat.ltb i 9 then (if Nat.ltb k 9 then A i k else B i (k - 9)%nat)
                          else (if Nat.ltb k 9 then C (i - 9)%nat k else D (i - 9)%nat (k - 9)%nat))
  <= Rmax (a + b) (c + d).
Proof.
  intros A B C D a b c d HA HB HC HD.
  assert (Ha := Rle_trans _ _ _ (mnorm_nonneg 9 9 A) HA). assert (Hb := Rle_trans _ _ _ (mnorm_nonneg 9 5 B) HB).
  apply fmax_le; [eapply Rle_trans; [| apply Rmax_l]; lra|].
  intros i Hi. unfold mrow. replace 14%nat with (9 + 5)%nat by reflexivity. rewrite msum_add.
  destruct (Nat.ltb_spec i 9) as [H9|H9].
  - eapply Rle_trans; [| apply Rmax_l]. apply Rplus_le_compat.
    + eapply Rle_trans; [| exact HA]. eapply Rle_trans; [| apply (mrow_le_mnorm 9 9 A i H9)].
      unfold mrow. apply Req_le. apply msum_ext. intros k Hk. rewrite (proj2 (Nat.ltb_lt k 9) Hk). reflexivity.
    + eapply Rle_trans; [| exact HB]. eapply Rle_trans; [| apply (mrow_le_mnorm 9 5 B i H9)].
      unfold mrow. apply Req_le. apply msum_ext. intros k Hk.
      replace (Nat.ltb (9 + k) 9) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (9 + k - 9)%nat with k by lia. reflexivity.
  - eapply Rle_trans; [| apply Rmax_r]. apply Rplus_le_compat.
    + eapply Rle_trans; [| exact HC]. eapply Rle_trans; [| apply (mrow_le_mnorm 5 9 C (i - 9) ltac:(lia))].
      unfold mrow. apply Req_le. apply msum_ext. intros k Hk. rewrite (proj2 (Nat.ltb_lt k 9) Hk). reflexivity.
    + eapply Rle_trans; [| exact HD]. eapply Rle_trans; [| apply (mrow_le_mnorm 5 5 D (i - 9) ltac:(lia))].
      unfold mrow. apply Req_le. apply msum_ext. intros k Hk.
      replace (Nat.ltb (9 + k) 9) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (9 + k - 9)%nat with k by lia. reflexivity.
Qed.

Lemma Nmat_sub :
  forall h Pp Pm' Sx Up V h2 Pp2 Pm2 Sx2 Up2 V2 i k,
  msub (Nmat h Pp Pm' Sx Up V) (Nmat h2 Pp2 Pm2 Sx2 Up2 V2) i k
  = (if Nat.ltb i 9 then
       (if Nat.ltb k 9 then msub (Nxx h Pp Sx Up V) (Nxx h2 Pp2 Sx2 Up2 V2) i k
        else msub (Nxp Pp Up) (Nxp Pp2 Up2) i (k - 9)%nat)
     else (if Nat.ltb k 9 then msub (Npx h Pp Pm' Sx Up V) (Npx h2 Pp2 Pm2 Sx2 Up2 V2) (i - 9)%nat k
           else msub (Npp h Pp Pm' Up) (Npp h2 Pp2 Pm2 Up2) (i - 9)%nat (k - 9)%nat)).
Proof.
  intros. unfold msub, Nmat. destruct (Nat.ltb i 9); destruct (Nat.ltb k 9); reflexivity.
Qed.

(** Bounds on N and on the difference of two N from bounds on their
    ingredients. *)
Section NDiff.

Variables h h2 h0 : R.
Variables Pp Pm' Sx Up V Pp2 Pm2 Sx2 Up2 V2 : mat.
Variables mi sx v q eM eSx eV eQ eh : R.
Hypothesis Hh : 0 <= h <= h0.
Hypothesis Hh2 : 0 <= h2 <= h0.
Hypothesis Hinv1 : exists X, is_inv 9 (mstack Pp Up) X.
Hypothesis Hinv2 : exists X, is_inv 9 (mstack Pp2 Up2) X.
Hypothesis Hmi1 : mnorm 9 9 (Mi Pp Up) <= mi.
Hypothesis Hmi2 : mnorm 9 9 (Mi Pp2 Up2) <= mi.
Hypothesis HM : mnorm 9 9 (msub (mstack Pp Up) (mstack Pp2 Up2)) <= eM.
Hypothesis Hsx1 : mnorm 5 9 Sx <= sx.
Hypothesis Hsx2 : mnorm 5 9 Sx2 <= sx.
Hypothesis HSx : mnorm 5 9 (msub Sx Sx2) <= eSx.
Hypothesis Hv1 : mnorm 4 9 V <= v.
Hypothesis Hv2 : mnorm 4 9 V2 <= v.
Hypothesis HV : mnorm 4 9 (msub V V2) <= eV.
Hypothesis Hq1 : mnorm 5 9 (Qm h Pp Pm') <= q.
Hypothesis Hq2 : mnorm 5 9 (Qm h2 Pp2 Pm2) <= q.
Hypothesis HQ : mnorm 5 9 (msub (Qm h Pp Pm') (Qm h2 Pp2 Pm2)) <= eQ.
Hypothesis Heh : Rabs (h - h2) <= eh.

Definition sv_b : R := h0 * sx + v.
Definition eMi_b : R := mi * eM * mi.
Definition eSV_b : R := eh * sx + h0 * eSx + eV.

Lemma Mi_inv1 : is_inv 9 (mstack Pp Up) (Mi Pp Up).
Proof. destruct Hinv1 as [X HX]. exact (minv_inv 9 _ X HX). Qed.
Lemma Mi_inv2 : is_inv 9 (mstack Pp2 Up2) (Mi Pp2 Up2).
Proof. destruct Hinv2 as [X HX]. exact (minv_inv 9 _ X HX). Qed.

Lemma nonneg_of : forall m n A b, mnorm m n A <= b -> 0 <= b.
Proof. intros m n A b H. eapply Rle_trans; [apply mnorm_nonneg | exact H]. Qed.

Lemma eMi_bound : mnorm 9 9 (msub (Mi Pp Up) (Mi Pp2 Up2)) <= eMi_b.
Proof.
  eapply Rle_trans; [apply (inv_diff 9 (mstack Pp Up) (mstack Pp2 Up2) _ _ Mi_inv1 Mi_inv2)|].
  unfold eMi_b. rewrite (mnorm_ext 9 9 (msub (mstack Pp2 Up2) (mstack Pp Up)) (fun i k => - msub (mstack Pp Up) (mstack Pp2 Up2) i k))
    by (intros; unfold msub; ring).
  rewrite mnorm_neg_r.
  apply Rmult_le_compat; [apply Rmult_le_pos; apply mnorm_nonneg | apply mnorm_nonneg | | exact Hmi2].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hmi1 | exact HM].
Qed.

Lemma SV_bound1 : mnorm 9 9 (SV h Sx V) <= sv_b.
Proof.
  eapply Rle_trans; [apply mnorm_mstack|]. unfold sv_b. apply Rplus_le_compat.
  - rewrite mnorm_neg_r, mnorm_scal_nonneg by lra.
    apply Rmult_le_compat; [lra | apply mnorm_nonneg | lra | exact Hsx1].
  - rewrite mnorm_neg_r. exact Hv1.
Qed.

Lemma SV_bound2 : mnorm 9 9 (SV h2 Sx2 V2) <= sv_b.
Proof.
  eapply Rle_trans; [apply mnorm_mstack|]. unfold sv_b. apply Rplus_le_compat.
  - rewrite mnorm_neg_r, mnorm_scal_nonneg by lra.
    apply Rmult_le_compat; [lra | apply mnorm_nonneg | lra | exact Hsx2].
  - rewrite mnorm_neg_r. exact Hv2.
Qed.

Lemma eSV_bound : mnorm 9 9 (msub (SV h Sx V) (SV h2 Sx2 V2)) <= eSV_b.
Proof.
  unfold SV. rewrite (mnorm_ext 9 9 _ (mstack (msub (fun i k => - (h * Sx i k)) (fun i k => - (h2 * Sx2 i k)))
                                               (msub (fun i k => - V i k) (fun i k => - V2 i k))))
    by (intros; apply msub_mstack).
  eapply Rle_trans; [apply mnorm_mstack|]. unfold eSV_b.
  assert (Hsx := nonneg_of _ _ _ _ Hsx1).
  apply Rplus_le_compat.
  - (* h Sx - h2 Sx2 = (h - h2) Sx + h2 (Sx - Sx2) *)
    rewrite (mnorm_ext 5 9 _ (fun i k => - (madd (fun i k => (h - h2) * Sx i k) (fun i k => h2 * msub Sx Sx2 i k) i k)))
      by (intros; unfold msub, madd; ring).
    rewrite mnorm_neg_r. eapply Rle_trans; [apply mnorm_madd_le|].
    rewrite mnorm_scal_abs, mnorm_scal_abs. rewrite (Rabs_right h2) by lra.
    apply Rplus_le_compat; apply Rmult_le_compat; try apply Rabs_pos; try apply mnorm_nonneg; try lra; assumption.
  - rewrite (mnorm_ext 4 9 _ (fun i k => - msub V V2 i k)) by (intros; unfold msub; ring).
    rewrite mnorm_neg_r. lra.
Qed.

Definition nxx_b : R := mi * sv_b.
Definition enxx_b : R := eMi_b * sv_b + mi * eSV_b.

Lemma Nxx_bound1 : mnorm 9 9 (Nxx h Pp Sx Up V) <= nxx_b.
Proof.
  unfold Nxx, nxx_b. eapply Rle_trans; [apply mnorm_mm|].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hmi1 | exact SV_bound1].
Qed.

Lemma Nxx_diff : mnorm 9 9 (msub (Nxx h Pp Sx Up V) (Nxx h2 Pp2 Sx2 Up2 V2)) <= enxx_b.
Proof.
  unfold Nxx, enxx_b. eapply Rle_trans; [apply mm_diff|]. apply Rplus_le_compat.
  - apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact eMi_bound | exact SV_bound1].
  - apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hmi2 | exact eSV_bound].
Qed.

Lemma Nxp_bound1 : mnorm 9 5 (Nxp Pp Up) <= mi.
Proof.
  unfold Nxp. eapply Rle_trans; [apply mnorm_mm|]. rewrite <- (Rmult_1_r mi).
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hmi1 | apply mnorm_E5].
Qed.

Lemma Nxp_diff : mnorm 9 5 (msub (Nxp Pp Up) (Nxp Pp2 Up2)) <= eMi_b.
Proof.
  unfold Nxp. eapply Rle_trans; [apply mm_diff|].
  rewrite (mnorm_ext 9 5 (msub E5 E5) (fun _ _ => 0)) by (intros; unfold msub; ring).
  replace (mnorm 9 5 (fun _ _ => 0)) with 0.
  - rewrite Rmult_0_r, Rplus_0_r. rewrite <- (Rmult_1_r eMi_b).
    apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact eMi_bound | apply mnorm_E5].
  - symmetry. apply Rle_antisym; [| apply mnorm_nonneg]. apply fmax_le; [lra|]. intros i Hi. unfold mrow.
    rewrite (msum_ext _ (fun _ => 0)) by (intros; apply Rabs_R0). rewrite msum_zero. lra.
Qed.

Definition npx_b : R := sx + q * nxx_b.
Definition enpx_b : R := eSx + eQ * nxx_b + q * enxx_b.

Lemma Npx_bound1 : mnorm 5 9 (Npx h Pp Pm' Sx Up V) <= npx_b.
Proof.
  unfold Npx, npx_b. rewrite (mnorm_ext 5 9 _ (madd (fun i c => - Sx i c) (mm 9 (Qm h Pp Pm') (mm 9 (Mi Pp Up) (SV h Sx V)))))
    by (intros; reflexivity).
  eapply Rle_trans; [apply mnorm_madd_le|]. rewrite mnorm_neg_r. apply Rplus_le_compat; [exact Hsx1|].
  eapply Rle_trans; [apply mnorm_mm|].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hq1 | exact Nxx_bound1].
Qed.

Lemma Npx_diff : mnorm 5 9 (msub (Npx h Pp Pm' Sx Up V) (Npx h2 Pp2 Pm2 Sx2 Up2 V2)) <= enpx_b.
Proof.
  unfold Npx, enpx_b.
  rewrite (mnorm_ext 5 9 _ (madd (fun i c => - msub Sx Sx2 i c)
                                 (msub (mm 9 (Qm h Pp Pm') (mm 9 (Mi Pp Up) (SV h Sx V)))
                                       (mm 9 (Qm h2 Pp2 Pm2) (mm 9 (Mi Pp2 Up2) (SV h2 Sx2 V2))))))
    by (intros; unfold msub, madd; ring).
  eapply Rle_trans; [apply mnorm_madd_le|]. rewrite mnorm_neg_r. rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact HSx|].
  eapply Rle_trans; [apply mm_diff|]. apply Rplus_le_compat.
  - apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact HQ | exact Nxx_bound1].
  - apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hq2 | exact Nxx_diff].
Qed.

Definition npp_b : R := q * mi.
Definition enpp_b : R := eQ * mi + q * eMi_b.

Lemma Npp_bound1 : mnorm 5 5 (Npp h Pp Pm' Up) <= npp_b.
Proof.
  unfold Npp, npp_b. eapply Rle_trans; [apply mnorm_mm|].
  apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hq1 | exact Nxp_bound1].
Qed.

Lemma Npp_diff : mnorm 5 5 (msub (Npp h Pp Pm' Up) (Npp h2 Pp2 Pm2 Up2)) <= enpp_b.
Proof.
  unfold Npp, enpp_b. eapply Rle_trans; [apply mm_diff|]. apply Rplus_le_compat.
  - apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact HQ | exact Nxp_bound1].
  - apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact Hq2 | exact Nxp_diff].
Qed.

(** The bounds on N and on the difference. *)
Theorem N_bound : mnorm 14 14 (Nmat h Pp Pm' Sx Up V) <= Rmax (nxx_b + mi) (npx_b + npp_b).
Proof.
  apply mnorm_Nblocks; [exact Nxx_bound1 | exact Nxp_bound1 | exact Npx_bound1 | exact Npp_bound1].
Qed.

Theorem N_diff :
  mnorm 14 14 (msub (Nmat h Pp Pm' Sx Up V) (Nmat h2 Pp2 Pm2 Sx2 Up2 V2))
  <= Rmax (enxx_b + eMi_b) (enpx_b + enpp_b).
Proof.
  rewrite (mnorm_ext 14 14 _ _ (fun i k _ _ => Nmat_sub h Pp Pm' Sx Up V h2 Pp2 Pm2 Sx2 Up2 V2 i k)).
  apply mnorm_Nblocks; [exact Nxx_diff | exact Nxp_diff | exact Npx_diff | exact Npp_diff].
Qed.

End NDiff.
