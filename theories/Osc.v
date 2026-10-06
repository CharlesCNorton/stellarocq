(** The comparison of a run of fine steps with one reference step, and the
    inverse of a perturbed matrix from bounds on one side.

    [osc_local]: k steps I + h A_j whose matrices lie within om of B and have
    norm at most nu differ from the one step I + k h B by at most
    k h om + (1 + h nu)^k - 1 - k h nu, which [pow_exp] bounds by
    k h om + e^(k h nu) - 1 - k h nu. Every level finer than a reference
    step is compared with that step in this way, with no derivative of the
    step matrices.

    [left_perturbed_inverse]: when R is an approximate inverse of M0 on the
    right, |I - M0 R| < 1, and on the left of M, |I - R M0| + |R (M - M0)| < 1,
    then M is invertible and its inverse has norm at most
    |R| / (1 - |I - R M0| - |R (M - M0)|). Only the product with R on the
    left meets the perturbation. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Stellarocq Require Import Mat Shoot Recur CFMS Step NBound TMat.

Local Open Scope R_scope.

Lemma mnorm_add_le :
  forall m n A B, mnorm m n (fun i j => A i j + B i j) <= mnorm m n A + mnorm m n B.
Proof.
  intros m n A B. apply fmax_le; [apply Rplus_le_le_0_compat; apply mnorm_nonneg|].
  intros i Hi. eapply Rle_trans; [| apply Rplus_le_compat; apply mrow_le_mnorm; exact Hi].
  unfold mrow. rewrite <- msum_plus. apply msum_le. intros j Hj. apply Rabs_triang.
Qed.

(** The norm of a sum of matrices. *)
Lemma mnorm_msum_le :
  forall m n (F : nat -> mat) k,
  mnorm m n (fun i j => msum (fun l => F l i j) k) <= msum (fun l => mnorm m n (F l)) k.
Proof.
  intros m n F k. induction k as [|k IH]; cbn [msum].
  - apply fmax_le; [lra|]. intros i Hi. unfold mrow.
    rewrite (msum_ext _ (fun _ => 0)) by (intros; apply Rabs_R0). rewrite msum_zero. lra.
  - eapply Rle_trans; [apply (mnorm_add_le m n (fun i j => msum (fun l => F l i j) k) (F k))|].
    lra.
Qed.

Lemma mnorm_zero_mat : forall m n, mnorm m n (fun _ _ => 0) = 0.
Proof.
  intros m n. apply Rle_antisym; [| apply mnorm_nonneg].
  apply fmax_le; [lra|]. intros i Hi. unfold mrow.
  rewrite (msum_ext _ (fun _ => 0)) by (intros; apply Rabs_R0). rewrite msum_zero. lra.
Qed.

Lemma pow_exp : forall x k, 0 <= x -> (1 + x) ^ k <= exp (INR k * x).
Proof.
  intros x k Hx. induction k as [|k IH].
  - cbn [pow INR]. rewrite Rmult_0_l, exp_0. lra.
  - rewrite S_INR. replace ((INR k + 1) * x) with (INR k * x + x) by ring. rewrite exp_plus.
    cbn [pow]. rewrite Rmult_comm.
    assert (H1 : 1 + x <= exp x).
    { destruct (Req_dec x 0) as [->|Hn]; [rewrite exp_0; lra|]. left. apply exp_ineq1. lra. }
    apply Rmult_le_compat; [apply pow_le; lra | lra | exact IH | exact H1].
Qed.

Lemma msum_const : forall c k, msum (fun _ => c) k = INR k * c.
Proof. intros c k. induction k as [|k IH]; cbn [msum]; [cbn; ring|]. rewrite IH, S_INR. ring. Qed.

(* ---------------------------------------------------------------- *)
(* A run of fine steps against one reference step                    *)

Section Local.

Variable n : nat.
Variable A : nat -> mat.
Variable B : mat.
Variables h om nu : R.
Variables a k : nat.
Hypothesis Hh : 0 <= h.
Hypothesis HA : forall i, (i < k)%nat -> mnorm n n (msub (A (a + i)%nat) B) <= om.
Hypothesis Hnu : forall i, (i < k)%nat -> mnorm n n (A (a + i)%nat) <= nu.

Definition fstep (j : nat) : mat := fun r c => mI r c + h * A j r c.
Let sumA (m : nat) : mat := fun r c => msum (fun i => A (a + i)%nat r c) m.

Lemma fstep_mul :
  forall j S r c, (r < n)%nat ->
  mm n (fstep j) S r c = S r c + h * mm n (A j) S r c.
Proof.
  intros j S r c Hr. unfold fstep, mm.
  rewrite (msum_ext _ (fun l => mI r l * S l c + h * (A j r l * S l c))) by (intros; ring).
  rewrite msum_plus, msum_scal. fold (mm n mI S r c). rewrite mm_mI_l by exact Hr. reflexivity.
Qed.

Lemma mm_minus_I :
  forall (X S : mat) r c, (c < n)%nat -> mm n X S r c = mm n X (fun i j => S i j - mI i j) r c + X r c.
Proof.
  intros X S r c Hc. unfold mm.
  rewrite (msum_ext (fun l => X r l * S l c) (fun l => X r l * (S l c - mI l c) + X r l * mI l c))
    by (intros; ring).
  rewrite msum_plus. f_equal. fold (mm n X mI r c). apply mm_mI_r. exact Hc.
Qed.

Lemma osc_run :
  forall m, (m <= k)%nat ->
  mnorm n n (fun r c => mprod n fstep a m r c - mI r c) <= (1 + h * nu) ^ m - 1 /\
  mnorm n n (fun r c => mprod n fstep a m r c - mI r c - h * sumA m r c) <= (1 + h * nu) ^ m - 1 - INR m * h * nu.
Proof.
  induction m as [|m IH]; intros Hm.
  - cbn [mprod pow INR]. unfold sumA. cbn [msum].
    rewrite (mnorm_ext n n (fun r c => mI r c - mI r c) (fun _ _ => 0)) by (intros; ring).
    rewrite (mnorm_ext n n (fun r c => mI r c - mI r c - h * 0) (fun _ _ => 0)) by (intros; ring).
    rewrite mnorm_zero_mat. split; lra.
  - destruct (IH ltac:(lia)) as [He Hrem].
    assert (Hnu0 : 0 <= nu) by (eapply Rle_trans; [apply mnorm_nonneg | apply (Hnu m); lia]).
    set (P0 := mprod n fstep a m) in *. set (Am := A (a + m)%nat).
    assert (HAm : mnorm n n Am <= nu) by (apply Hnu; lia).
    set (e := (1 + h * nu) ^ m - 1) in He.
    assert (He0 : 0 <= e) by (unfold e; assert (1 <= (1 + h * nu) ^ m) by (apply pow_R1_Rle; nra); lra).
    assert (HmA : mnorm n n (mm n Am (fun i j => P0 i j - mI i j)) <= nu * e).
    { eapply Rle_trans; [apply mnorm_mm|].
      apply Rmult_le_compat; [apply mnorm_nonneg | apply mnorm_nonneg | exact HAm | exact He]. }
    assert (Hstep : forall r c, (r < n)%nat -> (c < n)%nat ->
              mprod n fstep a (S m) r c = P0 r c + h * mm n Am (fun i j => P0 i j - mI i j) r c + h * Am r c).
    { intros r c Hr Hc. cbn [mprod]. fold P0.
      rewrite fstep_mul by exact Hr. fold Am. rewrite (mm_minus_I Am P0 r c Hc). ring. }
    assert (Hh1 : h * mnorm n n (mm n Am (fun i j => P0 i j - mI i j)) <= h * (nu * e))
      by (apply Rmult_le_compat_l; assumption).
    assert (Hh2 : h * mnorm n n Am <= h * nu) by (apply Rmult_le_compat_l; assumption).
    split.
    + rewrite (mnorm_ext n n (fun r c => mprod n fstep a (S m) r c - mI r c)
                 (fun r c => (P0 r c - mI r c) + (h * mm n Am (fun i j => P0 i j - mI i j) r c + h * Am r c)))
        by (intros r c Hr Hc; rewrite Hstep by assumption; ring).
      eapply Rle_trans; [apply mnorm_add_le|].
      eapply Rle_trans; [apply Rplus_le_compat_l; apply mnorm_add_le|].
      rewrite (mnorm_scal_nonneg n n h (mm n Am (fun i j => P0 i j - mI i j)) Hh).
      rewrite (mnorm_scal_nonneg n n h Am Hh).
      replace ((1 + h * nu) ^ S m - 1) with (e + h * (nu * e) + h * nu) by (unfold e; cbn [pow]; ring).
      lra.
    + rewrite (mnorm_ext n n (fun r c => mprod n fstep a (S m) r c - mI r c - h * sumA (S m) r c)
                 (fun r c => (P0 r c - mI r c - h * sumA m r c) + h * mm n Am (fun i j => P0 i j - mI i j) r c))
        by (intros r c Hr Hc; rewrite Hstep by assumption; unfold sumA; cbn [msum]; fold Am; ring).
      eapply Rle_trans; [apply mnorm_add_le|].
      rewrite (mnorm_scal_nonneg n n h (mm n Am (fun i j => P0 i j - mI i j)) Hh).
      replace ((1 + h * nu) ^ S m - 1 - INR (S m) * h * nu) with (((1 + h * nu) ^ m - 1 - INR m * h * nu) + h * (nu * e))
        by (unfold e; rewrite S_INR; cbn [pow]; ring).
      lra.
Qed.

Theorem osc_local :
  mnorm n n (msub (mprod n fstep a k) (fun r c => mI r c + INR k * h * B r c))
  <= INR k * h * om + ((1 + h * nu) ^ k - 1 - INR k * h * nu).
Proof.
  destruct (osc_run k (Nat.le_refl k)) as [_ Hr].
  rewrite (mnorm_ext n n (msub (mprod n fstep a k) (fun r c => mI r c + INR k * h * B r c))
             (fun r c => (mprod n fstep a k r c - mI r c - h * sumA k r c)
                         + h * msum (fun i => msub (A (a + i)%nat) B r c) k)).
  2: { intros r c _ _. unfold msub, sumA. rewrite msum_minus, msum_const. ring. }
  eapply Rle_trans; [apply mnorm_add_le|].
  rewrite (mnorm_scal_nonneg n n h _ Hh).
  assert (Hs : mnorm n n (fun r c => msum (fun i => msub (A (a + i)%nat) B r c) k) <= INR k * om).
  { eapply Rle_trans; [apply (mnorm_msum_le n n (fun i => msub (A (a + i)%nat) B))|].
    rewrite <- msum_const. apply msum_le. intros i Hi. apply HA. exact Hi. }
  assert (h * mnorm n n (fun r c => msum (fun i => msub (A (a + i)%nat) B r c) k) <= h * (INR k * om))
    by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

End Local.

(* ---------------------------------------------------------------- *)
(* An inverse from bounds on one side                                *)

Section LeftInverse.

Variable n : nat.

Lemma mv_mat_ext :
  forall (A B : mat) x r, (forall c, (c < n)%nat -> A r c = B r c) -> mv n A x r = mv n B x r.
Proof. intros A B x r H. unfold mv. apply msum_ext. intros c Hc. rewrite H by exact Hc. reflexivity. Qed.

Lemma mv_zero_in : forall (A : mat) x r, (forall c, (c < n)%nat -> x c = 0) -> mv n A x r = 0.
Proof.
  intros A x r H. unfold mv. rewrite (msum_ext _ (fun _ => 0)) by (intros c Hc; rewrite H by exact Hc; ring).
  apply msum_zero.
Qed.

(** A Neumann inverse of I - E on the left and on the right. *)
Lemma ninv_left :
  forall E th, mnorm n n E <= th -> th < 1 ->
  forall i j, (i < n)%nat -> (j < n)%nat -> mm n (ninv n E) (msub mI E) i j = mI i j.
Proof.
  intros E th HE Hth i j Hi Hj. unfold mm, msub.
  rewrite (msum_ext _ (fun l => ninv n E i l * mI l j - ninv n E i l * E l j)) by (intros; ring).
  rewrite msum_minus. fold (mm n (ninv n E) mI i j). fold (mm n (ninv n E) E i j).
  rewrite mm_mI_r by exact Hj. exact (neumann_left n E th HE Hth i j Hi Hj).
Qed.

Lemma ninv_right :
  forall E th, mnorm n n E <= th -> th < 1 ->
  forall i j, (i < n)%nat -> (j < n)%nat -> mm n (msub mI E) (ninv n E) i j = mI i j.
Proof.
  intros E th HE Hth i j Hi Hj. unfold mm, msub.
  rewrite (msum_ext _ (fun l => mI i l * ninv n E l j - E i l * ninv n E l j)) by (intros; ring).
  rewrite msum_minus. fold (mm n mI (ninv n E) i j). fold (mm n E (ninv n E) i j).
  rewrite mm_mI_l by exact Hi. exact (neumann_right n E th HE Hth i j Hi Hj).
Qed.

Theorem left_perturbed_inverse :
  forall (M M0 R : mat) th0 th1 th2,
  mnorm n n (msub mI (mm n R M0)) <= th0 ->
  mnorm n n (mm n R (msub M M0)) <= th1 -> th0 + th1 < 1 ->
  mnorm n n (msub mI (mm n M0 R)) <= th2 -> th2 < 1 ->
  exists X : mat,
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j) /\
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n M X i j = mI i j) /\
    mnorm n n X <= mnorm n n R / (1 - (th0 + th1)).
Proof.
  intros M M0 R th0 th1 th2 H0 H1 Hlt H2 Hlt2.
  set (E := msub mI (mm n R M)).
  assert (HE : mnorm n n E <= th0 + th1).
  { rewrite (mnorm_ext n n E (fun i j => msub mI (mm n R M0) i j + - mm n R (msub M M0) i j)).
    - eapply Rle_trans; [apply mnorm_add_le|]. rewrite mnorm_neg_r. lra.
    - intros i j _ _. unfold E, msub, mm.
      rewrite (msum_ext (fun l => R i l * (M l j - M0 l j)) (fun l => R i l * M l j - R i l * M0 l j))
        by (intros; ring).
      rewrite msum_minus. ring. }
  set (N := ninv n E).
  set (X := mm n N R).
  (* X M = N (I - E) = I *)
  assert (HXM : forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j).
  { intros i j Hi Hj. unfold X. rewrite mm_assoc.
    rewrite (mm_ext n N N (mm n R M) (msub mI E) i j).
    - exact (ninv_left E (th0 + th1) HE Hlt i j Hi Hj).
    - intros l Hl. reflexivity.
    - intros l Hl. unfold E, msub. ring. }
  (* (I - E) X = R *)
  assert (HIE : forall r c, (r < n)%nat -> (c < n)%nat -> mm n (msub mI E) X r c = R r c).
  { intros r c Hr Hc. unfold X. rewrite <- mm_assoc.
    rewrite (mm_ext n (mm n (msub mI E) N) mI R R r c).
    - apply mm_mI_l. exact Hr.
    - intros l Hl. exact (ninv_right E (th0 + th1) HE Hlt r l Hr Hl).
    - intros l Hl. reflexivity. }
  (* M0 R is invertible, so R is injective, and so is X *)
  set (E2 := msub mI (mm n M0 R)).
  assert (Hinj : forall v, (forall r, (r < n)%nat -> mv n X v r = 0) -> forall r, (r < n)%nat -> v r = 0).
  { intros v Hv.
    assert (HRv : forall r, (r < n)%nat -> mv n R v r = 0).
    { intros r Hr. rewrite <- (mv_mat_ext (mm n (msub mI E) X) R v r) by (intros c Hc; apply HIE; assumption).
      rewrite mv_mm. apply mv_zero_in. exact Hv. }
    intros r Hr.
    rewrite <- (mv_mI n v r Hr).
    rewrite <- (mv_mat_ext (mm n (ninv n E2) (msub mI E2)) mI v r)
      by (intros c Hc; exact (ninv_left E2 th2 H2 Hlt2 r c Hr Hc)).
    rewrite mv_mm.
    rewrite (mv_extn n (ninv n E2) (mv n (msub mI E2) v) (fun _ => 0) r).
    - apply mv_zero_in. intros; reflexivity.
    - intros c Hc. rewrite (mv_mat_ext (msub mI E2) (mm n M0 R) v c)
        by (intros c' Hc'; unfold E2, msub; ring).
      rewrite mv_mm. apply mv_zero_in. exact HRv. }
  exists X. split; [exact HXM|]. split.
  - intros i j Hi Hj.
    set (v := fun r => mm n M X r j - mI r j).
    assert (HXv : forall r, (r < n)%nat -> mv n X v r = 0).
    { intros r Hr. unfold v, mv.
      rewrite (msum_ext _ (fun l => X r l * mm n M X l j - X r l * mI l j)) by (intros; ring).
      rewrite msum_minus. fold (mm n X (mm n M X) r j). fold (mm n X mI r j).
      rewrite <- mm_assoc.
      rewrite (mm_ext n (mm n X M) mI X X r j) by (intros l Hl; first [apply HXM; assumption | reflexivity]).
      rewrite mm_mI_l by exact Hr. rewrite mm_mI_r by exact Hj. ring. }
    assert (Hz := Hinj v HXv i Hi). unfold v in Hz. lra.
  - unfold X. eapply Rle_trans; [apply mnorm_mm|].
    unfold Rdiv. rewrite Rmult_comm. apply Rmult_le_compat_l; [apply mnorm_nonneg|].
    exact (neumann_norm n E (th0 + th1) HE Hlt).
Qed.

End LeftInverse.
