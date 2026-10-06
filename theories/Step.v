(** The one-step map of the recursion as a matrix.

    [minv n M] is the inverse of M wherever M has one, picked out by
    Coquelicot's description operator from the unique two-sided inverse
    ([minv_spec]), so that the step map is a function of the blocks without a
    choice. With Mi the inverse of M = [Pp; Up], Q = (Pm' - Pp) / h, Pm' the
    next row's Pm, the step of Recur.v is z + h (N z + zeta) ([step_N]) with

      N = [ Mi [-h Sx; -V]                Mi [I; 0]   ]
          [ -Sx + Q Mi [-h Sx; -V]        Q Mi [I; 0] ]

    and zeta the sources carried through Mi and Q. N has no h in a
    denominator once Q is given, which is what lets its bounds hold
    uniformly as h goes to 0. *)

From Coq Require Import Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Mat Shoot Recur CFMS.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The inverse as a function                                         *)

Definition is_inv (n : nat) (M X : mat) : Prop :=
  forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j /\ mm n M X i j = mI i j.

Lemma inv_unique :
  forall n M X Y, is_inv n M X -> is_inv n M Y -> forall i j, (i < n)%nat -> (j < n)%nat -> X i j = Y i j.
Proof.
  intros n M X Y HX HY i j Hi Hj.
  assert (A : mm n (mm n X M) Y i j = mm n X (mm n M Y) i j) by apply mm_assoc.
  rewrite (mm_ext n (mm n X M) mI Y Y i j) in A by (intros l Hl; first [apply (HX i l Hi Hl) | reflexivity]).
  rewrite (mm_ext n X X (mm n M Y) mI i j) in A by (intros l Hl; first [reflexivity | apply (HY l j Hl Hj)]).
  rewrite mm_mI_l in A by exact Hi. rewrite mm_mI_r in A by exact Hj. symmetry. exact A.
Qed.

Definition minv (n : nat) (M : mat) : mat :=
  fun i j => iota (fun x : R => exists X, is_inv n M X /\ X i j = x).

Lemma minv_spec :
  forall n M X, is_inv n M X -> forall i j, (i < n)%nat -> (j < n)%nat -> minv n M i j = X i j.
Proof.
  intros n M X HX i j Hi Hj. unfold minv.
  apply (iota_unique (V := R_CompleteNormedModule)).
  - intros y [Y [HY <-]]. exact (inv_unique n M Y X HY HX i j Hi Hj).
  - exists X. split; [exact HX | reflexivity].
Qed.

Lemma minv_inv : forall n M X, is_inv n M X -> is_inv n M (minv n M).
Proof.
  intros n M X HX i j Hi Hj. split.
  - rewrite (mm_ext n (minv n M) X M M i j) by (intros l Hl; first [apply minv_spec; assumption | reflexivity]).
    apply HX; assumption.
  - rewrite (mm_ext n M M (minv n M) X i j) by (intros l Hl; first [reflexivity | apply minv_spec; assumption]).
    apply HX; assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Small facts about matrix-vector products                          *)

Lemma mv_scal_mat : forall n a A x i, mv n (fun r c => a * A r c) x i = a * mv n A x i.
Proof. intros n a A x i. unfold mv. rewrite <- msum_scal. apply msum_ext. intros; ring. Qed.

(** [I; 0], the five radial rows' unknowns placed in nine. *)
Definition E5 : mat := fun i c => if Nat.ltb i 5 then mI i c else 0.

Lemma mv_E5 : forall p i, (i < 9)%nat -> mv 9 E5 p i = if Nat.ltb i 5 then p i else 0.
Proof.
  intros p i Hi. unfold mv, E5. destruct (Nat.ltb_spec i 5) as [H5|H5].
  - rewrite (msum_single _ 9 i Hi).
    + unfold mI. rewrite Nat.eqb_refl. ring.
    + intros c Hc Hci. unfold mI. destruct (Nat.eqb_spec i c) as [->|]; [contradiction | ring].
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
Qed.

(** A product with E5 has nothing in its last four columns. *)
Lemma mm_E5_cols : forall A i c, (5 <= c < 9)%nat -> mm 9 A E5 i c = 0.
Proof.
  intros A i c Hc. unfold mm, E5. rewrite (msum_ext _ (fun _ => 0)); [apply msum_zero|].
  intros l Hl. destruct (Nat.ltb_spec l 5); [| ring].
  unfold mI. replace (Nat.eqb l c) with false by (symmetry; apply Nat.eqb_neq; lia). ring.
Qed.

Lemma mv_mstack9 :
  forall A B x i, mv 9 (mstack A B) x i = if Nat.ltb i 5 then mv 9 A x i else mv 9 B x (i - 5)%nat.
Proof. intros A B x i. rewrite mv_mstack. reflexivity. Qed.

Lemma mv_madd_mat : forall n A B x i, mv n (fun r c => A r c + B r c) x i = mv n A x i + mv n B x i.
Proof. intros n A B x i. unfold mv. rewrite <- msum_plus. apply msum_ext. intros; ring. Qed.

(** A product over m inner indices of a matrix-vector product over n columns. *)
Lemma mv_mm_dims :
  forall m n A B x i, mv m A (fun c => mv n B x c) i = mv n (mm m A B) x i.
Proof.
  intros m n A B x i. unfold mv, mm.
  rewrite (msum_ext _ (fun l => msum (fun c => A i l * B l c * x c) n))
    by (intros l _; rewrite <- msum_scal; apply msum_ext; intros; ring).
  rewrite msum_swap. apply msum_ext. intros c _. rewrite <- msum_scal_r. apply msum_ext. intros; ring.
Qed.

Lemma mv_mm_E5 : forall A p i, mv 9 (mm 9 A E5) p i = mv 5 (mm 9 A E5) p i.
Proof.
  intros A p i. unfold mv. replace 9%nat with (5 + 4)%nat at 1 by reflexivity. rewrite msum_add.
  rewrite (msum_ext (fun c => mm 9 A E5 i (5 + c)%nat * p (5 + c)%nat) (fun _ => 0))
    by (intros c Hc; rewrite mm_E5_cols by lia; ring).
  rewrite msum_zero. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* The blocks of N                                                   *)

Section N.

Variable h : R.
Variables Pp Pm' Sx Up V : mat.

Definition Mst : mat := mstack Pp Up.
Definition Mi : mat := minv 9 Mst.
Definition Qm : mat := fun i c => (Pm' i c - Pp i c) / h.

(** [-h Sx; -V] *)
Definition SV : mat := mstack (fun i c => - (h * Sx i c)) (fun i c => - V i c).

Definition Nxx : mat := mm 9 Mi SV.
Definition Nxp : mat := mm 9 Mi E5.
Definition Npx : mat := fun i c => - Sx i c + mm 9 Qm (mm 9 Mi SV) i c.
Definition Npp : mat := mm 9 Qm (mm 9 Mi E5).

Definition Nmat : mat :=
  fun i c => if Nat.ltb i 9 then (if Nat.ltb c 9 then Nxx i c else Nxp i (c - 9)%nat)
             else (if Nat.ltb c 9 then Npx (i - 9)%nat c else Npp (i - 9)%nat (c - 9)%nat).

Definition zeta (rs ru : vec) : vec :=
  let b := mv 9 Mi (stack (fun i => h * rs i) ru) in
  zjoin b (fun i => rs i + mv 9 Qm b i).

(** N applied to a state, by its two blocks of rows. *)
Lemma mv_Nmat_x :
  forall z i, (i < 9)%nat -> mv 14 Nmat z i = mv 9 Nxx (zx z) i + mv 5 Nxp (zp z) i.
Proof.
  intros z i Hi. unfold mv. replace 14%nat with (9 + 5)%nat by reflexivity. rewrite msum_add.
  unfold Nmat. rewrite (proj2 (Nat.ltb_lt i 9) Hi). reflexivity.
Qed.

Lemma mv_Nmat_p :
  forall z i, (i < 5)%nat -> mv 14 Nmat z (9 + i)%nat = mv 9 Npx (zx z) i + mv 5 Npp (zp z) i.
Proof.
  intros z i Hi. unfold mv. replace 14%nat with (9 + 5)%nat by reflexivity. rewrite msum_add.
  unfold Nmat. replace (Nat.ltb (9 + i) 9) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (9 + i - 9)%nat with i by lia. reflexivity.
Qed.

End N.

(* ---------------------------------------------------------------- *)
(* Recur's step through N                                            *)

Section StepN.

Variable h : R.
Hypothesis Hh : 0 < h.
Variables Pp Pm Sx Up V : nat -> mat.
Variable j : nat.
Hypothesis Hinv : exists X, is_inv 9 (mstack (Pp j) (Up j)) X.

Let MiF : nat -> mat := fun j => minv 9 (mstack (Pp j) (Up j)).
Let Mij : mat := Mi (Pp j) (Up j).

Lemma Mij_inv : is_inv 9 (mstack (Pp j) (Up j)) Mij.
Proof. destruct Hinv as [X HX]. exact (minv_inv 9 _ X HX). Qed.

(** The rows' right-hand side: the state's part through E5 and SV, and the
    sources' part. *)
Lemma rhs_split :
  forall z rs ru c, (c < 9)%nat ->
  Recur.rhs h Sx V j z rs ru c
  = mv 9 E5 (zp z) c + mv 9 (SV h (Sx j) (V j)) (zx z) c + stack (fun i => h * rs i) ru c.
Proof.
  intros z rs ru c Hc. unfold Recur.rhs, SV, stack. rewrite mv_E5 by exact Hc. rewrite mv_mstack9.
  destruct (Nat.ltb_spec c 5) as [H5|H5].
  - rewrite (mv_neg_mat 9 (fun i k => h * Sx j i k)), mv_scal_mat. ring.
  - rewrite mv_neg_mat. ring.
Qed.

Lemma dnext_N :
  forall z rs ru c, (c < 9)%nat ->
  dnext h Sx V MiF j z rs ru c
  = mv 9 (Nxx h (Pp j) (Sx j) (Up j) (V j)) (zx z) c + mv 5 (Nxp (Pp j) (Up j)) (zp z) c
    + mv 9 Mij (stack (fun i => h * rs i) ru) c.
Proof.
  intros z rs ru c Hc. unfold dnext, MiF. fold (Mst (Pp j) (Up j)). fold (Mi (Pp j) (Up j)). fold Mij.
  rewrite (mv_extn 9 Mij (Recur.rhs h Sx V j z rs ru)
             (fun c' => (mv 9 E5 (zp z) c' + mv 9 (SV h (Sx j) (V j)) (zx z) c') + stack (fun i => h * rs i) ru c') c)
    by (intros c' Hc'; apply rhs_split; exact Hc').
  rewrite mv_add, mv_add. unfold Nxx, Nxp. fold Mij.
  rewrite <- mv_mm_E5. rewrite !mv_mm_r. ring.
Qed.

(** Pp d is the radial part of the right-hand side, since M Mi is the identity. *)
Lemma Pp_dnext :
  forall z rs ru i, (i < 5)%nat ->
  mv 9 (Pp j) (dnext h Sx V MiF j z rs ru) i = zp z i - h * mv 9 (Sx j) (zx z) i + h * rs i.
Proof.
  intros z rs ru i Hi. unfold dnext, MiF. fold (Mst (Pp j) (Up j)). fold (Mi (Pp j) (Up j)). fold Mij.
  assert (H := right_inv_apply (mstack (Pp j) (Up j)) Mij (Recur.rhs h Sx V j z rs ru)
                 (fun r c Hr Hc => proj2 (Mij_inv r c Hr Hc)) i ltac:(lia)).
  rewrite mv_mstack9 in H. rewrite (proj2 (Nat.ltb_lt i 5) Hi) in H. rewrite H.
  unfold Recur.rhs, stack. rewrite (proj2 (Nat.ltb_lt i 5) Hi). reflexivity.
Qed.

Theorem step_N :
  forall z rs ru i, (i < 14)%nat ->
  step h Pm Sx V MiF j z rs ru i
  = z i + h * (mv 14 (Nmat h (Pp j) (Pm (S j)) (Sx j) (Up j) (V j)) z i
               + zeta h (Pp j) (Pm (S j)) (Up j) rs ru i).
Proof.
  intros z rs ru i Hi. unfold step, zeta, zjoin. cbv beta zeta.
  destruct (Nat.ltb_spec i 9) as [H9|H9].
  - rewrite (mv_Nmat_x h (Pp j) (Pm (S j)) (Sx j) (Up j) (V j) z i H9).
    rewrite dnext_N by exact H9. fold Mij. unfold zx. ring.
  - (* the p rows: Pm' d = Pp d + h Q d *)
    destruct (Nat.le_exists_sub 9 i H9) as [k [Ei _]]. subst i.
    assert (Hk : (k < 5)%nat) by lia.
    replace (k + 9)%nat with (9 + k)%nat by lia. replace (9 + k - 9)%nat with k by lia.
    rewrite (mv_Nmat_p h (Pp j) (Pm (S j)) (Sx j) (Up j) (V j) z k Hk).
    set (Q := Qm h (Pp j) (Pm (S j))).
    set (A := mv 9 (Nxx h (Pp j) (Sx j) (Up j) (V j)) (zx z)).
    set (B := fun c => mv 5 (Nxp (Pp j) (Up j)) (zp z) c).
    set (C := mv 9 (Mi (Pp j) (Up j)) (stack (fun i => h * rs i) ru)).
    assert (Hd : forall c, (c < 9)%nat -> dnext h Sx V MiF j z rs ru c = A c + B c + C c)
      by (intros c Hc; apply dnext_N; exact Hc).
    assert (HQ : mv 9 (Pm (S j)) (dnext h Sx V MiF j z rs ru) k
                 = mv 9 (Pp j) (dnext h Sx V MiF j z rs ru) k + h * mv 9 Q (dnext h Sx V MiF j z rs ru) k).
    { unfold mv, Q, Qm. rewrite <- msum_scal, <- msum_plus. apply msum_ext. intros c _. field. lra. }
    assert (HQd : mv 9 Q (dnext h Sx V MiF j z rs ru) k = mv 9 Q A k + mv 9 Q B k + mv 9 Q C k).
    { rewrite (mv_extn 9 Q (dnext h Sx V MiF j z rs ru) (fun c => A c + B c + C c) k Hd).
      rewrite mv_add, mv_add. reflexivity. }
    assert (HA : mv 9 Q A k = mv 9 (mm 9 Q (Nxx h (Pp j) (Sx j) (Up j) (V j))) (zx z) k) by apply mv_mm_r.
    assert (HB : mv 9 Q B k = mv 5 (Npp h (Pp j) (Pm (S j)) (Up j)) (zp z) k)
      by (unfold B, Npp, Nxp; fold Q; apply mv_mm_dims).
    assert (HNpx : mv 9 (Npx h (Pp j) (Pm (S j)) (Sx j) (Up j) (V j)) (zx z) k
                   = - mv 9 (Sx j) (zx z) k + mv 9 (mm 9 Q (Nxx h (Pp j) (Sx j) (Up j) (V j))) (zx z) k).
    { unfold Npx. fold Q. rewrite mv_madd_mat, mv_neg_mat. reflexivity. }
    rewrite HQ, Pp_dnext by exact Hk. rewrite HQd, HA, HB, HNpx.
    fold C. unfold zp. lra.
Qed.

End StepN.
