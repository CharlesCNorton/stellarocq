(** The linearized collocated rows of the three-dimensional problem at every
    level: a solution for every source, and one bound on every solution.

    At level K >= 16 the step is h = 2^-K and the rows are j = m + 1 .. 4m - 1,
    m = 2^(K-2), the nodes m and 4m held at zero. Each row has Recur.v's form
    with the blocks of CellTM.v at s = j h ([Pp3] .. [V3]), and its sources rs_j
    and ru_j enter the one-step recursion as Step.v's zeta ([zeta3]).
    [lin_exists]: for any sources the rows have a solution. [lin_bound]: one
    constant S, the same at every level, bounds the state (X_j, Pm_j d_j) of
    every solution at every node by S sum_j h |zeta_j| ([srcw]). Both read
    CFMS's run_exists and run_bound with the inverse of assemble3d_sound; the
    propagator over a part of a segment is bounded through its frame by
    |W^-1| e^(nu/16) |W|, nu the largest of the segment's cell bounds
    ([seg_prod_bound]), and the first step of every level is invertible by
    Final3d.psi0_ok ([Psi0_inv]), which lets a solution of the rows be read as
    a run from the node m. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat TMEval TMat Shoot Recur CFMS Step NBound Osc
  CellTM CellSound CellN CellMain Frames Assemble Check3d BMat Level3d Final3d.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The blocks of every row                                           *)

Definition Pp3 (K j : nat) : mat := bPp (INR j * hK K) (hK K).
Definition Pm3 (K j : nat) : mat := bPm (INR j * hK K) (hK K).
Definition Sx3 (K j : nat) : mat := bSx (INR j * hK K) (hK K).
Definition Up3 (K j : nat) : mat := bUp (INR j * hK K) (hK K).
Definition V3 (K j : nat) : mat := bV (INR j * hK K) (hK K).
Definition Mi3 (K j : nat) : mat := minv 9 (mstack (Pp3 K j) (Up3 K j)).

(** The sources of row j as the recursion's source. *)
Definition zeta3 (K j : nat) (rs ru : vec) : vec := zeta (hK K) (Pp3 K j) (Pm3 K (S j)) (Up3 K j) rs ru.

(** The weight of the sources of the rows m + 1 .. 4m - 1. *)
Definition srcw (K : nat) (rs ru : nat -> vec) : R :=
  msum (fun l => hK K * vnorm 14 (zeta3 K (S (cutK K 0) + l)%nat (rs (S (cutK K 0) + l)%nat) (ru (S (cutK K 0) + l)%nat)))
       (cutK K 12 - S (cutK K 0))%nat.

(* ---------------------------------------------------------------- *)
(* Arithmetic of the levels                                          *)

Lemma cutK_mono : forall K k l, (k <= l)%nat -> (cutK K k <= cutK K l)%nat.
Proof. intros K k l H. unfold cutK. apply Nat.add_le_mono_l. apply Nat.mul_le_mono_r. exact H. Qed.

Lemma cutK_12 : forall K, (16 <= K)%nat -> cutK K 12 = (4 * cutK K 0)%nat.
Proof.
  intros K HK. unfold cutK, fK. rewrite Nat.mul_0_l, Nat.add_0_r.
  replace (K - 2)%nat with (14 + (K - 16))%nat by lia. rewrite Nat.pow_add_r.
  replace (2 ^ 14)%nat with (4 * 4096)%nat by reflexivity. lia.
Qed.

Lemma cutK_0_pos : forall K, (0 < cutK K 0)%nat.
Proof. intros K. unfold cutK. rewrite Nat.mul_0_l, Nat.add_0_r. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma INR_cut0 : forall K, (16 <= K)%nat -> INR (cutK K 0) * hK K = / 4.
Proof.
  intros K HK. assert (H := cutK_s K 0 0 0 HK).
  replace (cutK K 0 + 0 * fK K + 0)%nat with (cutK K 0) in H by lia.
  rewrite H. cbn [INR]. field.
Qed.

Lemma lenK : forall K k, lenk (cutK K) k = (4096 * fK K)%nat.
Proof. intros K k. unfold lenk, cutK. lia. Qed.

Lemma INR_S_h : forall K j, INR (S j) * hK K = INR j * hK K + hK K.
Proof. intros K j. rewrite S_INR. ring. Qed.

(** Every row of a level lies in a reference step of a segment. *)
Lemma row_split :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  exists k i t, (k < 12)%nat /\ (i < 4096)%nat /\ (t < fK K)%nat /\ j = (cutK K k + i * fK K + t)%nat.
Proof.
  intros K j HK [Hlo Hhi].
  assert (Hf := fK_pos K).
  assert (Ec : forall k, cutK K k = (cutK K 0 + k * (4096 * fK K))%nat) by (intros k; unfold cutK; lia).
  rewrite (Ec 12%nat) in Hhi.
  assert (HF : exists F, F = (4096 * fK K)%nat) by eauto. destruct HF as [F EF]. rewrite <- EF in Ec, Hhi.
  assert (HD : exists dd, dd = (j - cutK K 0)%nat) by eauto. destruct HD as [dd Edd].
  assert (Hdd : (dd < F * 12)%nat) by lia.
  assert (Hm := Nat.mod_upper_bound dd F ltac:(lia)).
  assert (E1 := Nat.div_mod_eq dd F). assert (E2 := Nat.div_mod_eq (dd mod F) (fK K)).
  exists (dd / F)%nat, ((dd mod F) / fK K)%nat, ((dd mod F) mod fK K)%nat.
  split; [apply Nat.Div0.div_lt_upper_bound; exact Hdd|].
  split; [apply Nat.Div0.div_lt_upper_bound; lia|].
  split; [apply Nat.mod_upper_bound; lia|].
  rewrite Ec. nia.
Qed.

(** A node strictly inside a level is in a segment, at most its length from
    its cut. *)
Lemma node_seg :
  forall K j, (16 <= K)%nat -> (cutK K 0 < j <= cutK K 12)%nat ->
  exists k i, (k < 12)%nat /\ (i <= lenk (cutK K) k)%nat /\ j = (cutK K k + i)%nat.
Proof.
  intros K j HK Hj.
  destruct (Nat.eq_dec j (cutK K 12)) as [->|Hne].
  - exists 11%nat, (lenk (cutK K) 11). split; [lia|]. split; [lia|]. unfold lenk. assert (H := cutK_mono K 11 12 ltac:(lia)). lia.
  - destruct (row_split K j HK ltac:(lia)) as [k [i [t [Hk [Hi [Ht Ej]]]]]].
    exists k, (i * fK K + t)%nat. split; [exact Hk|]. split; [| lia].
    rewrite lenK. nia.
Qed.

(* ---------------------------------------------------------------- *)
(* Matrices                                                          *)

Lemma mnorm_I_plus :
  forall h (A : mat), 0 <= h -> mnorm 14 14 (fun r c => mI r c + h * A r c) <= 1 + h * mnorm 14 14 A.
Proof.
  intros h A Hh. eapply Rle_trans; [apply (mnorm_add_le 14 14 mI (fun r c => h * A r c))|].
  rewrite mnorm_scal_abs, Rabs_right by lra.
  assert (H1 := mnorm_mI 14). lra.
Qed.

Lemma gprodf_const : forall c a n, gprodf (fun _ => c) a n = c ^ n.
Proof. intros c a n. induction n as [|n IH]; cbn [gprodf pow]; [reflexivity | rewrite IH; ring]. Qed.

Lemma pow_le_exp : forall x n, 0 <= x -> (1 + x) ^ n <= exp (INR n * x).
Proof. intros x n Hx. apply pow_exp. exact Hx. Qed.

Lemma pow_mono_n : forall c n n', 1 <= c -> (n <= n')%nat -> c ^ n <= c ^ n'.
Proof.
  intros c n n' Hc Hn. replace n' with (n + (n' - n))%nat by lia. rewrite pow_add.
  assert (H1 : 1 <= c ^ (n' - n)) by (apply pow_R1_Rle; exact Hc).
  assert (H0 : 0 <= c ^ n) by (apply pow_le; lra). nra.
Qed.

(** A conjugate of an invertible matrix by an invertible pair is invertible. *)
Lemma is_inv_conj :
  forall (W Wi E Z : mat), is_inv 14 W Wi -> is_inv 14 E Z ->
  is_inv 14 (mm 14 (mm 14 Wi E) W) (mm 14 (mm 14 Wi Z) W).
Proof.
  intros W Wi E Z HW HE.
  assert (A1 : meq 14 (mm 14 W Wi) mI) by (intros i j Hi Hj; exact (proj2 (HW i j Hi Hj))).
  assert (A2 : meq 14 (mm 14 Wi W) mI) by (intros i j Hi Hj; exact (proj1 (HW i j Hi Hj))).
  assert (B1 : meq 14 (mm 14 Z E) mI) by (intros i j Hi Hj; exact (proj1 (HE i j Hi Hj))).
  assert (B2 : meq 14 (mm 14 E Z) mI) by (intros i j Hi Hj; exact (proj2 (HE i j Hi Hj))).
  assert (Gen : forall P Q, meq 14 (mm 14 Q P) mI ->
            meq 14 (mm 14 (mm 14 (mm 14 Wi Q) W) (mm 14 (mm 14 Wi P) W)) mI).
  { intros P Q HQP.
    eapply meq_trans; [apply mm_assoc_meq|].
    eapply meq_trans; [apply mm_meq; [apply meq_refl | apply meq_sym; apply mm_assoc_meq]|].
    eapply meq_trans; [apply mm_meq; [apply meq_refl | apply mm_meq; [apply meq_sym; apply mm_assoc_meq | apply meq_refl]]|].
    eapply meq_trans; [apply mm_meq; [apply meq_refl | apply mm_meq; [apply mm_meq; [exact A1 | apply meq_refl] | apply meq_refl]]|].
    eapply meq_trans; [apply mm_meq; [apply meq_refl | apply mm_meq; [apply mm_mI_meq_l | apply meq_refl]]|].
    eapply meq_trans; [apply meq_sym; apply mm_assoc_meq|].
    eapply meq_trans; [apply mm_meq; [apply mm_assoc_meq | apply meq_refl]|].
    eapply meq_trans; [apply mm_meq; [apply mm_meq; [apply meq_refl | exact HQP] | apply meq_refl]|].
    eapply meq_trans; [apply mm_meq; [apply mm_mI_meq_r | apply meq_refl]|].
    exact A2. }
  intros i j Hi Hj. split.
  - apply (Gen E Z B1); assumption.
  - apply (Gen Z E B2); assumption.
Qed.

Lemma is_inv_meq : forall A A' X, meq 14 A A' -> is_inv 14 A X -> is_inv 14 A' X.
Proof.
  intros A A' X HA HX i j Hi Hj. destruct (HX i j Hi Hj) as [H1 H2]. split.
  - rewrite (mm_ext 14 X X A' A i j) by (intros l Hl; first [reflexivity | symmetry; apply HA; assumption]). exact H1.
  - rewrite (mm_ext 14 A' A X X i j) by (intros l Hl; first [reflexivity | symmetry; apply HA; assumption]). exact H2.
Qed.

Lemma mv_scal_vec : forall n A a x i, mv n A (fun c => a * x c) i = a * mv n A x i.
Proof. intros n A a x i. unfold mv. rewrite <- msum_scal. apply msum_ext. intros; ring. Qed.

Lemma zjoin_lo : forall x p i, (i < 9)%nat -> zjoin x p i = x i.
Proof. intros x p i Hi. exact (zx_zjoin x p i Hi). Qed.

Lemma zjoin_hi : forall x p r, zjoin x p (9 + r)%nat = p r.
Proof. intros x p r. exact (zp_zjoin x p r). Qed.

(** The start rows [Pm(s + h, h), -h I] applied to a state. *)
Lemma mv_bC :
  forall s h x r, (r < 5)%nat -> mv 14 (bC s h) x r = mv 9 (bPm (s + h) h) x r - h * x (9 + r)%nat.
Proof.
  intros s h x r Hr. unfold mv. replace 14%nat with (9 + 5)%nat by reflexivity. rewrite msum_add. cbv beta.
  assert (A : msum (fun c => bC s h r c * x c) 9 = msum (fun c => bPm (s + h) h r c * x c) 9).
  { apply msum_ext. intros c Hc. unfold bC. rewrite (proj2 (Nat.ltb_lt c 9) Hc). reflexivity. }
  assert (B : msum (fun c => bC s h r (9 + c)%nat * x (9 + c)%nat) 5 = - h * x (9 + r)%nat).
  { rewrite (msum_single _ 5 r Hr).
    - cbv beta. unfold bC. replace (Nat.ltb (9 + r) 9) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (9 + r - 9)%nat with r by lia. rewrite Nat.eqb_refl. reflexivity.
    - intros c Hc Hcr. cbv beta. unfold bC. replace (Nat.ltb (9 + c) 9) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (9 + c - 9)%nat with c by lia. replace (Nat.eqb c r) with false by (symmetry; apply Nat.eqb_neq; lia).
      ring. }
  rewrite A, B. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* Every level                                                       *)

Section Lin.

Variable prec : F.precision.
Variables d kn : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs0 : imat.
Variable Rd : list (list (list (list (Z * Z)))).

Hypothesis Hcells : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hstart : forall WiI, owi prec frames 0 = Some WiI -> start_range prec d (mktab d) chh chh kn WiI = Some rs0.
Hypothesis Hok : assemble3d prec frames es cells rs0 Rd = true.

Let Wk : nat -> mat := Ws frames es.
Let Wik : nat -> mat := Wis frames es.

Lemma Wk_inv : forall k, (k < 12)%nat -> is_inv 14 (Wk k) (Wik k).
Proof. intros k Hk. exact (Ws_inv prec d Hd frames es cells rs0 Rd Hok k Hk). Qed.

Lemma HWW : forall k, (k < 12)%nat -> forall r c, (r < 14)%nat -> (c < 14)%nat -> mm 14 (Wik k) (Wk k) r c = mI r c.
Proof. intros k Hk r c Hr Hc. exact (proj1 (Wk_inv k Hk r c Hr Hc)). Qed.

Lemma HWW' : forall k, (k < 12)%nat -> forall r c, (r < 14)%nat -> (c < 14)%nat -> mm 14 (Wk k) (Wik k) r c = mI r c.
Proof. intros k Hk r c Hr Hc. exact (proj2 (Wk_inv k Hk r c Hr Hc)). Qed.

(** The step matrix of row j in frame k. *)
Let Ak (k K : nat) : nat -> mat := Aseg (gW frames k) (ge es k) (Xk frames k) K.

Lemma Ak_cell :
  forall k K i t, (k < 12)%nat -> (16 <= K)%nat -> (i < 4096)%nat -> (t < fK K)%nat ->
  icont 14 14 (gcell cells k i) (Ak k K (cutK K k + i * fK K + t)%nat).
Proof.
  intros k K i t Hk HK Hi Ht.
  destruct (Xk_inv prec d Hd frames es cells rs0 Rd Hok k Hk) as [HX [_ Howi]].
  exact (Aseg_cell prec d Hcov Hd kn (gW frames k) (gD frames k) (gWiI prec frames k) (ge es k) k (gcell cells k)
           Howi (Hcells k _ Hk Howi) (Xk frames k) HX K i t HK Hi Ht).
Qed.

Lemma Ak_nu :
  forall k K i t, (k < 12)%nat -> (16 <= K)%nat -> (i < 4096)%nat -> (t < fK K)%nat ->
  mnorm 14 14 (Ak k K (cutK K k + i * fK K + t)%nat) <= nu prec (gcell cells k i).
Proof.
  intros k K i t Hk HK Hi Ht.
  destruct (checks prec d Hd frames es cells rs0 Rd Hok) as (_ & Hc & _).
  exact (proj2 (proj1 (cell_ok_sound prec (gcell cells k i) (Hc k i Hk Hi)) _ (Ak_cell k K i t Hk HK Hi Ht))).
Qed.

(** The largest bound of a segment's reference steps. *)
Definition nuk (k : nat) : R := fmax (fun i => nu prec (gcell cells k i)) 4096.

Lemma Ak_nuk :
  forall k K j, (k < 12)%nat -> (16 <= K)%nat -> (cutK K k <= j < cutK K k + lenk (cutK K) k)%nat ->
  mnorm 14 14 (Ak k K j) <= nuk k.
Proof.
  intros k K j Hk HK Hj. rewrite lenK in Hj.
  assert (Hf := fK_pos K).
  set (dd := (j - cutK K k)%nat).
  assert (Hi : (dd / fK K < 4096)%nat) by (apply Nat.Div0.div_lt_upper_bound; unfold dd; lia).
  assert (Ht : (dd mod fK K < fK K)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Ej : j = (cutK K k + dd / fK K * fK K + dd mod fK K)%nat).
  { assert (E := Nat.div_mod_eq dd (fK K)). unfold dd in *. lia. }
  rewrite Ej. eapply Rle_trans; [apply (Ak_nu k K _ _ Hk HK Hi Ht)|].
  unfold nuk. apply (fmax_ge (fun i => nu prec (gcell cells k i))). exact Hi.
Qed.

Lemma nuk_nonneg : forall k, 0 <= nuk k.
Proof. intros k. apply fmax_nonneg. Qed.

(** A level's step in frame k is I + h A. *)
Lemma Psi_conj :
  forall k K a n, (k < 12)%nat ->
  meq 14 (mm 14 (mm 14 (Wk k) (mprod 14 (PsiK K) a n)) (Wik k)) (mprod 14 (fstep (Ak k K) (hK K)) a n).
Proof.
  intros k K a n Hk.
  eapply meq_trans; [apply meq_sym; apply mprod_conj; [exact (HWW k Hk) | exact (HWW' k Hk)]|].
  apply mprod_ext. intros i Hi. cbv beta. unfold PsiK, fstep, Ak, Aseg. fold (Ws frames es k) (Wis frames es k).
  apply (conj_step 14 (Wk k) (Wik k)). exact (HWW' k Hk).
Qed.

Lemma unconj :
  forall k (P Q : mat), (k < 12)%nat -> meq 14 (mm 14 (mm 14 (Wk k) P) (Wik k)) Q ->
  meq 14 P (mm 14 (mm 14 (Wik k) Q) (Wk k)).
Proof.
  intros k P Q Hk H.
  assert (A1 : meq 14 (mm 14 (Wik k) (Wk k)) mI) by (intros i j Hi Hj; exact (HWW k Hk i j Hi Hj)).
  apply meq_sym.
  eapply meq_trans; [apply mm_meq; [apply mm_meq; [apply meq_refl | apply meq_sym; exact H] | apply meq_refl]|].
  eapply meq_trans; [apply mm_meq; [apply meq_sym; apply mm_assoc_meq | apply meq_refl]|].
  eapply meq_trans; [apply mm_meq; [apply mm_meq; [apply meq_sym; apply mm_assoc_meq | apply meq_refl] | apply meq_refl]|].
  eapply meq_trans; [apply mm_meq; [apply mm_meq; [apply mm_meq; [exact A1 | apply meq_refl] | apply meq_refl] | apply meq_refl]|].
  eapply meq_trans; [apply mm_meq; [apply mm_meq; [apply mm_mI_meq_l | apply meq_refl] | apply meq_refl]|].
  eapply meq_trans; [apply mm_assoc_meq|].
  eapply meq_trans; [apply mm_meq; [apply meq_refl | exact A1]|].
  apply mm_mI_meq_r.
Qed.

(** The propagator over a part of a segment, through the frame. *)
Definition Gk (k : nat) : R := mnorm 14 14 (Wik k) * exp (nuk k / 16) * mnorm 14 14 (Wk k).

Lemma seg_prod_bound :
  forall K k i i', (16 <= K)%nat -> (k < 12)%nat -> (i <= i' <= lenk (cutK K) k)%nat ->
  mnorm 14 14 (mprod 14 (PsiK K) (cutK K k + i) (i' - i)) <= Gk k.
Proof.
  intros K k i i' HK Hk Hii.
  assert (Hh := hK_pos K).
  set (P := mprod 14 (PsiK K) (cutK K k + i) (i' - i)).
  assert (HP := unconj k P _ Hk (Psi_conj k K (cutK K k + i) (i' - i) Hk)).
  rewrite (mnorm_meq 14 _ _ HP).
  eapply Rle_trans; [apply mnorm_mm|].
  eapply Rle_trans; [apply Rmult_le_compat_r; [apply mnorm_nonneg | apply mnorm_mm]|].
  unfold Gk. apply Rmult_le_compat_r; [apply mnorm_nonneg|].
  apply Rmult_le_compat_l; [apply mnorm_nonneg|].
  (* the product of the steps in the frame *)
  assert (Hn0 := nuk_nonneg k).
  eapply Rle_trans.
  { apply (mprod_norm 14 (fstep (Ak k K) (hK K)) (fun _ => 1 + hK K * nuk k)); [lia|].
    intros l Hl. eapply Rle_trans; [apply mnorm_I_plus; lra|].
    apply Rplus_le_compat_l. apply Rmult_le_compat_l; [lra|].
    apply Ak_nuk; [exact Hk | exact HK | rewrite lenK in *; lia]. }
  rewrite gprodf_const.
  eapply Rle_trans; [apply (pow_mono_n _ _ (lenk (cutK K) k)); [nra | lia]|].
  eapply Rle_trans; [apply pow_le_exp; nra|].
  rewrite lenK, mult_INR.
  replace (INR 4096 * INR (fK K) * (hK K * nuk k)) with (INR 4096 * (INR (fK K) * hK K) * nuk k) by ring.
  rewrite fK_h by exact HK. right. f_equal. replace (INR 4096) with 4096 by (cbn; ring). field.
Qed.

Lemma Gk_nonneg : forall k, 0 <= Gk k.
Proof.
  intros k. unfold Gk. apply Rmult_le_pos; [apply Rmult_le_pos; [apply mnorm_nonneg | left; apply exp_pos] | apply mnorm_nonneg].
Qed.

(** The constants, sums over the twelve frames. *)
Definition Gall : R := msum Gk 12.
Definition Wmax : R := msum (fun k => mnorm 14 14 (Wk k)) 12.
Definition Wimax : R := msum (fun k => mnorm 14 14 (Wik k)) 12.

Lemma msum_ge12 : forall (f : nat -> R) k, (forall l, 0 <= f l) -> (k < 12)%nat -> f k <= msum f 12.
Proof. intros f k Hf Hk. apply (msum_ge f 12 k); [intros; apply Hf | exact Hk]. Qed.

(* ---------------------------------------------------------------- *)
(* The rows and the recursion                                        *)

(** M_j has an inverse at every row of a level. *)
Lemma M3_inv :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  exists X, is_inv 9 (mstack (Pp3 K j) (Up3 K j)) X.
Proof.
  intros K j HK Hj.
  destruct (row_split K j HK Hj) as [k [i [t [Hk [Hi [Ht Ej]]]]]].
  destruct (Xk_inv prec d Hd frames es cells rs0 Rd Hok k Hk) as [_ [HXc Howi]].
  destruct (cell_point K k i t HK Hi Ht) as [Hsub [Hu [Hw Hp]]].
  assert (Hj16 : (i / 16 < 256)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hq : (i mod 16 < 2 ^ 4)%nat) by (change (2 ^ 4)%nat with 16%nat; apply Nat.mod_upper_bound; lia).
  destruct (cell_ranges_sound prec d Hcov Hd (csc k (i / 16)) chh chalf chh kn 4 (gW frames k) (gWiI prec frames k) _
              (Xk frames k) (Hcells k _ Hk Howi _ Hj16) HXc (i mod 16) _ _ Hq Hsub Hu Hw Hp) as [HM _].
  replace (dyadR (csc k (i / 16)) + (INR (cutK K k + i * fK K + t) * hK K - dyadR (csc k (i / 16))))
    with (INR j * hK K) in HM by (rewrite Ej; ring).
  replace (dyadR chh + (hK K - dyadR chh)) with (hK K) in HM by ring.
  exact HM.
Qed.

Lemma Mi3_inv :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat -> is_inv 9 (mstack (Pp3 K j) (Up3 K j)) (Mi3 K j).
Proof. intros K j HK Hj. destruct (M3_inv K j HK Hj) as [X HX]. exact (minv_inv 9 _ X HX). Qed.

(** Recur's step at row j is the level's step with the row's source. *)
Lemma step3 :
  forall K j, (16 <= K)%nat -> (cutK K 0 <= j < cutK K 12)%nat ->
  forall z rs ru i, (i < 14)%nat ->
  step (hK K) (Pm3 K) (Sx3 K) (V3 K) (Mi3 K) j z rs ru i = mv 14 (PsiK K j) z i + hK K * zeta3 K j rs ru i.
Proof.
  intros K j HK Hj z rs ru i Hi.
  unfold Mi3. rewrite (step_N (hK K) (hK_pos K) (Pp3 K) (Pm3 K) (Sx3 K) (Up3 K) (V3 K) j (M3_inv K j HK Hj) z rs ru i Hi).
  unfold PsiK. rewrite mv_madd_mat, mv_scal_mat, mv_mI by exact Hi.
  assert (E : Pm3 K (S j) = bPm (INR j * hK K + hK K) (hK K)) by (unfold Pm3; rewrite INR_S_h; reflexivity).
  unfold zeta3. rewrite E. unfold bN, Pp3, Sx3, Up3, V3. ring.
Qed.

(** The start rows of the level's system are the start condition at m + 1
    seen from m. *)
Lemma start_cond :
  forall K x, (16 <= K)%nat -> forall r, (r < 5)%nat ->
  mv 14 (bCs (/ 4) (hK K)) x r
  = mv 9 (Pm3 K (S (cutK K 0))) (mv 14 (PsiK K (cutK K 0)) x) r - hK K * mv 14 (PsiK K (cutK K 0)) x (9 + r)%nat.
Proof.
  intros K x HK r Hr.
  assert (EP : PsiK K (cutK K 0) = fun i c => mI i c + hK K * bN (/ 4) (hK K) i c)
    by (unfold PsiK; rewrite INR_cut0 by exact HK; reflexivity).
  assert (EPm : Pm3 K (S (cutK K 0)) = bPm (/ 4 + hK K) (hK K))
    by (unfold Pm3; rewrite INR_S_h, INR_cut0 by exact HK; reflexivity).
  rewrite EP, EPm. unfold bCs. rewrite <- mv_mm_r. apply mv_bC. exact Hr.
Qed.

(** The first step of every level has an inverse: in frame 0 it is I + h A
    with h |A| <= 2^-16 nu < 1. *)
Lemma Psi0_inv : forall K, (16 <= K)%nat -> exists Y, is_inv 14 (PsiK K (cutK K 0)) Y.
Proof.
  intros K HK.
  assert (Hh := hK_pos K). assert (Hle := hK_le K HK).
  assert (E0 : (cutK K 0 + 0 * fK K + 0)%nat = cutK K 0) by lia.
  pose proof (Ak_nu 0 K 0 0 ltac:(lia) HK ltac:(lia) (fK_pos K)) as HA. rewrite E0 in HA.
  destruct (checks prec d Hd frames es cells rs0 Rd Hok) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  unfold psi0_ok in H10.
  assert (Hnu : contains (I.convert (inu prec (gcell cells 0 0))) (Xreal (nu prec (gcell cells 0 0)))) by apply iupmax_in.
  assert (Hhr : contains (I.convert (ihr prec)) (Xreal hr)) by apply dyad_correct.
  assert (Hs := I.sub_correct prec _ _ (Xreal (IZR 1)) _ (I.fromZ_correct prec 1) (I.mul_correct prec _ _ _ _ Hhr Hnu)).
  apply (sign_pos _ _ Hs) in H10.
  assert (Ehr : hr = / 65536) by (unfold hr, dyadR; cbn [fst snd]; rewrite pRZ16; ring).
  set (A := Ak 0%nat K (cutK K 0)) in HA.
  set (th := hK K * mnorm 14 14 A).
  assert (Hth : th < 1).
  { unfold th. assert (hK K * mnorm 14 14 A <= hr * nu prec (gcell cells 0 0)).
    { rewrite Ehr. apply Rmult_le_compat; [lra | apply mnorm_nonneg | lra | exact HA]. }
    lra. }
  set (E := fun r c => mI r c + hK K * A r c).
  assert (HD : forall M, meq 14 M E -> mnorm 14 14 (msub mI M) <= th).
  { intros M HM. rewrite (mnorm_meq 14 _ (fun r c => (- hK K) * A r c)).
    - rewrite mnorm_scal_abs, Rabs_Ropp, Rabs_right by lra. unfold th. lra.
    - intros r c Hr Hc. unfold msub. rewrite HM by assumption. unfold E. ring. }
  destruct (approx_inverse 14 E mI th (HD _ (mm_mI_meq_l 14 E)) (HD _ (mm_mI_meq_r 14 E)) Hth) as [Z [HZ1 [HZ2 _]]].
  assert (HZ : is_inv 14 E Z) by (intros i j Hi Hj; split; [apply HZ1 | apply HZ2]; assumption).
  assert (HC : meq 14 (mm 14 (mm 14 (Wk 0%nat) (PsiK K (cutK K 0))) (Wik 0%nat)) E).
  { unfold PsiK. eapply meq_trans; [apply (conj_step 14 (Wk 0%nat) (Wik 0%nat) (HWW' 0 ltac:(lia)))|].
    intros r c Hr Hc. reflexivity. }
  assert (HU := unconj 0 _ _ ltac:(lia) HC).
  exists (mm 14 (mm 14 (Wik 0%nat) Z) (Wk 0%nat)).
  apply (is_inv_meq (mm 14 (mm 14 (Wik 0%nat) E) (Wk 0%nat))).
  - apply meq_sym. exact HU.
  - apply is_inv_conj; [exact (Wk_inv 0 ltac:(lia)) | exact HZ].
Qed.

Lemma vnorm_zero : forall n, vnorm n (fun _ => 0) = 0.
Proof.
  intros n. apply Rle_antisym; [| apply vnorm_nonneg].
  apply vnorm_le; [lra|]. intros i _. rewrite Rabs_R0. lra.
Qed.

(** The rows' sources as the recursion's, none at the node m. *)
Definition src3 (K : nat) (rs ru : nat -> vec) (j : nat) : vec :=
  if Nat.eqb j (cutK K 0) then (fun _ => 0) else zeta3 K j (rs j) (ru j).

Lemma swt_src3 : forall K rs ru, (16 <= K)%nat -> swt (hK K) 12 (cutK K) (src3 K rs ru) = srcw K rs ru.
Proof.
  intros K rs ru HK. assert (Hh := hK_pos K). assert (Hm := cutK_0_pos K).
  assert (H12 : (cutK K 0 < cutK K 12)%nat) by (rewrite cutK_12 by exact HK; lia).
  unfold swt, srcw. replace (cutK K 12 - cutK K 0)%nat with (1 + (cutK K 12 - S (cutK K 0)))%nat by lia.
  rewrite msum_add. cbn [msum]. rewrite Nat.add_0_r.
  unfold src3 at 1. rewrite Nat.eqb_refl, vnorm_zero, Rmult_0_r, Rplus_0_l, Rplus_0_l.
  apply msum_ext. intros l Hl. unfold src3.
  replace (Nat.eqb (cutK K 0 + (1 + l)) (cutK K 0)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (cutK K 0 + (1 + l))%nat with (S (cutK K 0) + l)%nat by lia.
  rewrite Rabs_right by lra. reflexivity.
Qed.

(** For every source the rows have a solution. *)
Theorem lin_exists :
  forall K, (16 <= K)%nat -> forall rs ru : nat -> vec,
  exists X : nat -> vec,
    (forall j i, (j <= cutK K 0)%nat -> X j i = 0) /\
    (forall i, (i < 9)%nat -> X (cutK K 12) i = 0) /\
    (forall j, (cutK K 0 < j < cutK K 12)%nat ->
       (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs j i) /\
       (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru j i)).
Proof.
  intros K HK rs ru.
  assert (Hh := hK_pos K). assert (Hm0 := cutK_0_pos K).
  assert (H12 : (cutK K 0 < cutK K 12)%nat) by (rewrite cutK_12 by exact HK; lia).
  destruct (assemble3d_sound prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hstart Hok) as [q Hq].
  destruct (Hq K HK) as [XK [_ [HXr _]]].
  destruct (run_exists (hK K) (PsiK K) 12 ltac:(lia) (cutK K) (fun k _ => cutK_mono K k (S k) (Nat.le_succ_diag_r k))
              Wk Wik HWW (bCs (/ 4) (hK K)) (Wk 11%nat) (Wik 11%nat) (HWW 11 ltac:(lia)) XK HXr (src3 K rs ru))
    as [z [Hrun [Hs He]]].
  assert (Hza : forall r, (r < 14)%nat -> z (S (cutK K 0)) r = mv 14 (PsiK K (cutK K 0)) (z (cutK K 0)) r).
  { intros r Hr. rewrite (Hrun (cutK K 0) ltac:(lia) r Hr). unfold src3. rewrite Nat.eqb_refl. cbv beta. ring. }
  assert (Hst : forall i, (i < 5)%nat ->
            zp (z (S (cutK K 0))) i = mv 9 (Pm3 K (S (cutK K 0))) (zx (z (S (cutK K 0)))) i / hK K).
  { intros i Hi. assert (H0 := Hs i Hi). rewrite (start_cond K (z (cutK K 0)) HK i Hi) in H0.
    rewrite <- (Hza (9 + i)%nat ltac:(lia)) in H0.
    rewrite (mv_extn 9 (Pm3 K (S (cutK K 0))) (mv 14 (PsiK K (cutK K 0)) (z (cutK K 0))) (z (S (cutK K 0))) i)
      in H0 by (intros c Hc; symmetry; apply Hza; lia).
    unfold zp, zx. change (fun i0 => z (S (cutK K 0)) i0) with (z (S (cutK K 0))).
    replace (mv 9 (Pm3 K (S (cutK K 0))) (z (S (cutK K 0))) i) with (hK K * z (S (cutK K 0)) (9 + i)%nat) by lra.
    field. lra. }
  assert (Hrun' : forall j, (S (cutK K 0) <= j < S (cutK K 0) + (cutK K 12 - S (cutK K 0)))%nat ->
            forall i, (i < 14)%nat -> z (S j) i = step (hK K) (Pm3 K) (Sx3 K) (V3 K) (Mi3 K) j (z j) (rs j) (ru j) i).
  { intros j Hj i Hi. rewrite (Hrun j ltac:(lia) i Hi). rewrite (step3 K j HK ltac:(lia) (z j) (rs j) (ru j) i Hi).
    unfold src3. replace (Nat.eqb j (cutK K 0)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
  assert (Hinv : forall j, (S (cutK K 0) <= j < S (cutK K 0) + (cutK K 12 - S (cutK K 0)))%nat ->
            forall i k, (i < 9)%nat -> (k < 9)%nat -> mm 9 (M (Pp3 K) (Up3 K) j) (Mi3 K j) i k = mI i k).
  { intros j Hj i k Hi Hk. exact (proj2 (Mi3_inv K j HK ltac:(lia) i k Hi Hk)). }
  exists (nodes (S (cutK K 0)) z). split; [| split].
  - intros j i Hj. unfold nodes. rewrite (proj2 (Nat.ltb_lt j (S (cutK K 0))) ltac:(lia)). reflexivity.
  - intros i Hi. unfold nodes. rewrite (proj2 (Nat.ltb_ge (cutK K 12) (S (cutK K 0))) ltac:(lia)).
    unfold zx. apply He. exact Hi.
  - intros j Hj.
    exact (step_rows (hK K) Hh (Pp3 K) (Pm3 K) (Sx3 K) (Up3 K) (V3 K) (Mi3 K) (S (cutK K 0))
             (cutK K 12 - S (cutK K 0)) z rs ru ltac:(lia) Hst Hrun' Hinv j ltac:(lia)).
Qed.

(** Every solution of the rows is bounded by its sources, with one constant
    for every level. *)
Theorem lin_bound :
  exists S, 0 <= S /\
  forall K, (16 <= K)%nat -> forall (rs ru : nat -> vec) (X : nat -> vec),
  (forall i, (i < 9)%nat -> X (cutK K 0) i = 0) ->
  (forall i, (i < 9)%nat -> X (cutK K 12) i = 0) ->
  (forall j, (cutK K 0 < j < cutK K 12)%nat ->
     (forall i, (i < 5)%nat -> rs_row (hK K) (Pp3 K) (Pm3 K) (Sx3 K) X j i = rs j i) /\
     (forall i, (i < 4)%nat -> ru_row (hK K) (Up3 K) (V3 K) X j i = ru j i)) ->
  forall j, (cutK K 0 < j <= cutK K 12)%nat ->
  vnorm 14 (state (hK K) (Pm3 K) X j) <= S * srcw K rs ru.
Proof.
  destruct (assemble3d_sound prec d kn Hcov Hd frames es cells rs0 Rd Hcells Hstart Hok) as [q Hq].
  assert (Hq0 : 0 <= q).
  { destruct (Hq 16%nat ltac:(lia)) as [X16 [_ [_ H16]]]. eapply Rle_trans; [apply mnorm_nonneg | exact H16]. }
  assert (HG0 : 0 <= Gall) by (apply msum_nonneg; intros; apply Gk_nonneg).
  assert (HW0 : 0 <= Wmax) by (apply msum_nonneg; intros; apply mnorm_nonneg).
  assert (HWi0 : 0 <= Wimax) by (apply msum_nonneg; intros; apply mnorm_nonneg).
  exists (Gall * (Wimax * (q * (Wmax * Gall))) + Gall). split.
  { apply Rplus_le_le_0_compat; [| exact HG0].
    repeat (apply Rmult_le_pos; try assumption). }
  intros K HK rs ru X HXm HXe Hrows j Hj.
  assert (Hh := hK_pos K). assert (Hm0 := cutK_0_pos K).
  assert (H12 : (cutK K 0 < cutK K 12)%nat) by (rewrite cutK_12 by exact HK; lia).
  destruct (Hq K HK) as [XK [HXl [_ HXq]]].
  destruct (Psi0_inv K HK) as [Y HY].
  set (st := state (hK K) (Pm3 K) X).
  set (z := fun l => if Nat.eqb l (cutK K 0) then mv 14 Y (st (S (cutK K 0))) else st l).
  assert (Hz : forall l, l <> cutK K 0 -> z l = st l).
  { intros l Hl. unfold z. replace (Nat.eqb l (cutK K 0)) with false by (symmetry; apply Nat.eqb_neq; exact Hl).
    reflexivity. }
  assert (HPY : forall r, (r < 14)%nat -> mv 14 (PsiK K (cutK K 0)) (z (cutK K 0)) r = st (S (cutK K 0)) r).
  { intros r Hr. unfold z. rewrite Nat.eqb_refl.
    apply mv_inv_cancel; [intros i k Hi Hk; exact (proj2 (HY i k Hi Hk)) | exact Hr]. }
  (* the states form a run with the rows' sources *)
  assert (Hrun : runs (hK K) (PsiK K) z (src3 K rs ru) (cutK K 0) (cutK K 12)).
  { intros l Hl r Hr.
    destruct (Nat.eq_dec l (cutK K 0)) as [->|Hne].
    - rewrite (Hz (S (cutK K 0))) by lia. rewrite HPY by exact Hr.
      unfold src3. rewrite Nat.eqb_refl. cbv beta. ring.
    - rewrite (Hz (S l)) by lia. rewrite (Hz l Hne).
      destruct (Hrows l ltac:(lia)) as [Hs Hu].
      unfold st. rewrite <- (rows_step (hK K) Hh (Pp3 K) (Pm3 K) (Sx3 K) (Up3 K) (V3 K) (Mi3 K) X (rs l) (ru l) l
                              (fun i k Hi Hk => proj1 (Mi3_inv K l HK ltac:(lia) i k Hi Hk)) Hs Hu r Hr).
      rewrite (step3 K l HK ltac:(lia) _ (rs l) (ru l) r Hr).
      unfold src3. replace (Nat.eqb l (cutK K 0)) with false by (symmetry; apply Nat.eqb_neq; exact Hne).
      reflexivity. }
  (* the start condition *)
  assert (Hst : forall r, (r < 5)%nat -> mv 14 (bCs (/ 4) (hK K)) (z (cutK K 0)) r = 0).
  { intros r Hr. rewrite (start_cond K (z (cutK K 0)) HK r Hr).
    rewrite (HPY (9 + r)%nat ltac:(lia)).
    rewrite (mv_extn 9 (Pm3 K (S (cutK K 0))) (mv 14 (PsiK K (cutK K 0)) (z (cutK K 0))) (X (S (cutK K 0))) r).
    2: { intros c Hc. rewrite HPY by lia. unfold st, state. apply zjoin_lo. exact Hc. }
    unfold st, state. rewrite zjoin_hi.
    rewrite (mv_extn 9 (Pm3 K (S (cutK K 0))) (slope (hK K) X (S (cutK K 0))) (fun c => / hK K * X (S (cutK K 0)) c) r).
    2: { intros c Hc. unfold slope. replace (S (cutK K 0) - 1)%nat with (cutK K 0) by lia. rewrite HXm by exact Hc.
         field. lra. }
    rewrite mv_scal_vec. field. lra. }
  (* the end condition *)
  assert (Hen : forall r, (r < 9)%nat -> z (cutK K 12) r = 0).
  { intros r Hr. rewrite Hz by lia. unfold st, state. rewrite zjoin_lo by exact Hr. apply HXe. exact Hr. }
  (* the bound of the run *)
  destruct (node_seg K j HK Hj) as [k [i [Hk [Hi Ej]]]].
  assert (HB := run_bound (hK K) (PsiK K) 12 ltac:(lia) (cutK K) (fun k _ => cutK_mono K k (S k) (Nat.le_succ_diag_r k))
                  Wk Wik HWW (bCs (/ 4) (hK K)) (Wk 11%nat) XK q Gall Wmax Wimax HXl HXq
                  (fun k Hk i i' Hii => Rle_trans _ _ _ (seg_prod_bound K k i i' HK Hk Hii)
                                          (msum_ge12 Gk k Gk_nonneg Hk))
                  (fun k Hk => msum_ge12 (fun k => mnorm 14 14 (Wk k)) k (fun _ => mnorm_nonneg _ _ _) Hk)
                  (msum_ge12 (fun k => mnorm 14 14 (Wk k)) 11 (fun _ => mnorm_nonneg _ _ _) ltac:(lia))
                  (fun k Hk => msum_ge12 (fun k => mnorm 14 14 (Wik k)) k (fun _ => mnorm_nonneg _ _ _) Hk)
                  z (src3 K rs ru) Hrun Hst Hen k i Hk Hi).
  rewrite <- Ej in HB. rewrite (Hz j) in HB by lia. rewrite swt_src3 in HB by exact HK.
  fold st. eapply Rle_trans; [exact HB|]. right. ring.
Qed.

End Lin.
