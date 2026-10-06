(** Multiple shooting with the boundary conditions as constraint rows.

    A run of the recursion z_{j+1} = Psi_j z_j + h src_j over the rows
    cut 0, ..., cut nseg is cut into nseg segments. Its unknowns are the states
    at the first nseg cuts in segment coordinates, zeta_k = W_k z_{cut k}, and
    the free part p of the last state, whose coefficient part must vanish.
    The system has nseg + 1 block rows of 14:

      Cs Wi_0 zeta_0 = 0                       (the start condition, 5 rows,
                                               padded with rows that zero the
                                               9 unused entries of p's group)
      zeta_{k+1} - W_{k+1} Y_k Wi_k zeta_k = W_{k+1} pi_k   (junction k)
      We Y_last Wi_last zeta_last - We E0 p = - We pi_last (the end)

    with Y_k the propagator and pi_k the particular solution of segment k,
    E0 p = (0, p). [msys] is that matrix laid out flat with 14 x 14 blocks.
    [run_solves] reads a run satisfying both conditions as a solution of the
    system, and [solves_run] reads a solution of the system back as such a
    run. With a two-sided inverse of the flat matrix, every run satisfying the
    boundary conditions is bounded by the sources ([run_bound]), and for every
    source there is one ([run_exists]). *)

From Coq Require Import Reals Bool Lra Lia.
From Stellarocq Require Import Mat Shoot Recur.

Local Open Scope R_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------- *)
(* Vectors and matrices of 14                                        *)

Lemma mv_extn : forall n A x y i, (forall k, (k < n)%nat -> x k = y k) -> mv n A x i = mv n A y i.
Proof. intros n A x y i H. unfold mv. apply msum_ext. intros k Hk. rewrite H by exact Hk. reflexivity. Qed.

Lemma mv_add : forall n A x y i, mv n A (fun k => x k + y k) i = mv n A x i + mv n A y i.
Proof. intros n A x y i. unfold mv. rewrite <- msum_plus. apply msum_ext. intros; ring. Qed.

Lemma mv_sub : forall n A x y i, mv n A (fun k => x k - y k) i = mv n A x i - mv n A y i.
Proof. intros n A x y i. unfold mv. rewrite <- msum_minus. apply msum_ext. intros; ring. Qed.

Lemma mv_neg_mat : forall n A x i, mv n (fun r c => - A r c) x i = - mv n A x i.
Proof.
  intros n A x i. unfold mv.
  replace (- msum (fun j => A i j * x j) n) with (-1 * msum (fun j => A i j * x j) n) by ring.
  rewrite <- msum_scal. apply msum_ext. intros; ring.
Qed.

Lemma mv_zero_mat : forall n x i, mv n (fun _ _ => 0) x i = 0.
Proof. intros n x i. unfold mv. rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero. Qed.

Lemma mv_zero_vec : forall n A i, mv n A (fun _ => 0) i = 0.
Proof. intros n A i. unfold mv. rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero. Qed.

Lemma mv_mm_r : forall n A B x i, mv n A (mv n B x) i = mv n (mm n A B) x i.
Proof. intros n A B x i. symmetry. apply mv_mm. Qed.

(** An inverse on the right of a product cancels. *)
Lemma mv_inv_cancel :
  forall n A Ai x i, (forall r c, (r < n)%nat -> (c < n)%nat -> mm n Ai A r c = mI r c) ->
  (i < n)%nat -> mv n Ai (mv n A x) i = x i.
Proof.
  intros n A Ai x i H Hi. rewrite mv_mm_r. unfold mv.
  rewrite (msum_ext _ (fun k => mI i k * x k)) by (intros k Hk; rewrite H by assumption; reflexivity).
  fold (mv n mI x i). apply mv_mI. exact Hi.
Qed.

(** vnorm of a matrix-vector product. *)
Lemma vnorm_mv : forall n A x, vnorm n (mv n A x) <= mnorm n n A * vnorm n x.
Proof. intros n A x. apply mv_bound. Qed.

Lemma vnorm_scal : forall n a x, vnorm n (fun c => a * x c) = Rabs a * vnorm n x.
Proof.
  intros n a x. unfold vnorm. induction n as [|n IH]; cbn [fmax]; [ring|].
  rewrite IH, Rabs_mult. rewrite RmaxRmult by apply Rabs_pos. reflexivity.
Qed.

Lemma vnorm_ext : forall n x y, (forall k, (k < n)%nat -> x k = y k) -> vnorm n x = vnorm n y.
Proof.
  intros n x y H. unfold vnorm. apply Rle_antisym; apply fmax_mono; intros i Hi; rewrite H by exact Hi; lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Flat matrices of 14 x 14 blocks                                   *)

Definition flat (B : nat -> nat -> mat) : mat :=
  fun r c => B (r / 14)%nat (c / 14)%nat (r mod 14)%nat (c mod 14)%nat.

Definition blk (u : vec) (J : nat) : vec := fun j => u (14 * J + j)%nat.

Lemma msum_add : forall f a b, msum f (a + b) = msum f a + msum (fun c => f (a + c)%nat) b.
Proof.
  intros f a b. induction b as [|b IH]; cbn [msum].
  - rewrite Nat.add_0_r. ring.
  - rewrite Nat.add_succ_r. cbn [msum]. rewrite IH. ring.
Qed.

Lemma msum_blocks :
  forall f ng, msum f (14 * ng) = msum (fun J => msum (fun j => f (14 * J + j)%nat) 14) ng.
Proof.
  intros f ng. induction ng as [|ng IH]; [reflexivity|].
  replace (14 * S ng)%nat with (14 * ng + 14)%nat by lia.
  rewrite msum_add, IH. reflexivity.
Qed.

Lemma div14 : forall J j, (j < 14)%nat -> ((14 * J + j) / 14)%nat = J.
Proof. intros J j Hj. symmetry. apply (Nat.div_unique (14 * J + j) 14 J j); lia. Qed.

Lemma mod14 : forall J j, (j < 14)%nat -> ((14 * J + j) mod 14)%nat = j.
Proof. intros J j Hj. symmetry. apply (Nat.mod_unique (14 * J + j) 14 J j); lia. Qed.

Lemma flat_mv :
  forall B ng u (I i : nat), (i < 14)%nat ->
  mv (14 * ng) (flat B) u (14 * I + i)%nat = msum (fun J => mv 14 (B I J) (blk u J) i) ng.
Proof.
  intros B ng u I i Hi. unfold mv. rewrite msum_blocks. apply msum_ext. intros J HJ.
  apply msum_ext. intros j Hj. unfold flat, blk. rewrite !div14, !mod14 by assumption. reflexivity.
Qed.

(** A flat vector from its blocks. *)
Definition unblk (U : nat -> vec) : vec := fun r => U (r / 14)%nat (r mod 14)%nat.

Lemma blk_unblk : forall U J j, (j < 14)%nat -> blk (unblk U) J j = U J j.
Proof. intros U J j Hj. unfold blk, unblk. rewrite div14, mod14 by exact Hj. reflexivity. Qed.

(** A sum over the blocks with two nonzero terms. *)
Lemma msum_le_prefix :
  forall f a b, (forall j, 0 <= f j) -> (a <= b)%nat -> msum f a <= msum f b.
Proof.
  intros f a b Hf Hab. replace b with (a + (b - a))%nat by lia. rewrite msum_add.
  assert (0 <= msum (fun c => f (a + c)%nat) (b - a)) by (apply msum_nonneg; intros; apply Hf). lra.
Qed.

Lemma msum_two :
  forall f ng a b, (a < ng)%nat -> (b < ng)%nat -> a <> b ->
  (forall J, (J < ng)%nat -> J <> a -> J <> b -> f J = 0) ->
  msum f ng = f a + f b.
Proof.
  intros f ng a b Ha Hb Hab H.
  rewrite (msum_ext f (fun J => (if Nat.eqb J a then f J else 0) + (if Nat.eqb J a then 0 else f J))).
  2: { intros J HJ. destruct (Nat.eqb J a); ring. }
  rewrite msum_plus. f_equal.
  - rewrite (msum_single (fun J => if Nat.eqb J a then f J else 0) ng a Ha).
    + rewrite Nat.eqb_refl. reflexivity.
    + intros J HJ HJa. destruct (Nat.eqb_spec J a); [contradiction | reflexivity].
  - rewrite (msum_single _ ng b Hb).
    + destruct (Nat.eqb_spec b a); [lia | reflexivity].
    + intros J HJ HJb. destruct (Nat.eqb_spec J a); [reflexivity|]. apply H; assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Runs of the recursion                                             *)

Section Run.

Variable h : R.
Variable Psi : nat -> mat.

(** From the zero state at row a, i steps with sources. *)
Fixpoint part (src : nat -> vec) (a i : nat) : vec :=
  match i with
  | O => fun _ => 0
  | S i' => fun r => mv 14 (Psi (a + i')%nat) (part src a i') r + h * src (a + i')%nat r
  end.

Definition runs (z src : nat -> vec) (a b : nat) : Prop :=
  forall j, (a <= j < b)%nat -> forall r, (r < 14)%nat -> z (S j) r = mv 14 (Psi j) (z j) r + h * src j r.

(** Superposition: the state i steps after a is the propagated state at a
    plus the particular part. *)
Lemma run_split :
  forall z src a b, runs z src a b ->
  forall i, (a + i <= b)%nat -> forall r, (r < 14)%nat ->
  z (a + i)%nat r = mv 14 (mprod 14 Psi a i) (z a) r + part src a i r.
Proof.
  intros z src a b Hrun i. induction i as [|i IH]; intros Hi r Hr.
  - rewrite Nat.add_0_r. cbn [mprod part]. rewrite mv_mI by exact Hr. ring.
  - replace (a + S i)%nat with (S (a + i)) by lia.
    rewrite (Hrun (a + i)%nat ltac:(lia) r Hr). cbn [mprod part].
    rewrite (mv_extn 14 (Psi (a + i)%nat) (z (a + i)%nat)
               (fun r' => mv 14 (mprod 14 Psi a i) (z a) r' + part src a i r') r)
      by (intros k Hk; apply IH; [lia | exact Hk]).
    rewrite mv_add, mv_mm_r. ring.
Qed.

(** The run from a given state. *)
Definition run_from (z0 : vec) (src : nat -> vec) (a : nat) : nat -> vec :=
  fun j => fun r => mv 14 (mprod 14 Psi a (j - a)) z0 r + part src a (j - a) r.

Lemma run_from_runs : forall z0 src a b, runs (run_from z0 src a) src a b.
Proof.
  intros z0 src a b j Hj r Hr. unfold run_from.
  replace (S j - a)%nat with (S (j - a)) by lia. cbn [mprod part].
  replace (a + (j - a))%nat with j by lia.
  rewrite mv_add, mv_mm_r. ring.
Qed.

Lemma run_from_start : forall z0 src a r, (r < 14)%nat -> run_from z0 src a a r = z0 r.
Proof.
  intros z0 src a r Hr. unfold run_from. rewrite Nat.sub_diag. cbn [mprod part].
  rewrite mv_mI by exact Hr. ring.
Qed.

Lemma mv_msum :
  forall n A (g : nat -> vec) m i,
  mv n A (fun c => msum (fun i' => g i' c) m) i = msum (fun i' => mv n A (g i') i) m.
Proof.
  intros n A g m i. unfold mv.
  rewrite (msum_ext _ (fun c => msum (fun i' => A i c * g i' c) m)) by (intros c _; rewrite <- msum_scal; reflexivity).
  apply msum_swap.
Qed.

(** The particular part as the sum of the sources carried to its end. *)
Lemma part_sum :
  forall src a i r, (r < 14)%nat ->
  part src a i r = msum (fun i' => mv 14 (mprod 14 Psi (S (a + i')) (i - S i')) (fun c => h * src (a + i')%nat c) r) i.
Proof.
  intros src a i. induction i as [|i IH]; intros r Hr; [reflexivity|].
  cbn [part msum].
  rewrite (mv_extn 14 (Psi (a + i)%nat) (part src a i)
             (fun c => msum (fun i' => mv 14 (mprod 14 Psi (S (a + i')) (i - S i')) (fun c0 => h * src (a + i')%nat c0) c) i) r)
    by (intros k Hk; apply IH; exact Hk).
  rewrite mv_msum.
  replace (S i - S i)%nat with O by lia. cbn [mprod]. rewrite mv_mI by exact Hr.
  f_equal. apply msum_ext. intros i' Hi'.
  rewrite mv_mm_r. replace (S i - S i')%nat with (S (i - S i')) by lia. cbn [mprod].
  replace (S (a + i') + (i - S i'))%nat with (a + i)%nat by lia. reflexivity.
Qed.

(** The particular part is bounded by the sources through the propagators
    after each of them. *)
Lemma part_bound :
  forall src a i G,
  (forall i', (i' < i)%nat -> mnorm 14 14 (mprod 14 Psi (S (a + i')) (i - S i')) <= G) ->
  vnorm 14 (part src a i) <= G * msum (fun i' => Rabs h * vnorm 14 (src (a + i')%nat)) i.
Proof.
  intros src a i G Hb. destruct i as [|i].
  - cbn [part msum]. unfold vnorm. rewrite Rmult_0_r. apply fmax_le; [lra|]. intros; rewrite Rabs_R0; lra.
  - assert (HG : 0 <= G) by (eapply Rle_trans; [apply mnorm_nonneg | apply (Hb O); lia]).
    apply vnorm_le; [apply Rmult_le_pos; [exact HG | apply msum_nonneg; intros; apply Rmult_le_pos; [apply Rabs_pos | apply vnorm_nonneg]]|].
    intros r Hr. rewrite part_sum by exact Hr. eapply Rle_trans; [apply msum_abs|].
    rewrite <- msum_scal. apply msum_le. intros i' Hi'.
    eapply Rle_trans; [apply (vnorm_ge 14 (mv 14 _ _) r Hr)|].
    eapply Rle_trans; [apply vnorm_mv|].
    rewrite vnorm_scal.
    replace (G * (Rabs h * vnorm 14 (src (a + i')%nat))) with ((Rabs h * vnorm 14 (src (a + i')%nat)) * G) by ring.
    rewrite Rmult_comm. apply Rmult_le_compat_l; [apply Rmult_le_pos; [apply Rabs_pos | apply vnorm_nonneg]|].
    apply Hb. exact Hi'.
Qed.

End Run.

(* ---------------------------------------------------------------- *)
(* The system                                                        *)

(** The padded start rows, the rows that zero p's unused entries, and the
    end selector E0 p = (0, p). *)
Definition padrows (Cs : mat) : mat := fun r c => if Nat.ltb r 5 then Cs r c else 0.
Definition D9 : mat := fun r c => if Nat.leb 5 r && Nat.eqb r c then 1 else 0.
Definition E0p : mat := fun r c => if Nat.leb 9 r && Nat.eqb (r - 9) c && Nat.ltb c 5 then 1 else 0.

Lemma mv_padrows : forall Cs x i, mv 14 (padrows Cs) x i = if Nat.ltb i 5 then mv 14 Cs x i else 0.
Proof.
  intros Cs x i. unfold mv, padrows. destruct (Nat.ltb i 5); [reflexivity|].
  rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
Qed.

Lemma mv_D9 : forall x i, (i < 14)%nat -> mv 14 D9 x i = if Nat.leb 5 i then x i else 0.
Proof.
  intros x i Hi. unfold mv, D9. destruct (Nat.leb_spec 5 i) as [H5|H5]; cbn [andb].
  - rewrite (msum_single _ 14 i Hi).
    + rewrite Nat.eqb_refl. ring.
    + intros j Hj Hji. destruct (Nat.eqb_spec i j) as [->|]; [contradiction | ring].
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
Qed.

Lemma mv_E0p : forall x i, (i < 14)%nat -> mv 14 E0p x i = if Nat.leb 9 i then x (i - 9)%nat else 0.
Proof.
  intros x i Hi. unfold mv, E0p. destruct (Nat.leb_spec 9 i) as [H9|H9]; cbn [andb].
  - rewrite (msum_single _ 14 (i - 9) ltac:(lia)).
    + rewrite Nat.eqb_refl. replace (Nat.ltb (i - 9) 5) with true by (symmetry; apply Nat.ltb_lt; lia).
      cbn [andb]. ring.
    + intros j Hj Hji. replace (Nat.eqb (i - 9) j) with false by (symmetry; apply Nat.eqb_neq; lia).
      cbn [andb]. ring.
  - rewrite (msum_ext _ (fun _ => 0)) by (intros; ring). apply msum_zero.
Qed.

Section MS.

Variable h : R.
Variable Psi : nat -> mat.
Variable nseg : nat.
Hypothesis Hnseg : (1 <= nseg)%nat.
Variable cut : nat -> nat.
Hypothesis Hcut : forall k, (k < nseg)%nat -> (cut k <= cut (S k))%nat.
Variables W Wi : nat -> mat.
Hypothesis HWW : forall k, (k < nseg)%nat -> forall r c, (r < 14)%nat -> (c < 14)%nat ->
  mm 14 (Wi k) (W k) r c = mI r c.
Hypothesis HWW' : forall k, (k < nseg)%nat -> forall r c, (r < 14)%nat -> (c < 14)%nat ->
  mm 14 (W k) (Wi k) r c = mI r c.
Variable Cs : mat.
Variables We Wei : mat.
Hypothesis HWe : forall r c, (r < 14)%nat -> (c < 14)%nat -> mm 14 Wei We r c = mI r c.

Definition lenk (k : nat) : nat := (cut (S k) - cut k)%nat.
Definition Yk (k : nat) : mat := mprod 14 Psi (cut k) (lenk k).
Definition pik (src : nat -> vec) (k : nat) : vec := part h Psi src (cut k) (lenk k).

Definition jun (k : nat) : mat := mm 14 (W (S k)) (mm 14 (Yk k) (Wi k)).
Definition endb : mat := mm 14 We (mm 14 (Yk (nseg - 1)) (Wi (nseg - 1))).

Definition mblock (I J : nat) : mat :=
  if Nat.eqb I 0 then
    (if Nat.eqb J 0 then mm 14 (padrows Cs) (Wi 0) else if Nat.eqb J nseg then D9 else fun _ _ => 0)
  else if Nat.eqb I nseg then
    (if Nat.eqb J (nseg - 1) then endb else if Nat.eqb J nseg then (fun r c => - mm 14 We E0p r c)
     else fun _ _ => 0)
  else
    (if Nat.eqb J (I - 1) then (fun r c => - jun (I - 1) r c) else if Nat.eqb J I then mI else fun _ _ => 0).

Definition msys : mat := flat mblock.
Definition msdim : nat := (14 * S nseg)%nat.

Definition rhs (src : nat -> vec) : vec :=
  unblk (fun I => if Nat.eqb I 0 then (fun _ => 0)
                  else if Nat.eqb I nseg then (fun r => - mv 14 We (pik src (nseg - 1)) r)
                  else mv 14 (W I) (pik src (I - 1))).

(** The unknowns a run gives: its states at the cuts in segment coordinates,
    and the free part of its last state. *)
Definition ufrom (z : nat -> vec) : vec :=
  unblk (fun I => if Nat.ltb I nseg then mv 14 (W I) (z (cut I))
                  else fun r => if Nat.ltb r 5 then zp (z (cut nseg)) r else 0).

Lemma cut_mono : forall k l, (k <= l <= nseg)%nat -> (cut k <= cut l)%nat.
Proof.
  intros k l [Hkl Hl]. induction Hkl as [|l Hkl IH]; [lia|].
  specialize (IH ltac:(lia)). specialize (Hcut l ltac:(lia)). lia.
Qed.

(** The state at a cut is the propagated state at the cut before plus that
    segment's particular part. *)
Lemma run_cut :
  forall z src, runs h Psi z src (cut 0) (cut nseg) ->
  forall k, (k < nseg)%nat -> forall r, (r < 14)%nat ->
  z (cut (S k)) r = mv 14 (Yk k) (z (cut k)) r + pik src k r.
Proof.
  intros z src Hrun k Hk r Hr. unfold Yk, pik, lenk.
  assert (Hm := cut_mono k (S k) ltac:(lia)).
  assert (H0 := cut_mono 0 k ltac:(lia)). assert (HN := cut_mono (S k) nseg ltac:(lia)).
  replace (cut (S k)) with (cut k + (cut (S k) - cut k))%nat at 1 by lia.
  apply (run_split h Psi z src (cut k) (cut nseg)); [| lia | exact Hr].
  intros j Hj. apply Hrun. lia.
Qed.

Lemma blk_ufrom_lt :
  forall z J j, (J < nseg)%nat -> (j < 14)%nat -> blk (ufrom z) J j = mv 14 (W J) (z (cut J)) j.
Proof.
  intros z J j HJ Hj. unfold ufrom. rewrite blk_unblk by exact Hj.
  rewrite (proj2 (Nat.ltb_lt J nseg) HJ). reflexivity.
Qed.

Lemma blk_ufrom_end :
  forall z j, (j < 14)%nat -> blk (ufrom z) nseg j = if Nat.ltb j 5 then zp (z (cut nseg)) j else 0.
Proof.
  intros z j Hj. unfold ufrom. rewrite blk_unblk by exact Hj. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

Lemma blk_rhs :
  forall src I i, (i < 14)%nat ->
  blk (rhs src) I i = (if Nat.eqb I 0 then 0
                      else if Nat.eqb I nseg then - mv 14 We (pik src (nseg - 1)) i
                      else mv 14 (W I) (pik src (I - 1)) i).
Proof.
  intros src I i Hi. unfold rhs. rewrite blk_unblk by exact Hi.
  destruct (Nat.eqb I 0); [reflexivity|]. destruct (Nat.eqb I nseg); reflexivity.
Qed.

(** W then Wi is the identity on a vector. *)
Lemma WiW : forall k x r, (k < nseg)%nat -> (r < 14)%nat ->
  mv 14 (Wi k) (mv 14 (W k) x) r = x r.
Proof. intros k x r Hk Hr. apply mv_inv_cancel; [intros; apply HWW; assumption | exact Hr]. Qed.

Lemma WWi : forall k x r, (k < nseg)%nat -> (r < 14)%nat ->
  mv 14 (W k) (mv 14 (Wi k) x) r = x r.
Proof. intros k x r Hk Hr. apply mv_inv_cancel; [intros; apply HWW'; assumption | exact Hr]. Qed.

(** A product applied after Wi then W. *)
Lemma mv_mm_WiW :
  forall A k x r, (k < nseg)%nat -> mv 14 (mm 14 A (Wi k)) (mv 14 (W k) x) r = mv 14 A x r.
Proof.
  intros A k x r Hk. rewrite <- mv_mm_r. apply mv_extn. intros c Hc. apply WiW; assumption.
Qed.

(** The row blocks of the system, applied. *)
Lemma msys_row :
  forall u I i, (I <= nseg)%nat -> (i < 14)%nat ->
  mv msdim msys u (14 * I + i)%nat = msum (fun J => mv 14 (mblock I J) (blk u J) i) (S nseg).
Proof. intros u I i HI Hi. unfold msdim, msys. apply flat_mv. exact Hi. Qed.

Lemma mv_zero_block : forall x i, mv 14 (fun _ _ => 0) x i = 0.
Proof. intros. apply mv_zero_mat. Qed.

(** A run with both boundary conditions solves the system. *)
Theorem run_solves :
  forall z src,
  runs h Psi z src (cut 0) (cut nseg) ->
  (forall r, (r < 5)%nat -> mv 14 Cs (z (cut 0)) r = 0) ->
  (forall r, (r < 9)%nat -> z (cut nseg) r = 0) ->
  forall I i, (I <= nseg)%nat -> (i < 14)%nat ->
  mv msdim msys (ufrom z) (14 * I + i)%nat = blk (rhs src) I i.
Proof.
  intros z src Hrun Hs He I i HI Hi.
  rewrite msys_row by assumption. rewrite blk_rhs by exact Hi.
  destruct (Nat.eqb_spec I 0) as [->|HI0].
  - (* the start rows *)
    rewrite (msum_two _ (S nseg) 0 nseg ltac:(lia) ltac:(lia) ltac:(lia)).
    2: { intros J HJ HJ0 HJn. unfold mblock. cbn [Nat.eqb].
         rewrite (proj2 (Nat.eqb_neq J 0) HJ0), (proj2 (Nat.eqb_neq J nseg) HJn). apply mv_zero_block. }
    unfold mblock. cbn [Nat.eqb].
    replace (Nat.eqb nseg 0) with false by (symmetry; apply Nat.eqb_neq; lia). rewrite Nat.eqb_refl.
    rewrite (mv_extn 14 (mm 14 (padrows Cs) (Wi 0)) (blk (ufrom z) 0) (mv 14 (W 0) (z (cut 0))) i)
      by (intros c Hc; apply blk_ufrom_lt; [lia | exact Hc]).
    rewrite mv_mm_WiW by lia. rewrite mv_padrows, mv_D9 by exact Hi.
    destruct (Nat.ltb_spec i 5) as [H5|H5].
    + rewrite Hs by exact H5. replace (Nat.leb 5 i) with false by (symmetry; apply Nat.leb_gt; lia). ring.
    + replace (Nat.leb 5 i) with true by (symmetry; apply Nat.leb_le; lia).
      rewrite blk_ufrom_end by exact Hi. replace (Nat.ltb i 5) with false by (symmetry; apply Nat.ltb_ge; lia). ring.
  - destruct (Nat.eqb_spec I nseg) as [->|HIn].
    + (* the end rows *)
      rewrite (msum_two _ (S nseg) (nseg - 1) nseg ltac:(lia) ltac:(lia) ltac:(lia)).
      2: { intros J HJ HJ1 HJn. unfold mblock.
           replace (Nat.eqb nseg 0) with false by (symmetry; apply Nat.eqb_neq; lia). rewrite Nat.eqb_refl.
           rewrite (proj2 (Nat.eqb_neq J (nseg - 1)) HJ1), (proj2 (Nat.eqb_neq J nseg) HJn). apply mv_zero_block. }
      unfold mblock.
      replace (Nat.eqb nseg 0) with false by (symmetry; apply Nat.eqb_neq; lia). rewrite !Nat.eqb_refl.
      replace (Nat.eqb nseg (nseg - 1)) with false by (symmetry; apply Nat.eqb_neq; lia).
      rewrite (mv_extn 14 endb (blk (ufrom z) (nseg - 1)) (mv 14 (W (nseg - 1)) (z (cut (nseg - 1)))) i)
        by (intros c Hc; apply blk_ufrom_lt; [lia | exact Hc]).
      assert (A1 : mv 14 endb (mv 14 (W (nseg - 1)) (z (cut (nseg - 1)))) i
                   = mv 14 We (mv 14 (Yk (nseg - 1)) (z (cut (nseg - 1)))) i).
      { unfold endb. rewrite <- mv_mm_r. apply mv_extn. intros c Hc. apply mv_mm_WiW. lia. }
      rewrite A1. rewrite mv_neg_mat, <- mv_mm_r.
      (* E0 applied to p is the last state *)
      assert (HE : forall c, (c < 14)%nat -> mv 14 E0p (blk (ufrom z) nseg) c = z (cut nseg) c).
      { intros c Hc. rewrite mv_E0p by exact Hc. destruct (Nat.leb_spec 9 c) as [H9|H9].
        - rewrite blk_ufrom_end by lia. replace (Nat.ltb (c - 9) 5) with true by (symmetry; apply Nat.ltb_lt; lia).
          unfold zp. f_equal. lia.
        - rewrite He by exact H9. reflexivity. }
      rewrite (mv_extn 14 We (mv 14 E0p (blk (ufrom z) nseg)) (z (cut nseg)) i) by exact HE.
      assert (Hz : forall c, (c < 14)%nat ->
                z (cut nseg) c = mv 14 (Yk (nseg - 1)) (z (cut (nseg - 1))) c + pik src (nseg - 1) c).
      { intros c Hc. replace nseg with (S (nseg - 1)) at 1 by lia. apply run_cut; [exact Hrun | lia | exact Hc]. }
      rewrite (mv_extn 14 We (z (cut nseg))
                 (fun c => mv 14 (Yk (nseg - 1)) (z (cut (nseg - 1))) c + pik src (nseg - 1) c) i) by exact Hz.
      rewrite mv_add. ring.
    + (* a junction *)
      rewrite (msum_two _ (S nseg) (I - 1) I ltac:(lia) ltac:(lia) ltac:(lia)).
      2: { intros J HJ HJ1 HJI. unfold mblock.
           rewrite (proj2 (Nat.eqb_neq I 0) HI0), (proj2 (Nat.eqb_neq I nseg) HIn).
           rewrite (proj2 (Nat.eqb_neq J (I - 1)) HJ1), (proj2 (Nat.eqb_neq J I) HJI). apply mv_zero_block. }
      unfold mblock.
      rewrite (proj2 (Nat.eqb_neq I 0) HI0), (proj2 (Nat.eqb_neq I nseg) HIn), !Nat.eqb_refl.
      replace (Nat.eqb I (I - 1)) with false by (symmetry; apply Nat.eqb_neq; lia).
      rewrite mv_mI by exact Hi. rewrite blk_ufrom_lt by (lia || exact Hi).
      rewrite mv_neg_mat.
      rewrite (mv_extn 14 (jun (I - 1)) (blk (ufrom z) (I - 1)) (mv 14 (W (I - 1)) (z (cut (I - 1)))) i)
        by (intros c Hc; apply blk_ufrom_lt; [lia | exact Hc]).
      assert (A2 : mv 14 (jun (I - 1)) (mv 14 (W (I - 1)) (z (cut (I - 1)))) i
                   = mv 14 (W I) (mv 14 (Yk (I - 1)) (z (cut (I - 1)))) i).
      { unfold jun. replace (S (I - 1)) with I by lia. rewrite <- mv_mm_r. apply mv_extn.
        intros c Hc. apply mv_mm_WiW. lia. }
      rewrite A2.
      assert (Hz : forall c, (c < 14)%nat ->
                z (cut I) c = mv 14 (Yk (I - 1)) (z (cut (I - 1))) c + pik src (I - 1) c).
      { intros c Hc. replace I with (S (I - 1)) at 1 by lia. apply run_cut; [exact Hrun | lia | exact Hc]. }
      rewrite (mv_extn 14 (W I) (z (cut I))
                 (fun c => mv 14 (Yk (I - 1)) (z (cut (I - 1))) c + pik src (I - 1) c) i) by exact Hz.
      rewrite mv_add. ring.
Qed.

(** The row equations of a solution, block by block. *)
Section Back.

Variables (u : vec) (src : nat -> vec).
Hypothesis Hsol : forall I i, (I <= nseg)%nat -> (i < 14)%nat ->
  mv msdim msys u (14 * I + i)%nat = blk (rhs src) I i.

Definition zrun : nat -> vec := run_from h Psi (mv 14 (Wi 0) (blk u 0)) src (cut 0).

Lemma zrun_runs : runs h Psi zrun src (cut 0) (cut nseg).
Proof. apply run_from_runs. Qed.

Lemma row_start :
  forall i, (i < 14)%nat ->
  mv 14 (mm 14 (padrows Cs) (Wi 0)) (blk u 0) i + mv 14 D9 (blk u nseg) i = 0.
Proof.
  intros i Hi. specialize (Hsol 0 i ltac:(lia) Hi). rewrite msys_row in Hsol by lia.
  rewrite blk_rhs in Hsol by exact Hi. rewrite Nat.eqb_refl in Hsol.
  rewrite (msum_two _ (S nseg) 0 nseg ltac:(lia) ltac:(lia) ltac:(lia)) in Hsol.
  - unfold mblock in Hsol. cbn [Nat.eqb] in Hsol.
    replace (Nat.eqb nseg 0) with false in Hsol by (symmetry; apply Nat.eqb_neq; lia).
    rewrite Nat.eqb_refl in Hsol. exact Hsol.
  - intros J HJ HJ0 HJn. unfold mblock. cbn [Nat.eqb].
    rewrite (proj2 (Nat.eqb_neq J 0) HJ0), (proj2 (Nat.eqb_neq J nseg) HJn). apply mv_zero_block.
Qed.

Lemma row_junction :
  forall I i, (1 <= I < nseg)%nat -> (i < 14)%nat ->
  - mv 14 (jun (I - 1)) (blk u (I - 1)) i + blk u I i = mv 14 (W I) (pik src (I - 1)) i.
Proof.
  intros I i HI Hi. specialize (Hsol I i ltac:(lia) Hi). rewrite msys_row in Hsol by lia.
  rewrite blk_rhs in Hsol by exact Hi.
  rewrite (proj2 (Nat.eqb_neq I 0) ltac:(lia)), (proj2 (Nat.eqb_neq I nseg) ltac:(lia)) in Hsol.
  rewrite (msum_two _ (S nseg) (I - 1) I ltac:(lia) ltac:(lia) ltac:(lia)) in Hsol.
  - unfold mblock in Hsol.
    rewrite (proj2 (Nat.eqb_neq I 0) ltac:(lia)), (proj2 (Nat.eqb_neq I nseg) ltac:(lia)), !Nat.eqb_refl in Hsol.
    replace (Nat.eqb I (I - 1)) with false in Hsol by (symmetry; apply Nat.eqb_neq; lia).
    rewrite mv_neg_mat, mv_mI in Hsol by exact Hi. exact Hsol.
  - intros J HJ HJ1 HJI. unfold mblock.
    rewrite (proj2 (Nat.eqb_neq I 0) ltac:(lia)), (proj2 (Nat.eqb_neq I nseg) ltac:(lia)).
    rewrite (proj2 (Nat.eqb_neq J (I - 1)) HJ1), (proj2 (Nat.eqb_neq J I) HJI). apply mv_zero_block.
Qed.

Lemma row_end :
  forall i, (i < 14)%nat ->
  mv 14 endb (blk u (nseg - 1)) i - mv 14 (mm 14 We E0p) (blk u nseg) i = - mv 14 We (pik src (nseg - 1)) i.
Proof.
  intros i Hi. specialize (Hsol nseg i ltac:(lia) Hi). rewrite msys_row in Hsol by lia.
  rewrite blk_rhs in Hsol by exact Hi.
  replace (Nat.eqb nseg 0) with false in Hsol by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Nat.eqb_refl in Hsol.
  rewrite (msum_two _ (S nseg) (nseg - 1) nseg ltac:(lia) ltac:(lia) ltac:(lia)) in Hsol.
  - unfold mblock in Hsol.
    replace (Nat.eqb nseg 0) with false in Hsol by (symmetry; apply Nat.eqb_neq; lia).
    rewrite !Nat.eqb_refl in Hsol.
    replace (Nat.eqb nseg (nseg - 1)) with false in Hsol by (symmetry; apply Nat.eqb_neq; lia).
    rewrite mv_neg_mat in Hsol. lra.
  - intros J HJ HJ1 HJn. unfold mblock.
    replace (Nat.eqb nseg 0) with false by (symmetry; apply Nat.eqb_neq; lia). rewrite Nat.eqb_refl.
    rewrite (proj2 (Nat.eqb_neq J (nseg - 1)) HJ1), (proj2 (Nat.eqb_neq J nseg) HJn). apply mv_zero_block.
Qed.

(** The run passes through Wi_k of the solution's block k at every cut. *)
Lemma zrun_cuts :
  forall k, (k < nseg)%nat -> forall r, (r < 14)%nat -> zrun (cut k) r = mv 14 (Wi k) (blk u k) r.
Proof.
  intros k. induction k as [|k IH]; intros Hk r Hr.
  - unfold zrun. apply run_from_start. exact Hr.
  - rewrite (run_cut zrun src zrun_runs k ltac:(lia) r Hr).
    (* the junction row gives block k + 1 *)
    assert (Hb : forall c, (c < 14)%nat ->
              blk u (S k) c = mv 14 (W (S k)) (fun c' => mv 14 (Yk k) (zrun (cut k)) c' + pik src k c') c).
    { intros c Hc. assert (J := row_junction (S k) c ltac:(lia) Hc). replace (S k - 1)%nat with k in J by lia.
      rewrite mv_add.
      rewrite (mv_extn 14 (W (S k)) (mv 14 (Yk k) (zrun (cut k))) (mv 14 (Yk k) (mv 14 (Wi k) (blk u k))) c)
        by (intros c' Hc'; apply mv_extn; intros c'' Hc''; apply IH; lia).
      unfold jun in J. rewrite <- mv_mm_r in J.
      assert (E : mv 14 (W (S k)) (mv 14 (mm 14 (Yk k) (Wi k)) (blk u k)) c
                  = mv 14 (W (S k)) (mv 14 (Yk k) (mv 14 (Wi k) (blk u k))) c)
        by (apply mv_extn; intros; symmetry; apply mv_mm_r).
      lra. }
    rewrite (mv_extn 14 (Wi (S k)) (blk u (S k)) _ r Hb). rewrite WiW by assumption. reflexivity.
Qed.

Theorem solves_start : forall r, (r < 5)%nat -> mv 14 Cs (zrun (cut 0)) r = 0.
Proof.
  intros r Hr. assert (H := row_start r ltac:(lia)).
  rewrite mv_D9 in H by lia. replace (Nat.leb 5 r) with false in H by (symmetry; apply Nat.leb_gt; lia).
  rewrite <- mv_mm_r, mv_padrows in H. rewrite (proj2 (Nat.ltb_lt r 5) Hr) in H.
  rewrite (mv_extn 14 Cs (zrun (cut 0)) (mv 14 (Wi 0) (blk u 0)) r)
    by (intros c Hc; apply zrun_cuts; lia).
  lra.
Qed.

Theorem solves_end : forall r, (r < 9)%nat -> zrun (cut nseg) r = 0.
Proof.
  intros r Hr.
  (* We applied to (Y z_last + pi_last - E0 p) vanishes, and We is injective *)
  assert (H : forall i, (i < 14)%nat ->
            mv 14 We (fun c => zrun (cut nseg) c - mv 14 E0p (blk u nseg) c) i = 0).
  { intros i Hi. assert (E := row_end i Hi). rewrite mv_sub.
    rewrite (mv_extn 14 We (zrun (cut nseg))
               (fun c => mv 14 (Yk (nseg - 1)) (zrun (cut (nseg - 1))) c + pik src (nseg - 1) c) i).
    2: { intros c Hc. replace nseg with (S (nseg - 1)) at 1 by lia.
         apply (run_cut zrun src zrun_runs (nseg - 1) ltac:(lia) c Hc). }
    rewrite mv_add.
    assert (E2 : mv 14 We (mv 14 (Yk (nseg - 1)) (zrun (cut (nseg - 1)))) i
                 = mv 14 endb (blk u (nseg - 1)) i).
    { unfold endb. rewrite <- mv_mm_r. apply mv_extn. intros c Hc. rewrite <- mv_mm_r.
      apply mv_extn. intros c' Hc'. apply zrun_cuts; lia. }
    assert (E3 : mv 14 (mm 14 We E0p) (blk u nseg) i = mv 14 We (mv 14 E0p (blk u nseg)) i)
      by (symmetry; apply mv_mm_r).
    lra. }
  assert (Hz : forall c, (c < 14)%nat -> zrun (cut nseg) c - mv 14 E0p (blk u nseg) c = 0).
  { intros c Hc. rewrite <- (mv_inv_cancel 14 We Wei (fun c' => zrun (cut nseg) c' - mv 14 E0p (blk u nseg) c') c)
      by first [exact Hc | intros; apply HWe; assumption].
    rewrite (mv_extn 14 Wei _ (fun _ => 0)) by (intros; apply H; assumption). apply mv_zero_vec. }
  specialize (Hz r ltac:(lia)). rewrite mv_E0p in Hz by lia.
  replace (Nat.leb 9 r) with false in Hz by (symmetry; apply Nat.leb_gt; lia). lra.
Qed.

End Back.

(** Every row of the flat system is in a block row. *)
Lemma row_split : forall r, (r < msdim)%nat -> r = (14 * (r / 14) + r mod 14)%nat /\ (r / 14 <= nseg)%nat /\ (r mod 14 < 14)%nat.
Proof.
  intros r Hr. unfold msdim in Hr. split; [apply Nat.div_mod; lia|]. split.
  - apply Nat.lt_succ_r. apply Nat.Div0.div_lt_upper_bound. lia.
  - apply Nat.mod_upper_bound. lia.
Qed.

(** The total weight of the sources over the run. *)
Definition swt (src : nat -> vec) : R :=
  msum (fun j => Rabs h * vnorm 14 (src (cut 0 + j)%nat)) (cut nseg - cut 0).

Lemma swt_seg :
  forall src k, (k < nseg)%nat ->
  msum (fun i' => Rabs h * vnorm 14 (src (cut k + i')%nat)) (lenk k) <= swt src.
Proof.
  intros src k Hk. unfold swt, lenk.
  assert (H0 := cut_mono 0 k ltac:(lia)). assert (H1 := cut_mono k (S k) ltac:(lia)).
  assert (H2 := cut_mono (S k) nseg ltac:(lia)).
  set (f := fun j => Rabs h * vnorm 14 (src (cut 0 + j)%nat)).
  assert (Hf : forall j, 0 <= f j) by (intros; unfold f; apply Rmult_le_pos; [apply Rabs_pos | apply vnorm_nonneg]).
  replace (cut nseg - cut 0)%nat with ((cut k - cut 0) + ((cut (S k) - cut k) + (cut nseg - cut (S k))))%nat by lia.
  rewrite msum_add, msum_add.
  assert (A : msum (fun i' => Rabs h * vnorm 14 (src (cut k + i')%nat)) (cut (S k) - cut k)
              = msum (fun c => f (cut k - cut 0 + c)%nat) (cut (S k) - cut k)).
  { apply msum_ext. intros c Hc. unfold f. do 3 f_equal. lia. }
  rewrite A.
  assert (B1 : 0 <= msum f (cut k - cut 0)) by (apply msum_nonneg; intros; apply Hf).
  assert (B2 : 0 <= msum (fun c => f (cut k - cut 0 + (cut (S k) - cut k + c))%nat) (cut nseg - cut (S k)))
    by (apply msum_nonneg; intros; apply Hf).
  lra.
Qed.

Lemma vnorm_blk : forall u J, (J <= nseg)%nat -> vnorm 14 (blk u J) <= vnorm msdim u.
Proof.
  intros u J HJ. apply vnorm_le; [apply vnorm_nonneg|]. intros j Hj. unfold blk.
  apply vnorm_ge. unfold msdim. lia.
Qed.

Section Bound.

Variable X : mat.
Variables q G Wm Wim : R.
Hypothesis HXl : forall r c, (r < msdim)%nat -> (c < msdim)%nat -> mm msdim X msys r c = mI r c.
Hypothesis Hq : mnorm msdim msdim X <= q.
Hypothesis HG : forall k, (k < nseg)%nat -> forall i i', (i <= i' <= lenk k)%nat ->
  mnorm 14 14 (mprod 14 Psi (cut k + i) (i' - i)) <= G.
Hypothesis HWm : forall k, (k < nseg)%nat -> mnorm 14 14 (W k) <= Wm.
Hypothesis HWem : mnorm 14 14 We <= Wm.
Hypothesis HWim : forall k, (k < nseg)%nat -> mnorm 14 14 (Wi k) <= Wim.

Lemma pik_bound : forall src k, (k < nseg)%nat -> vnorm 14 (pik src k) <= G * swt src.
Proof.
  intros src k Hk. unfold pik. eapply Rle_trans.
  - apply part_bound. intros i' Hi'. replace (S (cut k + i')) with (cut k + S i')%nat by lia.
    apply (HG k Hk (S i') (lenk k)). lia.
  - apply Rmult_le_compat_l; [| apply swt_seg; exact Hk].
    eapply Rle_trans; [apply mnorm_nonneg | apply (HG k Hk 0 0); lia].
Qed.

Lemma rhs_bound : forall src, vnorm msdim (rhs src) <= Wm * (G * swt src).
Proof.
  intros src.
  assert (HG0 : 0 <= G) by (eapply Rle_trans; [apply mnorm_nonneg | apply (HG 0 ltac:(lia) 0 0); lia]).
  assert (HW0 : 0 <= Wm) by (eapply Rle_trans; [apply mnorm_nonneg | exact HWem]).
  assert (Hs0 : 0 <= swt src) by (apply msum_nonneg; intros; apply Rmult_le_pos; [apply Rabs_pos | apply vnorm_nonneg]).
  apply vnorm_le; [apply Rmult_le_pos; [exact HW0 | apply Rmult_le_pos; assumption]|].
  intros r Hr. destruct (row_split r Hr) as [Er [HI Hi]].
  rewrite Er. fold (blk (rhs src) (r / 14) (r mod 14)). rewrite blk_rhs by exact Hi.
  destruct (Nat.eqb (r / 14) 0).
  - rewrite Rabs_R0. apply Rmult_le_pos; [exact HW0 | apply Rmult_le_pos; assumption].
  - destruct (Nat.eqb_spec (r / 14) nseg) as [Hn|Hn].
    + rewrite Rabs_Ropp. eapply Rle_trans; [apply (vnorm_ge 14 (mv 14 We (pik src (nseg - 1))) _ Hi)|].
      eapply Rle_trans; [apply vnorm_mv|].
      apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact HWem | apply pik_bound; lia].
    + eapply Rle_trans; [apply (vnorm_ge 14 (mv 14 (W (r / 14)) (pik src (r / 14 - 1))) _ Hi)|].
      eapply Rle_trans; [apply vnorm_mv|].
      apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | apply HWm; lia | apply pik_bound; lia].
Qed.

(** Every run with both boundary conditions is bounded by its sources. *)
Theorem run_bound :
  forall z src,
  runs h Psi z src (cut 0) (cut nseg) ->
  (forall r, (r < 5)%nat -> mv 14 Cs (z (cut 0)) r = 0) ->
  (forall r, (r < 9)%nat -> z (cut nseg) r = 0) ->
  forall k i, (k < nseg)%nat -> (i <= lenk k)%nat ->
  vnorm 14 (z (cut k + i)%nat) <= G * (Wim * (q * (Wm * (G * swt src)))) + G * swt src.
Proof.
  intros z src Hrun Hs He k i Hk Hi.
  set (u := ufrom z).
  assert (Hsys : forall c, (c < msdim)%nat -> mv msdim msys u c = rhs src c).
  { intros c Hc. destruct (row_split c Hc) as [Ec [HI Hi']]. unfold u. rewrite Ec at 1.
    rewrite (run_solves z src Hrun Hs He (c / 14) (c mod 14) HI Hi').
    unfold blk. rewrite <- Ec. reflexivity. }
  assert (Hu : forall r, (r < msdim)%nat -> u r = mv msdim X (rhs src) r).
  { intros r Hr. rewrite <- (mv_inv_cancel msdim msys X u r HXl Hr).
    apply mv_extn. intros c Hc. apply Hsys. exact Hc. }
  assert (Hun : vnorm msdim u <= q * (Wm * (G * swt src))).
  { rewrite (vnorm_ext msdim u (mv msdim X (rhs src))) by exact Hu.
    eapply Rle_trans; [apply vnorm_mv|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | exact Hq | apply rhs_bound]. }
  (* the state at the cut *)
  assert (Hzc : vnorm 14 (z (cut k)) <= Wim * (q * (Wm * (G * swt src)))).
  { rewrite (vnorm_ext 14 (z (cut k)) (mv 14 (Wi k) (blk u k))).
    - eapply Rle_trans; [apply vnorm_mv|].
      apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | apply HWim; exact Hk|].
      eapply Rle_trans; [apply vnorm_blk; lia | exact Hun].
    - intros c Hc. unfold u. rewrite (mv_extn 14 (Wi k) (blk (ufrom z) k) (mv 14 (W k) (z (cut k))) c)
        by (intros c' Hc'; apply blk_ufrom_lt; assumption).
      symmetry. apply WiW; assumption. }
  (* inside the segment *)
  assert (H0 := cut_mono 0 k ltac:(lia)). assert (HN := cut_mono (S k) nseg ltac:(lia)).
  assert (H1 := cut_mono k (S k) ltac:(lia)).
  assert (Hsplit : forall r, (r < 14)%nat ->
            z (cut k + i)%nat r = mv 14 (mprod 14 Psi (cut k) i) (z (cut k)) r + part h Psi src (cut k) i r).
  { intros r Hr. apply (run_split h Psi z src (cut k) (cut nseg)); [| unfold lenk in Hi; lia | exact Hr].
    intros j Hj. apply Hrun. lia. }
  rewrite (vnorm_ext 14 (z (cut k + i)%nat) (fun r => mv 14 (mprod 14 Psi (cut k) i) (z (cut k)) r + part h Psi src (cut k) i r))
    by exact Hsplit.
  eapply Rle_trans.
  { apply vnorm_le; [apply Rplus_le_le_0_compat; apply vnorm_nonneg|].
    intros r Hr. eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; apply vnorm_ge; exact Hr. }
  apply Rplus_le_compat.
  - eapply Rle_trans; [apply vnorm_mv|].
    apply Rmult_le_compat; [apply mnorm_nonneg | apply vnorm_nonneg | | exact Hzc].
    assert (HG0 := HG k Hk 0 i ltac:(lia)). rewrite Nat.add_0_r, Nat.sub_0_r in HG0. exact HG0.
  - eapply Rle_trans.
    + apply part_bound. intros i' Hi'. replace (S (cut k + i')) with (cut k + S i')%nat by lia.
      apply (HG k Hk (S i') i). lia.
    + apply Rmult_le_compat_l; [eapply Rle_trans; [apply mnorm_nonneg | apply (HG k Hk 0 0); lia]|].
      eapply Rle_trans; [| apply (swt_seg src k Hk)].
      apply (msum_le_prefix (fun i' => Rabs h * vnorm 14 (src (cut k + i')%nat)) i (lenk k)); [|exact Hi].
      intros; apply Rmult_le_pos; [apply Rabs_pos | apply vnorm_nonneg].
Qed.

End Bound.

(** For every source there is a run with both boundary conditions. *)
Theorem run_exists :
  forall X, (forall r c, (r < msdim)%nat -> (c < msdim)%nat -> mm msdim msys X r c = mI r c) ->
  forall src, exists z,
  runs h Psi z src (cut 0) (cut nseg) /\
  (forall r, (r < 5)%nat -> mv 14 Cs (z (cut 0)) r = 0) /\
  (forall r, (r < 9)%nat -> z (cut nseg) r = 0).
Proof.
  intros X HXr src.
  set (u := mv msdim X (rhs src)).
  assert (Hsol : forall I i, (I <= nseg)%nat -> (i < 14)%nat ->
            mv msdim msys u (14 * I + i)%nat = blk (rhs src) I i).
  { intros I i HI Hi. unfold u. rewrite mv_mm_r. unfold blk.
    unfold mv at 1. rewrite (msum_ext _ (fun c => mI (14 * I + i)%nat c * rhs src c))
      by (intros c Hc; rewrite HXr by (unfold msdim in *; lia || exact Hc); reflexivity).
    fold (mv msdim mI (rhs src) (14 * I + i)%nat). apply mv_mI. unfold msdim. lia. }
  exists (zrun u src). split; [apply zrun_runs|]. split.
  - apply solves_start. exact Hsol.
  - apply solves_end. exact Hsol.
Qed.

End MS.

(* ---------------------------------------------------------------- *)
(* Perturbing an approximately inverted matrix                       *)

Section Perturb.

Variable n : nat.

(** If R inverts M0 to within th0 on both sides and the change M - M0 moves
    each product by at most th1, R inverts M to within th0 + th1, and M has an
    inverse. *)
Lemma mnorm_neg : forall A, mnorm n n (fun i j => - A i j) = mnorm n n A.
Proof.
  intros A. unfold mnorm, mrow. apply Rle_antisym; apply fmax_mono; intros i Hi; apply msum_le;
    intros j Hj; rewrite Rabs_Ropp; lra.
Qed.

Theorem perturbed_inverse :
  forall M M0 R th0 th1,
  mnorm n n (msub mI (mm n R M0)) <= th0 -> mnorm n n (msub mI (mm n M0 R)) <= th0 ->
  mnorm n n (mm n R (msub M M0)) <= th1 -> mnorm n n (mm n (msub M M0) R) <= th1 ->
  th0 + th1 < 1 ->
  exists X : mat,
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n X M i j = mI i j) /\
    (forall i j, (i < n)%nat -> (j < n)%nat -> mm n M X i j = mI i j) /\
    mnorm n n X <= mnorm n n R / (1 - (th0 + th1)).
Proof.
  intros M M0 R th0 th1 H1 H2 H3 H4 Hlt.
  apply approx_inverse; [| | exact Hlt].
  - rewrite (mnorm_meq n _ (madd (msub mI (mm n R M0)) (fun i j => - mm n R (msub M M0) i j))).
    + eapply Rle_trans; [apply mnorm_madd|]. rewrite mnorm_neg. lra.
    + intros i j _ _. unfold msub at 1 2, madd. unfold mm at 1 2 3. unfold msub.
      rewrite (msum_ext (fun k => R i k * (M k j - M0 k j)) (fun k => R i k * M k j - R i k * M0 k j))
        by (intros; ring).
      rewrite msum_minus. ring.
  - rewrite (mnorm_meq n _ (madd (msub mI (mm n M0 R)) (fun i j => - mm n (msub M M0) R i j))).
    + eapply Rle_trans; [apply mnorm_madd|]. rewrite mnorm_neg. lra.
    + intros i j _ _. unfold msub at 1 2, madd. unfold mm at 1 2 3. unfold msub.
      rewrite (msum_ext (fun k => (M i k - M0 i k) * R k j) (fun k => M i k * R k j - M0 i k * R k j))
        by (intros; ring).
      rewrite msum_minus. ring.
Qed.

(** A product R D bounded by R's rows against bounds on D's row sums. *)
Lemma mnorm_mm_rowsums :
  forall (Rm D : mat) (rho : nat -> R) b,
  (forall j, (j < n)%nat -> mrow n D j <= rho j) ->
  (forall i, (i < n)%nat -> msum (fun j => Rabs (Rm i j) * rho j) n <= b) -> 0 <= b ->
  mnorm n n (mm n Rm D) <= b.
Proof.
  intros Rm D rho b HD HR Hb. apply fmax_le; [exact Hb|]. intros i Hi. unfold mrow, mm.
  eapply Rle_trans.
  { apply (msum_le _ (fun k => msum (fun j => Rabs (Rm i j) * Rabs (D j k)) n)). intros k Hk.
    eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros j Hj. rewrite Rabs_mult. lra. }
  rewrite msum_swap. eapply Rle_trans; [| apply (HR i Hi)].
  apply msum_le. intros j Hj. rewrite msum_scal. apply Rmult_le_compat_l; [apply Rabs_pos | apply HD; exact Hj].
Qed.

(** A product D R bounded by D's row sums against R's rows where D does not
    vanish. *)
Lemma mnorm_mm_cols :
  forall (D Rm : mat) (sigma : nat -> R) b,
  (forall j c, (j < n)%nat -> (c < n)%nat -> Rabs (D j c) * mrow n Rm c <= Rabs (D j c) * sigma j) ->
  (forall j, (j < n)%nat -> mrow n D j * sigma j <= b) -> 0 <= b ->
  mnorm n n (mm n D Rm) <= b.
Proof.
  intros D Rm sigma b HDR Hb Hb0. apply fmax_le; [exact Hb0|]. intros j Hj. unfold mrow at 1. unfold mm.
  eapply Rle_trans.
  { apply (msum_le _ (fun k => msum (fun c => Rabs (D j c) * Rabs (Rm c k)) n)). intros k Hk.
    eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros c Hc. rewrite Rabs_mult. lra. }
  rewrite msum_swap. eapply Rle_trans; [| apply (Hb j Hj)].
  unfold mrow. rewrite <- msum_scal_r. apply msum_le. intros c Hc.
  rewrite msum_scal. apply HDR; assumption.
Qed.

End Perturb.
