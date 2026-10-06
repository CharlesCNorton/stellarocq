(** Families carried by a box of modes, and their exact transforms.

    [supp K1 K2 u] says that u has no coefficient outside |m| <= K1,
    |n| <= K2. Sums, multiples and derivatives keep the box, a product of
    families carried by two boxes is carried by their sum ([fmul_supp]), and
    a list of modes is carried by any box holding its entries
    ([flist_supp]). On a grid with 2 K1 < N1 and 2 K2 < N2 the transforms of
    a family carried by the box are its symmetrised coefficients exactly
    ([dftc_exact], [dfts_exact]), so the norm of a canonical one is the
    weighted sum of its transforms over the box ([nbound_exact]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierDFT FourierCanon FourierModel
  FourierList.
Local Open Scope R_scope.

Definition supp (K1 K2 : nat) (u : fser) : Prop :=
  forall m n, in_box K1 K2 m n = false -> fc u m n = 0 /\ fs u m n = 0.

Lemma in_box_false (K1 K2 : nat) (m n : Z) :
  in_box K1 K2 m n = false <-> (Z.of_nat K1 < Z.abs m)%Z \/ (Z.of_nat K2 < Z.abs n)%Z.
Proof.
  unfold in_box. split.
  - intros H. apply andb_false_iff in H.
    destruct H as [H | H]; apply Z.leb_gt in H; [left | right]; exact H.
  - intros [H | H]; apply andb_false_iff; [left | right]; apply Z.leb_gt; exact H.
Qed.

Lemma supp_mono (K1 K2 L1 L2 : nat) (u : fser) :
  (K1 <= L1)%nat -> (K2 <= L2)%nat -> supp K1 K2 u -> supp L1 L2 u.
Proof.
  intros H1 H2 H m n Hmn. apply H. apply in_box_false. apply in_box_false in Hmn. lia.
Qed.

Lemma fadd_supp (K1 K2 : nat) (u v : fser) : supp K1 K2 u -> supp K1 K2 v -> supp K1 K2 (fadd u v).
Proof.
  intros Hu Hv m n H. destruct (Hu m n H) as [A B]. destruct (Hv m n H) as [C D].
  simpl. rewrite A, B, C, D. split; ring.
Qed.

Lemma fscal_supp (K1 K2 : nat) (c : R) (u : fser) : supp K1 K2 u -> supp K1 K2 (fscal c u).
Proof. intros Hu m n H. destruct (Hu m n H) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma fsub_supp (K1 K2 : nat) (u v : fser) : supp K1 K2 u -> supp K1 K2 v -> supp K1 K2 (fsub u v).
Proof. intros Hu Hv. apply fadd_supp; [exact Hu | apply fscal_supp, Hv]. Qed.

Lemma dt_supp (K1 K2 : nat) (u : fser) : supp K1 K2 u -> supp K1 K2 (dt u).
Proof. intros Hu m n H. destruct (Hu m n H) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma dp_supp (K1 K2 : nat) (u : fser) : supp K1 K2 u -> supp K1 K2 (dp u).
Proof. intros Hu m n H. destruct (Hu m n H) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma fsingle_supp (K1 K2 : nat) (k1 k2 : Z) (c s : R) :
  (Z.abs k1 <= Z.of_nat K1)%Z -> (Z.abs k2 <= Z.of_nat K2)%Z -> supp K1 K2 (fsingle k1 k2 c s).
Proof.
  intros H1 H2 m n H. apply in_box_false in H. unfold fsingle, at2. simpl.
  destruct (Z.eqb_spec m k1); destruct (Z.eqb_spec n k2); simpl; try (split; reflexivity); lia.
Qed.

Lemma flist_supp (K1 K2 : nat) (l : list fent) :
  List.Forall (fun e => (Z.abs (fe_m e) <= Z.of_nat K1)%Z /\ (Z.abs (fe_n e) <= Z.of_nat K2)%Z) l ->
  supp K1 K2 (flist l).
Proof.
  intros H. induction H as [| e l [He1 He2] _ IH].
  - intros m n _. simpl. split; reflexivity.
  - rewrite flist_cons. apply fadd_supp; [apply fsingle_supp; assumption | exact IH].
Qed.

(** A convolution of functions carried by two ranges is carried by their sum. *)
Lemma conv_p_supp (f g : Z -> Z -> R) (K1 K2 L1 L2 : nat) (m n : Z) :
  (forall k l, in_box K1 K2 k l = false -> f k l = 0) ->
  (forall k l, in_box L1 L2 k l = false -> g k l = 0) ->
  in_box (K1 + L1) (K2 + L2) m n = false -> conv_p f g m n = 0.
Proof.
  intros Hf Hg H. apply in_box_false in H. unfold conv_p.
  rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_const0 |].
  intros k l. destruct (in_box K1 K2 k l) eqn:Ek.
  - rewrite (Hg (m - k)%Z (n - l)%Z); [ring |].
    apply in_box_false. unfold in_box in Ek. apply andb_prop in Ek. destruct Ek as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - rewrite (Hf k l Ek). ring.
Qed.

Lemma conv_m_supp (f g : Z -> Z -> R) (K1 K2 L1 L2 : nat) (m n : Z) :
  (forall k l, in_box K1 K2 k l = false -> f k l = 0) ->
  (forall k l, in_box L1 L2 k l = false -> g k l = 0) ->
  in_box (K1 + L1) (K2 + L2) m n = false -> conv_m f g m n = 0.
Proof.
  intros Hf Hg H. apply in_box_false in H. unfold conv_m.
  rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_const0 |].
  intros k l. destruct (in_box K1 K2 k l) eqn:Ek.
  - rewrite (Hg (k - m)%Z (l - n)%Z); [ring |].
    apply in_box_false. unfold in_box in Ek. apply andb_prop in Ek. destruct Ek as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - rewrite (Hf k l Ek). ring.
Qed.

Theorem fmul_supp (K1 K2 L1 L2 : nat) (u v : fser) :
  supp K1 K2 u -> supp L1 L2 v -> supp (K1 + L1) (K2 + L2) (fmul u v).
Proof.
  intros Hu Hv m n H.
  assert (Fc : forall k l, in_box K1 K2 k l = false -> fc u k l = 0) by (intros k l Hk; apply (Hu k l Hk)).
  assert (Fs : forall k l, in_box K1 K2 k l = false -> fs u k l = 0) by (intros k l Hk; apply (Hu k l Hk)).
  assert (Gc : forall k l, in_box L1 L2 k l = false -> fc v k l = 0) by (intros k l Hk; apply (Hv k l Hk)).
  assert (Gs : forall k l, in_box L1 L2 k l = false -> fs v k l = 0) by (intros k l Hk; apply (Hv k l Hk)).
  unfold fmul. simpl.
  rewrite (conv_p_supp _ _ K1 K2 L1 L2 m n Fc Gc H), (conv_p_supp _ _ K1 K2 L1 L2 m n Fs Gs H),
    (conv_m_supp _ _ K1 K2 L1 L2 m n Fc Gc H), (conv_m_supp _ _ K1 K2 L1 L2 m n Fs Gs H),
    (conv_p_supp _ _ K1 K2 L1 L2 m n Fc Gs H), (conv_p_supp _ _ K1 K2 L1 L2 m n Fs Gc H),
    (conv_m_supp _ _ K1 K2 L1 L2 m n Fc Gs H), (conv_m_supp _ _ K1 K2 L1 L2 m n Fs Gc H).
  split; ring.
Qed.

(** * Exact transforms *)

Section Exact.

Variables (N1 N2 K1 K2 : nat) (u : fser).
Hypothesis HN1 : (2 * K1 < N1)%nat.
Hypothesis HN2 : (2 * K2 < N2)%nat.
Hypothesis Hu : supp K1 K2 u.

Lemma Hpos1 : (0 < N1)%nat. Proof. lia. Qed.
Lemma Hpos2 : (0 < N2)%nat. Proof. lia. Qed.

(** A family carried by the box has a finite norm on every strip. *)
Lemma supp_nbound (rho : R) : nbound rho (bsum K1 K2 (nterm rho u)) u.
Proof.
  intros N. apply sqsum_box.
  - intros m n. apply nterm_nonneg.
  - intros m n H. destruct (Hu m n H) as [A B]. unfold nterm. rewrite A, B, Rabs_R0. ring.
Qed.

Theorem dftc_exact (k l : Z) :
  (Z.abs k <= Z.of_nat K1)%Z -> (Z.abs l <= Z.of_nat K2)%Z -> dftc N1 N2 u k l = ccan u k l.
Proof.
  intros Hk Hl.
  rewrite (dftc_alias N1 N2 u _ k l Hpos1 Hpos2 (supp_nbound 0)), ccan_zz.
  apply zz_sum_ext. intros m n.
  destruct (in_box K1 K2 m n) eqn:E.
  - unfold in_box in E. apply andb_prop in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    destruct (alias_in_box N1 N2 K1 K2 k l m n Hpos1 Hpos2 Hk Hl ltac:(lia) ltac:(lia)) as [A1 A2].
    rewrite A1, A2. reflexivity.
  - destruct (Hu m n E) as [A _]. rewrite A. ring.
Qed.

Theorem dfts_exact (k l : Z) :
  (Z.abs k <= Z.of_nat K1)%Z -> (Z.abs l <= Z.of_nat K2)%Z -> dfts N1 N2 u k l = scan u k l.
Proof.
  intros Hk Hl.
  rewrite (dfts_alias N1 N2 u _ k l Hpos1 Hpos2 (supp_nbound 0)), scan_zz.
  apply zz_sum_ext. intros m n.
  destruct (in_box K1 K2 m n) eqn:E.
  - unfold in_box in E. apply andb_prop in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    destruct (alias_in_box N1 N2 K1 K2 k l m n Hpos1 Hpos2 Hk Hl ltac:(lia) ltac:(lia)) as [A1 A2].
    rewrite A1, A2. reflexivity.
  - destruct (Hu m n E) as [_ A]. rewrite A. ring.
Qed.

Theorem nbound_exact (rho : R) :
  is_canon u ->
  nbound rho (bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k l) + Rabs (dfts N1 N2 u k l)) * wt rho k l)) u.
Proof.
  intros [Cc Cs]. intros N. eapply Rle_trans; [apply (supp_nbound rho N) |].
  apply bsum_le. intros k l E. unfold in_box in E. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  rewrite (dftc_exact k l E1 E2), (dfts_exact k l E1 E2).
  unfold nterm, ccan, scan. rewrite (Cc k l), (Cs k l).
  replace (/ 2 * (fc u k l + fc u k l)) with (fc u k l) by field.
  replace (/ 2 * (fs u k l - - fs u k l)) with (fs u k l) by field. lra.
Qed.

End Exact.
