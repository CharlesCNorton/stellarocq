(** Transforms and norms of the families of one field period.

    A family of period P has no modes off the multiples of P in the second
    index, so its norm is a sum over the modes (k, P l) of a box alone
    ([bsum_per]). On a grid of P M points in the second angle its values
    repeat every M points, and each row transform at a multiple P l of the
    index is P times the row transform at l over one period of M points
    ([rowG_per], [rowH_per]). The norm bound of FourierModel.v then holds with
    the box read at the multiples of P only ([nbound_model_per]), and so does
    the exact norm of a finitely supported family ([nbound_exact_per]). *)

From Coq Require Import ZArith Reals Lra Lia Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierDFT FourierCanon FourierModel FourierPer FourierSupp KCheckDFT.
Local Open Scope R_scope.

(** * Sums in blocks *)

Lemma fsum_add_len (h : nat -> R) (n d : nat) :
  fsum h (n + d) = fsum h n + fsum (fun i => h (n + i)%nat) d.
Proof.
  induction d as [| d IH].
  - rewrite Nat.add_0_r. cbn [fsum]. ring.
  - rewrite Nat.add_succ_r. cbn [fsum]. rewrite IH. ring.
Qed.

Lemma fsum_blocks (h : nat -> R) (M P : nat) :
  fsum h (P * M) = fsum (fun c => fsum (fun b => h (c * M + b)%nat) M) P.
Proof.
  induction P as [| P IH].
  - reflexivity.
  - replace (S P * M)%nat with (P * M + M)%nat by lia.
    rewrite fsum_add_len, IH. cbn [fsum]. reflexivity.
Qed.

Lemma fsum_const (x : R) (n : nat) : fsum (fun _ => x) n = INR n * x.
Proof. induction n as [| n IH]; cbn [fsum]; [simpl; ring | rewrite IH, S_INR; ring]. Qed.

Lemma fsum_zero (n : nat) : fsum (fun _ => 0) n = 0.
Proof. rewrite fsum_const. ring. Qed.

(** * Row transforms over one period *)

Section RowPer.

Variables (P M : nat) (f g : nat -> nat -> R) (a : nat).
Hypothesis HP : (0 < P)%nat.
Hypothesis HM : (0 < M)%nat.
Hypothesis Hfg : forall c b, (b < M)%nat -> f a (c * M + b)%nat = g a b.

Lemma gpt_block (l : Z) (c b : nat) :
  IZR (Z.of_nat P * l) * gpt (P * M) (c * M + b) = 2 * PI * IZR (l * Z.of_nat c) + IZR l * gpt M b.
Proof.
  unfold gpt. rewrite !mult_IZR, <- !INR_IZR_INZ, !mult_INR, plus_INR, mult_INR.
  assert (INR P <> 0) by (apply not_0_INR; lia).
  assert (INR M <> 0) by (apply not_0_INR; lia).
  field. split; assumption.
Qed.

Lemma cos_block (l : Z) (c b : nat) :
  cos (IZR (Z.of_nat P * l) * gpt (P * M) (c * M + b)) = cos (IZR l * gpt M b).
Proof. rewrite gpt_block, cos_plus, cos_2piz, sin_2piz. ring. Qed.

Lemma sin_block (l : Z) (c b : nat) :
  sin (IZR (Z.of_nat P * l) * gpt (P * M) (c * M + b)) = sin (IZR l * gpt M b).
Proof. rewrite gpt_block, sin_plus, cos_2piz, sin_2piz. ring. Qed.

Theorem rowG_per (l : Z) : rowG f (P * M) (Z.of_nat P * l) a = INR P * rowG g M l a.
Proof.
  unfold rowG. rewrite fsum_blocks.
  rewrite (fsum_ext _ (fun _ => fsum (fun b => g a b * cos (IZR l * gpt M b)) M)).
  - apply fsum_const.
  - intros c. apply fsum_ext_lt. intros b Hb. rewrite (Hfg c b Hb), cos_block. reflexivity.
Qed.

Theorem rowH_per (l : Z) : rowH f (P * M) (Z.of_nat P * l) a = INR P * rowH g M l a.
Proof.
  unfold rowH. rewrite fsum_blocks.
  rewrite (fsum_ext _ (fun _ => fsum (fun b => g a b * sin (IZR l * gpt M b)) M)).
  - apply fsum_const.
  - intros c. apply fsum_ext_lt. intros b Hb. rewrite (Hfg c b Hb), sin_block. reflexivity.
Qed.

End RowPer.

(** * Sums over the multiples of P *)

Section Mult.

Variable P : Z.
Hypothesis HP : (0 < P)%Z.

Let Pn := Z.to_nat P.

Lemma HPz : Z.of_nat Pn = P.
Proof. unfold Pn. apply Z2Nat.id. lia. Qed.

Lemma HPn : (0 < Pn)%nat.
Proof. pose proof HPz. lia. Qed.

Lemma off_opp (l : Z) : off P l -> off P (- l).
Proof.
  unfold off. intros H E. apply H. apply Z.mod_divide; [lia |].
  apply Z.mod_divide in E; [| lia]. apply Z.divide_opp_r in E. rewrite Z.opp_involutive in E. exact E.
Qed.

Lemma off_mid (K s : nat) : (0 < s < Pn)%nat ->
  off P (Z.of_nat (Pn * K + s)) /\ off P (- Z.of_nat (Pn * K + s)).
Proof.
  intros Hs. pose proof HPz as Hz.
  assert (E : Z.of_nat (Pn * K + s) = (P * Z.of_nat K + Z.of_nat s)%Z)
    by (rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Hz; ring).
  assert (ND : ~ (P | P * Z.of_nat K + Z.of_nat s)%Z).
  { intros D. assert (D2 : (P | Z.of_nat s)%Z).
    { apply (Z.divide_add_cancel_r P (P * Z.of_nat K) (Z.of_nat s)); [apply Z.divide_factor_l | exact D]. }
    apply Z.divide_pos_le in D2; lia. }
  assert (O : off P (Z.of_nat (Pn * K + s))).
  { unfold off. intros Hm. apply ND. rewrite <- E. apply Z.mod_divide; [lia | exact Hm]. }
  exact (conj O (off_opp _ O)).
Qed.

Lemma zsum_add_len (f : Z -> R) (n d : nat) :
  zsum f (n + d) = zsum f n + fsum (fun i => f (Z.of_nat (n + S i)) + f (- Z.of_nat (n + S i))%Z) d.
Proof.
  induction d as [| d IH].
  - rewrite Nat.add_0_r. cbn [fsum]. ring.
  - rewrite Nat.add_succ_r, zsum_S, IH. cbn [fsum]. rewrite <- Nat.add_succ_r. ring.
Qed.

Lemma zsum_mid_zero (f : Z -> R) (K r : nat) :
  (forall l, off P l -> f l = 0) -> (r < Pn)%nat -> zsum f (Pn * K + r) = zsum f (Pn * K).
Proof.
  intros Hf Hr. rewrite zsum_add_len.
  rewrite (fsum_ext_lt _ (fun _ => 0)); [rewrite fsum_zero; ring |].
  intros i Hi. assert (Hs : (0 < S i < Pn)%nat) by lia.
  destruct (off_mid K (S i) Hs) as [A B]. rewrite (Hf _ A), (Hf _ B). ring.
Qed.

Lemma zsum_per_mult (f : Z -> R) (K : nat) :
  (forall l, off P l -> f l = 0) -> zsum f (Pn * K) = zsum (fun l => f (P * l)%Z) K.
Proof.
  intros Hf. pose proof HPn as Hp. induction K as [| K IH].
  - rewrite Nat.mul_0_r, !zsum_0, Z.mul_0_r. reflexivity.
  - assert (E : (Pn * S K = S (Pn * K + (Pn - 1)))%nat) by lia.
    assert (Ez : Z.of_nat (S (Pn * K + (Pn - 1))) = (P * Z.of_nat (S K))%Z)
      by (rewrite <- E, Nat2Z.inj_mul, HPz; reflexivity).
    assert (Hr : (Pn - 1 < Pn)%nat) by lia.
    rewrite E, zsum_S, (zsum_mid_zero f K (Pn - 1) Hf Hr), IH, zsum_S, Ez.
    replace (P * - Z.of_nat (S K))%Z with (- (P * Z.of_nat (S K)))%Z by ring. reflexivity.
Qed.

(** The last multiple of P in the range |l| <= Kfull K is P K. *)
Definition Kfull (K : nat) : nat := (Pn * K + (Pn - 1))%nat.

Lemma zsum_per (f : Z -> R) (K : nat) :
  (forall l, off P l -> f l = 0) -> zsum f (Kfull K) = zsum (fun l => f (P * l)%Z) K.
Proof.
  intros Hf. unfold Kfull. assert (Hr : (Pn - 1 < Pn)%nat) by (pose proof HPn; lia).
  rewrite (zsum_mid_zero f K (Pn - 1) Hf Hr). apply zsum_per_mult, Hf.
Qed.

Lemma bsum_per (K1 K2 : nat) (g : Z -> Z -> R) :
  (forall k l, off P l -> g k l = 0) -> bsum K1 (Kfull K2) g = bsum K1 K2 (fun k l => g k (P * l)%Z).
Proof. intros Hg. unfold bsum. apply zsum_ext. intros k. apply zsum_per. intros l Hl. apply Hg, Hl. Qed.

Lemma bsum_ext_in (K1 K2 : nat) (f g : Z -> Z -> R) :
  (forall k l, in_box K1 K2 k l = true -> f k l = g k l) -> bsum K1 K2 f = bsum K1 K2 g.
Proof. intros H. apply Rle_antisym; apply bsum_le; intros k l Hkl; rewrite (H k l Hkl); lra. Qed.

Lemma in_box_per (K1 K2 : nat) (k l : Z) :
  in_box K1 K2 k l = true -> in_box K1 (Kfull K2) k (P * l) = true.
Proof.
  unfold in_box, Kfull. intros E. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply andb_true_intro. split; apply Z.leb_le; [exact E1 |].
  rewrite Z.abs_mul, (Z.abs_eq P) by lia. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, HPz.
  assert (0 <= Z.of_nat (Pn - 1))%Z by lia.
  assert (P * Z.abs l <= P * Z.of_nat K2)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Lemma bsum_per_in (K1 K2 : nat) (g : Z -> Z -> R) :
  (forall k l, in_box K1 (Kfull K2) k l = true -> off P l -> g k l = 0) ->
  bsum K1 (Kfull K2) g = bsum K1 K2 (fun k l => g k (P * l)%Z).
Proof.
  intros Hg.
  set (g' := fun k l => if in_box K1 (Kfull K2) k l then g k l else 0).
  rewrite (bsum_ext_in K1 (Kfull K2) g g') by (intros k l E; unfold g'; rewrite E; reflexivity).
  rewrite bsum_per.
  - apply bsum_ext_in. intros k l E. unfold g'. rewrite (in_box_per K1 K2 k l E). reflexivity.
  - intros k l Hl. unfold g'. destruct (in_box K1 (Kfull K2) k l) eqn:E; [apply Hg; assumption | reflexivity].
Qed.

(** * The norm of a family of period P from its transforms *)

Theorem nbound_model_per (N1 N2 K1 K2 : nat) (u : fser) (w w' Mw : R) :
  (0 < N1)%nat -> (0 < N2)%nat -> 0 <= w -> w <= w' -> is_canon u -> is_per P u -> nbound w' Mw u ->
  nbound w (bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k (P * l)) + Rabs (dfts N1 N2 u k (P * l))
                                   + 2 * (Mw * exp (- (w' * dmode N1 N2 k (P * l))))) * wt w k (P * l))
            + exp (- ((w' - w) * sout K1 (Kfull K2))) * Mw) u.
Proof.
  intros HN1 HN2 Hw Hww Cu Qu Hu N.
  assert (Hw' : 0 <= w') by lra.
  assert (HM : 0 <= Mw) by exact (nbound_nonneg _ _ _ Hu).
  set (inp := fun m n => if in_box K1 (Kfull K2) m n then nterm w u m n else 0).
  set (outp := fun m n => if in_box K1 (Kfull K2) m n then 0 else nterm w u m n).
  rewrite (sqsum_ext _ (fun m n => inp m n + outp m n))
    by (intros m n; unfold inp, outp; destruct (in_box K1 (Kfull K2) m n); ring).
  rewrite sqsum_plus.
  assert (Hin : sqsum inp N <=
                bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k (P * l)) + Rabs (dfts N1 N2 u k (P * l))
                                        + 2 * (Mw * exp (- (w' * dmode N1 N2 k (P * l))))) * wt w k (P * l))).
  { apply Rle_trans with (bsum K1 (Kfull K2) inp).
    - apply sqsum_box.
      + intros m n. unfold inp. destruct (in_box K1 (Kfull K2) m n); [apply nterm_nonneg | lra].
      + intros m n H. unfold inp. rewrite H. reflexivity.
    - rewrite bsum_per.
      2: { intros k l Hl. unfold inp. destruct (in_box K1 (Kfull K2) k l); [| reflexivity].
           unfold nterm. destruct (Qu k l Hl) as [A B]. rewrite A, B, Rabs_R0. ring. }
      apply bsum_le. intros k l _. unfold inp.
      pose proof (wt_pos w k (P * l)) as Hwt.
      pose proof (exp_pos (- (w' * dmode N1 N2 k (P * l)))) as He.
      pose proof (Rabs_pos (dftc N1 N2 u k (P * l))). pose proof (Rabs_pos (dfts N1 N2 u k (P * l))).
      assert (Hme : 0 <= Mw * exp (- (w' * dmode N1 N2 k (P * l)))) by (apply Rmult_le_pos; lra).
      destruct (in_box K1 (Kfull K2) k (P * l)); [| apply Rmult_le_pos; lra].
      pose proof (dftc_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu k (P * l)) as Ec.
      pose proof (dfts_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu k (P * l)) as Es.
      destruct Cu as [Cc Cs].
      assert (Fc : fc u k (P * l) = ccan u k (P * l)) by (unfold ccan; rewrite (Cc k (P * l)%Z); field).
      assert (Fs : fs u k (P * l) = scan u k (P * l)) by (unfold scan; rewrite (Cs k (P * l)%Z); field).
      unfold nterm. rewrite Fc, Fs.
      rewrite Rabs_minus_sym in Ec, Es.
      pose proof (Rabs_triang (ccan u k (P * l) - dftc N1 N2 u k (P * l)) (dftc N1 N2 u k (P * l))) as U1.
      pose proof (Rabs_triang (scan u k (P * l) - dfts N1 N2 u k (P * l)) (dfts N1 N2 u k (P * l))) as U2.
      replace (ccan u k (P * l) - dftc N1 N2 u k (P * l) + dftc N1 N2 u k (P * l)) with (ccan u k (P * l))
        in U1 by ring.
      replace (scan u k (P * l) - dfts N1 N2 u k (P * l) + dfts N1 N2 u k (P * l)) with (scan u k (P * l))
        in U2 by ring.
      set (e := Mw * exp (- (w' * dmode N1 N2 k (P * l)))) in *.
      nra. }
  assert (Hout : sqsum outp N <= exp (- ((w' - w) * sout K1 (Kfull K2))) * Mw).
  { apply Rle_trans with (sqsum (fun m n => exp (- ((w' - w) * sout K1 (Kfull K2))) * nterm w' u m n) N).
    - apply sqsum_le. intros m n. unfold outp.
      destruct (in_box K1 (Kfull K2) m n) eqn:E.
      + apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply nterm_nonneg].
      + apply out_box; assumption.
    - rewrite sqsum_scal. apply Rmult_le_compat_l; [apply Rlt_le, exp_pos | apply Hu]. }
  lra.
Qed.

(** * Diamonds of modes

    The weights of a box grow to e^(w (K1 + kappa K2)) at its corners. Over the
    diamond 10 |k| + |n| <= D they stay below e^(w D / 10), and every mode
    outside it has size at least (D + 1) / 10, so the norm bound holds with the
    box sum masked to the diamond and the tail taken at that size
    ([nbound_model_dia]). *)

Definition in_dq (D : nat) (k n : Z) : bool := (10 * Z.abs k + Z.abs n <=? Z.of_nat D)%Z.

Lemma out_dq (D : nat) (m n : Z) : in_dq D m n = false -> kappa * INR (S D) <= msize m n.
Proof.
  unfold in_dq, msize, kappa. intros H. apply Z.leb_gt in H.
  assert (E : INR (S D) <= 10 * Rabs (IZR m) + Rabs (IZR n)).
  { rewrite <- !abs_IZR, INR_IZR_INZ, Nat2Z.inj_succ.
    replace 10 with (IZR 10) by reflexivity. rewrite <- mult_IZR, <- plus_IZR. apply IZR_le. lia. }
  lra.
Qed.

Lemma out_dq_box (D : nat) (u : fser) (w w' : R) (m n : Z) :
  w <= w' -> in_dq D m n = false ->
  nterm w u m n <= exp (- ((w' - w) * (kappa * INR (S D)))) * nterm w' u m n.
Proof.
  intros Hww H. pose proof (out_dq D m n H) as Hs.
  unfold nterm, wt.
  assert (E : exp (w * msize m n) <= exp (- ((w' - w) * (kappa * INR (S D)))) * exp (w' * msize m n)).
  { rewrite <- exp_plus. apply exp_mono.
    assert (0 <= w' - w) by lra. pose proof (Rmult_le_compat_l (w' - w) _ _ H0 Hs). nra. }
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)).
  pose proof (exp_pos (w * msize m n)). nra.
Qed.

Lemma in_dq_box (D K1 K2 : nat) (m n : Z) :
  (D < 10 * S K1)%nat -> (D < Pn * S K2)%nat -> in_dq D m n = true -> in_box K1 (Kfull K2) m n = true.
Proof.
  unfold in_dq, in_box, Kfull. intros H1 H2 E. apply Z.leb_le in E.
  pose proof HPn as Hp.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Theorem nbound_model_dia (N1 N2 K1 K2 D : nat) (u : fser) (w w' Mw : R) :
  (0 < N1)%nat -> (0 < N2)%nat -> 0 <= w -> w <= w' ->
  (D < 10 * S K1)%nat -> (D < Pn * S K2)%nat -> is_canon u -> is_per P u -> nbound w' Mw u ->
  nbound w (bsum K1 K2 (fun k l => if in_dq D k (P * l)
                                   then (Rabs (dftc N1 N2 u k (P * l)) + Rabs (dfts N1 N2 u k (P * l))
                                         + 2 * (Mw * exp (- (w' * dmode N1 N2 k (P * l))))) * wt w k (P * l)
                                   else 0)
            + exp (- ((w' - w) * (kappa * INR (S D)))) * Mw) u.
Proof.
  intros HN1 HN2 Hw Hww HD1 HD2 Cu Qu Hu N.
  assert (Hw' : 0 <= w') by lra.
  assert (HM : 0 <= Mw) by exact (nbound_nonneg _ _ _ Hu).
  set (inp := fun m n => if in_dq D m n then nterm w u m n else 0).
  set (outp := fun m n => if in_dq D m n then 0 else nterm w u m n).
  rewrite (sqsum_ext _ (fun m n => inp m n + outp m n))
    by (intros m n; unfold inp, outp; destruct (in_dq D m n); ring).
  rewrite sqsum_plus.
  assert (Hin : sqsum inp N <=
                bsum K1 K2 (fun k l => if in_dq D k (P * l)
                                       then (Rabs (dftc N1 N2 u k (P * l)) + Rabs (dfts N1 N2 u k (P * l))
                                             + 2 * (Mw * exp (- (w' * dmode N1 N2 k (P * l))))) * wt w k (P * l)
                                       else 0)).
  { apply Rle_trans with (bsum K1 (Kfull K2) inp).
    - apply sqsum_box.
      + intros m n. unfold inp. destruct (in_dq D m n); [apply nterm_nonneg | lra].
      + intros m n H. unfold inp. destruct (in_dq D m n) eqn:E; [| reflexivity].
        rewrite (in_dq_box D K1 K2 m n HD1 HD2 E) in H. discriminate.
    - rewrite bsum_per.
      2: { intros k l Hl. unfold inp. destruct (in_dq D k l); [| reflexivity].
           unfold nterm. destruct (Qu k l Hl) as [A B]. rewrite A, B, Rabs_R0. ring. }
      apply bsum_le. intros k l _. unfold inp.
      destruct (in_dq D k (P * l)); [| lra].
      pose proof (wt_pos w k (P * l)) as Hwt.
      pose proof (dftc_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu k (P * l)) as Ec.
      pose proof (dfts_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu k (P * l)) as Es.
      destruct Cu as [Cc Cs].
      assert (Fc : fc u k (P * l) = ccan u k (P * l)) by (unfold ccan; rewrite (Cc k (P * l)%Z); field).
      assert (Fs : fs u k (P * l) = scan u k (P * l)) by (unfold scan; rewrite (Cs k (P * l)%Z); field).
      unfold nterm. rewrite Fc, Fs.
      rewrite Rabs_minus_sym in Ec, Es.
      pose proof (Rabs_triang (ccan u k (P * l) - dftc N1 N2 u k (P * l)) (dftc N1 N2 u k (P * l))) as U1.
      pose proof (Rabs_triang (scan u k (P * l) - dfts N1 N2 u k (P * l)) (dfts N1 N2 u k (P * l))) as U2.
      replace (ccan u k (P * l) - dftc N1 N2 u k (P * l) + dftc N1 N2 u k (P * l)) with (ccan u k (P * l))
        in U1 by ring.
      replace (scan u k (P * l) - dfts N1 N2 u k (P * l) + dfts N1 N2 u k (P * l)) with (scan u k (P * l))
        in U2 by ring.
      set (e := Mw * exp (- (w' * dmode N1 N2 k (P * l)))) in *.
      nra. }
  assert (Hout : sqsum outp N <= exp (- ((w' - w) * (kappa * INR (S D)))) * Mw).
  { apply Rle_trans with (sqsum (fun m n => exp (- ((w' - w) * (kappa * INR (S D)))) * nterm w' u m n) N).
    - apply sqsum_le. intros m n. unfold outp.
      destruct (in_dq D m n) eqn:E.
      + apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply nterm_nonneg].
      + apply out_dq_box; assumption.
    - rewrite sqsum_scal. apply Rmult_le_compat_l; [apply Rlt_le, exp_pos | apply Hu]. }
  lra.
Qed.

(** The mean of a canonical family from its transform at the origin. *)
Theorem mean_err (N1 N2 : nat) (u : fser) (w' Mw : R) :
  (0 < N1)%nat -> (0 < N2)%nat -> 0 <= w' -> is_canon u -> nbound w' Mw u ->
  Rabs (dftc N1 N2 u 0 0 - fc u 0 0) <= Mw * exp (- (w' * dmode N1 N2 0 0)).
Proof.
  intros HN1 HN2 Hw' [Cc _] Hu.
  pose proof (dftc_err_kl N1 N2 u w' Mw HN1 HN2 Hw' Hu 0 0) as E.
  assert (F : ccan u 0 0 = fc u 0 0) by (unfold ccan; rewrite (Cc 0%Z 0%Z); simpl; field).
  rewrite F in E. exact E.
Qed.

(** * The exact norm of a finitely supported family of period P *)

Theorem nbound_exact_per (N1 N2 K1 K2 : nat) (u : fser) (rho : R) :
  (2 * K1 < N1)%nat -> (2 * Kfull K2 < N2)%nat -> supp K1 (Kfull K2) u -> is_canon u -> is_per P u ->
  nbound rho (bsum K1 K2 (fun k l => (Rabs (dftc N1 N2 u k (P * l)) + Rabs (dfts N1 N2 u k (P * l)))
                                     * wt rho k (P * l))) u.
Proof.
  intros H1 H2 Hs Cu Qu.
  pose proof (nbound_exact N1 N2 K1 (Kfull K2) u H1 H2 Hs rho Cu) as E.
  rewrite (bsum_per_in K1 K2) in E; [exact E |].
  intros k l Hkl Hl. unfold in_box in Hkl. apply andb_prop in Hkl. destruct Hkl as [Hk Hl2].
  apply Z.leb_le in Hk. apply Z.leb_le in Hl2.
  rewrite (dftc_exact N1 N2 K1 (Kfull K2) u H1 H2 Hs k l Hk Hl2),
    (dfts_exact N1 N2 K1 (Kfull K2) u H1 H2 Hs k l Hk Hl2).
  unfold ccan, scan.
  destruct (Qu k l Hl) as [A B]. destruct (Qu (- k)%Z (- l)%Z (off_opp l Hl)) as [C D].
  rewrite A, B, C, D.
  replace (/ 2 * (0 + 0)) with 0 by ring. replace (/ 2 * (0 - 0)) with 0 by ring.
  rewrite Rabs_R0. ring.
Qed.

End Mult.
