(** Limits of coefficient families.

    A sequence of families that is Cauchy in the norm of a strip rho >= 0
    ([ncauchy]) has every coefficient Cauchy, and [flim] is the family of the
    coefficient limits. The family at step n is within the Cauchy bound of the
    limit on the same strip ([nbound_flim_sub]); the functions they carry
    converge to the function of the limit ([feval_flim]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg.
Local Open Scope R_scope.

Section Limit.

Variable rho : R.
Hypothesis Hr : 0 <= rho.
Variable us : nat -> fser.

(** Past step N every two families differ by at most eps(N) in norm, with
    eps(N) falling to zero. *)
Variable eps : nat -> R.
Hypothesis eps_lim : is_lim_seq eps 0.
Hypothesis cauchy : forall N n m, (N <= n)%nat -> (N <= m)%nat ->
  nbound rho (eps N) (fsub (us n) (us m)).

Lemma coef_cauchy_c (k l : Z) :
  forall N n m, (N <= n)%nat -> (N <= m)%nat -> Rabs (fc (us n) k l - fc (us m) k l) <= eps N.
Proof.
  intros N n m Hn Hm.
  pose proof (tbound_fc rho _ _ Hr (cauchy N n m Hn Hm) k l) as H.
  simpl in H. replace (fc (us n) k l + -1 * fc (us m) k l) with (fc (us n) k l - fc (us m) k l)
    in H by ring. exact H.
Qed.

Lemma coef_cauchy_s (k l : Z) :
  forall N n m, (N <= n)%nat -> (N <= m)%nat -> Rabs (fs (us n) k l - fs (us m) k l) <= eps N.
Proof.
  intros N n m Hn Hm.
  pose proof (tbound_fs rho _ _ Hr (cauchy N n m Hn Hm) k l) as H.
  simpl in H. replace (fs (us n) k l + -1 * fs (us m) k l) with (fs (us n) k l - fs (us m) k l)
    in H by ring. exact H.
Qed.

Lemma seq_cauchy_ex (x : nat -> R) :
  (forall N n m, (N <= n)%nat -> (N <= m)%nat -> Rabs (x n - x m) <= eps N) ->
  ex_finite_lim_seq x.
Proof.
  intros H. apply ex_lim_seq_cauchy_corr. intros e.
  pose proof eps_lim as HL. apply is_lim_seq_spec in HL.
  destruct (HL (pos_div_2 e)) as [N HN].
  exists N. intros n m Hn Hm.
  specialize (HN N (le_n N)). rewrite Rminus_0_r in HN. simpl in HN.
  apply Rabs_lt_between in HN.
  pose proof (H N n m Hn Hm). pose proof (cond_pos e). lra.
Qed.

Definition flim : fser :=
  {| fc := fun k l => real (Lim_seq (fun n => fc (us n) k l)) ;
     fs := fun k l => real (Lim_seq (fun n => fs (us n) k l)) |}.

Lemma flim_c_is_lim (k l : Z) : is_lim_seq (fun n => fc (us n) k l) (fc flim k l).
Proof.
  destruct (seq_cauchy_ex _ (coef_cauchy_c k l)) as [x Hx].
  simpl. rewrite (is_lim_seq_unique _ _ Hx). exact Hx.
Qed.

Lemma flim_s_is_lim (k l : Z) : is_lim_seq (fun n => fs (us n) k l) (fs flim k l).
Proof.
  destruct (seq_cauchy_ex _ (coef_cauchy_s k l)) as [x Hx].
  simpl. rewrite (is_lim_seq_unique _ _ Hx). exact Hx.
Qed.

(** Finite sums of limits are limits of finite sums. *)
Lemma zsum_lim (g : nat -> Z -> R) (h : Z -> R) (M : nat) :
  (forall j, is_lim_seq (fun n => g n j) (h j)) ->
  is_lim_seq (fun n => zsum (g n) M) (zsum h M).
Proof.
  intros H. induction M as [| M IH].
  - eapply is_lim_seq_ext; [intros; rewrite zsum_0; reflexivity |]. rewrite zsum_0. apply H.
  - eapply is_lim_seq_ext; [intros; rewrite zsum_S; reflexivity |]. rewrite zsum_S.
    apply is_lim_seq_plus'; [exact IH | apply is_lim_seq_plus'; apply H].
Qed.

Lemma sqsum_lim (g : nat -> Z -> Z -> R) (h : Z -> Z -> R) (M : nat) :
  (forall j1 j2, is_lim_seq (fun n => g n j1 j2) (h j1 j2)) ->
  is_lim_seq (fun n => sqsum (g n) M) (sqsum h M).
Proof.
  intros H. unfold sqsum.
  apply (zsum_lim (fun n j1 => zsum (fun j2 => g n j1 j2) M) (fun j1 => zsum (fun j2 => h j1 j2) M)).
  intros j1. apply (zsum_lim (fun n j2 => g n j1 j2) (fun j2 => h j1 j2)). intros j2. apply H.
Qed.

Theorem nbound_flim_sub (N n : nat) : (N <= n)%nat -> nbound rho (eps N) (fsub (us n) flim).
Proof.
  intros Hn M.
  (* the partial sum is the limit in m of the partial sums against us m *)
  assert (Hlim : is_lim_seq (fun m => sqsum (nterm rho (fsub (us n) (us m))) M)
                            (sqsum (nterm rho (fsub (us n) flim)) M)).
  { apply (sqsum_lim (fun m => nterm rho (fsub (us n) (us m)))). intros k l.
    unfold nterm. simpl.
    apply is_lim_seq_mult'; [| apply is_lim_seq_const].
    apply is_lim_seq_plus'.
    - apply (is_lim_seq_abs (fun m => fc (us n) k l + -1 * fc (us m) k l)
                            (fc (us n) k l + -1 * fc flim k l)).
      apply is_lim_seq_plus'; [apply is_lim_seq_const |].
      apply is_lim_seq_mult'; [apply is_lim_seq_const | apply flim_c_is_lim].
    - apply (is_lim_seq_abs (fun m => fs (us n) k l + -1 * fs (us m) k l)
                            (fs (us n) k l + -1 * fs flim k l)).
      apply is_lim_seq_plus'; [apply is_lim_seq_const |].
      apply is_lim_seq_mult'; [apply is_lim_seq_const | apply flim_s_is_lim]. }
  apply (is_lim_seq_le_loc (fun m => sqsum (nterm rho (fsub (us n) (us m))) M) (fun _ => eps N)
           (sqsum (nterm rho (fsub (us n) flim)) M) (eps N)).
  - exists N. intros m Hm. apply (cauchy N n m Hn Hm).
  - exact Hlim.
  - apply is_lim_seq_const.
Qed.

Theorem nbound_flim (N : nat) (M : R) : nbound rho M (us N) -> nbound rho (M + eps N) flim.
Proof.
  intros H.
  assert (E : feq flim (fsub (us N) (fsub (us N) flim))).
  { intros k l. simpl. split; ring. }
  apply (nbound_feq _ _ _ _ (feq_sym _ _ E)).
  apply nbound_fsub; [exact H | apply nbound_flim_sub; lia].
Qed.

Theorem feval_flim (t p : R) (N0 : nat) (M : R) :
  nbound rho M (us N0) -> is_lim_seq (fun n => feval (us n) t p) (feval flim t p).
Proof.
  intros H0.
  assert (Hlim_b : forall n, (N0 <= n)%nat -> nbound 0 (M + eps N0 + eps N0) (us n)).
  { intros n Hn.
    assert (E : feq (us n) (fadd (fsub (us n) (us N0)) (us N0))).
    { intros k l. simpl. split; ring. }
    apply (nbound_feq _ _ _ _ (feq_sym _ _ E)).
    replace (M + eps N0 + eps N0) with (eps N0 + (M + eps N0)) by ring.
    apply nbound_fadd.
    - apply (nbound_mono rho); [exact Hr | apply (cauchy N0 n N0 Hn (le_n N0))].
    - apply (nbound_mono rho); [exact Hr |].
      eapply nbound_feq; [apply feq_refl |].
      intros K. eapply Rle_trans; [apply (H0 K) |].
      pose proof (nbound_nonneg _ _ _ (cauchy N0 N0 N0 (le_n N0) (le_n N0))). lra. }
  assert (Hflim : nbound 0 (M + eps N0) flim).
  { apply (nbound_mono rho); [exact Hr | apply nbound_flim, H0]. }
  apply is_lim_seq_spec. intros e.
  pose proof eps_lim as HL. apply is_lim_seq_spec in HL.
  destruct (HL e) as [N1 HN1].
  exists (Nat.max N0 N1). intros n Hn.
  specialize (HN1 N1 (le_n N1)). rewrite Rminus_0_r in HN1.
  apply Rabs_lt_between in HN1.
  pose proof (nbound_flim_sub N1 n ltac:(lia)) as Hd.
  pose proof (Hlim_b n ltac:(lia)) as Hn'.
  rewrite <- (feval_fsub (us n) flim _ _ t p Hn' Hflim).
  eapply Rle_lt_trans.
  - apply (feval_bound _ (eps N1)). apply (nbound_mono rho); [exact Hr | exact Hd].
  - lra.
Qed.

End Limit.
