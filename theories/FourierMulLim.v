(** The product of families carries the product of the functions.

    What a family loses by truncation to the square |m|, |n| <= N is bounded by
    the tail of its norm series ([nbound_tail]), which falls to zero. The
    product of two families differs from the product of their truncations by
    (u - u_N) v + u_N (v - v_N), bounded by those tails, and the product of
    truncations carries the product of their functions ([feval_fmul_trunc]),
    so [feval_fmul]: the function of [fmul u v] is the product of the
    functions of u and v. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem.
Local Open Scope R_scope.

(** * Sums over a square depend only on the square *)

Lemma zsum_ext_in (f g : Z -> R) (N : nat) :
  (forall m, (Z.abs m <= Z.of_nat N)%Z -> f m = g m) -> zsum f N = zsum g N.
Proof.
  induction N as [| N IH]; intros H.
  - rewrite !zsum_0. apply H. simpl. lia.
  - rewrite !zsum_S. rewrite IH by (intros m Hm; apply H; lia).
    rewrite (H (Z.of_nat (S N))) by lia. rewrite (H (- Z.of_nat (S N))%Z) by lia. reflexivity.
Qed.

Lemma sqsum_ext_in (f g : Z -> Z -> R) (N : nat) :
  (forall m n, (Z.abs m <= Z.of_nat N)%Z -> (Z.abs n <= Z.of_nat N)%Z -> f m n = g m n) ->
  sqsum f N = sqsum g N.
Proof.
  intros H. unfold sqsum. apply zsum_ext_in. intros m Hm. apply zsum_ext_in. intros n Hn.
  apply H; assumption.
Qed.

Definition in_part (N : nat) (f : Z -> Z -> R) (m n : Z) : R := if in_sq N m n then f m n else 0.
Definition out_part (N : nat) (f : Z -> Z -> R) (m n : Z) : R := if in_sq N m n then 0 else f m n.

Lemma sqsum_zero (N : nat) : sqsum (fun _ _ => 0) N = 0.
Proof.
  unfold sqsum. rewrite (zsum_ext _ (fun _ => 0 * 0)).
  - rewrite zsum_scal. ring.
  - intros m. rewrite (zsum_ext _ (fun _ => 0 * 0)) by (intros; ring). rewrite zsum_scal. ring.
Qed.

Lemma sqsum_in_part (N M : nat) (f : Z -> Z -> R) :
  (N <= M)%nat -> sqsum (in_part N f) M = sqsum f N.
Proof.
  intros H. replace M with (N + (M - N))%nat by lia.
  generalize (M - N)%nat as k. intros k.
  induction k as [| k IH].
  - rewrite Nat.add_0_r. apply sqsum_ext_in. intros m n Hm Hn.
    unfold in_part, in_sq. destruct (Z.leb_spec (Z.abs m) (Z.of_nat N)); [| lia].
    destruct (Z.leb_spec (Z.abs n) (Z.of_nat N)); [reflexivity | lia].
  - replace (N + S k)%nat with (S (N + k)) by lia.
    rewrite sqsum_S, IH.
    assert (Hl : layer (in_part N f) (N + k) = 0).
    { unfold layer. cbv zeta.
      set (s := Z.of_nat (S (N + k))).
      assert (Hz : forall m n, (Z.abs m > Z.of_nat N)%Z \/ (Z.abs n > Z.of_nat N)%Z ->
                     in_part N f m n = 0).
      { intros m n Hmn. unfold in_part, in_sq.
        destruct (Z.leb_spec (Z.abs m) (Z.of_nat N)); destruct (Z.leb_spec (Z.abs n) (Z.of_nat N));
          simpl; try reflexivity; lia. }
      rewrite (zsum_ext (in_part N f s) (fun _ => 0 * 0)) by (intros; rewrite Hz by (unfold s; lia); ring).
      rewrite (zsum_ext (in_part N f (- s)%Z) (fun _ => 0 * 0))
        by (intros; rewrite Hz by (unfold s; lia); ring).
      rewrite (zsum_ext (fun m => in_part N f m s + in_part N f m (- s)%Z) (fun _ => 0 * 0))
        by (intros; rewrite !Hz by (unfold s; lia); ring).
      rewrite !zsum_scal. ring. }
    rewrite Hl. ring.
Qed.

Lemma sqsum_out_part_small (N M : nat) (f : Z -> Z -> R) :
  (M <= N)%nat -> sqsum (out_part N f) M = 0.
Proof.
  intros H. rewrite <- (sqsum_zero M). apply sqsum_ext_in. intros m n Hm Hn.
  unfold out_part, in_sq.
  destruct (Z.leb_spec (Z.abs m) (Z.of_nat N)); [| lia].
  destruct (Z.leb_spec (Z.abs n) (Z.of_nat N)); [reflexivity | lia].
Qed.

Lemma in_out (N : nat) (f : Z -> Z -> R) (m n : Z) : in_part N f m n + out_part N f m n = f m n.
Proof. unfold in_part, out_part. destruct (in_sq N m n); ring. Qed.

(** * The tail of a norm series *)

Section Tail.

Variables (u : fser) (Mu : R).
Hypothesis Hu : nbound 0 Mu u.

Definition nlim : R := real (Lim_seq (fun N => sqsum (nterm 0 u) N)).

Lemma nlim_is_lim : is_lim_seq (fun N => sqsum (nterm 0 u) N) nlim.
Proof.
  destruct (nbound_cv u Mu Hu) as [l Hl]. unfold nlim. rewrite (is_lim_seq_unique _ _ Hl). exact Hl.
Qed.

Lemma sqsum_nterm_incr (N : nat) : sqsum (nterm 0 u) N <= sqsum (nterm 0 u) (S N).
Proof.
  rewrite sqsum_S.
  assert (0 <= layer (nterm 0 u) N).
  { apply Rle_trans with (Rabs (layer (nterm 0 u) N)); [apply Rabs_pos |].
    apply layer_dom. intros m n. rewrite Rabs_pos_eq by apply nterm_nonneg. lra. }
  lra.
Qed.

Lemma partial_le_nlim (N : nat) : sqsum (nterm 0 u) N <= nlim.
Proof. apply (is_lim_seq_incr_compare _ _ nlim_is_lim sqsum_nterm_incr). Qed.

Lemma nterm_fsub_trunc (N : nat) (m n : Z) :
  nterm 0 (fsub u (trunc N u)) m n = out_part N (nterm 0 u) m n.
Proof.
  unfold nterm, out_part, fsub, fadd, fscal, trunc. simpl.
  destruct (in_sq N m n);
    replace (fc u m n + -1 * fc u m n) with 0 by ring;
    replace (fs u m n + -1 * fs u m n) with 0 by ring;
    rewrite ?Rabs_R0; try ring.
  replace (fc u m n + -1 * 0) with (fc u m n) by ring.
  replace (fs u m n + -1 * 0) with (fs u m n) by ring. reflexivity.
Qed.

Theorem nbound_tail (N : nat) : nbound 0 (nlim - sqsum (nterm 0 u) N) (fsub u (trunc N u)).
Proof.
  intros M.
  rewrite (sqsum_ext _ (out_part N (nterm 0 u))) by apply nterm_fsub_trunc.
  pose proof (partial_le_nlim N).
  destruct (Nat.le_ge_cases M N) as [HMN | HNM].
  - rewrite sqsum_out_part_small by exact HMN. lra.
  - assert (Hsplit : sqsum (in_part N (nterm 0 u)) M + sqsum (out_part N (nterm 0 u)) M
                     = sqsum (nterm 0 u) M).
    { rewrite <- sqsum_plus. apply sqsum_ext. intros m n. apply in_out. }
    rewrite (sqsum_in_part N M) in Hsplit by exact HNM.
    pose proof (partial_le_nlim M). lra.
Qed.

Lemma tail_small (eps : posreal) : exists N, nlim - sqsum (nterm 0 u) N < eps.
Proof.
  pose proof nlim_is_lim as H. apply is_lim_seq_spec in H.
  destruct (H eps) as [N HN]. exists N.
  specialize (HN N (le_n N)). apply Rabs_lt_between in HN. lra.
Qed.

Lemma partial_mono (N N' : nat) : (N <= N')%nat -> sqsum (nterm 0 u) N <= sqsum (nterm 0 u) N'.
Proof.
  intros H. replace N' with (N + (N' - N))%nat by lia.
  generalize (N' - N)%nat as k. intros k.
  induction k as [| k IH]; [rewrite Nat.add_0_r; lra |].
  replace (N + S k)%nat with (S (N + k)) by lia.
  eapply Rle_trans; [exact IH | apply sqsum_nterm_incr].
Qed.

Lemma nbound_trunc (N : nat) : nbound 0 Mu (trunc N u).
Proof.
  intros M. eapply Rle_trans; [| apply (Hu M)].
  apply sqsum_le. intros m n. unfold nterm, trunc. simpl.
  destruct (in_sq N m n); [lra |].
  rewrite Rabs_R0. replace ((0 + 0) * wt 0 m n) with 0 by ring.
  apply Rmult_le_pos; [| apply Rlt_le, wt_pos].
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). lra.
Qed.

End Tail.

(** * The product of functions *)

Theorem feval_fmul (u v : fser) (Mu Mv t p : R) :
  nbound 0 Mu u -> nbound 0 Mv v ->
  feval (fmul u v) t p = feval u t p * feval v t p.
Proof.
  intros Hu Hv.
  assert (HMu : 0 <= Mu) by (apply (nbound_nonneg 0 Mu u Hu)).
  assert (HMv : 0 <= Mv) by (apply (nbound_nonneg 0 Mv v Hv)).
  set (D := feval (fmul u v) t p - feval u t p * feval v t p).
  (* for every N, |D| <= 2 (tail_u(N) Mv + Mu tail_v(N)) *)
  assert (Hbound : forall N, Rabs D <= 2 * ((nlim u - sqsum (nterm 0 u) N) * Mv
                                        + Mu * (nlim v - sqsum (nterm 0 v) N))).
  { intros N.
    set (uN := trunc N u). set (vN := trunc N v).
    set (tu := nlim u - sqsum (nterm 0 u) N). set (tv := nlim v - sqsum (nterm 0 v) N).
    pose proof (nbound_tail u Mu Hu N) as Htu. fold tu uN in Htu.
    pose proof (nbound_tail v Mv Hv N) as Htv. fold tv vN in Htv.
    pose proof (nbound_trunc u Mu Hu N) as HuN. fold uN in HuN.
    pose proof (nbound_trunc v Mv Hv N) as HvN. fold vN in HvN.
    assert (Htu0 : 0 <= tu) by (apply (nbound_nonneg 0 tu _ Htu)).
    assert (Htv0 : 0 <= tv) by (apply (nbound_nonneg 0 tv _ Htv)).
    (* u = (u - uN) + uN and v = (v - vN) + vN, mode by mode *)
    assert (Eu : feq u (fadd (fsub u uN) uN)).
    { intros m n. simpl. split; ring. }
    assert (Ev : feq v (fadd (fsub v vN) vN)).
    { intros m n. simpl. split; ring. }
    (* the function of the product, split *)
    assert (E1 : feval (fmul u v) t p
                 = feval (fmul (fsub u uN) v) t p + feval (fmul uN (fsub v vN)) t p
                   + feval (fmul uN vN) t p).
    { rewrite (feval_feq _ _ t p (fmul_feq_l _ _ v Eu)).
      rewrite (feval_feq _ _ t p (fmul_fadd_l 0 (Rle_refl 0) _ _ v tu Mu Mv Htu HuN Hv)).
      rewrite (feval_fadd _ _ (tu * Mv) (Mu * Mv) t p (nbound_fmul 0 _ _ _ _ (Rle_refl 0) Htu Hv)
                 (nbound_fmul 0 _ _ _ _ (Rle_refl 0) HuN Hv)).
      rewrite (feval_feq (fmul uN v) _ t p (fmul_feq_r uN _ _ Ev)).
      rewrite (feval_feq _ _ t p (fmul_fadd_r 0 (Rle_refl 0) uN _ _ Mu tv Mv HuN Htv HvN)).
      rewrite (feval_fadd _ _ (Mu * tv) (Mu * Mv) t p (nbound_fmul 0 _ _ _ _ (Rle_refl 0) HuN Htv)
                 (nbound_fmul 0 _ _ _ _ (Rle_refl 0) HuN HvN)).
      ring. }
    pose proof (feval_fmul_trunc u v Mu Mv N t p Hu Hv) as Ht. fold uN vN in Ht.
    rewrite Ht in E1.
    (* the functions of u and v, split *)
    assert (E2 : feval u t p = feval (fsub u uN) t p + feval uN t p).
    { rewrite (feval_feq _ _ t p Eu). apply (feval_fadd _ _ tu Mu t p Htu HuN). }
    assert (E3 : feval v t p = feval (fsub v vN) t p + feval vN t p).
    { rewrite (feval_feq _ _ t p Ev). apply (feval_fadd _ _ tv Mv t p Htv HvN). }
    pose proof (feval_bound _ _ t p (nbound_fmul 0 _ _ _ _ (Rle_refl 0) Htu Hv)) as B1.
    pose proof (feval_bound _ _ t p (nbound_fmul 0 _ _ _ _ (Rle_refl 0) HuN Htv)) as B2.
    pose proof (feval_bound _ _ t p Htu) as B3. pose proof (feval_bound _ _ t p Htv) as B4.
    pose proof (feval_bound _ _ t p HuN) as B5. pose proof (feval_bound _ _ t p HvN) as B6.
    pose proof (feval_bound _ _ t p Hv) as B7.
    unfold D. rewrite E1, E2, E3.
    set (a := feval (fsub u uN) t p) in *. set (b := feval uN t p) in *.
    set (c := feval (fsub v vN) t p) in *. set (d := feval vN t p) in *.
    set (x := feval (fmul (fsub u uN) v) t p) in *. set (y := feval (fmul uN (fsub v vN)) t p) in *.
    replace (x + y + b * d - (a + b) * (c + d)) with (x + y - (a * (c + d) + b * c)) by ring.
    assert (T : Rabs (x + y - (a * (c + d) + b * c))
                <= Rabs x + Rabs y + Rabs a * Rabs (c + d) + Rabs b * Rabs c).
    { unfold Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
      pose proof (Rabs_triang x y) as T1.
      pose proof (Rabs_triang (a * (c + d)) (b * c)) as T2. rewrite !Rabs_mult in T2. lra. }
    assert (Hcd : Rabs (c + d) <= Mv) by (rewrite <- E3; exact B7).
    assert (P1 : Rabs a * Rabs (c + d) <= tu * Mv)
      by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact B3 | exact Hcd]).
    assert (P2 : Rabs b * Rabs c <= Mu * tv)
      by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact B5 | exact B4]).
    lra. }
  (* |D| is below every positive number *)
  destruct (Req_dec D 0) as [HD | HD]; [unfold D in HD; lra |].
  exfalso.
  assert (Hpos : 0 < Rabs D) by (apply Rabs_pos_lt, HD).
  set (e := Rabs D / (4 * (Mu + Mv + 1))).
  assert (He : 0 < e) by (unfold e; apply Rdiv_lt_0_compat; lra).
  destruct (tail_small u Mu Hu (mkposreal e He)) as [N1 HN1].
  destruct (tail_small v Mv Hv (mkposreal e He)) as [N2 HN2].
  simpl in HN1, HN2.
  set (N := Nat.max N1 N2).
  pose proof (Hbound N) as HB.
  pose proof (partial_mono u N1 N ltac:(unfold N; lia)) as Hm1.
  pose proof (partial_mono v N2 N ltac:(unfold N; lia)) as Hm2.
  pose proof (partial_le_nlim u Mu Hu N) as Hl1.
  pose proof (partial_le_nlim v Mv Hv N) as Hl2.
  set (tu := nlim u - sqsum (nterm 0 u) N) in *.
  set (tv := nlim v - sqsum (nterm 0 v) N) in *.
  assert (Htu : 0 <= tu <= e) by (unfold tu; lra).
  assert (Htv : 0 <= tv <= e) by (unfold tv; lra).
  assert (Hbig : 2 * (tu * Mv + Mu * tv) <= 2 * (e * (Mu + Mv))).
  { assert (tu * Mv <= e * Mv) by (apply Rmult_le_compat_r; lra).
    assert (Mu * tv <= Mu * e) by (apply Rmult_le_compat_l; lra). nra. }
  assert (Hsmall : 2 * (e * (Mu + Mv)) < Rabs D).
  { unfold e.
    replace (2 * (Rabs D / (4 * (Mu + Mv + 1)) * (Mu + Mv)))
      with (Rabs D * ((Mu + Mv) / (2 * (Mu + Mv + 1)))) by (field; lra).
    rewrite <- (Rmult_1_r (Rabs D)) at 2.
    apply Rmult_lt_compat_l; [exact Hpos |].
    apply Rmult_lt_reg_r with (2 * (Mu + Mv + 1)); [lra |].
    replace ((Mu + Mv) / (2 * (Mu + Mv + 1)) * (2 * (Mu + Mv + 1))) with (Mu + Mv) by (field; lra).
    lra. }
  lra.
Qed.
