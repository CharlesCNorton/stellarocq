(** Families of one field period.

    A family belongs to period P when its coefficients vanish off the modes
    whose second index is a multiple of P; its function is then periodic in
    the second angle with period 2 pi / P. Sums, multiples, products,
    derivatives, L, its inverse, limits, Newton inverses and inverse square
    roots keep the class ([fmul_per], [linv_per], [finv_per],
    [fisqrt_per]). On such families the inverse of L needs the rotation
    number to be Diophantine only against the multiples of P ([dioph_per]),
    and loses (1 + 1 / (e delta)) / gamma_P of the strip
    ([nbound_linv_per]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Dioph Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulLim FourierLim FourierInv FourierSqrt FourierParity.
Local Open Scope R_scope.

Section Period.

Variable P : Z.
Hypothesis HP : (0 < P)%Z.

Definition off (n : Z) : Prop := (n mod P <> 0)%Z.

Definition is_per (u : fser) : Prop := forall m n, off n -> fc u m n = 0 /\ fs u m n = 0.

Lemma off_split (n l : Z) : off n -> off l \/ off (n - l).
Proof.
  unfold off. intros Hn.
  destruct (Z.eq_dec (l mod P) 0) as [Hl | Hl]; [right | left; exact Hl].
  intros Hnl. apply Hn.
  apply Z.mod_divide; [lia |].
  apply Z.mod_divide in Hl; [| lia]. apply Z.mod_divide in Hnl; [| lia].
  replace n with (l + (n - l))%Z by ring. apply Z.divide_add_r; assumption.
Qed.

Lemma off_split' (n l : Z) : off n -> off l \/ off (l - n).
Proof.
  intros Hn. destruct (off_split n l Hn) as [H | H]; [left; exact H | right].
  unfold off in *. intros E. apply H.
  apply Z.mod_divide; [lia |]. apply Z.mod_divide in E; [| lia].
  replace (n - l)%Z with (- (l - n))%Z by ring. apply Z.divide_opp_r, E.
Qed.

Lemma off_zero : ~ off 0.
Proof. unfold off. rewrite Z.mod_0_l by lia. auto. Qed.

(** * Products *)

Lemma conv_p_off (f g : Z -> Z -> R) (m n : Z) :
  (forall k l, off l -> f k l = 0) -> (forall k l, off l -> g k l = 0) -> off n -> conv_p f g m n = 0.
Proof.
  intros Hf Hg Hn. unfold conv_p. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |].
  intros k l. destruct (off_split n l Hn) as [H | H]; [rewrite (Hf k l H) | rewrite (Hg _ _ H)]; ring.
Qed.

Lemma conv_m_off (f g : Z -> Z -> R) (m n : Z) :
  (forall k l, off l -> f k l = 0) -> (forall k l, off l -> g k l = 0) -> off n -> conv_m f g m n = 0.
Proof.
  intros Hf Hg Hn. unfold conv_m. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |].
  intros k l. destruct (off_split' n l Hn) as [H | H]; [rewrite (Hf k l H) | rewrite (Hg _ _ H)]; ring.
Qed.

Lemma fmul_per (u v : fser) : is_per u -> is_per v -> is_per (fmul u v).
Proof.
  intros Hu Hv m n Hn.
  assert (Uc : forall k l, off l -> fc u k l = 0) by (intros k l H; exact (proj1 (Hu k l H))).
  assert (Us : forall k l, off l -> fs u k l = 0) by (intros k l H; exact (proj2 (Hu k l H))).
  assert (Vc : forall k l, off l -> fc v k l = 0) by (intros k l H; exact (proj1 (Hv k l H))).
  assert (Vs : forall k l, off l -> fs v k l = 0) by (intros k l H; exact (proj2 (Hv k l H))).
  simpl. split.
  - rewrite (conv_p_off (fc u) (fc v)), (conv_p_off (fs u) (fs v)),
      (conv_m_off (fc u) (fc v)), (conv_m_off (fs u) (fs v)) by assumption. ring.
  - rewrite (conv_p_off (fc u) (fs v)), (conv_p_off (fs u) (fc v)),
      (conv_m_off (fc u) (fs v)), (conv_m_off (fs u) (fc v)) by assumption. ring.
Qed.

(** * Linear operations *)

Lemma fadd_per (u v : fser) : is_per u -> is_per v -> is_per (fadd u v).
Proof.
  intros Hu Hv m n Hn. destruct (Hu m n Hn) as [A B]. destruct (Hv m n Hn) as [C D].
  simpl. rewrite A, B, C, D. split; ring.
Qed.

Lemma fscal_per (c : R) (u : fser) : is_per u -> is_per (fscal c u).
Proof. intros Hu m n Hn. destruct (Hu m n Hn) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma fsub_per (u v : fser) : is_per u -> is_per v -> is_per (fsub u v).
Proof. intros Hu Hv. apply fadd_per; [exact Hu | apply fscal_per, Hv]. Qed.

Lemma fzero_per : is_per fzero.
Proof. intros m n _. split; reflexivity. Qed.

Lemma fsingle0_per (c s : R) : is_per (fsingle 0 0 c s).
Proof.
  intros m n Hn. unfold fsingle, at2. simpl.
  destruct (Z.eqb_spec n 0) as [E | E]; [subst n; exfalso; exact (off_zero Hn) |].
  rewrite Bool.andb_false_r. split; reflexivity.
Qed.

Lemma fone_per : is_per fone.
Proof. unfold fone. apply fsingle0_per. Qed.

(** * Derivatives, the operator L and its inverse *)

Lemma dt_per (u : fser) : is_per u -> is_per (dt u).
Proof. intros Hu m n Hn. destruct (Hu m n Hn) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma dp_per (u : fser) : is_per u -> is_per (dp u).
Proof. intros Hu m n Hn. destruct (Hu m n Hn) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma lc_per (rho0 : R) (u : fser) : is_per u -> is_per (lc rho0 u).
Proof. intros Hu m n Hn. destruct (Hu m n Hn) as [A B]. simpl. rewrite A, B. split; ring. Qed.

Lemma linv_per (rho0 : R) (u : fser) : is_per u -> is_per (linv rho0 u).
Proof.
  intros Hu m n Hn. destruct (Hu m n Hn) as [A B]. simpl.
  destruct (is_mean m n); [split; reflexivity |]. rewrite A, B. unfold Rdiv. split; ring.
Qed.

(** * Limits, inverses and inverse square roots *)

Lemma flim_per (us : nat -> fser) : (forall k, is_per (us k)) -> is_per (flim us).
Proof.
  intros H m n Hn. simpl. split.
  - rewrite (Lim_seq_ext _ (fun _ => 0)) by (intros k; exact (proj1 (H k m n Hn))).
    rewrite Lim_seq_const. reflexivity.
  - rewrite (Lim_seq_ext _ (fun _ => 0)) by (intros k; exact (proj2 (H k m n Hn))).
    rewrite Lim_seq_const. reflexivity.
Qed.

Lemma finv_per (u y0 : fser) : is_per u -> is_per y0 -> is_per (finv u y0).
Proof.
  intros Hu Hy0. unfold finv. apply flim_per. intros k.
  assert (H : is_per (iy u y0 k) /\ is_per (ie u y0 k)).
  { induction k as [| k [IHy IHe]].
    - unfold iy, ie. simpl. split; [exact Hy0 |].
      apply fsub_per; [apply fone_per | apply fmul_per; assumption].
    - rewrite iy_S, ie_S. split.
      + apply fmul_per; [exact IHy | apply fadd_per; [apply fone_per | exact IHe]].
      + apply fmul_per; assumption. }
  apply H.
Qed.

Lemma fisqrt_per (D y0 : fser) : is_per D -> is_per y0 -> is_per (fisqrt D y0).
Proof.
  intros HD Hy0. unfold fisqrt. apply flim_per. intros k.
  assert (H : is_per (sy D y0 k) /\ is_per (se D y0 k)).
  { induction k as [| k [IHy IHe]].
    - unfold sy, se. simpl. split; [exact Hy0 |].
      apply fsub_per; [apply fone_per |].
      apply fmul_per; [exact HD | apply fmul_per; assumption].
    - rewrite sy_S, se_S. unfold half_step, err_step. split.
      + apply fmul_per; [exact IHy |].
        apply fadd_per; [apply fone_per | apply fscal_per, IHe].
      + apply fadd_per; apply fscal_per.
        * apply fmul_per; assumption.
        * apply fmul_per; [apply fmul_per; assumption | exact IHe]. }
  apply H.
Qed.

(** * The inverse of L on one period *)

(** The rotation number rho0 against the multiples of P. *)
Definition dioph_per (rho0 gamma : R) : Prop :=
  forall k m : Z, m <> 0%Z -> gamma / Rabs (IZR m) <= Rabs (IZR m * rho0 - IZR (P * k)).

Variables rho0 gamma : R.
Hypothesis Hdio : dioph_per rho0 gamma.
Hypothesis Hg : 0 < gamma <= 1.

Lemma divisor_bound_per (m n : Z) :
  is_mean m n = false -> ~ off n ->
  0 < Rabs (divisor rho0 m n) /\ gamma <= Rabs (divisor rho0 m n) * (1 + msize m n).
Proof.
  intros Hmn Hon. unfold is_mean in Hmn.
  assert (Hs := msize_nonneg m n).
  assert (Hdiv : (P | n)%Z).
  { apply Z.mod_divide; [lia |]. unfold off in Hon. destruct (Z.eq_dec (n mod P) 0) as [E | E]; [exact E |].
    exfalso. exact (Hon E). }
  destruct Hdiv as [k Hk].
  destruct (Z.eq_dec m 0) as [Hm | Hm].
  - subst m. rewrite Z.eqb_refl in Hmn. simpl in Hmn.
    assert (Hn : n <> 0%Z) by (intros ->; discriminate).
    pose proof (abs_IZR_ge_1 n Hn) as H1.
    unfold divisor. rewrite Rmult_0_r, Rplus_0_l.
    split; [lra |].
    apply Rle_trans with (1 * 1); [lra |].
    apply Rmult_le_compat; lra.
  - pose proof (abs_IZR_ge_1 m Hm) as H1.
    pose proof (Hdio (- k)%Z m Hm) as Hd.
    replace (IZR m * rho0 - IZR (P * - k)) with (divisor rho0 m n) in Hd
      by (unfold divisor; rewrite Hk, !mult_IZR, opp_IZR; ring).
    assert (Hpos : 0 < gamma / Rabs (IZR m)) by (apply Rdiv_lt_0_compat; lra).
    split; [lra |].
    apply Rle_trans with (Rabs (divisor rho0 m n) * Rabs (IZR m)).
    + apply Rmult_le_reg_r with (/ Rabs (IZR m)); [apply Rinv_0_lt_compat; lra |].
      replace (Rabs (divisor rho0 m n) * Rabs (IZR m) * / Rabs (IZR m))
        with (Rabs (divisor rho0 m n)) by (field; lra).
      exact Hd.
    + apply Rmult_le_compat_l; [apply Rabs_pos |].
      unfold msize. pose proof (kappa_abs_nonneg n). lra.
Qed.

Theorem nbound_linv_per (rho delta M : R) (u : fser) :
  is_per u -> 0 < delta -> nbound rho M u ->
  nbound (rho - delta) (linv_const gamma delta * M) (linv rho0 u).
Proof.
  intros Hper Hd H N.
  assert (Hc : 0 <= linv_const gamma delta).
  { unfold linv_const. apply Rmult_le_pos.
    - assert (0 < / (exp 1 * delta)).
      { apply Rinv_0_lt_compat, Rmult_lt_0_compat; [apply exp_pos | exact Hd]. }
      lra.
    - apply Rlt_le, Rinv_0_lt_compat. lra. }
  apply Rle_trans with (sqsum (fun m n => linv_const gamma delta * nterm rho u m n) N).
  - apply sqsum_le. intros m n. unfold nterm at 1. simpl.
    destruct (is_mean m n) eqn:Hmn.
    + rewrite Rabs_R0, Rplus_0_l, Rmult_0_l.
      apply Rmult_le_pos; [exact Hc | apply nterm_nonneg].
    + destruct (Classical_Prop.classic (off n)) as [Hoff | Hon].
      * destruct (Hper m n Hoff) as [A B]. rewrite A, B. unfold Rdiv.
        rewrite Rmult_0_l, Ropp_0, Rabs_R0, Rplus_0_l, Rmult_0_l.
        apply Rmult_le_pos; [exact Hc | apply nterm_nonneg].
      * destruct (divisor_bound_per m n Hmn Hon) as [Hd0 Hdg].
        set (D := Rabs (divisor rho0 m n)) in *.
        assert (Hdn : divisor rho0 m n <> 0).
        { intros E. unfold D in Hd0. rewrite E, Rabs_R0 in Hd0. lra. }
        unfold Rdiv. rewrite Rabs_Ropp, !Rabs_mult, Rabs_Rinv by exact Hdn. fold D.
        unfold nterm. rewrite wt_shift.
        set (A := Rabs (fc u m n)). set (B := Rabs (fs u m n)).
        assert (HA : 0 <= A) by apply Rabs_pos. assert (HB : 0 <= B) by apply Rabs_pos.
        assert (Hw : 0 < wt rho m n) by apply wt_pos.
        assert (Hs := msize_nonneg m n).
        assert (Hdec := exp_decay (msize m n) delta Hs Hd).
        assert (Hle1 : exp (- (delta * msize m n)) <= 1).
        { rewrite <- exp_0. apply exp_mono.
          pose proof (Rmult_le_pos delta (msize m n) (Rlt_le _ _ Hd) Hs). lra. }
        assert (He : 0 < exp (- (delta * msize m n))) by apply exp_pos.
        assert (Hinv : / D <= (1 + msize m n) / gamma).
        { apply Rmult_le_reg_l with (D * gamma); [apply Rmult_lt_0_compat; lra |].
          replace (D * gamma * / D) with gamma by (field; lra).
          replace (D * gamma * ((1 + msize m n) / gamma)) with (D * (1 + msize m n))
            by (field; lra).
          exact Hdg. }
        assert (Hdecay : (1 + msize m n) * exp (- (delta * msize m n)) <= 1 + / (exp 1 * delta)).
        { rewrite Rmult_plus_distr_r, Rmult_1_l. lra. }
        replace ((B * / D + A * / D) * (wt rho m n * exp (- (delta * msize m n))))
          with ((A + B) * wt rho m n * (/ D * exp (- (delta * msize m n)))) by ring.
        replace (linv_const gamma delta * ((A + B) * wt rho m n))
          with ((A + B) * wt rho m n * linv_const gamma delta) by ring.
        apply Rmult_le_compat_l; [apply Rmult_le_pos; lra |].
        unfold linv_const.
        apply Rle_trans with ((1 + msize m n) / gamma * exp (- (delta * msize m n))).
        -- apply Rmult_le_compat_r; lra.
        -- replace ((1 + msize m n) / gamma * exp (- (delta * msize m n)))
             with ((1 + msize m n) * exp (- (delta * msize m n)) / gamma) by (field; lra).
           apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Hdecay].
  - rewrite sqsum_scal.
    apply Rmult_le_compat_l; [exact Hc | apply H].
Qed.

End Period.

(** A rotation number that is Diophantine with exponent one per field
    period is Diophantine against the multiples of P, P times over. *)
Lemma dioph_per_of (P : Z) (beta gamma : R) :
  (0 < P)%Z -> diophantine1 beta gamma -> dioph_per P (IZR P * beta) (IZR P * gamma).
Proof.
  intros HP Hd k m Hm.
  pose proof (Hd k m Hm) as H.
  assert (HP' : 0 < IZR P) by (apply IZR_lt; exact HP).
  replace (IZR m * (IZR P * beta) - IZR (P * k)) with (IZR P * (IZR m * beta - IZR k))
    by (rewrite mult_IZR; ring).
  rewrite Rabs_mult, (Rabs_pos_eq (IZR P)) by lra.
  unfold Rdiv. rewrite Rmult_assoc. apply Rmult_le_compat_l; [lra | exact H].
Qed.
