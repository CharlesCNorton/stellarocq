(** Shifts, reflections and the projection onto one field period.

    [fshift c u] is the family whose function is u's moved by c in the second
    angle ([feval_fshift]) and [frefl u] the family whose function is u's at
    (-t, -p) ([feval_frefl]). [fproj P u] keeps the coefficients of the modes
    whose second index is a multiple of P; its function, P times over, is the
    sum of u's over the P shifts by the multiples of 2 pi / P
    ([feval_fproj]), since sums of cosines and sines over the P-th roots of
    unity vanish away from the multiples of P ([cos_roots], [sin_roots]).
    The sum of a family and its reflection is even and their difference is
    odd. *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierDFT FourierParity FourierCanon FourierPer.
Local Open Scope R_scope.

Definition fshift (c : R) (u : fser) : fser :=
  {| fc := fun m n => fc u m n * cos (IZR n * c) + fs u m n * sin (IZR n * c) ;
     fs := fun m n => fs u m n * cos (IZR n * c) - fc u m n * sin (IZR n * c) |}.

Definition frefl (u : fser) : fser := {| fc := fc u ; fs := fun m n => - fs u m n |}.

Definition fproj (P : Z) (u : fser) : fser :=
  {| fc := fun m n => if Z.eqb (n mod P) 0 then fc u m n else 0 ;
     fs := fun m n => if Z.eqb (n mod P) 0 then fs u m n else 0 |}.

(** * Evaluation *)

Lemma term_fshift (c : R) (u : fser) (t p : R) (m n : Z) :
  term (fshift c u) t p m n = term u t (p + c) m n.
Proof.
  unfold term, mode. cbn [fc fs fshift].
  set (A := IZR m * t + IZR n * p).
  replace (IZR m * t + IZR n * (p + c)) with (A + IZR n * c) by (unfold A; ring).
  rewrite (cos_plus A), (sin_plus A). ring.
Qed.

Theorem feval_fshift (c : R) (u : fser) (t p : R) : feval (fshift c u) t p = feval u t (p + c).
Proof. unfold feval. apply zz_sum_ext. intros m n. apply term_fshift. Qed.

Lemma term_frefl (u : fser) (t p : R) (m n : Z) : term (frefl u) t p m n = term u (- t) (- p) m n.
Proof.
  unfold term, mode. cbn [fc fs frefl].
  replace (IZR m * - t + IZR n * - p) with (- (IZR m * t + IZR n * p)) by ring.
  rewrite cos_neg, sin_neg. ring.
Qed.

Theorem feval_frefl (u : fser) (t p : R) : feval (frefl u) t p = feval u (- t) (- p).
Proof. unfold feval. apply zz_sum_ext. intros m n. apply term_frefl. Qed.

(** * Norms *)

Lemma nbound_frefl (rho M : R) (u : fser) : nbound rho M u -> nbound rho M (frefl u).
Proof.
  intros H N. eapply Rle_trans; [| apply (H N)]. right.
  apply sqsum_ext. intros m n. unfold nterm. simpl. rewrite Rabs_Ropp. reflexivity.
Qed.

Lemma nbound_fproj (P : Z) (rho M : R) (u : fser) : nbound rho M u -> nbound rho M (fproj P u).
Proof.
  intros H N. eapply Rle_trans; [| apply (H N)]. apply sqsum_le. intros m n. unfold nterm. simpl.
  destruct (Z.eqb _ _); [lra |].
  rewrite Rabs_R0, Rplus_0_l, Rmult_0_l.
  apply Rmult_le_pos; [| apply Rlt_le, wt_pos].
  pose proof (Rabs_pos (fc u m n)). pose proof (Rabs_pos (fs u m n)). lra.
Qed.

(** * Canonical families, parity and period *)

Lemma mod_opp_zero (P n : Z) : (0 < P)%Z -> Z.eqb ((- n) mod P) 0 = Z.eqb (n mod P) 0.
Proof.
  intros HP.
  destruct (Z.eqb_spec (n mod P) 0) as [E | E]; destruct (Z.eqb_spec ((- n) mod P) 0) as [E' | E']; auto.
  - exfalso. apply E'. apply Z.mod_divide; [lia |]. apply Z.mod_divide in E; [| lia].
    apply Z.divide_opp_r, E.
  - exfalso. apply E. apply Z.mod_divide; [lia |]. apply Z.mod_divide in E'; [| lia].
    apply Z.divide_opp_r in E'. rewrite Z.opp_involutive in E'. exact E'.
Qed.

Lemma fproj_canon (P : Z) (u : fser) : (0 < P)%Z -> is_canon u -> is_canon (fproj P u).
Proof.
  intros HP [Hc Hs]. split; intros m n; simpl; rewrite (mod_opp_zero P n HP);
    destruct (Z.eqb _ _); [apply Hc | reflexivity | apply Hs | ring].
Qed.

Lemma frefl_canon (u : fser) : is_canon u -> is_canon (frefl u).
Proof. intros [Hc Hs]. split; intros m n; simpl; [apply Hc | rewrite Hs; ring]. Qed.

Lemma fproj_per (P : Z) (u : fser) : is_per P (fproj P u).
Proof.
  intros m n Hn. unfold off in Hn. simpl.
  destruct (Z.eqb_spec (n mod P) 0) as [E | E]; [contradiction | split; reflexivity].
Qed.

Lemma frefl_per (P : Z) (u : fser) : is_per P u -> is_per P (frefl u).
Proof. intros H m n Hn. destruct (H m n Hn) as [A B]. simpl. rewrite A, B. split; [reflexivity | ring]. Qed.

Lemma fproj_even (P : Z) (u : fser) : is_even u -> is_even (fproj P u).
Proof. intros H m n. simpl. destruct (Z.eqb _ _); [apply H | reflexivity]. Qed.

Lemma fproj_odd (P : Z) (u : fser) : is_odd u -> is_odd (fproj P u).
Proof. intros H m n. simpl. destruct (Z.eqb _ _); [apply H | reflexivity]. Qed.

Lemma fsym_even (u : fser) : is_even (fadd u (frefl u)).
Proof. intros m n. simpl. ring. Qed.

Lemma fasym_odd (u : fser) : is_odd (fsub u (frefl u)).
Proof. intros m n. simpl. ring. Qed.

(** * Derivatives, the projection and the reflection *)

Lemma dt_fproj (P : Z) (u : fser) : feq (dt (fproj P u)) (fproj P (dt u)).
Proof. intros m n. simpl. destruct (Z.eqb _ _); split; ring. Qed.

Lemma dp_fproj (P : Z) (u : fser) : feq (dp (fproj P u)) (fproj P (dp u)).
Proof. intros m n. simpl. destruct (Z.eqb _ _); split; ring. Qed.

Lemma dt_frefl (u : fser) : feq (dt (frefl u)) (fscal (-1) (frefl (dt u))).
Proof. intros m n. simpl. split; ring. Qed.

Lemma dp_frefl (u : fser) : feq (dp (frefl u)) (fscal (-1) (frefl (dp u))).
Proof. intros m n. simpl. split; ring. Qed.

Lemma fproj_fadd (P : Z) (u v : fser) : feq (fproj P (fadd u v)) (fadd (fproj P u) (fproj P v)).
Proof. intros m n. simpl. destruct (Z.eqb _ _); split; ring. Qed.

Lemma fproj_fscal (P : Z) (c : R) (u : fser) : feq (fproj P (fscal c u)) (fscal c (fproj P u)).
Proof. intros m n. simpl. destruct (Z.eqb _ _); split; ring. Qed.

Lemma frefl_fadd (u v : fser) : feq (frefl (fadd u v)) (fadd (frefl u) (frefl v)).
Proof. intros m n. simpl. split; ring. Qed.

(** Projecting a product with a family of the period projects the other
    factor alone: in the convolution, every term off the multiples of P has
    a factor off them. *)
Lemma fproj_fmul_per (P : Z) (A B : fser) :
  (0 < P)%Z -> is_per P B -> feq (fproj P (fmul A B)) (fmul (fproj P A) B).
Proof.
  intros HP HB m n.
  assert (Bc : forall k l, off P l -> fc B k l = 0) by (intros k l H; exact (proj1 (HB k l H))).
  assert (Bs : forall k l, off P l -> fs B k l = 0) by (intros k l H; exact (proj2 (HB k l H))).
  assert (Hcp : forall (f g : Z -> Z -> R), (forall k l, off P l -> g k l = 0) ->
            conv_p (fun k l => if Z.eqb (l mod P) 0 then f k l else 0) g m n
            = if Z.eqb (n mod P) 0 then conv_p f g m n else 0).
  { intros f g Hg. unfold conv_p.
    destruct (Z.eqb_spec (n mod P) 0) as [E | E].
    - apply zz_sum_ext. intros k l.
      destruct (Z.eqb_spec (l mod P) 0) as [El | El]; [reflexivity |].
      rewrite (Hg (m - k)%Z (n - l)%Z); [ring |].
      intros E'. apply El. apply Z.mod_divide; [lia |]. apply Z.mod_divide in E; [| lia].
      apply Z.mod_divide in E'; [| lia].
      replace l with (n - (n - l))%Z by ring. apply Z.divide_sub_r; assumption.
    - rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |]. intros k l.
      destruct (Z.eqb_spec (l mod P) 0) as [El | El]; [| ring].
      rewrite (Hg (m - k)%Z (n - l)%Z); [ring |].
      intros E'. apply E. apply Z.mod_divide; [lia |]. apply Z.mod_divide in El; [| lia].
      apply Z.mod_divide in E'; [| lia].
      replace n with (l + (n - l))%Z by ring. apply Z.divide_add_r; assumption. }
  assert (Hcm : forall (f g : Z -> Z -> R), (forall k l, off P l -> g k l = 0) ->
            conv_m (fun k l => if Z.eqb (l mod P) 0 then f k l else 0) g m n
            = if Z.eqb (n mod P) 0 then conv_m f g m n else 0).
  { intros f g Hg. unfold conv_m.
    destruct (Z.eqb_spec (n mod P) 0) as [E | E].
    - apply zz_sum_ext. intros k l.
      destruct (Z.eqb_spec (l mod P) 0) as [El | El]; [reflexivity |].
      rewrite (Hg (k - m)%Z (l - n)%Z); [ring |].
      intros E'. apply El. apply Z.mod_divide; [lia |]. apply Z.mod_divide in E; [| lia].
      apply Z.mod_divide in E'; [| lia].
      replace l with ((l - n) + n)%Z by ring. apply Z.divide_add_r; assumption.
    - rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_zero |]. intros k l.
      destruct (Z.eqb_spec (l mod P) 0) as [El | El]; [| ring].
      rewrite (Hg (k - m)%Z (l - n)%Z); [ring |].
      intros E'. apply E. apply Z.mod_divide; [lia |]. apply Z.mod_divide in El; [| lia].
      apply Z.mod_divide in E'; [| lia].
      replace n with (l - (l - n))%Z by ring. apply Z.divide_sub_r; assumption. }
  unfold fmul, fproj. cbn [fc fs].
  rewrite !Hcp, !Hcm by assumption.
  destruct (Z.eqb _ _); split; ring.
Qed.

(** * Sums over the roots of unity *)

Lemma fsum_const (c : R) (N : nat) : fsum (fun _ => c) N = INR N * c.
Proof. induction N as [| N IH]; [simpl; ring |]. simpl fsum. rewrite IH, S_INR. ring. Qed.

Lemma cos_zperiod (x : R) (z : Z) : cos (x + IZR z * (2 * PI)) = cos x.
Proof.
  destruct (Z_le_gt_dec 0 z) as [H | H].
  - rewrite <- (Z2Nat.id z H), <- INR_IZR_INZ.
    replace (x + INR (Z.to_nat z) * (2 * PI)) with (x + 2 * INR (Z.to_nat z) * PI) by ring.
    apply cos_period.
  - set (k := Z.to_nat (- z)).
    replace (IZR z) with (- INR k) by (unfold k; rewrite INR_IZR_INZ, Z2Nat.id by lia; rewrite opp_IZR; ring).
    rewrite <- (cos_period (x + - INR k * (2 * PI)) k).
    f_equal. ring.
Qed.

Lemma sin_zperiod (x : R) (z : Z) : sin (x + IZR z * (2 * PI)) = sin x.
Proof.
  destruct (Z_le_gt_dec 0 z) as [H | H].
  - rewrite <- (Z2Nat.id z H), <- INR_IZR_INZ.
    replace (x + INR (Z.to_nat z) * (2 * PI)) with (x + 2 * INR (Z.to_nat z) * PI) by ring.
    apply sin_period.
  - set (k := Z.to_nat (- z)).
    replace (IZR z) with (- INR k) by (unfold k; rewrite INR_IZR_INZ, Z2Nat.id by lia; rewrite opp_IZR; ring).
    rewrite <- (sin_period (x + - INR k * (2 * PI)) k).
    f_equal. ring.
Qed.

Lemma cos_telescope (A x : R) (N : nat) :
  2 * sin (x / 2) * fsum (fun k => cos (A + INR k * x)) N = sin (A + (INR N - / 2) * x) - sin (A - x / 2).
Proof.
  induction N as [| N IH].
  - simpl fsum. replace (A + (INR 0 - / 2) * x) with (A - x / 2) by (simpl; field). ring.
  - simpl fsum. rewrite Rmult_plus_distr_l, IH, S_INR.
    assert (E : 2 * sin (x / 2) * cos (A + INR N * x)
                = sin (A + INR N * x + x / 2) - sin (A + INR N * x - x / 2)).
    { rewrite sin_plus, sin_minus. ring. }
    rewrite E.
    replace (A + (INR N + 1 - / 2) * x) with (A + INR N * x + x / 2) by field.
    replace (A + (INR N - / 2) * x) with (A + INR N * x - x / 2) by field.
    ring.
Qed.

Lemma sin_telescope (A x : R) (N : nat) :
  2 * sin (x / 2) * fsum (fun k => sin (A + INR k * x)) N = cos (A - x / 2) - cos (A + (INR N - / 2) * x).
Proof.
  induction N as [| N IH].
  - simpl fsum. replace (A + (INR 0 - / 2) * x) with (A - x / 2) by (simpl; field). ring.
  - simpl fsum. rewrite Rmult_plus_distr_l, IH, S_INR.
    assert (E : 2 * sin (x / 2) * sin (A + INR N * x)
                = cos (A + INR N * x - x / 2) - cos (A + INR N * x + x / 2)).
    { rewrite cos_plus, cos_minus. ring. }
    rewrite E.
    replace (A + (INR N + 1 - / 2) * x) with (A + INR N * x + x / 2) by field.
    replace (A + (INR N - / 2) * x) with (A + INR N * x - x / 2) by field.
    ring.
Qed.

Section Roots.

Variable P : Z.
Hypothesis HP : (0 < P)%Z.

Let NP := Z.to_nat P.

Lemma INR_NP : INR NP = IZR P.
Proof. unfold NP. rewrite INR_IZR_INZ, Z2Nat.id by lia. reflexivity. Qed.

Lemma IZR_P_pos : 0 < IZR P. Proof. apply IZR_lt. exact HP. Qed.

Lemma half_sin_nz (n : Z) : (n mod P <> 0)%Z -> sin (2 * PI * IZR n / IZR P / 2) <> 0.
Proof.
  intros Hn E. apply sin_eq_0_0 in E. destruct E as [k Hk].
  apply Hn. apply Z.mod_divide; [lia |]. exists k.
  pose proof IZR_P_pos. pose proof PI_RGT_0.
  apply eq_IZR. rewrite mult_IZR.
  apply (Rmult_eq_reg_r (PI / IZR P)); [| apply Rgt_not_eq, Rdiv_lt_0_compat; lra].
  replace (IZR n * (PI / IZR P)) with (2 * PI * IZR n / IZR P / 2) by (field; lra).
  rewrite Hk. field. lra.
Qed.

Lemma roots_period (A : R) (n : Z) :
  A + (INR NP - / 2) * (2 * PI * IZR n / IZR P) = A - 2 * PI * IZR n / IZR P / 2 + IZR n * (2 * PI).
Proof. rewrite INR_NP. pose proof IZR_P_pos. field. lra. Qed.

Theorem cos_roots (A : R) (n : Z) :
  fsum (fun k => cos (A + INR k * (2 * PI * IZR n / IZR P))) NP
  = if Z.eqb (n mod P) 0 then IZR P * cos A else 0.
Proof.
  destruct (Z.eqb_spec (n mod P) 0) as [E | E].
  - apply Z.mod_divide in E; [| lia]. destruct E as [j Hj].
    rewrite (fsum_ext _ (fun _ => cos A)).
    + rewrite fsum_const, INR_NP. ring.
    + intros k. rewrite Hj, mult_IZR.
      replace (A + INR k * (2 * PI * (IZR j * IZR P) / IZR P)) with (A + IZR (Z.of_nat k * j) * (2 * PI))
        by (rewrite mult_IZR, <- INR_IZR_INZ; pose proof IZR_P_pos; field; lra).
      apply cos_zperiod.
  - set (x := 2 * PI * IZR n / IZR P).
    pose proof (cos_telescope A x NP) as T. unfold x in T at 3. rewrite roots_period, sin_zperiod in T.
    fold x in T.
    apply (Rmult_eq_reg_l (2 * sin (x / 2))); [| pose proof (half_sin_nz n E); unfold x; lra].
    rewrite T. ring.
Qed.

Theorem sin_roots (A : R) (n : Z) :
  fsum (fun k => sin (A + INR k * (2 * PI * IZR n / IZR P))) NP
  = if Z.eqb (n mod P) 0 then IZR P * sin A else 0.
Proof.
  destruct (Z.eqb_spec (n mod P) 0) as [E | E].
  - apply Z.mod_divide in E; [| lia]. destruct E as [j Hj].
    rewrite (fsum_ext _ (fun _ => sin A)).
    + rewrite fsum_const, INR_NP. ring.
    + intros k. rewrite Hj, mult_IZR.
      replace (A + INR k * (2 * PI * (IZR j * IZR P) / IZR P)) with (A + IZR (Z.of_nat k * j) * (2 * PI))
        by (rewrite mult_IZR, <- INR_IZR_INZ; pose proof IZR_P_pos; field; lra).
      apply sin_zperiod.
  - set (x := 2 * PI * IZR n / IZR P).
    pose proof (sin_telescope A x NP) as T. unfold x in T at 4. rewrite roots_period, cos_zperiod in T.
    fold x in T.
    apply (Rmult_eq_reg_l (2 * sin (x / 2))); [| pose proof (half_sin_nz n E); unfold x; lra].
    rewrite T. ring.
Qed.

(** The projection's function is the average over the shifts. *)
Theorem feval_fproj (M : R) (u : fser) (t p : R) :
  nbound 0 M u ->
  IZR P * feval (fproj P u) t p = fsum (fun k => feval u t (p + INR k * (2 * PI / IZR P))) NP.
Proof.
  intros Hu.
  assert (Hs : forall k, abs_summable (term u t (p + INR k * (2 * PI / IZR P))) M).
  { intros k. apply summable_of_nbound, Hu. }
  unfold feval at 2.
  rewrite (zz_sum_fsum (fun k => term u t (p + INR k * (2 * PI / IZR P))) M NP Hs).
  unfold feval. rewrite <- (zz_sum_scal (IZR P) _ M) by (apply summable_of_nbound, nbound_fproj, Hu).
  apply zz_sum_ext. intros m n.
  rewrite (fsum_ext _ (fun k => fc u m n * cos (mode m n t p + INR k * (2 * PI * IZR n / IZR P))
                               + fs u m n * sin (mode m n t p + INR k * (2 * PI * IZR n / IZR P)))).
  - rewrite fsum_plus, !fsum_scal, cos_roots, sin_roots. unfold term. simpl.
    destruct (Z.eqb _ _); ring.
  - intros k. unfold term, mode.
    replace (IZR m * t + IZR n * (p + INR k * (2 * PI / IZR P)))
      with (IZR m * t + IZR n * p + INR k * (2 * PI * IZR n / IZR P)) by (pose proof IZR_P_pos; field; lra).
    reflexivity.
Qed.

End Roots.
