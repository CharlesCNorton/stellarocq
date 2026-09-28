(** * The node residual, and the residuals of states without stellarator symmetry

    [Continuum.continuum_force] proves that the continuum residual of a
    stellarator-symmetric state is mu0 (J x B - grad p) of the reconstructed
    field. This file proves what the other readings of the residual of
    Physics.v compute.

    [continuum_force_asym] is the same theorem for a state without
    stellarator symmetry, whose R gains a sine series and whose Z and lambda
    gain cosine series, over the same modes and by the same radial rules;
    [ajet] is the jet of such a reconstruction, each quantity the sum of its
    two series.

    [node_residual] and [node_residual_asym] take the residual at a node
    ([residual] with the output [RResidual]). Its angular outputs are
    [cres_u] and [cres_v] of the field at the outer half point, and its
    radial output is [node_rs], VMEC's combination of the fields at the two
    half points: their average for a value, and their difference over the
    spacing for a radial derivative. The field at a half point is that of
    the series whose coefficients and radial slopes are VMEC's half-grid
    values and slopes ([hjet], and [ajet] at s = 0). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Deriv Cell Force Series Recon Continuum.
Import ListNotations.

(** * Terms from coefficients *)

Lemma Forall2_map_r {A B C : Type} (P : B -> C -> Prop) (g : A -> C) (l : list A) (cs : list B) :
  Forall2 (fun a c => P c (g a)) l cs -> Forall2 P cs (map g l).
Proof. intros H. induction H as [| a c l' cs' Ha Hs IH]; cbn [map]; constructor; assumption. Qed.

Lemma in_combine_seq {A : Type} (x : nat * A) (n : nat) (l : list A) :
  In x (combine (seq 0 n) l) -> (fst x < n)%nat.
Proof. destruct x as [j a]. intros H. apply in_combine_l in H. apply in_seq in H. cbn [fst]. lia. Qed.

Lemma coef2_terms (E : env ExtendedR) (f f1 : nat -> Z -> R) (modes : list (Z * Z)) (cs : list coef2) :
  Forall2 (fun jmn c => xeval E (c_val c) = Xreal (f (fst jmn) (fst (snd jmn))) /\
                        xeval E (c_ds c) = Xreal (f1 (fst jmn) (fst (snd jmn))))
          (combine (seq 0 (length modes)) modes) cs ->
  Forall2 (kcoef2_ok E 0) cs (cterms f f1 modes).
Proof.
  intros H. unfold cterms. apply Forall2_map_r. eapply Forall2_impl; [| exact H].
  intros jmn c HH. cbv beta in HH |- *. destruct HH as [H1 H2].
  unfold kcoef2_ok, mkterm. cbn [tc tc1]. split; assumption.
Qed.

Lemma coefe_terms (exps : list Z) (E : env ExtendedR) (g : nat -> R) (modes : list (Z * Z)) (cs : list expr)
    (base K rl : nat) :
  (forall j, (j < length modes)%nat -> xeval E (slot_node exps base K rl j) = Xreal (g j)) ->
  Forall2 (fun jmn c => xeval E c = xeval E (slot_node exps base K rl (fst jmn)))
          (combine (seq 0 (length modes)) modes) cs ->
  Forall2 (kcoefe_ok E 0) cs (cterms (fun j _ => g j) (fun _ _ => 0%R) modes).
Proof.
  intros Hg H. unfold cterms. apply Forall2_map_r.
  refine (forall2_combine_seq _ _ _ cs _ H).
  intros x c Hin Hc. cbv beta in Hc |- *. unfold kcoefe_ok, mkterm. cbn [tc]. rewrite Hc.
  apply Hg. exact (in_combine_seq x _ _ Hin).
Qed.

Lemma kers_cterms (E : env ExtendedR) (u v : R) (f f1 : nat -> Z -> R) (modes : list (Z * Z))
    (kers : list mode_kernels) :
  Forall2 (fun mn k => mk_m k = fst mn /\ mk_n k = snd mn /\
     xeval E (mk_cos k) = Xreal (cos (IZR (fst mn) * u - IZR (snd mn) * v)) /\
     xeval E (mk_sin k) = Xreal (sin (IZR (fst mn) * u - IZR (snd mn) * v))) modes kers ->
  Forall2 (kker_ok E u v) kers (cterms f f1 modes).
Proof. intros KV. exact (kernels_terms E u v _ _ _ modes kers 0 KV). Qed.

(** * Sums of two series *)

Lemma padd_values (E : env ExtendedR) (e1 e2 : bool) (kers : list mode_kernels) (c1 c2 : list coef2)
    (t1 t2 : list term) (s u v : R) (q : partials) :
  Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E s (snd kc) t) (combine kers c1) t1 ->
  Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E s (snd kc) t) (combine kers c2) t2 ->
  let p := padd (assemble kers c1 e1) (assemble kers c2 e2) in
  (xeval E (p_0 q) = xeval E (p_0 p) /\ xeval E (p_s q) = xeval E (p_s p) /\
   xeval E (p_u q) = xeval E (p_u p) /\ xeval E (p_v q) = xeval E (p_v p) /\
   xeval E (p_su q) = xeval E (p_su p) /\ xeval E (p_sv q) = xeval E (p_sv p) /\
   xeval E (p_uu q) = xeval E (p_uu p) /\ xeval E (p_uv q) = xeval E (p_uv p) /\
   xeval E (p_vv q) = xeval E (p_vv p)) ->
  xeval E (p_0 q) = Xreal (Series.S0 e1 t1 s u v + Series.S0 e2 t2 s u v) /\
  xeval E (p_s q) = Xreal (S_s e1 t1 s u v + S_s e2 t2 s u v) /\
  xeval E (p_u q) = Xreal (S_u e1 t1 s u v + S_u e2 t2 s u v) /\
  xeval E (p_v q) = Xreal (S_v e1 t1 s u v + S_v e2 t2 s u v) /\
  xeval E (p_su q) = Xreal (S_su e1 t1 s u v + S_su e2 t2 s u v) /\
  xeval E (p_sv q) = Xreal (S_sv e1 t1 s u v + S_sv e2 t2 s u v) /\
  xeval E (p_uu q) = Xreal (S_uu e1 t1 s u v + S_uu e2 t2 s u v) /\
  xeval E (p_uv q) = Xreal (S_uv e1 t1 s u v + S_uv e2 t2 s u v) /\
  xeval E (p_vv q) = Xreal (S_vv e1 t1 s u v + S_vv e2 t2 s u v).
Proof.
  intros H1 H2. cbv zeta. intros HP.
  pose proof (assemble_values E e1 kers c1 t1 s u v H1) as A.
  pose proof (assemble_values E e2 kers c2 t2 s u v H2) as B. cbv zeta in A, B.
  destruct A as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  unfold padd in P1, P2, P3, P4, P5, P6, P7, P8, P9.
  cbn [p_0 p_s p_u p_v p_su p_sv p_uu p_uv p_vv xeval] in P1, P2, P3, P4, P5, P6, P7, P8, P9.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - rewrite P1, A1, B1. reflexivity.
  - rewrite P2, A2, B2. reflexivity.
  - rewrite P3, A3, B3. reflexivity.
  - rewrite P4, A4, B4. reflexivity.
  - rewrite P5, A5, B5. reflexivity.
  - rewrite P6, A6, B6. reflexivity.
  - rewrite P7, A7, B7. reflexivity.
  - rewrite P8, A8, B8. reflexivity.
  - rewrite P9, A9, B9. reflexivity.
Qed.

Lemma ladd_values (E : env ExtendedR) (e1 e2 : bool) (kers : list mode_kernels) (c1 c2 : list expr)
    (t1 t2 : list term) (s u v : R) (q : lpartials) :
  Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E s (snd kc) t) (combine kers c1) t1 ->
  Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E s (snd kc) t) (combine kers c2) t2 ->
  let p := ladd (lambda_terms kers c1 e1) (lambda_terms kers c2 e2) in
  (xeval E (l_u q) = xeval E (l_u p) /\ xeval E (l_v q) = xeval E (l_v p) /\
   xeval E (l_uu q) = xeval E (l_uu p) /\ xeval E (l_uv q) = xeval E (l_uv p) /\
   xeval E (l_vv q) = xeval E (l_vv p)) ->
  xeval E (l_u q) = Xreal (S_u e1 t1 s u v + S_u e2 t2 s u v) /\
  xeval E (l_v q) = Xreal (S_v e1 t1 s u v + S_v e2 t2 s u v) /\
  xeval E (l_uu q) = Xreal (S_uu e1 t1 s u v + S_uu e2 t2 s u v) /\
  xeval E (l_uv q) = Xreal (S_uv e1 t1 s u v + S_uv e2 t2 s u v) /\
  xeval E (l_vv q) = Xreal (S_vv e1 t1 s u v + S_vv e2 t2 s u v).
Proof.
  intros H1 H2. cbv zeta. intros HP.
  pose proof (lambda_terms_values E e1 kers c1 t1 s u v H1) as A.
  pose proof (lambda_terms_values E e2 kers c2 t2 s u v H2) as B. cbv zeta in A, B.
  destruct A as (A1 & A2 & A3 & A4 & A5). destruct B as (B1 & B2 & B3 & B4 & B5).
  destruct HP as (P1 & P2 & P3 & P4 & P5).
  unfold ladd in P1, P2, P3, P4, P5. cbn [l_u l_v l_uu l_uv l_vv xeval] in P1, P2, P3, P4, P5.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - rewrite P1, A1, B1. reflexivity.
  - rewrite P2, A2, B2. reflexivity.
  - rewrite P3, A3, B3. reflexivity.
  - rewrite P4, A4, B4. reflexivity.
  - rewrite P5, A5, B5. reflexivity.
Qed.

Lemma fadd_values (E : env ExtendedR) (e1 e2 : bool) (kers : list mode_kernels) (c1 c2 : list coef3)
    (t1 t2 : list term) (s u v : R) (q : fpartials) :
  Forall2 (kc_ok E s u v) (combine kers c1) t1 -> Forall2 (kc_ok E s u v) (combine kers c2) t2 ->
  let p := fadd (fassemble kers c1 e1) (fassemble kers c2 e2) in
  (xeval E (fp_0 q) = xeval E (fp_0 p) /\ xeval E (fp_s q) = xeval E (fp_s p) /\
   xeval E (fp_ss q) = xeval E (fp_ss p) /\ xeval E (fp_u q) = xeval E (fp_u p) /\
   xeval E (fp_v q) = xeval E (fp_v p) /\ xeval E (fp_su q) = xeval E (fp_su p) /\
   xeval E (fp_sv q) = xeval E (fp_sv p) /\ xeval E (fp_uu q) = xeval E (fp_uu p) /\
   xeval E (fp_uv q) = xeval E (fp_uv p) /\ xeval E (fp_vv q) = xeval E (fp_vv p)) ->
  xeval E (fp_0 q) = Xreal (Series.S0 e1 t1 s u v + Series.S0 e2 t2 s u v) /\
  xeval E (fp_s q) = Xreal (S_s e1 t1 s u v + S_s e2 t2 s u v) /\
  xeval E (fp_ss q) = Xreal (S_ss e1 t1 s u v + S_ss e2 t2 s u v) /\
  xeval E (fp_u q) = Xreal (S_u e1 t1 s u v + S_u e2 t2 s u v) /\
  xeval E (fp_v q) = Xreal (S_v e1 t1 s u v + S_v e2 t2 s u v) /\
  xeval E (fp_su q) = Xreal (S_su e1 t1 s u v + S_su e2 t2 s u v) /\
  xeval E (fp_sv q) = Xreal (S_sv e1 t1 s u v + S_sv e2 t2 s u v) /\
  xeval E (fp_uu q) = Xreal (S_uu e1 t1 s u v + S_uu e2 t2 s u v) /\
  xeval E (fp_uv q) = Xreal (S_uv e1 t1 s u v + S_uv e2 t2 s u v) /\
  xeval E (fp_vv q) = Xreal (S_vv e1 t1 s u v + S_vv e2 t2 s u v).
Proof.
  intros H1 H2. cbv zeta. intros HP.
  pose proof (fassemble_values E e1 kers c1 t1 s u v H1) as A.
  pose proof (fassemble_values E e2 kers c2 t2 s u v H2) as B. cbv zeta in A, B.
  destruct A as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  unfold fadd in P1, P2, P3, P4, P5, P6, P7, P8, P9, P10.
  cbn [fp_0 fp_s fp_ss fp_u fp_v fp_su fp_sv fp_uu fp_uv fp_vv xeval] in P1, P2, P3, P4, P5, P6, P7, P8, P9, P10.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  - rewrite P1, A1, B1. reflexivity.
  - rewrite P2, A2, B2. reflexivity.
  - rewrite P3, A3, B3. reflexivity.
  - rewrite P4, A4, B4. reflexivity.
  - rewrite P5, A5, B5. reflexivity.
  - rewrite P6, A6, B6. reflexivity.
  - rewrite P7, A7, B7. reflexivity.
  - rewrite P8, A8, B8. reflexivity.
  - rewrite P9, A9, B9. reflexivity.
  - rewrite P10, A10, B10. reflexivity.
Qed.

Lemma fladd_values (E : env ExtendedR) (e1 e2 : bool) (kers : list mode_kernels) (c1 c2 : list coef3)
    (t1 t2 : list term) (s u v : R) (q : flpartials) :
  Forall2 (kcl_ok E s u v) (combine kers c1) t1 -> Forall2 (kcl_ok E s u v) (combine kers c2) t2 ->
  let p := fladd (flambda_terms kers c1 e1) (flambda_terms kers c2 e2) in
  (xeval E (flp_u q) = xeval E (flp_u p) /\ xeval E (flp_v q) = xeval E (flp_v p) /\
   xeval E (flp_su q) = xeval E (flp_su p) /\ xeval E (flp_sv q) = xeval E (flp_sv p) /\
   xeval E (flp_uu q) = xeval E (flp_uu p) /\ xeval E (flp_uv q) = xeval E (flp_uv p) /\
   xeval E (flp_vv q) = xeval E (flp_vv p)) ->
  xeval E (flp_u q) = Xreal (S_u e1 t1 s u v + S_u e2 t2 s u v) /\
  xeval E (flp_v q) = Xreal (S_v e1 t1 s u v + S_v e2 t2 s u v) /\
  xeval E (flp_su q) = Xreal (S_su e1 t1 s u v + S_su e2 t2 s u v) /\
  xeval E (flp_sv q) = Xreal (S_sv e1 t1 s u v + S_sv e2 t2 s u v) /\
  xeval E (flp_uu q) = Xreal (S_uu e1 t1 s u v + S_uu e2 t2 s u v) /\
  xeval E (flp_uv q) = Xreal (S_uv e1 t1 s u v + S_uv e2 t2 s u v) /\
  xeval E (flp_vv q) = Xreal (S_vv e1 t1 s u v + S_vv e2 t2 s u v).
Proof.
  intros H1 H2. cbv zeta. intros HP.
  pose proof (flambda_values E e1 kers c1 t1 s u v H1) as A.
  pose proof (flambda_values E e2 kers c2 t2 s u v H2) as B. cbv zeta in A, B.
  destruct A as (A1 & A2 & A3 & A4 & A5 & A6 & A7). destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  unfold fladd in P1, P2, P3, P4, P5, P6, P7.
  cbn [flp_u flp_v flp_su flp_sv flp_uu flp_uv flp_vv xeval] in P1, P2, P3, P4, P5, P6, P7.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite P1, A1, B1. reflexivity.
  - rewrite P2, A2, B2. reflexivity.
  - rewrite P3, A3, B3. reflexivity.
  - rewrite P4, A4, B4. reflexivity.
  - rewrite P5, A5, B5. reflexivity.
  - rewrite P6, A6, B6. reflexivity.
  - rewrite P7, A7, B7. reflexivity.
Qed.

(** * The jet of a state without stellarator symmetry *)

(** R is the cosine series of tR plus the sine series of tRa, Z the sine
    series of tZ plus the cosine series of tZa, lambda the sine series of tL
    plus the cosine series of tLa, all read at (s, u, v). *)
Definition ajet (tR tRa tZ tZa tL tLa : list term) (s u v io iop ph mpp : R) : jet :=
  Jet (Series.S0 true tR s u v + Series.S0 false tRa s u v) (S_s true tR s u v + S_s false tRa s u v)
      (S_u true tR s u v + S_u false tRa s u v) (S_v true tR s u v + S_v false tRa s u v)
      (S_ss true tR s u v + S_ss false tRa s u v)
      (S_su true tR s u v + S_su false tRa s u v) (S_sv true tR s u v + S_sv false tRa s u v)
      (S_uu true tR s u v + S_uu false tRa s u v) (S_uv true tR s u v + S_uv false tRa s u v)
      (S_vv true tR s u v + S_vv false tRa s u v)
      (S_s false tZ s u v + S_s true tZa s u v) (S_u false tZ s u v + S_u true tZa s u v)
      (S_v false tZ s u v + S_v true tZa s u v) (S_ss false tZ s u v + S_ss true tZa s u v)
      (S_su false tZ s u v + S_su true tZa s u v) (S_sv false tZ s u v + S_sv true tZa s u v)
      (S_uu false tZ s u v + S_uu true tZa s u v) (S_uv false tZ s u v + S_uv true tZa s u v)
      (S_vv false tZ s u v + S_vv true tZa s u v)
      (S_u false tL s u v + S_u true tLa s u v) (S_v false tL s u v + S_v true tLa s u v)
      (S_su false tL s u v + S_su true tLa s u v) (S_sv false tL s u v + S_sv true tLa s u v)
      (S_uu false tL s u v + S_uu true tLa s u v) (S_uv false tL s u v + S_uv true tLa s u v)
      (S_vv false tL s u v + S_vv true tLa s u v)
      io iop ph mpp.

Ltac half_close :=
  splits; xcalc; xclose;
  unfold hjet, ajet, Bcov_u, Bcov_v, f_mu0Js, f_B_s_u, f_B_s_v, f_B_u_v, f_B_v_u, f_dcov, f_guu, f_guv, f_gvv,
    f_gsu, f_gsv, f_gsu_u, f_gsu_v, f_gsv_u, f_gsv_v, f_guu_v, f_guv_u, f_guv_v, f_gvv_u,
    f_Bu, f_Bv, f_Bu_u, f_Bv_u, f_Bu_v, f_Bv_v, f_dB, f_g2, f_bu_num, f_bv_num,
    f_g_u, f_g_v, f_tau_u, f_tau_v, f_sqrtg, f_tau;
  cbn [jR jRs jRu jRv jRss jRsu jRsv jRuu jRuv jRvv jZs jZu jZv jZss jZsu jZsv jZuu jZuv jZvv
       jLu jLv jLsu jLsv jLuu jLuv jLvv jiota jiotap jphip jmu0pp];
  reflexivity.

(** * The half points *)

Section HalfField.
Variable exps : list Z.
Variable E : env ExtendedR.

(** The half-point coefficients of a state without stellarator symmetry. *)
Lemma half_coefs_ok2 (b : builder) (modes : list (Z * Z)) (K ra rb rl : nat) (sa' sb' sh' : expr)
    (b' : builder) (hc : half_coefs) :
  half_coefs_b exps b true modes K ra rb rl sa' sb' sh' = (b', hc) -> extends b b' /\
  (sound E (b_binds b') -> forall (a bb h : R) (yRa yRb yZa yZb yAa yAb yBa yBb : nat -> R),
   xeval E sa' = Xreal a -> xeval E sb' = Xreal bb -> xeval E sh' = Xreal h ->
   (0 < a)%R -> (0 < bb)%R -> (0 < h)%R -> (bb - a <> 0)%R ->
   (forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
      xeval E (slot_node exps (base_R K) K ra j) = Xreal (yRa j) /\ xeval E (slot_node exps (base_R K) K rb j) = Xreal (yRb j)) ->
   (forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
      xeval E (slot_node exps (base_Z K) K ra j) = Xreal (yZa j) /\ xeval E (slot_node exps (base_Z K) K rb j) = Xreal (yZb j)) ->
   (forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
      xeval E (slot_node exps (base_Ra K) K ra j) = Xreal (yAa j) /\ xeval E (slot_node exps (base_Ra K) K rb j) = Xreal (yAb j)) ->
   (forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
      xeval E (slot_node exps (base_Za K) K ra j) = Xreal (yBa j) /\ xeval E (slot_node exps (base_Za K) K rb j) = Xreal (yBb j)) ->
   Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) a bb h (yRa (fst jmn)) (yRb (fst jmn))) /\
                         xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) a bb h (yRa (fst jmn)) (yRb (fst jmn))))
           (combine (seq 0 (length modes)) modes) (hc_R hc) /\
   Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) a bb h (yZa (fst jmn)) (yZb (fst jmn))) /\
                         xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) a bb h (yZa (fst jmn)) (yZb (fst jmn))))
           (combine (seq 0 (length modes)) modes) (hc_Z hc) /\
   Forall2 (fun jmn c => xeval E c = xeval E (slot_node exps (base_L K) K rl (fst jmn)))
           (combine (seq 0 (length modes)) modes) (hc_L hc) /\
   Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) a bb h (yAa (fst jmn)) (yAb (fst jmn))) /\
                         xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) a bb h (yAa (fst jmn)) (yAb (fst jmn))))
           (combine (seq 0 (length modes)) modes) (hc_Ra hc) /\
   Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) a bb h (yBa (fst jmn)) (yBb (fst jmn))) /\
                         xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) a bb h (yBa (fst jmn)) (yBb (fst jmn))))
           (combine (seq 0 (length modes)) modes) (hc_Za hc) /\
   Forall2 (fun jmn c => xeval E c = xeval E (slot_node exps (base_La K) K rl (fst jmn)))
           (combine (seq 0 (length modes)) modes) (hc_La hc)).
Proof.
  unfold half_coefs_b. intros H. repeat stepH H. injection H as <- <-.
  cbn [hc_R hc_Z hc_L hc_Ra hc_Za hc_La].
  match goal with Q0 : half_scalars_b _ _ _ _ = _ |- _ => rename Q0 into QA end.
  match goal with Q1 : halfcoefs_b _ _ _ (base_R _) _ _ _ _ _ = _ |- _ => rename Q1 into QB end.
  match goal with Q2 : halfcoefs_b _ _ _ (base_Z _) _ _ _ _ _ = _ |- _ => rename Q2 into QC end.
  match goal with Q3 : lambdacoefs_b _ _ (base_L _) _ _ _ _ = _ |- _ => rename Q3 into QD end.
  match goal with Q4 : halfcoefs_b _ _ _ (base_Ra _) _ _ _ _ _ = _ |- _ => rename Q4 into QE end.
  match goal with Q5 : halfcoefs_b _ _ _ (base_Za _) _ _ _ _ _ = _ |- _ => rename Q5 into QF end.
  match goal with Q6 : lambdacoefs_b _ _ (base_La _) _ _ _ _ = _ |- _ => rename Q6 into QG end.
  destruct (half_scalars_ok E _ _ _ _ _ _ QA) as [X0 V0].
  destruct (halfcoefs_spec exps _ _ _ _ _ _ _ _ _ _ QB) as [X1 _].
  destruct (halfcoefs_spec exps _ _ _ _ _ _ _ _ _ _ QC) as [X2 _].
  destruct (lambdacoefs_ok exps E _ _ _ _ _ _ _ _ QD) as [X3 V3].
  destruct (halfcoefs_spec exps _ _ _ _ _ _ _ _ _ _ QE) as [X4 _].
  destruct (halfcoefs_spec exps _ _ _ _ _ _ _ _ _ _ QF) as [X5 _].
  destruct (lambdacoefs_ok exps E _ _ _ _ _ _ _ _ QG) as [X6 V6].
  split; [ext_chain |].
  intros S6 a bb hh yRa yRb yZa yZb yAa yAb yBa yBb Ha Hb Hh Pa Pb Ph Hab HyR HyZ HyA HyB.
  pose proof (sound_extends E _ _ X6 S6) as S5.
  pose proof (sound_extends E _ _ X5 S5) as S4.
  pose proof (sound_extends E _ _ X4 S4) as S3.
  pose proof (sound_extends E _ _ X3 S3) as S2.
  pose proof (sound_extends E _ _ X2 S2) as S1.
  pose proof (sound_extends E _ _ X1 S1) as S0.
  destruct (V0 S0 a bb hh Ha Hb Hh Pa Pb Ph Hab) as (H1 & H2 & H3 & H4 & H5 & H6).
  refine (conj (halfcoefs_values exps E _ _ _ _ _ a bb hh yRa yRb H1 H2 H3 H4 H5 H6 modes 0 _ _ _ QB HyR S1)
         (conj (halfcoefs_values exps E _ _ _ _ _ a bb hh yZa yZb H1 H2 H3 H4 H5 H6 modes 0 _ _ _ QC HyZ S2)
         (conj (V3 S3)
         (conj (halfcoefs_values exps E _ _ _ _ _ a bb hh yAa yAb H1 H2 H3 H4 H5 H6 modes 0 _ _ _ QE HyA S4)
         (conj (halfcoefs_values exps E _ _ _ _ _ a bb hh yBa yBb H1 H2 H3 H4 H5 H6 modes 0 _ _ _ QF HyB S5)
               (V6 S6)))))).
Qed.

(** The field of a half point of a stellarator-symmetric state. *)
Lemma half_point_ok (b : builder) (kers : list mode_kernels) (hc : half_coefs) (iota : expr)
    (b' : builder) (q : halfq) :
  half_point_b exps b false kers hc iota = (b', q) -> extends b b' /\
  (sound E (b_binds b') -> forall (tR tZ tL : list term) (u v io ph : R),
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_R hc)) tR ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_Z hc)) tZ ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E 0 (snd kc) t) (combine kers (hc_L hc)) tL ->
   xeval E iota = Xreal io -> xeval E (vPhip exps) = Xreal ph ->
   f_sqrtg (hjet tR tZ tL u v io ph) <> 0%R ->
   xeval E (q_Bu q) = Xreal (f_Bu (hjet tR tZ tL u v io ph)) /\
   xeval E (q_Bv q) = Xreal (f_Bv (hjet tR tZ tL u v io ph)) /\
   xeval E (q_B_u q) = Xreal (Bcov_u (hjet tR tZ tL u v io ph)) /\
   xeval E (q_B_v q) = Xreal (Bcov_v (hjet tR tZ tL u v io ph)) /\
   xeval E (q_B_s_u q) = Xreal (f_B_s_u (hjet tR tZ tL u v io ph)) /\
   xeval E (q_B_s_v q) = Xreal (f_B_s_v (hjet tR tZ tL u v io ph)) /\
   xeval E (q_mu0Js q) = Xreal (f_mu0Js (hjet tR tZ tL u v io ph))).
Proof.
  unfold half_point_b. cbv beta iota zeta. repeat step. intros H. injection H as <- <-.
  match goal with
  | QR : partials_b _ (assemble _ _ true) = _, QZ : partials_b _ (assemble _ _ false) = _,
    QL : lambda_partials_b _ _ = _ |- _ =>
      pose proof (proj1 (partials_ok E _ _ _ _ QR)); pose proof (proj1 (partials_ok E _ _ _ _ QZ));
      pose proof (proj1 (lambda_partials_ok E _ _ _ _ QL))
  end.
  ext_of_allocs. split; [ext_chain |].
  intros S tR tZ tL u v io ph HR HZ HL Hio Hph Hsg. peel.
  match goal with
  | QL : lambda_partials_b ?b1 _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (sound_extends E _ _ (proj1 (lambda_partials_ok E _ _ _ _ QL)) S) as SL;
      pose proof (proj2 (lambda_partials_ok E _ _ _ _ QL) S) as PL
  end.
  match goal with
  | QZ : partials_b ?b1 (assemble _ _ false) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (sound_extends E _ _ (proj1 (partials_ok E _ _ _ _ QZ)) S) as SZ;
      pose proof (proj2 (partials_ok E _ _ _ _ QZ) S) as PZ
  end.
  match goal with
  | QR : partials_b ?b1 (assemble _ _ true) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (proj2 (partials_ok E _ _ _ _ QR) S) as PR
  end.
  pose proof (assemble_values E true kers (hc_R hc) tR 0 u v HR) as FR.
  pose proof (assemble_values E false kers (hc_Z hc) tZ 0 u v HZ) as FZ.
  pose proof (lambda_terms_values E false kers (hc_L hc) tL 0 u v HL) as FL.
  cbv zeta in FR, FZ, FL.
  destruct PR as (PR1 & PR2 & PR3 & PR4 & PR5 & PR6 & PR7 & PR8 & PR9).
  destruct PZ as (PZ1 & PZ2 & PZ3 & PZ4 & PZ5 & PZ6 & PZ7 & PZ8 & PZ9).
  destruct PL as (PL1 & PL2 & PL3 & PL4 & PL5).
  destruct FR as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & FR8 & FR9).
  destruct FZ as (FZ1 & FZ2 & FZ3 & FZ4 & FZ5 & FZ6 & FZ7 & FZ8 & FZ9).
  destruct FL as (FL1 & FL2 & FL3 & FL4 & FL5).
  pose proof (eq_trans PR1 FR1) as W1. pose proof (eq_trans PR2 FR2) as W2.
  pose proof (eq_trans PR3 FR3) as W3. pose proof (eq_trans PR4 FR4) as W4.
  pose proof (eq_trans PR5 FR5) as W5. pose proof (eq_trans PR6 FR6) as W6.
  pose proof (eq_trans PR7 FR7) as W7. pose proof (eq_trans PR8 FR8) as W8.
  pose proof (eq_trans PR9 FR9) as W9.
  pose proof (eq_trans PZ1 FZ1) as W10. pose proof (eq_trans PZ2 FZ2) as W11.
  pose proof (eq_trans PZ3 FZ3) as W12. pose proof (eq_trans PZ4 FZ4) as W13.
  pose proof (eq_trans PZ5 FZ5) as W14. pose proof (eq_trans PZ6 FZ6) as W15.
  pose proof (eq_trans PZ7 FZ7) as W16. pose proof (eq_trans PZ8 FZ8) as W17.
  pose proof (eq_trans PZ9 FZ9) as W18.
  pose proof (eq_trans PL1 FL1) as W19. pose proof (eq_trans PL2 FL2) as W20.
  pose proof (eq_trans PL3 FL3) as W21. pose proof (eq_trans PL4 FL4) as W22.
  pose proof (eq_trans PL5 FL5) as W23.
  clear PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PZ1 PZ2 PZ3 PZ4 PZ5 PZ6 PZ7 PZ8 PZ9 PL1 PL2 PL3 PL4 PL5
        FR1 FR2 FR3 FR4 FR5 FR6 FR7 FR8 FR9 FZ1 FZ2 FZ3 FZ4 FZ5 FZ6 FZ7 FZ8 FZ9 FL1 FL2 FL3 FL4 FL5.
  unfold f_sqrtg, f_tau, hjet in Hsg. cbn [jR jRs jRu jZs jZu] in Hsg.
  unfold Physics.e1, Physics.esq, Physics.zmul in *.
  cbn [q_Bu q_Bv q_B_u q_B_v q_B_s_u q_B_s_v q_mu0Js].
  half_close.
Qed.

(** The field of a half point of a state without stellarator symmetry. *)
Lemma half_point_ok2 (b : builder) (kers : list mode_kernels) (hc : half_coefs) (iota : expr)
    (b' : builder) (q : halfq) :
  half_point_b exps b true kers hc iota = (b', q) -> extends b b' /\
  (sound E (b_binds b') -> forall (tR tRa tZ tZa tL tLa : list term) (u v io ph : R),
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_R hc)) tR ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_Ra hc)) tRa ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_Z hc)) tZ ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_Za hc)) tZa ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E 0 (snd kc) t) (combine kers (hc_L hc)) tL ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E 0 (snd kc) t) (combine kers (hc_La hc)) tLa ->
   xeval E iota = Xreal io -> xeval E (vPhip exps) = Xreal ph ->
   f_sqrtg (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0) <> 0%R ->
   xeval E (q_Bu q) = Xreal (f_Bu (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0)) /\
   xeval E (q_Bv q) = Xreal (f_Bv (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0)) /\
   xeval E (q_B_u q) = Xreal (Bcov_u (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0)) /\
   xeval E (q_B_v q) = Xreal (Bcov_v (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0)) /\
   xeval E (q_B_s_u q) = Xreal (f_B_s_u (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0)) /\
   xeval E (q_B_s_v q) = Xreal (f_B_s_v (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0)) /\
   xeval E (q_mu0Js q) = Xreal (f_mu0Js (ajet tR tRa tZ tZa tL tLa 0 u v io 0 ph 0))).
Proof.
  unfold half_point_b. cbv beta iota zeta. repeat step. intros H. injection H as <- <-.
  match goal with
  | QR : partials_b _ (padd (assemble _ _ true) _) = _, QZ : partials_b _ (padd (assemble _ _ false) _) = _,
    QL : lambda_partials_b _ _ = _ |- _ =>
      pose proof (proj1 (partials_ok E _ _ _ _ QR)); pose proof (proj1 (partials_ok E _ _ _ _ QZ));
      pose proof (proj1 (lambda_partials_ok E _ _ _ _ QL))
  end.
  ext_of_allocs. split; [ext_chain |].
  intros S tR tRa tZ tZa tL tLa u v io ph HR HRa HZ HZa HL HLa Hio Hph Hsg. peel.
  match goal with
  | QL : lambda_partials_b ?b1 _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (sound_extends E _ _ (proj1 (lambda_partials_ok E _ _ _ _ QL)) S) as SL;
      pose proof (ladd_values E false true kers (hc_L hc) (hc_La hc) tL tLa 0 u v _ HL HLa
                    (proj2 (lambda_partials_ok E _ _ _ _ QL) S)) as WL
  end.
  match goal with
  | QZ : partials_b ?b1 (padd (assemble _ _ false) _) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (sound_extends E _ _ (proj1 (partials_ok E _ _ _ _ QZ)) S) as SZ;
      pose proof (padd_values E false true kers (hc_Z hc) (hc_Za hc) tZ tZa 0 u v _ HZ HZa
                    (proj2 (partials_ok E _ _ _ _ QZ) S)) as WZ
  end.
  match goal with
  | QR : partials_b ?b1 (padd (assemble _ _ true) _) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (padd_values E true false kers (hc_R hc) (hc_Ra hc) tR tRa 0 u v _ HR HRa
                    (proj2 (partials_ok E _ _ _ _ QR) S)) as WR
  end.
  destruct WR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9).
  destruct WZ as (W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18).
  destruct WL as (W19 & W20 & W21 & W22 & W23).
  unfold f_sqrtg, f_tau, ajet in Hsg. cbn [jR jRs jRu jZs jZu] in Hsg.
  unfold Physics.e1, Physics.esq, Physics.zmul in *.
  cbn [q_Bu q_Bv q_B_u q_B_v q_B_s_u q_B_s_v q_mu0Js].
  half_close.
Qed.

End HalfField.

(** * The node residual *)

Ltac node_close :=
  unfold Physics.mu0, Physics.e1, Physics.e2, Physics.e4, Physics.r_u_e, Physics.r_v_e in *;
  splits; xcalc; xclose; unfold node_rs, cres_u, cres_v, mu0r; ring.

Theorem node_residual (exps : list Z) (prof : pprofile) (modes : list (Z * Z)) (env : env ExtendedR) (wm : nat)
    (sa sj sb shm shp u0 v0 phip im ip pp : R) (yR yZ yL : nat -> nat -> R) :
  let r := residual exps (PConfig false prof RResidual) modes in
  well_formed wm (r_binds r) = true ->
  let E := xextend env (r_binds r) in
  xeval E (slot_s_a exps) = Xreal sa -> xeval E (slot_s_j exps) = Xreal sj -> xeval E (slot_s_b exps) = Xreal sb ->
  xeval E (slot_s_hm exps) = Xreal shm -> xeval E (slot_s_hp exps) = Xreal shp ->
  xeval E (vU exps) = Xreal u0 -> xeval E (vV exps) = Xreal v0 -> xeval E (vPhip exps) = Xreal phip ->
  xeval E (slot_iota_m exps) = Xreal im -> xeval E (slot_iota_p exps) = Xreal ip ->
  xeval E (pprime exps prof) = Xreal pp ->
  (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_R (length modes)) (length modes) row j) = Xreal (yR row j)) ->
  (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_Z (length modes)) (length modes) row j) = Xreal (yZ row j)) ->
  (forall row j, (row < 2)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_L (length modes)) (length modes) row j) = Xreal (yL row j)) ->
  (0 < sa)%R -> (0 < sj)%R -> (0 < sb)%R -> (0 < shm)%R -> (0 < shp)%R ->
  (sj - sa <> 0)%R -> (sb - sj <> 0)%R -> (shp - shm <> 0)%R ->
  let jm := hjet (cterms (hya sa sj shm yR) (hda sa sj shm yR) modes)
                 (cterms (hya sa sj shm yZ) (hda sa sj shm yZ) modes)
                 (cterms (fun j _ => yL 0%nat j) (fun _ _ => 0%R) modes) u0 v0 im phip in
  let jp := hjet (cterms (hyb sj sb shp yR) (hdb sj sb shp yR) modes)
                 (cterms (hyb sj sb shp yZ) (hdb sj sb shp yZ) modes)
                 (cterms (fun j _ => yL 1%nat j) (fun _ _ => 0%R) modes) u0 v0 ip phip in
  f_sqrtg jm <> 0%R -> f_sqrtg jp <> 0%R ->
  xeval E (r_s r) = Xreal (node_rs jm jp (1 / (shp - shm)) (mu0r * pp)) /\
  xeval E (r_u r) = Xreal (cres_u jp) /\ xeval E (r_v r) = Xreal (cres_v jp).
Proof.
  intros r Hwf E Hsa Hsj Hsb Hshm Hshp Hu Hv Hph Him Hip Hpp HyR HyZ HyL Pa Pj Pb Phm Php Daj Djb Dh.
  cbv zeta. intros Hm Hp.
  assert (HR : residual exps (PConfig false prof RResidual) modes = r) by reflexivity.
  clearbody r. revert HR.
  unfold residual. cbv beta iota zeta delta [is_radial pc_out pc_lasym pc_prof].
  destruct (residual_pre exps (PConfig false prof RResidual) modes) as [bst kers hcp qp mq mu0pp rs tt] eqn:Hpre.
  unfold residual_tail.
  cbv beta iota zeta delta [pc_out pc_lasym st_b st_kers st_hcp st_qp st_mq st_mu0pp st_rs st_tt].
  repeat step. intros HR. subst r. cbn [r_binds r_s r_u r_v] in *.
  revert Hpre. unfold residual_pre. cbv beta iota zeta delta [pc_out pc_lasym pc_prof].
  repeat step. intros Hpre.
  injection Hpre as E1 E2 E3 E4 E5 E6 E7 E8. subst bst kers hcp qp mq mu0pp rs tt.
  match type of Hwf with well_formed _ (bindings_of ?bl) = true =>
    assert (S : sound E (b_binds bl)) by exact (sound_final env wm bl Hwf) end.
  clearbody E. peel.
  match goal with Q : half_point_b exps _ false _ _ (slot_iota_p exps) = (_, ?q) |- _ => rename q into qp0 end.
  match goal with Q : half_point_b exps _ false _ _ (slot_iota_m exps) = (_, ?q) |- _ => rename q into qm0 end.
  match goal with Q : kernels_b exps _ modes = (_, ?ks) |- _ => rename ks into kers0 end.
  match goal with Q : half_coefs_b exps _ false modes _ 0 1 0 _ _ _ = (_, ?h) |- _ => rename h into hcm0 end.
  match goal with Q : half_coefs_b exps _ false modes _ 1 2 1 _ _ _ = (_, ?h) |- _ => rename h into hcp0 end.
  match goal with
  | QP : half_point_b exps _ false _ _ (slot_iota_p exps) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_point_ok exps E _ _ _ _ _ _ QP) as [Xp Vp];
      pose proof (sound_extends E _ _ Xp S) as Sqm; pose proof (Vp S) as Vp'
  end.
  match goal with
  | QM : half_point_b exps _ false _ _ (slot_iota_m exps) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_point_ok exps E _ _ _ _ _ _ QM) as [Xm Vm];
      pose proof (sound_extends E _ _ Xm S) as Sks; pose proof (Vm S) as Vm'
  end.
  match goal with
  | Q : kernels_b exps _ modes = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (kernels_values exps E u0 v0 modes _ _ _ Q S Hu Hv) as KV;
      pose proof (sound_extends E _ _ (proj1 (kernels_spec exps modes _ _ _ Q)) S) as Shp
  end.
  assert (HyR01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_R (length modes)) (length modes) 0 j) = Xreal (yR 0%nat j) /\
    xeval E (slot_node exps (base_R (length modes)) (length modes) 1 j) = Xreal (yR 1%nat j))
    by (intros j _ Hj; split; apply HyR; lia).
  assert (HyR12 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_R (length modes)) (length modes) 1 j) = Xreal (yR 1%nat j) /\
    xeval E (slot_node exps (base_R (length modes)) (length modes) 2 j) = Xreal (yR 2%nat j))
    by (intros j _ Hj; split; apply HyR; lia).
  assert (HyZ01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_Z (length modes)) (length modes) 0 j) = Xreal (yZ 0%nat j) /\
    xeval E (slot_node exps (base_Z (length modes)) (length modes) 1 j) = Xreal (yZ 1%nat j))
    by (intros j _ Hj; split; apply HyZ; lia).
  assert (HyZ12 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_Z (length modes)) (length modes) 1 j) = Xreal (yZ 1%nat j) /\
    xeval E (slot_node exps (base_Z (length modes)) (length modes) 2 j) = Xreal (yZ 2%nat j))
    by (intros j _ Hj; split; apply HyZ; lia).
  assert (GL0 : forall j, (j < length modes)%nat ->
    xeval E (slot_node exps (base_L (length modes)) (length modes) 0 j) = Xreal (yL 0%nat j))
    by (intros j Hj; apply HyL; lia).
  assert (GL1 : forall j, (j < length modes)%nat ->
    xeval E (slot_node exps (base_L (length modes)) (length modes) 1 j) = Xreal (yL 1%nat j))
    by (intros j Hj; apply HyL; lia).
  match goal with
  | Q : half_coefs_b exps _ false modes _ 1 2 1 _ _ _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_coefs_ok exps E _ _ _ _ _ _ _ _ _ _ _ Q) as [Xh Vh];
      pose proof (sound_extends E _ _ Xh S) as Shm;
      destruct (Vh S sj sb shp (yR 1%nat) (yR 2%nat) (yZ 1%nat) (yZ 2%nat) Hsj Hsb Hshp Pj Pb Php Djb
                  HyR12 HyZ12) as (CRp & CZp & CLp)
  end.
  match goal with
  | Q : half_coefs_b exps _ false modes _ 0 1 0 _ _ _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_coefs_ok exps E _ _ _ _ _ _ _ _ _ _ _ Q) as [Xh' Vh'];
      destruct (Vh' S sa sj shm (yR 0%nat) (yR 1%nat) (yZ 0%nat) (yZ 1%nat) Hsa Hsj Hshm Pa Pj Phm Daj
                  HyR01 HyZ01) as (CRm & CZm & CLm)
  end.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_R hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hya sa sj shm yR) (hda sa sj shm yR) modes kers0 KV)
    (coef2_terms E (hya sa sj shm yR) (hda sa sj shm yR) modes (hc_R hcm0) CRm)) as ZRm.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Z hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hya sa sj shm yZ) (hda sa sj shm yZ) modes kers0 KV)
    (coef2_terms E (hya sa sj shm yZ) (hda sa sj shm yZ) modes (hc_Z hcm0) CZm)) as ZZm.
  pose proof (zip_ok (kcoefe_ok E 0) kers0 (hc_L hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (fun j _ => yL 0%nat j) (fun _ _ => 0%R) modes kers0 KV)
    (coefe_terms exps E (yL 0%nat) modes (hc_L hcm0) (base_L (length modes)) (length modes) 0 GL0 CLm)) as ZLm.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_R hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hyb sj sb shp yR) (hdb sj sb shp yR) modes kers0 KV)
    (coef2_terms E (hyb sj sb shp yR) (hdb sj sb shp yR) modes (hc_R hcp0) CRp)) as ZRp.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Z hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hyb sj sb shp yZ) (hdb sj sb shp yZ) modes kers0 KV)
    (coef2_terms E (hyb sj sb shp yZ) (hdb sj sb shp yZ) modes (hc_Z hcp0) CZp)) as ZZp.
  pose proof (zip_ok (kcoefe_ok E 0) kers0 (hc_L hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (fun j _ => yL 1%nat j) (fun _ _ => 0%R) modes kers0 KV)
    (coefe_terms exps E (yL 1%nat) modes (hc_L hcp0) (base_L (length modes)) (length modes) 1 GL1 CLp)) as ZLp.
  destruct (Vm' _ _ _ u0 v0 im phip ZRm ZZm ZLm Him Hph Hm) as (Mu & Mv & Mcu & Mcv & Msu & Msv & Mj).
  destruct (Vp' _ _ _ u0 v0 ip phip ZRp ZZp ZLp Hip Hph Hp) as (Qu & Qv & Qcu & Qcv & Qsu & Qsv & Qj).
  node_close.
Qed.

Theorem node_residual_asym (exps : list Z) (prof : pprofile) (modes : list (Z * Z)) (env : env ExtendedR)
    (wm : nat) (sa sj sb shm shp u0 v0 phip im ip pp : R) (yR yZ yL yRa yZa yLa : nat -> nat -> R) :
  let r := residual exps (PConfig true prof RResidual) modes in
  well_formed wm (r_binds r) = true ->
  let E := xextend env (r_binds r) in
  xeval E (slot_s_a exps) = Xreal sa -> xeval E (slot_s_j exps) = Xreal sj -> xeval E (slot_s_b exps) = Xreal sb ->
  xeval E (slot_s_hm exps) = Xreal shm -> xeval E (slot_s_hp exps) = Xreal shp ->
  xeval E (vU exps) = Xreal u0 -> xeval E (vV exps) = Xreal v0 -> xeval E (vPhip exps) = Xreal phip ->
  xeval E (slot_iota_m exps) = Xreal im -> xeval E (slot_iota_p exps) = Xreal ip ->
  xeval E (pprime exps prof) = Xreal pp ->
  (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_R (length modes)) (length modes) row j) = Xreal (yR row j)) ->
  (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_Z (length modes)) (length modes) row j) = Xreal (yZ row j)) ->
  (forall row j, (row < 2)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_L (length modes)) (length modes) row j) = Xreal (yL row j)) ->
  (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_Ra (length modes)) (length modes) row j) = Xreal (yRa row j)) ->
  (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_Za (length modes)) (length modes) row j) = Xreal (yZa row j)) ->
  (forall row j, (row < 2)%nat -> (j < length modes)%nat ->
     xeval E (slot_node exps (base_La (length modes)) (length modes) row j) = Xreal (yLa row j)) ->
  (0 < sa)%R -> (0 < sj)%R -> (0 < sb)%R -> (0 < shm)%R -> (0 < shp)%R ->
  (sj - sa <> 0)%R -> (sb - sj <> 0)%R -> (shp - shm <> 0)%R ->
  let jm := ajet (cterms (hya sa sj shm yR) (hda sa sj shm yR) modes)
                 (cterms (hya sa sj shm yRa) (hda sa sj shm yRa) modes)
                 (cterms (hya sa sj shm yZ) (hda sa sj shm yZ) modes)
                 (cterms (hya sa sj shm yZa) (hda sa sj shm yZa) modes)
                 (cterms (fun j _ => yL 0%nat j) (fun _ _ => 0%R) modes)
                 (cterms (fun j _ => yLa 0%nat j) (fun _ _ => 0%R) modes) 0 u0 v0 im 0 phip 0 in
  let jp := ajet (cterms (hyb sj sb shp yR) (hdb sj sb shp yR) modes)
                 (cterms (hyb sj sb shp yRa) (hdb sj sb shp yRa) modes)
                 (cterms (hyb sj sb shp yZ) (hdb sj sb shp yZ) modes)
                 (cterms (hyb sj sb shp yZa) (hdb sj sb shp yZa) modes)
                 (cterms (fun j _ => yL 1%nat j) (fun _ _ => 0%R) modes)
                 (cterms (fun j _ => yLa 1%nat j) (fun _ _ => 0%R) modes) 0 u0 v0 ip 0 phip 0 in
  f_sqrtg jm <> 0%R -> f_sqrtg jp <> 0%R ->
  xeval E (r_s r) = Xreal (node_rs jm jp (1 / (shp - shm)) (mu0r * pp)) /\
  xeval E (r_u r) = Xreal (cres_u jp) /\ xeval E (r_v r) = Xreal (cres_v jp).
Proof.
  intros r Hwf E Hsa Hsj Hsb Hshm Hshp Hu Hv Hph Him Hip Hpp HyR HyZ HyL HyRa HyZa HyLa
         Pa Pj Pb Phm Php Daj Djb Dh.
  cbv zeta. intros Hm Hp.
  assert (HR : residual exps (PConfig true prof RResidual) modes = r) by reflexivity.
  clearbody r. revert HR.
  unfold residual. cbv beta iota zeta delta [is_radial pc_out pc_lasym pc_prof].
  destruct (residual_pre exps (PConfig true prof RResidual) modes) as [bst kers hcp qp mq mu0pp rs tt] eqn:Hpre.
  unfold residual_tail.
  cbv beta iota zeta delta [pc_out pc_lasym st_b st_kers st_hcp st_qp st_mq st_mu0pp st_rs st_tt].
  repeat step. intros HR. subst r. cbn [r_binds r_s r_u r_v] in *.
  revert Hpre. unfold residual_pre. cbv beta iota zeta delta [pc_out pc_lasym pc_prof].
  repeat step. intros Hpre.
  injection Hpre as E1 E2 E3 E4 E5 E6 E7 E8. subst bst kers hcp qp mq mu0pp rs tt.
  match type of Hwf with well_formed _ (bindings_of ?bl) = true =>
    assert (S : sound E (b_binds bl)) by exact (sound_final env wm bl Hwf) end.
  clearbody E. peel.
  match goal with Q : half_point_b exps _ true _ _ (slot_iota_p exps) = (_, ?q) |- _ => rename q into qp0 end.
  match goal with Q : half_point_b exps _ true _ _ (slot_iota_m exps) = (_, ?q) |- _ => rename q into qm0 end.
  match goal with Q : kernels_b exps _ modes = (_, ?ks) |- _ => rename ks into kers0 end.
  match goal with Q : half_coefs_b exps _ true modes _ 0 1 0 _ _ _ = (_, ?h) |- _ => rename h into hcm0 end.
  match goal with Q : half_coefs_b exps _ true modes _ 1 2 1 _ _ _ = (_, ?h) |- _ => rename h into hcp0 end.
  match goal with
  | QP : half_point_b exps _ true _ _ (slot_iota_p exps) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_point_ok2 exps E _ _ _ _ _ _ QP) as [Xp Vp];
      pose proof (sound_extends E _ _ Xp S) as Sqm; pose proof (Vp S) as Vp'
  end.
  match goal with
  | QM : half_point_b exps _ true _ _ (slot_iota_m exps) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_point_ok2 exps E _ _ _ _ _ _ QM) as [Xm Vm];
      pose proof (sound_extends E _ _ Xm S) as Sks; pose proof (Vm S) as Vm'
  end.
  match goal with
  | Q : kernels_b exps _ modes = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (kernels_values exps E u0 v0 modes _ _ _ Q S Hu Hv) as KV;
      pose proof (sound_extends E _ _ (proj1 (kernels_spec exps modes _ _ _ Q)) S) as Shp
  end.
  assert (Y2 : forall (y : nat -> nat -> R) (base : nat),
    (forall row j, (row < 3)%nat -> (j < length modes)%nat ->
       xeval E (slot_node exps base (length modes) row j) = Xreal (y row j)) ->
    forall ra, (ra < 2)%nat -> forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps base (length modes) ra j) = Xreal (y ra j) /\
    xeval E (slot_node exps base (length modes) (Datatypes.S ra) j) = Xreal (y (Datatypes.S ra) j))
    by (intros y base Hy ra Hra j _ Hj; split; apply Hy; lia).
  assert (GL : forall (y : nat -> nat -> R) (base : nat),
    (forall row j, (row < 2)%nat -> (j < length modes)%nat ->
       xeval E (slot_node exps base (length modes) row j) = Xreal (y row j)) ->
    forall rl, (rl < 2)%nat -> forall j, (j < length modes)%nat ->
    xeval E (slot_node exps base (length modes) rl j) = Xreal (y rl j))
    by (intros y base Hy rl Hrl j Hj; apply Hy; lia).
  match goal with
  | Q : half_coefs_b exps _ true modes _ 1 2 1 _ _ _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_coefs_ok2 exps E _ _ _ _ _ _ _ _ _ _ _ Q) as [Xh Vh];
      pose proof (sound_extends E _ _ Xh S) as Shm;
      destruct (Vh S sj sb shp (yR 1%nat) (yR 2%nat) (yZ 1%nat) (yZ 2%nat) (yRa 1%nat) (yRa 2%nat)
                  (yZa 1%nat) (yZa 2%nat) Hsj Hsb Hshp Pj Pb Php Djb
                  (Y2 yR _ HyR 1%nat ltac:(lia)) (Y2 yZ _ HyZ 1%nat ltac:(lia)) (Y2 yRa _ HyRa 1%nat ltac:(lia))
                  (Y2 yZa _ HyZa 1%nat ltac:(lia))) as (CRp & CZp & CLp & CAp & CBp & CMp)
  end.
  match goal with
  | Q : half_coefs_b exps _ true modes _ 0 1 0 _ _ _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      destruct (half_coefs_ok2 exps E _ _ _ _ _ _ _ _ _ _ _ Q) as [Xh' Vh'];
      destruct (Vh' S sa sj shm (yR 0%nat) (yR 1%nat) (yZ 0%nat) (yZ 1%nat) (yRa 0%nat) (yRa 1%nat)
                  (yZa 0%nat) (yZa 1%nat) Hsa Hsj Hshm Pa Pj Phm Daj
                  (Y2 yR _ HyR 0%nat ltac:(lia)) (Y2 yZ _ HyZ 0%nat ltac:(lia)) (Y2 yRa _ HyRa 0%nat ltac:(lia))
                  (Y2 yZa _ HyZa 0%nat ltac:(lia))) as (CRm & CZm & CLm & CAm & CBm & CMm)
  end.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_R hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hya sa sj shm yR) (hda sa sj shm yR) modes kers0 KV)
    (coef2_terms E (hya sa sj shm yR) (hda sa sj shm yR) modes (hc_R hcm0) CRm)) as ZRm.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Ra hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hya sa sj shm yRa) (hda sa sj shm yRa) modes kers0 KV)
    (coef2_terms E (hya sa sj shm yRa) (hda sa sj shm yRa) modes (hc_Ra hcm0) CAm)) as ZAm.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Z hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hya sa sj shm yZ) (hda sa sj shm yZ) modes kers0 KV)
    (coef2_terms E (hya sa sj shm yZ) (hda sa sj shm yZ) modes (hc_Z hcm0) CZm)) as ZZm.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Za hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hya sa sj shm yZa) (hda sa sj shm yZa) modes kers0 KV)
    (coef2_terms E (hya sa sj shm yZa) (hda sa sj shm yZa) modes (hc_Za hcm0) CBm)) as ZBm.
  pose proof (zip_ok (kcoefe_ok E 0) kers0 (hc_L hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (fun j _ => yL 0%nat j) (fun _ _ => 0%R) modes kers0 KV)
    (coefe_terms exps E (yL 0%nat) modes (hc_L hcm0) (base_L (length modes)) (length modes) 0
       (GL yL _ HyL 0%nat ltac:(lia)) CLm)) as ZLm.
  pose proof (zip_ok (kcoefe_ok E 0) kers0 (hc_La hcm0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (fun j _ => yLa 0%nat j) (fun _ _ => 0%R) modes kers0 KV)
    (coefe_terms exps E (yLa 0%nat) modes (hc_La hcm0) (base_La (length modes)) (length modes) 0
       (GL yLa _ HyLa 0%nat ltac:(lia)) CMm)) as ZMm.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_R hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hyb sj sb shp yR) (hdb sj sb shp yR) modes kers0 KV)
    (coef2_terms E (hyb sj sb shp yR) (hdb sj sb shp yR) modes (hc_R hcp0) CRp)) as ZRp.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Ra hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hyb sj sb shp yRa) (hdb sj sb shp yRa) modes kers0 KV)
    (coef2_terms E (hyb sj sb shp yRa) (hdb sj sb shp yRa) modes (hc_Ra hcp0) CAp)) as ZAp.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Z hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hyb sj sb shp yZ) (hdb sj sb shp yZ) modes kers0 KV)
    (coef2_terms E (hyb sj sb shp yZ) (hdb sj sb shp yZ) modes (hc_Z hcp0) CZp)) as ZZp.
  pose proof (zip_ok (kcoef2_ok E 0) kers0 (hc_Za hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (hyb sj sb shp yZa) (hdb sj sb shp yZa) modes kers0 KV)
    (coef2_terms E (hyb sj sb shp yZa) (hdb sj sb shp yZa) modes (hc_Za hcp0) CBp)) as ZBp.
  pose proof (zip_ok (kcoefe_ok E 0) kers0 (hc_L hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (fun j _ => yL 1%nat j) (fun _ _ => 0%R) modes kers0 KV)
    (coefe_terms exps E (yL 1%nat) modes (hc_L hcp0) (base_L (length modes)) (length modes) 1
       (GL yL _ HyL 1%nat ltac:(lia)) CLp)) as ZLp.
  pose proof (zip_ok (kcoefe_ok E 0) kers0 (hc_La hcp0) _ (kker_ok E u0 v0)
    (kers_cterms E u0 v0 (fun j _ => yLa 1%nat j) (fun _ _ => 0%R) modes kers0 KV)
    (coefe_terms exps E (yLa 1%nat) modes (hc_La hcp0) (base_La (length modes)) (length modes) 1
       (GL yLa _ HyLa 1%nat ltac:(lia)) CMp)) as ZMp.
  destruct (Vm' _ _ _ _ _ _ u0 v0 im phip ZRm ZAm ZZm ZBm ZLm ZMm Him Hph Hm)
    as (Mu & Mv & Mcu & Mcv & Msu & Msv & Mj).
  destruct (Vp' _ _ _ _ _ _ u0 v0 ip phip ZRp ZAp ZZp ZBp ZLp ZMp Hip Hph Hp)
    as (Qu & Qv & Qcu & Qcv & Qsu & Qsv & Qj).
  node_close.
Qed.

(** * The continuum residual of a state without stellarator symmetry *)

Theorem fp_residual_asym (exps : list Z) (prof : pprofile) (modes : list (Z * Z)) (b0 : builder)
    (env : env ExtendedR) (wm : nat) (bf : builder) (rr : residual3)
    (sa sj sb shm shp s0 u0 v0 phip im ip pp : R) (yR yZ yL yRa yZa yLa : nat -> nat -> R) :
  let K := length modes in
  full_point_b exps b0 true modes K prof RRadial = (bf, rr) ->
  well_formed wm (r_binds rr) = true ->
  let E := xextend env (r_binds rr) in
  xeval E (slot_s_a exps) = Xreal sa -> xeval E (slot_s_j exps) = Xreal sj -> xeval E (slot_s_b exps) = Xreal sb ->
  xeval E (slot_s_hm exps) = Xreal shm -> xeval E (slot_s_hp exps) = Xreal shp ->
  xeval E (vS exps) = Xreal s0 -> xeval E (vU exps) = Xreal u0 -> xeval E (vV exps) = Xreal v0 ->
  xeval E (vPhip exps) = Xreal phip ->
  xeval E (slot_iota_m exps) = Xreal im -> xeval E (slot_iota_p exps) = Xreal ip ->
  xeval E (pprime exps prof) = Xreal pp ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_R K) K row j) = Xreal (yR row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Z K) K row j) = Xreal (yZ row j)) ->
  (forall row j, (row < 2)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_L K) K row j) = Xreal (yL row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Ra K) K row j) = Xreal (yRa row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Za K) K row j) = Xreal (yZa row j)) ->
  (forall row j, (row < 2)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_La K) K row j) = Xreal (yLa row j)) ->
  (0 < sa)%R -> (0 < sj)%R -> (0 < sb)%R -> (0 < shm)%R -> (0 < shp)%R -> (0 < s0)%R ->
  (sj - sa <> 0)%R -> (sb - sj <> 0)%R -> (shp - shm <> 0)%R ->
  let tR := rterms sa sj sb shm shp yR modes in
  let tZ := rterms sa sj sb shm shp yZ modes in
  let tL := lterms shm shp yL modes in
  let tRa := rterms sa sj sb shm shp yRa modes in
  let tZa := rterms sa sj sb shm shp yZa modes in
  let tLa := lterms shm shp yLa modes in
  sqrtg (fun s u v => Series.S0 true tR s u v + Series.S0 false tRa s u v)%R
        (fun s u v => S_s true tR s u v + S_s false tRa s u v)%R
        (fun s u v => S_u true tR s u v + S_u false tRa s u v)%R
        (fun s u v => S_s false tZ s u v + S_s true tZa s u v)%R
        (fun s u v => S_u false tZ s u v + S_u true tZa s u v)%R s0 u0 v0 <> 0%R ->
  let J := ajet tR tRa tZ tZa tL tLa s0 u0 v0 (iotaf shm shp im ip s0) ((ip - im) * (1 / (shp - shm)))%R phip
                (mu0r * pp)%R in
  xeval E (r_s rr) = Xreal (cres_s J) /\ xeval E (r_u rr) = Xreal (cres_u J) /\
  xeval E (r_v rr) = Xreal (cres_v J).
Proof.
  intros K HFP Hwf E Hsa Hsj Hsb Hshm Hshp Hs Hu Hv Hph Him Hip Hpp HyR HyZ HyL HyRa HyZa HyLa
         Pa Pj Pb Phm Php Ps Daj Djb Dh tR tZ tL tRa tZa tLa Hsg J.
  revert HFP. unfold full_point_b. cbv beta iota zeta delta [is_axis].
  repeat step.
  repeat match goal with Q : (match _ with _ => _ end) = _ |- _ => stepH Q end.
  repeat match goal with Q : (_, _) = (_, _) |- _ => injection Q as <- <- end.
  intros HFP. injection HFP as <- <-. cbn [r_binds r_s r_u r_v fst snd] in *.
  match type of Hwf with well_formed _ (bindings_of ?bl) = true =>
    assert (S : sound E (b_binds bl)) by exact (sound_final env wm bl Hwf) end.
  clearbody E. peel.
  (* every stage's bindings hold their values *)
  repeat match goal with
  | S : sound E (b_binds ?b'), Q : flambda_partials_b ?b ?p = (?b', ?q) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (flambda_ok E b p b' q Q)) S) end
  | S : sound E (b_binds ?b'), Q : fpartials_b ?b ?p = (?b', ?q) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (fpartials_ok E b p b' q Q)) S) end
  | S : sound E (b_binds ?b'), Q : radcoefs_b _ ?b _ _ _ _ _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (radcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : hermcoefs_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (hermcoefs_spec _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : rad_scalars_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (rad_scalars_ok E _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : herm_scalars_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (herm_scalars_ok E _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : kernels_b _ ?b _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (kernels_spec _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : halfcoefs_b _ ?b _ _ _ _ _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (halfcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : half_scalars_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (half_scalars_ok E _ _ _ _ _ _ Q)) S) end
  end.
  (* the half-point scalars and coefficients *)
  match goal with
  | Q : half_scalars_b _ (slot_s_a exps) (slot_s_j exps) (slot_s_hm exps) = (?b', _),
    S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (half_scalars_ok E _ _ _ _ _ _ Q)) S sa sj shm Hsa Hsj Hshm Pa Pj Phm Daj)
        as (Hm1 & Hm2 & Hm3 & Hm4 & Hm5 & Hm6)
  end.
  match goal with
  | Q : half_scalars_b _ (slot_s_j exps) (slot_s_b exps) (slot_s_hp exps) = (?b', _),
    S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (half_scalars_ok E _ _ _ _ _ _ Q)) S sj sb shp Hsj Hsb Hshp Pj Pb Php Djb)
        as (Hp1 & Hp2 & Hp3 & Hp4 & Hp5 & Hp6)
  end.
  assert (Y01 : forall (y : nat -> nat -> R) (base : nat),
    (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps base K row j) = Xreal (y row j)) ->
    forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps base K 0 j) = Xreal (y 0%nat j) /\
    xeval E (slot_node exps base K 1 j) = Xreal (y 1%nat j))
    by (intros y base Hy j _ Hj; split; apply Hy; unfold K; lia).
  assert (Y12 : forall (y : nat -> nat -> R) (base : nat),
    (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps base K row j) = Xreal (y row j)) ->
    forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps base K 1 j) = Xreal (y 1%nat j) /\
    xeval E (slot_node exps base K 2 j) = Xreal (y 2%nat j))
    by (intros y base Hy j _ Hj; split; apply Hy; unfold K; lia).
  assert (HyL01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_L K) K 0 j) = Xreal (yL 0%nat j) /\
    xeval E (slot_node exps (base_L K) K 1 j) = Xreal (yL 1%nat j)) by (intros j _ Hj; split; apply HyL; unfold K; lia).
  assert (HyLa01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_La K) K 0 j) = Xreal (yLa 0%nat j) /\
    xeval E (slot_node exps (base_La K) K 1 j) = Xreal (yLa 1%nat j)) by (intros j _ Hj; split; apply HyLa; unfold K; lia).
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_R K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_R K) K 0 1 sa sj shm (yR 0%nat) (yR 1%nat)
                    Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 modes 0 _ b' cs Q (Y01 yR _ HyR) S) as CRm
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_R K) K 1 2 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_R K) K 1 2 sj sb shp (yR 1%nat) (yR 2%nat)
                    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 modes 0 _ b' cs Q (Y12 yR _ HyR) S) as CRp
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Z K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Z K) K 0 1 sa sj shm (yZ 0%nat) (yZ 1%nat)
                    Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 modes 0 _ b' cs Q (Y01 yZ _ HyZ) S) as CZm
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Z K) K 1 2 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Z K) K 1 2 sj sb shp (yZ 1%nat) (yZ 2%nat)
                    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 modes 0 _ b' cs Q (Y12 yZ _ HyZ) S) as CZp
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Ra K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Ra K) K 0 1 sa sj shm (yRa 0%nat) (yRa 1%nat)
                    Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 modes 0 _ b' cs Q (Y01 yRa _ HyRa) S) as CAm
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Ra K) K 1 2 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Ra K) K 1 2 sj sb shp (yRa 1%nat) (yRa 2%nat)
                    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 modes 0 _ b' cs Q (Y12 yRa _ HyRa) S) as CAp
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Za K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Za K) K 0 1 sa sj shm (yZa 0%nat) (yZa 1%nat)
                    Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 modes 0 _ b' cs Q (Y01 yZa _ HyZa) S) as CBm
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Za K) K 1 2 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Za K) K 1 2 sj sb shp (yZa 1%nat) (yZa 2%nat)
                    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 modes 0 _ b' cs Q (Y12 yZa _ HyZa) S) as CBp
  end.
  (* the kernels and the radial scalars *)
  match goal with
  | Q : kernels_b exps _ modes = (?b', ?kers), S : sound E (b_binds ?b') |- _ =>
      pose proof (kernels_values exps E u0 v0 modes _ b' kers Q S Hu Hv) as KV
  end.
  match goal with
  | Q : herm_scalars_b _ (slot_s_hm exps) (slot_s_hp exps) (vS exps) = (?b', _), S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (herm_scalars_ok E _ _ _ _ _ _ Q)) S shm shp s0 Hshm Hshp Hs Dh)
        as (HH1 & HH2 & HH3 & HH4 & HH5 & HH6 & HH7 & HH8 & HH9)
  end.
  match goal with
  | Q : rad_scalars_b _ (slot_s_hm exps) (slot_s_hp exps) (vS exps) = (?b', _), S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (rad_scalars_ok E _ _ _ _ _ _ Q)) S shm shp s0 Hshm Hshp Hs Phm Php Ps Dh)
        as (RS1 & RS2 & RS3 & RS4 & RS5 & RS6)
  end.
  (* the coefficients at the radius *)
  match goal with
  | Q1 : halfcoefs_b exps _ _ (base_R K) K 0 1 modes 0 = (_, ?ca),
    Q2 : halfcoefs_b exps _ _ (base_R K) K 1 2 modes 0 = (_, ?cb),
    A : hermcoefs_b _ ?hm ?ca ?cb = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (herm_terms E b' hm shm (shp - shm) s0 (hya sa sj shm yR) (hda sa sj shm yR)
                    (hyb sj sb shp yR) (hdb sj sb shp yR) S Dh HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9
                    _ ca cb cs CRm CRp (proj2 (hermcoefs_spec _ _ _ _ _ _ A))) as TR
  end.
  match goal with
  | Q1 : halfcoefs_b exps _ _ (base_Z K) K 0 1 modes 0 = (_, ?ca),
    Q2 : halfcoefs_b exps _ _ (base_Z K) K 1 2 modes 0 = (_, ?cb),
    A : hermcoefs_b _ ?hm ?ca ?cb = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (herm_terms E b' hm shm (shp - shm) s0 (hya sa sj shm yZ) (hda sa sj shm yZ)
                    (hyb sj sb shp yZ) (hdb sj sb shp yZ) S Dh HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9
                    _ ca cb cs CZm CZp (proj2 (hermcoefs_spec _ _ _ _ _ _ A))) as TZ
  end.
  match goal with
  | Q1 : halfcoefs_b exps _ _ (base_Ra K) K 0 1 modes 0 = (_, ?ca),
    Q2 : halfcoefs_b exps _ _ (base_Ra K) K 1 2 modes 0 = (_, ?cb),
    A : hermcoefs_b _ ?hm ?ca ?cb = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (herm_terms E b' hm shm (shp - shm) s0 (hya sa sj shm yRa) (hda sa sj shm yRa)
                    (hyb sj sb shp yRa) (hdb sj sb shp yRa) S Dh HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9
                    _ ca cb cs CAm CAp (proj2 (hermcoefs_spec _ _ _ _ _ _ A))) as TA
  end.
  match goal with
  | Q1 : halfcoefs_b exps _ _ (base_Za K) K 0 1 modes 0 = (_, ?ca),
    Q2 : halfcoefs_b exps _ _ (base_Za K) K 1 2 modes 0 = (_, ?cb),
    A : hermcoefs_b _ ?hm ?ca ?cb = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (herm_terms E b' hm shm (shp - shm) s0 (hya sa sj shm yZa) (hda sa sj shm yZa)
                    (hyb sj sb shp yZa) (hdb sj sb shp yZa) S Dh HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9
                    _ ca cb cs CBm CBp (proj2 (hermcoefs_spec _ _ _ _ _ _ A))) as TB
  end.
  match goal with
  | Q : radcoefs_b exps _ ?rl (base_L K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (rad_terms exps E b' rl shm shp s0 yL (base_L K) K 0 1 S RS1 RS2 RS3 RS4 RS5 RS6 modes 0 cs
                    HyL01 (proj2 (radcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q))) as TL
  end.
  match goal with
  | Q : radcoefs_b exps _ ?rl (base_La K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (rad_terms exps E b' rl shm shp s0 yLa (base_La K) K 0 1 S RS1 RS2 RS3 RS4 RS5 RS6 modes 0 cs
                    HyLa01 (proj2 (radcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q))) as TM
  end.
  (* the series and their derivatives at the point *)
  match goal with
  | Q : fpartials_b _ (fadd (fassemble ?kers ?cs true) (fassemble _ ?csa false)) = (?b', ?q),
    S : sound E (b_binds ?b') |- _ =>
      pose proof (fadd_values E true false kers cs csa tR tRa s0 u0 v0 q
        (zip_ok (kcoef_ok E s0) kers cs tR (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TR)
        (zip_ok (kcoef_ok E s0) kers csa tRa (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TA)
        (proj2 (fpartials_ok E _ _ _ _ Q) S)) as WR
  end.
  match goal with
  | Q : fpartials_b _ (fadd (fassemble ?kers ?cs false) (fassemble _ ?csa true)) = (?b', ?q),
    S : sound E (b_binds ?b') |- _ =>
      pose proof (fadd_values E false true kers cs csa tZ tZa s0 u0 v0 q
        (zip_ok (kcoef_ok E s0) kers cs tZ (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TZ)
        (zip_ok (kcoef_ok E s0) kers csa tZa (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TB)
        (proj2 (fpartials_ok E _ _ _ _ Q) S)) as WZ
  end.
  match goal with
  | Q : flambda_partials_b _ (fladd (flambda_terms ?kers ?cs false) (flambda_terms _ ?csa true)) = (?b', ?q),
    S : sound E (b_binds ?b') |- _ =>
      pose proof (fladd_values E false true kers cs csa tL tLa s0 u0 v0 q
        (zip_ok (kcoefl_ok E s0) kers cs tL (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TL)
        (zip_ok (kcoefl_ok E s0) kers csa tLa (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TM)
        (proj2 (flambda_ok E _ _ _ _ Q) S)) as WL
  end.
  destruct WR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10).
  destruct WZ as (W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20).
  destruct WL as (W21 & W22 & W23 & W24 & W25 & W26 & W27).
  (* the formula stage *)
  unfold sqrtg in Hsg. cbv beta in Hsg.
  unfold Physics.e1, Physics.esq, Physics.zmul, Physics.mu0, Physics.e4, Physics.r_u_e, Physics.r_v_e in *.
  splits; xcalc; xclose;
    unfold J, ajet, iotaf, mu0r, cres_s, cres_u, cres_v, f_mu0Js, f_B_u_s, f_B_v_s, f_B_s_u, f_B_s_v, f_B_u_v,
      f_B_v_u, f_dcov, f_guu, f_guv, f_gvv, f_gsu, f_gsv, f_guu_s, f_guv_s, f_gvv_s, f_gsu_u, f_gsu_v, f_gsv_u,
      f_gsv_v, f_guu_v, f_guv_u, f_guv_v, f_gvv_u, f_Bu, f_Bv, f_Bu_s, f_Bv_s, f_Bu_u, f_Bv_u, f_Bu_v, f_Bv_v,
      f_dB, f_g2, f_bu_num, f_bv_num, f_g_s, f_g_u, f_g_v, f_tau_s, f_tau_u, f_tau_v, f_sqrtg, f_tau;
    cbn [jR jRs jRu jRv jRss jRsu jRsv jRuu jRuv jRvv jZs jZu jZv jZss jZsu jZsv jZuu jZuv jZvv
         jLu jLv jLsu jLsv jLuu jLuv jLvv jiota jiotap jphip jmu0pp];
    reflexivity.
Qed.

Theorem continuum_force_asym (exps : list Z) (prof : pprofile) (modes : list (Z * Z)) (env : env ExtendedR)
    (wm : nat) (sa sj sb shm shp s0 u0 v0 phip im ip pp : R) (yR yZ yL yRa yZa yLa : nat -> nat -> R)
    (p : R -> R) (G1 G2 G3 P : R * R * R -> R) (a11 a12 a13 a21 a22 a23 a31 a32 a33 q1 q2 q3 : R) :
  let K := length modes in
  let r := residual exps (PConfig true prof RRadial) modes in
  well_formed wm (r_binds r) = true ->
  let E := xextend env (r_binds r) in
  xeval E (slot_s_a exps) = Xreal sa -> xeval E (slot_s_j exps) = Xreal sj -> xeval E (slot_s_b exps) = Xreal sb ->
  xeval E (slot_s_hm exps) = Xreal shm -> xeval E (slot_s_hp exps) = Xreal shp ->
  xeval E (vS exps) = Xreal s0 -> xeval E (vU exps) = Xreal u0 -> xeval E (vV exps) = Xreal v0 ->
  xeval E (vPhip exps) = Xreal phip ->
  xeval E (slot_iota_m exps) = Xreal im -> xeval E (slot_iota_p exps) = Xreal ip ->
  xeval E (pprime exps prof) = Xreal pp ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_R K) K row j) = Xreal (yR row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Z K) K row j) = Xreal (yZ row j)) ->
  (forall row j, (row < 2)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_L K) K row j) = Xreal (yL row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Ra K) K row j) = Xreal (yRa row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Za K) K row j) = Xreal (yZa row j)) ->
  (forall row j, (row < 2)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_La K) K row j) = Xreal (yLa row j)) ->
  (0 < sa)%R -> (0 < sj)%R -> (0 < sb)%R -> (0 < shm)%R -> (0 < shp)%R -> (0 < s0)%R ->
  (sj - sa <> 0)%R -> (sb - sj <> 0)%R -> (shp - shm <> 0)%R ->
  let tR := rterms sa sj sb shm shp yR modes in
  let tZ := rterms sa sj sb shm shp yZ modes in
  let tL := lterms shm shp yL modes in
  let tRa := rterms sa sj sb shm shp yRa modes in
  let tZa := rterms sa sj sb shm shp yZa modes in
  let tLa := lterms shm shp yLa modes in
  let FR := fun s u v => (Series.S0 true tR s u v + Series.S0 false tRa s u v)%R in
  let FRs := fun s u v => (S_s true tR s u v + S_s false tRa s u v)%R in
  let FRu := fun s u v => (S_u true tR s u v + S_u false tRa s u v)%R in
  let FRv := fun s u v => (S_v true tR s u v + S_v false tRa s u v)%R in
  let FZ := fun s u v => (Series.S0 false tZ s u v + Series.S0 true tZa s u v)%R in
  let FZs := fun s u v => (S_s false tZ s u v + S_s true tZa s u v)%R in
  let FZu := fun s u v => (S_u false tZ s u v + S_u true tZa s u v)%R in
  let FZv := fun s u v => (S_v false tZ s u v + S_v true tZa s u v)%R in
  let FLu := fun s u v => (S_u false tL s u v + S_u true tLa s u v)%R in
  let FLv := fun s u v => (S_v false tL s u v + S_v true tLa s u v)%R in
  let iota := iotaf shm shp im ip in
  sqrtg FR FRs FRu FZs FZu s0 u0 v0 <> 0%R ->
  is_derive p s0 pp ->
  filterdiff G1 (locally (emb FR FZ s0 u0 v0)) (lin3 a11 a12 a13) ->
  filterdiff G2 (locally (emb FR FZ s0 u0 v0)) (lin3 a21 a22 a23) ->
  filterdiff G3 (locally (emb FR FZ s0 u0 v0)) (lin3 a31 a32 a33) ->
  filterdiff P (locally (emb FR FZ s0 u0 v0)) (lin3 q1 q2 q3) ->
  represents G1 G2 G3 P (fun t => emb FR FZ t u0 v0)
    (fun t => Bc1 FR FRs FRu FRv FZs FZu FLu FLv iota phip t u0 v0)
    (fun t => Bc2 FR FRs FRu FRv FZs FZu FLu FLv iota phip t u0 v0)
    (fun t => Bc3 FR FRs FRu FZs FZu FZv FLu FLv iota phip t u0 v0) p s0 ->
  represents G1 G2 G3 P (fun t => emb FR FZ s0 t v0)
    (fun t => Bc1 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 t v0)
    (fun t => Bc2 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 t v0)
    (fun t => Bc3 FR FRs FRu FZs FZu FZv FLu FLv iota phip s0 t v0) (fun _ => p s0) u0 ->
  represents G1 G2 G3 P (fun t => emb FR FZ s0 u0 t)
    (fun t => Bc1 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 u0 t)
    (fun t => Bc2 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 u0 t)
    (fun t => Bc3 FR FRs FRu FZs FZu FZv FLu FLv iota phip s0 u0 t) (fun _ => p s0) v0 ->
  let G01 := G1 (emb FR FZ s0 u0 v0) in let G02 := G2 (emb FR FZ s0 u0 v0) in
  let G03 := G3 (emb FR FZ s0 u0 v0) in
  let w1 := (a32 - a23)%R in let w2 := (a13 - a31)%R in let w3 := (a21 - a12)%R in
  let F1 := ((w2 * G03 - w3 * G02) - mu0r * q1)%R in
  let F2 := ((w3 * G01 - w1 * G03) - mu0r * q2)%R in
  let F3 := ((w1 * G02 - w2 * G01) - mu0r * q3)%R in
  let c := cos v0 in let sn := sin v0 in
  xeval E (r_s r) = Xreal (dot3 F1 F2 F3 (FRs s0 u0 v0 * c) (FRs s0 u0 v0 * sn) (FZs s0 u0 v0))%R /\
  xeval E (r_u r) = Xreal (dot3 F1 F2 F3 (FRu s0 u0 v0 * c) (FRu s0 u0 v0 * sn) (FZu s0 u0 v0))%R /\
  xeval E (r_v r) = Xreal (dot3 F1 F2 F3 (FRv s0 u0 v0 * c - FR s0 u0 v0 * sn) (FRv s0 u0 v0 * sn + FR s0 u0 v0 * c)
                             (FZv s0 u0 v0))%R.
Proof.
  intros K r Hwf E Hsa Hsj Hsb Hshm Hshp Hs Hu Hv Hph Him Hip Hpp HyR HyZ HyL HyRa HyZa HyLa
         Pa Pj Pb Phm Php Ps Daj Djb Dh
         tR tZ tL tRa tZa tLa FR FRs FRu FRv FZ FZs FZu FZv FLu FLv iota Hsg Hp HG1 HG2 HG3 HP Hsl Hul Hvl
         G01 G02 G03 w1 w2 w3 F1 F2 F3 c sn.
  set (FP := full_point_b exps (Builder (base_scratch_of true RRadial K) []) true modes K prof RRadial).
  assert (HFP : FP = (fst FP, r)) by (change r with (snd FP); apply surjective_pairing).
  pose proof (fp_residual_asym exps prof modes (Builder (base_scratch_of true RRadial K) []) env wm (fst FP) r
                sa sj sb shm shp s0 u0 v0 phip im ip pp yR yZ yL yRa yZa yLa HFP Hwf
                Hsa Hsj Hsb Hshm Hshp Hs Hu Hv Hph Him Hip Hpp HyR HyZ HyL HyRa HyZa HyLa
                Pa Pj Pb Phm Php Ps Daj Djb Dh Hsg) as (Rs & Ru & Rv).
  (* the reconstruction's derivatives along the three coordinate lines *)
  assert (C1R := rterms_d1 sa sj sb shm shp yR modes s0 Dh).
  assert (C2R := rterms_d2 sa sj sb shm shp yR modes s0 Dh).
  assert (C1Z := rterms_d1 sa sj sb shm shp yZ modes s0 Dh).
  assert (C2Z := rterms_d2 sa sj sb shm shp yZ modes s0 Dh).
  assert (C1A := rterms_d1 sa sj sb shm shp yRa modes s0 Dh).
  assert (C2A := rterms_d2 sa sj sb shm shp yRa modes s0 Dh).
  assert (C1B := rterms_d1 sa sj sb shm shp yZa modes s0 Dh).
  assert (C2B := rterms_d2 sa sj sb shm shp yZa modes s0 Dh).
  assert (C1L := lterms_d1 shm shp yL modes s0 Ps).
  assert (C1M := lterms_d1 shm shp yLa modes s0 Ps).
  destruct (table_s true tR s0 C1R u0 v0) as (TRs1 & TRs2 & TRs3).
  destruct (table_s false tRa s0 C1A u0 v0) as (TAs1 & TAs2 & TAs3).
  destruct (table_s false tZ s0 C1Z u0 v0) as (TZs1 & TZs2 & TZs3).
  destruct (table_s true tZa s0 C1B u0 v0) as (TBs1 & TBs2 & TBs3).
  destruct (table_s false tL s0 C1L u0 v0) as (TLs1 & TLs2 & TLs3).
  destruct (table_s true tLa s0 C1M u0 v0) as (TMs1 & TMs2 & TMs3).
  pose proof (table_ss true tR s0 C2R u0 v0) as TRss.
  pose proof (table_ss false tRa s0 C2A u0 v0) as TAss.
  pose proof (table_ss false tZ s0 C2Z u0 v0) as TZss.
  pose proof (table_ss true tZa s0 C2B u0 v0) as TBss.
  destruct (table_u true tR s0 u0 v0) as (TRu1 & TRu2 & TRu3 & TRu4).
  destruct (table_u false tRa s0 u0 v0) as (TAu1 & TAu2 & TAu3 & TAu4).
  destruct (table_u false tZ s0 u0 v0) as (TZu1 & TZu2 & TZu3 & TZu4).
  destruct (table_u true tZa s0 u0 v0) as (TBu1 & TBu2 & TBu3 & TBu4).
  destruct (table_u false tL s0 u0 v0) as (TLu1 & TLu2 & TLu3 & TLu4).
  destruct (table_u true tLa s0 u0 v0) as (TMu1 & TMu2 & TMu3 & TMu4).
  destruct (table_v true tR s0 u0 v0) as (TRv1 & TRv2 & TRv3 & TRv4).
  destruct (table_v false tRa s0 u0 v0) as (TAv1 & TAv2 & TAv3 & TAv4).
  destruct (table_v false tZ s0 u0 v0) as (TZv1 & TZv2 & TZv3 & TZv4).
  destruct (table_v true tZa s0 u0 v0) as (TBv1 & TBv2 & TBv3 & TBv4).
  destruct (table_v false tL s0 u0 v0) as (TLv1 & TLv2 & TLv3 & TLv4).
  destruct (table_v true tLa s0 u0 v0) as (TMv1 & TMv2 & TMv3 & TMv4).
  destruct (force_law FR FZ FRs FRu FRv FZs FZu FZv FLu FLv iota p phip mu0r s0 u0 v0
              (S_ss true tR s0 u0 v0 + S_ss false tRa s0 u0 v0)%R (S_su true tR s0 u0 v0 + S_su false tRa s0 u0 v0)%R
              (S_sv true tR s0 u0 v0 + S_sv false tRa s0 u0 v0)%R (S_uu true tR s0 u0 v0 + S_uu false tRa s0 u0 v0)%R
              (S_uv true tR s0 u0 v0 + S_uv false tRa s0 u0 v0)%R (S_vv true tR s0 u0 v0 + S_vv false tRa s0 u0 v0)%R
              (S_ss false tZ s0 u0 v0 + S_ss true tZa s0 u0 v0)%R (S_su false tZ s0 u0 v0 + S_su true tZa s0 u0 v0)%R
              (S_sv false tZ s0 u0 v0 + S_sv true tZa s0 u0 v0)%R (S_uu false tZ s0 u0 v0 + S_uu true tZa s0 u0 v0)%R
              (S_uv false tZ s0 u0 v0 + S_uv true tZa s0 u0 v0)%R (S_vv false tZ s0 u0 v0 + S_vv true tZa s0 u0 v0)%R
              (S_su false tL s0 u0 v0 + S_su true tLa s0 u0 v0)%R (S_sv false tL s0 u0 v0 + S_sv true tLa s0 u0 v0)%R
              (S_uu false tL s0 u0 v0 + S_uu true tLa s0 u0 v0)%R (S_uv false tL s0 u0 v0 + S_uv true tLa s0 u0 v0)%R
              (S_vv false tL s0 u0 v0 + S_vv true tLa s0 u0 v0)%R
              ((ip - im) * (1 / (shp - shm)))%R pp
              (conj (D_add _ _ _ _ _ TRs1 TAs1) (conj (D_add _ _ _ _ _ TRu1 TAu1) (D_add _ _ _ _ _ TRv1 TAv1)))
              (conj (D_add _ _ _ _ _ TRss TAss) (conj (D_add _ _ _ _ _ TRu2 TAu2) (D_add _ _ _ _ _ TRv2 TAv2)))
              (conj (D_add _ _ _ _ _ TRs2 TAs2) (conj (D_add _ _ _ _ _ TRu3 TAu3) (D_add _ _ _ _ _ TRv3 TAv3)))
              (conj (D_add _ _ _ _ _ TRs3 TAs3) (conj (D_add _ _ _ _ _ TRu4 TAu4) (D_add _ _ _ _ _ TRv4 TAv4)))
              (conj (D_add _ _ _ _ _ TZs1 TBs1) (conj (D_add _ _ _ _ _ TZu1 TBu1) (D_add _ _ _ _ _ TZv1 TBv1)))
              (conj (D_add _ _ _ _ _ TZss TBss) (conj (D_add _ _ _ _ _ TZu2 TBu2) (D_add _ _ _ _ _ TZv2 TBv2)))
              (conj (D_add _ _ _ _ _ TZs2 TBs2) (conj (D_add _ _ _ _ _ TZu3 TBu3) (D_add _ _ _ _ _ TZv3 TBv3)))
              (conj (D_add _ _ _ _ _ TZs3 TBs3) (conj (D_add _ _ _ _ _ TZu4 TBu4) (D_add _ _ _ _ _ TZv4 TBv4)))
              (conj (D_add _ _ _ _ _ TLs2 TMs2) (conj (D_add _ _ _ _ _ TLu3 TMu3) (D_add _ _ _ _ _ TLv3 TMv3)))
              (conj (D_add _ _ _ _ _ TLs3 TMs3) (conj (D_add _ _ _ _ _ TLu4 TMu4) (D_add _ _ _ _ _ TLv4 TMv4)))
              (iotaf_d shm shp im ip s0) Hp Hsg G1 G2 G3 P a11 a12 a13 a21 a22 a23 a31 a32 a33 q1 q2 q3
              HG1 HG2 HG3 HP Hsl Hul Hvl) as (Fs & Fu & Fv).
  refine (conj _ (conj _ _)).
  - etransitivity; [exact Rs |]. f_equal. symmetry. exact Fs.
  - etransitivity; [exact Ru |]. f_equal. symmetry. exact Fu.
  - etransitivity; [exact Rv |]. f_equal. symmetry. exact Fv.
Qed.
