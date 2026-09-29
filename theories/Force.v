(** * The continuum residual is mu0 (J x B - grad p)

    Physics.v writes the continuum force residual ([full_point_b]) as
    formulas in the local derivatives of R, Z and lambda at one point, the
    jet: the Jacobian, the metric, the contravariant and covariant field and
    their derivatives, combined into three numbers. This file proves that
    those three numbers are the components of mu0 (J x B - grad p) along the
    coordinate directions e_s, e_u, e_v, with mu0 J the curl of the field
    computed in Cartesian coordinates ([force_law]).

    The field is VMEC's. Flux coordinates (s, u, v) are embedded
    cylindrically, x = (R cos v, R sin v, Z), so e_i = dx/di and
    sqrt(g) = e_s . (e_u x e_v) = R (R_u Z_s - R_s Z_u) ([sqrtg_triple]), and

      B = B^u e_u + B^v e_v,  B^u = phip (iota - lambda_v) / sqrt(g),
                              B^v = phip (1 + lambda_u) / sqrt(g).

    The statement quantifies over the Cartesian field. For any G = (G1, G2,
    G3) and P on R^3 that are differentiable at the point and equal the
    field and the pressure p(s) along the three coordinate lines through it,

      (curl G x G - mu0 grad P) . e_s = cres_s,   . e_u = cres_u,
                                                  . e_v = cres_v,

    where cres_s, cres_u, cres_v are the formulas of [full_point_b] at the
    jet of R, Z, lambda, iota and p at the point. No inverse of the
    coordinate map enters: the derivative of G is fixed by its values along
    three independent lines, and so is its curl.

    The proof has three parts. Along one coordinate line, the derivative of
    the covariant component B . e_i is computed twice: from the formulas,
    by the product and quotient rules ([cov_s_formula] and its two
    siblings), and from G, by the chain rule through the Cartesian
    derivative of G ([cov_s_chain]); the two agree, since they are
    derivatives of one function. Across lines, the mixed derivatives of the
    embedding are symmetric, so d_j B_i - d_i B_j = e_i . (A - A^T) e_j with
    A the derivative of G, which is e_i . (curl G x e_j) ([curl_identity]).
    Along the lines the pressure is p(s), which fixes grad P . e_j. *)

From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Local Open Scope R_scope.

(** * Differentiability on R^3 and the chain rule along a path *)

(** The linear map with gradient (a1, a2, a3). A function of R^3 is
    differentiable at x with that gradient when it is [filterdiff] there
    with this map, which is Frechet differentiability. *)
Definition lin3 (a1 a2 a3 : R) (h : R * R * R) : R :=
  a1 * fst (fst h) + a2 * snd (fst h) + a3 * snd h.

Lemma fd_pair {U V : NormedModule R_AbsRing} (f : R -> U) (g : R -> V) (x : R) lf lg :
  filterdiff f (locally x) lf -> filterdiff g (locally x) lg ->
  filterdiff (fun t => (f t, g t)) (locally x) (fun t => (lf t, lg t)).
Proof.
  intros Hf Hg.
  apply (filterdiff_comp'_2 f g (fun a b => (a, b)) x lf lg (fun a b => (a, b)) Hf Hg).
  apply (filterdiff_ext_lin _ (fun t => t)).
  - apply (filterdiff_ext (fun t => t)); [intros [a b]; reflexivity | apply filterdiff_id].
  - intros [a b]; reflexivity.
Qed.

Lemma chain3 (f : R * R * R -> R) (x : R * R * R) (a1 a2 a3 : R)
    (p1 p2 p3 : R -> R) (t0 d1 d2 d3 : R) :
  filterdiff f (locally x) (lin3 a1 a2 a3) -> (p1 t0, p2 t0, p3 t0) = x ->
  is_derive p1 t0 d1 -> is_derive p2 t0 d2 -> is_derive p3 t0 d3 ->
  is_derive (fun t => f (p1 t, p2 t, p3 t)) t0 (a1 * d1 + a2 * d2 + a3 * d3).
Proof.
  intros Hf Hp H1 H2 H3. unfold is_derive in *.
  pose proof (fd_pair (fun t => (p1 t, p2 t)) p3 t0 _ _ (fd_pair p1 p2 t0 _ _ H1 H2) H3) as Hd.
  cbv beta in Hd. rewrite <- Hp in Hf.
  eapply filterdiff_ext_lin.
  - exact (filterdiff_comp' (fun t => (p1 t, p2 t, p3 t)) f t0 _ _ Hd Hf).
  - intros y. unfold lin3. cbn. unfold scal. cbn. unfold mult. cbn. ring.
Qed.

(** * Derivative rules in the form used below *)

Lemma D_const (c x : R) : is_derive (fun _ => c) x 0.
Proof. exact (is_derive_const c x). Qed.

Lemma D_add (f g : R -> R) (x a b : R) :
  is_derive f x a -> is_derive g x b -> is_derive (fun t => f t + g t) x (a + b).
Proof. intros Hf Hg. exact (is_derive_plus f g x a b Hf Hg). Qed.

Lemma D_sub (f g : R -> R) (x a b : R) :
  is_derive f x a -> is_derive g x b -> is_derive (fun t => f t - g t) x (a - b).
Proof. intros Hf Hg. exact (is_derive_minus f g x a b Hf Hg). Qed.

Lemma D_mul (f g : R -> R) (x a b : R) :
  is_derive f x a -> is_derive g x b -> is_derive (fun t => f t * g t) x (a * g x + f x * b).
Proof.
  intros Hf Hg. pose proof (is_derive_mult f g x a b Hf Hg ltac:(intros; apply Rmult_comm)) as H.
  exact H.
Qed.

Lemma D_div (f g : R -> R) (x a b : R) :
  is_derive f x a -> is_derive g x b -> g x <> 0 ->
  is_derive (fun t => f t / g t) x ((a * g x - f x * b) / (g x * g x)).
Proof.
  intros Hf Hg Hn. pose proof (is_derive_div f g x a b Hf Hg Hn) as H.
  replace (g x * g x) with (g x ^ 2) by ring. exact H.
Qed.

Lemma D_cos (f : R -> R) (x a : R) :
  is_derive f x a -> is_derive (fun t => cos (f t)) x (- sin (f x) * a).
Proof.
  intros Hf. pose proof (is_derive_comp cos f x (- sin (f x)) a
    ltac:(apply is_derive_Reals, derivable_pt_lim_cos) Hf) as H.
  eapply is_derive_ext; [intros t; reflexivity |]. replace (- sin (f x) * a) with (scal a (- sin (f x))).
  - exact H.
  - unfold scal; cbn; unfold mult; cbn; ring.
Qed.

Lemma D_sin (f : R -> R) (x a : R) :
  is_derive f x a -> is_derive (fun t => sin (f t)) x (cos (f x) * a).
Proof.
  intros Hf. pose proof (is_derive_comp sin f x (cos (f x)) a
    ltac:(apply is_derive_Reals, derivable_pt_lim_sin) Hf) as H.
  replace (cos (f x) * a) with (scal a (cos (f x))).
  - exact H.
  - unfold scal; cbn; unfold mult; cbn; ring.
Qed.

(** * The continuum residual as Physics.v writes it *)

(** The jet at a point: R with its first and second derivatives, the first
    and second derivatives of Z, the derivatives of lambda the field reads,
    iota and its radial derivative, the flux derivative phip, and mu0 times
    the pressure gradient. *)
Record jet := Jet {
  jR : R ; jRs : R ; jRu : R ; jRv : R ;
  jRss : R ; jRsu : R ; jRsv : R ; jRuu : R ; jRuv : R ; jRvv : R ;
  jZs : R ; jZu : R ; jZv : R ;
  jZss : R ; jZsu : R ; jZsv : R ; jZuu : R ; jZuv : R ; jZvv : R ;
  jLu : R ; jLv : R ; jLsu : R ; jLsv : R ; jLuu : R ; jLuv : R ; jLvv : R ;
  jiota : R ; jiotap : R ; jphip : R ; jmu0pp : R }.

(** The quantities of [full_point_b], in its order and with its names. *)
Section Formulas.
Variable j : jet.
Let R0 := jR j.  Let Rs := jRs j.   Let Ru := jRu j.   Let Rv := jRv j.
Let Rss := jRss j. Let Rsu := jRsu j. Let Rsv := jRsv j.
Let Ruu := jRuu j. Let Ruv := jRuv j. Let Rvv := jRvv j.
Let Zs := jZs j.   Let Zu := jZu j.   Let Zv := jZv j.
Let Zss := jZss j. Let Zsu := jZsu j. Let Zsv := jZsv j.
Let Zuu := jZuu j. Let Zuv := jZuv j. Let Zvv := jZvv j.
Let Lu := jLu j. Let Lv := jLv j. Let Lsu := jLsu j. Let Lsv := jLsv j.
Let Luu := jLuu j. Let Luv := jLuv j. Let Lvv := jLvv j.
Let phip := jphip j.

Definition f_tau := Ru * Zs - Rs * Zu.
Definition f_sqrtg := R0 * f_tau.
Definition f_tau_s := (Rsu * Zs + Ru * Zss) - (Rss * Zu + Rs * Zsu).
Definition f_tau_u := (Ruu * Zs + Ru * Zsu) - (Rsu * Zu + Rs * Zuu).
Definition f_tau_v := (Ruv * Zs + Ru * Zsv) - (Rsv * Zu + Rs * Zuv).
Definition f_g_s := Rs * f_tau + R0 * f_tau_s.
Definition f_g_u := Ru * f_tau + R0 * f_tau_u.
Definition f_g_v := Rv * f_tau + R0 * f_tau_v.
Definition f_guu := Ru * Ru + Zu * Zu.
Definition f_guv := Ru * Rv + Zu * Zv.
Definition f_gvv := (Rv * Rv + Zv * Zv) + R0 * R0.
Definition f_gsu := Rs * Ru + Zs * Zu.
Definition f_gsv := Rs * Rv + Zs * Zv.
Definition f_guu_s := 2 * (Ru * Rsu + Zu * Zsu).
Definition f_guv_s := (Rsu * Rv + Ru * Rsv) + (Zsu * Zv + Zu * Zsv).
Definition f_gvv_s := 2 * ((Rv * Rsv + Zv * Zsv) + R0 * Rs).
Definition f_gsu_u := (Rsu * Ru + Rs * Ruu) + (Zsu * Zu + Zs * Zuu).
Definition f_gsu_v := (Rsv * Ru + Rs * Ruv) + (Zsv * Zu + Zs * Zuv).
Definition f_gsv_u := (Rsu * Rv + Rs * Ruv) + (Zsu * Zv + Zs * Zuv).
Definition f_gsv_v := (Rsv * Rv + Rs * Rvv) + (Zsv * Zv + Zs * Zvv).
Definition f_guu_v := 2 * (Ru * Ruv + Zu * Zuv).
Definition f_guv_u := (Ruu * Rv + Ru * Ruv) + (Zuu * Zv + Zu * Zuv).
Definition f_guv_v := (Ruv * Rv + Ru * Rvv) + (Zuv * Zv + Zu * Zvv).
Definition f_gvv_u := 2 * ((Rv * Ruv + Zv * Zuv) + R0 * Ru).
Definition f_bu_num := jiota j - Lv.
Definition f_bv_num := 1 + Lu.
Definition f_Bu := phip * f_bu_num / f_sqrtg.
Definition f_Bv := phip * f_bv_num / f_sqrtg.
Definition f_g2 := f_sqrtg * f_sqrtg.
Definition f_dB (nums gd : R) := phip * (nums * f_sqrtg - gd) / f_g2.
Definition f_Bu_s := f_dB (jiotap j - Lsv) (f_bu_num * f_g_s).
Definition f_Bv_s := f_dB Lsu (f_bv_num * f_g_s).
Definition f_Bu_u := f_dB (- Luv) (f_bu_num * f_g_u).
Definition f_Bv_u := f_dB Luu (f_bv_num * f_g_u).
Definition f_Bu_v := f_dB (- Lvv) (f_bu_num * f_g_v).
Definition f_Bv_v := f_dB Luv (f_bv_num * f_g_v).
Definition f_dcov (gu gud gv gvd bud bvd : R) :=
  (gud * f_Bu + gu * bud) + (gvd * f_Bv + gv * bvd).
Definition f_B_u_s := f_dcov f_guu f_guu_s f_guv f_guv_s f_Bu_s f_Bv_s.
Definition f_B_v_s := f_dcov f_guv f_guv_s f_gvv f_gvv_s f_Bu_s f_Bv_s.
Definition f_B_s_u := f_dcov f_gsu f_gsu_u f_gsv f_gsv_u f_Bu_u f_Bv_u.
Definition f_B_s_v := f_dcov f_gsu f_gsu_v f_gsv f_gsv_v f_Bu_v f_Bv_v.
Definition f_B_u_v := f_dcov f_guu f_guu_v f_guv f_guv_v f_Bu_v f_Bv_v.
Definition f_B_v_u := f_dcov f_guv f_guv_u f_gvv f_gvv_u f_Bu_u f_Bv_u.
Definition f_mu0Js := f_B_v_u - f_B_u_v.

(** The three components [full_point_b] returns. *)
Definition cres_s := ((f_B_s_v - f_B_v_s) * f_Bv - (f_B_u_s - f_B_s_u) * f_Bu) - jmu0pp j.
Definition cres_u := - (f_mu0Js * f_Bv).
Definition cres_v := f_mu0Js * f_Bu.

End Formulas.

(** * Vectors *)

Definition dot3 (a1 a2 a3 b1 b2 b3 : R) : R := a1 * b1 + a2 * b2 + a3 * b3.

(** e_s . (e_u x e_v) for the cylindrical embedding is Physics.v's Jacobian. *)
Lemma sqrtg_triple (R Rs Ru Rv Zs Zu Zv v : R) :
  let es1 := Rs * cos v in let es2 := Rs * sin v in let es3 := Zs in
  let eu1 := Ru * cos v in let eu2 := Ru * sin v in let eu3 := Zu in
  let ev1 := Rv * cos v - R * sin v in let ev2 := Rv * sin v + R * cos v in let ev3 := Zv in
  dot3 es1 es2 es3 (eu2 * ev3 - eu3 * ev2) (eu3 * ev1 - eu1 * ev3) (eu1 * ev2 - eu2 * ev1)
  = R * (Ru * Zs - Rs * Zu).
Proof.
  cbv zeta. unfold dot3. pose proof (sin2_cos2 v) as E. unfold Rsqr in E.
  replace (R * (Ru * Zs - Rs * Zu)) with (R * (Ru * Zs - Rs * Zu) * (sin v * sin v + cos v * cos v))
    by (rewrite E; ring).
  ring.
Qed.

(** * Along one coordinate line *)

(** Everything along a line through the point, parametrized by t: the
    values of R, Z and their first derivatives, the two derivatives of
    lambda the field reads, iota, and the toroidal angle, with their
    derivatives at t0. *)
Section Line.

Variables (r rs ru rv z zs zu zv lu lv io an : R -> R) (phip t0 : R).
Variables (dr drs dru drv dz dzs dzu dzv dlu dlv dio dan : R).
Hypothesis Dr : is_derive r t0 dr.
Hypothesis Drs : is_derive rs t0 drs.
Hypothesis Dru : is_derive ru t0 dru.
Hypothesis Drv : is_derive rv t0 drv.
Hypothesis Dz : is_derive z t0 dz.
Hypothesis Dzs : is_derive zs t0 dzs.
Hypothesis Dzu : is_derive zu t0 dzu.
Hypothesis Dzv : is_derive zv t0 dzv.
Hypothesis Dlu : is_derive lu t0 dlu.
Hypothesis Dlv : is_derive lv t0 dlv.
Hypothesis Dio : is_derive io t0 dio.
Hypothesis Dan : is_derive an t0 dan.

Definition l_sg (t : R) := r t * (ru t * zs t - rs t * zu t).
Definition l_bu (t : R) := phip * (io t - lv t) / l_sg t.
Definition l_bv (t : R) := phip * (1 + lu t) / l_sg t.

(** The coordinate vectors and the field in Cartesian components. *)
Definition l_es1 t := rs t * cos (an t).
Definition l_es2 t := rs t * sin (an t).
Definition l_es3 t := zs t.
Definition l_eu1 t := ru t * cos (an t).
Definition l_eu2 t := ru t * sin (an t).
Definition l_eu3 t := zu t.
Definition l_ev1 t := rv t * cos (an t) - r t * sin (an t).
Definition l_ev2 t := rv t * sin (an t) + r t * cos (an t).
Definition l_ev3 t := zv t.
Definition l_B1 t := l_bu t * l_eu1 t + l_bv t * l_ev1 t.
Definition l_B2 t := l_bu t * l_eu2 t + l_bv t * l_ev2 t.
Definition l_B3 t := l_bu t * l_eu3 t + l_bv t * l_ev3 t.

(** The covariant components B . e_i. *)
Definition l_cs t := dot3 (l_B1 t) (l_B2 t) (l_B3 t) (l_es1 t) (l_es2 t) (l_es3 t).
Definition l_cu t := dot3 (l_B1 t) (l_B2 t) (l_B3 t) (l_eu1 t) (l_eu2 t) (l_eu3 t).
Definition l_cv t := dot3 (l_B1 t) (l_B2 t) (l_B3 t) (l_ev1 t) (l_ev2 t) (l_ev3 t).

Lemma trig1 (t : R) : sin (an t) * sin (an t) + cos (an t) * cos (an t) = 1.
Proof. pose proof (sin2_cos2 (an t)) as E. unfold Rsqr in E. exact E. Qed.

Lemma l_cs_metric (t : R) :
  l_cs t = (rs t * ru t + zs t * zu t) * l_bu t + (rs t * rv t + zs t * zv t) * l_bv t.
Proof.
  unfold l_cs, dot3, l_B1, l_B2, l_B3, l_es1, l_es2, l_es3, l_eu1, l_eu2, l_eu3, l_ev1, l_ev2, l_ev3.
  pose proof (trig1 t) as E.
  replace (rs t * ru t) with (rs t * ru t * (sin (an t) * sin (an t) + cos (an t) * cos (an t)))
    by (rewrite E; ring).
  replace (rs t * rv t) with (rs t * rv t * (sin (an t) * sin (an t) + cos (an t) * cos (an t)))
    by (rewrite E; ring).
  ring.
Qed.

Lemma l_cu_metric (t : R) :
  l_cu t = (ru t * ru t + zu t * zu t) * l_bu t + (ru t * rv t + zu t * zv t) * l_bv t.
Proof.
  unfold l_cu, dot3, l_B1, l_B2, l_B3, l_eu1, l_eu2, l_eu3, l_ev1, l_ev2, l_ev3.
  pose proof (trig1 t) as E.
  replace (ru t * ru t) with (ru t * ru t * (sin (an t) * sin (an t) + cos (an t) * cos (an t)))
    by (rewrite E; ring).
  replace (ru t * rv t) with (ru t * rv t * (sin (an t) * sin (an t) + cos (an t) * cos (an t)))
    by (rewrite E; ring).
  ring.
Qed.

Lemma l_cv_metric (t : R) :
  l_cv t = (ru t * rv t + zu t * zv t) * l_bu t + ((rv t * rv t + zv t * zv t) + r t * r t) * l_bv t.
Proof.
  unfold l_cv, dot3, l_B1, l_B2, l_B3, l_eu1, l_eu2, l_eu3, l_ev1, l_ev2, l_ev3.
  pose proof (trig1 t) as E.
  replace (ru t * rv t) with (ru t * rv t * (sin (an t) * sin (an t) + cos (an t) * cos (an t)))
    by (rewrite E; ring).
  replace (rv t * rv t + zv t * zv t + r t * r t)
    with ((rv t * rv t + r t * r t) * (sin (an t) * sin (an t) + cos (an t) * cos (an t)) + zv t * zv t)
    by (rewrite E; ring).
  ring.
Qed.

(** The derivatives at t0, by the rules. *)
Definition d_tau := (dru * zs t0 + ru t0 * dzs) - (drs * zu t0 + rs t0 * dzu).
Definition d_sg := dr * (ru t0 * zs t0 - rs t0 * zu t0) + r t0 * d_tau.
Definition d_bu := phip * ((dio - dlv) * l_sg t0 - (io t0 - lv t0) * d_sg) / (l_sg t0 * l_sg t0).
Definition d_bv := phip * (dlu * l_sg t0 - (1 + lu t0) * d_sg) / (l_sg t0 * l_sg t0).

Lemma D_sg : is_derive l_sg t0 d_sg.
Proof.
  unfold l_sg, d_sg, d_tau.
  apply (is_derive_ext (fun t => r t * (ru t * zs t - rs t * zu t))); [reflexivity |].
  eapply is_derive_ext; [intros t; reflexivity |].
  pose proof (D_mul r (fun t => ru t * zs t - rs t * zu t) t0 dr _ Dr
               (D_sub _ _ t0 _ _ (D_mul ru zs t0 _ _ Dru Dzs) (D_mul rs zu t0 _ _ Drs Dzu))) as H.
  cbv beta in H. replace (dr * (ru t0 * zs t0 - rs t0 * zu t0) + r t0 * (dru * zs t0 + ru t0 * dzs - (drs * zu t0 + rs t0 * dzu)))
    with (dr * (ru t0 * zs t0 - rs t0 * zu t0) + r t0 * (dru * zs t0 + ru t0 * dzs - (drs * zu t0 + rs t0 * dzu))) by ring.
  exact H.
Qed.

Hypothesis Hsg : l_sg t0 <> 0.

Lemma D_bu : is_derive l_bu t0 d_bu.
Proof.
  unfold l_bu, d_bu.
  pose proof (D_div (fun t => phip * (io t - lv t)) l_sg t0 (phip * (dio - dlv)) d_sg
    ltac:(apply (is_derive_ext (fun t => phip * (io t - lv t))); [reflexivity |];
          pose proof (D_mul (fun _ => phip) (fun t => io t - lv t) t0 0 (dio - dlv) (D_const phip t0)
                        (D_sub io lv t0 _ _ Dio Dlv)) as H; cbv beta in H;
          replace (phip * (dio - dlv)) with (0 * (io t0 - lv t0) + phip * (dio - dlv)) by ring; exact H)
    D_sg Hsg) as H.
  cbv beta in H. replace (phip * ((dio - dlv) * l_sg t0 - (io t0 - lv t0) * d_sg) / (l_sg t0 * l_sg t0))
    with ((phip * (dio - dlv) * l_sg t0 - phip * (io t0 - lv t0) * d_sg) / (l_sg t0 * l_sg t0))
    by (unfold Rdiv; ring).
  exact H.
Qed.

Lemma D_bv : is_derive l_bv t0 d_bv.
Proof.
  unfold l_bv, d_bv.
  pose proof (D_div (fun t => phip * (1 + lu t)) l_sg t0 (phip * dlu) d_sg
    ltac:(pose proof (D_mul (fun _ => phip) (fun t => 1 + lu t) t0 0 (0 + dlu) (D_const phip t0)
                        (D_add (fun _ => 1) lu t0 _ _ (D_const 1 t0) Dlu)) as H; cbv beta in H;
          replace (phip * dlu) with (0 * (1 + lu t0) + phip * (0 + dlu)) by ring; exact H)
    D_sg Hsg) as H.
  cbv beta in H. replace (phip * (dlu * l_sg t0 - (1 + lu t0) * d_sg) / (l_sg t0 * l_sg t0))
    with ((phip * dlu * l_sg t0 - phip * (1 + lu t0) * d_sg) / (l_sg t0 * l_sg t0))
    by (unfold Rdiv; ring).
  exact H.
Qed.

(** The derivative of a product of two line functions. *)
Lemma D_mul2 (f g : R -> R) (a b : R) :
  is_derive f t0 a -> is_derive g t0 b -> is_derive (fun t => f t * g t) t0 (a * g t0 + f t0 * b).
Proof. apply D_mul. Qed.

(** B . e_s, B . e_u, B . e_v are differentiable along the line, with the
    derivative the product rule gives from the metric form. *)
Lemma D_cs :
  is_derive l_cs t0
    ((drs * ru t0 + rs t0 * dru + (dzs * zu t0 + zs t0 * dzu)) * l_bu t0
     + (rs t0 * ru t0 + zs t0 * zu t0) * d_bu
     + ((drs * rv t0 + rs t0 * drv + (dzs * zv t0 + zs t0 * dzv)) * l_bv t0
        + (rs t0 * rv t0 + zs t0 * zv t0) * d_bv)).
Proof.
  apply (is_derive_ext (fun t => (rs t * ru t + zs t * zu t) * l_bu t + (rs t * rv t + zs t * zv t) * l_bv t));
    [intros t; symmetry; apply l_cs_metric |].
  apply (D_add (fun t => (rs t * ru t + zs t * zu t) * l_bu t) (fun t => (rs t * rv t + zs t * zv t) * l_bv t)).
  - apply (D_mul (fun t => rs t * ru t + zs t * zu t) l_bu).
    + apply (D_add (fun t => rs t * ru t) (fun t => zs t * zu t)); apply D_mul; assumption.
    + exact D_bu.
  - apply (D_mul (fun t => rs t * rv t + zs t * zv t) l_bv).
    + apply (D_add (fun t => rs t * rv t) (fun t => zs t * zv t)); apply D_mul; assumption.
    + exact D_bv.
Qed.

Lemma D_cu :
  is_derive l_cu t0
    ((dru * ru t0 + ru t0 * dru + (dzu * zu t0 + zu t0 * dzu)) * l_bu t0
     + (ru t0 * ru t0 + zu t0 * zu t0) * d_bu
     + ((dru * rv t0 + ru t0 * drv + (dzu * zv t0 + zu t0 * dzv)) * l_bv t0
        + (ru t0 * rv t0 + zu t0 * zv t0) * d_bv)).
Proof.
  apply (is_derive_ext (fun t => (ru t * ru t + zu t * zu t) * l_bu t + (ru t * rv t + zu t * zv t) * l_bv t));
    [intros t; symmetry; apply l_cu_metric |].
  apply (D_add (fun t => (ru t * ru t + zu t * zu t) * l_bu t) (fun t => (ru t * rv t + zu t * zv t) * l_bv t)).
  - apply (D_mul (fun t => ru t * ru t + zu t * zu t) l_bu).
    + apply (D_add (fun t => ru t * ru t) (fun t => zu t * zu t)); apply D_mul; assumption.
    + exact D_bu.
  - apply (D_mul (fun t => ru t * rv t + zu t * zv t) l_bv).
    + apply (D_add (fun t => ru t * rv t) (fun t => zu t * zv t)); apply D_mul; assumption.
    + exact D_bv.
Qed.

Lemma D_cv :
  is_derive l_cv t0
    ((dru * rv t0 + ru t0 * drv + (dzu * zv t0 + zu t0 * dzv)) * l_bu t0
     + (ru t0 * rv t0 + zu t0 * zv t0) * d_bu
     + ((drv * rv t0 + rv t0 * drv + (dzv * zv t0 + zv t0 * dzv) + (dr * r t0 + r t0 * dr)) * l_bv t0
        + ((rv t0 * rv t0 + zv t0 * zv t0) + r t0 * r t0) * d_bv)).
Proof.
  apply (is_derive_ext (fun t => (ru t * rv t + zu t * zv t) * l_bu t
                                 + ((rv t * rv t + zv t * zv t) + r t * r t) * l_bv t));
    [intros t; symmetry; apply l_cv_metric |].
  apply (D_add (fun t => (ru t * rv t + zu t * zv t) * l_bu t)
               (fun t => ((rv t * rv t + zv t * zv t) + r t * r t) * l_bv t)).
  - apply (D_mul (fun t => ru t * rv t + zu t * zv t) l_bu).
    + apply (D_add (fun t => ru t * rv t) (fun t => zu t * zv t)); apply D_mul; assumption.
    + exact D_bu.
  - apply (D_mul (fun t => (rv t * rv t + zv t * zv t) + r t * r t) l_bv).
    + apply (D_add (fun t => rv t * rv t + zv t * zv t) (fun t => r t * r t)).
      * apply (D_add (fun t => rv t * rv t) (fun t => zv t * zv t)); apply D_mul; assumption.
      * apply D_mul; assumption.
    + exact D_bv.
Qed.

(** The Cartesian path and the derivatives of the coordinate vectors. *)
Definition l_x (t : R) : R * R * R := (r t * cos (an t), r t * sin (an t), z t).
Definition d_x1 := dr * cos (an t0) + r t0 * (- sin (an t0) * dan).
Definition d_x2 := dr * sin (an t0) + r t0 * (cos (an t0) * dan).
Definition d_es1 := drs * cos (an t0) + rs t0 * (- sin (an t0) * dan).
Definition d_es2 := drs * sin (an t0) + rs t0 * (cos (an t0) * dan).
Definition d_eu1 := dru * cos (an t0) + ru t0 * (- sin (an t0) * dan).
Definition d_eu2 := dru * sin (an t0) + ru t0 * (cos (an t0) * dan).
Definition d_ev1 := (drv * cos (an t0) + rv t0 * (- sin (an t0) * dan))
                    - (dr * sin (an t0) + r t0 * (cos (an t0) * dan)).
Definition d_ev2 := (drv * sin (an t0) + rv t0 * (cos (an t0) * dan))
                    + (dr * cos (an t0) + r t0 * (- sin (an t0) * dan)).

Lemma D_rc (f : R -> R) (a : R) : is_derive f t0 a ->
  is_derive (fun t => f t * cos (an t)) t0 (a * cos (an t0) + f t0 * (- sin (an t0) * dan)).
Proof. intros H. apply (D_mul f (fun t => cos (an t))); [exact H | apply D_cos, Dan]. Qed.

Lemma D_rsn (f : R -> R) (a : R) : is_derive f t0 a ->
  is_derive (fun t => f t * sin (an t)) t0 (a * sin (an t0) + f t0 * (cos (an t0) * dan)).
Proof. intros H. apply (D_mul f (fun t => sin (an t))); [exact H | apply D_sin, Dan]. Qed.

(** The Cartesian components of the field along the line, differentiated by
    the product rule. *)
Definition d_B1 := d_bu * l_eu1 t0 + l_bu t0 * d_eu1 + (d_bv * l_ev1 t0 + l_bv t0 * d_ev1).
Definition d_B2 := d_bu * l_eu2 t0 + l_bu t0 * d_eu2 + (d_bv * l_ev2 t0 + l_bv t0 * d_ev2).
Definition d_B3 := d_bu * l_eu3 t0 + l_bu t0 * dzu + (d_bv * l_ev3 t0 + l_bv t0 * dzv).

Lemma D_B : is_derive l_B1 t0 d_B1 /\ is_derive l_B2 t0 d_B2 /\ is_derive l_B3 t0 d_B3.
Proof.
  refine (conj _ (conj _ _)).
  - apply (D_add (fun t => l_bu t * l_eu1 t) (fun t => l_bv t * l_ev1 t)).
    + apply (D_mul l_bu l_eu1); [exact D_bu | apply D_rc, Dru].
    + apply (D_mul l_bv l_ev1); [exact D_bv |].
      apply (D_sub (fun t => rv t * cos (an t)) (fun t => r t * sin (an t))); [apply D_rc, Drv | apply D_rsn, Dr].
  - apply (D_add (fun t => l_bu t * l_eu2 t) (fun t => l_bv t * l_ev2 t)).
    + apply (D_mul l_bu l_eu2); [exact D_bu | apply D_rsn, Dru].
    + apply (D_mul l_bv l_ev2); [exact D_bv |].
      apply (D_add (fun t => rv t * sin (an t)) (fun t => r t * cos (an t))); [apply D_rsn, Drv | apply D_rc, Dr].
  - apply (D_add (fun t => l_bu t * l_eu3 t) (fun t => l_bv t * l_ev3 t)).
    + apply (D_mul l_bu l_eu3); [exact D_bu | exact Dzu].
    + apply (D_mul l_bv l_ev3); [exact D_bv | exact Dzv].
Qed.

(** A field G on R^3, differentiable at the point with derivative rows
    (a11 a12 a13), (a21 a22 a23), (a31 a32 a33), and a function E_i along
    the line: the derivative of G . E along the path is (A x') . E + G . E'. *)
Variables (G1 G2 G3 : R * R * R -> R) (a11 a12 a13 a21 a22 a23 a31 a32 a33 : R).
Hypothesis HG1 : filterdiff G1 (locally (l_x t0)) (lin3 a11 a12 a13).
Hypothesis HG2 : filterdiff G2 (locally (l_x t0)) (lin3 a21 a22 a23).
Hypothesis HG3 : filterdiff G3 (locally (l_x t0)) (lin3 a31 a32 a33).

Lemma D_Gx1 : is_derive (fun t => G1 (l_x t)) t0 (a11 * d_x1 + a12 * d_x2 + a13 * dz).
Proof.
  exact (chain3 G1 (l_x t0) a11 a12 a13 (fun t => r t * cos (an t)) (fun t => r t * sin (an t)) z t0 _ _ _
           HG1 eq_refl (D_rc r dr Dr) (D_rsn r dr Dr) Dz).
Qed.

Lemma D_Gx2 : is_derive (fun t => G2 (l_x t)) t0 (a21 * d_x1 + a22 * d_x2 + a23 * dz).
Proof.
  exact (chain3 G2 (l_x t0) a21 a22 a23 (fun t => r t * cos (an t)) (fun t => r t * sin (an t)) z t0 _ _ _
           HG2 eq_refl (D_rc r dr Dr) (D_rsn r dr Dr) Dz).
Qed.

Lemma D_Gx3 : is_derive (fun t => G3 (l_x t)) t0 (a31 * d_x1 + a32 * d_x2 + a33 * dz).
Proof.
  exact (chain3 G3 (l_x t0) a31 a32 a33 (fun t => r t * cos (an t)) (fun t => r t * sin (an t)) z t0 _ _ _
           HG3 eq_refl (D_rc r dr Dr) (D_rsn r dr Dr) Dz).
Qed.

Lemma D_Gdot (E1 E2 E3 : R -> R) (d1 d2 d3 : R) :
  is_derive E1 t0 d1 -> is_derive E2 t0 d2 -> is_derive E3 t0 d3 ->
  is_derive (fun t => dot3 (G1 (l_x t)) (G2 (l_x t)) (G3 (l_x t)) (E1 t) (E2 t) (E3 t)) t0
    ((a11 * d_x1 + a12 * d_x2 + a13 * dz) * E1 t0 + G1 (l_x t0) * d1
     + ((a21 * d_x1 + a22 * d_x2 + a23 * dz) * E2 t0 + G2 (l_x t0) * d2)
     + ((a31 * d_x1 + a32 * d_x2 + a33 * dz) * E3 t0 + G3 (l_x t0) * d3)).
Proof.
  intros H1 H2 H3. unfold dot3.
  apply (D_add (fun t => G1 (l_x t) * E1 t + G2 (l_x t) * E2 t) (fun t => G3 (l_x t) * E3 t)).
  - apply (D_add (fun t => G1 (l_x t) * E1 t) (fun t => G2 (l_x t) * E2 t));
      apply D_mul; [apply D_Gx1 | exact H1 | apply D_Gx2 | exact H2].
  - apply D_mul; [apply D_Gx3 | exact H3].
Qed.

(** Where G equals the reconstructed field along the line near t0, the two
    derivatives of each covariant component agree. *)
Hypothesis Hagree : locally t0 (fun t => G1 (l_x t) = l_B1 t /\ G2 (l_x t) = l_B2 t /\ G3 (l_x t) = l_B3 t).

Lemma agree_dot (E1 E2 E3 : R -> R) :
  locally t0 (fun t => dot3 (G1 (l_x t)) (G2 (l_x t)) (G3 (l_x t)) (E1 t) (E2 t) (E3 t)
                       = dot3 (l_B1 t) (l_B2 t) (l_B3 t) (E1 t) (E2 t) (E3 t)).
Proof.
  apply (filter_imp (fun t => G1 (l_x t) = l_B1 t /\ G2 (l_x t) = l_B2 t /\ G3 (l_x t) = l_B3 t));
    [| exact Hagree].
  intros t [E1' [E2' E3']]. rewrite E1', E2', E3'. reflexivity.
Qed.

Lemma G_at_t0 : G1 (l_x t0) = l_B1 t0 /\ G2 (l_x t0) = l_B2 t0 /\ G3 (l_x t0) = l_B3 t0.
Proof. exact (locally_singleton _ _ Hagree). Qed.

Lemma cov_by_G (E1 E2 E3 : R -> R) (d1 d2 d3 dc : R) :
  is_derive E1 t0 d1 -> is_derive E2 t0 d2 -> is_derive E3 t0 d3 ->
  is_derive (fun t => dot3 (l_B1 t) (l_B2 t) (l_B3 t) (E1 t) (E2 t) (E3 t)) t0 dc ->
  dc = (a11 * d_x1 + a12 * d_x2 + a13 * dz) * E1 t0 + G1 (l_x t0) * d1
       + ((a21 * d_x1 + a22 * d_x2 + a23 * dz) * E2 t0 + G2 (l_x t0) * d2)
       + ((a31 * d_x1 + a32 * d_x2 + a33 * dz) * E3 t0 + G3 (l_x t0) * d3).
Proof.
  intros H1 H2 H3 Hc.
  pose proof (D_Gdot E1 E2 E3 d1 d2 d3 H1 H2 H3) as HG.
  pose proof (is_derive_ext_loc _ _ t0 _ (agree_dot E1 E2 E3) HG) as HG'.
  rewrite <- (is_derive_unique _ _ _ Hc). apply is_derive_unique. exact HG'.
Qed.

(** The three instances. *)
Lemma cov_s_chain :
  (drs * ru t0 + rs t0 * dru + (dzs * zu t0 + zs t0 * dzu)) * l_bu t0
  + (rs t0 * ru t0 + zs t0 * zu t0) * d_bu
  + ((drs * rv t0 + rs t0 * drv + (dzs * zv t0 + zs t0 * dzv)) * l_bv t0
     + (rs t0 * rv t0 + zs t0 * zv t0) * d_bv)
  = (a11 * d_x1 + a12 * d_x2 + a13 * dz) * l_es1 t0 + G1 (l_x t0) * d_es1
    + ((a21 * d_x1 + a22 * d_x2 + a23 * dz) * l_es2 t0 + G2 (l_x t0) * d_es2)
    + ((a31 * d_x1 + a32 * d_x2 + a33 * dz) * l_es3 t0 + G3 (l_x t0) * dzs).
Proof.
  apply cov_by_G; [apply D_rc, Drs | apply D_rsn, Drs | exact Dzs | exact D_cs].
Qed.

Lemma cov_u_chain :
  (dru * ru t0 + ru t0 * dru + (dzu * zu t0 + zu t0 * dzu)) * l_bu t0
  + (ru t0 * ru t0 + zu t0 * zu t0) * d_bu
  + ((dru * rv t0 + ru t0 * drv + (dzu * zv t0 + zu t0 * dzv)) * l_bv t0
     + (ru t0 * rv t0 + zu t0 * zv t0) * d_bv)
  = (a11 * d_x1 + a12 * d_x2 + a13 * dz) * l_eu1 t0 + G1 (l_x t0) * d_eu1
    + ((a21 * d_x1 + a22 * d_x2 + a23 * dz) * l_eu2 t0 + G2 (l_x t0) * d_eu2)
    + ((a31 * d_x1 + a32 * d_x2 + a33 * dz) * l_eu3 t0 + G3 (l_x t0) * dzu).
Proof.
  apply cov_by_G; [apply D_rc, Dru | apply D_rsn, Dru | exact Dzu | exact D_cu].
Qed.

Lemma cov_v_chain :
  (dru * rv t0 + ru t0 * drv + (dzu * zv t0 + zu t0 * dzv)) * l_bu t0
  + (ru t0 * rv t0 + zu t0 * zv t0) * d_bu
  + ((drv * rv t0 + rv t0 * drv + (dzv * zv t0 + zv t0 * dzv) + (dr * r t0 + r t0 * dr)) * l_bv t0
     + ((rv t0 * rv t0 + zv t0 * zv t0) + r t0 * r t0) * d_bv)
  = (a11 * d_x1 + a12 * d_x2 + a13 * dz) * l_ev1 t0 + G1 (l_x t0) * d_ev1
    + ((a21 * d_x1 + a22 * d_x2 + a23 * dz) * l_ev2 t0 + G2 (l_x t0) * d_ev2)
    + ((a31 * d_x1 + a32 * d_x2 + a33 * dz) * l_ev3 t0 + G3 (l_x t0) * dzv).
Proof.
  apply cov_by_G; [| | exact Dzv | exact D_cv].
  - apply (D_sub (fun t => rv t * cos (an t)) (fun t => r t * sin (an t))); [apply D_rc, Drv | apply D_rsn, Dr].
  - apply (D_add (fun t => rv t * sin (an t)) (fun t => r t * cos (an t))); [apply D_rsn, Drv | apply D_rc, Dr].
Qed.

(** A scalar P on R^3 equal to a function pl along the line: its gradient
    along the path is the derivative of pl. *)
Variables (P : R * R * R -> R) (q1 q2 q3 : R) (pl : R -> R) (dpl : R).
Hypothesis HP : filterdiff P (locally (l_x t0)) (lin3 q1 q2 q3).
Hypothesis HPagree : locally t0 (fun t => P (l_x t) = pl t).
Hypothesis Dpl : is_derive pl t0 dpl.

Lemma grad_by_line : q1 * d_x1 + q2 * d_x2 + q3 * dz = dpl.
Proof.
  assert (H : is_derive (fun t => P (l_x t)) t0 (q1 * d_x1 + q2 * d_x2 + q3 * dz)).
  { exact (chain3 P (l_x t0) q1 q2 q3 (fun t => r t * cos (an t)) (fun t => r t * sin (an t)) z t0 _ _ _
             HP eq_refl (D_rc r dr Dr) (D_rsn r dr Dr) Dz). }
  pose proof (is_derive_ext_loc _ _ t0 _ HPagree H) as H'.
  rewrite <- (is_derive_unique _ _ _ H'). apply is_derive_unique. exact Dpl.
Qed.

End Line.

(** * The curl identity *)

(** With A the derivative of G, the antisymmetric part of A acts as the
    curl: d_j B_i - d_i B_j = e_i . (A - A^T) e_j = e_i . (curl G x e_j).
    Here each d_j B_i is given in the form the lines produce, (A e_j) . e_i
    + G . d_j e_i, with the mixed derivatives of the coordinate vectors
    equal in pairs. *)
Lemma curl_identity
    (a11 a12 a13 a21 a22 a23 a31 a32 a33 : R)
    (es1 es2 es3 eu1 eu2 eu3 ev1 ev2 ev3 : R) (bu bv : R)
    (dsu1 dsu2 dsu3 dsv1 dsv2 dsv3 duv1 duv2 duv3 : R) :
  let G1 := bu * eu1 + bv * ev1 in let G2 := bu * eu2 + bv * ev2 in let G3 := bu * eu3 + bv * ev3 in
  let Ae1 x1 x2 x3 := a11 * x1 + a12 * x2 + a13 * x3 in
  let Ae2 x1 x2 x3 := a21 * x1 + a22 * x2 + a23 * x3 in
  let Ae3 x1 x2 x3 := a31 * x1 + a32 * x2 + a33 * x3 in
  let D (xj1 xj2 xj3 ei1 ei2 ei3 d1 d2 d3 : R) :=
    Ae1 xj1 xj2 xj3 * ei1 + G1 * d1 + (Ae2 xj1 xj2 xj3 * ei2 + G2 * d2) + (Ae3 xj1 xj2 xj3 * ei3 + G3 * d3) in
  let B_s_u := D eu1 eu2 eu3 es1 es2 es3 dsu1 dsu2 dsu3 in
  let B_u_s := D es1 es2 es3 eu1 eu2 eu3 dsu1 dsu2 dsu3 in
  let B_s_v := D ev1 ev2 ev3 es1 es2 es3 dsv1 dsv2 dsv3 in
  let B_v_s := D es1 es2 es3 ev1 ev2 ev3 dsv1 dsv2 dsv3 in
  let B_u_v := D ev1 ev2 ev3 eu1 eu2 eu3 duv1 duv2 duv3 in
  let B_v_u := D eu1 eu2 eu3 ev1 ev2 ev3 duv1 duv2 duv3 in
  let w1 := a32 - a23 in let w2 := a13 - a31 in let w3 := a21 - a12 in
  let c1 := w2 * G3 - w3 * G2 in let c2 := w3 * G1 - w1 * G3 in let c3 := w1 * G2 - w2 * G1 in
  dot3 c1 c2 c3 es1 es2 es3 = (B_s_v - B_v_s) * bv - (B_u_s - B_s_u) * bu /\
  dot3 c1 c2 c3 eu1 eu2 eu3 = - ((B_v_u - B_u_v) * bv) /\
  dot3 c1 c2 c3 ev1 ev2 ev3 = (B_v_u - B_u_v) * bu.
Proof. cbv zeta. unfold dot3. repeat split; ring. Qed.

(** * The force in the coordinates *)

(** [force_law] reads the curl off a Cartesian field G that agrees with the
    reconstructed field along the three coordinate lines. The same force is
    written here with no such field. In the orthonormal frame
    (e_R, e_phi, e_Z) at the toroidal angle of the point, the coordinate
    vectors e_s, e_u, e_v, their derivatives along the coordinate lines, and
    the field B = B^u e_u + B^v e_v with its derivatives d_j B along the lines
    are formulas in the jet. grad s, grad u and grad v are the dual basis,
    e_u x e_v / sqrt(g) and its two cyclic companions, and the curl is
    sum_j grad x^j x d_j B: the derivative of the field along the coordinate
    lines carried through the inverse of the Jacobian matrix, which is the
    curl in coordinates. [force_coords] states that the three formulas of
    [full_point_b] are the components along e_s, e_u and e_v of
    (curl B) x B - mu0 p' grad s. *)

Record vec := V { vx : R ; vy : R ; vz : R }.

Definition vdot (a b : vec) : R := vx a * vx b + vy a * vy b + vz a * vz b.
Definition vcross (a b : vec) : vec :=
  V (vy a * vz b - vz a * vy b) (vz a * vx b - vx a * vz b) (vx a * vy b - vy a * vx b).
Definition vadd (a b : vec) : vec := V (vx a + vx b) (vy a + vy b) (vz a + vz b).
Definition vscale (k : R) (a : vec) : vec := V (k * vx a) (k * vy a) (k * vz a).

Section Coordinates.
Variable j : jet.

(** The coordinate vectors at the point. *)
Definition c_es := V (jRs j) 0 (jZs j).
Definition c_eu := V (jRu j) 0 (jZu j).
Definition c_ev := V (jRv j) (jR j) (jZv j).

(** Their derivatives along the coordinate lines, d_j e_i = d_i e_j. The frame
    turns with the toroidal angle: d_v e_R = e_phi and d_v e_phi = - e_R. *)
Definition c_esu := V (jRsu j) 0 (jZsu j).
Definition c_esv := V (jRsv j) (jRs j) (jZsv j).
Definition c_euu := V (jRuu j) 0 (jZuu j).
Definition c_euv := V (jRuv j) (jRu j) (jZuv j).
Definition c_evv := V (jRvv j - jR j) (2 * jRv j) (jZvv j).

(** The field, and its derivatives along the lines by the product rule. *)
Definition c_B := vadd (vscale (f_Bu j) c_eu) (vscale (f_Bv j) c_ev).
Definition c_dB (bu' bv' : R) (eu' ev' : vec) : vec :=
  vadd (vadd (vscale bu' c_eu) (vscale (f_Bu j) eu')) (vadd (vscale bv' c_ev) (vscale (f_Bv j) ev')).
Definition c_Bs := c_dB (f_Bu_s j) (f_Bv_s j) c_esu c_esv.
Definition c_Bu := c_dB (f_Bu_u j) (f_Bv_u j) c_euu c_euv.
Definition c_Bv := c_dB (f_Bu_v j) (f_Bv_v j) c_euv c_evv.

(** The dual basis. *)
Definition c_gs := vscale (/ f_sqrtg j) (vcross c_eu c_ev).
Definition c_gu := vscale (/ f_sqrtg j) (vcross c_ev c_es).
Definition c_gv := vscale (/ f_sqrtg j) (vcross c_es c_eu).

(** The curl in the coordinates, and the force. *)
Definition c_curl := vadd (vadd (vcross c_gs c_Bs) (vcross c_gu c_Bu)) (vcross c_gv c_Bv).
Definition c_force := vadd (vcross c_curl c_B) (vscale (- jmu0pp j) c_gs).

(** The derivatives of the covariant components the formulas carry are those
    of B . e_i along the lines. *)
Lemma cov_coords :
  f_B_s_u j = vdot c_Bu c_es + vdot c_B c_esu /\
  f_B_u_s j = vdot c_Bs c_eu + vdot c_B c_esu /\
  f_B_s_v j = vdot c_Bv c_es + vdot c_B c_esv /\
  f_B_v_s j = vdot c_Bs c_ev + vdot c_B c_esv /\
  f_B_u_v j = vdot c_Bv c_eu + vdot c_B c_euv /\
  f_B_v_u j = vdot c_Bu c_ev + vdot c_B c_euv.
Proof.
  unfold f_B_s_u, f_B_u_s, f_B_s_v, f_B_v_s, f_B_u_v, f_B_v_u, f_dcov,
    f_guu, f_guv, f_gvv, f_gsu, f_gsv, f_guu_s, f_guv_s, f_gvv_s, f_gsu_u, f_gsu_v, f_gsv_u,
    f_gsv_v, f_guu_v, f_guv_u, f_guv_v, f_gvv_u,
    c_Bs, c_Bu, c_Bv, c_dB, c_B, c_es, c_eu, c_ev, c_esu, c_esv, c_euu, c_euv, c_evv,
    vdot, vadd, vscale.
  cbn [vx vy vz].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); ring.
Qed.

(** e_s . (e_u x e_v) is the Jacobian. *)
Lemma triple_coords : vdot (vcross c_eu c_ev) c_es = f_sqrtg j.
Proof.
  unfold vdot, vcross, c_es, c_eu, c_ev, f_sqrtg, f_tau. cbn [vx vy vz]. ring.
Qed.

Theorem force_coords :
  f_sqrtg j <> 0 ->
  vdot c_force c_es = cres_s j /\ vdot c_force c_eu = cres_u j /\ vdot c_force c_ev = cres_v j.
Proof.
  intros Hsg.
  destruct cov_coords as (Csu & Cus & Csv & Cvs & Cuv & Cvu).
  unfold cres_s, cres_u, cres_v, f_mu0Js.
  rewrite Csu, Cus, Csv, Cvs, Cuv, Cvu.
  unfold c_force, c_curl, c_gs, c_gu, c_gv, c_Bs, c_Bu, c_Bv, c_dB, c_B,
    c_es, c_eu, c_ev, c_esu, c_esv, c_euu, c_euv, c_evv, vdot, vcross, vadd, vscale.
  cbn [vx vy vz].
  unfold f_sqrtg, f_tau in *.
  destruct (Rmult_neq_0_reg _ _ Hsg) as [HR Ht].
  refine (conj _ (conj _ _)); field; repeat split; assumption.
Qed.

End Coordinates.

(** * The force law *)

Section Continuum.

(** R, Z and lambda as functions of (s, u, v), their first partial
    derivatives as functions, and the jet at the point (s0, u0, v0). *)
Variables (FR FZ FRs FRu FRv FZs FZu FZv FLu FLv : R -> R -> R -> R) (iota p : R -> R).
Variables (phip mu0 s0 u0 v0 : R).
Variables (Rss Rsu Rsv Ruu Ruv Rvv Zss Zsu Zsv Zuu Zuv Zvv Lsu Lsv Luu Luv Lvv iotap pp : R).

(** Partial derivatives at the point, along the three coordinate lines. *)
Definition lines3 (F : R -> R -> R -> R) (ds du dv : R) : Prop :=
  is_derive (fun t => F t u0 v0) s0 ds /\ is_derive (fun t => F s0 t v0) u0 du /\
  is_derive (fun t => F s0 u0 t) v0 dv.

Hypothesis HR : lines3 FR (FRs s0 u0 v0) (FRu s0 u0 v0) (FRv s0 u0 v0).
Hypothesis HRs : lines3 FRs Rss Rsu Rsv.
Hypothesis HRu : lines3 FRu Rsu Ruu Ruv.
Hypothesis HRv : lines3 FRv Rsv Ruv Rvv.
Hypothesis HZ : lines3 FZ (FZs s0 u0 v0) (FZu s0 u0 v0) (FZv s0 u0 v0).
Hypothesis HZs : lines3 FZs Zss Zsu Zsv.
Hypothesis HZu : lines3 FZu Zsu Zuu Zuv.
Hypothesis HZv : lines3 FZv Zsv Zuv Zvv.
Hypothesis HLu : lines3 FLu Lsu Luu Luv.
Hypothesis HLv : lines3 FLv Lsv Luv Lvv.
Hypothesis Hiota : is_derive iota s0 iotap.
Hypothesis Hp : is_derive p s0 pp.

(** The embedding, the Jacobian and the field. *)
Definition emb (s u v : R) : R * R * R := (FR s u v * cos v, FR s u v * sin v, FZ s u v).
Definition sqrtg (s u v : R) : R := FR s u v * (FRu s u v * FZs s u v - FRs s u v * FZu s u v).
Definition Bup (s u v : R) : R := phip * (iota s - FLv s u v) / sqrtg s u v.
Definition Bvp (s u v : R) : R := phip * (1 + FLu s u v) / sqrtg s u v.
Definition Bc1 (s u v : R) : R := Bup s u v * (FRu s u v * cos v) + Bvp s u v * (FRv s u v * cos v - FR s u v * sin v).
Definition Bc2 (s u v : R) : R := Bup s u v * (FRu s u v * sin v) + Bvp s u v * (FRv s u v * sin v + FR s u v * cos v).
Definition Bc3 (s u v : R) : R := Bup s u v * FZu s u v + Bvp s u v * FZv s u v.

Hypothesis Hsg : sqrtg s0 u0 v0 <> 0.

(** The Cartesian field and pressure: differentiable at the point, equal to
    the field and to p(s) along the three coordinate lines through it. *)
Variables (G1 G2 G3 P : R * R * R -> R).
Variables (a11 a12 a13 a21 a22 a23 a31 a32 a33 q1 q2 q3 : R).
Hypothesis HG1 : filterdiff G1 (locally (emb s0 u0 v0)) (lin3 a11 a12 a13).
Hypothesis HG2 : filterdiff G2 (locally (emb s0 u0 v0)) (lin3 a21 a22 a23).
Hypothesis HG3 : filterdiff G3 (locally (emb s0 u0 v0)) (lin3 a31 a32 a33).
Hypothesis HP : filterdiff P (locally (emb s0 u0 v0)) (lin3 q1 q2 q3).

Definition represents (x : R -> R * R * R) (b1 b2 b3 pr : R -> R) (t0 : R) : Prop :=
  locally t0 (fun t => G1 (x t) = b1 t /\ G2 (x t) = b2 t /\ G3 (x t) = b3 t /\ P (x t) = pr t).

Hypothesis Hs_line : represents (fun t => emb t u0 v0) (fun t => Bc1 t u0 v0) (fun t => Bc2 t u0 v0)
                       (fun t => Bc3 t u0 v0) p s0.
Hypothesis Hu_line : represents (fun t => emb s0 t v0) (fun t => Bc1 s0 t v0) (fun t => Bc2 s0 t v0)
                       (fun t => Bc3 s0 t v0) (fun _ => p s0) u0.
Hypothesis Hv_line : represents (fun t => emb s0 u0 t) (fun t => Bc1 s0 u0 t) (fun t => Bc2 s0 u0 t)
                       (fun t => Bc3 s0 u0 t) (fun _ => p s0) v0.

(** The jet of the reconstruction at the point. *)
Definition jet0 : jet :=
  Jet (FR s0 u0 v0) (FRs s0 u0 v0) (FRu s0 u0 v0) (FRv s0 u0 v0)
      Rss Rsu Rsv Ruu Ruv Rvv
      (FZs s0 u0 v0) (FZu s0 u0 v0) (FZv s0 u0 v0)
      Zss Zsu Zsv Zuu Zuv Zvv
      (FLu s0 u0 v0) (FLv s0 u0 v0) Lsu Lsv Luu Luv Lvv
      (iota s0) iotap phip (mu0 * pp).

(** The derivative of the covariant component B . e_i along e_j, in the form
    the chain rule through G gives: (A e_j) . e_i + G . d_j e_i. *)
Definition Dform (x1 x2 x3 e1 e2 e3 d1 d2 d3 : R) : R :=
  (a11 * x1 + a12 * x2 + a13 * x3) * e1 + G1 (emb s0 u0 v0) * d1
  + ((a21 * x1 + a22 * x2 + a23 * x3) * e2 + G2 (emb s0 u0 v0) * d2)
  + ((a31 * x1 + a32 * x2 + a33 * x3) * e3 + G3 (emb s0 u0 v0) * d3).

(** The coordinate vectors at the point and their mixed derivatives, which
    are symmetric: d_u e_s = d_s e_u, d_v e_s = d_s e_v, d_v e_u = d_u e_v. *)
Definition es1 := FRs s0 u0 v0 * cos v0.
Definition es2 := FRs s0 u0 v0 * sin v0.
Definition es3 := FZs s0 u0 v0.
Definition eu1 := FRu s0 u0 v0 * cos v0.
Definition eu2 := FRu s0 u0 v0 * sin v0.
Definition eu3 := FZu s0 u0 v0.
Definition ev1 := FRv s0 u0 v0 * cos v0 - FR s0 u0 v0 * sin v0.
Definition ev2 := FRv s0 u0 v0 * sin v0 + FR s0 u0 v0 * cos v0.
Definition ev3 := FZv s0 u0 v0.
Definition dsu1 := Rsu * cos v0.
Definition dsu2 := Rsu * sin v0.
Definition dsv1 := Rsv * cos v0 - FRs s0 u0 v0 * sin v0.
Definition dsv2 := Rsv * sin v0 + FRs s0 u0 v0 * cos v0.
Definition duv1 := Ruv * cos v0 - FRu s0 u0 v0 * sin v0.
Definition duv2 := Ruv * sin v0 + FRu s0 u0 v0 * cos v0.

Lemma D_idR (x : R) : is_derive (fun t => t) x 1.
Proof. exact (is_derive_id x). Qed.

Lemma Hsg_R : FR s0 u0 v0 <> 0.
Proof. intros E. apply Hsg. unfold sqrtg. rewrite E. ring. Qed.

Lemma Hsg_tau : FRu s0 u0 v0 * FZs s0 u0 v0 - FRs s0 u0 v0 * FZu s0 u0 v0 <> 0.
Proof. intros E. apply Hsg. unfold sqrtg. rewrite E. ring. Qed.

Ltac agree3 H :=
  eapply filter_imp; [| exact H]; intros ?t [?A1 [?A2 [?A3 _]]];
  split; [assumption | split; assumption].
Ltac agreeP H := eapply filter_imp; [| exact H]; intros ?t [_ [_ [_ ?A4]]]; assumption.

Ltac close_formula := unfold f_B_s_u, f_B_u_s, f_B_s_v, f_B_v_s, f_B_u_v, f_B_v_u, f_dcov,
  f_guu, f_guv, f_gvv, f_gsu, f_gsv, f_guu_s, f_guv_s, f_gvv_s, f_gsu_u, f_gsu_v, f_gsv_u, f_gsv_v,
  f_guu_v, f_guv_u, f_guv_v, f_gvv_u, f_Bu, f_Bv, f_Bu_s, f_Bv_s, f_Bu_u, f_Bv_u, f_Bu_v, f_Bv_v,
  f_dB, f_g2, f_bu_num, f_bv_num, f_g_s, f_g_u, f_g_v, f_tau_s, f_tau_u, f_tau_v, f_sqrtg, f_tau,
  jet0, l_bu, l_bv, d_bu, d_bv, l_sg, d_sg, d_tau; cbn [jR jRs jRu jRv jRss jRsu jRsv jRuu jRuv jRvv
  jZs jZu jZv jZss jZsu jZsv jZuu jZuv jZvv jLu jLv jLsu jLsv jLuu jLuv jLvv jiota jiotap jphip jmu0pp];
  cbv beta; field; repeat split; first [exact Hsg_R | exact Hsg_tau | (unfold sqrtg in Hsg; exact Hsg)].

Ltac close_chain := unfold Dform, d_x1, d_x2, d_es1, d_es2, d_eu1, d_eu2, d_ev1, d_ev2,
  l_es1, l_es2, l_es3, l_eu1, l_eu2, l_eu3, l_ev1, l_ev2, l_ev3,
  es1, es2, es3, eu1, eu2, eu3, ev1, ev2, ev3, dsu1, dsu2, dsv1, dsv2, duv1, duv2, l_x, emb;
  cbv beta; ring.

Ltac via H := match type of H with ?L = ?Rr => transitivity L; [| transitivity Rr; [exact H |]] end.

(** d_u B_s, from the line along u. *)
Lemma E_s_u : f_B_s_u jet0 = Dform eu1 eu2 eu3 es1 es2 es3 dsu1 dsu2 Zsu.
Proof.
  pose proof (cov_s_chain _ _ _ _ _ _ _ _ _ _ _ _ phip u0 _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 (proj2 HR)) (proj1 (proj2 HRs)) (proj1 (proj2 HRu)) (proj1 (proj2 HRv))
    (proj1 (proj2 HZ)) (proj1 (proj2 HZs)) (proj1 (proj2 HZu)) (proj1 (proj2 HZv))
    (proj1 (proj2 HLu)) (proj1 (proj2 HLv)) (D_const (iota s0) u0) (D_const v0 u0) Hsg
    G1 G2 G3 a11 a12 a13 a21 a22 a23 a31 a32 a33 HG1 HG2 HG3 ltac:(agree3 Hu_line)) as H.
  via H; [close_formula | close_chain].
Qed.

(** d_s B_u, from the line along s. *)
Lemma E_u_s : f_B_u_s jet0 = Dform es1 es2 es3 eu1 eu2 eu3 dsu1 dsu2 Zsu.
Proof.
  pose proof (cov_u_chain _ _ _ _ _ _ _ _ _ _ _ _ phip s0 _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 HR) (proj1 HRs) (proj1 HRu) (proj1 HRv) (proj1 HZ) (proj1 HZs) (proj1 HZu) (proj1 HZv)
    (proj1 HLu) (proj1 HLv) Hiota (D_const v0 s0) Hsg
    G1 G2 G3 a11 a12 a13 a21 a22 a23 a31 a32 a33 HG1 HG2 HG3 ltac:(agree3 Hs_line)) as H.
  via H; [close_formula | close_chain].
Qed.

(** d_v B_s, from the line along v. *)
Lemma E_s_v : f_B_s_v jet0 = Dform ev1 ev2 ev3 es1 es2 es3 dsv1 dsv2 Zsv.
Proof.
  pose proof (cov_s_chain _ _ _ _ _ _ _ _ _ _ _ _ phip v0 _ _ _ _ _ _ _ _ _ _ _ _
    (proj2 (proj2 HR)) (proj2 (proj2 HRs)) (proj2 (proj2 HRu)) (proj2 (proj2 HRv))
    (proj2 (proj2 HZ)) (proj2 (proj2 HZs)) (proj2 (proj2 HZu)) (proj2 (proj2 HZv))
    (proj2 (proj2 HLu)) (proj2 (proj2 HLv)) (D_const (iota s0) v0) (D_idR v0) Hsg
    G1 G2 G3 a11 a12 a13 a21 a22 a23 a31 a32 a33 HG1 HG2 HG3 ltac:(agree3 Hv_line)) as H.
  via H; [close_formula | close_chain].
Qed.

(** d_s B_v, from the line along s. *)
Lemma E_v_s : f_B_v_s jet0 = Dform es1 es2 es3 ev1 ev2 ev3 dsv1 dsv2 Zsv.
Proof.
  pose proof (cov_v_chain _ _ _ _ _ _ _ _ _ _ _ _ phip s0 _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 HR) (proj1 HRs) (proj1 HRu) (proj1 HRv) (proj1 HZ) (proj1 HZs) (proj1 HZu) (proj1 HZv)
    (proj1 HLu) (proj1 HLv) Hiota (D_const v0 s0) Hsg
    G1 G2 G3 a11 a12 a13 a21 a22 a23 a31 a32 a33 HG1 HG2 HG3 ltac:(agree3 Hs_line)) as H.
  via H; [close_formula | close_chain].
Qed.

(** d_v B_u, from the line along v. *)
Lemma E_u_v : f_B_u_v jet0 = Dform ev1 ev2 ev3 eu1 eu2 eu3 duv1 duv2 Zuv.
Proof.
  pose proof (cov_u_chain _ _ _ _ _ _ _ _ _ _ _ _ phip v0 _ _ _ _ _ _ _ _ _ _ _ _
    (proj2 (proj2 HR)) (proj2 (proj2 HRs)) (proj2 (proj2 HRu)) (proj2 (proj2 HRv))
    (proj2 (proj2 HZ)) (proj2 (proj2 HZs)) (proj2 (proj2 HZu)) (proj2 (proj2 HZv))
    (proj2 (proj2 HLu)) (proj2 (proj2 HLv)) (D_const (iota s0) v0) (D_idR v0) Hsg
    G1 G2 G3 a11 a12 a13 a21 a22 a23 a31 a32 a33 HG1 HG2 HG3 ltac:(agree3 Hv_line)) as H.
  via H; [close_formula | close_chain].
Qed.

(** d_u B_v, from the line along u. *)
Lemma E_v_u : f_B_v_u jet0 = Dform eu1 eu2 eu3 ev1 ev2 ev3 duv1 duv2 Zuv.
Proof.
  pose proof (cov_v_chain _ _ _ _ _ _ _ _ _ _ _ _ phip u0 _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 (proj2 HR)) (proj1 (proj2 HRs)) (proj1 (proj2 HRu)) (proj1 (proj2 HRv))
    (proj1 (proj2 HZ)) (proj1 (proj2 HZs)) (proj1 (proj2 HZu)) (proj1 (proj2 HZv))
    (proj1 (proj2 HLu)) (proj1 (proj2 HLv)) (D_const (iota s0) u0) (D_const v0 u0) Hsg
    G1 G2 G3 a11 a12 a13 a21 a22 a23 a31 a32 a33 HG1 HG2 HG3 ltac:(agree3 Hu_line)) as H.
  via H; [close_formula | close_chain].
Qed.

(** G at the point is the reconstructed field there. *)
Lemma E_G :
  G1 (emb s0 u0 v0) = f_Bu jet0 * eu1 + f_Bv jet0 * ev1 /\
  G2 (emb s0 u0 v0) = f_Bu jet0 * eu2 + f_Bv jet0 * ev2 /\
  G3 (emb s0 u0 v0) = f_Bu jet0 * eu3 + f_Bv jet0 * ev3.
Proof.
  destruct (G_at_t0 (fun t => FR t u0 v0) (fun t => FRs t u0 v0) (fun t => FRu t u0 v0)
              (fun t => FRv t u0 v0) (fun t => FZ t u0 v0) (fun t => FZs t u0 v0) (fun t => FZu t u0 v0)
              (fun t => FZv t u0 v0) (fun t => FLu t u0 v0) (fun t => FLv t u0 v0) iota (fun _ => v0)
              phip s0 G1 G2 G3 ltac:(agree3 Hs_line)) as [A1 [A2 A3]].
  refine (conj _ (conj _ _)); [etransitivity; [exact A1 |] | etransitivity; [exact A2 |]
                                | etransitivity; [exact A3 |]];
    unfold l_B1, l_B2, l_B3, l_bu, l_bv, l_sg, l_eu1, l_eu2, l_eu3, l_ev1, l_ev2, l_ev3,
      f_Bu, f_Bv, f_bu_num, f_bv_num, f_sqrtg, f_tau, jet0, eu1, eu2, eu3, ev1, ev2, ev3;
    cbn [jR jRs jRu jRv jZs jZu jZv jLu jLv jiota jphip]; reflexivity.
Qed.

(** The pressure gradient along the three coordinate directions. *)
Lemma E_P :
  q1 * es1 + q2 * es2 + q3 * es3 = pp /\ q1 * eu1 + q2 * eu2 + q3 * eu3 = 0 /\
  q1 * ev1 + q2 * ev2 + q3 * ev3 = 0.
Proof.
  pose proof (grad_by_line (fun t => FR t u0 v0) (fun t => FZ t u0 v0) (fun _ => v0) s0 _ _ _
    (proj1 HR) (proj1 HZ) (D_const v0 s0) P q1 q2 q3 p pp HP ltac:(agreeP Hs_line) Hp) as Hs.
  pose proof (grad_by_line (fun t => FR s0 t v0) (fun t => FZ s0 t v0) (fun _ => v0) u0 _ _ _
    (proj1 (proj2 HR)) (proj1 (proj2 HZ)) (D_const v0 u0) P q1 q2 q3 (fun _ => p s0) 0 HP
    ltac:(agreeP Hu_line) (D_const (p s0) u0)) as Hu.
  pose proof (grad_by_line (fun t => FR s0 u0 t) (fun t => FZ s0 u0 t) (fun t => t) v0 _ _ _
    (proj2 (proj2 HR)) (proj2 (proj2 HZ)) (D_idR v0) P q1 q2 q3 (fun _ => p s0) 0 HP
    ltac:(agreeP Hv_line) (D_const (p s0) v0)) as Hv.
  unfold d_x1, d_x2 in Hs, Hu, Hv. unfold es1, es2, es3, eu1, eu2, eu3, ev1, ev2, ev3.
  refine (conj _ (conj _ _)).
  - rewrite <- Hs. ring.
  - rewrite <- Hu. ring.
  - rewrite <- Hv. ring.
Qed.

(** The frame at the toroidal angle of the point, turned into the Cartesian
    frame. *)
Definition rotx (w : vec) : R := cos v0 * vx w - sin v0 * vy w.
Definition roty (w : vec) : R := sin v0 * vx w + cos v0 * vy w.

Ltac close_line := unfold d_B1, d_B2, d_B3, d_bu, d_bv, d_sg, d_tau, d_eu1, d_eu2, d_ev1, d_ev2,
  l_bu, l_bv, l_sg, l_eu1, l_eu2, l_eu3, l_ev1, l_ev2, l_ev3,
  rotx, roty, c_Bs, c_Bu, c_Bv, c_dB, c_eu, c_ev, c_esu, c_esv, c_euu, c_euv, c_evv, vadd, vscale,
  f_Bu, f_Bv, f_Bu_s, f_Bv_s, f_Bu_u, f_Bv_u, f_Bu_v, f_Bv_v, f_dB, f_g2, f_bu_num, f_bv_num,
  f_g_s, f_g_u, f_g_v, f_tau_s, f_tau_u, f_tau_v, f_sqrtg, f_tau, jet0;
  cbn [vx vy vz jR jRs jRu jRv jRss jRsu jRsv jRuu jRuv jRvv jZs jZu jZv jZss jZsu jZsv jZuu jZuv
       jZvv jLu jLv jLsu jLsv jLuu jLuv jLvv jiota jiotap jphip jmu0pp];
  cbv beta; field; repeat split; first [exact Hsg_R | exact Hsg_tau | (unfold sqrtg in Hsg; exact Hsg)].

Ltac fit H W := match type of H with is_derive _ _ ?X => replace W with X; [exact H | close_line] end.

(** The derivatives of the field along the three coordinate lines, in the
    Cartesian frame, are [c_Bs], [c_Bu] and [c_Bv] of the jet, turned by the
    toroidal angle. *)
Lemma lines_coords :
  (is_derive (fun t => Bc1 t u0 v0) s0 (rotx (c_Bs jet0)) /\
   is_derive (fun t => Bc2 t u0 v0) s0 (roty (c_Bs jet0)) /\
   is_derive (fun t => Bc3 t u0 v0) s0 (vz (c_Bs jet0))) /\
  (is_derive (fun t => Bc1 s0 t v0) u0 (rotx (c_Bu jet0)) /\
   is_derive (fun t => Bc2 s0 t v0) u0 (roty (c_Bu jet0)) /\
   is_derive (fun t => Bc3 s0 t v0) u0 (vz (c_Bu jet0))) /\
  (is_derive (fun t => Bc1 s0 u0 t) v0 (rotx (c_Bv jet0)) /\
   is_derive (fun t => Bc2 s0 u0 t) v0 (roty (c_Bv jet0)) /\
   is_derive (fun t => Bc3 s0 u0 t) v0 (vz (c_Bv jet0))).
Proof.
  destruct (D_B _ _ _ _ _ _ _ _ _ _ _ phip s0 _ _ _ _ _ _ _ _ _ _ _
              (proj1 HR) (proj1 HRs) (proj1 HRu) (proj1 HRv) (proj1 HZs) (proj1 HZu) (proj1 HZv)
              (proj1 HLu) (proj1 HLv) Hiota (D_const v0 s0) Hsg) as (S1 & S2 & S3).
  destruct (D_B _ _ _ _ _ _ _ _ _ _ _ phip u0 _ _ _ _ _ _ _ _ _ _ _
              (proj1 (proj2 HR)) (proj1 (proj2 HRs)) (proj1 (proj2 HRu)) (proj1 (proj2 HRv))
              (proj1 (proj2 HZs)) (proj1 (proj2 HZu)) (proj1 (proj2 HZv))
              (proj1 (proj2 HLu)) (proj1 (proj2 HLv)) (D_const (iota s0) u0) (D_const v0 u0) Hsg)
    as (U1 & U2 & U3).
  destruct (D_B _ _ _ _ _ _ _ _ _ _ _ phip v0 _ _ _ _ _ _ _ _ _ _ _
              (proj2 (proj2 HR)) (proj2 (proj2 HRs)) (proj2 (proj2 HRu)) (proj2 (proj2 HRv))
              (proj2 (proj2 HZs)) (proj2 (proj2 HZu)) (proj2 (proj2 HZv))
              (proj2 (proj2 HLu)) (proj2 (proj2 HLv)) (D_const (iota s0) v0) (D_idR v0) Hsg)
    as (V1 & V2 & V3).
  refine (conj (conj _ (conj _ _)) (conj (conj _ (conj _ _)) (conj _ (conj _ _)))).
  - fit S1 (rotx (c_Bs jet0)).
  - fit S2 (roty (c_Bs jet0)).
  - fit S3 (vz (c_Bs jet0)).
  - fit U1 (rotx (c_Bu jet0)).
  - fit U2 (roty (c_Bu jet0)).
  - fit U3 (vz (c_Bu jet0)).
  - fit V1 (rotx (c_Bv jet0)).
  - fit V2 (roty (c_Bv jet0)).
  - fit V3 (vz (c_Bv jet0)).
Qed.

Theorem force_law :
  let G01 := G1 (emb s0 u0 v0) in let G02 := G2 (emb s0 u0 v0) in let G03 := G3 (emb s0 u0 v0) in
  let w1 := a32 - a23 in let w2 := a13 - a31 in let w3 := a21 - a12 in
  let F1 := (w2 * G03 - w3 * G02) - mu0 * q1 in
  let F2 := (w3 * G01 - w1 * G03) - mu0 * q2 in
  let F3 := (w1 * G02 - w2 * G01) - mu0 * q3 in
  let c := cos v0 in let sn := sin v0 in
  dot3 F1 F2 F3 (FRs s0 u0 v0 * c) (FRs s0 u0 v0 * sn) (FZs s0 u0 v0) = cres_s jet0 /\
  dot3 F1 F2 F3 (FRu s0 u0 v0 * c) (FRu s0 u0 v0 * sn) (FZu s0 u0 v0) = cres_u jet0 /\
  dot3 F1 F2 F3 (FRv s0 u0 v0 * c - FR s0 u0 v0 * sn) (FRv s0 u0 v0 * sn + FR s0 u0 v0 * c)
       (FZv s0 u0 v0) = cres_v jet0.
Proof.
  cbv zeta.
  destruct E_G as [EG1 [EG2 EG3]].
  destruct E_P as [EPs [EPu EPv]].
  unfold cres_s, cres_u, cres_v, f_mu0Js.
  rewrite E_s_u, E_u_s, E_s_v, E_v_s, E_u_v, E_v_u.
  change (jmu0pp jet0) with (mu0 * pp).
  change (FRs s0 u0 v0 * cos v0) with es1. change (FRs s0 u0 v0 * sin v0) with es2.
  change (FZs s0 u0 v0) with es3.
  change (FRu s0 u0 v0 * cos v0) with eu1. change (FRu s0 u0 v0 * sin v0) with eu2.
  change (FZu s0 u0 v0) with eu3.
  change (FRv s0 u0 v0 * cos v0 - FR s0 u0 v0 * sin v0) with ev1.
  change (FRv s0 u0 v0 * sin v0 + FR s0 u0 v0 * cos v0) with ev2.
  change (FZv s0 u0 v0) with ev3.
  unfold Dform. rewrite EG1, EG2, EG3. rewrite <- EPs.
  refine (conj _ (conj _ _)).
  - unfold dot3. ring.
  - match goal with |- ?L = ?Rr => transitivity (Rr - mu0 * (q1 * eu1 + q2 * eu2 + q3 * eu3)) end.
    + unfold dot3. ring.
    + rewrite EPu. ring.
  - match goal with |- ?L = ?Rr => transitivity (Rr - mu0 * (q1 * ev1 + q2 * ev2 + q3 * ev3)) end.
    + unfold dot3. ring.
    + rewrite EPv. ring.
Qed.

End Continuum.
