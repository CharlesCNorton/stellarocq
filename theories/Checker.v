(** The certificate checker and its correctness theorem.

    A certificate is a list of evaluation points. Each point carries the
    integer mantissas and power-of-two exponents of every environment entry,
    exact images of the IEEE doubles in a wout file, together with claimed
    per-component bounds N * 2^q on the mu0-scaled force residual, and the
    working precision of the interval arithmetic.

    [check_cert] extends the environment of each point by the bindings of
    Physics.v, evaluates the three residual components with the sound
    interval evaluator, and tests |r| <= N * 2^q through the signs of
    (eps - r) and (r + eps). The theorem [check_cert_correct] states that a
    [true] verdict proves, for every point, that the residual expressions
    denote real numbers whose absolute values obey the claimed bounds. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics.

Import ListNotations.

Open Scope Z_scope.

(* ---------------------------------------------------------------- *)
(* Certificates                                                      *)

(** One evaluation point: mantissas and exponents of its environment. *)
Record cpoint := CPoint {
  pt_ms : list Z ;
  pt_es : list Z
}.

(** A certificate: working precision in bits, mode numbers, three claimed
    bounds, evaluation points. *)
Record cert := Cert {
  c_prec : Z ;
  c_cfg : pconfig ;
  c_modes : list (Z * Z) ;
  c_NS : Z ; c_qS : Z ;
  c_NU : Z ; c_qU : Z ;
  c_NV : Z ; c_qV : Z ;
  c_points : list cpoint
}.

(** Working precision of the interval arithmetic of a certificate. *)
Definition prec_of (c : cert) : F.precision := F.PtoP (Z.to_pos (c_prec c)).

(* ---------------------------------------------------------------- *)
(* The boolean check                                                 *)

(** Interval environment: one exact point interval per mantissa. *)
Definition ienv_of (prec : F.precision) (ms : list Z) : env I.type :=
  of_list (map (I.fromZ prec) ms).

(** Extended-real environment: the same mantissas as real numbers. *)
Definition xenv_of (ms : list Z) : env ExtendedR :=
  of_list (map (fun z => Xreal (IZR z)) ms).

(** True when the interval is known to contain only nonnegative reals. *)
Definition nonneg (xi : I.type) : bool :=
  match I.sign_large xi with
  | Xgt | Xeq => true
  | _ => false
  end.

(** The claimed bound N * 2^q as an expression. *)
Definition eps_e (N q : Z) : expr := Emul (EfromZ N) (epow2 q).

(** Check |r| <= N * 2^q by the signs of (eps - r) and (r + eps). *)
Definition check1 (prec : F.precision) (ienv : env I.type) (r : expr)
    (N q : Z) : bool :=
  nonneg (ieval prec ienv (Esub (eps_e N q) r)) &&
  nonneg (ieval prec ienv (Eadd r (eps_e N q))).

(** Check the three residual components of one point. *)
Definition check_point (c : cert) (p : cpoint) : bool :=
  let prec := prec_of c in
  let r3 := residual (pt_es p) (c_cfg c) (c_modes c) in
  let ienv := iextend prec (ienv_of prec (pt_ms p)) (r_binds r3) in
  check1 prec ienv (r_s r3) (c_NS c) (c_qS c) &&
  check1 prec ienv (r_u r3) (c_NU c) (c_qU c) &&
  check1 prec ienv (r_v r3) (c_NV c) (c_qV c).

(** Check every point of a certificate. *)
Definition check_cert (c : cert) : bool :=
  forallb (check_point c) (c_points c).

(* ---------------------------------------------------------------- *)
(* Facts about the environment                                       *)

(** The two environments built from the same mantissas satisfy env_ok. *)
Lemma env_ok_fromZ :
  forall prec ms, env_ok (ienv_of prec ms) (xenv_of ms).
Proof.
  intros prec ms n.
  unfold ienv_of, xenv_of. rewrite !eget_of_list.
  revert ms.
  induction n as [|n IH]; intros [|z ms]; simpl.
  - rewrite ?I.nai_correct. exact I.
  - apply I.fromZ_correct.
  - rewrite ?I.nai_correct. exact I.
  - apply IH.
Qed.

(* ---------------------------------------------------------------- *)
(* The value of epow2                                                *)

(** Multiplication of extended reals on real arguments. *)
Lemma Xmul_real :
  forall a b, Xmul (Xreal a) (Xreal b) = Xreal (a * b)%R.
Proof. reflexivity. Qed.

(** The power expression evaluates to the real power of two. *)
Lemma xeval_epow2 :
  forall env e, xeval env (epow2 e) = Xreal (powerRZ 2%R e).
Proof. reflexivity. Qed.

(** The bound expression evaluates to the real number N * 2^q. *)
Lemma xeval_eps_e :
  forall env N q,
  xeval env (eps_e N q) = Xreal (IZR N * powerRZ 2%R q).
Proof.
  intros env N q. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* From the boolean check to real bounds                             *)

(** A nonneg verdict on a containing interval yields a nonnegative real. *)
Lemma nonneg_correct :
  forall xi v,
  contains (I.convert xi) v ->
  nonneg xi = true ->
  exists r, v = Xreal r /\ (0 <= r)%R.
Proof.
  intros xi v Hc.
  unfold nonneg.
  generalize (I.sign_large_correct xi).
  case (I.sign_large xi); intros H Ht; try discriminate Ht.
  - exists 0%R. split. now apply H. lra.
  - destruct (H v Hc) as [Hr Hle].
    exists (proj_val v). now split.
Qed.

(** A real-valued subtraction has real-valued operands. *)
Lemma Xsub_real :
  forall a b z, Xsub a b = Xreal z ->
  exists x y, a = Xreal x /\ b = Xreal y /\ z = (x - y)%R.
Proof.
  intros [|x] [|y] z H; simpl in H; try discriminate.
  injection H as <-. eauto.
Qed.

(** A real-valued addition has real-valued operands. *)
Lemma Xadd_real :
  forall a b z, Xadd a b = Xreal z ->
  exists x y, a = Xreal x /\ b = Xreal y /\ z = (x + y)%R.
Proof.
  intros [|x] [|y] z H; simpl in H; try discriminate.
  injection H as <-. eauto.
Qed.

(** A passing check1 on contained environments proves the expression is
    real and within the bound. *)
Lemma check1_correct :
  forall prec ienv xenv r N q,
  env_ok ienv xenv ->
  check1 prec ienv r N q = true ->
  exists x,
    xeval xenv r = Xreal x /\
    (Rabs x <= IZR N * powerRZ 2%R q)%R.
Proof.
  intros prec ienv xenv r N q Henv Hchk.
  apply andb_prop in Hchk. destruct Hchk as [H1 H2].
  assert (Hc1 := ieval_correct prec _ _ (Esub (eps_e N q) r) Henv).
  destruct (nonneg_correct _ _ Hc1 H1) as [d1 [Hd1 Hge1]].
  change (Xsub (xeval xenv (eps_e N q)) (xeval xenv r) = Xreal d1) in Hd1.
  rewrite xeval_eps_e in Hd1.
  destruct (Xsub_real _ _ _ Hd1) as [eps1 [x1 [He1 [Hx1 Hv1]]]].
  injection He1 as <-.
  assert (Hc2 := ieval_correct prec _ _ (Eadd r (eps_e N q)) Henv).
  destruct (nonneg_correct _ _ Hc2 H2) as [d2 [Hd2 Hge2]].
  change (Xadd (xeval xenv r) (xeval xenv (eps_e N q)) = Xreal d2) in Hd2.
  rewrite xeval_eps_e in Hd2.
  destruct (Xadd_real _ _ _ Hd2) as [x2 [eps2 [Hx2 [He2 Hv2]]]].
  injection He2 as <-.
  rewrite Hx1 in Hx2. injection Hx2 as <-.
  exists x1. split. exact Hx1.
  apply Rabs_le. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Main theorem                                                      *)

(** The extended-real environment of a point: its mantissas as reals,
    extended by the bindings of the residual. *)
Definition point_env (c : cert) (p : cpoint) : env ExtendedR :=
  xextend (xenv_of (pt_ms p)) (r_binds (residual (pt_es p) (c_cfg c) (c_modes c))).

(** What a passing verdict means for one point: three real values, bounded. *)
Definition point_sound (c : cert) (p : cpoint) : Prop :=
  let r3 := residual (pt_es p) (c_cfg c) (c_modes c) in
  let env := point_env c p in
  (exists x, xeval env (r_s r3) = Xreal x /\
             (Rabs x <= IZR (c_NS c) * powerRZ 2%R (c_qS c))%R) /\
  (exists x, xeval env (r_u r3) = Xreal x /\
             (Rabs x <= IZR (c_NU c) * powerRZ 2%R (c_qU c))%R) /\
  (exists x, xeval env (r_v r3) = Xreal x /\
             (Rabs x <= IZR (c_NV c) * powerRZ 2%R (c_qV c))%R).

(* ---------------------------------------------------------------- *)
(* The reversed check: bounded away from zero                        *)

(** True when |r| >= N 2^q, proven by showing the enclosure sits at or above
    the bound, or at or below its negation. An enclosure straddling zero
    proves neither and the check fails.

    Where [check1] certifies that a residual component is small, this
    certifies that one is not. A point where some component of the force
    residual is bounded away from zero is a point where the reconstructed
    field is not in equilibrium, by the stated margin, and no refinement of
    the arithmetic can change that. Over a cell it is an obstruction: no
    field of this form balances there. *)
Definition check1_lower (prec : F.precision) (ienv : env I.type) (r : expr)
    (N q : Z) : bool :=
  nonneg (ieval prec ienv (Esub r (eps_e N q))) ||
  nonneg (ieval prec ienv (Esub (Eneg r) (eps_e N q))).

(** A point is not balanced when some component is bounded away from zero. *)
Definition check_point_lower (c : cert) (p : cpoint) : bool :=
  let prec := prec_of c in
  let r3 := residual (pt_es p) (c_cfg c) (c_modes c) in
  let ienv := iextend prec (ienv_of prec (pt_ms p)) (r_binds r3) in
  check1_lower prec ienv (r_s r3) (c_NS c) (c_qS c) ||
  check1_lower prec ienv (r_u r3) (c_NU c) (c_qU c) ||
  check1_lower prec ienv (r_v r3) (c_NV c) (c_qV c).

(** Every point of the certificate is out of balance. *)
Definition check_cert_lower (c : cert) : bool :=
  forallb (check_point_lower c) (c_points c).

(** A passing reversed check proves the expression is real and at least the
    claimed size. *)
Lemma check1_lower_correct :
  forall prec ienv xenv r N q,
  env_ok ienv xenv ->
  check1_lower prec ienv r N q = true ->
  exists x,
    xeval xenv r = Xreal x /\
    (IZR N * powerRZ 2%R q <= Rabs x)%R.
Proof.
  intros prec ienv xenv r N q Henv Hchk.
  apply orb_prop in Hchk. destruct Hchk as [H|H].
  - assert (Hc := ieval_correct prec _ _ (Esub r (eps_e N q)) Henv).
    destruct (nonneg_correct _ _ Hc H) as [d [Hd Hge]].
    change (Xsub (xeval xenv r) (xeval xenv (eps_e N q)) = Xreal d) in Hd.
    rewrite xeval_eps_e in Hd.
    destruct (Xsub_real _ _ _ Hd) as [x [e [Hx [He Hv]]]].
    injection He as <-.
    exists x. split. exact Hx.
    apply Rle_trans with x. lra. apply Rle_abs.
  - assert (Hc := ieval_correct prec _ _ (Esub (Eneg r) (eps_e N q)) Henv).
    destruct (nonneg_correct _ _ Hc H) as [d [Hd Hge]].
    change (Xsub (Xneg (xeval xenv r)) (xeval xenv (eps_e N q)) = Xreal d) in Hd.
    rewrite xeval_eps_e in Hd.
    destruct (Xsub_real _ _ _ Hd) as [nx [e [Hnx [He Hv]]]].
    injection He as <-.
    destruct (xeval xenv r) as [|x] eqn:Hr. discriminate Hnx.
    simpl in Hnx. injection Hnx as Hnx.
    exists x. split. reflexivity.
    apply Rle_trans with (- x)%R. lra.
    rewrite <- Rabs_Ropp. apply Rle_abs.
Qed.

(** What a passing reversed verdict means for one point: some component is
    a real number at least the claimed size, so the field is out of force
    balance there by that margin. *)
Definition point_not_balanced (c : cert) (p : cpoint) : Prop :=
  let r3 := residual (pt_es p) (c_cfg c) (c_modes c) in
  let env := point_env c p in
  (exists x, xeval env (r_s r3) = Xreal x /\
             (IZR (c_NS c) * powerRZ 2%R (c_qS c) <= Rabs x)%R) \/
  (exists x, xeval env (r_u r3) = Xreal x /\
             (IZR (c_NU c) * powerRZ 2%R (c_qU c) <= Rabs x)%R) \/
  (exists x, xeval env (r_v r3) = Xreal x /\
             (IZR (c_NV c) * powerRZ 2%R (c_qV c) <= Rabs x)%R).

(** A true reversed verdict puts every point of the certificate out of
    balance. *)
Theorem check_cert_lower_correct :
  forall c,
  check_cert_lower c = true ->
  Forall (point_not_balanced c) (c_points c).
Proof.
  intros c Hchk.
  unfold check_cert_lower in Hchk.
  rewrite forallb_forall in Hchk.
  apply Forall_forall.
  intros p Hin.
  specialize (Hchk p Hin).
  unfold check_point_lower in Hchk.
  assert (Henv : env_ok
            (iextend (prec_of c) (ienv_of (prec_of c) (pt_ms p))
                     (r_binds (residual (pt_es p) (c_cfg c) (c_modes c))))
            (point_env c p)).
  { unfold point_env. apply iextend_correct. apply env_ok_fromZ. }
  unfold point_not_balanced.
  apply orb_prop in Hchk. destruct Hchk as [Hchk|Hv].
  - apply orb_prop in Hchk. destruct Hchk as [Hs|Hu].
    + left. exact (check1_lower_correct _ _ _ _ _ _ Henv Hs).
    + right; left. exact (check1_lower_correct _ _ _ _ _ _ Henv Hu).
  - right; right. exact (check1_lower_correct _ _ _ _ _ _ Henv Hv).
Qed.

(** A true verdict makes every point of the certificate sound. *)
Theorem check_cert_correct :
  forall c,
  check_cert c = true ->
  Forall (point_sound c) (c_points c).
Proof.
  intros c Hchk.
  unfold check_cert in Hchk.
  rewrite forallb_forall in Hchk.
  apply Forall_forall.
  intros p Hin.
  specialize (Hchk p Hin).
  unfold check_point in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hsu Hv].
  apply andb_prop in Hsu. destruct Hsu as [Hs Hu].
  assert (Henv : env_ok
            (iextend (prec_of c) (ienv_of (prec_of c) (pt_ms p))
                     (r_binds (residual (pt_es p) (c_cfg c) (c_modes c))))
            (point_env c p)).
  { unfold point_env. apply iextend_correct. apply env_ok_fromZ. }
  unfold point_sound.
  repeat split.
  - exact (check1_correct _ _ _ _ _ _ Henv Hs).
  - exact (check1_correct _ _ _ _ _ _ Henv Hu).
  - exact (check1_correct _ _ _ _ _ _ Henv Hv).
Qed.
