(** Discrete Fourier harmonics of the residual over the points of a certificate.

    A point certificate bounds each residual component at the angles it lists.
    For a three-dimensional equilibrium that bound measures the modes the
    solver does not carry: a spectral solution balances forces mode by mode
    over the set it retains, and what it leaves pointwise is the truncation.
    The quantity such a solution makes small is the harmonic of the residual
    at a retained mode, and over a uniform grid of angles that harmonic is a
    finite sum,

      H = sum_i r(p_i) k(p_i),   k = cos(m u - n v) or sin(m u - n v),

    which needs no quadrature. [harm_i] evaluates it in the interval
    arithmetic of Expr.v, one product per point and [Cell.isum] over them, and
    [harm_encloses] states that the result contains the real sum whenever the
    point certificate passes, which is what makes every r(p_i) a real number.
    The driver divides by the number of points to report a mean. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell.

Import ListNotations.

Open Scope Z_scope.

Section Harmonic.

Variable c : cert.

(** Which component of the residual is projected. *)
Variable sel : residual3 -> expr.

(** The kernel: sine or cosine of m u - n v. *)
Variable sine : bool.
Variable m n : Z.

(** It reads the two angles and nothing else, so it is written over an
    environment that holds only them: slot 0 the poloidal mantissa, slot 1 the
    toroidal one, eu and ev their exponents. A node's kernels then cost the
    angle list and not the node's coefficient rows. *)
Definition kern_e (eu ev : Z) : expr :=
  let a := Esub (Emul (EfromZ m) (Emul (Evar 0) (epow2 eu)))
                (Emul (EfromZ n) (Emul (Evar 1) (epow2 ev))) in
  if sine then Esin a else Ecos a.

Definition kern_at (prec : F.precision) (mu eu mv ev : Z) : I.type :=
  ieval prec (ienv_of prec [mu; mv]) (kern_e eu ev).

(** The angles of a point: slots 1 and 2 of its environment. *)
Definition p_mu (p : cpoint) : Z := nth 1 (pt_ms p) 0.
Definition p_eu (p : cpoint) : Z := nth 1 (pt_es p) 0.
Definition p_mv (p : cpoint) : Z := nth 2 (pt_ms p) 0.
Definition p_ev (p : cpoint) : Z := nth 2 (pt_es p) 0.

(** The component at a point, as the checker computes it and as a real. *)
Definition comp_i (p : cpoint) : I.type :=
  let prec := prec_of c in
  let r3 := residual (pt_es p) (c_cfg c) (c_modes c) in
  ieval prec (iextend prec (ienv_of prec (pt_ms p)) (r_binds r3)) (sel r3).

Definition comp_x (p : cpoint) : ExtendedR :=
  xeval (point_env c p) (sel (residual (pt_es p) (c_cfg c) (c_modes c))).

(** The kernel at a point. *)
Definition kern_i (p : cpoint) : I.type :=
  kern_at (prec_of c) (p_mu p) (p_eu p) (p_mv p) (p_ev p).

Definition kern_x (p : cpoint) : ExtendedR :=
  xeval (xenv_of [p_mu p; p_mv p]) (kern_e (p_eu p) (p_ev p)).

Lemma comp_contains :
  forall p, contains (I.convert (comp_i p)) (comp_x p).
Proof.
  intros p. unfold comp_i, comp_x, point_env.
  apply ieval_correct. apply iextend_correct. apply env_ok_fromZ.
Qed.

Lemma kern_contains :
  forall p, contains (I.convert (kern_i p)) (kern_x p).
Proof.
  intros p. unfold kern_i, kern_at, kern_x.
  apply ieval_correct. apply env_ok_fromZ.
Qed.

(** One term of the sum, and the sum, in both meanings. *)
Definition term_i (p : cpoint) : I.type :=
  I.mul (prec_of c) (comp_i p) (kern_i p).

Definition harm_i (pts : list cpoint) : I.type :=
  isum (prec_of c) (map term_i pts).

Definition term_r (p : cpoint) : R :=
  (proj_val (comp_x p) * proj_val (kern_x p))%R.

Definition harm_r (pts : list cpoint) : R :=
  fold_right Rplus 0%R (map term_r pts).

(** Where every component and every kernel value is a real number, the
    interval sum contains the real one. *)
Lemma harm_contains :
  forall pts,
  (forall p, In p pts -> exists x, comp_x p = Xreal x) ->
  (forall p, In p pts -> exists k, kern_x p = Xreal k) ->
  contains (I.convert (harm_i pts)) (Xreal (harm_r pts)).
Proof.
  induction pts as [|p tl IH]; intros Hc Hk.
  - apply (isum_correct (prec_of c) [] []). reflexivity.
    intros k Hk0. simpl in Hk0. lia.
  - unfold harm_i, harm_r in *. cbn [map isum fold_right].
    change (Xreal (term_r p + fold_right Rplus 0%R (map term_r tl)))
      with (Xadd (Xreal (term_r p))
                 (Xreal (fold_right Rplus 0%R (map term_r tl)))).
    apply I.add_correct.
    + destruct (Hc p (or_introl eq_refl)) as [x Hx].
      destruct (Hk p (or_introl eq_refl)) as [k Hk'].
      unfold term_i, term_r. rewrite Hx, Hk'. cbn [proj_val].
      change (Xreal (x * k)) with (Xmul (Xreal x) (Xreal k)).
      apply I.mul_correct.
      * rewrite <- Hx. apply comp_contains.
      * rewrite <- Hk'. apply kern_contains.
    + apply IH; intros q Hq; [apply Hc | apply Hk]; now right.
Qed.

(** The kernel is a real number at every point: its enclosure is tested
    against 2, which a sine or a cosine of a real argument always meets. *)
Definition kern_ok_at (prec : F.precision) (mu eu mv ev : Z) : bool :=
  check1 prec (ienv_of prec [mu; mv]) (kern_e eu ev) 2 0.

Definition kern_ok : bool :=
  forallb (fun p => kern_ok_at (prec_of c) (p_mu p) (p_eu p) (p_mv p) (p_ev p))
          (c_points c).

Lemma kern_ok_real :
  kern_ok = true ->
  forall p, In p (c_points c) -> exists k, kern_x p = Xreal k.
Proof.
  intros Hok p Hin. unfold kern_ok in Hok.
  rewrite forallb_forall in Hok. specialize (Hok p Hin).
  unfold kern_ok_at in Hok.
  destruct (check1_correct _ _ _ _ _ _
              (env_ok_fromZ (prec_of c) [p_mu p; p_mv p]) Hok)
    as [k [Hk _]].
  exists k. exact Hk.
Qed.

End Harmonic.

(** A passing point certificate makes every component real at every point,
    so the harmonic of each component is enclosed. *)
Theorem harm_encloses :
  forall c sine m n,
  check_cert c = true ->
  kern_ok c sine m n = true ->
  contains (I.convert (harm_i c r_s sine m n (c_points c)))
           (Xreal (harm_r c r_s sine m n (c_points c))) /\
  contains (I.convert (harm_i c r_u sine m n (c_points c)))
           (Xreal (harm_r c r_u sine m n (c_points c))) /\
  contains (I.convert (harm_i c r_v sine m n (c_points c)))
           (Xreal (harm_r c r_v sine m n (c_points c))).
Proof.
  intros c sine m n Hchk Hker.
  assert (Hsound := check_cert_correct c Hchk).
  rewrite Forall_forall in Hsound.
  assert (Hk := kern_ok_real c sine m n Hker).
  repeat split; apply harm_contains; try exact Hk;
    intros p Hin; destruct (Hsound p Hin) as [[xs [Hs _]] [[xu [Hu _]] [xv [Hv _]]]];
    unfold comp_x; eauto.
Qed.
