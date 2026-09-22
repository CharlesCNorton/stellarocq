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

(* ---------------------------------------------------------------- *)
(* Two components in a fixed ratio                                   *)

(** The sum is linear in the component. Where one component is lam times
    another at every point of a list, their harmonics at any kernel are in
    that ratio too, so a proportionality that holds pointwise is read off the
    numbers the checker reports. *)
Lemma harm_r_scale :
  forall c sel1 sel2 sine m n (lam : R) pts,
  (forall p, In p pts ->
     exists x y, comp_x c sel1 p = Xreal x /\ comp_x c sel2 p = Xreal y /\
                 x = (lam * y)%R) ->
  harm_r c sel1 sine m n pts = (lam * harm_r c sel2 sine m n pts)%R.
Proof.
  intros c sel1 sel2 sine m n lam pts H.
  induction pts as [|p tl IH].
  - unfold harm_r. simpl. ring.
  - unfold harm_r in *. cbn [map fold_right].
    rewrite IH by (intros q Hq; apply H; now right).
    destruct (H p (or_introl eq_refl)) as [x [y [Hx [Hy Hxy]]]].
    unfold term_r. rewrite Hx, Hy. cbn [proj_val]. rewrite Hxy. ring.
Qed.

(** A product of two reals lies between the products of their bounds. *)
Lemma prod_between :
  forall x y a b r s : R,
  (a <= x <= b)%R -> (r <= y <= s)%R ->
  (Rmin (Rmin (a * r) (a * s)) (Rmin (b * r) (b * s)) <= x * y <=
   Rmax (Rmax (a * r) (a * s)) (Rmax (b * r) (b * s)))%R.
Proof.
  intros x y a b r s [Hax Hxb] [Hry Hys].
  assert (Hlo : (Rmin (Rmin (a * r) (a * s)) (Rmin (b * r) (b * s)) <= x * y)%R).
  { destruct (Rle_or_lt 0 y) as [Hy|Hy].
    - apply Rle_trans with (a * y)%R.
      + destruct (Rle_or_lt 0 a) as [Ha|Ha].
        * apply Rle_trans with (a * r)%R.
          apply Rle_trans with (Rmin (a * r) (a * s)); apply Rmin_l.
          apply Rmult_le_compat_l; assumption.
        * apply Rle_trans with (a * s)%R.
          apply Rle_trans with (Rmin (a * r) (a * s)). apply Rmin_l. apply Rmin_r.
          nra.
      + nra.
    - apply Rle_trans with (b * y)%R.
      + destruct (Rle_or_lt 0 b) as [Hb|Hb].
        * apply Rle_trans with (b * r)%R.
          apply Rle_trans with (Rmin (b * r) (b * s)). apply Rmin_r. apply Rmin_l.
          apply Rmult_le_compat_l; assumption.
        * apply Rle_trans with (b * s)%R.
          apply Rle_trans with (Rmin (b * r) (b * s)); apply Rmin_r.
          nra.
      + nra. }
  assert (Hhi : (x * y <= Rmax (Rmax (a * r) (a * s)) (Rmax (b * r) (b * s)))%R).
  { destruct (Rle_or_lt 0 y) as [Hy|Hy].
    - apply Rle_trans with (b * y)%R.
      + nra.
      + destruct (Rle_or_lt 0 b) as [Hb|Hb].
        * apply Rle_trans with (b * s)%R.
          apply Rmult_le_compat_l; assumption.
          apply Rle_trans with (Rmax (b * r) (b * s)); apply Rmax_r.
        * apply Rle_trans with (b * r)%R.
          nra.
          apply Rle_trans with (Rmax (b * r) (b * s)). apply Rmax_l. apply Rmax_r.
    - apply Rle_trans with (a * y)%R.
      + nra.
      + destruct (Rle_or_lt 0 a) as [Ha|Ha].
        * apply Rle_trans with (a * s)%R.
          apply Rmult_le_compat_l; assumption.
          apply Rle_trans with (Rmax (a * r) (a * s)). apply Rmax_r. apply Rmax_l.
        * apply Rle_trans with (a * r)%R.
          nra.
          apply Rle_trans with (Rmax (a * r) (a * s)); apply Rmax_l. }
  split; assumption.
Qed.

(** The box the ratio of two enclosed numbers lies in, as gen/quasisym.py
    computes it: the four quotients of the endpoints, when the divisor's
    enclosure excludes zero. *)
Definition ratio_box (a b c d : R) : R * R :=
  (Rmin (Rmin (a / c) (a / d)) (Rmin (b / c) (b / d)),
   Rmax (Rmax (a / c) (a / d)) (Rmax (b / c) (b / d)))%R.

Lemma quotient_between :
  forall x y a b c d : R,
  (a <= x <= b)%R -> (c <= y <= d)%R -> (0 < c \/ d < 0)%R ->
  (fst (ratio_box a b c d) <= x / y <= snd (ratio_box a b c d))%R.
Proof.
  intros x y a b c d Hx [Hcy Hyd] Hsign.
  assert (Hy : y <> 0%R) by (destruct Hsign; lra).
  assert (Hc : c <> 0%R) by (destruct Hsign; lra).
  assert (Hd : d <> 0%R) by (destruct Hsign; lra).
  (* 1/y lies between 1/d and 1/c on either side of zero *)
  assert (Hinv : (/ d <= / y <= / c)%R).
  { destruct Hsign as [Hpos|Hneg].
    - split; apply Rinv_le_contravar; lra.
    - split.
      + apply Ropp_le_cancel. rewrite <- !Rinv_opp. apply Rinv_le_contravar; lra.
      + apply Ropp_le_cancel. rewrite <- !Rinv_opp. apply Rinv_le_contravar; lra. }
  unfold ratio_box, Rdiv. cbn [fst snd].
  assert (H := prod_between x (/ y) a b (/ d) (/ c) Hx Hinv).
  (* the four corners, in the order the box lists them *)
  rewrite (Rmin_comm (a * / d) (a * / c)), (Rmin_comm (b * / d) (b * / c)),
          (Rmax_comm (a * / d) (a * / c)), (Rmax_comm (b * / d) (b * / c)) in H.
  exact H.
Qed.

(** What two harmonics decide. If one component is lam times another at every
    point, their harmonics at any kernel are in the ratio lam, so lam lies in
    the ratio box of each kernel's certified enclosures; two kernels whose
    boxes are disjoint leave no such lam. The bounds are reals, which is what
    an enclosure from [harm_encloses] hands to whoever reads it. *)
Theorem harmonic_ratios_refute :
  forall c sel1 sel2 pts (lam : R) sine1 m1 n1 sine2 m2 n2
         (a1 b1 c1 d1 a2 b2 c2 d2 : R),
  (forall p, In p pts ->
     exists x y, comp_x c sel1 p = Xreal x /\ comp_x c sel2 p = Xreal y /\
                 x = (lam * y)%R) ->
  (a1 <= harm_r c sel1 sine1 m1 n1 pts <= b1)%R ->
  (c1 <= harm_r c sel2 sine1 m1 n1 pts <= d1)%R -> (0 < c1 \/ d1 < 0)%R ->
  (a2 <= harm_r c sel1 sine2 m2 n2 pts <= b2)%R ->
  (c2 <= harm_r c sel2 sine2 m2 n2 pts <= d2)%R -> (0 < c2 \/ d2 < 0)%R ->
  (snd (ratio_box a1 b1 c1 d1) < fst (ratio_box a2 b2 c2 d2) \/
   snd (ratio_box a2 b2 c2 d2) < fst (ratio_box a1 b1 c1 d1))%R ->
  False.
Proof.
  intros c sel1 sel2 pts lam sine1 m1 n1 sine2 m2 n2 a1 b1 c1 d1 a2 b2 c2 d2
         Hprop H1 H2 Hs1 H3 H4 Hs2 Hdis.
  assert (E1 := harm_r_scale c sel1 sel2 sine1 m1 n1 lam pts Hprop).
  assert (E2 := harm_r_scale c sel1 sel2 sine2 m2 n2 lam pts Hprop).
  assert (Hy1 : harm_r c sel2 sine1 m1 n1 pts <> 0%R) by (destruct Hs1; lra).
  assert (Hy2 : harm_r c sel2 sine2 m2 n2 pts <> 0%R) by (destruct Hs2; lra).
  assert (L1 : lam = (harm_r c sel1 sine1 m1 n1 pts / harm_r c sel2 sine1 m1 n1 pts)%R)
    by (rewrite E1; field; exact Hy1).
  assert (L2 : lam = (harm_r c sel1 sine2 m2 n2 pts / harm_r c sel2 sine2 m2 n2 pts)%R)
    by (rewrite E2; field; exact Hy2).
  assert (B1 := quotient_between _ _ a1 b1 c1 d1 H1 H2 Hs1).
  assert (B2 := quotient_between _ _ a2 b2 c2 d2 H3 H4 Hs2).
  rewrite <- L1 in B1. rewrite <- L2 in B2.
  destruct Hdis; lra.
Qed.

(** The two-term quasisymmetry residual read this way. A certificate whose
    output is [RQuasiTwo] carries the defect Q = t1 - F0 t2 as its first
    component and t2 = F0 J C as its third; the ratio the criterion asks to be
    a flux function is t1 / (J C), and where it is one constant F on the
    points, Q = (F / F0 - 1) t2 at each of them. Two kernels whose certified
    ratio boxes of Q against t2 are disjoint therefore refute every such F on
    those points. *)
Definition two_term_constant (c : cert) (lam : R) (pts : list cpoint) : Prop :=
  forall p, In p pts ->
  exists q t, comp_x c r_s p = Xreal q /\ comp_x c r_v p = Xreal t /\
              q = (lam * t)%R.

Theorem two_term_refuted :
  forall c pts sine1 m1 n1 sine2 m2 n2 (a1 b1 c1 d1 a2 b2 c2 d2 : R),
  (a1 <= harm_r c r_s sine1 m1 n1 pts <= b1)%R ->
  (c1 <= harm_r c r_v sine1 m1 n1 pts <= d1)%R -> (0 < c1 \/ d1 < 0)%R ->
  (a2 <= harm_r c r_s sine2 m2 n2 pts <= b2)%R ->
  (c2 <= harm_r c r_v sine2 m2 n2 pts <= d2)%R -> (0 < c2 \/ d2 < 0)%R ->
  (snd (ratio_box a1 b1 c1 d1) < fst (ratio_box a2 b2 c2 d2) \/
   snd (ratio_box a2 b2 c2 d2) < fst (ratio_box a1 b1 c1 d1))%R ->
  forall lam, ~ two_term_constant c lam pts.
Proof.
  intros c pts sine1 m1 n1 sine2 m2 n2 a1 b1 c1 d1 a2 b2 c2 d2
         H1 H2 Hs1 H3 H4 Hs2 Hdis lam Hconst.
  exact (harmonic_ratios_refute c r_s r_v pts lam sine1 m1 n1 sine2 m2 n2
           a1 b1 c1 d1 a2 b2 c2 d2 Hconst H1 H2 Hs1 H3 H4 Hs2 Hdis).
Qed.
