(** A floor on the two-term quasisymmetry defect over a box of states.

    [Project.two_term_refuted] reads two harmonics of the terms of the
    two-term quasisymmetry residual at the points of one state, and concludes
    that no flux function makes their ratio constant. This carries the same
    reading over a box of states and turns the refutation into a number.

    The certificate lists points of one surface and a box of states; the
    residual is [RQuasiTwo], whose second and third components are the two
    terms t1 and t2 of the criterion t1 = lam t2, lam constant on the surface.
    At every point the checker encloses each term over the whole box, and a
    bound on its magnitude makes it a real number there. The discrete
    harmonic of a term against cos or sin (m u - n v), summed over the points,
    is then enclosed over the box as well ([qharm_contains]).

    [qs_floor] is the conclusion. If at two kernels the harmonic of t2 stays
    away from zero by e over the box, and the boxes of the ratios h / t of the
    two harmonics are apart by g, then for every state of the box and every
    lam some point has |t1 - lam t2| >= e g / (2 N), N the number of points.
    So no state of the box is quasisymmetric on that surface, and each misses
    by at least that much at one of the points. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell Box Integral BoxCell Project.

Import ListNotations.
Local Open Scope R_scope.

Record qcert := QCert {
  qc_prec : Z ;
  qc_cfg : pconfig ;
  qc_modes : list (Z * Z) ;
  qc_es : list Z ;
  qc_ms : list Z ;
  qc_ds : list Z ;
  qc_su : nat ; qc_sv : nat ;
  qc_N1 : Z ; qc_q1 : Z ;
  qc_N2 : Z ; qc_q2 : Z ;
  qc_pts : list (Z * Z) }.

Definition qprec (c : qcert) : F.precision := F.PtoP (Z.to_pos (qc_prec c)).
Definition qres (c : qcert) : residual3 := residual (qc_es c) (qc_cfg c) (qc_modes c).
Definition qW (c : qcert) : env I.type := wide_ienv (qprec c) (qc_ms c) (qc_ds c).

(** The environment of a point over the box. *)
Definition qenv_i (c : qcert) (p : Z * Z) : env I.type :=
  iextend (qprec c) (icell_centre (qprec c) (qW c) (qc_su c) (qc_sv c) (fst p) (snd p))
          (r_binds (qres c)).

(** Component k at a point: its enclosure over the box, and its value at one
    state. *)
Definition qcomp_i (c : qcert) (k : nat) (p : Z * Z) : I.type :=
  ieval (qprec c) (qenv_i c p) (icomp (qres c) k).

Definition qval (c : qcert) (k : nat) (xs : list R) (p : Z * Z) : ExtendedR :=
  xeval (surf (qc_su c) (qc_sv c) (r_binds (qres c)) (xenv_R xs)
              (IZR (fst p)) (IZR (snd p)))
        (icomp (qres c) k).

(** The kernel at a point, in both meanings. *)
Definition qeu (c : qcert) : Z := nth (qc_su c) (qc_es c) 0%Z.
Definition qev (c : qcert) : Z := nth (qc_sv c) (qc_es c) 0%Z.

Definition qkern_i (c : qcert) (sine : bool) (m n : Z) (p : Z * Z) : I.type :=
  kern_at sine m n (qprec c) (fst p) (qeu c) (snd p) (qev c).

Definition qkern_r (c : qcert) (sine : bool) (m n : Z) (p : Z * Z) : R :=
  let a := IZR m * (IZR (fst p) * powerRZ 2 (qeu c))
           - IZR n * (IZR (snd p) * powerRZ 2 (qev c)) in
  if sine then sin a else cos a.

(** The harmonic of component k, over the box and at one state. *)
Definition qharm_i (c : qcert) (k : nat) (sine : bool) (m n : Z) : I.type :=
  isum (qprec c) (map (fun p => I.mul (qprec c) (qcomp_i c k p) (qkern_i c sine m n p))
                      (qc_pts c)).

Definition qharm_r (c : qcert) (k : nat) (xs : list R) (sine : bool) (m n : Z) : R :=
  fold_right Rplus 0
    (map (fun p => proj_val (qval c k xs p) * qkern_r c sine m n p) (qc_pts c)).

(** The same sum from enclosures of the component computed once per point,
    so that many kernels cost one evaluation of the bindings per point. *)
Fixpoint qharm_from (c : qcert) (vals : list I.type) (pts : list (Z * Z))
    (sine : bool) (m n : Z) : list I.type :=
  match vals, pts with
  | v :: vt, p :: pt => I.mul (qprec c) v (qkern_i c sine m n p) :: qharm_from c vt pt sine m n
  | _, _ => []
  end.

Lemma qharm_from_map :
  forall c k sine m n pts,
  qharm_from c (map (qcomp_i c k) pts) pts sine m n
  = map (fun p => I.mul (qprec c) (qcomp_i c k p) (qkern_i c sine m n p)) pts.
Proof.
  intros c k sine m n pts. induction pts as [|p tl IH]; simpl. reflexivity.
  now rewrite IH.
Qed.

(** What the driver evaluates: the harmonic from the per-point enclosures. *)
Definition qharm_vals (c : qcert) (vals : list I.type) (sine : bool) (m n : Z) : I.type :=
  isum (qprec c) (qharm_from c vals (qc_pts c) sine m n).

Lemma qharm_vals_eq :
  forall c k sine m n,
  qharm_vals c (map (qcomp_i c k) (qc_pts c)) sine m n = qharm_i c k sine m n.
Proof.
  intros c k sine m n. unfold qharm_vals, qharm_i. now rewrite qharm_from_map.
Qed.

(** Both terms are bounded at every point over the box, which is what makes
    them real. *)
Definition check_qcert (c : qcert) : bool :=
  forallb (fun p =>
             check1 (qprec c) (qenv_i c p) (icomp (qres c) 1) (qc_N1 c) (qc_q1 c) &&
             check1 (qprec c) (qenv_i c p) (icomp (qres c) 2) (qc_N2 c) (qc_q2 c))
          (qc_pts c).

(* ---------------------------------------------------------------- *)
(* Soundness                                                         *)

Lemma qkern_contains :
  forall c sine m n p,
  contains (I.convert (qkern_i c sine m n p)) (Xreal (qkern_r c sine m n p)).
Proof.
  intros c sine m n p. unfold qkern_i, kern_at.
  assert (H := ieval_correct (qprec c) _ _ (kern_e sine m n (qeu c) (qev c))
                 (env_ok_fromZ (qprec c) [fst p; snd p])).
  replace (Xreal (qkern_r c sine m n p))
    with (xeval (xenv_of [fst p; snd p]) (kern_e sine m n (qeu c) (qev c))).
  exact H.
  unfold kern_e, qkern_r, xenv_of.
  destruct sine; cbn [xeval]; rewrite !eget_of_list; reflexivity.
Qed.

Lemma qkern_bounded :
  forall c sine m n p, Rabs (qkern_r c sine m n p) <= 1.
Proof.
  intros c sine m n p. unfold qkern_r. cbv zeta.
  destruct sine; apply Rabs_le; split.
  - generalize (SIN_bound (IZR m * (IZR (fst p) * powerRZ 2 (qeu c))
                           - IZR n * (IZR (snd p) * powerRZ 2 (qev c)))). lra.
  - generalize (SIN_bound (IZR m * (IZR (fst p) * powerRZ 2 (qeu c))
                           - IZR n * (IZR (snd p) * powerRZ 2 (qev c)))). lra.
  - generalize (COS_bound (IZR m * (IZR (fst p) * powerRZ 2 (qeu c))
                           - IZR n * (IZR (snd p) * powerRZ 2 (qev c)))). lra.
  - generalize (COS_bound (IZR m * (IZR (fst p) * powerRZ 2 (qeu c))
                           - IZR n * (IZR (snd p) * powerRZ 2 (qev c)))). lra.
Qed.

(** At every state of the box and every point, each term is a real number in
    its enclosure. *)
Lemma qval_sound :
  forall c, check_qcert c = true ->
  forall xs, in_box (qc_ms c) (qc_ds c) xs ->
  forall p, In p (qc_pts c) ->
  forall k, k = 1%nat \/ k = 2%nat ->
  exists w, qval c k xs p = Xreal w /\ contains (I.convert (qcomp_i c k p)) (Xreal w).
Proof.
  intros c Hchk xs Hin p Hp k Hk.
  unfold check_qcert in Hchk. rewrite forallb_forall in Hchk.
  specialize (Hchk p Hp). apply andb_prop in Hchk. destruct Hchk as [H1 H2].
  assert (HW := wide_env_ok (qprec c) (qc_ms c) (qc_ds c) xs Hin).
  assert (Henv := iextend_correct (qprec c) (r_binds (qres c)) _ _
                    (icell_centre_ok (qprec c) _ (xenv_R xs) (qc_su c) (qc_sv c)
                       (fst p) (snd p) HW)).
  assert (Hc := ieval_correct (qprec c) _ _ (icomp (qres c) k) Henv).
  destruct Hk as [Hk|Hk]; subst k.
  - destruct (check1_correct _ _ _ _ _ _ Henv H1) as [w [Hw _]].
    exists w. split. exact Hw. unfold qcomp_i, qenv_i. rewrite <- Hw. exact Hc.
  - destruct (check1_correct _ _ _ _ _ _ Henv H2) as [w [Hw _]].
    exists w. split. exact Hw. unfold qcomp_i, qenv_i. rewrite <- Hw. exact Hc.
Qed.

(** The harmonic over the box contains the harmonic at each of its states. *)
Theorem qharm_contains :
  forall c, check_qcert c = true ->
  forall xs, in_box (qc_ms c) (qc_ds c) xs ->
  forall k sine m n, k = 1%nat \/ k = 2%nat ->
  contains (I.convert (qharm_i c k sine m n)) (Xreal (qharm_r c k xs sine m n)).
Proof.
  intros c Hchk xs Hin k sine m n Hk.
  unfold qharm_i, qharm_r.
  assert (Hall : forall p, In p (qc_pts c) ->
            exists w, qval c k xs p = Xreal w /\
                      contains (I.convert (qcomp_i c k p)) (Xreal w))
    by (intros p Hp; exact (qval_sound c Hchk xs Hin p Hp k Hk)).
  induction (qc_pts c) as [|p tl IH].
  - apply (isum_correct (qprec c) [] []). reflexivity. intros j Hj. simpl in Hj. lia.
  - cbn [map isum fold_right].
    change (Xreal (proj_val (qval c k xs p) * qkern_r c sine m n p
                   + fold_right Rplus 0
                       (map (fun p0 => proj_val (qval c k xs p0) * qkern_r c sine m n p0) tl)))
      with (Xadd (Xreal (proj_val (qval c k xs p) * qkern_r c sine m n p))
                 (Xreal (fold_right Rplus 0
                    (map (fun p0 => proj_val (qval c k xs p0) * qkern_r c sine m n p0) tl)))).
    apply I.add_correct.
    + destruct (Hall p (or_introl eq_refl)) as [w [Hw Hc]].
      rewrite Hw. cbn [proj_val].
      change (Xreal (w * qkern_r c sine m n p))
        with (Xmul (Xreal w) (Xreal (qkern_r c sine m n p))).
      apply I.mul_correct. exact Hc. apply qkern_contains.
    + apply IH. intros q Hq. apply Hall. now right.
Qed.

(* ---------------------------------------------------------------- *)
(* The floor                                                         *)

(** The largest value of a function on a nonempty list is taken at one of
    its elements. *)
Lemma list_argmax :
  forall {A : Type} (f : A -> R) (l : list A), l <> [] ->
  exists a, In a l /\ forall b, In b l -> f b <= f a.
Proof.
  intros A f l. induction l as [|x tl IH]; intros Hne. now destruct Hne.
  destruct tl as [|y tl'].
  - exists x. split. now left. intros b [<-|[]]. lra.
  - destruct (IH ltac:(discriminate)) as [a [Ha Hmax]].
    destruct (Rle_or_lt (f x) (f a)) as [Hxa|Hax].
    + exists a. split. now right. intros b [<-|Hb]. exact Hxa. now apply Hmax.
    + exists x. split. now left. intros b [<-|Hb]. lra.
      apply Rle_trans with (f a). now apply Hmax. lra.
Qed.

(** A sum of products against numbers bounded by one is bounded by the
    length of the list times the largest magnitude of the first factor. *)
Lemma sum_kernel_bound :
  forall {A : Type} (f g : A -> R) (l : list A) (M : R),
  (forall a, In a l -> Rabs (f a) <= M) ->
  (forall a, In a l -> Rabs (g a) <= 1) ->
  Rabs (fold_right Rplus 0 (map (fun a => f a * g a) l)) <= INR (length l) * M.
Proof.
  intros A f g l M Hf Hg. induction l as [|a tl IH].
  - simpl. rewrite Rabs_R0. lra.
  - cbn [map fold_right length]. rewrite S_INR.
    eapply Rle_trans. apply Rabs_triang.
    assert (H1 : Rabs (f a * g a) <= M).
    { rewrite Rabs_mult.
      assert (Hfa := Hf a (or_introl eq_refl)).
      assert (Hga := Hg a (or_introl eq_refl)).
      assert (0 <= Rabs (f a)) by apply Rabs_pos.
      assert (0 <= Rabs (g a)) by apply Rabs_pos.
      nra. }
    assert (H2 := IH (fun b Hb => Hf b (or_intror Hb)) (fun b Hb => Hg b (or_intror Hb))).
    lra.
Qed.

(** The harmonic of t1 - lam t2 is the difference of the harmonics. *)
Lemma harm_linear :
  forall {A : Type} (f g k : A -> R) (lam : R) (l : list A),
  fold_right Rplus 0 (map (fun a => (f a - lam * g a) * k a) l)
  = fold_right Rplus 0 (map (fun a => f a * k a) l)
    - lam * fold_right Rplus 0 (map (fun a => g a * k a) l).
Proof.
  intros A f g k lam l. induction l as [|a tl IH]; simpl. ring.
  rewrite IH. ring.
Qed.

Theorem qs_floor :
  forall c, check_qcert c = true ->
  forall (s1 s2 : bool) (m1 n1 m2 n2 : Z) (a1 b1 c1 d1 a2 b2 c2 d2 e g : R),
  (forall xs, in_box (qc_ms c) (qc_ds c) xs ->
     (a1 <= qharm_r c 1 xs s1 m1 n1 <= b1) /\ (c1 <= qharm_r c 2 xs s1 m1 n1 <= d1) /\
     (a2 <= qharm_r c 1 xs s2 m2 n2 <= b2) /\ (c2 <= qharm_r c 2 xs s2 m2 n2 <= d2)) ->
  (0 < c1 \/ d1 < 0) -> (0 < c2 \/ d2 < 0) ->
  0 < e -> e <= Rabs c1 -> e <= Rabs d1 -> e <= Rabs c2 -> e <= Rabs d2 ->
  0 < g ->
  (snd (ratio_box a1 b1 c1 d1) + g <= fst (ratio_box a2 b2 c2 d2) \/
   snd (ratio_box a2 b2 c2 d2) + g <= fst (ratio_box a1 b1 c1 d1)) ->
  forall xs, in_box (qc_ms c) (qc_ds c) xs ->
  forall lam : R,
  exists p, In p (qc_pts c) /\
    exists w1 w2, qval c 1 xs p = Xreal w1 /\ qval c 2 xs p = Xreal w2 /\
      e * g / (2 * INR (length (qc_pts c))) <= Rabs (w1 - lam * w2).
Proof.
  intros c Hchk s1 s2 m1 n1 m2 n2 a1 b1 c1 d1 a2 b2 c2 d2 e g Hbounds
         Hs1 Hs2 He He1 He2 He3 He4 Hg Hdis xs Hin lam.
  destruct (Hbounds xs Hin) as [H1 [H2 [H3 H4]]].
  set (h1 := qharm_r c 1 xs s1 m1 n1) in *.
  set (t1 := qharm_r c 2 xs s1 m1 n1) in *.
  set (h2 := qharm_r c 1 xs s2 m2 n2) in *.
  set (t2 := qharm_r c 2 xs s2 m2 n2) in *.
  (* the harmonics of t2 are at least e in magnitude *)
  assert (Et1 : e <= Rabs t1).
  { destruct Hs1 as [Hp|Hn].
    - rewrite Rabs_right by lra. rewrite Rabs_right in He1 by lra. lra.
    - rewrite Rabs_left by lra. rewrite Rabs_left in He2 by lra. lra. }
  assert (Et2 : e <= Rabs t2).
  { destruct Hs2 as [Hp|Hn].
    - rewrite Rabs_right by lra. rewrite Rabs_right in He3 by lra. lra.
    - rewrite Rabs_left by lra. rewrite Rabs_left in He4 by lra. lra. }
  assert (Ht1 : t1 <> 0) by (intros Hz; rewrite Hz, Rabs_R0 in Et1; lra).
  assert (Ht2 : t2 <> 0) by (intros Hz; rewrite Hz, Rabs_R0 in Et2; lra).
  assert (R1 := quotient_between h1 t1 a1 b1 c1 d1 H1 H2 Hs1).
  assert (R2 := quotient_between h2 t2 a2 b2 c2 d2 H3 H4 Hs2).
  (* one of the two ratios is at least g / 2 from lam *)
  assert (Hfar : g / 2 <= Rabs (h1 / t1 - lam) \/ g / 2 <= Rabs (h2 / t2 - lam)).
  { destruct (Rle_or_lt (g / 2) (Rabs (h1 / t1 - lam))) as [Ha|Ha]. now left. right.
    apply Rabs_def2 in Ha. destruct Ha as [Ha1 Ha2].
    destruct R1 as [R1l R1h]. destruct R2 as [R2l R2h].
    destruct Hdis as [Hd|Hd].
    - apply Rle_trans with (h2 / t2 - lam). lra. apply Rle_abs.
    - apply Rle_trans with (- (h2 / t2 - lam)). lra. rewrite <- Rabs_Ropp. apply Rle_abs. }
  (* so the harmonic of t1 - lam t2 at that kernel is at least e g / 2 *)
  assert (Hbig : exists s m n, e * g / 2 <= Rabs (qharm_r c 1 xs s m n - lam * qharm_r c 2 xs s m n)).
  { destruct Hfar as [Hf|Hf].
    - exists s1, m1, n1.
      change (qharm_r c 1 xs s1 m1 n1) with h1. change (qharm_r c 2 xs s1 m1 n1) with t1.
      replace (h1 - lam * t1) with (t1 * (h1 / t1 - lam)) by (field; exact Ht1).
      rewrite Rabs_mult.
      assert (0 <= Rabs (h1 / t1 - lam)) by apply Rabs_pos.
      assert (0 <= e) by lra.
      apply Rle_trans with (e * Rabs (h1 / t1 - lam)).
      + replace (e * g / 2) with (e * (g / 2)) by field. apply Rmult_le_compat_l; lra.
      + apply Rmult_le_compat_r; lra.
    - exists s2, m2, n2.
      change (qharm_r c 1 xs s2 m2 n2) with h2. change (qharm_r c 2 xs s2 m2 n2) with t2.
      replace (h2 - lam * t2) with (t2 * (h2 / t2 - lam)) by (field; exact Ht2).
      rewrite Rabs_mult.
      assert (0 <= Rabs (h2 / t2 - lam)) by apply Rabs_pos.
      assert (0 <= e) by lra.
      apply Rle_trans with (e * Rabs (h2 / t2 - lam)).
      + replace (e * g / 2) with (e * (g / 2)) by field. apply Rmult_le_compat_l; lra.
      + apply Rmult_le_compat_r; lra. }
  destruct Hbig as [s [m [n Hbig]]].
  (* the points are not empty, since the harmonics are not zero *)
  assert (Hne : qc_pts c <> []).
  { intros Hnil. apply Ht1. unfold t1, qharm_r. rewrite Hnil. reflexivity. }
  (* the point where |t1 - lam t2| is largest *)
  set (dev := fun p => Rabs (proj_val (qval c 1 xs p) - lam * proj_val (qval c 2 xs p))).
  destruct (list_argmax dev (qc_pts c) Hne) as [p [Hp Hmax]].
  exists p. split. exact Hp.
  destruct (qval_sound c Hchk xs Hin p Hp 1%nat (or_introl eq_refl)) as [w1 [Hw1 _]].
  destruct (qval_sound c Hchk xs Hin p Hp 2%nat (or_intror eq_refl)) as [w2 [Hw2 _]].
  exists w1, w2. split. exact Hw1. split. exact Hw2.
  assert (Hdev : dev p = Rabs (w1 - lam * w2)) by (unfold dev; rewrite Hw1, Hw2; reflexivity).
  rewrite <- Hdev.
  (* the harmonic is at most N times the largest deviation *)
  assert (E : qharm_r c 1 xs s m n - lam * qharm_r c 2 xs s m n
              = fold_right Rplus 0
                  (map (fun q => (proj_val (qval c 1 xs q) - lam * proj_val (qval c 2 xs q))
                                 * qkern_r c s m n q) (qc_pts c))).
  { unfold qharm_r. symmetry.
    apply (harm_linear (fun q => proj_val (qval c 1 xs q)) (fun q => proj_val (qval c 2 xs q))
                       (qkern_r c s m n) lam (qc_pts c)). }
  assert (Hsum : Rabs (qharm_r c 1 xs s m n - lam * qharm_r c 2 xs s m n)
                 <= INR (length (qc_pts c)) * dev p).
  { rewrite E.
    apply (sum_kernel_bound
             (fun q => proj_val (qval c 1 xs q) - lam * proj_val (qval c 2 xs q))
             (qkern_r c s m n)).
    - intros q Hq. exact (Hmax q Hq).
    - intros q Hq. apply qkern_bounded. }
  assert (HN : 0 < INR (length (qc_pts c))).
  { apply lt_0_INR. destruct (qc_pts c) as [|p0 tl0].
    - exfalso. now apply Hne.
    - simpl. lia. }
  apply Rmult_le_reg_l with (2 * INR (length (qc_pts c))). lra.
  replace (2 * INR (length (qc_pts c)) * (e * g / (2 * INR (length (qc_pts c)))))
    with (e * g) by (field; lra).
  lra.
Qed.
