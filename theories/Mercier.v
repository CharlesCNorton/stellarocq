(** The Mercier criterion assembled from certified enclosures.

    Quad.v encloses the four angular integrals of `mercier.f90` and, off the
    free-radius reconstruction, the flux functions beside them. Combining them
    into DShear, DCurr, DWell, DGeod and DMerc was arithmetic done outside the
    checker, in rational arithmetic on the printed endpoints. Here the
    combination is an expression, evaluated by the same sound interval
    evaluator as everything else, and what a run establishes is a theorem about
    the criterion rather than about its four ingredients.

    The inputs arrive as intervals rather than as points, since that is what a
    covering produces. [mbox] is a claimed interval with dyadic endpoints,
    [in_mbox] says a real lies in it, and [mercier_encloses] states that the
    computed interval contains the criterion of any reals that do.

    Normalization. `mercier.f90` works in the flux variable PHI, so every
    radial derivative it uses is d/dPHI = (d/ds)/phip_real with

      phip_real = 2 pi phips signgs,

    and its surface quantities are averages multiplied by 4 pi^2, which is the
    integral over the angular torus that a cell certificate encloses.

    What a covering reports needs one more factor. iota' and mu0 p' are flux
    functions, and the machinery that certifies them integrates them over the
    angles like everything else, so what comes back is 4 pi^2 times the value.
    V'' and the current gradient are integrals already. Writing the certified
    quantities as they arrive,

      shear = iota' / (4 pi^2 phip_real)
      vpp   = V'' / phip_real^2
      presp = (mu0 p') / (4 pi^2 phip_real)
      ip    = signgs (integral of dB_u/ds) / (2 pi phip_real)

    Each of these is checked against the file's own DShear, DCurr, DWell and
    DMerc by the regression suite rather than argued from the source, on a
    sheared equilibrium where every term contributes.

    The four terms are then `mercier.f90`'s own:

      DShear = shear^2 / 4
      DCurr  = -shear (tjb - ip tbb)
      DWell  = presp (vpp - presp tpp) tbb
      DGeod  = tjb^2 - tbb tjj
      DMerc  = DShear + DCurr + DWell + DGeod.

    DGeod is a difference of two numbers that agree to ten digits, so no
    enclosure decides its sign however fine the covering.
    [mercier_geodesic_nonpositive] of Quad.v decides it by inequality instead,
    and [dgeod_nonpositive] below is that theorem read at these slots, so the
    sign enters this file as a proof rather than as an assumption. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell Quad.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Interval inputs                                                   *)

(** A claimed interval, both endpoints dyadic. *)
Record mbox := MBox {
  mb_mlo : Z ; mb_elo : Z ;
  mb_mhi : Z ; mb_ehi : Z
}.

(** The real numbers it claims. *)
Definition in_mbox (b : mbox) (x : R) : Prop :=
  IZR (mb_mlo b) * powerRZ 2 (mb_elo b) <= x <=
  IZR (mb_mhi b) * powerRZ 2 (mb_ehi b).

(** The interval the checker computes for it. Both endpoints are evaluated
    the way every other number in the development is, so an endpoint that is
    not exactly representable widens outward rather than being rounded to
    something the theorem does not cover. *)
Definition box_i (prec : F.precision) (b : mbox) : I.type :=
  I.join (ieval prec eempty (eps_e (mb_mlo b) (mb_elo b)))
         (ieval prec eempty (eps_e (mb_mhi b) (mb_ehi b))).

Lemma box_correct :
  forall prec b x, in_mbox b x -> contains (I.convert (box_i prec b)) (Xreal x).
Proof.
  intros prec [mlo elo mhi ehi] x [Hlo Hhi]. unfold in_mbox in *. simpl in *.
  apply (contains_between _ (IZR mlo * powerRZ 2 elo)
                            (IZR mhi * powerRZ 2 ehi)).
  - apply I.join_correct. left.
    assert (H := ieval_correct prec eempty eempty (eps_e mlo elo) env_ok_nil).
    rewrite xeval_eps_e in H. exact H.
  - apply I.join_correct. right.
    assert (H := ieval_correct prec eempty eempty (eps_e mhi ehi) env_ok_nil).
    rewrite xeval_eps_e in H. exact H.
  - split; assumption.
Qed.

(** The two environments: the boxes, and any reals inside them. *)
Definition menv (prec : F.precision) (bs : list mbox) : env I.type :=
  of_list (map (box_i prec) bs).

Definition mxenv (vs : list R) : env ExtendedR :=
  of_list (map Xreal vs).

Lemma env_ok_mbox :
  forall prec bs vs, Forall2 in_mbox bs vs -> env_ok (menv prec bs) (mxenv vs).
Proof.
  intros prec bs vs H n.
  unfold menv, mxenv. rewrite !eget_of_list.
  revert n. induction H as [|b v bs vs Hb Hall IH]; intros n; simpl.
  - destruct n; rewrite ?I.nai_correct; exact I.
  - destruct n as [|n].
    + now apply box_correct.
    + apply IH.
Qed.

(** A slot inside the list reads the real it was given. *)
Lemma eget_mxenv :
  forall vs k, (k < length vs)%nat ->
  eget k (mxenv vs) Xnan = Xreal (nth k vs 0).
Proof.
  intros vs k Hk.
  unfold mxenv. rewrite eget_of_list.
  rewrite (nth_indep _ Xnan (Xreal 0)) by (rewrite length_map; lia).
  now rewrite (map_nth Xreal vs 0 k).
Qed.

(* ---------------------------------------------------------------- *)
(* The slots of the criterion                                        *)

(** The four angular integrals, then the flux functions, then the two
    numbers of the file that set the normalization. Every one of them is a
    quantity some certificate encloses, except phips and signgs, which are
    exact and which gen/verify_cert.py checks against the wout. *)
Definition s_tpp : nat := 0.
Definition s_tbb : nat := 1.
Definition s_tjb : nat := 2.
Definition s_tjj : nat := 3.
Definition s_vpp : nat := 4.      (* V'' = d2V/ds2 *)
Definition s_pp : nat := 5.       (* mu0 dp/ds as the certificate computes it *)
Definition s_iotap : nat := 6.    (* diota/ds *)
Definition s_ipint : nat := 7.    (* the angular integral of dB_u/ds *)
Definition s_phip : nat := 8.     (* the wout's phips *)
Definition s_sg : nat := 9.       (* signgs, +1 or -1 *)

Definition n_mslots : nat := 10.

Definition e_two_pi : expr := Emul (EfromZ 2) Epi.
Definition e_four_pi2 : expr := Emul (EfromZ 4) (Emul Epi Epi).

(** phip_real = 2 pi phips signgs. *)
Definition e_phip_real : expr :=
  Emul e_two_pi (Emul (Evar s_phip) (Evar s_sg)).

(** iota' arrives multiplied by 4 pi^2, since it is carried as an
    integrand. *)
Definition e_shear : expr :=
  Ediv (Evar s_iotap) (Emul e_four_pi2 e_phip_real).

Definition e_vpp : expr :=
  Ediv (Evar s_vpp) (Emul e_phip_real e_phip_real).

Definition e_presp : expr :=
  Ediv (Evar s_pp) (Emul e_four_pi2 e_phip_real).

Definition e_ip : expr :=
  Ediv (Emul (Evar s_sg) (Evar s_ipint)) (Emul e_two_pi e_phip_real).

(* ---------------------------------------------------------------- *)
(* The four terms                                                    *)

Definition e_dshear : expr := Ediv (Emul e_shear e_shear) (EfromZ 4).

Definition e_dcurr : expr :=
  Eneg (Emul e_shear (Esub (Evar s_tjb) (Emul e_ip (Evar s_tbb)))).

Definition e_dwell : expr :=
  Emul (Emul e_presp (Esub e_vpp (Emul e_presp (Evar s_tpp)))) (Evar s_tbb).

Definition e_dgeod : expr :=
  Esub (Emul (Evar s_tjb) (Evar s_tjb)) (Emul (Evar s_tbb) (Evar s_tjj)).

(** The three terms an enclosure decides, and the whole criterion. *)
Definition e_dstable : expr := Eadd (Eadd e_dshear e_dcurr) e_dwell.

Definition e_dmerc : expr := Eadd e_dstable e_dgeod.

(** What the checker computes for one of them. *)
Definition merc_i (prec : F.precision) (bs : list mbox) (e : expr) : I.type :=
  ieval prec (menv prec bs) e.

(** Any criterion assembled from reals inside the boxes lies in the interval
    the checker computes. This is the whole of the assembly: no step of it
    happens outside the evaluator whose soundness is proven. *)
Theorem mercier_encloses :
  forall prec bs vs e,
  Forall2 in_mbox bs vs ->
  contains (I.convert (merc_i prec bs e)) (xeval (mxenv vs) e).
Proof.
  intros prec bs vs e H.
  apply ieval_correct. now apply env_ok_mbox.
Qed.

(* ---------------------------------------------------------------- *)
(* The sign of the geodesic term                                     *)

(** DGeod is the Cauchy-Schwarz defect of the three integrals, so it is never
    positive whatever the covering says. This is [mercier_geodesic_nonpositive]
    of Quad.v read at the slots this file uses: the three slots hold the three
    integrals, and the conclusion is the sign of the term built from them. *)
Theorem dgeod_nonpositive :
  forall (vs : list R) (f g w : R -> R) (a b : R),
  (length vs = n_mslots)%nat ->
  nth s_tjb vs 0 = RInt (fun x => f x * g x * w x) a b ->
  nth s_tbb vs 0 = RInt (fun x => g x * g x * w x) a b ->
  nth s_tjj vs 0 = RInt (fun x => f x * f x * w x) a b ->
  a <= b ->
  ex_RInt (fun x => f x * f x * w x) a b ->
  ex_RInt (fun x => g x * g x * w x) a b ->
  ex_RInt (fun x => f x * g x * w x) a b ->
  ((forall x, a < x < b -> 0 <= w x) \/ (forall x, a < x < b -> w x <= 0)) ->
  exists d, xeval (mxenv vs) e_dgeod = Xreal d /\ d <= 0.
Proof.
  intros vs f g w a b Hlen Hjb Hbb Hjj Hab Hff Hgg Hfg Hw.
  assert (Hjbk : (s_tjb < length vs)%nat)
    by (rewrite Hlen; unfold s_tjb, n_mslots; lia).
  assert (Hbbk : (s_tbb < length vs)%nat)
    by (rewrite Hlen; unfold s_tbb, n_mslots; lia).
  assert (Hjjk : (s_tjj < length vs)%nat)
    by (rewrite Hlen; unfold s_tjj, n_mslots; lia).
  exists (nth s_tjb vs 0 * nth s_tjb vs 0
          - nth s_tbb vs 0 * nth s_tjj vs 0).
  split.
  - unfold e_dgeod. cbn [xeval].
    rewrite (eget_mxenv vs s_tjb Hjbk).
    rewrite (eget_mxenv vs s_tbb Hbbk).
    rewrite (eget_mxenv vs s_tjj Hjjk).
    reflexivity.
  - rewrite Hjb, Hbb, Hjj.
    now apply (mercier_geodesic_nonpositive f g w a b).
Qed.

(* ---------------------------------------------------------------- *)
(* A verdict of instability                                          *)

(** The three terms an enclosure decides, bounded above by -N 2^q. *)
Definition check_unstable (prec : F.precision) (bs : list mbox) (N q : Z)
    : bool :=
  nonneg (ieval prec (menv prec bs) (Esub (Eneg e_dstable) (eps_e N q))).

(** What a passing check means. The first three terms are below the claimed
    negative margin, and since the geodesic term is never positive, so is the
    whole criterion: the surface is Mercier unstable by that margin.

    The hypothesis on DGeod is discharged by [dgeod_nonpositive] whenever the
    three slots hold the integrals they are meant to, which is what a covering
    of the torus establishes. It is a hypothesis here rather than an appeal to
    that theorem so that this statement stays about the numbers, and so that
    what it needs from the physics is on its face. *)
Theorem mercier_unstable_correct :
  forall prec bs vs N q,
  Forall2 in_mbox bs vs ->
  check_unstable prec bs N q = true ->
  exists ds,
    xeval (mxenv vs) e_dstable = Xreal ds /\
    ds <= - (IZR N * powerRZ 2 q) /\
    forall dg, xeval (mxenv vs) e_dgeod = Xreal dg -> dg <= 0 ->
      xeval (mxenv vs) e_dmerc = Xreal (ds + dg) /\
      ds + dg <= - (IZR N * powerRZ 2 q).
Proof.
  intros prec bs vs N q Hin Hchk.
  unfold check_unstable in Hchk.
  assert (Hc := ieval_correct prec _ _ (Esub (Eneg e_dstable) (eps_e N q))
                  (env_ok_mbox prec bs vs Hin)).
  destruct (nonneg_correct _ _ Hc Hchk) as [r [Hr Hge]].
  cbn [xeval] in Hr.
  rewrite xeval_eps_e in Hr.
  destruct (xeval (mxenv vs) e_dstable) as [|ds] eqn:Hds.
  { cbn in Hr. discriminate. }
  cbn in Hr. injection Hr as Hr.
  exists ds. split. reflexivity.
  split. lra.
  intros dg Hdg Hneg.
  split.
  - unfold e_dmerc. cbn [xeval]. rewrite Hds, Hdg. reflexivity.
  - lra.
Qed.

(** The same reading for a stable surface: the whole criterion positive. Here
    the geodesic term has to be enclosed rather than signed, since its
    inequality points the wrong way, which is why a proof of stability is
    harder to come by than a proof of instability. *)
Definition check_stable (prec : F.precision) (bs : list mbox) (N q : Z)
    : bool :=
  nonneg (ieval prec (menv prec bs) (Esub e_dmerc (eps_e N q))).

Theorem mercier_stable_correct :
  forall prec bs vs N q,
  Forall2 in_mbox bs vs ->
  check_stable prec bs N q = true ->
  exists dm,
    xeval (mxenv vs) e_dmerc = Xreal dm /\
    IZR N * powerRZ 2 q <= dm.
Proof.
  intros prec bs vs N q Hin Hchk.
  unfold check_stable in Hchk.
  assert (Hc := ieval_correct prec _ _ (Esub e_dmerc (eps_e N q))
                  (env_ok_mbox prec bs vs Hin)).
  destruct (nonneg_correct _ _ Hc Hchk) as [r [Hr Hge]].
  cbn [xeval] in Hr.
  rewrite xeval_eps_e in Hr.
  destruct (xeval (mxenv vs) e_dmerc) as [|dm] eqn:Hdm.
  { cbn in Hr. discriminate. }
  cbn in Hr. injection Hr as Hr.
  exists dm. split. reflexivity. lra.
Qed.
