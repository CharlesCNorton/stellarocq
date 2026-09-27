(** Newcomb's condition broken on a rational surface, at every state of a box.

    In straight-field-line angles, a nested-surface field whose rotational
    transform is n/m on a surface has closed field lines there, and the
    integral of dl/B along the line theta = alpha + iota v through m toroidal
    turns is (2 pi m / phip) times the sum over p of G_{pm,pn} e^{i p m alpha},
    G the Fourier coefficients of the Jacobian. A smooth equilibrium with
    p' <> 0 on that surface has the integral the same on every line (Newcomb
    1959), which is [newcomb_condition]: the resonant harmonic of the Jacobian
    vanishes. Where it does not, the integral varies along the surface by at
    least 2 (2 pi m / |phip|) |G_{m,n}|.

    [newcomb_violated] reads four certificates, each established by its own
    checker, over a family of states that share every slot but the free
    radius of slot 0: two point certificates of the [RIota] output, one at
    each end of the radius interval, claiming m iota - n of opposite signs
    there; a point certificate of the [RNewcomb] output's third component,
    mu0 dp/ds, from below over the interval; and a harmonic certificate of
    its first component, the torus integral of sqrt(g) cos(m u - n v),
    claimed at most -F over the interval. It concludes that at some radius of
    the interval iota is exactly n/m, mu0 dp/ds is at least the floor in
    size, and the resonant harmonic is at most -F: [newcomb_condition] fails
    for every state of the family. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell Box Integral Harmonic BoxCell.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The rational surface                                              *)

Section IotaGap.

Variable exps : list Z.
Variable lasym : bool.
Variable prof : pprofile.
Variable modes : list (Z * Z).
Variable hm hn : Z.

Definition igap_r3 : residual3 := residual exps (PConfig lasym prof (RIota hm hn)) modes.

(** The value of input slot k, scaled by its exponent, as an expression reads
    it. *)
Definition inval (X : env ExtendedR) (k : nat) : ExtendedR := xeval X (evar exps k).

Lemma xeval_evar_eset :
  forall X k n v, k <> n -> xeval (eset n X v) (evar exps k) = xeval X (evar exps k).
Proof.
  intros X k n v Hkn. unfold evar. cbn [xeval].
  rewrite eget_eset_neq by exact Hkn. reflexivity.
Qed.

(** The first component of [RIota m n] is m iota - n, with iota the linear
    interpolant between the two half points at the free radius of slot 0. *)
Lemma igap_value :
  forall X,
  xeval (xextend X (r_binds igap_r3)) (r_s igap_r3) =
  Xsub (Xmul (Xreal (IZR hm))
             (Xadd (inval X 9)
                   (Xmul (Xdiv (Xsub (inval X 0) (inval X 7))
                               (Xsub (inval X 8) (inval X 7)))
                         (Xsub (inval X 10) (inval X 9)))))
       (Xreal (IZR hn)).
Proof.
  intros X.
  set (b0 := base_scratch_of lasym (RIota hm hn) (length modes)).
  assert (Hb0 : (11 <= b0)%nat).
  { unfold b0, base_scratch_of, base_W. destruct lasym; simpl; lia. }
  unfold igap_r3, residual. cbn [pc_out pc_lasym pc_prof is_radial].
  fold b0. unfold iota_b, alloc, bindings_of.
  cbn [b_next b_binds rev app r_binds r_s fst snd].
  unfold xextend. cbn [fold_left fst snd].
  cbn [xeval].
  repeat first [rewrite eget_eset_eq | rewrite eget_eset_neq by lia].
  cbn [xeval].
  unfold slot_iota_m, slot_iota_p, vS, slot_s_hm, slot_s_hp.
  repeat rewrite xeval_evar_eset by lia.
  unfold inval. reflexivity.
Qed.

(** m iota - n as a real function of the physical radius and of the half
    points' radii and iotas. *)
Definition gap_real (S0 SM SP IM IP : R) : R :=
  IZR hm * (IM + (S0 - SM) / (SP - SM) * (IP - IM)) - IZR hn.

(** The physical value of slot k of a state. *)
Definition phys (ys : list R) (k : nat) : R := nth k ys 0 * powerRZ 2 (nth k exps 0%Z).

Lemma inval_angles :
  forall ys u v k, (k < length ys)%nat -> k <> 1%nat -> k <> 2%nat ->
  inval (eset 1 (eset 2 (xenv_R ys) (Xreal v)) (Xreal u)) k = Xreal (phys ys k).
Proof.
  intros ys u v k Hk H1 H2. unfold inval.
  rewrite !xeval_evar_eset by lia. unfold evar. cbn [xeval].
  rewrite eget_xenv_R by exact Hk. reflexivity.
Qed.

(** Where the first component is real, the half points are distinct and it is
    [gap_real] of the state. *)
Lemma igap_real :
  forall ys u v w, (11 <= length ys)%nat ->
  xeval (surf 1 2 (r_binds igap_r3) (xenv_R ys) u v) (r_s igap_r3) = Xreal w ->
  phys ys 8 - phys ys 7 <> 0 /\
  w = gap_real (phys ys 0) (phys ys 7) (phys ys 8) (phys ys 9) (phys ys 10).
Proof.
  intros ys u v w Hl Hw. unfold surf in Hw. rewrite igap_value in Hw.
  rewrite !inval_angles in Hw by lia.
  cbn in Hw. unfold Xdiv' in Hw.
  destruct (is_zero_spec (phys ys 8 - phys ys 7)) as [Hz|Hz]; [discriminate|].
  injection Hw as <-. split. exact Hz. unfold gap_real. reflexivity.
Qed.

Lemma igap_at :
  forall ys u v, (11 <= length ys)%nat -> phys ys 8 - phys ys 7 <> 0 ->
  xeval (surf 1 2 (r_binds igap_r3) (xenv_R ys) u v) (r_s igap_r3) =
  Xreal (gap_real (phys ys 0) (phys ys 7) (phys ys 8) (phys ys 9) (phys ys 10)).
Proof.
  intros ys u v Hl Hz. unfold surf. rewrite igap_value.
  rewrite !inval_angles by lia.
  cbn. unfold Xdiv'.
  destruct (is_zero_spec (phys ys 8 - phys ys 7)) as [Hz'|Hz']; [contradiction|].
  unfold gap_real. reflexivity.
Qed.

End IotaGap.

(* ---------------------------------------------------------------- *)
(* The crossing                                                      *)

(** An affine function at most -eps at a and at least eps at b vanishes
    between them. *)
Lemma affine_crossing :
  forall c0 c1 a b eps,
  a <= b -> 0 < eps ->
  c0 + c1 * a <= - eps -> eps <= c0 + c1 * b ->
  exists s, a <= s <= b /\ c0 + c1 * s = 0.
Proof.
  intros c0 c1 a b eps Hab Heps Ha Hb.
  assert (Hc : 0 < c1).
  { destruct (Rle_lt_dec c1 0) as [Hle|Hlt]; [|exact Hlt].
    assert (c1 * (b - a) <= 0) by nra. lra. }
  exists (- c0 / c1).
  assert (Hs : c0 + c1 * (- c0 / c1) = 0) by (field; lra).
  split; [split|exact Hs].
  - apply Rmult_le_reg_l with c1; [exact Hc|].
    replace (c1 * (- c0 / c1)) with (- c0) by (field; lra). lra.
  - apply Rmult_le_reg_l with c1; [exact Hc|].
    replace (c1 * (- c0 / c1)) with (- c0) by (field; lra). lra.
Qed.

(** The state with the free radius of slot 0 replaced. *)
Definition set0 (xs : list R) (s : R) : list R :=
  match xs with [] => [] | _ :: tl => s :: tl end.

Lemma length_set0 : forall xs s, length (set0 xs s) = length xs.
Proof. intros [|x tl] s; reflexivity. Qed.

Lemma nth_set0_S : forall xs s k, nth (S k) (set0 xs s) 0 = nth (S k) xs 0.
Proof. intros [|x tl] s k; reflexivity. Qed.

Lemma nth_set0_0 : forall xs s, xs <> [] -> nth 0 (set0 xs s) 0 = s.
Proof. intros [|x tl] s H; [contradiction|reflexivity]. Qed.

Lemma phys_set0_S :
  forall exps xs s k, phys exps (set0 xs s) (S k) = phys exps xs (S k).
Proof. intros exps xs s k. unfold phys. rewrite nth_set0_S. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* Newcomb's condition                                               *)

(** The premise, in Fourier form: at every radius of an interval where iota
    is n/m and dp/ds is not zero, the resonant harmonic of the Jacobian in
    straight-field-line angles vanishes. [gap], [pp] and [harm] are m iota - n,
    mu0 dp/ds and the torus integral of sqrt(g) cos(m u - n v) as functions
    of the radius. *)
Definition newcomb_condition (gap pp harm : R -> R) (a b : R) : Prop :=
  forall s, a <= s <= b -> gap s = 0 -> pp s <> 0 -> harm s = 0.

(** The ceiling a harmonic certificate claims on its integral:
    -(integral) - N 2^q >= 0. *)
Definition harm_ceiling_e (N q : Z) : expr := Esub (Eneg (Evar 0)) (eps_e N q).

Lemma harm_ceiling_correct :
  forall prec T h N q,
  contains (I.convert T) (Xreal h) ->
  nonneg (ieval prec (eset 0 eempty T) (harm_ceiling_e N q)) = true ->
  h <= - (IZR N * powerRZ 2 q).
Proof.
  intros prec T h N q HT Hchk.
  assert (Henv : env_ok (eset 0 eempty T) (eset 0 eempty (Xreal h))).
  { apply env_ok_eset. apply env_ok_nil. exact HT. }
  destruct (nonneg_correct _ _ (ieval_correct prec _ _ (harm_ceiling_e N q) Henv) Hchk)
    as [r [Hr Hge]].
  unfold harm_ceiling_e in Hr. cbn [xeval] in Hr. rewrite eget_eset_eq in Hr.
  rewrite xeval_eps_e in Hr. simpl in Hr. injection Hr as <-. lra.
Qed.

Section Violated.

Variable lasym : bool.
Variable prof : pprofile.
Variable modes : list (Z * Z).
Variable exps : list Z.
Variable hm hn : Z.

(** The certificates and what ties them to one resonance and one state. *)
Variable hc : hcert.
Variable clo chi cpp : bpcert.
Variable plo phi ppt : bpt.
Variable NF qF : Z.

Hypothesis Hhc : check_harm hc = true.
Hypothesis Hhc_ceiling :
  nonneg (ieval (hprec_of hc) (eset 0 eempty (harm_total hc)) (harm_ceiling_e NF qF)) = true.
Hypothesis Hclo : check_bpcert clo = true.
Hypothesis Hchi : check_bpcert chi = true.
Hypothesis Hcpp : check_bpcert cpp = true.
Hypothesis Hplo : In plo (bpc_pts clo).
Hypothesis Hphi : In phi (bpc_pts chi).
Hypothesis Hppt : In ppt (bpc_pts cpp).
Hypothesis Hmlo : bp_mode plo = 3%Z.
Hypothesis Hmhi : bp_mode phi = 2%Z.
Hypothesis Hmpp : bp_mode ppt = 1%Z.
Hypothesis HNlo : (0 < bp_N plo)%Z.
Hypothesis HNhi : (0 < bp_N phi)%Z.

Hypothesis Hcfg_lo : bpc_cfg clo = PConfig lasym prof (RIota hm hn).
Hypothesis Hcfg_hi : bpc_cfg chi = PConfig lasym prof (RIota hm hn).
Hypothesis Hcfg_pp : bpc_cfg cpp = PConfig lasym prof (RNewcomb hm hn).
Hypothesis Hcfg_hc : hc_cfg hc = PConfig lasym prof (RNewcomb hm hn).
Hypothesis Hmodes : bpc_modes clo = modes /\ bpc_modes chi = modes /\
                    bpc_modes cpp = modes /\ hc_modes hc = modes.
Hypothesis Hexps : bpc_es clo = exps /\ bpc_es chi = exps /\
                   bpc_es cpp = exps /\ hc_es hc = exps.
Hypothesis Hslots : bpc_su clo = 1%nat /\ bpc_sv clo = 2%nat /\
                    bpc_su chi = 1%nat /\ bpc_sv chi = 2%nat /\
                    bpc_su cpp = 1%nat /\ bpc_sv cpp = 2%nat /\
                    hc_su hc = 1%nat /\ hc_sv hc = 2%nat.
Hypothesis Hcomps : bpc_comp clo = 0%nat /\ bpc_comp chi = 0%nat /\
                    bpc_comp cpp = 2%nat /\ hc_comp hc = 0%nat.

(** The state, and the interval of its free radius the boxes cover. *)
Variable xs : list R.
Variable a b : R.
Hypothesis Hab : a <= b.
Hypothesis Hlen : (11 <= length xs)%nat.
Hypothesis Hbox_lo : in_box (bpc_ms clo) (bpc_ds clo) (set0 xs a).
Hypothesis Hbox_hi : in_box (bpc_ms chi) (bpc_ds chi) (set0 xs b).
Hypothesis Hbox_mid : forall s, a <= s <= b ->
  in_box (hc_ms hc) (hc_ds hc) (set0 xs s) /\ in_box (bpc_ms cpp) (bpc_ds cpp) (set0 xs s).

Definition gap_of (s : R) : R :=
  gap_real hm hn (phys exps (set0 xs s) 0) (phys exps xs 7) (phys exps xs 8)
           (phys exps xs 9) (phys exps xs 10).

Theorem newcomb_violated :
  exists s, a <= s <= b /\
    xeval (surf 1 2 (r_binds (igap_r3 exps lasym prof modes hm hn))
                (xenv_R (set0 xs s)) 0 0)
          (r_s (igap_r3 exps lasym prof modes hm hn)) = Xreal 0 /\
    gap_of s = 0 /\
    (exists w,
       xeval (surf 1 2 (r_binds (bpres cpp)) (xenv_R (set0 xs s))
                   (IZR (bp_mu ppt)) (IZR (bp_mv ppt)))
             (icomp (bpres cpp) 2) = Xreal w /\
       IZR (bp_N ppt) * powerRZ 2 (bp_q ppt) <= Rabs w) /\
    harm_value hc (set0 xs s) <= - (IZR NF * powerRZ 2 qF).
Proof.
  destruct Hmodes as [Hm1 [Hm2 [Hm3 Hm4]]].
  destruct Hexps as [He1 [He2 [He3 He4]]].
  destruct Hslots as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 [Hs6 [Hs7 Hs8]]]]]]].
  destruct Hcomps as [Hc1 [Hc2 [Hc3 Hc4]]].
  assert (Hne : xs <> []) by (intros ->; simpl in Hlen; lia).
  assert (Hr_lo : bpres clo = igap_r3 exps lasym prof modes hm hn)
    by (unfold bpres, igap_r3; rewrite Hcfg_lo, Hm1, He1; reflexivity).
  assert (Hr_hi : bpres chi = igap_r3 exps lasym prof modes hm hn)
    by (unfold bpres, igap_r3; rewrite Hcfg_hi, Hm2, He2; reflexivity).
  (* the two ends *)
  assert (Slo := proj1 (Forall_forall _ _) (check_bpcert_correct clo Hclo) plo Hplo
                   (set0 xs a) Hbox_lo).
  assert (Shi := proj1 (Forall_forall _ _) (check_bpcert_correct chi Hchi) phi Hphi
                   (set0 xs b) Hbox_hi).
  destruct Slo as [wa [Hwa Cwa]]. destruct Shi as [wb [Hwb Cwb]].
  rewrite Hs1, Hs2, Hc1, Hr_lo in Hwa. rewrite Hs3, Hs4, Hc2, Hr_hi in Hwb.
  cbn [icomp] in Hwa, Hwb.
  unfold bpt_claim in Cwa, Cwb. rewrite Hmlo in Cwa. rewrite Hmhi in Cwb.
  cbn in Cwa, Cwb.
  assert (La : (11 <= length (set0 xs a))%nat) by (rewrite length_set0; exact Hlen).
  assert (Lb : (11 <= length (set0 xs b))%nat) by (rewrite length_set0; exact Hlen).
  destruct (igap_real exps lasym prof modes hm hn _ _ _ _ La Hwa) as [Hz Ea].
  destruct (igap_real exps lasym prof modes hm hn _ _ _ _ Lb Hwb) as [_ Eb].
  unfold phys in Hz, Ea, Eb.
  rewrite !nth_set0_S in Hz. rewrite !nth_set0_S in Ea. rewrite !nth_set0_S in Eb.
  rewrite nth_set0_0 in Ea by exact Hne. rewrite nth_set0_0 in Eb by exact Hne.
  (* the affine function of the free radius *)
  set (e0 := powerRZ 2 (nth 0 exps 0%Z)).
  set (SM := nth 7 xs 0 * powerRZ 2 (nth 7 exps 0%Z)) in *.
  set (SP := nth 8 xs 0 * powerRZ 2 (nth 8 exps 0%Z)) in *.
  set (IM := nth 9 xs 0 * powerRZ 2 (nth 9 exps 0%Z)) in *.
  set (IP := nth 10 xs 0 * powerRZ 2 (nth 10 exps 0%Z)) in *.
  set (c1 := IZR hm * (e0 / (SP - SM) * (IP - IM))).
  set (c0 := IZR hm * (IM - SM / (SP - SM) * (IP - IM)) - IZR hn).
  assert (Haff : forall s, gap_real hm hn (s * e0) SM SP IM IP = c0 + c1 * s).
  { intros s. unfold gap_real, c0, c1. field. exact Hz. }
  assert (Hepsa : 0 < IZR (bp_N plo) * powerRZ 2 (bp_q plo)).
  { apply Rmult_lt_0_compat. apply IZR_lt. exact HNlo. apply powerRZ_lt. lra. }
  assert (Hepsb : 0 < IZR (bp_N phi) * powerRZ 2 (bp_q phi)).
  { apply Rmult_lt_0_compat. apply IZR_lt. exact HNhi. apply powerRZ_lt. lra. }
  set (eps := Rmin (IZR (bp_N plo) * powerRZ 2 (bp_q plo))
                   (IZR (bp_N phi) * powerRZ 2 (bp_q phi))).
  assert (Heps : 0 < eps) by (apply Rmin_pos; assumption).
  assert (Ga : c0 + c1 * a <= - eps).
  { rewrite <- Haff. fold e0 in Ea. rewrite <- Ea.
    assert (eps <= IZR (bp_N plo) * powerRZ 2 (bp_q plo)) by apply Rmin_l. lra. }
  assert (Gb : eps <= c0 + c1 * b).
  { rewrite <- Haff. fold e0 in Eb. rewrite <- Eb.
    assert (eps <= IZR (bp_N phi) * powerRZ 2 (bp_q phi)) by apply Rmin_r. lra. }
  destruct (affine_crossing c0 c1 a b eps Hab Heps Ga Gb) as [s [Hs Hs0]].
  exists s. split. exact Hs.
  destruct (Hbox_mid s Hs) as [Bh Bp].
  assert (Ls : (11 <= length (set0 xs s))%nat) by (rewrite length_set0; exact Hlen).
  assert (Hzs : phys exps (set0 xs s) 8 - phys exps (set0 xs s) 7 <> 0).
  { unfold phys. rewrite !nth_set0_S. exact Hz. }
  assert (Gs : gap_real hm hn (phys exps (set0 xs s) 0) (phys exps (set0 xs s) 7)
                 (phys exps (set0 xs s) 8) (phys exps (set0 xs s) 9)
                 (phys exps (set0 xs s) 10) = 0).
  { unfold phys. rewrite !nth_set0_S. rewrite nth_set0_0 by exact Hne.
    fold e0 SM SP IM IP. rewrite Haff. exact Hs0. }
  split.
  { rewrite (igap_at exps lasym prof modes hm hn _ _ _ Ls Hzs). rewrite Gs. reflexivity. }
  split.
  { unfold gap_of.
    rewrite <- (phys_set0_S exps xs s 6), <- (phys_set0_S exps xs s 7),
            <- (phys_set0_S exps xs s 8), <- (phys_set0_S exps xs s 9).
    exact Gs. }
  split.
  { assert (Spp := proj1 (Forall_forall _ _) (check_bpcert_correct cpp Hcpp) ppt Hppt
                     (set0 xs s) Bp).
    destruct Spp as [w [Hw Cw]].
    rewrite Hs5, Hs6, Hc3 in Hw.
    unfold bpt_claim in Cw. rewrite Hmpp in Cw. cbn in Cw.
    exists w. split. exact Hw. exact Cw. }
  destruct (harm_correct hc Hhc (set0 xs s) Bh) as [_ Hin].
  exact (harm_ceiling_correct _ _ _ _ _ Hin Hhc_ceiling).
Qed.

End Violated.

(** So the premise fails for the state: at the radius the theorem finds, iota
    is n/m, dp/ds is not zero and the resonant harmonic is not zero. *)
Corollary newcomb_fails :
  forall (gap pp harm : R -> R) a b s F,
  a <= s <= b -> gap s = 0 -> pp s <> 0 -> harm s <= - F -> 0 < F ->
  ~ newcomb_condition gap pp harm a b.
Proof.
  intros gap pp harm a b s F Hs Hg Hp Hh HF Hn.
  assert (H0 := Hn s Hs Hg Hp). lra.
Qed.
