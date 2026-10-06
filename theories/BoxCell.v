(** A component bounded over a cell of two slots, at every state of a box.

    Cell.v bounds a component over a cell at the one state a file names. Here
    the state ranges over a box as in Box.v, so a verdict holds for every
    field whose inputs lie in it: the value at the centre of the cell is an
    interval over the box, and each step to a point of the cell is charged
    against a derivative bound taken over the cell and the box together. The
    derivative families are those of Integral.v, whose value slots agree with
    the plain bindings.

    [check_bccert_correct] states that a passing verdict bounds the component
    by the claimed N 2^q at every point of every cell and at every state of
    the box. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Quad Box Integral.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* One cell                                                          *)

Section OneCell.

Variable su sv : nat.
Hypothesis Huv : su <> sv.
Variable base len : nat.
Variable binds : list binding.
Hypothesis Hsu : (su < base)%nat.
Hypothesis Hsv : (sv < base)%nat.
Hypothesis Hlen0 : (0 < len)%nat.
Hypothesis Hwf : well_formed base binds = true.
Hypothesis Hlen : len = length binds.
Variable X : env ExtendedR.
Hypothesis HXu : forall k, (base <= k)%nat -> eget k X Xnan = Xnan.
Hypothesis HXr : forall k, (k < base)%nat -> exists v, eget k X Xnan = Xreal v.
Variable n : nat.
Hypothesis Hbn : (base <= n)%nat.
Hypothesis Hnl : (n < base + len)%nat.

(** The walk from the centre of a cell: along the first slot at the centre of
    the second, then along the second. *)
Lemma cell_walk :
  forall cu hu cv hv Du Dv w0 u v,
  0 <= hu -> 0 <= hv ->
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  eget n (surf su sv binds X cu cv) Xnan = Xreal w0 ->
  (forall u' v', cu - hu <= u' <= cu + hu -> cv - hv <= v' <= cv + hv ->
     exists d, eget (n + len) (EUs su sv base len binds X u' v') Xnan = Xreal d /\
               Rabs d <= Du) ->
  (forall u' v', cu - hu <= u' <= cu + hu -> cv - hv <= v' <= cv + hv ->
     exists d, eget (n + len) (EVs su sv base len binds X u' v') Xnan = Xreal d /\
               Rabs d <= Dv) ->
  exists w, eget n (surf su sv binds X u v) Xnan = Xreal w /\
            Rabs (w - w0) <= Du * hu + Dv * hv.
Proof using All.
  intros cu hu cv hv Du Dv w0 u v Hhu Hhv Hu Hv Hw0 HDu HDv.
  destruct (surf_HU su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr n Hbn Hnl)
    as [HU1 _].
  destruct (surf_HV su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr n Hbn Hnl)
    as [HV1 _].
  assert (EU := EUs_values su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr
                  n Hbn Hnl).
  assert (EV := EVs_values su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr
                  n Hbn Hnl).
  (* along the first slot at v = cv *)
  destruct (bound_between_dist (fun s => EUs su sv base len binds X s cv) n (n + len) Du
              (cu - hu) (cu + hu) cu u (HU1 cv)
              (fun t Ht => HDu t cv Ht ltac:(lra)) ltac:(lra) Hu)
    as [a0 [a1 [Ha0 [Ha1 Hinc_u]]]].
  (* along the second slot at u *)
  destruct (bound_between_dist (fun s => EVs su sv base len binds X u s) n (n + len) Dv
              (cv - hv) (cv + hv) cv v (HV1 u)
              (fun t Ht => HDv u t Hu Ht) ltac:(lra) Hv)
    as [b0 [b1 [Hb0 [Hb1 Hinc_v]]]].
  cbv beta in Ha0, Ha1, Hb0, Hb1.
  rewrite (EU cu cv n Hnl) in Ha0. rewrite (EU u cv n Hnl) in Ha1.
  rewrite (EV u cv n Hnl) in Hb0. rewrite (EV u v n Hnl) in Hb1.
  rewrite Hw0 in Ha0. injection Ha0 as <-.
  rewrite Ha1 in Hb0. injection Hb0 as <-.
  exists b1. split. exact Hb1.
  assert (HDu0 : 0 <= Du).
  { destruct (HDu cu cv ltac:(lra) ltac:(lra)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  assert (HDv0 : 0 <= Dv).
  { destruct (HDv cu cv ltac:(lra) ltac:(lra)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  replace (b1 - w0) with ((a1 - w0) + (b1 - a1)) by ring.
  eapply Rle_trans. apply Rabs_triang.
  apply Rplus_le_compat.
  - eapply Rle_trans. exact Hinc_u. apply Rmult_le_compat_l. exact HDu0.
    apply Rabs_le. lra.
  - eapply Rle_trans. exact Hinc_v. apply Rmult_le_compat_l. exact HDv0.
    apply Rabs_le. lra.
Qed.

(** The Taylor step itself, as the two legs use it: from the value and the
    derivative at c, with the second derivative bounded along the leg. *)
Lemma taylor_bound :
  forall a0 a1 d h Dd M x c,
  0 <= h -> Rabs d <= Dd -> 0 <= M -> Rabs (x - c) <= h ->
  Rabs (a1 - a0 - d * (x - c)) <= M * Rabs (x - c) * Rabs (x - c) ->
  Rabs (a1 - a0) <= h * Dd + M * h * h.
Proof.
  intros a0 a1 d h Dd M x c Hh Hd HM Hx Htay.
  assert (T1 : Rabs (d * (x - c)) <= h * Dd).
  { rewrite Rabs_mult. rewrite Rmult_comm.
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (T2 : M * Rabs (x - c) * Rabs (x - c) <= M * h * h).
  { apply Rmult_le_compat.
    - apply Rmult_le_pos. exact HM. apply Rabs_pos.
    - apply Rabs_pos.
    - apply Rmult_le_compat_l. exact HM. exact Hx.
    - exact Hx. }
  replace (a1 - a0) with ((a1 - a0 - d * (x - c)) + d * (x - c)) by ring.
  eapply Rle_trans. apply Rabs_triang. lra.
Qed.

(** The walk with both legs charged against derivatives on the line through
    the centre: along the first slot at the centre of the second, Taylor from
    the centre with the second derivative bounded along that line; then along
    the second slot, Taylor from the line with the first derivative bounded on
    the line and the second over the cell. Only the last of the four bounds
    ranges over the whole cell, and it is paid for against the square of the
    half-width. *)
Lemma cell_walk_tt :
  forall cu hu cv hv Du Duu Dv Dvv u v,
  0 <= hu -> 0 <= hv ->
  cu - hu <= u <= cu + hu -> cv - hv <= v <= cv + hv ->
  (exists d, eget (n + len) (EUs su sv base len binds X cu cv) Xnan = Xreal d /\
             Rabs d <= Du) ->
  (forall u', cu - hu <= u' <= cu + hu ->
     exists d, eget (n + 2 * len) (EUs su sv base len binds X u' cv) Xnan = Xreal d /\
               Rabs d <= Duu) ->
  (forall u', cu - hu <= u' <= cu + hu ->
     exists d, eget (n + len) (EVs su sv base len binds X u' cv) Xnan = Xreal d /\
               Rabs d <= Dv) ->
  (forall u' v', cu - hu <= u' <= cu + hu -> cv - hv <= v' <= cv + hv ->
     exists d, eget (n + 2 * len) (EVs su sv base len binds X u' v') Xnan = Xreal d /\
               Rabs d <= Dvv) ->
  exists w0 w,
    eget n (surf su sv binds X cu cv) Xnan = Xreal w0 /\
    eget n (surf su sv binds X u v) Xnan = Xreal w /\
    Rabs (w - w0) <= hu * Du + Duu * hu * hu + (hv * Dv + Dvv * hv * hv).
Proof using All.
  intros cu hu cv hv Du Duu Dv Dvv u v Hhu Hhv Hu Hv [d0 [Hd0 Hd0b]] HDuu HDv HDvv.
  destruct (surf_HU su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr n Hbn Hnl)
    as [HU1 HU2].
  destruct (surf_HV su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr n Hbn Hnl)
    as [HV1 HV2].
  assert (EU := EUs_values su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr
                  n Hbn Hnl).
  assert (EV := EVs_values su sv Huv base len binds Hsu Hsv Hlen0 Hwf Hlen X HXu HXr
                  n Hbn Hnl).
  (* along the first slot at v = cv, from the centre *)
  destruct (taylor_step (fun s => EUs su sv base len binds X s cv) n (n + len)
              (n + 2 * len) Duu cu hu Hhu (HU1 cv) (HU2 cv) HDuu)
    as [a0 [e0 [Ha0 [He0 Hstep]]]].
  cbv beta in Ha0, He0.
  rewrite Hd0 in He0. injection He0 as <-.
  destruct (Hstep u Hu) as [a1 [Ha1 Htay]]. cbv beta in Ha1.
  (* along the second slot at u, from the line v = cv *)
  destruct (taylor_step (fun s => EVs su sv base len binds X u s) n (n + len)
              (n + 2 * len) Dvv cv hv Hhv (HV1 u) (HV2 u)
              (fun t Ht => HDvv u t Hu Ht))
    as [b0 [e1 [Hb0 [He1 Hstep2]]]].
  cbv beta in Hb0, He1.
  destruct (HDv u Hu) as [d1 [Hd1 Hd1b]].
  rewrite Hd1 in He1. injection He1 as <-.
  destruct (Hstep2 v Hv) as [b1 [Hb1 Htay2]]. cbv beta in Hb1.
  rewrite (EU cu cv n Hnl) in Ha0. rewrite (EU u cv n Hnl) in Ha1.
  rewrite (EV u cv n Hnl) in Hb0. rewrite (EV u v n Hnl) in Hb1.
  rewrite Ha1 in Hb0. injection Hb0 as <-.
  exists a0, b1. split. exact Ha0. split. exact Hb1.
  assert (HDuu0 : 0 <= Duu).
  { destruct (HDuu cu ltac:(lra)) as [d [_ Hd]]. generalize (Rabs_pos d). lra. }
  assert (HDvv0 : 0 <= Dvv).
  { destruct (HDvv cu cv ltac:(lra) ltac:(lra)) as [d [_ Hd]].
    generalize (Rabs_pos d). lra. }
  assert (Hau : Rabs (u - cu) <= hu) by (apply Rabs_le; lra).
  assert (Hav : Rabs (v - cv) <= hv) by (apply Rabs_le; lra).
  assert (L1 := taylor_bound a0 a1 d0 hu Du Duu u cu Hhu Hd0b HDuu0 Hau Htay).
  assert (L2 := taylor_bound a1 b1 d1 hv Dv Dvv v cv Hhv Hd1b HDvv0 Hav Htay2).
  replace (b1 - a0) with ((a1 - a0) + (b1 - a1)) by ring.
  eapply Rle_trans. apply Rabs_triang. lra.
Qed.

End OneCell.

(* ---------------------------------------------------------------- *)
(* The certificate                                                   *)

Open Scope Z_scope.

(** Per cell: the centre mantissas of the two slots, and the claimed bounds on
    the two first derivatives and on the component. *)
Record bcell := BCellC {
  bl_mu : Z ; bl_mv : Z ;
  bl_NDu : Z ; bl_qDu : Z ;
  bl_NDv : Z ; bl_qDv : Z ;
  bl_Nc : Z ; bl_qc : Z }.

(** The state box, the two slots, their half-widths, the component, and the
    cells. *)
Record bccert := BCCert {
  bcc_prec : Z ;
  bcc_cfg : pconfig ;
  bcc_modes : list (Z * Z) ;
  bcc_es : list Z ;
  bcc_ms : list Z ;
  bcc_ds : list Z ;
  bcc_su : nat ; bcc_sv : nat ;
  bcc_du : Z ; bcc_dv : Z ;
  bcc_comp : nat ;
  bcc_cells : list bcell }.

Definition bcprec_of (c : bccert) : F.precision := F.PtoP (Z.to_pos (bcc_prec c)).
Definition bcres (c : bccert) : residual3 := residual (bcc_es c) (bcc_cfg c) (bcc_modes c).
Definition bcbase (c : bccert) : nat :=
  base_scratch_of (pc_lasym (bcc_cfg c)) (pc_out (bcc_cfg c)) (length (bcc_modes c)).

(** The claimed cell bound against the centre value and the two steps, once
    with the centre value and once with its negation:
    eps_c - (+-V + du Du + dv Dv) >= 0. *)
Definition bcell_comb_e (du dv : Z) (b : bcell) (neg : bool) (V : expr) : expr :=
  Esub (eps_e (bl_Nc b) (bl_qc b))
       (Eadd (if neg then Eneg V else V)
             (Eadd (Emul (EfromZ du) (eps_e (bl_NDu b) (bl_qDu b)))
                   (Emul (EfromZ dv) (eps_e (bl_NDv b) (bl_qDv b))))).

(** The checks of one cell. The centre value enters the combination through a
    scratch environment holding its enclosure in slot 0. *)
Definition check_bcell (prec : F.precision) (W : env I.type) (su sv len n : nat)
    (binds wu wv : list binding) (du dv : Z) (b : bcell) : bool :=
  let IB := icell_box prec W su sv (bl_mu b) (bl_mv b) du dv in
  let envu := iextend prec IB wu in
  let envv := iextend prec IB wv in
  let V := ieval prec (iextend prec (icell_centre prec W su sv (bl_mu b) (bl_mv b)) binds)
                 (Evar n) in
  let ev := eset 0 eempty V in
  check1 prec envu (Evar (n + len)) (bl_NDu b) (bl_qDu b) &&
  check1 prec envv (Evar (n + len)) (bl_NDv b) (bl_qDv b) &&
  nonneg (ieval prec ev (bcell_comb_e du dv b false (Evar 0))) &&
  nonneg (ieval prec ev (bcell_comb_e du dv b true (Evar 0))).

Definition check_bccert (c : bccert) : bool :=
  let prec := bcprec_of c in
  let r3 := bcres c in
  let binds := r_binds r3 in
  let base := bcbase c in
  let len := length binds in
  let su := bcc_su c in let sv := bcc_sv c in
  let W := wide_ienv prec (bcc_ms c) (bcc_ds c) in
  match slot_of (icomp r3 (bcc_comp c)) with
  | None => false
  | Some n =>
      let wu := with_derivs2 su base len binds in
      let wv := with_derivs2 sv base len binds in
      Nat.eqb (length (bcc_ms c)) base &&
      negb (Nat.eqb su sv) && Nat.ltb su base && Nat.ltb sv base &&
      Nat.ltb 0 len && well_formed base binds &&
      Nat.leb base n && Nat.ltb n (base + len) &&
      Z.leb 0 (bcc_du c) && Z.leb 0 (bcc_dv c) &&
      forallb (check_bcell prec W su sv len n binds wu wv (bcc_du c) (bcc_dv c))
              (bcc_cells c)
  end.

Close Scope Z_scope.

(** What a passing verdict says of one cell: at every state of the box and
    every point of the cell the component is real and within the cell bound. *)
Definition bcell_sound (c : bccert) (b : bcell) : Prop :=
  forall xs, in_box (bcc_ms c) (bcc_ds c) xs ->
  forall u v,
  IZR (bl_mu b - bcc_du c) <= u <= IZR (bl_mu b + bcc_du c) ->
  IZR (bl_mv b - bcc_dv c) <= v <= IZR (bl_mv b + bcc_dv c) ->
  exists w,
    xeval (surf (bcc_su c) (bcc_sv c) (r_binds (bcres c)) (xenv_R xs) u v)
          (icomp (bcres c) (bcc_comp c)) = Xreal w /\
    Rabs w <= IZR (bl_Nc b) * powerRZ 2 (bl_qc b).

(** The two combinations, as real inequalities. *)
Lemma bcell_comb_correct :
  forall prec du dv b V w0 neg,
  contains (I.convert V) (Xreal w0) ->
  nonneg (ieval prec (eset 0 eempty V) (bcell_comb_e du dv b neg (Evar 0))) = true ->
  (if neg then - w0 else w0)
  + (IZR du * (IZR (bl_NDu b) * powerRZ 2 (bl_qDu b))
     + IZR dv * (IZR (bl_NDv b) * powerRZ 2 (bl_qDv b)))
  <= IZR (bl_Nc b) * powerRZ 2 (bl_qc b).
Proof.
  intros prec du dv b V w0 neg HV Hchk.
  assert (Henv : env_ok (eset 0 eempty V) (eset 0 eempty (Xreal w0))).
  { apply env_ok_eset. apply env_ok_nil. exact HV. }
  assert (Hc := ieval_correct prec _ _ (bcell_comb_e du dv b neg (Evar 0)) Henv).
  destruct (nonneg_correct _ _ Hc Hchk) as [r [Hr Hge]].
  unfold bcell_comb_e in Hr.
  destruct neg; cbn [xeval] in Hr; rewrite eget_eset_eq in Hr;
    rewrite !xeval_eps_e in Hr; simpl in Hr; injection Hr as <-; lra.
Qed.

Theorem check_bccert_correct :
  forall c, check_bccert c = true -> Forall (bcell_sound c) (bcc_cells c).
Proof.
  intros c Hchk.
  unfold check_bccert in Hchk. cbv zeta in Hchk.
  revert Hchk.
  destruct (slot_of (icomp (bcres c) (bcc_comp c))) as [n|] eqn:Hn; intros Hchk;
    [|discriminate].
  assert (Hcomp : icomp (bcres c) (bcc_comp c) = Evar n).
  { destruct (icomp (bcres c) (bcc_comp c)); simpl in Hn; congruence. }
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
         end.
  match goal with H : Nat.eqb (length (bcc_ms c)) _ = true |- _ =>
    apply Nat.eqb_eq in H; rename H into Hms end.
  match goal with H : negb (Nat.eqb (bcc_su c) (bcc_sv c)) = true |- _ =>
    apply negb_true_iff, Nat.eqb_neq in H; rename H into Huv end.
  match goal with H : Nat.ltb (bcc_su c) _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hsu end.
  match goal with H : Nat.ltb (bcc_sv c) _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hsv end.
  match goal with H : Nat.ltb 0 _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hlen0 end.
  match goal with H : well_formed _ _ = true |- _ => rename H into Hwf end.
  match goal with H : Nat.leb _ n = true |- _ =>
    apply Nat.leb_le in H; rename H into Hbn end.
  match goal with H : Nat.ltb n _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hnl end.
  match goal with H : Z.leb 0 (bcc_du c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdu end.
  match goal with H : Z.leb 0 (bcc_dv c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdv end.
  match goal with H : forallb _ _ = true |- _ => rename H into Hcells end.
  apply Forall_forall. intros b Hb.
  rewrite forallb_forall in Hcells. specialize (Hcells b Hb).
  unfold check_bcell in Hcells. cbv zeta in Hcells.
  apply andb_prop in Hcells. destruct Hcells as [Hcells Hneg].
  apply andb_prop in Hcells. destruct Hcells as [Hcells Hpos].
  apply andb_prop in Hcells. destruct Hcells as [HDu HDv].
  intros xs Hin u v Hu Hv.
  rewrite Hcomp. cbn [xeval].
  set (prec := bcprec_of c) in *.
  set (binds := r_binds (bcres c)) in *.
  set (base := bcbase c) in *.
  set (len := length binds) in *.
  set (su := bcc_su c) in *. set (sv := bcc_sv c) in *.
  set (W := wide_ienv prec (bcc_ms c) (bcc_ds c)) in *.
  set (X := xenv_R xs).
  assert (HXin : length xs = base) by (destruct Hin as [Hl _]; lia).
  destruct (xenv_R_inputs xs base HXin) as [HXu HXr]. fold X in HXu, HXr.
  assert (HW : env_ok W X) by (unfold W, X; now apply wide_env_ok).
  set (mu := bl_mu b) in *. set (mv := bl_mv b) in *.
  set (du := bcc_du c) in *. set (dv := bcc_dv c) in *.
  assert (Hhu : 0 <= IZR du) by (apply IZR_le; exact Hdu).
  assert (Hhv : 0 <= IZR dv) by (apply IZR_le; exact Hdv).
  assert (Hcu : forall t, IZR mu - IZR du <= t <= IZR mu + IZR du ->
            IZR (mu - du) <= t <= IZR (mu + du))
    by (intros t Ht; rewrite minus_IZR, plus_IZR; exact Ht).
  assert (Hcv : forall t, IZR mv - IZR dv <= t <= IZR mv + IZR dv ->
            IZR (mv - dv) <= t <= IZR (mv + dv))
    by (intros t Ht; rewrite minus_IZR, plus_IZR; exact Ht).
  set (Du := IZR (bl_NDu b) * powerRZ 2 (bl_qDu b)).
  set (Dv := IZR (bl_NDv b) * powerRZ 2 (bl_qDv b)).
  assert (HbU : forall u' v', IZR mu - IZR du <= u' <= IZR mu + IZR du ->
            IZR mv - IZR dv <= v' <= IZR mv + IZR dv ->
            exists d, eget (n + len) (EUs su sv base len binds X u' v') Xnan = Xreal d
                      /\ Rabs d <= Du).
  { intros u' v' H1 H2.
    assert (Henv := iextend_correct prec (with_derivs2 su base len binds) _ _
                      (icell_box_ok prec W X su sv mu mv du dv u' v' HW
                         (Hcu u' H1) (Hcv v' H2))).
    destruct (check1_correct _ _ _ _ _ _ Henv HDu) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  assert (HbV : forall u' v', IZR mu - IZR du <= u' <= IZR mu + IZR du ->
            IZR mv - IZR dv <= v' <= IZR mv + IZR dv ->
            exists d, eget (n + len) (EVs su sv base len binds X u' v') Xnan = Xreal d
                      /\ Rabs d <= Dv).
  { intros u' v' H1 H2.
    assert (Henv : env_ok (iextend prec (icell_box prec W su sv mu mv du dv)
                                   (with_derivs2 sv base len binds))
                          (EVs su sv base len binds X u' v')).
    { unfold EVs, F2. apply iextend_correct.
      rewrite (eset_comm _ sv su) by (intros H; apply Huv; now symmetry).
      exact (icell_box_ok prec W X su sv mu mv du dv u' v' HW (Hcu u' H1) (Hcv v' H2)). }
    destruct (check1_correct _ _ _ _ _ _ Henv HDv) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  (* the centre value: real, since its first derivative is, and enclosed *)
  destruct (surf_HU su sv Huv base len binds Hsu Hsv Hlen0 Hwf eq_refl X HXu HXr
              n Hbn Hnl) as [HU1 _].
  assert (EU := EUs_values su sv Huv base len binds Hsu Hsv Hlen0 Hwf eq_refl X HXu HXr
                  n Hbn Hnl).
  assert (Hw0 : exists w0, eget n (surf su sv binds X (IZR mu) (IZR mv)) Xnan = Xreal w0).
  { destruct (HbU (IZR mu) (IZR mv) ltac:(lra) ltac:(lra)) as [d [Hd _]].
    specialize (HU1 (IZR mv) (IZR mu)). rewrite Hd in HU1.
    unfold Xderive_pt, slot_along in HU1.
    rewrite (EU (IZR mu) (IZR mv) n Hnl) in HU1.
    destruct (eget n (surf su sv binds X (IZR mu) (IZR mv)) Xnan) as [|w0].
    contradiction. now exists w0. }
  destruct Hw0 as [w0 Hw0].
  assert (HV : contains (I.convert (ieval prec (iextend prec
                  (icell_centre prec W su sv mu mv) binds) (Evar n))) (Xreal w0)).
  { rewrite <- Hw0.
    exact (ieval_correct prec _ _ (Evar n)
             (iextend_correct prec binds _ _
                (icell_centre_ok prec W X su sv mu mv HW))). }
  assert (C1 := bcell_comb_correct prec du dv b _ w0 false HV Hpos).
  assert (C2 := bcell_comb_correct prec du dv b _ w0 true HV Hneg).
  cbv iota in C1, C2.
  rewrite minus_IZR, plus_IZR in Hu, Hv.
  destruct (cell_walk su sv Huv base len binds Hsu Hsv Hlen0 Hwf eq_refl X HXu HXr
              n Hbn Hnl (IZR mu) (IZR du) (IZR mv) (IZR dv) Du Dv w0 u v Hhu Hhv
              Hu Hv Hw0 HbU HbV) as [w [Hw Hwb]].
  exists w. split. exact Hw.
  fold Du Dv in C1, C2.
  assert (H1 := Rle_abs (w - w0)).
  assert (H2 : - (w - w0) <= Rabs (w - w0)) by (rewrite <- Rabs_Ropp; apply Rle_abs).
  apply Rabs_le. split; nra.
Qed.

(* ---------------------------------------------------------------- *)
(* The Taylor cell over a box of states                              *)

(** The same verdict with both legs of the walk charged as [cell_walk_tt]
    charges them. The centre value and the first slot's derivative there are
    read from one evaluation of that slot's derivative family at the centre,
    whose value slots are the plain bindings; the first slot's second
    derivative and the second slot's first derivative from the families over
    the line through the centre along the first slot; and the second slot's
    second derivative from its family over the cell. *)

Open Scope Z_scope.

Record btcell := BTCellC {
  bt_mu : Z ; bt_mv : Z ;
  bt_NDu : Z ; bt_qDu : Z ;
  bt_NDuu : Z ; bt_qDuu : Z ;
  bt_NDv : Z ; bt_qDv : Z ;
  bt_NDvv : Z ; bt_qDvv : Z ;
  bt_Nc : Z ; bt_qc : Z }.

Record btcert := BTCert {
  btc_prec : Z ;
  btc_cfg : pconfig ;
  btc_modes : list (Z * Z) ;
  btc_es : list Z ;
  btc_ms : list Z ;
  btc_ds : list Z ;
  btc_su : nat ; btc_sv : nat ;
  btc_du : Z ; btc_dv : Z ;
  btc_comp : nat ;
  btc_cells : list btcell }.

Definition btprec_of (c : btcert) : F.precision := F.PtoP (Z.to_pos (btc_prec c)).
Definition btres (c : btcert) : residual3 := residual (btc_es c) (btc_cfg c) (btc_modes c).
Definition btbase (c : btcert) : nat :=
  base_scratch_of (pc_lasym (btc_cfg c)) (pc_out (btc_cfg c)) (length (btc_modes c)).

(** eps_c - (+-V + (du Du + du^2 Duu) + (dv Dv + dv^2 Dvv)) >= 0. *)
Definition btcell_comb_e (du dv : Z) (b : btcell) (neg : bool) (V : expr) : expr :=
  Esub (eps_e (bt_Nc b) (bt_qc b))
       (Eadd (if neg then Eneg V else V)
             (Eadd (Eadd (Emul (EfromZ du) (eps_e (bt_NDu b) (bt_qDu b)))
                         (Emul (Emul (EfromZ du) (EfromZ du))
                               (eps_e (bt_NDuu b) (bt_qDuu b))))
                   (Eadd (Emul (EfromZ dv) (eps_e (bt_NDv b) (bt_qDv b)))
                         (Emul (Emul (EfromZ dv) (EfromZ dv))
                               (eps_e (bt_NDvv b) (bt_qDvv b)))))).

Definition check_btcell (prec : F.precision) (W : env I.type) (su sv len n : nat)
    (wu wv : list binding) (du dv : Z) (b : btcell) : bool :=
  let IB := icell_box prec W su sv (bt_mu b) (bt_mv b) du dv in
  let IL := icell_box prec W su sv (bt_mu b) (bt_mv b) du 0 in
  let envc := iextend prec (icell_centre prec W su sv (bt_mu b) (bt_mv b)) wu in
  let envlu := iextend prec IL wu in
  let envlv := iextend prec IL wv in
  let envv := iextend prec IB wv in
  let ev := eset 0 eempty (ieval prec envc (Evar n)) in
  check1 prec envc (Evar (n + len)) (bt_NDu b) (bt_qDu b) &&
  check1 prec envlu (Evar (n + 2 * len)) (bt_NDuu b) (bt_qDuu b) &&
  check1 prec envlv (Evar (n + len)) (bt_NDv b) (bt_qDv b) &&
  check1 prec envv (Evar (n + 2 * len)) (bt_NDvv b) (bt_qDvv b) &&
  nonneg (ieval prec ev (btcell_comb_e du dv b false (Evar 0))) &&
  nonneg (ieval prec ev (btcell_comb_e du dv b true (Evar 0))).

Definition check_btcert (c : btcert) : bool :=
  let prec := btprec_of c in
  let r3 := btres c in
  let binds := r_binds r3 in
  let base := btbase c in
  let len := length binds in
  let su := btc_su c in let sv := btc_sv c in
  let W := wide_ienv prec (btc_ms c) (btc_ds c) in
  match slot_of (icomp r3 (btc_comp c)) with
  | None => false
  | Some n =>
      let wu := with_derivs2 su base len binds in
      let wv := with_derivs2 sv base len binds in
      Nat.eqb (length (btc_ms c)) base &&
      negb (Nat.eqb su sv) && Nat.ltb su base && Nat.ltb sv base &&
      Nat.ltb 0 len && well_formed base binds &&
      Nat.leb base n && Nat.ltb n (base + len) &&
      Z.leb 0 (btc_du c) && Z.leb 0 (btc_dv c) &&
      forallb (check_btcell prec W su sv len n wu wv (btc_du c) (btc_dv c))
              (btc_cells c)
  end.

Close Scope Z_scope.

Definition btcell_sound (c : btcert) (b : btcell) : Prop :=
  forall xs, in_box (btc_ms c) (btc_ds c) xs ->
  forall u v,
  IZR (bt_mu b - btc_du c) <= u <= IZR (bt_mu b + btc_du c) ->
  IZR (bt_mv b - btc_dv c) <= v <= IZR (bt_mv b + btc_dv c) ->
  exists w,
    xeval (surf (btc_su c) (btc_sv c) (r_binds (btres c)) (xenv_R xs) u v)
          (icomp (btres c) (btc_comp c)) = Xreal w /\
    Rabs w <= IZR (bt_Nc b) * powerRZ 2 (bt_qc b).

Lemma btcell_comb_correct :
  forall prec du dv b V w0 neg,
  contains (I.convert V) (Xreal w0) ->
  nonneg (ieval prec (eset 0 eempty V) (btcell_comb_e du dv b neg (Evar 0))) = true ->
  (if neg then - w0 else w0)
  + ((IZR du * (IZR (bt_NDu b) * powerRZ 2 (bt_qDu b))
      + IZR du * IZR du * (IZR (bt_NDuu b) * powerRZ 2 (bt_qDuu b)))
     + (IZR dv * (IZR (bt_NDv b) * powerRZ 2 (bt_qDv b))
        + IZR dv * IZR dv * (IZR (bt_NDvv b) * powerRZ 2 (bt_qDvv b))))
  <= IZR (bt_Nc b) * powerRZ 2 (bt_qc b).
Proof.
  intros prec du dv b V w0 neg HV Hchk.
  assert (Henv : env_ok (eset 0 eempty V) (eset 0 eempty (Xreal w0))).
  { apply env_ok_eset. apply env_ok_nil. exact HV. }
  assert (Hc := ieval_correct prec _ _ (btcell_comb_e du dv b neg (Evar 0)) Henv).
  destruct (nonneg_correct _ _ Hc Hchk) as [r [Hr Hge]].
  unfold btcell_comb_e in Hr.
  destruct neg; cbn [xeval] in Hr; rewrite eget_eset_eq in Hr;
    rewrite !xeval_eps_e in Hr; simpl in Hr; injection Hr as <-; lra.
Qed.

Theorem check_btcert_correct :
  forall c, check_btcert c = true -> Forall (btcell_sound c) (btc_cells c).
Proof.
  intros c Hchk.
  unfold check_btcert in Hchk. cbv zeta in Hchk.
  revert Hchk.
  destruct (slot_of (icomp (btres c) (btc_comp c))) as [n|] eqn:Hn; intros Hchk;
    [|discriminate].
  assert (Hcomp : icomp (btres c) (btc_comp c) = Evar n).
  { destruct (icomp (btres c) (btc_comp c)); simpl in Hn; congruence. }
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
         end.
  match goal with H : Nat.eqb (length (btc_ms c)) _ = true |- _ =>
    apply Nat.eqb_eq in H; rename H into Hms end.
  match goal with H : negb (Nat.eqb (btc_su c) (btc_sv c)) = true |- _ =>
    apply negb_true_iff, Nat.eqb_neq in H; rename H into Huv end.
  match goal with H : Nat.ltb (btc_su c) _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hsu end.
  match goal with H : Nat.ltb (btc_sv c) _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hsv end.
  match goal with H : Nat.ltb 0 _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hlen0 end.
  match goal with H : well_formed _ _ = true |- _ => rename H into Hwf end.
  match goal with H : Nat.leb _ n = true |- _ =>
    apply Nat.leb_le in H; rename H into Hbn end.
  match goal with H : Nat.ltb n _ = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hnl end.
  match goal with H : Z.leb 0 (btc_du c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdu end.
  match goal with H : Z.leb 0 (btc_dv c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdv end.
  match goal with H : forallb _ _ = true |- _ => rename H into Hcells end.
  apply Forall_forall. intros b Hb.
  rewrite forallb_forall in Hcells. specialize (Hcells b Hb).
  unfold check_btcell in Hcells. cbv zeta in Hcells.
  apply andb_prop in Hcells. destruct Hcells as [Hcells Hneg].
  apply andb_prop in Hcells. destruct Hcells as [Hcells Hpos].
  apply andb_prop in Hcells. destruct Hcells as [Hcells HDvv].
  apply andb_prop in Hcells. destruct Hcells as [Hcells HDv].
  apply andb_prop in Hcells. destruct Hcells as [HDu HDuu].
  intros xs Hin u v Hu Hv.
  rewrite Hcomp. cbn [xeval].
  set (prec := btprec_of c) in *.
  set (binds := r_binds (btres c)) in *.
  set (base := btbase c) in *.
  set (len := length binds) in *.
  set (su := btc_su c) in *. set (sv := btc_sv c) in *.
  set (W := wide_ienv prec (btc_ms c) (btc_ds c)) in *.
  set (X := xenv_R xs).
  assert (HXin : length xs = base) by (destruct Hin as [Hl _]; lia).
  destruct (xenv_R_inputs xs base HXin) as [HXu HXr]. fold X in HXu, HXr.
  assert (HW : env_ok W X) by (unfold W, X; now apply wide_env_ok).
  set (mu := bt_mu b) in *. set (mv := bt_mv b) in *.
  set (du := btc_du c) in *. set (dv := btc_dv c) in *.
  assert (Hhu : 0 <= IZR du) by (apply IZR_le; exact Hdu).
  assert (Hhv : 0 <= IZR dv) by (apply IZR_le; exact Hdv).
  assert (Hcu : forall t, IZR mu - IZR du <= t <= IZR mu + IZR du ->
            IZR (mu - du) <= t <= IZR (mu + du))
    by (intros t Ht; rewrite minus_IZR, plus_IZR; exact Ht).
  assert (Hcv : forall t, IZR mv - IZR dv <= t <= IZR mv + IZR dv ->
            IZR (mv - dv) <= t <= IZR (mv + dv))
    by (intros t Ht; rewrite minus_IZR, plus_IZR; exact Ht).
  set (Du := IZR (bt_NDu b) * powerRZ 2 (bt_qDu b)).
  set (Duu := IZR (bt_NDuu b) * powerRZ 2 (bt_qDuu b)).
  set (Dv := IZR (bt_NDv b) * powerRZ 2 (bt_qDv b)).
  set (Dvv := IZR (bt_NDvv b) * powerRZ 2 (bt_qDvv b)).
  (* the line through the centre along the first slot *)
  assert (Hline : IZR (mv - 0) <= IZR mv <= IZR (mv + 0))
    by (rewrite Z.sub_0_r, Z.add_0_r; lra).
  (* the first slot's family at the centre *)
  assert (Henvc : env_ok (iextend prec (icell_centre prec W su sv mu mv)
                                  (with_derivs2 su base len binds))
                         (EUs su sv base len binds X (IZR mu) (IZR mv))).
  { exact (iextend_correct prec (with_derivs2 su base len binds) _ _
             (icell_centre_ok prec W X su sv mu mv HW)). }
  assert (Hb0 : exists d, eget (n + len) (EUs su sv base len binds X (IZR mu) (IZR mv))
                            Xnan = Xreal d /\ Rabs d <= Du).
  { destruct (check1_correct _ _ _ _ _ _ Henvc HDu) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  assert (HbUU : forall u', IZR mu - IZR du <= u' <= IZR mu + IZR du ->
            exists d, eget (n + 2 * len) (EUs su sv base len binds X u' (IZR mv)) Xnan
                      = Xreal d /\ Rabs d <= Duu).
  { intros u' H1.
    assert (Henv := iextend_correct prec (with_derivs2 su base len binds) _ _
                      (icell_box_ok prec W X su sv mu mv du 0 u' (IZR mv) HW
                         (Hcu u' H1) Hline)).
    destruct (check1_correct _ _ _ _ _ _ Henv HDuu) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  assert (HbV : forall u', IZR mu - IZR du <= u' <= IZR mu + IZR du ->
            exists d, eget (n + len) (EVs su sv base len binds X u' (IZR mv)) Xnan
                      = Xreal d /\ Rabs d <= Dv).
  { intros u' H1.
    assert (Henv : env_ok (iextend prec (icell_box prec W su sv mu mv du 0)
                                   (with_derivs2 sv base len binds))
                          (EVs su sv base len binds X u' (IZR mv))).
    { unfold EVs, F2. apply iextend_correct.
      rewrite (eset_comm _ sv su) by (intros H; apply Huv; now symmetry).
      exact (icell_box_ok prec W X su sv mu mv du 0 u' (IZR mv) HW (Hcu u' H1) Hline). }
    destruct (check1_correct _ _ _ _ _ _ Henv HDv) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  assert (HbVV : forall u' v', IZR mu - IZR du <= u' <= IZR mu + IZR du ->
            IZR mv - IZR dv <= v' <= IZR mv + IZR dv ->
            exists d, eget (n + 2 * len) (EVs su sv base len binds X u' v') Xnan = Xreal d
                      /\ Rabs d <= Dvv).
  { intros u' v' H1 H2.
    assert (Henv : env_ok (iextend prec (icell_box prec W su sv mu mv du dv)
                                   (with_derivs2 sv base len binds))
                          (EVs su sv base len binds X u' v')).
    { unfold EVs, F2. apply iextend_correct.
      rewrite (eset_comm _ sv su) by (intros H; apply Huv; now symmetry).
      exact (icell_box_ok prec W X su sv mu mv du dv u' v' HW (Hcu u' H1) (Hcv v' H2)). }
    destruct (check1_correct _ _ _ _ _ _ Henv HDvv) as [d [Hd Hdb]].
    exists d. split. exact Hd. exact Hdb. }
  rewrite minus_IZR, plus_IZR in Hu, Hv.
  destruct (cell_walk_tt su sv Huv base len binds Hsu Hsv Hlen0 Hwf eq_refl X HXu HXr
              n Hbn Hnl (IZR mu) (IZR du) (IZR mv) (IZR dv) Du Duu Dv Dvv u v Hhu Hhv
              Hu Hv Hb0 HbUU HbV HbVV) as [w0 [w [Hw0 [Hw Hwb]]]].
  (* the centre value as the family reads it *)
  assert (EU := EUs_values su sv Huv base len binds Hsu Hsv Hlen0 Hwf eq_refl X HXu HXr
                  n Hbn Hnl).
  assert (HV : contains (I.convert (ieval prec (iextend prec
                  (icell_centre prec W su sv mu mv) (with_derivs2 su base len binds))
                  (Evar n))) (Xreal w0)).
  { rewrite <- Hw0, <- (EU (IZR mu) (IZR mv) n Hnl).
    exact (ieval_correct prec _ _ (Evar n) Henvc). }
  assert (C1 := btcell_comb_correct prec du dv b _ w0 false HV Hpos).
  assert (C2 := btcell_comb_correct prec du dv b _ w0 true HV Hneg).
  cbv iota in C1, C2.
  exists w. split. exact Hw.
  fold Du Duu Dv Dvv in C1, C2.
  assert (H1 := Rle_abs (w - w0)).
  assert (H2 : - (w - w0) <= Rabs (w - w0)) by (rewrite <- Rabs_Ropp; apply Rle_abs).
  apply Rabs_le. split; nra.
Qed.

(* ---------------------------------------------------------------- *)
(* The component at points                                           *)

(** A claim at each listed pair of angle mantissas on the component, at every
    state of the box: mode 0 bounds its magnitude from above by N 2^q, mode 1
    from below, mode 2 claims the component is at least N 2^q and mode 3 at
    most -N 2^q. The evaluation is at the point itself, so its enclosure is
    as narrow as the box of states allows. *)

Open Scope Z_scope.

Record bpt := BPt { bp_mu : Z ; bp_mv : Z ; bp_N : Z ; bp_q : Z ; bp_mode : Z }.

Record bpcert := BPCert {
  bpc_prec : Z ;
  bpc_cfg : pconfig ;
  bpc_modes : list (Z * Z) ;
  bpc_es : list Z ;
  bpc_ms : list Z ;
  bpc_ds : list Z ;
  bpc_su : nat ; bpc_sv : nat ;
  bpc_comp : nat ;
  bpc_pts : list bpt }.

Definition bpprec_of (c : bpcert) : F.precision := F.PtoP (Z.to_pos (bpc_prec c)).
Definition bpres (c : bpcert) : residual3 := residual (bpc_es c) (bpc_cfg c) (bpc_modes c).

Definition check_bpt (prec : F.precision) (W : env I.type) (su sv : nat)
    (binds : list binding) (r : expr) (p : bpt) : bool :=
  let env := iextend prec (icell_centre prec W su sv (bp_mu p) (bp_mv p)) binds in
  if Z.eqb (bp_mode p) 0 then check1 prec env r (bp_N p) (bp_q p)
  else if Z.eqb (bp_mode p) 1 then check1_lower prec env r (bp_N p) (bp_q p)
  else if Z.eqb (bp_mode p) 2 then
    nonneg (ieval prec env (Esub r (eps_e (bp_N p) (bp_q p))))
  else if Z.eqb (bp_mode p) 3 then
    nonneg (ieval prec env (Esub (Eneg r) (eps_e (bp_N p) (bp_q p))))
  else false.

Definition check_bpcert (c : bpcert) : bool :=
  let prec := bpprec_of c in
  let r3 := bpres c in
  forallb (check_bpt prec (wide_ienv prec (bpc_ms c) (bpc_ds c)) (bpc_su c) (bpc_sv c)
                     (r_binds r3) (icomp r3 (bpc_comp c)))
          (bpc_pts c).

Close Scope Z_scope.

Definition bpt_claim (mode : Z) (a w : R) : Prop :=
  if Z.eqb mode 0 then Rabs w <= a
  else if Z.eqb mode 1 then a <= Rabs w
  else if Z.eqb mode 2 then a <= w
  else w <= - a.

Definition bpt_sound (c : bpcert) (p : bpt) : Prop :=
  forall xs, in_box (bpc_ms c) (bpc_ds c) xs ->
  exists w,
    xeval (surf (bpc_su c) (bpc_sv c) (r_binds (bpres c)) (xenv_R xs)
                (IZR (bp_mu p)) (IZR (bp_mv p)))
          (icomp (bpres c) (bpc_comp c)) = Xreal w /\
    bpt_claim (bp_mode p) (IZR (bp_N p) * powerRZ 2 (bp_q p)) w.

Lemma sign_claim_correct :
  forall prec ienv xenv r N q (neg : bool),
  env_ok ienv xenv ->
  nonneg (ieval prec ienv (Esub (if neg then Eneg r else r) (eps_e N q))) = true ->
  exists w, xeval xenv r = Xreal w /\
            (if neg then w <= - (IZR N * powerRZ 2 q) else IZR N * powerRZ 2 q <= w).
Proof.
  intros prec ienv xenv r N q neg Henv Hchk.
  assert (Hc := ieval_correct prec _ _ (Esub (if neg then Eneg r else r) (eps_e N q)) Henv).
  destruct (nonneg_correct _ _ Hc Hchk) as [d [Hd Hge]].
  cbn [xeval] in Hd. rewrite xeval_eps_e in Hd.
  destruct neg; cbn [xeval] in Hd;
    destruct (xeval xenv r) as [|w]; simpl in Hd; try discriminate;
    injection Hd as <-; exists w; split; try reflexivity; lra.
Qed.

Theorem check_bpcert_correct :
  forall c, check_bpcert c = true -> Forall (bpt_sound c) (bpc_pts c).
Proof.
  intros c Hchk. unfold check_bpcert in Hchk. cbv zeta in Hchk.
  apply Forall_forall. intros p Hp.
  rewrite forallb_forall in Hchk. specialize (Hchk p Hp).
  intros xs Hin.
  assert (HW := wide_env_ok (bpprec_of c) (bpc_ms c) (bpc_ds c) xs Hin).
  assert (Henv := iextend_correct (bpprec_of c) (r_binds (bpres c)) _ _
                    (icell_centre_ok (bpprec_of c) _ (xenv_R xs) (bpc_su c) (bpc_sv c)
                       (bp_mu p) (bp_mv p) HW)).
  unfold check_bpt in Hchk. unfold bpt_claim.
  destruct (Z.eqb (bp_mode p) 0).
  { destruct (check1_correct _ _ _ _ _ _ Henv Hchk) as [w [Hw Hb]].
    exists w. split. exact Hw. exact Hb. }
  destruct (Z.eqb (bp_mode p) 1).
  { destruct (check1_lower_correct _ _ _ _ _ _ Henv Hchk) as [w [Hw Hb]].
    exists w. split. exact Hw. exact Hb. }
  destruct (Z.eqb (bp_mode p) 2).
  { destruct (sign_claim_correct _ _ _ _ _ _ false Henv Hchk) as [w [Hw Hb]].
    exists w. split. exact Hw. exact Hb. }
  destruct (Z.eqb (bp_mode p) 3); [|discriminate].
  destruct (sign_claim_correct _ _ _ _ _ _ true Henv Hchk) as [w [Hw Hb]].
  exists w. split. exact Hw. exact Hb.
Qed.

(* ---------------------------------------------------------------- *)
(* The cells tile a field period                                     *)

(** A certificate bounds each cell it lists. That the cells leave no gap
    over a field period of the surface is a property of the list, checked
    here: the cells are, in order, the grid of nu by nv cells from (au, av)
    in mantissa units, and the grid reaches from at most 0 to at least a
    period of each angle in physical units, 2 pi in the first and 2 pi / nfp
    in the second, which the checker decides against its enclosure of pi. *)

Fixpoint zz_eqb (l1 l2 : list (Z * Z)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a, b) :: t1, (c, d) :: t2 => Z.eqb a c && Z.eqb b d && zz_eqb t1 t2
  | _, _ => false
  end.

Lemma zz_eqb_eq : forall l1 l2, zz_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|[a b] t1 IH]; intros [|[c d] t2] H; simpl in H;
    try discriminate; try reflexivity.
  apply andb_prop in H. destruct H as [H Ht].
  apply andb_prop in H. destruct H as [Ha Hb].
  apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst.
  now rewrite (IH t2 Ht).
Qed.

Definition grid (au du av dv : Z) (nu nv : nat) : list (Z * Z) :=
  flat_map (fun j => map (fun i => (icentre au du i, icentre av dv j)) (seq 0 nu))
           (seq 0 nv).

Lemma in_grid :
  forall au du av dv nu nv i j, (i < nu)%nat -> (j < nv)%nat ->
  In (icentre au du i, icentre av dv j) (grid au du av dv nu nv).
Proof.
  intros au du av dv nu nv i j Hi Hj. unfold grid.
  apply in_flat_map. exists j. split.
  - apply in_seq. lia.
  - apply (in_map (fun i => (icentre au du i, icentre av dv j))). apply in_seq. lia.
Qed.

(** A point of [a, a + 2 N d] lies in one of the N cells of half-width d. *)
Lemma tile_index :
  forall a d N x, 0 <= IZR d -> (0 < N)%nat ->
  IZR a <= x <= IZR a + 2 * INR N * IZR d ->
  exists i, (i < N)%nat /\
    IZR (icentre a d i) - IZR d <= x <= IZR (icentre a d i) + IZR d.
Proof.
  intros a d N x Hd. induction N as [|N IH]; intros HN Hx; [lia|].
  destruct (Nat.eq_dec N 0) as [->|HN0].
  - exists 0%nat. split; [lia|].
    destruct (icentre_edges a d 0) as [E1 E2]. rewrite E1, E2.
    simpl in Hx |- *. lra.
  - destruct (Rle_dec x (IZR a + 2 * INR N * IZR d)) as [Hle|Hgt].
    + destruct (IH ltac:(lia) (conj (proj1 Hx) Hle)) as [i [Hi Hin]].
      exists i. split; [lia|exact Hin].
    + apply Rnot_le_lt in Hgt.
      exists N. split; [lia|].
      destruct (icentre_edges a d N) as [E1 E2]. rewrite E1, E2. lra.
Qed.

Definition bt_tiles (c : btcert) (au av : Z) (nu nv : nat) : bool :=
  zz_eqb (map (fun b => (bt_mu b, bt_mv b)) (btc_cells c))
         (grid au (btc_du c) av (btc_dv c) nu nv) &&
  Z.leb 0 (btc_du c) && Z.leb 0 (btc_dv c) && Nat.ltb 0 nu && Nat.ltb 0 nv.

Theorem bt_tiles_cover :
  forall c au av nu nv, bt_tiles c au av nu nv = true ->
  forall u v,
  IZR au <= u <= IZR au + 2 * INR nu * IZR (btc_du c) ->
  IZR av <= v <= IZR av + 2 * INR nv * IZR (btc_dv c) ->
  exists b, In b (btc_cells c) /\
    IZR (bt_mu b - btc_du c) <= u <= IZR (bt_mu b + btc_du c) /\
    IZR (bt_mv b - btc_dv c) <= v <= IZR (bt_mv b + btc_dv c).
Proof.
  intros c au av nu nv Ht u v Hu Hv.
  unfold bt_tiles in Ht.
  repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  match goal with H : zz_eqb _ _ = true |- _ =>
    apply zz_eqb_eq in H; rename H into Heq end.
  match goal with H : Z.leb 0 (btc_du c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdu end.
  match goal with H : Z.leb 0 (btc_dv c) = true |- _ =>
    apply Z.leb_le in H; rename H into Hdv end.
  match goal with H : Nat.ltb 0 nu = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hnu end.
  match goal with H : Nat.ltb 0 nv = true |- _ =>
    apply Nat.ltb_lt in H; rename H into Hnv end.
  destruct (tile_index au (btc_du c) nu u (IZR_le 0 _ Hdu) Hnu Hu) as [i [Hi Hui]].
  destruct (tile_index av (btc_dv c) nv v (IZR_le 0 _ Hdv) Hnv Hv) as [j [Hj Hvj]].
  assert (Hg := in_grid au (btc_du c) av (btc_dv c) nu nv i j Hi Hj).
  rewrite <- Heq in Hg.
  apply in_map_iff in Hg. destruct Hg as [b [Hbe Hb]].
  injection Hbe as Hmu Hmv.
  exists b. split. exact Hb.
  rewrite !minus_IZR, !plus_IZR, Hmu, Hmv. split; lra.
Qed.

(** The grid reaches a period: k (a + 2 n d) 2^e - 2 pi >= 0. *)
Definition period_e (a d : Z) (n : nat) (e k : Z) : expr :=
  Esub (Emul (EfromZ k) (Emul (EfromZ (a + 2 * Z.of_nat n * d)) (Epow2 e)))
       (Emul (EfromZ 2) Epi).

Lemma period_correct :
  forall prec a d n e k,
  nonneg (ieval prec eempty (period_e a d n e k)) = true ->
  2 * PI <= IZR k * (IZR (a + 2 * Z.of_nat n * d) * powerRZ 2 e).
Proof.
  intros prec a d n e k H.
  remember (a + 2 * Z.of_nat n * d)%Z as A eqn:HA.
  destruct (nonneg_correct _ _ (ieval_correct prec eempty eempty _ env_ok_nil) H)
    as [r [Hr Hge]].
  unfold period_e in Hr. rewrite <- HA in Hr.
  cbn [xeval] in Hr. simpl in Hr. injection Hr as <-. lra.
Qed.

Definition bt_period (c : btcert) (au av : Z) (nu nv : nat) (nfp : Z) : bool :=
  let prec := btprec_of c in
  let eu := nth (btc_su c) (btc_es c) 0%Z in
  let ev := nth (btc_sv c) (btc_es c) 0%Z in
  Z.leb au 0 && Z.leb av 0 && Z.ltb 0 nfp &&
  nonneg (ieval prec eempty (period_e au (btc_du c) nu eu 1)) &&
  nonneg (ieval prec eempty (period_e av (btc_dv c) nv ev nfp)).

(** The largest cell bound. *)
Definition btsup (c : btcert) : R :=
  fold_right Rmax 0 (map (fun b => IZR (bt_Nc b) * powerRZ 2 (bt_qc b)) (btc_cells c)).

Lemma fold_Rmax_ge : forall l x, In x l -> x <= fold_right Rmax 0 l.
Proof.
  induction l as [|a l IH]; intros x Hx; simpl in Hx |- *. contradiction.
  destruct Hx as [<-|Hx]. apply Rmax_l.
  eapply Rle_trans. apply IH, Hx. apply Rmax_r.
Qed.

(** From a physical angle to the mantissa units of its slot, for an angle in
    the period the grid spans. *)
Lemma angle_in_grid :
  forall a d n e k X,
  0 < IZR k -> IZR a <= 0 ->
  2 * PI <= IZR k * (IZR (a + 2 * Z.of_nat n * d) * powerRZ 2 e) ->
  0 <= X <= 2 * PI / IZR k ->
  IZR a <= X / powerRZ 2 e <= IZR a + 2 * INR n * IZR d.
Proof.
  intros a d n e k X Hk Ha Hp HX.
  assert (Hpe : 0 < powerRZ 2 e) by (apply powerRZ_lt; lra).
  set (A := IZR (a + 2 * Z.of_nat n * d)) in Hp.
  assert (HA : A = IZR a + 2 * INR n * IZR d).
  { unfold A. rewrite plus_IZR, !mult_IZR, <- INR_IZR_INZ. ring. }
  assert (HXA : X <= A * powerRZ 2 e).
  { destruct HX as [_ HX].
    apply Rle_trans with (2 * PI / IZR k). exact HX.
    unfold Rdiv. apply Rle_trans with (IZR k * (A * powerRZ 2 e) * / IZR k).
    - apply Rmult_le_compat_r. left. now apply Rinv_0_lt_compat. exact Hp.
    - right. field. lra. }
  rewrite <- HA. split.
  - apply Rle_trans with 0. exact Ha.
    unfold Rdiv. apply Rmult_le_pos. lra. left. now apply Rinv_0_lt_compat.
  - unfold Rdiv. apply Rle_trans with (A * powerRZ 2 e * / powerRZ 2 e).
    + apply Rmult_le_compat_r. left. now apply Rinv_0_lt_compat. exact HXA.
    + right. field. lra.
Qed.

(** The verdict over the whole surface: at every point of a field period and
    every state of the box the component is real and at most the largest cell
    bound. The angles are physical, the slot values times their powers of
    two. *)
Theorem bt_surface :
  forall c au av nu nv nfp,
  check_btcert c = true -> bt_tiles c au av nu nv = true ->
  bt_period c au av nu nv nfp = true ->
  forall xs, in_box (btc_ms c) (btc_ds c) xs ->
  forall U V, 0 <= U <= 2 * PI -> 0 <= V <= 2 * PI / IZR nfp ->
  exists w,
    xeval (surf (btc_su c) (btc_sv c) (r_binds (btres c)) (xenv_R xs)
                (U / powerRZ 2 (nth (btc_su c) (btc_es c) 0%Z))
                (V / powerRZ 2 (nth (btc_sv c) (btc_es c) 0%Z)))
          (icomp (btres c) (btc_comp c)) = Xreal w /\
    Rabs w <= btsup c.
Proof.
  intros c au av nu nv nfp Hc Ht Hp xs Hin U V HU HV.
  unfold bt_period in Hp. cbv zeta in Hp.
  repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  match goal with H : Z.leb au 0 = true |- _ =>
    apply Z.leb_le, IZR_le in H; rename H into Hau end.
  match goal with H : Z.leb av 0 = true |- _ =>
    apply Z.leb_le, IZR_le in H; rename H into Hav end.
  match goal with H : Z.ltb 0 nfp = true |- _ =>
    apply Z.ltb_lt, IZR_lt in H; rename H into Hnfp end.
  match goal with H : nonneg (ieval _ _ (period_e au _ _ _ _)) = true |- _ =>
    apply period_correct in H; rename H into Pu end.
  match goal with H : nonneg (ieval _ _ (period_e av _ _ _ _)) = true |- _ =>
    apply period_correct in H; rename H into Pv end.
  assert (Hu := angle_in_grid au (btc_du c) nu _ 1 U ltac:(simpl; lra) Hau Pu
                  ltac:(simpl IZR; unfold Rdiv; rewrite Rinv_1, Rmult_1_r; exact HU)).
  assert (Hv := angle_in_grid av (btc_dv c) nv _ nfp V Hnfp Hav Pv HV).
  destruct (bt_tiles_cover c au av nu nv Ht _ _ Hu Hv) as [b [Hb [Hbu Hbv]]].
  assert (Hs := proj1 (Forall_forall _ _) (check_btcert_correct c Hc) b Hb).
  destruct (Hs xs Hin _ _ Hbu Hbv) as [w [Hw Hwb]].
  exists w. split. exact Hw.
  eapply Rle_trans. exact Hwb.
  apply fold_Rmax_ge.
  apply (in_map (fun b => IZR (bt_Nc b) * powerRZ 2 (bt_qc b))). exact Hb.
Qed.
