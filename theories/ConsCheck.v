(** The consistency check of the three-dimensional collocated rows.

    At the exact solution the radial row of collocation point kp is the
    output of [out_list u v 0 true], an expression in the node s (slot 0) and
    the step h (slot 1). The poloidal row is read in the coordinate
    t = s + h/2 of the outer half point it is formed at: [jet_layer_t] is the
    jet layer with every jet expression taken at s = t - h/2 ([subs0]), so
    that the output of [out_list_t] is the poloidal row of the node t - h/2
    as an expression in t and h.

    [cons2_cell_ok] decides, over a cell of s or t and every h in
    [-hhi, hhi], that the row and its first and second derivatives along h
    are real and that the second is within C; [cons2_sound] states it for
    the real functions of h, through DerivSeq. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Checker Newton TMEval RegResidual Jet LinCheck DerivSeq
  AdjointSound QDiff CellTM Check3d Ball3d Ball3dSound.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* An expression in place of slot 0                                  *)

Fixpoint subs0 (a e : expr) : expr :=
  match e with
  | Evar n     => if Nat.eqb n 0 then a else Evar n
  | EfromZ z   => EfromZ z
  | Epi        => Epi
  | Eneg x     => Eneg (subs0 a x)
  | Eadd x y   => Eadd (subs0 a x) (subs0 a y)
  | Esub x y   => Esub (subs0 a x) (subs0 a y)
  | Emul x y   => Emul (subs0 a x) (subs0 a y)
  | Ediv x y   => Ediv (subs0 a x) (subs0 a y)
  | Esqrt x    => Esqrt (subs0 a x)
  | Esin x     => Esin (subs0 a x)
  | Ecos x     => Ecos (subs0 a x)
  | Eexp x     => Eexp (subs0 a x)
  | Eatan x    => Eatan (subs0 a x)
  | Epow2 z    => Epow2 z
  end.

Lemma xeval_subs0 : forall a e E, xeval E (subs0 a e) = xeval (eset 0 E (xeval E a)) e.
Proof.
  intros a e E. induction e; cbn [subs0].
  - destruct (Nat.eqb_spec n 0) as [->|Hn]; cbn [xeval].
    + rewrite eget_eset_eq. reflexivity.
    + rewrite eget_eset_neq by exact Hn. reflexivity.
  all: cbn [xeval]; try rewrite IHe; try rewrite IHe1, IHe2; reflexivity.
Qed.

Lemma vars_below_subs0 :
  forall n a e, vars_below n a = true -> vars_below n e = true -> vars_below n (subs0 a e) = true.
Proof.
  intros n a e Ha. induction e; cbn [subs0 vars_below]; intros He;
    try (apply andb_prop in He; destruct He as [H1 H2]; rewrite IHe1, IHe2 by assumption; reflexivity);
    try (apply IHe; exact He); try exact He.
  destruct (Nat.eqb n0 0); [exact Ha | exact He].
Qed.

(* ---------------------------------------------------------------- *)
(* The lists                                                         *)

(** s = t - h/2, with t in slot 0 and h in slot 1. *)
Definition et : expr := Esub (Evar 0) (Emul ehalf2 (Evar 1)).

Definition jet_layer_t (u v : expr) : list binding :=
  map (fun i => (3 + i, subs0 et (jet_e u v (EfromZ 0) (EfromZ 0) (3 + i)))%nat) (seq 0 (ntop - 3)).

Definition out_list_t (u v : expr) : list binding :=
  jet_layer_t u v ++ reg_binds modes3d ++ [(rtop3, reg_fu modes3d)].

Lemma out_list_t_len : forall u v, length (out_list_t u v) = len0.
Proof.
  intros. unfold out_list_t, len0, jet_layer_t. rewrite !length_app, length_map, length_seq. cbn [length]. lia.
Qed.

(** The radial row in s, the poloidal row in t. *)
Definition clist (u v : expr) (r : bool) : list binding := if r then out_list u v 0 true else out_list_t u v.

Lemma clist_len : forall u v r, length (clist u v r) = len0.
Proof. intros u v [|]; [apply out_list_len | apply out_list_t_len]. Qed.

(** The row, its derivative along h at rtop3 + len0, and the derivative of
    that at rtop3 + 3 len0. *)
Definition hlist2 (u v : expr) (r : bool) : list binding :=
  with_dseq 1 3 (2 * len0) (with_dseq 1 3 len0 (clist u v r)).

Lemma rtop3_len0 : rtop3 = (2 + len0)%nat.
Proof. unfold rtop3, len0. rewrite ntop_val. lia. Qed.

Lemma len0_pos : (0 < len0)%nat.
Proof. unfold len0. lia. Qed.

(* ---------------------------------------------------------------- *)
(* The check                                                         *)

Section Check.

Variable prec : F.precision.

Definition zneg (z : Z * Z) : Z * Z := (Z.opp (fst z), snd z).

Definition cbox (slo shi hhi : Z * Z) : env I.type :=
  box_env prec (ival prec slo shi) (ival prec (zneg hhi) hhi).

Definition cons2_tab (u v : expr) (r : bool) (slo shi hhi : Z * Z) : option I.type :=
  let F := iextend prec (cbox slo shi hhi) (hlist2 u v r) in
  if rb prec (eget rtop3 F I.nai) && rb prec (eget (rtop3 + len0) F I.nai) && rb prec (eget (rtop3 + 3 * len0) F I.nai)
  then Some (ibound prec (eget (rtop3 + 3 * len0) F I.nai)) else None.

(** Point kp of the radial (r = true) or poloidal rows over cell c of s or t. *)
Definition cons2_cell_ok (C hhi : Z * Z) (r : bool) (kp c : nat) : bool :=
  match cons2_tab (fst (pt r kp)) (snd (pt r kp)) r (clo c) (chi c) hhi with
  | Some B => le_bound prec C B
  | None => false
  end.

End Check.

Strategy expand [jet_layer_t out_list_t clist hlist2 zneg cbox cons2_tab cons2_cell_ok].

(* ---------------------------------------------------------------- *)
(* Facts computed once                                               *)

Lemma clist_split :
  forall u v (r : bool), clist u v r = (if r then jet_layer u v 0 else jet_layer_t u v) ++ tail r.
Proof. intros u v [|]; unfold clist, out_list, out_list_t, tail; cbv beta iota; reflexivity. Qed.

Lemma tail_wf : forall r, well_formed 87 (tail r) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma layer_len : forall u v (r : bool), length (if r then jet_layer u v 0 else jet_layer_t u v) = 84%nat.
Proof. intros u v [|]; unfold jet_layer, jet_layer_t; rewrite length_map, length_seq, ntop_val; reflexivity. Qed.

Lemma clist_wf :
  forall (r : bool) kp, (kp < (if r then 5 else 4))%nat -> well_formed 3 (clist (fst (pt r kp)) (snd (pt r kp)) r) = true.
Proof.
  intros r kp Hkp. rewrite clist_split, DivDiff.well_formed_app. apply andb_true_intro. split.
  - destruct r; cbn in Hkp.
    + do 5 (destruct kp as [|kp]; [vm_compute; reflexivity|]). lia.
    + do 4 (destruct kp as [|kp]; [vm_compute; reflexivity|]). lia.
  - rewrite layer_len. apply tail_wf.
Qed.

(* ---------------------------------------------------------------- *)
(* Soundness                                                         *)

Lemma dyadR_zneg : forall z, dyadR (zneg z) = - dyadR z.
Proof. intros [m e]. unfold dyadR, zneg. cbn [fst snd]. rewrite opp_IZR. ring. Qed.

Lemma pin_high : forall s h t k, (3 <= k)%nat -> eget k (pin s h t) Xnan = Xnan.
Proof.
  intros s h t k Hk. unfold pin.
  rewrite (eget_eset_neq _ 2) by lia. rewrite (eget_eset_neq _ 1) by lia. rewrite (eget_eset_neq _ 0) by lia.
  apply eget_eempty.
Qed.

Lemma pin_low : forall s h t k, (k < 3)%nat -> exists y, eget k (pin s h t) Xnan = Xreal y.
Proof.
  intros s h t k Hk. unfold pin. destruct k as [|[|[|k]]].
  - exists s. rewrite (eget_eset_neq _ 2) by lia. rewrite (eget_eset_neq _ 1) by lia. apply eget_eset_eq.
  - exists h. rewrite (eget_eset_neq _ 2) by lia. apply eget_eset_eq.
  - exists t. apply eget_eset_eq.
  - lia.
Qed.

Lemma pin_1 : forall s h t x k, eget k (eset 1 (pin s h t) (Xreal x)) Xnan = eget k (pin s x t) Xnan.
Proof.
  intros s h t x k. unfold pin. destruct (Nat.eq_dec k 1) as [->|H1].
  - rewrite eget_eset_eq. rewrite (eget_eset_neq _ 2) by lia. rewrite eget_eset_eq. reflexivity.
  - rewrite (eget_eset_neq _ 1) by exact H1. destruct (Nat.eq_dec k 2) as [->|H2].
    + rewrite !eget_eset_eq. reflexivity.
    + rewrite !(eget_eset_neq _ 2) by exact H2. rewrite !(eget_eset_neq _ 1) by exact H1. reflexivity.
Qed.

Lemma pin_get1 : forall s h t, eget 1 (pin s h t) Xnan = Xreal h.
Proof. intros. unfold pin. rewrite (eget_eset_neq _ 2) by lia. apply eget_eset_eq. Qed.

Section Sound.

Variable prec : F.precision.

Lemma cbox_ok :
  forall slo shi hhi s h, dyadR slo <= s <= dyadR shi -> - dyadR hhi <= h <= dyadR hhi ->
  env_ok (cbox prec slo shi hhi) (pin s h 0).
Proof.
  intros slo shi hhi s h Hs Hh k. unfold cbox, box_env, pin.
  destruct (Nat.eq_dec k 2) as [->|H2]; [rewrite !eget_eset_eq; apply I.fromZ_correct|].
  rewrite !(eget_eset_neq _ 2) by exact H2.
  destruct (Nat.eq_dec k 1) as [->|H1].
  - rewrite !eget_eset_eq. apply ival_contains. rewrite dyadR_zneg. exact Hh.
  - rewrite !(eget_eset_neq _ 1) by exact H1. destruct (Nat.eq_dec k 0) as [->|H0].
    + rewrite !eget_eset_eq. apply ival_contains. exact Hs.
    + rewrite !(eget_eset_neq _ 0) by exact H0. rewrite !eget_eempty. rewrite I.nai_correct. exact I.
Qed.

End Sound.

(** Appending the derivative bindings leaves the lower slots. *)
Lemma with_dseq_low :
  forall x base n bs E k, (x < base)%nat -> (0 < n)%nat -> well_formed base bs = true -> (k < base + n)%nat ->
  eget k (xextend E (with_dseq x base n bs)) Xnan = eget k (xextend E bs) Xnan.
Proof.
  intros x base n bs E k Hx Hn Hwf Hk. unfold with_dseq. rewrite xextend_app.
  apply (eget_above _ _ (base + n)); [exact (dbinds_wf x base n Hx Hn bs base Hwf (le_n base)) | exact Hk].
Qed.

(** A real derivative slot is the derivative of its value slot along input x. *)
Lemma dseq_deriv :
  forall (x base n : nat) (bs : list binding) (env0 : env ExtendedR) (g : nat),
  (x < base)%nat -> (0 < n)%nat -> well_formed base bs = true -> length bs = n ->
  (forall k, (base <= k)%nat -> eget k env0 Xnan = Xnan) ->
  (forall k, (k < base)%nat -> exists v, eget k env0 Xnan = Xreal v) ->
  (base <= g < base + n)%nat ->
  (exists y, eget g (xextend env0 bs) Xnan = Xreal y) ->
  (exists d, eget (g + n) (xextend env0 (with_dseq x base n bs)) Xnan = Xreal d) ->
  derivable_pt_lim (fun t => xr (eget g (xextend (eset x env0 (Xreal t)) bs) Xnan))
                   (xr (eget x env0 Xnan))
                   (xr (eget (g + n) (xextend env0 (with_dseq x base n bs)) Xnan)).
Proof.
  intros x base n bs env0 g Hx Hn Hwf Hl Hun Hin Hg [y Hy] [d Hd].
  destruct (Hin x Hx) as [t0 Ht0].
  assert (HS := sinv_base x base n Hx Hn env0 Hun Hin).
  destruct (dseq_correct x base n Hx Hn bs (fun t => eset x env0 (Xreal t)) Hwf Hl HS) as [_ HD].
  specialize (HD (g - base)%nat t0 ltac:(lia)).
  replace (base + (g - base))%nat with g in HD by lia.
  replace (base + n + (g - base))%nat with (g + n)%nat in HD by lia.
  assert (HE : forall k, eget k (eset x env0 (Xreal t0)) Xnan = eget k env0 Xnan).
  { intros k. destruct (Nat.eq_dec k x) as [->|Hne];
      [rewrite eget_eset_eq; symmetry; exact Ht0 | apply eget_eset_neq; exact Hne]. }
  rewrite (env_agree _ _ env0 HE) in HD. rewrite Hd in HD.
  assert (Hlow : forall E, eget g (xextend E (with_dseq x base n bs)) Xnan = eget g (xextend E bs) Xnan).
  { intros E. apply with_dseq_low; [exact Hx | exact Hn | exact Hwf | lia]. }
  assert (Hv : slot_along (fun t => xextend (eset x env0 (Xreal t)) (with_dseq x base n bs)) g (Xreal t0) = Xreal y).
  { cbn [slot_along]. rewrite (env_agree _ _ env0 HE), Hlow. exact Hy. }
  rewrite Ht0, Hd. cbn [xr].
  assert (HX := Xderive_real _ t0 _ y Hv HD).
  eapply dpl_ext; [| exact HX]. intros t. cbn [slot_along]. rewrite Hlow. reflexivity.
Qed.

(** The three slots the check reads, as values of the inputs s (or t) and h. *)
Definition cv0 (L : list binding) (s h : R) : ExtendedR := eget rtop3 (xextend (pin s h 0) L) Xnan.
Definition cv1 (L : list binding) (s h : R) : ExtendedR :=
  eget (rtop3 + len0) (xextend (pin s h 0) (with_dseq 1 3 len0 L)) Xnan.
Definition cv2 (L : list binding) (s h : R) : ExtendedR :=
  eget (rtop3 + 3 * len0) (xextend (pin s h 0) (with_dseq 1 3 (2 * len0) (with_dseq 1 3 len0 L))) Xnan.

Strategy expand [cv0 cv1 cv2].

(** For a well-formed list of length len0 from 3 whose three slots are real
    at (s, h): the row's derivative along h is the first slot's, and the
    first's derivative is the second's. *)
Lemma cv_derivs :
  forall L s h, well_formed 3 L = true -> length L = len0 ->
  (exists y, cv0 L s h = Xreal y) -> (exists y, cv1 L s h = Xreal y) ->
  (exists y, cv2 L s h = Xreal y) ->
  derivable_pt_lim (fun x => xr (cv0 L s x)) h (xr (cv1 L s h)) /\
  derivable_pt_lim (fun x => xr (cv1 L s x)) h (xr (cv2 L s h)).
Proof.
  intros L s h Hwf Hl H0 H1 H2. unfold cv0, cv1, cv2 in *.
  assert (H13 : (1 < 3)%nat) by lia. assert (Hn := len0_pos).
  assert (Hr := rtop3_len0).
  assert (Hwf1 : well_formed 3 (with_dseq 1 3 len0 L) = true) by exact (with_dseq_wf 1 3 len0 H13 Hn L Hwf Hl).
  assert (Hl1 : length (with_dseq 1 3 len0 L) = (2 * len0)%nat) by (rewrite length_with_dseq, Hl; reflexivity).
  assert (Hn2 : (0 < 2 * len0)%nat) by lia.
  assert (Hun : forall k, (3 <= k)%nat -> eget k (pin s h 0) Xnan = Xnan) by (intros; apply pin_high; assumption).
  assert (Hin : forall k, (k < 3)%nat -> exists v, eget k (pin s h 0) Xnan = Xreal v) by (intros; apply pin_low; assumption).
  split.
  - assert (D := dseq_deriv 1 3 len0 L (pin s h 0) rtop3 H13 Hn Hwf Hl Hun Hin ltac:(lia) H0 H1).
    rewrite pin_get1 in D. change (xr (Xreal h)) with h in D.
    eapply dpl_ext; [| exact D]. intros x. cbv beta. apply (f_equal xr). apply env_agree. intros k. apply pin_1.
  - destruct H2 as [y2 H2].
    assert (H2' : exists y, eget (rtop3 + len0 + 2 * len0)
                    (xextend (pin s h 0) (with_dseq 1 3 (2 * len0) (with_dseq 1 3 len0 L))) Xnan = Xreal y).
    { exists y2. replace (rtop3 + len0 + 2 * len0)%nat with (rtop3 + 3 * len0)%nat by lia. exact H2. }
    assert (D := dseq_deriv 1 3 (2 * len0) (with_dseq 1 3 len0 L) (pin s h 0) (rtop3 + len0) H13 Hn2 Hwf1 Hl1
                   Hun Hin ltac:(lia) H1 H2').
    rewrite pin_get1 in D. change (xr (Xreal h)) with h in D.
    replace (rtop3 + len0 + 2 * len0)%nat with (rtop3 + 3 * len0)%nat in D by lia.
    eapply dpl_ext; [| exact D]. intros x. cbv beta. apply (f_equal xr). apply env_agree. intros k. apply pin_1.
Qed.

Lemma some_inj : forall (A : Type) (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. injection H as H. exact H. Qed.

(** The three slots of a passing table over its box, for any point. *)
Lemma cons2_tab_sound :
  forall prec u v r slo shi hhi B, well_formed 3 (clist u v r) = true ->
  cons2_tab prec u v r slo shi hhi = Some B ->
  forall s h, dyadR slo <= s <= dyadR shi -> - dyadR hhi <= h <= dyadR hhi ->
  (exists y, cv0 (clist u v r) s h = Xreal y) /\ (exists y, cv1 (clist u v r) s h = Xreal y) /\
  (exists y, cv2 (clist u v r) s h = Xreal y /\ Rabs y <= rmid B) /\
  contains (I.convert B) (Xreal (rmid B)).
Proof.
  intros prec u v r slo shi hhi B Hwf HT s h Hs Hh.
  assert (Hl := clist_len u v r).
  assert (HE := cbox_ok prec slo shi hhi s h Hs Hh).
  assert (HF := iextend_correct prec (hlist2 u v r) _ _ HE).
  unfold cons2_tab in HT. cbv zeta in HT.
  destruct (rb prec (eget rtop3 (iextend prec (cbox prec slo shi hhi) (hlist2 u v r)) I.nai) &&
            rb prec (eget (rtop3 + len0) (iextend prec (cbox prec slo shi hhi) (hlist2 u v r)) I.nai) &&
            rb prec (eget (rtop3 + 3 * len0) (iextend prec (cbox prec slo shi hhi) (hlist2 u v r)) I.nai)) eqn:H3;
    [| discriminate].
  apply some_inj in HT. subst B.
  apply andb_prop in H3. destruct H3 as [H3 Hc]. apply andb_prop in H3. destruct H3 as [Ha Hb].
  destruct (rb_sound prec _ _ (HF rtop3) Ha) as [y0 [E0 _]].
  destruct (rb_sound prec _ _ (HF (rtop3 + len0)%nat) Hb) as [y1 [E1 _]].
  destruct (rb_sound prec _ _ (HF (rtop3 + 3 * len0)%nat) Hc) as [y2 [E2 Hy2]].
  unfold hlist2 in E0, E1, E2.
  assert (H13 : (1 < 3)%nat) by lia. assert (Hn := len0_pos). assert (Hr := rtop3_len0).
  assert (Hwf1 : well_formed 3 (with_dseq 1 3 len0 (clist u v r)) = true)
    by exact (with_dseq_wf 1 3 len0 H13 Hn (clist u v r) Hwf Hl).
  rewrite (with_dseq_low 1 3 (2 * len0) _ _ rtop3 H13 ltac:(lia) Hwf1 ltac:(lia)) in E0.
  rewrite (with_dseq_low 1 3 len0 _ _ rtop3 H13 Hn Hwf ltac:(lia)) in E0.
  rewrite (with_dseq_low 1 3 (2 * len0) _ _ (rtop3 + len0) H13 ltac:(lia) Hwf1 ltac:(lia)) in E1.
  unfold cv0, cv1, cv2.
  split; [exists y0; exact E0|]. split; [exists y1; exact E1|]. split; [exists y2; split; [exact E2 | exact Hy2]|].
  exact (iupmax_in prec [I.abs (eget (rtop3 + 3 * len0) (iextend prec (cbox prec slo shi hhi) (hlist2 u v r)) I.nai)]).
Qed.

(** What a passing check states at every point of its box. *)
Theorem cons2_sound :
  forall prec C hhi (r : bool) kp c, (kp < (if r then 5 else 4))%nat ->
  cons2_cell_ok prec C hhi r kp c = true ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> - dyadR hhi <= h <= dyadR hhi ->
  (exists y, cv0 (clist (fst (pt r kp)) (snd (pt r kp)) r) s h = Xreal y) /\
  derivable_pt_lim (fun x => xr (cv0 (clist (fst (pt r kp)) (snd (pt r kp)) r) s x)) h
                   (xr (cv1 (clist (fst (pt r kp)) (snd (pt r kp)) r) s h)) /\
  derivable_pt_lim (fun x => xr (cv1 (clist (fst (pt r kp)) (snd (pt r kp)) r) s x)) h
                   (xr (cv2 (clist (fst (pt r kp)) (snd (pt r kp)) r) s h)) /\
  Rabs (xr (cv2 (clist (fst (pt r kp)) (snd (pt r kp)) r) s h)) <= dyadR C.
Proof.
  intros prec C hhi r kp c Hkp Hok s h Hs Hh.
  assert (Hwf := clist_wf r kp Hkp).
  assert (Hl := clist_len (fst (pt r kp)) (snd (pt r kp)) r).
  unfold cons2_cell_ok in Hok.
  destruct (cons2_tab prec (fst (pt r kp)) (snd (pt r kp)) r (clo c) (chi c) hhi) as [B|] eqn:HT; [| discriminate].
  destruct (cons2_tab_sound prec _ _ r _ _ hhi B Hwf HT s h Hs Hh) as (C0 & C1 & [y2 [E2 Hy2]] & HBc).
  destruct (cv_derivs _ s h Hwf Hl C0 C1 (ex_intro _ y2 E2)) as [D1 D2].
  split; [exact C0|]. split; [exact D1|]. split; [exact D2|].
  rewrite E2. change (xr (Xreal y2)) with y2.
  assert (HB := le_bound_sound prec C B (rmid B) HBc Hok). lra.
Qed.
