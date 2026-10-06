(** * The stages of the continuum reconstruction

    Each stage of [full_point_b] that recurs over the modes allocates a few
    bindings per mode. For each, this file states which bindings it adds and
    what the coefficients and kernels it returns refer to: the kernels
    ([kernels_spec]), the half-point coefficients ([halfcoefs_spec]), the
    Hermite coefficients ([hermcoefs_spec]) and the coefficients of lambda
    ([radcoefs_spec]). A builder only grows ([extends]), so a binding added
    by any stage is among the final bindings. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics.
Import ListNotations.

Definition extends (b b' : builder) : Prop := exists l, b_binds b' = l ++ b_binds b.

Lemma extends_refl (b : builder) : extends b b.
Proof. exists []. reflexivity. Qed.

Lemma extends_trans (a b c : builder) : extends a b -> extends b c -> extends a c.
Proof. intros [l1 H1] [l2 H2]. exists (l2 ++ l1). rewrite H2, H1, app_assoc. reflexivity. Qed.

Lemma in_extends (b b' : builder) (q : binding) : extends b b' -> In q (b_binds b) -> In q (b_binds b').
Proof. intros [l H] Hq. rewrite H. apply in_or_app. right. exact Hq. Qed.

Lemma alloc_spec (b : builder) (e : expr) (b' : builder) (x : expr) :
  alloc b e = (b', x) -> extends b b' /\ In (b_next b, e) (b_binds b') /\ x = Evar (b_next b).
Proof.
  unfold alloc. intros H. injection H as <- <-.
  split; [exists [(b_next b, e)]; reflexivity | split; [left; reflexivity | reflexivity]].
Qed.

Ltac allocs :=
  repeat match goal with
  | A : alloc _ _ = (_, _) |- _ =>
      apply alloc_spec in A; let X := fresh "X" in let I := fresh "I" in destruct A as [X [I ->]]
  end.

Ltac lift :=
  repeat match goal with
  | X : extends ?a ?b, I : In ?q (b_binds ?a) |- _ =>
      apply (in_extends a b q X) in I
  end.

Section Stages.
Variable exps : list Z.

(** The kernels: for each mode, a slot holding cos(m u - n v) and one
    holding sin(m u - n v). *)
Lemma kernels_spec (modes : list (Z * Z)) : forall b b' kers,
  kernels_b exps b modes = (b', kers) -> extends b b' /\
  Forall2 (fun mn k => mk_m k = fst mn /\ mk_n k = snd mn /\
    (exists c, mk_cos k = Evar c /\ In (c, Ecos (kern_arg exps (fst mn) (snd mn))) (b_binds b')) /\
    (exists c, mk_sin k = Evar c /\ In (c, Esin (kern_arg exps (fst mn) (snd mn))) (b_binds b'))) modes kers.
Proof.
  induction modes as [| [mm nn] tl IH]; intros b b' kers H.
  - cbn in H. injection H as <- <-. split; [apply extends_refl | constructor].
  - cbn [kernels_b] in H.
    destruct (alloc b (Ecos (kern_arg exps mm nn))) as [b1 c] eqn:A1.
    destruct (alloc b1 (Esin (kern_arg exps mm nn))) as [b2 s] eqn:A2.
    destruct (kernels_b exps b2 tl) as [b3 rest] eqn:A3.
    injection H as <- <-. destruct (IH _ _ _ A3) as [X3 F3]. allocs.
    split; [repeat (eapply extends_trans; [eassumption |]); apply extends_refl |].
    constructor; [| exact F3]. cbn [fst snd mk_m mk_n mk_cos mk_sin]. lift.
    split; [reflexivity | split; [reflexivity | split]];
      (eexists; split; [reflexivity | eassumption]).
Qed.

(** The half-point coefficients: every value and slope is a slot the stage
    binds. *)
Definition bound (b : builder) (e : expr) : Prop := exists n x, e = Evar n /\ In (n, x) (b_binds b).

Lemma bound_extends (b b' : builder) (e : expr) : extends b b' -> bound b e -> bound b' e.
Proof. intros X [n [x [-> I]]]. exists n, x. split; [reflexivity | exact (in_extends _ _ _ X I)]. Qed.

Lemma halfcoefs_spec (hs : half_scalars) (base K ra rb : nat) (modes : list (Z * Z)) : forall k b b' cs,
  halfcoefs_b exps b hs base K ra rb modes k = (b', cs) -> extends b b' /\
  length cs = length modes /\ Forall (fun c => bound b' (c_val c) /\ bound b' (c_ds c)) cs.
Proof.
  induction modes as [| mn tl IH]; intros k b b' cs H.
  - cbn in H. injection H as <- <-. split; [apply extends_refl | split; [reflexivity | constructor]].
  - cbn [halfcoefs_b] in H.
    destruct (halfcoef_b b hs (fst mn) (slot_node exps base K ra k) (slot_node exps base K rb k))
      as [b1 c] eqn:A1.
    destruct (halfcoefs_b exps b1 hs base K ra rb tl (S k)) as [b2 rest] eqn:A2.
    injection H as <- <-.
    assert (Hc : extends b b1 /\ bound b1 (c_val c) /\ bound b1 (c_ds c)).
    { unfold halfcoef_b in A1. destruct (Z.even (fst mn)).
      - destruct (alloc b (Emul (hs_half hs) (Eadd (slot_node exps base K ra k) (slot_node exps base K rb k))))
          as [ba x1] eqn:B1.
        destruct (alloc ba (Emul (Esub (slot_node exps base K rb k) (slot_node exps base K ra k)) (hs_inv_h hs)))
          as [bb x2] eqn:B2.
        injection A1 as <- <-. allocs. cbn [c_val c_ds]. lift.
        split; [repeat (eapply extends_trans; [eassumption |]); apply extends_refl |].
        split; (eexists; eexists; split; [reflexivity | eassumption]).
      - destruct (alloc b (Emul (slot_node exps base K ra k) (hs_inv_sqrt_a hs))) as [ba qa] eqn:B1.
        destruct (alloc ba (Emul (slot_node exps base K rb k) (hs_inv_sqrt_b hs))) as [bb qb] eqn:B2.
        destruct (alloc bb (Emul (hs_sqrt_h hs) (Emul (hs_half hs) (Eadd qa qb)))) as [bc cv] eqn:B3.
        destruct (alloc bc (Eadd (Emul (hs_sqrt_h hs) (Emul (Esub qb qa) (hs_inv_h hs))) (Emul cv (hs_inv_2s hs))))
          as [bd cs'] eqn:B4.
        injection A1 as <- <-. allocs. cbn [c_val c_ds]. lift.
        split; [repeat (eapply extends_trans; [eassumption |]); apply extends_refl |].
        split; (eexists; eexists; split; [reflexivity | eassumption]). }
    destruct Hc as [X1 [Bv Bd]]. destruct (IH _ _ _ _ A2) as [X2 [L2 F2]].
    split; [exact (extends_trans _ _ _ X1 X2) |]. split; [cbn; rewrite L2; reflexivity |].
    constructor; [split; apply (bound_extends b1); assumption | exact F2].
Qed.

(** The Hermite coefficients: for each pair of half-point coefficients, the
    bindings of [hermcoef_b]. *)
Definition herm_binds (b : builder) (hm : herm_scalars) (ca cb : coef2) (c : coef3) : Prop :=
  exists ndy nsec nal nbe nc ncs ncss,
    t_val c = Evar nc /\ t_ds c = Evar ncs /\ t_dss c = Evar ncss /\
    In (ndy, Esub (c_val cb) (c_val ca)) (b_binds b) /\
    In (nsec, Emul (Evar ndy) (hm_invH hm)) (b_binds b) /\
    In (nal, Esub (c_ds ca) (Evar nsec)) (b_binds b) /\
    In (nbe, Esub (c_ds cb) (Evar nsec)) (b_binds b) /\
    In (nc, Eadd (Eadd (c_val ca) (Emul (hm_t hm) (Evar ndy)))
                 (Emul (hm_H hm) (Eadd (Emul (hm_h10 hm) (Evar nal)) (Emul (hm_h11 hm) (Evar nbe)))))
       (b_binds b) /\
    In (ncs, Eadd (Evar nsec) (Eadd (Emul (hm_g10 hm) (Evar nal)) (Emul (hm_g11 hm) (Evar nbe))))
       (b_binds b) /\
    In (ncss, Emul (Eadd (Emul (hm_m0 hm) (Evar nal)) (Emul (hm_m1 hm) (Evar nbe))) (hm_invH hm))
       (b_binds b).

Lemma herm_binds_extends (b b' : builder) hm ca cb c :
  extends b b' -> herm_binds b hm ca cb c -> herm_binds b' hm ca cb c.
Proof.
  intros X (ndy & nsec & nal & nbe & nc & ncs & ncss & H1 & H2 & H3 & I1 & I2 & I3 & I4 & I5 & I6 & I7).
  exists ndy, nsec, nal, nbe, nc, ncs, ncss.
  repeat split; try assumption; apply (in_extends b); assumption.
Qed.

Lemma hermcoefs_spec (hm : herm_scalars) (cas : list coef2) : forall cbs b b' cs,
  hermcoefs_b b hm cas cbs = (b', cs) -> extends b b' /\
  Forall2 (fun ab c => herm_binds b' hm (fst ab) (snd ab) c) (combine cas cbs) cs.
Proof.
  induction cas as [| ca ta IH]; intros cbs b b' cs H.
  - cbn in H. injection H as <- <-. split; [apply extends_refl | constructor].
  - destruct cbs as [| cb tb].
    + cbn in H. injection H as <- <-. split; [apply extends_refl | constructor].
    + cbn [hermcoefs_b] in H.
      destruct (hermcoef_b b hm ca cb) as [b1 c] eqn:A1.
      destruct (hermcoefs_b b1 hm ta tb) as [b2 rest] eqn:A2.
      injection H as <- <-.
      assert (Hc : extends b b1 /\ herm_binds b1 hm ca cb c).
      { unfold hermcoef_b in A1.
        destruct (alloc b (Esub (c_val cb) (c_val ca))) as [b3 dy] eqn:B1.
        destruct (alloc b3 (Emul dy (hm_invH hm))) as [b4 sec] eqn:B2.
        destruct (alloc b4 (Esub (c_ds ca) sec)) as [b5 al] eqn:B3.
        destruct (alloc b5 (Esub (c_ds cb) sec)) as [b6 be] eqn:B4.
        destruct (alloc b6 (Eadd (Eadd (c_val ca) (Emul (hm_t hm) dy))
                           (Emul (hm_H hm) (Eadd (Emul (hm_h10 hm) al) (Emul (hm_h11 hm) be)))))
          as [b7 cv] eqn:B5.
        destruct (alloc b7 (Eadd sec (Eadd (Emul (hm_g10 hm) al) (Emul (hm_g11 hm) be)))) as [b8 cs1] eqn:B6.
        destruct (alloc b8 (Emul (Eadd (Emul (hm_m0 hm) al) (Emul (hm_m1 hm) be)) (hm_invH hm)))
          as [b9 css] eqn:B7.
        injection A1 as <- <-. allocs.
        split; [repeat (eapply extends_trans; [eassumption |]); apply extends_refl |].
        exists (b_next b), (b_next b3), (b_next b4), (b_next b5), (b_next b6), (b_next b7), (b_next b8).
        cbn [t_val t_ds t_dss]. repeat split; try reflexivity; lift; assumption. }
      destruct Hc as [X1 Hc]. destruct (IH _ _ _ _ A2) as [X2 F2].
      split; [exact (extends_trans _ _ _ X1 X2) |].
      constructor; [apply (herm_binds_extends b1); assumption | exact F2].
Qed.

(** The coefficients of lambda at a free radius, by the parity rule. *)
Definition rad_binds (b : builder) (rs : rad_scalars) (m : Z) (ya yb : expr) (c : coef3) : Prop :=
  if Z.even m then
    exists nd nc ncs,
      t_val c = Evar nc /\ t_ds c = Evar ncs /\
      In (nd, Esub yb ya) (b_binds b) /\
      In (nc, Eadd ya (Emul (rs_w rs) (Evar nd))) (b_binds b) /\
      In (ncs, Emul (Evar nd) (rs_inv_h rs)) (b_binds b)
  else
    exists nqa nqb ndq nq nqs nc ncs,
      t_val c = Evar nc /\ t_ds c = Evar ncs /\
      In (nqa, Emul ya (rs_inv_sqrt_a rs)) (b_binds b) /\
      In (nqb, Emul yb (rs_inv_sqrt_b rs)) (b_binds b) /\
      In (ndq, Esub (Evar nqb) (Evar nqa)) (b_binds b) /\
      In (nq, Eadd (Evar nqa) (Emul (rs_w rs) (Evar ndq))) (b_binds b) /\
      In (nqs, Emul (Evar ndq) (rs_inv_h rs)) (b_binds b) /\
      In (nc, Emul (rs_sqrt rs) (Evar nq)) (b_binds b) /\
      In (ncs, Eadd (Emul (rs_sqrt rs) (Evar nqs)) (Emul (Evar nc) (rs_inv_2s rs))) (b_binds b).

Lemma rad_binds_extends (b b' : builder) rs m ya yb c :
  extends b b' -> rad_binds b rs m ya yb c -> rad_binds b' rs m ya yb c.
Proof.
  intros X H. unfold rad_binds in *. destruct (Z.even m).
  - destruct H as (nd & nc & ncs & H1 & H2 & I1 & I2 & I3).
    exists nd, nc, ncs. repeat split; try assumption; apply (in_extends b); assumption.
  - destruct H as (nqa & nqb & ndq & nq & nqs & nc & ncs & H1 & H2 & I1 & I2 & I3 & I4 & I5 & I6 & I7).
    exists nqa, nqb, ndq, nq, nqs, nc, ncs. repeat split; try assumption; apply (in_extends b); assumption.
Qed.

Lemma radcoefs_spec (rs : rad_scalars) (base K ra rb : nat) (modes : list (Z * Z)) : forall k b b' cs,
  radcoefs_b exps b rs base K ra rb modes k = (b', cs) -> extends b b' /\
  Forall2 (fun jmn c => rad_binds b' rs (fst (snd jmn)) (slot_node exps base K ra (fst jmn))
                                  (slot_node exps base K rb (fst jmn)) c)
          (combine (seq k (length modes)) modes) cs.
Proof.
  induction modes as [| mn tl IH]; intros k b b' cs H.
  - cbn in H. injection H as <- <-. split; [apply extends_refl | constructor].
  - cbn [radcoefs_b] in H.
    destruct (radcoef_b b rs (fst mn) (slot_node exps base K ra k) (slot_node exps base K rb k))
      as [b1 c] eqn:A1.
    destruct (radcoefs_b exps b1 rs base K ra rb tl (S k)) as [b2 rest] eqn:A2.
    injection H as <- <-.
    assert (Hc : extends b b1 /\ rad_binds b1 rs (fst mn) (slot_node exps base K ra k)
                                           (slot_node exps base K rb k) c).
    { unfold radcoef_b in A1. unfold rad_binds. destruct (Z.even (fst mn)).
      - destruct (alloc b (Esub (slot_node exps base K rb k) (slot_node exps base K ra k))) as [b3 d] eqn:B1.
        destruct (alloc b3 (Eadd (slot_node exps base K ra k) (Emul (rs_w rs) d))) as [b4 cv] eqn:B2.
        destruct (alloc b4 (Emul d (rs_inv_h rs))) as [b5 cs1] eqn:B3.
        injection A1 as <- <-. allocs.
        split; [repeat (eapply extends_trans; [eassumption |]); apply extends_refl |].
        exists (b_next b), (b_next b3), (b_next b4). cbn [t_val t_ds].
        repeat split; try reflexivity; lift; assumption.
      - destruct (alloc b (Emul (slot_node exps base K ra k) (rs_inv_sqrt_a rs))) as [b3 qa] eqn:B1.
        destruct (alloc b3 (Emul (slot_node exps base K rb k) (rs_inv_sqrt_b rs))) as [b4 qb] eqn:B2.
        destruct (alloc b4 (Esub qb qa)) as [b5 dq] eqn:B3.
        destruct (alloc b5 (Eadd qa (Emul (rs_w rs) dq))) as [b6 q] eqn:B4.
        destruct (alloc b6 (Emul dq (rs_inv_h rs))) as [b7 qs] eqn:B5.
        destruct (alloc b7 (Emul (rs_sqrt rs) q)) as [b8 cv] eqn:B6.
        destruct (alloc b8 (Eadd (Emul (rs_sqrt rs) qs) (Emul cv (rs_inv_2s rs)))) as [b9 cs1] eqn:B7.
        destruct (alloc b9 (Esub (Emul (rs_inv_sqrt rs) qs) (Emul cv (rs_inv_4s2 rs)))) as [b10 css] eqn:B8.
        injection A1 as <- <-. allocs.
        split; [repeat (eapply extends_trans; [eassumption |]); apply extends_refl |].
        exists (b_next b), (b_next b3), (b_next b4), (b_next b5), (b_next b6), (b_next b7), (b_next b8).
        cbn [t_val t_ds]. repeat split; try reflexivity; lift; assumption. }
    destruct Hc as [X1 Hc]. destruct (IH _ _ _ _ A2) as [X2 F2].
    split; [exact (extends_trans _ _ _ X1 X2) |].
    cbn [length seq combine]. constructor; [apply (rad_binds_extends b1); assumption | exact F2].
Qed.

End Stages.
