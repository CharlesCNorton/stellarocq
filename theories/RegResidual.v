(** The node residual of the half-grid rule without the radial step in a
    denominator.

    Physics.v's node residual reads R and Z on the nodes j-1, j, j+1 and
    divides by the spacing twice: in the half-grid slopes and in the centred
    difference of the half-point fields. Written in the slots of a node jet,
    x = y_j, dm = (y_j - y_{j-1}) / h, dp = (y_{j+1} - y_j) / h and
    e = (dp - dm) / h for each coefficient, with the square roots of the five
    radii s - h, s - h/2, s, s + h/2, s + h as slots of their own, it divides by
    nothing that vanishes with h:

      - the half-grid value and slope of a coefficient at a half point are
        rational in the inner node value ya, the difference quotient d of the
        two nodes and the roots ([hr_val], [hr_slope]): for even m,
        ya + h d / 2 and d; for odd m, with the identity
        rb^2 - ra^2 = h, sqrt sh (ya / ra + (ya + h d) / rb) / 2 and
        sqrt sh (d / rb - ya / (ra rb (ra + rb))) + value / (2 sh);
      - the half-point field is rational in those coefficients, the stream
        function and the transform, so the difference of its two half points
        over h is DivDiff's divided difference, a binding list over three
        layers (minus, plus, difference) of the half-point slots.

    The construction is [prelim], which lays the three layers of every input
    of the half point out from the jet ([descr]), then [with_dd] of the
    half point's own bindings, and the radial and poloidal components read
    from the layers ([reg_fs], [reg_fu]). [reg_fs_ok] and [reg_fu_ok] state
    that wherever they are real they are the forced node residual of
    Residuals.node_residual: node_rs of the two half-point jets, with the
    reciprocal of the spacing h, less the source. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Deriv DivDiff Physics Recon Continuum Force Series Residuals HalfNZ.

Import ListNotations.
Local Open Scope R_scope.

(** No exponents: every slot holds its value. *)
Definition rexps : list Z := [].

Section Reg.

Variable modes : list (Z * Z).

Definition rK : nat := length modes.

(* ---------------------------------------------------------------- *)
(* The half point's slots                                            *)

(** Slots 1, 2, 3 are u, v and phip, as the builders read them; the inputs of
    the half-grid rule start at rk0, leaving the slots in between, three
    times over, to the jet. *)
Definition rk0 : nat := 9 + 4 * rK.
Definition s_h : nat := rk0.
Definition s_ra : nat := rk0 + 1.
Definition s_rb : nat := rk0 + 2.
Definition s_rh : nat := rk0 + 3.
Definition s_io : nat := rk0 + 4.
Definition s_yR (k : nat) : nat := rk0 + 5 + k.
Definition s_dR (k : nat) : nat := rk0 + 5 + rK + k.
Definition s_yZ (k : nat) : nat := rk0 + 5 + 2 * rK + k.
Definition s_dZ (k : nat) : nat := rk0 + 5 + 3 * rK + k.
Definition s_L (k : nat) : nat := rk0 + 5 + 4 * rK + k.
Definition sub_base : nat := rk0 + 5 + 5 * rK.

Definition ehalf : expr := Ediv e1 e2.

(** The half-grid value and slope of a mode of poloidal number m from the
    inner node value y and the difference quotient d of the two nodes. *)
Definition hr_val (m : Z) (y d : expr) : expr :=
  if Z.even m then Eadd y (Emul (Emul (Evar s_h) ehalf) d)
  else Emul (Evar s_rh)
         (Emul ehalf (Eadd (Ediv y (Evar s_ra))
                           (Ediv (Eadd y (Emul (Evar s_h) d)) (Evar s_rb)))).

Definition hr_slope (m : Z) (y d v : expr) : expr :=
  if Z.even m then d
  else Eadd (Emul (Evar s_rh)
                  (Esub (Ediv d (Evar s_rb))
                        (Ediv y (Emul (Emul (Evar s_ra) (Evar s_rb))
                                      (Eadd (Evar s_ra) (Evar s_rb))))))
            (Ediv v (Emul e2 (Emul (Evar s_rh) (Evar s_rh)))).

Fixpoint hr_b (b : builder) (ys ds : nat -> nat) (ms : list (Z * Z)) (k : nat)
    : builder * list coef2 :=
  match ms with
  | [] => (b, [])
  | mn :: tl =>
      let (b, v) := alloc b (hr_val (fst mn) (Evar (ys k)) (Evar (ds k))) in
      let (b, s) := alloc b (hr_slope (fst mn) (Evar (ys k)) (Evar (ds k)) v) in
      let (b, rest) := hr_b b ys ds tl (S k) in
      (b, Coef2 v s :: rest)
  end.

(** The half point: the half-grid rule, the kernels, and the field. *)
Definition reg_sub : builder * halfq :=
  let b := Builder sub_base [] in
  let (b, cR) := hr_b b s_yR s_dR modes 0 in
  let (b, cZ) := hr_b b s_yZ s_dZ modes 0 in
  let (b, kers) := kernels_b rexps b modes in
  half_point_b rexps b false kers
    (HCoefs cR cZ (map (fun k => Evar (s_L k)) (seq 0 rK)) [] [] []) (Evar s_io).

Definition sub_binds : list binding := bindings_of (fst reg_sub).
Definition sub_q : halfq := snd reg_sub.

(** The fixed slots: u, v, phip and h, and every binding over them alone. *)
Definition fx_in (k : nat) : bool :=
  Nat.eqb k 1 || Nat.eqb k 2 || Nat.eqb k 3 || Nat.eqb k s_h.

Fixpoint fix_tab (f : nat -> bool) (bs : list binding) : nat -> bool :=
  match bs with
  | [] => f
  | (n, e) :: tl => fix_tab (fun k => if Nat.eqb k n then fixed f e else f k) tl
  end.

Definition rfx : nat -> bool := fix_tab fx_in sub_binds.

(** The slots the layers are related on: the inputs the half point reads and
    its bindings. *)
Definition rcov (k : nat) : bool :=
  Nat.eqb k 1 || Nat.eqb k 2 || Nat.eqb k 3 || Nat.leb rk0 k.

(* ---------------------------------------------------------------- *)
(* The jet's slots                                                   *)

Definition o_xR (k : nat) : nat := 12 + k.
Definition o_dmR (k : nat) : nat := 12 + rK + k.
Definition o_dpR (k : nat) : nat := 12 + 2 * rK + k.
Definition o_eR (k : nat) : nat := 12 + 3 * rK + k.
Definition o_xZ (k : nat) : nat := 12 + 4 * rK + k.
Definition o_dmZ (k : nat) : nat := 12 + 5 * rK + k.
Definition o_dpZ (k : nat) : nat := 12 + 6 * rK + k.
Definition o_eZ (k : nat) : nat := 12 + 7 * rK + k.
Definition o_Lm (k : nat) : nat := 12 + 8 * rK + k.
Definition o_Lp (k : nat) : nat := 12 + 9 * rK + k.
Definition o_Ldd (k : nat) : nat := 12 + 10 * rK + k.
Definition o_im : nat := 12 + 11 * rK.
Definition o_ip : nat := 13 + 11 * rK.
Definition o_idd : nat := 14 + 11 * rK.
(** The roots of s - h, s - h/2, s, s + h/2, s + h. *)
Definition o_r (i : nat) : nat := 15 + 11 * rK + i.
Definition o_h : nat := 20 + 11 * rK.
Definition o_mpp : nat := 21 + 11 * rK.
Definition o_fs : nat := 22 + 11 * rK.
Definition o_fu : nat := 23 + 11 * rK.

(** The three layers of each input of the half-grid rule, in the order of
    its slots from rk0: minus, plus, and the divided difference. *)
Definition dsc_h : expr * expr * expr := (Evar o_h, Evar o_h, EfromZ 0).
Definition dsc_root (a b : nat) : expr * expr * expr :=
  (Evar (o_r a), Evar (o_r b), Ediv e1 (Eadd (Evar (o_r b)) (Evar (o_r a)))).
Definition dsc_y (ox odm : nat -> nat) (k : nat) : expr * expr * expr :=
  (Esub (Evar (ox k)) (Emul (Evar o_h) (Evar (odm k))), Evar (ox k), Evar (odm k)).
Definition dsc_d (odm odp oe : nat -> nat) (k : nat) : expr * expr * expr :=
  (Evar (odm k), Evar (odp k), Evar (oe k)).
Definition dsc_L (k : nat) : expr * expr * expr := (Evar (o_Lm k), Evar (o_Lp k), Evar (o_Ldd k)).

Definition descr : list (expr * expr * expr) :=
  [dsc_h; dsc_root 0 2; dsc_root 2 4; dsc_root 1 3; (Evar o_im, Evar o_ip, Evar o_idd)]
  ++ map (dsc_y o_xR o_dmR) (seq 0 rK) ++ map (dsc_d o_dmR o_dpR o_eR) (seq 0 rK)
  ++ map (dsc_y o_xZ o_dmZ) (seq 0 rK) ++ map (dsc_d o_dmZ o_dpZ o_eZ) (seq 0 rK)
  ++ map dsc_L (seq 0 rK).

Fixpoint prelim_from (i : nat) (l : list (expr * expr * expr)) : list binding :=
  match l with
  | [] => []
  | (a, b, c) :: tl => (lm i, a) :: (lp i, b) :: (ld i, c) :: prelim_from (S i) tl
  end.

Definition prelim : list binding := prelim_from rk0 descr.

(** The whole list: the layers of the inputs, then the half point over the
    three layers. *)
Definition reg_binds : list binding := prelim ++ with_dd rfx sub_binds.

Definition ravg (q : expr) : expr := Emul ehalf (Eadd (ren lm q) (ren lp q)).

Definition reg_rs : expr :=
  Esub (Esub (Emul (Esub (ravg (q_B_s_v sub_q)) (dd rfx (q_B_v sub_q))) (ravg (q_Bv sub_q)))
             (Emul (Esub (dd rfx (q_B_u sub_q)) (ravg (q_B_s_u sub_q))) (ravg (q_Bu sub_q))))
       (Evar o_mpp).

Definition reg_fs : expr := Esub reg_rs (Evar o_fs).

Definition reg_fu : expr :=
  Esub (Eneg (Emul (ren lp (q_mu0Js sub_q)) (ren lp (q_Bv sub_q)))) (Evar o_fu).

(* ---------------------------------------------------------------- *)
(* Real values of expressions                                        *)

(** The real value of an expression over real slots, and the condition
    under which xeval gives it: every divisor nonzero. *)
Fixpoint rv (g : nat -> R) (e : expr) : R :=
  match e with
  | Evar n     => g n
  | EfromZ z   => IZR z
  | Epi        => PI
  | Eneg a     => - rv g a
  | Eadd a b   => rv g a + rv g b
  | Esub a b   => rv g a - rv g b
  | Emul a b   => rv g a * rv g b
  | Ediv a b   => rv g a / rv g b
  | Esqrt a    => sqrt (rv g a)
  | Esin a     => sin (rv g a)
  | Ecos a     => cos (rv g a)
  | Eexp a     => exp (rv g a)
  | Eatan a    => atan (rv g a)
  | Epow2 z    => powerRZ 2 z
  end.

Fixpoint defd (g : nat -> R) (e : expr) : Prop :=
  match e with
  | Ediv a b   => defd g a /\ defd g b /\ rv g b <> 0
  | Eneg a | Esqrt a | Esin a | Ecos a | Eexp a | Eatan a => defd g a
  | Eadd a b | Esub a b | Emul a b => defd g a /\ defd g b
  | _          => True
  end.

Lemma Xdiv_r : forall x y, y <> 0 -> Xdiv (Xreal x) (Xreal y) = Xreal (x / y).
Proof. intros x y Hy. cbn [Xbind2]. unfold Xdiv'. rewrite (is_zero_false y Hy). reflexivity. Qed.

Lemma xeval_rv :
  forall E g e, (forall k, occurs k e -> eget k E Xnan = Xreal (g k)) -> defd g e ->
  xeval E e = Xreal (rv g e).
Proof.
  intros E g e. induction e; simpl; intros Hg Hd.
  - apply Hg. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - destruct Hd as [H1 H2].
    rewrite IHe1, IHe2 by (try assumption; intros k Hk; apply Hg; tauto). reflexivity.
  - destruct Hd as [H1 H2].
    rewrite IHe1, IHe2 by (try assumption; intros k Hk; apply Hg; tauto). reflexivity.
  - destruct Hd as [H1 H2].
    rewrite IHe1, IHe2 by (try assumption; intros k Hk; apply Hg; tauto). reflexivity.
  - destruct Hd as [H1 [H2 H3]].
    rewrite IHe1, IHe2 by (try assumption; intros k Hk; apply Hg; tauto). apply Xdiv_r. exact H3.
  - rewrite IHe by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - reflexivity.
Qed.

(** The real reading of an environment's slot. *)
Definition gof (E : env ExtendedR) (k : nat) : R :=
  match eget k E Xnan with Xreal r => r | Xnan => 0 end.

Lemma gof_eq : forall E k r, eget k E Xnan = Xreal r -> gof E k = r.
Proof. intros E k r H. unfold gof. rewrite H. reflexivity. Qed.

Lemma xeval_gof :
  forall E e, (forall k, occurs k e -> exists r, eget k E Xnan = Xreal r) -> defd (gof E) e ->
  xeval E e = Xreal (rv (gof E) e).
Proof.
  intros E e Hr Hd. apply xeval_rv; [| exact Hd].
  intros k Hk. destruct (Hr k Hk) as [r Hk']. rewrite Hk'. f_equal. symmetry. apply gof_eq. exact Hk'.
Qed.

(* ---------------------------------------------------------------- *)
(* The half-grid rule                                                *)

Lemma hr_b_spec :
  forall ys ds ms k b b' cs,
  hr_b b ys ds ms k = (b', cs) ->
  extends b b' /\
  Forall2 (fun jmn c => exists v s, c = Coef2 (Evar v) (Evar s) /\
              In (v, hr_val (fst (snd jmn)) (Evar (ys (fst jmn))) (Evar (ds (fst jmn))))
                 (b_binds b') /\
              In (s, hr_slope (fst (snd jmn)) (Evar (ys (fst jmn))) (Evar (ds (fst jmn))) (Evar v))
                 (b_binds b'))
          (combine (seq k (length ms)) ms) cs.
Proof.
  intros ys ds ms. induction ms as [|mn tl IH]; intros k b b' cs H.
  - cbn in H. injection H as <- <-. split; [apply extends_refl | constructor].
  - cbn [hr_b] in H.
    destruct (alloc b (hr_val (fst mn) (Evar (ys k)) (Evar (ds k)))) as [b1 v] eqn:A1.
    destruct (alloc b1 (hr_slope (fst mn) (Evar (ys k)) (Evar (ds k)) v)) as [b2 s] eqn:A2.
    destruct (hr_b b2 ys ds tl (S k)) as [b3 rest] eqn:A3.
    injection H as <- <-.
    destruct (alloc_spec b _ b1 v A1) as [X1 [I1 E1]].
    destruct (alloc_spec b1 _ b2 s A2) as [X2 [I2 E2]].
    destruct (IH (S k) b2 b3 rest A3) as [X3 F3].
    split; [exact (extends_trans _ _ _ X1 (extends_trans _ _ _ X2 X3)) |].
    cbn [length seq combine]. constructor.
    + exists (b_next b), (b_next b1). subst v s. split; [reflexivity |]. cbn [fst snd].
      split.
      * apply (in_extends b1 b3); [exact (extends_trans _ _ _ X2 X3) | exact I1].
      * apply (in_extends b2 b3 _ X3). exact I2.
    + exact F3.
Qed.

(** The rule's value and slope are VMEC's half-grid value and slope of the
    two nodes ya and ya + h d, whose radii differ by h. *)
(** Every slot an expression reads holds a real number. *)
Ltac slots_real :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; simpl in Hk;
  repeat match type of Hk with _ \/ _ => destruct Hk as [Hk|Hk] end;
  try contradiction; subst k; eexists; eassumption.

Lemma hr_ok :
  forall m (E : env ExtendedR) ky kd ya dd hh sa sb sh,
  eget s_h E Xnan = Xreal hh -> eget s_ra E Xnan = Xreal (sqrt sa) ->
  eget s_rb E Xnan = Xreal (sqrt sb) -> eget s_rh E Xnan = Xreal (sqrt sh) ->
  eget ky E Xnan = Xreal ya -> eget kd E Xnan = Xreal dd ->
  0 < sa -> 0 < sb -> 0 < sh -> sb - sa = hh -> hh <> 0 ->
  xeval E (hr_val m (Evar ky) (Evar kd)) = Xreal (hval m sa sb sh ya (ya + hh * dd)) /\
  (forall kv, eget kv E Xnan = Xreal (hval m sa sb sh ya (ya + hh * dd)) ->
   xeval E (hr_slope m (Evar ky) (Evar kd) (Evar kv)) = Xreal (hslope m sa sb sh ya (ya + hh * dd))).
Proof.
  intros m E ky kd ya dd hh sa sb sh Hh Ha Hb Hs Hy Hd Pa Pb Ps Hab Hh0.
  assert (Ra := sqrt_lt_R0 sa Pa). assert (Rb := sqrt_lt_R0 sb Pb). assert (Rs := sqrt_lt_R0 sh Ps).
  assert (Qa := sqrt_sqrt sa (Rlt_le _ _ Pa)). assert (Qb := sqrt_sqrt sb (Rlt_le _ _ Pb)).
  assert (Qs := sqrt_sqrt sh (Rlt_le _ _ Ps)).
  assert (H2 : IZR 2 <> 0) by (apply not_0_IZR; lia).
  assert (Gh := gof_eq _ _ _ Hh). assert (Ga := gof_eq _ _ _ Ha). assert (Gb := gof_eq _ _ _ Hb).
  assert (Gs := gof_eq _ _ _ Hs). assert (Gy := gof_eq _ _ _ Hy). assert (Gd := gof_eq _ _ _ Hd).
  unfold hr_val, hr_slope, hval, hslope, ehalf, e1, e2. destruct (Z.even m).
  - split.
    + rewrite (xeval_gof E); [| slots_real | cbn; repeat split; exact H2].
      cbn [rv]. rewrite Gh, Gy, Gd. f_equal. field.
    + intros kv _. rewrite (xeval_gof E); [| slots_real | exact I].
      cbn [rv]. rewrite Gd. f_equal. rewrite <- Hab. field. lra.
  - assert (Hv : xeval E (Emul (Evar s_rh) (Emul (Ediv (EfromZ 1) (EfromZ 2))
                   (Eadd (Ediv (Evar ky) (Evar s_ra))
                         (Ediv (Eadd (Evar ky) (Emul (Evar s_h) (Evar kd))) (Evar s_rb)))))
                 = Xreal (sqrt sh * (1 / 2 * (ya * (1 / sqrt sa) + (ya + hh * dd) * (1 / sqrt sb))))).
    { rewrite (xeval_gof E); [| slots_real |].
      - cbn [rv]. rewrite Gh, Ga, Gb, Gs, Gy, Gd. f_equal. field. lra.
      - cbn [defd rv]. rewrite Ga, Gb. repeat split; try exact H2; lra. }
    split; [exact Hv |].
    intros kv Hv'. assert (Gv := gof_eq _ _ _ Hv').
    rewrite (xeval_gof E); [| slots_real |].
    + cbn [rv]. rewrite Ga, Gb, Gs, Gy, Gd, Gv. f_equal.
      set (ra := sqrt sa) in *. set (rb := sqrt sb) in *. set (rh := sqrt sh) in *.
      assert (Hhh : hh = rb * rb - ra * ra) by lra.
      rewrite <- Qa, <- Qb, <- Qs, Hhh. field. repeat split; try lra; nra.
    + cbn [defd rv]. rewrite Ga, Gb, Gs. repeat split; try lra;
        repeat apply Rmult_integral_contrapositive_currified; try exact H2; try nra; lra.
Qed.

(** The rule's coefficients over a block of modes, in a sound environment. *)
Lemma hr_b_values :
  forall (E : env ExtendedR) b b' ys ds ms cs (ya yb dd : nat -> R) hh sa sb sh,
  hr_b b ys ds ms 0 = (b', cs) -> sound E (b_binds b') ->
  eget s_h E Xnan = Xreal hh -> eget s_ra E Xnan = Xreal (sqrt sa) ->
  eget s_rb E Xnan = Xreal (sqrt sb) -> eget s_rh E Xnan = Xreal (sqrt sh) ->
  (forall j, (j < length ms)%nat ->
     eget (ys j) E Xnan = Xreal (ya j) /\ eget (ds j) E Xnan = Xreal (dd j) /\
     ya j + hh * dd j = yb j) ->
  0 < sa -> 0 < sb -> 0 < sh -> sb - sa = hh -> hh <> 0 ->
  Forall2 (fun jmn c =>
     xeval E (c_val c) = Xreal (hval (fst (snd jmn)) sa sb sh (ya (fst jmn)) (yb (fst jmn))) /\
     xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) sa sb sh (ya (fst jmn)) (yb (fst jmn))))
    (combine (seq 0 (length ms)) ms) cs.
Proof.
  intros E b b' ys ds ms cs ya yb dd hh sa sb sh Hb S Hh Ha Hbb Hs Hyd Pa Pb Ps Hab Hh0.
  destruct (hr_b_spec ys ds ms 0 b b' cs Hb) as [_ F].
  eapply forall2_combine_seq; [| exact F].
  intros [j mn] c Hin [v [s [Hc [Iv Is]]]]. subst c. cbn [fst snd] in *.
  assert (Hj := in_combine_seq (j, mn) _ _ Hin). cbn [fst] in Hj.
  destruct (Hyd j Hj) as [Hy [Hd Hyb]].
  destruct (hr_ok (fst mn) E (ys j) (ds j) (ya j) (dd j) hh sa sb sh Hh Ha Hbb Hs Hy Hd
              Pa Pb Ps Hab Hh0) as [V1 V2].
  rewrite Hyb in V1, V2.
  assert (Ev : eget v E Xnan = Xreal (hval (fst mn) sa sb sh (ya j) (yb j)))
    by (rewrite (S _ _ Iv); exact V1).
  cbn [c_val c_ds xeval]. split; [exact Ev |].
  rewrite (S _ _ Is). exact (V2 v Ev).
Qed.

(** The stages of the half point. *)
Lemma reg_sub_spec :
  exists b1 cR b2 cZ b3 kers,
  hr_b (Builder sub_base []) s_yR s_dR modes 0 = (b1, cR) /\
  hr_b b1 s_yZ s_dZ modes 0 = (b2, cZ) /\
  kernels_b rexps b2 modes = (b3, kers) /\
  half_point_b rexps b3 false kers
    (HCoefs cR cZ (map (fun k => Evar (s_L k)) (seq 0 rK)) [] [] []) (Evar s_io) = reg_sub.
Proof.
  unfold reg_sub.
  destruct (hr_b (Builder sub_base []) s_yR s_dR modes 0) as [b1 cR] eqn:A1.
  destruct (hr_b b1 s_yZ s_dZ modes 0) as [b2 cZ] eqn:A2.
  destruct (kernels_b rexps b2 modes) as [b3 kers] eqn:A3.
  exists b1, cR, b2, cZ, b3, kers.
  repeat split; first [reflexivity | assumption].
Qed.

(* ---------------------------------------------------------------- *)
(* The layers of the inputs                                          *)

Lemma prelim_from_slots :
  forall l i k, In k (map fst (prelim_from i l)) -> (lm i <= k)%nat.
Proof.
  induction l as [|[[a b] c] tl IH]; intros i k Hin; [destruct Hin|].
  simpl in Hin. unfold lm, lp, ld in *.
  destruct Hin as [<-|[<-|[<-|Hin]]]; try lia.
  specialize (IH (S i) k Hin). lia.
Qed.

Lemma prelim_from_vals :
  forall l i (E : env ExtendedR),
  (forall a b c, In (a, b, c) l -> forall k, occurs k a \/ occurs k b \/ occurs k c -> (k < lm i)%nat) ->
  forall t a b c, nth_error l t = Some (a, b, c) ->
  eget (lm (i + t)) (xextend E (prelim_from i l)) Xnan = xeval E a /\
  eget (lp (i + t)) (xextend E (prelim_from i l)) Xnan = xeval E b /\
  eget (ld (i + t)) (xextend E (prelim_from i l)) Xnan = xeval E c.
Proof.
  induction l as [|[[a0 b0] c0] tl IH]; intros i E Hr t a b c Ht; [destruct t; discriminate|].
  set (E3 := xextend E [(lm i, a0); (lp i, b0); (ld i, c0)]).
  change (xextend E (prelim_from i ((a0, b0, c0) :: tl))) with (xextend E3 (prelim_from (S i) tl)).
  assert (Hr0 : forall k, occurs k a0 \/ occurs k b0 \/ occurs k c0 -> (k < lm i)%nat)
    by (apply Hr; left; reflexivity).
  (* E3 agrees with E below lm i *)
  assert (Hlow : forall k, (k < lm i)%nat -> eget k E3 Xnan = eget k E Xnan).
  { intros k Hk. unfold E3, lm, lp, ld in *. simpl. rewrite !eget_eset_neq by lia. reflexivity. }
  assert (Hev : forall e, (forall k, occurs k e -> (k < lm i)%nat) -> xeval E3 e = xeval E e).
  { intros e He. rewrite !xeval_f. apply xevalf_ext. intros k Hk. apply Hlow, He, Hk. }
  destruct t as [|t].
  - cbn in Ht. injection Ht as <- <- <-.
    rewrite Nat.add_0_r.
    assert (Hnot : forall k, (k <= ld i)%nat -> ~ In k (map fst (prelim_from (S i) tl))).
    { intros k Hk Hin. pose proof (prelim_from_slots tl (S i) k Hin). unfold lm, ld in *. lia. }
    rewrite !eget_xextend_notin by (apply Hnot; unfold lm, lp, ld; lia).
    unfold E3. simpl. unfold lm, lp, ld.
    split; [| split].
    + rewrite eget_eset_neq by lia. rewrite eget_eset_neq by lia. apply eget_eset_eq.
    + rewrite eget_eset_neq by lia. rewrite eget_eset_eq.
      rewrite !xeval_f. apply xevalf_ext. intros k Hk. cbv beta.
      assert (Hk' := Hr0 k (or_intror (or_introl Hk))). unfold lm in Hk'.
      rewrite eget_eset_neq by lia. reflexivity.
    + rewrite eget_eset_eq.
      rewrite !xeval_f. apply xevalf_ext. intros k Hk. cbv beta.
      assert (Hk' := Hr0 k (or_intror (or_intror Hk))). unfold lm in Hk'.
      rewrite eget_eset_neq by lia. rewrite eget_eset_neq by lia. reflexivity.
  - cbn in Ht. replace (i + S t)%nat with (S i + t)%nat by lia.
    assert (Hr' : forall a b c, In (a, b, c) tl -> forall k,
               occurs k a \/ occurs k b \/ occurs k c -> (k < lm (S i))%nat).
    { intros a' b' c' Hin k Hk. pose proof (Hr a' b' c' (or_intror Hin) k Hk). unfold lm in *. lia. }
    destruct (IH (S i) E3 Hr' t a b c Ht) as [V1 [V2 V3]].
    assert (Hin : In (a, b, c) tl) by (eapply nth_error_In; exact Ht).
    rewrite V1, V2, V3.
    repeat split; apply Hev; intros k Hk; apply (Hr a b c (or_intror Hin)); tauto.
Qed.

Lemma prelim_from_low :
  forall l i (E : env ExtendedR) k, (k < lm i)%nat ->
  eget k (xextend E (prelim_from i l)) Xnan = eget k E Xnan.
Proof.
  intros l i E k Hk. apply eget_xextend_notin. intros Hin.
  pose proof (prelim_from_slots l i k Hin). lia.
Qed.

(** What the descriptors read: the jet's slots, all below lm rk0. *)
Lemma descr_reads :
  forall a b c, In (a, b, c) descr ->
  forall k, occurs k a \/ occurs k b \/ occurs k c -> (k < lm rk0)%nat.
Proof.
  intros a b c Hin k Hk. unfold descr in Hin.
  enough (Hk' : (k < 24 + 11 * rK)%nat) by (unfold lm, rk0; lia).
  repeat (apply in_app_iff in Hin; destruct Hin as [Hin|Hin]);
    [simpl in Hin; destruct Hin as [H|[H|[H|[H|[H|H]]]]]; try contradiction;
     unfold dsc_h, dsc_root in H; injection H as <- <- <-
    | apply in_map_iff in Hin; destruct Hin as [j [Heq Hj]]; apply in_seq in Hj;
      unfold dsc_y, dsc_d, dsc_L in Heq; injection Heq as <- <- <- ..];
    unfold e1, o_h, o_r, o_im, o_ip, o_idd, o_xR, o_dmR, o_dpR, o_eR, o_xZ, o_dmZ, o_dpZ, o_eZ,
      o_Lm, o_Lp, o_Ldd in Hk;
    cbn [occurs] in Hk; lia.
Qed.

Lemma length_descr : length descr = (5 + 5 * rK)%nat.
Proof. unfold descr. rewrite !length_app, !length_map, !length_seq. simpl. lia. Qed.

Lemma nth_error_map_seq_app :
  forall (A : Type) (f : nat -> A) n (l : list A) t, (t < n)%nat ->
  nth_error (map f (seq 0 n) ++ l) t = Some (f t).
Proof.
  intros A f n l t Ht.
  rewrite (nth_error_nth' _ (f 0%nat)) by (rewrite length_app, length_map, length_seq; lia).
  rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma nth_error_skip :
  forall (A : Type) (l1 l2 : list A) t, nth_error (l1 ++ l2) (length l1 + t) = nth_error l2 t.
Proof. intros A l1 l2 t. rewrite nth_error_app2 by lia. f_equal. lia. Qed.

Definition dsc_io : expr * expr * expr := (Evar o_im, Evar o_ip, Evar o_idd).

Lemma descr_split :
  descr = [dsc_h; dsc_root 0 2; dsc_root 2 4; dsc_root 1 3; dsc_io]
          ++ map (dsc_y o_xR o_dmR) (seq 0 rK) ++ map (dsc_d o_dmR o_dpR o_eR) (seq 0 rK)
          ++ map (dsc_y o_xZ o_dmZ) (seq 0 rK) ++ map (dsc_d o_dmZ o_dpZ o_eZ) (seq 0 rK)
          ++ map dsc_L (seq 0 rK).
Proof. reflexivity. Qed.

Lemma descr_at_head :
  nth_error descr 0 = Some dsc_h /\ nth_error descr 1 = Some (dsc_root 0 2) /\
  nth_error descr 2 = Some (dsc_root 2 4) /\ nth_error descr 3 = Some (dsc_root 1 3) /\
  nth_error descr 4 = Some dsc_io.
Proof. repeat split; reflexivity. Qed.

Lemma descr_at_block :
  forall k, (k < rK)%nat ->
  nth_error descr (5 + k) = Some (dsc_y o_xR o_dmR k) /\
  nth_error descr (5 + rK + k) = Some (dsc_d o_dmR o_dpR o_eR k) /\
  nth_error descr (5 + 2 * rK + k) = Some (dsc_y o_xZ o_dmZ k) /\
  nth_error descr (5 + 3 * rK + k) = Some (dsc_d o_dmZ o_dpZ o_eZ k) /\
  nth_error descr (5 + 4 * rK + k) = Some (dsc_L k).
Proof.
  intros k Hk. rewrite descr_split.
  set (H5 := [dsc_h; dsc_root 0 2; dsc_root 2 4; dsc_root 1 3; dsc_io]).
  set (M1 := map (dsc_y o_xR o_dmR) (seq 0 rK)).
  set (M2 := map (dsc_d o_dmR o_dpR o_eR) (seq 0 rK)).
  set (M3 := map (dsc_y o_xZ o_dmZ) (seq 0 rK)).
  set (M4 := map (dsc_d o_dmZ o_dpZ o_eZ) (seq 0 rK)).
  set (M5 := map dsc_L (seq 0 rK)).
  assert (L5 : length H5 = 5%nat) by reflexivity.
  assert (LM : forall (f : nat -> expr * expr * expr), length (map f (seq 0 rK)) = rK)
    by (intros f; rewrite length_map, length_seq; reflexivity).
  replace (5 + k)%nat with (length H5 + k)%nat by (rewrite L5; reflexivity).
  replace (5 + rK + k)%nat with (length H5 + (length M1 + k))%nat by (rewrite L5; unfold M1; rewrite LM; lia).
  replace (5 + 2 * rK + k)%nat with (length H5 + (length M1 + (length M2 + k)))%nat
    by (rewrite L5; unfold M1, M2; rewrite !LM; lia).
  replace (5 + 3 * rK + k)%nat with (length H5 + (length M1 + (length M2 + (length M3 + k))))%nat
    by (rewrite L5; unfold M1, M2, M3; rewrite !LM; lia).
  replace (5 + 4 * rK + k)%nat
    with (length H5 + (length M1 + (length M2 + (length M3 + (length M4 + k)))))%nat
    by (rewrite L5; unfold M1, M2, M3, M4; rewrite !LM; lia).
  rewrite !nth_error_skip.
  unfold M1, M2, M3, M4, M5.
  repeat split; try (apply nth_error_map_seq_app; exact Hk).
  rewrite (nth_error_nth' _ (dsc_L 0%nat)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* The slots of the layers, and the checks the construction needs    *)

Definition rtop : nat := (sub_base + length sub_binds)%nat.

(** What the transform needs of the half point, decided by computation for a
    given list of modes: its bindings are well formed from sub_base, read only
    the slots the layers are related on, and its outputs read slots below the
    top and covered ones. *)
Definition reg_outputs : list expr :=
  [q_Bu sub_q; q_Bv sub_q; q_B_u sub_q; q_B_v sub_q; q_B_s_u sub_q; q_B_s_v sub_q; q_mu0Js sub_q].

Definition reg_ok : bool :=
  well_formed sub_base sub_binds &&
  forallb (fun b => fixed rcov (snd b)) sub_binds &&
  forallb (fun q => vars_below rtop q && fixed rcov q) reg_outputs.

Lemma fix_tab_notin :
  forall bs f k, ~ In k (map fst bs) -> fix_tab f bs k = f k.
Proof.
  induction bs as [|[n e] tl IH]; intros f k Hk; [reflexivity|].
  simpl in Hk. cbn [fix_tab]. rewrite IH by tauto.
  destruct (Nat.eqb_spec k n) as [->|Hkn]; [exfalso; tauto | reflexivity].
Qed.

Lemma fixed_ext :
  forall f g e, (forall k, occurs k e -> f k = g k) -> fixed f e = fixed g e.
Proof.
  intros f g e. induction e; cbn [fixed occurs]; intros H.
  - apply H. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHe. exact H.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - rewrite IHe1, IHe2 by (intros k Hk; apply H; tauto). reflexivity.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - reflexivity.
Qed.

(** The table holds, at each binding's slot, whether its expression is fixed
    under the table itself. *)
Lemma fix_tab_bind :
  forall bs f next n e, well_formed next bs = true -> In (n, e) bs ->
  fix_tab f bs n = fixed (fix_tab f bs) e.
Proof.
  induction bs as [|[n0 e0] tl IH]; intros f next n e Hwf Hin; [destruct Hin|].
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hn0 He0]. apply Nat.eqb_eq in Hn0. subst n0.
  cbn [fix_tab].
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->.
    assert (Hout : forall k, (k <= n)%nat -> ~ In k (map fst tl)).
    { intros k Hk Hin. pose proof (well_formed_slots tl (S n) k Htl Hin). lia. }
    rewrite fix_tab_notin by (apply Hout; lia).
    rewrite Nat.eqb_refl. symmetry. apply fixed_ext. intros k Hk.
    pose proof (occurs_below n e k He0 Hk) as Hkn.
    rewrite fix_tab_notin by (apply Hout; lia).
    destruct (Nat.eqb_spec k n) as [->|]; [lia | reflexivity].
  - exact (IH _ (S next) n e Htl Hin).
Qed.

Lemma with_dd_slots :
  forall fx bs next k, well_formed next bs = true -> In k (map fst (with_dd fx bs)) ->
  (lm next <= k)%nat.
Proof.
  intros fx bs next k Hwf Hin.
  pose proof (well_formed_slots _ _ k (with_dd_wf fx bs next Hwf) Hin). lia.
Qed.

Section Values.

(** The outer environment: u, v and phip in the three layers of their slots,
    the jet of the node, the transform and the stream function at the two
    half points with their divided differences, the roots of the five radii,
    the step, mu0 p' at the node and the two sources. *)
Variable E : env ExtendedR.
Variables u v phip h s mpp fs fu im ip idd : R.
Variables xR dmR dpR eR xZ dmZ dpZ eZ Lm Lp Ldd : nat -> R.

Hypothesis Hu : eget 3 E Xnan = Xreal u /\ eget 4 E Xnan = Xreal u /\ eget 5 E Xnan = Xreal 0.
Hypothesis Hv : eget 6 E Xnan = Xreal v /\ eget 7 E Xnan = Xreal v /\ eget 8 E Xnan = Xreal 0.
Hypothesis Hph : eget 9 E Xnan = Xreal phip /\ eget 10 E Xnan = Xreal phip /\ eget 11 E Xnan = Xreal 0.
Hypothesis HjR : forall k, (k < rK)%nat ->
  eget (o_xR k) E Xnan = Xreal (xR k) /\ eget (o_dmR k) E Xnan = Xreal (dmR k) /\
  eget (o_dpR k) E Xnan = Xreal (dpR k) /\ eget (o_eR k) E Xnan = Xreal (eR k).
Hypothesis HjZ : forall k, (k < rK)%nat ->
  eget (o_xZ k) E Xnan = Xreal (xZ k) /\ eget (o_dmZ k) E Xnan = Xreal (dmZ k) /\
  eget (o_dpZ k) E Xnan = Xreal (dpZ k) /\ eget (o_eZ k) E Xnan = Xreal (eZ k).
Hypothesis HjL : forall k, (k < rK)%nat ->
  eget (o_Lm k) E Xnan = Xreal (Lm k) /\ eget (o_Lp k) E Xnan = Xreal (Lp k) /\
  eget (o_Ldd k) E Xnan = Xreal (Ldd k).
Hypothesis Hio : eget o_im E Xnan = Xreal im /\ eget o_ip E Xnan = Xreal ip /\
  eget o_idd E Xnan = Xreal idd.
Hypothesis Hroots :
  eget (o_r 0) E Xnan = Xreal (sqrt (s - h)) /\ eget (o_r 1) E Xnan = Xreal (sqrt (s - h / 2)) /\
  eget (o_r 2) E Xnan = Xreal (sqrt s) /\ eget (o_r 3) E Xnan = Xreal (sqrt (s + h / 2)) /\
  eget (o_r 4) E Xnan = Xreal (sqrt (s + h)).
Hypothesis Hrest : eget o_h E Xnan = Xreal h /\ eget o_mpp E Xnan = Xreal mpp /\
  eget o_fs E Xnan = Xreal fs /\ eget o_fu E Xnan = Xreal fu.
Hypothesis Hh0 : h <> 0.
Hypothesis Hsh : 0 < s - h.
Hypothesis Hsp : 0 < s + h.
Hypothesis HrelR : forall k, (k < rK)%nat -> dpR k - dmR k = h * eR k.
Hypothesis HrelZ : forall k, (k < rK)%nat -> dpZ k - dmZ k = h * eZ k.
Hypothesis HrelL : forall k, (k < rK)%nat -> Lp k - Lm k = h * Ldd k.
Hypothesis HrelI : ip - im = h * idd.
Hypothesis Hok : reg_ok = true.

Let Ep := xextend E prelim.
Let F := xextend E reg_binds.
Let Fm := layer_env F lm rtop.
Let Fp := layer_env F lp rtop.

Lemma ok_parts :
  well_formed sub_base sub_binds = true /\
  forallb (fun b => fixed rcov (snd b)) sub_binds = true /\
  forallb (fun q => vars_below rtop q && fixed rcov q) reg_outputs = true.
Proof.
  pose proof Hok as H. unfold reg_ok in H. rewrite !Bool.andb_true_iff in H.
  destruct H as [[H1 H2] H3]. auto.
Qed.

Lemma ok_wf : well_formed sub_base sub_binds = true.
Proof. exact (proj1 ok_parts). Qed.

Lemma ok_cov : forall n e, In (n, e) sub_binds -> fixed rcov e = true.
Proof.
  intros n e Hin. pose proof (proj1 (proj2 ok_parts)) as H1. rewrite forallb_forall in H1.
  exact (H1 (n, e) Hin).
Qed.

Lemma ok_out : forall q, In q reg_outputs -> vars_below rtop q = true /\ fixed rcov q = true.
Proof.
  intros q Hin. pose proof (proj2 (proj2 ok_parts)) as H2. rewrite forallb_forall in H2.
  apply andb_prop. exact (H2 q Hin).
Qed.

Lemma F_split : F = xextend Ep (with_dd rfx sub_binds).
Proof. unfold F, Ep, reg_binds. apply xextend_app. Qed.

(** Below the transform's slots, F holds what the layers of the inputs hold. *)
Lemma F_low : forall k, (k < lm sub_base)%nat -> eget k F Xnan = eget k Ep Xnan.
Proof.
  intros k Hk. rewrite F_split. apply eget_xextend_notin. intros Hin.
  pose proof (with_dd_slots rfx sub_binds sub_base k ok_wf Hin). lia.
Qed.

Lemma Ep_input :
  forall t a b c, nth_error descr t = Some (a, b, c) ->
  eget (lm (rk0 + t)) Ep Xnan = xeval E a /\ eget (lp (rk0 + t)) Ep Xnan = xeval E b /\
  eget (ld (rk0 + t)) Ep Xnan = xeval E c.
Proof. intros t a b c Ht. exact (prelim_from_vals descr rk0 E descr_reads t a b c Ht). Qed.

Lemma Ep_low : forall k, (k < lm rk0)%nat -> eget k Ep Xnan = eget k E Xnan.
Proof. intros k Hk. exact (prelim_from_low descr rk0 E k Hk). Qed.

Lemma sub_base_top : (sub_base <= rtop)%nat.
Proof. unfold rtop. lia. Qed.

(** The two value layers at an input of the half point. *)
Lemma layer_at :
  forall t a b c, nth_error descr t = Some (a, b, c) ->
  eget (rk0 + t) Fm Xnan = xeval E a /\ eget (rk0 + t) Fp Xnan = xeval E b.
Proof.
  intros t a b c Ht.
  assert (Hlt : (t < 5 + 5 * rK)%nat).
  { rewrite <- length_descr. apply nth_error_Some. rewrite Ht. discriminate. }
  assert (Hs : (rk0 + t < rtop)%nat) by (pose proof sub_base_top; unfold sub_base in *; lia).
  destruct (Ep_input t a b c Ht) as [V1 [V2 _]].
  unfold Fm, Fp. rewrite !eget_layer_env by exact Hs.
  rewrite !F_low by (unfold lm, lp, sub_base; lia).
  split; assumption.
Qed.

(** The layers of slots 1, 2, 3. *)
Lemma layer_uvp :
  eget 1 Fm Xnan = Xreal u /\ eget 1 Fp Xnan = Xreal u /\
  eget 2 Fm Xnan = Xreal v /\ eget 2 Fp Xnan = Xreal v /\
  eget 3 Fm Xnan = Xreal phip /\ eget 3 Fp Xnan = Xreal phip.
Proof.
  assert (Hb : (3 < rtop)%nat) by (pose proof sub_base_top; unfold sub_base, rk0 in *; lia).
  unfold Fm, Fp. rewrite !eget_layer_env by lia.
  rewrite !F_low by (unfold lm, lp, sub_base, rk0; lia).
  rewrite !Ep_low by (unfold lm, lp, rk0; lia).
  unfold lm, lp. cbn [Nat.mul Nat.add].
  destruct Hu as [U1 [U2 _]]. destruct Hv as [V1 [V2 _]]. destruct Hph as [P1 [P2 _]].
  repeat split; assumption.
Qed.

Lemma root_rel :
  forall A B, 0 < A -> 0 < B -> B - A = h -> sqrt B - sqrt A = h * (1 / (sqrt B + sqrt A)).
Proof.
  intros A B HA HB HBA.
  assert (SA := sqrt_lt_R0 A HA). assert (SB := sqrt_lt_R0 B HB).
  assert (QA := sqrt_sqrt A (Rlt_le _ _ HA)). assert (QB := sqrt_sqrt B (Rlt_le _ _ HB)).
  assert (E1 : h = sqrt B * sqrt B - sqrt A * sqrt A) by lra.
  rewrite E1. field. lra.
Qed.

(** Each descriptor's three expressions are real, and the plus less the minus
    is h times the divided difference. *)
Lemma descr_rel :
  forall a b c, In (a, b, c) descr ->
  exists am ap d, xeval E a = Xreal am /\ xeval E b = Xreal ap /\ xeval E c = Xreal d /\
                  ap - am = h * d.
Proof.
  destruct Hroots as [R0 [R1 [R2 [R3 R4]]]]. destruct Hrest as [Hh _].
  destruct Hio as [I1 [I2 I3]].
  assert (Root : forall A B ka kb, 0 < A -> 0 < B -> B - A = h ->
            eget ka E Xnan = Xreal (sqrt A) -> eget kb E Xnan = Xreal (sqrt B) ->
            exists am ap d, xeval E (Evar ka) = Xreal am /\ xeval E (Evar kb) = Xreal ap /\
              xeval E (Ediv e1 (Eadd (Evar kb) (Evar ka))) = Xreal d /\ ap - am = h * d).
  { intros A B ka kb HA HB HBA Ha Hb. exists (sqrt A), (sqrt B), (1 / (sqrt B + sqrt A)).
    assert (SA := sqrt_lt_R0 A HA). assert (SB := sqrt_lt_R0 B HB).
    cbn [xeval]. rewrite Ha, Hb. split; [reflexivity|]. split; [reflexivity|]. split.
    - unfold e1. cbn [xeval]. apply Xdiv_r. lra.
    - apply root_rel; assumption. }
  intros a b c Hin. rewrite descr_split in Hin.
  repeat (apply in_app_iff in Hin; destruct Hin as [Hin|Hin]).
  - simpl in Hin. destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]; try contradiction.
    + unfold dsc_h in Hq. injection Hq as <- <- <-. exists h, h, 0. cbn [xeval]. rewrite Hh.
      repeat split; try reflexivity. ring.
    + unfold dsc_root in Hq. injection Hq as <- <- <-.
      apply (Root (s - h) s); [lra | lra | ring | exact R0 | exact R2].
    + unfold dsc_root in Hq. injection Hq as <- <- <-.
      apply (Root s (s + h)); [lra | lra | ring | exact R2 | exact R4].
    + unfold dsc_root in Hq. injection Hq as <- <- <-.
      apply (Root (s - h / 2) (s + h / 2)); [lra | lra | field | exact R1 | exact R3].
    + unfold dsc_io in Hq. injection Hq as <- <- <-. exists im, ip, idd. cbn [xeval].
      rewrite I1, I2, I3. repeat split; try reflexivity. exact HrelI.
  - apply in_map_iff in Hin. destruct Hin as [j [Hq Hj]]. apply in_seq in Hj.
    destruct (HjR j ltac:(lia)) as [X1 [X2 _]]. unfold dsc_y in Hq. injection Hq as <- <- <-.
    exists (xR j - h * dmR j), (xR j), (dmR j). cbn [xeval]. rewrite X1, X2, Hh.
    repeat split; try reflexivity. ring.
  - apply in_map_iff in Hin. destruct Hin as [j [Hq Hj]]. apply in_seq in Hj.
    destruct (HjR j ltac:(lia)) as [_ [X2 [X3 X4]]]. unfold dsc_d in Hq. injection Hq as <- <- <-.
    exists (dmR j), (dpR j), (eR j). cbn [xeval]. rewrite X2, X3, X4.
    repeat split; try reflexivity. apply HrelR. lia.
  - apply in_map_iff in Hin. destruct Hin as [j [Hq Hj]]. apply in_seq in Hj.
    destruct (HjZ j ltac:(lia)) as [X1 [X2 _]]. unfold dsc_y in Hq. injection Hq as <- <- <-.
    exists (xZ j - h * dmZ j), (xZ j), (dmZ j). cbn [xeval]. rewrite X1, X2, Hh.
    repeat split; try reflexivity. ring.
  - apply in_map_iff in Hin. destruct Hin as [j [Hq Hj]]. apply in_seq in Hj.
    destruct (HjZ j ltac:(lia)) as [_ [X2 [X3 X4]]]. unfold dsc_d in Hq. injection Hq as <- <- <-.
    exists (dmZ j), (dpZ j), (eZ j). cbn [xeval]. rewrite X2, X3, X4.
    repeat split; try reflexivity. apply HrelZ. lia.
  - apply in_map_iff in Hin. destruct Hin as [j [Hq Hj]]. apply in_seq in Hj.
    destruct (HjL j ltac:(lia)) as [X1 [X2 X3]]. unfold dsc_L in Hq. injection Hq as <- <- <-.
    exists (Lm j), (Lp j), (Ldd j). cbn [xeval]. rewrite X1, X2, X3.
    repeat split; try reflexivity. apply HrelL. lia.
Qed.

Lemma rfx_low : forall k, (k < sub_base)%nat -> rfx k = fx_in k.
Proof.
  intros k Hk. unfold rfx. apply fix_tab_notin. intros Hin.
  pose proof (well_formed_slots sub_binds sub_base k ok_wf Hin). lia.
Qed.

(** The layers of the inputs are related as the transform requires. *)
Lemma dd_inv_Ep : dd_inv rfx h rcov Ep sub_base.
Proof.
  destruct Hu as [U1 [U2 U3]]. destruct Hv as [V1 [V2 V3]]. destruct Hph as [P1 [P2 P3]].
  assert (Low : forall k, (k < lm rk0)%nat -> eget k Ep Xnan = eget k E Xnan) by exact Ep_low.
  assert (Hrk : (12 < lm rk0)%nat) by (unfold lm, rk0; lia).
  assert (InDescr : forall k, (rk0 <= k < sub_base)%nat ->
            exists a b c, nth_error descr (k - rk0) = Some (a, b, c) /\
              eget (lm k) Ep Xnan = xeval E a /\ eget (lp k) Ep Xnan = xeval E b /\
              eget (ld k) Ep Xnan = xeval E c).
  { intros k Hk.
    assert (Ht : (k - rk0 < length descr)%nat) by (rewrite length_descr; unfold sub_base in Hk; lia).
    destruct (nth_error descr (k - rk0)) as [[[a b] c]|] eqn:Hn;
      [| apply nth_error_None in Hn; lia].
    destruct (Ep_input (k - rk0) a b c Hn) as [W1 [W2 W3]].
    replace (rk0 + (k - rk0))%nat with k in W1, W2, W3 by lia.
    exists a, b, c. auto. }
  split.
  - intros k am ap d Hk Hc Ha Hp Hd.
    unfold rcov in Hc. rewrite !Bool.orb_true_iff in Hc.
    destruct Hc as [[[Hc|Hc]|Hc]|Hc].
    + apply Nat.eqb_eq in Hc. subst k.
      rewrite Low in Ha, Hp, Hd by (unfold lm, lp, ld, rk0; lia). unfold lm, lp, ld in Ha, Hp, Hd.
      cbn [Nat.mul Nat.add] in Ha, Hp, Hd.
      rewrite U1 in Ha. rewrite U2 in Hp. rewrite U3 in Hd.
      injection Ha as <-. injection Hp as <-. injection Hd as <-. ring.
    + apply Nat.eqb_eq in Hc. subst k.
      rewrite Low in Ha, Hp, Hd by (unfold lm, lp, ld, rk0; lia). unfold lm, lp, ld in Ha, Hp, Hd.
      cbn [Nat.mul Nat.add] in Ha, Hp, Hd.
      rewrite V1 in Ha. rewrite V2 in Hp. rewrite V3 in Hd.
      injection Ha as <-. injection Hp as <-. injection Hd as <-. ring.
    + apply Nat.eqb_eq in Hc. subst k.
      rewrite Low in Ha, Hp, Hd by (unfold lm, lp, ld, rk0; lia). unfold lm, lp, ld in Ha, Hp, Hd.
      cbn [Nat.mul Nat.add] in Ha, Hp, Hd.
      rewrite P1 in Ha. rewrite P2 in Hp. rewrite P3 in Hd.
      injection Ha as <-. injection Hp as <-. injection Hd as <-. ring.
    + apply Nat.leb_le in Hc.
      destruct (InDescr k (conj Hc Hk)) as [a [b [c [Hn [W1 [W2 W3]]]]]].
      destruct (descr_rel a b c (nth_error_In _ _ Hn)) as [am' [ap' [d' [A1 [A2 [A3 Rel]]]]]].
      rewrite W1, A1 in Ha. rewrite W2, A2 in Hp. rewrite W3, A3 in Hd.
      injection Ha as <-. injection Hp as <-. injection Hd as <-. exact Rel.
  - intros k Hk Hc Hf. rewrite rfx_low in Hf by exact Hk.
    unfold fx_in in Hf. rewrite !Bool.orb_true_iff in Hf.
    destruct Hf as [[[Hf|Hf]|Hf]|Hf]; apply Nat.eqb_eq in Hf; subst k.
    + rewrite !Low by (unfold lm, lp, rk0; lia). unfold lm, lp. cbn [Nat.mul Nat.add].
      rewrite U1, U2. reflexivity.
    + rewrite !Low by (unfold lm, lp, rk0; lia). unfold lm, lp. cbn [Nat.mul Nat.add].
      rewrite V1, V2. reflexivity.
    + rewrite !Low by (unfold lm, lp, rk0; lia). unfold lm, lp. cbn [Nat.mul Nat.add].
      rewrite P1, P2. reflexivity.
    + destruct (InDescr s_h ltac:(unfold s_h, sub_base; lia)) as [a [b [c [Hn [W1 [W2 _]]]]]].
      replace (s_h - rk0)%nat with 0%nat in Hn by (unfold s_h; lia).
      rewrite (proj1 descr_at_head) in Hn. unfold dsc_h in Hn. injection Hn as <- <- <-.
      rewrite W1, W2. reflexivity.
Qed.

(** Through the half point's own bindings. *)
Lemma dd_inv_F : dd_inv rfx h rcov F rtop.
Proof.
  rewrite F_split. unfold rtop. apply dd_bindings; [exact dd_inv_Ep | exact ok_wf |].
  intros n e Hin.
  destruct (well_formed_in sub_binds sub_base n e ok_wf Hin) as [Hn _].
  split; [| split].
  - unfold rcov. rewrite !Bool.orb_true_iff. right. apply Nat.leb_le. unfold sub_base in Hn. lia.
  - intros k Hk. exact (fixed_occurs rcov e k (ok_cov n e Hin) Hk).
  - intros Hf. unfold rfx in *.
    rewrite <- (fix_tab_bind sub_binds fx_in sub_base n e ok_wf Hin). exact Hf.
Qed.

(** What each value layer holds at the inputs of the half point. *)
Lemma layer_vals :
  (eget s_h Fm Xnan = Xreal h /\ eget s_h Fp Xnan = Xreal h) /\
  (eget s_ra Fm Xnan = Xreal (sqrt (s - h)) /\ eget s_ra Fp Xnan = Xreal (sqrt s)) /\
  (eget s_rb Fm Xnan = Xreal (sqrt s) /\ eget s_rb Fp Xnan = Xreal (sqrt (s + h))) /\
  (eget s_rh Fm Xnan = Xreal (sqrt (s - h / 2)) /\ eget s_rh Fp Xnan = Xreal (sqrt (s + h / 2))) /\
  (eget s_io Fm Xnan = Xreal im /\ eget s_io Fp Xnan = Xreal ip) /\
  (forall j, (j < rK)%nat ->
     (eget (s_yR j) Fm Xnan = Xreal (xR j - h * dmR j) /\ eget (s_yR j) Fp Xnan = Xreal (xR j)) /\
     (eget (s_dR j) Fm Xnan = Xreal (dmR j) /\ eget (s_dR j) Fp Xnan = Xreal (dpR j)) /\
     (eget (s_yZ j) Fm Xnan = Xreal (xZ j - h * dmZ j) /\ eget (s_yZ j) Fp Xnan = Xreal (xZ j)) /\
     (eget (s_dZ j) Fm Xnan = Xreal (dmZ j) /\ eget (s_dZ j) Fp Xnan = Xreal (dpZ j)) /\
     (eget (s_L j) Fm Xnan = Xreal (Lm j) /\ eget (s_L j) Fp Xnan = Xreal (Lp j))).
Proof.
  assert (At : forall t a b c va vb, nth_error descr t = Some (a, b, c) ->
            xeval E a = Xreal va -> xeval E b = Xreal vb ->
            eget (rk0 + t) Fm Xnan = Xreal va /\ eget (rk0 + t) Fp Xnan = Xreal vb).
  { intros t a b c va vb Ht Ha Hb. destruct (layer_at t a b c Ht) as [L1 L2].
    rewrite L1, L2. auto. }
  destruct descr_at_head as [D0 [D1 [D2 [D3 D4]]]].
  unfold dsc_h in D0. unfold dsc_root in D1, D2, D3. unfold dsc_io in D4.
  destruct Hroots as [R0 [R1 [R2 [R3 R4]]]]. destruct Hrest as [Hh _].
  destruct Hio as [I1 [I2 _]].
  split. { replace s_h with (rk0 + 0)%nat by (unfold s_h; lia).
           apply (At 0%nat _ _ _ h h D0); cbn [xeval]; exact Hh. }
  split. { apply (At 1%nat _ _ _ _ _ D1); cbn [xeval]; [exact R0 | exact R2]. }
  split. { apply (At 2%nat _ _ _ _ _ D2); cbn [xeval]; [exact R2 | exact R4]. }
  split. { apply (At 3%nat _ _ _ _ _ D3); cbn [xeval]; [exact R1 | exact R3]. }
  split. { apply (At 4%nat _ _ _ _ _ D4); cbn [xeval]; [exact I1 | exact I2]. }
  intros j Hj.
  destruct (descr_at_block j Hj) as [B1 [B2 [B3 [B4 B5]]]].
  unfold dsc_y in B1, B3. unfold dsc_d in B2, B4. unfold dsc_L in B5.
  destruct (HjR j Hj) as [X1 [X2 [X3 X4]]]. destruct (HjZ j Hj) as [Z1 [Z2 [Z3 Z4]]].
  destruct (HjL j Hj) as [Y1 [Y2 Y3]].
  split. { replace (s_yR j) with (rk0 + (5 + j))%nat by (unfold s_yR; lia).
           apply (At _ _ _ _ _ _ B1); cbn [xeval]; [rewrite X1, X2, Hh; reflexivity | exact X1]. }
  split. { replace (s_dR j) with (rk0 + (5 + rK + j))%nat by (unfold s_dR; lia).
           apply (At _ _ _ _ _ _ B2); cbn [xeval]; [exact X2 | exact X3]. }
  split. { replace (s_yZ j) with (rk0 + (5 + 2 * rK + j))%nat by (unfold s_yZ; lia).
           apply (At _ _ _ _ _ _ B3); cbn [xeval]; [rewrite Z1, Z2, Hh; reflexivity | exact Z1]. }
  split. { replace (s_dZ j) with (rk0 + (5 + 3 * rK + j))%nat by (unfold s_dZ; lia).
           apply (At _ _ _ _ _ _ B4); cbn [xeval]; [exact Z2 | exact Z3]. }
  { replace (s_L j) with (rk0 + (5 + 4 * rK + j))%nat by (unfold s_L; lia).
    apply (At _ _ _ _ _ _ B5); cbn [xeval]; [exact Y1 | exact Y2]. }
Qed.

(** Each value layer, read as an environment, is sound for the half point's
    bindings. *)
Lemma sound_layers : sound Fm (b_binds (fst reg_sub)) /\ sound Fp (b_binds (fst reg_sub)).
Proof.
  assert (Hin : forall n e, In (n, e) (b_binds (fst reg_sub)) -> In (n, e) sub_binds)
    by (intros n e H; unfold sub_binds, bindings_of; apply in_rev; rewrite rev_involutive; exact H).
  split; intros n e H; unfold Fm, Fp, rtop; rewrite F_split.
  - exact (layer_sound rfx sub_binds Ep sub_base lm (or_introl eq_refl) ok_wf n e (Hin n e H)).
  - exact (layer_sound rfx sub_binds Ep sub_base lp (or_intror eq_refl) ok_wf n e (Hin n e H)).
Qed.

Lemma ren_layer :
  forall f q, vars_below rtop q = true ->
  xeval F (ren f q) = xeval (layer_env F f rtop) q.
Proof.
  intros f q Hb. rewrite !xeval_f, xevalf_ren. apply xevalf_ext. intros k Hk.
  symmetry. apply eget_layer_env. exact (occurs_below _ _ _ Hb Hk).
Qed.

(** The divided difference of an output is the difference of its two layers
    over h. *)
Lemma dd_rel :
  forall q, In q reg_outputs ->
  forall am ap d, xeval Fm q = Xreal am -> xeval Fp q = Xreal ap ->
  xeval F (dd rfx q) = Xreal d -> ap - am = h * d.
Proof.
  intros q Hin am ap d Ha Hp Hd. destruct (ok_out q Hin) as [Hb Hcov].
  destruct dd_inv_F as [Rel Fx].
  apply (dd_correct rfx (fun k => eget k F Xnan) h q).
  - intros k am' ap' d' Hk A P D.
    exact (Rel k am' ap' d' (occurs_below _ _ _ Hb Hk) (fixed_occurs rcov q k Hcov Hk) A P D).
  - intros k Hk Hf. exact (Fx k (occurs_below _ _ _ Hb Hk) (fixed_occurs rcov q k Hcov Hk) Hf).
  - rewrite <- xeval_f. rewrite (ren_layer lm q Hb). exact Ha.
  - rewrite <- xeval_f. rewrite (ren_layer lp q Hb). exact Hp.
  - rewrite <- xeval_f. exact Hd.
Qed.

Lemma coefL_terms (E' : env ExtendedR) (g : nat -> R) :
  (forall j, (j < rK)%nat -> eget (s_L j) E' Xnan = Xreal (g j)) ->
  Forall2 (kcoefe_ok E' 0) (map (fun k => Evar (s_L k)) (seq 0 rK))
          (cterms (fun j _ => g j) (fun _ _ => 0%R) modes).
Proof.
  intros Hg. unfold cterms.
  assert (Gen : forall (ms : list (Z * Z)) k,
            (forall j, (k <= j < k + length ms)%nat -> eget (s_L j) E' Xnan = Xreal (g j)) ->
            Forall2 (kcoefe_ok E' 0) (map (fun k => Evar (s_L k)) (seq k (length ms)))
              (map (mkterm (fun j _ _ => g j) (fun _ _ _ => 0%R) (fun _ _ _ => 0%R))
                   (combine (seq k (length ms)) ms))).
  { induction ms as [|mn tl IH]; intros k Hk; [constructor|].
    cbn [length seq map combine]. constructor.
    - unfold kcoefe_ok, mkterm. cbn [tc fst snd xeval]. apply Hk. simpl. lia.
    - apply IH. intros j Hj. apply Hk. simpl. lia. }
  apply Gen. intros j Hj. apply Hg. unfold rK. lia.
Qed.

(** The node's three rows of each coefficient, and the jets of the field at
    the two half points that node_residual reads. *)
Definition yR (row j : nat) : R :=
  match row with O => xR j - h * dmR j | 1%nat => xR j | _ => xR j + h * dpR j end.
Definition yZ (row j : nat) : R :=
  match row with O => xZ j - h * dmZ j | 1%nat => xZ j | _ => xZ j + h * dpZ j end.

Definition jm : jet :=
  hjet (cterms (hya (s - h) s (s - h / 2) yR) (hda (s - h) s (s - h / 2) yR) modes)
       (cterms (hya (s - h) s (s - h / 2) yZ) (hda (s - h) s (s - h / 2) yZ) modes)
       (cterms (fun j _ => Lm j) (fun _ _ => 0%R) modes) u v im phip.
Definition jp : jet :=
  hjet (cterms (hyb s (s + h) (s + h / 2) yR) (hdb s (s + h) (s + h / 2) yR) modes)
       (cterms (hyb s (s + h) (s + h / 2) yZ) (hdb s (s + h) (s + h / 2) yZ) modes)
       (cterms (fun j _ => Lp j) (fun _ _ => 0%R) modes) u v ip phip.

Lemma xeval_phip :
  forall E', eget 3 E' Xnan = Xreal phip -> xeval E' (vPhip rexps) = Xreal phip.
Proof.
  intros E' H3. unfold vPhip, evar, epow2. cbn [xeval nth rexps]. rewrite H3.
  cbn [Xmul]. f_equal. simpl. ring.
Qed.

Lemma xeval_uv :
  forall E', eget 1 E' Xnan = Xreal u -> eget 2 E' Xnan = Xreal v ->
  xeval E' (vU rexps) = Xreal u /\ xeval E' (vV rexps) = Xreal v.
Proof.
  intros E' H1 H2. unfold vU, vV, evar, epow2. cbn [xeval nth rexps]. rewrite H1, H2.
  cbn [Xmul]. split; f_equal; simpl; ring.
Qed.

(** The field of each half point, read from its layer where that half
    point's Jacobian is nonzero; and a real B^v in a layer makes it
    nonzero. *)
Lemma half_layers :
  ((f_sqrtg jm <> 0 ->
    xeval Fm (q_Bu sub_q) = Xreal (f_Bu jm) /\ xeval Fm (q_Bv sub_q) = Xreal (f_Bv jm) /\
    xeval Fm (q_B_u sub_q) = Xreal (Bcov_u jm) /\ xeval Fm (q_B_v sub_q) = Xreal (Bcov_v jm) /\
    xeval Fm (q_B_s_u sub_q) = Xreal (f_B_s_u jm) /\ xeval Fm (q_B_s_v sub_q) = Xreal (f_B_s_v jm) /\
    xeval Fm (q_mu0Js sub_q) = Xreal (f_mu0Js jm)) /\
   (forall y, xeval Fm (q_Bv sub_q) = Xreal y -> f_sqrtg jm <> 0)) /\
  ((f_sqrtg jp <> 0 ->
    xeval Fp (q_Bu sub_q) = Xreal (f_Bu jp) /\ xeval Fp (q_Bv sub_q) = Xreal (f_Bv jp) /\
    xeval Fp (q_B_u sub_q) = Xreal (Bcov_u jp) /\ xeval Fp (q_B_v sub_q) = Xreal (Bcov_v jp) /\
    xeval Fp (q_B_s_u sub_q) = Xreal (f_B_s_u jp) /\ xeval Fp (q_B_s_v sub_q) = Xreal (f_B_s_v jp) /\
    xeval Fp (q_mu0Js sub_q) = Xreal (f_mu0Js jp)) /\
   (forall y, xeval Fp (q_Bv sub_q) = Xreal y -> f_sqrtg jp <> 0)).
Proof.
  destruct reg_sub_spec as [b1 [cR [b2 [cZ [b3 [kers [Q1 [Q2 [Q3 Q4]]]]]]]]].
  rewrite (surjective_pairing reg_sub) in Q4. unfold sub_q.
  destruct (half_point_ok rexps Fm _ _ _ _ _ _ Q4) as [X4 V4].
  destruct (half_point_ok rexps Fp _ _ _ _ _ _ Q4) as [_ W4].
  assert (V4' := half_point_bv_nz rexps Fm _ _ _ _ _ _ Q4).
  assert (W4' := half_point_bv_nz rexps Fp _ _ _ _ _ _ Q4).
  destruct sound_layers as [Sm Sp].
  destruct (kernels_spec rexps modes _ _ _ Q3) as [X3 _].
  destruct (hr_b_spec s_yZ s_dZ modes 0 _ _ _ Q2) as [X2 _].
  assert (Sm3 := sound_extends Fm _ _ X4 Sm). assert (Sp3 := sound_extends Fp _ _ X4 Sp).
  assert (Sm2 := sound_extends Fm _ _ X3 Sm3). assert (Sp2 := sound_extends Fp _ _ X3 Sp3).
  assert (Sm1 := sound_extends Fm _ _ X2 Sm2). assert (Sp1 := sound_extends Fp _ _ X2 Sp2).
  destruct layer_vals as [[Hhm Hhp] [[Ram Rap] [[Rbm Rbp] [[Rhm Rhp] [[Iom Iop] Blk]]]]].
  destruct layer_uvp as [Um [Up [Vm [Vp [Pm Pp]]]]].
  assert (P0 : 0 < s - h) by exact Hsh.
  assert (P1 : 0 < s - h / 2) by lra. assert (P2 : 0 < s) by lra.
  assert (P3 : 0 < s + h / 2) by lra. assert (P4 : 0 < s + h) by lra.
  assert (Hne : h <> 0) by lra.
  assert (Dm : s - (s - h) = h) by ring. assert (Dp : s + h - s = h) by ring.
  (* the node rows of each coefficient in the two layers *)
  assert (YRm : forall j, (j < length modes)%nat ->
            eget (s_yR j) Fm Xnan = Xreal (yR 0 j) /\ eget (s_dR j) Fm Xnan = Xreal (dmR j) /\
            yR 0 j + h * dmR j = yR 1 j).
  { intros j Hj. destruct (Blk j Hj) as [[A _] [[B _] _]]. cbn [yR]. split; [exact A|].
    split; [exact B | ring]. }
  assert (YZm : forall j, (j < length modes)%nat ->
            eget (s_yZ j) Fm Xnan = Xreal (yZ 0 j) /\ eget (s_dZ j) Fm Xnan = Xreal (dmZ j) /\
            yZ 0 j + h * dmZ j = yZ 1 j).
  { intros j Hj. destruct (Blk j Hj) as [_ [_ [[A _] [[B _] _]]]]. cbn [yZ]. split; [exact A|].
    split; [exact B | ring]. }
  assert (YRp : forall j, (j < length modes)%nat ->
            eget (s_yR j) Fp Xnan = Xreal (yR 1 j) /\ eget (s_dR j) Fp Xnan = Xreal (dpR j) /\
            yR 1 j + h * dpR j = yR 2 j).
  { intros j Hj. destruct (Blk j Hj) as [[_ A] [[_ B] _]]. cbn [yR]. split; [exact A|].
    split; [exact B | ring]. }
  assert (YZp : forall j, (j < length modes)%nat ->
            eget (s_yZ j) Fp Xnan = Xreal (yZ 1 j) /\ eget (s_dZ j) Fp Xnan = Xreal (dpZ j) /\
            yZ 1 j + h * dpZ j = yZ 2 j).
  { intros j Hj. destruct (Blk j Hj) as [_ [_ [[_ A] [[_ B] _]]]]. cbn [yZ]. split; [exact A|].
    split; [exact B | ring]. }
  (* the minus layer: radii s - h, s, s - h/2; the plus layer: s, s + h, s + h/2 *)
  assert (CRm := hr_b_values Fm _ _ s_yR s_dR modes cR (yR 0) (yR 1) dmR h (s - h) s (s - h / 2)
                   Q1 Sm1 Hhm Ram Rbm Rhm YRm P0 P2 P1 Dm Hne).
  assert (CZm := hr_b_values Fm _ _ s_yZ s_dZ modes cZ (yZ 0) (yZ 1) dmZ h (s - h) s (s - h / 2)
                   Q2 Sm2 Hhm Ram Rbm Rhm YZm P0 P2 P1 Dm Hne).
  assert (CRp := hr_b_values Fp _ _ s_yR s_dR modes cR (yR 1) (yR 2) dpR h s (s + h) (s + h / 2)
                   Q1 Sp1 Hhp Rap Rbp Rhp YRp P2 P4 P3 Dp Hne).
  assert (CZp := hr_b_values Fp _ _ s_yZ s_dZ modes cZ (yZ 1) (yZ 2) dpZ h s (s + h) (s + h / 2)
                   Q2 Sp2 Hhp Rap Rbp Rhp YZp P2 P4 P3 Dp Hne).
  destruct (xeval_uv Fm Um Vm) as [UVm1 UVm2]. destruct (xeval_uv Fp Up Vp) as [UVp1 UVp2].
  assert (KVm := kernels_values rexps Fm u v modes _ _ _ Q3 Sm3 UVm1 UVm2).
  assert (KVp := kernels_values rexps Fp u v modes _ _ _ Q3 Sp3 UVp1 UVp2).
  assert (LLm : forall j, (j < rK)%nat -> eget (s_L j) Fm Xnan = Xreal (Lm j))
    by (intros j Hj; exact (proj1 (proj2 (proj2 (proj2 (proj2 (Blk j Hj))))))).
  assert (LLp : forall j, (j < rK)%nat -> eget (s_L j) Fp Xnan = Xreal (Lp j))
    by (intros j Hj; exact (proj2 (proj2 (proj2 (proj2 (proj2 (Blk j Hj))))))).
  assert (TRm := zip_ok (kcoef2_ok Fm 0) kers cR _ (kker_ok Fm u v) (kers_cterms Fm u v _ _ modes kers KVm)
                   (coef2_terms Fm (hya (s - h) s (s - h / 2) yR) (hda (s - h) s (s - h / 2) yR) modes cR CRm)).
  assert (TZm := zip_ok (kcoef2_ok Fm 0) kers cZ _ (kker_ok Fm u v) (kers_cterms Fm u v _ _ modes kers KVm)
                   (coef2_terms Fm (hya (s - h) s (s - h / 2) yZ) (hda (s - h) s (s - h / 2) yZ) modes cZ CZm)).
  assert (TLm := zip_ok (kcoefe_ok Fm 0) kers _ _ (kker_ok Fm u v)
                   (kers_cterms Fm u v (fun j _ => Lm j) (fun _ _ => 0%R) modes kers KVm) (coefL_terms Fm Lm LLm)).
  assert (TRp := zip_ok (kcoef2_ok Fp 0) kers cR _ (kker_ok Fp u v) (kers_cterms Fp u v _ _ modes kers KVp)
                   (coef2_terms Fp (hyb s (s + h) (s + h / 2) yR) (hdb s (s + h) (s + h / 2) yR) modes cR CRp)).
  assert (TZp := zip_ok (kcoef2_ok Fp 0) kers cZ _ (kker_ok Fp u v) (kers_cterms Fp u v _ _ modes kers KVp)
                   (coef2_terms Fp (hyb s (s + h) (s + h / 2) yZ) (hdb s (s + h) (s + h / 2) yZ) modes cZ CZp)).
  assert (TLp := zip_ok (kcoefe_ok Fp 0) kers _ _ (kker_ok Fp u v)
                   (kers_cterms Fp u v (fun j _ => Lp j) (fun _ _ => 0%R) modes kers KVp) (coefL_terms Fp Lp LLp)).
  split; split.
  - intros Hm. eapply (V4 Sm _ _ _ u v im phip TRm TZm TLm); [cbn [xeval]; exact Iom | exact (xeval_phip Fm Pm) | exact Hm].
  - intros y Hy. eapply (V4' Sm _ _ _ u v im phip TRm TZm TLm);
      [cbn [xeval]; exact Iom | exact (xeval_phip Fm Pm) | exact Hy].
  - intros Hp. eapply (W4 Sp _ _ _ u v ip phip TRp TZp TLp); [cbn [xeval]; exact Iop | exact (xeval_phip Fp Pp) | exact Hp].
  - intros y Hy. eapply (W4' Sp _ _ _ u v ip phip TRp TZp TLp);
      [cbn [xeval]; exact Iop | exact (xeval_phip Fp Pp) | exact Hy].
Qed.

Lemma half_fields :
  f_sqrtg jm <> 0 -> f_sqrtg jp <> 0 ->
  (xeval Fm (q_Bu sub_q) = Xreal (f_Bu jm) /\ xeval Fm (q_Bv sub_q) = Xreal (f_Bv jm) /\
   xeval Fm (q_B_u sub_q) = Xreal (Bcov_u jm) /\ xeval Fm (q_B_v sub_q) = Xreal (Bcov_v jm) /\
   xeval Fm (q_B_s_u sub_q) = Xreal (f_B_s_u jm) /\ xeval Fm (q_B_s_v sub_q) = Xreal (f_B_s_v jm) /\
   xeval Fm (q_mu0Js sub_q) = Xreal (f_mu0Js jm)) /\
  (xeval Fp (q_Bu sub_q) = Xreal (f_Bu jp) /\ xeval Fp (q_Bv sub_q) = Xreal (f_Bv jp) /\
   xeval Fp (q_B_u sub_q) = Xreal (Bcov_u jp) /\ xeval Fp (q_B_v sub_q) = Xreal (Bcov_v jp) /\
   xeval Fp (q_B_s_u sub_q) = Xreal (f_B_s_u jp) /\ xeval Fp (q_B_s_v sub_q) = Xreal (f_B_s_v jp) /\
   xeval Fp (q_mu0Js sub_q) = Xreal (f_mu0Js jp)).
Proof. intros Hm Hp. destruct half_layers as [[A _] [B _]]. split; [exact (A Hm) | exact (B Hp)]. Qed.

(** A real B^v in a layer makes that half point's Jacobian nonzero. *)
Lemma bv_real_nz :
  (forall y, xeval Fm (q_Bv sub_q) = Xreal y -> f_sqrtg jm <> 0) /\
  (forall y, xeval Fp (q_Bv sub_q) = Xreal y -> f_sqrtg jp <> 0).
Proof. destruct half_layers as [[_ A] [_ B]]. split; [exact A | exact B]. Qed.

Lemma Xmul_real_inv : forall x y r, Xmul x y = Xreal r -> (exists a, x = Xreal a) /\ (exists b, y = Xreal b).
Proof. intros [|a] [|b] r H; cbn in H; try discriminate; split; eexists; reflexivity. Qed.

Lemma Xadd_real_inv : forall x y r, Xadd x y = Xreal r -> (exists a, x = Xreal a) /\ (exists b, y = Xreal b).
Proof. intros [|a] [|b] r H; cbn in H; try discriminate; split; eexists; reflexivity. Qed.

Lemma Xsub_real_inv : forall x y r, Xsub x y = Xreal r -> (exists a, x = Xreal a) /\ (exists b, y = Xreal b).
Proof. intros [|a] [|b] r H; cbn in H; try discriminate; split; eexists; reflexivity. Qed.

Lemma Xneg_real_inv : forall x r, Xneg x = Xreal r -> exists a, x = Xreal a.
Proof. intros [|a] r H; cbn in H; try discriminate. eexists; reflexivity. Qed.

Lemma in_outputs :
  In (q_Bu sub_q) reg_outputs /\ In (q_Bv sub_q) reg_outputs /\ In (q_B_u sub_q) reg_outputs /\
  In (q_B_v sub_q) reg_outputs /\ In (q_B_s_u sub_q) reg_outputs /\
  In (q_B_s_v sub_q) reg_outputs /\ In (q_mu0Js sub_q) reg_outputs.
Proof.
  unfold reg_outputs. cbn [In].
  split; [left; reflexivity|]. split; [right; left; reflexivity|].
  split; [do 2 right; left; reflexivity|]. split; [do 3 right; left; reflexivity|].
  split; [do 4 right; left; reflexivity|]. split; [do 5 right; left; reflexivity|].
  do 6 right; left; reflexivity.
Qed.

Lemma ravg_val :
  forall q am ap, In q reg_outputs -> xeval Fm q = Xreal am -> xeval Fp q = Xreal ap ->
  xeval F (ravg q) = Xreal (1 / 2 * (am + ap)).
Proof.
  intros q am ap Hin Ha Hp. destruct (ok_out q Hin) as [Hb _].
  unfold ravg, ehalf, e1, e2. cbn [xeval].
  rewrite (ren_layer lm q Hb), (ren_layer lp q Hb). fold Fm Fp. rewrite Ha, Hp.
  rewrite Xdiv_r by (apply not_0_IZR; lia). reflexivity.
Qed.

Lemma F_outer : forall k, (k < lm rk0)%nat -> eget k F Xnan = eget k E Xnan.
Proof.
  intros k Hk. rewrite F_low by (unfold lm, sub_base in *; lia). apply Ep_low. exact Hk.
Qed.

(** The poloidal component: the forced r_u of node_residual at the outer half
    point. *)
Theorem reg_fu_ok :
  f_sqrtg jm <> 0 -> f_sqrtg jp <> 0 -> xeval F reg_fu = Xreal (cres_u jp - fu).
Proof.
  intros Hm Hp.
  destruct (half_fields Hm Hp) as [_ [_ [Pv [_ [_ [_ [_ Pj]]]]]]].
  destruct in_outputs as [_ [Iv [_ [_ [_ [_ Ij]]]]]].
  destruct Hrest as [_ [_ [_ Hfu]]].
  unfold reg_fu. cbn [xeval].
  rewrite (ren_layer lp _ (proj1 (ok_out _ Ij))), (ren_layer lp _ (proj1 (ok_out _ Iv))).
  fold Fp. rewrite Pj, Pv.
  rewrite F_outer by (unfold o_fu, lm, rk0; lia). rewrite Hfu.
  reflexivity.
Qed.

(** The radial component: wherever it is real, the forced r_s of
    node_residual, node_rs of the two half-point jets with the reciprocal of
    the spacing, less the source. *)
Theorem reg_fs_ok :
  f_sqrtg jm <> 0 -> f_sqrtg jp <> 0 ->
  forall r, xeval F reg_fs = Xreal r -> r = node_rs jm jp (1 / h) mpp - fs.
Proof.
  intros Hm Hp r Hr.
  destruct (half_fields Hm Hp)
    as [[Mu [Mv [Mcu [Mcv [Msu [Msv _]]]]]] [Pu [Pv [Pcu [Pcv [Psu [Psv _]]]]]]].
  destruct in_outputs as [Iu [Iv [Icu [Icv [Isu [Isv _]]]]]].
  destruct Hrest as [_ [Hmpp [Hfs _]]].
  unfold reg_fs, reg_rs in Hr. cbn [xeval] in Hr.
  rewrite (ravg_val _ _ _ Isv Msv Psv), (ravg_val _ _ _ Iv Mv Pv), (ravg_val _ _ _ Isu Msu Psu),
    (ravg_val _ _ _ Iu Mu Pu) in Hr.
  rewrite (F_outer o_mpp) in Hr by (unfold o_mpp, lm, rk0; lia).
  rewrite (F_outer o_fs) in Hr by (unfold o_fs, lm, rk0; lia).
  rewrite Hmpp, Hfs in Hr.
  destruct (xeval F (dd rfx (q_B_v sub_q))) as [|dv] eqn:Edv; [cbn in Hr; discriminate|].
  destruct (xeval F (dd rfx (q_B_u sub_q))) as [|du] eqn:Edu; [cbn in Hr; discriminate|].
  assert (Rv := dd_rel _ Icv _ _ _ Mcv Pcv Edv).
  assert (Ru := dd_rel _ Icu _ _ _ Mcu Pcu Edu).
  cbn in Hr. injection Hr as <-.
  unfold node_rs. rewrite Rv, Ru. field. lra.
Qed.

(** A real radial output has both half points' Jacobians nonzero, and a real
    poloidal output the outer one's. *)
Lemma fs_real_nz : forall r, xeval F reg_fs = Xreal r -> f_sqrtg jm <> 0 /\ f_sqrtg jp <> 0.
Proof.
  intros r Hr. destruct in_outputs as [_ [Iv _]].
  unfold reg_fs, reg_rs in Hr. cbn [xeval] in Hr.
  apply Xsub_real_inv in Hr as [[a1 Ha1] _].
  apply Xsub_real_inv in Ha1 as [[a2 Ha2] _].
  apply Xsub_real_inv in Ha2 as [[a3 Ha3] _].
  apply Xmul_real_inv in Ha3 as [_ [a4 Ha4]].
  unfold ravg in Ha4. cbn [xeval] in Ha4.
  apply Xmul_real_inv in Ha4 as [_ [a5 Ha5]].
  apply Xadd_real_inv in Ha5 as [[am Ham] [ap Hap]].
  rewrite (ren_layer lm _ (proj1 (ok_out _ Iv))) in Ham.
  rewrite (ren_layer lp _ (proj1 (ok_out _ Iv))) in Hap.
  destruct bv_real_nz as [Nm Np]. split; [exact (Nm am Ham) | exact (Np ap Hap)].
Qed.

Lemma fu_real_nz : forall r, xeval F reg_fu = Xreal r -> f_sqrtg jp <> 0.
Proof.
  intros r Hr. destruct in_outputs as [_ [Iv _]].
  unfold reg_fu in Hr. cbn [xeval] in Hr.
  apply Xsub_real_inv in Hr as [[a1 Ha1] _].
  apply Xneg_real_inv in Ha1 as [a2 Ha2].
  apply Xmul_real_inv in Ha2 as [_ [ap Hap]].
  rewrite (ren_layer lp _ (proj1 (ok_out _ Iv))) in Hap.
  exact (proj2 bv_real_nz ap Hap).
Qed.

(** The poloidal output from the outer half point alone. *)
Theorem reg_fu_ok_p : f_sqrtg jp <> 0 -> xeval F reg_fu = Xreal (cres_u jp - fu).
Proof.
  intros Hp.
  destruct half_layers as [_ [B _]]. destruct (B Hp) as [_ [Pv [_ [_ [_ [_ Pj]]]]]].
  destruct in_outputs as [_ [Iv [_ [_ [_ [_ Ij]]]]]].
  destruct Hrest as [_ [_ [_ Hfu]]].
  unfold reg_fu. cbn [xeval].
  rewrite (ren_layer lp _ (proj1 (ok_out _ Ij))), (ren_layer lp _ (proj1 (ok_out _ Iv))).
  fold Fp. rewrite Pj, Pv.
  rewrite F_outer by (unfold o_fu, lm, rk0; lia). rewrite Hfu.
  reflexivity.
Qed.

End Values.

End Reg.

(** The modes of the three-dimensional manufactured problem. *)
Definition modes3d : list (Z * Z) := [(0, 0); (0, 3); (1, -3); (1, 0); (1, 3)]%Z.

Lemma reg_ok_3d : reg_ok modes3d = true.
Proof. vm_compute. reflexivity. Qed.
