(** The linearized collocated rows as a one-step recursion.

    A row j of the linearized system couples the perturbation X_j of the
    node's nine coefficients to its neighbours through the slopes
    d_j = (X_j - X_{j-1}) / h and d_{j+1}. Its five radial rows and four
    poloidal rows read

      (Pp_j d_{j+1} - Pm_j d_j) / h + Sx_j X_j = rs_j,
      Up_j d_{j+1} + V_j X_j = ru_j,

    with Pp = Re + h Rdp, Pm = Re - h Rdm, Sx = Rx from the radial residual's
    partial derivatives in the node value x, the two slopes dm and dp and the
    second difference e of the jet, and Up = Rdp, V = Rx from the poloidal
    residual's, which reads no dm and no e. Stacking Pp_j over Up_j gives the
    9 x 9 matrix M_j; with its inverse, the row determines d_{j+1} from X_j and
    p_j = Pm_j d_j, so the state z_j = (X_j, p_j) of 14 numbers advances by
    [step]: d_{j+1} = M_j^-1 [p_j - h Sx_j X_j + h rs_j; - V_j X_j + ru_j],
    X_{j+1} = X_j + h d_{j+1}, p_{j+1} = Pm_{j+1} d_{j+1}.

    [rows_step] reads a solution of the rows as a run of the recursion, and
    [step_rows] reads a run of the recursion whose first state satisfies
    the start condition p = Pm X / h back as a solution of the rows with the
    node before the first at zero. *)

From Coq Require Import Reals Lra Lia.
From Stellarocq Require Import Mat.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Vectors of 9 and of 14                                            *)

(** The state: the node's nine coefficients in 0 .. 8 and p in 9 .. 13. *)
Definition zjoin (x p : vec) : vec := fun i => if Nat.ltb i 9 then x i else p (i - 9)%nat.
Definition zx (z : vec) : vec := fun i => z i.
Definition zp (z : vec) : vec := fun i => z (9 + i)%nat.

(** The right-hand side of the stacked rows: five radial entries over four
    poloidal ones. *)
Definition stack (a b : vec) : vec := fun i => if Nat.ltb i 5 then a i else b (i - 5)%nat.

(** M_j, Pp_j over Up_j. *)
Definition mstack (A B : mat) : mat := fun i k => if Nat.ltb i 5 then A i k else B (i - 5)%nat k.

Lemma mv_mstack :
  forall A B x i, mv 9 (mstack A B) x i = stack (mv 9 A x) (mv 9 B x) i.
Proof.
  intros A B x i. unfold mv, mstack, stack. destruct (Nat.ltb i 5); reflexivity.
Qed.

Lemma zx_zjoin : forall x p i, (i < 9)%nat -> zx (zjoin x p) i = x i.
Proof. intros x p i Hi. unfold zx, zjoin. rewrite (proj2 (Nat.ltb_lt i 9) Hi). reflexivity. Qed.

Lemma zp_zjoin : forall x p i, zp (zjoin x p) i = p i.
Proof.
  intros x p i. unfold zp, zjoin. replace (Nat.ltb (9 + i) 9) with false by (symmetry; apply Nat.ltb_ge; lia).
  f_equal. lia.
Qed.

Lemma mv_ext9 : forall A x y i, (forall k, (k < 9)%nat -> x k = y k) -> mv 9 A x i = mv 9 A y i.
Proof. intros A x y i H. unfold mv. apply msum_ext. intros k Hk. rewrite H by exact Hk. reflexivity. Qed.

(** A left inverse recovers a vector from its image. *)
Lemma left_inv_apply :
  forall (Mj Mij : mat) (d b : vec),
  (forall i k, (i < 9)%nat -> (k < 9)%nat -> mm 9 Mij Mj i k = mI i k) ->
  (forall i, (i < 9)%nat -> mv 9 Mj d i = b i) ->
  forall i, (i < 9)%nat -> mv 9 Mij b i = d i.
Proof.
  intros Mj Mij d b HL Hb i Hi.
  rewrite (mv_ext9 Mij b (mv 9 Mj d) i) by (intros k Hk; symmetry; apply Hb; exact Hk).
  rewrite <- mv_mm.
  unfold mv. rewrite (msum_ext _ (fun k => mI i k * d k)) by (intros k Hk; rewrite HL by assumption; reflexivity).
  fold (mv 9 mI d i). apply mv_mI. exact Hi.
Qed.

(** A right inverse solves. *)
Lemma right_inv_apply :
  forall (Mj Mij : mat) (b : vec),
  (forall i k, (i < 9)%nat -> (k < 9)%nat -> mm 9 Mj Mij i k = mI i k) ->
  forall i, (i < 9)%nat -> mv 9 Mj (mv 9 Mij b) i = b i.
Proof.
  intros Mj Mij b HR i Hi. rewrite <- mv_mm.
  unfold mv. rewrite (msum_ext _ (fun k => mI i k * b k)) by (intros k Hk; rewrite HR by assumption; reflexivity).
  fold (mv 9 mI b i). apply mv_mI. exact Hi.
Qed.

Section Rows.

Variable h : R.
Hypothesis Hh : 0 < h.

(** The blocks of every row, and an inverse of each M_j. *)
Variables Pp Pm Sx Up V Mi : nat -> mat.

Definition M (j : nat) : mat := mstack (Pp j) (Up j).

(** The slope into node j. *)
Definition slope (X : nat -> vec) (j : nat) : vec := fun i => (X j i - X (j - 1)%nat i) / h.

(** The radial and poloidal rows of the linearized system at node j. *)
Definition rs_row (X : nat -> vec) (j : nat) : vec :=
  fun i => (mv 9 (Pp j) (slope X (S j)) i - mv 9 (Pm j) (slope X j) i) / h + mv 9 (Sx j) (X j) i.
Definition ru_row (X : nat -> vec) (j : nat) : vec :=
  fun i => mv 9 (Up j) (slope X (S j)) i + mv 9 (V j) (X j) i.

(** The right-hand side the rows give M_j d_{j+1}. *)
Definition rhs (j : nat) (z rs ru : vec) : vec :=
  stack (fun i => zp z i - h * mv 9 (Sx j) (zx z) i + h * rs i)
        (fun i => - mv 9 (V j) (zx z) i + ru i).

(** One step of the recursion. *)
Definition dnext (j : nat) (z rs ru : vec) : vec := mv 9 (Mi j) (rhs j z rs ru).
Definition step (j : nat) (z rs ru : vec) : vec :=
  zjoin (fun i => zx z i + h * dnext j z rs ru i) (mv 9 (Pm (S j)) (dnext j z rs ru)).

(** The state of a node: its coefficients and Pm times its slope. *)
Definition state (X : nat -> vec) (j : nat) : vec := zjoin (X j) (mv 9 (Pm j) (slope X j)).

(** A solution of the rows advances by [step]. *)
Theorem rows_step :
  forall X rs ru j,
  (forall i k, (i < 9)%nat -> (k < 9)%nat -> mm 9 (Mi j) (M j) i k = mI i k) ->
  (forall i, (i < 5)%nat -> rs_row X j i = rs i) ->
  (forall i, (i < 4)%nat -> ru_row X j i = ru i) ->
  forall i, (i < 14)%nat -> step j (state X j) rs ru i = state X (S j) i.
Proof.
  intros X rs ru j HL Hs Hu.
  assert (Hd : forall i, (i < 9)%nat -> dnext j (state X j) rs ru i = slope X (S j) i).
  { intros i Hi. unfold dnext. apply (left_inv_apply (M j) (Mi j) (slope X (S j))); [exact HL| |exact Hi].
    intros i' Hi'. unfold M. rewrite mv_mstack. unfold rhs, stack. cbv beta.
    destruct (Nat.ltb_spec i' 5) as [H5|H5].
    - specialize (Hs i' H5). unfold rs_row in Hs.
      unfold state. rewrite zp_zjoin.
      rewrite (mv_ext9 (Sx j) (zx (zjoin (X j) (mv 9 (Pm j) (slope X j)))) (X j) i')
        by (intros k Hk; apply zx_zjoin; exact Hk).
      apply (Rmult_eq_compat_l h) in Hs.
      replace (h * ((mv 9 (Pp j) (slope X (S j)) i' - mv 9 (Pm j) (slope X j) i') / h + mv 9 (Sx j) (X j) i'))
        with (mv 9 (Pp j) (slope X (S j)) i' - mv 9 (Pm j) (slope X j) i' + h * mv 9 (Sx j) (X j) i')
        in Hs by (field; lra).
      lra.
    - specialize (Hu (i' - 5)%nat ltac:(lia)). unfold ru_row in Hu.
      unfold state.
      rewrite (mv_ext9 (V j) (zx (zjoin (X j) (mv 9 (Pm j) (slope X j)))) (X j) (i' - 5))
        by (intros k Hk; apply zx_zjoin; exact Hk).
      lra. }
  intros i Hi. unfold step.
  change (state X (S j) i) with (zjoin (X (S j)) (mv 9 (Pm (S j)) (slope X (S j))) i).
  unfold zjoin at 1 2. cbv beta.
  destruct (Nat.ltb_spec i 9) as [H9|H9].
  - rewrite Hd by exact H9. unfold zx, state, zjoin. rewrite (proj2 (Nat.ltb_lt i 9) H9).
    unfold slope. replace (S j - 1)%nat with j by lia. field. lra.
  - apply mv_ext9. intros k Hk. apply Hd. exact Hk.
Qed.

(** Read back: a run of the recursion from a state with p = Pm X / h is the
    sequence of states of a solution of the rows, whose nodes are the states'
    first nine entries from a on and zero before. *)
Section Back.

Variables (a n : nat) (Z : nat -> vec) (RS RU : nat -> vec).

Definition nodes (j : nat) : vec := fun i => if Nat.ltb j a then 0 else zx (Z j) i.

Hypothesis Ha : (0 < a)%nat.
Hypothesis Hstart : forall i, (i < 5)%nat -> zp (Z a) i = mv 9 (Pm a) (zx (Z a)) i / h.
Hypothesis Hrun : forall j, (a <= j < a + n)%nat ->
  forall i, (i < 14)%nat -> Z (S j) i = step j (Z j) (RS j) (RU j) i.
Hypothesis Hinv : forall j, (a <= j < a + n)%nat ->
  forall i k, (i < 9)%nat -> (k < 9)%nat -> mm 9 (M j) (Mi j) i k = mI i k.

Lemma nodes_from : forall j i, (a <= j)%nat -> nodes j i = zx (Z j) i.
Proof. intros j i Hj. unfold nodes. rewrite (proj2 (Nat.ltb_ge j a) Hj). reflexivity. Qed.

(** The slope into node j + 1 is the step's d. *)
Lemma slope_run :
  forall j, (a <= j < a + n)%nat -> forall i, (i < 9)%nat ->
  slope nodes (S j) i = dnext j (Z j) (RS j) (RU j) i.
Proof.
  intros j Hj i Hi. unfold slope. replace (S j - 1)%nat with j by lia.
  rewrite !nodes_from by lia. unfold zx at 1. rewrite (Hrun j Hj i ltac:(lia)). unfold step.
  unfold zjoin. rewrite (proj2 (Nat.ltb_lt i 9) Hi). unfold zx. field. lra.
Qed.

(** p is Pm times the slope at every state of the run. *)
Lemma p_run :
  forall j, (a <= j <= a + n)%nat -> forall i, (i < 5)%nat ->
  zp (Z j) i = mv 9 (Pm j) (slope nodes j) i.
Proof.
  intros j Hj i Hi.
  destruct (Nat.eq_dec j a) as [->|Hne].
  - rewrite Hstart by exact Hi. unfold mv, Rdiv. rewrite <- msum_scal_r.
    apply msum_ext. intros k Hk. unfold slope.
    rewrite (nodes_from a k) by lia. unfold nodes.
    replace (Nat.ltb (a - 1) a) with true by (symmetry; apply Nat.ltb_lt; lia).
    field. lra.
  - destruct j as [|j']; [lia|].
    assert (Hj' : (a <= j' < a + n)%nat) by lia.
    unfold zp. rewrite (Hrun j' Hj' (9 + i) ltac:(lia)).
    fold (zp (step j' (Z j') (RS j') (RU j')) i). unfold step. rewrite zp_zjoin.
    apply mv_ext9. intros k Hk. symmetry. apply slope_run; assumption.
Qed.

(** The run solves the rows. *)
Theorem step_rows :
  forall j, (a <= j < a + n)%nat ->
  (forall i, (i < 5)%nat -> rs_row nodes j i = RS j i) /\
  (forall i, (i < 4)%nat -> ru_row nodes j i = RU j i).
Proof.
  intros j Hj.
  assert (HM : forall i, (i < 9)%nat ->
            mv 9 (M j) (slope nodes (S j)) i = rhs j (Z j) (RS j) (RU j) i).
  { intros i Hi. rewrite (mv_ext9 (M j) (slope nodes (S j)) (dnext j (Z j) (RS j) (RU j)) i)
      by (intros k Hk; apply slope_run; assumption).
    unfold dnext. apply right_inv_apply; [apply Hinv; exact Hj | exact Hi]. }
  assert (Hx : forall k, (k < 9)%nat -> zx (Z j) k = nodes j k) by (intros k Hk; symmetry; apply nodes_from; lia).
  split.
  - intros i Hi. specialize (HM i ltac:(lia)). unfold M in HM. rewrite mv_mstack in HM.
    unfold rhs, stack in HM. cbv beta in HM. rewrite (proj2 (Nat.ltb_lt i 5) Hi) in HM.
    rewrite (p_run j ltac:(lia) i Hi) in HM.
    rewrite (mv_ext9 (Sx j) (zx (Z j)) (nodes j) i) in HM by exact Hx.
    unfold rs_row. apply (Rmult_eq_reg_l h); [| lra].
    replace (h * ((mv 9 (Pp j) (slope nodes (S j)) i - mv 9 (Pm j) (slope nodes j) i) / h
                  + mv 9 (Sx j) (nodes j) i))
      with (mv 9 (Pp j) (slope nodes (S j)) i - mv 9 (Pm j) (slope nodes j) i + h * mv 9 (Sx j) (nodes j) i)
      by (field; lra).
    lra.
  - intros i Hi. specialize (HM (5 + i)%nat ltac:(lia)). unfold M in HM. rewrite mv_mstack in HM.
    unfold rhs, stack in HM. cbv beta in HM.
    replace (Nat.ltb (5 + i) 5) with false in HM by (symmetry; apply Nat.ltb_ge; lia).
    replace (5 + i - 5)%nat with i in HM by lia.
    rewrite (mv_ext9 (V j) (zx (Z j)) (nodes j) i) in HM by exact Hx.
    unfold ru_row. lra.
Qed.

End Back.

End Rows.
