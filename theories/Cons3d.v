(** Consistency of order h^2 of the collocated three-dimensional problem at
    the exact solution.

    The half-grid rule reads two nodes symmetrically: the value and slope of
    a coefficient at a half point are the same with the nodes exchanged
    ([hval_swap], [hslope_swap]). So the half-point jets of the exact
    solution at the step -h are those at h exchanged ([jm3_neg], [jp3_neg]),
    the radial node residual, whose difference of the two half points is
    taken over the step, is even in h ([node_rs_neg]), and the poloidal
    residual at the outer half point t, read at the node t - h/2 with the
    step h, is even in h as well ([jp3_shift]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coq Require Import FunctionalExtensionality.
From Stellarocq Require Import Expr Continuum RegResidual Jet.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* The half-grid rule exchanges its nodes                            *)

Lemma hval_swap : forall m sa sb sh ya yb, hval m sa sb sh ya yb = hval m sb sa sh yb ya.
Proof. intros. unfold hval. destruct (Z.even m); ring. Qed.

Lemma inv_sub_swap : forall a b, 1 / (a - b) = - (1 / (b - a)).
Proof.
  intros a b. replace (a - b) with (- (b - a)) by ring. unfold Rdiv. rewrite !Rmult_1_l. apply Rinv_opp.
Qed.

Lemma hslope_swap : forall m sa sb sh ya yb, hslope m sa sb sh ya yb = hslope m sb sa sh yb ya.
Proof.
  intros. unfold hslope. rewrite (inv_sub_swap sa sb). destruct (Z.even m); ring.
Qed.

(** The node values the rule reads at the step -h. *)
Lemma dmX_neg : forall X s h, h <> 0 -> dmX X s (- h) = dpX X s h.
Proof. intros X s h Hh. unfold dmX, dpX. replace (s - - h) with (s + h) by ring. field. exact Hh. Qed.

Lemma dpX_neg : forall X s h, h <> 0 -> dpX X s (- h) = dmX X s h.
Proof. intros X s h Hh. unfold dmX, dpX. replace (s + - h) with (s - h) by ring. field. exact Hh. Qed.

Lemma node_m_neg : forall X s h, h <> 0 -> X s - - h * dmX X s (- h) = X s + h * dpX X s h.
Proof. intros X s h Hh. rewrite dmX_neg by exact Hh. ring. Qed.

Lemma node_p_neg : forall X s h, h <> 0 -> X s + - h * dpX X s (- h) = X s - h * dmX X s h.
Proof. intros X s h Hh. rewrite dpX_neg by exact Hh. ring. Qed.

(* ---------------------------------------------------------------- *)
(* The half-point jets at -h                                         *)

Lemma jm3_neg : forall u v s h, h <> 0 -> jm3 u v s (- h) = jp3 u v s h.
Proof.
  intros u v s h Hh. unfold jm3, jp3, jm, jp.
  replace (s - - h) with (s + h) by ring. replace (s - - h / 2) with (s + h / 2) by field.
  f_equal; f_equal; apply functional_extensionality; intros j; apply functional_extensionality; intros m;
    unfold hya, hyb, hda, hdb; cbn [yR yZ];
    first [rewrite hval_swap | rewrite hslope_swap]; f_equal; apply node_m_neg; exact Hh.
Qed.

Lemma jp3_neg : forall u v s h, h <> 0 -> jp3 u v s (- h) = jm3 u v s h.
Proof.
  intros u v s h Hh. unfold jm3, jp3, jm, jp.
  replace (s + - h) with (s - h) by ring. replace (s + - h / 2) with (s - h / 2) by field.
  f_equal; f_equal; apply functional_extensionality; intros j; apply functional_extensionality; intros m;
    unfold hya, hyb, hda, hdb; cbn [yR yZ];
    first [rewrite hval_swap | rewrite hslope_swap]; f_equal; apply node_p_neg; exact Hh.
Qed.

(** The radial node residual is even in the step. *)
Lemma node_rs_swap : forall jm' jp' ih mpp, node_rs jm' jp' ih mpp = node_rs jp' jm' (- ih) mpp.
Proof. intros. unfold node_rs. ring. Qed.

Lemma node_rs_neg :
  forall u v s h mpp, h <> 0 ->
  node_rs (jm3 u v s (- h)) (jp3 u v s (- h)) (1 / - h) mpp = node_rs (jm3 u v s h) (jp3 u v s h) (1 / h) mpp.
Proof.
  intros u v s h mpp Hh. rewrite jm3_neg, jp3_neg by exact Hh. rewrite node_rs_swap.
  replace (- (1 / - h)) with (1 / h) by (field; exact Hh). reflexivity.
Qed.

(** The outer half point t read from the node t - h/2 with the step h, and
    from t + h/2 with -h: the same jet. *)
Lemma node_shift_p : forall X t h, h <> 0 -> X (t + h / 2) + - h * dpX X (t + h / 2) (- h) = X (t - h / 2).
Proof. intros X t h Hh. unfold dpX. replace (t + h / 2 + - h) with (t - h / 2) by field. field. exact Hh. Qed.

Lemma node_shift_q : forall X t h, h <> 0 -> X (t - h / 2) + h * dpX X (t - h / 2) h = X (t + h / 2).
Proof. intros X t h Hh. unfold dpX. replace (t - h / 2 + h) with (t + h / 2) by field. field. exact Hh. Qed.

Lemma jp3_shift : forall u v t h, h <> 0 -> jp3 u v (t + h / 2) (- h) = jp3 u v (t - h / 2) h.
Proof.
  intros u v t h Hh. unfold jp3, jp.
  replace (t + h / 2 + - h) with (t - h / 2) by field. replace (t + h / 2 + - h / 2) with t by field.
  replace (t - h / 2 + h) with (t + h / 2) by field. replace (t - h / 2 + h / 2) with t by field.
  f_equal; f_equal; apply functional_extensionality; intros j; apply functional_extensionality; intros m;
    unfold hyb, hdb; cbn [yR yZ];
    first [rewrite hval_swap | rewrite hslope_swap];
    (f_equal; [apply node_shift_p; exact Hh | symmetry; apply node_shift_q; exact Hh]).
Qed.
