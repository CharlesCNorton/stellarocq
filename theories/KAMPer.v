(** Pairs and matrices of families of one field period.

    A pair or a matrix of families belongs to period P when every entry
    does ([vper], [mper]); the operations of the Newton step on pairs and
    matrices keep the class. *)

From Coq Require Import ZArith Reals Lra Lia.
From Stellarocq Require Import Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierInv FourierPer KAMVec.
Local Open Scope R_scope.

Section Period.

Variable P : Z.
Hypothesis HP : (0 < P)%Z.

Definition vper (u : vf) : Prop := is_per P (vR u) /\ is_per P (vZ u).
Definition mper (A : mf) : Prop :=
  is_per P (mRR A) /\ is_per P (mRZ A) /\ is_per P (mZR A) /\ is_per P (mZZ A).

Lemma vper_vadd (u v : vf) : vper u -> vper v -> vper (vadd u v).
Proof. intros [A B] [C D]. split; apply fadd_per; assumption. Qed.

Lemma vper_vsub (u v : vf) : vper u -> vper v -> vper (vsub u v).
Proof. intros [A B] [C D]. split; apply fsub_per; assumption. Qed.

Lemma vper_vscal (c : R) (u : vf) : vper u -> vper (vscal c u).
Proof. intros [A B]. split; apply fscal_per; assumption. Qed.

Lemma vper_vsmul (s : fser) (u : vf) : is_per P s -> vper u -> vper (vsmul s u).
Proof. intros Hs [A B]. split; apply fmul_per; assumption. Qed.

Lemma vper_vdt (u : vf) : vper u -> vper (vdt u).
Proof. intros [A B]. split; apply dt_per; assumption. Qed.

Lemma vper_vlc (om : R) (u : vf) : vper u -> vper (vlc om u).
Proof. intros [A B]. split; apply lc_per; assumption. Qed.

Lemma vper_vJ (u : vf) : vper u -> vper (vJ u).
Proof. intros [A B]. split; [apply fscal_per, B | exact A]. Qed.

Lemma wedge_per (u v : vf) : vper u -> vper v -> is_per P (wedge u v).
Proof. intros [A B] [C D]. unfold wedge. apply fsub_per; apply fmul_per; assumption. Qed.

Lemma vdot_per (u v : vf) : vper u -> vper v -> is_per P (vdot u v).
Proof. intros [A B] [C D]. unfold vdot. apply fadd_per; apply fmul_per; assumption. Qed.

Lemma mapp_per (A : mf) (u : vf) : mper A -> vper u -> vper (mapp A u).
Proof.
  intros [H1 [H2 [H3 H4]]] [U1 U2]. unfold mapp. split; simpl; apply fadd_per; apply fmul_per; assumption.
Qed.

Lemma mtr_per (A : mf) : mper A -> is_per P (mtr A).
Proof. intros [H1 [_ [_ H4]]]. unfold mtr. apply fadd_per; assumption. Qed.

Lemma fconst_per (c : R) : is_per P (fconst c).
Proof. unfold fconst. apply fsingle0_per, HP. Qed.

End Period.
