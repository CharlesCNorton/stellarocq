(** One source along a finite torus: supports and norms of its families.

    Along a torus whose two families are carried by the box (Km, Kn), the
    distance families of a source are carried by (Km, Kn + 1) ([fr1_supp],
    [fr2_supp], [fr3_supp]), q by (2 Km, 2 Kn + 2) ([fq_supp]), and with a seed
    Y carried by (Ky1, Ky2) the defect 1 - q Y^2 by (2 Km + 2 Ky1,
    2 Kn + 2 + 2 Ky2) ([defect_supp]), so its norm is read exactly from the
    transforms on a grid past that box. The distance families are bounded
    by the norms of the torus, of cos p and of the source's coordinates
    ([fr1_nb], [fr2_nb], [fr3_nb]), and q by the sum of their squares
    ([fq_nb]). At a point the defect is 1 - q(t, p) Y(t, p)^2 ([defect_val]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierParity FourierDFT FourierCanon FourierModel FourierList FourierSupp KAMVec KAMFin
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldTaylor.
Local Open Scope R_scope.

Lemma supp_canon (K1 K2 : nat) (u : fser) : supp K1 K2 u -> supp K1 K2 (canon u).
Proof.
  intros H m n Hmn. unfold canon, ccan, scan. simpl.
  assert (Hmn' : in_box K1 K2 (- m) (- n) = false).
  { apply in_box_false. apply in_box_false in Hmn. rewrite !Z.abs_opp. exact Hmn. }
  destruct (H m n Hmn) as [A B]. destruct (H _ _ Hmn') as [C D].
  rewrite A, B, C, D. split; ring.
Qed.

Lemma cosf_supp : supp 0 1 cosf.
Proof. unfold cosf. apply fadd_supp; apply fsingle_supp; simpl; lia. Qed.

Lemma sinf_supp : supp 0 1 sinf.
Proof. unfold sinf. apply fadd_supp; apply fsingle_supp; simpl; lia. Qed.

Lemma fconst_supp (K1 K2 : nat) (c : R) : supp K1 K2 (fconst c).
Proof. unfold fconst. apply fsingle_supp; simpl; lia. Qed.

Lemma fone_supp (K1 K2 : nat) : supp K1 K2 fone.
Proof. unfold fone. apply fsingle_supp; simpl; lia. Qed.

Section Source.

Variables (sc : src) (K : vf) (Km Kn : nat).
Hypothesis SR : supp Km Kn (vR K).
Hypothesis SZ : supp Km Kn (vZ K).

Lemma fr1_supp : supp Km (S Kn) (fr1 sc K).
Proof.
  unfold fr1, fx1. apply fsub_supp; [| apply fconst_supp].
  replace Km with (Km + 0)%nat by lia. replace (S Kn) with (Kn + 1)%nat by lia.
  apply fmul_supp; [exact SR | exact cosf_supp].
Qed.

Lemma fr2_supp : supp Km (S Kn) (fr2 sc K).
Proof.
  unfold fr2, fx2. apply fsub_supp; [| apply fconst_supp].
  replace Km with (Km + 0)%nat by lia. replace (S Kn) with (Kn + 1)%nat by lia.
  apply fmul_supp; [exact SR | exact sinf_supp].
Qed.

Lemma fr3_supp : supp Km (S Kn) (fr3 sc K).
Proof.
  unfold fr3. apply fsub_supp; [| apply fconst_supp].
  apply (supp_mono Km Kn); [lia | lia | exact SZ].
Qed.

Lemma fq_supp : supp (Km + Km) (S Kn + S Kn) (fq sc K).
Proof.
  unfold fq. apply fadd_supp; [apply fadd_supp |]; apply fmul_supp;
    first [exact fr1_supp | exact fr2_supp | exact fr3_supp].
Qed.

Variables (Y : fser) (Ky1 Ky2 : nat).
Hypothesis SY : supp Ky1 Ky2 Y.

Definition defect : fser := fsub fone (fmul (fq sc K) (fmul Y Y)).

Theorem defect_supp : supp ((Km + Km) + (Ky1 + Ky1)) ((S Kn + S Kn) + (Ky2 + Ky2)) defect.
Proof.
  unfold defect. apply fsub_supp; [apply fone_supp |].
  apply fmul_supp; [exact fq_supp | apply fmul_supp; exact SY].
Qed.

End Source.

(** * Norms *)

Section Norms.

Variables (sc : src) (K : vf) (w NR NZ : R).
Hypothesis Hw : 0 <= w.
Hypothesis BR : nbound w NR (vR K).
Hypothesis BZ : nbound w NZ (vZ K).

Theorem fr1_nb : nbound w (NR * wt w 0 1 + Rabs (sp1 sc)) (fr1 sc K).
Proof.
  unfold fr1, fx1. apply nbound_fsub; [apply nbound_fmul; [exact Hw | exact BR | apply nb_cosf] | apply nbound_fconst].
Qed.

Theorem fr2_nb : nbound w (NR * wt w 0 1 + Rabs (sp2 sc)) (fr2 sc K).
Proof.
  unfold fr2, fx2. apply nbound_fsub; [apply nbound_fmul; [exact Hw | exact BR | apply nb_sinf] | apply nbound_fconst].
Qed.

Theorem fr3_nb : nbound w (NZ + Rabs (sp3 sc)) (fr3 sc K).
Proof. unfold fr3. apply nbound_fsub; [exact BZ | apply nbound_fconst]. Qed.

Theorem fq_nb (r1 r2 r3 : R) :
  nbound w r1 (fr1 sc K) -> nbound w r2 (fr2 sc K) -> nbound w r3 (fr3 sc K) ->
  nbound w (r1 * r1 + r2 * r2 + r3 * r3) (fq sc K).
Proof.
  intros B1 B2 B3. unfold fq. apply nbound_fadd; [apply nbound_fadd |]; apply nbound_fmul; assumption.
Qed.

End Norms.

(** * The defect at a point *)

Theorem defect_val (sc : src) (K : vf) (Y : fser) (rho : R) (t p : R) :
  0 < rho -> vfin rho K -> fin 0 Y ->
  feval (defect sc K Y) t p
  = 1 - qk sc (kx1 (feval (vR K) t p) p) (kx2 (feval (vR K) t p) p) (feval (vZ K) t p) * (feval Y t p * feval Y t p).
Proof.
  intros Hr FK FY.
  destruct (E_q sc K rho Hr FK) as [Fq Eq].
  assert (Fq0 : fin 0 (fq sc K)) by (apply (fin_mono rho); [lra | exact Fq]).
  assert (FYY : fin 0 (fmul Y Y)) by exact (fin_fmul 0 _ _ (Rle_refl 0) FY FY).
  assert (Fone : fin 0 fone) by (exists 1; apply nbound_fone).
  unfold defect.
  rewrite (feval_fsub' t p _ _ Fone (fin_fmul 0 _ _ (Rle_refl 0) Fq0 FYY)).
  rewrite (feval_fmul' t p _ _ Fq0 FYY), (feval_fmul' t p _ _ FY FY), Eq, feval_fone. reflexivity.
Qed.
