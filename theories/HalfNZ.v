(** A half point whose contravariant field B^v is real has a nonzero
    Jacobian.

    [half_point_bv_nz]: with the hypotheses of Residuals.half_point_ok other
    than sqrt(g) <> 0, a real value of the slot B^v = phip (1 + lambda_u) /
    sqrt(g) makes sqrt(g) of the half-point jet nonzero, since a division by
    zero has no value. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Deriv Cell Force Series Recon Continuum Residuals.
Import ListNotations.

Section HalfNZ.
Variable exps : list Z.
Variable E : env ExtendedR.

Lemma half_point_bv_nz (b : builder) (kers : list mode_kernels) (hc : half_coefs) (iota : expr)
    (b' : builder) (q : halfq) :
  half_point_b exps b false kers hc iota = (b', q) ->
  (sound E (b_binds b') -> forall (tR tZ tL : list term) (u v io ph : R),
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_R hc)) tR ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E 0 (snd kc) t) (combine kers (hc_Z hc)) tZ ->
   Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E 0 (snd kc) t) (combine kers (hc_L hc)) tL ->
   xeval E iota = Xreal io -> xeval E (vPhip exps) = Xreal ph ->
   forall y, xeval E (q_Bv q) = Xreal y -> f_sqrtg (hjet tR tZ tL u v io ph) <> 0%R).
Proof.
  unfold half_point_b. cbv beta iota zeta. repeat step. intros H. injection H as <- <-.
  intros S tR tZ tL u v io ph HR HZ HL Hio Hph y Hy Hsg. peel.
  match goal with
  | QL : lambda_partials_b ?b1 _ = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (sound_extends E _ _ (proj1 (lambda_partials_ok E _ _ _ _ QL)) S) as SL;
      pose proof (proj2 (lambda_partials_ok E _ _ _ _ QL) S) as PL
  end.
  match goal with
  | QZ : partials_b ?b1 (assemble _ _ false) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (sound_extends E _ _ (proj1 (partials_ok E _ _ _ _ QZ)) S) as SZ;
      pose proof (proj2 (partials_ok E _ _ _ _ QZ) S) as PZ
  end.
  match goal with
  | QR : partials_b ?b1 (assemble _ _ true) = (?b2, _), S : sound E (b_binds ?b2) |- _ =>
      pose proof (proj2 (partials_ok E _ _ _ _ QR) S) as PR
  end.
  pose proof (assemble_values E true kers (hc_R hc) tR 0 u v HR) as FR.
  pose proof (assemble_values E false kers (hc_Z hc) tZ 0 u v HZ) as FZ.
  pose proof (lambda_terms_values E false kers (hc_L hc) tL 0 u v HL) as FL.
  cbv zeta in FR, FZ, FL.
  destruct PR as (PR1 & PR2 & PR3 & PR4 & PR5 & PR6 & PR7 & PR8 & PR9).
  destruct PZ as (PZ1 & PZ2 & PZ3 & PZ4 & PZ5 & PZ6 & PZ7 & PZ8 & PZ9).
  destruct PL as (PL1 & PL2 & PL3 & PL4 & PL5).
  destruct FR as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & FR8 & FR9).
  destruct FZ as (FZ1 & FZ2 & FZ3 & FZ4 & FZ5 & FZ6 & FZ7 & FZ8 & FZ9).
  destruct FL as (FL1 & FL2 & FL3 & FL4 & FL5).
  pose proof (eq_trans PR1 FR1) as W1. pose proof (eq_trans PR2 FR2) as W2.
  pose proof (eq_trans PR3 FR3) as W3. pose proof (eq_trans PR4 FR4) as W4.
  pose proof (eq_trans PR5 FR5) as W5. pose proof (eq_trans PR6 FR6) as W6.
  pose proof (eq_trans PR7 FR7) as W7. pose proof (eq_trans PR8 FR8) as W8.
  pose proof (eq_trans PR9 FR9) as W9.
  pose proof (eq_trans PZ1 FZ1) as W10. pose proof (eq_trans PZ2 FZ2) as W11.
  pose proof (eq_trans PZ3 FZ3) as W12. pose proof (eq_trans PZ4 FZ4) as W13.
  pose proof (eq_trans PZ5 FZ5) as W14. pose proof (eq_trans PZ6 FZ6) as W15.
  pose proof (eq_trans PZ7 FZ7) as W16. pose proof (eq_trans PZ8 FZ8) as W17.
  pose proof (eq_trans PZ9 FZ9) as W18.
  pose proof (eq_trans PL1 FL1) as W19. pose proof (eq_trans PL2 FL2) as W20.
  pose proof (eq_trans PL3 FL3) as W21. pose proof (eq_trans PL4 FL4) as W22.
  pose proof (eq_trans PL5 FL5) as W23.
  clear PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PZ1 PZ2 PZ3 PZ4 PZ5 PZ6 PZ7 PZ8 PZ9 PL1 PL2 PL3 PL4 PL5
        FR1 FR2 FR3 FR4 FR5 FR6 FR7 FR8 FR9 FZ1 FZ2 FZ3 FZ4 FZ5 FZ6 FZ7 FZ8 FZ9 FL1 FL2 FL3 FL4 FL5.
  unfold f_sqrtg, f_tau, hjet in Hsg. cbn [jR jRs jRu jZs jZu] in Hsg.
  unfold Physics.e1, Physics.esq, Physics.zmul in *.
  cbn [q_Bv] in Hy. revert Hy. xcalc.
  cbv [Xbind2 Xbind Xdiv' Xsqrt'].
  rewrite Hsg, is_zero_0. intros Hy. discriminate Hy.
Qed.

End HalfNZ.
