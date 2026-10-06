(** Taylor bounds for the field of one source between two tori.

    For two tori K and K', the field of one source along K' is its field
    along K, plus its derivatives in R and Z along K applied to the
    difference of the tori, plus a remainder of second order in that
    difference. Along the tori x' = x + dx with dx = (dR cos p, dR sin p, dZ)
    and q' = q + e with e = 2 r.dx + |dx|^2, so the inverse square root
    splits as y' = y z with z the inverse square root of 1 + e y^2
    ([tz]), taken from the approximant 1 - e y^2 / 2. The remainder is then
    an explicit family in y, z, r and dx ([tXR], [tXP], [tXZ]), equal to the
    difference by its function ([r2R_feq], [r2P_feq], [r2Z_feq]). *)

From Coq Require Import ZArith Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon KAMVec KAMFin Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel.
Local Open Scope R_scope.

(** * Pointwise facts *)

Lemma h3_y (q : R) : 0 < q -> / (q * sqrt q) = / sqrt q * / sqrt q * / sqrt q.
Proof.
  intros H. pose proof (sqrt_sqrt q (Rlt_le _ _ H)) as S. pose proof (sqrt_lt_R0 q H) as P.
  replace (q * sqrt q) with (sqrt q * sqrt q * sqrt q) by (rewrite S; reflexivity). field. lra.
Qed.

Lemma h5_y (q : R) : 0 < q ->
  / (q * q * sqrt q) = / sqrt q * / sqrt q * / sqrt q * / sqrt q * / sqrt q.
Proof.
  intros H. pose proof (sqrt_sqrt q (Rlt_le _ _ H)) as S. pose proof (sqrt_lt_R0 q H) as P.
  replace (q * q * sqrt q) with (sqrt q * sqrt q * (sqrt q * sqrt q) * sqrt q) by (rewrite S; reflexivity).
  field. lra.
Qed.

Lemma isq_split (q e : R) : 0 < q -> 0 < q + e ->
  / sqrt (q + e) = / sqrt q * / sqrt (1 + e * (/ sqrt q * / sqrt q)).
Proof.
  intros Hq Hqe. pose proof (sqrt_sqrt q (Rlt_le _ _ Hq)) as S. pose proof (sqrt_lt_R0 q Hq) as P.
  pose proof (sqrt_lt_R0 _ Hqe) as P'.
  replace (1 + e * (/ sqrt q * / sqrt q)) with ((q + e) / q).
  2: { set (s := sqrt q) in *. rewrite <- S. field. lra. }
  rewrite sqrt_div_alt by exact Hq. field. split; lra.
Qed.

(** The remainder at one point. Between the points (R0, phi, Z0) and
    (R1, phi, Z1), with e = q1 - q0 in the form [pe], y the inverse square
    root at the first point and y z at the second, the field at the second
    point less the field and its derivatives at the first is [pX] in each
    Cartesian component, read in e_R, e_phi and e_z. *)
Definition pe (sc : src) (R0 R1 Z0 Z1 phi : R) : R :=
  2 * ((kx1 R0 phi - sp1 sc) * ((R1 - R0) * cos phi) + (kx2 R0 phi - sp2 sc) * ((R1 - R0) * sin phi)
       + (Z0 - sp3 sc) * (Z1 - Z0))
  + ((R1 - R0) * cos phi * ((R1 - R0) * cos phi) + (R1 - R0) * sin phi * ((R1 - R0) * sin phi)
     + (Z1 - Z0) * (Z1 - Z0)).

Definition pxx (R0 R1 Z0 Z1 phi : R) : R :=
  (R1 - R0) * cos phi * ((R1 - R0) * cos phi) + (R1 - R0) * sin phi * ((R1 - R0) * sin phi)
  + (Z1 - Z0) * (Z1 - Z0).

Definition pX (c cd xx e y z : R) : R :=
  c * (y * y * y) * (z * (z * z) - 1 + 3 / 2 * (e * (y * y))) + cd * (y * y * y) * (z * (z * z) - 1)
  - 3 / 2 * (c * xx * (y * y * y * y * y)).

Lemma r2_point (sc : src) (R0 R1 Z0 Z1 phi y z e : R) :
  e = pe sc R0 R1 Z0 Z1 phi ->
  h3 sc (kx1 R0 phi) (kx2 R0 phi) Z0 = y * y * y ->
  h5 sc (kx1 R0 phi) (kx2 R0 phi) Z0 = y * y * y * y * y ->
  h3 sc (kx1 R1 phi) (kx2 R1 phi) Z1 = y * z * (y * z) * (y * z) ->
  let c1 := ck1 sc (kx1 R0 phi) (kx2 R0 phi) Z0 in
  let c2 := ck2 sc (kx1 R0 phi) (kx2 R0 phi) Z0 in
  let c3 := ck3 sc (kx1 R0 phi) (kx2 R0 phi) Z0 in
  let cd1 := sd2 sc * (Z1 - Z0) - sd3 sc * ((R1 - R0) * sin phi) in
  let cd2 := sd3 sc * ((R1 - R0) * cos phi) - sd1 sc * (Z1 - Z0) in
  let cd3 := sd1 sc * ((R1 - R0) * sin phi) - sd2 sc * ((R1 - R0) * cos phi) in
  let xx := pxx R0 R1 Z0 Z1 phi in
  fR sc R1 phi Z1 - fR sc R0 phi Z0 - (fR_R sc R0 phi Z0 * (R1 - R0) + fR_Z sc R0 phi Z0 * (Z1 - Z0))
    = pX c1 cd1 xx e y z * cos phi + pX c2 cd2 xx e y z * sin phi /\
  fP sc R1 phi Z1 - fP sc R0 phi Z0 - (fP_R sc R0 phi Z0 * (R1 - R0) + fP_Z sc R0 phi Z0 * (Z1 - Z0))
    = -1 * pX c1 cd1 xx e y z * sin phi + pX c2 cd2 xx e y z * cos phi /\
  fZ sc R1 phi Z1 - fZ sc R0 phi Z0 - (fZ_R sc R0 phi Z0 * (R1 - R0) + fZ_Z sc R0 phi Z0 * (Z1 - Z0))
    = pX c3 cd3 xx e y z.
Proof.
  intros He H3 H5 H3' c1 c2 c3 cd1 cd2 cd3 xx.
  unfold fR, fP, fZ, fR_R, fR_Z, fP_R, fP_Z, fZ_R, fZ_Z, JeR1, JeR2, JeR3,
    J11, J12, J13, J21, J22, J23, J31, J32, J33, bk1, bk2, bk3.
  rewrite H3, H5, H3'.
  subst e. unfold c1, c2, c3, cd1, cd2, cd3, xx, pX, pe, pxx, ck1, ck2, ck3, kx1, kx2.
  refine (conj _ (conj _ _)); field.
Qed.

(** The change of the Jacobian along a direction v between the two points:
    (d x v) y^3 (z^3 - 1) - 3 y^5 (c (r.v) (z^5 - 1) + (c (dx.v) + (d x dx) (r.v)
    + (d x dx) (dx.v)) z^5), in each Cartesian component. *)
Definition pJd (dv c cd re de y z : R) : R :=
  dv * (y * y * y) * (z * (z * z) - 1)
  - 3 * (y * y * y * y * y * (c * re * (z * (z * z) * (z * z) - 1)
                              + (c * de + cd * re + cd * de) * (z * (z * z) * (z * z)))).

Lemma dj_point (sc : src) (R0 R1 Z0 Z1 phi y z : R) :
  h3 sc (kx1 R0 phi) (kx2 R0 phi) Z0 = y * y * y ->
  h5 sc (kx1 R0 phi) (kx2 R0 phi) Z0 = y * y * y * y * y ->
  h3 sc (kx1 R1 phi) (kx2 R1 phi) Z1 = y * z * (y * z) * (y * z) ->
  h5 sc (kx1 R1 phi) (kx2 R1 phi) Z1 = y * z * (y * z) * (y * z) * (y * z) * (y * z) ->
  let c := cos phi in let s := sin phi in
  let c1 := ck1 sc (kx1 R0 phi) (kx2 R0 phi) Z0 in
  let c2 := ck2 sc (kx1 R0 phi) (kx2 R0 phi) Z0 in
  let c3 := ck3 sc (kx1 R0 phi) (kx2 R0 phi) Z0 in
  let cd1 := sd2 sc * (Z1 - Z0) - sd3 sc * ((R1 - R0) * s) in
  let cd2 := sd3 sc * ((R1 - R0) * c) - sd1 sc * (Z1 - Z0) in
  let cd3 := sd1 sc * ((R1 - R0) * s) - sd2 sc * ((R1 - R0) * c) in
  let reR := (kx1 R0 phi - sp1 sc) * c + (kx2 R0 phi - sp2 sc) * s in
  let deR := (R1 - R0) * c * c + (R1 - R0) * s * s in
  let reZ := Z0 - sp3 sc in
  let deZ := Z1 - Z0 in
  let JR1 := pJd (- sd3 sc * s) c1 cd1 reR deR y z in
  let JR2 := pJd (sd3 sc * c) c2 cd2 reR deR y z in
  let JR3 := pJd (sd1 sc * s - sd2 sc * c) c3 cd3 reR deR y z in
  let JZ1 := pJd (sd2 sc) c1 cd1 reZ deZ y z in
  let JZ2 := pJd (- sd1 sc) c2 cd2 reZ deZ y z in
  let JZ3 := pJd 0 c3 cd3 reZ deZ y z in
  fR_R sc R1 phi Z1 - fR_R sc R0 phi Z0 = JR1 * c + JR2 * s /\
  fR_Z sc R1 phi Z1 - fR_Z sc R0 phi Z0 = JZ1 * c + JZ2 * s /\
  fP_R sc R1 phi Z1 - fP_R sc R0 phi Z0 = -1 * JR1 * s + JR2 * c /\
  fP_Z sc R1 phi Z1 - fP_Z sc R0 phi Z0 = -1 * JZ1 * s + JZ2 * c /\
  fZ_R sc R1 phi Z1 - fZ_R sc R0 phi Z0 = JR3 /\
  fZ_Z sc R1 phi Z1 - fZ_Z sc R0 phi Z0 = JZ3.
Proof.
  intros H3 H5 H3' H5' c s c1 c2 c3 cd1 cd2 cd3 reR deR reZ deZ JR1 JR2 JR3 JZ1 JZ2 JZ3.
  unfold fR_R, fR_Z, fP_R, fP_Z, fZ_R, fZ_Z, JeR1, JeR2, JeR3,
    J11, J12, J13, J21, J22, J23, J31, J32, J33.
  rewrite H3, H5, H3', H5'.
  unfold JR1, JR2, JR3, JZ1, JZ2, JZ3, c1, c2, c3, cd1, cd2, cd3, reR, deR, reZ, deZ, pJd, ck1, ck2, ck3,
    kx1, kx2, c, s.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); ring.
Qed.

(** * The families between two tori *)

Section Taylor.

Variables (sc : src) (Y : fser) (K K' : vf) (w : R).
Hypothesis Hw : 0 < w.
Hypothesis FK : vfin w K.
Hypothesis FK' : vfin w K'.
Hypothesis Hq : isq_ok w (fq sc K) Y.
Hypothesis Hq' : isq_ok w (fq sc K') Y.
Hypothesis Hy : 0 < feval (fy sc Y K) 0 0.
Hypothesis Hy' : 0 < feval (fy sc Y K') 0 0.

Definition tdR : fser := fsub (vR K') (vR K).
Definition tdZ : fser := fsub (vZ K') (vZ K).
Definition tx1 : fser := fmul tdR cosf.
Definition tx2 : fser := fmul tdR sinf.
Definition tee : fser :=
  fadd (fscal 2 (fadd (fadd (fmul (fr1 sc K) tx1) (fmul (fr2 sc K) tx2)) (fmul (fr3 sc K) tdZ)))
       (fadd (fadd (fmul tx1 tx1) (fmul tx2 tx2)) (fmul tdZ tdZ)).
Definition teps : fser := fmul tee (fmul (fy sc Y K) (fy sc Y K)).
Definition ts2 : fser := fsub fone (fscal (/ 2) teps).
Definition tz : fser := fisqrt (fadd fone teps) ts2.

Definition tcd1 : fser := fsub (fscal (sd2 sc) tdZ) (fscal (sd3 sc) tx2).
Definition tcd2 : fser := fsub (fscal (sd3 sc) tx1) (fscal (sd1 sc) tdZ).
Definition tcd3 : fser := fsub (fscal (sd1 sc) tx2) (fscal (sd2 sc) tx1).
Definition txx : fser := fadd (fadd (fmul tx1 tx1) (fmul tx2 tx2)) (fmul tdZ tdZ).
Definition tz3 : fser := fmul tz (fmul tz tz).
Definition tA : fser := fadd (fsub tz3 fone) (fscal (3 / 2) teps).
Definition tB : fser := fsub tz3 fone.
Definition tX (c cd : fser) : fser :=
  fsub (fadd (fmul (fmul c (fh3 sc Y K)) tA) (fmul (fmul cd (fh3 sc Y K)) tB))
       (fscal (3 / 2) (fmul (fmul c txx) (fh5 sc Y K))).
Definition tXR : fser := fadd (fmul (tX (fc1 sc K) tcd1) cosf) (fmul (tX (fc2 sc K) tcd2) sinf).
Definition tXP : fser := fadd (fmul (fscal (-1) (tX (fc1 sc K) tcd1)) sinf) (fmul (tX (fc2 sc K) tcd2) cosf).
Definition tXZ : fser := tX (fc3 sc K) tcd3.

(** The change of the Jacobian, in the directions e_R and e_z. *)
Definition tz5 : fser := fmul tz3 (fmul tz tz).
Definition tB5 : fser := fsub tz5 fone.
Definition treR : fser := fadd (fmul (fr1 sc K) cosf) (fmul (fr2 sc K) sinf).
Definition tdeR : fser := fadd (fmul tx1 cosf) (fmul tx2 sinf).
Definition tdvR1 : fser := fscal (- sd3 sc) sinf.
Definition tdvR2 : fser := fscal (sd3 sc) cosf.
Definition tdvR3 : fser := fsub (fscal (sd1 sc) sinf) (fscal (sd2 sc) cosf).
Definition tdvZ1 : fser := fconst (sd2 sc).
Definition tdvZ2 : fser := fconst (- sd1 sc).
Definition tdvZ3 : fser := fconst 0.
Definition tJd (dv c cd re de : fser) : fser :=
  fsub (fmul (fmul dv (fh3 sc Y K)) tB)
       (fscal 3 (fmul (fh5 sc Y K) (fadd (fmul (fmul c re) tB5)
                                          (fmul (fadd (fadd (fmul c de) (fmul cd re)) (fmul cd de)) tz5)))).
Definition tJR1 : fser := tJd tdvR1 (fc1 sc K) tcd1 treR tdeR.
Definition tJR2 : fser := tJd tdvR2 (fc2 sc K) tcd2 treR tdeR.
Definition tJR3 : fser := tJd tdvR3 (fc3 sc K) tcd3 treR tdeR.
Definition tJZ1 : fser := tJd tdvZ1 (fc1 sc K) tcd1 (fr3 sc K) tdZ.
Definition tJZ2 : fser := tJd tdvZ2 (fc2 sc K) tcd2 (fr3 sc K) tdZ.
Definition tJZ3 : fser := tJd tdvZ3 (fc3 sc K) tcd3 (fr3 sc K) tdZ.
Definition tLRR : fser := fadd (fmul tJR1 cosf) (fmul tJR2 sinf).
Definition tLRZ : fser := fadd (fmul tJZ1 cosf) (fmul tJZ2 sinf).
Definition tLPR : fser := fadd (fmul (fscal (-1) tJR1) sinf) (fmul tJR2 cosf).
Definition tLPZ : fser := fadd (fmul (fscal (-1) tJZ1) sinf) (fmul tJZ2 cosf).
Definition tLZR : fser := tJR3.
Definition tLZZ : fser := tJZ3.
Definition dFRR : fser := fsub (FR_R sc Y K') (FR_R sc Y K).
Definition dFRZ : fser := fsub (FR_Z sc Y K') (FR_Z sc Y K).
Definition dFPR : fser := fsub (FP_R sc Y K') (FP_R sc Y K).
Definition dFPZ : fser := fsub (FP_Z sc Y K') (FP_Z sc Y K).
Definition dFZR : fser := fsub (FZ_R sc Y K') (FZ_R sc Y K).
Definition dFZZ : fser := fsub (FZ_Z sc Y K') (FZ_Z sc Y K).

Definition r2R : fser :=
  fsub (fsub (FR sc Y K') (FR sc Y K)) (fadd (fmul (FR_R sc Y K) tdR) (fmul (FR_Z sc Y K) tdZ)).
Definition r2P : fser :=
  fsub (fsub (FP sc Y K') (FP sc Y K)) (fadd (fmul (FP_R sc Y K) tdR) (fmul (FP_Z sc Y K) tdZ)).
Definition r2Z : fser :=
  fsub (fsub (FZ sc Y K') (FZ sc Y K)) (fadd (fmul (FZ_R sc Y K) tdR) (fmul (FZ_Z sc Y K) tdZ)).

Lemma Hw0 : 0 <= w. Proof. lra. Qed.

(** The functions of the families. *)
Let KR (t p : R) : R := feval (vR K) t p.
Let KZ (t p : R) : R := feval (vZ K) t p.
Let KR' (t p : R) : R := feval (vR K') t p.
Let KZ' (t p : R) : R := feval (vZ K') t p.

Lemma E_tdR : ev w tdR (fun t p => KR' t p - KR t p).
Proof. apply (ev_fsub _ Hw0); apply ev_self; [exact (proj1 FK') | exact (proj1 FK)]. Qed.
Lemma E_tdZ : ev w tdZ (fun t p => KZ' t p - KZ t p).
Proof. apply (ev_fsub _ Hw0); apply ev_self; [exact (proj2 FK') | exact (proj2 FK)]. Qed.
Lemma E_tx1 : ev w tx1 (fun t p => (KR' t p - KR t p) * cos p).
Proof. apply (ev_fmul _ Hw0); [exact E_tdR | exact (ev_cosf w Hw0)]. Qed.
Lemma E_tx2 : ev w tx2 (fun t p => (KR' t p - KR t p) * sin p).
Proof. apply (ev_fmul _ Hw0); [exact E_tdR | exact (ev_sinf w Hw0)]. Qed.

Let r1 (t p : R) : R := kx1 (KR t p) p - sp1 sc.
Let r2 (t p : R) : R := kx2 (KR t p) p - sp2 sc.
Let r3 (t p : R) : R := KZ t p - sp3 sc.
Let ev_ (t p : R) : R :=
  2 * (r1 t p * ((KR' t p - KR t p) * cos p) + r2 t p * ((KR' t p - KR t p) * sin p)
       + r3 t p * (KZ' t p - KZ t p))
  + ((KR' t p - KR t p) * cos p * ((KR' t p - KR t p) * cos p)
     + (KR' t p - KR t p) * sin p * ((KR' t p - KR t p) * sin p)
     + (KZ' t p - KZ t p) * (KZ' t p - KZ t p)).
Let yv (t p : R) : R := / sqrt (qk sc (kx1 (KR t p) p) (kx2 (KR t p) p) (KZ t p)).

Lemma E_tee : ev w tee ev_.
Proof.
  pose proof (E_r1 sc K w Hw FK) as A1. pose proof (E_r2 sc K w Hw FK) as A2.
  pose proof (E_r3 sc K w Hw FK) as A3.
  pose proof (ev_fmul _ Hw0 _ _ _ _ A1 E_tx1) as M1. pose proof (ev_fmul _ Hw0 _ _ _ _ A2 E_tx2) as M2.
  pose proof (ev_fmul _ Hw0 _ _ _ _ A3 E_tdZ) as M3.
  pose proof (ev_fscal _ Hw0 2 _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ M1 M2) M3)) as S1.
  pose proof (ev_fmul _ Hw0 _ _ _ _ E_tx1 E_tx1) as N1. pose proof (ev_fmul _ Hw0 _ _ _ _ E_tx2 E_tx2) as N2.
  pose proof (ev_fmul _ Hw0 _ _ _ _ E_tdZ E_tdZ) as N3.
  pose proof (ev_fadd _ Hw0 _ _ _ _ S1 (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ N1 N2) N3)) as T.
  unfold tee. eapply ev_ext; [| exact T]. intros t p. cbv beta. reflexivity.
Qed.

Lemma E_teps : ev w teps (fun t p => ev_ t p * (yv t p * yv t p)).
Proof.
  pose proof (E_y sc Y K w Hw FK Hq Hy) as Ey.
  pose proof (ev_fmul _ Hw0 _ _ _ _ E_tee (ev_fmul _ Hw0 _ _ _ _ Ey Ey)) as T.
  unfold teps. eapply ev_ext; [| exact T]. intros t p. cbv beta. reflexivity.
Qed.

Lemma E_one_eps : ev w (fadd fone teps) (fun t p => 1 + ev_ t p * (yv t p * yv t p)).
Proof.
  pose proof (ev_fadd _ Hw0 _ _ _ _ (ev_fconst w 1) E_teps) as T.
  eapply ev_ext; [| exact T]. intros t p. cbv beta. reflexivity.
Qed.

(** * The remainder as an explicit family *)

Section Remainder.

Hypothesis CK : vcanon K.
Hypothesis CK' : vcanon K'.
Hypothesis CY : is_canon Y.
Hypothesis Hzq : isq_ok w (fadd fone teps) ts2.
Hypothesis Hz0 : 0 < feval tz 0 0.

Let zv (t p : R) : R := / sqrt (1 + ev_ t p * (yv t p * yv t p)).

Lemma E_tz : ev w tz zv.
Proof. exact (isq_ev w (fadd fone teps) ts2 Hzq _ Hz0 E_one_eps). Qed.

Lemma E_tz3 : ev w tz3 (fun t p => zv t p * (zv t p * zv t p)).
Proof. exact (ev_fmul _ Hw0 _ _ _ _ E_tz (ev_fmul _ Hw0 _ _ _ _ E_tz E_tz)). Qed.

Lemma E_tA : ev w tA (fun t p => zv t p * (zv t p * zv t p) - 1 + 3 / 2 * (ev_ t p * (yv t p * yv t p))).
Proof.
  pose proof (ev_fadd _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ E_tz3 (ev_fconst w 1)) (ev_fscal _ Hw0 (3 / 2) _ _ E_teps)) as T.
  unfold tA. eapply ev_ext; [| exact T]. intros t p. cbv beta. reflexivity.
Qed.

Lemma E_tB : ev w tB (fun t p => zv t p * (zv t p * zv t p) - 1).
Proof.
  pose proof (ev_fsub _ Hw0 _ _ _ _ E_tz3 (ev_fconst w 1)) as T.
  unfold tB. eapply ev_ext; [| exact T]. intros t p. cbv beta. reflexivity.
Qed.

Lemma E_txx : ev w txx (fun t p => pxx (KR t p) (KR' t p) (KZ t p) (KZ' t p) p).
Proof.
  pose proof (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ E_tx1 E_tx1)
               (ev_fmul _ Hw0 _ _ _ _ E_tx2 E_tx2)) (ev_fmul _ Hw0 _ _ _ _ E_tdZ E_tdZ)) as T.
  unfold txx. eapply ev_ext; [| exact T]. intros t p. cbv beta. unfold pxx. reflexivity.
Qed.

Let h3v (t p : R) : R := h3 sc (kx1 (KR t p) p) (kx2 (KR t p) p) (KZ t p).
Let h5v (t p : R) : R := h5 sc (kx1 (KR t p) p) (kx2 (KR t p) p) (KZ t p).

Lemma E_tX (c cd : fser) (fc fcd : R -> R -> R) : ev w c fc -> ev w cd fcd ->
  ev w (tX c cd) (fun t p => pX (fc t p) (fcd t p) (pxx (KR t p) (KR' t p) (KZ t p) (KZ' t p) p)
                               (ev_ t p) (yv t p) (zv t p)
                             + (fc t p * (h3v t p - yv t p * yv t p * yv t p)
                                  * (zv t p * (zv t p * zv t p) - 1 + 3 / 2 * (ev_ t p * (yv t p * yv t p)))
                                + fcd t p * (h3v t p - yv t p * yv t p * yv t p) * (zv t p * (zv t p * zv t p) - 1)
                                - 3 / 2 * (fc t p * pxx (KR t p) (KR' t p) (KZ t p) (KZ' t p) p
                                           * (h5v t p - yv t p * yv t p * yv t p * yv t p * yv t p)))).
Proof.
  intros Ec Ecd.
  pose proof (E_h3 sc Y K w Hw FK Hq Hy) as Eh3. pose proof (E_h5 sc Y K w Hw FK Hq Hy) as Eh5.
  pose proof (ev_fsub _ Hw0 _ _ _ _
               (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Ec Eh3) E_tA)
                  (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Ecd Eh3) E_tB))
               (ev_fscal _ Hw0 (3 / 2) _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Ec E_txx) Eh5))) as T.
  unfold tX. eapply ev_ext; [| exact T]. intros t p. unfold pX, h3v, h5v, KR, KZ, KR', KZ'. cbv beta.
  field.
Qed.

Lemma E_tcd1 : ev w tcd1 (fun t p => sd2 sc * (KZ' t p - KZ t p) - sd3 sc * ((KR' t p - KR t p) * sin p)).
Proof. exact (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (sd2 sc) _ _ E_tdZ) (ev_fscal _ Hw0 (sd3 sc) _ _ E_tx2)). Qed.
Lemma E_tcd2 : ev w tcd2 (fun t p => sd3 sc * ((KR' t p - KR t p) * cos p) - sd1 sc * (KZ' t p - KZ t p)).
Proof. exact (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (sd3 sc) _ _ E_tx1) (ev_fscal _ Hw0 (sd1 sc) _ _ E_tdZ)). Qed.
Lemma E_tcd3 : ev w tcd3
  (fun t p => sd1 sc * ((KR' t p - KR t p) * sin p) - sd2 sc * ((KR' t p - KR t p) * cos p)).
Proof. exact (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (sd1 sc) _ _ E_tx2) (ev_fscal _ Hw0 (sd2 sc) _ _ E_tx1)). Qed.

(** The pointwise facts behind the split y' = y z. *)
Lemma split_facts (t p : R) :
  h3 sc (kx1 (feval (vR K) t p) p) (kx2 (feval (vR K) t p) p) (feval (vZ K) t p) = yv t p * yv t p * yv t p /\
  h5 sc (kx1 (feval (vR K) t p) p) (kx2 (feval (vR K) t p) p) (feval (vZ K) t p)
    = yv t p * yv t p * yv t p * yv t p * yv t p /\
  h3 sc (kx1 (feval (vR K') t p) p) (kx2 (feval (vR K') t p) p) (feval (vZ K') t p)
    = yv t p * zv t p * (yv t p * zv t p) * (yv t p * zv t p).
Proof.
  pose proof (q_pos sc Y K w Hw FK Hq t p) as Q0. pose proof (q_pos sc Y K' w Hw FK' Hq' t p) as Q1.
  cbv beta in Q0, Q1.
  set (q0 := qk sc (kx1 (feval (vR K) t p) p) (kx2 (feval (vR K) t p) p) (feval (vZ K) t p)) in *.
  set (q1 := qk sc (kx1 (feval (vR K') t p) p) (kx2 (feval (vR K') t p) p) (feval (vZ K') t p)) in *.
  assert (Eq : q1 = q0 + ev_ t p).
  { unfold q0, q1, ev_, r1, r2, r3, KR, KZ, KR', KZ', qk, kx1, kx2. ring. }
  assert (Q01 : 0 < q0 + ev_ t p) by (rewrite <- Eq; exact Q1).
  refine (conj _ (conj _ _)).
  - unfold h3, yv, KR, KZ. fold q0. apply h3_y, Q0.
  - unfold h5, yv, KR, KZ. fold q0. apply h5_y, Q0.
  - unfold h3. fold q1. rewrite (h3_y _ Q1), Eq, (isq_split q0 (ev_ t p) Q0 Q01).
    unfold zv, yv, KR, KZ. fold q0. reflexivity.
Qed.

Lemma r2_pointwise (t p : R) :
  feval r2R t p = feval tXR t p /\ feval r2P t p = feval tXP t p /\ feval r2Z t p = feval tXZ t p.
Proof.
  pose proof (E_FR sc Y K' w Hw FK' Hq' Hy') as A1. pose proof (E_FR sc Y K w Hw FK Hq Hy) as A0.
  pose proof (E_FR_R sc Y K w Hw FK Hq Hy) as AR. pose proof (E_FR_Z sc Y K w Hw FK Hq Hy) as AZ.
  pose proof (E_FP sc Y K' w Hw FK' Hq' Hy') as B1. pose proof (E_FP sc Y K w Hw FK Hq Hy) as B0.
  pose proof (E_FP_R sc Y K w Hw FK Hq Hy) as BR. pose proof (E_FP_Z sc Y K w Hw FK Hq Hy) as BZ.
  pose proof (E_FZ sc Y K' w Hw FK' Hq' Hy') as G1. pose proof (E_FZ sc Y K w Hw FK Hq Hy) as G0.
  pose proof (E_FZ_R sc Y K w Hw FK Hq Hy) as GR. pose proof (E_FZ_Z sc Y K w Hw FK Hq Hy) as GZ.
  pose proof (E_tX _ _ _ _ (E_c1 sc K w Hw FK) E_tcd1) as X1.
  pose proof (E_tX _ _ _ _ (E_c2 sc K w Hw FK) E_tcd2) as X2.
  pose proof (E_tX _ _ _ _ (E_c3 sc K w Hw FK) E_tcd3) as X3.
  pose proof (ev_cosf w Hw0) as Ec. pose proof (ev_sinf w Hw0) as Es.
  destruct (split_facts t p) as [H3 [H5 H3']].
  assert (He : ev_ t p = pe sc (feval (vR K) t p) (feval (vR K') t p) (feval (vZ K) t p) (feval (vZ K') t p) p)
    by reflexivity.
  destruct (r2_point sc (feval (vR K) t p) (feval (vR K') t p) (feval (vZ K) t p) (feval (vZ K') t p) p
              (yv t p) (zv t p) (ev_ t p) He H3 H5 H3') as [PR [PP PZ]].
  unfold r2R, r2P, r2Z, tXR, tXP, tXZ.
  rewrite (proj2 (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ A1 A0)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ AR E_tdR) (ev_fmul _ Hw0 _ _ _ _ AZ E_tdZ)))),
    (proj2 (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ B1 B0)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ BR E_tdR) (ev_fmul _ Hw0 _ _ _ _ BZ E_tdZ)))),
    (proj2 (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ G1 G0)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ GR E_tdR) (ev_fmul _ Hw0 _ _ _ _ GZ E_tdZ)))),
    (proj2 (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ X1 Ec) (ev_fmul _ Hw0 _ _ _ _ X2 Es))),
    (proj2 (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (-1) _ _ X1) Es)
             (ev_fmul _ Hw0 _ _ _ _ X2 Ec))),
    (proj2 X3).
  unfold h3v, h5v. unfold KR, KZ, KR', KZ'. cbv beta.
  rewrite PR, PP, PZ, H3, H5. unfold pX.
  refine (conj _ (conj _ _)); ring.
Qed.

Lemma split_h5 (t p : R) :
  h5 sc (kx1 (feval (vR K') t p) p) (kx2 (feval (vR K') t p) p) (feval (vZ K') t p)
    = yv t p * zv t p * (yv t p * zv t p) * (yv t p * zv t p) * (yv t p * zv t p) * (yv t p * zv t p).
Proof.
  pose proof (q_pos sc Y K w Hw FK Hq t p) as Q0. pose proof (q_pos sc Y K' w Hw FK' Hq' t p) as Q1.
  cbv beta in Q0, Q1.
  set (q0 := qk sc (kx1 (feval (vR K) t p) p) (kx2 (feval (vR K) t p) p) (feval (vZ K) t p)) in *.
  set (q1 := qk sc (kx1 (feval (vR K') t p) p) (kx2 (feval (vR K') t p) p) (feval (vZ K') t p)) in *.
  assert (Eq : q1 = q0 + ev_ t p).
  { unfold q0, q1, ev_, r1, r2, r3, KR, KZ, KR', KZ', qk, kx1, kx2. ring. }
  assert (Q01 : 0 < q0 + ev_ t p) by (rewrite <- Eq; exact Q1).
  unfold h5. fold q1. rewrite (h5_y _ Q1), Eq, (isq_split q0 (ev_ t p) Q0 Q01).
  unfold zv, yv, KR, KZ. fold q0. reflexivity.
Qed.

Lemma dj_pointwise (t p : R) :
  feval dFRR t p = feval tLRR t p /\ feval dFRZ t p = feval tLRZ t p /\
  feval dFPR t p = feval tLPR t p /\ feval dFPZ t p = feval tLPZ t p /\
  feval dFZR t p = feval tLZR t p /\ feval dFZZ t p = feval tLZZ t p.
Proof.
  pose proof (E_FR_R sc Y K' w Hw FK' Hq' Hy') as A1. pose proof (E_FR_R sc Y K w Hw FK Hq Hy) as A0.
  pose proof (E_FR_Z sc Y K' w Hw FK' Hq' Hy') as A1'. pose proof (E_FR_Z sc Y K w Hw FK Hq Hy) as A0'.
  pose proof (E_FP_R sc Y K' w Hw FK' Hq' Hy') as B1. pose proof (E_FP_R sc Y K w Hw FK Hq Hy) as B0.
  pose proof (E_FP_Z sc Y K' w Hw FK' Hq' Hy') as B1'. pose proof (E_FP_Z sc Y K w Hw FK Hq Hy) as B0'.
  pose proof (E_FZ_R sc Y K' w Hw FK' Hq' Hy') as G1. pose proof (E_FZ_R sc Y K w Hw FK Hq Hy) as G0.
  pose proof (E_FZ_Z sc Y K' w Hw FK' Hq' Hy') as G1'. pose proof (E_FZ_Z sc Y K w Hw FK Hq Hy) as G0'.
  pose proof (ev_cosf w Hw0) as Ec. pose proof (ev_sinf w Hw0) as Es.
  pose proof (E_h3 sc Y K w Hw FK Hq Hy) as Eh3. pose proof (E_h5 sc Y K w Hw FK Hq Hy) as Eh5.
  pose proof (ev_fmul _ Hw0 _ _ _ _ E_tz3 (ev_fmul _ Hw0 _ _ _ _ E_tz E_tz)) as Ez5.
  pose proof (ev_fsub _ Hw0 _ _ _ _ Ez5 (ev_fconst w 1)) as EB5.
  pose proof (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (E_r1 sc K w Hw FK) Ec)
                (ev_fmul _ Hw0 _ _ _ _ (E_r2 sc K w Hw FK) Es)) as ERe.
  pose proof (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ E_tx1 Ec) (ev_fmul _ Hw0 _ _ _ _ E_tx2 Es)) as EDe.
  pose proof (E_r3 sc K w Hw FK) as ER3.
  pose (EJ := fun dv c cd re de fdv fc fcd fre fde
                  (Hdv : ev w dv fdv) (Hc : ev w c fc) (Hcd : ev w cd fcd) (Hre : ev w re fre) (Hde : ev w de fde) =>
    ev_fsub _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Hdv Eh3) E_tB)
      (ev_fscal _ Hw0 3 _ _ (ev_fmul _ Hw0 _ _ _ _ Eh5
         (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Hc Hre) EB5)
            (ev_fmul _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Hc Hde)
                                                          (ev_fmul _ Hw0 _ _ _ _ Hcd Hre))
                                    (ev_fmul _ Hw0 _ _ _ _ Hcd Hde)) Ez5))))).
  pose proof (EJ _ _ _ _ _ _ _ _ _ _ (ev_fscal _ Hw0 (- sd3 sc) _ _ Es) (E_c1 sc K w Hw FK) E_tcd1 ERe EDe) as J1.
  pose proof (EJ _ _ _ _ _ _ _ _ _ _ (ev_fscal _ Hw0 (sd3 sc) _ _ Ec) (E_c2 sc K w Hw FK) E_tcd2 ERe EDe) as J2.
  pose proof (EJ _ _ _ _ _ _ _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (sd1 sc) _ _ Es)
                                         (ev_fscal _ Hw0 (sd2 sc) _ _ Ec))
                (E_c3 sc K w Hw FK) E_tcd3 ERe EDe) as J3.
  pose proof (EJ _ _ _ _ _ _ _ _ _ _ (ev_fconst w (sd2 sc)) (E_c1 sc K w Hw FK) E_tcd1 ER3 E_tdZ) as L1.
  pose proof (EJ _ _ _ _ _ _ _ _ _ _ (ev_fconst w (- sd1 sc)) (E_c2 sc K w Hw FK) E_tcd2 ER3 E_tdZ) as L2.
  pose proof (EJ _ _ _ _ _ _ _ _ _ _ (ev_fconst w 0) (E_c3 sc K w Hw FK) E_tcd3 ER3 E_tdZ) as L3.
  clear EJ.
  destruct (split_facts t p) as [H3 [H5 H3']]. pose proof (split_h5 t p) as H5'.
  destruct (dj_point sc (feval (vR K) t p) (feval (vR K') t p) (feval (vZ K) t p) (feval (vZ K') t p) p
              (yv t p) (zv t p) H3 H5 H3' H5') as [P1 [P2 [P3 [P4 [P5 P6]]]]].
  unfold dFRR, dFRZ, dFPR, dFPZ, dFZR, dFZZ, tLRR, tLRZ, tLPR, tLPZ, tLZR, tLZZ,
    tJR1, tJR2, tJR3, tJZ1, tJZ2, tJZ3, tdvR1, tdvR2, tdvR3, tdvZ1, tdvZ2, tdvZ3.
  rewrite (proj2 (ev_fsub _ Hw0 _ _ _ _ A1 A0)), (proj2 (ev_fsub _ Hw0 _ _ _ _ A1' A0')),
    (proj2 (ev_fsub _ Hw0 _ _ _ _ B1 B0)), (proj2 (ev_fsub _ Hw0 _ _ _ _ B1' B0')),
    (proj2 (ev_fsub _ Hw0 _ _ _ _ G1 G0)), (proj2 (ev_fsub _ Hw0 _ _ _ _ G1' G0')),
    (proj2 (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ J1 Ec) (ev_fmul _ Hw0 _ _ _ _ J2 Es))),
    (proj2 (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ L1 Ec) (ev_fmul _ Hw0 _ _ _ _ L2 Es))),
    (proj2 (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (-1) _ _ J1) Es)
             (ev_fmul _ Hw0 _ _ _ _ J2 Ec))),
    (proj2 (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (-1) _ _ L1) Es)
             (ev_fmul _ Hw0 _ _ _ _ L2 Ec))),
    (proj2 J3), (proj2 L3).
  unfold KR, KZ, KR', KZ'. cbv beta.
  rewrite P1, P2, P3, P4, P5, P6, H3, H5. unfold pJd.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); ring.
Qed.

End Remainder.

(** * Norms *)

Lemma feq_by_ev (u v : fser) (f g : R -> R -> R) :
  is_canon u -> is_canon v -> ev w u f -> ev w v g -> (forall t p, f t p = g t p) -> feq u v.
Proof.
  intros Cu Cv [Fu Eu] [Fv Ev] H.
  destruct (fin_mono w 0 u Hw0 Fu) as [Mu Bu]. destruct (fin_mono w 0 v Hw0 Fv) as [Mv Bv].
  apply (canon_feq u v Mu Mv Cu Cv Bu Bv). intros t p. rewrite Eu, Ev. apply H.
Qed.

Lemma wt01 : wt w 0 (-1) = wt w 0 1.
Proof. unfold wt, msize. change (IZR (-1)) with (- IZR 1). rewrite Rabs_Ropp. reflexivity. Qed.

Lemma nb_cosf : nbound w (wt w 0 1) cosf.
Proof.
  unfold cosf. replace (wt w 0 1) with ((Rabs (/ 2) + Rabs 0) * wt w 0 1 + (Rabs (/ 2) + Rabs 0) * wt w 0 (-1)).
  - apply nbound_fadd; apply nbound_fsingle.
  - rewrite wt01, Rabs_R0, Rabs_right by lra. field.
Qed.

Lemma nb_sinf : nbound w (wt w 0 1) sinf.
Proof.
  unfold sinf. replace (wt w 0 1) with ((Rabs 0 + Rabs (/ 2)) * wt w 0 1 + (Rabs 0 + Rabs (- / 2)) * wt w 0 (-1)).
  - apply nbound_fadd; apply nbound_fsingle.
  - rewrite wt01, Rabs_R0, Rabs_Ropp, Rabs_right by lra. field.
Qed.

Section Bounds.

Hypothesis CK : vcanon K.
Hypothesis CY : is_canon Y.
Variables (h hm rho1 rho2 rho3 yb : R).
Hypothesis Hh : 0 <= h.
Hypothesis Hhm : h <= hm.
Hypothesis HD : vbound w h (vsub K' K).
Hypothesis B1 : nbound w rho1 (fr1 sc K).
Hypothesis B2 : nbound w rho2 (fr2 sc K).
Hypothesis B3 : nbound w rho3 (fr3 sc K).
Hypothesis BY : nbound w yb (fy sc Y K).

(** A bound on the norms of cos p and sin p on the strip. *)
Variable cs : R.
Hypothesis Hcs : nbound w cs cosf /\ nbound w cs sinf.

Lemma nbc : nbound w cs cosf. Proof. exact (proj1 Hcs). Qed.
Lemma nbs : nbound w cs sinf. Proof. exact (proj2 Hcs). Qed.

Definition tE1 : R := 2 * (rho1 * cs + rho2 * cs + rho3) + hm * (2 * (cs * cs) + 1).
Definition tP1 : R := tE1 * (yb * yb).
Definition tS2 : R := 1 + hm * tP1 / 2.
Definition tT1 : R := 3 / 4 * (tP1 * tP1) + / 4 * (hm * (tP1 * (tP1 * tP1))).

Lemma cs_pos : 0 <= cs. Proof. exact (nbound_nonneg _ _ _ nbc). Qed.
Lemma rho1_nn : 0 <= rho1. Proof. exact (nbound_nonneg _ _ _ B1). Qed.
Lemma rho2_nn : 0 <= rho2. Proof. exact (nbound_nonneg _ _ _ B2). Qed.
Lemma rho3_nn : 0 <= rho3. Proof. exact (nbound_nonneg _ _ _ B3). Qed.
Lemma yb_nn : 0 <= yb. Proof. exact (nbound_nonneg _ _ _ BY). Qed.

Lemma tE1_nn : 0 <= tE1.
Proof.
  unfold tE1. pose proof cs_pos. pose proof rho1_nn. pose proof rho2_nn. pose proof rho3_nn.
  assert (0 <= hm) by lra. apply Rplus_le_le_0_compat; [| apply Rmult_le_pos; nra]. nra.
Qed.

Lemma tP1_nn : 0 <= tP1. Proof. unfold tP1. pose proof tE1_nn. pose proof yb_nn. nra. Qed.

Lemma nb_tdR : nbound w h tdR. Proof. exact (proj1 HD). Qed.
Lemma nb_tdZ : nbound w h tdZ. Proof. exact (proj2 HD). Qed.
Lemma nb_tx1 : nbound w (h * cs) tx1. Proof. exact (nbound_fmul w h cs tdR cosf Hw0 nb_tdR nbc). Qed.
Lemma nb_tx2 : nbound w (h * cs) tx2. Proof. exact (nbound_fmul w h cs tdR sinf Hw0 nb_tdR nbs). Qed.

Lemma nb_tee : nbound w (h * tE1) tee.
Proof.
  pose proof (nbound_fmul w _ _ _ _ Hw0 B1 nb_tx1) as M1. pose proof (nbound_fmul w _ _ _ _ Hw0 B2 nb_tx2) as M2.
  pose proof (nbound_fmul w _ _ _ _ Hw0 B3 nb_tdZ) as M3.
  pose proof (nbound_fscal w _ 2 _ (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ M1 M2) M3)) as S.
  pose proof (nbound_fmul w _ _ _ _ Hw0 nb_tx1 nb_tx1) as N1. pose proof (nbound_fmul w _ _ _ _ Hw0 nb_tx2 nb_tx2) as N2.
  pose proof (nbound_fmul w _ _ _ _ Hw0 nb_tdZ nb_tdZ) as N3.
  pose proof (nbound_fadd w _ _ _ _ S (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ N1 N2) N3)) as T.
  unfold tee. refine (nbound_le w _ _ _ _ T).
  rewrite Rabs_right by lra. unfold tE1. pose proof cs_pos. pose proof rho1_nn. pose proof rho2_nn.
  pose proof rho3_nn. assert (Hhh : h * h <= h * hm) by (apply Rmult_le_compat_l; assumption).
  assert (Hcc : 0 <= cs * cs) by nra. nra.
Qed.

Lemma nb_teps : nbound w (h * tP1) teps.
Proof.
  pose proof (nbound_fmul w _ _ _ _ Hw0 nb_tee (nbound_fmul w _ _ _ _ Hw0 BY BY)) as T.
  unfold teps, tP1. refine (nbound_le w _ _ _ _ T). right. ring.
Qed.

Lemma nb_ts2 : nbound w tS2 ts2.
Proof.
  pose proof (nbound_fsub w _ _ _ _ (nbound_fone w) (nbound_fscal w _ (/ 2) _ nb_teps)) as T.
  unfold ts2. refine (nbound_le w _ _ _ _ T).
  rewrite Rabs_right by lra. unfold tS2. pose proof tP1_nn.
  assert (h * tP1 <= hm * tP1) by (apply Rmult_le_compat_r; assumption). lra.
Qed.

Lemma tS2_ge1 : 1 <= tS2.
Proof. unfold tS2. pose proof tP1_nn. assert (0 <= hm * tP1) by (apply Rmult_le_pos; lra). lra. Qed.

(** Canonical form of the families. *)
Hypothesis CK' : vcanon K'.

Lemma C_teps : is_canon teps.
Proof. destruct CK as [CKR CKZ]. destruct CK' as [CKR' CKZ']. unfold teps, tee, tx1, tx2, tdR, tdZ. canon_tac. Qed.
Lemma C_ts2 : is_canon ts2.
Proof. unfold ts2. apply fsub_canon; [apply fone_canon | apply fscal_canon, C_teps]. Qed.
Lemma C_tz : is_canon tz.
Proof. unfold tz. apply fisqrt_canon; [apply fadd_canon; [apply fone_canon | apply C_teps] | apply C_ts2]. Qed.

(** The defect of 1 - eps/2 as the inverse square root of 1 + eps is
    3/4 eps^2 - eps^3/4. *)
Definition tdef : fser := fsub fone (fmul (fadd fone teps) (fmul ts2 ts2)).
Definition tdef' : fser :=
  fsub (fscal (3 / 4) (fmul teps teps)) (fscal (/ 4) (fmul teps (fmul teps teps))).

Lemma F_teps : fin w teps. Proof. exists (h * tP1). exact nb_teps. Qed.

Lemma tdef_feq : feq tdef tdef'.
Proof.
  pose proof (ev_self w teps F_teps) as E. pose proof (ev_fconst w 1) as E1.
  eapply (feq_by_ev tdef tdef').
  - unfold tdef. apply fsub_canon; [apply fone_canon |].
    apply fmul_canon; [apply fadd_canon; [apply fone_canon | apply C_teps] | apply fmul_canon; apply C_ts2].
  - unfold tdef'. apply fsub_canon; apply fscal_canon; repeat (first [apply C_teps | apply fmul_canon]).
  - exact (ev_fsub _ Hw0 _ _ _ _ E1 (ev_fmul _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ E1 E)
             (ev_fmul _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ E1 (ev_fscal _ Hw0 (/ 2) _ _ E))
                (ev_fsub _ Hw0 _ _ _ _ E1 (ev_fscal _ Hw0 (/ 2) _ _ E))))).
  - exact (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (3 / 4) _ _ (ev_fmul _ Hw0 _ _ _ _ E E))
             (ev_fscal _ Hw0 (/ 4) _ _ (ev_fmul _ Hw0 _ _ _ _ E (ev_fmul _ Hw0 _ _ _ _ E E)))).
  - intros t p. cbv beta. field.
Qed.

Lemma nb_tdef : nbound w (h * h * tT1) tdef.
Proof.
  apply (nbound_feq w _ tdef' tdef (feq_sym _ _ tdef_feq)).
  pose proof (nbound_fsub w _ _ _ _ (nbound_fscal w _ (3 / 4) _ (nbound_fmul w _ _ _ _ Hw0 nb_teps nb_teps))
                (nbound_fscal w _ (/ 4) _ (nbound_fmul w _ _ _ _ Hw0 nb_teps
                   (nbound_fmul w _ _ _ _ Hw0 nb_teps nb_teps)))) as T.
  unfold tdef'. refine (nbound_le w _ _ _ _ T).
  rewrite !Rabs_right by lra. unfold tT1. pose proof tP1_nn.
  assert (A : h * tP1 * (h * tP1 * (h * tP1)) <= h * h * (hm * (tP1 * (tP1 * tP1)))).
  { replace (h * tP1 * (h * tP1 * (h * tP1))) with (h * h * (h * (tP1 * (tP1 * tP1)))) by ring.
    apply Rmult_le_compat_l; [nra |]. apply Rmult_le_compat_r; [nra | exact Hhm]. }
  nra.
Qed.

Hypothesis Hsm1 : hm * hm * tT1 < 1.

Lemma tT1_nn : 0 <= tT1.
Proof.
  unfold tT1. pose proof tP1_nn. assert (0 <= hm) by lra.
  assert (A : 0 <= tP1 * tP1) by nra. assert (B : 0 <= tP1 * (tP1 * tP1)) by (apply Rmult_le_pos; lra).
  apply Rplus_le_le_0_compat; apply Rmult_le_pos; try lra. apply Rmult_le_pos; lra.
Qed.

Lemma hh_le : h * h <= hm * hm. Proof. nra. Qed.

Lemma th_lt1 : 0 <= h * h * tT1 < 1.
Proof. pose proof tT1_nn. pose proof hh_le. split; [nra |]. nra. Qed.

Lemma Hzq : isq_ok w (fadd fone teps) ts2.
Proof.
  split; [exact Hw |]. exists (1 + h * tP1), tS2, (h * h * tT1).
  refine (conj (nbound_fadd w _ _ _ _ (nbound_fone w) nb_teps) (conj nb_ts2 (conj th_lt1 nb_tdef))).
Qed.

Definition tRB : R := 2 * tS2 * tT1 / ((1 - hm * hm * tT1) * (1 - hm * hm * tT1)).

Lemma inv_eps0_le (Y0 q Q : R) :
  0 <= Y0 -> 0 <= q <= Q -> Q < 1 -> inv_eps Y0 q 0 <= 2 * Y0 * q / ((1 - Q) * (1 - Q)).
Proof.
  intros HY [Hq0 HqQ] HQ. unfold inv_eps, inv_T. simpl pow. rewrite Rmult_1_r.
  assert (A : 0 < 1 - Q) by lra. assert (B : 0 < 1 - q) by lra.
  replace (2 * (Y0 / (1 - q) * (q / (1 - q)))) with (2 * Y0 * q * / ((1 - q) * (1 - q))) by (field; lra).
  unfold Rdiv. apply Rmult_le_compat_l; [nra |].
  apply Rinv_le_contravar; [nra |]. apply Rmult_le_compat; lra.
Qed.

Definition trho : fser := fsub ts2 tz.

Lemma nb_trho : nbound w (h * h * tRB) trho.
Proof.
  pose proof (nbound_fisqrt_sub w Hw0 (fadd fone teps) ts2 tS2 (h * h * tT1) nb_ts2 th_lt1 nb_tdef) as T.
  unfold trho, tz. refine (nbound_le w _ _ _ _ T).
  pose proof tT1_nn. pose proof tS2_ge1.
  eapply Rle_trans; [apply (inv_eps0_le tS2 (h * h * tT1) (hm * hm * tT1)) |].
  - lra.
  - split; [nra |]. apply Rmult_le_compat_r; [lra | exact hh_le].
  - exact Hsm1.
  - unfold tRB. apply Req_le. field. nra.
Qed.

Lemma tRB_nn : 0 <= tRB.
Proof.
  unfold tRB. pose proof tT1_nn. pose proof tS2_ge1. apply Rmult_le_pos; [nra |].
  apply Rlt_le, Rinv_0_lt_compat. nra.
Qed.

Hypothesis Hsm2 : hm * tP1 / 2 + hm * hm * tRB < 1.

Lemma F_tz : fin w tz. Proof. exact (isq_fin w _ _ Hzq). Qed.

Lemma Hz0 : 0 < feval tz 0 0.
Proof.
  pose proof (feval_bound trho _ 0 0 (nbound_mono w 0 _ _ Hw0 nb_trho)) as A.
  pose proof (feval_bound teps _ 0 0 (nbound_mono w 0 _ _ Hw0 nb_teps)) as B.
  assert (F0 : fin 0 fone) by exact (fin_fconst 0 1).
  assert (Fe : fin 0 teps) by exact (fin_mono w 0 _ Hw0 F_teps).
  assert (Fs : fin 0 (fscal (/ 2) teps)) by (apply fin_fscal; exact Fe).
  assert (Fs2 : fin 0 ts2) by (apply fin_fsub; assumption).
  assert (Fz : fin 0 tz) by exact (fin_mono w 0 _ Hw0 F_tz).
  unfold trho in A. rewrite (feval_fsub' 0 0 _ _ Fs2 Fz) in A.
  unfold ts2 in A. rewrite (feval_fsub' 0 0 _ _ F0 Fs), (feval_fscal' 0 0 _ _ Fe), feval_fone in A.
  apply Rabs_le_between in A. apply Rabs_le_between in B.
  pose proof tP1_nn. pose proof tRB_nn. pose proof hh_le.
  assert (h * tP1 <= hm * tP1) by (apply Rmult_le_compat_r; lra).
  assert (h * h * tRB <= hm * hm * tRB) by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

Lemma C_trho : is_canon trho. Proof. unfold trho. apply fsub_canon; [apply C_ts2 | apply C_tz]. Qed.

(** z^3 - 1 + 3/2 eps, with z = s2 - rho and s2 = 1 - eps/2. *)
Definition tA' : fser :=
  fadd (fsub (fscal (3 / 4) (fmul teps teps)) (fscal (/ 8) (fmul teps (fmul teps teps))))
       (fadd (fscal (-3) (fmul (fmul ts2 ts2) trho))
             (fsub (fscal 3 (fmul ts2 (fmul trho trho))) (fmul trho (fmul trho trho)))).

Lemma tA_feq : feq tA tA'.
Proof.
  pose proof (ev_self w teps F_teps) as E. pose proof (ev_self w tz F_tz) as Z.
  pose proof (ev_fconst w 1) as E1.
  pose proof (ev_fsub _ Hw0 _ _ _ _ E1 (ev_fscal _ Hw0 (/ 2) _ _ E)) as S.
  pose proof (ev_fsub _ Hw0 _ _ _ _ S Z) as Rh.
  eapply (feq_by_ev tA tA').
  - unfold tA, tz3. apply fadd_canon; [apply fsub_canon; [| apply fone_canon] | apply fscal_canon, C_teps].
    apply fmul_canon; [apply C_tz | apply fmul_canon; apply C_tz].
  - unfold tA'. pose proof C_teps. pose proof C_ts2. pose proof C_trho.
    repeat (first [assumption | apply fadd_canon | apply fsub_canon | apply fscal_canon | apply fmul_canon]).
  - exact (ev_fadd _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Z (ev_fmul _ Hw0 _ _ _ _ Z Z)) E1)
             (ev_fscal _ Hw0 (3 / 2) _ _ E)).
  - exact (ev_fadd _ Hw0 _ _ _ _
             (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (3 / 4) _ _ (ev_fmul _ Hw0 _ _ _ _ E E))
                (ev_fscal _ Hw0 (/ 8) _ _ (ev_fmul _ Hw0 _ _ _ _ E (ev_fmul _ Hw0 _ _ _ _ E E))))
             (ev_fadd _ Hw0 _ _ _ _ (ev_fscal _ Hw0 (-3) _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ S S) Rh))
                (ev_fsub _ Hw0 _ _ _ _ (ev_fscal _ Hw0 3 _ _ (ev_fmul _ Hw0 _ _ _ _ S (ev_fmul _ Hw0 _ _ _ _ Rh Rh)))
                   (ev_fmul _ Hw0 _ _ _ _ Rh (ev_fmul _ Hw0 _ _ _ _ Rh Rh))))).
  - intros t p. cbv beta. field.
Qed.

Definition tA1 : R :=
  3 / 4 * (tP1 * tP1) + / 8 * (hm * (tP1 * (tP1 * tP1))) + 3 * (tS2 * tS2 * tRB)
  + 3 * (tS2 * (hm * hm * (tRB * tRB))) + hm * hm * (hm * hm) * (tRB * (tRB * tRB)).

Lemma tA1_nn : 0 <= tA1.
Proof.
  unfold tA1. pose proof tP1_nn. pose proof tS2_ge1. pose proof tRB_nn. assert (0 <= hm) by lra.
  assert (0 <= / 8) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  assert (0 <= 3 / 4) by lra.
  assert (0 <= tP1 * tP1) by nra. assert (0 <= tP1 * (tP1 * tP1)) by (apply Rmult_le_pos; nra).
  assert (0 <= tRB * tRB) by nra. assert (0 <= tRB * (tRB * tRB)) by (apply Rmult_le_pos; nra).
  assert (0 <= hm * hm) by nra.
  assert (0 <= 3 / 4 * (tP1 * tP1)) by (apply Rmult_le_pos; lra).
  assert (0 <= / 8 * (hm * (tP1 * (tP1 * tP1)))) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
  assert (0 <= tS2 * tS2 * tRB) by (apply Rmult_le_pos; nra).
  assert (0 <= tS2 * (hm * hm * (tRB * tRB))) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
  assert (0 <= hm * hm * (hm * hm) * (tRB * (tRB * tRB))) by (apply Rmult_le_pos; [nra | lra]).
  lra.
Qed.

Lemma nb_tA : nbound w (h * h * tA1) tA.
Proof.
  apply (nbound_feq w _ tA' tA (feq_sym _ _ tA_feq)).
  pose proof nb_ts2 as S2. pose proof nb_trho as Rh.
  pose proof (nbound_fadd w _ _ _ _
    (nbound_fsub w _ _ _ _ (nbound_fscal w _ (3 / 4) _ (nbound_fmul w _ _ _ _ Hw0 nb_teps nb_teps))
       (nbound_fscal w _ (/ 8) _ (nbound_fmul w _ _ _ _ Hw0 nb_teps (nbound_fmul w _ _ _ _ Hw0 nb_teps nb_teps))))
    (nbound_fadd w _ _ _ _ (nbound_fscal w _ (-3) _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 S2 S2) Rh))
       (nbound_fsub w _ _ _ _ (nbound_fscal w _ 3 _ (nbound_fmul w _ _ _ _ Hw0 S2 (nbound_fmul w _ _ _ _ Hw0 Rh Rh)))
          (nbound_fmul w _ _ _ _ Hw0 Rh (nbound_fmul w _ _ _ _ Hw0 Rh Rh))))) as T.
  unfold tA'. refine (nbound_le w _ _ _ _ T).
  rewrite (Rabs_right (3 / 4)), (Rabs_right (/ 8)), (Rabs_left (-3)), (Rabs_right 3) by lra.
  unfold tA1. pose proof tP1_nn. pose proof tS2_ge1. pose proof tRB_nn.
  assert (Hm0 : 0 <= hm) by lra.
  assert (P3 : 0 <= tP1 * (tP1 * tP1)) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
  assert (R2 : 0 <= tRB * tRB) by nra.
  assert (R3 : 0 <= tRB * (tRB * tRB)) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
  assert (E1 : h * tP1 * (h * tP1 * (h * tP1)) <= h * h * (hm * (tP1 * (tP1 * tP1)))).
  { replace (h * tP1 * (h * tP1 * (h * tP1))) with (h * h * (h * (tP1 * (tP1 * tP1)))) by ring.
    apply Rmult_le_compat_l; [nra |]. apply Rmult_le_compat_r; lra. }
  assert (E2 : tS2 * (h * h * tRB * (h * h * tRB)) <= h * h * (tS2 * (hm * hm * (tRB * tRB)))).
  { replace (tS2 * (h * h * tRB * (h * h * tRB))) with (h * h * (tS2 * (h * h * (tRB * tRB)))) by ring.
    apply Rmult_le_compat_l; [nra |]. apply Rmult_le_compat_l; [lra |].
    apply Rmult_le_compat_r; [lra | exact hh_le]. }
  assert (E3 : h * h * tRB * (h * h * tRB * (h * h * tRB)) <= h * h * (hm * hm * (hm * hm) * (tRB * (tRB * tRB)))).
  { replace (h * h * tRB * (h * h * tRB * (h * h * tRB))) with (h * h * (h * h * (h * h) * (tRB * (tRB * tRB))))
      by ring.
    apply Rmult_le_compat_l; [nra |]. apply Rmult_le_compat_r; [lra |].
    pose proof hh_le. apply Rmult_le_compat; nra. }
  apply Rle_trans with (h * h * (3 / 4 * (tP1 * tP1)) + / 8 * (h * tP1 * (h * tP1 * (h * tP1)))
                        + 3 * (h * h * (tS2 * tS2 * tRB)) + 3 * (tS2 * (h * h * tRB * (h * h * tRB)))
                        + h * h * tRB * (h * h * tRB * (h * h * tRB))).
  { right. ring. }
  replace (h * h * (3 / 4 * (tP1 * tP1) + / 8 * (hm * (tP1 * (tP1 * tP1))) + 3 * (tS2 * tS2 * tRB)
                    + 3 * (tS2 * (hm * hm * (tRB * tRB))) + hm * hm * (hm * hm) * (tRB * (tRB * tRB))))
    with (h * h * (3 / 4 * (tP1 * tP1)) + / 8 * (h * h * (hm * (tP1 * (tP1 * tP1))))
          + 3 * (h * h * (tS2 * tS2 * tRB)) + 3 * (h * h * (tS2 * (hm * hm * (tRB * tRB))))
          + h * h * (hm * hm * (hm * hm) * (tRB * (tRB * tRB)))) by ring.
  assert (Q8 : 0 <= / 8) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  pose proof (Rmult_le_compat_l _ _ _ Q8 E1). lra.
Qed.

Definition tB1 : R := 3 / 2 * tP1 + hm * tA1.

Lemma tB_feq : feq tB (fsub tA (fscal (3 / 2) teps)).
Proof.
  pose proof (ev_self w teps F_teps) as E. pose proof (ev_self w tz F_tz) as Z.
  pose proof (ev_fconst w 1) as E1.
  pose proof (ev_fmul _ Hw0 _ _ _ _ Z (ev_fmul _ Hw0 _ _ _ _ Z Z)) as Z3.
  eapply (feq_by_ev tB (fsub tA (fscal (3 / 2) teps))).
  - unfold tB, tz3. apply fsub_canon; [| apply fone_canon]. apply fmul_canon; [apply C_tz | apply fmul_canon; apply C_tz].
  - unfold tA, tz3. apply fsub_canon; [| apply fscal_canon, C_teps].
    apply fadd_canon; [apply fsub_canon; [| apply fone_canon] | apply fscal_canon, C_teps].
    apply fmul_canon; [apply C_tz | apply fmul_canon; apply C_tz].
  - exact (ev_fsub _ Hw0 _ _ _ _ Z3 E1).
  - exact (ev_fsub _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ Z3 E1) (ev_fscal _ Hw0 (3 / 2) _ _ E))
             (ev_fscal _ Hw0 (3 / 2) _ _ E)).
  - intros t p. cbv beta. ring.
Qed.

Lemma nb_tB : nbound w (h * tB1) tB.
Proof.
  apply (nbound_feq w _ _ tB (feq_sym _ _ tB_feq)).
  pose proof (nbound_fsub w _ _ _ _ nb_tA (nbound_fscal w _ (3 / 2) _ nb_teps)) as T.
  refine (nbound_le w _ _ _ _ T). rewrite Rabs_right by lra. unfold tB1.
  pose proof tA1_nn. pose proof tP1_nn.
  assert (h * h * tA1 <= h * (hm * tA1)).
  { rewrite Rmult_assoc. apply Rmult_le_compat_l; [lra |]. apply Rmult_le_compat_r; lra. }
  nra.
Qed.

(** The factors of the remainder. *)
Lemma nb_fh3 : nbound w (yb * (yb * yb)) (fh3 sc Y K).
Proof. exact (nbound_fmul w _ _ _ _ Hw0 BY (nbound_fmul w _ _ _ _ Hw0 BY BY)). Qed.

Lemma nb_fh5 : nbound w (yb * (yb * yb) * (yb * yb)) (fh5 sc Y K).
Proof. exact (nbound_fmul w _ _ _ _ Hw0 nb_fh3 (nbound_fmul w _ _ _ _ Hw0 BY BY)). Qed.

Lemma nb_txx : nbound w (h * h * (2 * (cs * cs) + 1)) txx.
Proof.
  pose proof (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 nb_tx1 nb_tx1)
                (nbound_fmul w _ _ _ _ Hw0 nb_tx2 nb_tx2)) (nbound_fmul w _ _ _ _ Hw0 nb_tdZ nb_tdZ)) as T.
  unfold txx. refine (nbound_le w _ _ _ _ T). right. ring.
Qed.

Lemma nb_tX (c cd : fser) (Cc Dc : R) : nbound w Cc c -> nbound w (h * Dc) cd ->
  nbound w (h * h * (Cc * (yb * (yb * yb)) * tA1 + Dc * (yb * (yb * yb)) * tB1
                     + 3 / 2 * (Cc * (2 * (cs * cs) + 1) * (yb * (yb * yb) * (yb * yb))))) (tX c cd).
Proof.
  intros Bc Bcd.
  pose proof (nbound_fsub w _ _ _ _
    (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Bc nb_fh3) nb_tA)
       (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Bcd nb_fh3) nb_tB))
    (nbound_fscal w _ (3 / 2) _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Bc nb_txx) nb_fh5))) as T.
  unfold tX. refine (nbound_le w _ _ _ _ T). rewrite Rabs_right by lra. right. ring.
Qed.

Definition tC1 : R := Rabs (sd2 sc) * rho3 + Rabs (sd3 sc) * rho2.
Definition tC2 : R := Rabs (sd3 sc) * rho1 + Rabs (sd1 sc) * rho3.
Definition tC3 : R := Rabs (sd1 sc) * rho2 + Rabs (sd2 sc) * rho1.
Definition tD1 : R := Rabs (sd2 sc) + Rabs (sd3 sc) * cs.
Definition tD2 : R := Rabs (sd3 sc) * cs + Rabs (sd1 sc).
Definition tD3 : R := Rabs (sd1 sc) * cs + Rabs (sd2 sc) * cs.

Lemma nb_fc1 : nbound w tC1 (fc1 sc K).
Proof. exact (nbound_fsub w _ _ _ _ (nbound_fscal w _ (sd2 sc) _ B3) (nbound_fscal w _ (sd3 sc) _ B2)). Qed.
Lemma nb_fc2 : nbound w tC2 (fc2 sc K).
Proof. exact (nbound_fsub w _ _ _ _ (nbound_fscal w _ (sd3 sc) _ B1) (nbound_fscal w _ (sd1 sc) _ B3)). Qed.
Lemma nb_fc3 : nbound w tC3 (fc3 sc K).
Proof. exact (nbound_fsub w _ _ _ _ (nbound_fscal w _ (sd1 sc) _ B2) (nbound_fscal w _ (sd2 sc) _ B1)). Qed.

Lemma nb_tcd1 : nbound w (h * tD1) tcd1.
Proof.
  pose proof (nbound_fsub w _ _ _ _ (nbound_fscal w _ (sd2 sc) _ nb_tdZ) (nbound_fscal w _ (sd3 sc) _ nb_tx2)) as T.
  unfold tcd1. refine (nbound_le w _ _ _ _ T). right. unfold tD1. ring.
Qed.
Lemma nb_tcd2 : nbound w (h * tD2) tcd2.
Proof.
  pose proof (nbound_fsub w _ _ _ _ (nbound_fscal w _ (sd3 sc) _ nb_tx1) (nbound_fscal w _ (sd1 sc) _ nb_tdZ)) as T.
  unfold tcd2. refine (nbound_le w _ _ _ _ T). right. unfold tD2. ring.
Qed.
Lemma nb_tcd3 : nbound w (h * tD3) tcd3.
Proof.
  pose proof (nbound_fsub w _ _ _ _ (nbound_fscal w _ (sd1 sc) _ nb_tx2) (nbound_fscal w _ (sd2 sc) _ nb_tx1)) as T.
  unfold tcd3. refine (nbound_le w _ _ _ _ T). right. unfold tD3. ring.
Qed.

Definition tXb (Cc Dc : R) : R :=
  Cc * (yb * (yb * yb)) * tA1 + Dc * (yb * (yb * yb)) * tB1
  + 3 / 2 * (Cc * (2 * (cs * cs) + 1) * (yb * (yb * yb) * (yb * yb))).

(** The second-order remainders of the three cylindrical components. *)
Definition tRRb : R := (tXb tC1 tD1 + tXb tC2 tD2) * cs.
Definition tRZb : R := tXb tC3 tD3.

Lemma nb_tXR : nbound w (h * h * tRRb) tXR.
Proof.
  pose proof (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nb_tX _ _ _ _ nb_fc1 nb_tcd1) nbc)
                (nbound_fmul w _ _ _ _ Hw0 (nb_tX _ _ _ _ nb_fc2 nb_tcd2) nbs)) as T.
  unfold tXR. refine (nbound_le w _ _ _ _ T). right. unfold tRRb, tXb. ring.
Qed.

Lemma nb_tXP : nbound w (h * h * tRRb) tXP.
Proof.
  pose proof (nbound_fadd w _ _ _ _
                (nbound_fmul w _ _ _ _ Hw0 (nbound_fscal w _ (-1) _ (nb_tX _ _ _ _ nb_fc1 nb_tcd1)) nbs)
                (nbound_fmul w _ _ _ _ Hw0 (nb_tX _ _ _ _ nb_fc2 nb_tcd2) nbc)) as T.
  unfold tXP. refine (nbound_le w _ _ _ _ T). rewrite Rabs_left by lra. right. unfold tRRb, tXb. ring.
Qed.

Lemma nb_tXZ : nbound w (h * h * tRZb) tXZ.
Proof. exact (nb_tX _ _ _ _ nb_fc3 nb_tcd3). Qed.

(** Canonical form of the remainder families. *)
Lemma C_tdR : is_canon tdR.
Proof. destruct CK as [A _]. destruct CK' as [B _]. unfold tdR. apply fsub_canon; assumption. Qed.
Lemma C_tdZ : is_canon tdZ.
Proof. destruct CK as [_ A]. destruct CK' as [_ B]. unfold tdZ. apply fsub_canon; assumption. Qed.
Lemma C_tx1 : is_canon tx1. Proof. unfold tx1. apply fmul_canon; [apply C_tdR | apply cosf_canon]. Qed.
Lemma C_tx2 : is_canon tx2. Proof. unfold tx2. apply fmul_canon; [apply C_tdR | apply sinf_canon]. Qed.
Lemma C_fy : is_canon (fy sc Y K).
Proof. destruct CK as [CKR CKZ]. unfold fy, fq, fr1, fr2, fr3, fx1, fx2. canon_tac. Qed.
Lemma C_fh3 : is_canon (fh3 sc Y K).
Proof. unfold fh3. pose proof C_fy. apply fmul_canon; [assumption | apply fmul_canon; assumption]. Qed.
Lemma C_fh5 : is_canon (fh5 sc Y K).
Proof. unfold fh5. pose proof C_fy. pose proof C_fh3. apply fmul_canon; [assumption | apply fmul_canon; assumption]. Qed.
Lemma C_tz3 : is_canon tz3. Proof. unfold tz3. pose proof C_tz. apply fmul_canon; [| apply fmul_canon]; assumption. Qed.
Lemma C_tA : is_canon tA.
Proof.
  unfold tA. apply fadd_canon; [apply fsub_canon; [apply C_tz3 | apply fone_canon] | apply fscal_canon, C_teps].
Qed.
Lemma C_tB : is_canon tB. Proof. unfold tB. apply fsub_canon; [apply C_tz3 | apply fone_canon]. Qed.
Lemma C_txx : is_canon txx.
Proof.
  unfold txx. pose proof C_tx1. pose proof C_tx2. pose proof C_tdZ.
  apply fadd_canon; [apply fadd_canon |]; apply fmul_canon; assumption.
Qed.
Lemma C_tX (c cd : fser) : is_canon c -> is_canon cd -> is_canon (tX c cd).
Proof.
  intros Cc Ccd. unfold tX. pose proof C_fh3. pose proof C_fh5. pose proof C_tA. pose proof C_tB. pose proof C_txx.
  apply fsub_canon; [apply fadd_canon |]; [| | apply fscal_canon]; repeat (first [assumption | apply fmul_canon]).
Qed.
Lemma C_fc1 : is_canon (fc1 sc K).
Proof. destruct CK as [CKR CKZ]. unfold fc1, fr2, fr3, fx2. canon_tac. Qed.
Lemma C_fc2 : is_canon (fc2 sc K).
Proof. destruct CK as [CKR CKZ]. unfold fc2, fr1, fr3, fx1. canon_tac. Qed.
Lemma C_fc3 : is_canon (fc3 sc K).
Proof. destruct CK as [CKR CKZ]. unfold fc3, fr1, fr2, fx1, fx2. canon_tac. Qed.
Lemma C_tcd1 : is_canon tcd1.
Proof. unfold tcd1. apply fsub_canon; apply fscal_canon; [apply C_tdZ | apply C_tx2]. Qed.
Lemma C_tcd2 : is_canon tcd2.
Proof. unfold tcd2. apply fsub_canon; apply fscal_canon; [apply C_tx1 | apply C_tdZ]. Qed.
Lemma C_tcd3 : is_canon tcd3.
Proof. unfold tcd3. apply fsub_canon; apply fscal_canon; [apply C_tx2 | apply C_tx1]. Qed.

Lemma C_r2 : is_canon r2R /\ is_canon r2P /\ is_canon r2Z.
Proof.
  destruct (srcjet_canon sc Y K CK CY) as [A1 [A2 [A3 [A4 [A5 [_ [A7 [A8 [_ [A10 [A11 _]]]]]]]]]]].
  destruct (srcjet_canon sc Y K' CK' CY) as [D1 [D2 [D3 _]]].
  cbn [jR jP jZ jR_R jR_Z jP_R jP_Z jZ_R jZ_Z srcjet] in *.
  pose proof C_tdR. pose proof C_tdZ.
  unfold r2R, r2P, r2Z. refine (conj _ (conj _ _));
    apply fsub_canon; [apply fsub_canon | | apply fsub_canon | | apply fsub_canon | ]; try assumption;
    apply fadd_canon; apply fmul_canon; assumption.
Qed.

Lemma C_tXs : is_canon tXR /\ is_canon tXP /\ is_canon tXZ.
Proof.
  pose proof (C_tX _ _ C_fc1 C_tcd1). pose proof (C_tX _ _ C_fc2 C_tcd2). pose proof (C_tX _ _ C_fc3 C_tcd3).
  pose proof cosf_canon. pose proof sinf_canon.
  unfold tXR, tXP, tXZ. refine (conj _ (conj _ _)); try assumption;
    apply fadd_canon; apply fmul_canon; try assumption; apply fscal_canon; assumption.
Qed.

(** The second-order Taylor remainder of the field of one source. *)
Theorem src_r2 : nbound w (h * h * tRRb) r2R /\ nbound w (h * h * tRRb) r2P /\ nbound w (h * h * tRZb) r2Z.
Proof.
  destruct C_r2 as [CR [CP CZ]]. destruct C_tXs as [DR [DP DZ]].
  pose proof (E_FR sc Y K' w Hw FK' Hq' Hy') as A1. pose proof (E_FR sc Y K w Hw FK Hq Hy) as A0.
  pose proof (E_FR_R sc Y K w Hw FK Hq Hy) as AR. pose proof (E_FR_Z sc Y K w Hw FK Hq Hy) as AZ.
  pose proof (E_FP sc Y K' w Hw FK' Hq' Hy') as B1'. pose proof (E_FP sc Y K w Hw FK Hq Hy) as B0.
  pose proof (E_FP_R sc Y K w Hw FK Hq Hy) as BR. pose proof (E_FP_Z sc Y K w Hw FK Hq Hy) as BZ.
  pose proof (E_FZ sc Y K' w Hw FK' Hq' Hy') as G1. pose proof (E_FZ sc Y K w Hw FK Hq Hy) as G0.
  pose proof (E_FZ_R sc Y K w Hw FK Hq Hy) as GR. pose proof (E_FZ_Z sc Y K w Hw FK Hq Hy) as GZ.
  assert (FR2 : fin w r2R).
  { exact (proj1 (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ A1 A0)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ AR E_tdR) (ev_fmul _ Hw0 _ _ _ _ AZ E_tdZ)))). }
  assert (FP2 : fin w r2P).
  { exact (proj1 (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ B1' B0)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ BR E_tdR) (ev_fmul _ Hw0 _ _ _ _ BZ E_tdZ)))). }
  assert (FZ2 : fin w r2Z).
  { exact (proj1 (ev_fsub _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ G1 G0)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ GR E_tdR) (ev_fmul _ Hw0 _ _ _ _ GZ E_tdZ)))). }
  destruct (fin_mono w 0 _ Hw0 FR2) as [M1 N1]. destruct (fin_mono w 0 _ Hw0 FP2) as [M2 N2].
  destruct (fin_mono w 0 _ Hw0 FZ2) as [M3 N3].
  pose proof (nbound_mono w 0 _ _ Hw0 nb_tXR) as O1. pose proof (nbound_mono w 0 _ _ Hw0 nb_tXP) as O2.
  pose proof (nbound_mono w 0 _ _ Hw0 nb_tXZ) as O3.
  refine (conj _ (conj _ _)).
  - apply (nbound_feq w _ tXR r2R); [| exact nb_tXR].
    apply feq_sym, (canon_feq _ _ M1 _ CR DR N1 O1). intros t p. exact (proj1 (r2_pointwise Hzq Hz0 t p)).
  - apply (nbound_feq w _ tXP r2P); [| exact nb_tXP].
    apply feq_sym, (canon_feq _ _ M2 _ CP DP N2 O2). intros t p. exact (proj1 (proj2 (r2_pointwise Hzq Hz0 t p))).
  - apply (nbound_feq w _ tXZ r2Z); [| exact nb_tXZ].
    apply feq_sym, (canon_feq _ _ M3 _ CZ DZ N3 O3). intros t p. exact (proj2 (proj2 (r2_pointwise Hzq Hz0 t p))).
Qed.

(** * The change of the Jacobian *)

Definition tZb : R := tS2 + hm * hm * tRB.
Definition tZ1 : R := tP1 / 2 + hm * tRB.
Definition tZ5 : R := tZ1 * (1 + tZb + tZb * tZb + tZb * (tZb * tZb) + tZb * tZb * (tZb * tZb)).
Definition tZb5 : R := tZb * (tZb * tZb) * (tZb * tZb).

Lemma tZb_ge1 : 1 <= tZb.
Proof. unfold tZb. pose proof tS2_ge1. pose proof tRB_nn. assert (0 <= hm * hm) by nra. nra. Qed.

Lemma tz_feq : feq tz (fsub ts2 trho).
Proof. intros m n. unfold trho, fsub, fadd, fscal. simpl. split; ring. Qed.

Lemma nb_tz : nbound w tZb tz.
Proof.
  apply (nbound_feq w _ (fsub ts2 trho) tz (feq_sym _ _ tz_feq)).
  pose proof (nbound_fsub w _ _ _ _ nb_ts2 nb_trho) as T. refine (nbound_le w _ _ _ _ T).
  unfold tZb. pose proof tRB_nn. pose proof hh_le.
  assert (h * h * tRB <= hm * hm * tRB) by (apply Rmult_le_compat_r; lra). lra.
Qed.

Lemma tzm1_feq : feq (fsub tz fone) (fsub (fscal (- / 2) teps) trho).
Proof. intros m n. unfold trho, ts2, fsub, fadd, fscal. simpl. split; ring. Qed.

Lemma nb_tzm1 : nbound w (h * tZ1) (fsub tz fone).
Proof.
  apply (nbound_feq w _ _ _ (feq_sym _ _ tzm1_feq)).
  pose proof (nbound_fsub w _ _ _ _ (nbound_fscal w _ (- / 2) _ nb_teps) nb_trho) as T.
  refine (nbound_le w _ _ _ _ T). rewrite Rabs_Ropp, Rabs_right by lra. unfold tZ1.
  pose proof tRB_nn. assert (h * h * tRB <= h * (hm * tRB)).
  { rewrite Rmult_assoc. apply Rmult_le_compat_l; [lra |]. apply Rmult_le_compat_r; lra. }
  lra.
Qed.

Lemma C_tz5 : is_canon tz5.
Proof. unfold tz5. pose proof C_tz. pose proof C_tz3. apply fmul_canon; [| apply fmul_canon]; assumption. Qed.

Lemma tB5_feq : feq tB5 (fmul (fsub tz fone)
                               (fadd (fadd (fadd (fadd fone tz) (fmul tz tz)) tz3) (fmul (fmul tz tz) (fmul tz tz)))).
Proof.
  pose proof (ev_self w tz F_tz) as Z. pose proof (ev_fconst w 1) as E1.
  pose proof C_tz as Cz. pose proof C_tz3 as Cz3. pose proof C_tz5 as Cz5. pose proof fone_canon as C1.
  eapply feq_by_ev.
  - unfold tB5. apply fsub_canon; assumption.
  - apply fmul_canon; [apply fsub_canon; assumption |].
    repeat (first [assumption | apply fadd_canon | apply fmul_canon]).
  - exact (ev_fsub _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Z (ev_fmul _ Hw0 _ _ _ _ Z Z))
                                    (ev_fmul _ Hw0 _ _ _ _ Z Z)) E1).
  - exact (ev_fmul _ Hw0 _ _ _ _ (ev_fsub _ Hw0 _ _ _ _ Z E1)
             (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ (ev_fadd _ Hw0 _ _ _ _ E1 Z)
                                                              (ev_fmul _ Hw0 _ _ _ _ Z Z))
                                       (ev_fmul _ Hw0 _ _ _ _ Z (ev_fmul _ Hw0 _ _ _ _ Z Z)))
                (ev_fmul _ Hw0 _ _ _ _ (ev_fmul _ Hw0 _ _ _ _ Z Z) (ev_fmul _ Hw0 _ _ _ _ Z Z)))).
  - intros t p. cbv beta. ring.
Qed.

Lemma nb_tB5 : nbound w (h * tZ5) tB5.
Proof.
  apply (nbound_feq w _ _ _ (feq_sym _ _ tB5_feq)).
  pose proof nb_tz as Z.
  pose proof (nbound_fmul w _ _ _ _ Hw0 nb_tzm1
                (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _
                   (nbound_fadd w _ _ _ _ (nbound_fone w) Z) (nbound_fmul w _ _ _ _ Hw0 Z Z))
                   (nbound_fmul w _ _ _ _ Hw0 Z (nbound_fmul w _ _ _ _ Hw0 Z Z)))
                   (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Z Z) (nbound_fmul w _ _ _ _ Hw0 Z Z)))) as T.
  refine (nbound_le w _ _ _ _ T). right. unfold tZ5. ring.
Qed.

Lemma nb_tz5 : nbound w tZb5 tz5.
Proof.
  pose proof nb_tz as Z.
  exact (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Z (nbound_fmul w _ _ _ _ Hw0 Z Z))
           (nbound_fmul w _ _ _ _ Hw0 Z Z)).
Qed.

Definition tJb (DV Cc Dc RE DE : R) : R :=
  DV * (yb * (yb * yb)) * tB1
  + 3 * (yb * (yb * yb) * (yb * yb) * (Cc * RE * tZ5 + (Cc * DE + Dc * RE + hm * (Dc * DE)) * tZb5)).

Lemma nb_tJd (dv c cd re de : fser) (DV Cc Dc RE DE : R) :
  0 <= Dc -> 0 <= DE ->
  nbound w DV dv -> nbound w Cc c -> nbound w (h * Dc) cd -> nbound w RE re -> nbound w (h * DE) de ->
  nbound w (h * tJb DV Cc Dc RE DE) (tJd dv c cd re de).
Proof.
  intros HDc HDE Bdv Bc Bcd Bre Bde.
  pose proof (nbound_fsub w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Bdv nb_fh3) nb_tB)
    (nbound_fscal w _ 3 _ (nbound_fmul w _ _ _ _ Hw0 nb_fh5
       (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fmul w _ _ _ _ Hw0 Bc Bre) nb_tB5)
          (nbound_fmul w _ _ _ _ Hw0 (nbound_fadd w _ _ _ _ (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 Bc Bde)
                                        (nbound_fmul w _ _ _ _ Hw0 Bcd Bre)) (nbound_fmul w _ _ _ _ Hw0 Bcd Bde))
             nb_tz5))))) as T.
  unfold tJd. refine (nbound_le w _ _ _ _ T). rewrite (Rabs_right 3) by lra. unfold tJb.
  pose proof yb_nn. pose proof tZb_ge1.
  assert (Y5 : 0 <= yb * (yb * yb) * (yb * yb)) by (apply Rmult_le_pos; nra).
  assert (Z5 : 0 <= tZb5) by (unfold tZb5; apply Rmult_le_pos; [apply Rmult_le_pos |]; nra).
  assert (DD : h * Dc * (h * DE) <= h * (hm * (Dc * DE))).
  { replace (h * Dc * (h * DE)) with (h * (h * (Dc * DE))) by ring.
    apply Rmult_le_compat_l; [lra |]. apply Rmult_le_compat_r; [nra | lra]. }
  assert (DD' : h * Dc * (h * DE) * tZb5 <= h * (hm * (Dc * DE)) * tZb5) by (apply Rmult_le_compat_r; lra).
  assert (DD'' : yb * (yb * yb) * (yb * yb) * (h * Dc * (h * DE) * tZb5)
                 <= yb * (yb * yb) * (yb * yb) * (h * (hm * (Dc * DE)) * tZb5)) by (apply Rmult_le_compat_l; lra).
  apply Rle_trans with (DV * (yb * (yb * yb)) * (h * tB1)
    + 3 * (yb * (yb * yb) * (yb * yb) * (Cc * RE * (h * tZ5) + (Cc * (h * DE) + h * Dc * RE) * tZb5)
           + yb * (yb * yb) * (yb * yb) * (h * Dc * (h * DE) * tZb5))).
  { right. ring. }
  apply Rle_trans with (DV * (yb * (yb * yb)) * (h * tB1)
    + 3 * (yb * (yb * yb) * (yb * yb) * (Cc * RE * (h * tZ5) + (Cc * (h * DE) + h * Dc * RE) * tZb5)
           + yb * (yb * yb) * (yb * yb) * (h * (hm * (Dc * DE)) * tZb5))).
  { lra. }
  right. ring.
Qed.

Lemma nb_treR : nbound w (rho1 * cs + rho2 * cs) treR.
Proof. exact (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 B1 nbc) (nbound_fmul w _ _ _ _ Hw0 B2 nbs)). Qed.

Lemma nb_tdeR : nbound w (h * (2 * (cs * cs))) tdeR.
Proof.
  pose proof (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 nb_tx1 nbc)
                (nbound_fmul w _ _ _ _ Hw0 nb_tx2 nbs)) as T.
  unfold tdeR. refine (nbound_le w _ _ _ _ T). right. ring.
Qed.

Lemma nb_tdZ1 : nbound w (h * 1) tdZ.
Proof. apply (nbound_le w h); [right; ring | exact nb_tdZ]. Qed.

Definition tDVR1 : R := Rabs (- sd3 sc) * cs.
Definition tDVR2 : R := Rabs (sd3 sc) * cs.
Definition tDVR3 : R := Rabs (sd1 sc) * cs + Rabs (sd2 sc) * cs.
Definition tRER : R := rho1 * cs + rho2 * cs.
Definition tDER : R := 2 * (cs * cs).

Lemma D_nn : 0 <= tD1 /\ 0 <= tD2 /\ 0 <= tD3 /\ 0 <= tDER.
Proof.
  pose proof cs_pos. pose proof (Rabs_pos (sd1 sc)). pose proof (Rabs_pos (sd2 sc)). pose proof (Rabs_pos (sd3 sc)).
  unfold tD1, tD2, tD3, tDER. refine (conj _ (conj _ (conj _ _))); nra.
Qed.

Lemma nb_tJs :
  nbound w (h * tJb tDVR1 tC1 tD1 tRER tDER) tJR1 /\ nbound w (h * tJb tDVR2 tC2 tD2 tRER tDER) tJR2 /\
  nbound w (h * tJb tDVR3 tC3 tD3 tRER tDER) tJR3 /\
  nbound w (h * tJb (Rabs (sd2 sc)) tC1 tD1 rho3 1) tJZ1 /\
  nbound w (h * tJb (Rabs (- sd1 sc)) tC2 tD2 rho3 1) tJZ2 /\
  nbound w (h * tJb (Rabs 0) tC3 tD3 rho3 1) tJZ3.
Proof.
  destruct D_nn as [N1 [N2 [N3 N4]]].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact (nb_tJd _ _ _ _ _ _ _ _ _ _ N1 N4 (nbound_fscal w _ _ _ nbs) nb_fc1 nb_tcd1 nb_treR nb_tdeR).
  - exact (nb_tJd _ _ _ _ _ _ _ _ _ _ N2 N4 (nbound_fscal w _ _ _ nbc) nb_fc2 nb_tcd2 nb_treR nb_tdeR).
  - exact (nb_tJd _ _ _ _ _ _ _ _ _ _ N3 N4
             (nbound_fsub w _ _ _ _ (nbound_fscal w _ _ _ nbs) (nbound_fscal w _ _ _ nbc))
             nb_fc3 nb_tcd3 nb_treR nb_tdeR).
  - exact (nb_tJd _ _ _ _ _ _ _ _ _ _ N1 Rle_0_1 (nbound_fconst w _) nb_fc1 nb_tcd1 B3 nb_tdZ1).
  - exact (nb_tJd _ _ _ _ _ _ _ _ _ _ N2 Rle_0_1 (nbound_fconst w _) nb_fc2 nb_tcd2 B3 nb_tdZ1).
  - exact (nb_tJd _ _ _ _ _ _ _ _ _ _ N3 Rle_0_1 (nbound_fconst w _) nb_fc3 nb_tcd3 B3 nb_tdZ1).
Qed.

Lemma C_tJd (dv c cd re de : fser) :
  is_canon dv -> is_canon c -> is_canon cd -> is_canon re -> is_canon de -> is_canon (tJd dv c cd re de).
Proof.
  intros A1 A2 A3 A4 A5. pose proof C_fh3. pose proof C_fh5. pose proof C_tB. pose proof C_tz5.
  assert (is_canon tB5) by (unfold tB5; apply fsub_canon; [apply C_tz5 | apply fone_canon]).
  unfold tJd. repeat (first [assumption | apply fsub_canon | apply fadd_canon | apply fscal_canon | apply fmul_canon]).
Qed.

Lemma C_tLs : is_canon tLRR /\ is_canon tLRZ /\ is_canon tLPR /\ is_canon tLPZ /\ is_canon tLZR /\ is_canon tLZZ.
Proof.
  destruct CK as [CKR CKZ].
  pose proof cosf_canon as Cc. pose proof sinf_canon as Cs.
  assert (C3 : is_canon (fr3 sc K)) by (unfold fr3; apply fsub_canon; [assumption | apply fconst_canon]).
  assert (CR : is_canon treR).
  { unfold treR, fr1, fr2, fx1, fx2. canon_tac. }
  assert (CD : is_canon tdeR).
  { unfold tdeR. pose proof C_tx1. pose proof C_tx2. apply fadd_canon; apply fmul_canon; assumption. }
  pose proof C_tdZ as CdZ.
  assert (V1 : is_canon tdvR1) by (unfold tdvR1; apply fscal_canon, sinf_canon).
  assert (V2 : is_canon tdvR2) by (unfold tdvR2; apply fscal_canon, cosf_canon).
  assert (V3 : is_canon tdvR3).
  { unfold tdvR3. apply fsub_canon; apply fscal_canon; [apply sinf_canon | apply cosf_canon]. }
  assert (W1 : is_canon tdvZ1) by apply fconst_canon.
  assert (W2 : is_canon tdvZ2) by apply fconst_canon.
  assert (W3 : is_canon tdvZ3) by apply fconst_canon.
  pose proof (C_tJd _ _ _ _ _ V1 C_fc1 C_tcd1 CR CD) as J1.
  pose proof (C_tJd _ _ _ _ _ V2 C_fc2 C_tcd2 CR CD) as J2.
  pose proof (C_tJd _ _ _ _ _ V3 C_fc3 C_tcd3 CR CD) as J3.
  pose proof (C_tJd _ _ _ _ _ W1 C_fc1 C_tcd1 C3 CdZ) as L1.
  pose proof (C_tJd _ _ _ _ _ W2 C_fc2 C_tcd2 C3 CdZ) as L2.
  pose proof (C_tJd _ _ _ _ _ W3 C_fc3 C_tcd3 C3 CdZ) as L3.
  unfold tLRR, tLRZ, tLPR, tLPZ, tLZR, tLZZ, tJR1, tJR2, tJR3, tJZ1, tJZ2, tJZ3.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); try assumption;
    apply fadd_canon; apply fmul_canon; try assumption; apply fscal_canon; assumption.
Qed.

Lemma C_dFs : is_canon dFRR /\ is_canon dFRZ /\ is_canon dFPR /\ is_canon dFPZ /\ is_canon dFZR /\ is_canon dFZZ.
Proof.
  destruct (srcjet_canon sc Y K CK CY) as [_ [_ [_ [A4 [A5 [_ [A7 [A8 [_ [A10 [A11 _]]]]]]]]]]].
  destruct (srcjet_canon sc Y K' CK' CY) as [_ [_ [_ [B4 [B5 [_ [B7 [B8 [_ [B10 [B11 _]]]]]]]]]]].
  cbn [jR_R jR_Z jP_R jP_Z jZ_R jZ_Z srcjet] in *.
  unfold dFRR, dFRZ, dFPR, dFPZ, dFZR, dFZZ.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); apply fsub_canon; assumption.
Qed.

Definition tLRRb : R := (tJb tDVR1 tC1 tD1 tRER tDER + tJb tDVR2 tC2 tD2 tRER tDER) * cs.
Definition tLRZb : R := (tJb (Rabs (sd2 sc)) tC1 tD1 rho3 1 + tJb (Rabs (- sd1 sc)) tC2 tD2 rho3 1) * cs.
Definition tLZRb : R := tJb tDVR3 tC3 tD3 tRER tDER.
Definition tLZZb : R := tJb (Rabs 0) tC3 tD3 rho3 1.

(** The change of the derivatives of the field of one source between the tori. *)
Theorem src_lip :
  nbound w (h * tLRRb) dFRR /\ nbound w (h * tLRZb) dFRZ /\ nbound w (h * tLRRb) dFPR /\
  nbound w (h * tLRZb) dFPZ /\ nbound w (h * tLZRb) dFZR /\ nbound w (h * tLZZb) dFZZ.
Proof.
  destruct nb_tJs as [J1 [J2 [J3 [L1 [L2 L3]]]]].
  assert (BRR : nbound w (h * tLRRb) tLRR).
  { pose proof (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 J1 nbc) (nbound_fmul w _ _ _ _ Hw0 J2 nbs)) as T.
    unfold tLRR. refine (nbound_le w _ _ _ _ T). right. unfold tLRRb. ring. }
  assert (BRZ : nbound w (h * tLRZb) tLRZ).
  { pose proof (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 L1 nbc) (nbound_fmul w _ _ _ _ Hw0 L2 nbs)) as T.
    unfold tLRZ. refine (nbound_le w _ _ _ _ T). right. unfold tLRZb. ring. }
  assert (BPR : nbound w (h * tLRRb) tLPR).
  { pose proof (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fscal w _ (-1) _ J1) nbs)
                  (nbound_fmul w _ _ _ _ Hw0 J2 nbc)) as T.
    unfold tLPR. refine (nbound_le w _ _ _ _ T). rewrite Rabs_left by lra. right. unfold tLRRb. ring. }
  assert (BPZ : nbound w (h * tLRZb) tLPZ).
  { pose proof (nbound_fadd w _ _ _ _ (nbound_fmul w _ _ _ _ Hw0 (nbound_fscal w _ (-1) _ L1) nbs)
                  (nbound_fmul w _ _ _ _ Hw0 L2 nbc)) as T.
    unfold tLPZ. refine (nbound_le w _ _ _ _ T). rewrite Rabs_left by lra. right. unfold tLRZb. ring. }
  destruct C_tLs as [DRR [DRZ [DPR [DPZ [DZR DZZ]]]]].
  destruct C_dFs as [ERR [ERZ [EPR [EPZ [EZR EZZ]]]]].
  assert (Fd : forall (u u' : fser) (f f' : R -> R -> R), ev w u' f' -> ev w u f -> exists M, nbound 0 M (fsub u' u)).
  { intros u u' f f' E' E. destruct (fin_mono w 0 _ Hw0 (proj1 (ev_fsub _ Hw0 _ _ _ _ E' E))) as [M HM].
    exists M. exact HM. }
  destruct (Fd _ _ _ _ (E_FR_R sc Y K' w Hw FK' Hq' Hy') (E_FR_R sc Y K w Hw FK Hq Hy)) as [M1 N1].
  destruct (Fd _ _ _ _ (E_FR_Z sc Y K' w Hw FK' Hq' Hy') (E_FR_Z sc Y K w Hw FK Hq Hy)) as [M2 N2].
  destruct (Fd _ _ _ _ (E_FP_R sc Y K' w Hw FK' Hq' Hy') (E_FP_R sc Y K w Hw FK Hq Hy)) as [M3 N3].
  destruct (Fd _ _ _ _ (E_FP_Z sc Y K' w Hw FK' Hq' Hy') (E_FP_Z sc Y K w Hw FK Hq Hy)) as [M4 N4].
  destruct (Fd _ _ _ _ (E_FZ_R sc Y K' w Hw FK' Hq' Hy') (E_FZ_R sc Y K w Hw FK Hq Hy)) as [M5 N5].
  destruct (Fd _ _ _ _ (E_FZ_Z sc Y K' w Hw FK' Hq' Hy') (E_FZ_Z sc Y K w Hw FK Hq Hy)) as [M6 N6].
  pose proof (dj_pointwise Hzq Hz0) as P.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - apply (nbound_feq w _ tLRR dFRR); [| exact BRR].
    apply feq_sym, (canon_feq _ _ M1 _ ERR DRR N1 (nbound_mono w 0 _ _ Hw0 BRR)).
    intros t p. exact (proj1 (P t p)).
  - apply (nbound_feq w _ tLRZ dFRZ); [| exact BRZ].
    apply feq_sym, (canon_feq _ _ M2 _ ERZ DRZ N2 (nbound_mono w 0 _ _ Hw0 BRZ)).
    intros t p. exact (proj1 (proj2 (P t p))).
  - apply (nbound_feq w _ tLPR dFPR); [| exact BPR].
    apply feq_sym, (canon_feq _ _ M3 _ EPR DPR N3 (nbound_mono w 0 _ _ Hw0 BPR)).
    intros t p. exact (proj1 (proj2 (proj2 (P t p)))).
  - apply (nbound_feq w _ tLPZ dFPZ); [| exact BPZ].
    apply feq_sym, (canon_feq _ _ M4 _ EPZ DPZ N4 (nbound_mono w 0 _ _ Hw0 BPZ)).
    intros t p. exact (proj1 (proj2 (proj2 (proj2 (P t p))))).
  - apply (nbound_feq w _ tLZR dFZR); [| exact (proj1 (proj2 (proj2 nb_tJs)))].
    apply feq_sym, (canon_feq _ _ M5 _ EZR DZR N5 (nbound_mono w 0 _ _ Hw0 J3)).
    intros t p. exact (proj1 (proj2 (proj2 (proj2 (proj2 (P t p)))))).
  - apply (nbound_feq w _ tLZZ dFZZ); [| exact L3].
    apply feq_sym, (canon_feq _ _ M6 _ EZZ DZZ N6 (nbound_mono w 0 _ _ Hw0 L3)).
    intros t p. exact (proj2 (proj2 (proj2 (proj2 (proj2 (P t p)))))).
Qed.

End Bounds.

End Taylor.
