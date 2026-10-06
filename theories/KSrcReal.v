(** The sources along a reference torus, moved to the first torus, and the
    crude norms of the field there.

    The reference torus is the first torus with every mode outside a small
    box cleared ([Kref]); its distance to the first torus on a strip is at
    most the norm of the cleared modes ([ref_dist]). Along it the distance
    families of a source are bounded by the norms of the reference torus
    ([r1r], [r2r], [r3r]), the seed Y by the weighted transforms of its
    values on a grid ([MYr]) and the defect 1 - q Y^2 by the weighted
    transforms of its values on a grid past its support ([THr]). FieldBall.v
    moves these bounds to the first torus ([src_at]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity FourierDFT
  FourierCanon FourierPer FourierSym FourierList FourierModel FourierSupp FourierModelPer KAMVec KAMFin KAMPer
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldTaylor FieldTotal FieldCrude FieldBall FieldLine
  KCheckErr KFix KCheckKern KEngine KDense KSrc KRef KCheckE0.
Import ListNotations.
Local Open Scope R_scope.

(** The source of the data: point and weighted tangent at scale 2^-s. *)
Definition src_of (s : Z) (x : (Z * Z * Z) * (Z * Z * Z)) : src :=
  let '((p1, p2, p3), (d1, d2, d3)) := x in mksrc (dy s p1) (dy s p2) (dy s p3) (dy s d1) (dy s d2) (dy s d3).

(** The seed of a source: rows of (cosine, sine) mantissas over
    zrange Ky1 x zrange Ky2, every toroidal mode. *)
Definition yfam (sY : Z) (Ky1 Ky2 : nat) (rows : list (list (Z * Z))) : list (Z * list (Z * (R * R))) :=
  dfam sY (zrange Ky1) (pns 1 Ky2) rows.
Definition yser (sY : Z) (Ky1 Ky2 : nat) (rows : list (list (Z * Z))) : fser := cden (yfam sY Ky1 Ky2 rows).

Definition srcl (s sY : Z) (Ky1 Ky2 : nat) (xs : list ((Z * Z * Z) * (Z * Z * Z)))
    (ys : list (list (list (Z * Z)))) : list (src * fser) :=
  map (fun xy => (src_of s (fst xy), yser sY Ky1 Ky2 (snd xy))) (combine xs ys).

Lemma zrange_abs (K : nat) (k : Z) : In k (zrange K) -> (Z.abs k <= Z.of_nat K)%Z.
Proof. apply in_zrange. Qed.

Theorem yser_supp (sY : Z) (Ky1 Ky2 : nat) (rows : list (list (Z * Z))) : supp Ky1 Ky2 (yser sY Ky1 Ky2 rows).
Proof.
  unfold yser, cden. apply supp_canon, flist_supp. apply dfam_forall. intros k n c sn Hk Hn _.
  cbn [fe_m fe_n]. split; [apply zrange_abs, Hk |].
  unfold pns in Hn. apply in_map_iff in Hn. destruct Hn as [l [El Hl]]. subst n.
  rewrite Z.mul_1_l. apply zrange_abs, Hl.
Qed.

Lemma yser_canon (sY : Z) (Ky1 Ky2 : nat) (rows : list (list (Z * Z))) : is_canon (yser sY Ky1 Ky2 rows).
Proof. apply cden_canon. Qed.

Lemma srcl_canon (s sY : Z) (Ky1 Ky2 : nat) xs ys : List.Forall (fun sy => is_canon (snd sy)) (srcl s sY Ky1 Ky2 xs ys).
Proof.
  unfold srcl. apply Forall_forall. intros sy H. apply in_map_iff in H. destruct H as [xy [E _]]. subst sy.
  apply yser_canon.
Qed.

Lemma in_srcl (s sY : Z) (Ky1 Ky2 : nat) xs ys (sy : src * fser) :
  In sy (srcl s sY Ky1 Ky2 xs ys) -> exists rows, snd sy = yser sY Ky1 Ky2 rows.
Proof. unfold srcl. intros H. apply in_map_iff in H. destruct H as [xy [E _]]. subst sy. exists (snd xy). reflexivity. Qed.

(** * Norms of the finite families of a torus *)

Definition fnorm (w : R) (f : list (Z * list (Z * (R * R)))) : R := esum (ewt w) (dents f).

Lemma lc_cden_nb (om w : R) (f : list (Z * list (Z * (R * R)))) :
  nbound w (Rabs om * fnorm w (fam_dt f) + fnorm w (fam_dp f)) (lc om (cden f)).
Proof.
  apply (nbound_feq w _ (fadd (fscal om (dt (cden f))) (dp (cden f)))); [apply feq_sym, lc_feq |].
  apply nbound_fadd.
  - apply nbound_fscal. apply (nbound_feq w _ (cden (fam_dt f))); [apply feq_sym, dt_cden | apply nbound_cden].
  - apply (nbound_feq w _ (cden (fam_dp f))); [apply feq_sym, dp_cden | apply nbound_cden].
Qed.

Lemma dt_cden_nb (w : R) (f : list (Z * list (Z * (R * R)))) : nbound w (fnorm w (fam_dt f)) (dt (cden f)).
Proof. apply (nbound_feq w _ (cden (fam_dt f))); [apply feq_sym, dt_cden | apply nbound_cden]. Qed.

(** * The first torus and the reference torus *)

Section Ref.

Variables (P : Z) (Km Kn : nat) (s0 : Z) (rowsR rowsZ : list (list Z)) (Kr1 Kr2 : nat).
Hypothesis HP : (0 < P)%Z.

Definition fRf : list (Z * list (Z * (R * R))) := dfam s0 (zrange Km) (pns P Kn) (crows rowsR).
Definition fZf : list (Z * list (Z * (R * R))) := dfam s0 (zrange Km) (pns P Kn) (srows rowsZ).
Definition K0v : vf := mkvf (cden fRf) (cden fZf).
Definition Kref : vf := mkvf (cden (fam_map (gmask Kr1 Kr2) fRf)) (cden (fam_map (gmask Kr1 Kr2) fZf)).

Definition NRr (w : R) : R := esum (ewt w) (dents (fam_map (gmask Kr1 Kr2) fRf)).
Definition NZr (w : R) : R := esum (ewt w) (dents (fam_map (gmask Kr1 Kr2) fZf)).
Definition rref (w : R) : R :=
  esum (ewt w) (dents (fam_map (gtail Kr1 Kr2) fRf)) + esum (ewt w) (dents (fam_map (gtail Kr1 Kr2) fZf)).

Lemma esum_ewt_nonneg (w : R) (es : list fent) : 0 <= esum (ewt w) es.
Proof.
  apply esum_nonneg. intros e. unfold ewt. apply Rmult_le_pos; [| apply Rlt_le, wt_pos].
  pose proof (Rabs_pos (fe_c e)). pose proof (Rabs_pos (fe_s e)). lra.
Qed.

Theorem ref_dist (w : R) : vbound w (rref w) (vsub K0v Kref).
Proof.
  unfold rref. pose proof (esum_ewt_nonneg w (dents (fam_map (gtail Kr1 Kr2) fRf))).
  pose proof (esum_ewt_nonneg w (dents (fam_map (gtail Kr1 Kr2) fZf))).
  split; cbn [vsub vR vZ K0v Kref].
  - apply (nbound_feq w _ (cden (fam_map (gtail Kr1 Kr2) fRf))); [apply feq_sym, cden_sub_split, gmask_tail |].
    apply (nbound_le w (esum (ewt w) (dents (fam_map (gtail Kr1 Kr2) fRf)))); [lra | apply nbound_cden].
  - apply (nbound_feq w _ (cden (fam_map (gtail Kr1 Kr2) fZf))); [apply feq_sym, cden_sub_split, gmask_tail |].
    apply (nbound_le w (esum (ewt w) (dents (fam_map (gtail Kr1 Kr2) fZf)))); [lra | apply nbound_cden].
Qed.

Lemma K0v_fin (w : R) : vfin w K0v.
Proof. split; [exists (esum (ewt w) (dents fRf)) | exists (esum (ewt w) (dents fZf))]; apply nbound_cden. Qed.

Lemma Kref_fin (w : R) : vfin w Kref.
Proof. split; [exists (NRr w) | exists (NZr w)]; apply nbound_cden. Qed.

Lemma K0v_canon : vcanon K0v. Proof. split; apply cden_canon. Qed.
Lemma Kref_canon : vcanon Kref. Proof. split; apply cden_canon. Qed.

Lemma K0v_sym : vsym K0v. Proof. split; [apply cden_even | apply cden_odd]. Qed.
Lemma K0v_per : vper P K0v. Proof. split; apply cden_per; exact HP. Qed.

Lemma Kref_supp : supp Kr1 Kr2 (vR Kref) /\ supp Kr1 Kr2 (vZ Kref).
Proof. split; apply cden_mask_supp. Qed.

Lemma NRr_nb (w : R) : nbound w (NRr w) (vR Kref). Proof. apply nbound_cden. Qed.
Lemma NZr_nb (w : R) : nbound w (NZr w) (vZ Kref). Proof. apply nbound_cden. Qed.

(** * One source along the reference torus *)

Definition csw (w : R) : R := wt w 0 1.

Lemma csw_nb (w : R) : nbound w (csw w) cosf /\ nbound w (csw w) sinf.
Proof. split; [apply (nb_cosf w) | apply (nb_sinf w)]. Qed.

Definition r1r (w : R) (sc : src) : R := NRr w * csw w + Rabs (sp1 sc).
Definition r2r (w : R) (sc : src) : R := NRr w * csw w + Rabs (sp2 sc).
Definition r3r (w : R) (sc : src) : R := NZr w + Rabs (sp3 sc).
Definition MDr (w : R) (sc : src) : R := r1r w sc * r1r w sc + r2r w sc * r2r w sc + r3r w sc * r3r w sc.

Lemma r_nb (w : R) (sc : src) : 0 <= w ->
  nbound w (r1r w sc) (fr1 sc Kref) /\ nbound w (r2r w sc) (fr2 sc Kref) /\ nbound w (r3r w sc) (fr3 sc Kref) /\
  nbound w (MDr w sc) (fq sc Kref).
Proof.
  intros Hw.
  assert (B1 : nbound w (r1r w sc) (fr1 sc Kref)) by (apply fr1_nb; [exact Hw | apply NRr_nb]).
  assert (B2 : nbound w (r2r w sc) (fr2 sc Kref)) by (apply fr2_nb; [exact Hw | apply NRr_nb]).
  assert (B3 : nbound w (r3r w sc) (fr3 sc Kref)) by (apply fr3_nb; apply NZr_nb).
  refine (conj B1 (conj B2 (conj B3 _))). unfold MDr. apply fq_nb; assumption.
Qed.

(** The exact bounds read from grids of N1s x N2s points of the whole torus. *)
Variables (N1s N2s Ky1 Ky2 : nat).

Definition K1x : nat := (Kr1 + Kr1) + (Ky1 + Ky1).
Definition K2x : nat := (S Kr2 + S Kr2) + (Ky2 + Ky2).

Definition THr (w : R) (sy : src * fser) : R := rexact 1 N1s N2s K1x K2x (defect (fst sy) Kref (snd sy)) w.
Definition MYr (w : R) (sy : src * fser) : R := rexact 1 N1s N2s Ky1 Ky2 (snd sy) w.

Hypothesis HN1s : (2 * K1x < N1s)%nat.
Hypothesis HN2s : (2 * K2x < N2s)%nat.

Lemma Kfull1 (K : nat) : Kfull (Z.of_nat 1) K = K.
Proof. unfold Kfull. simpl. lia. Qed.

Lemma per1 (u : fser) : FourierPer.is_per (Z.of_nat 1) u.
Proof. intros m n Hn. exfalso. apply Hn. simpl. apply Z.mod_1_r. Qed.

Lemma defect_canon (sc : src) (Y : fser) : is_canon Y -> is_canon (defect sc Kref Y).
Proof.
  intros CY. destruct Kref_canon as [CKR CKZ].
  unfold defect. apply fsub_canon; [apply fone_canon |].
  apply fmul_canon; [| apply fmul_canon; exact CY].
  unfold fq, fr1, fr2, fr3, fx1, fx2. canon_tac.
Qed.

Theorem THr_nb (w : R) (sy : src * fser) :
  supp Ky1 Ky2 (snd sy) -> is_canon (snd sy) -> nbound w (THr w sy) (defect (fst sy) Kref (snd sy)).
Proof.
  intros SY CY. destruct Kref_supp as [SR SZ].
  apply exact_nbound; [lia | lia | rewrite Kfull1; lia | rewrite Kfull1 | apply defect_canon, CY | apply per1].
  exact (defect_supp (fst sy) Kref Kr1 Kr2 SR SZ (snd sy) Ky1 Ky2 SY).
Qed.

Theorem MYr_nb (w : R) (sy : src * fser) : supp Ky1 Ky2 (snd sy) -> is_canon (snd sy) -> nbound w (MYr w sy) (snd sy).
Proof.
  intros SY CY. apply exact_nbound; [lia | unfold K1x in HN1s; lia | rewrite Kfull1; unfold K2x in HN2s; lia |
                                     rewrite Kfull1; exact SY | exact CY | apply per1].
Qed.

(** * The source on the first torus *)

Definition r1k (w : R) (sc : src) : R := r1r w sc + rref w * csw w.
Definition r2k (w : R) (sc : src) : R := r2r w sc + rref w * csw w.
Definition r3k (w : R) (sc : src) : R := r3r w sc + rref w.
Definition thk (w : R) (sy : src * fser) : R :=
  bth (rref w) (r1r w (fst sy)) (r2r w (fst sy)) (r3r w (fst sy)) (MYr w sy) (THr w sy) (csw w).
Definition ybk (w : R) (sy : src * fser) : R :=
  byb (rref w) (r1r w (fst sy)) (r2r w (fst sy)) (r3r w (fst sy)) (MYr w sy) (THr w sy) (csw w).
Definition MDk (w : R) (sy : src * fser) : R :=
  MDr w (fst sy) + rref w * bE1 (rref w) (r1r w (fst sy)) (r2r w (fst sy)) (r3r w (fst sy)) (csw w).

(** The conditions a check verifies for one source on a strip. *)
Definition src_cond (w : R) (sy : src * fser) : Prop :=
  thk w sy < 1 /\ inv_eps (MYr w sy) (thk w sy) 0 < feval (snd sy) 0 0.

Lemma rref_nonneg (w : R) : 0 <= rref w.
Proof.
  unfold rref. pose proof (esum_ewt_nonneg w (dents (fam_map (gtail Kr1 Kr2) fRf))).
  pose proof (esum_ewt_nonneg w (dents (fam_map (gtail Kr1 Kr2) fZf))). lra.
Qed.

Theorem src_at (w : R) (sy : src * fser) :
  0 < w -> supp Ky1 Ky2 (snd sy) -> is_canon (snd sy) -> src_cond w sy ->
  nbound w (r1k w (fst sy)) (fr1 (fst sy) K0v) /\ nbound w (r2k w (fst sy)) (fr2 (fst sy) K0v) /\
  nbound w (r3k w (fst sy)) (fr3 (fst sy) K0v) /\ nbound w (MYr w sy) (snd sy) /\
  nbound w (MDk w sy) (fq (fst sy) K0v) /\
  nbound w (thk w sy) (fsub fone (fmul (fq (fst sy) K0v) (fmul (snd sy) (snd sy)))) /\
  nbound w (ybk w sy) (fy (fst sy) (snd sy) K0v) /\
  isq_ok w (fq (fst sy) K0v) (snd sy) /\ 0 < feval (fy (fst sy) (snd sy) K0v) 0 0.
Proof.
  intros Hw SY CY [Hth Hpos]. destruct sy as [sc Y]. cbn [fst snd] in *.
  assert (Hw' : 0 <= w) by lra.
  destruct (r_nb w sc Hw') as [B1 [B2 [B3 BD]]].
  pose proof (THr_nb w (sc, Y) SY CY) as BT. cbn [fst snd] in BT.
  pose proof (MYr_nb w (sc, Y) SY CY) as BY. cbn [fst snd] in BY.
  pose proof (ref_dist w) as HD. pose proof (rref_nonneg w) as Hr.
  pose proof (csw_nb w) as Hcs.
  assert (HY00 : feval Y 0 0 <= feval Y 0 0) by lra.
  unfold r1k, r2k, r3k, thk, ybk, MDk in *. cbn [fst snd] in *.
  refine (conj _ (conj _ (conj _ (conj BY (conj _ (conj _ (conj _ (conj _ _)))))))).
  - exact (ball_r1 sc Kref K0v w (rref w) (r1r w sc) Hw (Kref_fin w) (K0v_fin w) Kref_canon K0v_canon HD B1 (csw w) Hcs).
  - exact (ball_r2 sc Kref K0v w (rref w) (r2r w sc) Hw (Kref_fin w) (K0v_fin w) Kref_canon K0v_canon HD B2 (csw w) Hcs).
  - exact (ball_r3 sc Kref K0v w (rref w) (r3r w sc) HD B3).
  - exact (ball_q sc Kref K0v w (rref w) (r1r w sc) (r2r w sc) (r3r w sc) (MDr w sc) Hw Hr (Kref_fin w) (K0v_fin w)
             Kref_canon K0v_canon HD B1 B2 B3 BD (csw w) Hcs).
  - exact (ball_def sc Y Kref K0v w (rref w) (r1r w sc) (r2r w sc) (r3r w sc) (MYr w (sc, Y)) (THr w (sc, Y)) Hw Hr
             (Kref_fin w) (K0v_fin w) Kref_canon K0v_canon CY HD B1 B2 B3 BY BT (csw w) Hcs).
  - exact (ball_y sc Y Kref K0v w (rref w) (r1r w sc) (r2r w sc) (r3r w sc) (MYr w (sc, Y)) (THr w (sc, Y)) Hw Hr
             (Kref_fin w) (K0v_fin w) Kref_canon K0v_canon CY HD B1 B2 B3 BY BT (csw w) Hcs Hth).
  - exact (ball_isq sc Y Kref K0v w (rref w) (r1r w sc) (r2r w sc) (r3r w sc) (MYr w (sc, Y)) (MDr w sc) (THr w (sc, Y))
             Hw Hr (Kref_fin w) (K0v_fin w) Kref_canon K0v_canon CY HD B1 B2 B3 BY BD BT (csw w) Hcs Hth).
  - exact (ball_y0 sc Y Kref K0v w (rref w) (r1r w sc) (r2r w sc) (r3r w sc) (MYr w (sc, Y)) (MDr w sc) (THr w (sc, Y))
             (feval Y 0 0) Hw Hr (Kref_fin w) (K0v_fin w) Kref_canon K0v_canon CY HD B1 B2 B3 BY BD BT HY00
             (csw w) Hcs Hth Hpos).
Qed.

(** * Crude norms of the field along the first torus *)

Variable l : list (src * fser).
Hypothesis Hl : List.Forall (fun sy => supp Ky1 Ky2 (snd sy) /\ is_canon (snd sy)) l.

Definition crude_ok (w : R) : Prop := List.Forall (src_cond w) l.

Lemma crude_src (w : R) : 0 < w -> crude_ok w -> List.Forall (fun sy =>
  nbound w (r1k w (fst sy)) (fr1 (fst sy) K0v) /\ nbound w (r2k w (fst sy)) (fr2 (fst sy) K0v) /\
  nbound w (r3k w (fst sy)) (fr3 (fst sy) K0v) /\ nbound w (ybk w sy) (fy (fst sy) (snd sy) K0v)) l.
Proof.
  intros Hw Hc. unfold crude_ok in Hc. rewrite Forall_forall in *. intros sy I.
  destruct (Hl sy I) as [SY CY]. destruct (src_at w sy Hw SY CY (Hc sy I)) as [A [B [C [_ [_ [_ [D _]]]]]]].
  exact (conj A (conj B (conj C D))).
Qed.

Definition kr1 (w : R) (sy : src * fser) : R := r1k w (fst sy).
Definition kr2 (w : R) (sy : src * fser) : R := r2k w (fst sy).
Definition kr3 (w : R) (sy : src * fser) : R := r3k w (fst sy).

Definition tR (w : R) : R := Rabs (IZR P) * ((1 + Rabs (-1)) * lsum (sRP (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).
Definition tP (w : R) : R := Rabs (IZR P) * ((1 + Rabs 1) * lsum (sRP (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).
Definition tZ (w : R) : R := Rabs (IZR P) * ((1 + Rabs 1) * lsum (sZ (kr1 w) (kr2 w) (ybk w)) l).
Definition tRR (w : R) : R := Rabs (IZR P) * ((1 + Rabs (-1)) * lsum (sRR (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).
Definition tRZ (w : R) : R := Rabs (IZR P) * ((1 + Rabs 1) * lsum (sRZ (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).
Definition tPR (w : R) : R := Rabs (IZR P) * ((1 + Rabs 1) * lsum (sRR (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).
Definition tPZ (w : R) : R := Rabs (IZR P) * ((1 + Rabs (-1)) * lsum (sRZ (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).
Definition tZR (w : R) : R := Rabs (IZR P) * ((1 + Rabs 1) * lsum (sZR (csw w) (kr1 w) (kr2 w) (ybk w)) l).
Definition tZZ (w : R) : R := Rabs (IZR P) * ((1 + Rabs (-1)) * lsum (sZZ (kr1 w) (kr2 w) (kr3 w) (ybk w)) l).

Theorem crude_tot (w : R) : 0 < w -> crude_ok w ->
  nbound w (tR w) (jR (tot P l K0v)) /\ nbound w (tP w) (jP (tot P l K0v)) /\ nbound w (tZ w) (jZ (tot P l K0v)) /\
  nbound w (tRR w) (jR_R (tot P l K0v)) /\ nbound w (tRZ w) (jR_Z (tot P l K0v)) /\
  nbound w (tPR w) (jP_R (tot P l K0v)) /\ nbound w (tPZ w) (jP_Z (tot P l K0v)) /\
  nbound w (tZR w) (jZ_R (tot P l K0v)) /\ nbound w (tZZ w) (jZ_Z (tot P l K0v)).
Proof.
  intros Hw Hc. pose proof (crude_src w Hw Hc) as Hs. assert (Hw' : 0 <= w) by lra.
  destruct (csw_nb w) as [BC BS].
  unfold tR, tP, tZ, tRR, tRZ, tPR, tPZ, tZR, tZZ.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - exact (tot_R_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_P_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_Z_nb P l K0v w (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' Hs).
  - exact (tot_RR_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_RZ_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_PR_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_PZ_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_ZR_nb P l K0v w (csw w) (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' BC BS Hs).
  - exact (tot_ZZ_nb P l K0v w (kr1 w) (kr2 w) (kr3 w) (ybk w) Hw' Hs).
Qed.

(** The crude norms of the numerators of the error and of the defects of the
    seeds of 1 / B_phi and 1 / (B_phi |a|^2). *)
Theorem crude_num (om w : R) (Ub gs : fser) (MU MG : R) : 0 < w -> crude_ok w -> nbound w MU Ub -> nbound w MG gs ->
  nbound w (tP w * (Rabs om * fnorm w (fam_dt fRf) + fnorm w (fam_dp fRf)) + fnorm w fRf * tR w) (errF_R P l om K0v) /\
  nbound w (tP w * (Rabs om * fnorm w (fam_dt fZf) + fnorm w (fam_dp fZf)) + fnorm w fRf * tZ w) (errF_Z P l om K0v) /\
  nbound w (1 + tP w * MU) (defU P l K0v Ub) /\
  nbound w (1 + tP w * (fnorm w (fam_dt fRf) * fnorm w (fam_dt fRf) + fnorm w (fam_dt fZf) * fnorm w (fam_dt fZf)) * MG)
    (defG P l K0v gs).
Proof.
  intros Hw Hc HU HG. assert (Hw' : 0 <= w) by lra.
  destruct (crude_tot w Hw Hc) as [TR [TP [TZ _]]].
  assert (KR : nbound w (fnorm w fRf) (vR K0v)) by apply nbound_cden.
  assert (A : nbound w (fnorm w (fam_dt fRf) * fnorm w (fam_dt fRf) + fnorm w (fam_dt fZf) * fnorm w (fam_dt fZf))
                (vdot (vdt K0v) (vdt K0v))).
  { unfold vdot, vdt. cbn [vR vZ K0v]. apply nbound_fadd; apply nbound_fmul; try exact Hw'; apply dt_cden_nb. }
  unfold errF_R, errF_Z, defU, defG, lj.
  refine (conj _ (conj _ (conj _ _))).
  - apply nbound_fsub; apply nbound_fmul; try exact Hw'; try assumption. apply lc_cden_nb.
  - apply nbound_fsub; apply nbound_fmul; try exact Hw'; try assumption. apply lc_cden_nb.
  - apply nbound_fsub; [apply nbound_fone |]. apply nbound_fmul; assumption.
  - apply nbound_fsub; [apply nbound_fone |]. apply nbound_fmul; [exact Hw' | | exact HG].
    apply nbound_fmul; assumption.
Qed.

End Ref.
