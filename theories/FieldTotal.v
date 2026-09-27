(** The field of all the images between two tori.

    Each component of the total jet is P times the projection onto one field
    period of a symmetrised sum over the base sources: the component of each
    source plus or minus its reflection ([ssum], [tot_R], ...). Between two
    stellarator-symmetric tori K and K' of the field period, the second-order
    remainder of each component of the total field is the same projection of
    the symmetrised sum of the remainders of the sources ([tot_r2_R], ...),
    and the change of each derivative is the projection of the symmetrised
    sum of their changes ([tot_d_RR], ...); their norms are at most twice P
    times the sums of the norms over the sources. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity
  FourierDFT FourierCanon FourierPer FourierSym KAMVec KAMFin KAMPer Hypotheses Invariance CoilSym
  FieldKern FieldFam FieldModel FieldTaylor.
Import ListNotations.
Local Open Scope R_scope.

(** * Symmetrised sums over the base sources *)

Definition ssum (sg : R) (g : src * fser -> fser) (l : list (src * fser)) : fser :=
  fold_right (fun sy acc => fadd (fadd (g sy) (fscal sg (frefl (g sy)))) acc) fzero l.

Lemma ssum_cons (sg : R) (g : src * fser -> fser) (sy : src * fser) (l : list (src * fser)) :
  ssum sg g (sy :: l) = fadd (fadd (g sy) (fscal sg (frefl (g sy)))) (ssum sg g l).
Proof. reflexivity. Qed.

Lemma ssum_fin (rho sg : R) (g : src * fser -> fser) (l : list (src * fser)) :
  List.Forall (fun sy => fin rho (g sy)) l -> fin rho (ssum sg g l).
Proof.
  intros H. induction H as [| sy l' Hg _ IH]; [exists 0; apply nbound_fzero |].
  rewrite ssum_cons. apply fin_fadd; [apply fin_fadd; [exact Hg | apply fin_fscal, fin_frefl, Hg] | exact IH].
Qed.

Lemma ssum_val (sg : R) (g : src * fser -> fser) (l : list (src * fser)) (t p : R) :
  List.Forall (fun sy => fin 0 (g sy)) l ->
  feval (ssum sg g l) t p = lsum (fun sy => feval (g sy) t p + sg * feval (g sy) (- t) (- p)) l.
Proof.
  intros H. induction H as [| sy l' Hg Hl IH]; [apply feval_fzero' |].
  rewrite ssum_cons. unfold lsum. simpl. fold (lsum (fun sy => feval (g sy) t p + sg * feval (g sy) (- t) (- p)) l').
  assert (Fr : fin 0 (fscal sg (frefl (g sy)))) by (apply fin_fscal, fin_frefl, Hg).
  rewrite (feval_fadd' t p _ _ (fin_fadd 0 _ _ Hg Fr) (ssum_fin 0 sg g l' Hl)),
    (feval_fadd' t p _ _ Hg Fr), (feval_fscal' t p _ _ (fin_frefl _ _ Hg)), feval_frefl, IH.
  reflexivity.
Qed.

Lemma ssum_nb (rho sg : R) (g : src * fser -> fser) (M : src * fser -> R) (l : list (src * fser)) :
  List.Forall (fun sy => nbound rho (M sy) (g sy)) l ->
  nbound rho ((1 + Rabs sg) * lsum M l) (ssum sg g l).
Proof.
  intros H. induction H as [| sy l' Hg _ IH].
  - unfold lsum. simpl. rewrite Rmult_0_r. apply nbound_fzero.
  - rewrite ssum_cons. unfold lsum. simpl. fold (lsum M l').
    replace ((1 + Rabs sg) * (M sy + lsum M l')) with (M sy + Rabs sg * M sy + (1 + Rabs sg) * lsum M l')
      by ring.
    apply nbound_fadd; [apply nbound_fadd; [exact Hg | apply nbound_fscal, nbound_frefl, Hg] | exact IH].
Qed.

Lemma ssum_canon (sg : R) (g : src * fser -> fser) (l : list (src * fser)) :
  List.Forall (fun sy => is_canon (g sy)) l -> is_canon (ssum sg g l).
Proof.
  intros H. induction H as [| sy l' Hg _ IH]; [apply fzero_canon |].
  rewrite ssum_cons. apply fadd_canon; [apply fadd_canon; [exact Hg | apply fscal_canon, frefl_canon, Hg] | exact IH].
Qed.

Lemma ssum_fsub (sg : R) (g1 g2 : src * fser -> fser) (l : list (src * fser)) :
  feq (fsub (ssum sg g1 l) (ssum sg g2 l)) (ssum sg (fun sy => fsub (g1 sy) (g2 sy)) l).
Proof.
  induction l as [| sy l IH]; intros m n; simpl; [split; ring |].
  destruct (IH m n) as [A B]. simpl in A, B. split; [rewrite <- A | rewrite <- B]; ring.
Qed.

(** * The components of the total jet as symmetrised sums *)

Ltac ssum_ind l K :=
  let IH := fresh "IH" in let sy := fresh "sy" in let tl := fresh "tl" in
  induction l as [| sy tl IH]; intros m n;
  [cbn [fc fs jR jP jZ jR_R jR_Z jP_R jP_Z jZ_R jZ_Z srcjets jzero ssum fold_right fzero]; split; ring |];
  destruct (IH m n) as [A B];
  change (srcjets (sy :: tl) K) with (jadd (symjet (srcjet (fst sy) (snd sy) K)) (srcjets tl K));
  rewrite ssum_cons;
  cbn [fc fs jR jP jZ jR_R jR_Z jP_R jP_Z jZ_R jZ_Z jadd jmap2 symjet srcjet fadd fsub fscal frefl];
  split; [rewrite A | rewrite B]; ring.

Section Comp.

Variables (K : vf) (l : list (src * fser)).

Definition sfam (f : src -> fser -> vf -> fser) (K : vf) : src * fser -> fser :=
  fun sy => f (fst sy) (snd sy) K.

Lemma sj_R : feq (jR (srcjets l K)) (ssum (-1) (sfam FR K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_P : feq (jP (srcjets l K)) (ssum 1 (sfam FP K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_Z : feq (jZ (srcjets l K)) (ssum 1 (sfam FZ K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_RR : feq (jR_R (srcjets l K)) (ssum (-1) (sfam FR_R K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_RZ : feq (jR_Z (srcjets l K)) (ssum 1 (sfam FR_Z K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_PR : feq (jP_R (srcjets l K)) (ssum 1 (sfam FP_R K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_PZ : feq (jP_Z (srcjets l K)) (ssum (-1) (sfam FP_Z K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_ZR : feq (jZ_R (srcjets l K)) (ssum 1 (sfam FZ_R K) l). Proof. unfold sfam. ssum_ind l K. Qed.
Lemma sj_ZZ : feq (jZ_Z (srcjets l K)) (ssum (-1) (sfam FZ_Z K) l). Proof. unfold sfam. ssum_ind l K. Qed.

End Comp.

(** * P times the projection of a symmetrised sum *)

Definition tsum (P : Z) (sg : R) (g : src * fser -> fser) (l : list (src * fser)) : fser :=
  fscal (IZR P) (fproj P (ssum sg g l)).

Lemma tsum_congr (P : Z) (u v : fser) : feq u v -> feq (fscal (IZR P) (fproj P u)) (fscal (IZR P) (fproj P v)).
Proof. intros H m n. destruct (H m n) as [A B]. simpl. rewrite A, B. split; reflexivity. Qed.

Section TotComp.

Variables (P : Z) (K : vf) (l : list (src * fser)).

Lemma tot_R : feq (jR (tot P l K)) (tsum P (-1) (sfam FR K) l). Proof. exact (tsum_congr P _ _ (sj_R K l)). Qed.
Lemma tot_P : feq (jP (tot P l K)) (tsum P 1 (sfam FP K) l). Proof. exact (tsum_congr P _ _ (sj_P K l)). Qed.
Lemma tot_Z : feq (jZ (tot P l K)) (tsum P 1 (sfam FZ K) l). Proof. exact (tsum_congr P _ _ (sj_Z K l)). Qed.
Lemma tot_RR : feq (jR_R (tot P l K)) (tsum P (-1) (sfam FR_R K) l).
Proof. exact (tsum_congr P _ _ (sj_RR K l)). Qed.
Lemma tot_RZ : feq (jR_Z (tot P l K)) (tsum P 1 (sfam FR_Z K) l). Proof. exact (tsum_congr P _ _ (sj_RZ K l)). Qed.
Lemma tot_PR : feq (jP_R (tot P l K)) (tsum P 1 (sfam FP_R K) l). Proof. exact (tsum_congr P _ _ (sj_PR K l)). Qed.
Lemma tot_PZ : feq (jP_Z (tot P l K)) (tsum P (-1) (sfam FP_Z K) l).
Proof. exact (tsum_congr P _ _ (sj_PZ K l)). Qed.
Lemma tot_ZR : feq (jZ_R (tot P l K)) (tsum P 1 (sfam FZ_R K) l). Proof. exact (tsum_congr P _ _ (sj_ZR K l)). Qed.
Lemma tot_ZZ : feq (jZ_Z (tot P l K)) (tsum P (-1) (sfam FZ_Z K) l).
Proof. exact (tsum_congr P _ _ (sj_ZZ K l)). Qed.

End TotComp.

Lemma tsum_fin (rho : R) (P : Z) (sg : R) (g : src * fser -> fser) (l : list (src * fser)) :
  List.Forall (fun sy => fin rho (g sy)) l -> fin rho (tsum P sg g l).
Proof. intros H. unfold tsum. apply fin_fscal. destruct (ssum_fin rho sg g l H) as [M HM]. exists M. apply nbound_fproj, HM. Qed.

Lemma tsum_nb (rho : R) (P : Z) (sg : R) (g : src * fser -> fser) (M : src * fser -> R) (l : list (src * fser)) :
  List.Forall (fun sy => nbound rho (M sy) (g sy)) l ->
  nbound rho (Rabs (IZR P) * ((1 + Rabs sg) * lsum M l)) (tsum P sg g l).
Proof. intros H. unfold tsum. apply nbound_fscal, nbound_fproj, ssum_nb, H. Qed.

Lemma tsum_canon (P : Z) (sg : R) (g : src * fser -> fser) (l : list (src * fser)) :
  (0 < P)%Z -> List.Forall (fun sy => is_canon (g sy)) l -> is_canon (tsum P sg g l).
Proof. intros HP H. unfold tsum. apply fscal_canon, fproj_canon; [exact HP | apply ssum_canon, H]. Qed.

Lemma tsum_val (P : Z) (sg : R) (g : src * fser -> fser) (l : list (src * fser)) (t p : R) :
  (0 < P)%Z -> List.Forall (fun sy => fin 0 (g sy)) l ->
  feval (tsum P sg g l) t p
  = fsum (fun k => lsum (fun sy => feval (g sy) t (p + INR k * (2 * PI / IZR P))
                                    + sg * feval (g sy) (- t) (- (p + INR k * (2 * PI / IZR P)))) l)
         (Z.to_nat P).
Proof.
  intros HP H. unfold tsum. rewrite (Epr P HP _ t p (ssum_fin 0 sg g l H)). apply fsum_ext. intros k.
  cbv beta. apply ssum_val, H.
Qed.

Lemma lsum_lin4 {A : Type} (a b c d : A -> R) (x y : R) (l : list A) :
  lsum (fun s => a s - b s - (c s * x + d s * y)) l = lsum a l - lsum b l - (lsum c l * x + lsum d l * y).
Proof. unfold lsum. induction l as [| s l IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fsum_lin4 (a b c d : nat -> R) (x y : R) (n : nat) :
  fsum (fun k => a k - b k - (c k * x + d k * y)) n = fsum a n - fsum b n - (fsum c n * x + fsum d n * y).
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma lsum_Forall {A : Type} (f g : A -> R) (l : list A) :
  List.Forall (fun a => f a = g a) l -> lsum f l = lsum g l.
Proof. intros H. unfold lsum. induction H as [| a l' E _ IH]; simpl; [reflexivity | rewrite E, IH; reflexivity]. Qed.

Lemma fin_feq (rho : R) (u v : fser) : feq u v -> fin rho v -> fin rho u.
Proof. intros E [M H]. exists M. exact (nbound_feq rho M v u (feq_sym _ _ E) H). Qed.

(** * The remainder of the total field between two tori *)

Section TotR2.

Variables (P : Z) (w : R) (K K' : vf) (l : list (src * fser)).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hw : 0 < w.
Hypothesis SK : vsym K.
Hypothesis SK' : vsym K'.
Hypothesis QK : vper P K.
Hypothesis QK' : vper P K'.
Hypothesis FK : vfin w K.
Hypothesis FK' : vfin w K'.

Lemma F_tdR : fin w (tdR K K'). Proof. unfold tdR. apply fin_fsub; [exact (proj1 FK') | exact (proj1 FK)]. Qed.
Lemma F_tdZ : fin w (tdZ K K'). Proof. unfold tdZ. apply fin_fsub; [exact (proj2 FK') | exact (proj2 FK)]. Qed.

Lemma f0w (u : fser) : fin w u -> fin 0 u. Proof. apply fin_mono. lra. Qed.

Lemma tdR_sym (t p : R) (k : nat) :
  feval (tdR K K') t (p + INR k * (2 * PI / IZR P)) = feval (tdR K K') t p /\
  feval (tdR K K') (- t) (- (p + INR k * (2 * PI / IZR P))) = feval (tdR K K') t p.
Proof.
  assert (Q : is_per P (tdR K K')) by (unfold tdR; apply fsub_per; [exact (proj1 QK') | exact (proj1 QK)]).
  assert (E : is_even (tdR K K')) by (unfold tdR; apply fsub_even; [exact (proj1 SK') | exact (proj1 SK)]).
  rewrite (feval_even_refl _ _ _ E). split; apply feval_per_shift; assumption.
Qed.

Lemma tdZ_sym (t p : R) (k : nat) :
  feval (tdZ K K') t (p + INR k * (2 * PI / IZR P)) = feval (tdZ K K') t p /\
  feval (tdZ K K') (- t) (- (p + INR k * (2 * PI / IZR P))) = - feval (tdZ K K') t p.
Proof.
  assert (Q : is_per P (tdZ K K')) by (unfold tdZ; apply fsub_per; [exact (proj2 QK') | exact (proj2 QK)]).
  assert (O : is_odd (tdZ K K')) by (unfold tdZ; apply fsub_odd; [exact (proj2 SK') | exact (proj2 SK)]).
  rewrite (feval_odd_refl _ _ _ (f0w _ F_tdZ) O). split; [| f_equal]; apply feval_per_shift; assumption.
Qed.

Theorem tot_r2_gen (sg sgZ : R) (F F' FRd FZd r2 : src * fser -> fser) (BF BF' BR BZ : fser) :
  sgZ = - sg ->
  feq BF' (tsum P sg F' l) -> feq BF (tsum P sg F l) -> feq BR (tsum P sg FRd l) -> feq BZ (tsum P sgZ FZd l) ->
  List.Forall (fun sy => fin w (F sy) /\ fin w (F' sy) /\ fin w (FRd sy) /\ fin w (FZd sy) /\ fin w (r2 sy) /\
     (forall t p, feval (r2 sy) t p = feval (F' sy) t p - feval (F sy) t p
                  - (feval (FRd sy) t p * feval (tdR K K') t p + feval (FZd sy) t p * feval (tdZ K K') t p))) l ->
  forall t p,
  feval (fsub (fsub BF' BF) (fadd (fmul BR (tdR K K')) (fmul BZ (tdZ K K')))) t p = feval (tsum P sg r2 l) t p.
Proof.
  intros HsZ E' E ER EZ Hl t p.
  assert (A : List.Forall (fun sy => fin 0 (F sy)) l) by (eapply Forall_impl; [| exact Hl]; intros sy H; apply f0w, H).
  assert (A' : List.Forall (fun sy => fin 0 (F' sy)) l)
    by (eapply Forall_impl; [| exact Hl]; intros sy H; apply f0w, H).
  assert (AR : List.Forall (fun sy => fin 0 (FRd sy)) l)
    by (eapply Forall_impl; [| exact Hl]; intros sy H; apply f0w, H).
  assert (AZ : List.Forall (fun sy => fin 0 (FZd sy)) l)
    by (eapply Forall_impl; [| exact Hl]; intros sy H; apply f0w, H).
  assert (A2 : List.Forall (fun sy => fin 0 (r2 sy)) l)
    by (eapply Forall_impl; [| exact Hl]; intros sy H; apply f0w, H).
  pose proof (fin_feq 0 _ _ E' (tsum_fin 0 P sg F' l A')) as G'.
  pose proof (fin_feq 0 _ _ E (tsum_fin 0 P sg F l A)) as G.
  pose proof (fin_feq 0 _ _ ER (tsum_fin 0 P sg FRd l AR)) as GR.
  pose proof (fin_feq 0 _ _ EZ (tsum_fin 0 P sgZ FZd l AZ)) as GZ.
  pose proof (f0w _ F_tdR) as DR. pose proof (f0w _ F_tdZ) as DZ.
  rewrite (feval_fsub' t p _ _ (fin_fsub 0 _ _ G' G) (fin_fadd 0 _ _ (fin_fmul 0 _ _ (Rle_refl 0) GR DR)
                                                        (fin_fmul 0 _ _ (Rle_refl 0) GZ DZ))),
    (feval_fsub' t p _ _ G' G), (feval_fadd' t p _ _ (fin_fmul 0 _ _ (Rle_refl 0) GR DR)
                                   (fin_fmul 0 _ _ (Rle_refl 0) GZ DZ)),
    (feval_fmul' t p _ _ GR DR), (feval_fmul' t p _ _ GZ DZ).
  rewrite (feval_feq _ _ t p E'), (feval_feq _ _ t p E), (feval_feq _ _ t p ER), (feval_feq _ _ t p EZ).
  rewrite !tsum_val by assumption.
  set (x := feval (tdR K K') t p). set (y := feval (tdZ K K') t p).
  rewrite <- fsum_lin4. apply fsum_ext. intros k.
  rewrite <- lsum_lin4. apply lsum_Forall.
  eapply Forall_impl; [| exact Hl]. intros sy [_ [_ [_ [_ [_ H2]]]]].
  destruct (tdR_sym t p k) as [R1 R2]. destruct (tdZ_sym t p k) as [Z1 Z2].
  rewrite !H2, R1, R2, Z1, Z2. fold x y. rewrite HsZ. ring.
Qed.

End TotR2.

(** * The data of each source on a torus *)

(** The seed of the source converges along K, positively, and the source's
    distance families and inverse square root have the given norms, small
    enough for the split of the inverse square root at step hm. *)
Definition src_ok (w hm cs : R) (K : vf) (sy : src * fser) (r1 r2 r3 yb : R) : Prop :=
  isq_ok w (fq (fst sy) K) (snd sy) /\ 0 < feval (fy (fst sy) (snd sy) K) 0 0 /\
  nbound w r1 (fr1 (fst sy) K) /\ nbound w r2 (fr2 (fst sy) K) /\ nbound w r3 (fr3 (fst sy) K) /\
  nbound w yb (fy (fst sy) (snd sy) K) /\
  hm * hm * tT1 hm r1 r2 r3 yb cs < 1 /\ hm * tP1 hm r1 r2 r3 yb cs / 2 + hm * hm * tRB hm r1 r2 r3 yb cs < 1.

Lemma fsub_congr (u u' v v' : fser) : feq u u' -> feq v v' -> feq (fsub u v) (fsub u' v').
Proof. intros A B m n. destruct (A m n) as [A1 A2]. destruct (B m n) as [B1 B2]. simpl. rewrite A1, A2, B1, B2. auto. Qed.

Lemma tsum_fsub (P : Z) (sg : R) (g1 g2 : src * fser -> fser) (l : list (src * fser)) :
  feq (fsub (tsum P sg g1 l) (tsum P sg g2 l)) (tsum P sg (fun sy => fsub (g1 sy) (g2 sy)) l).
Proof.
  eapply feq_trans; [| apply tsum_congr, ssum_fsub].
  intros m n. unfold tsum. simpl. destruct (Z.eqb _ _); split; ring.
Qed.

Section TotBounds.

Variables (P : Z) (w h hm cs : R) (K K' : vf) (l : list (src * fser)).
Variables (dr1 dr2 dr3 dyb : src * fser -> R).
Hypothesis Hcs : nbound w cs cosf /\ nbound w cs sinf.
Hypothesis HP : (0 < P)%Z.
Hypothesis Hw : 0 < w.
Hypothesis SK : vsym K.
Hypothesis SK' : vsym K'.
Hypothesis QK : vper P K.
Hypothesis QK' : vper P K'.
Hypothesis FK : vfin w K.
Hypothesis FK' : vfin w K'.
Hypothesis CK : vcanon K.
Hypothesis CK' : vcanon K'.
Hypothesis Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Hypothesis Hh : 0 <= h.
Hypothesis Hhm : h <= hm.
Hypothesis HD : vbound w h (vsub K' K).
Hypothesis Hsrc : List.Forall (fun sy => src_ok w hm cs K sy (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) /\
                     isq_ok w (fq (fst sy) K') (snd sy) /\ 0 < feval (fy (fst sy) (snd sy) K') 0 0) l.

Lemma Hsrc_all : List.Forall (fun sy => src_ok w hm cs K sy (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) /\
                     isq_ok w (fq (fst sy) K') (snd sy) /\ 0 < feval (fy (fst sy) (snd sy) K') 0 0 /\
                     is_canon (snd sy)) l.
Proof.
  apply Forall_forall. intros sy I. rewrite Forall_forall in Hsrc, Cl.
  destruct (Hsrc sy I) as [A [B C]]. exact (conj A (conj B (conj C (Cl sy I)))).
Qed.

Lemma srcs_K : srcs_ok w l K.
Proof. unfold srcs_ok. eapply Forall_impl; [| exact Hsrc]. intros sy [[A [B _]] _]. exact (conj A B). Qed.

Lemma srcs_K' : srcs_ok w l K'.
Proof. unfold srcs_ok. eapply Forall_impl; [| exact Hsrc]. intros sy [_ [A B]]. exact (conj A B). Qed.

Definition TR2R : R := Rabs (IZR P) * (2 * lsum (fun sy => tRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l).
Definition TR2Z : R := Rabs (IZR P) * (2 * lsum (fun sy => tRZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l).

Lemma lsum_scal {A : Type} (c : R) (f : A -> R) (l0 : list A) : lsum (fun a => c * f a) l0 = c * lsum f l0.
Proof. unfold lsum. induction l0 as [| a l0 IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma Rabs_m1' : Rabs (-1) = 1. Proof. rewrite Rabs_left by lra. ring. Qed.
Lemma one_p_abs (sg : R) : sg = 1 \/ sg = -1 -> 1 + Rabs sg = 2.
Proof. intros [-> | ->]; [rewrite Rabs_R1 | rewrite Rabs_m1']; ring. Qed.

(** The per-source remainder data. *)
Lemma src_data (sy : src * fser) : In sy l ->
  (nbound w (h * h * tRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (r2R (fst sy) (snd sy) K K') /\
   nbound w (h * h * tRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (r2P (fst sy) (snd sy) K K') /\
   nbound w (h * h * tRZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (r2Z (fst sy) (snd sy) K K')) /\
  (nbound w (h * tLRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (dFRR (fst sy) (snd sy) K K') /\
   nbound w (h * tLRZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (dFRZ (fst sy) (snd sy) K K') /\
   nbound w (h * tLRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (dFPR (fst sy) (snd sy) K K') /\
   nbound w (h * tLRZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (dFPZ (fst sy) (snd sy) K K') /\
   nbound w (h * tLZRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (dFZR (fst sy) (snd sy) K K') /\
   nbound w (h * tLZZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) (dFZZ (fst sy) (snd sy) K K')).
Proof.
  intros I. pose proof Hsrc_all as H. rewrite Forall_forall in H.
  destruct (H sy I) as [[Q [Y0 [B1 [B2 [B3 [BY [S1 S2]]]]]]] [Q' [Y0' CY]]].
  split.
  - exact (src_r2 (fst sy) (snd sy) K K' w Hw FK FK' Q Q' Y0 Y0' CK CY h hm _ _ _ _ Hh Hhm HD B1 B2 B3 BY cs Hcs CK' S1 S2).
  - exact (src_lip (fst sy) (snd sy) K K' w Hw FK FK' Q Q' Y0 Y0' CK CY h hm _ _ _ _ Hh Hhm HD B1 B2 B3 BY cs Hcs CK' S1 S2).
Qed.

Lemma ev_src (sy : src * fser) (Kx : vf) : vfin w Kx -> isq_ok w (fq (fst sy) Kx) (snd sy) ->
  0 < feval (fy (fst sy) (snd sy) Kx) 0 0 ->
  fin w (FR (fst sy) (snd sy) Kx) /\ fin w (FP (fst sy) (snd sy) Kx) /\ fin w (FZ (fst sy) (snd sy) Kx) /\
  fin w (FR_R (fst sy) (snd sy) Kx) /\ fin w (FR_Z (fst sy) (snd sy) Kx) /\
  fin w (FP_R (fst sy) (snd sy) Kx) /\ fin w (FP_Z (fst sy) (snd sy) Kx) /\
  fin w (FZ_R (fst sy) (snd sy) Kx) /\ fin w (FZ_Z (fst sy) (snd sy) Kx).
Proof.
  intros F Q Y0. destruct (srcjet_fin (fst sy) (snd sy) Kx w Hw F Q Y0)
    as [A1 [A2 [A3 [A4 [A5 [_ [A7 [A8 [_ [A10 [A11 _]]]]]]]]]]].
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A7 (conj A8 (conj A10 A11)))))))).
Qed.

Lemma f0w' (u : fser) : fin w u -> fin 0 u. Proof. apply fin_mono. lra. Qed.

Lemma Hw0' : 0 <= w. Proof. lra. Qed.

Lemma rel_eval (a' a bR bZ dR dZ : fser) (t p : R) :
  fin 0 a' -> fin 0 a -> fin 0 bR -> fin 0 bZ -> fin 0 dR -> fin 0 dZ ->
  feval (fsub (fsub a' a) (fadd (fmul bR dR) (fmul bZ dZ))) t p
  = feval a' t p - feval a t p - (feval bR t p * feval dR t p + feval bZ t p * feval dZ t p).
Proof.
  intros F1 F2 F3 F4 F5 F6.
  assert (M1 : fin 0 (fmul bR dR)) by (apply fin_fmul; [lra | assumption | assumption]).
  assert (M2 : fin 0 (fmul bZ dZ)) by (apply fin_fmul; [lra | assumption | assumption]).
  rewrite (feval_fsub' t p _ _ (fin_fsub 0 _ _ F1 F2) (fin_fadd 0 _ _ M1 M2)), (feval_fsub' t p _ _ F1 F2),
    (feval_fadd' t p _ _ M1 M2), (feval_fmul' t p _ _ F3 F5), (feval_fmul' t p _ _ F4 F6).
  reflexivity.
Qed.

(** The per-source remainders are the differences, point by point. *)
Lemma src_rel (sy : src * fser) : In sy l ->
  let sc := fst sy in let Y := snd sy in
  (forall t p, feval (r2R sc Y K K') t p = feval (FR sc Y K') t p - feval (FR sc Y K) t p
     - (feval (FR_R sc Y K) t p * feval (tdR K K') t p + feval (FR_Z sc Y K) t p * feval (tdZ K K') t p)) /\
  (forall t p, feval (r2P sc Y K K') t p = feval (FP sc Y K') t p - feval (FP sc Y K) t p
     - (feval (FP_R sc Y K) t p * feval (tdR K K') t p + feval (FP_Z sc Y K) t p * feval (tdZ K K') t p)) /\
  (forall t p, feval (r2Z sc Y K K') t p = feval (FZ sc Y K') t p - feval (FZ sc Y K) t p
     - (feval (FZ_R sc Y K) t p * feval (tdR K K') t p + feval (FZ_Z sc Y K) t p * feval (tdZ K K') t p)).
Proof.
  intros I sc Y. pose proof Hsrc_all as H. rewrite Forall_forall in H.
  destruct (H sy I) as [[Q [Y0 _]] [Q' [Y0' _]]].
  destruct (ev_src sy K FK Q Y0) as [A1 [A2 [A3 [A4 [A5 [A7 [A8 [A10 A11]]]]]]]].
  destruct (ev_src sy K' FK' Q' Y0') as [B1 [B2 [B3 _]]].
  pose proof (f0w' _ (F_tdR w K K' FK FK')) as DR. pose proof (f0w' _ (F_tdZ w K K' FK FK')) as DZ.
  refine (conj _ (conj _ _)); intros t p; unfold r2R, r2P, r2Z.
  - exact (rel_eval _ _ _ _ _ _ t p (f0w' _ B1) (f0w' _ A1) (f0w' _ A4) (f0w' _ A5) DR DZ).
  - exact (rel_eval _ _ _ _ _ _ t p (f0w' _ B2) (f0w' _ A2) (f0w' _ A7) (f0w' _ A8) DR DZ).
  - exact (rel_eval _ _ _ _ _ _ t p (f0w' _ B3) (f0w' _ A3) (f0w' _ A10) (f0w' _ A11) DR DZ).
Qed.

Lemma lsum_hh (c : R) (f : src * fser -> R) :
  Rabs (IZR P) * ((1 + Rabs (-1)) * lsum (fun sy => c * f sy) l) = c * (Rabs (IZR P) * (2 * lsum f l)) /\
  Rabs (IZR P) * ((1 + Rabs 1) * lsum (fun sy => c * f sy) l) = c * (Rabs (IZR P) * (2 * lsum f l)).
Proof. rewrite lsum_scal, Rabs_m1', Rabs_R1. split; ring. Qed.

Lemma tot_jc : jcanon (tot P l K) /\ jcanon (tot P l K').
Proof. split; apply tot_canon; assumption. Qed.

Lemma tot_jf : jfin w (tot P l K) /\ jfin w (tot P l K').
Proof. split; apply tot_fin; try assumption; [exact srcs_K | exact srcs_K']. Qed.

Lemma C_td : is_canon (tdR K K') /\ is_canon (tdZ K K').
Proof.
  destruct CK as [A B]. destruct CK' as [A' B']. unfold tdR, tdZ. split; apply fsub_canon; assumption.
Qed.

Lemma nb0 (u : fser) : fin w u -> exists M, nbound 0 M u.
Proof. intros F. destruct (f0w' _ F) as [M H]. exists M. exact H. Qed.

(** The second-order remainder of the total field, in each component. *)
Theorem tot_r2 :
  nbound w (h * h * TR2R) (fsub (fsub (jR (tot P l K')) (jR (tot P l K)))
                               (fadd (fmul (jR_R (tot P l K)) (tdR K K')) (fmul (jR_Z (tot P l K)) (tdZ K K')))) /\
  nbound w (h * h * TR2R) (fsub (fsub (jP (tot P l K')) (jP (tot P l K)))
                               (fadd (fmul (jP_R (tot P l K)) (tdR K K')) (fmul (jP_Z (tot P l K)) (tdZ K K')))) /\
  nbound w (h * h * TR2Z) (fsub (fsub (jZ (tot P l K')) (jZ (tot P l K)))
                               (fadd (fmul (jZ_R (tot P l K)) (tdR K K')) (fmul (jZ_Z (tot P l K)) (tdZ K K')))).
Proof.
  destruct tot_jc as [[C1 [C2 [C3 [C4 [C5 [_ [C7 [C8 [_ [C10 [C11 _]]]]]]]]]]] [D1 [D2 [D3 _]]]].
  destruct tot_jf as [[F1 [F2 [F3 [F4 [F5 [_ [F7 [F8 [_ [F10 [F11 _]]]]]]]]]]] [G1 [G2 [G3 _]]]].
  destruct C_td as [CdR CdZ]. pose proof (F_tdR w K K' FK FK') as FdR. pose proof (F_tdZ w K K' FK FK') as FdZ.
  assert (Hin : forall sy, In sy l -> fin w (r2R (fst sy) (snd sy) K K') /\ fin w (r2P (fst sy) (snd sy) K K') /\
                                      fin w (r2Z (fst sy) (snd sy) K K') /\
                                      is_canon (r2R (fst sy) (snd sy) K K') /\ is_canon (r2P (fst sy) (snd sy) K K') /\
                                      is_canon (r2Z (fst sy) (snd sy) K K')).
  { intros sy I. destruct (src_data sy I) as [[R1 [R2 R3]] _].
    pose proof Hsrc_all as H. rewrite Forall_forall in H. destruct (H sy I) as [_ [_ [_ CY]]].
    destruct (C_r2 (fst sy) (snd sy) K K' CK CY CK') as [E1 [E2 E3]].
    refine (conj _ (conj _ (conj _ (conj E1 (conj E2 E3))))); eexists; eassumption. }
  assert (Hsd : forall sy, In sy l -> _) by (intros sy I; exact (proj1 (src_data sy I))).
  assert (Hr : forall sy, In sy l -> _) by (intros sy I; exact (src_rel sy I)).
  assert (He : forall sy, In sy l -> _) by (intros sy I; pose proof Hsrc_all as H; rewrite Forall_forall in H;
    destruct (H sy I) as [[Q [Y0 _]] [Q' [Y0' _]]]; exact (conj (ev_src sy K FK Q Y0) (ev_src sy K' FK' Q' Y0'))).
  pose proof (lsum_hh (h * h) (fun sy => tRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs)) as [LR LR'].
  pose proof (lsum_hh (h * h) (fun sy => tRZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs)) as [_ LZ].
  assert (Fin : forall (a' a bR bZ : fser), fin w a' -> fin w a -> fin w bR -> fin w bZ ->
             fin w (fsub (fsub a' a) (fadd (fmul bR (tdR K K')) (fmul bZ (tdZ K K'))))).
  { intros a' a bR bZ A1 A2 A3 A4.
    exact (fin_fsub w _ _ (fin_fsub w _ _ A1 A2) (fin_fadd w _ _ (fin_fmul w _ _ Hw0' A3 FdR) (fin_fmul w _ _ Hw0' A4 FdZ))). }
  assert (Can : forall (a' a bR bZ : fser), is_canon a' -> is_canon a -> is_canon bR -> is_canon bZ ->
             is_canon (fsub (fsub a' a) (fadd (fmul bR (tdR K K')) (fmul bZ (tdZ K K'))))).
  { intros a' a bR bZ A1 A2 A3 A4. apply fsub_canon; [apply fsub_canon; assumption |].
    apply fadd_canon; apply fmul_canon; assumption. }
  refine (conj _ (conj _ _)).
  - assert (Bd : nbound w (h * h * TR2R) (tsum P (-1) (fun sy => r2R (fst sy) (snd sy) K K') l)).
    { unfold TR2R. rewrite <- LR. apply tsum_nb. apply Forall_forall. intros sy I. exact (proj1 (Hsd sy I)). }
    destruct (nb0 _ (Fin _ _ _ _ G1 F1 F4 F5)) as [M1 N1].
    apply (nbound_feq w _ _ _ (feq_sym _ _ (canon_feq _ _ M1 _ (Can _ _ _ _ D1 C1 C4 C5)
             (tsum_canon P (-1) _ l HP (proj2 (Forall_forall _ l)
                (fun sy I => proj1 (proj2 (proj2 (proj2 (Hin sy I))))))) N1 (nbound_mono w 0 _ _ Hw0' Bd)
             (fun t p => tot_r2_gen P w K K' l HP Hw SK SK' QK QK' FK FK' (-1) 1
               (sfam FR K) (sfam FR K') (sfam FR_R K) (sfam FR_Z K) (fun sy => r2R (fst sy) (snd sy) K K') _ _ _ _
               ltac:(lra) (tot_R P K' l) (tot_R P K l) (tot_RR P K l) (tot_RZ P K l)
               (proj2 (Forall_forall _ l) (fun sy I =>
                  conj (proj1 (proj1 (He sy I))) (conj (proj1 (proj2 (He sy I)))
                    (conj (proj1 (proj2 (proj2 (proj2 (proj1 (He sy I))))))
                      (conj (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (He sy I)))))))
                        (conj (proj1 (Hin sy I)) (proj1 (Hr sy I))))))))
               t p)))).
    exact Bd.
  - assert (Bd : nbound w (h * h * TR2R) (tsum P 1 (fun sy => r2P (fst sy) (snd sy) K K') l)).
    { unfold TR2R. rewrite <- LR'. apply tsum_nb. apply Forall_forall. intros sy I. exact (proj1 (proj2 (Hsd sy I))). }
    destruct (nb0 _ (Fin _ _ _ _ G2 F2 F7 F8)) as [M1 N1].
    apply (nbound_feq w _ _ _ (feq_sym _ _ (canon_feq _ _ M1 _ (Can _ _ _ _ D2 C2 C7 C8)
             (tsum_canon P 1 _ l HP (proj2 (Forall_forall _ l)
                (fun sy I => proj1 (proj2 (proj2 (proj2 (proj2 (Hin sy I)))))))) N1 (nbound_mono w 0 _ _ Hw0' Bd)
             (fun t p => tot_r2_gen P w K K' l HP Hw SK SK' QK QK' FK FK' 1 (-1)
               (sfam FP K) (sfam FP K') (sfam FP_R K) (sfam FP_Z K) (fun sy => r2P (fst sy) (snd sy) K K') _ _ _ _
               ltac:(lra) (tot_P P K' l) (tot_P P K l) (tot_PR P K l) (tot_PZ P K l)
               (proj2 (Forall_forall _ l) (fun sy I =>
                  conj (proj1 (proj2 (proj1 (He sy I)))) (conj (proj1 (proj2 (proj2 (He sy I))))
                    (conj (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (He sy I))))))))
                      (conj (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (He sy I)))))))))
                        (conj (proj1 (proj2 (Hin sy I))) (proj1 (proj2 (Hr sy I)))))))))
               t p)))).
    exact Bd.
  - assert (Bd : nbound w (h * h * TR2Z) (tsum P 1 (fun sy => r2Z (fst sy) (snd sy) K K') l)).
    { unfold TR2Z. rewrite <- LZ. apply tsum_nb. apply Forall_forall. intros sy I. exact (proj2 (proj2 (Hsd sy I))). }
    destruct (nb0 _ (Fin _ _ _ _ G3 F3 F10 F11)) as [M1 N1].
    apply (nbound_feq w _ _ _ (feq_sym _ _ (canon_feq _ _ M1 _ (Can _ _ _ _ D3 C3 C10 C11)
             (tsum_canon P 1 _ l HP (proj2 (Forall_forall _ l)
                (fun sy I => proj2 (proj2 (proj2 (proj2 (proj2 (Hin sy I)))))))) N1 (nbound_mono w 0 _ _ Hw0' Bd)
             (fun t p => tot_r2_gen P w K K' l HP Hw SK SK' QK QK' FK FK' 1 (-1)
               (sfam FZ K) (sfam FZ K') (sfam FZ_R K) (sfam FZ_Z K) (fun sy => r2Z (fst sy) (snd sy) K K') _ _ _ _
               ltac:(lra) (tot_Z P K' l) (tot_Z P K l) (tot_ZR P K l) (tot_ZZ P K l)
               (proj2 (Forall_forall _ l) (fun sy I =>
                  conj (proj1 (proj2 (proj2 (proj1 (He sy I))))) (conj (proj1 (proj2 (proj2 (proj2 (He sy I)))))
                    (conj (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (He sy I))))))))))
                      (conj (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (He sy I))))))))))
                        (conj (proj1 (proj2 (proj2 (Hin sy I)))) (proj2 (proj2 (Hr sy I)))))))))
               t p)))).
    exact Bd.
Qed.

Definition TLRR : R := Rabs (IZR P) * (2 * lsum (fun sy => tLRRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l).
Definition TLRZ : R := Rabs (IZR P) * (2 * lsum (fun sy => tLRZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l).
Definition TLZR : R := Rabs (IZR P) * (2 * lsum (fun sy => tLZRb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l).
Definition TLZZ : R := Rabs (IZR P) * (2 * lsum (fun sy => tLZZb (fst sy) hm (dr1 sy) (dr2 sy) (dr3 sy) (dyb sy) cs) l).

(** The change of the derivatives of the total field. *)
Theorem tot_lip :
  nbound w (h * TLRR) (fsub (jR_R (tot P l K')) (jR_R (tot P l K))) /\
  nbound w (h * TLRZ) (fsub (jR_Z (tot P l K')) (jR_Z (tot P l K))) /\
  nbound w (h * TLRR) (fsub (jP_R (tot P l K')) (jP_R (tot P l K))) /\
  nbound w (h * TLRZ) (fsub (jP_Z (tot P l K')) (jP_Z (tot P l K))) /\
  nbound w (h * TLZR) (fsub (jZ_R (tot P l K')) (jZ_R (tot P l K))) /\
  nbound w (h * TLZZ) (fsub (jZ_Z (tot P l K')) (jZ_Z (tot P l K))).
Proof.
  assert (Hsd : forall sy, In sy l -> _) by (intros sy I; exact (proj2 (src_data sy I))).
  assert (T : forall (sg : R) (f : src * fser -> R) (u u' : fser) (g : src -> fser -> vf -> fser),
            (sg = 1 \/ sg = -1) ->
            feq u' (tsum P sg (sfam g K') l) -> feq u (tsum P sg (sfam g K) l) ->
            (forall sy, In sy l -> nbound w (h * f sy) (fsub (g (fst sy) (snd sy) K') (g (fst sy) (snd sy) K))) ->
            nbound w (h * (Rabs (IZR P) * (2 * lsum f l))) (fsub u' u)).
  { intros sg f u u' g Hs E' E Hb.
    apply (nbound_feq w _ (tsum P sg (fun sy => fsub (sfam g K' sy) (sfam g K sy)) l)).
    - apply feq_sym. eapply feq_trans; [apply (fsub_congr _ _ _ _ E' E) |]. apply tsum_fsub.
    - replace (h * (Rabs (IZR P) * (2 * lsum f l))) with (Rabs (IZR P) * ((1 + Rabs sg) * lsum (fun sy => h * f sy) l))
        by (rewrite lsum_scal, (one_p_abs sg Hs); ring).
      apply tsum_nb. apply Forall_forall. exact Hb. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact (T (-1) _ _ _ FR_R (or_intror eq_refl) (tot_RR P K' l) (tot_RR P K l) (fun sy I => proj1 (Hsd sy I))).
  - exact (T 1 _ _ _ FR_Z (or_introl eq_refl) (tot_RZ P K' l) (tot_RZ P K l)
             (fun sy I => proj1 (proj2 (Hsd sy I)))).
  - exact (T 1 _ _ _ FP_R (or_introl eq_refl) (tot_PR P K' l) (tot_PR P K l)
             (fun sy I => proj1 (proj2 (proj2 (Hsd sy I))))).
  - exact (T (-1) _ _ _ FP_Z (or_intror eq_refl) (tot_PZ P K' l) (tot_PZ P K l)
             (fun sy I => proj1 (proj2 (proj2 (proj2 (Hsd sy I)))))).
  - exact (T 1 _ _ _ FZ_R (or_introl eq_refl) (tot_ZR P K' l) (tot_ZR P K l)
             (fun sy I => proj1 (proj2 (proj2 (proj2 (proj2 (Hsd sy I))))))).
  - exact (T (-1) _ _ _ FZ_Z (or_intror eq_refl) (tot_ZZ P K' l) (tot_ZZ P K l)
             (fun sy I => proj2 (proj2 (proj2 (proj2 (proj2 (Hsd sy I))))))).
Qed.

End TotBounds.
