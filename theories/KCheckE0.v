(** The numerators of the error of the first torus and the defects of two
    seeds, on a grid.

    At a point of the torus, the field of the base sources at the P shifts of
    p, point and image, encloses B_R, B_phi and B_Z of the total field
    ([icompv_ok] of KJet.v with [val_R], [val_P], [val_Z] of FieldJetVal.v),
    and with enclosures of R, Z and their t and p derivatives it encloses the
    numerators F_R = B_phi (L K)_R - R B_R and F_Z = B_phi (L K)_Z - R B_Z of
    the error. With enclosures of a seed Ub of 1 / B_phi and a seed gs of
    1 / (B_phi |a|^2), a = d_t K, it also encloses their defects
    1 - B_phi Ub ([defU]) and 1 - B_phi |a|^2 gs ([defG]) ([epoint4_ok]). Row
    by row over a grid it encloses the four at every point ([egrid_ok]), which
    is what the model check of KEngine.v reads. The positivity every value
    needs is formed in the same pass and read from the same grid. *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierInv FourierDFT FourierCanon FourierPer FourierList KAMVec KAMFin KAMPer Hypotheses Invariance
  CoilSym FieldKern FieldFam FieldModel FieldLine FieldJetVal KCheckErr KFix KCheckKern KEngine KGrid KJet.
Import ListNotations.
Local Open Scope R_scope.

(** A family of period P repeats on the grid after one period of M points. *)
Lemma per_grid (Pn N1 M : nat) (u : fser) :
  (0 < Pn)%nat -> (0 < M)%nat -> is_per (Z.of_nat Pn) u ->
  forall a c b, (b < M)%nat ->
  feval u (gpt N1 a) (gpt (Pn * M) (c * M + b)) = feval u (gpt N1 a) (gpt (Pn * M) b).
Proof.
  intros HPn HM Qu a c b Hb.
  assert (E : gpt (Pn * M) (c * M + b) = gpt (Pn * M) b + INR c * (2 * PI / IZR (Z.of_nat Pn))).
  { unfold gpt. rewrite <- INR_IZR_INZ, plus_INR, !mult_INR.
    assert (INR Pn <> 0) by (apply not_0_INR; lia). assert (INR M <> 0) by (apply not_0_INR; lia).
    field. split; assumption. }
  rewrite E. apply feval_per_shift; [lia | exact Qu].
Qed.

(** The numerators are canonical and of period P. *)
Lemma errF_canon (P : Z) (l : list (src * fser)) (om : R) (K : vf) :
  (0 < P)%Z -> vcanon K -> List.Forall (fun sy => is_canon (snd sy)) l ->
  is_canon (errF_R P l om K) /\ is_canon (errF_Z P l om K).
Proof.
  intros HP CK Cl. pose proof (tot_canon P l K HP CK Cl) as C.
  destruct C as [CR [CPh [CZ _]]]. destruct CK as [CKR CKZ].
  unfold errF_R, errF_Z, lj. split; apply fsub_canon; apply fmul_canon; try assumption; apply lc_canon; assumption.
Qed.

Lemma errF_per (P : Z) (l : list (src * fser)) (om : R) (K : vf) :
  (0 < P)%Z -> vper P K -> is_per P (errF_R P l om K) /\ is_per P (errF_Z P l om K).
Proof.
  intros HP [QR QZ]. pose proof (tot_per P l K) as Q. destruct Q as [Q1 [Q2 [Q3 _]]].
  unfold errF_R, errF_Z, lj. split; apply (fsub_per P); apply (fmul_per P HP); try assumption;
    apply (lc_per P); assumption.
Qed.

(** * The defects of the seeds of 1 / B_phi and of 1 / (B_phi |a|^2) *)

Definition defU (P : Z) (l : list (src * fser)) (K : vf) (Ub : fser) : fser :=
  fsub fone (fmul (jP (tot P l K)) Ub).
Definition defG (P : Z) (l : list (src * fser)) (K : vf) (gs : fser) : fser :=
  fsub fone (fmul (fmul (jP (tot P l K)) (vdot (vdt K) (vdt K))) gs).

Lemma def_canon (P : Z) (l : list (src * fser)) (K : vf) (Ub gs : fser) :
  (0 < P)%Z -> vcanon K -> List.Forall (fun sy => is_canon (snd sy)) l -> is_canon Ub -> is_canon gs ->
  is_canon (defU P l K Ub) /\ is_canon (defG P l K gs).
Proof.
  intros HP CK Cl CU Cg. pose proof (tot_canon P l K HP CK Cl) as C.
  destruct C as [_ [CPh _]]. destruct CK as [CKR CKZ].
  unfold defU, defG. split; apply fsub_canon; try apply fone_canon; apply fmul_canon; try assumption.
  apply fmul_canon; [exact CPh |]. apply vdot_canon; split; apply dt_canon; assumption.
Qed.

Lemma def_per (P : Z) (l : list (src * fser)) (K : vf) (Ub gs : fser) :
  (0 < P)%Z -> vper P K -> is_per P Ub -> is_per P gs -> is_per P (defU P l K Ub) /\ is_per P (defG P l K gs).
Proof.
  intros HP [QR QZ] QU Qg. pose proof (tot_per P l K) as Q. destruct Q as [_ [Q2 _]].
  pose proof (fone_per P HP) as Q1.
  unfold defU, defG, vdot, vdt. cbn [vR vZ]. split; apply (fsub_per P); try exact Q1.
  - apply (fmul_per P HP); assumption.
  - apply (fmul_per P HP); [| exact Qg]. apply (fmul_per P HP); [exact Q2 |].
    apply (fadd_per P); apply (fmul_per P HP); apply (dt_per P); assumption.
Qed.

Module E0Ops (J : RI).

Module JO := JetOps J.
Module EN := Engine J.
Import JO JO.KO.

(** * One point *)

(** The flag of positivity, and the numerators F_R, F_Z and the two defects. *)
Definition epoint4 (Ss : list (i3 * i3)) (OM : J.t) (CSk : list (J.t * J.t)) (Rr Zz tR pR tZ pZ Uv Gv : J.t) :
    bool * ((J.t * J.t) * (J.t * J.t)) :=
  let '(ok, (BR, BP, BZ)) := icompvp Ss Rr Zz CSk in
  (ok, ((J.sub (J.mul BP (J.add (J.mul OM tR) pR)) (J.mul Rr BR),
         J.sub (J.mul BP (J.add (J.mul OM tZ) pZ)) (J.mul Rr BZ)),
        (J.sub one (J.mul BP Uv),
         J.sub one (J.mul (J.mul BP (J.add (J.mul tR tR) (J.mul tZ tZ))) Gv)))).

Section Point.

Variables (P : Z) (rho om : R) (K : vf) (l : list (src * fser)) (Ub gs : fser).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.
Hypothesis FU : fin 0 Ub.
Hypothesis Fg : fin 0 gs.

(** The four real values an entry of the grid encloses. *)
Definition e4in (E : (J.t * J.t) * (J.t * J.t)) (t p : R) : Prop :=
  inR (fst (fst E)) (feval (errF_R P l om K) t p) /\ inR (snd (fst E)) (feval (errF_Z P l om K) t p) /\
  inR (fst (snd E)) (feval (defU P l K Ub) t p) /\ inR (snd (snd E)) (feval (defG P l K gs) t p).

Lemma fin_BP : fin 0 (jP (tot P l K)).
Proof. destruct (tot_fin P rho K l Hr FK Hl) as [_ [F _]]. apply (fin_mono rho); [lra | exact F]. Qed.

Lemma feval_defU (t p : R) : feval (defU P l K Ub) t p = 1 - feval (jP (tot P l K)) t p * feval Ub t p.
Proof.
  unfold defU. assert (F1 : fin 0 fone) by (exists 1; apply nbound_fone).
  rewrite (feval_fsub' t p _ _ F1 (fin_fmul 0 _ _ (Rle_refl 0) fin_BP FU)).
  rewrite (feval_fmul' t p _ _ fin_BP FU), feval_fone. reflexivity.
Qed.

Lemma feval_defG (t p : R) :
  feval (defG P l K gs) t p
  = 1 - feval (jP (tot P l K)) t p * (feval (dt (vR K)) t p * feval (dt (vR K)) t p
                                      + feval (dt (vZ K)) t p * feval (dt (vZ K)) t p) * feval gs t p.
Proof.
  unfold defG. assert (F1 : fin 0 fone) by (exists 1; apply nbound_fone).
  assert (FtR : fin 0 (dt (vR K))) by exact (fin_dt0 rho _ Hr (proj1 FK)).
  assert (FtZ : fin 0 (dt (vZ K))) by exact (fin_dt0 rho _ Hr (proj2 FK)).
  assert (Fa : fin 0 (vdot (vdt K) (vdt K))) by (apply fin_vdot; [lra | split; assumption | split; assumption]).
  assert (Fm : fin 0 (fmul (jP (tot P l K)) (vdot (vdt K) (vdt K)))) by exact (fin_fmul 0 _ _ (Rle_refl 0) fin_BP Fa).
  rewrite (feval_fsub' t p _ _ F1 (fin_fmul 0 _ _ (Rle_refl 0) Fm Fg)).
  rewrite (feval_fmul' t p _ _ Fm Fg), (feval_fmul' t p _ _ fin_BP Fa), feval_fone.
  unfold vdot, vdt. cbn [vR vZ].
  rewrite (feval_fadd' t p _ _ (fin_fmul 0 _ _ (Rle_refl 0) FtR FtR) (fin_fmul 0 _ _ (Rle_refl 0) FtZ FtZ)).
  rewrite (feval_fmul' t p _ _ FtR FtR), (feval_fmul' t p _ _ FtZ FtZ). reflexivity.
Qed.

Theorem epoint4_ok (Ss : list (i3 * i3)) (OM : J.t) (CSk : list (J.t * J.t)) (Rr Zz tR pR tZ pZ Uv Gv : J.t) (t p : R) :
  src_in Ss l -> inR OM om ->
  Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk
          (map (fun k => p + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P))) ->
  fst (epoint4 Ss OM CSk Rr Zz tR pR tZ pZ Uv Gv) = true ->
  inR Rr (feval (vR K) t p) -> inR Zz (feval (vZ K) t p) ->
  inR tR (feval (dt (vR K)) t p) -> inR pR (feval (dp (vR K)) t p) ->
  inR tZ (feval (dt (vZ K)) t p) -> inR pZ (feval (dp (vZ K)) t p) ->
  inR Uv (feval Ub t p) -> inR Gv (feval gs t p) ->
  e4in (snd (epoint4 Ss OM CSk Rr Zz tR pR tZ pZ Uv Gv)) t p.
Proof.
  intros Hs HOM HT Hpos HR HZ HtR HpR HtZ HpZ HU HG.
  unfold epoint4 in *. rewrite icompvp_eq in *.
  pose proof (icompv_ok Ss l Rr Zz _ _ CSk _ Hs HR HZ HT) as Hc.
  destruct (icompv Ss Rr Zz CSk) as [[BR BP] BZ].
  cbn [fst snd] in Hpos. specialize (Hc Hpos). destruct Hc as [HBR [HBP HBZ]].
  rewrite (link_R P K l t p) in HBR. rewrite (link_P P K l t p) in HBP. rewrite (link_Z P K l t p) in HBZ.
  rewrite <- (val_R P rho K l HP Hr FK SK QK Hl t p) in HBR.
  rewrite <- (val_P P rho K l HP Hr FK SK QK Hl t p) in HBP.
  rewrite <- (val_Z P rho K l HP Hr FK SK QK Hl t p) in HBZ.
  pose proof FK as [[MR BRn] [MZ BZn]].
  unfold e4in. cbn [fst snd].
  rewrite (feval_errF_R P l om rho K Hr FK Hl t p), (feval_errF_Z P l om rho K Hr FK Hl t p).
  rewrite (feval_lc om rho MR (vR K) t p Hr BRn), (feval_lc om rho MZ (vZ K) t p Hr BZn).
  rewrite feval_defU, feval_defG. unfold lj.
  split; [| split; [| split]].
  - apply inR_sub; apply inR_mul; try assumption. apply inR_add; [apply inR_mul |]; assumption.
  - apply inR_sub; apply inR_mul; try assumption. apply inR_add; [apply inR_mul |]; assumption.
  - apply inR_sub; [apply inR_Z | apply inR_mul; assumption].
  - apply inR_sub; [apply inR_Z |]. apply inR_mul; [apply inR_mul; [exact HBP |] | exact HG].
    apply inR_add; apply inR_mul; assumption.
Qed.

End Point.

(** * The grid *)

(** The rows at one poloidal angle of the eight grids a point reads. *)
Record rows8 := mkrows8 {
  r8R : list J.t ; r8Z : list J.t ; r8tR : list J.t ; r8pR : list J.t ;
  r8tZ : list J.t ; r8pZ : list J.t ; r8U : list J.t ; r8G : list J.t }.

Fixpoint zip8 (GR GZ GtR GpR GtZ GpZ GU GG : list (list J.t)) : list rows8 :=
  match GR, GZ, GtR, GpR, GtZ, GpZ, GU, GG with
  | a1 :: r1, a2 :: r2, a3 :: r3, a4 :: r4, a5 :: r5, a6 :: r6, a7 :: r7, a8 :: r8 =>
      mkrows8 a1 a2 a3 a4 a5 a6 a7 a8 :: zip8 r1 r2 r3 r4 r5 r6 r7 r8
  | _, _, _, _, _, _, _, _ => []
  end.

Fixpoint erow (Ss : list (i3 * i3)) (OM : J.t) (CSks : list (list (J.t * J.t)))
    (Rs Zs tRs pRs tZs pZs Us Gs : list J.t) : list (bool * ((J.t * J.t) * (J.t * J.t))) :=
  match CSks, Rs, Zs, tRs, pRs, tZs, pZs, Us, Gs with
  | CSk :: CSks', Rr :: Rs', Zz :: Zs', tR :: tRs', pR :: pRs', tZ :: tZs', pZ :: pZs', Uv :: Us', Gv :: Gs' =>
      epoint4 Ss OM CSk Rr Zz tR pR tZ pZ Uv Gv :: erow Ss OM CSks' Rs' Zs' tRs' pRs' tZs' pZs' Us' Gs'
  | _, _, _, _, _, _, _, _, _ => []
  end.

Definition egrid (Ss : list (i3 * i3)) (OM : J.t) (CSks : list (list (J.t * J.t)))
    (GR GZ GtR GpR GtZ GpZ GU GG : list (list J.t)) : list (list (bool * ((J.t * J.t) * (J.t * J.t)))) :=
  pmap (fun r => erow Ss OM CSks (r8R r) (r8Z r) (r8tR r) (r8pR r) (r8tZ r) (r8pZ r) (r8U r) (r8G r))
       (zip8 GR GZ GtR GpR GtZ GpZ GU GG).

(** Every flag of a grid is set. *)
Definition eflags (EG : list (list (bool * ((J.t * J.t) * (J.t * J.t))))) : bool :=
  forallb (forallb fst) EG.

Section Grid.

Variables (P : Z) (rho om : R) (K : vf) (l : list (src * fser)) (Ub gs : fser).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.
Hypothesis FU : fin 0 Ub.
Hypothesis Fg : fin 0 gs.

Variables (N1 N2 : nat) (ta pb : nat -> R).

Definition egood (EG : list (list ((J.t * J.t) * (J.t * J.t)))) : Prop :=
  Forall2 (fun Row a => Forall2 (fun E b => e4in P om K l Ub gs E (ta a) (pb b)) Row (seq 0 N2)) EG (seq 0 N1).

Definition gin (G : list (list J.t)) (f : R -> R -> R) : Prop :=
  Forall2 (fun Row a => EN.encl Row (map (fun b => f (ta a) (pb b)) (seq 0 N2))) G (seq 0 N1).

Theorem egrid_ok (Ss : list (i3 * i3)) (OM : J.t) (CSks : list (list (J.t * J.t)))
    (GR GZ GtR GpR GtZ GpZ GU GG : list (list J.t)) :
  src_in Ss l -> inR OM om ->
  Forall2 (fun CSk b => Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk
                          (map (fun k => pb b + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P)))) CSks (seq 0 N2) ->
  gin GR (fun t p => feval (vR K) t p) -> gin GZ (fun t p => feval (vZ K) t p) ->
  gin GtR (fun t p => feval (dt (vR K)) t p) -> gin GpR (fun t p => feval (dp (vR K)) t p) ->
  gin GtZ (fun t p => feval (dt (vZ K)) t p) -> gin GpZ (fun t p => feval (dp (vZ K)) t p) ->
  gin GU (fun t p => feval Ub t p) -> gin GG (fun t p => feval gs t p) ->
  eflags (egrid Ss OM CSks GR GZ GtR GpR GtZ GpZ GU GG) = true ->
  egood (map (map snd) (egrid Ss OM CSks GR GZ GtR GpR GtZ GpZ GU GG)).
Proof.
  intros Hs HOM HT HGR HGZ HGtR HGpR HGtZ HGpZ HGU HGG Hpos. unfold egood, eflags, egrid, pmap, gin in *.
  generalize (seq 0 N1) HGR HGZ HGtR HGpR HGtZ HGpZ HGU HGG Hpos.
  clear HGR HGZ HGtR HGpR HGtZ HGpZ HGU HGG Hpos.
  intros as_ HGR. revert GZ GtR GpR GtZ GpZ GU GG.
  induction HGR as [| Rs a GR as_ HRs _ IH]; intros GZ GtR GpR GtZ GpZ GU GG HGZ HGtR HGpR HGtZ HGpZ HGU HGG Hpos.
  - constructor.
  - inversion HGZ as [| Zs a1 GZ' as1 HZs HGZ']; subst.
    inversion HGtR as [| tRs a2 GtR' as2 HtRs HGtR']; subst.
    inversion HGpR as [| pRs a3 GpR' as3 HpRs HGpR']; subst.
    inversion HGtZ as [| tZs a4 GtZ' as4 HtZs HGtZ']; subst.
    inversion HGpZ as [| pZs a5 GpZ' as5 HpZs HGpZ']; subst.
    inversion HGU as [| Us a6 GU' as6 HUs HGU']; subst.
    inversion HGG as [| Gs a7 GG' as7 HGs HGG']; subst.
    cbn [zip8 map forallb r8R r8Z r8tR r8pR r8tZ r8pZ r8U r8G] in *. apply andb_prop in Hpos.
    destruct Hpos as [Hrow Hrest].
    constructor; [| apply IH; assumption].
    clear IH Hrest HGZ' HGtR' HGpR' HGtZ' HGpZ' HGU' HGG' HGZ HGtR HGpR HGtZ HGpZ HGU HGG.
    generalize (seq 0 N2) HT HRs HZs HtRs HpRs HtZs HpZs HUs HGs Hrow.
    clear HT HRs HZs HtRs HpRs HtZs HpZs HUs HGs Hrow.
    intros bs HT. revert Rs Zs tRs pRs tZs pZs Us Gs.
    induction HT as [| CSk b CSks bs HCSk _ IHb]; intros Rs Zs tRs pRs tZs pZs Us Gs HRs HZs HtRs HpRs HtZs HpZs HUs HGs Hrow.
    + inversion HRs; subst. constructor.
    + inversion HRs as [| Rr r Rs' rs HRr HRs']; subst. inversion HZs as [| Zz z Zs' zs HZz HZs']; subst.
      inversion HtRs as [| tR x1 tRs' x1s HtR HtRs']; subst. inversion HpRs as [| pR x2 pRs' x2s HpR HpRs']; subst.
      inversion HtZs as [| tZ x3 tZs' x3s HtZ HtZs']; subst. inversion HpZs as [| pZ x4 pZs' x4s HpZ HpZs']; subst.
      inversion HUs as [| Uv x5 Us' x5s HUv HUs']; subst. inversion HGs as [| Gv x6 Gs' x6s HGv HGs']; subst.
      cbn [erow map forallb] in *. apply andb_prop in Hrow. destruct Hrow as [Hc Hrow'].
      constructor; [| apply IHb; assumption].
      apply (epoint4_ok P rho om K l Ub gs HP Hr FK SK QK Hl FU Fg); assumption.
Qed.

End Grid.

End E0Ops.
