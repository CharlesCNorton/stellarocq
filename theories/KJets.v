(** The check of the jet of the field along the first torus against its
    finite approximants.

    The nine components of the jet of the total field along the first torus,
    the field and its R and Z derivatives, less finite families given by
    their coefficients ([udef]), are evaluated on a grid: the jet from the
    sources at the P shifts of each point with the positivity of every
    distance ([icompp] of KJet.v), the finite families from their row sums at
    each toroidal angle and the table of the poloidal angle ([jpoint_ok]).
    The model check of KEngine.v bounds the norm of each difference on the
    strip of the iteration from a bound on the wide strip ([check_jets_ok]),
    so the norm of each component is at most the norm of its finite family
    plus that bound. *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierInv FourierParity FourierDFT FourierCanon FourierPer FourierList FourierModel FourierModelPer
  KAMVec KAMFin KAMPer Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldLine FieldJetVal KCheckErr
  KFix KCheckKern KEngine KTab KDense KGrid KJet KCheckE0 KE0.
Import ListNotations.
Local Open Scope R_scope.

(** The components of a jet in the order of the check. *)
Definition jsel (i : nat) (Jt : cjet) : fser :=
  match i with
  | 0 => jR Jt | 1 => jP Jt | 2 => jZ Jt | 3 => jR_R Jt | 4 => jR_Z Jt | 5 => jP_R Jt | 6 => jP_Z Jt
  | 7 => jZ_R Jt | _ => jZ_Z Jt
  end%nat.

Definition gsel {A : Type} (i : nat) (x : j9 A) : A :=
  match i with
  | 0 => g_R x | 1 => g_P x | 2 => g_Z x | 3 => g_RR x | 4 => g_RZ x | 5 => g_PR x | 6 => g_PZ x
  | 7 => g_ZR x | _ => g_ZZ x
  end%nat.

(** The component less its finite family. *)
Definition udef (P : Z) (l : list (src * fser)) (K : vf) (fJs : list (list (Z * list (Z * (R * R))))) (i : nat) : fser :=
  fsub (jsel i (tot P l K)) (cden (nth i fJs [])).

Lemma jsel_canon (P : Z) (l : list (src * fser)) (K : vf) (i : nat) :
  (0 < P)%Z -> vcanon K -> List.Forall (fun sy => is_canon (snd sy)) l -> is_canon (jsel i (tot P l K)).
Proof.
  intros HP CK Cl. destruct (tot_canon P l K HP CK Cl) as [C0 [C1 [C2 [C3 [C4 [_ [C6 [C7 [_ [C9 [C10 _]]]]]]]]]]].
  destruct i as [| [| [| [| [| [| [| [| i]]]]]]]]; assumption.
Qed.

Lemma jsel_per (P : Z) (l : list (src * fser)) (K : vf) (i : nat) : is_per P (jsel i (tot P l K)).
Proof.
  destruct (tot_per P l K) as [C0 [C1 [C2 [C3 [C4 [_ [C6 [C7 [_ [C9 [C10 _]]]]]]]]]]].
  destruct i as [| [| [| [| [| [| [| [| i]]]]]]]]; assumption.
Qed.

Section Val.

Variables (P : Z) (rho : R) (K : vf) (l : list (src * fser)).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.

Lemma jsel_fin (i : nat) : fin 0 (jsel i (tot P l K)).
Proof.
  destruct (tot_fin P rho K l Hr FK Hl) as [C0 [C1 [C2 [C3 [C4 [_ [C6 [C7 [_ [C9 [C10 _]]]]]]]]]]].
  apply (fin_mono rho); [lra |]. destruct i as [| [| [| [| [| [| [| [| i]]]]]]]]; assumption.
Qed.

End Val.

Module JetsCheck (J : RI).

Module E := E0Check J.
Module JO := E.EO.JO.
Import E.TB E.TB.E E.TB.E.KO.

(** * One point *)

Definition jpoint (Ss : list (i3 * i3)) (CSk : list (J.t * J.t)) (AB9 : list (list (J.t * J.t))) (TT : list (J.t * J.t))
    (Rr Zz : J.t) : bool * list J.t :=
  let '(ok, Jv) := JO.icompp Ss Rr Zz CSk in
  (ok, E.GO.zipw J.sub [g_R Jv; g_P Jv; g_Z Jv; g_RR Jv; g_RZ Jv; g_PR Jv; g_PZ Jv; g_ZR Jv; g_ZZ Jv]
                 (map (ival TT) AB9)).

Section Point.

Variables (P : Z) (rho : R) (K : vf) (l : list (src * fser)) (fJs : list (list (Z * list (Z * (R * R))))).
Variables (Kj1 : nat) (nsJ : list Z).
Hypothesis HP : (0 < P)%Z.
Hypothesis Hr : 0 < rho.
Hypothesis FK : vfin rho K.
Hypothesis SK : vsym K.
Hypothesis QK : vper P K.
Hypothesis Hl : srcs_ok rho l K.
Hypothesis L9 : length fJs = 9%nat.

Definition fams_in (F9 : list (list (Z * list (Z * (J.t * J.t))))) : Prop :=
  Forall2 (fun F f => fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = nsJ) f /\ map fst f = zrange Kj1) F9 fJs.

Lemma gsel_link (i : nat) (t p : R) :
  gsel i (JO.rcomp l (feval (vR K) t p) (feval (vZ K) t p) (map (fun k => p + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P))))
  = feval (jsel i (tot P l K)) t p.
Proof.
  destruct i as [| [| [| [| [| [| [| [| i]]]]]]]]; cbn [gsel jsel].
  - rewrite (JO.link_R P K l t p). symmetry. exact (val_R P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_P P K l t p). symmetry. exact (val_P P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_Z P K l t p). symmetry. exact (val_Z P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_RR P K l t p). symmetry. exact (val_R_R P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_RZ P K l t p). symmetry. exact (val_R_Z P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_PR P K l t p). symmetry. exact (val_P_R P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_PZ P K l t p). symmetry. exact (val_P_Z P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_ZR P K l t p). symmetry. exact (val_Z_R P rho K l HP Hr FK SK QK Hl t p).
  - rewrite (JO.link_ZZ P K l t p). symmetry. exact (val_Z_Z P rho K l HP Hr FK SK QK Hl t p).
Qed.

Lemma feval_udef (i : nat) (t p : R) :
  feval (udef P l K fJs i) t p = feval (jsel i (tot P l K)) t p - feval (flist (dents (nth i fJs []))) t p.
Proof.
  unfold udef. assert (Fc : fin 0 (cden (nth i fJs []))) by (eexists; apply nbound_cden).
  rewrite (feval_fsub' t p _ _ (jsel_fin P rho K l Hr FK Hl i) Fc). unfold cden.
  rewrite (feval_canon _ (esum (ewt 0) (dents (nth i fJs []))) t p (nbound_flist 0 _)). reflexivity.
Qed.

Definition udvals (t p : R) : list R := map (fun i => feval (udef P l K fJs i) t p) (seq 0 9).

Lemma map_seq_nth {A B : Type} (g : A -> B) (xs : list A) (d : A) :
  map g xs = map (fun i => g (nth i xs d)) (seq 0 (length xs)).
Proof.
  induction xs as [| x xs IH]; [reflexivity |]. cbn [length seq map nth]. f_equal.
  rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma zipw_sub_ok {A : Type} (Xs Ys : list J.t) (f g : A -> R) (L : list A) :
  Forall2 inR Xs (map f L) -> Forall2 inR Ys (map g L) -> Forall2 inR (E.GO.zipw J.sub Xs Ys) (map (fun x => f x - g x) L).
Proof.
  revert Xs Ys. induction L as [| x L IH]; intros Xs Ys HX HY.
  - inversion HX; subst. constructor.
  - inversion HX as [| X a Xs' b HXa HX']; subst. inversion HY as [| Y c Ys' e HYc HY']; subst.
    cbn [E.GO.zipw map]. constructor; [apply inR_sub; assumption | apply IH; assumption].
Qed.

Lemma fins_ok (F9 : list (list (Z * list (Z * (J.t * J.t))))) (T TT : list (J.t * J.t)) (t p : R) :
  fams_in F9 -> tab_in T nsJ p -> tab_in TT (zrange Kj1) t ->
  Forall2 inR (map (ival TT) (map (fun F => iABs F T) F9)) (map (fun f => feval (flist (dents f)) t p) fJs).
Proof.
  intros HF HT HTT. unfold fams_in in HF. rewrite map_map. clear L9.
  induction HF as [| F f Fs fs [HFf [Hns Hks]] _ IH]; [constructor |].
  cbn [map]. constructor; [| exact IH].
  rewrite <- Hks in HTT. exact (ival_ok t p TT F f T nsJ HFf Hns HT HTT).
Qed.

Theorem jpoint_ok (Ss : list (i3 * i3)) (CSk : list (J.t * J.t)) (F9 : list (list (Z * list (Z * (J.t * J.t)))))
    (T TT : list (J.t * J.t)) (Rr Zz : J.t) (t p : R) :
  JO.src_in Ss l -> fams_in F9 -> tab_in T nsJ p -> tab_in TT (zrange Kj1) t ->
  Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk
          (map (fun k => p + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P))) ->
  fst (jpoint Ss CSk (map (fun F => iABs F T) F9) TT Rr Zz) = true ->
  inR Rr (feval (vR K) t p) -> inR Zz (feval (vZ K) t p) ->
  Forall2 inR (snd (jpoint Ss CSk (map (fun F => iABs F T) F9) TT Rr Zz)) (udvals t p).
Proof.
  intros Hs HF HT HTT HCS Hc HR HZ. unfold jpoint in *. rewrite JO.icompp_eq in *.
  pose proof (JO.icomp_ok Ss l Rr Zz _ _ CSk _ Hs HR HZ HCS) as Hj.
  destruct (JO.icomp Ss Rr Zz CSk) as [a1 a2 a3 a4 a5 a6 a7 a8 a9] eqn:Ej.
  cbn [fst snd] in Hc |- *. specialize (Hj Hc).
  set (rc := JO.rcomp l (feval (vR K) t p) (feval (vZ K) t p) (map (fun k => p + INR k * (2 * PI / IZR P))
                                                                   (seq 0 (Z.to_nat P)))) in Hj.
  assert (HJ : Forall2 inR [a1; a2; a3; a4; a5; a6; a7; a8; a9] (map (fun i => gsel i rc) (seq 0 9))).
  { destruct Hj as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). cbn [seq map gsel].
    repeat constructor; assumption. }
  replace (map (fun i => gsel i rc) (seq 0 9)) with (map (fun i => feval (jsel i (tot P l K)) t p) (seq 0 9)) in HJ
    by (apply map_ext; intros i; symmetry; apply gsel_link).
  pose proof (fins_ok F9 T TT t p HF HT HTT) as HFs.
  rewrite (map_seq_nth _ fJs []), L9 in HFs.
  unfold udvals. replace (map (fun i => feval (udef P l K fJs i) t p) (seq 0 9))
    with (map (fun i => feval (jsel i (tot P l K)) t p - feval (flist (dents (nth i fJs []))) t p) (seq 0 9))
    by (apply map_ext; intros i; symmetry; apply feval_udef).
  exact (zipw_sub_ok _ _ _ _ _ HJ HFs).
Qed.

(** * The grid *)

Fixpoint jrow (Ss : list (i3 * i3)) (cols : list (list (J.t * J.t) * list (list (J.t * J.t)))) (TT : list (J.t * J.t))
    (Rs Zs : list J.t) : list (bool * list J.t) :=
  match cols, Rs, Zs with
  | c :: cols', Rr :: Rs', Zz :: Zs' => jpoint Ss (fst c) (snd c) TT Rr Zz :: jrow Ss cols' TT Rs' Zs'
  | _, _, _ => []
  end.

Definition jgrid (Ss : list (i3 * i3)) (cols : list (list (J.t * J.t) * list (list (J.t * J.t))))
    (TTs : list (list (J.t * J.t))) (GR GZ : list (list J.t)) : list (list (bool * list J.t)) :=
  pmap (fun x => jrow Ss cols (fst x) (fst (snd x)) (snd (snd x))) (combine TTs (combine GR GZ)).

Definition jflags (JG : list (list (bool * list J.t))) : bool := forallb (forallb fst) JG.

Variables (N1 N2 : nat) (ta pb : nat -> R).

Theorem jgrid_ok (Ss : list (i3 * i3)) (F9 : list (list (Z * list (Z * (J.t * J.t))))) (CSks : list (list (J.t * J.t)))
    (Ts TTs : list (list (J.t * J.t))) (GR GZ : list (list J.t)) :
  JO.src_in Ss l -> fams_in F9 ->
  Forall2 (fun T b => tab_in T nsJ (pb b)) Ts (seq 0 N2) ->
  Forall2 (fun TT a => tab_in TT (zrange Kj1) (ta a)) TTs (seq 0 N1) ->
  Forall2 (fun CSk b => Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk
                          (map (fun k => pb b + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P)))) CSks (seq 0 N2) ->
  Forall2 (fun Row a => encl Row (map (fun b => feval (vR K) (ta a) (pb b)) (seq 0 N2))) GR (seq 0 N1) ->
  Forall2 (fun Row a => encl Row (map (fun b => feval (vZ K) (ta a) (pb b)) (seq 0 N2))) GZ (seq 0 N1) ->
  jflags (jgrid Ss (combine CSks (map (fun T => map (fun F => iABs F T) F9) Ts)) TTs GR GZ) = true ->
  Forall2 (fun Row a => Forall2 (fun E b => Forall2 inR (snd E) (udvals (ta a) (pb b))) Row (seq 0 N2))
          (jgrid Ss (combine CSks (map (fun T => map (fun F => iABs F T) F9) Ts)) TTs GR GZ) (seq 0 N1).
Proof.
  intros Hs HF HTs HTTs HCS HGR HGZ Hc. unfold jflags, jgrid, pmap in *.
  set (cols := combine CSks (map (fun T => map (fun F => iABs F T) F9) Ts)) in *.
  assert (Hcols : Forall2 (fun c b => Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) (fst c)
                                        (map (fun k => pb b + INR k * (2 * PI / IZR P)) (seq 0 (Z.to_nat P))) /\
                                      exists T, tab_in T nsJ (pb b) /\ snd c = map (fun F => iABs F T) F9) cols (seq 0 N2)).
  { unfold cols. clear -HCS HTs. revert Ts HTs. induction HCS as [| CSk b CSks bs HC _ IH]; intros Ts HTs.
    - constructor.
    - inversion HTs as [| T b' Ts' bs' HT HTs']; subst. cbn [combine map]. constructor; [| apply IH; exact HTs'].
      cbn [fst snd]. split; [exact HC | exists T; split; [exact HT | reflexivity]]. }
  clearbody cols. clear HCS HTs.
  generalize (seq 0 N1) HTTs HGR HGZ Hc. clear HTTs HGR HGZ Hc. intros as_ HTTs. revert GR GZ.
  induction HTTs as [| TT a TTs as_ HTT _ IH]; intros GR GZ HGR HGZ Hc.
  - constructor.
  - inversion HGR as [| Rs a1 GR' as1 HRs HGR']; subst. inversion HGZ as [| Zs a2 GZ' as2 HZs HGZ']; subst.
    cbn [combine map forallb fst snd] in Hc |- *. apply andb_prop in Hc. destruct Hc as [Hrow Hrest].
    constructor; [| apply IH; assumption].
    clear IH Hrest HGR' HGZ' HGR HGZ. generalize (seq 0 N2) Hcols HRs HZs Hrow. clear Hcols HRs HZs Hrow.
    intros bs Hcols. revert Rs Zs.
    induction Hcols as [| c b cols bs [HC [T [HT Ec]]] _ IHb]; intros Rs Zs HRs HZs Hrow.
    + inversion HRs; subst. constructor.
    + inversion HRs as [| Rr r Rs' rs HRr HRs']; subst. inversion HZs as [| Zz z Zs' zs HZz HZs']; subst.
      cbn [jrow forallb] in Hrow |- *. apply andb_prop in Hrow. destruct Hrow as [Hp Hrow'].
      constructor; [| apply IHb; assumption].
      rewrite Ec in Hp |- *. exact (jpoint_ok Ss (fst c) F9 T TT Rr Zz (ta a) (pb b) Hs HF HT HTT HC Hp HRr HZz).
Qed.

End Point.

(** * The check *)

(** The parity of each component: cosines for the even ones. *)
Definition jpar : list bool :=
  false :: true :: true :: false :: true :: true :: false :: true :: false :: nil.

Definition fJd (P : Z) (sJ : Z) (Kj1 Kj2 : nat) (rowsJ : list (list (list Z))) : list (list (Z * list (Z * (R * R)))) :=
  map (fun x : bool * list (list Z) => dfam sJ (zrange Kj1) (pns P Kj2) (if fst x then crows (snd x) else srows (snd x)))
      (combine jpar rowsJ).
Definition FJd (P : Z) (sJ : Z) (Kj1 Kj2 : nat) (rowsJ : list (list (list Z))) : list (list (Z * list (Z * (J.t * J.t)))) :=
  map (fun x : bool * list (list Z) => E.DO.ifam sJ (zrange Kj1) (pns P Kj2) (if fst x then crows (snd x) else srows (snd x)))
      (combine jpar rowsJ).

Lemma fams_gen (P sJ : Z) (Kj1 Kj2 : nat) (pars : list bool) (rowsJ : list (list (list Z))) :
  (0 <= sJ)%Z ->
  List.Forall (fun rows => length rows = length (zrange Kj1)) rowsJ ->
  List.Forall (List.Forall (fun r => length r = length (pns P Kj2))) rowsJ ->
  Forall2 (fun F f => fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = pns P Kj2) f /\ map fst f = zrange Kj1)
    (map (fun x : bool * list (list Z) =>
            E.DO.ifam sJ (zrange Kj1) (pns P Kj2) (if fst x then crows (snd x) else srows (snd x))) (combine pars rowsJ))
    (map (fun x : bool * list (list Z) =>
            dfam sJ (zrange Kj1) (pns P Kj2) (if fst x then crows (snd x) else srows (snd x))) (combine pars rowsJ)).
Proof.
  intros HsJ Hk. revert pars. induction Hk as [| rows rs Lk Lks IH]; intros pars Hn; [destruct pars; constructor |].
  destruct pars as [| b pars]; [constructor |].
  apply Forall_cons_iff in Hn. destruct Hn as [Ln Lns].
  cbn [combine map fst snd]. constructor; [| apply IH; exact Lns].
  split; [| split].
  - apply E.DO.ifam_in, HsJ.
  - apply dfam_ns. destruct b; [apply crows_len | apply srows_len]; exact Ln.
  - apply dfam_ks. destruct b; [unfold crows | unfold srows]; rewrite length_map; exact Lk.
Qed.

Section Check.

Variables (Pn N1 M K1 K2 D Km Kn Kj1 Kj2 : nat) (s0 sJ : Z) (rowsR rowsZ : list (list Z)) (rowsJ : list (list (list Z))).
Variables (Ss : list (i3 * i3)) (s1 sM sPM : J.t * J.t).
Variables (Ew Ewm EAt EwP EwPm EBt ET : J.t) (IMs IBs : list J.t).

Let P : Z := Z.of_nat Pn.

Definition jgrid0 : list (list (bool * list J.t)) :=
  let tts := E.TTs N1 Km s1 in let ts := E.Ts M Kn sM in
  jgrid Ss (combine (E.CSks Pn M sPM) (map (fun T => map (fun F => iABs F T) (FJd P sJ Kj1 Kj2 rowsJ)) (E.Ts M Kj2 sM)))
    (E.TTs N1 Kj1 s1) (E.GO.gvals (E.FR Pn Km Kn s0 rowsR) tts ts) (E.GO.gvals (E.FZ Pn Km Kn s0 rowsZ) tts ts).

Definition jets_res : bool * list J.t :=
  let JG := jgrid0 in
  let tk := E.TK N1 K1 s1 in let ct := E.CT M K2 sM in
  let wa := E.WA K1 Ew in let ea := E.EA K1 Ewm EAt in let wb := E.WB K2 EwP in let eb := E.EB K2 EwPm EBt in
  let bnd (i : nat) := bnd_model Pn K1 K2 (map (map (fun e => nth i (snd e) J.zero)) JG) ct tk (E.inv_NM N1 M) D
                         wa ea wb eb (nth i IMs J.zero) ET (J.of_q 2 0) in
  let bs := map bnd (seq 0 9) in
  (jflags JG && Nat.eqb (length rowsJ) 9 && Nat.eqb (length IBs) 9 &&
   forallb (fun x => ile (fst x) (snd x)) (combine bs IBs), bs).

Definition check_jets : bool := fst jets_res.

Section Sound.

Variables (l : list (src * fser)) (rho w w' : R) (Mws Bs : list R).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HM : (0 < M)%nat.
Hypothesis Hs0 : (0 <= s0)%Z.
Hypothesis HsJ : (0 <= sJ)%Z.
Hypothesis LR : length rowsR = length (zrange Km).
Hypothesis LZ : length rowsZ = length (zrange Km).
Hypothesis LRn : List.Forall (fun r => length r = length (pns P Kn)) rowsR.
Hypothesis LZn : List.Forall (fun r => length r = length (pns P Kn)) rowsZ.
Hypothesis LJk : List.Forall (fun rows => length rows = length (zrange Kj1)) rowsJ.
Hypothesis LJn : List.Forall (List.Forall (fun r => length r = length (pns P Kj2))) rowsJ.
Hypothesis Hs1 : pinR s1 (cos (2 * PI / INR N1), sin (2 * PI / INR N1)).
Hypothesis HsM : pinR sM (cos (2 * PI / INR M), sin (2 * PI / INR M)).
Hypothesis HsPM : pinR sPM (cos (2 * PI / INR (Pn * M)), sin (2 * PI / INR (Pn * M))).
Hypothesis HEw : inR Ew (exp w).
Hypothesis HEwm : inR Ewm (exp (- w')).
Hypothesis HEAt : inR EAt (exp (- (w' * (INR N1 - INR K1)))).
Hypothesis HEwP : inR EwP (exp (w * (kappa * INR Pn))).
Hypothesis HEwPm : inR EwPm (exp (- (w' * (kappa * INR Pn)))).
Hypothesis HEBt : inR EBt (exp (- (w' * (kappa * (INR (Pn * M) - INR Pn * INR K2))))).
Hypothesis HET : inR ET (exp (- ((w' - w) * (kappa * INR (S D))))).
Hypothesis HIM : Forall2 inR IMs Mws.
Hypothesis HIB : Forall2 inR IBs Bs.
Hypothesis HSs : JO.src_in Ss l.
Hypothesis Hr : 0 < rho.
Hypothesis Hl : srcs_ok rho l (E.K0d Pn Km Kn s0 rowsR rowsZ).
Hypothesis Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Hypothesis Hw : 0 <= w.
Hypothesis Hww : w <= w'.
Hypothesis HD1 : (D < 10 * S K1)%nat.
Hypothesis HD2 : (D < Pn * S K2)%nat.

Let K := E.K0d Pn Km Kn s0 rowsR rowsZ.
Let fJs := fJd P sJ Kj1 Kj2 rowsJ.

Hypothesis Hu : forall i, (i < 9)%nat -> nbound w' (nth i Mws 0) (udef P l K fJs i).

Lemma HP' : (0 < P)%Z. Proof. unfold P. lia. Qed.

Lemma fams_ok : fams_in fJs Kj1 (pns P Kj2) (FJd P sJ Kj1 Kj2 rowsJ).
Proof. exact (fams_gen P sJ Kj1 Kj2 jpar rowsJ HsJ LJk LJn). Qed.

Lemma udef_canon (i : nat) : is_canon (udef P l K fJs i).
Proof.
  unfold udef. apply fsub_canon; [apply jsel_canon; [exact HP' | apply E.K0d_canon | exact Cl] | apply cden_canon].
Qed.

Lemma nth_fJs_per (i : nat) : is_per P (cden (nth i fJs [])).
Proof.
  destruct (Nat.lt_ge_cases i (length fJs)) as [Hi | Hi].
  - pose proof (nth_In fJs [] Hi) as Hin. unfold fJs, fJd in Hin |- *. apply in_map_iff in Hin.
    destruct Hin as [[b rows] [E _]]. rewrite <- E. destruct b; apply cden_per, HP'.
  - rewrite nth_overflow by exact Hi. intros m n _. unfold cden, canon, ccan, scan. simpl. split; ring.
Qed.

Lemma udef_per (i : nat) : is_per P (udef P l K fJs i).
Proof. unfold udef. apply (fsub_per P); [apply jsel_per | apply nth_fJs_per]. Qed.

Lemma inR_nth (Xs : list J.t) (xs : list R) (i : nat) : Forall2 inR Xs xs -> inR (nth i Xs J.zero) (nth i xs 0).
Proof.
  intros H. revert i. induction H as [| X x Xs xs Hx _ IH]; intros i.
  - destruct i; exact inR_zero.
  - destruct i as [| i]; [exact Hx | exact (IH i)].
Qed.

Lemma forallb_combine_nth {A B : Type} (f : A * B -> bool) (xs : list A) (ys : list B) (dx : A) (dy : B) (i : nat) :
  forallb f (combine xs ys) = true -> (i < length xs)%nat -> (i < length ys)%nat -> f (nth i xs dx, nth i ys dy) = true.
Proof.
  revert ys i. induction xs as [| x xs IH]; intros ys i H Hx Hy; [simpl in Hx; lia |].
  destruct ys as [| y ys]; [simpl in Hy; lia |]. cbn [combine forallb] in H. apply andb_prop in H.
  destruct H as [H0 H1]. destruct i as [| i]; [exact H0 |]. cbn [nth].
  apply IH; [exact H1 | simpl in Hx; lia | simpl in Hy; lia].
Qed.

Lemma fJs_len : length rowsJ = 9%nat -> length fJs = 9%nat.
Proof. intros H. unfold fJs, fJd. rewrite length_map, length_combine, H. reflexivity. Qed.

Theorem check_jets_ok : check_jets = true -> forall i, (i < 9)%nat -> nbound w (nth i Bs 0) (udef P l K fJs i).
Proof.
  intros Hc i Hi. unfold check_jets, jets_res in Hc. cbv zeta in Hc. cbn [fst] in Hc.
  apply andb_prop in Hc. destruct Hc as [Hc Hcl]. apply andb_prop in Hc. destruct Hc as [Hc HLB].
  apply andb_prop in Hc. destruct Hc as [Hflags HL9]. apply Nat.eqb_eq in HL9, HLB.
  destruct (E.grid_cden Pn N1 M s0 s1 sM HPn HN1 HM Hs0 Hs1 HsM Km Kn (crows rowsR)
              ltac:(unfold crows; rewrite length_map; exact LR) (crows_len _ _ LRn)) as [GR _].
  destruct (E.grid_cden Pn N1 M s0 s1 sM HPn HN1 HM Hs0 Hs1 HsM Km Kn (srows rowsZ)
              ltac:(unfold srows; rewrite length_map; exact LZ) (srows_len _ _ LZn)) as [GZ _].
  pose proof (jgrid_ok P rho K l fJs Kj1 (pns P Kj2) HP' Hr (E.K0d_fin Pn Km Kn s0 rowsR rowsZ rho)
                (E.K0d_sym Pn Km Kn s0 rowsR rowsZ) (E.K0d_per Pn Km Kn s0 rowsR rowsZ HPn) Hl (fJs_len HL9)
                N1 M (gpt N1) (gpt (Pn * M)) Ss (FJd P sJ Kj1 Kj2 rowsJ) (E.CSks Pn M sPM) (E.Ts M Kj2 sM)
                (E.TTs N1 Kj1 s1) _ _ HSs fams_ok (E.ts_ok Pn M Kj2 sM HPn HM HsM) (E.tts_ok N1 Kj1 s1 HN1 Hs1)
                (E.csks_ok Pn N1 M sPM HPn HN1 HM HsPM) GR GZ Hflags) as HJ.
  fold jgrid0 in HJ. set (JG := jgrid0) in *.
  assert (HV : Forall2 (fun Row a => encl Row (map (fun b => feval (udef P l K fJs i) (gpt N1 a) (gpt (Pn * M) b))
                                                  (seq 0 M)))
                       (map (map (fun e => nth i (snd e) J.zero)) JG) (seq 0 N1)).
  { apply forall2_map_l. eapply Forall2_impl; [| exact HJ]. intros Row a HR.
    apply forall2_map_l, forall2_map_r. eapply Forall2_impl; [| exact HR]. intros e b He.
    pose proof (forall2_nth inR _ _ J.zero 0 i He) as G. unfold udvals in G.
    rewrite length_map, length_seq in G. specialize (G Hi). rewrite nth_map_seq in G by exact Hi. exact G. }
  pose proof (E.ct_ok M K2 sM HM HsM) as HCT. pose proof (E.tk_ok N1 K1 s1 HN1 Hs1) as HTK.
  pose proof (E.inv_NM_ok Pn N1 M HN1 HM) as HINV.
  assert (HI2 : inR (J.of_q 2 0) 2) by apply inR_Z.
  pose proof (forallb_combine_nth _ _ _ J.zero J.zero i Hcl ltac:(rewrite length_map, length_seq; exact Hi)
                ltac:(rewrite HLB; exact Hi)) as Hci.
  cbn [fst snd] in Hci. rewrite nth_map_seq in Hci by exact Hi.
  exact (check_model_ok Pn N1 M K1 K2 (udef P l K fJs i) HPn HN1 HM (per_grid Pn N1 M _ HPn HM (udef_per i))
           (map (map (fun e => nth i (snd e) J.zero)) JG) HV (E.CT M K2 sM) (E.TK N1 K1 s1) (E.inv_NM N1 M) HCT HTK HINV
           D w w' (nth i Mws 0) (nth i Bs 0) Hw Hww HD1 HD2 (udef_canon i) (udef_per i) (Hu i Hi)
           (E.WA K1 Ew) (E.EA K1 Ewm EAt) (E.WB K2 EwP) (E.EB K2 EwPm EBt) (nth i IMs J.zero) ET (nth i IBs J.zero)
           (J.of_q 2 0) (E.wa_ok K1 w Ew HEw) (E.ea_ok N1 K1 w' Ewm EAt HEwm HEAt) (E.wb_ok Pn K2 w EwP HEwP)
           (E.eb_ok Pn M K2 w' EwPm EBt HEwPm HEBt) (inR_nth _ _ i HIM) HET (inR_nth _ _ i HIB) HI2 Hci).
Qed.

End Sound.

End Check.

(** * The check from raw data *)

Record jetsdata := mkjd {
  jd_P : nat ; jd_N1 : nat ; jd_M : nat ; jd_K1 : nat ; jd_K2 : nat ; jd_D : nat ; jd_Km : nat ; jd_Kn : nat ;
  jd_Kj1 : nat ; jd_Kj2 : nat ; jd_s0 : Z ; jd_sJ : Z ;
  jd_rowsR : list (list Z) ; jd_rowsZ : list (list Z) ; jd_rowsJ : list (list (list Z)) ;
  jd_ssrc : Z ; jd_srcs : list ((Z * Z * Z) * (Z * Z * Z)) ;
  jd_trig : list J.t ; jd_exp : list J.t ; jd_IMs : list J.t ; jd_IBs : list J.t }.

(** The verdict and the nine bounds, with the seeds of the check of the first
    torus: trigonometric for N1, M and P M, and the seven exponentials. *)
Definition res_jets (d : jetsdata) : bool * list J.t :=
  let tr := jd_trig d in let ex := jd_exp d in
  jets_res (jd_P d) (jd_N1 d) (jd_M d) (jd_K1 d) (jd_K2 d) (jd_D d) (jd_Km d) (jd_Kn d) (jd_Kj1 d) (jd_Kj2 d)
    (jd_s0 d) (jd_sJ d) (jd_rowsR d) (jd_rowsZ d) (jd_rowsJ d) (E.src_i (jd_ssrc d) (jd_srcs d))
    (E.nth0 tr 0, E.nth0 tr 1) (E.nth0 tr 2, E.nth0 tr 3) (E.nth0 tr 4, E.nth0 tr 5)
    (E.nth0 ex 0) (E.nth0 ex 1) (E.nth0 ex 2) (E.nth0 ex 3) (E.nth0 ex 4) (E.nth0 ex 5) (E.nth0 ex 6)
    (jd_IMs d) (jd_IBs d).

End JetsCheck.
