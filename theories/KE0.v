(** The check of the error of the first torus and of the defects of the
    seeds of 1 / B_phi and 1 / (B_phi |a|^2).

    From enclosures of cos(2 pi / N) and sin(2 pi / N) for the three grid
    sizes in use (N1 poloidal points, M toroidal points of one period and
    P M of the whole torus) the tables of the grid are rotations
    ([tk_ok], [ct_ok], [tts_ok], [ts_ok], [csks_ok]); from enclosures of a few
    exponentials the weights and aliasing factors are powers ([wa_ok],
    [ea_ok], [wb_ok], [eb_ok]). With them the torus, its derivatives, the two
    seeds and the field of the sources on the grid give the numerators of the
    error and the two defects at every point ([egrid_ok] of KCheckE0.v), and
    the model check of KEngine.v bounds their norms on the strip of the
    iteration from bounds on the wide strip ([check_E0_ok]). The torus is
    given by cosine coefficients of R and sine coefficients of Z, and the
    seeds by cosine coefficients, over the toroidal modes of period P, so
    its symmetry and period and theirs hold by construction. *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierParity FourierDFT FourierCanon FourierPer FourierList FourierModel FourierModelPer KAMVec
  KAMFin KAMPer Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel FieldLine FieldJetVal KCheckErr
  KFix KCheckKern KEngine KTab KDense KGrid KJet KCheckE0.
Import ListNotations.
Local Open Scope R_scope.

Lemma forall2_self {A B : Type} (Rel : A -> B -> Prop) (f : B -> A) (l : list B) :
  (forall x, In x l -> Rel (f x) x) -> Forall2 Rel (map f l) l.
Proof.
  induction l as [| x l IH]; intros H; [constructor |]. cbn [map]. constructor.
  - apply H. left. reflexivity.
  - apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma forall2_diag {A : Type} (Rel : A -> A -> Prop) (l : list A) :
  (forall x, In x l -> Rel x x) -> Forall2 Rel l l.
Proof.
  induction l as [| x l IH]; intros H; [constructor |]. constructor.
  - apply H. left. reflexivity.
  - apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma gpt_mul (Pn M b : nat) (l : Z) : (0 < Pn)%nat -> (0 < M)%nat ->
  IZR (Z.of_nat Pn * l) * gpt (Pn * M) b = IZR l * gpt M b.
Proof.
  intros HP HM. unfold gpt. rewrite mult_IZR, <- INR_IZR_INZ, mult_INR.
  assert (INR Pn <> 0) by (apply not_0_INR; lia). assert (INR M <> 0) by (apply not_0_INR; lia).
  field. split; assumption.
Qed.

Lemma gpt_shift (Pn M b k : nat) : (0 < Pn)%nat -> (0 < M)%nat ->
  gpt (Pn * M) (b + k * M) = gpt (Pn * M) b + INR k * (2 * PI / IZR (Z.of_nat Pn)).
Proof.
  intros HP HM. unfold gpt. rewrite <- INR_IZR_INZ, plus_INR, !mult_INR.
  assert (INR Pn <> 0) by (apply not_0_INR; lia). assert (INR M <> 0) by (apply not_0_INR; lia).
  field. split; assumption.
Qed.

Module E0Check (J : RI).

Module TB := Tab J.
Module GO := GridOps J.
Module DO := DenseOps J.
Module EO := E0Ops J.
Import TB TB.E TB.E.KO.

(** * Tables *)

Section Tables.

Variables (Pn N1 M K1 K2 Km Kn : nat) (s1 sM sPM : J.t * J.t).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HM : (0 < M)%nat.
Hypothesis Hs1 : pinR s1 (cos (2 * PI / INR N1), sin (2 * PI / INR N1)).
Hypothesis HsM : pinR sM (cos (2 * PI / INR M), sin (2 * PI / INR M)).
Hypothesis HsPM : pinR sPM (cos (2 * PI / INR (Pn * M)), sin (2 * PI / INR (Pn * M))).

Definition B1 : list (J.t * J.t) := base s1 N1.
Definition BM : list (J.t * J.t) := base sM M.
Definition BPM : list (J.t * J.t) := base sPM (Pn * M).

Definition TK : list (list (J.t * J.t)) := map (fun k => krowi B1 N1 k N1) (zrange K1).
Definition CT : list (list (J.t * J.t)) := map (fun l => krowi BM M l M) (zrange K2).
Definition TTs : list (list (J.t * J.t)) := map (fun st => ztab st Km) B1.
Definition Ts : list (list (J.t * J.t)) := map (fun st => ztab st Kn) BM.
Definition CSks : list (list (J.t * J.t)) :=
  map (fun b => map (fun k => nth (b + k * M) BPM one2) (seq 0 Pn)) (seq 0 M).

Lemma tk_ok :
  Forall2 (fun row k => Forall2 (fun CS a => inR (fst CS) (cos (IZR k * gpt N1 a)) /\
                                            inR (snd CS) (sin (IZR k * gpt N1 a))) row (seq 0 N1)) TK (zrange K1).
Proof. unfold TK. apply forall2_self. intros k _. apply krowi_ok; assumption. Qed.

Lemma ct_ok :
  Forall2 (fun row l => Forall2 (fun CS b => inR (fst CS) (cos (IZR l * gpt M b)) /\
                                            inR (snd CS) (sin (IZR l * gpt M b))) row (seq 0 M)) CT (zrange K2).
Proof. unfold CT. apply forall2_self. intros l _. apply krowi_ok; assumption. Qed.

Lemma tts_ok : Forall2 (fun TT a => tab_in TT (zrange Km) (gpt N1 a)) TTs (seq 0 N1).
Proof.
  unfold TTs, B1. pose proof (base_ok s1 N1 HN1 Hs1) as HB.
  apply forall2_map_l. apply forall2_map_r' in HB. eapply Forall2_impl; [| exact HB].
  intros st a [H1 H2]. apply ztab_ok. split; assumption.
Qed.

Lemma ts_ok : Forall2 (fun T b => tab_in T (pns (Z.of_nat Pn) Kn) (gpt (Pn * M) b)) Ts (seq 0 M).
Proof.
  unfold Ts, BM, pns. pose proof (base_ok sM M HM HsM) as HB.
  apply forall2_map_l. apply forall2_map_r' in HB. eapply Forall2_impl; [| exact HB].
  intros st b [H1 H2]. unfold tab_in. apply forall2_map_r.
  pose proof (ztab_ok st (gpt M b) Kn (conj H1 H2)) as HZ.
  eapply Forall2_impl; [| exact HZ]. intros CS l [C S]. rewrite gpt_mul by assumption. split; assumption.
Qed.

Lemma csks_ok :
  Forall2 (fun CSk b => Forall2 (fun CS ph => inR (fst CS) (cos ph) /\ inR (snd CS) (sin ph)) CSk
                          (map (fun k => gpt (Pn * M) b + INR k * (2 * PI / IZR (Z.of_nat Pn)))
                               (seq 0 (Z.to_nat (Z.of_nat Pn))))) CSks (seq 0 M).
Proof.
  unfold CSks. rewrite Nat2Z.id. apply forall2_self. intros b Hb. apply in_seq in Hb.
  apply forall2_map_l. apply forall2_map_r. apply forall2_diag. intros k Hk. apply in_seq in Hk.
  assert (HN : (0 < Pn * M)%nat) by lia.
  pose proof (base_ok sPM (Pn * M) HN HsPM) as HB.
  assert (Hj : (b + k * M < Pn * M)%nat) by nia.
  pose proof (forall2_nth pinR _ _ one2 (0, 0) (b + k * M) HB) as G.
  rewrite length_map, length_seq in G. specialize (G Hj). rewrite nth_map_seq in G by exact Hj.
  unfold BPM. rewrite <- gpt_shift by assumption. exact G.
Qed.

End Tables.

(** * Weights and aliasing factors *)

Section Weights.

(** The aliasing factors decay away from the edge of the box, so their tables
    start from the edge, e^(-w' (N1 - K1)) and e^(-w' kappa (P M - P K2)),
    and step inward by e^(-w') and e^(-w' kappa P); every entry is then held
    to the relative accuracy of the arithmetic. *)
Variables (Pn N1 M K1 K2 D : nat) (w w' : R) (Ew Ewm EAt EwP EwPm EBt : J.t).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HEw : inR Ew (exp w).
Hypothesis HEwm : inR Ewm (exp (- w')).
Hypothesis HEAt : inR EAt (exp (- (w' * (INR N1 - INR K1)))).
Hypothesis HEwP : inR EwP (exp (w * (kappa * INR Pn))).
Hypothesis HEwPm : inR EwPm (exp (- (w' * (kappa * INR Pn)))).
Hypothesis HEBt : inR EBt (exp (- (w' * (kappa * (INR (Pn * M) - INR Pn * INR K2))))).

Definition WA : list J.t := zexp Ew (J.of_q 1 0) K1.
Definition EA : list J.t := zexp_rev Ewm EAt K1.
Definition WB : list J.t := zexp EwP (J.of_q 1 0) K2.
Definition EB : list J.t := zexp_rev EwPm EBt K2.

Lemma one_exp : inR (J.of_q 1 0) (exp 0).
Proof. rewrite exp_0. apply inR_Z. Qed.

Lemma abs_P (l : Z) : Rabs (IZR (Z.of_nat Pn * l)) = INR Pn * Rabs (IZR l).
Proof. rewrite mult_IZR, Rabs_mult, <- INR_IZR_INZ, Rabs_pos_eq by apply pos_INR. reflexivity. Qed.

Lemma wa_ok : Forall2 (fun X k => inR X (exp (w * Rabs (IZR k)))) WA (zrange K1).
Proof.
  unfold WA. eapply Forall2_impl; [| exact (zexp_ok Ew _ w 0 K1 HEw one_exp)].
  intros X k H. replace (w * Rabs (IZR k)) with (0 + w * Rabs (IZR k)) by ring. exact H.
Qed.

Lemma ea_ok : Forall2 (fun X k => inR X (exp (- (w' * (INR N1 - Rabs (IZR k)))))) EA (zrange K1).
Proof.
  unfold EA. eapply Forall2_impl; [| exact (zexp_rev_ok Ewm EAt (- w') _ K1 HEwm HEAt)].
  intros X k H. replace (- (w' * (INR N1 - Rabs (IZR k))))
    with (- (w' * (INR N1 - INR K1)) + - w' * (INR K1 - Rabs (IZR k))) by ring.
  exact H.
Qed.

Lemma wb_ok : Forall2 (fun X l => inR X (exp (w * (kappa * Rabs (IZR (Z.of_nat Pn * l)))))) WB (zrange K2).
Proof.
  unfold WB. eapply Forall2_impl; [| exact (zexp_ok EwP _ _ 0 K2 HEwP one_exp)].
  intros X l H. rewrite abs_P. replace (w * (kappa * (INR Pn * Rabs (IZR l))))
    with (0 + w * (kappa * INR Pn) * Rabs (IZR l)) by ring. exact H.
Qed.

Lemma eb_ok : Forall2 (fun X l => inR X (exp (- (w' * (kappa * (INR (Pn * M) - Rabs (IZR (Z.of_nat Pn * l))))))))
                      EB (zrange K2).
Proof.
  unfold EB. eapply Forall2_impl; [| exact (zexp_rev_ok EwPm EBt _ _ K2 HEwPm HEBt)].
  intros X l H. rewrite abs_P.
  replace (- (w' * (kappa * (INR (Pn * M) - INR Pn * Rabs (IZR l)))))
    with (- (w' * (kappa * (INR (Pn * M) - INR Pn * INR K2))) + - (w' * (kappa * INR Pn)) * (INR K2 - Rabs (IZR l)))
    by ring. exact H.
Qed.

End Weights.

(** * The check *)

Lemma ggrid_ext (G : list (list J.t)) (N1 N2 : nat) (f g : R -> R -> R) (ta pb : nat -> R) :
  (forall t p, f t p = g t p) -> GO.ggrid G N1 N2 f ta pb -> GO.ggrid G N1 N2 g ta pb.
Proof.
  intros E H. unfold GO.ggrid in *. eapply Forall2_impl; [| exact H]. intros Row a HR.
  unfold GO.EN.encl in *. replace (map (fun b => g (ta a) (pb b)) (seq 0 N2)) with (map (fun b => f (ta a) (pb b)) (seq 0 N2));
    [exact HR |]. apply map_ext. intros b. apply E.
Qed.

(** One of the four values of every entry of a grid. *)
Lemma sel_grid (sel : (J.t * J.t) * (J.t * J.t) -> J.t) (f : R -> R -> R)
    (EG : list (list (bool * ((J.t * J.t) * (J.t * J.t))))) (N1 N2 : nat) (ta pb : nat -> R)
    (Pr : (J.t * J.t) * (J.t * J.t) -> R -> R -> Prop) :
  (forall E t p, Pr E t p -> inR (sel E) (f t p)) ->
  Forall2 (fun Row a => Forall2 (fun E b => Pr E (ta a) (pb b)) Row (seq 0 N2)) (map (map snd) EG) (seq 0 N1) ->
  Forall2 (fun Row a => GO.EN.encl Row (map (fun b => f (ta a) (pb b)) (seq 0 N2)))
          (map (map (fun x => sel (snd x))) EG) (seq 0 N1).
Proof.
  intros Hs H. replace (map (map (fun x => sel (snd x))) EG) with (map (map sel) (map (map snd) EG)).
  - apply forall2_map_l. eapply Forall2_impl; [| exact H]. intros Row a HR.
    apply forall2_map_l, forall2_map_r. eapply Forall2_impl; [| exact HR]. intros E b HE. exact (Hs _ _ _ HE).
  - rewrite map_map. apply map_ext. intros row. rewrite map_map. reflexivity.
Qed.

Section Check.

Variables (Pn N1 M K1 K2 D Km Kn Kmu Knu Kmg Kng : nat) (s0 : Z).
Variables (rowsR rowsZ rowsU rowsG : list (list Z)).
Variables (Ss : list (i3 * i3)) (OM : J.t) (s1 sM sPM : J.t * J.t).
Variables (Ew Ewm EAt EwP EwPm EBt ET : J.t) (IMR IMZ IMU IMG IBR IBZ IBU IBG : J.t).

Let P : Z := Z.of_nat Pn.

Definition FR : list (Z * list (Z * (J.t * J.t))) := DO.ifam s0 (zrange Km) (pns P Kn) (crows rowsR).
Definition FZ : list (Z * list (Z * (J.t * J.t))) := DO.ifam s0 (zrange Km) (pns P Kn) (srows rowsZ).
Definition FU : list (Z * list (Z * (J.t * J.t))) := DO.ifam s0 (zrange Kmu) (pns P Knu) (crows rowsU).
Definition FG : list (Z * list (Z * (J.t * J.t))) := DO.ifam s0 (zrange Kmg) (pns P Kng) (crows rowsG).

Definition egrid0 : list (list (bool * ((J.t * J.t) * (J.t * J.t)))) :=
  let tts := TTs N1 Km s1 in let ts := Ts M Kn sM in
  EO.egrid Ss OM (CSks Pn M sPM)
    (GO.gvals FR tts ts) (GO.gvals FZ tts ts)
    (GO.gvals (DO.ifam_dt FR) tts ts) (GO.gvals (DO.ifam_dp FR) tts ts)
    (GO.gvals (DO.ifam_dt FZ) tts ts) (GO.gvals (DO.ifam_dp FZ) tts ts)
    (GO.gvals FU (TTs N1 Kmu s1) (Ts M Knu sM)) (GO.gvals FG (TTs N1 Kmg s1) (Ts M Kng sM)).

Definition inv_NM : J.t := J.div (J.of_q 1 0) (J.of_q (Z.of_nat (N1 * M)) 0).

Definition selR (x : bool * ((J.t * J.t) * (J.t * J.t))) : J.t := fst (fst (snd x)).
Definition selZ (x : bool * ((J.t * J.t) * (J.t * J.t))) : J.t := snd (fst (snd x)).
Definition selU (x : bool * ((J.t * J.t) * (J.t * J.t))) : J.t := fst (snd (snd x)).
Definition selG (x : bool * ((J.t * J.t) * (J.t * J.t))) : J.t := snd (snd (snd x)).

(** The four bounds, and the check of the four claims. *)
Definition e0_res : bool * list J.t :=
  let EG := egrid0 in
  let tk := TK N1 K1 s1 in let ct := CT M K2 sM in
  let wa := WA K1 Ew in let ea := EA K1 Ewm EAt in let wb := WB K2 EwP in let eb := EB K2 EwPm EBt in
  let two := J.of_q 2 0 in
  let bR := bnd_model Pn K1 K2 (map (map selR) EG) ct tk inv_NM D wa ea wb eb IMR ET two in
  let bZ := bnd_model Pn K1 K2 (map (map selZ) EG) ct tk inv_NM D wa ea wb eb IMZ ET two in
  let bU := bnd_model Pn K1 K2 (map (map selU) EG) ct tk inv_NM D wa ea wb eb IMU ET two in
  let bG := bnd_model Pn K1 K2 (map (map selG) EG) ct tk inv_NM D wa ea wb eb IMG ET two in
  (EO.eflags EG && ile bR IBR && ile bZ IBZ && ile bU IBU && ile bG IBG, [bR; bZ; bU; bG]).

Definition check_E0 : bool := fst e0_res.

(** The real torus and seeds of the data. *)
Definition fR0 : list (Z * list (Z * (R * R))) := dfam s0 (zrange Km) (pns P Kn) (crows rowsR).
Definition fZ0 : list (Z * list (Z * (R * R))) := dfam s0 (zrange Km) (pns P Kn) (srows rowsZ).
Definition fU0 : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmu) (pns P Knu) (crows rowsU).
Definition fG0 : list (Z * list (Z * (R * R))) := dfam s0 (zrange Kmg) (pns P Kng) (crows rowsG).
Definition K0d : vf := mkvf (cden fR0) (cden fZ0).
Definition Ubd : fser := cden fU0.
Definition gsd : fser := cden fG0.

Lemma K0d_fin (rho : R) : vfin rho K0d.
Proof. split; [exists (esum (ewt rho) (dents fR0)) | exists (esum (ewt rho) (dents fZ0))]; apply nbound_cden. Qed.

Lemma K0d_canon : vcanon K0d.
Proof. split; apply cden_canon. Qed.

Lemma K0d_sym : vsym K0d.
Proof. split; [apply cden_even | apply cden_odd]. Qed.

Lemma K0d_per : (0 < Pn)%nat -> vper P K0d.
Proof. intros H. split; apply cden_per; unfold P; lia. Qed.

Lemma cden_fin0 (f : list (Z * list (Z * (R * R)))) : fin 0 (cden f).
Proof. exists (esum (ewt 0) (dents f)). apply nbound_cden. Qed.

Lemma inv_NM_ok : (0 < N1)%nat -> (0 < M)%nat -> inR inv_NM (/ (INR N1 * INR M)).
Proof.
  intros H1 HM. unfold inv_NM. replace (/ (INR N1 * INR M)) with (IZR 1 / IZR (Z.of_nat (N1 * M))).
  - apply inR_div; [apply inR_Z | apply inR_Z |]. rewrite <- INR_IZR_INZ, mult_INR.
    apply Rgt_not_eq, Rmult_lt_0_compat; apply lt_0_INR; lia.
  - rewrite <- INR_IZR_INZ, mult_INR. simpl. field. split; apply Rgt_not_eq, lt_0_INR; lia.
Qed.

Section Sound.

Variables (l : list (src * fser)) (om rho w w' MwR MwZ MwU MwG BR BZ BU BG : R).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HM : (0 < M)%nat.
Hypothesis Hs0 : (0 <= s0)%Z.
Hypothesis LR : length rowsR = length (zrange Km).
Hypothesis LZ : length rowsZ = length (zrange Km).
Hypothesis LU : length rowsU = length (zrange Kmu).
Hypothesis LG : length rowsG = length (zrange Kmg).
Hypothesis LRn : Forall (fun r => length r = length (pns P Kn)) rowsR.
Hypothesis LZn : Forall (fun r => length r = length (pns P Kn)) rowsZ.
Hypothesis LUn : Forall (fun r => length r = length (pns P Knu)) rowsU.
Hypothesis LGn : Forall (fun r => length r = length (pns P Kng)) rowsG.
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
Hypothesis HIMR : inR IMR MwR.
Hypothesis HIMZ : inR IMZ MwZ.
Hypothesis HIMU : inR IMU MwU.
Hypothesis HIMG : inR IMG MwG.
Hypothesis HIBR : inR IBR BR.
Hypothesis HIBZ : inR IBZ BZ.
Hypothesis HIBU : inR IBU BU.
Hypothesis HIBG : inR IBG BG.
Hypothesis HOM : inR OM om.
Hypothesis HSs : EO.JO.src_in Ss l.
Hypothesis Hr : 0 < rho.
Hypothesis Hl : srcs_ok rho l K0d.
Hypothesis Cl : List.Forall (fun sy => is_canon (snd sy)) l.
Hypothesis Hw : 0 <= w.
Hypothesis Hww : w <= w'.
Hypothesis HD1 : (D < 10 * S K1)%nat.
Hypothesis HD2 : (D < Pn * S K2)%nat.
Hypothesis HuR : nbound w' MwR (errF_R P l om K0d).
Hypothesis HuZ : nbound w' MwZ (errF_Z P l om K0d).
Hypothesis HuU : nbound w' MwU (defU P l K0d Ubd).
Hypothesis HuG : nbound w' MwG (defG P l K0d gsd).

Lemma HP' : (0 < P)%Z. Proof. unfold P. lia. Qed.

Lemma grid_of (Kx Ky : nat) (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R))))
    (g : R -> R -> R) :
  fam_in F f -> Forall (fun kr => map fst (snd kr) = pns P Ky) f -> map fst f = zrange Kx ->
  (forall t p, feval (flist (dents f)) t p = g t p) ->
  GO.ggrid (GO.gvals F (TTs N1 Kx s1) (Ts M Ky sM)) N1 M g (gpt N1) (gpt (Pn * M)).
Proof.
  intros HF Hns Hks Hg. apply (ggrid_ext _ _ _ (fun t p => feval (flist (dents f)) t p)); [exact Hg |].
  apply (GO.gvals_ok F f (pns P Ky)); [exact HF | exact Hns | exact (ts_ok Pn M Ky sM HPn HM HsM) |].
  rewrite Hks. exact (tts_ok N1 Kx s1 HN1 Hs1).
Qed.

Lemma grid_cden (Kx Ky : nat) (rows : list (list (Z * Z))) :
  length rows = length (zrange Kx) -> Forall (fun r => length r = length (pns P Ky)) rows ->
  GO.ggrid (GO.gvals (DO.ifam s0 (zrange Kx) (pns P Ky) rows) (TTs N1 Kx s1) (Ts M Ky sM)) N1 M
    (fun t p => feval (cden (dfam s0 (zrange Kx) (pns P Ky) rows)) t p) (gpt N1) (gpt (Pn * M)) /\
  GO.ggrid (GO.gvals (DO.ifam_dt (DO.ifam s0 (zrange Kx) (pns P Ky) rows)) (TTs N1 Kx s1) (Ts M Ky sM)) N1 M
    (fun t p => feval (dt (cden (dfam s0 (zrange Kx) (pns P Ky) rows))) t p) (gpt N1) (gpt (Pn * M)) /\
  GO.ggrid (GO.gvals (DO.ifam_dp (DO.ifam s0 (zrange Kx) (pns P Ky) rows)) (TTs N1 Kx s1) (Ts M Ky sM)) N1 M
    (fun t p => feval (dp (cden (dfam s0 (zrange Kx) (pns P Ky) rows))) t p) (gpt N1) (gpt (Pn * M)).
Proof.
  intros Hl1 Hl2.
  pose proof (DO.ifam_in s0 (zrange Kx) (pns P Ky) rows Hs0) as I.
  pose proof (dfam_ns s0 (zrange Kx) (pns P Ky) rows Hl2) as N.
  pose proof (dfam_ks s0 (zrange Kx) (pns P Ky) rows Hl1) as Ks.
  split; [| split].
  - apply (grid_of Kx Ky _ (dfam s0 (zrange Kx) (pns P Ky) rows)); try assumption.
    intros t p. rewrite feval_cden. apply feval_dents.
  - apply (grid_of Kx Ky _ (fam_dt (dfam s0 (zrange Kx) (pns P Ky) rows)));
      [apply DO.ifam_dt_in, I | apply DO.fam_dt_ns, N | rewrite DO.fam_dt_ks; exact Ks |].
    intros t p. rewrite feval_dt_cden. apply feval_dents.
  - apply (grid_of Kx Ky _ (fam_dp (dfam s0 (zrange Kx) (pns P Ky) rows)));
      [apply DO.ifam_dp_in, I | apply DO.fam_dp_ns, N | rewrite DO.fam_dp_ks; exact Ks |].
    intros t p. rewrite feval_dp_cden. apply feval_dents.
Qed.

Theorem check_E0_ok : check_E0 = true ->
  nbound w BR (errF_R P l om K0d) /\ nbound w BZ (errF_Z P l om K0d) /\
  nbound w BU (defU P l K0d Ubd) /\ nbound w BG (defG P l K0d gsd).
Proof.
  intros Hc. unfold check_E0, e0_res in Hc. cbv zeta in Hc. cbn [fst] in Hc.
  apply andb_prop in Hc. destruct Hc as [Hc HcG]. apply andb_prop in Hc. destruct Hc as [Hc HcU].
  apply andb_prop in Hc. destruct Hc as [Hc HcZ]. apply andb_prop in Hc. destruct Hc as [Hpos HcR].
  destruct (grid_cden Km Kn (crows rowsR) ltac:(unfold crows; rewrite length_map; exact LR) (crows_len _ _ LRn))
    as [GR [GtR GpR]].
  destruct (grid_cden Km Kn (srows rowsZ) ltac:(unfold srows; rewrite length_map; exact LZ) (srows_len _ _ LZn))
    as [GZ [GtZ GpZ]].
  destruct (grid_cden Kmu Knu (crows rowsU) ltac:(unfold crows; rewrite length_map; exact LU) (crows_len _ _ LUn))
    as [GU _].
  destruct (grid_cden Kmg Kng (crows rowsG) ltac:(unfold crows; rewrite length_map; exact LG) (crows_len _ _ LGn))
    as [GG _].
  pose proof (EO.egrid_ok P rho om K0d l Ubd gsd HP' Hr (K0d_fin rho) K0d_sym (K0d_per HPn) Hl
                (cden_fin0 fU0) (cden_fin0 fG0) N1 M (gpt N1) (gpt (Pn * M))
                Ss OM (CSks Pn M sPM) _ _ _ _ _ _ _ _ HSs HOM (csks_ok Pn N1 M sPM HPn HN1 HM HsPM)
                GR GZ GtR GpR GtZ GpZ GU GG Hpos) as HE.
  fold egrid0 in HE. unfold EO.egood in HE.
  destruct (errF_canon P l om K0d HP' K0d_canon Cl) as [CuR CuZ].
  destruct (errF_per P l om K0d HP' (K0d_per HPn)) as [QuR QuZ].
  destruct (def_canon P l K0d Ubd gsd HP' K0d_canon Cl (cden_canon _) (cden_canon _)) as [CuU CuG].
  destruct (def_per P l K0d Ubd gsd HP' (K0d_per HPn) (cden_per _ _ _ _ _ HP') (cden_per _ _ _ _ _ HP'))
    as [QuU QuG].
  assert (HI2 : inR (J.of_q 2 0) 2) by apply inR_Z.
  set (Pr := fun E t p => EO.e4in P om K0d l Ubd gsd E t p).
  pose proof (sel_grid (fun E => fst (fst E)) (fun t p => feval (errF_R P l om K0d) t p) egrid0 N1 M (gpt N1)
                (gpt (Pn * M)) Pr (fun E t p (H : Pr E t p) => proj1 H) HE) as HVR.
  pose proof (sel_grid (fun E => snd (fst E)) (fun t p => feval (errF_Z P l om K0d) t p) egrid0 N1 M (gpt N1)
                (gpt (Pn * M)) Pr (fun E t p (H : Pr E t p) => proj1 (proj2 H)) HE) as HVZ.
  pose proof (sel_grid (fun E => fst (snd E)) (fun t p => feval (defU P l K0d Ubd) t p) egrid0 N1 M (gpt N1)
                (gpt (Pn * M)) Pr (fun E t p (H : Pr E t p) => proj1 (proj2 (proj2 H))) HE) as HVU.
  pose proof (sel_grid (fun E => snd (snd E)) (fun t p => feval (defG P l K0d gsd) t p) egrid0 N1 M (gpt N1)
                (gpt (Pn * M)) Pr (fun E t p (H : Pr E t p) => proj2 (proj2 (proj2 H))) HE) as HVG.
  pose proof (ct_ok M K2 sM HM HsM) as HCT. pose proof (tk_ok N1 K1 s1 HN1 Hs1) as HTK.
  pose proof (inv_NM_ok HN1 HM) as HINV.
  pose proof (wa_ok K1 w Ew HEw) as HWA. pose proof (ea_ok N1 K1 w' Ewm EAt HEwm HEAt) as HEA.
  pose proof (wb_ok Pn K2 w EwP HEwP) as HWB. pose proof (eb_ok Pn M K2 w' EwPm EBt HEwPm HEBt) as HEB.
  split; [| split; [| split]].
  - exact (check_model_ok Pn N1 M K1 K2 (errF_R P l om K0d) HPn HN1 HM (per_grid Pn N1 M _ HPn HM QuR)
             (map (map selR) egrid0) HVR (CT M K2 sM) (TK N1 K1 s1) inv_NM HCT HTK HINV
             D w w' MwR BR Hw Hww HD1 HD2 CuR QuR HuR
             (WA K1 Ew) (EA K1 Ewm EAt) (WB K2 EwP) (EB K2 EwPm EBt) IMR ET IBR (J.of_q 2 0)
             HWA HEA HWB HEB HIMR HET HIBR HI2 HcR).
  - exact (check_model_ok Pn N1 M K1 K2 (errF_Z P l om K0d) HPn HN1 HM (per_grid Pn N1 M _ HPn HM QuZ)
             (map (map selZ) egrid0) HVZ (CT M K2 sM) (TK N1 K1 s1) inv_NM HCT HTK HINV
             D w w' MwZ BZ Hw Hww HD1 HD2 CuZ QuZ HuZ
             (WA K1 Ew) (EA K1 Ewm EAt) (WB K2 EwP) (EB K2 EwPm EBt) IMZ ET IBZ (J.of_q 2 0)
             HWA HEA HWB HEB HIMZ HET HIBZ HI2 HcZ).
  - exact (check_model_ok Pn N1 M K1 K2 (defU P l K0d Ubd) HPn HN1 HM (per_grid Pn N1 M _ HPn HM QuU)
             (map (map selU) egrid0) HVU (CT M K2 sM) (TK N1 K1 s1) inv_NM HCT HTK HINV
             D w w' MwU BU Hw Hww HD1 HD2 CuU QuU HuU
             (WA K1 Ew) (EA K1 Ewm EAt) (WB K2 EwP) (EB K2 EwPm EBt) IMU ET IBU (J.of_q 2 0)
             HWA HEA HWB HEB HIMU HET HIBU HI2 HcU).
  - exact (check_model_ok Pn N1 M K1 K2 (defG P l K0d gsd) HPn HN1 HM (per_grid Pn N1 M _ HPn HM QuG)
             (map (map selG) egrid0) HVG (CT M K2 sM) (TK N1 K1 s1) inv_NM HCT HTK HINV
             D w w' MwG BG Hw Hww HD1 HD2 CuG QuG HuG
             (WA K1 Ew) (EA K1 Ewm EAt) (WB K2 EwP) (EB K2 EwPm EBt) IMG ET IBG (J.of_q 2 0)
             HWA HEA HWB HEB HIMG HET HIBG HI2 HcG).
Qed.

End Sound.

End Check.

(** * The check from raw data

    Everything the check reads is formed here from integers: the sources, the
    torus and the seeds from mantissas at their scales, the rotation number
    P (-b + sqrt 5) / (2 a) of a noble number, and the enclosures of the
    trigonometric and exponential seeds and the claims, so the program that
    runs it only parses integers. *)

Record e0data := mke0 {
  e0_P : nat ; e0_N1 : nat ; e0_M : nat ; e0_K1 : nat ; e0_K2 : nat ; e0_D : nat ;
  e0_Km : nat ; e0_Kn : nat ; e0_Kmu : nat ; e0_Knu : nat ; e0_Kmg : nat ; e0_Kng : nat ;
  e0_s0 : Z ; e0_rowsR : list (list Z) ; e0_rowsZ : list (list Z) ; e0_rowsU : list (list Z) ;
  e0_rowsG : list (list Z) ;
  e0_ssrc : Z ; e0_srcs : list ((Z * Z * Z) * (Z * Z * Z)) ;
  e0_a : Z ; e0_b : Z ;
  e0_trig : list J.t ;
  e0_exp : list J.t ;
  e0_bounds : list J.t }.

Definition i3q (s : Z) (x : Z * Z * Z) : i3 :=
  let '(x1, x2, x3) := x in (J.of_q x1 s, J.of_q x2 s, J.of_q x3 s).

Definition src_i (s : Z) (xs : list ((Z * Z * Z) * (Z * Z * Z))) : list (i3 * i3) :=
  map (fun pd => (i3q s (fst pd), i3q s (snd pd))) xs.

(** P (- b + sqrt 5) / (2 a). *)
Definition om_i (P : nat) (a b : Z) : J.t :=
  J.mul (J.of_q (Z.of_nat P) 0) (J.div (J.add (J.of_q (- b) 0) (J.sqrt (J.of_q 5 0))) (J.of_q (2 * a) 0)).

Definition nth0 (l : list J.t) (i : nat) : J.t := nth i l J.zero.

(** The verdict and the four bounds: the trigonometric seeds for N1, M and
    P M, the exponentials e^w, e^(-w'), e^(-w' (N1 - K1)), e^(w kappa P),
    e^(-w' kappa P), e^(-w' kappa (P M - P K2)), e^(-(w' - w) kappa (D + 1)),
    and the claims Mw and B for F_R, F_Z and the two defects. *)
Definition res_E0 (d : e0data) : bool * list J.t :=
  let tr := e0_trig d in let ex := e0_exp d in let bd := e0_bounds d in
  e0_res (e0_P d) (e0_N1 d) (e0_M d) (e0_K1 d) (e0_K2 d) (e0_D d) (e0_Km d) (e0_Kn d) (e0_Kmu d) (e0_Knu d)
    (e0_Kmg d) (e0_Kng d) (e0_s0 d) (e0_rowsR d) (e0_rowsZ d) (e0_rowsU d) (e0_rowsG d)
    (src_i (e0_ssrc d) (e0_srcs d)) (om_i (e0_P d) (e0_a d) (e0_b d))
    (nth0 tr 0, nth0 tr 1) (nth0 tr 2, nth0 tr 3) (nth0 tr 4, nth0 tr 5)
    (nth0 ex 0) (nth0 ex 1) (nth0 ex 2) (nth0 ex 3) (nth0 ex 4) (nth0 ex 5) (nth0 ex 6)
    (nth0 bd 0) (nth0 bd 1) (nth0 bd 2) (nth0 bd 3) (nth0 bd 4) (nth0 bd 5) (nth0 bd 6) (nth0 bd 7).

Definition run_E0 (d : e0data) : bool := fst (res_E0 d).

End E0Check.
