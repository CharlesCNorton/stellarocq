(** The finite twist on a grid, over intervals.

    The 23 dense families of KTfin.v are evaluated on one grid of N1 poloidal
    points and M toroidal points over one field period ([igrids]); the grids
    are regrouped point by point ([tpoints]) and the point formula [tpt] is
    carried out over intervals ([itpt], [itpt_ok]), giving at every point
    enclosures of the finite normal N, of L N - DV N and of the finite twist.
    Their weighted transforms over the boxes of KTfin.v enclose sums that
    bound their norms exactly, N on the strip of the iteration and the other
    three on the strip one loss narrower, and the transform of the twist at
    the origin encloses its mean ([tcheck_ok]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt FourierParity FourierDFT
  FourierCanon FourierPer FourierList FourierModel FourierSupp FourierModelPer KAMVec KAMFin KAMPer KAMStep KAMDiff
  KFix KCheckKern KEngine KTab KDense KGrid KCheckE0 KE0 KTwist KTfin.
Import ListNotations.
Local Open Scope R_scope.

Lemma Kfull_ge (Pn K : nat) : (Pn * K <= Kfull (Z.of_nat Pn) K)%nat.
Proof. unfold Kfull. rewrite Nat2Z.id. lia. Qed.

Lemma Kfull_mono (Pn K K' : nat) : (K <= K')%nat -> (Kfull (Z.of_nat Pn) K <= Kfull (Z.of_nat Pn) K')%nat.
Proof. intros H. unfold Kfull. rewrite Nat2Z.id. nia. Qed.

Module TGrid (J : RI).

Module E := E0Check J.
Import E.TB E.TB.E E.TB.E.KO.

Ltac irs := repeat (first [assumption | apply inR_add | apply inR_sub | apply inR_mul | apply inR_abs | apply inR_neg
                          | apply inR_Z | exact inR_zero]).

Definition m1 : J.t := J.of_q (-1) 0.

(** Transposing a table whose entries are related to both of their indices. *)
Lemma tr_rel {A X Y : Type} (d : A) (Rel : A -> X -> Y -> Prop) (ys : list Y) :
  forall (rows : list (list A)) (xs : list X),
  Forall2 (fun row x => Forall2 (fun e y => Rel e x y) row ys) rows xs ->
  Forall2 (fun col y => Forall2 (fun e x => Rel e x y) col xs) (tr d (length ys) rows) ys.
Proof.
  induction ys as [| y ys IH]; intros rows xs H; [constructor |].
  cbn [length tr]. constructor.
  - induction H as [| row x rows xs HR _ IHH]; [constructor |].
    cbn [map]. constructor; [| exact IHH]. inversion HR as [| e y' row' ys' He Hrow]; subst. exact He.
  - apply IH. induction H as [| row x rows xs HR _ IHH]; [constructor |].
    cbn [map]. constructor; [| exact IHH]. inversion HR as [| e y' row' ys' He Hrow]; subst. exact Hrow.
Qed.

(** * The point *)

Definition itpt (OM : J.t) (X : list J.t) : list J.t :=
  let v i := nth i X J.zero in
  let aR := v 1%nat in let aZ := v 2%nat in
  let laR := J.add (J.mul OM (v 3%nat)) (v 4%nat) in let laZ := J.add (J.mul OM (v 5%nat)) (v 6%nat) in
  let g := v 7%nat in let lg := J.add (J.mul OM (v 8%nat)) (v 9%nat) in
  let bb := v 10%nat in let lb := J.add (J.mul OM (v 11%nat)) (v 12%nat) in
  let U := v 13%nat in let Jv i := v (14 + i)%nat in
  let W := J.mul (v 0%nat) U in
  let WR := J.sub U (J.mul W (J.mul U (Jv 5%nat))) in let WZ := J.mul m1 (J.mul W (J.mul U (Jv 6%nat))) in
  let NR := J.add (J.mul g (J.mul m1 aZ)) (J.mul bb aR) in let NZ := J.add (J.mul g aR) (J.mul bb aZ) in
  let lNR := J.add (J.add (J.mul lg (J.mul m1 aZ)) (J.mul g (J.mul m1 laZ))) (J.add (J.mul lb aR) (J.mul bb laR)) in
  let lNZ := J.add (J.add (J.mul lg aR) (J.mul g laR)) (J.add (J.mul lb aZ) (J.mul bb laZ)) in
  let KR := J.sub lNR (J.add (J.mul (J.add (J.mul WR (Jv 0%nat)) (J.mul W (Jv 3%nat))) NR)
                             (J.mul (J.add (J.mul WZ (Jv 0%nat)) (J.mul W (Jv 4%nat))) NZ)) in
  let KZ := J.sub lNZ (J.add (J.mul (J.add (J.mul WR (Jv 2%nat)) (J.mul W (Jv 7%nat))) NR)
                             (J.mul (J.add (J.mul WZ (Jv 2%nat)) (J.mul W (Jv 8%nat))) NZ)) in
  [NR; NZ; KR; KZ; J.mul (Jv 1%nat) (J.sub (J.mul KR NZ) (J.mul KZ NR))].

Lemma nth_in (Xs : list J.t) (xs : list R) (i : nat) : Forall2 inR Xs xs -> inR (nth i Xs J.zero) (nth i xs 0).
Proof.
  intros H. revert i. induction H as [| X x Xs xs Hx _ IH]; intros i; [destruct i; exact inR_zero |].
  destruct i; [exact Hx | exact (IH i)].
Qed.

Lemma itpt_ok (OM : J.t) (om : R) (X : list J.t) (x : list R) :
  inR OM om -> Forall2 inR X x -> Forall2 inR (itpt OM X) (tpt om x).
Proof.
  intros HOM HX. pose proof (fun i => nth_in X x i HX) as V.
  assert (M1 : inR m1 (-1)) by exact (inR_Z (-1)).
  pose proof (V 0%nat) as V0. pose proof (V 1%nat) as V1. pose proof (V 2%nat) as V2. pose proof (V 3%nat) as V3.
  pose proof (V 4%nat) as V4. pose proof (V 5%nat) as V5. pose proof (V 6%nat) as V6. pose proof (V 7%nat) as V7.
  pose proof (V 8%nat) as V8. pose proof (V 9%nat) as V9. pose proof (V 10%nat) as V10. pose proof (V 11%nat) as V11.
  pose proof (V 12%nat) as V12. pose proof (V 13%nat) as V13. pose proof (V 14%nat) as V14.
  pose proof (V 15%nat) as V15. pose proof (V 16%nat) as V16. pose proof (V 17%nat) as V17.
  pose proof (V 18%nat) as V18. pose proof (V 19%nat) as V19. pose proof (V 20%nat) as V20.
  pose proof (V 21%nat) as V21. pose proof (V 22%nat) as V22. clear V.
  unfold itpt, tpt. cbv zeta. cbn [Nat.add].
  apply Forall2_cons; [irs |]. apply Forall2_cons; [irs |]. apply Forall2_cons; [irs |].
  apply Forall2_cons; [irs |]. apply Forall2_cons; [irs |]. apply Forall2_nil.
Qed.

(** * The grids *)

Definition fam_t : Type := list (Z * list (Z * (J.t * J.t))).

Section IFam.

Variables (Pn : nat) (s0 sJ : Z) (Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 : nat).
Variables (rowsR rowsZ rowsG rowsB rowsU : list (list Z)) (rowsJ : list (list (list Z))).

Definition iFR : fam_t := E.DO.ifam s0 (zrange Km) (pns (Z.of_nat Pn) Kn) (crows rowsR).
Definition iFZ : fam_t := E.DO.ifam s0 (zrange Km) (pns (Z.of_nat Pn) Kn) (srows rowsZ).
Definition iFG : fam_t := E.DO.ifam s0 (zrange Kmg) (pns (Z.of_nat Pn) Kng) (crows rowsG).
Definition iFB : fam_t := E.DO.ifam s0 (zrange Kmb) (pns (Z.of_nat Pn) Knb) (srows rowsB).
Definition iFU : fam_t := E.DO.ifam s0 (zrange Kmu) (pns (Z.of_nat Pn) Knu) (crows rowsU).
Definition iFJs : list fam_t :=
  map (fun x : bool * list (list Z) =>
         E.DO.ifam sJ (zrange Kj1) (pns (Z.of_nat Pn) Kj2) (if fst x then crows (snd x) else srows (snd x)))
      (combine tjpar rowsJ).

(** The 23 interval families with their boxes, in the order of [tbasics]. *)
Definition ibasics : list (nat * nat * fam_t) :=
  [(Km, Kn, iFR); (Km, Kn, E.DO.ifam_dt iFR); (Km, Kn, E.DO.ifam_dt iFZ);
   (Km, Kn, E.DO.ifam_dt (E.DO.ifam_dt iFR)); (Km, Kn, E.DO.ifam_dp (E.DO.ifam_dt iFR));
   (Km, Kn, E.DO.ifam_dt (E.DO.ifam_dt iFZ)); (Km, Kn, E.DO.ifam_dp (E.DO.ifam_dt iFZ));
   (Kmg, Kng, iFG); (Kmg, Kng, E.DO.ifam_dt iFG); (Kmg, Kng, E.DO.ifam_dp iFG);
   (Kmb, Knb, iFB); (Kmb, Knb, E.DO.ifam_dt iFB); (Kmb, Knb, E.DO.ifam_dp iFB); (Kmu, Knu, iFU)]
  ++ map (fun i => (Kj1, Kj2, nth i iFJs [])) (seq 0 9).

End IFam.

Definition igrids (N1 M : nat) (s1 sM : J.t * J.t) (ib : list (nat * nat * fam_t)) : list (list (list J.t)) :=
  map (fun x => let '(Kx, Ky, F) := x in E.GO.gvals F (E.TTs N1 Kx s1) (E.Ts M Ky sM)) ib.

Definition tpoints (N1 M : nat) (Gs : list (list (list J.t))) : list (list (list J.t)) :=
  map (tr J.zero M) (tr [] N1 Gs).

Definition tout (OM : J.t) (PTS : list (list (list J.t))) : list (list (list J.t)) := pmap (map (itpt OM)) PTS.

Definition tsel (i : nat) (OG : list (list (list J.t))) : list (list J.t) := map (map (fun o => nth i o J.zero)) OG.

Lemma jets_parts_gen (Pn : nat) (sJ : Z) (Kj1 Kj2 : nat) (pars : list bool) (rowsJ : list (list (list Z))) :
  (0 <= sJ)%Z ->
  List.Forall (fun rows => length rows = length (zrange Kj1)) rowsJ ->
  List.Forall (List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Kj2))) rowsJ ->
  Forall2 (fun F f => fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Kj2) f /\
                      map fst f = zrange Kj1)
    (map (fun x : bool * list (list Z) =>
            E.DO.ifam sJ (zrange Kj1) (pns (Z.of_nat Pn) Kj2) (if fst x then crows (snd x) else srows (snd x)))
         (combine pars rowsJ))
    (map (fun x : bool * list (list Z) =>
            dfam sJ (zrange Kj1) (pns (Z.of_nat Pn) Kj2) (if fst x then crows (snd x) else srows (snd x)))
         (combine pars rowsJ)).
Proof.
  intros HsJ Hk. revert pars. induction Hk as [| rows rs Lk Lks IH]; intros pars Hn; [destruct pars; constructor |].
  destruct pars as [| b pars]; [constructor |].
  apply Forall_cons_iff in Hn. destruct Hn as [Ln Lns].
  cbn [combine map fst snd]. constructor; [| apply IH; exact Lns].
  refine (conj (E.DO.ifam_in _ _ _ _ HsJ) (conj _ _)).
  - apply dfam_ns. destruct b; [apply crows_len | apply srows_len]; exact Ln.
  - apply dfam_ks. destruct b; [unfold crows | unfold srows]; rewrite length_map; exact Lk.
Qed.

(** * The check *)

Section TCheck.

Variables (Pn N1 M : nat) (s0 sJ : Z) (Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 : nat).
Variables (rowsR rowsZ rowsG rowsB rowsU : list (list Z)) (rowsJ : list (list (list Z))).
Variables (s1 sM : J.t * J.t) (OM Ew EwP Ewd EwdP : J.t).

Definition tOG : list (list (list J.t)) :=
  tout OM (tpoints N1 M (igrids N1 M s1 sM
    (ibasics Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ))).

(** The bounds of the norms of the two components of N, of L N - DV N and of
    the twist, and the enclosure of the mean of the twist. *)
Definition tcheck_res : list J.t :=
  let OG := tOG in let INV := E.inv_NM N1 M in
  let bx (i K1 K2 : nat) (E1 E2 : J.t) :=
    ibox_x K1 K2 (tsel i OG) (E.CT M K2 sM) (E.TK N1 K1 s1) INV (E.WA K1 E1) (E.WB K2 E2) in
  [bx 0%nat (bN1 Km Kmg) (bN2 Kn Kng) Ew EwP; bx 1%nat (bN1 Km Kmg) (bN2 Kn Kng) Ew EwP;
   bx 2%nat (bK1 Km Kmg Kmu Kj1) (bK2 Kn Kng Knu Kj2) Ewd EwdP; bx 3%nat (bK1 Km Kmg Kmu Kj1) (bK2 Kn Kng Knu Kj2) Ewd EwdP;
   bx 4%nat (bT1 Km Kmg Kmu Kj1) (bT2 Kn Kng Knu Kj2) Ewd EwdP;
   iC INV (hd [] (E.TK N1 0 s1)) (hd [] (GHt 0 (tsel 4 OG) (E.CT M 0 sM)))].

Section Sound.

Variables (om w wd : R).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HM : (0 < M)%nat.
Hypothesis Hs0 : (0 <= s0)%Z.
Hypothesis HsJ : (0 <= sJ)%Z.
Hypothesis LR : length rowsR = length (zrange Km).
Hypothesis LZ : length rowsZ = length (zrange Km).
Hypothesis LG : length rowsG = length (zrange Kmg).
Hypothesis LB : length rowsB = length (zrange Kmb).
Hypothesis LU : length rowsU = length (zrange Kmu).
Hypothesis LRn : List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Kn)) rowsR.
Hypothesis LZn : List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Kn)) rowsZ.
Hypothesis LGn : List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Kng)) rowsG.
Hypothesis LBn : List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Knb)) rowsB.
Hypothesis LUn : List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Knu)) rowsU.
Hypothesis LJk : List.Forall (fun rows => length rows = length (zrange Kj1)) rowsJ.
Hypothesis LJn : List.Forall (List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Kj2))) rowsJ.
Hypothesis L9 : length rowsJ = 9%nat.
Hypothesis Hs1 : pinR s1 (cos (2 * PI / INR N1), sin (2 * PI / INR N1)).
Hypothesis HsM : pinR sM (cos (2 * PI / INR M), sin (2 * PI / INR M)).
Hypothesis HOM : inR OM om.
Hypothesis HEw : inR Ew (exp w).
Hypothesis HEwP : inR EwP (exp (w * (kappa * INR Pn))).
Hypothesis HEwd : inR Ewd (exp wd).
Hypothesis HEwdP : inR EwdP (exp (wd * (kappa * INR Pn))).
Hypothesis HBm : (Kmb <= Kmg)%nat.
Hypothesis HBn : (Knb <= Kng)%nat.
Hypothesis HNx : (2 * bT1 Km Kmg Kmu Kj1 < N1)%nat.
Hypothesis HMx : (2 * Kfull (Z.of_nat Pn) (bT2 Kn Kng Knu Kj2) < Pn * M)%nat.

Let ta := gpt N1.
Let pb := gpt (Pn * M).
Let TB := tbasics Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ.
Let IB := ibasics Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ.
Let Nf := tNf Pn s0 Km Kn Kmg Kng Kmb Knb rowsR rowsZ rowsG rowsB.
Let kmf := tkmf Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om.
Let Tf := tTf Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om.

(** A dense family of the data and its derivatives on the grid. *)
Lemma gfam (Kx Ky : nat) (F : fam_t) (f : list (Z * list (Z * (R * R)))) :
  fam_in F f -> List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Ky) f -> map fst f = zrange Kx ->
  E.GO.ggrid (E.GO.gvals F (E.TTs N1 Kx s1) (E.Ts M Ky sM)) N1 M (fun t p => feval (cden f) t p) ta pb.
Proof.
  intros HF Hns Hks. apply (E.grid_of Pn N1 M s1 sM HPn HN1 HM Hs1 HsM Kx Ky F f); try assumption.
  intros t p. cbv beta. rewrite feval_cden. apply feval_dents.
Qed.

Lemma dfam_parts (s : Z) (Kx Ky : nat) (rows : list (list (Z * Z))) :
  (0 <= s)%Z -> length rows = length (zrange Kx) -> List.Forall (fun r => length r = length (pns (Z.of_nat Pn) Ky)) rows ->
  let f := dfam s (zrange Kx) (pns (Z.of_nat Pn) Ky) rows in
  let F := E.DO.ifam s (zrange Kx) (pns (Z.of_nat Pn) Ky) rows in
  (fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Ky) f /\ map fst f = zrange Kx).
Proof.
  intros Hs Hl Hn f F. refine (conj (E.DO.ifam_in _ _ _ _ Hs) (conj (dfam_ns _ _ _ _ Hn) (dfam_ks _ _ _ _ Hl))).
Qed.

Lemma dt_parts (F : fam_t) (f : list (Z * list (Z * (R * R)))) (Ky : nat) (Kx : nat) :
  (fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Ky) f /\ map fst f = zrange Kx) ->
  (fam_in (E.DO.ifam_dt F) (fam_dt f) /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Ky) (fam_dt f) /\
   map fst (fam_dt f) = zrange Kx) /\
  (fam_in (E.DO.ifam_dp F) (fam_dp f) /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Ky) (fam_dp f) /\
   map fst (fam_dp f) = zrange Kx).
Proof.
  intros [A [B C]]. split; (split; [| split]).
  - apply E.DO.ifam_dt_in, A.
  - apply E.DO.fam_dt_ns, B.
  - rewrite E.DO.fam_dt_ks. exact C.
  - apply E.DO.ifam_dp_in, A.
  - apply E.DO.fam_dp_ns, B.
  - rewrite E.DO.fam_dp_ks. exact C.
Qed.

Lemma jets_parts :
  Forall2 (fun F f => fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Kj2) f /\
                      map fst f = zrange Kj1)
    (iFJs Pn sJ Kj1 Kj2 rowsJ) (tfJs Pn sJ Kj1 Kj2 rowsJ).
Proof. exact (jets_parts_gen Pn sJ Kj1 Kj2 tjpar rowsJ HsJ LJk LJn). Qed.

Lemma jet_grid (i : nat) : (i < 9)%nat ->
  E.GO.ggrid (E.GO.gvals (nth i (iFJs Pn sJ Kj1 Kj2 rowsJ) []) (E.TTs N1 Kj1 s1) (E.Ts M Kj2 sM)) N1 M
    (fun t p => feval (tJf Pn sJ Kj1 Kj2 rowsJ i) t p) ta pb.
Proof.
  intros Hi9. unfold tJf, tfJ.
  assert (Hi : (i < length (tfJs Pn sJ Kj1 Kj2 rowsJ))%nat)
    by (unfold tfJs; rewrite length_map, length_combine, L9; simpl; lia).
  destruct (forall2_nth _ _ _ [] [] i jets_parts Hi) as [A [B C]]. apply gfam; assumption.
Qed.

Lemma gfam' (Kx Ky : nat) (F : fam_t) (f : list (Z * list (Z * (R * R)))) :
  (fam_in F f /\ List.Forall (fun kr => map fst (snd kr) = pns (Z.of_nat Pn) Ky) f /\ map fst f = zrange Kx) ->
  E.GO.ggrid (E.GO.gvals F (E.TTs N1 Kx s1) (E.Ts M Ky sM)) N1 M (fun t p => feval (cden f) t p) ta pb.
Proof. intros [A [B C]]. exact (gfam Kx Ky F f A B C). Qed.

(** Every basic grid encloses its family. *)
Lemma grids_ok :
  Forall2 (fun G B => E.GO.ggrid G N1 M (fun t p => feval B t p) ta pb) (igrids N1 M s1 sM IB) TB.
Proof.
  pose proof (dfam_parts s0 Km Kn (crows rowsR) Hs0 ltac:(unfold crows; rewrite length_map; exact LR)
                (crows_len _ _ LRn)) as PR.
  pose proof (dfam_parts s0 Km Kn (srows rowsZ) Hs0 ltac:(unfold srows; rewrite length_map; exact LZ)
                (srows_len _ _ LZn)) as PZ.
  pose proof (dfam_parts s0 Kmg Kng (crows rowsG) Hs0 ltac:(unfold crows; rewrite length_map; exact LG)
                (crows_len _ _ LGn)) as PG.
  pose proof (dfam_parts s0 Kmb Knb (srows rowsB) Hs0 ltac:(unfold srows; rewrite length_map; exact LB)
                (srows_len _ _ LBn)) as PB.
  pose proof (dfam_parts s0 Kmu Knu (crows rowsU) Hs0 ltac:(unfold crows; rewrite length_map; exact LU)
                (crows_len _ _ LUn)) as PU.
  cbv zeta in PR, PZ, PG, PB, PU.
  destruct (dt_parts _ _ _ _ PR) as [PRt PRp]. destruct (dt_parts _ _ _ _ PZ) as [PZt PZp].
  destruct (dt_parts _ _ _ _ PRt) as [PRtt PRtp]. destruct (dt_parts _ _ _ _ PZt) as [PZtt PZtp].
  destruct (dt_parts _ _ _ _ PG) as [PGt PGp]. destruct (dt_parts _ _ _ _ PB) as [PBt PBp].
  unfold IB, TB, ibasics, tbasics, igrids, iFR, iFZ, iFG, iFB, iFU, tfR, tfZ, tfG, tfB, tfU, tgs, tb, tUb.
  cbn [map app seq].
  apply Forall2_cons; [apply gfam'; exact PR |]. apply Forall2_cons; [apply gfam'; exact PRt |].
  apply Forall2_cons; [apply gfam'; exact PZt |]. apply Forall2_cons; [apply gfam'; exact PRtt |].
  apply Forall2_cons; [apply gfam'; exact PRtp |]. apply Forall2_cons; [apply gfam'; exact PZtt |].
  apply Forall2_cons; [apply gfam'; exact PZtp |]. apply Forall2_cons; [apply gfam'; exact PG |].
  apply Forall2_cons; [apply gfam'; exact PGt |]. apply Forall2_cons; [apply gfam'; exact PGp |].
  apply Forall2_cons; [apply gfam'; exact PB |]. apply Forall2_cons; [apply gfam'; exact PBt |].
  apply Forall2_cons; [apply gfam'; exact PBp |]. apply Forall2_cons; [apply gfam'; exact PU |].
  repeat (apply Forall2_cons; [apply jet_grid; lia |]). apply Forall2_nil.
Qed.

(** At every point of the grid, the enclosures of the 23 values. *)
Lemma points_ok :
  Forall2 (fun Row a => Forall2 (fun V b => Forall2 inR V (bvals Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2
                                                          rowsR rowsZ rowsG rowsB rowsU rowsJ (ta a) (pb b)))
                                 Row (seq 0 M))
          (tpoints N1 M (igrids N1 M s1 sM IB)) (seq 0 N1).
Proof.
  pose proof grids_ok as G. unfold E.GO.ggrid in G.
  pose proof (tr_rel [] (fun (Row : list J.t) (B : fser) (a : nat) =>
                           encl Row (map (fun b => feval B (ta a) (pb b)) (seq 0 M)))
                (seq 0 N1) (igrids N1 M s1 sM IB) TB G) as T1.
  rewrite length_seq in T1. unfold tpoints. apply forall2_map_l.
  eapply Forall2_impl; [| exact T1]. intros col a Hcol. cbv beta in Hcol.
  assert (Hc : Forall2 (fun row B => Forall2 (fun X b => inR X (feval B (ta a) (pb b))) row (seq 0 M)) col TB).
  { eapply Forall2_impl; [| exact Hcol]. intros row B HR.
    exact (forall2_map_r' inR (fun b => feval B (ta a) (pb b)) row (seq 0 M) HR). }
  pose proof (tr_rel J.zero (fun (X : J.t) (B : fser) (b : nat) => inR X (feval B (ta a) (pb b)))
                (seq 0 M) col TB Hc) as T2.
  rewrite length_seq in T2. eapply Forall2_impl; [| exact T2]. intros V b HV. cbv beta in HV.
  unfold bvals. fold TB. apply forall2_map_r. exact HV.
Qed.

(** At every point, the enclosures of the five values. *)
Lemma out_ok :
  Forall2 (fun Row a => Forall2 (fun O b => Forall2 inR O (tvals Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2
                                                          rowsR rowsZ rowsG rowsB rowsU rowsJ om (ta a) (pb b)))
                                 Row (seq 0 M))
          (tout OM (tpoints N1 M (igrids N1 M s1 sM IB))) (seq 0 N1).
Proof.
  pose proof points_ok as HP. unfold tout, pmap. apply forall2_map_l.
  eapply Forall2_impl; [| exact HP]. intros Row a HR. apply forall2_map_l.
  eapply Forall2_impl; [| exact HR]. intros V b HV.
  rewrite tpt_ok. exact (itpt_ok OM om V _ HOM HV).
Qed.

Lemma sel_ok (i : nat) (u : fser) :
  (forall t p, nth i (tvals Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om t p) 0
               = feval u t p) ->
  Forall2 (fun Row a => encl Row (map (fun b => feval u (ta a) (pb b)) (seq 0 M)))
          (tsel i (tout OM (tpoints N1 M (igrids N1 M s1 sM IB)))) (seq 0 N1).
Proof.
  intros Hu. pose proof out_ok as HO. unfold tsel. apply forall2_map_l.
  eapply Forall2_impl; [| exact HO]. intros Row a HR. unfold encl. apply forall2_map_l, forall2_map_r.
  eapply Forall2_impl; [| exact HR]. intros O b HOb. cbv beta. rewrite <- Hu. exact (nth_in O _ i HOb).
Qed.

(** The exact bound of one of the five from its grid. *)
Lemma box_ok (i K1 K2 : nat) (u : fser) (rho : R) (E1 E2 : J.t) :
  (forall t p, nth i (tvals Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om t p) 0
               = feval u t p) ->
  is_canon u -> is_per (Z.of_nat Pn) u -> supp K1 (Pn * K2) u ->
  (K1 <= bT1 Km Kmg Kmu Kj1)%nat -> (K2 <= bT2 Kn Kng Knu Kj2)%nat ->
  inR E1 (exp rho) -> inR E2 (exp (rho * (kappa * INR Pn))) ->
  let V := tsel i (tout OM (tpoints N1 M (igrids N1 M s1 sM IB))) in
  inR (ibox_x K1 K2 V (E.CT M K2 sM) (E.TK N1 K1 s1) (E.inv_NM N1 M) (E.WA K1 E1) (E.WB K2 E2))
      (rexact Pn N1 M K1 K2 u rho) /\ nbound rho (rexact Pn N1 M K1 K2 u rho) u.
Proof.
  intros Hu Cu Qu Su H1 H2 HE1 HE2 V. split.
  - apply (ibox_x_rexact Pn N1 M K1 K2 u HPn HN1 HM (per_grid Pn N1 M u HPn HM Qu) V (sel_ok i u Hu)
             (E.CT M K2 sM) (E.TK N1 K1 s1) (E.inv_NM N1 M) (E.ct_ok M K2 sM HM HsM) (E.tk_ok N1 K1 s1 HN1 Hs1)
             (E.inv_NM_ok Pn N1 M HN1 HM) rho (E.WA K1 E1) (E.WB K2 E2) (E.wa_ok K1 rho E1 HE1)
             (E.wb_ok Pn K2 rho E2 HE2)).
  - apply exact_nbound; [exact HPn | lia | | | exact Cu | exact Qu].
    + pose proof (Kfull_mono Pn K2 (bT2 Kn Kng Knu Kj2) H2). lia.
    + apply (supp_mono K1 (Pn * K2)); [lia | apply Kfull_ge | exact Su].
Qed.

(** The results of the check. *)
Theorem tcheck_ok :
  let res := tcheck_res in
  (inR (nth 0 res J.zero) (rexact Pn N1 M (bN1 Km Kmg) (bN2 Kn Kng) (vR Nf) w) /\
   nbound w (rexact Pn N1 M (bN1 Km Kmg) (bN2 Kn Kng) (vR Nf) w) (vR Nf)) /\
  (inR (nth 1 res J.zero) (rexact Pn N1 M (bN1 Km Kmg) (bN2 Kn Kng) (vZ Nf) w) /\
   nbound w (rexact Pn N1 M (bN1 Km Kmg) (bN2 Kn Kng) (vZ Nf) w) (vZ Nf)) /\
  (inR (nth 2 res J.zero) (rexact Pn N1 M (bK1 Km Kmg Kmu Kj1) (bK2 Kn Kng Knu Kj2) (vR kmf) wd) /\
   nbound wd (rexact Pn N1 M (bK1 Km Kmg Kmu Kj1) (bK2 Kn Kng Knu Kj2) (vR kmf) wd) (vR kmf)) /\
  (inR (nth 3 res J.zero) (rexact Pn N1 M (bK1 Km Kmg Kmu Kj1) (bK2 Kn Kng Knu Kj2) (vZ kmf) wd) /\
   nbound wd (rexact Pn N1 M (bK1 Km Kmg Kmu Kj1) (bK2 Kn Kng Knu Kj2) (vZ kmf) wd) (vZ kmf)) /\
  (inR (nth 4 res J.zero) (rexact Pn N1 M (bT1 Km Kmg Kmu Kj1) (bT2 Kn Kng Knu Kj2) Tf wd) /\
   nbound wd (rexact Pn N1 M (bT1 Km Kmg Kmu Kj1) (bT2 Kn Kng Knu Kj2) Tf wd) Tf) /\
  inR (nth 5 res J.zero) (fc Tf 0 0).
Proof.
  intros res.
  destruct (tf_canon Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om)
    as [C1 [C2 [C3 [C4 C5]]]].
  destruct (tf_per Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om HPn)
    as [Q1 [Q2 [Q3 [Q4 Q5]]]].
  destruct (SN Pn s0 Km Kn Kmg Kng Kmb Knb rowsR rowsZ rowsG rowsB HPn HBm HBn) as [S1 S2].
  destruct (SK Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om HPn HBm HBn)
    as [S3 S4].
  pose proof (ST Pn s0 sJ Km Kn Kmg Kng Kmb Knb Kmu Knu Kj1 Kj2 rowsR rowsZ rowsG rowsB rowsU rowsJ om HPn HBm HBn)
    as S5.
  fold Nf kmf Tf in C1, C2, C3, C4, C5, Q1, Q2, Q3, Q4, Q5, S1, S2, S3, S4, S5.
  assert (LN : (bN1 Km Kmg <= bT1 Km Kmg Kmu Kj1)%nat /\ (bN2 Kn Kng <= bT2 Kn Kng Knu Kj2)%nat)
    by (unfold bT1, bT2, bK1, bK2, bN1, bN2; lia).
  assert (LK : (bK1 Km Kmg Kmu Kj1 <= bT1 Km Kmg Kmu Kj1)%nat /\ (bK2 Kn Kng Knu Kj2 <= bT2 Kn Kng Knu Kj2)%nat)
    by (unfold bT1, bT2; lia).
  destruct LN as [LN1 LN2]. destruct LK as [LK1 LK2].
  unfold res, tcheck_res. cbn [nth]. unfold tOG. fold IB.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - apply (box_ok 0 _ _ (vR Nf) w Ew EwP); first [assumption | (intros; reflexivity) | lia].
  - apply (box_ok 1 _ _ (vZ Nf) w Ew EwP); first [assumption | (intros; reflexivity) | lia].
  - apply (box_ok 2 _ _ (vR kmf) wd Ewd EwdP); first [assumption | (intros; reflexivity) | lia].
  - apply (box_ok 3 _ _ (vZ kmf) wd Ewd EwdP); first [assumption | (intros; reflexivity) | lia].
  - apply (box_ok 4 _ _ Tf wd Ewd EwdP); first [assumption | (intros; reflexivity) | lia].
  - set (V := tsel 4 (tout OM (tpoints N1 M (igrids N1 M s1 sM IB)))).
    pose proof (sel_ok 4 Tf (fun t p => eq_refl)) as HV. fold V in HV.
    pose proof (GHt_ok Pn N1 M 0 Tf V HV (E.CT M 0 sM) (E.ct_ok M 0 sM HM HsM)) as HG.
    pose proof (E.tk_ok N1 0 s1 HN1 Hs1) as HT.
    assert (Z0 : zrange 0 = [0%Z]) by reflexivity. rewrite Z0 in HG, HT.
    pose proof (forall2_nth _ _ _ [] 0%Z 0 HG ltac:(simpl; lia)) as Hgh.
    pose proof (forall2_nth _ _ _ [] 0%Z 0 HT ltac:(simpl; lia)) as Htk.
    cbn [nth] in Hgh, Htk.
    change (hd [] (E.TK N1 0 s1)) with (nth 0 (E.TK N1 0 s1) []).
    change (hd [] (GHt 0 V (E.CT M 0 sM))) with (nth 0 (GHt 0 V (E.CT M 0 sM)) []).
    destruct (iCS_ok Pn N1 M Tf (E.inv_NM N1 M) (E.inv_NM_ok Pn N1 M HN1 HM) _ _ 0 0 Htk Hgh) as [HC _].
    destruct (rCS_dft Pn N1 M Tf HPn HN1 HM (per_grid Pn N1 M Tf HPn HM Q5) 0 0) as [ER _].
    rewrite ER, Z.mul_0_r in HC.
    assert (HNx' : (2 * bT1 Km Kmg Kmu Kj1 < N1)%nat) by exact HNx.
    assert (S5' : supp (bT1 Km Kmg Kmu Kj1) (Kfull (Z.of_nat Pn) (bT2 Kn Kng Knu Kj2)) Tf)
      by (apply (supp_mono (bT1 Km Kmg Kmu Kj1) (Pn * bT2 Kn Kng Knu Kj2)); [lia | apply Kfull_ge | exact S5]).
    rewrite (dftc_exact N1 (Pn * M) (bT1 Km Kmg Kmu Kj1) (Kfull (Z.of_nat Pn) (bT2 Kn Kng Knu Kj2)) Tf HNx' HMx S5' 0 0
               ltac:(simpl; lia) ltac:(simpl; lia)) in HC.
    destruct C5 as [Cc _]. unfold ccan in HC. rewrite (Cc 0%Z 0%Z) in HC.
    replace (/ 2 * (fc Tf 0 0 + fc Tf 0 0)) with (fc Tf 0 0) in HC by field. exact HC.
Qed.

End Sound.

End TCheck.

End TGrid.
