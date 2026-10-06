(** The assembly check of the three-dimensional problem, and the uniform
    invertibility of its block system.

    [assemble3d] reads the frames W_k with their approximate inverses D_k and
    rescaling exponents e_k, the ranges of the 49152 reference steps and of
    the start rows, and an approximate inverse R of the reference system M0,
    given by 14 x 14 blocks. It encloses each frame's inverse
    (Frames.winv_encl), checks every step and segment (Check3d), forms M0 from
    the reference products, and bounds |I - R M0|, |I - M0 R| and the row
    sums of |R| rho, rho the bound on the rows of the start, junction and end
    blocks of every level's system less M0's.

    [assemble3d_sound]: when the steps' and the start rows' ranges are those
    their cells' checks returned and [assemble3d] returns true, there is one q
    such that for every h = 2^-K, K >= 16, CFMS's block system of level K in
    the rescaled frames is invertible with an inverse of norm at most q. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Checker Cell Newton Mat IMat TMEval TMat Shoot Recur CFMS Step NBound Osc
  CellTM CellSound CellN CellMain Frames Assemble Check3d BMat Level3d.

Import ListNotations.
Local Open Scope R_scope.

Definition frame : Type := (list (list (Z * Z)) * list (list (Z * Z)))%type.

Section Defs.

Variable prec : F.precision.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs : imat.
Variable Rd : list (list (list (list (Z * Z)))).

Definition gW (k : nat) : list (list (Z * Z)) := fst (nth k frames ([], [])).
Definition gD (k : nat) : list (list (Z * Z)) := snd (nth k frames ([], [])).
Definition ge (k : nat) : Z := nth k es 0%Z.
Definition gcell (k i : nat) : imat := nth i (nth k cells []) [].

Definition owi (k : nat) : option imat := winv_encl prec (gW k) (gD k).
Definition gWiI (k : nat) : imat := match owi k with Some X => X | None => [] end.

(** The rescaled frame and the enclosure of its inverse. *)
Definition iWs (k : nat) : imat := itab 14 14 (fun r c => I.mul prec (Newton.dyad prec (1%Z, ge k)) (dyad prec (dentry (gW k) r c))).
Definition iWis (k : nat) : imat :=
  let WI := gWiI k in itab 14 14 (fun r c => I.mul prec (Newton.dyad prec (1%Z, (- ge k)%Z)) (iget WI r c)).

(** W_I W_(I-1)^-1, the coupling of a junction. *)
Definition iT (I : nat) : imat := imm prec 14 14 14 (iWs I) (iWis (I - 1)).
Definition iP (k : nat) : imat := iprod prec (gcell k) 4096.
Definition idl (k : nat) : I.type := delta_of prec (gcell k) 4096.

(** The start rows in the rescaled frame, and their midpoints. *)
Definition iRsS : imat := itab 5 14 (fun r c => I.mul prec (Newton.dyad prec (1%Z, (- ge 0)%Z)) (iget rs r c)).
Definition iSref : imat := itab 5 14 (fun r c => I.singleton (I.midpoint (iget iRsS r c))).

Definition ubound (X : I.type) : I.type := iupmax prec [X].

(** The reference products, the deltas of the segments and the junctions'
    couplings, each computed once. *)
Definition gPs : list imat := map iP (seq 0 12).
Definition gdls : list I.type := map idl (seq 0 12).
Definition gTs : list imat := map iT (seq 0 12).

(** The bound on row j of every level's system less M0, from the segments'
    deltas dls and the couplings Ts, and a point above it. *)
Definition irho_raw (dls : list I.type) (Ts : list imat) (j : nat) : I.type :=
  let I := (j / 14)%nat in let r := (j mod 14)%nat in
  if Nat.eqb I 0 then (if Nat.ltb r 5 then irowsum prec 14 (isub prec 5 14 iRsS iSref) r else I.zero)
  else if Nat.eqb I 12 then nth 11 dls I.zero
  else I.mul prec (irowsum prec 14 (nth I Ts []) r) (nth (I - 1) dls I.zero).

Definition irho (dls : list I.type) (Ts : list imat) (j : nat) : I.type := ubound (irho_raw dls Ts j).

Definition iD9 : imat := itab 14 14 (fun r c => I.fromZ prec (if Nat.leb 5 r && Nat.eqb r c then 1%Z else 0%Z)).
Definition iE0p : imat := itab 14 14 (fun r c => I.fromZ prec (if Nat.leb 9 r && Nat.eqb (r - 9) c && Nat.ltb c 5 then 1%Z else 0%Z)).
Definition iB00 : imat := itab 14 14 (fun r c => if Nat.ltb r 5 then iget iSref r c else I.zero).
Definition ineg (A : imat) : imat := itab 14 14 (fun r c => I.neg (iget A r c)).

(** The reference system, block by block, from the reference products Ps. *)
Definition iM0 (Ps : list imat) : bimat :=
  btab 13 (fun I K =>
    if Nat.eqb I 0 then (if Nat.eqb K 0 then iB00 else if Nat.eqb K 12 then iD9 else izmat)
    else if Nat.eqb I 12 then
      (if Nat.eqb K 11 then nth 11 Ps [] else if Nat.eqb K 12 then ineg (imm prec 14 14 14 (iWs 11) iE0p) else izmat)
    else (if Nat.eqb K (I - 1) then ineg (imm prec 14 14 14 (iT I) (nth (I - 1) Ps [])) else if Nat.eqb K I then iI prec 14
          else izmat)).

Definition iR : bimat := btab 13 (fun I K => idmat prec 14 14 (nth K (nth I Rd []) [])).

Definition iRM0 (RB M0 : bimat) : bimat := bIsub prec 13 (bmm prec 13 RB M0).
Definition iM0R (RB M0 : bimat) : bimat := bIsub prec 13 (bmm prec 13 M0 RB).

Definition rows : list (nat * nat) := list_prod (seq 0 13) (seq 0 14).

(** The first reference step's matrices are small against the reference
    step: 2^-16 nu < 1, so the first step of every level is invertible. *)
Definition psi0_ok : bool := ipos (I.sub prec (I.fromZ prec 1) (I.mul prec (ihr prec) (inu prec (gcell 0 0)))).

Definition th_of (B : bimat) : I.type := iupmax prec (map (fun Ir => browsum prec 13 B (fst Ir) (snd Ir)) rows).

(** Row (I, r) of |R| rho, R the block matrix RB and rho the list rv. *)
Definition irow1 (RB : bimat) (rv : list I.type) (I r : nat) : I.type :=
  isum prec (map (fun K => isum prec (map (fun c => I.mul prec (I.abs (iget (bget RB I K) r c)) (nth (14 * K + c) rv I.zero))
                                        (seq 0 14))) (seq 0 13)).
Definition ith1 (RB : bimat) (rv : list I.type) : I.type := iupmax prec (map (fun Ir => irow1 RB rv (fst Ir) (snd Ir)) rows).

Definition assemble3d : bool :=
  let RB := iR in
  let M0 := iM0 gPs in
  let dls := gdls in
  let Ts := gTs in
  let rv := map (irho dls Ts) (seq 0 182) in
  let rr := map (irho_raw dls Ts) (seq 0 182) in
  let RM0 := iRM0 RB M0 in
  let M0R := iM0R RB M0 in
  let th0 := th_of RM0 in
  let th2 := th_of M0R in
  let th1 := ith1 RB rv in
  forallb (fun k => match owi k with Some _ => true | None => false end) (seq 0 12) &&
  forallb (fun k => forallb (fun i => cell_ok prec (gcell k i)) (seq 0 4096)) (seq 0 12) &&
  forallb (fun k => delta_ok prec (gcell k) 4096) (seq 0 12) &&
  forallb (fun j => nonneg (I.sub prec (nth j rv I.zero) (nth j rr I.zero)) && nonneg (nth j rv I.zero)) (seq 0 182) &&
  bnorm_le prec 13 RM0 th0 && bnorm_le prec 13 M0R th2 &&
  forallb (fun Ir => nonneg (I.sub prec th1 (irow1 RB rv (fst Ir) (snd Ir)))) rows &&
  ipos (I.sub prec (I.fromZ prec 1) (I.add prec th0 th1)) && ipos (I.sub prec (I.fromZ prec 1) th2) &&
  psi0_ok.

End Defs.

Strategy expand [gW gD ge gcell owi gWiI iWs iWis iT iP idl gPs gdls gTs iRsS iSref ubound irho irho_raw iD9 iE0p
                 iB00 ineg iM0 iR iRM0 iM0R th_of irow1 ith1 psi0_ok assemble3d].

(* ---------------------------------------------------------------- *)
(* What a successful check encloses                                  *)

Lemma dyadR_pow : forall e, dyadR (1%Z, e) = powerRZ 2 e.
Proof. intros e. unfold dyadR. cbn [fst snd]. ring. Qed.

Lemma dyad_pow : forall prec e, contains (I.convert (Newton.dyad prec (1%Z, e))) (Xreal (powerRZ 2 e)).
Proof. intros prec e. rewrite <- dyadR_pow. apply dyad_correct. Qed.

Lemma nonneg_sub_le :
  forall prec A B a b, contains (I.convert A) (Xreal a) -> contains (I.convert B) (Xreal b) ->
  nonneg (I.sub prec A B) = true -> b <= a.
Proof.
  intros prec A B a b HA HB H. destruct (nonneg_correct _ _ (I.sub_correct prec _ _ _ _ HA HB) H) as [y [Ey Hy]].
  injection Ey as <-. lra.
Qed.

Lemma ineg_cont : forall A M, icont 14 14 A M -> icont 14 14 (ineg A) (fun r c => - M r c).
Proof.
  intros A M HA. apply itab_correct. intros r c Hr Hc.
  exact (I.neg_correct _ (Xreal (M r c)) (HA r c Hr Hc)).
Qed.

Lemma mrow_mm_le : forall (A B : mat) r, mrow 14 (mm 14 A B) r <= mrow 14 A r * mnorm 14 14 B.
Proof.
  intros A B r. unfold mrow at 1, mm.
  eapply Rle_trans.
  { apply (msum_le _ (fun c => msum (fun l => Rabs (A r l) * Rabs (B l c)) 14)). intros c Hc.
    eapply Rle_trans; [apply msum_abs|]. apply msum_le. intros l Hl. rewrite Rabs_mult. lra. }
  rewrite msum_swap. unfold mrow. rewrite <- msum_scal_r. apply msum_le. intros l Hl.
  rewrite msum_scal. apply Rmult_le_compat_l; [apply Rabs_pos | exact (mrow_le_mnorm 14 14 B l Hl)].
Qed.

Section Sound.

Variable prec : F.precision.
Variables d kn : nat.
Hypothesis Hcov : covered d = true.
Hypothesis Hd : (1 <= d)%nat.
Variable frames : list frame.
Variable es : list Z.
Variable cells : list (list imat).
Variable rs : imat.
Variable Rd : list (list (list (list (Z * Z)))).

Hypothesis Hcells : forall k WiI, (k < 12)%nat -> owi prec frames k = Some WiI ->
  forall j, (j < 256)%nat ->
  cell_ranges prec d (mktab d) (csc k j) chh chalf chh kn 4 (gW frames k) WiI
  = Some (map (fun q => gcell cells k (16 * j + q)%nat) (seq 0 16)).
Hypothesis Hstart : forall WiI, owi prec frames 0 = Some WiI -> start_range prec d (mktab d) chh chh kn WiI = Some rs.
Hypothesis Hok : assemble3d prec frames es cells rs Rd = true.

Let M0I : bimat := iM0 prec frames es rs (gPs prec cells).
Let dls : list I.type := gdls prec cells.
Let Ts : list imat := gTs prec frames es.
Let rv : list I.type := map (irho prec es rs dls Ts) (seq 0 182).
Let rr : list I.type := map (irho_raw prec es rs dls Ts) (seq 0 182).
Let RBI : bimat := iR prec Rd.
Let th0I : I.type := th_of prec (iRM0 prec RBI M0I).
Let th2I : I.type := th_of prec (iM0R prec RBI M0I).
Let th1I : I.type := ith1 prec RBI rv.

Lemma checks :
  (forall k, (k < 12)%nat -> exists X, owi prec frames k = Some X) /\
  (forall k i, (k < 12)%nat -> (i < 4096)%nat -> cell_ok prec (gcell cells k i) = true) /\
  (forall k, (k < 12)%nat -> delta_ok prec (gcell cells k) 4096 = true) /\
  (forall j, (j < 182)%nat ->
     nonneg (I.sub prec (nth j rv I.zero) (nth j rr I.zero)) = true /\ nonneg (nth j rv I.zero) = true) /\
  bnorm_le prec 13 (iRM0 prec RBI M0I) th0I = true /\
  bnorm_le prec 13 (iM0R prec RBI M0I) th2I = true /\
  (forall I r, (I < 13)%nat -> (r < 14)%nat -> nonneg (I.sub prec th1I (irow1 prec RBI rv I r)) = true) /\
  ipos (I.sub prec (I.fromZ prec 1) (I.add prec th0I th1I)) = true /\
  ipos (I.sub prec (I.fromZ prec 1) th2I) = true /\
  psi0_ok prec cells = true.
Proof.
  assert (H := Hok). unfold assemble3d in H. cbv zeta in H.
  apply andb_prop in H. destruct H as [H H10].
  apply andb_prop in H. destruct H as [H H9]. apply andb_prop in H. destruct H as [H H8].
  apply andb_prop in H. destruct H as [H H7]. apply andb_prop in H. destruct H as [H H6].
  apply andb_prop in H. destruct H as [H H5]. apply andb_prop in H. destruct H as [H H4].
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  rewrite forallb_forall in H1, H2, H3, H4, H7.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
  - intros k Hk. specialize (H1 k ltac:(apply in_seq; lia)). destruct (owi prec frames k) as [X|]; [exists X; reflexivity | discriminate].
  - intros k i Hk Hi. specialize (H2 k ltac:(apply in_seq; lia)). rewrite forallb_forall in H2.
    exact (H2 i ltac:(apply in_seq; lia)).
  - intros k Hk. exact (H3 k ltac:(apply in_seq; lia)).
  - intros j Hj. specialize (H4 j ltac:(apply in_seq; lia)). apply andb_prop in H4. exact H4.
  - exact H5.
  - exact H6.
  - intros I r HI Hr. exact (H7 (I, r) ltac:(unfold rows; apply in_prod; apply in_seq; lia)).
  - exact H8.
  - split; [exact H9 | exact H10].
Qed.

(** The inverse of each frame. *)
Definition Xk (k : nat) : mat := minv 14 (dmatR (gW frames k)).
Definition Ws (k : nat) : mat := scale (ge es k) (dmatR (gW frames k)).
Definition Wis (k : nat) : mat := scale (- ge es k) (Xk k).

Lemma Xk_inv :
  forall k, (k < 12)%nat ->
  is_inv 14 (dmatR (gW frames k)) (Xk k) /\ icont 14 14 (gWiI prec frames k) (Xk k) /\
  owi prec frames k = Some (gWiI prec frames k).
Proof.
  intros k Hk. destruct (proj1 checks k Hk) as [X0 HX0].
  assert (Hg : gWiI prec frames k = X0) by (unfold gWiI; rewrite HX0; reflexivity).
  destruct (winv_encl_sound prec (gW frames k) (gD frames k) X0 HX0) as [[Y HY] Hall].
  assert (HXk : is_inv 14 (dmatR (gW frames k)) (Xk k)) by exact (minv_inv 14 _ Y HY).
  split; [exact HXk|]. split; [rewrite Hg; exact (Hall _ HXk) | rewrite Hg; exact HX0].
Qed.

Lemma Ws_inv : forall k, (k < 12)%nat -> is_inv 14 (Ws k) (Wis k).
Proof. intros k Hk. apply scale_inv. exact (proj1 (Xk_inv k Hk)). Qed.

Lemma Ws_cont : forall k, icont 14 14 (iWs prec frames es k) (Ws k).
Proof.
  intros k. apply itab_correct. intros r c Hr Hc. unfold Ws, scale, dmatR.
  apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); [apply dyad_pow | apply dyad_correct].
Qed.

Lemma Wis_cont : forall k, (k < 12)%nat -> icont 14 14 (iWis prec frames es k) (Wis k).
Proof.
  intros k Hk. unfold iWis. cbv zeta. apply itab_correct. intros r c Hr Hc. unfold Wis, scale.
  apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); [apply dyad_pow | apply (proj1 (proj2 (Xk_inv k Hk))); assumption].
Qed.

Lemma T_cont : forall I, (1 <= I < 12)%nat -> icont 14 14 (iT prec frames es I) (mm 14 (Ws I) (Wis (I - 1))).
Proof. intros I HI. apply imm_correct; [apply Ws_cont | apply Wis_cont; lia]. Qed.

Definition Pref (k : nat) : mat := mprod 14 (fun i => gref (gcell cells k i)) 0 4096.
Definition dl (k : nat) : R := rmid (idl prec cells k).

Lemma P_cont : forall k, icont 14 14 (iP prec cells k) (Pref k).
Proof. intros k. apply iprod_cont. Qed.

Lemma dl_in : forall k, contains (I.convert (idl prec cells k)) (Xreal (dl k)).
Proof. intros k. unfold dl, idl, delta_of. apply iupmax_in. Qed.

Lemma dls_nth : forall k, (k < 12)%nat -> nth k dls I.zero = idl prec cells k.
Proof. intros k Hk. unfold dls, gdls. apply nth_map_seq_lt. exact Hk. Qed.

Lemma Ps_nth : forall k, (k < 12)%nat -> nth k (gPs prec cells) [] = iP prec cells k.
Proof. intros k Hk. unfold gPs. apply nth_map_seq_lt. exact Hk. Qed.

Lemma Ts_nth : forall k, (k < 12)%nat -> nth k Ts [] = iT prec frames es k.
Proof. intros k Hk. unfold Ts, gTs. apply nth_map_seq_lt. exact Hk. Qed.

Lemma rv_nth : forall j, (j < 182)%nat -> nth j rv I.zero = irho prec es rs dls Ts j.
Proof. intros j Hj. unfold rv. apply nth_map_seq_lt. exact Hj. Qed.

Lemma rr_nth : forall j, (j < 182)%nat -> nth j rr I.zero = irho_raw prec es rs dls Ts j.
Proof. intros j Hj. unfold rr. apply nth_map_seq_lt. exact Hj. Qed.

Definition rho (j : nat) : R := rmid (nth j rv I.zero).

Lemma rho_in : forall j, (j < 182)%nat -> contains (I.convert (nth j rv I.zero)) (Xreal (rho j)).
Proof. intros j Hj. unfold rho. rewrite (rv_nth j Hj). unfold irho, ubound. apply iupmax_in. Qed.

Lemma rho_ge :
  forall j x, (j < 182)%nat -> contains (I.convert (irho_raw prec es rs dls Ts j)) (Xreal x) -> x <= rho j /\ 0 <= rho j.
Proof.
  intros j x Hj Hx. destruct (proj1 (proj2 (proj2 (proj2 checks))) j Hj) as [H1 H2].
  rewrite (rr_nth j Hj) in H1.
  assert (Hs := I.sub_correct prec _ _ _ _ (rho_in j Hj) Hx).
  destruct (nonneg_correct _ _ Hs H1) as [y [Ey Hy]]. injection Ey as <-.
  destruct (nonneg_correct _ _ (rho_in j Hj) H2) as [z [Ez Hz]]. injection Ez as <-.
  split; lra.
Qed.

(* The reference system *)

Definition Sref : mat := fun r c => if Nat.ltb r 5 then rmid (iget (iRsS prec es rs) r c) else 0.
Definition Jref (k : nat) : mat := mm 14 (mm 14 (Ws (S k)) (Wis k)) (Pref k).
Definition Rr (I K : nat) : mat := dmatR (nth K (nth I Rd []) []).
Definition G0 : nat -> nat -> mat := gblock 12 Sref Jref (Pref 11) (Ws 11).

Lemma Sref_cont5 : icont 5 14 (iSref prec es rs) (fun r c => rmid (iget (iRsS prec es rs) r c)).
Proof. apply itab_correct. intros r c _ _. unfold rmid. apply I.singleton_correct. Qed.

Lemma B00_cont : icont 14 14 (iB00 prec es rs) Sref.
Proof.
  apply itab_correct. intros r c Hr Hc. unfold Sref. destruct (Nat.ltb_spec r 5) as [H5|H5].
  - apply (Sref_cont5 r c H5 Hc).
  - exact zero_contains.
Qed.

Lemma ifz_cont : forall b : bool, contains (I.convert (I.fromZ prec (if b then 1%Z else 0%Z))) (Xreal (if b then 1 else 0)).
Proof. intros [|]; apply I.fromZ_correct. Qed.

Lemma M0_cont : bcont 13 M0I G0.
Proof.
  intros I K HI HK. unfold M0I, iM0. rewrite bget_btab by assumption. unfold G0, gblock.
  replace (12 - 1)%nat with 11%nat by reflexivity.
  destruct (Nat.eqb_spec I 0) as [E0|E0].
  - destruct (Nat.eqb K 0); [apply B00_cont|].
    destruct (Nat.eqb K 12); [| apply izmat_cont].
    apply itab_correct. intros r c _ _. unfold D9. apply ifz_cont.
  - destruct (Nat.eqb_spec I 12) as [E12|E12].
    + destruct (Nat.eqb K 11); [rewrite Ps_nth by lia; apply P_cont|].
      destruct (Nat.eqb K 12); [| apply izmat_cont].
      apply ineg_cont. apply imm_correct; [apply Ws_cont|].
      apply itab_correct. intros r c _ _. unfold E0p. apply ifz_cont.
    + destruct (Nat.eqb K (I - 1)).
      * apply ineg_cont. unfold Jref. replace (S (I - 1)) with I by lia. rewrite Ps_nth by lia.
        apply imm_correct; [apply T_cont; lia | apply P_cont].
      * destruct (Nat.eqb K I); [apply iI_correct | apply izmat_cont].
Qed.

Lemma R_cont : bcont 13 (iR prec Rd) Rr.
Proof. intros I K HI HK. unfold iR. rewrite bget_btab by assumption. apply idmat_correct. Qed.

Lemma flat_ext_split :
  forall nb (A B : mat), (forall I K r c, (I < nb)%nat -> (K < nb)%nat -> (r < 14)%nat -> (c < 14)%nat ->
     A (14 * I + r)%nat (14 * K + c)%nat = B (14 * I + r)%nat (14 * K + c)%nat) ->
  mnorm (14 * nb) (14 * nb) A = mnorm (14 * nb) (14 * nb) B.
Proof.
  intros nb A B H. apply mnorm_ext. intros i j Hi Hj.
  destruct (flat_split nb i Hi) as [I [r [HI [Hr ->]]]]. destruct (flat_split nb j Hj) as [K [c [HK [Hc ->]]]].
  apply H; assumption.
Qed.

Lemma th0_bound : mnorm (14 * 13) (14 * 13) (msub mI (mm (14 * 13) (flat Rr) (flat G0))) <= rmid th0I.
Proof.
  assert (Hb := bnorm_le_correct prec 13 (iRM0 prec RBI M0I) _ th0I (rmid th0I) ltac:(lia)
                  (bIsub_cont prec 13 _ _ (bmm_cont prec 13 _ _ _ _ R_cont M0_cont))
                  ltac:(unfold th0I, th_of; apply iupmax_in) (proj1 (proj2 (proj2 (proj2 (proj2 checks)))))).
  rewrite <- (flat_ext_split 13 _ _ (fun I K r c HI HK Hr Hc => eq_refl)) in Hb.
  eapply Rle_trans; [| exact Hb]. right. apply flat_ext_split. intros I K r c HI HK Hr Hc.
  rewrite flat_entry by assumption. unfold msub. rewrite flat_mI, flat_mm by assumption.
  destruct (Nat.eqb I K); reflexivity.
Qed.

Lemma th2_bound : mnorm (14 * 13) (14 * 13) (msub mI (mm (14 * 13) (flat G0) (flat Rr))) <= rmid th2I.
Proof.
  assert (Hb := bnorm_le_correct prec 13 (iM0R prec RBI M0I) _ th2I (rmid th2I) ltac:(lia)
                  (bIsub_cont prec 13 _ _ (bmm_cont prec 13 _ _ _ _ M0_cont R_cont))
                  ltac:(unfold th2I, th_of; apply iupmax_in)
                  (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 checks))))))).
  eapply Rle_trans; [| exact Hb]. right. apply flat_ext_split. intros I K r c HI HK Hr Hc.
  rewrite flat_entry by assumption. unfold msub. rewrite flat_mI, flat_mm by assumption.
  destruct (Nat.eqb I K); reflexivity.
Qed.

Lemma th1_bound :
  forall i, (i < 14 * 13)%nat -> msum (fun j => Rabs (flat Rr i j) * rho j) (14 * 13) <= rmid th1I.
Proof.
  intros i Hi. destruct (flat_split 13 i Hi) as [I [r [HI [Hr ->]]]].
  rewrite msum_blocks. cbv beta.
  assert (Hc : contains (I.convert (irow1 prec RBI rv I r))
                 (Xreal (msum (fun K => msum (fun c => Rabs (flat Rr (14 * I + r)%nat (14 * K + c)%nat) * rho (14 * K + c)%nat)
                                               14) 13))).
  { unfold irow1. apply isum_msum. intros K HK. apply isum_msum. intros c Hc.
    rewrite flat_entry by assumption.
    apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); [| apply rho_in; lia].
    exact (I.abs_correct _ (Xreal (Rr I K r c)) (R_cont I K HI HK r c Hr Hc)). }
  assert (H7 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 checks)))))) I r HI Hr).
  assert (Hth : contains (I.convert th1I) (Xreal (rmid th1I))) by (unfold th1I, ith1; apply iupmax_in).
  exact (nonneg_sub_le prec _ _ _ _ Hth Hc H7).
Qed.

Lemma th_lt : rmid th0I + rmid th1I < 1 /\ rmid th2I < 1.
Proof.
  destruct checks as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  assert (H0 : contains (I.convert th0I) (Xreal (rmid th0I))) by (unfold th0I, th_of; apply iupmax_in).
  assert (H1 : contains (I.convert th1I) (Xreal (rmid th1I))) by (unfold th1I, ith1; apply iupmax_in).
  assert (H2 : contains (I.convert th2I) (Xreal (rmid th2I))) by (unfold th2I, th_of; apply iupmax_in).
  assert (A := I.sub_correct prec _ _ (Xreal (IZR 1)) _ (I.fromZ_correct prec 1) (I.add_correct prec _ _ _ _ H0 H1)).
  assert (B := I.sub_correct prec _ _ (Xreal (IZR 1)) _ (I.fromZ_correct prec 1) H2).
  split; [apply (sign_pos _ _ A) in H8 | apply (sign_pos _ _ B) in H9]; lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Every level                                                       *)

Lemma lenk_cutK : forall K k, lenk (cutK K) k = (4096 * fK K)%nat.
Proof. intros K k. unfold lenk, cutK. lia. Qed.

Section Level.

Variable K : nat.
Hypothesis HK : (16 <= K)%nat.

Let h : R := hK K.
Let Cs : mat := bCs (/ 4) h.

(** The propagator of segment k in its frame's coordinates. *)
Definition Pk (k : nat) : mat := mm 14 (mm 14 (Ws k) (mprod 14 (PsiK K) (cutK K k) (4096 * fK K))) (Wis k).

Lemma Pk_close : forall k, (k < 12)%nat -> mnorm 14 14 (msub (Pk k) (Pref k)) <= dl k.
Proof.
  intros k Hk. destruct (Xk_inv k Hk) as [HX [_ Howi]].
  destruct checks as (_ & Hc & Hdl & _).
  exact (seg_level prec d Hcov Hd kn (gW frames k) (gD frames k) (gWiI prec frames k) (ge es k) k (gcell cells k)
           Howi (Hcells k _ Hk Howi) (fun i Hi => Hc k i Hk Hi) (Hdl k Hk) (Xk k) HX K HK).
Qed.

Lemma start_rows : forall r, (r < 14)%nat -> mrow 14 (msub (mm 14 (padrows Cs) (Wis 0)) Sref) r <= rho r.
Proof.
  intros r Hr.
  destruct (Xk_inv 0 ltac:(lia)) as [HX [HXc Howi]].
  destruct (cell_point K 0 0 0 HK ltac:(lia) (fK_pos K)) as [_ [_ [Hw Hp]]].
  assert (HS := start_range_sound prec d Hcov Hd chh chh kn (gWiI prec frames 0) rs (Xk 0) (Hstart _ Howi) HXc
                  (hK K - dyadR chh) Hw Hp).
  replace (dyadR chh + (hK K - dyadR chh)) with h in HS by (unfold h; ring).
  destruct (Nat.ltb_spec r 5) as [H5|H5].
  - (* the start rows lie in the rescaled range *)
    assert (HR : icont 5 14 (iRsS prec es rs) (mm 14 Cs (Wis 0))).
    { apply itab_correct. intros r' c Hr' Hc. unfold Wis. rewrite mm_scale_r.
      apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); [apply dyad_pow | apply HS; assumption]. }
    assert (Hrow := irowsum_correct prec 5 14 _ _ r (isub_correct prec 5 14 _ _ _ _ HR Sref_cont5) H5).
    assert (Hraw : contains (I.convert (irho_raw prec es rs dls Ts r))
                     (Xreal (mrow 14 (msub (mm 14 Cs (Wis 0)) (fun r c => rmid (iget (iRsS prec es rs) r c))) r))).
    { unfold irho_raw. cbv zeta. rewrite Nat.div_small, Nat.mod_small by lia. cbn [Nat.eqb].
      replace (Nat.ltb r 5) with true by (symmetry; apply Nat.ltb_lt; exact H5). exact Hrow. }
    eapply Rle_trans; [| exact (proj1 (rho_ge r _ ltac:(lia) Hraw))].
    assert (Hpad : forall c, mm 14 (padrows Cs) (Wis 0) r c = mm 14 Cs (Wis 0) r c).
    { intros c. unfold mm. apply msum_ext. intros l Hl. unfold padrows.
      replace (Nat.ltb r 5) with true by (symmetry; apply Nat.ltb_lt; exact H5). reflexivity. }
    right. unfold mrow, msub. apply msum_ext. intros c Hc. rewrite Hpad. unfold Sref.
    replace (Nat.ltb r 5) with true by (symmetry; apply Nat.ltb_lt; exact H5). reflexivity.
  - assert (Hraw : contains (I.convert (irho_raw prec es rs dls Ts r)) (Xreal 0)).
    { unfold irho_raw. cbv zeta. rewrite Nat.div_small, Nat.mod_small by lia. cbn [Nat.eqb].
      replace (Nat.ltb r 5) with false by (symmetry; apply Nat.ltb_ge; exact H5). exact zero_contains. }
    eapply Rle_trans; [| exact (proj2 (rho_ge r 0 ltac:(lia) Hraw))].
    right. unfold mrow, msub. rewrite (msum_ext _ (fun _ => 0)); [apply msum_zero|].
    intros c Hc. unfold Sref. replace (Nat.ltb r 5) with false by (symmetry; apply Nat.ltb_ge; exact H5).
    unfold mm, padrows. rewrite (msum_ext _ (fun _ => 0)).
    + rewrite msum_zero. replace (0 - 0) with 0 by ring. apply Rabs_R0.
    + intros l Hl. replace (Nat.ltb r 5) with false by (symmetry; apply Nat.ltb_ge; exact H5). ring.
Qed.

Lemma mm_msub_r : forall (A B C : mat) i j, mm 14 A (msub B C) i j = mm 14 A B i j - mm 14 A C i j.
Proof. intros. unfold mm, msub. rewrite <- msum_minus. apply msum_ext. intros; ring. Qed.

(** A junction is the coupling W_I W_k^-1 times the propagator in frame k. *)
Lemma jun_split :
  forall k, (k < 12)%nat ->
  meq 14 (jun (PsiK K) (cutK K) Ws Wis k) (mm 14 (mm 14 (Ws (S k)) (Wis k)) (Pk k)).
Proof.
  intros k Hk. unfold jun, Yk. rewrite lenk_cutK. unfold Pk.
  set (Y := mprod 14 (PsiK K) (cutK K k) (4096 * fK K)).
  assert (HI : meq 14 (mm 14 (Wis k) (Ws k)) mI) by (intros i j Hi Hj; exact (proj1 (Ws_inv k Hk i j Hi Hj))).
  apply meq_sym.
  eapply meq_trans; [apply mm_assoc_meq|].
  apply mm_meq; [apply meq_refl|].
  eapply meq_trans; [apply meq_sym; apply mm_assoc_meq|].
  apply mm_meq; [| apply meq_refl].
  eapply meq_trans; [apply meq_sym; apply mm_assoc_meq|].
  eapply meq_trans; [apply mm_meq; [exact HI | apply meq_refl]|].
  apply mm_mI_meq_l.
Qed.

Lemma junction_rows :
  forall I r, (1 <= I < 12)%nat -> (r < 14)%nat ->
  mrow 14 (msub (jun (PsiK K) (cutK K) Ws Wis (I - 1)%nat) (Jref (I - 1)%nat)) r <= rho (14 * I + r)%nat.
Proof.
  intros I r HI Hr.
  set (k := (I - 1)%nat). assert (Hk : (k < 12)%nat) by (unfold k; lia).
  assert (HSk : S k = I) by (unfold k; lia).
  set (T := mm 14 (Ws (S k)) (Wis k)).
  assert (HD : forall c, (c < 14)%nat ->
             msub (jun (PsiK K) (cutK K) Ws Wis k) (Jref k) r c = mm 14 T (msub (Pk k) (Pref k)) r c).
  { intros c Hc. rewrite mm_msub_r. unfold msub. rewrite (jun_split k Hk r c Hr Hc). reflexivity. }
  assert (Hrow : mrow 14 (msub (jun (PsiK K) (cutK K) Ws Wis k) (Jref k)) r = mrow 14 (mm 14 T (msub (Pk k) (Pref k))) r)
    by (unfold mrow; apply msum_ext; intros c Hc; rewrite (HD c Hc); reflexivity).
  rewrite Hrow.
  eapply Rle_trans; [apply mrow_mm_le|].
  assert (HT0 : 0 <= mrow 14 T r) by (unfold mrow; apply msum_nonneg; intros; apply Rabs_pos).
  eapply Rle_trans; [apply Rmult_le_compat_l; [exact HT0 | exact (Pk_close k Hk)]|].
  assert (Hraw : contains (I.convert (irho_raw prec es rs dls Ts (14 * I + r))) (Xreal (mrow 14 T r * dl k))).
  { unfold irho_raw. cbv zeta. rewrite div14, mod14 by exact Hr.
    replace (Nat.eqb I 0) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb I 12) with false by (symmetry; apply Nat.eqb_neq; lia).
    fold k. rewrite dls_nth by exact Hk. rewrite Ts_nth by lia.
    apply (I.mul_correct prec _ _ (Xreal _) (Xreal _)); [| apply dl_in].
    apply (irowsum_correct prec 14 14 _ _ r); [| exact Hr]. unfold T. rewrite HSk. apply T_cont. lia. }
  exact (proj1 (rho_ge (14 * I + r)%nat _ ltac:(lia) Hraw)).
Qed.

Lemma end_rows :
  forall r, (r < 14)%nat -> mrow 14 (msub (endb (PsiK K) 12 (cutK K) Wis (Ws 11)) (Pref 11)) r <= rho (14 * 12 + r)%nat.
Proof.
  intros r Hr.
  assert (HE : forall c, (c < 14)%nat -> endb (PsiK K) 12 (cutK K) Wis (Ws 11) r c = Pk 11 r c).
  { intros c Hc. unfold endb, Yk, Pk. rewrite lenk_cutK. replace (12 - 1)%nat with 11%nat by reflexivity.
    symmetry. apply mm_assoc. }
  assert (Hrow : mrow 14 (msub (endb (PsiK K) 12 (cutK K) Wis (Ws 11)) (Pref 11)) r = mrow 14 (msub (Pk 11) (Pref 11)) r)
    by (unfold mrow, msub; apply msum_ext; intros c Hc; rewrite (HE c Hc); reflexivity).
  rewrite Hrow.
  eapply Rle_trans; [exact (mrow_le_mnorm 14 14 _ r Hr)|].
  eapply Rle_trans; [exact (Pk_close 11 ltac:(lia))|].
  assert (Hraw : contains (I.convert (irho_raw prec es rs dls Ts (14 * 12 + r))) (Xreal (dl 11))).
  { unfold irho_raw. cbv zeta. rewrite div14, mod14 by exact Hr. cbn [Nat.eqb]. rewrite dls_nth by lia. apply dl_in. }
  exact (proj1 (rho_ge (14 * 12 + r)%nat _ ltac:(lia) Hraw)).
Qed.

End Level.

(** Every level's block system is invertible, with one bound on the norm of
    its inverse. *)
Theorem assemble3d_sound :
  exists q, forall K, (16 <= K)%nat ->
  let M := msys (PsiK K) 12 (cutK K) Ws Wis (bCs (/ 4) (hK K)) (Ws 11) in
  exists X,
    (forall i j, (i < 14 * 13)%nat -> (j < 14 * 13)%nat -> mm (14 * 13) X M i j = mI i j) /\
    (forall i j, (i < 14 * 13)%nat -> (j < 14 * 13)%nat -> mm (14 * 13) M X i j = mI i j) /\
    mnorm (14 * 13) (14 * 13) X <= q.
Proof.
  exists (mnorm (14 * 13) (14 * 13) (flat Rr) / (1 - (rmid th0I + rmid th1I))).
  intros K HK M.
  destruct th_lt as [Hlt0 Hlt2].
  destruct (block_system_inverse 12 (mm 14 (padrows (bCs (/ 4) (hK K))) (Wis 0)) (jun (PsiK K) (cutK K) Ws Wis)
              (endb (PsiK K) 12 (cutK K) Wis (Ws 11)) Sref Jref (Pref 11) (Ws 11) (flat Rr) rho
              (rmid th0I) (rmid th1I) (rmid th2I) ltac:(lia)
              th0_bound th2_bound Hlt2 (start_rows K HK) (junction_rows K HK) (end_rows K HK) th1_bound Hlt0)
    as [X [H1 [H2 H3]]].
  exists X. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

End Sound.
