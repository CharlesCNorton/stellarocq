(** A dense family split by a mask of modes, and the reference torus.

    A map of the coefficients of a dense family that keeps its modes
    ([fam_map]) lists the same entries with new coefficients. When two such
    maps add up to the identity, the family is the sum of the two it gives
    ([cden_split]), so the family less the first is the second
    ([cden_sub_split]); a map that clears every coefficient outside a box
    gives a family carried by that box ([cden_mask_supp]). With the mask of a
    small box this splits a torus into a reference torus of few modes and a
    tail whose norm bounds their distance. The interval families follow the
    same maps ([ifam_map_in]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierParity FourierDFT FourierCanon FourierPer FourierList FourierModel FourierSupp KAMVec
  KFix KCheckKern KEngine KDense KSrc.
Import ListNotations.
Local Open Scope R_scope.

Definition fam_map (g : Z -> Z -> R * R -> R * R) (f : list (Z * list (Z * (R * R)))) :
    list (Z * list (Z * (R * R))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, g (fst kr) (fst e) (snd e))) (snd kr))) f.

Definition emap (g : Z -> Z -> R * R -> R * R) (e : fent) : fent :=
  let cs := g (fe_m e) (fe_n e) (fe_c e, fe_s e) in mkfent (fe_m e) (fe_n e) (fst cs) (snd cs).

Lemma dents_fam_map (g : Z -> Z -> R * R -> R * R) (f : list (Z * list (Z * (R * R)))) :
  dents (fam_map g f) = map (emap g) (dents f).
Proof.
  induction f as [| [k row] f IH]; [reflexivity |].
  unfold dents, fam_map in *. cbn [flat_map map fst snd]. rewrite map_app, IH. f_equal.
  rewrite !map_map. apply map_ext. intros [n [c s]]. unfold emap. cbn [fst snd fe_m fe_n fe_c fe_s].
  destruct (g k n (c, s)) as [c' s']. reflexivity.
Qed.

Lemma flist_split (h1 h2 : fent -> fent) (es : list fent) :
  (forall e, fe_m (h1 e) = fe_m e /\ fe_n (h1 e) = fe_n e /\ fe_m (h2 e) = fe_m e /\ fe_n (h2 e) = fe_n e /\
             fe_c (h1 e) + fe_c (h2 e) = fe_c e /\ fe_s (h1 e) + fe_s (h2 e) = fe_s e) ->
  feq (flist es) (fadd (flist (map h1 es)) (flist (map h2 es))).
Proof.
  intros H. induction es as [| e es IH].
  - intros m n. simpl. split; ring.
  - intros m n. cbn [map]. rewrite !flist_cons. destruct (IH m n) as [A B].
    destruct (H e) as [E1 [E2 [E3 [E4 [E5 E6]]]]].
    unfold fadd, fsingle, at2 in *. simpl in *. rewrite A, B, E1, E2, E3, E4, <- E5, <- E6.
    destruct (_ && _)%bool; split; ring.
Qed.

Lemma canon_fadd_feq (u v : fser) : feq (canon (fadd u v)) (fadd (canon u) (canon v)).
Proof. intros m n. unfold canon, ccan, scan, fadd. simpl. split; ring. Qed.

Section Split.

Variables (g1 g2 : Z -> Z -> R * R -> R * R).
Hypothesis Hg : forall k n cs, fst (g1 k n cs) + fst (g2 k n cs) = fst cs /\ snd (g1 k n cs) + snd (g2 k n cs) = snd cs.

Theorem cden_split (f : list (Z * list (Z * (R * R)))) :
  feq (cden f) (fadd (cden (fam_map g1 f)) (cden (fam_map g2 f))).
Proof.
  unfold cden. rewrite !dents_fam_map.
  eapply feq_trans; [apply canon_feq_congr, (flist_split (emap g1) (emap g2)) |].
  - intros [m n c s]. unfold emap. cbn [fe_m fe_n fe_c fe_s]. destruct (Hg m n (c, s)) as [A B].
    repeat split; assumption.
  - apply canon_fadd_feq.
Qed.

Theorem cden_sub_split (f : list (Z * list (Z * (R * R)))) :
  feq (fsub (cden f) (cden (fam_map g1 f))) (cden (fam_map g2 f)).
Proof.
  intros m n. destruct (cden_split f m n) as [A B]. unfold fsub, fadd, fscal in *. simpl in *.
  rewrite A, B. split; ring.
Qed.

End Split.

(** * The mask of a box and its complement *)

Definition gmask (K1 K2 : nat) (k n : Z) (cs : R * R) : R * R := if in_box K1 K2 k n then cs else (0, 0).
Definition gtail (K1 K2 : nat) (k n : Z) (cs : R * R) : R * R := if in_box K1 K2 k n then (0, 0) else cs.

Lemma gmask_tail (K1 K2 : nat) (k n : Z) (cs : R * R) :
  fst (gmask K1 K2 k n cs) + fst (gtail K1 K2 k n cs) = fst cs /\
  snd (gmask K1 K2 k n cs) + snd (gtail K1 K2 k n cs) = snd cs.
Proof. unfold gmask, gtail. destruct (in_box K1 K2 k n); simpl; split; ring. Qed.

Lemma fsingle_zero_supp (K1 K2 : nat) (k n : Z) : supp K1 K2 (fsingle k n 0 0).
Proof. intros m p _. unfold fsingle, at2. simpl. destruct (_ && _)%bool; split; reflexivity. Qed.

Theorem cden_mask_supp (K1 K2 : nat) (f : list (Z * list (Z * (R * R)))) :
  supp K1 K2 (cden (fam_map (gmask K1 K2) f)).
Proof.
  unfold cden. apply supp_canon. rewrite dents_fam_map. generalize (dents f). intros es.
  induction es as [| e es IH]; [intros m n _; simpl; split; reflexivity |].
  cbn [map]. rewrite flist_cons. apply fadd_supp; [| exact IH].
  unfold emap, gmask. cbn [fe_m fe_n fe_c fe_s].
  destruct (in_box K1 K2 (fe_m e) (fe_n e)) eqn:E; cbn [fst snd].
  - apply fsingle_supp; unfold in_box in E; apply andb_prop in E; destruct E as [E1 E2];
      apply Z.leb_le in E1, E2; lia.
  - apply fsingle_zero_supp.
Qed.

(** The maps keep the classes of the family. *)
Lemma emap_even (g : Z -> Z -> R * R -> R * R) (es : list fent) :
  (forall k n c, snd (g k n (c, 0)) = 0) -> Forall (fun e => fe_s e = 0) es -> Forall (fun e => fe_s e = 0) (map (emap g) es).
Proof.
  intros Hg H. induction H as [| e es He _ IH]; [constructor |]. cbn [map]. constructor; [| exact IH].
  unfold emap. cbn [fe_s]. rewrite He. apply Hg.
Qed.

Lemma emap_odd (g : Z -> Z -> R * R -> R * R) (es : list fent) :
  (forall k n s, fst (g k n (0, s)) = 0) -> Forall (fun e => fe_c e = 0) es -> Forall (fun e => fe_c e = 0) (map (emap g) es).
Proof.
  intros Hg H. induction H as [| e es He _ IH]; [constructor |]. cbn [map]. constructor; [| exact IH].
  unfold emap. cbn [fe_c]. rewrite He. apply Hg.
Qed.

Lemma emap_modes (g : Z -> Z -> R * R -> R * R) (Pe : Z -> Prop) (es : list fent) :
  Forall (fun e => Pe (fe_n e)) es -> Forall (fun e => Pe (fe_n e)) (map (emap g) es).
Proof. intros H. induction H as [| e es He _ IH]; [constructor |]. cbn [map]. constructor; [exact He | exact IH]. Qed.

Lemma gmask_c0 (K1 K2 : nat) (k n : Z) (x : R) : snd (gmask K1 K2 k n (x, 0)) = 0.
Proof. unfold gmask. destruct (in_box K1 K2 k n); reflexivity. Qed.
Lemma gmask_s0 (K1 K2 : nat) (k n : Z) (x : R) : fst (gmask K1 K2 k n (0, x)) = 0.
Proof. unfold gmask. destruct (in_box K1 K2 k n); reflexivity. Qed.

Theorem cden_mask_even (K1 K2 : nat) (s : Z) (ks ns : list Z) (rows : list (list Z)) :
  is_even (cden (fam_map (gmask K1 K2) (dfam s ks ns (crows rows)))).
Proof.
  unfold cden. apply canon_even, flist_even. rewrite dents_fam_map.
  apply emap_even; [intros k n c; apply gmask_c0 |].
  apply dfam_forall. intros k n c sn _ _ H.
  unfold crows in H. rewrite <- concat_map in H. apply in_map_iff in H.
  destruct H as [m [Em _]]. inversion Em; subst. cbn [fe_s]. apply dy_0.
Qed.

Theorem cden_mask_odd (K1 K2 : nat) (s : Z) (ks ns : list Z) (rows : list (list Z)) :
  is_odd (cden (fam_map (gmask K1 K2) (dfam s ks ns (srows rows)))).
Proof.
  unfold cden. apply canon_odd, flist_odd. rewrite dents_fam_map.
  apply emap_odd; [intros k n x; apply gmask_s0 |].
  apply dfam_forall. intros k n c sn _ _ H.
  unfold srows in H. rewrite <- concat_map in H. apply in_map_iff in H.
  destruct H as [m [Em _]]. inversion Em; subst. cbn [fe_c]. apply dy_0.
Qed.

Theorem cden_mask_per (K1 K2 : nat) (P : Z) (s : Z) (ks : list Z) (Kn : nat) (rows : list (list (Z * Z))) :
  (0 < P)%Z -> is_per P (cden (fam_map (gmask K1 K2) (dfam s ks (pns P Kn) rows))).
Proof.
  intros HP. unfold cden. apply canon_per, flist_per. rewrite dents_fam_map.
  apply (emap_modes _ (fun n => (n mod P = 0)%Z)).
  apply dfam_forall. intros k n c sn _ Hn _.
  unfold pns in Hn. apply in_map_iff in Hn. destruct Hn as [l [El _]]. subst n. cbn [fe_n].
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(** * Interval families under the maps *)

Module RefOps (J : RI).

Module DO := DenseOps J.
Import DO DO.EN DO.EN.KO.

Definition imask (K1 K2 : nat) (F : list (Z * list (Z * (J.t * J.t)))) : list (Z * list (Z * (J.t * J.t))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, if in_box K1 K2 (fst kr) (fst e) then snd e else (J.zero, J.zero)))
                             (snd kr))) F.
Definition itail (K1 K2 : nat) (F : list (Z * list (Z * (J.t * J.t)))) : list (Z * list (Z * (J.t * J.t))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, if in_box K1 K2 (fst kr) (fst e) then (J.zero, J.zero) else snd e))
                             (snd kr))) F.

Theorem imask_in (K1 K2 : nat) (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) :
  fam_in F f -> fam_in (imask K1 K2 F) (fam_map (gmask K1 K2) f).
Proof.
  intros H. induction H as [| I e F f [Ek HR] _ IH]; [constructor |].
  cbn [imask fam_map map]. constructor; [| exact IH]. cbn [fst snd]. split; [exact Ek |].
  rewrite Ek. clear -HR. induction HR as [| Ie re row rs [En [HC HS]] _ IHr]; [constructor |].
  cbn [map]. constructor; [| exact IHr]. cbn [fst snd]. split; [exact En |].
  rewrite En. unfold gmask. destruct (in_box K1 K2 (fst e) (fst re)); cbn [fst snd];
    [split; assumption | split; apply inR_zero].
Qed.

Theorem itail_in (K1 K2 : nat) (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) :
  fam_in F f -> fam_in (itail K1 K2 F) (fam_map (gtail K1 K2) f).
Proof.
  intros H. induction H as [| I e F f [Ek HR] _ IH]; [constructor |].
  cbn [itail fam_map map]. constructor; [| exact IH]. cbn [fst snd]. split; [exact Ek |].
  rewrite Ek. clear -HR. induction HR as [| Ie re row rs [En [HC HS]] _ IHr]; [constructor |].
  cbn [map]. constructor; [| exact IHr]. cbn [fst snd]. split; [exact En |].
  rewrite En. unfold gtail. destruct (in_box K1 K2 (fst e) (fst re)); cbn [fst snd];
    [split; apply inR_zero | split; assumption].
Qed.

Lemma fam_map_ns (g : Z -> Z -> R * R -> R * R) (f : list (Z * list (Z * (R * R)))) (ns : list Z) :
  Forall (fun kr => map fst (snd kr) = ns) f -> Forall (fun kr => map fst (snd kr) = ns) (fam_map g f).
Proof.
  intros H. induction H as [| kr f Hk _ IH]; [constructor |]. cbn [fam_map map]. constructor; [| exact IH].
  cbn [snd]. rewrite map_map. rewrite <- Hk. apply map_ext. intros e. reflexivity.
Qed.

Lemma fam_map_ks (g : Z -> Z -> R * R -> R * R) (f : list (Z * list (Z * (R * R)))) :
  map fst (fam_map g f) = map fst f.
Proof. unfold fam_map. rewrite map_map. reflexivity. Qed.

End RefOps.
