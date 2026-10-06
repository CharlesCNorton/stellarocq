(** Dense finite families as canonical families, and their derivatives.

    The certificate gives each finite family as rows of coefficients over a
    box of modes; the family itself is the canonical form of their sum,
    [cden f], which has the same values ([feval_cden]) and the norm of the
    weighted sum of the coefficients ([nbound_cden]). Its derivatives in t
    and p are the dense families with each coefficient pair turned by the
    mode ([fam_dt], [fam_dp]), so their values are read the same way
    ([feval_dt_cden], [feval_dp_cden]); the interval families of the
    derivatives are formed by the same exact scalings ([ifam_dt_in],
    [ifam_dp_in]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierParity FourierDFT FourierCanon FourierPer FourierList KAMVec KFix KCheckKern KEngine.
Import ListNotations.
Local Open Scope R_scope.

Definition cden (f : list (Z * list (Z * (R * R)))) : fser := canon (flist (dents f)).

Lemma cden_canon (f : list (Z * list (Z * (R * R)))) : is_canon (cden f).
Proof. apply canon_is_canon. Qed.

Theorem nbound_cden (w : R) (f : list (Z * list (Z * (R * R)))) : nbound w (esum (ewt w) (dents f)) (cden f).
Proof. apply nbound_canon, nbound_flist. Qed.

Theorem feval_cden (f : list (Z * list (Z * (R * R)))) (t p : R) : feval (cden f) t p = dval f t p.
Proof.
  unfold cden. rewrite (feval_canon _ (esum (ewt 0) (dents f)) t p (nbound_flist 0 _)). apply feval_dents.
Qed.

Definition fam_dt (f : list (Z * list (Z * (R * R)))) : list (Z * list (Z * (R * R))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, (IZR (fst kr) * snd (snd e), - (IZR (fst kr) * fst (snd e))))) (snd kr))) f.
Definition fam_dp (f : list (Z * list (Z * (R * R)))) : list (Z * list (Z * (R * R))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, (IZR (fst e) * snd (snd e), - (IZR (fst e) * fst (snd e))))) (snd kr))) f.

Lemma dents_dt (f : list (Z * list (Z * (R * R)))) : map edt (dents f) = dents (fam_dt f).
Proof.
  induction f as [| [k row] f IH]; [reflexivity |].
  unfold dents, fam_dt in *. cbn [flat_map map fst snd]. rewrite map_app, IH. f_equal.
  rewrite !map_map. apply map_ext. intros [n [c s]]. reflexivity.
Qed.

Lemma dents_dp (f : list (Z * list (Z * (R * R)))) : map edp (dents f) = dents (fam_dp f).
Proof.
  induction f as [| [k row] f IH]; [reflexivity |].
  unfold dents, fam_dp in *. cbn [flat_map map fst snd]. rewrite map_app, IH. f_equal.
  rewrite !map_map. apply map_ext. intros [n [c s]]. reflexivity.
Qed.

Lemma dt_canon_feq (u : fser) : feq (dt (canon u)) (canon (dt u)).
Proof.
  intros m n. unfold canon, ccan, scan, dt. simpl. rewrite !opp_IZR. split; ring.
Qed.

Lemma dp_canon_feq (u : fser) : feq (dp (canon u)) (canon (dp u)).
Proof.
  intros m n. unfold canon, ccan, scan, dp. simpl. rewrite !opp_IZR. split; ring.
Qed.

Lemma canon_feq_congr (u v : fser) : feq u v -> feq (canon u) (canon v).
Proof.
  intros H m n. unfold canon, ccan, scan. simpl.
  destruct (H m n) as [A B]. destruct (H (- m)%Z (- n)%Z) as [C D]. rewrite A, B, C, D. split; ring.
Qed.

Theorem dt_cden (f : list (Z * list (Z * (R * R)))) : feq (dt (cden f)) (cden (fam_dt f)).
Proof.
  unfold cden. eapply feq_trans; [apply dt_canon_feq |]. apply canon_feq_congr.
  rewrite <- dents_dt. apply dt_flist.
Qed.

Theorem dp_cden (f : list (Z * list (Z * (R * R)))) : feq (dp (cden f)) (cden (fam_dp f)).
Proof.
  unfold cden. eapply feq_trans; [apply dp_canon_feq |]. apply canon_feq_congr.
  rewrite <- dents_dp. apply dp_flist.
Qed.

Theorem feval_dt_cden (f : list (Z * list (Z * (R * R)))) (t p : R) :
  feval (dt (cden f)) t p = dval (fam_dt f) t p.
Proof. rewrite (feval_feq _ _ t p (dt_cden f)). apply feval_cden. Qed.

Theorem feval_dp_cden (f : list (Z * list (Z * (R * R)))) (t p : R) :
  feval (dp (cden f)) t p = dval (fam_dp f) t p.
Proof. rewrite (feval_feq _ _ t p (dp_cden f)). apply feval_cden. Qed.

(** * Families from certificate data

    A number of the certificate is a mantissa m at a common scale s, the real
    m / 2^s. A dense family is given by its rows of mantissa pairs over the
    modes ks x ns. *)

Definition dy (s m : Z) : R := IZR m / IZR (2 ^ s).

Definition dfam (s : Z) (ks ns : list Z) (rows : list (list (Z * Z))) : list (Z * list (Z * (R * R))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, (dy s (fst (snd e)), dy s (snd (snd e))))) (combine ns (snd kr))))
      (combine ks rows).

Lemma dfam_ns (s : Z) (ks ns : list Z) (rows : list (list (Z * Z))) :
  Forall (fun r => length r = length ns) rows ->
  Forall (fun kr => map fst (snd kr) = ns) (dfam s ks ns rows).
Proof.
  intros H. unfold dfam. revert ks. induction H as [| r rows Hr _ IH]; intros ks.
  - destruct ks; constructor.
  - destruct ks as [| k ks]; [constructor |]. cbn [combine map]. constructor; [| apply IH].
    cbn [snd]. rewrite map_map. cbn [fst]. clear -Hr. revert r Hr.
    induction ns as [| n ns IHn]; intros r Hr; [reflexivity |].
    destruct r as [| x r]; [discriminate |]. cbn [combine map]. f_equal. apply IHn. simpl in Hr. lia.
Qed.

Lemma dfam_ks (s : Z) (ks ns : list Z) (rows : list (list (Z * Z))) :
  length rows = length ks -> map fst (dfam s ks ns rows) = ks.
Proof.
  unfold dfam. rewrite map_map. revert rows. induction ks as [| k ks IH]; intros rows H; [reflexivity |].
  destruct rows as [| r rows]; [discriminate |]. cbn [combine map]. f_equal. apply IH. simpl in H. lia.
Qed.

(** Every entry of a family from data is a mode of ks x ns with coefficients
    from the rows. *)
Lemma dfam_forall (Pe : fent -> Prop) (s : Z) (ks ns : list Z) (rows : list (list (Z * Z))) :
  (forall k n c sn, In k ks -> In n ns -> In (c, sn) (concat rows) -> Pe (mkfent k n (dy s c) (dy s sn))) ->
  Forall Pe (dents (dfam s ks ns rows)).
Proof.
  intros H. apply Forall_forall. intros e He. unfold dents in He. apply in_flat_map in He.
  destruct He as [kr [Hkr He]]. unfold dfam in Hkr. apply in_map_iff in Hkr. destruct Hkr as [[k r] [Ekr Hkr]].
  subst kr. cbn [fst snd] in He. apply in_map_iff in He. destruct He as [[n [c' s']] [Ee He]].
  apply in_map_iff in He. destruct He as [[n' [c sn]] [En He]]. cbn [fst snd] in En. inversion En; subst n' c' s'.
  subst e. apply H.
  - exact (in_combine_l _ _ _ _ Hkr).
  - exact (in_combine_l _ _ _ _ He).
  - apply in_concat. exists r. split; [exact (in_combine_r _ _ _ _ Hkr) | exact (in_combine_r _ _ _ _ He)].
Qed.

(** Rows of cosine mantissas alone, and of sine mantissas alone. *)
Definition crows (rows : list (list Z)) : list (list (Z * Z)) := map (map (fun m => (m, 0%Z))) rows.
Definition srows (rows : list (list Z)) : list (list (Z * Z)) := map (map (fun m => (0%Z, m))) rows.

Lemma crows_len (rows : list (list Z)) (n : nat) :
  Forall (fun r => length r = n) rows -> Forall (fun r => length r = n) (crows rows).
Proof. intros H. unfold crows. apply Forall_map. eapply Forall_impl; [| exact H]. intros r Hr. rewrite length_map. exact Hr. Qed.

Lemma srows_len (rows : list (list Z)) (n : nat) :
  Forall (fun r => length r = n) rows -> Forall (fun r => length r = n) (srows rows).
Proof. intros H. unfold srows. apply Forall_map. eapply Forall_impl; [| exact H]. intros r Hr. rewrite length_map. exact Hr. Qed.

Lemma dy_0 (s : Z) : dy s 0 = 0.
Proof. unfold dy. simpl. unfold Rdiv. ring. Qed.

Theorem cden_even (s : Z) (ks ns : list Z) (rows : list (list Z)) : is_even (cden (dfam s ks ns (crows rows))).
Proof.
  unfold cden. apply canon_even, flist_even. apply dfam_forall. intros k n c sn _ _ H.
  unfold crows in H. rewrite <- concat_map in H. apply in_map_iff in H.
  destruct H as [m [Em _]]. inversion Em; subst. cbn [fe_s]. apply dy_0.
Qed.

Theorem cden_odd (s : Z) (ks ns : list Z) (rows : list (list Z)) : is_odd (cden (dfam s ks ns (srows rows))).
Proof.
  unfold cden. apply canon_odd, flist_odd. apply dfam_forall. intros k n c sn _ _ H.
  unfold srows in H. rewrite <- concat_map in H. apply in_map_iff in H.
  destruct H as [m [Em _]]. inversion Em; subst. cbn [fe_c]. apply dy_0.
Qed.

(** The toroidal modes P l of a family of period P. *)
Definition pns (P : Z) (Kn : nat) : list Z := map (fun l => (P * l)%Z) (zrange Kn).

Theorem cden_per (P : Z) (s : Z) (ks : list Z) (Kn : nat) (rows : list (list (Z * Z))) :
  (0 < P)%Z -> is_per P (cden (dfam s ks (pns P Kn) rows)).
Proof.
  intros HP. unfold cden. apply canon_per, flist_per. apply dfam_forall. intros k n c sn _ Hn _.
  unfold pns in Hn. apply in_map_iff in Hn. destruct Hn as [l [El _]]. subst n. cbn [fe_n].
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(** * Interval families of the derivatives *)

Module DenseOps (J : RI).

Module EN := Engine J.
Import EN EN.KO.

(** The interval family of certificate data, each number enclosed at its scale. *)
Definition ifam (s : Z) (ks ns : list Z) (rows : list (list (Z * Z))) : list (Z * list (Z * (J.t * J.t))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, (J.of_q (fst (snd e)) s, J.of_q (snd (snd e)) s))) (combine ns (snd kr))))
      (combine ks rows).

Theorem ifam_in (s : Z) (ks ns : list Z) (rows : list (list (Z * Z))) :
  (0 <= s)%Z -> fam_in (ifam s ks ns rows) (dfam s ks ns rows).
Proof.
  intros Hs. unfold ifam, dfam. generalize (combine ks rows). intros l.
  induction l as [| [k r] l IH]; [constructor |]. cbn [map]. constructor; [| exact IH]. cbn [fst snd].
  split; [reflexivity |]. generalize (combine ns r). intros es.
  induction es as [| [n [c s']] es IHe]; [constructor |]. cbn [map]. constructor; [| exact IHe].
  cbn [fst snd]. split; [reflexivity |]. split; apply inR_q, Hs.
Qed.

Definition ifam_dt (F : list (Z * list (Z * (J.t * J.t)))) : list (Z * list (Z * (J.t * J.t))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, (J.mul (J.of_q (fst kr) 0) (snd (snd e)),
                                                 J.neg (J.mul (J.of_q (fst kr) 0) (fst (snd e)))))) (snd kr))) F.
Definition ifam_dp (F : list (Z * list (Z * (J.t * J.t)))) : list (Z * list (Z * (J.t * J.t))) :=
  map (fun kr => (fst kr, map (fun e => (fst e, (J.mul (J.of_q (fst e) 0) (snd (snd e)),
                                                 J.neg (J.mul (J.of_q (fst e) 0) (fst (snd e)))))) (snd kr))) F.

Theorem ifam_dt_in (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) :
  fam_in F f -> fam_in (ifam_dt F) (fam_dt f).
Proof.
  intros H. induction H as [| I e F f [Ek HR] _ IH]; [constructor |].
  cbn [ifam_dt fam_dt map]. constructor; [| exact IH]. cbn [fst snd]. split; [exact Ek |].
  rewrite Ek. clear -HR. induction HR as [| Ie re row rs [En [HC HS]] _ IHr]; [constructor |].
  cbn [map]. constructor; [| exact IHr]. cbn [fst snd]. split; [exact En |].
  split; [apply inR_mul; [apply inR_Z | exact HS] | apply inR_neg, inR_mul; [apply inR_Z | exact HC]].
Qed.

Theorem ifam_dp_in (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) :
  fam_in F f -> fam_in (ifam_dp F) (fam_dp f).
Proof.
  intros H. induction H as [| I e F f [Ek HR] _ IH]; [constructor |].
  cbn [ifam_dp fam_dp map]. constructor; [| exact IH]. cbn [fst snd]. split; [exact Ek |].
  clear -HR. induction HR as [| Ie re row rs [En [HC HS]] _ IHr]; [constructor |].
  cbn [map]. constructor; [| exact IHr]. cbn [fst snd]. split; [exact En |].
  rewrite En. split; [apply inR_mul; [apply inR_Z | exact HS] | apply inR_neg, inR_mul; [apply inR_Z | exact HC]].
Qed.

Lemma fam_dt_ns (f : list (Z * list (Z * (R * R)))) (ns : list Z) :
  Forall (fun kr => map fst (snd kr) = ns) f -> Forall (fun kr => map fst (snd kr) = ns) (fam_dt f).
Proof.
  intros H. induction H as [| kr f Hk _ IH]; [constructor |]. cbn [fam_dt map]. constructor; [| exact IH].
  cbn [snd]. rewrite map_map. rewrite <- Hk. apply map_ext. intros e. reflexivity.
Qed.

Lemma fam_dp_ns (f : list (Z * list (Z * (R * R)))) (ns : list Z) :
  Forall (fun kr => map fst (snd kr) = ns) f -> Forall (fun kr => map fst (snd kr) = ns) (fam_dp f).
Proof.
  intros H. induction H as [| kr f Hk _ IH]; [constructor |]. cbn [fam_dp map]. constructor; [| exact IH].
  cbn [snd]. rewrite map_map. rewrite <- Hk. apply map_ext. intros e. reflexivity.
Qed.

Lemma fam_dt_ks (f : list (Z * list (Z * (R * R)))) : map fst (fam_dt f) = map fst f.
Proof. unfold fam_dt. rewrite map_map. reflexivity. Qed.
Lemma fam_dp_ks (f : list (Z * list (Z * (R * R)))) : map fst (fam_dp f) = map fst f.
Proof. unfold fam_dp. rewrite map_map. reflexivity. Qed.

End DenseOps.
