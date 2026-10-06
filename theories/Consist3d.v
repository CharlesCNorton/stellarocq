(** Consistency of order h^2 of the collocated three-dimensional rows at the
    exact solution, and convergence.

    At the exact jet and a step h in [0, hhi], each row is the output of the
    consistency check's list: the flattened residual holds the values of
    RegResidual's bindings ([anf_sound]), the jet's inputs are real over a
    ball cell, and the check's jet layer is Jet's outer environment
    ([layer_s]). The poloidal rows are read at the outer half point t, where
    the check's layer in t agrees with the outer environment of the node
    t - h/2 off slot 0, which no binding of the residual reads ([layer_t],
    [tail_free0]). Where the check passes the radial row is real at h and -h,
    so the Jacobians at the two half points are nonzero and the row is the
    node residual, even in h by Cons3d ([even_s]); the poloidal row at t is
    even in h as well ([even_t]). An even function whose second derivative is
    within B on [-a, a] moves by at most 2 B x^2 from 0 to x ([even_c2]), so
    every row at the exact solution is within 2 C h^2 of its source
    ([colloc3d_consistent]), which is the hypothesis of
    [Stab3d.colloc3d_second_order] ([colloc3d_convergent]). *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Deriv DivDiff Cell Checker Newton TMEval Continuum RegResidual Jet LinCheck
  DerivSeq Adjoint AdjointSound QDiff CellTM Check3d Ball3d Taylor Ball3dSound Affine Row3d Mat Recur Level3d Lin3d
  Disc3d Stab3d Cons3d ConsCheck.

Import ListNotations.
Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Real functions                                                    *)

Lemma bound_by_eq : forall a b a' b' B : R, a = a' -> b = b' -> Rabs (a' - b') <= B -> Rabs (a - b) <= B.
Proof. intros a b a' b' B -> -> H. exact H. Qed.

Lemma xr_eq_of : forall (X Y : ExtendedR) (a b : R), X = Xreal a -> Y = Xreal b -> a = b -> xr X = xr Y.
Proof. intros X Y a b -> -> ->. reflexivity. Qed.

Lemma xreal_inj : forall a b : R, Xreal a = Xreal b -> a = b.
Proof. intros a b H. injection H as H. exact H. Qed.

Lemma sub_eq : forall a b c : R, a = b -> a - c = b - c.
Proof. intros a b c ->. reflexivity. Qed.

Lemma mvt_abs :
  forall (g g1 : R -> R) (a b B : R), a < b ->
  (forall x, a <= x <= b -> derivable_pt_lim g x (g1 x)) -> (forall x, a <= x <= b -> Rabs (g1 x) <= B) ->
  Rabs (g b - g a) <= B * (b - a).
Proof.
  intros g g1 a b B Hab D HB.
  destruct (MVT_cor2 g g1 a b Hab D) as [c [Hc Hcab]].
  rewrite Hc, Rabs_mult, (Rabs_right (b - a)) by lra.
  apply Rmult_le_compat_r; [lra | apply HB; lra].
Qed.

(** An even function with |f''| <= B on [-a, a] moves by at most 2 B x^2. *)
Lemma even_c2 :
  forall (f f1 f2 : R -> R) (a B : R),
  (forall x, - a <= x <= a -> derivable_pt_lim f x (f1 x)) ->
  (forall x, - a <= x <= a -> derivable_pt_lim f1 x (f2 x)) ->
  (forall x, - a <= x <= a -> Rabs (f2 x) <= B) ->
  (forall x, 0 < x <= a -> f (- x) = f x) ->
  forall x, 0 < x <= a -> Rabs (f x - f 0) <= 2 * B * (x * x).
Proof.
  intros f f1 f2 a B D1 D2 HB Hev x Hx.
  assert (HB0 : 0 <= B) by (eapply Rle_trans; [apply Rabs_pos | apply (HB x); lra]).
  destruct (MVT_cor2 f f1 (- x) x ltac:(lra) (fun c Hc => D1 c ltac:(lra))) as [xi [Hxi Hxir]].
  rewrite (Hev x Hx) in Hxi.
  assert (Hz : f1 xi = 0).
  { assert (H0 : f1 xi * (2 * x) = 0) by (replace (2 * x) with (x - - x) by ring; lra).
    destruct (Rmult_integral _ _ H0) as [H|H]; [exact H | lra]. }
  destruct (MVT_cor2 f f1 0 x ltac:(lra) (fun c Hc => D1 c ltac:(lra))) as [eta [Heta Hetar]].
  assert (Hf1 : Rabs (f1 eta) <= B * (2 * x)).
  { destruct (Rlt_le_dec xi eta) as [Hlt|Hle].
    - assert (M := mvt_abs f1 f2 xi eta B Hlt (fun c Hc => D2 c ltac:(lra)) (fun c Hc => HB c ltac:(lra))).
      rewrite Hz, Rminus_0_r in M. eapply Rle_trans; [exact M|]. apply Rmult_le_compat_l; lra.
    - destruct (Rle_lt_or_eq_dec eta xi Hle) as [Hlt|Heq].
      + assert (M := mvt_abs f1 f2 eta xi B Hlt (fun c Hc => D2 c ltac:(lra)) (fun c Hc => HB c ltac:(lra))).
        rewrite Hz, Rminus_0_l, Rabs_Ropp in M. eapply Rle_trans; [exact M|]. apply Rmult_le_compat_l; lra.
      + rewrite Heq, Hz, Rabs_R0. apply Rmult_le_pos; lra. }
  rewrite Heta, Rminus_0_r, Rabs_mult, (Rabs_right x) by lra.
  replace (2 * B * (x * x)) with (B * (2 * x) * x) by ring.
  apply Rmult_le_compat_r; lra.
Qed.

(* ---------------------------------------------------------------- *)
(* The cells of the radius                                           *)

Lemma clo_ge : forall c, / 4 <= dyadR (clo c).
Proof.
  intros c. unfold dyadR, clo. cbn [fst snd]. rewrite <- INR_IZR_INZ, plus_INR, pRZm8.
  assert (H := pos_INR c). replace (INR 64) with 64 by (cbn; ring). lra.
Qed.

Lemma cell_any : forall t, / 4 <= t <= 1 -> exists c, (c < 192)%nat /\ dyadR (clo c) <= t <= dyadR (chi c).
Proof.
  intros t Ht.
  remember ((t - / 4) * 256) as x eqn:Ex.
  assert (Hx1 : x <= 192) by lra.
  destruct (base_Int_part x) as [H1 H2].
  assert (Hz : (0 <= Int_part x)%Z).
  { apply le_IZR. destruct (Z_lt_le_dec (Int_part x) 0) as [Hn|Hn]; [|apply IZR_le; exact Hn].
    exfalso. apply Z.lt_le_pred in Hn. apply IZR_le in Hn. rewrite <- Z.sub_1_r, minus_IZR in Hn. cbn in Hn. lra. }
  destruct (Nat.lt_ge_cases (Z.to_nat (Int_part x)) 192) as [Hlt|Hge].
  - exists (Z.to_nat (Int_part x)). split; [exact Hlt|].
    unfold dyadR, clo, chi. cbn [fst snd]. rewrite <- !INR_IZR_INZ, !plus_INR, pRZm8.
    rewrite (INR_IZR_INZ (Z.to_nat (Int_part x))), Z2Nat.id by exact Hz.
    replace (INR 64) with 64 by (cbn; ring). replace (INR 65) with 65 by (cbn; ring).
    split; lra.
  - exists 191%nat. split; [lia|].
    assert (H192 : (192 <= Int_part x)%Z) by (rewrite <- (Z2Nat.id (Int_part x)) by exact Hz; lia).
    apply IZR_le in H192.
    assert (Et : t = 1) by lra. subst t.
    unfold dyadR, clo, chi. cbn [fst snd]. rewrite pRZm8.
    replace (IZR (Z.of_nat (64 + 191))) with 255 by reflexivity.
    replace (IZR (Z.of_nat (65 + 191))) with 256 by reflexivity.
    lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Facts of the nine points, computed                                 *)

Lemma pt_const :
  forall (r : bool) kp, (kp < (if r then 5 else 4))%nat ->
  exists a b, forall E, xeval E (fst (pt r kp)) = Xreal a /\ xeval E (snd (pt r kp)) = Xreal b.
Proof.
  intros [|] kp Hkp; cbn in Hkp;
    (do 5 (destruct kp as [|kp]; [eexists; eexists; intros E; split; reflexivity|])); lia.
Qed.

Lemma jet_vars :
  forall (r : bool) kp, (kp < (if r then 5 else 4))%nat ->
  forallb (fun k => vars_below 2 (jet_e (fst (pt r kp)) (snd (pt r kp)) (EfromZ 0) (EfromZ 0) k)) (seq 0 87) = true.
Proof.
  intros [|] kp Hkp; cbn in Hkp; (do 5 (destruct kp as [|kp]; [vm_compute; reflexivity|])); lia.
Qed.

Lemma jet_layer_wf :
  forall (r : bool) kp, (kp < (if r then 5 else 4))%nat ->
  well_formed 3 (jet_layer (fst (pt r kp)) (snd (pt r kp)) 0) = true.
Proof.
  intros [|] kp Hkp; cbn in Hkp; (do 5 (destruct kp as [|kp]; [vm_compute; reflexivity|])); lia.
Qed.

Lemma jet_layer_t_wf :
  forall kp, (kp < 4)%nat -> well_formed 3 (jet_layer_t (fst (pt false kp)) (snd (pt false kp))) = true.
Proof.
  intros kp Hkp. assert (H := clist_wf false kp Hkp). rewrite clist_split, DivDiff.well_formed_app in H.
  apply andb_prop in H. exact (proj1 H).
Qed.

(** No binding of the residual reads or writes slot 0. *)
Lemma tail_free0 : forall r, forallb (fun b => var_free 0 (snd b) && negb (Nat.eqb (fst b) 0)) (tail r) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma rtop3_nz : rtop3 <> 0%nat.
Proof. rewrite rtop3_len0. lia. Qed.

Lemma tail_len : forall r, (rtop3 < 87 + length (tail r))%nat.
Proof. intros r. unfold tail, rtop3. rewrite length_app, ntop_val. cbn [length]. lia. Qed.

(* ---------------------------------------------------------------- *)
(* The check's layers are the outer environment                      *)

Lemma xeval_eq_env : forall E1 E2 e, (forall k, eget k E1 Xnan = eget k E2 Xnan) -> xeval E1 e = xeval E2 e.
Proof.
  intros E1 E2 e H. induction e; cbn [xeval]; try rewrite IHe; try rewrite IHe1, IHe2; try reflexivity. apply H.
Qed.

(** Bindings that neither read nor write slot 0 keep two environments that
    agree off slot 0 in agreement there. *)
Lemma xextend_agree0 :
  forall L E1 E2, forallb (fun b => var_free 0 (snd b) && negb (Nat.eqb (fst b) 0)) L = true ->
  (forall k, k <> 0%nat -> eget k E1 Xnan = eget k E2 Xnan) ->
  forall k, k <> 0%nat -> eget k (xextend E1 L) Xnan = eget k (xextend E2 L) Xnan.
Proof.
  induction L as [|[n e] L IH]; intros E1 E2 HL H k Hk; [exact (H k Hk)|].
  cbn [forallb fst snd] in HL. apply andb_prop in HL. destruct HL as [Hb HL].
  apply andb_prop in Hb. destruct Hb as [Hf Hn].
  change (xextend E1 ((n, e) :: L)) with (xextend (eset n E1 (xeval E1 e)) L).
  change (xextend E2 ((n, e) :: L)) with (xextend (eset n E2 (xeval E2 e)) L).
  apply IH; [exact HL | | exact Hk].
  intros k' Hk'. destruct (Nat.eq_dec k' n) as [->|Hne].
  - rewrite !eget_eset_eq.
    rewrite <- (xeval_eset_free 0 e E1 (eget 0 E2 Xnan) Hf). apply xeval_eq_env.
    intros i. destruct (Nat.eq_dec i 0) as [->|Hi].
    + rewrite eget_eset_eq. reflexivity.
    + rewrite eget_eset_neq by exact Hi. apply H. exact Hi.
  - rewrite !eget_eset_neq by exact Hne. apply H. exact Hk'.
Qed.

Lemma pin_get0 : forall s h t, eget 0 (pin s h t) Xnan = Xreal s.
Proof. intros. reflexivity. Qed.

Lemma pin_base : forall s h t j, (j < 2)%nat -> eget j (pin s h t) Xnan = eget j (base s h) Xnan.
Proof. intros s h t j Hj. destruct j as [|[|j]]; [reflexivity | reflexivity | lia]. Qed.

Lemma outer_high :
  forall u v s h k, (87 <= k)%nat -> eget k (outer u v (EfromZ 0) (EfromZ 0) s h) Xnan = Xnan.
Proof.
  intros u v s h k Hk. unfold outer. rewrite eget_of_list. apply nth_overflow.
  rewrite length_map, length_seq, ntop_val. exact Hk.
Qed.

(** The jet layer in s is the outer environment at (s, h). *)
Lemma layer_s :
  forall u v s h,
  forallb (fun k => vars_below 2 (jet_e u v (EfromZ 0) (EfromZ 0) k)) (seq 0 87) = true ->
  well_formed 3 (jet_layer u v 0) = true ->
  forall k, eget k (xextend (pin s h 0) (jet_layer u v 0)) Xnan = eget k (outer u v (EfromZ 0) (EfromZ 0) s h) Xnan.
Proof.
  intros u v s h Hv Hw k. rewrite forallb_forall in Hv.
  assert (Hj : forall E, (forall j, (j < 2)%nat -> eget j E Xnan = eget j (base s h) Xnan) ->
               forall k, (k < 87)%nat ->
               xeval E (jet_e u v (EfromZ 0) (EfromZ 0) k) = eget k (outer u v (EfromZ 0) (EfromZ 0) s h) Xnan).
  { intros E HE k' Hk'. rewrite outer_get by (rewrite ntop_val; exact Hk').
    apply (xeval_agree 2); [apply Hv; apply in_seq; lia | exact HE]. }
  destruct (Nat.lt_ge_cases k 87) as [Hk|Hk].
  - destruct (Nat.lt_ge_cases k 3) as [Hk3|Hk3].
    + transitivity (eget k (pin s h 0) Xnan); [exact (eget_above _ _ 3 k Hw Hk3)|].
      transitivity (xeval (pin s h 0) (jet_e u v (EfromZ 0) (EfromZ 0) k));
        [| exact (Hj (pin s h 0) (pin_base s h 0) k Hk)].
      destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | lia].
    + assert (Hin : In (k, jet_e u v (EfromZ 0) (EfromZ 0) k) (jet_layer u v 0)).
      { unfold jet_layer. apply in_map_iff. exists (k - 3)%nat. split.
        - cbv beta zeta. replace (3 + (k - 3))%nat with k by lia.
          rewrite (proj2 (Nat.eqb_neq k 0)) by lia. reflexivity.
        - apply in_seq. rewrite ntop_val. lia. }
      transitivity (xeval (xextend (pin s h 0) (jet_layer u v 0)) (jet_e u v (EfromZ 0) (EfromZ 0) k));
        [exact (wf_holds _ (pin s h 0) 3 _ _ Hw Hin)|].
      apply Hj; [| exact Hk].
      intros j Hj2. transitivity (eget j (pin s h 0) Xnan); [exact (eget_above _ _ 3 j Hw ltac:(lia)) | exact (pin_base s h 0 j Hj2)].
  - transitivity (eget k (pin s h 0) Xnan).
    { apply eget_xextend_notin. intros Hin. apply jet_layer_slots in Hin. lia. }
    transitivity Xnan; [exact (pin_high s h 0 k ltac:(lia)) | symmetry; exact (outer_high u v s h k Hk)].
Qed.

(** The jet layer in t is, off slot 0, the outer environment at (t - h/2, h). *)
Lemma layer_t :
  forall u v t h,
  forallb (fun k => vars_below 2 (jet_e u v (EfromZ 0) (EfromZ 0) k)) (seq 0 87) = true ->
  well_formed 3 (jet_layer_t u v) = true ->
  forall k, k <> 0%nat ->
  eget k (xextend (pin t h 0) (jet_layer_t u v)) Xnan = eget k (outer u v (EfromZ 0) (EfromZ 0) (t - h / 2) h) Xnan.
Proof.
  intros u v t h Hv Hw k Hk0. rewrite forallb_forall in Hv.
  assert (Hj : forall E, (forall j, (j < 2)%nat -> eget j E Xnan = eget j (base (t - h / 2) h) Xnan) ->
               forall k, (k < 87)%nat ->
               xeval E (jet_e u v (EfromZ 0) (EfromZ 0) k) =
               eget k (outer u v (EfromZ 0) (EfromZ 0) (t - h / 2) h) Xnan).
  { intros E HE k' Hk'. rewrite outer_get by (rewrite ntop_val; exact Hk').
    apply (xeval_agree 2); [apply Hv; apply in_seq; lia | exact HE]. }
  assert (Het : xeval (pin t h 0) et = Xreal (t - h / 2)).
  { unfold et. cbn [xeval]. rewrite xeval_half2, pin_get0, pin_get1.
    repeat (first [rewrite Xsub_rr | rewrite Xmul_rr]). f_equal. field. }
  destruct (Nat.lt_ge_cases k 87) as [Hk|Hk].
  - destruct (Nat.lt_ge_cases k 3) as [Hk3|Hk3].
    + transitivity (eget k (pin t h 0) Xnan); [exact (eget_above _ _ 3 k Hw Hk3)|].
      transitivity (xeval (base (t - h / 2) h) (jet_e u v (EfromZ 0) (EfromZ 0) k));
        [| exact (Hj (base (t - h / 2) h) (fun j _ => eq_refl) k Hk)].
      destruct k as [|[|[|k]]]; [lia | reflexivity | reflexivity | lia].
    + assert (Hin : In (k, subs0 et (jet_e u v (EfromZ 0) (EfromZ 0) k)) (jet_layer_t u v)).
      { unfold jet_layer_t. apply in_map_iff. exists (k - 3)%nat. split.
        - cbv beta. replace (3 + (k - 3))%nat with k by lia. reflexivity.
        - apply in_seq. rewrite ntop_val. lia. }
      transitivity (xeval (xextend (pin t h 0) (jet_layer_t u v)) (subs0 et (jet_e u v (EfromZ 0) (EfromZ 0) k)));
        [exact (wf_holds _ (pin t h 0) 3 _ _ Hw Hin)|].
      assert (Hvs : vars_below 2 (subs0 et (jet_e u v (EfromZ 0) (EfromZ 0) k)) = true)
        by (apply vars_below_subs0; [reflexivity | apply Hv; apply in_seq; lia]).
      transitivity (xeval (pin t h 0) (subs0 et (jet_e u v (EfromZ 0) (EfromZ 0) k))).
      { apply (xeval_agree 2 _ _ _ Hvs). intros j Hj2. exact (eget_above _ _ 3 j Hw ltac:(lia)). }
      rewrite xeval_subs0, Het.
      apply Hj; [| exact Hk].
      intros j Hj2. destruct j as [|[|j]]; [| | lia].
      * rewrite eget_eset_eq. reflexivity.
      * rewrite eget_eset_neq by lia. reflexivity.
  - transitivity (eget k (pin t h 0) Xnan).
    { apply eget_xextend_notin. intros Hin. unfold jet_layer_t in Hin. rewrite map_map in Hin.
      apply in_map_iff in Hin. destruct Hin as [i [Ei Hi]]. apply in_seq in Hi. cbn [fst] in Ei.
      rewrite ntop_val in Hi. lia. }
    transitivity Xnan; [exact (pin_high t h 0 k ltac:(lia)) | symmetry; exact (outer_high u v _ h k Hk)].
Qed.

(** Stated for any slot, so that no conversion or unification reads the
    concrete one. *)
Lemma xextend_single : forall E n q, eget n (xextend E [(n, q)]) Xnan = xeval E q.
Proof. intros E n q. change (xextend E [(n, q)]) with (eset n E (xeval E q)). apply eget_eset_eq. Qed.

Lemma eget_xextend_app :
  forall k E l1 l2, eget k (xextend E (l1 ++ l2)) Xnan = eget k (xextend (xextend E l1) l2) Xnan.
Proof. intros k E l1 l2. rewrite xextend_app. reflexivity. Qed.

Lemma tail_out :
  forall E (r : bool),
  eget rtop3 (xextend E (tail r)) Xnan =
  xeval (xextend E (reg_binds modes3d)) (if r then reg_fs modes3d else reg_fu modes3d).
Proof.
  intros E r. unfold tail.
  transitivity (eget rtop3 (xextend (xextend E (reg_binds modes3d))
                                    [(rtop3, if r then reg_fs modes3d else reg_fu modes3d)]) Xnan);
    [exact (eget_xextend_app rtop3 E (reg_binds modes3d) [(rtop3, if r then reg_fs modes3d else reg_fu modes3d)])|].
  exact (xextend_single (xextend E (reg_binds modes3d)) rtop3 (if r then reg_fs modes3d else reg_fu modes3d)).
Qed.

(** The radial row of the check is RegResidual's at (s, h). *)
Lemma cv0_s :
  forall u v s h,
  forallb (fun k => vars_below 2 (jet_e u v (EfromZ 0) (EfromZ 0) k)) (seq 0 87) = true ->
  well_formed 3 (jet_layer u v 0) = true ->
  cv0 (clist u v true) s h = xeval (xextend (outer u v (EfromZ 0) (EfromZ 0) s h) (reg_binds modes3d)) (reg_fs modes3d).
Proof.
  intros u v s h Hv Hw. unfold cv0.
  transitivity (eget rtop3 (xextend (xextend (pin s h 0) (jet_layer u v 0)) (tail true)) Xnan).
  { rewrite clist_split. exact (eget_xextend_app rtop3 (pin s h 0) (jet_layer u v 0) (tail true)). }
  transitivity (eget rtop3 (xextend (outer u v (EfromZ 0) (EfromZ 0) s h) (tail true)) Xnan);
    [exact (env_agree (tail true) _ _ (layer_s u v s h Hv Hw) rtop3)|].
  exact (tail_out _ true).
Qed.

(** The poloidal row of the check at (t, h) is RegResidual's at (t - h/2, h). *)
Lemma cv0_t :
  forall u v t h,
  forallb (fun k => vars_below 2 (jet_e u v (EfromZ 0) (EfromZ 0) k)) (seq 0 87) = true ->
  well_formed 3 (jet_layer_t u v) = true ->
  cv0 (clist u v false) t h =
  xeval (xextend (outer u v (EfromZ 0) (EfromZ 0) (t - h / 2) h) (reg_binds modes3d)) (reg_fu modes3d).
Proof.
  intros u v t h Hv Hw. unfold cv0.
  transitivity (eget rtop3 (xextend (xextend (pin t h 0) (jet_layer_t u v)) (tail false)) Xnan).
  { rewrite clist_split. exact (eget_xextend_app rtop3 (pin t h 0) (jet_layer_t u v) (tail false)). }
  transitivity (eget rtop3 (xextend (outer u v (EfromZ 0) (EfromZ 0) (t - h / 2) h) (tail false)) Xnan);
    [exact (xextend_agree0 (tail false) _ _ (tail_free0 false) (layer_t u v t h Hv Hw) rtop3 rtop3_nz)|].
  exact (tail_out _ false).
Qed.

(* ---------------------------------------------------------------- *)
(* Evenness in h                                                     *)

Lemma even_s :
  forall kp, (kp < 5)%nat -> forall s x, 0 < x < s ->
  (exists y, cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s x = Xreal y) ->
  (exists y, cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s (- x) = Xreal y) ->
  xr (cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s (- x)) =
  xr (cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s x).
Proof.
  intros kp Hkp s x Hx [y Hy] [y' Hy'].
  apply (xr_eq_of _ _ y' y Hy' Hy).
  assert (Hv := jet_vars true kp Hkp). assert (Hw := jet_layer_wf true kp Hkp).
  destruct (pt_const true kp Hkp) as [a [b Hab]].
  rewrite (cv0_s _ _ s x Hv Hw) in Hy. rewrite (cv0_s _ _ s (- x) Hv Hw) in Hy'.
  assert (Hxn : x <> 0) by lra. assert (Hxn' : - x <> 0) by lra.
  assert (Hf0 : forall s h, xeval (base s h) (EfromZ 0) = Xreal (IZR 0)) by (intros; reflexivity).
  destruct (exact_fs_nz _ _ _ _ a b (IZR 0) (IZR 0) s x Hxn ltac:(lra) (proj1 (Hab _)) (proj2 (Hab _))
              (Hf0 s x) (Hf0 s x) y Hy) as [Hm Hp].
  assert (Ey := exact_fs _ _ _ _ a b (IZR 0) (IZR 0) s x Hxn ltac:(lra) (proj1 (Hab _)) (proj2 (Hab _))
                  (Hf0 s x) (Hf0 s x) Hm Hp y Hy).
  destruct (exact_fs_nz _ _ _ _ a b (IZR 0) (IZR 0) s (- x) Hxn' ltac:(lra) (proj1 (Hab _)) (proj2 (Hab _))
              (Hf0 s (- x)) (Hf0 s (- x)) y' Hy') as [Hm' Hp'].
  assert (Ey' := exact_fs _ _ _ _ a b (IZR 0) (IZR 0) s (- x) Hxn' ltac:(lra) (proj1 (Hab _)) (proj2 (Hab _))
                   (Hf0 s (- x)) (Hf0 s (- x)) Hm' Hp' y' Hy').
  rewrite Ey', Ey. apply sub_eq. exact (node_rs_neg a b s x mpp3 Hxn).
Qed.

Lemma even_t :
  forall kp, (kp < 4)%nat -> forall t x, 0 < x -> 3 * x < 2 * t ->
  (exists y, cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t x = Xreal y) ->
  (exists y, cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t (- x) = Xreal y) ->
  xr (cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t (- x)) =
  xr (cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t x).
Proof.
  intros kp Hkp t x Hx Htx [y Hy] [y' Hy'].
  apply (xr_eq_of _ _ y' y Hy' Hy).
  assert (Hv := jet_vars false kp Hkp). assert (Hw := jet_layer_t_wf kp Hkp).
  destruct (pt_const false kp Hkp) as [a [b Hab]].
  rewrite (cv0_t _ _ t x Hv Hw) in Hy. rewrite (cv0_t _ _ t (- x) Hv Hw) in Hy'.
  assert (Hxn : x <> 0) by lra. assert (Hxn' : - x <> 0) by lra.
  assert (Hf0 : forall s h, xeval (base s h) (EfromZ 0) = Xreal (IZR 0)) by (intros; reflexivity).
  assert (Hp := exact_fu_nz _ _ _ _ a b (IZR 0) (IZR 0) (t - x / 2) x Hxn ltac:(lra) (proj1 (Hab _)) (proj2 (Hab _))
                  (Hf0 _ _) (Hf0 _ _) y Hy).
  assert (Ey := exact_fu_p _ _ _ _ a b (IZR 0) (IZR 0) (t - x / 2) x Hxn ltac:(lra) (proj1 (Hab _)) (proj2 (Hab _))
                  (Hf0 _ _) (Hf0 _ _) Hp).
  rewrite Hy in Ey. apply xreal_inj in Ey.
  assert (Hp' := exact_fu_nz _ _ _ _ a b (IZR 0) (IZR 0) (t - - x / 2) (- x) Hxn' ltac:(lra) (proj1 (Hab _))
                   (proj2 (Hab _)) (Hf0 _ _) (Hf0 _ _) y' Hy').
  assert (Ey' := exact_fu_p _ _ _ _ a b (IZR 0) (IZR 0) (t - - x / 2) (- x) Hxn' ltac:(lra) (proj1 (Hab _))
                   (proj2 (Hab _)) (Hf0 _ _) (Hf0 _ _) Hp').
  rewrite Hy' in Ey'. apply xreal_inj in Ey'.
  rewrite Ey, Ey'. apply sub_eq.
  replace (t - - x / 2) with (t + x / 2) by field.
  apply (f_equal Force.cres_u). exact (jp3_shift a b t x Hxn).
Qed.

(* ---------------------------------------------------------------- *)
(* The rows of a passing check                                       *)

Lemma cons_s :
  forall prec C hhi kp c, (kp < 5)%nat -> cons2_cell_ok prec C hhi true kp c = true -> dyadR hhi < / 8 ->
  forall s, dyadR (clo c) <= s <= dyadR (chi c) -> forall x, 0 < x <= dyadR hhi ->
  Rabs (xr (cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s x)
        - xr (cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s 0)) <= 2 * dyadR C * (x * x).
Proof.
  intros prec C hhi kp c Hkp Hok Hh8 s Hs x Hx.
  assert (Hs4 := clo_ge c).
  assert (Hc2 := fun y Hy => cons2_sound prec C hhi true kp c Hkp Hok s y Hs Hy).
  apply (even_c2 (fun y => xr (cv0 (clist (fst (pt true kp)) (snd (pt true kp)) true) s y))
                 (fun y => xr (cv1 (clist (fst (pt true kp)) (snd (pt true kp)) true) s y))
                 (fun y => xr (cv2 (clist (fst (pt true kp)) (snd (pt true kp)) true) s y)) (dyadR hhi) (dyadR C)).
  - intros y Hy. exact (proj1 (proj2 (Hc2 y Hy))).
  - intros y Hy. exact (proj1 (proj2 (proj2 (Hc2 y Hy)))).
  - intros y Hy. exact (proj2 (proj2 (proj2 (Hc2 y Hy)))).
  - intros y Hy. cbv beta.
    apply even_s; [exact Hkp | lra | exact (proj1 (Hc2 y ltac:(lra))) | exact (proj1 (Hc2 (- y) ltac:(lra)))].
  - exact Hx.
Qed.

Lemma cons_t :
  forall prec C hhi kp c, (kp < 4)%nat -> cons2_cell_ok prec C hhi false kp c = true -> dyadR hhi < / 8 ->
  forall t, dyadR (clo c) <= t <= dyadR (chi c) -> forall x, 0 < x <= dyadR hhi ->
  Rabs (xr (cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t x)
        - xr (cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t 0)) <= 2 * dyadR C * (x * x).
Proof.
  intros prec C hhi kp c Hkp Hok Hh8 t Ht x Hx.
  assert (Ht4 := clo_ge c).
  assert (Hc2 := fun y Hy => cons2_sound prec C hhi false kp c Hkp Hok t y Ht Hy).
  apply (even_c2 (fun y => xr (cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t y))
                 (fun y => xr (cv1 (clist (fst (pt false kp)) (snd (pt false kp)) false) t y))
                 (fun y => xr (cv2 (clist (fst (pt false kp)) (snd (pt false kp)) false) t y)) (dyadR hhi) (dyadR C)).
  - intros y Hy. exact (proj1 (proj2 (Hc2 y Hy))).
  - intros y Hy. exact (proj1 (proj2 (proj2 (Hc2 y Hy)))).
  - intros y Hy. exact (proj2 (proj2 (proj2 (Hc2 y Hy)))).
  - intros y Hy. cbv beta.
    apply even_t; [exact Hkp | lra | lra | exact (proj1 (Hc2 y ltac:(lra))) | exact (proj1 (Hc2 (- y) ltac:(lra)))].
  - exact Hx.
Qed.

(* ---------------------------------------------------------------- *)
(* The collocated rows at the exact solution                         *)

Lemma anfs_split : forall r, anf 87 (tail r) = (ab r, snd (fst (anfs r)), ttop r).
Proof.
  intros r. unfold ab, ttop.
  assert (H : anf 87 (tail r) = anfs r) by (unfold anfs; destruct r; unfold anf_r, anf_p; reflexivity).
  rewrite H. destruct (anfs r) as [[a m] t]. reflexivity.
Qed.

(** At an unmoved jet, a row is the check's list's output. *)
Lemma Fz_layer :
  forall prec Kb rx rd hhi (r : bool) kp c, ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  forall z, (forall k, z k = 0) ->
  Fz r kp s h z = xr (eget rtop3 (xextend (pin s h 0) (jet_layer (fst (pt r kp)) (snd (pt r kp)) 0 ++ tail r)) Xnan).
Proof.
  intros prec Kb rx rd hhi r kp c Hok s h Hs Hh z Hz.
  assert (HR := jet_real prec r kp c rx rd hhi Kb Hok s h Hs Hh).
  assert (HE : forall k, eget k (Ez r kp s h z) Xnan = eget k (Ex r kp s h) Xnan).
  { intros k. rewrite Ez_get. destruct (inxd k) eqn:Hk; [|reflexivity].
    destruct (inxd_range k Hk) as [Hk' _]. destruct (HR k ltac:(lia)) as [x Hx].
    rewrite Hx, Hz. cbn [xr]. rewrite Rplus_0_r. reflexivity. }
  destruct (tail_facts r) as [_ [_ [Htop [Ho [Hwft _]]]]].
  destruct (anf_sound 87 (tail r) (ab r) (snd (fst (anfs r))) (ttop r) (tail_wf r) (anfs_split r))
    as [_ [_ [_ [_ HA]]]].
  unfold Fz. apply (f_equal xr).
  transitivity (eget (tout r) (xextend (Ex r kp s h) (tl r)) Xnan); [exact (env_agree (tl r) _ _ HE (tout r))|].
  transitivity (eget (tout r) (xextend (Ex r kp s h) (ab r)) Xnan);
    [exact (tail_low (ab r) (ttop r) (tout r) Hwft (Ex r kp s h) (tout r) ltac:(lia))|].
  transitivity (eget rtop3 (xextend (Ex r kp s h) (tail r)) Xnan); [exact (HA (Ex r kp s h) rtop3 (tail_len r))|].
  unfold Ex.
  exact (eq_sym (eget_xextend_app rtop3 (pin s h 0) (jet_layer (fst (pt r kp)) (snd (pt r kp)) 0) (tail r))).
Qed.

(** With the second differences unmoved as well, the row is the same. *)
Lemma Rv_Fz :
  forall prec Kb rx rd hhi (r : bool) kp c, ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true ->
  forall s h, dyadR (clo c) <= s <= dyadR (chi c) -> 0 <= h <= dyadR hhi ->
  forall z w, (forall k, z k = 0) -> (forall k, w k = 0) -> Rv r kp s h z w = Fz r kp s h z.
Proof.
  intros prec Kb rx rd hhi r kp c Hok s h Hs Hh z w Hz Hw.
  assert (HR := jet_real prec r kp c rx rd hhi Kb Hok s h Hs Hh).
  assert (HE : forall k, eget k (Ezw r kp s h z w) Xnan = eget k (Ez r kp s h z) Xnan).
  { intros k. rewrite Ezw_get. destruct (ine k) eqn:He; [|reflexivity].
    assert (Hk := ine_range k He).
    assert (Hxd : inxd k = false).
    { destruct (inxd k) eqn:Hx; [|reflexivity]. destruct (inxd_range k Hx) as [_ Hn]. rewrite He in Hn. discriminate. }
    rewrite Ez_get, Hxd. cbv iota. destruct (HR k ltac:(lia)) as [x Hx].
    rewrite Hx, Hw. cbn [xr]. rewrite Rplus_0_r. reflexivity. }
  unfold Rv, Fz. apply (f_equal xr). exact (env_agree (tl r) _ _ HE (tout r)).
Qed.

Lemma zj_zero : forall h j k, zj h (fun _ _ => 0) j k = 0.
Proof.
  intros h j k. unfold zj, slope. cbv beta. destruct (inxd k); [| reflexivity].
  destruct (Nat.eqb (upart k) 0); [reflexivity|].
  destruct (Nat.eqb (upart k) 1); unfold Rdiv; ring.
Qed.

Lemma wj_zero : forall h j k, wj h (fun _ _ => 0) j k = 0.
Proof. intros h j k. unfold wj, slope. cbv beta. destruct (ine k); [unfold Rdiv; ring | reflexivity]. Qed.

Lemma cv0_s_eq :
  forall u v s h, eget rtop3 (xextend (pin s h 0) (jet_layer u v 0 ++ tail true)) Xnan = cv0 (clist u v true) s h.
Proof. intros u v s h. unfold cv0. rewrite clist_split. reflexivity. Qed.

Lemma pol_eq :
  forall kp, (kp < 4)%nat -> forall s h t, t = s + h / 2 ->
  eget rtop3 (xextend (pin s h 0) (jet_layer (fst (pt false kp)) (snd (pt false kp)) 0 ++ tail false)) Xnan =
  cv0 (clist (fst (pt false kp)) (snd (pt false kp)) false) t h.
Proof.
  intros kp Hkp s h t Ht.
  assert (Hv := jet_vars false kp Hkp). assert (Hw := jet_layer_wf false kp Hkp).
  assert (Hwt := jet_layer_t_wf kp Hkp).
  rewrite (cv0_t (fst (pt false kp)) (snd (pt false kp)) t h Hv Hwt).
  assert (Es : t - h / 2 = s) by (rewrite Ht; field).
  rewrite Es.
  transitivity (eget rtop3 (xextend (xextend (pin s h 0) (jet_layer (fst (pt false kp)) (snd (pt false kp)) 0))
                                    (tail false)) Xnan);
    [exact (eget_xextend_app rtop3 (pin s h 0) (jet_layer (fst (pt false kp)) (snd (pt false kp)) 0) (tail false))|].
  transitivity (eget rtop3 (xextend (outer (fst (pt false kp)) (snd (pt false kp)) (EfromZ 0) (EfromZ 0) s h)
                                    (tail false)) Xnan);
    [exact (env_agree (tail false) _ _ (layer_s (fst (pt false kp)) (snd (pt false kp)) s h Hv Hw) rtop3)|].
  exact (tail_out (outer (fst (pt false kp)) (snd (pt false kp)) (EfromZ 0) (EfromZ 0) s h) false).
Qed.

Lemma GS_cons :
  forall prec Kb rx rd hhi C K j kp c,
  ball_cell_ok prec Kb rx rd hhi true (dtails true) kp c = true ->
  cons2_cell_ok prec C hhi true kp c = true -> (kp < 5)%nat ->
  / 65536 <= dyadR hhi -> dyadR hhi < / 8 -> (16 <= K)%nat ->
  dyadR (clo c) <= sK K j <= dyadR (chi c) ->
  Rabs (GS K (fun _ _ => 0) j kp) <= 2 * dyadR C * (hK K * hK K).
Proof.
  intros prec Kb rx rd hhi C K j kp c Hb Hc Hkp Hh0 Hh8 HK Hs.
  assert (Hh := hK_pos K). assert (Hhl := hK_le K HK).
  assert (H1 : 0 <= hK K <= dyadR hhi) by lra.
  assert (H0 : 0 <= 0 <= dyadR hhi) by lra.
  unfold GS.
  apply (bound_by_eq _ _ _ _ _
           (eq_trans (Rv_Fz prec Kb rx rd hhi true kp c Hb (sK K j) (hK K) Hs H1
                        (zj (hK K) (fun _ _ => 0) j) (wj (hK K) (fun _ _ => 0) j) (zj_zero (hK K) j) (wj_zero (hK K) j))
                     (Fz_layer prec Kb rx rd hhi true kp c Hb (sK K j) (hK K) Hs H1
                        (zj (hK K) (fun _ _ => 0) j) (zj_zero (hK K) j)))
           (Fz_layer prec Kb rx rd hhi true kp c Hb (sK K j) 0 Hs H0 (fun _ => 0) (fun _ => eq_refl))).
  apply (bound_by_eq _ _ _ _ _
           (f_equal xr (cv0_s_eq (fst (pt true kp)) (snd (pt true kp)) (sK K j) (hK K)))
           (f_equal xr (cv0_s_eq (fst (pt true kp)) (snd (pt true kp)) (sK K j) 0))).
  exact (cons_s prec C hhi kp c Hkp Hc Hh8 (sK K j) Hs (hK K) ltac:(lra)).
Qed.

Lemma GU_cons :
  forall prec Kb rx rd hhi C K j kp c c',
  ball_cell_ok prec Kb rx rd hhi false (dtails false) kp c = true ->
  ball_cell_ok prec Kb rx rd hhi false (dtails false) kp c' = true ->
  cons2_cell_ok prec C hhi false kp c' = true -> (kp < 4)%nat ->
  / 65536 <= dyadR hhi -> dyadR hhi < / 8 -> (16 <= K)%nat ->
  dyadR (clo c) <= sK K j <= dyadR (chi c) ->
  dyadR (clo c') <= sK K j + hK K / 2 <= dyadR (chi c') ->
  Rabs (GU K (fun _ _ => 0) j kp) <= 2 * dyadR C * (hK K * hK K).
Proof.
  intros prec Kb rx rd hhi C K j kp c c' Hb Hb' Hc Hkp Hh0 Hh8 HK Hs Ht.
  assert (Hh := hK_pos K). assert (Hhl := hK_le K HK).
  assert (H1 : 0 <= hK K <= dyadR hhi) by lra.
  assert (H0 : 0 <= 0 <= dyadR hhi) by lra.
  assert (Ht0 : sK K j + hK K / 2 = sK K j + hK K / 2 + 0 / 2) by field.
  unfold GU.
  apply (bound_by_eq _ _ _ _ _
           (eq_trans (Rv_Fz prec Kb rx rd hhi false kp c Hb (sK K j) (hK K) Hs H1
                        (zj (hK K) (fun _ _ => 0) j) (wj (hK K) (fun _ _ => 0) j) (zj_zero (hK K) j) (wj_zero (hK K) j))
                     (Fz_layer prec Kb rx rd hhi false kp c Hb (sK K j) (hK K) Hs H1
                        (zj (hK K) (fun _ _ => 0) j) (zj_zero (hK K) j)))
           (Fz_layer prec Kb rx rd hhi false kp c' Hb' (sK K j + hK K / 2) 0 Ht H0 (fun _ => 0) (fun _ => eq_refl))).
  apply (bound_by_eq _ _ _ _ _
           (f_equal xr (pol_eq kp Hkp (sK K j) (hK K) (sK K j + hK K / 2) eq_refl))
           (f_equal xr (pol_eq kp Hkp (sK K j + hK K / 2) 0 (sK K j + hK K / 2) Ht0))).
  exact (cons_t prec C hhi kp c' Hkp Hc Hh8 (sK K j + hK K / 2) Ht (hK K) ltac:(lra)).
Qed.

(** Consistency: where the ball and consistency checks pass, every row of
    the collocated equations at the exact solution is within 2 C h^2 of its
    source at every h = 2^-K, K >= 16. *)
Theorem colloc3d_consistent :
  forall prec Kb rx rd hhi C,
  (forall (r : bool) kp c, (kp < (if r then 5 else 4))%nat -> (c < 192)%nat ->
     ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true) ->
  (forall (r : bool) kp c, (kp < (if r then 5 else 4))%nat -> (c < 192)%nat ->
     cons2_cell_ok prec C hhi r kp c = true) ->
  / 65536 <= dyadR hhi -> dyadR hhi < / 8 ->
  forall K, (16 <= K)%nat -> forall j, (cutK K 0 < j < cutK K 12)%nat ->
  (forall kp, (kp < 5)%nat -> Rabs (GS K (fun _ _ => 0) j kp) <= 2 * dyadR C * (hK K * hK K)) /\
  (forall kp, (kp < 4)%nat -> Rabs (GU K (fun _ _ => 0) j kp) <= 2 * dyadR C * (hK K * hK K)).
Proof.
  intros prec Kb rx rd hhi C Hball Hcons Hh0 Hh8 K HK j Hj.
  destruct (ball_cell K j HK ltac:(lia)) as [c [Hc Hs]].
  assert (Hh := hK_pos K).
  assert (E0 := cutK_s K 0 0 0 HK). assert (E12 := cutK_s K 12 0 0 HK).
  rewrite Nat.mul_0_l, !Nat.add_0_r in E0, E12.
  change (INR 0) with 0 in E0, E12.
  replace (INR 12) with 12 in E12 by (cbn; ring).
  assert (Hj0 : INR (cutK K 0) + 1 <= INR j) by (rewrite <- S_INR; apply le_INR; lia).
  assert (Hj1 : INR j + 1 <= INR (cutK K 12)) by (rewrite <- S_INR; apply le_INR; lia).
  assert (A0 := Rmult_le_compat_r (hK K) _ _ (Rlt_le _ _ Hh) Hj0).
  assert (A1 := Rmult_le_compat_r (hK K) _ _ (Rlt_le _ _ Hh) Hj1).
  assert (Ht : / 4 <= sK K j + hK K / 2 <= 1) by (unfold sK; split; nra).
  destruct (cell_any _ Ht) as [c' [Hc' Ht']].
  split.
  - intros kp Hkp.
    exact (GS_cons prec Kb rx rd hhi C K j kp c (Hball true kp c Hkp Hc) (Hcons true kp c Hkp Hc) Hkp Hh0 Hh8 HK Hs).
  - intros kp Hkp.
    exact (GU_cons prec Kb rx rd hhi C K j kp c c' (Hball false kp c Hkp Hc) (Hball false kp c' Hkp Hc')
             (Hcons false kp c' Hkp Hc') Hkp Hh0 Hh8 HK Hs Ht').
Qed.

(** Convergence: where the cell, start, assembly, ball and consistency checks
    pass, the collocated equations have, at every fine enough h = 2^-K, a
    solution within C h^2 of the exact solution. *)
Theorem colloc3d_convergent :
  forall prec d kn, TMEval.covered d = true -> (1 <= d)%nat ->
  forall frames es cells rs0 Rd BM BMM BQ,
  (forall k WiI, (k < 12)%nat -> Final3d.owi prec frames k = Some WiI -> forall j, (j < 256)%nat ->
     cell_ranges2 prec d (TMEval.mktab d) (csc k j) chh chalf chh kn 4 (Final3d.gW frames k) WiI BM BMM BQ =
     Some (map (fun q => Final3d.gcell cells k (16 * j + q)) (seq 0 16))) ->
  (forall WiI, Final3d.owi prec frames 0 = Some WiI ->
     start_range prec d (TMEval.mktab d) chh chh kn WiI = Some rs0) ->
  Final3d.assemble3d prec frames es cells rs0 Rd = true ->
  forall Kb rx rd hhi C,
  (forall (r : bool) kp c, (kp < (if r then 5 else 4))%nat -> (c < 192)%nat ->
     ball_cell_ok prec Kb rx rd hhi r (dtails r) kp c = true) ->
  (forall (r : bool) kp c, (kp < (if r then 5 else 4))%nat -> (c < 192)%nat ->
     cons2_cell_ok prec C hhi r kp c = true) ->
  0 <= dyadR Kb -> 0 < dyadR rx -> 0 < dyadR rd -> / 65536 <= dyadR hhi -> dyadR hhi < / 8 -> 0 <= dyadR C ->
  exists C' K0, 0 <= C' /\ forall K, (K0 <= K)%nat ->
  exists x : nat -> Mat.vec,
    (forall i, (i < 9)%nat -> x (cutK K 0) i = 0) /\ (forall i, (i < 9)%nat -> x (cutK K 12) i = 0) /\
    (forall j, (cutK K 0 < j < cutK K 12)%nat ->
       (forall kp, (kp < 5)%nat -> GS K x j kp = 0) /\ (forall kp, (kp < 4)%nat -> GU K x j kp = 0)) /\
    (forall j, (cutK K 0 <= j <= cutK K 12)%nat -> Mat.vnorm 9 (x j) <= C' * (hK K * hK K)).
Proof.
  intros prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok Kb rx rd hhi C Hball Hcons
         HKb Hrx Hrd Hh0 Hh8 HC.
  apply (colloc3d_second_order prec d kn Hcov Hd frames es cells rs0 Rd BM BMM BQ Hcells2 Hstart Hok
           Kb rx rd hhi Hball HKb Hrx Hrd ltac:(lra) (2 * dyadR C) 16 ltac:(lra)).
  intros K HK j Hj. exact (colloc3d_consistent prec Kb rx rd hhi C Hball Hcons Hh0 Hh8 K HK j Hj).
Qed.
