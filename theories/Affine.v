(** Affineness of a flattened binding list in marked inputs.

    [edeg] is the degree of an expression in the marked inputs of a list,
    0, 1, or 2 for anything higher or not polynomial, and [aff_ok] decides
    that every slot of the list has degree at most one. Then on each fibre of
    the unmarked inputs every slot is affine in the marked ones ([aff_sound]):
    for environments E and E' that agree on the unmarked inputs and are real
    on the marked ones, the value of a slot at E' is its value at E plus a
    fixed linear combination of the marked inputs' changes, with no
    combination at all for a slot of degree zero. The list is one of single
    operations on atoms, as AdjointSound's flattening produces. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Deriv DivDiff Mat AdjointSound.

Import ListNotations.
Local Open Scope R_scope.

Fixpoint edeg (dg : env nat) (e : expr) : nat :=
  match e with
  | Evar k => eget k dg 0%nat
  | EfromZ _ | Epi | Epow2 _ => 0%nat
  | Eneg a => edeg dg a
  | Eadd a b | Esub a b => Nat.max (edeg dg a) (edeg dg b)
  | Emul a b => Nat.min 2 (edeg dg a + edeg dg b)
  | Ediv a b => if Nat.eqb (edeg dg b) 0 then edeg dg a else 2%nat
  | Esqrt a | Esin a | Ecos a | Eexp a | Eatan a => if Nat.eqb (edeg dg a) 0 then 0%nat else 2%nat
  end.

Section Aff.

Variable base : nat.
Variable mark : nat -> bool.

Definition dg0 : env nat := fold_left (fun D k => eset k D (if mark k then 1%nat else 0%nat)) (seq 0 base) eempty.

Definition degs (p : list binding) : env nat := fold_left (fun D b => eset (fst b) D (edeg D (snd b))) p dg0.


Definition aff_step (st : bool * env nat) (b : binding) : bool * env nat :=
  (fst st && Nat.leb (edeg (snd st) (snd b)) 1, eset (fst b) (snd st) (edeg (snd st) (snd b))).

Definition aff_ok (p : list binding) : bool := fst (fold_left aff_step p (true, dg0)).

Lemma aff_fold :
  forall p ok D, fold_left aff_step p (ok, D)
               = (ok && fst (fold_left aff_step p (true, D)), fold_left (fun D b => eset (fst b) D (edeg D (snd b))) p D).
Proof.
  induction p as [|b p IH]; intros ok D.
  - cbn [fold_left fst]. rewrite andb_true_r. reflexivity.
  - cbn [fold_left].
    replace (aff_step (ok, D) b) with (ok && Nat.leb (edeg D (snd b)) 1, eset (fst b) D (edeg D (snd b)))
      by reflexivity.
    replace (aff_step (true, D) b) with (true && Nat.leb (edeg D (snd b)) 1, eset (fst b) D (edeg D (snd b)))
      by reflexivity.
    rewrite (IH (ok && _) _), (IH (true && _) _). cbn [fst andb]. rewrite andb_assoc. reflexivity.
Qed.

Lemma aff_ok_eq : forall p, aff_ok p = fst (fold_left aff_step p (true, dg0)).
Proof. reflexivity. Qed.

Lemma aff_ok_snoc :
  forall p b, aff_ok (p ++ [b]) = aff_ok p && Nat.leb (edeg (degs p) (snd b)) 1.
Proof.
  intros p b. rewrite !aff_ok_eq. unfold degs. rewrite fold_left_app.
  destruct (fold_left aff_step p (true, dg0)) as [ok D] eqn:Ef.
  assert (HD : D = fold_left (fun D b => eset (fst b) D (edeg D (snd b))) p dg0).
  { assert (H := aff_fold p true dg0). rewrite Ef in H. apply (f_equal snd) in H. cbn [snd] in H. exact H. }
  cbn [fold_left]. unfold aff_step at 1. cbn [fst snd]. rewrite <- HD. reflexivity.
Qed.

Lemma degs_snoc : forall p b, degs (p ++ [b]) = eset (fst b) (degs p) (edeg (degs p) (snd b)).
Proof. intros p b. unfold degs. rewrite fold_left_app. reflexivity. Qed.

Lemma dg0_get : forall k, (k < base)%nat -> eget k dg0 0%nat = if mark k then 1%nat else 0%nat.
Proof.
  intros k Hk. unfold dg0.
  assert (Gen : forall l D, NoDup l -> In k l ->
            eget k (fold_left (fun D k => eset k D (if mark k then 1%nat else 0%nat)) l D) 0%nat = if mark k then 1%nat else 0%nat).
  { induction l as [|a l IH]; intros D Hnd Hin; [destruct Hin|].
    cbn [fold_left]. inversion Hnd as [|? ? Hna Hnd']; subst.
    destruct Hin as [->|Hin].
    - assert (Hkeep : forall l' D', ~ In k l' ->
                eget k (fold_left (fun D k0 => eset k0 D (if mark k0 then 1%nat else 0%nat)) l' D') 0%nat = eget k D' 0%nat).
      { induction l' as [|a' l' IH']; intros D' Hn; [reflexivity|]. cbn [fold_left].
        rewrite IH' by (intros H; apply Hn; right; exact H). apply eget_eset_neq. intros E. apply Hn. left. symmetry. exact E. }
      rewrite Hkeep by exact Hna. apply eget_eset_eq.
    - apply IH; assumption. }
  apply Gen; [apply seq_NoDup | apply in_seq; lia].
Qed.

(** The change of the marked inputs. *)
Definition dshift (E E' : env ExtendedR) (j : nat) : R :=
  if mark j then xr (eget j E' Xnan) - xr (eget j E Xnan) else 0.

(** E' is on the fibre of E: the same unmarked inputs, real marked ones. *)
Definition fib (E E' : env ExtendedR) : Prop :=
  (forall j, (j < base)%nat -> mark j = false -> eget j E' Xnan = eget j E Xnan) /\
  (forall j, (j < base)%nat -> mark j = true -> exists x, eget j E' Xnan = Xreal x).

Variable E : env ExtendedR.

(** Slot k of the list p is affine on the fibre of E. *)
Definition aff_slot (p : list binding) (k : nat) : Prop :=
  exists L : nat -> R, (eget k (degs p) 0%nat = 0%nat -> forall j, L j = 0) /\
  forall E', fib E E' ->
  eget k (xextend E' p) Xnan = Xreal (xr (eget k (xextend E p) Xnan) + msum (fun j => L j * dshift E E' j) base).

Definition aff_expr (p : list binding) (a : expr) : Prop :=
  exists L : nat -> R, (edeg (degs p) a = 0%nat -> forall j, L j = 0) /\
  forall E', fib E E' ->
  xeval (xextend E' p) a = Xreal (xr (xeval (xextend E p) a) + msum (fun j => L j * dshift E E' j) base).

Lemma msum_zero_L : forall (L : nat -> R) f, (forall j, L j = 0) -> msum (fun j => L j * f j) base = 0.
Proof. intros L f H. rewrite (msum_ext _ (fun _ => 0)) by (intros; rewrite H; ring). apply msum_zero. Qed.

Lemma aff_const : forall p a, xeval (xextend E p) a = xeval eempty a -> (forall E', xeval (xextend E' p) a = xeval eempty a) ->
  (exists y, xeval eempty a = Xreal y) -> aff_expr p a.
Proof.
  intros p a HE HE' [y Hy]. exists (fun _ => 0). split; [intros; reflexivity|].
  intros E' _. rewrite HE', HE, Hy. cbn [xr]. rewrite msum_zero_L by (intros; reflexivity). f_equal. ring.
Qed.

(** The inputs are affine. *)
Lemma aff_input :
  forall k, (k < base)%nat -> (exists x, eget k E Xnan = Xreal x) -> aff_slot [] k.
Proof.
  intros k Hk [x Hx]. unfold aff_slot, degs. cbn [fold_left xextend].
  exists (fun j => if Nat.eqb j k then (if mark k then 1 else 0) else 0). split.
  - intros H0 j. rewrite (dg0_get k Hk) in H0. destruct (Nat.eqb j k); [| reflexivity].
    destruct (mark k); [discriminate | reflexivity].
  - intros E' [Hun Hm]. rewrite (msum_single _ base k Hk).
    + rewrite Nat.eqb_refl. unfold dshift. destruct (mark k) eqn:Mk.
      * destruct (Hm k Hk Mk) as [x' Hx']. rewrite Hx', Hx. cbn [xr]. f_equal. ring.
      * rewrite (Hun k Hk Mk), Hx. cbn [xr]. f_equal. ring.
    + intros j Hj Hne. rewrite (proj2 (Nat.eqb_neq j k) Hne). ring.
Qed.

Hypothesis HE0 : forall j, (j < base)%nat -> exists x, eget j E Xnan = Xreal x.

Lemma fib_refl : fib E E.
Proof. split; [intros; reflexivity | intros j Hj _; exact (HE0 j Hj)]. Qed.

Lemma dshift_refl : forall j, dshift E E j = 0.
Proof. intros j. unfold dshift. destruct (mark j); ring. Qed.

Lemma aff_real : forall p a, aff_expr p a -> xeval (xextend E p) a = Xreal (xr (xeval (xextend E p) a)).
Proof.
  intros p a [L [_ HL]]. rewrite (HL E fib_refl) at 1. f_equal.
  rewrite (msum_ext _ (fun _ => 0)) by (intros; rewrite dshift_refl; ring). rewrite msum_zero. ring.
Qed.

Lemma Xneg_r' : forall a, Xneg (Xreal a) = Xreal (- a).
Proof. reflexivity. Qed.

Lemma aff_add : forall p a b, aff_expr p a -> aff_expr p b -> aff_expr p (Eadd a b).
Proof.
  intros p a b Ha Hb. assert (Ra := aff_real p a Ha). assert (Rb := aff_real p b Hb).
  destruct Ha as [La [Ha0 Ha]]. destruct Hb as [Lb [Hb0 Hb]].
  exists (fun j => La j + Lb j). split.
  - intros H0 j. cbn [edeg] in H0. rewrite (Ha0 ltac:(lia)), (Hb0 ltac:(lia)). ring.
  - intros E' HE'. cbn [xeval]. rewrite (Ha E' HE'), (Hb E' HE'), Ra, Rb, !Xadd_r. cbn [xr].
    f_equal. rewrite (msum_ext (fun j => (La j + Lb j) * dshift E E' j)
      (fun j => La j * dshift E E' j + Lb j * dshift E E' j)) by (intros; ring). rewrite msum_plus. ring.
Qed.

Lemma aff_sub : forall p a b, aff_expr p a -> aff_expr p b -> aff_expr p (Esub a b).
Proof.
  intros p a b Ha Hb. assert (Ra := aff_real p a Ha). assert (Rb := aff_real p b Hb).
  destruct Ha as [La [Ha0 Ha]]. destruct Hb as [Lb [Hb0 Hb]].
  exists (fun j => La j - Lb j). split.
  - intros H0 j. cbn [edeg] in H0. rewrite (Ha0 ltac:(lia)), (Hb0 ltac:(lia)). ring.
  - intros E' HE'. cbn [xeval]. rewrite (Ha E' HE'), (Hb E' HE'), Ra, Rb, !Xsub_r. cbn [xr].
    f_equal. rewrite (msum_ext (fun j => (La j - Lb j) * dshift E E' j)
      (fun j => La j * dshift E E' j - Lb j * dshift E E' j)) by (intros; ring). rewrite msum_minus. ring.
Qed.

Lemma aff_neg : forall p a, aff_expr p a -> aff_expr p (Eneg a).
Proof.
  intros p a Ha. assert (Ra := aff_real p a Ha). destruct Ha as [La [Ha0 Ha]].
  exists (fun j => - La j). split.
  - intros H0 j. cbn [edeg] in H0. rewrite (Ha0 H0). ring.
  - intros E' HE'. cbn [xeval]. rewrite (Ha E' HE'), Ra, !Xneg_r'. cbn [xr].
    f_equal. rewrite (msum_ext (fun j => - La j * dshift E E' j) (fun j => -1 * (La j * dshift E E' j))) by (intros; ring).
    rewrite msum_scal. ring.
Qed.

Lemma aff_flat : forall p a, aff_expr p a -> edeg (degs p) a = 0%nat ->
  forall E', fib E E' -> xeval (xextend E' p) a = xeval (xextend E p) a.
Proof.
  intros p a Ha H0 E' HE'. assert (Ra := aff_real p a Ha). destruct Ha as [La [Ha0 Ha]].
  rewrite (Ha E' HE'). rewrite (msum_zero_L La) by exact (Ha0 H0). rewrite Rplus_0_r. symmetry. exact Ra.
Qed.

Lemma aff_mul : forall p a b, aff_expr p a -> aff_expr p b -> (edeg (degs p) (Emul a b) <= 1)%nat -> aff_expr p (Emul a b).
Proof.
  intros p a b Ha Hb Hd. cbn [edeg] in Hd.
  assert (Ra := aff_real p a Ha). assert (Rb := aff_real p b Hb).
  destruct (Nat.eq_dec (edeg (degs p) a) 0) as [Da|Da].
  - assert (Fa := aff_flat p a Ha Da).
    destruct Hb as [Lb [Hb0 Hb]].
    exists (fun j => xr (xeval (xextend E p) a) * Lb j). split.
    + intros H0 j. cbn [edeg] in H0. rewrite (Hb0 ltac:(lia)). ring.
    + intros E' HE'. cbn [xeval]. rewrite (Fa E' HE'), (Hb E' HE'), Ra, Rb, !Xmul_r. cbn [xr].
      f_equal. rewrite (msum_ext (fun j => xr (xeval (xextend E p) a) * Lb j * dshift E E' j)
        (fun j => xr (xeval (xextend E p) a) * (Lb j * dshift E E' j))) by (intros; ring). rewrite msum_scal. ring.
  - assert (Db : edeg (degs p) b = 0%nat) by lia.
    assert (Fb := aff_flat p b Hb Db).
    destruct Ha as [La [Ha0 Ha]].
    exists (fun j => La j * xr (xeval (xextend E p) b)). split.
    + intros H0 j. cbn [edeg] in H0. lia.
    + intros E' HE'. cbn [xeval]. rewrite (Ha E' HE'), (Fb E' HE'), Ra, Rb, !Xmul_r. cbn [xr].
      f_equal. rewrite (msum_ext (fun j => La j * xr (xeval (xextend E p) b) * dshift E E' j)
        (fun j => xr (xeval (xextend E p) b) * (La j * dshift E E' j))) by (intros; ring). rewrite msum_scal. ring.
Qed.

Lemma aff_div : forall p a b, aff_expr p a -> aff_expr p b -> (edeg (degs p) (Ediv a b) <= 1)%nat ->
  (exists y, xeval (xextend E p) (Ediv a b) = Xreal y) -> aff_expr p (Ediv a b).
Proof.
  intros p a b Ha Hb Hd [y Hy]. cbn [edeg] in Hd.
  destruct (Nat.eqb_spec (edeg (degs p) b) 0) as [Db|Db]; [| lia].
  assert (Ra := aff_real p a Ha). assert (Rb := aff_real p b Hb).
  assert (Fb := aff_flat p b Hb Db).
  cbn [xeval] in Hy. rewrite Ra, Rb in Hy. assert (Hnz := Xdiv_real_nz _ _ _ Hy).
  destruct Ha as [La [Ha0 Ha]].
  exists (fun j => La j / xr (xeval (xextend E p) b)). split.
  - intros H0 j. cbn [edeg] in H0. rewrite Db in H0. cbn in H0. rewrite (Ha0 H0). unfold Rdiv. ring.
  - intros E' HE'. cbn [xeval]. rewrite (Ha E' HE'), (Fb E' HE'), Ra, Rb.
    rewrite !Xdiv_ok by exact Hnz. cbn [xr]. f_equal.
    rewrite (msum_ext (fun j => La j / xr (xeval (xextend E p) b) * dshift E E' j)
      (fun j => / xr (xeval (xextend E p) b) * (La j * dshift E E' j))) by (intros; unfold Rdiv; ring).
    rewrite msum_scal. field. exact Hnz.
Qed.

Lemma aff_fun :
  forall p a (op : expr -> expr), (forall E1, xeval E1 (op a) = xeval E1 (op a)) ->
  aff_expr p a -> edeg (degs p) a = 0%nat -> (forall E1 E2, xeval E1 a = xeval E2 a -> xeval E1 (op a) = xeval E2 (op a)) ->
  (exists y, xeval (xextend E p) (op a) = Xreal y) -> edeg (degs p) (op a) = 0%nat -> aff_expr p (op a).
Proof.
  intros p a op _ Ha Da Hop [y Hy] Dop. assert (Fa := aff_flat p a Ha Da).
  exists (fun _ => 0). split; [intros; reflexivity|].
  intros E' HE'. rewrite (Hop _ _ (Fa E' HE')), Hy. cbn [xr]. f_equal.
  rewrite msum_zero_L by (intros; reflexivity). ring.
Qed.

(** An atom of the list is affine when every slot below it is. *)
Lemma aff_atom :
  forall p a, is_atom a = true -> vars_below (base + length p) a = true ->
  (forall k, (k < base + length p)%nat -> aff_slot p k) -> aff_expr p a.
Proof.
  intros p a Ha Hv Hs. destruct a; try discriminate.
  - cbn [vars_below] in Hv. apply Nat.ltb_lt in Hv. destruct (Hs n Hv) as [L [HL0 HL]].
    exists L. split; [exact HL0|]. intros E' HE'. cbn [xeval]. exact (HL E' HE').
  - apply aff_const; [reflexivity | intros; reflexivity | eexists; reflexivity].
  - apply aff_const; [reflexivity | intros; reflexivity | eexists; reflexivity].
  - apply aff_const; [reflexivity | intros; reflexivity | eexists; reflexivity].
Qed.

(** Every slot of the list is affine on the fibre. *)
Theorem aff_sound :
  forall p, well_formed base p = true -> forallb (fun b => single (snd b)) p = true -> aff_ok p = true ->
  (forall k, (base <= k < base + length p)%nat -> exists y, eget k (xextend E p) Xnan = Xreal y) ->
  forall k, (k < base + length p)%nat -> aff_slot p k.
Proof.
  induction p as [|[n e] p IH] using rev_ind; intros Hwf Hs Hok Hre k Hk.
  - cbn [length] in Hk. rewrite Nat.add_0_r in Hk. apply aff_input; [exact Hk | exact (HE0 k Hk)].
  - rewrite DivDiff.well_formed_app in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwfp Hwfb].
    cbn [well_formed] in Hwfb. apply andb_prop in Hwfb. destruct Hwfb as [Hwfb _].
    apply andb_prop in Hwfb. destruct Hwfb as [Hn Hve]. apply Nat.eqb_eq in Hn.
    rewrite forallb_app in Hs. apply andb_prop in Hs. destruct Hs as [Hsp Hse]. cbn [forallb snd] in Hse.
    rewrite andb_true_r in Hse.
    rewrite aff_ok_snoc in Hok. apply andb_prop in Hok. destruct Hok as [Hokp Hoke]. cbn [snd] in Hoke.
    apply Nat.leb_le in Hoke.
    rewrite length_app in Hk, Hre. cbn [length] in Hk, Hre.
    assert (Hrep : forall k', (base <= k' < base + length p)%nat -> exists y, eget k' (xextend E p) Xnan = Xreal y).
    { intros k' Hk'. destruct (Hre k' ltac:(lia)) as [y Hy]. exists y. rewrite xextend_snoc in Hy.
      rewrite eget_eset_neq in Hy by lia. exact Hy. }
    assert (IHp := IH Hwfp Hsp Hokp Hrep).
    destruct (Nat.eq_dec k n) as [->|Hkn].
    + (* the new slot *)
      assert (Hy : exists y, xeval (xextend E p) e = Xreal y).
      { destruct (Hre n ltac:(lia)) as [y Hy]. exists y. rewrite xextend_snoc, eget_eset_eq in Hy. exact Hy. }
      assert (Hae : aff_expr p e).
      { rewrite Hn in Hve. destruct e; cbn [single] in Hse; cbn [vars_below] in Hve;
          try (apply andb_prop in Hse; destruct Hse as [Hsa Hsb]; apply andb_prop in Hve; destruct Hve as [Hva Hvb]).
        - apply aff_atom; [reflexivity | exact Hve | exact IHp].
        - apply aff_atom; [reflexivity | exact Hve | exact IHp].
        - apply aff_atom; [reflexivity | exact Hve | exact IHp].
        - apply aff_neg. apply aff_atom; assumption.
        - apply aff_add; apply aff_atom; assumption.
        - apply aff_sub; apply aff_atom; assumption.
        - apply aff_mul; [apply aff_atom; assumption | apply aff_atom; assumption | exact Hoke].
        - apply aff_div; [apply aff_atom; assumption | apply aff_atom; assumption | exact Hoke | exact Hy].
        - discriminate.
        - cbn [edeg] in Hoke. destruct (Nat.eqb_spec (edeg (degs p) e) 0) as [D0|D0]; [| lia].
          apply (aff_fun p e Esin); [reflexivity | apply aff_atom; assumption | exact D0 |
            intros E1 E2 H; cbn [xeval]; rewrite H; reflexivity | exact Hy | cbn [edeg]; rewrite D0; reflexivity].
        - cbn [edeg] in Hoke. destruct (Nat.eqb_spec (edeg (degs p) e) 0) as [D0|D0]; [| lia].
          apply (aff_fun p e Ecos); [reflexivity | apply aff_atom; assumption | exact D0 |
            intros E1 E2 H; cbn [xeval]; rewrite H; reflexivity | exact Hy | cbn [edeg]; rewrite D0; reflexivity].
        - cbn [edeg] in Hoke. destruct (Nat.eqb_spec (edeg (degs p) e) 0) as [D0|D0]; [| lia].
          apply (aff_fun p e Eexp); [reflexivity | apply aff_atom; assumption | exact D0 |
            intros E1 E2 H; cbn [xeval]; rewrite H; reflexivity | exact Hy | cbn [edeg]; rewrite D0; reflexivity].
        - cbn [edeg] in Hoke. destruct (Nat.eqb_spec (edeg (degs p) e) 0) as [D0|D0]; [| lia].
          apply (aff_fun p e Eatan); [reflexivity | apply aff_atom; assumption | exact D0 |
            intros E1 E2 H; cbn [xeval]; rewrite H; reflexivity | exact Hy | cbn [edeg]; rewrite D0; reflexivity].
        - apply aff_atom; [reflexivity | exact Hve | exact IHp]. }
      destruct Hae as [L [HL0 HL]]. exists L. split.
      * rewrite degs_snoc. cbn [fst snd]. rewrite eget_eset_eq. exact HL0.
      * intros E' HE'. rewrite !xextend_snoc, !eget_eset_eq. exact (HL E' HE').
    + assert (Hk' : (k < base + length p)%nat) by lia.
      destruct (IHp k Hk') as [L [HL0 HL]]. exists L. split.
      * rewrite degs_snoc. cbn [fst]. rewrite eget_eset_neq by exact Hkn. exact HL0.
      * intros E' HE'. rewrite !xextend_snoc. rewrite !eget_eset_neq by exact Hkn. exact (HL E' HE').
Qed.

End Aff.
