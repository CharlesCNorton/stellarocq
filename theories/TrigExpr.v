(** Which expressions are trigonometric polynomials in the angles.

    [tdeg] reads an expression and returns a bound on its degree in each of
    two angle slots, or nothing when the expression leaves the class: the
    angles may enter only through kernels cos(m u - n v) and sin(m u - n v)
    of the shape Physics.v writes, and a division, square root, exponential
    or arctangent may act only on something that reads no angle.
    [tdeg_binds] carries the bound through a binding list slot by slot.

    [tdeg_binds_sound] states what a bound means: along the angles the slot
    is either real everywhere or nowhere, and where it is real it is a
    trigonometric polynomial of that degree in the sense of TrigPoly.v. So
    [TrigPoly.exact2] applies, and an equispaced double sum over enough points
    is the integral over the torus; Harmonic.v is the checker built on it. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Quad Box TrigPoly.

Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* Families of values along the angles                               *)

(** A value along the two angles is uniform when it is real at every angle
    or at none, and polynomial of a degree when, being real, it is a
    trigonometric polynomial of that degree. *)
Definition fam := R -> R -> ExtendedR.

Definition unif (f : fam) : Prop :=
  (forall U V, exists r, f U V = Xreal r) \/ (forall U V, f U V = Xnan).

Definition good (d : nat * nat) (f : fam) : Prop :=
  unif f /\
  ((forall U V, exists r, f U V = Xreal r) ->
   TP2 (fst d) (snd d) (fun U V => proj_val (f U V))).

Definition constant (f : fam) : Prop := forall U V U' V', f U V = f U' V'.

Lemma good_ext : forall d f g, (forall U V, f U V = g U V) -> good d f -> good d g.
Proof.
  intros d f g H [Hu Hp]. split.
  - destruct Hu as [Hu|Hu]; [left|right]; intros U V; rewrite <- H; apply Hu.
  - intros Hr. apply (tp2_ext _ _ (fun U V => proj_val (f U V))).
    + intros U V. now rewrite H.
    + apply Hp. intros U V. rewrite H. apply Hr.
Qed.

Lemma good_mono :
  forall du dv du' dv' f, good (du, dv) f -> (du <= du')%nat -> (dv <= dv')%nat ->
  good (du', dv') f.
Proof.
  intros du dv du' dv' f [Hu Hp] H1 H2. split. exact Hu.
  intros Hr. apply (TP2_mono du dv). now apply Hp. exact H1. exact H2.
Qed.

Lemma good_const : forall f, constant f -> good (0, 0)%nat f.
Proof.
  intros f Hc. split.
  - destruct (f 0 0) as [|r] eqn:H0.
    + right. intros U V. rewrite (Hc U V 0 0). exact H0.
    + left. intros U V. exists r. rewrite (Hc U V 0 0). exact H0.
  - intros _. apply (tp2_ext 0 0 (fun _ _ => proj_val (f 0 0))).
    + intros U V. now rewrite (Hc U V 0 0).
    + apply TP2_const.
Qed.

(** A polynomial of degree zero is constant. *)
Lemma TP1_0_const : forall f, TP1 0 f -> forall x y, f x = f y.
Proof.
  intros f Hf. induction Hf; intros x y.
  - reflexivity.
  - assert (k = 0%nat) by lia. subst k. simpl. rewrite !Rmult_0_l, cos_0.
    rewrite (IHHf x y). reflexivity.
  - assert (k = 0%nat) by lia. subst k. simpl. rewrite !Rmult_0_l, sin_0.
    rewrite (IHHf x y). reflexivity.
  - rewrite <- !H. apply IHHf.
Qed.

Lemma TP2_slice_v : forall Du Dv F, TP2 Du Dv F -> forall u, TP1 Dv (fun v => F u v).
Proof.
  intros Du Dv F HF u. induction HF.
  - apply tp1_zero.
  - apply TP1_add. exact IHHF. now apply TP1_scal.
  - apply (tp1_ext Dv (fun v => F u v)). intros v. apply H. exact IHHF.
Qed.

Lemma TP2_00_const : forall F, TP2 0 0 F -> forall U V U' V', F U V = F U' V'.
Proof.
  intros F HF U V U' V'.
  rewrite (TP1_0_const _ (TP2_slice 0 0 F HF V) U U').
  apply (TP1_0_const _ (TP2_slice_v 0 0 F HF U') V V').
Qed.

(** A good family of degree zero is constant. *)
Lemma good_00_constant : forall f, good (0, 0)%nat f -> constant f.
Proof.
  intros f [[Hr|Hn] Hp] U V U' V'.
  - specialize (Hp Hr). simpl in Hp.
    destruct (Hr U V) as [a Ha]. destruct (Hr U' V') as [b Hb].
    assert (E := TP2_00_const _ Hp U V U' V'). cbv beta in E.
    rewrite Ha, Hb in *. simpl in E. now subst.
  - now rewrite Hn, Hn.
Qed.

(** A function of a constant is constant. *)
Lemma constant_map :
  forall (g : ExtendedR -> ExtendedR) f, constant f -> constant (fun U V => g (f U V)).
Proof. intros g f Hc U V U' V'. now rewrite (Hc U V U' V'). Qed.

Lemma good_neg : forall d f, good d f -> good d (fun U V => Xneg (f U V)).
Proof.
  intros d f [Hu Hp]. split.
  - destruct Hu as [Hr|Hn].
    + left. intros U V. destruct (Hr U V) as [r Hr']. rewrite Hr'. now exists (- r).
    + right. intros U V. now rewrite Hn.
  - intros Hr. assert (Hr' : forall U V, exists r, f U V = Xreal r).
    { intros U V. destruct (Hr U V) as [r H]. destruct (f U V); [discriminate|]. now exists r0. }
    apply (tp2_ext _ _ (fun U V => (-1) * proj_val (f U V))).
    + intros U V. destruct (Hr' U V) as [r H]. rewrite H. simpl. ring.
    + apply TP2_scal. now apply Hp.
Qed.

(** Binary sums and products: real where both are, and polynomial. *)
Lemma unif2 :
  forall (op : ExtendedR -> ExtendedR -> ExtendedR) f g,
  (forall a b, op (Xreal a) (Xreal b) <> Xnan) ->
  (forall y, op Xnan y = Xnan) -> (forall x, op x Xnan = Xnan) ->
  unif f -> unif g -> unif (fun U V => op (f U V) (g U V)).
Proof.
  intros op f g Hop Hl Hr [Hf|Hf] [Hg|Hg].
  - left. intros U V. destruct (Hf U V) as [a Ha]. destruct (Hg U V) as [b Hb].
    rewrite Ha, Hb. destruct (op (Xreal a) (Xreal b)) as [|r] eqn:E.
    + exfalso. now apply (Hop a b).
    + now exists r.
  - right. intros U V. now rewrite Hg, Hr.
  - right. intros U V. now rewrite Hf, Hl.
  - right. intros U V. now rewrite Hf, Hl.
Qed.

Lemma both_real :
  forall (f g : fam), (forall U V, exists r, Xadd (f U V) (g U V) = Xreal r) \/
              (forall U V, exists r, Xmul (f U V) (g U V) = Xreal r) \/
              (forall U V, exists r, Xsub (f U V) (g U V) = Xreal r) ->
  (forall U V, exists r, f U V = Xreal r) /\ (forall U V, exists r, g U V = Xreal r).
Proof.
  intros f g H. split; intros U V;
    destruct H as [H|[H|H]]; destruct (H U V) as [r Hr];
    destruct (f U V) as [|a]; destruct (g U V) as [|b]; simpl in Hr;
    try discriminate; eauto.
Qed.

Lemma good_add :
  forall du dv eu ev f g, good (du, dv) f -> good (eu, ev) g ->
  good (Nat.max du eu, Nat.max dv ev) (fun U V => Xadd (f U V) (g U V)).
Proof.
  intros du dv eu ev f g [Hfu Hfp] [Hgu Hgp]. split.
  - apply unif2; try easy. intros [|x]; reflexivity.
  - intros Hr. cbn [fst snd]. destruct (both_real f g (or_introl Hr)) as [Hrf Hrg].
    apply (tp2_ext _ _ (fun U V => proj_val (f U V) + proj_val (g U V))).
    + intros U V. destruct (Hrf U V) as [a Ha]. destruct (Hrg U V) as [b Hb].
      rewrite Ha, Hb. reflexivity.
    + apply TP2_add.
      * apply (TP2_mono du dv). now apply Hfp. lia. lia.
      * apply (TP2_mono eu ev). now apply Hgp. lia. lia.
Qed.

Lemma good_sub :
  forall du dv eu ev f g, good (du, dv) f -> good (eu, ev) g ->
  good (Nat.max du eu, Nat.max dv ev) (fun U V => Xsub (f U V) (g U V)).
Proof.
  intros du dv eu ev f g [Hfu Hfp] [Hgu Hgp]. split.
  - apply unif2; try easy. intros [|x]; reflexivity.
  - intros Hr. cbn [fst snd].
    destruct (both_real f g (or_intror (or_intror Hr))) as [Hrf Hrg].
    apply (tp2_ext _ _ (fun U V => proj_val (f U V) - proj_val (g U V))).
    + intros U V. destruct (Hrf U V) as [a Ha]. destruct (Hrg U V) as [b Hb].
      rewrite Ha, Hb. reflexivity.
    + apply TP2_sub.
      * apply (TP2_mono du dv). now apply Hfp. lia. lia.
      * apply (TP2_mono eu ev). now apply Hgp. lia. lia.
Qed.

Lemma good_mul :
  forall du dv eu ev f g, good (du, dv) f -> good (eu, ev) g ->
  good (du + eu, dv + ev)%nat (fun U V => Xmul (f U V) (g U V)).
Proof.
  intros du dv eu ev f g [Hfu Hfp] [Hgu Hgp]. split.
  - apply unif2; try easy. intros [|x]; reflexivity.
  - intros Hr. cbn [fst snd].
    destruct (both_real f g (or_intror (or_introl Hr))) as [Hrf Hrg].
    apply (tp2_ext _ _ (fun U V => proj_val (f U V) * proj_val (g U V))).
    + intros U V. destruct (Hrf U V) as [a Ha]. destruct (Hrg U V) as [b Hb].
      rewrite Ha, Hb. reflexivity.
    + apply TP2_mul. now apply Hfp. now apply Hgp.
Qed.

(** Division by a constant. *)
Lemma good_div_const :
  forall d f g, good d f -> constant g -> good d (fun U V => Xdiv (f U V) (g U V)).
Proof.
  intros d f g [Hfu Hfp] Hc.
  destruct (g 0 0) as [|c] eqn:Hg0.
  - (* NaN everywhere *)
    apply good_ext with (f := fun _ _ => Xnan).
    + intros U V. rewrite (Hc U V 0 0), Hg0. destruct (f U V); reflexivity.
    + split. right. reflexivity. intros H. destruct (H 0 0) as [r Hr]. discriminate.
  - destruct (is_zero_spec c) as [Hz|Hz].
    + apply good_ext with (f := fun _ _ => Xnan).
      * intros U V. rewrite (Hc U V 0 0), Hg0. destruct (f U V); simpl; try reflexivity.
        unfold Xdiv'. subst c. destruct (is_zero_spec 0); [reflexivity|lra].
      * split. right. reflexivity. intros H. destruct (H 0 0) as [r Hr]. discriminate.
    + apply good_ext with (f := fun U V => Xmul (f U V) (Xreal (/ c))).
      * intros U V. rewrite (Hc U V 0 0), Hg0. destruct (f U V) as [|a]; simpl.
        reflexivity. unfold Xdiv'. destruct (is_zero_spec c); [contradiction|].
        reflexivity.
      * destruct d as [du dv].
        replace (du, dv) with (du + 0, dv + 0)%nat by (f_equal; lia).
        apply good_mul. split. exact Hfu. exact Hfp.
        apply good_const. intros U V U' V'. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* The degree of an expression                                       *)

Section Degree.

Variable su sv base : nat.
Variable eu ev : Z.

(** A kernel argument m u - n v, read off the slots of the two angles with
    their exponents, as Physics.kern_arg writes it. *)
Definition kern_shape (a : expr) : option (Z * Z) :=
  match a with
  | Esub (Emul (EfromZ m) (Emul (Evar k1) (Epow2 e1)))
         (Emul (EfromZ n) (Emul (Evar k2) (Epow2 e2))) =>
      if Nat.eqb k1 su && Nat.eqb k2 sv && Z.eqb e1 eu && Z.eqb e2 ev
      then Some (m, n) else None
  | _ => None
  end.

Definition dmax (a b : nat * nat) : nat * nat :=
  (Nat.max (fst a) (fst b), Nat.max (snd a) (snd b)).
Definition dadd (a b : nat * nat) : nat * nat :=
  (fst a + fst b, snd a + snd b)%nat.
Definition is00 (d : nat * nat) : bool :=
  Nat.eqb (fst d) 0 && Nat.eqb (snd d) 0.

Fixpoint tdeg (tab : env (option (nat * nat))) (e : expr) : option (nat * nat) :=
  match e with
  | Evar k =>
      if Nat.eqb k su || Nat.eqb k sv then None
      else if Nat.ltb k base then Some (0, 0)%nat else eget k tab None
  | EfromZ _ => Some (0, 0)%nat
  | Epi => Some (0, 0)%nat
  | Epow2 _ => Some (0, 0)%nat
  | Eneg a => tdeg tab a
  | Eadd a b | Esub a b =>
      match tdeg tab a, tdeg tab b with
      | Some x, Some y => Some (dmax x y) | _, _ => None end
  | Emul a b =>
      match tdeg tab a, tdeg tab b with
      | Some x, Some y => Some (dadd x y) | _, _ => None end
  | Ediv a b =>
      match tdeg tab a, tdeg tab b with
      | Some x, Some y => if is00 y then Some x else None | _, _ => None end
  | Esqrt a | Eexp a | Eatan a =>
      match tdeg tab a with
      | Some x => if is00 x then Some (0, 0)%nat else None | None => None end
  | Ecos a | Esin a =>
      match kern_shape a with
      | Some (m, n) => Some (Z.abs_nat m, Z.abs_nat n)
      | None =>
          match tdeg tab a with
          | Some x => if is00 x then Some (0, 0)%nat else None | None => None end
      end
  end.

Fixpoint tdeg_binds (tab : env (option (nat * nat))) (bs : list binding)
    : env (option (nat * nat)) :=
  match bs with
  | [] => tab
  | (k, e) :: tl => tdeg_binds (eset k tab (tdeg tab e)) tl
  end.

(** The state at the angles (U, V): the angle slots hold U and V in their
    mantissa units, everything else of the input as the state gives it. *)
Variable X : env ExtendedR.

Definition at_angles (U V : R) : env ExtendedR :=
  eset su (eset sv X (Xreal (V / powerRZ 2 ev))) (Xreal (U / powerRZ 2 eu)).

Hypothesis Hsu : (su < base)%nat.
Hypothesis Hsv : (sv < base)%nat.
Hypothesis Huv : su <> sv.

(** What holds of an environment family and a degree table. *)
Definition dinv (tab : env (option (nat * nat))) (E : R -> R -> env ExtendedR) : Prop :=
  (forall k, (k < base)%nat -> k <> su -> k <> sv ->
     forall U V, eget k (E U V) Xnan = eget k X Xnan) /\
  (forall U V, eget su (E U V) Xnan = Xreal (U / powerRZ 2 eu) /\
               eget sv (E U V) Xnan = Xreal (V / powerRZ 2 ev)) /\
  (forall k d, eget k tab None = Some d -> good d (fun U V => eget k (E U V) Xnan)).

Lemma dinv_start : dinv eempty at_angles.
Proof using Huv Hsu Hsv.
  split; [|split].
  - intros k Hk H1 H2 U V. unfold at_angles.
    rewrite eget_eset_neq by exact H1. now rewrite eget_eset_neq by exact H2.
  - intros U V. unfold at_angles. split.
    + now rewrite eget_eset_eq.
    + rewrite eget_eset_neq by (intros H; apply Huv; now symmetry).
      now rewrite eget_eset_eq.
  - intros k d H. rewrite eget_eempty in H. discriminate.
Qed.

Lemma powerRZ_2_neq : forall e, powerRZ 2 e <> 0.
Proof. intros e. apply powerRZ_NOR. lra. Qed.

(** The kernels are what their shape says. *)
Lemma kern_value :
  forall tab E a m n U V, dinv tab E -> kern_shape a = Some (m, n) ->
  xeval (E U V) a = Xreal (IZR m * U - IZR n * V).
Proof using.
  intros tab E a m n U V [_ [Hang _]] Hk.
  destruct a; try discriminate.
  destruct a1; try discriminate. destruct a1_1; try discriminate.
  destruct a1_2; try discriminate. destruct a1_2_1; try discriminate.
  destruct a1_2_2; try discriminate.
  destruct a2; try discriminate. destruct a2_1; try discriminate.
  destruct a2_2; try discriminate. destruct a2_2_1; try discriminate.
  destruct a2_2_2; try discriminate.
  simpl in Hk.
  destruct (Nat.eqb n0 su) eqn:E1; [|discriminate].
  destruct (Nat.eqb n1 sv) eqn:E2; [|discriminate].
  destruct (Z.eqb z0 eu) eqn:E3; [|discriminate].
  destruct (Z.eqb z2 ev) eqn:E4; [|discriminate].
  simpl in Hk. injection Hk as <- <-.
  apply Nat.eqb_eq in E1, E2. apply Z.eqb_eq in E3, E4. subst.
  destruct (Hang U V) as [Hu Hv].
  simpl. rewrite Hu, Hv. simpl. f_equal.
  assert (H1 := powerRZ_2_neq eu). assert (H2 := powerRZ_2_neq ev).
  field. split; assumption.
Qed.

(** The degree an expression is given bounds it. *)
Lemma tdeg_sound :
  forall tab E e d, dinv tab E -> tdeg tab e = Some d ->
  good d (fun U V => xeval (E U V) e).
Proof using Hsu Hsv Huv.
  intros tab E e. induction e; intros d Hinv Hd; simpl in Hd.
  - (* a slot *)
    destruct Hinv as [Hin [Hang Htab]].
    destruct (Nat.eqb n su || Nat.eqb n sv) eqn:Hs; [discriminate|].
    apply orb_false_iff in Hs. destruct Hs as [H1 H2].
    apply Nat.eqb_neq in H1, H2.
    destruct (Nat.ltb n base) eqn:Hb.
    + injection Hd as <-. apply Nat.ltb_lt in Hb.
      apply good_const. intros U V U' V'. simpl.
      rewrite (Hin n Hb H1 H2 U V), (Hin n Hb H1 H2 U' V'). reflexivity.
    + simpl. exact (Htab n d Hd).
  - injection Hd as <-. apply good_const. intros U V U' V'. reflexivity.
  - injection Hd as <-. apply good_const. intros U V U' V'. reflexivity.
  - simpl. apply good_neg. now apply IHe.
  - destruct (tdeg tab e1) as [x|] eqn:H1; [|discriminate].
    destruct (tdeg tab e2) as [y|] eqn:H2; [|discriminate].
    injection Hd as <-. destruct x as [x1 x2], y as [y1 y2].
    exact (good_add _ _ _ _ _ _ (IHe1 _ Hinv eq_refl) (IHe2 _ Hinv eq_refl)).
  - destruct (tdeg tab e1) as [x|] eqn:H1; [|discriminate].
    destruct (tdeg tab e2) as [y|] eqn:H2; [|discriminate].
    injection Hd as <-. destruct x as [x1 x2], y as [y1 y2].
    exact (good_sub _ _ _ _ _ _ (IHe1 _ Hinv eq_refl) (IHe2 _ Hinv eq_refl)).
  - destruct (tdeg tab e1) as [x|] eqn:H1; [|discriminate].
    destruct (tdeg tab e2) as [y|] eqn:H2; [|discriminate].
    injection Hd as <-. destruct x as [x1 x2], y as [y1 y2].
    exact (good_mul _ _ _ _ _ _ (IHe1 _ Hinv eq_refl) (IHe2 _ Hinv eq_refl)).
  - destruct (tdeg tab e1) as [x|] eqn:H1; [|discriminate].
    destruct (tdeg tab e2) as [y|] eqn:H2; [|discriminate].
    destruct (is00 y) eqn:Hy; [|discriminate]. injection Hd as <-.
    unfold is00 in Hy. apply andb_prop in Hy. destruct Hy as [Ha Hb].
    apply Nat.eqb_eq in Ha, Hb. destruct y as [y1 y2]. simpl in Ha, Hb. subst.
    apply good_div_const. exact (IHe1 _ Hinv eq_refl).
    apply good_00_constant. exact (IHe2 _ Hinv eq_refl).
  - (* sqrt *)
    destruct (tdeg tab e) as [x|] eqn:H1; [|discriminate].
    destruct (is00 x) eqn:Hx; [|discriminate]. injection Hd as <-.
    unfold is00 in Hx. apply andb_prop in Hx. destruct Hx as [Ha Hb].
    apply Nat.eqb_eq in Ha, Hb. destruct x as [x1 x2]. simpl in Ha, Hb. subst.
    apply good_const. apply (constant_map (fun y => Xsqrt y)).
    apply good_00_constant. exact (IHe _ Hinv eq_refl).
  - (* sin *)
    destruct (kern_shape e) as [[m n]|] eqn:Hk.
    + injection Hd as <-. split.
      * left. intros U V. simpl. rewrite (kern_value tab E e m n U V Hinv Hk).
        eexists. reflexivity.
      * intros _. apply (tp2_ext _ _ (fun U V => sin (IZR m * U - IZR n * V))).
        -- intros U V. simpl. now rewrite (kern_value tab E e m n U V Hinv Hk).
        -- apply TP2_sin_kernel.
    + destruct (tdeg tab e) as [x|] eqn:H1; [|discriminate].
      destruct (is00 x) eqn:Hx; [|discriminate]. injection Hd as <-.
      unfold is00 in Hx. apply andb_prop in Hx. destruct Hx as [Ha Hb].
      apply Nat.eqb_eq in Ha, Hb. destruct x as [x1 x2]. simpl in Ha, Hb. subst.
      apply good_const. apply (constant_map (fun y => Xsin y)).
      apply good_00_constant. exact (IHe _ Hinv eq_refl).
  - (* cos *)
    destruct (kern_shape e) as [[m n]|] eqn:Hk.
    + injection Hd as <-. split.
      * left. intros U V. simpl. rewrite (kern_value tab E e m n U V Hinv Hk).
        eexists. reflexivity.
      * intros _. apply (tp2_ext _ _ (fun U V => cos (IZR m * U - IZR n * V))).
        -- intros U V. simpl. now rewrite (kern_value tab E e m n U V Hinv Hk).
        -- apply TP2_cos_kernel.
    + destruct (tdeg tab e) as [x|] eqn:H1; [|discriminate].
      destruct (is00 x) eqn:Hx; [|discriminate]. injection Hd as <-.
      unfold is00 in Hx. apply andb_prop in Hx. destruct Hx as [Ha Hb].
      apply Nat.eqb_eq in Ha, Hb. destruct x as [x1 x2]. simpl in Ha, Hb. subst.
      apply good_const. apply (constant_map (fun y => Xcos y)).
      apply good_00_constant. exact (IHe _ Hinv eq_refl).
  - (* exp *)
    destruct (tdeg tab e) as [x|] eqn:H1; [|discriminate].
    destruct (is00 x) eqn:Hx; [|discriminate]. injection Hd as <-.
    unfold is00 in Hx. apply andb_prop in Hx. destruct Hx as [Ha Hb].
    apply Nat.eqb_eq in Ha, Hb. destruct x as [x1 x2]. simpl in Ha, Hb. subst.
    apply good_const. apply (constant_map (fun y => Xexp y)).
    apply good_00_constant. exact (IHe _ Hinv eq_refl).
  - (* atan *)
    destruct (tdeg tab e) as [x|] eqn:H1; [|discriminate].
    destruct (is00 x) eqn:Hx; [|discriminate]. injection Hd as <-.
    unfold is00 in Hx. apply andb_prop in Hx. destruct Hx as [Ha Hb].
    apply Nat.eqb_eq in Ha, Hb. destruct x as [x1 x2]. simpl in Ha, Hb. subst.
    apply good_const. apply (constant_map (fun y => Xatan y)).
    apply good_00_constant. exact (IHe _ Hinv eq_refl).
  - injection Hd as <-. apply good_const. intros U V U' V'. reflexivity.
Qed.

(** One binding keeps the invariant: the new slot is good at the degree its
    expression is given, and nothing else changes. *)
Lemma dinv_step :
  forall tab E k e,
  dinv tab E -> (base <= k)%nat ->
  dinv (eset k tab (tdeg tab e))
       (fun U V => eset k (E U V) (xeval (E U V) e)).
Proof using Hsu Hsv Huv.
  intros tab E k e Hinv Hk.
  assert (Hinv0 := Hinv). destruct Hinv as [Hin [Hang Htab]].
  split; [|split].
  - intros j Hj H1 H2 U V. rewrite eget_eset_neq by lia. now apply Hin.
  - intros U V. destruct (Hang U V) as [Hu Hv].
    rewrite !eget_eset_neq by lia. now split.
  - intros j d Hjd. destruct (Nat.eq_dec j k) as [->|Hjk].
    + rewrite eget_eset_eq in Hjd.
      apply good_ext with (f := fun U V => xeval (E U V) e).
      * intros U V. now rewrite eget_eset_eq.
      * exact (tdeg_sound tab E e d Hinv0 Hjd).
    + rewrite eget_eset_neq in Hjd by exact Hjk.
      apply good_ext with (f := fun U V => eget j (E U V) Xnan).
      * intros U V. now rewrite eget_eset_neq by exact Hjk.
      * exact (Htab j d Hjd).
Qed.

Lemma dinv_binds :
  forall bs tab E next,
  dinv tab E -> well_formed next bs = true -> (base <= next)%nat ->
  dinv (tdeg_binds tab bs) (fun U V => xextend (E U V) bs).
Proof using Hsu Hsv Huv.
  induction bs as [|[k e] tl IH]; intros tab E next Hinv Hwf Hn.
  - exact Hinv.
  - simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
    apply andb_prop in Hwf. destruct Hwf as [Hk _]. apply Nat.eqb_eq in Hk. subst k.
    simpl tdeg_binds.
    apply (IH _ (fun U V => eset next (E U V) (xeval (E U V) e)) (S next)).
    + now apply dinv_step.
    + exact Htl.
    + lia.
Qed.

(** What a degree bound read off a binding list means for a slot after it. *)
Theorem tdeg_binds_sound :
  forall bs n d,
  well_formed base bs = true ->
  eget n (tdeg_binds eempty bs) None = Some d ->
  good d (fun U V => eget n (xextend (at_angles U V) bs) Xnan).
Proof using Hsu Hsv Huv.
  intros bs n d Hwf Hd.
  destruct (dinv_binds bs eempty at_angles base dinv_start Hwf (le_n _))
    as [_ [_ Htab]].
  exact (Htab n d Hd).
Qed.

End Degree.
