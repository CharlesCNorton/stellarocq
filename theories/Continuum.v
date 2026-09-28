(** * The continuum residual is mu0 (J x B - grad p) of the reconstructed field

    [continuum_force] is the whole chain for the continuum residual Physics.v
    builds ([residual] with the output [RRadial]) for a stellarator-symmetric
    state. Read in the environment its bindings produce, its three outputs
    are the covariant components along e_s, e_u and e_v of
    mu0 (J x B - grad p) of the field VMEC's ansatz gives the
    reconstruction: R and Z are the Fourier series whose coefficient of each
    mode is the cubic Hermite in the radius through VMEC's half-grid value
    and slope at the two half points ([hval], [hslope], from the node values
    by the parity rule), lambda is the sine series whose coefficients follow
    the parity rule linearly between the half points, iota is linear between
    them, and p is any pressure whose derivative at the point is the
    profile's [pprime].

    The proof reads the builder one stage at a time. Every binding of every
    stage lies among the final bindings, which the checker's well-formedness
    test makes hold their values ([sound]); from them each stage's outputs
    have the values of the reconstruction and of its derivatives
    ([Series]), the formula stage evaluates [Force.cres_s], [cres_u] and
    [cres_v] of that jet ([fp_residual]), and [Force.force_law] identifies
    those with the force. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Deriv Cell Force Series Recon.
Import ListNotations.

(** * Bindings that hold their values *)

Definition sound (E : env ExtendedR) (l : list binding) : Prop :=
  forall n e, In (n, e) l -> eget n E Xnan = xeval E e.

Lemma sound_extends (E : env ExtendedR) (b b' : builder) :
  extends b b' -> sound E (b_binds b') -> sound E (b_binds b).
Proof. intros [l H] S n e Hin. apply S. rewrite H. apply in_or_app. right. exact Hin. Qed.

Lemma alloc_sound (E : env ExtendedR) (b : builder) (e : expr) (b' : builder) (x : expr) :
  alloc b e = (b', x) -> sound E (b_binds b') -> sound E (b_binds b) /\ xeval E x = xeval E e.
Proof.
  unfold alloc. intros H S. injection H as <- <-. cbn [b_binds] in S. split.
  - intros n e' Hin. apply S. right. exact Hin.
  - cbn [xeval]. apply S. left. reflexivity.
Qed.

(** The final bindings of a residual the checker accepts hold their values. *)
Lemma sound_final (env : env ExtendedR) (m : nat) (b : builder) :
  well_formed m (bindings_of b) = true -> sound (xextend env (bindings_of b)) (b_binds b).
Proof.
  intros Hwf n e Hin. apply (binding_holds _ env m n e Hwf). unfold bindings_of.
  apply (proj1 (in_rev _ _)). exact Hin.
Qed.

Lemma is_zero_false (x : R) : x <> 0%R -> is_zero x = false.
Proof.
  intros H. generalize (is_zero_spec x). case (is_zero x); [intros Hz; inversion Hz; contradiction | reflexivity].
Qed.

Ltac step :=
  match goal with
  | |- match ?t with _ => _ end = _ -> _ =>
      let Q := fresh "Q" in destruct t as [? ?] eqn:Q; cbv beta iota zeta
  end.

Ltac stepH H :=
  match type of H with
  | (match ?t with _ => _ end) = _ => let A := fresh "A" in destruct t as [? ?] eqn:A; cbv beta iota zeta in H
  end.

Ltac ext_of_allocs :=
  repeat match goal with
  | A : alloc ?b ?e = (?b', ?x) |- _ =>
      lazymatch goal with
      | _ : extends b b' |- _ => fail
      | _ => pose proof (proj1 (alloc_spec b e b' x A))
      end
  end.

Ltac ext_chain := repeat (eapply extends_trans; [eassumption |]); apply extends_refl.

Ltac peel :=
  repeat match goal with
  | S : sound ?E (b_binds ?b'), A : alloc ?b ?e = (?b', ?x) |- _ =>
      let V := fresh "V" in let S1 := fresh "S" in
      destruct (alloc_sound E b e b' x A S) as [S1 V]; clear A
  end.

Ltac xcalc :=
  repeat (first [ progress cbn [xeval]
                | match goal with V : xeval ?E ?x = _ |- context [xeval ?E ?x] => rewrite V end ]).

Ltac nz := first [ assumption | lra
  | apply Rgt_not_eq, sqrt_lt_R0; lra
  | apply Rmult_integral_contrapositive_currified; nz ].

Ltac xclose :=
  cbv [Xbind2 Xbind Xdiv' Xsqrt'];
  repeat match goal with |- context [is_zero ?d] => rewrite (is_zero_false d) by nz end;
  f_equal.

Ltac splits := repeat match goal with |- _ /\ _ => split end.

(** * The stages of [full_point_b] *)

Section Stages.
Variable exps : list Z.
Variable E : env ExtendedR.

Lemma half_scalars_ok (b : builder) (sa sb sh : expr) (b' : builder) (hs : half_scalars) :
  half_scalars_b b sa sb sh = (b', hs) -> extends b b' /\
  (sound E (b_binds b') -> forall a bb h : R,
   xeval E sa = Xreal a -> xeval E sb = Xreal bb -> xeval E sh = Xreal h ->
   (0 < a)%R -> (0 < bb)%R -> (0 < h)%R -> (bb - a <> 0)%R ->
   xeval E (hs_half hs) = Xreal (1 / 2) /\ xeval E (hs_inv_h hs) = Xreal (1 / (bb - a)) /\
   xeval E (hs_sqrt_h hs) = Xreal (sqrt h) /\ xeval E (hs_inv_sqrt_a hs) = Xreal (1 / sqrt a) /\
   xeval E (hs_inv_sqrt_b hs) = Xreal (1 / sqrt bb) /\ xeval E (hs_inv_2s hs) = Xreal (1 / (2 * h))).
Proof.
  unfold half_scalars_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S a bb h Ha Hb Hh Pa Pb Ph Hab. peel. unfold Physics.e1, Physics.e2 in *.
  cbn [hs_half hs_inv_h hs_sqrt_h hs_inv_sqrt_a hs_inv_sqrt_b hs_inv_2s].
  splits; xcalc; xclose; first [reflexivity | ring | field; nz].
Qed.

Lemma herm_scalars_ok (b : builder) (sa sb s : expr) (b' : builder) (hm : herm_scalars) :
  herm_scalars_b b sa sb s = (b', hm) -> extends b b' /\
  (sound E (b_binds b') -> forall a bb x : R,
   xeval E sa = Xreal a -> xeval E sb = Xreal bb -> xeval E s = Xreal x -> (bb - a <> 0)%R ->
   let t := ((x - a) * (1 / (bb - a)))%R in
   xeval E (hm_H hm) = Xreal (bb - a) /\ xeval E (hm_invH hm) = Xreal (1 / (bb - a)) /\
   xeval E (hm_t hm) = Xreal t /\
   xeval E (hm_h10 hm) = Xreal (t * (t * t) - 2 * (t * t) + t) /\
   xeval E (hm_h11 hm) = Xreal (t * (t * t) - t * t) /\
   xeval E (hm_g10 hm) = Xreal (3 * (t * t) - 4 * t + 1) /\ xeval E (hm_g11 hm) = Xreal (3 * (t * t) - 2 * t) /\
   xeval E (hm_m0 hm) = Xreal (6 * t - 4) /\ xeval E (hm_m1 hm) = Xreal (6 * t - 2)).
Proof.
  unfold herm_scalars_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S a bb x Ha Hb Hx Hab. peel. unfold Physics.e1, Physics.esq, Physics.zmul in *.
  cbn [hm_H hm_invH hm_t hm_h10 hm_h11 hm_g10 hm_g11 hm_m0 hm_m1].
  splits; xcalc; xclose; first [reflexivity | ring | field; nz].
Qed.

Lemma rad_scalars_ok (b : builder) (sa sb s : expr) (b' : builder) (rl : rad_scalars) :
  rad_scalars_b b sa sb s = (b', rl) -> extends b b' /\
  (sound E (b_binds b') -> forall a bb x : R,
   xeval E sa = Xreal a -> xeval E sb = Xreal bb -> xeval E s = Xreal x ->
   (0 < a)%R -> (0 < bb)%R -> (0 < x)%R -> (bb - a <> 0)%R ->
   xeval E (rs_w rl) = Xreal ((x - a) * (1 / (bb - a))) /\ xeval E (rs_inv_h rl) = Xreal (1 / (bb - a)) /\
   xeval E (rs_sqrt rl) = Xreal (sqrt x) /\ xeval E (rs_inv_sqrt_a rl) = Xreal (1 / sqrt a) /\
   xeval E (rs_inv_sqrt_b rl) = Xreal (1 / sqrt bb) /\ xeval E (rs_inv_2s rl) = Xreal (1 / (2 * x))).
Proof.
  unfold rad_scalars_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S a bb x Ha Hb Hx Pa Pb Px Hab. peel. unfold Physics.e1, Physics.e2, Physics.e4, Physics.esq in *.
  cbn [rs_w rs_inv_h rs_sqrt rs_inv_sqrt_a rs_inv_sqrt_b rs_inv_2s].
  splits; xcalc; xclose; first [reflexivity | ring | field; nz].
Qed.

Lemma fpartials_ok (b : builder) (p : fpartials) (b' : builder) (q : fpartials) :
  fpartials_b b p = (b', q) -> extends b b' /\
  (sound E (b_binds b') ->
   xeval E (fp_0 q) = xeval E (fp_0 p) /\ xeval E (fp_s q) = xeval E (fp_s p) /\
   xeval E (fp_ss q) = xeval E (fp_ss p) /\ xeval E (fp_u q) = xeval E (fp_u p) /\
   xeval E (fp_v q) = xeval E (fp_v p) /\ xeval E (fp_su q) = xeval E (fp_su p) /\
   xeval E (fp_sv q) = xeval E (fp_sv p) /\ xeval E (fp_uu q) = xeval E (fp_uu p) /\
   xeval E (fp_uv q) = xeval E (fp_uv p) /\ xeval E (fp_vv q) = xeval E (fp_vv p)).
Proof.
  unfold fpartials_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S. peel. cbn [fp_0 fp_s fp_ss fp_u fp_v fp_su fp_sv fp_uu fp_uv fp_vv]. splits; assumption.
Qed.

Lemma flambda_ok (b : builder) (p : flpartials) (b' : builder) (q : flpartials) :
  flambda_partials_b b p = (b', q) -> extends b b' /\
  (sound E (b_binds b') ->
   xeval E (flp_u q) = xeval E (flp_u p) /\ xeval E (flp_v q) = xeval E (flp_v p) /\
   xeval E (flp_su q) = xeval E (flp_su p) /\ xeval E (flp_sv q) = xeval E (flp_sv p) /\
   xeval E (flp_uu q) = xeval E (flp_uu p) /\ xeval E (flp_uv q) = xeval E (flp_uv p) /\
   xeval E (flp_vv q) = xeval E (flp_vv p)).
Proof.
  unfold flambda_partials_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S. peel. cbn [flp_u flp_v flp_su flp_sv flp_uu flp_uv flp_vv]. splits; assumption.
Qed.

(** VMEC's half-grid value and slope of one coefficient of poloidal number
    m between the nodes sa and sb, at the half point sh, from its node values
    ya and yb, as [halfcoef_b] writes them. *)
Definition hval (m : Z) (sa sb sh ya yb : R) : R :=
  if Z.even m then (1 / 2 * (ya + yb))%R
  else (sqrt sh * (1 / 2 * (ya * (1 / sqrt sa) + yb * (1 / sqrt sb))))%R.
Definition hslope (m : Z) (sa sb sh ya yb : R) : R :=
  if Z.even m then ((yb - ya) * (1 / (sb - sa)))%R
  else (sqrt sh * ((yb * (1 / sqrt sb) - ya * (1 / sqrt sa)) * (1 / (sb - sa)))
        + sqrt sh * (1 / 2 * (ya * (1 / sqrt sa) + yb * (1 / sqrt sb))) * (1 / (2 * sh)))%R.

Lemma halfcoefs_values (hs : half_scalars) (base K ra rb : nat) (sa sb sh : R) (ya yb : nat -> R) :
  xeval E (hs_half hs) = Xreal (1 / 2) -> xeval E (hs_inv_h hs) = Xreal (1 / (sb - sa)) ->
  xeval E (hs_sqrt_h hs) = Xreal (sqrt sh) -> xeval E (hs_inv_sqrt_a hs) = Xreal (1 / sqrt sa) ->
  xeval E (hs_inv_sqrt_b hs) = Xreal (1 / sqrt sb) -> xeval E (hs_inv_2s hs) = Xreal (1 / (2 * sh)) ->
  forall (modes : list (Z * Z)) (k : nat) (b b' : builder) (cs : list coef2),
  halfcoefs_b exps b hs base K ra rb modes k = (b', cs) ->
  (forall j, (k <= j)%nat -> (j < k + length modes)%nat ->
     xeval E (slot_node exps base K ra j) = Xreal (ya j) /\ xeval E (slot_node exps base K rb j) = Xreal (yb j)) ->
  sound E (b_binds b') ->
  Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) sa sb sh (ya (fst jmn)) (yb (fst jmn))) /\
                        xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) sa sb sh (ya (fst jmn)) (yb (fst jmn))))
          (combine (seq k (length modes)) modes) cs.
Proof.
  intros Hh Hi Hq Ha Hb H2 modes. induction modes as [| mn tl IH]; intros k b b' cs H Hy Sd.
  - cbn in H. injection H as <- <-. constructor.
  - cbn [halfcoefs_b] in H.
    destruct (halfcoef_b b hs (fst mn) (slot_node exps base K ra k) (slot_node exps base K rb k))
      as [b1 c] eqn:A1.
    destruct (halfcoefs_b exps b1 hs base K ra rb tl (Datatypes.S k)) as [b2 rest] eqn:A2.
    injection H as <- <-.
    destruct (halfcoefs_spec exps hs base K ra rb tl (Datatypes.S k) b1 b2 rest A2) as [X2 _].
    pose proof (sound_extends E b1 b2 X2 Sd) as S1.
    cbn [length seq combine]. constructor.
    + destruct (Hy k ltac:(lia) ltac:(cbn [length]; lia)) as [Ya Yb].
      unfold halfcoef_b in A1. unfold hval, hslope. cbn [fst snd].
      destruct (Z.even (fst mn)); repeat stepH A1; injection A1 as <- <-; clear Sd; peel;
        cbn [c_val c_ds]; split; xcalc; xclose; first [reflexivity | ring].
    + apply (IH (Datatypes.S k) b1 b2 rest A2); [intros j Hj1 Hj2; apply Hy; cbn [length]; lia | exact Sd].
Qed.

Lemma kernels_values (u v : R) (modes : list (Z * Z)) (b b' : builder) (kers : list mode_kernels) :
  kernels_b exps b modes = (b', kers) -> sound E (b_binds b') ->
  xeval E (vU exps) = Xreal u -> xeval E (vV exps) = Xreal v ->
  Forall2 (fun mn k => mk_m k = fst mn /\ mk_n k = snd mn /\
    xeval E (mk_cos k) = Xreal (cos (IZR (fst mn) * u - IZR (snd mn) * v)) /\
    xeval E (mk_sin k) = Xreal (sin (IZR (fst mn) * u - IZR (snd mn) * v))) modes kers.
Proof.
  intros H S Hu Hv. destruct (kernels_spec exps modes b b' kers H) as [_ F].
  eapply Forall2_impl; [| exact F]. intros mn k (Hm & Hn & [c [Hc Ic]] & [d [Hd Id]]).
  refine (conj Hm (conj Hn (conj _ _))).
  - rewrite Hc. cbn [xeval]. rewrite (S c _ Ic). unfold kern_arg. cbn [xeval]. rewrite Hu, Hv. reflexivity.
  - rewrite Hd. cbn [xeval]. rewrite (S d _ Id). unfold kern_arg. cbn [xeval]. rewrite Hu, Hv. reflexivity.
Qed.

End Stages.

(** * Values of the series *)

Lemma esum_map_val {A B : Type} (E : env ExtendedR) (f : A -> expr) (g : B -> R) (ps : list A) (ts : list B) :
  Forall2 (fun p t => xeval E (f p) = Xreal (g t)) ps ts ->
  xeval E (esum (map f ps)) = Xreal (lsum g ts).
Proof.
  intros H. induction H as [| p t ps ts Hp Hs IH]; [reflexivity |].
  destruct ps as [| p' ps'].
  - inversion Hs; subst. cbn [map esum]. rewrite Hp. unfold lsum. cbn [map fold_right]. f_equal. ring.
  - change (esum (map f (p :: p' :: ps'))) with (Eadd (f p) (esum (map f (p' :: ps')))).
    cbn [xeval]. rewrite Hp, IH. unfold lsum. cbn [map fold_right]. reflexivity.
Qed.

(** A mode's kernels and coefficient against a term of the series. *)
Definition kker_ok (E : env ExtendedR) (u v : R) (k : mode_kernels) (t : term) : Prop :=
  mk_m k = tm t /\ mk_n k = tn t /\
  xeval E (mk_cos k) = Xreal (cos (ang t u v)) /\ xeval E (mk_sin k) = Xreal (sin (ang t u v)).
Definition kcoef_ok (E : env ExtendedR) (s : R) (c : coef3) (t : term) : Prop :=
  xeval E (t_val c) = Xreal (tc t s) /\ xeval E (t_ds c) = Xreal (tc1 t s) /\ xeval E (t_dss c) = Xreal (tc2 t s).
Definition kcoefl_ok (E : env ExtendedR) (s : R) (c : coef3) (t : term) : Prop :=
  xeval E (t_val c) = Xreal (tc t s) /\ xeval E (t_ds c) = Xreal (tc1 t s).

Definition kc_ok (E : env ExtendedR) (s u v : R) (kc : mode_kernels * coef3) (t : term) : Prop :=
  kker_ok E u v (fst kc) t /\ kcoef_ok E s (snd kc) t.
Definition kcl_ok (E : env ExtendedR) (s u v : R) (kc : mode_kernels * coef3) (t : term) : Prop :=
  kker_ok E u v (fst kc) t /\ kcoefl_ok E s (snd kc) t.

Lemma zip_ok {C : Type} (Pc : C -> term -> Prop) (kers : list mode_kernels) (cs : list C) (ts : list term)
    (P : mode_kernels -> term -> Prop) :
  Forall2 P kers ts -> Forall2 Pc cs ts ->
  Forall2 (fun kc t => P (fst kc) t /\ Pc (snd kc) t) (combine kers cs) ts.
Proof.
  intros H1. revert cs. induction H1 as [| k t ks ts' Hk Hks IH]; intros cs H2.
  - cbn. constructor.
  - inversion H2 as [| c t0 cs' ts0 Hc Hcs]; subst. cbn [combine]. constructor; [split; assumption | auto].
Qed.

Lemma fassemble_values (E : env ExtendedR) (even : bool) (kers : list mode_kernels) (coefs : list coef3)
    (ts : list term) (s u v : R) :
  Forall2 (kc_ok E s u v) (combine kers coefs) ts ->
  let p := fassemble kers coefs even in
  xeval E (fp_0 p) = Xreal (S0 even ts s u v) /\ xeval E (fp_s p) = Xreal (S_s even ts s u v) /\
  xeval E (fp_ss p) = Xreal (S_ss even ts s u v) /\ xeval E (fp_u p) = Xreal (S_u even ts s u v) /\
  xeval E (fp_v p) = Xreal (S_v even ts s u v) /\ xeval E (fp_su p) = Xreal (S_su even ts s u v) /\
  xeval E (fp_sv p) = Xreal (S_sv even ts s u v) /\ xeval E (fp_uu p) = Xreal (S_uu even ts s u v) /\
  xeval E (fp_uv p) = Xreal (S_uv even ts s u v) /\ xeval E (fp_vv p) = Xreal (S_vv even ts s u v).
Proof.
  intros H p. unfold p, fassemble. cbn [fp_0 fp_s fp_ss fp_u fp_v fp_su fp_sv fp_uu fp_uv fp_vv].
  unfold S0, S_s, S_ss, S_u, S_v, S_su, S_sv, S_uu, S_uv, S_vv.
  splits; apply esum_map_val; (eapply Forall2_impl; [| exact H]);
    intros [k c] t ((Hm & Hn & Hcos & Hsin) & (Hv & Hd & Hdd)); cbn [fst snd] in *; unfold zmul; cbn [xeval];
    unfold k0, k1, su, sv, ang in *; destruct even;
    rewrite ?Hcos, ?Hsin, ?Hv, ?Hd, ?Hdd, ?Hm, ?Hn; cbv [Xbind2 Xbind]; f_equal;
    rewrite ?opp_IZR, ?mult_IZR; ring.
Qed.

Lemma flambda_values (E : env ExtendedR) (even : bool) (kers : list mode_kernels) (coefs : list coef3)
    (ts : list term) (s u v : R) :
  Forall2 (kcl_ok E s u v) (combine kers coefs) ts ->
  let p := flambda_terms kers coefs even in
  xeval E (flp_u p) = Xreal (S_u even ts s u v) /\ xeval E (flp_v p) = Xreal (S_v even ts s u v) /\
  xeval E (flp_su p) = Xreal (S_su even ts s u v) /\ xeval E (flp_sv p) = Xreal (S_sv even ts s u v) /\
  xeval E (flp_uu p) = Xreal (S_uu even ts s u v) /\ xeval E (flp_uv p) = Xreal (S_uv even ts s u v) /\
  xeval E (flp_vv p) = Xreal (S_vv even ts s u v).
Proof.
  intros H p. unfold p, flambda_terms. cbn [flp_u flp_v flp_su flp_sv flp_uu flp_uv flp_vv].
  unfold S_u, S_v, S_su, S_sv, S_uu, S_uv, S_vv.
  splits; apply esum_map_val; (eapply Forall2_impl; [| exact H]);
    intros [k c] t ((Hm & Hn & Hcos & Hsin) & (Hv & Hd)); cbn [fst snd] in *; unfold zmul; cbn [xeval];
    unfold k0, k1, su, sv, ang in *; destruct even;
    rewrite ?Hcos, ?Hsin, ?Hv, ?Hd, ?Hm, ?Hn; cbv [Xbind2 Xbind]; f_equal;
    rewrite ?opp_IZR, ?mult_IZR; ring.
Qed.

(** * The terms of the reconstruction *)

Definition mkterm (f f1 f2 : nat -> Z -> R -> R) (jmn : nat * (Z * Z)) : term :=
  Term (fst (snd jmn)) (snd (snd jmn)) (f (fst jmn) (fst (snd jmn))) (f1 (fst jmn) (fst (snd jmn)))
       (f2 (fst jmn) (fst (snd jmn))).

Lemma kernels_terms (E : env ExtendedR) (u v : R) (f f1 f2 : nat -> Z -> R -> R) :
  forall (modes : list (Z * Z)) (kers : list mode_kernels) (k : nat),
  Forall2 (fun mn ker => mk_m ker = fst mn /\ mk_n ker = snd mn /\
     xeval E (mk_cos ker) = Xreal (cos (IZR (fst mn) * u - IZR (snd mn) * v)) /\
     xeval E (mk_sin ker) = Xreal (sin (IZR (fst mn) * u - IZR (snd mn) * v))) modes kers ->
  Forall2 (kker_ok E u v) kers (map (mkterm f f1 f2) (combine (seq k (length modes)) modes)).
Proof.
  intros modes kers k H. revert k. induction H as [| mn ker ms ks Hk Hs IH]; intros k; [constructor |].
  cbn [length seq combine map]. constructor; [| apply IH].
  destruct Hk as (Hm & Hn & Hc & Hs'). unfold kker_ok, mkterm, ang. cbn [tm tn fst snd].
  exact (conj Hm (conj Hn (conj Hc Hs'))).
Qed.

(** The values of a Hermite coefficient, from those of the Hermite scalars
    and of the two half-point coefficients. *)
Lemma herm_values (E : env ExtendedR) (b : builder) (hm : herm_scalars) (ca cb : coef2) (c : coef3)
    (t H iH h10 h11 g10 g11 m0 m1 ya da yb db : R) :
  sound E (b_binds b) -> herm_binds b hm ca cb c ->
  xeval E (hm_t hm) = Xreal t -> xeval E (hm_H hm) = Xreal H -> xeval E (hm_invH hm) = Xreal iH ->
  xeval E (hm_h10 hm) = Xreal h10 -> xeval E (hm_h11 hm) = Xreal h11 ->
  xeval E (hm_g10 hm) = Xreal g10 -> xeval E (hm_g11 hm) = Xreal g11 ->
  xeval E (hm_m0 hm) = Xreal m0 -> xeval E (hm_m1 hm) = Xreal m1 ->
  xeval E (c_val ca) = Xreal ya -> xeval E (c_ds ca) = Xreal da ->
  xeval E (c_val cb) = Xreal yb -> xeval E (c_ds cb) = Xreal db ->
  let sec := ((yb - ya) * iH)%R in let al := (da - sec)%R in let be := (db - sec)%R in
  xeval E (t_val c) = Xreal (ya + t * (yb - ya) + H * (h10 * al + h11 * be))%R /\
  xeval E (t_ds c) = Xreal (sec + (g10 * al + g11 * be))%R /\
  xeval E (t_dss c) = Xreal ((m0 * al + m1 * be) * iH)%R.
Proof.
  intros S (ndy & nsec & nal & nbe & nc & ncs & ncss & Ev & Ed & Edd & I1 & I2 & I3 & I4 & I5 & I6 & I7)
         Ht HH HiH H10 H11 G10 G11 M0 M1 Ya Da Yb Db sec al be.
  rewrite Ev, Ed, Edd. cbn [xeval].
  rewrite (S _ _ I5), (S _ _ I6), (S _ _ I7). cbn [xeval].
  rewrite (S _ _ I3), (S _ _ I4). cbn [xeval].
  rewrite (S _ _ I2). cbn [xeval]. rewrite (S _ _ I1). cbn [xeval].
  rewrite Ht, HH, HiH, H10, H11, G10, G11, M0, M1, Ya, Da, Yb, Db. cbv [Xbind2 Xbind].
  unfold al, be, sec. refine (conj _ (conj _ _)); f_equal; ring.
Qed.

Lemma herm_terms (E : env ExtendedR) (b : builder) (hm : herm_scalars) (sa H x : R)
    (ya da yb db : nat -> Z -> R) :
  sound E (b_binds b) -> (H <> 0)%R ->
  let t := ((x - sa) * (1 / H))%R in
  xeval E (hm_H hm) = Xreal H -> xeval E (hm_invH hm) = Xreal (1 / H) -> xeval E (hm_t hm) = Xreal t ->
  xeval E (hm_h10 hm) = Xreal (t * (t * t) - 2 * (t * t) + t) ->
  xeval E (hm_h11 hm) = Xreal (t * (t * t) - t * t) ->
  xeval E (hm_g10 hm) = Xreal (3 * (t * t) - 4 * t + 1) -> xeval E (hm_g11 hm) = Xreal (3 * (t * t) - 2 * t) ->
  xeval E (hm_m0 hm) = Xreal (6 * t - 4) -> xeval E (hm_m1 hm) = Xreal (6 * t - 2) ->
  forall (idx : list (nat * (Z * Z))) (cas cbs : list coef2) (cs : list coef3),
  Forall2 (fun jmn ca => xeval E (c_val ca) = Xreal (ya (fst jmn) (fst (snd jmn))) /\
                         xeval E (c_ds ca) = Xreal (da (fst jmn) (fst (snd jmn)))) idx cas ->
  Forall2 (fun jmn cb => xeval E (c_val cb) = Xreal (yb (fst jmn) (fst (snd jmn))) /\
                         xeval E (c_ds cb) = Xreal (db (fst jmn) (fst (snd jmn)))) idx cbs ->
  Forall2 (fun ab c => herm_binds b hm (fst ab) (snd ab) c) (combine cas cbs) cs ->
  Forall2 (kcoef_ok E x) cs
    (map (mkterm (fun j m => herm sa H (ya j m) (da j m) (yb j m) (db j m))
                 (fun j m => herm1 sa H (ya j m) (da j m) (yb j m) (db j m))
                 (fun j m => herm2 sa H (ya j m) (da j m) (yb j m) (db j m))) idx).
Proof.
  intros S HH t HH' HiH Ht H10 H11 G10 G11 M0 M1 idx cas cbs cs HA. revert cbs cs.
  induction HA as [| jmn ca idx' cas' Ha HAs IH]; intros cbs cs HB HC.
  - inversion HB; subst. cbn in HC. inversion HC. constructor.
  - inversion HB as [| jmn' cb idx'' cbs' Hb HBs]; subst. cbn [combine] in HC.
    inversion HC as [| ab c abs cs' Hc HCs]; subst. cbn [map]. constructor.
    + destruct Ha as [Ya Da]. destruct Hb as [Yb Db]. cbn [fst snd] in Hc.
      destruct (herm_values E b hm ca cb c t H (1 / H) _ _ _ _ _ _ _ _ _ _ S Hc Ht HH' HiH H10 H11 G10 G11 M0 M1
                  Ya Da Yb Db) as (V1 & V2 & V3).
      unfold kcoef_ok, mkterm. cbn [tc tc1 tc2 fst snd]. rewrite V1, V2, V3.
      unfold herm, herm1, herm2, h_al, h_be, h_t, h_sec, t.
      refine (conj _ (conj _ _)); f_equal; unfold Rdiv; ring.
    + exact (IH cbs' cs' HBs HCs).
Qed.

(** The values of a coefficient of lambda, by the parity of its mode. *)
Lemma rad_values (E : env ExtendedR) (b : builder) (rs : rad_scalars) (m : Z) (ya yb : expr) (c : coef3)
    (w ih sq isa isb i2s y1 y2 : R) :
  sound E (b_binds b) -> rad_binds b rs m ya yb c ->
  xeval E (rs_w rs) = Xreal w -> xeval E (rs_inv_h rs) = Xreal ih -> xeval E (rs_sqrt rs) = Xreal sq ->
  xeval E (rs_inv_sqrt_a rs) = Xreal isa -> xeval E (rs_inv_sqrt_b rs) = Xreal isb ->
  xeval E (rs_inv_2s rs) = Xreal i2s -> xeval E ya = Xreal y1 -> xeval E yb = Xreal y2 ->
  if Z.even m then
    xeval E (t_val c) = Xreal (y1 + w * (y2 - y1))%R /\ xeval E (t_ds c) = Xreal ((y2 - y1) * ih)%R
  else
    xeval E (t_val c) = Xreal (sq * (y1 * isa + w * (y2 * isb - y1 * isa)))%R /\
    xeval E (t_ds c) = Xreal (sq * ((y2 * isb - y1 * isa) * ih)
                              + sq * (y1 * isa + w * (y2 * isb - y1 * isa)) * i2s)%R.
Proof.
  intros S Hr Hw Hih Hsq Hisa Hisb Hi2s Y1 Y2. unfold rad_binds in Hr. destruct (Z.even m).
  - destruct Hr as (nd & nc & ncs & Ev & Ed & I1 & I2 & I3). rewrite Ev, Ed. cbn [xeval].
    rewrite (S _ _ I2), (S _ _ I3). cbn [xeval]. rewrite (S _ _ I1). cbn [xeval].
    rewrite Hw, Hih, Y1, Y2. cbv [Xbind2 Xbind]. split; f_equal; ring.
  - destruct Hr as (nqa & nqb & ndq & nq & nqs & nc & ncs & Ev & Ed & I1 & I2 & I3 & I4 & I5 & I6 & I7).
    rewrite Ev, Ed.
    repeat (cbn [xeval]; match goal with |- context [eget ?n E Xnan] =>
              match goal with I : In (n, ?e) _ |- _ => rewrite (S n e I) end end).
    cbn [xeval]. rewrite Hw, Hih, Hsq, Hisa, Hisb, Hi2s, Y1, Y2. cbv [Xbind2 Xbind]. split; f_equal; ring.
Qed.

(** The coefficient of lambda of mode j at the radius s, from its values ya,
    yb at the half points sa and sa + 1/ih. *)
Definition lcoef (shm shp : R) (y : nat -> nat -> R) (j : nat) (m : Z) : R -> R :=
  if Z.even m then lin shm (1 / (shp - shm)) (y 0%nat j) (y 1%nat j)
  else sqlin shm (1 / (shp - shm)) (y 0%nat j) (y 1%nat j) (1 / sqrt shm) (1 / sqrt shp).
Definition lcoef1 (shm shp : R) (y : nat -> nat -> R) (j : nat) (m : Z) : R -> R :=
  if Z.even m then lin1 (1 / (shp - shm)) (y 0%nat j) (y 1%nat j)
  else sqlin1 shm (1 / (shp - shm)) (y 0%nat j) (y 1%nat j) (1 / sqrt shm) (1 / sqrt shp).

Lemma rad_terms (exps : list Z) (E : env ExtendedR) (b : builder) (rs : rad_scalars) (shm shp x : R)
    (y : nat -> nat -> R) (base K ra rb : nat) :
  sound E (b_binds b) ->
  xeval E (rs_w rs) = Xreal ((x - shm) * (1 / (shp - shm))) -> xeval E (rs_inv_h rs) = Xreal (1 / (shp - shm)) ->
  xeval E (rs_sqrt rs) = Xreal (sqrt x) -> xeval E (rs_inv_sqrt_a rs) = Xreal (1 / sqrt shm) ->
  xeval E (rs_inv_sqrt_b rs) = Xreal (1 / sqrt shp) -> xeval E (rs_inv_2s rs) = Xreal (1 / (2 * x)) ->
  forall (modes : list (Z * Z)) (k : nat) (cs : list coef3),
  (forall j, (k <= j)%nat -> (j < k + length modes)%nat ->
     xeval E (slot_node exps base K ra j) = Xreal (y 0%nat j) /\ xeval E (slot_node exps base K rb j) = Xreal (y 1%nat j)) ->
  Forall2 (fun jmn c => rad_binds b rs (fst (snd jmn)) (slot_node exps base K ra (fst jmn))
                                  (slot_node exps base K rb (fst jmn)) c)
          (combine (seq k (length modes)) modes) cs ->
  Forall2 (kcoefl_ok E x) cs
    (map (mkterm (lcoef shm shp y) (lcoef1 shm shp y) (fun _ _ _ => 0%R)) (combine (seq k (length modes)) modes)).
Proof.
  intros S Hw Hih Hsq Hisa Hisb Hi2s modes. induction modes as [| mn tl IH]; intros k cs Hy HF.
  - cbn in HF. inversion HF. constructor.
  - cbn [length seq combine map] in HF |- *. inversion HF as [| jmn c jmns cs' Hc HCs]; subst. constructor.
    + destruct (Hy k ltac:(lia) ltac:(cbn [length]; lia)) as [Y1 Y2]. cbn [fst snd] in Hc.
      pose proof (rad_values E b rs (fst mn) _ _ c _ _ _ _ _ _ _ _ S Hc Hw Hih Hsq Hisa Hisb Hi2s Y1 Y2) as HV.
      unfold kcoefl_ok, mkterm. cbn [tc tc1 fst snd]. unfold lcoef, lcoef1, sqlin1, sqlin, lin, lin1.
      destruct (Z.even (fst mn)); destruct HV as [V1 V2]; rewrite V1, V2; split; f_equal; unfold Rdiv; ring.
    + apply IH; [intros j Hj1 Hj2; apply Hy; cbn [length]; lia | exact HCs].
Qed.

Lemma forall2_combine_seq {A B : Type} (P : nat * A -> B -> Prop) (Q : nat * A -> B -> Prop) :
  forall (l : list (nat * A)) (cs : list B), (forall x c, In x l -> P x c -> Q x c) -> Forall2 P l cs -> Forall2 Q l cs.
Proof. intros l cs H F. induction F; constructor; [apply H; [left; reflexivity | assumption] |
  apply IHF; intros; apply H; [right |]; assumption]. Qed.

(** * The reconstruction *)

Section Reconstruction.
Variables (sa sj sb shm shp : R).

Definition hya (y : nat -> nat -> R) (j : nat) (m : Z) : R := hval m sa sj shm (y 0%nat j) (y 1%nat j).
Definition hda (y : nat -> nat -> R) (j : nat) (m : Z) : R := hslope m sa sj shm (y 0%nat j) (y 1%nat j).
Definition hyb (y : nat -> nat -> R) (j : nat) (m : Z) : R := hval m sj sb shp (y 1%nat j) (y 2%nat j).
Definition hdb (y : nat -> nat -> R) (j : nat) (m : Z) : R := hslope m sj sb shp (y 1%nat j) (y 2%nat j).

(** The terms of R or Z: each mode's coefficient is the cubic Hermite between
    the half points through VMEC's half-grid values and slopes. *)
Definition rterms (y : nat -> nat -> R) (modes : list (Z * Z)) : list term :=
  map (mkterm (fun j m => herm shm (shp - shm) (hya y j m) (hda y j m) (hyb y j m) (hdb y j m))
              (fun j m => herm1 shm (shp - shm) (hya y j m) (hda y j m) (hyb y j m) (hdb y j m))
              (fun j m => herm2 shm (shp - shm) (hya y j m) (hda y j m) (hyb y j m) (hdb y j m)))
      (combine (seq 0 (length modes)) modes).

(** The terms of lambda. *)
Definition lterms (y : nat -> nat -> R) (modes : list (Z * Z)) : list term :=
  map (mkterm (lcoef shm shp y) (lcoef1 shm shp y) (fun _ _ _ => 0%R)) (combine (seq 0 (length modes)) modes).

(** iota, linear between the half points. *)
Definition iotaf (im ip : R) (s : R) : R := (im + (s - shm) * (1 / (shp - shm)) * (ip - im))%R.

End Reconstruction.

(** mu0 as Physics.v writes it. *)
Definition mu0r : R := (IZR 4 * PI / IZR 10000000)%R.

(** * The continuum residual evaluates the force formulas at the jet *)

Theorem fp_residual (exps : list Z) (prof : pprofile) (modes : list (Z * Z)) (b0 : builder) (env : env ExtendedR)
    (wm : nat) (bf : builder) (rr : residual3)
    (sa sj sb shm shp s0 u0 v0 phip im ip pp : R) (yR yZ yL : nat -> nat -> R) :
  let K := length modes in
  full_point_b exps b0 false modes K prof RRadial = (bf, rr) ->
  well_formed wm (r_binds rr) = true ->
  let E := xextend env (r_binds rr) in
  xeval E (slot_s_a exps) = Xreal sa -> xeval E (slot_s_j exps) = Xreal sj -> xeval E (slot_s_b exps) = Xreal sb ->
  xeval E (slot_s_hm exps) = Xreal shm -> xeval E (slot_s_hp exps) = Xreal shp ->
  xeval E (vS exps) = Xreal s0 -> xeval E (vU exps) = Xreal u0 -> xeval E (vV exps) = Xreal v0 ->
  xeval E (vPhip exps) = Xreal phip ->
  xeval E (slot_iota_m exps) = Xreal im -> xeval E (slot_iota_p exps) = Xreal ip ->
  xeval E (pprime exps prof) = Xreal pp ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_R K) K row j) = Xreal (yR row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Z K) K row j) = Xreal (yZ row j)) ->
  (forall row j, (row < 2)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_L K) K row j) = Xreal (yL row j)) ->
  (0 < sa)%R -> (0 < sj)%R -> (0 < sb)%R -> (0 < shm)%R -> (0 < shp)%R -> (0 < s0)%R ->
  (sj - sa <> 0)%R -> (sb - sj <> 0)%R -> (shp - shm <> 0)%R ->
  let tR := rterms sa sj sb shm shp yR modes in
  let tZ := rterms sa sj sb shm shp yZ modes in
  let tL := lterms shm shp yL modes in
  sqrtg (S0 true tR) (S_s true tR) (S_u true tR) (S_s false tZ) (S_u false tZ) s0 u0 v0 <> 0%R ->
  let J := jet0 (S0 true tR) (S_s true tR) (S_u true tR) (S_v true tR) (S_s false tZ) (S_u false tZ)
                (S_v false tZ) (S_u false tL) (S_v false tL) (iotaf shm shp im ip) phip mu0r s0 u0 v0
                (S_ss true tR s0 u0 v0) (S_su true tR s0 u0 v0) (S_sv true tR s0 u0 v0)
                (S_uu true tR s0 u0 v0) (S_uv true tR s0 u0 v0) (S_vv true tR s0 u0 v0)
                (S_ss false tZ s0 u0 v0) (S_su false tZ s0 u0 v0) (S_sv false tZ s0 u0 v0)
                (S_uu false tZ s0 u0 v0) (S_uv false tZ s0 u0 v0) (S_vv false tZ s0 u0 v0)
                (S_su false tL s0 u0 v0) (S_sv false tL s0 u0 v0) (S_uu false tL s0 u0 v0)
                (S_uv false tL s0 u0 v0) (S_vv false tL s0 u0 v0) ((ip - im) * (1 / (shp - shm)))%R pp in
  xeval E (r_s rr) = Xreal (cres_s J) /\ xeval E (r_u rr) = Xreal (cres_u J) /\
  xeval E (r_v rr) = Xreal (cres_v J).
Proof.
  intros K HFP Hwf E Hsa Hsj Hsb Hshm Hshp Hs Hu Hv Hph Him Hip Hpp HyR HyZ HyL Pa Pj Pb Phm Php Ps Daj Djb Dh
         tR tZ tL Hsg J.
  revert HFP. unfold full_point_b. cbv beta iota zeta delta [is_axis].
  repeat step.
  repeat match goal with Q : (match _ with _ => _ end) = _ |- _ => stepH Q end.
  repeat match goal with Q : (_, _) = (_, _) |- _ => injection Q as <- <- end.
  intros HFP. injection HFP as <- <-. cbn [r_binds r_s r_u r_v fst snd] in *.
  match type of Hwf with well_formed _ (bindings_of ?bl) = true =>
    assert (S : sound E (b_binds bl)) by exact (sound_final env wm bl Hwf) end.
  clearbody E. peel.
  (* every stage's bindings hold their values *)
  repeat match goal with
  | S : sound E (b_binds ?b'), Q : flambda_partials_b ?b ?p = (?b', ?q) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (flambda_ok E b p b' q Q)) S) end
  | S : sound E (b_binds ?b'), Q : fpartials_b ?b ?p = (?b', ?q) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (fpartials_ok E b p b' q Q)) S) end
  | S : sound E (b_binds ?b'), Q : radcoefs_b _ ?b _ _ _ _ _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (radcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : hermcoefs_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (hermcoefs_spec _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : rad_scalars_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (rad_scalars_ok E _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : herm_scalars_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (herm_scalars_ok E _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : kernels_b _ ?b _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (kernels_spec _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : halfcoefs_b _ ?b _ _ _ _ _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (halfcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q)) S) end
  | S : sound E (b_binds ?b'), Q : half_scalars_b ?b _ _ _ = (?b', _) |- _ =>
      lazymatch goal with _ : sound E (b_binds b) |- _ => fail | _ =>
        pose proof (sound_extends E b b' (proj1 (half_scalars_ok E _ _ _ _ _ _ Q)) S) end
  end.
  (* the half-point scalars and coefficients *)
  match goal with
  | Q : half_scalars_b _ (slot_s_a exps) (slot_s_j exps) (slot_s_hm exps) = (?b', _),
    S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (half_scalars_ok E _ _ _ _ _ _ Q)) S sa sj shm Hsa Hsj Hshm Pa Pj Phm Daj)
        as (Hm1 & Hm2 & Hm3 & Hm4 & Hm5 & Hm6)
  end.
  match goal with
  | Q : half_scalars_b _ (slot_s_j exps) (slot_s_b exps) (slot_s_hp exps) = (?b', _),
    S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (half_scalars_ok E _ _ _ _ _ _ Q)) S sj sb shp Hsj Hsb Hshp Pj Pb Php Djb)
        as (Hp1 & Hp2 & Hp3 & Hp4 & Hp5 & Hp6)
  end.
  assert (HyR01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_R K) K 0 j) = Xreal (yR 0%nat j) /\
    xeval E (slot_node exps (base_R K) K 1 j) = Xreal (yR 1%nat j)) by (intros j _ Hj; split; apply HyR; unfold K; lia).
  assert (HyR12 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_R K) K 1 j) = Xreal (yR 1%nat j) /\
    xeval E (slot_node exps (base_R K) K 2 j) = Xreal (yR 2%nat j)) by (intros j _ Hj; split; apply HyR; unfold K; lia).
  assert (HyZ01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_Z K) K 0 j) = Xreal (yZ 0%nat j) /\
    xeval E (slot_node exps (base_Z K) K 1 j) = Xreal (yZ 1%nat j)) by (intros j _ Hj; split; apply HyZ; unfold K; lia).
  assert (HyZ12 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_Z K) K 1 j) = Xreal (yZ 1%nat j) /\
    xeval E (slot_node exps (base_Z K) K 2 j) = Xreal (yZ 2%nat j)) by (intros j _ Hj; split; apply HyZ; unfold K; lia).
  assert (HyL01 : forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
    xeval E (slot_node exps (base_L K) K 0 j) = Xreal (yL 0%nat j) /\
    xeval E (slot_node exps (base_L K) K 1 j) = Xreal (yL 1%nat j)) by (intros j _ Hj; split; apply HyL; unfold K; lia).
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_R K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_R K) K 0 1 sa sj shm (yR 0%nat) (yR 1%nat)
                    Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 modes 0 _ b' cs Q HyR01 S) as CRm
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_R K) K 1 2 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_R K) K 1 2 sj sb shp (yR 1%nat) (yR 2%nat)
                    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 modes 0 _ b' cs Q HyR12 S) as CRp
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Z K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Z K) K 0 1 sa sj shm (yZ 0%nat) (yZ 1%nat)
                    Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 modes 0 _ b' cs Q HyZ01 S) as CZm
  end.
  match goal with
  | Q : halfcoefs_b exps _ ?hs (base_Z K) K 1 2 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (halfcoefs_values exps E hs (base_Z K) K 1 2 sj sb shp (yZ 1%nat) (yZ 2%nat)
                    Hp1 Hp2 Hp3 Hp4 Hp5 Hp6 modes 0 _ b' cs Q HyZ12 S) as CZp
  end.
  (* the kernels and the radial scalars *)
  match goal with
  | Q : kernels_b exps _ modes = (?b', ?kers), S : sound E (b_binds ?b') |- _ =>
      pose proof (kernels_values exps E u0 v0 modes _ b' kers Q S Hu Hv) as KV
  end.
  match goal with
  | Q : herm_scalars_b _ (slot_s_hm exps) (slot_s_hp exps) (vS exps) = (?b', _), S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (herm_scalars_ok E _ _ _ _ _ _ Q)) S shm shp s0 Hshm Hshp Hs Dh)
        as (HH1 & HH2 & HH3 & HH4 & HH5 & HH6 & HH7 & HH8 & HH9)
  end.
  match goal with
  | Q : rad_scalars_b _ (slot_s_hm exps) (slot_s_hp exps) (vS exps) = (?b', _), S : sound E (b_binds ?b') |- _ =>
      destruct ((proj2 (rad_scalars_ok E _ _ _ _ _ _ Q)) S shm shp s0 Hshm Hshp Hs Phm Php Ps Dh)
        as (RS1 & RS2 & RS3 & RS4 & RS5 & RS6)
  end.
  (* the coefficients at the radius *)
  match goal with
  | Q1 : halfcoefs_b exps _ _ (base_R K) K 0 1 modes 0 = (_, ?ca),
    Q2 : halfcoefs_b exps _ _ (base_R K) K 1 2 modes 0 = (_, ?cb),
    A : hermcoefs_b _ ?hm ?ca ?cb = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (herm_terms E b' hm shm (shp - shm) s0 (hya sa sj shm yR) (hda sa sj shm yR)
                    (hyb sj sb shp yR) (hdb sj sb shp yR) S Dh HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9
                    _ ca cb cs CRm CRp (proj2 (hermcoefs_spec _ _ _ _ _ _ A))) as TR
  end.
  match goal with
  | Q1 : halfcoefs_b exps _ _ (base_Z K) K 0 1 modes 0 = (_, ?ca),
    Q2 : halfcoefs_b exps _ _ (base_Z K) K 1 2 modes 0 = (_, ?cb),
    A : hermcoefs_b _ ?hm ?ca ?cb = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (herm_terms E b' hm shm (shp - shm) s0 (hya sa sj shm yZ) (hda sa sj shm yZ)
                    (hyb sj sb shp yZ) (hdb sj sb shp yZ) S Dh HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9
                    _ ca cb cs CZm CZp (proj2 (hermcoefs_spec _ _ _ _ _ _ A))) as TZ
  end.
  match goal with
  | Q : radcoefs_b exps _ ?rl (base_L K) K 0 1 modes 0 = (?b', ?cs), S : sound E (b_binds ?b') |- _ =>
      pose proof (rad_terms exps E b' rl shm shp s0 yL (base_L K) K 0 1 S RS1 RS2 RS3 RS4 RS5 RS6 modes 0 cs
                    HyL01 (proj2 (radcoefs_spec _ _ _ _ _ _ _ _ _ _ _ Q))) as TL
  end.
  (* the series and their derivatives at the point *)
  match goal with
  | Q : fpartials_b _ (fassemble ?kers ?cs true) = (?b', ?q), S : sound E (b_binds ?b') |- _ =>
      pose proof (proj2 (fpartials_ok E _ _ _ _ Q) S) as PR;
      pose proof (fassemble_values E true kers cs tR s0 u0 v0
                    (zip_ok (kcoef_ok E s0) kers cs tR (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TR))
        as FR
  end.
  match goal with
  | Q : fpartials_b _ (fassemble ?kers ?cs false) = (?b', ?q), S : sound E (b_binds ?b') |- _ =>
      pose proof (proj2 (fpartials_ok E _ _ _ _ Q) S) as PZ;
      pose proof (fassemble_values E false kers cs tZ s0 u0 v0
                    (zip_ok (kcoef_ok E s0) kers cs tZ (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TZ))
        as FZ
  end.
  match goal with
  | Q : flambda_partials_b _ (flambda_terms ?kers ?cs false) = (?b', ?q), S : sound E (b_binds ?b') |- _ =>
      pose proof (proj2 (flambda_ok E _ _ _ _ Q) S) as PL;
      pose proof (flambda_values E false kers cs tL s0 u0 v0
                    (zip_ok (kcoefl_ok E s0) kers cs tL (kker_ok E u0 v0) (kernels_terms E u0 v0 _ _ _ modes kers 0 KV) TL))
        as FL
  end.
  cbv zeta in FR, FZ, FL.
  destruct PR as (PR1 & PR2 & PR3 & PR4 & PR5 & PR6 & PR7 & PR8 & PR9 & PR10).
  destruct PZ as (PZ1 & PZ2 & PZ3 & PZ4 & PZ5 & PZ6 & PZ7 & PZ8 & PZ9 & PZ10).
  destruct PL as (PL1 & PL2 & PL3 & PL4 & PL5 & PL6 & PL7).
  destruct FR as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & FR8 & FR9 & FR10).
  destruct FZ as (FZ1 & FZ2 & FZ3 & FZ4 & FZ5 & FZ6 & FZ7 & FZ8 & FZ9 & FZ10).
  destruct FL as (FL1 & FL2 & FL3 & FL4 & FL5 & FL6 & FL7).
  (* each series slot's value directly, so that no assembled sum reaches the goal *)
  pose proof (eq_trans PR1 FR1) as W1. pose proof (eq_trans PR2 FR2) as W2.
  pose proof (eq_trans PR3 FR3) as W3. pose proof (eq_trans PR4 FR4) as W4.
  pose proof (eq_trans PR5 FR5) as W5. pose proof (eq_trans PR6 FR6) as W6.
  pose proof (eq_trans PR7 FR7) as W7. pose proof (eq_trans PR8 FR8) as W8.
  pose proof (eq_trans PR9 FR9) as W9. pose proof (eq_trans PR10 FR10) as W10.
  pose proof (eq_trans PZ1 FZ1) as W11. pose proof (eq_trans PZ2 FZ2) as W12.
  pose proof (eq_trans PZ3 FZ3) as W13. pose proof (eq_trans PZ4 FZ4) as W14.
  pose proof (eq_trans PZ5 FZ5) as W15. pose proof (eq_trans PZ6 FZ6) as W16.
  pose proof (eq_trans PZ7 FZ7) as W17. pose proof (eq_trans PZ8 FZ8) as W18.
  pose proof (eq_trans PZ9 FZ9) as W19. pose proof (eq_trans PZ10 FZ10) as W20.
  pose proof (eq_trans PL1 FL1) as W21. pose proof (eq_trans PL2 FL2) as W22.
  pose proof (eq_trans PL3 FL3) as W23. pose proof (eq_trans PL4 FL4) as W24.
  pose proof (eq_trans PL5 FL5) as W25. pose proof (eq_trans PL6 FL6) as W26.
  pose proof (eq_trans PL7 FL7) as W27.
  clear PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PZ1 PZ2 PZ3 PZ4 PZ5 PZ6 PZ7 PZ8 PZ9 PZ10
        PL1 PL2 PL3 PL4 PL5 PL6 PL7 FR1 FR2 FR3 FR4 FR5 FR6 FR7 FR8 FR9 FR10
        FZ1 FZ2 FZ3 FZ4 FZ5 FZ6 FZ7 FZ8 FZ9 FZ10 FL1 FL2 FL3 FL4 FL5 FL6 FL7.
  (* the formula stage *)
  unfold sqrtg in Hsg. cbv beta in Hsg.
  unfold Physics.e1, Physics.esq, Physics.zmul, Physics.mu0, Physics.e4, Physics.r_u_e, Physics.r_v_e in *.
  splits; xcalc; xclose;
    unfold J, jet0, iotaf, mu0r, cres_s, cres_u, cres_v, f_mu0Js, f_B_u_s, f_B_v_s, f_B_s_u, f_B_s_v, f_B_u_v,
      f_B_v_u, f_dcov, f_guu, f_guv, f_gvv, f_gsu, f_gsv, f_guu_s, f_guv_s, f_gvv_s, f_gsu_u, f_gsu_v, f_gsv_u,
      f_gsv_v, f_guu_v, f_guv_u, f_guv_v, f_gvv_u, f_Bu, f_Bv, f_Bu_s, f_Bv_s, f_Bu_u, f_Bv_u, f_Bu_v, f_Bv_v,
      f_dB, f_g2, f_bu_num, f_bv_num, f_g_s, f_g_u, f_g_v, f_tau_s, f_tau_u, f_tau_v, f_sqrtg, f_tau;
    cbn [jR jRs jRu jRv jRss jRsu jRsv jRuu jRuv jRvv jZs jZu jZv jZss jZsu jZsv jZuu jZuv jZvv
         jLu jLv jLsu jLsv jLuu jLuv jLvv jiota jiotap jphip jmu0pp];
    reflexivity.
Qed.

(** * The reconstruction's derivatives *)

Lemma rterms_d1 (sa sj sb shm shp : R) (y : nat -> nat -> R) (modes : list (Z * Z)) (x : R) :
  (shp - shm <> 0)%R -> forall t, In t (rterms sa sj sb shm shp y modes) -> is_derive (tc t) x (tc1 t x).
Proof.
  intros Dh t Ht. unfold rterms in Ht. apply in_map_iff in Ht. destruct Ht as [jmn [<- _]].
  unfold mkterm. cbn [tc tc1]. apply herm_d1. exact Dh.
Qed.

Lemma rterms_d2 (sa sj sb shm shp : R) (y : nat -> nat -> R) (modes : list (Z * Z)) (x : R) :
  (shp - shm <> 0)%R -> forall t, In t (rterms sa sj sb shm shp y modes) -> is_derive (tc1 t) x (tc2 t x).
Proof.
  intros Dh t Ht. unfold rterms in Ht. apply in_map_iff in Ht. destruct Ht as [jmn [<- _]].
  unfold mkterm. cbn [tc1 tc2]. apply herm_d2. exact Dh.
Qed.

Lemma lterms_d1 (shm shp : R) (y : nat -> nat -> R) (modes : list (Z * Z)) (x : R) :
  (0 < x)%R -> forall t, In t (lterms shm shp y modes) -> is_derive (tc t) x (tc1 t x).
Proof.
  intros Px t Ht. unfold lterms in Ht. apply in_map_iff in Ht. destruct Ht as [jmn [<- _]].
  unfold mkterm, lcoef, lcoef1. cbn [tc tc1]. destruct (Z.even (fst (snd jmn))).
  - apply lin_d1.
  - apply sqlin_d1. exact Px.
Qed.

Lemma iotaf_d (shm shp im ip x : R) :
  is_derive (iotaf shm shp im ip) x ((ip - im) * (1 / (shp - shm)))%R.
Proof. unfold iotaf. auto_derive; [exact I | ring]. Qed.

(** * The continuum residual is mu0 (J x B - grad p) *)

Theorem continuum_force (exps : list Z) (prof : pprofile) (modes : list (Z * Z)) (env : env ExtendedR) (wm : nat)
    (sa sj sb shm shp s0 u0 v0 phip im ip pp : R) (yR yZ yL : nat -> nat -> R) (p : R -> R)
    (G1 G2 G3 P : R * R * R -> R) (a11 a12 a13 a21 a22 a23 a31 a32 a33 q1 q2 q3 : R) :
  let K := length modes in
  let r := residual exps (PConfig false prof RRadial) modes in
  well_formed wm (r_binds r) = true ->
  let E := xextend env (r_binds r) in
  xeval E (slot_s_a exps) = Xreal sa -> xeval E (slot_s_j exps) = Xreal sj -> xeval E (slot_s_b exps) = Xreal sb ->
  xeval E (slot_s_hm exps) = Xreal shm -> xeval E (slot_s_hp exps) = Xreal shp ->
  xeval E (vS exps) = Xreal s0 -> xeval E (vU exps) = Xreal u0 -> xeval E (vV exps) = Xreal v0 ->
  xeval E (vPhip exps) = Xreal phip ->
  xeval E (slot_iota_m exps) = Xreal im -> xeval E (slot_iota_p exps) = Xreal ip ->
  xeval E (pprime exps prof) = Xreal pp ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_R K) K row j) = Xreal (yR row j)) ->
  (forall row j, (row < 3)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_Z K) K row j) = Xreal (yZ row j)) ->
  (forall row j, (row < 2)%nat -> (j < K)%nat -> xeval E (slot_node exps (base_L K) K row j) = Xreal (yL row j)) ->
  (0 < sa)%R -> (0 < sj)%R -> (0 < sb)%R -> (0 < shm)%R -> (0 < shp)%R -> (0 < s0)%R ->
  (sj - sa <> 0)%R -> (sb - sj <> 0)%R -> (shp - shm <> 0)%R ->
  let tR := rterms sa sj sb shm shp yR modes in
  let tZ := rterms sa sj sb shm shp yZ modes in
  let tL := lterms shm shp yL modes in
  let FR := Series.S0 true tR in let FRs := S_s true tR in let FRu := S_u true tR in let FRv := S_v true tR in
  let FZ := Series.S0 false tZ in let FZs := S_s false tZ in let FZu := S_u false tZ in
  let FZv := S_v false tZ in let FLu := S_u false tL in let FLv := S_v false tL in
  let iota := iotaf shm shp im ip in
  sqrtg FR FRs FRu FZs FZu s0 u0 v0 <> 0%R ->
  is_derive p s0 pp ->
  filterdiff G1 (locally (emb FR FZ s0 u0 v0)) (lin3 a11 a12 a13) ->
  filterdiff G2 (locally (emb FR FZ s0 u0 v0)) (lin3 a21 a22 a23) ->
  filterdiff G3 (locally (emb FR FZ s0 u0 v0)) (lin3 a31 a32 a33) ->
  filterdiff P (locally (emb FR FZ s0 u0 v0)) (lin3 q1 q2 q3) ->
  represents G1 G2 G3 P (fun t => emb FR FZ t u0 v0)
    (fun t => Bc1 FR FRs FRu FRv FZs FZu FLu FLv iota phip t u0 v0)
    (fun t => Bc2 FR FRs FRu FRv FZs FZu FLu FLv iota phip t u0 v0)
    (fun t => Bc3 FR FRs FRu FZs FZu FZv FLu FLv iota phip t u0 v0) p s0 ->
  represents G1 G2 G3 P (fun t => emb FR FZ s0 t v0)
    (fun t => Bc1 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 t v0)
    (fun t => Bc2 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 t v0)
    (fun t => Bc3 FR FRs FRu FZs FZu FZv FLu FLv iota phip s0 t v0) (fun _ => p s0) u0 ->
  represents G1 G2 G3 P (fun t => emb FR FZ s0 u0 t)
    (fun t => Bc1 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 u0 t)
    (fun t => Bc2 FR FRs FRu FRv FZs FZu FLu FLv iota phip s0 u0 t)
    (fun t => Bc3 FR FRs FRu FZs FZu FZv FLu FLv iota phip s0 u0 t) (fun _ => p s0) v0 ->
  let G01 := G1 (emb FR FZ s0 u0 v0) in let G02 := G2 (emb FR FZ s0 u0 v0) in
  let G03 := G3 (emb FR FZ s0 u0 v0) in
  let w1 := (a32 - a23)%R in let w2 := (a13 - a31)%R in let w3 := (a21 - a12)%R in
  let F1 := ((w2 * G03 - w3 * G02) - mu0r * q1)%R in
  let F2 := ((w3 * G01 - w1 * G03) - mu0r * q2)%R in
  let F3 := ((w1 * G02 - w2 * G01) - mu0r * q3)%R in
  let c := cos v0 in let sn := sin v0 in
  xeval E (r_s r) = Xreal (dot3 F1 F2 F3 (FRs s0 u0 v0 * c) (FRs s0 u0 v0 * sn) (FZs s0 u0 v0))%R /\
  xeval E (r_u r) = Xreal (dot3 F1 F2 F3 (FRu s0 u0 v0 * c) (FRu s0 u0 v0 * sn) (FZu s0 u0 v0))%R /\
  xeval E (r_v r) = Xreal (dot3 F1 F2 F3 (FRv s0 u0 v0 * c - FR s0 u0 v0 * sn) (FRv s0 u0 v0 * sn + FR s0 u0 v0 * c)
                             (FZv s0 u0 v0))%R.
Proof.
  intros K r Hwf E Hsa Hsj Hsb Hshm Hshp Hs Hu Hv Hph Him Hip Hpp HyR HyZ HyL Pa Pj Pb Phm Php Ps Daj Djb Dh
         tR tZ tL FR FRs FRu FRv FZ FZs FZu FZv FLu FLv iota Hsg Hp HG1 HG2 HG3 HP Hsl Hul Hvl
         G01 G02 G03 w1 w2 w3 F1 F2 F3 c sn.
  set (FP := full_point_b exps (Builder (base_scratch_of false RRadial K) []) false modes K prof RRadial).
  assert (HFP : FP = (fst FP, r)) by (change r with (snd FP); apply surjective_pairing).
  pose proof (fp_residual exps prof modes (Builder (base_scratch_of false RRadial K) []) env wm (fst FP) r
                sa sj sb shm shp s0 u0 v0 phip im ip pp yR yZ yL HFP Hwf
                Hsa Hsj Hsb Hshm Hshp Hs Hu Hv Hph Him Hip Hpp HyR HyZ HyL Pa Pj Pb Phm Php Ps Daj Djb Dh Hsg)
    as (Rs & Ru & Rv).
  (* the reconstruction's derivatives along the three coordinate lines *)
  assert (C1R := rterms_d1 sa sj sb shm shp yR modes s0 Dh).
  assert (C2R := rterms_d2 sa sj sb shm shp yR modes s0 Dh).
  assert (C1Z := rterms_d1 sa sj sb shm shp yZ modes s0 Dh).
  assert (C2Z := rterms_d2 sa sj sb shm shp yZ modes s0 Dh).
  assert (C1L := lterms_d1 shm shp yL modes s0 Ps).
  destruct (table_s true tR s0 C1R u0 v0) as (TRs1 & TRs2 & TRs3).
  destruct (table_s false tZ s0 C1Z u0 v0) as (TZs1 & TZs2 & TZs3).
  destruct (table_s false tL s0 C1L u0 v0) as (TLs1 & TLs2 & TLs3).
  pose proof (table_ss true tR s0 C2R u0 v0) as TRss.
  pose proof (table_ss false tZ s0 C2Z u0 v0) as TZss.
  destruct (table_u true tR s0 u0 v0) as (TRu1 & TRu2 & TRu3 & TRu4).
  destruct (table_u false tZ s0 u0 v0) as (TZu1 & TZu2 & TZu3 & TZu4).
  destruct (table_u false tL s0 u0 v0) as (TLu1 & TLu2 & TLu3 & TLu4).
  destruct (table_v true tR s0 u0 v0) as (TRv1 & TRv2 & TRv3 & TRv4).
  destruct (table_v false tZ s0 u0 v0) as (TZv1 & TZv2 & TZv3 & TZv4).
  destruct (table_v false tL s0 u0 v0) as (TLv1 & TLv2 & TLv3 & TLv4).
  destruct (force_law FR FZ FRs FRu FRv FZs FZu FZv FLu FLv iota p phip mu0r s0 u0 v0
              (S_ss true tR s0 u0 v0) (S_su true tR s0 u0 v0) (S_sv true tR s0 u0 v0)
              (S_uu true tR s0 u0 v0) (S_uv true tR s0 u0 v0) (S_vv true tR s0 u0 v0)
              (S_ss false tZ s0 u0 v0) (S_su false tZ s0 u0 v0) (S_sv false tZ s0 u0 v0)
              (S_uu false tZ s0 u0 v0) (S_uv false tZ s0 u0 v0) (S_vv false tZ s0 u0 v0)
              (S_su false tL s0 u0 v0) (S_sv false tL s0 u0 v0) (S_uu false tL s0 u0 v0)
              (S_uv false tL s0 u0 v0) (S_vv false tL s0 u0 v0) ((ip - im) * (1 / (shp - shm)))%R pp
              (conj TRs1 (conj TRu1 TRv1)) (conj TRss (conj TRu2 TRv2)) (conj TRs2 (conj TRu3 TRv3))
              (conj TRs3 (conj TRu4 TRv4))
              (conj TZs1 (conj TZu1 TZv1)) (conj TZss (conj TZu2 TZv2)) (conj TZs2 (conj TZu3 TZv3))
              (conj TZs3 (conj TZu4 TZv4))
              (conj TLs2 (conj TLu3 TLv3)) (conj TLs3 (conj TLu4 TLv4))
              (iotaf_d shm shp im ip s0) Hp Hsg G1 G2 G3 P a11 a12 a13 a21 a22 a23 a31 a32 a33 q1 q2 q3
              HG1 HG2 HG3 HP Hsl Hul Hvl) as (Fs & Fu & Fv).
  refine (conj _ (conj _ _)).
  - etransitivity; [exact Rs |]. f_equal. symmetry. exact Fs.
  - etransitivity; [exact Ru |]. f_equal. symmetry. exact Fu.
  - etransitivity; [exact Rv |]. f_equal. symmetry. exact Fv.
Qed.

(** * The node residual *)

(** The node residual reads the field at the two half points around a node:
    its angular components are those of the outer half point, and its radial
    component combines the half points by VMEC's averages and differences.
    At a half point the reconstruction is VMEC's own: each coefficient is its
    half-grid value, with its half-grid slope for the radial derivative. *)

(** The covariant components B_u and B_v of the field of a jet, and the
    radial component of the node residual from the jets of the two half
    points, with ih the reciprocal of their spacing and mpp mu0 dp/ds. *)
Definition Bcov_u (j : jet) : R := (f_guu j * f_Bu j + f_guv j * f_Bv j)%R.
Definition Bcov_v (j : jet) : R := (f_guv j * f_Bu j + f_gvv j * f_Bv j)%R.
Definition node_rs (jm jp : jet) (ih mpp : R) : R :=
  (((1 / 2 * (f_B_s_v jm + f_B_s_v jp) - (Bcov_v jp - Bcov_v jm) * ih) * (1 / 2 * (f_Bv jm + f_Bv jp))
    - ((Bcov_u jp - Bcov_u jm) * ih - 1 / 2 * (f_B_s_u jm + f_B_s_u jp)) * (1 / 2 * (f_Bu jm + f_Bu jp)))
   - mpp)%R.

(** The terms of a series whose coefficients are numbers, and the jet of the
    field at a half point from the series of R, Z and lambda there. *)
Definition cterms (f f1 : nat -> Z -> R) (modes : list (Z * Z)) : list term :=
  map (mkterm (fun j m _ => f j m) (fun j m _ => f1 j m) (fun _ _ _ => 0%R)) (combine (seq 0 (length modes)) modes).

Definition hjet (tR tZ tL : list term) (u v io ph : R) : jet :=
  Jet (Series.S0 true tR 0 u v) (S_s true tR 0 u v) (S_u true tR 0 u v) (S_v true tR 0 u v) 0
      (S_su true tR 0 u v) (S_sv true tR 0 u v) (S_uu true tR 0 u v) (S_uv true tR 0 u v) (S_vv true tR 0 u v)
      (S_s false tZ 0 u v) (S_u false tZ 0 u v) (S_v false tZ 0 u v) 0
      (S_su false tZ 0 u v) (S_sv false tZ 0 u v) (S_uu false tZ 0 u v) (S_uv false tZ 0 u v)
      (S_vv false tZ 0 u v)
      (S_u false tL 0 u v) (S_v false tL 0 u v) 0 0 (S_uu false tL 0 u v) (S_uv false tL 0 u v) (S_vv false tL 0 u v)
      io 0 ph 0.

Section HalfPoint.
Variable exps : list Z.
Variable E : env ExtendedR.

Lemma partials_ok (b : builder) (p : partials) (b' : builder) (q : partials) :
  partials_b b p = (b', q) -> extends b b' /\
  (sound E (b_binds b') ->
   xeval E (p_0 q) = xeval E (p_0 p) /\ xeval E (p_s q) = xeval E (p_s p) /\
   xeval E (p_u q) = xeval E (p_u p) /\ xeval E (p_v q) = xeval E (p_v p) /\
   xeval E (p_su q) = xeval E (p_su p) /\ xeval E (p_sv q) = xeval E (p_sv p) /\
   xeval E (p_uu q) = xeval E (p_uu p) /\ xeval E (p_uv q) = xeval E (p_uv p) /\
   xeval E (p_vv q) = xeval E (p_vv p)).
Proof.
  unfold partials_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S. peel. cbn [p_0 p_s p_u p_v p_su p_sv p_uu p_uv p_vv]. splits; assumption.
Qed.

Lemma lambda_partials_ok (b : builder) (p : lpartials) (b' : builder) (q : lpartials) :
  lambda_partials_b b p = (b', q) -> extends b b' /\
  (sound E (b_binds b') ->
   xeval E (l_u q) = xeval E (l_u p) /\ xeval E (l_v q) = xeval E (l_v p) /\
   xeval E (l_uu q) = xeval E (l_uu p) /\ xeval E (l_uv q) = xeval E (l_uv p) /\
   xeval E (l_vv q) = xeval E (l_vv p)).
Proof.
  unfold lambda_partials_b. intros H. repeat stepH H. injection H as <- <-. ext_of_allocs.
  split; [ext_chain |].
  intros S. peel. cbn [l_u l_v l_uu l_uv l_vv]. splits; assumption.
Qed.

Lemma lambdacoefs_ok (base K row : nat) (modes : list (Z * Z)) : forall k b b' cs,
  lambdacoefs_b exps b base K row modes k = (b', cs) -> extends b b' /\
  (sound E (b_binds b') ->
   Forall2 (fun jmn c => xeval E c = xeval E (slot_node exps base K row (fst jmn)))
           (combine (seq k (length modes)) modes) cs).
Proof.
  induction modes as [| mn tl IH]; intros k b b' cs H.
  - cbn in H. injection H as <- <-. split; [apply extends_refl | intros; constructor].
  - cbn [lambdacoefs_b] in H.
    destruct (alloc b (slot_node exps base K row k)) as [b1 l] eqn:A1.
    destruct (lambdacoefs_b exps b1 base K row tl (Datatypes.S k)) as [b2 rest] eqn:A2.
    injection H as <- <-. destruct (IH _ _ _ _ A2) as [X2 F2].
    destruct (alloc_spec _ _ _ _ A1) as [X1 _].
    split; [exact (extends_trans _ _ _ X1 X2) |].
    intros Sd. cbn [length seq combine]. constructor.
    + cbn [fst]. exact (proj2 (alloc_sound E _ _ _ _ A1 (sound_extends E b1 b2 X2 Sd))).
    + exact (F2 Sd).
Qed.

(** The half-point coefficients of R, Z and lambda of a stellarator-symmetric
    state, between the node rows ra and rb and at the lambda row rl. *)
Lemma half_coefs_ok (b : builder) (modes : list (Z * Z)) (K ra rb rl : nat) (sa' sb' sh' : expr)
    (b' : builder) (hc : half_coefs) :
  half_coefs_b exps b false modes K ra rb rl sa' sb' sh' = (b', hc) -> extends b b' /\
  (sound E (b_binds b') -> forall (a bb h : R) (yRa yRb yZa yZb : nat -> R),
   xeval E sa' = Xreal a -> xeval E sb' = Xreal bb -> xeval E sh' = Xreal h ->
   (0 < a)%R -> (0 < bb)%R -> (0 < h)%R -> (bb - a <> 0)%R ->
   (forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
      xeval E (slot_node exps (base_R K) K ra j) = Xreal (yRa j) /\ xeval E (slot_node exps (base_R K) K rb j) = Xreal (yRb j)) ->
   (forall j, (0 <= j)%nat -> (j < 0 + length modes)%nat ->
      xeval E (slot_node exps (base_Z K) K ra j) = Xreal (yZa j) /\ xeval E (slot_node exps (base_Z K) K rb j) = Xreal (yZb j)) ->
   Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) a bb h (yRa (fst jmn)) (yRb (fst jmn))) /\
                         xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) a bb h (yRa (fst jmn)) (yRb (fst jmn))))
           (combine (seq 0 (length modes)) modes) (hc_R hc) /\
   Forall2 (fun jmn c => xeval E (c_val c) = Xreal (hval (fst (snd jmn)) a bb h (yZa (fst jmn)) (yZb (fst jmn))) /\
                         xeval E (c_ds c) = Xreal (hslope (fst (snd jmn)) a bb h (yZa (fst jmn)) (yZb (fst jmn))))
           (combine (seq 0 (length modes)) modes) (hc_Z hc) /\
   Forall2 (fun jmn c => xeval E c = xeval E (slot_node exps (base_L K) K rl (fst jmn)))
           (combine (seq 0 (length modes)) modes) (hc_L hc)).
Proof.
  unfold half_coefs_b. intros H. repeat stepH H. injection H as <- <-. cbn [hc_R hc_Z hc_L].
  match goal with
  | Q0 : half_scalars_b _ _ _ _ = _ |- _ => rename Q0 into QA end.
  match goal with
  | Q1 : halfcoefs_b _ _ _ (base_R _) _ _ _ _ _ = _ |- _ => rename Q1 into QB end.
  match goal with
  | Q2 : halfcoefs_b _ _ _ (base_Z _) _ _ _ _ _ = _ |- _ => rename Q2 into QC end.
  match goal with
  | Q3 : lambdacoefs_b _ _ _ _ _ _ _ = _ |- _ => rename Q3 into QD end.
  destruct (half_scalars_ok E _ _ _ _ _ _ QA) as [X0 V0].
  destruct (halfcoefs_spec _ _ _ _ _ _ _ _ _ _ _ QB) as [X1 _].
  destruct (halfcoefs_spec _ _ _ _ _ _ _ _ _ _ _ QC) as [X2 _].
  destruct (lambdacoefs_ok _ _ _ _ _ _ _ _ QD) as [X3 V3].
  split; [exact (extends_trans _ _ _ X0 (extends_trans _ _ _ X1 (extends_trans _ _ _ X2 X3))) |].
  intros S4 a bb hh yRa yRb yZa yZb Ha Hb Hh Pa Pb Ph Hab HyR HyZ.
  pose proof (sound_extends E _ _ X3 S4) as S3.
  pose proof (sound_extends E _ _ X2 S3) as S2.
  pose proof (sound_extends E _ _ X1 S2) as S1.
  destruct (V0 S1 a bb hh Ha Hb Hh Pa Pb Ph Hab) as (H1 & H2 & H3 & H4 & H5 & H6).
  refine (conj (halfcoefs_values _ E _ _ _ _ _ a bb hh yRa yRb H1 H2 H3 H4 H5 H6 modes 0 _ _ _ QB HyR S2)
               (conj (halfcoefs_values _ E _ _ _ _ _ a bb hh yZa yZb H1 H2 H3 H4 H5 H6 modes 0 _ _ _ QC HyZ S3)
                     (V3 S4))).
Qed.

End HalfPoint.

(** The nine sums of [assemble] and the five of [lambda_terms], from the
    values of the kernels and the coefficients. *)
Definition kcoef2_ok (E : env ExtendedR) (s : R) (c : coef2) (t : term) : Prop :=
  xeval E (c_val c) = Xreal (tc t s) /\ xeval E (c_ds c) = Xreal (tc1 t s).
Definition kcoefe_ok (E : env ExtendedR) (s : R) (c : expr) (t : term) : Prop := xeval E c = Xreal (tc t s).

Lemma assemble_values (E : env ExtendedR) (even : bool) (kers : list mode_kernels) (coefs : list coef2)
    (ts : list term) (s u v : R) :
  Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoef2_ok E s (snd kc) t) (combine kers coefs) ts ->
  let p := assemble kers coefs even in
  xeval E (p_0 p) = Xreal (Series.S0 even ts s u v) /\ xeval E (p_s p) = Xreal (S_s even ts s u v) /\
  xeval E (p_u p) = Xreal (S_u even ts s u v) /\ xeval E (p_v p) = Xreal (S_v even ts s u v) /\
  xeval E (p_su p) = Xreal (S_su even ts s u v) /\ xeval E (p_sv p) = Xreal (S_sv even ts s u v) /\
  xeval E (p_uu p) = Xreal (S_uu even ts s u v) /\ xeval E (p_uv p) = Xreal (S_uv even ts s u v) /\
  xeval E (p_vv p) = Xreal (S_vv even ts s u v).
Proof.
  intros H p. unfold p, assemble. cbn [p_0 p_s p_u p_v p_su p_sv p_uu p_uv p_vv].
  unfold Series.S0, S_s, S_u, S_v, S_su, S_sv, S_uu, S_uv, S_vv.
  splits; apply esum_map_val; (eapply Forall2_impl; [| exact H]);
    intros [k c] t ((Hm & Hn & Hcos & Hsin) & (Hv & Hd)); cbn [fst snd] in *; unfold zmul; cbn [xeval];
    unfold k0, k1, su, sv, ang in *; destruct even;
    rewrite ?Hcos, ?Hsin, ?Hv, ?Hd, ?Hm, ?Hn; cbv [Xbind2 Xbind]; f_equal;
    rewrite ?opp_IZR, ?mult_IZR; ring.
Qed.

Lemma lambda_terms_values (E : env ExtendedR) (even : bool) (kers : list mode_kernels) (coefs : list expr)
    (ts : list term) (s u v : R) :
  Forall2 (fun kc t => kker_ok E u v (fst kc) t /\ kcoefe_ok E s (snd kc) t) (combine kers coefs) ts ->
  let p := lambda_terms kers coefs even in
  xeval E (l_u p) = Xreal (S_u even ts s u v) /\ xeval E (l_v p) = Xreal (S_v even ts s u v) /\
  xeval E (l_uu p) = Xreal (S_uu even ts s u v) /\ xeval E (l_uv p) = Xreal (S_uv even ts s u v) /\
  xeval E (l_vv p) = Xreal (S_vv even ts s u v).
Proof.
  intros H p. unfold p, lambda_terms. cbn [l_u l_v l_uu l_uv l_vv].
  unfold S_u, S_v, S_uu, S_uv, S_vv.
  splits; apply esum_map_val; (eapply Forall2_impl; [| exact H]);
    intros [k c] t ((Hm & Hn & Hcos & Hsin) & Hv); cbn [fst snd] in *; unfold kcoefe_ok in Hv; unfold zmul;
    cbn [xeval]; unfold k0, k1, su, sv, ang in *; destruct even;
    rewrite ?Hcos, ?Hsin, ?Hv, ?Hm, ?Hn; cbv [Xbind2 Xbind]; f_equal;
    rewrite ?opp_IZR, ?mult_IZR; ring.
Qed.
