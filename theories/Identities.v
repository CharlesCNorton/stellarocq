(** Identities of the reconstruction, proven rather than assumed.

    Hypotheses.v lists what the model assumes. This file holds the
    statements that do not have to be assumed because they follow from how
    the field is built, and proves them. Each is a property a floating-point
    code can only test at sample points. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal.
From Stellarocq Require Import Expr Physics Deriv.

Import ListNotations.

(* ---------------------------------------------------------------- *)
(* The field is exactly solenoidal                                   *)

(** div B = 0, exactly.

    [div_angular] is the whole divergence of the Jacobian-weighted field,
    since the radial contravariant component of VMEC's ansatz is
    identically zero. Wherever phip and the mixed second derivative of
    lambda take real values, the sum is zero: not small, zero.

    The two terms are phip times the same lambda_uv with opposite signs, so
    what is certified is that the assembled Fourier series has a symmetric
    mixed partial and that the two contravariant components are built from
    it consistently. Negating either sign in [lambda_terms] breaks it. *)
Theorem divergence_free :
  forall exps pL env p l,
  xeval env (vPhip exps) = Xreal p ->
  xeval env (l_uv pL) = Xreal l ->
  xeval env (div_angular exps pL) = Xreal 0.
Proof.
  intros exps pL env p l Hp Hl.
  unfold div_angular. cbn [xeval]. rewrite Hp, Hl. cbn.
  apply f_equal. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* The pressure is a flux function                                   *)

(** Slot 1 is the poloidal angle and slot 2 the toroidal one. *)
Definition slot_u : nat := 1.
Definition slot_v : nat := 2.

(** A power of two is a closed expression. *)
Lemma var_free_epow2 : forall n z, var_free n (epow2 z) = true.
Proof. intros n z. reflexivity. Qed.

(** An environment slot other than n, scaled by its exponent. *)
Lemma var_free_evar :
  forall n exps k, k <> n -> var_free n (evar exps k) = true.
Proof.
  intros n exps k Hk. simpl.
  rewrite andb_true_r.
  apply negb_true_iff, Nat.eqb_neq. exact Hk.
Qed.

(** A sum of closed expressions is closed. *)
Lemma var_free_esum :
  forall n l, forallb (var_free n) l = true -> var_free n (esum l) = true.
Proof.
  intros n l.
  induction l as [|a [|b tl] IH]; simpl in *; intros H.
  - reflexivity.
  - now rewrite andb_true_r in H.
  - apply andb_prop in H. destruct H as [Ha Hb].
    rewrite Ha. simpl. apply IH. exact Hb.
Qed.

(** A power of a closed expression is closed. *)
Lemma var_free_ppow :
  forall n b k, var_free n b = true -> var_free n (ppow b k) = true.
Proof.
  intros n b k Hb.
  induction k as [|k IH]; simpl; [reflexivity | now rewrite Hb, IH].
Qed.

(** A leaf of a pressure expression: a constant, a power of two, or an
    environment slot that is not one of the two angles. *)
Local Ltac leaf :=
  solve [ reflexivity
        | apply var_free_epow2
        | apply var_free_evar; unfold slot_u, slot_v in *; lia ].

(** Walk an expression built only from such leaves. *)
Local Ltac closed :=
  repeat (cbn [var_free esum map seq poly dpoly slot_am vS n_am esq e1 e2
               etanh gs_bump gs_bump_d lorentz_d lorentz_edge];
          match goal with
          | |- (_ && _)%bool = true => apply andb_true_intro; split
          | |- var_free _ (ppow _ _) = true => apply var_free_ppow
          | |- var_free _ (esum _) = true => apply var_free_esum
          | |- forallb _ _ = true =>
              apply forallb_forall; let Hx := fresh in intros ? Hx;
              apply in_map_iff in Hx;
              destruct Hx as [? [? _]]; subst
          | _ => leaf
          end).

(** A power series over the am slots does not read either angle. *)

Lemma var_free_poly :
  forall n exps off m,
  n = slot_u \/ n = slot_v ->
  var_free n (poly exps off m) = true /\
  var_free n (dpoly exps off m) = true.
Proof.
  intros n exps off m Hn. unfold poly, dpoly. split; closed.
Qed.

(** Nor does the Gaussian factor of a two_power_gs profile. *)
Lemma var_free_gs :
  forall n exps g,
  n = slot_u \/ n = slot_v ->
  var_free n (gs_val exps g) = true /\ var_free n (gs_der exps g) = true.
Proof.
  intros n exps g Hn.
  induction g as [|g IH]; simpl gs_val; simpl gs_der.
  - split; reflexivity.
  - destruct IH as [IH1 IH2].
    split; cbn [var_free]; apply andb_true_intro; split;
      solve [ assumption | unfold gs_bump, gs_bump_d; closed ].
Qed.

(** dp/ds reads the node radius and the profile coefficients and nothing
    else, so the pressure of the reconstruction is a flux function for
    every parameterization the checker admits. This is the one model
    assumption of Hypotheses.v that is a theorem rather than a premise. *)
Theorem pressure_is_a_flux_function :
  forall exps prof,
  var_free slot_u (pprime exps prof) = true /\
  var_free slot_v (pprime exps prof) = true.
Proof.
  intros exps prof.
  assert (Hone : forall n, n = slot_u \/ n = slot_v ->
                 var_free n (pprime exps prof) = true).
  { intros n Hn.
    destruct prof as [|p q| |nn nd| |p q g| |p q r t]; unfold pprime.
    - apply (proj2 (var_free_poly n exps 0 n_am Hn)).
    - closed.
    - closed.
    - destruct (var_free_poly n exps 0 nn Hn) as [Hn1 Hd1].
      destruct (var_free_poly n exps 10 nd Hn) as [Hn2 Hd2].
      cbn [var_free esq]. rewrite Hn1, Hd1, Hn2, Hd2. reflexivity.
    - closed.
    - destruct (var_free_gs n exps g Hn) as [Hgv Hgd].
      cbn [var_free]. rewrite Hgv, Hgd, !andb_true_r.
      apply andb_true_intro. split; closed.
    - destruct (var_free_poly n exps 0 16 Hn) as [_ Hd].
      cbn [var_free]. rewrite Hd. cbn [andb]. closed.
    - closed. }
  split; apply Hone; auto.
Qed.

(* ---------------------------------------------------------------- *)
(* The value of a sum of expressions                                 *)

(** A sum whose terms all vanish vanishes. The series of Physics.v are
    built with [esum], so this is what says that a reconstruction given
    zero coefficients contributes nothing. *)
Lemma xeval_esum_zero :
  forall env l,
  Forall (fun e => xeval env e = Xreal 0%R) l ->
  xeval env (esum l) = Xreal 0%R.
Proof.
  intros env l H.
  induction l as [|a l IH].
  - reflexivity.
  - inversion H as [|x xs Ha Hl]; subst.
    destruct l as [|b tl].
    + exact Ha.
    + change (esum (a :: b :: tl)) with (Eadd a (esum (b :: tl))).
      cbn [xeval]. rewrite Ha, (IH Hl). cbn.
      apply f_equal. ring.
Qed.

(** A product with a vanishing factor vanishes, provided the other factor
    is a real number. *)
Lemma xeval_mul_zero :
  forall env a b x,
  xeval env a = Xreal 0%R -> xeval env b = Xreal x ->
  xeval env (Emul a b) = Xreal 0%R.
Proof.
  intros env a b x Ha Hb. cbn [xeval]. rewrite Ha, Hb. cbn.
  apply f_equal. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* The antisymmetric half contributes nothing when it is zero        *)

(** Every term of an assembled series is a coefficient times a kernel, so a
    series whose coefficients all vanish has value zero wherever the
    kernels are real. This is what makes the lasym reconstruction reduce to
    the symmetric one: [test_lasym.py] checks that reduction by running the
    solver twice, and here it is a statement about the series itself. *)
Lemma assemble_value_zero :
  forall env kers coefs even,
  (forall c, In c coefs -> xeval env (c_val c) = Xreal 0%R) ->
  (forall k, In k kers ->
     (exists x, xeval env (mk_cos k) = Xreal x) /\
     (exists x, xeval env (mk_sin k) = Xreal x)) ->
  xeval env (p_0 (assemble kers coefs even)) = Xreal 0%R.
Proof.
  intros env kers coefs even Hc Hk.
  unfold assemble, p_0. cbn [p_0].
  apply xeval_esum_zero.
  apply Forall_forall. intros e He.
  apply in_map_iff in He. destruct He as [kc [<- Hin]].
  destruct kc as [kk cc].
  destruct (Hk kk (in_combine_l _ _ _ _ Hin)) as [[xc Hcos] [xs Hsin]].
  apply (xeval_mul_zero env _ _ (if even then xc else xs)).
  - cbn [snd]. apply Hc. exact (in_combine_r _ _ _ _ Hin).
  - cbn [fst]. destruct even; assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* An axisymmetric reconstruction has no toroidal variation          *)

(** A product of two real values is real. *)
Lemma xeval_mul_real :
  forall env a b x y,
  xeval env a = Xreal x -> xeval env b = Xreal y ->
  xeval env (Emul a b) = Xreal (x * y)%R.
Proof. intros env a b x y Ha Hb. cbn [xeval]. now rewrite Ha, Hb. Qed.

(** A term scaled by the integer zero is zero wherever the rest is real. *)
Lemma xeval_zmul_zero :
  forall env e x, xeval env e = Xreal x -> xeval env (zmul 0 e) = Xreal 0%R.
Proof.
  intros env e x He. unfold zmul. cbn [xeval]. rewrite He. cbn.
  apply f_equal. ring.
Qed.

(** A sum over a list whose every term vanishes vanishes. *)
Lemma xeval_esum_map_zero :
  forall (A : Type) env (l : list A) (f : A -> expr),
  (forall a, In a l -> xeval env (f a) = Xreal 0%R) ->
  xeval env (esum (map f l)) = Xreal 0%R.
Proof.
  intros A env l f H. apply xeval_esum_zero.
  apply Forall_forall. intros e He.
  apply in_map_iff in He. destruct He as [a [<- Ha]]. now apply H.
Qed.

(** Every mode of an axisymmetric equilibrium has n = 0, and every toroidal
    derivative of an assembled series carries a factor n. So those
    derivatives are exactly zero, not merely small: the reconstruction has
    no toroidal variation at all.

    This is what lets a cell certificate span the whole toroidal angle in a
    single cell. The checker sees that the derivative it has to enclose is
    the zero expression, so the mean-value step over the toroidal angle
    costs nothing however wide the cell, and the covering of an axisymmetric
    case is one dimensional. *)
Theorem toroidal_terms_vanish :
  forall env kers coefs even,
  (forall k, In k kers -> mk_n k = 0%Z) ->
  (forall k, In k kers ->
     (exists x, xeval env (mk_cos k) = Xreal x) /\
     (exists x, xeval env (mk_sin k) = Xreal x)) ->
  (forall c, In c coefs ->
     (exists x, xeval env (c_val c) = Xreal x) /\
     (exists x, xeval env (c_ds c) = Xreal x)) ->
  xeval env (p_v (assemble kers coefs even)) = Xreal 0%R /\
  xeval env (p_sv (assemble kers coefs even)) = Xreal 0%R /\
  xeval env (p_uv (assemble kers coefs even)) = Xreal 0%R /\
  xeval env (p_vv (assemble kers coefs even)) = Xreal 0%R.
Proof.
  intros env kers coefs even Hn Hk Hc.
  assert (Hpair : forall kc, In kc (combine kers coefs) ->
            mk_n (fst kc) = 0%Z /\
            (exists x, xeval env (mk_cos (fst kc)) = Xreal x) /\
            (exists x, xeval env (mk_sin (fst kc)) = Xreal x) /\
            (exists x, xeval env (c_val (snd kc)) = Xreal x) /\
            (exists x, xeval env (c_ds (snd kc)) = Xreal x)).
  { intros [kk cc] Hin.
    assert (Hkk := in_combine_l _ _ _ _ Hin).
    assert (Hcc := in_combine_r _ _ _ _ Hin).
    destruct (Hk kk Hkk) as [Hc1 Hs1]. destruct (Hc cc Hcc) as [Hv1 Hd1].
    cbn [fst snd]. repeat split; try assumption. now apply Hn. }
  unfold assemble. cbn [p_v p_sv p_uv p_vv].
  repeat split; apply xeval_esum_map_zero; intros kc Hkc;
    destruct (Hpair kc Hkc) as [Hzero [[xc Hcos] [[xs Hsin] [[xv Hval] [xd Hds]]]]];
    rewrite Hzero.
  - destruct even; cbn [Z.opp];
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R);
        now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R);
        now apply xeval_mul_real ].
  - destruct even; cbn [Z.opp];
      [ apply (xeval_zmul_zero _ _ (xd * xs)%R);
        now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xd * xc)%R);
        now apply xeval_mul_real ].
  - rewrite Z.mul_0_r.
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real ].
  - cbn [Z.mul Z.opp].
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real ].
Qed.

(** The same for the stream function, whose angular derivatives are the
    only way lambda enters the field. *)
Theorem toroidal_lambda_terms_vanish :
  forall env kers coefs even,
  (forall k, In k kers -> mk_n k = 0%Z) ->
  (forall k, In k kers ->
     (exists x, xeval env (mk_cos k) = Xreal x) /\
     (exists x, xeval env (mk_sin k) = Xreal x)) ->
  (forall c, In c coefs -> exists x, xeval env c = Xreal x) ->
  xeval env (l_v (lambda_terms kers coefs even)) = Xreal 0%R /\
  xeval env (l_uv (lambda_terms kers coefs even)) = Xreal 0%R /\
  xeval env (l_vv (lambda_terms kers coefs even)) = Xreal 0%R.
Proof.
  intros env kers coefs even Hn Hk Hc.
  assert (Hpair : forall kc, In kc (combine kers coefs) ->
            mk_n (fst kc) = 0%Z /\
            (exists x, xeval env (mk_cos (fst kc)) = Xreal x) /\
            (exists x, xeval env (mk_sin (fst kc)) = Xreal x) /\
            (exists x, xeval env (snd kc) = Xreal x)).
  { intros [kk cc] Hin.
    assert (Hkk := in_combine_l _ _ _ _ Hin).
    assert (Hcc := in_combine_r _ _ _ _ Hin).
    destruct (Hk kk Hkk) as [Hc1 Hs1].
    cbn [fst snd]. repeat split; try assumption. now apply Hn. now apply Hc. }
  unfold lambda_terms. cbn [l_v l_uv l_vv].
  repeat split; apply xeval_esum_map_zero; intros kc Hkc;
    destruct (Hpair kc Hkc) as [Hzero [[xc Hcos] [[xs Hsin] [xv Hval]]]];
    rewrite Hzero.
  - destruct even; cbn [Z.opp];
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
  - rewrite Z.mul_0_r.
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real ].
  - cbn [Z.mul Z.opp].
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real ].
Qed.

(* ---------------------------------------------------------------- *)
(* The gauge freedom of the stream function                          *)

(** Two sums whose terms agree pointwise have the same value. *)
Lemma xeval_esum_ext :
  forall env l1 l2,
  Forall2 (fun a b => xeval env a = xeval env b) l1 l2 ->
  xeval env (esum l1) = xeval env (esum l2).
Proof.
  intros env l1. induction l1 as [|a l1 IH]; intros l2 H.
  - inversion H; subst. reflexivity.
  - inversion H as [|x y l1' l2' Hab Hrest]; subst.
    destruct l1 as [|a2 l1''].
    + inversion Hrest; subst. exact Hab.
    + inversion Hrest as [|x2 y2 l1''' l2''' Hab2 Hrest2]; subst.
      change (esum (a :: a2 :: l1'')) with (Eadd a (esum (a2 :: l1''))).
      change (esum (y :: y2 :: l2''')) with (Eadd y (esum (y2 :: l2'''))).
      cbn [xeval]. rewrite Hab, (IH _ Hrest). reflexivity.
Qed.

(** The termwise step: two coefficient lists that agree except where the mode
    has m = n = 0 give a series whose terms agree pointwise, once a term of
    such a mode is known to vanish. *)
Lemma gauge_Forall2 :
  forall env (F : mode_kernels -> expr -> expr) kers coefs coefs',
  (forall k c c', In k kers -> xeval env c = xeval env c' ->
     xeval env (F k c) = xeval env (F k c')) ->
  (forall k c, In k kers -> mk_m k = 0%Z -> mk_n k = 0%Z ->
     (exists x, xeval env c = Xreal x) ->
     xeval env (F k c) = Xreal 0%R) ->
  (forall c, In c coefs -> exists x, xeval env c = Xreal x) ->
  (forall c, In c coefs' -> exists x, xeval env c = Xreal x) ->
  length coefs = length coefs' ->
  Forall2 (fun k cc => (mk_m k = 0%Z /\ mk_n k = 0%Z)
                       \/ xeval env (fst cc) = xeval env (snd cc))
          kers (combine coefs coefs') ->
  Forall2 (fun a b => xeval env a = xeval env b)
          (map (fun kc => F (fst kc) (snd kc)) (combine kers coefs))
          (map (fun kc => F (fst kc) (snd kc)) (combine kers coefs')).
Proof.
  intros env F kers. induction kers as [|k ks IH];
    intros coefs coefs' Hext Hzero Hr Hr' Hlen Hall.
  - simpl. constructor.
  - destruct coefs as [|c cs]; destruct coefs' as [|c' cs'];
      simpl in Hlen; try discriminate.
    + simpl in Hall. inversion Hall.
    + simpl in Hall.
      inversion Hall as [|kk cc kss ccs Hhead Htail]; subst.
      simpl. constructor.
      * cbn [fst snd] in Hhead |- *.
        destruct Hhead as [[Hm Hn]|Heq].
        -- rewrite (Hzero k c (or_introl eq_refl) Hm Hn
                      (Hr c (or_introl eq_refl))).
           rewrite (Hzero k c' (or_introl eq_refl) Hm Hn
                      (Hr' c' (or_introl eq_refl))).
           reflexivity.
        -- apply Hext. now left. exact Heq.
      * apply IH.
        -- intros x y y' Hin. apply Hext. now right.
        -- intros x y Hin. apply Hzero. now right.
        -- intros x Hx. apply Hr. now right.
        -- intros x Hx. apply Hr'. now right.
        -- now injection Hlen.
        -- exact Htail.
Qed.

(** The poloidal gauge freedom, as a theorem about the series rather than a
    convention. Every term of [lambda_terms] carries a factor m or n, so the
    m = 0, n = 0 coefficient of lambda drives nothing: two reconstructions
    that differ only there have the same angular derivatives of lambda, and
    therefore the same field and the same residual. VMEC uses that freedom
    to fix lambda, and nothing in the reconstruction depends on how it is
    fixed. *)
Theorem lambda_gauge :
  forall env kers coefs coefs' even,
  (forall k, In k kers ->
     (exists x, xeval env (mk_cos k) = Xreal x) /\
     (exists x, xeval env (mk_sin k) = Xreal x)) ->
  (forall c, In c coefs -> exists x, xeval env c = Xreal x) ->
  (forall c, In c coefs' -> exists x, xeval env c = Xreal x) ->
  length coefs = length coefs' ->
  Forall2 (fun k cc => (mk_m k = 0%Z /\ mk_n k = 0%Z)
                       \/ xeval env (fst cc) = xeval env (snd cc))
          kers (combine coefs coefs') ->
  xeval env (l_u (lambda_terms kers coefs even))
  = xeval env (l_u (lambda_terms kers coefs' even)) /\
  xeval env (l_v (lambda_terms kers coefs even))
  = xeval env (l_v (lambda_terms kers coefs' even)) /\
  xeval env (l_uu (lambda_terms kers coefs even))
  = xeval env (l_uu (lambda_terms kers coefs' even)) /\
  xeval env (l_uv (lambda_terms kers coefs even))
  = xeval env (l_uv (lambda_terms kers coefs' even)) /\
  xeval env (l_vv (lambda_terms kers coefs even))
  = xeval env (l_vv (lambda_terms kers coefs' even)).
Proof.
  intros env kers coefs coefs' even Hk Hr Hr' Hlen Hall.
  assert (Hgen : forall (zf : mode_kernels -> Z) (kf : mode_kernels -> expr),
            (forall k, mk_m k = 0%Z -> mk_n k = 0%Z -> zf k = 0%Z) ->
            (forall k, In k kers -> exists x, xeval env (kf k) = Xreal x) ->
            xeval env (esum (map (fun kc => zmul (zf (fst kc))
                                              (Emul (snd kc) (kf (fst kc))))
                                 (combine kers coefs)))
            = xeval env (esum (map (fun kc => zmul (zf (fst kc))
                                                (Emul (snd kc) (kf (fst kc))))
                                   (combine kers coefs')))).
  { intros zf kf Hzf Hkf.
    apply xeval_esum_ext.
    apply (gauge_Forall2 env (fun k c => zmul (zf k) (Emul c (kf k))));
      try assumption.
    - intros k c c' Hin Heq. unfold zmul. cbn [xeval]. now rewrite Heq.
    - intros k c Hin Hm Hn [x Hx].
      rewrite (Hzf k Hm Hn).
      destruct (Hkf k Hin) as [y Hy].
      apply (xeval_zmul_zero _ _ (x * y)%R). now apply xeval_mul_real. }
  unfold lambda_terms. cbn [l_u l_v l_uu l_uv l_vv].
  destruct even.
  - repeat split.
    + apply (Hgen (fun k => Z.opp (mk_m k)) (fun k => mk_sin k)).
      intros k Hm _. rewrite Hm. reflexivity.
      intros k Hin. exact (proj2 (Hk k Hin)).
    + apply (Hgen (fun k => mk_n k) (fun k => mk_sin k)).
      intros k _ Hn. exact Hn.
      intros k Hin. exact (proj2 (Hk k Hin)).
    + apply (Hgen (fun k => Z.opp (mk_m k * mk_m k)) (fun k => mk_cos k)).
      intros k Hm _. rewrite Hm. reflexivity.
      intros k Hin. exact (proj1 (Hk k Hin)).
    + apply (Hgen (fun k => (mk_m k * mk_n k)%Z) (fun k => mk_cos k)).
      intros k Hm _. rewrite Hm. reflexivity.
      intros k Hin. exact (proj1 (Hk k Hin)).
    + apply (Hgen (fun k => Z.opp (mk_n k * mk_n k)) (fun k => mk_cos k)).
      intros k _ Hn. rewrite Hn. reflexivity.
      intros k Hin. exact (proj1 (Hk k Hin)).
  - repeat split.
    + apply (Hgen (fun k => mk_m k) (fun k => mk_cos k)).
      intros k Hm _. exact Hm.
      intros k Hin. exact (proj1 (Hk k Hin)).
    + apply (Hgen (fun k => Z.opp (mk_n k)) (fun k => mk_cos k)).
      intros k _ Hn. rewrite Hn. reflexivity.
      intros k Hin. exact (proj1 (Hk k Hin)).
    + apply (Hgen (fun k => Z.opp (mk_m k * mk_m k)) (fun k => mk_sin k)).
      intros k Hm _. rewrite Hm. reflexivity.
      intros k Hin. exact (proj2 (Hk k Hin)).
    + apply (Hgen (fun k => (mk_m k * mk_n k)%Z) (fun k => mk_sin k)).
      intros k Hm _. rewrite Hm. reflexivity.
      intros k Hin. exact (proj2 (Hk k Hin)).
    + apply (Hgen (fun k => Z.opp (mk_n k * mk_n k)) (fun k => mk_sin k)).
      intros k _ Hn. rewrite Hn. reflexivity.
      intros k Hin. exact (proj2 (Hk k Hin)).
Qed.

(* ---------------------------------------------------------------- *)
(* An axisymmetric reconstruction is exactly quasisymmetric          *)

(** The third-order series carry the same integer factors as the lower
    orders, so the ones with a toroidal derivative vanish exactly when every
    n is zero; only the pure poloidal derivatives survive. This is what the
    quasisymmetry residual reads, and it is why that residual is the zero
    expression for an axisymmetric field. *)
Theorem toroidal_terms3_vanish :
  forall env kers coefs even,
  (forall k, In k kers -> mk_n k = 0%Z) ->
  (forall k, In k kers ->
     (exists x, xeval env (mk_cos k) = Xreal x) /\
     (exists x, xeval env (mk_sin k) = Xreal x)) ->
  (forall c, In c coefs ->
     (exists x, xeval env (c_val c) = Xreal x) /\
     (exists x, xeval env (c_ds c) = Xreal x)) ->
  xeval env (p3_uuv (assemble3 kers coefs even)) = Xreal 0%R /\
  xeval env (p3_uvv (assemble3 kers coefs even)) = Xreal 0%R /\
  xeval env (p3_vvv (assemble3 kers coefs even)) = Xreal 0%R /\
  xeval env (p3_suv (assemble3 kers coefs even)) = Xreal 0%R /\
  xeval env (p3_svv (assemble3 kers coefs even)) = Xreal 0%R.
Proof.
  intros env kers coefs even Hn Hk Hc.
  assert (Hpair : forall kc, In kc (combine kers coefs) ->
            mk_n (fst kc) = 0%Z /\
            (exists x, xeval env (mk_cos (fst kc)) = Xreal x) /\
            (exists x, xeval env (mk_sin (fst kc)) = Xreal x) /\
            (exists x, xeval env (c_val (snd kc)) = Xreal x) /\
            (exists x, xeval env (c_ds (snd kc)) = Xreal x)).
  { intros [kk cc] Hin.
    assert (Hkk := in_combine_l _ _ _ _ Hin).
    assert (Hcc := in_combine_r _ _ _ _ Hin).
    destruct (Hk kk Hkk) as [Hc1 Hs1]. destruct (Hc cc Hcc) as [Hv1 Hd1].
    cbn [fst snd]. repeat split; try assumption. now apply Hn. }
  unfold assemble3. cbn [p3_uuv p3_uvv p3_vvv p3_suv p3_svv].
  repeat split; apply xeval_esum_map_zero; intros kc Hkc;
    destruct (Hpair kc Hkc) as [Hzero [[xc Hcos] [[xs Hsin] [[xv Hval] [xd Hds]]]]];
    rewrite Hzero.
  - (* uuv: the switch of the toroidal angle carries n *)
    destruct even; cbn [Z.opp]; rewrite Z.mul_0_l;
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
  - (* uvv: the square of n *)
    rewrite Z.mul_0_l. cbn [Z.opp]. rewrite Z.mul_0_r.
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
  - (* vvv: both *)
    destruct even; cbn [Z.opp]; rewrite Z.mul_0_l;
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
  - (* suv: m n, on the radial derivative of the coefficient *)
    rewrite Z.mul_0_r.
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xd * xc)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xd * xs)%R); now apply xeval_mul_real ].
  - (* svv: n squared, on the radial derivative of the coefficient *)
    rewrite Z.mul_0_l. cbn [Z.opp].
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xd * xc)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xd * xs)%R); now apply xeval_mul_real ].
Qed.

(** The same for the stream function's third derivatives. *)
Theorem toroidal_lambda_terms3_vanish :
  forall env kers coefs even,
  (forall k, In k kers -> mk_n k = 0%Z) ->
  (forall k, In k kers ->
     (exists x, xeval env (mk_cos k) = Xreal x) /\
     (exists x, xeval env (mk_sin k) = Xreal x)) ->
  (forall c, In c coefs -> exists x, xeval env c = Xreal x) ->
  xeval env (l3_uuv (lambda_terms3 kers coefs even)) = Xreal 0%R /\
  xeval env (l3_uvv (lambda_terms3 kers coefs even)) = Xreal 0%R /\
  xeval env (l3_vvv (lambda_terms3 kers coefs even)) = Xreal 0%R.
Proof.
  intros env kers coefs even Hn Hk Hc.
  assert (Hpair : forall kc, In kc (combine kers coefs) ->
            mk_n (fst kc) = 0%Z /\
            (exists x, xeval env (mk_cos (fst kc)) = Xreal x) /\
            (exists x, xeval env (mk_sin (fst kc)) = Xreal x) /\
            (exists x, xeval env (snd kc) = Xreal x)).
  { intros [kk cc] Hin.
    assert (Hkk := in_combine_l _ _ _ _ Hin).
    assert (Hcc := in_combine_r _ _ _ _ Hin).
    destruct (Hk kk Hkk) as [Hc1 Hs1].
    cbn [fst snd]. repeat split; try assumption. now apply Hn. now apply Hc. }
  unfold lambda_terms3. cbn [l3_uuv l3_uvv l3_vvv].
  repeat split; apply xeval_esum_map_zero; intros kc Hkc;
    destruct (Hpair kc Hkc) as [Hzero [[xc Hcos] [[xs Hsin] [xv Hval]]]];
    rewrite Hzero.
  - destruct even; cbn [Z.opp]; rewrite Z.mul_0_l;
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
  - rewrite Z.mul_0_l. cbn [Z.opp]. rewrite Z.mul_0_r.
    destruct even;
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
  - destruct even; cbn [Z.opp]; rewrite Z.mul_0_l;
      [ apply (xeval_zmul_zero _ _ (xv * xs)%R); now apply xeval_mul_real
      | apply (xeval_zmul_zero _ _ (xv * xc)%R); now apply xeval_mul_real ].
Qed.

(** The (u, v)-Jacobian of two surface functions with no toroidal variation
    is zero. This is the whole of the quasisymmetry of an axisymmetric
    field once the toroidal derivatives are known to vanish, and it is stated
    on the combinator the residual is built with, for any real values of the
    poloidal derivatives and any nonzero denominator. What a covering bounds
    is this expression read at the slots of a point; what this says is that
    where the two toroidal derivatives are zero the bound is exact. *)
Theorem qs_triple_zero :
  forall env dB2u dB2v dW2u dW2v den a c d,
  xeval env dB2u = Xreal a ->
  xeval env dB2v = Xreal 0%R ->
  xeval env dW2u = Xreal c ->
  xeval env dW2v = Xreal 0%R ->
  xeval env den = Xreal d ->
  d <> 0%R ->
  xeval env (qs_triple_e dB2u dB2v dW2u dW2v den) = Xreal 0%R.
Proof.
  intros env dB2u dB2v dW2u dW2v den a c d Hu Hv Hwu Hwv Hd Hd0.
  unfold qs_triple_e. cbn [xeval].
  rewrite Hu, Hv, Hwu, Hwv, Hd.
  cbn [Xmul]. unfold Xdiv, Xdiv'.
  generalize (is_zero_spec d). case (is_zero d).
  - intros Hz. inversion Hz. contradiction.
  - intros _. cbn [Xsub]. f_equal. unfold Rdiv. ring.
Qed.
