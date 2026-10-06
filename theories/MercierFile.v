(** The Mercier criterion with the file's radial differences.

    [MercierRun.merc_run] reads the four flux-function derivatives the
    criterion needs, V'', mu0 p', iota' and the current gradient, as angular
    integrals of the free-radius reconstruction's radial derivatives. Here they
    are numbers of the certificate instead, as the file's centred differences
    of its half-grid profiles give them, each an exact dyadic times the
    angular area 4 pi^2 that the integrals carry; the four angular integrands
    of the surface, tpp, tbb, tjb and tjj, are integrated by the checker as
    before. [merc_run_q_correct] states that each term the run returns encloses
    that term of `mercier.f90` evaluated at those integrals and numbers. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell Quad Integrate Mercier MercierRun.

Import ListNotations.

Local Open Scope R_scope.

(** The two coverings of the surface integrands. *)
Definition merc_outs_q (A B : block) : bool :=
  match pc_out (bk_cfg A), pc_out (bk_cfg B) with
  | RMercierA, RMercierB => true
  | _, _ => false
  end.

Lemma merc_outs_q_ok :
  forall A B, merc_outs_q A B = true ->
  pc_out (bk_cfg A) = RMercierA /\ pc_out (bk_cfg B) = RMercierB.
Proof.
  intros A B H. unfold merc_outs_q in H.
  destruct (pc_out (bk_cfg A)); try discriminate;
  destruct (pc_out (bk_cfg B)); try discriminate.
  split; reflexivity.
Qed.

(** The six dyadic numbers: V'', mu0 p', iota', the current gradient, phips
    and signgs, each a mantissa and an exponent. *)
Record qnums := QNums {
  q_vp : Z * Z ; q_pp : Z * Z ; q_sh : Z * Z ; q_cg : Z * Z ;
  q_ph : Z * Z ; q_sg : Z * Z }.

Definition qval (p : Z * Z) : R := IZR (fst p) * powerRZ 2 (snd p).

Definition qi (prec : F.precision) (p : Z * Z) : I.type :=
  ieval prec eempty (eps_e (fst p) (snd p)).

(** A flux-function derivative d as its torus integral 4 pi^2 d. *)
Definition e4pi2 : expr := Emul (Emul (EfromZ 2) Epi) (Emul (EfromZ 2) Epi).

Definition qval4 (p : Z * Z) : R := qval p * ((2 * PI) * (2 * PI)).

Definition qi4 (prec : F.precision) (p : Z * Z) : I.type :=
  ieval prec eempty (Emul (eps_e (fst p) (snd p)) e4pi2).

(** The pressure derivative in pascals, carried to mu0 p' times 4 pi^2. *)
Definition qval4m (p : Z * Z) : R := qval4 p * (IZR 4 * PI / IZR 10000000).

Definition qi4m (prec : F.precision) (p : Z * Z) : I.type :=
  ieval prec eempty (Emul (Emul (eps_e (fst p) (snd p)) e4pi2) mu0).

Definition merc_run_q (prec : F.precision) (A B : block) (q : qnums)
    : option (list I.type * list I.type) :=
  if merc_outs_q A B then
    match torus prec A, torus prec B with
    | Some OA, Some OB =>
        let fi (O : list (I.type * I.type)) (c : nat) := fst (nth c O (I.nai, I.nai)) in
        let ins := [fi OA 0%nat; fi OA 1%nat; fi OA 2%nat; fi OB 0%nat;
                    qi4 prec (q_vp q); qi4m prec (q_pp q); qi4 prec (q_sh q); qi4 prec (q_cg q);
                    qi prec (q_ph q); qi prec (q_sg q)] in
        Some (ins, map (ieval prec (of_list ins)) merc_terms)
    | _, _ => None
    end
  else None.

(** The ten numbers the terms are evaluated at, in Mercier.v's slot order. *)
Definition merc_vals_q (A B : block) (q : qnums) : list R :=
  [torus_int A 0%nat; torus_int A 1%nat; torus_int A 2%nat; torus_int B 0%nat;
   qval4 (q_vp q); qval4m (q_pp q); qval4 (q_sh q); qval4 (q_cg q);
   qval (q_ph q); qval (q_sg q)].

Lemma qi_encloses : forall prec p, contains (I.convert (qi prec p)) (Xreal (qval p)).
Proof. intros prec [m e]. unfold qi, qval. apply eps_encloses. Qed.

Lemma qi4_encloses : forall prec p, contains (I.convert (qi4 prec p)) (Xreal (qval4 p)).
Proof.
  intros prec [m e]. unfold qi4, qval4, qval, e4pi2. cbn [fst snd].
  assert (H := ieval_correct prec eempty eempty
                 (Emul (eps_e m e) (Emul (Emul (EfromZ 2) Epi) (Emul (EfromZ 2) Epi))) env_ok_nil).
  cbn [xeval] in H. rewrite xeval_eps_e in H. exact H.
Qed.

Lemma qi4m_encloses : forall prec p, contains (I.convert (qi4m prec p)) (Xreal (qval4m p)).
Proof.
  intros prec [m e]. unfold qi4m, qval4m, qval4, qval, e4pi2, mu0, e4. cbn [fst snd].
  assert (H := ieval_correct prec eempty eempty
                 (Emul (Emul (eps_e m e) (Emul (Emul (EfromZ 2) Epi) (Emul (EfromZ 2) Epi)))
                       (Ediv (Emul (EfromZ 4) Epi) (EfromZ 10000000))) env_ok_nil).
  cbn [xeval] in H. rewrite xeval_eps_e in H. cbn [Xmul Xdiv Xbind2] in H. unfold Xdiv' in H.
  assert (Hz : is_zero (IZR 10000000) = false).
  { generalize (is_zero_spec (IZR 10000000)). case (is_zero (IZR 10000000)).
    - intros Hs. inversion Hs as [H0|]. exfalso. revert H0. apply not_0_IZR. discriminate.
    - reflexivity. }
  rewrite Hz in H. exact H.
Qed.

Theorem merc_run_q_correct :
  forall prec A B q ins Is,
  merc_run_q prec A B q = Some (ins, Is) ->
  pc_out (bk_cfg A) = RMercierA /\ pc_out (bk_cfg B) = RMercierB /\
  length Is = 6%nat /\
  forall k, (k < 6)%nat ->
  contains (I.convert (nth k Is I.nai))
    (xeval (mxenv (merc_vals_q A B q)) (nth k merc_terms e_dmerc)).
Proof.
  intros prec A B q ins Is H.
  unfold merc_run_q in H.
  destruct (merc_outs_q A B) eqn:Ho; [| discriminate].
  destruct (merc_outs_q_ok A B Ho) as (HA & HB).
  destruct (torus prec A) as [OA |] eqn:EA; [| discriminate].
  destruct (torus prec B) as [OB |] eqn:EB; [| discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => (ins, Is) end)) in H.
  cbv beta iota in H.
  pose proof (f_equal fst H) as H1. pose proof (f_equal snd H) as H2.
  cbn [fst snd] in H1, H2. subst ins Is.
  assert (Hall : Forall2 (fun i v => contains (I.convert i) (Xreal v))
            [fst (nth 0 OA (I.nai, I.nai)); fst (nth 1 OA (I.nai, I.nai)); fst (nth 2 OA (I.nai, I.nai));
             fst (nth 0 OB (I.nai, I.nai));
             qi4 prec (q_vp q); qi4m prec (q_pp q); qi4 prec (q_sh q); qi4 prec (q_cg q);
             qi prec (q_ph q); qi prec (q_sg q)]
            (merc_vals_q A B q)).
  { unfold merc_vals_q.
    apply Forall2_cons; [apply (torus_encloses prec A OA EA); lia |].
    apply Forall2_cons; [apply (torus_encloses prec A OA EA); lia |].
    apply Forall2_cons; [apply (torus_encloses prec A OA EA); lia |].
    apply Forall2_cons; [apply (torus_encloses prec B OB EB); lia |].
    apply Forall2_cons; [apply qi4_encloses |].
    apply Forall2_cons; [apply qi4m_encloses |].
    do 2 (apply Forall2_cons; [apply qi4_encloses |]).
    do 2 (apply Forall2_cons; [apply qi_encloses |]).
    apply Forall2_nil. }
  refine (conj HA (conj HB (conj _ _))).
  { rewrite length_map. reflexivity. }
  intros k Hk.
  rewrite (nth_map_lt _ _ _ merc_terms k e_dmerc I.nai ltac:(unfold merc_terms; simpl; lia)).
  exact (ieval_correct prec _ _ _ (env_ok_list _ _ Hall)).
Qed.

(** A run whose DMerc lies above N 2^q, and one whose DMerc lies below
    -N 2^q, with the file's differences. *)
Theorem merc_q_stable :
  forall prec A B q ins Is N e,
  merc_run_q prec A B q = Some (ins, Is) ->
  above prec (nth 5 Is I.nai) N e = true ->
  exists d, xeval (mxenv (merc_vals_q A B q)) e_dmerc = Xreal d /\ IZR N * powerRZ 2 e <= d.
Proof.
  intros prec A B q ins Is N e H Hb.
  destruct (merc_run_q_correct prec A B q ins Is H) as (_ & _ & _ & Hk).
  pose proof (Hk 5%nat ltac:(lia)) as H5. cbn [nth merc_terms] in H5.
  destruct (xeval (mxenv (merc_vals_q A B q)) e_dmerc) as [| d] eqn:Hd.
  - unfold above in Hb.
    assert (Henv : env_ok (eset 0 eempty (nth 5 Is I.nai)) (eset 0 eempty Xnan)).
    { apply env_ok_eset. apply env_ok_nil. exact H5. }
    destruct (nonneg_correct _ _ (ieval_correct prec _ _ (Esub (Evar 0) (eps_e N e)) Henv) Hb)
      as [r [Hr _]].
    cbn [xeval] in Hr. rewrite eget_eset_eq in Hr. simpl in Hr. discriminate.
  - exists d. split; [reflexivity |]. exact (above_correct prec _ d N e H5 Hb).
Qed.

Theorem merc_q_unstable :
  forall prec A B q ins Is N e,
  merc_run_q prec A B q = Some (ins, Is) ->
  below prec (nth 5 Is I.nai) N e = true ->
  exists d, xeval (mxenv (merc_vals_q A B q)) e_dmerc = Xreal d /\ d <= - (IZR N * powerRZ 2 e).
Proof.
  intros prec A B q ins Is N e H Hb.
  destruct (merc_run_q_correct prec A B q ins Is H) as (_ & _ & _ & Hk).
  pose proof (Hk 5%nat ltac:(lia)) as H5. cbn [nth merc_terms] in H5.
  destruct (xeval (mxenv (merc_vals_q A B q)) e_dmerc) as [| d] eqn:Hd.
  - unfold below in Hb.
    assert (Henv : env_ok (eset 0 eempty (nth 5 Is I.nai)) (eset 0 eempty Xnan)).
    { apply env_ok_eset. apply env_ok_nil. exact H5. }
    destruct (nonneg_correct _ _ (ieval_correct prec _ _ (Esub (Eneg (Evar 0)) (eps_e N e)) Henv) Hb)
      as [r [Hr _]].
    cbn [xeval] in Hr. rewrite eget_eset_eq in Hr. simpl in Hr. discriminate.
  - exists d. split; [reflexivity |]. exact (below_correct prec _ d N e H5 Hb).
Qed.
