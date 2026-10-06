(** The Mercier criterion of a surface in one run of the checker.

    Mercier.v assembles the criterion from ten enclosures handed to it. Here
    the checker computes eight of them itself, as integrals over the whole
    angular torus, [0, 2 pi] in both angles, of the integrands that four
    configurations of Physics.v carry at one node ([Integrate.integ2_torus]),
    and reads the other two, the file's phips and signgs, as numbers of the
    certificate. [merc_run_correct] states that each term the run returns
    encloses that term of `mercier.f90` evaluated at the reconstruction's own
    integrals, so no enclosure passes from one run to another.

    The four coverings are the half-grid integrands of [RMercierA] (tpp, tbb,
    tjb) and [RMercierB] (tjj), and the free-radius integrands of
    [RRadialGeom] (whose second component integrates to V'') and
    [RRadialShear] (iota', the integrand of the current gradient, and
    mu0 p'), in the slot order Mercier.v fixes. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell Quad Integrate Mercier.

Import ListNotations.

Local Open Scope R_scope.

(** One covering: a node's point, its configuration and modes, and a lattice
    of NU by NV cells of half-widths hu and hv from 0 in the two angle slots. *)
Record block := Block {
  bk_es : list Z ; bk_ms : list Z ; bk_cfg : pconfig ; bk_modes : list (Z * Z) ;
  bk_hu : Z ; bk_NU : nat ; bk_hv : Z ; bk_NV : nat }.

(** The poloidal and toroidal angle slots. *)
Definition su : nat := 1%nat.
Definition sv : nat := 2%nat.

Definition torus (prec : F.precision) (b : block) : option (list (I.type * I.type)) :=
  integ2_torus su sv prec (bk_es b) (bk_ms b) (bk_cfg b) (bk_modes b) (bk_hu b) (bk_NU b) (bk_hv b) (bk_NV b).

(** The integral of component c of a block over the angular torus, in the
    units of the angles: the integral over the mantissas of one period of
    each, scaled by 2 to the two exponents. *)
Definition torus_int (b : block) (c : nat) : R :=
  let r3 := residual (bk_es b) (bk_cfg b) (bk_modes b) in
  match slot_of (comp_of r3 c) with
  | Some n =>
      let f := cellf su sv (r_binds r3) n (bk_ms b) in
      RInt (fun v => RInt (fun u => f u v) 0 (period (nth su (bk_es b) 0%Z))) 0
           (period (nth sv (bk_es b) 0%Z))
      * powerRZ 2 (nth su (bk_es b) 0%Z + nth sv (bk_es b) 0%Z)
  | None => 0
  end.

(** A run's enclosure of component c of a block contains its torus integral. *)
Lemma torus_encloses :
  forall prec b Os, torus prec b = Some Os ->
  forall c, (c < 3)%nat ->
  contains (I.convert (fst (nth c Os (I.nai, I.nai)))) (Xreal (torus_int b c)).
Proof.
  intros prec b Os H c Hc.
  destruct (integ2_torus_correct su sv prec (bk_es b) (bk_ms b) (bk_cfg b) (bk_modes b)
              (bk_hu b) (bk_NU b) (bk_hv b) (bk_NV b) Os H c Hc) as [n [Hn [_ Hin]]].
  unfold torus_int. rewrite Hn. exact Hin.
Qed.

(** The six terms, in the order a run returns them. *)
Definition merc_terms : list expr := [e_dshear; e_dcurr; e_dwell; e_dgeod; e_dstable; e_dmerc].

(** The configurations of the four coverings. *)
Definition merc_outs (A B G S : block) : bool :=
  match pc_out (bk_cfg A), pc_out (bk_cfg B), pc_out (bk_cfg G), pc_out (bk_cfg S) with
  | RMercierA, RMercierB, RRadialGeom, RRadialShear => true
  | _, _, _, _ => false
  end.

Lemma merc_outs_ok :
  forall A B G S, merc_outs A B G S = true ->
  pc_out (bk_cfg A) = RMercierA /\ pc_out (bk_cfg B) = RMercierB /\
  pc_out (bk_cfg G) = RRadialGeom /\ pc_out (bk_cfg S) = RRadialShear.
Proof.
  intros A B G S H. unfold merc_outs in H.
  destruct (pc_out (bk_cfg A)); try discriminate;
  destruct (pc_out (bk_cfg B)); try discriminate;
  destruct (pc_out (bk_cfg G)); try discriminate;
  destruct (pc_out (bk_cfg S)); try discriminate.
  repeat split.
Qed.

(** The run: the ten inputs, the eight integrals and the two numbers, and the
    six terms. phips and signgs are the dyadic numbers phm 2^phe and
    sgm 2^sge. *)
Definition merc_run (prec : F.precision) (A B G S : block) (phm phe sgm sge : Z)
    : option (list I.type * list I.type) :=
  if merc_outs A B G S then
    match torus prec A, torus prec B, torus prec G, torus prec S with
    | Some OA, Some OB, Some OG, Some OS =>
        let fi (O : list (I.type * I.type)) (c : nat) := fst (nth c O (I.nai, I.nai)) in
        let ins := [fi OA 0%nat; fi OA 1%nat; fi OA 2%nat; fi OB 0%nat; fi OG 1%nat;
                    fi OS 2%nat; fi OS 0%nat; fi OS 1%nat;
                    ieval prec eempty (eps_e phm phe); ieval prec eempty (eps_e sgm sge)] in
        Some (ins, map (ieval prec (of_list ins)) merc_terms)
    | _, _, _, _ => None
    end
  else None.

(** The ten numbers the terms are evaluated at, in Mercier.v's slot order. *)
Definition merc_vals (A B G S : block) (phm phe sgm sge : Z) : list R :=
  [torus_int A 0%nat; torus_int A 1%nat; torus_int A 2%nat; torus_int B 0%nat; torus_int G 1%nat;
   torus_int S 2%nat; torus_int S 0%nat; torus_int S 1%nat;
   IZR phm * powerRZ 2 phe; IZR sgm * powerRZ 2 sge].

(** Intervals that each contain the matching real make an environment that
    contains the reals'. *)
Lemma env_ok_list :
  forall (ins : list I.type) (vs : list R),
  Forall2 (fun i v => contains (I.convert i) (Xreal v)) ins vs ->
  env_ok (of_list ins) (mxenv vs).
Proof.
  intros ins vs H n.
  unfold mxenv. rewrite !eget_of_list.
  revert n. induction H as [| i v ins vs Hiv Hall IH]; intros n; simpl.
  - destruct n; rewrite ?I.nai_correct; exact I.
  - destruct n as [| n]; [exact Hiv | apply IH].
Qed.

Lemma eps_encloses :
  forall prec m e, contains (I.convert (ieval prec eempty (eps_e m e))) (Xreal (IZR m * powerRZ 2 e)).
Proof.
  intros prec m e.
  assert (H := ieval_correct prec eempty eempty (eps_e m e) env_ok_nil).
  rewrite xeval_eps_e in H. exact H.
Qed.

Theorem merc_run_correct :
  forall prec A B G S phm phe sgm sge ins Is,
  merc_run prec A B G S phm phe sgm sge = Some (ins, Is) ->
  pc_out (bk_cfg A) = RMercierA /\ pc_out (bk_cfg B) = RMercierB /\
  pc_out (bk_cfg G) = RRadialGeom /\ pc_out (bk_cfg S) = RRadialShear /\
  Forall2 (fun i v => contains (I.convert i) (Xreal v)) ins (merc_vals A B G S phm phe sgm sge) /\
  length Is = 6%nat /\
  forall k, (k < 6)%nat ->
  contains (I.convert (nth k Is I.nai))
    (xeval (mxenv (merc_vals A B G S phm phe sgm sge)) (nth k merc_terms e_dmerc)).
Proof.
  intros prec A B G S phm phe sgm sge ins Is H.
  unfold merc_run in H.
  destruct (merc_outs A B G S) eqn:Ho; [| discriminate].
  destruct (merc_outs_ok A B G S Ho) as (HA & HB & HG & HS).
  destruct (torus prec A) as [OA |] eqn:EA; [| discriminate].
  destruct (torus prec B) as [OB |] eqn:EB; [| discriminate].
  destruct (torus prec G) as [OG |] eqn:EG; [| discriminate].
  destruct (torus prec S) as [OS |] eqn:ES; [| discriminate].
  (* injection would normalize the lists, so the equations are read off with
     beta, iota and the pair projections alone *)
  apply (f_equal (fun o => match o with Some x => x | None => (ins, Is) end)) in H.
  cbv beta iota in H.
  pose proof (f_equal fst H) as H1. pose proof (f_equal snd H) as H2.
  cbn [fst snd] in H1, H2. subst ins Is.
  assert (Hall : Forall2 (fun i v => contains (I.convert i) (Xreal v))
            [fst (nth 0 OA (I.nai, I.nai)); fst (nth 1 OA (I.nai, I.nai)); fst (nth 2 OA (I.nai, I.nai));
             fst (nth 0 OB (I.nai, I.nai)); fst (nth 1 OG (I.nai, I.nai));
             fst (nth 2 OS (I.nai, I.nai)); fst (nth 0 OS (I.nai, I.nai)); fst (nth 1 OS (I.nai, I.nai));
             ieval prec eempty (eps_e phm phe); ieval prec eempty (eps_e sgm sge)]
            (merc_vals A B G S phm phe sgm sge)).
  { unfold merc_vals.
    apply Forall2_cons; [apply (torus_encloses prec A OA EA); lia |].
    apply Forall2_cons; [apply (torus_encloses prec A OA EA); lia |].
    apply Forall2_cons; [apply (torus_encloses prec A OA EA); lia |].
    apply Forall2_cons; [apply (torus_encloses prec B OB EB); lia |].
    apply Forall2_cons; [apply (torus_encloses prec G OG EG); lia |].
    apply Forall2_cons; [apply (torus_encloses prec S OS ES); lia |].
    apply Forall2_cons; [apply (torus_encloses prec S OS ES); lia |].
    apply Forall2_cons; [apply (torus_encloses prec S OS ES); lia |].
    apply Forall2_cons; [apply eps_encloses |].
    apply Forall2_cons; [apply eps_encloses |].
    apply Forall2_nil. }
  refine (conj HA (conj HB (conj HG (conj HS (conj Hall (conj _ _)))))).
  { rewrite length_map. reflexivity. }
  intros k Hk.
  rewrite (nth_map_lt _ _ _ merc_terms k e_dmerc I.nai ltac:(unfold merc_terms; simpl; lia)).
  exact (ieval_correct prec _ _ _ (env_ok_list _ _ Hall)).
Qed.

(* ---------------------------------------------------------------- *)
(* Verdicts                                                          *)

(** A term at most -N 2^q, and a term at least N 2^q. *)
Definition below (prec : F.precision) (X : I.type) (N q : Z) : bool :=
  nonneg (ieval prec (eset 0 eempty X) (Esub (Eneg (Evar 0)) (eps_e N q))).

Definition above (prec : F.precision) (X : I.type) (N q : Z) : bool :=
  nonneg (ieval prec (eset 0 eempty X) (Esub (Evar 0) (eps_e N q))).

Lemma below_correct :
  forall prec X x N q, contains (I.convert X) (Xreal x) -> below prec X N q = true ->
  x <= - (IZR N * powerRZ 2 q).
Proof.
  intros prec X x N q HX Hchk.
  assert (Henv : env_ok (eset 0 eempty X) (eset 0 eempty (Xreal x))).
  { apply env_ok_eset. apply env_ok_nil. exact HX. }
  destruct (nonneg_correct _ _ (ieval_correct prec _ _ (Esub (Eneg (Evar 0)) (eps_e N q)) Henv) Hchk)
    as [r [Hr Hge]].
  cbn [xeval] in Hr. rewrite eget_eset_eq, xeval_eps_e in Hr. simpl in Hr.
  injection Hr as <-. lra.
Qed.

Lemma above_correct :
  forall prec X x N q, contains (I.convert X) (Xreal x) -> above prec X N q = true ->
  IZR N * powerRZ 2 q <= x.
Proof.
  intros prec X x N q HX Hchk.
  assert (Henv : env_ok (eset 0 eempty X) (eset 0 eempty (Xreal x))).
  { apply env_ok_eset. apply env_ok_nil. exact HX. }
  destruct (nonneg_correct _ _ (ieval_correct prec _ _ (Esub (Evar 0) (eps_e N q)) Henv) Hchk)
    as [r [Hr Hge]].
  cbn [xeval] in Hr. rewrite eget_eset_eq, xeval_eps_e in Hr. simpl in Hr.
  injection Hr as <-. lra.
Qed.

(** A run whose DMerc lies below -N 2^q proves the surface Mercier unstable
    by that margin: the criterion of the reconstruction's integrals is a real
    number there, and it is at most -N 2^q. *)
Theorem merc_unstable :
  forall prec A B G S phm phe sgm sge ins Is N q,
  merc_run prec A B G S phm phe sgm sge = Some (ins, Is) ->
  below prec (nth 5 Is I.nai) N q = true ->
  exists d, xeval (mxenv (merc_vals A B G S phm phe sgm sge)) e_dmerc = Xreal d /\
            d <= - (IZR N * powerRZ 2 q).
Proof.
  intros prec A B G S phm phe sgm sge ins Is N q H Hb.
  destruct (merc_run_correct prec A B G S phm phe sgm sge ins Is H) as (_ & _ & _ & _ & _ & _ & Hk).
  pose proof (Hk 5%nat ltac:(lia)) as H5. cbn [nth merc_terms] in H5.
  destruct (xeval (mxenv (merc_vals A B G S phm phe sgm sge)) e_dmerc) as [| d] eqn:Hd.
  - unfold below in Hb.
    assert (Henv : env_ok (eset 0 eempty (nth 5 Is I.nai)) (eset 0 eempty Xnan)).
    { apply env_ok_eset. apply env_ok_nil. exact H5. }
    destruct (nonneg_correct _ _ (ieval_correct prec _ _ (Esub (Eneg (Evar 0)) (eps_e N q)) Henv) Hb)
      as [r [Hr _]].
    cbn [xeval] in Hr. rewrite eget_eset_eq in Hr. simpl in Hr. discriminate.
  - exists d. split; [reflexivity |]. exact (below_correct prec _ d N q H5 Hb).
Qed.

(** And one whose DMerc lies above N 2^q proves it stable by that margin. *)
Theorem merc_stable :
  forall prec A B G S phm phe sgm sge ins Is N q,
  merc_run prec A B G S phm phe sgm sge = Some (ins, Is) ->
  above prec (nth 5 Is I.nai) N q = true ->
  exists d, xeval (mxenv (merc_vals A B G S phm phe sgm sge)) e_dmerc = Xreal d /\
            IZR N * powerRZ 2 q <= d.
Proof.
  intros prec A B G S phm phe sgm sge ins Is N q H Hb.
  destruct (merc_run_correct prec A B G S phm phe sgm sge ins Is H) as (_ & _ & _ & _ & _ & _ & Hk).
  pose proof (Hk 5%nat ltac:(lia)) as H5. cbn [nth merc_terms] in H5.
  destruct (xeval (mxenv (merc_vals A B G S phm phe sgm sge)) e_dmerc) as [| d] eqn:Hd.
  - unfold above in Hb.
    assert (Henv : env_ok (eset 0 eempty (nth 5 Is I.nai)) (eset 0 eempty Xnan)).
    { apply env_ok_eset. apply env_ok_nil. exact H5. }
    destruct (nonneg_correct _ _ (ieval_correct prec _ _ (Esub (Evar 0) (eps_e N q)) Henv) Hb)
      as [r [Hr _]].
    cbn [xeval] in Hr. rewrite eget_eset_eq in Hr. simpl in Hr. discriminate.
  - exists d. split; [reflexivity |]. exact (above_correct prec _ d N q H5 Hb).
Qed.
