(** Integrals over the angular torus that need no quadrature error.

    [check_harm] reads a component of the residual whose degree analysis
    (TrigExpr.v) puts it below the point counts of an equispaced grid, and
    evaluates it at the points of the grid over a box of states.
    [harm_correct] states that a passing verdict makes the integral of the
    component over the torus exist and lie in [harm_total], at every state of
    the box: the grid sum is the integral exactly, by [TrigPoly.exact2], so the
    only width left is that of the interval arithmetic over the box. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Quad Box TrigPoly
     TrigExpr Integral.

Import ListNotations.

Local Open Scope R_scope.

Open Scope Z_scope.

(** The state, the two angle slots, the component, and the number of points
    along each angle. *)
Record hcert := HCert {
  hc_prec : Z ;
  hc_cfg : pconfig ;
  hc_modes : list (Z * Z) ;
  hc_es : list Z ;
  hc_ms : list Z ;
  hc_ds : list Z ;
  hc_su : nat ; hc_sv : nat ;
  hc_comp : nat ;
  hc_Nu : nat ; hc_Nv : nat }.

Definition hprec_of (c : hcert) : F.precision := F.PtoP (Z.to_pos (hc_prec c)).
Definition hres (c : hcert) : residual3 := residual (hc_es c) (hc_cfg c) (hc_modes c).
Definition hbase (c : hcert) : nat :=
  base_scratch_of (pc_lasym (hc_cfg c)) (pc_out (hc_cfg c)) (length (hc_modes c)).
Definition hcomp (r3 : residual3) (k : nat) : expr :=
  match k with O => r_s r3 | 1%nat => r_u r3 | _ => r_v r3 end.

(** The mantissa of the angle of point j of N: 2 pi j / N in units of 2^e. *)
Definition angle_e (N j : nat) (e : Z) : expr :=
  Ediv (Emul (Emul (EfromZ 2) Epi) (EfromZ (Z.of_nat j)))
       (Emul (EfromZ (Z.of_nat N)) (Epow2 e)).

Definition angle_i (prec : F.precision) (N j : nat) (e : Z) : I.type :=
  ieval prec eempty (angle_e N j e).

(** The component at the point (j, l) of the grid, over the box. *)
Definition hpoint (prec : F.precision) (W : env I.type) (su sv : nat) (eu ev : Z)
    (Nu Nv : nat) (binds : list binding) (n : nat) (j l : nat) : I.type :=
  ieval prec
    (iextend prec (eset su (eset sv W (angle_i prec Nv l ev)) (angle_i prec Nu j eu)) binds)
    (Evar n).

(** Row l of the grid, summed along the first angle. *)
Definition hrow (prec : F.precision) (W : env I.type) (su sv : nat) (eu ev : Z)
    (Nu Nv : nat) (binds : list binding) (n : nat) (l : nat) : I.type :=
  isum prec (map (fun j => hpoint prec W su sv eu ev Nu Nv binds n j l) (seq 0 Nu)).

(** The weight of a point: (2 pi / Nu) (2 pi / Nv). *)
Definition hweight_e (Nu Nv : nat) : expr :=
  Emul (Ediv (Emul (EfromZ 2) Epi) (EfromZ (Z.of_nat Nu)))
       (Ediv (Emul (EfromZ 2) Epi) (EfromZ (Z.of_nat Nv))).

(** The rows of the grid, each summed. The residual and the box are built
    once. *)
Definition harm_rows (c : hcert) : list I.type :=
  let prec := hprec_of c in
  let r3 := hres c in
  let binds := r_binds r3 in
  let su := hc_su c in let sv := hc_sv c in
  let eu := nth su (hc_es c) 0 in let ev := nth sv (hc_es c) 0 in
  let W := wide_ienv prec (hc_ms c) (hc_ds c) in
  match slot_of (hcomp r3 (hc_comp c)) with
  | None => []
  | Some n =>
      map (fun l => hrow prec W su sv eu ev (hc_Nu c) (hc_Nv c) binds n l)
          (seq 0 (hc_Nv c))
  end.

(** The enclosure of the integral over the torus. *)
Definition harm_total (c : hcert) : I.type :=
  let prec := hprec_of c in
  I.mul prec (isum prec (harm_rows c)) (ieval prec eempty (hweight_e (hc_Nu c) (hc_Nv c))).

(** The layout, the angle slots, and a degree below the point counts. *)
Definition harm_struct (c : hcert) : bool :=
  let r3 := hres c in
  let binds := r_binds r3 in
  let su := hc_su c in let sv := hc_sv c in
  let eu := nth su (hc_es c) 0 in let ev := nth sv (hc_es c) 0 in
  let base := hbase c in
  match slot_of (hcomp r3 (hc_comp c)) with
  | None => false
  | Some n =>
      Nat.eqb (length (hc_ms c)) base &&
      negb (Nat.eqb su sv) && Nat.ltb su base && Nat.ltb sv base &&
      well_formed base binds &&
      match eget n (tdeg_binds su sv base eu ev eempty binds) None with
      | Some d => Nat.ltb (fst d) (hc_Nu c) && Nat.ltb (snd d) (hc_Nv c)
      | None => false
      end
  end.

(** An enclosure is bounded when it is not the whole line. One bounded point
    makes the component real there at every state of the box, and the degree
    analysis makes it real at every angle or at none, so one point is enough. *)
Definition bounded (x : I.type) : bool := I.bounded x.

Definition harm_first (c : hcert) : I.type :=
  let prec := hprec_of c in
  let r3 := hres c in
  let binds := r_binds r3 in
  let su := hc_su c in let sv := hc_sv c in
  let eu := nth su (hc_es c) 0 in let ev := nth sv (hc_es c) 0 in
  let W := wide_ienv prec (hc_ms c) (hc_ds c) in
  match slot_of (hcomp r3 (hc_comp c)) with
  | None => I.nai
  | Some n => hpoint prec W su sv eu ev (hc_Nu c) (hc_Nv c) binds n 0 0
  end.

Definition check_harm (c : hcert) : bool :=
  harm_struct c && Nat.ltb 0 (hc_Nu c) && Nat.ltb 0 (hc_Nv c) &&
  bounded (harm_first c).

Close Scope Z_scope.

(** The component as a function of the two angles in radians, at a state. *)
Definition harm_fun (c : hcert) (xs : list R) (U V : R) : R :=
  match slot_of (hcomp (hres c) (hc_comp c)) with
  | None => 0
  | Some n =>
      proj_val (eget n (xextend (at_angles (hc_su c) (hc_sv c)
                                   (nth (hc_su c) (hc_es c) 0%Z)
                                   (nth (hc_sv c) (hc_es c) 0%Z) (xenv_R xs) U V)
                                (r_binds (hres c))) Xnan)
  end.

Definition harm_value (c : hcert) (xs : list R) : R :=
  RInt (fun V => RInt (fun U => harm_fun c xs U V) 0 (0 + 2 * PI)) 0 (0 + 2 * PI).

(* ---------------------------------------------------------------- *)
(* Soundness                                                         *)

Lemma xeval_angle :
  forall N j e, (0 < N)%nat ->
  xeval eempty (angle_e N j e) = Xreal (node N 0 j / powerRZ 2 e).
Proof.
  intros N j e HN.
  assert (HN' : INR N <> 0) by (apply not_0_INR; lia).
  assert (Hp := powerRZ_2_neq e).
  change (xeval eempty (angle_e N j e))
    with (Xdiv (Xreal (2 * PI * IZR (Z.of_nat j)))
               (Xreal (IZR (Z.of_nat N) * powerRZ 2 e))).
  rewrite <- !INR_IZR_INZ. cbn [Xbind2]. unfold Xdiv'.
  destruct (is_zero_spec (INR N * powerRZ 2 e)) as [Hz|Hz].
  - exfalso. apply Rmult_integral in Hz. destruct Hz; contradiction.
  - f_equal. unfold node. field. split; assumption.
Qed.

Lemma angle_ok :
  forall prec N j e, (0 < N)%nat ->
  contains (I.convert (angle_i prec N j e)) (Xreal (node N 0 j / powerRZ 2 e)).
Proof.
  intros prec N j e HN. unfold angle_i. rewrite <- xeval_angle by exact HN.
  apply ieval_correct. apply env_ok_nil.
Qed.

Lemma xeval_hweight :
  forall Nu Nv, (0 < Nu)%nat -> (0 < Nv)%nat ->
  xeval eempty (hweight_e Nu Nv) = Xreal ((2 * PI / INR Nu) * (2 * PI / INR Nv)).
Proof.
  intros Nu Nv Hu Hv.
  assert (Hu' : INR Nu <> 0) by (apply not_0_INR; lia).
  assert (Hv' : INR Nv <> 0) by (apply not_0_INR; lia).
  change (xeval eempty (hweight_e Nu Nv))
    with (Xmul (Xdiv (Xreal (2 * PI)) (Xreal (IZR (Z.of_nat Nu))))
               (Xdiv (Xreal (2 * PI)) (Xreal (IZR (Z.of_nat Nv))))).
  rewrite <- !INR_IZR_INZ. cbn [Xbind2]. unfold Xdiv'.
  destruct (is_zero_spec (INR Nu)) as [H|H]; [contradiction|].
  destruct (is_zero_spec (INR Nv)) as [H'|H']; [contradiction|].
  reflexivity.
Qed.

(** A bounded enclosure holds a real. *)
Lemma bounded_real :
  forall x v, bounded x = true -> contains (I.convert x) v -> exists r, v = Xreal r.
Proof.
  intros x v Hb Hc. unfold bounded in Hb.
  destruct v as [|r]; [|now exists r].
  exfalso.
  destruct (I.bounded_correct x Hb) as [Hl _].
  destruct (I.lower_bounded_correct x Hl) as [_ Hp].
  unfold I.bounded_prop in Hp.
  assert (Hne : not_empty (I.convert x)).
  { revert Hc. destruct (I.convert x) as [|lo hi]; intros Hc.
    - exists 0%R. exact I.
    - simpl in Hc. contradiction. }
  rewrite (Hp Hne) in Hc. simpl in Hc. exact Hc.
Qed.

Lemma nth_map_seq_gen :
  forall (A : Type) (g : nat -> A) N k d, (k < N)%nat -> nth k (map g (seq 0 N)) d = g k.
Proof.
  intros A g N k d Hk.
  rewrite (nth_indep _ d (g O)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

(** The grid point (j, l) of the box contains the state at those angles. *)
Lemma hpoint_ok :
  forall prec ms ds xs su sv eu ev Nu Nv binds n j l,
  in_box ms ds xs -> (0 < Nu)%nat -> (0 < Nv)%nat ->
  contains (I.convert (hpoint prec (wide_ienv prec ms ds) su sv eu ev Nu Nv binds n j l))
           (eget n (xextend (at_angles su sv eu ev (xenv_R xs) (node Nu 0 j) (node Nv 0 l))
                            binds) Xnan).
Proof.
  intros prec ms ds xs su sv eu ev Nu Nv binds n j l Hin Hu Hv. unfold hpoint.
  change (eget n (xextend (at_angles su sv eu ev (xenv_R xs) (node Nu 0 j) (node Nv 0 l))
                          binds) Xnan)
    with (xeval (xextend (at_angles su sv eu ev (xenv_R xs) (node Nu 0 j) (node Nv 0 l))
                         binds) (Evar n)).
  apply ieval_correct. apply iextend_correct. unfold at_angles.
  apply env_ok_eset.
  - apply env_ok_eset. now apply wide_env_ok. now apply angle_ok.
  - now apply angle_ok.
Qed.

(** The double sum of the rule, regrouped as the checker groups it. *)
Lemma dsum2_rows :
  forall Nu Nv F,
  dsum2 Nu Nv 0 0 F
  = rsum (fun l => rsum (fun j => F (node Nu 0 j) (node Nv 0 l)) Nu) Nv
    * ((2 * PI / INR Nu) * (2 * PI / INR Nv)).
Proof.
  intros Nu Nv F. unfold dsum2, dsum1. cbv beta.
  rewrite (rsum_ext (fun l => rsum (fun j => F (node Nu 0 j) (node Nv 0 l)) Nu
                              * (2 * PI / INR Nu))
                    (fun l => (2 * PI / INR Nu)
                              * rsum (fun j => F (node Nu 0 j) (node Nv 0 l)) Nu))
    by (intros l; ring).
  rewrite rsum_scal. ring.
Qed.

(* ---------------------------------------------------------------- *)
(* The discrete harmonic over a box                                  *)

(** Without the degree bound the grid sum is still a certified quantity: the
    equispaced rule's harmonic of the component, which is what
    Project.harm_encloses computes for one state and gen/resonance.py tabulates.
    A floor on it at every state of a box says that no state there balances
    the force, since a sum of values that are all zero is zero. *)
Definition check_dharm (c : hcert) : bool :=
  match slot_of (hcomp (hres c) (hc_comp c)) with None => false | Some _ => true end
  && Nat.ltb 0 (hc_Nu c) && Nat.ltb 0 (hc_Nv c).

Theorem dharm_correct :
  forall c, check_dharm c = true ->
  forall xs, in_box (hc_ms c) (hc_ds c) xs ->
  contains (I.convert (harm_total c))
           (Xreal (dsum2 (hc_Nu c) (hc_Nv c) 0 0 (harm_fun c xs))).
Proof.
  intros c Hchk xs Hin.
  unfold check_dharm in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hchk HNv].
  apply andb_prop in Hchk. destruct Hchk as [Hs HNu].
  apply Nat.ltb_lt in HNu, HNv.
  unfold harm_total, harm_rows, harm_fun in *.
  cbv zeta in *.
  revert Hs.
  destruct (slot_of (hcomp (hres c) (hc_comp c))) as [n|] eqn:Hn; intros Hs; [|discriminate].
  set (prec := hprec_of c) in *.
  set (binds := r_binds (hres c)) in *.
  set (su := hc_su c) in *. set (sv := hc_sv c) in *.
  set (eu := nth su (hc_es c) 0%Z) in *. set (ev := nth sv (hc_es c) 0%Z) in *.
  set (W := wide_ienv prec (hc_ms c) (hc_ds c)) in *.
  set (X := xenv_R xs) in *.
  set (F := fun U V => proj_val (eget n (xextend (at_angles su sv eu ev X U V) binds) Xnan)).
  change (contains (I.convert (I.mul prec
            (isum prec (map (fun l => hrow prec W su sv eu ev (hc_Nu c) (hc_Nv c) binds n l)
                            (seq 0 (hc_Nv c))))
            (ieval prec eempty (hweight_e (hc_Nu c) (hc_Nv c)))))
          (Xreal (dsum2 (hc_Nu c) (hc_Nv c) 0 0 F))).
  rewrite dsum2_rows.
  change (Xreal (rsum (fun l => rsum (fun j => F (node (hc_Nu c) 0 j)
                                                (node (hc_Nv c) 0 l)) (hc_Nu c))
                      (hc_Nv c)
                 * ((2 * PI / INR (hc_Nu c)) * (2 * PI / INR (hc_Nv c)))))
    with (Xmul (Xreal (rsum (fun l => rsum (fun j => F (node (hc_Nu c) 0 j)
                                                      (node (hc_Nv c) 0 l)) (hc_Nu c))
                            (hc_Nv c)))
               (Xreal ((2 * PI / INR (hc_Nu c)) * (2 * PI / INR (hc_Nv c))))).
  apply I.mul_correct.
  - rewrite <- fold_seq_rsum.
    apply isum_correct. { now rewrite !length_map, !length_seq. }
    intros l Hl. rewrite length_map, length_seq in Hl.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hl), (nth_map_seq_gen _ _ _ _ _ Hl).
    unfold hrow. rewrite <- fold_seq_rsum.
    apply isum_correct. { now rewrite !length_map, !length_seq. }
    intros j Hj. rewrite length_map, length_seq in Hj.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hj), (nth_map_seq_gen _ _ _ _ _ Hj).
    unfold F. apply contains_proj.
    exact (hpoint_ok prec (hc_ms c) (hc_ds c) xs su sv eu ev (hc_Nu c) (hc_Nv c)
             binds n j l Hin HNu HNv).
  - rewrite <- xeval_hweight by assumption.
    apply ieval_correct. apply env_ok_nil.
Qed.

(** A passing verdict encloses the integral of the component over the angular
    torus, at every state of the box, and the integral exists. *)
Theorem harm_correct :
  forall c, check_harm c = true ->
  forall xs, in_box (hc_ms c) (hc_ds c) xs ->
  ex_RInt (fun V => RInt (fun U => harm_fun c xs U V) 0 (0 + 2 * PI)) 0 (0 + 2 * PI) /\
  contains (I.convert (harm_total c)) (Xreal (harm_value c xs)).
Proof.
  intros c Hchk xs Hin.
  unfold check_harm in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hchk Hfirst].
  apply andb_prop in Hchk. destruct Hchk as [Hchk HNv].
  apply andb_prop in Hchk. destruct Hchk as [Hstruct HNu].
  apply Nat.ltb_lt in HNu, HNv.
  unfold harm_struct, harm_first, harm_total, harm_rows, harm_value, harm_fun in *.
  cbv zeta in *.
  revert Hstruct Hfirst.
  destruct (slot_of (hcomp (hres c) (hc_comp c))) as [n|] eqn:Hn;
    intros Hstruct Hfirst; [|discriminate].
  set (prec := hprec_of c) in *.
  set (binds := r_binds (hres c)) in *.
  set (su := hc_su c) in *. set (sv := hc_sv c) in *.
  set (eu := nth su (hc_es c) 0%Z) in *. set (ev := nth sv (hc_es c) 0%Z) in *.
  set (W := wide_ienv prec (hc_ms c) (hc_ds c)) in *.
  set (X := xenv_R xs) in *.
  revert Hstruct.
  destruct (eget n (tdeg_binds su sv (hbase c) eu ev eempty binds) None) as [d|] eqn:Hdeg;
    intros Hstruct; [|now rewrite andb_false_r in Hstruct].
  apply andb_prop in Hstruct. destruct Hstruct as [Hstruct Hdd].
  apply andb_prop in Hdd. destruct Hdd as [Hdu Hdv]. apply Nat.ltb_lt in Hdu, Hdv.
  apply andb_prop in Hstruct. destruct Hstruct as [Hstruct Hwf].
  apply andb_prop in Hstruct. destruct Hstruct as [Hstruct Hsv].
  apply andb_prop in Hstruct. destruct Hstruct as [Hstruct Hsu].
  apply andb_prop in Hstruct. destruct Hstruct as [Hms Huv].
  apply Nat.ltb_lt in Hsu, Hsv. apply negb_true_iff, Nat.eqb_neq in Huv.
  set (E := fun U V => eget n (xextend (at_angles su sv eu ev X U V) binds) Xnan).
  (* the component is a good family of the degree the analysis gives *)
  assert (Hgood : good d E).
  { exact (tdeg_binds_sound su sv (hbase c) eu ev X Hsu Hsv Huv binds n d Hwf Hdeg). }
  (* real at the first point, hence everywhere *)
  assert (Hreal : forall U V, exists r, E U V = Xreal r).
  { destruct Hgood as [[Hr|Hnan] _]. exact Hr.
    exfalso.
    assert (Hc := hpoint_ok prec (hc_ms c) (hc_ds c) xs su sv eu ev (hc_Nu c) (hc_Nv c)
                    binds n 0 0 Hin HNu HNv).
    destruct (bounded_real _ _ Hfirst Hc) as [r Hr].
    change (E (node (hc_Nu c) 0 0) (node (hc_Nv c) 0 0) = Xreal r) in Hr.
    rewrite Hnan in Hr. discriminate. }
  assert (HTP := proj2 Hgood Hreal).
  set (F := fun U V => proj_val (E U V)).
  destruct (exact2 (fst d) (snd d) (hc_Nu c) (hc_Nv c) 0 0 F HTP Hdu Hdv) as [Hex Heq].
  enough (Hgoal :
    ex_RInt (fun V => RInt (fun U => F U V) 0 (0 + 2 * PI)) 0 (0 + 2 * PI) /\
    contains (I.convert (I.mul prec
                (isum prec (map (fun l => hrow prec W su sv eu ev (hc_Nu c) (hc_Nv c)
                                             binds n l) (seq 0 (hc_Nv c))))
                (ieval prec eempty (hweight_e (hc_Nu c) (hc_Nv c)))))
             (Xreal (RInt (fun V => RInt (fun U => F U V) 0 (0 + 2 * PI)) 0 (0 + 2 * PI))))
    by exact Hgoal.
  split. exact Hex.
  rewrite Heq, dsum2_rows.
  change (Xreal (rsum (fun l => rsum (fun j => F (node (hc_Nu c) 0 j)
                                                (node (hc_Nv c) 0 l)) (hc_Nu c))
                      (hc_Nv c)
                 * ((2 * PI / INR (hc_Nu c)) * (2 * PI / INR (hc_Nv c)))))
    with (Xmul (Xreal (rsum (fun l => rsum (fun j => F (node (hc_Nu c) 0 j)
                                                      (node (hc_Nv c) 0 l)) (hc_Nu c))
                            (hc_Nv c)))
               (Xreal ((2 * PI / INR (hc_Nu c)) * (2 * PI / INR (hc_Nv c))))).
  apply I.mul_correct.
  - rewrite <- fold_seq_rsum.
    apply isum_correct. { now rewrite !length_map, !length_seq. }
    intros l Hl. rewrite length_map, length_seq in Hl.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hl), (nth_map_seq_gen _ _ _ _ _ Hl).
    unfold hrow. rewrite <- fold_seq_rsum.
    apply isum_correct. { now rewrite !length_map, !length_seq. }
    intros j Hj. rewrite length_map, length_seq in Hj.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hj), (nth_map_seq_gen _ _ _ _ _ Hj).
    unfold F, E. apply contains_proj.
    exact (hpoint_ok prec (hc_ms c) (hc_ds c) xs su sv eu ev (hc_Nu c) (hc_Nv c)
             binds n j l Hin HNu HNv).
  - rewrite <- xeval_hweight by assumption.
    apply ieval_correct. apply env_ok_nil.
Qed.
