(** The discrete harmonic of Harmonic.v at one state, in intervals over floats
    of any precision.

    [Harmonic.dharm_correct] encloses the equispaced sum of a component over a
    grid of angles in binary64 intervals, whose rounding the second radial
    differences of the residual amplify by h^-2. [wharm_total] computes the
    same sum in the intervals of Wide.v at a precision the caller chooses, at
    the state whose slots are the certificate's mantissas, and
    [wdharm_correct] states that it encloses the sum. *)

From Coq Require Import ZArith Reals List Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Cell Box Integral Integrate Quad TrigPoly
  TrigExpr Harmonic Wide.

Import ListNotations.
Local Open Scope R_scope.

Section WideHarm.

Variable wprec : WF.precision.

(** The angle of point j of N, in units of 2^e. *)
Definition wangle (N j : nat) (e : Z) : WI.type := weval wprec eempty (angle_e N j e).

(** The component at the point (j, l) of the grid. *)
Definition whpoint (W : env WI.type) (su sv : nat) (eu ev : Z) (Nu Nv : nat)
    (binds : list binding) (n j l : nat) : WI.type :=
  weval wprec (wextend wprec (eset su (eset sv W (wangle Nv l ev)) (wangle Nu j eu)) binds)
        (Evar n).

Definition wsum (l : list WI.type) : WI.type :=
  fold_right (fun x acc => WI.add wprec x acc) WI.zero l.

(** Row l of the grid, summed along the first angle. *)
Definition whrow (W : env WI.type) (su sv : nat) (eu ev : Z) (Nu Nv : nat)
    (binds : list binding) (n l : nat) : WI.type :=
  wsum (map (fun j => whpoint W su sv eu ev Nu Nv binds n j l) (seq 0 Nu)).

(** The enclosure of the equispaced sum at the certificate's own state. *)
Definition wharm_total (c : hcert) : WI.type :=
  let binds := r_binds (hres c) in
  let su := hc_su c in let sv := hc_sv c in
  let eu := nth su (hc_es c) 0%Z in let ev := nth sv (hc_es c) 0%Z in
  let W := wenv_of wprec (hc_ms c) in
  match slot_of (hcomp (hres c) (hc_comp c)) with
  | None => WI.nai
  | Some n =>
      WI.mul wprec
        (wsum (map (fun l => whrow W su sv eu ev (hc_Nu c) (hc_Nv c) binds n l)
                   (seq 0 (hc_Nv c))))
        (weval wprec eempty (hweight_e (hc_Nu c) (hc_Nv c)))
  end.

Lemma wenv_ok_empty : wenv_ok (eempty : env WI.type) (eempty : env ExtendedR).
Proof.
  intros n. unfold eget, eempty. rewrite !FMapPositive.PositiveMap.gempty.
  rewrite WI.nai_correct. exact I.
Qed.

Lemma wangle_ok :
  forall N j e, (0 < N)%nat ->
  contains (WI.convert (wangle N j e)) (Xreal (node N 0 j / powerRZ 2 e)).
Proof.
  intros N j e HN. unfold wangle. rewrite <- xeval_angle by exact HN.
  apply weval_correct. apply wenv_ok_empty.
Qed.

Lemma wsum_correct :
  forall l (vs : list R),
  length l = length vs ->
  (forall k, (k < length l)%nat ->
     contains (WI.convert (nth k l WI.nai)) (Xreal (nth k vs 0))) ->
  contains (WI.convert (wsum l)) (Xreal (fold_right Rplus 0 vs)).
Proof.
  induction l as [|x l IH]; intros [|v vs] Hlen Hk; simpl in Hlen; try discriminate.
  - unfold wsum. cbn [fold_right]. rewrite WI.zero_correct. simpl. lra.
  - simpl. change (Xreal (v + fold_right Rplus 0 vs))
      with (Xadd (Xreal v) (Xreal (fold_right Rplus 0 vs))).
    apply WI.add_correct.
    + exact (Hk 0%nat ltac:(simpl; lia)).
    + apply IH. { lia. }
      intros k Hk'. exact (Hk (S k) ltac:(simpl; lia)).
Qed.

Lemma xenv_of_R : forall ms, xenv_of ms = xenv_R (map IZR ms).
Proof. intros ms. unfold xenv_of, xenv_R. now rewrite map_map. Qed.

(** The grid point (j, l) at the certificate's state. *)
Lemma whpoint_ok :
  forall ms su sv eu ev Nu Nv binds n j l,
  (0 < Nu)%nat -> (0 < Nv)%nat ->
  contains (WI.convert (whpoint (wenv_of wprec ms) su sv eu ev Nu Nv binds n j l))
           (eget n (xextend (at_angles su sv eu ev (xenv_R (map IZR ms))
                                       (node Nu 0 j) (node Nv 0 l)) binds) Xnan).
Proof.
  intros ms su sv eu ev Nu Nv binds n j l Hu Hv. unfold whpoint.
  change (eget n (xextend (at_angles su sv eu ev (xenv_R (map IZR ms))
                                     (node Nu 0 j) (node Nv 0 l)) binds) Xnan)
    with (xeval (xextend (at_angles su sv eu ev (xenv_R (map IZR ms))
                                    (node Nu 0 j) (node Nv 0 l)) binds) (Evar n)).
  apply weval_correct. apply wextend_correct. unfold at_angles.
  apply wenv_ok_eset.
  - apply wenv_ok_eset.
    + rewrite <- xenv_of_R. apply wenv_ok_fromZ.
    + now apply wangle_ok.
  - now apply wangle_ok.
Qed.

(** A passing [check_dharm] makes [wharm_total] enclose the equispaced sum of
    the component at the certificate's state. *)
Theorem wdharm_correct :
  forall c, check_dharm c = true ->
  contains (WI.convert (wharm_total c))
           (Xreal (dsum2 (hc_Nu c) (hc_Nv c) 0 0 (harm_fun c (map IZR (hc_ms c))))).
Proof.
  intros c Hchk.
  unfold check_dharm in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hchk HNv].
  apply andb_prop in Hchk. destruct Hchk as [Hs HNu].
  apply Nat.ltb_lt in HNu, HNv.
  unfold wharm_total, harm_fun in *.
  cbv zeta in *.
  revert Hs.
  destruct (slot_of (hcomp (hres c) (hc_comp c))) as [n|] eqn:Hn; intros Hs; [|discriminate].
  set (binds := r_binds (hres c)) in *.
  set (su := hc_su c) in *. set (sv := hc_sv c) in *.
  set (eu := nth su (hc_es c) 0%Z) in *. set (ev := nth sv (hc_es c) 0%Z) in *.
  set (X := xenv_R (map IZR (hc_ms c))) in *.
  set (F := fun U V => proj_val (eget n (xextend (at_angles su sv eu ev X U V) binds) Xnan)).
  change (contains (WI.convert (WI.mul wprec
            (wsum (map (fun l => whrow (wenv_of wprec (hc_ms c)) su sv eu ev
                                       (hc_Nu c) (hc_Nv c) binds n l)
                       (seq 0 (hc_Nv c))))
            (weval wprec eempty (hweight_e (hc_Nu c) (hc_Nv c)))))
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
  apply WI.mul_correct.
  - rewrite <- fold_seq_rsum.
    apply wsum_correct. { now rewrite !length_map, !length_seq. }
    intros l Hl. rewrite length_map, length_seq in Hl.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hl), (nth_map_seq_gen _ _ _ _ _ Hl).
    unfold whrow. rewrite <- fold_seq_rsum.
    apply wsum_correct. { now rewrite !length_map, !length_seq. }
    intros j Hj. rewrite length_map, length_seq in Hj.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hj), (nth_map_seq_gen _ _ _ _ _ Hj).
    unfold F. apply Integrate.contains_proj.
    exact (whpoint_ok (hc_ms c) su sv eu ev (hc_Nu c) (hc_Nv c) binds n j l HNu HNv).
  - rewrite <- xeval_hweight by assumption.
    apply weval_correct. apply wenv_ok_empty.
Qed.

(** Row l summed in the wide intervals and narrowed to binary64, and the sum of
    the narrowed rows times the weight in binary64: the form the checker's
    processes compute a row at a time. *)
Definition wharm_row (prec : F.precision) (c : hcert) (l : nat) : I.type :=
  let su := hc_su c in let sv := hc_sv c in
  match slot_of (hcomp (hres c) (hc_comp c)) with
  | None => I.nai
  | Some n =>
      narrow prec (whrow (wenv_of wprec (hc_ms c)) su sv (nth su (hc_es c) 0%Z)
                         (nth sv (hc_es c) 0%Z) (hc_Nu c) (hc_Nv c) (r_binds (hres c)) n l)
  end.

Definition wharm_total_b (prec : F.precision) (c : hcert) : I.type :=
  I.mul prec (isum prec (map (wharm_row prec c) (seq 0 (hc_Nv c))))
        (ieval prec eempty (hweight_e (hc_Nu c) (hc_Nv c))).

Theorem wdharm_b_correct :
  forall prec c, check_dharm c = true ->
  contains (I.convert (wharm_total_b prec c))
           (Xreal (dsum2 (hc_Nu c) (hc_Nv c) 0 0 (harm_fun c (map IZR (hc_ms c))))).
Proof.
  intros prec c Hchk.
  unfold check_dharm in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hchk HNv].
  apply andb_prop in Hchk. destruct Hchk as [Hs HNu].
  apply Nat.ltb_lt in HNu, HNv.
  unfold wharm_total_b, wharm_row, harm_fun in *.
  cbv zeta in *.
  revert Hs.
  destruct (slot_of (hcomp (hres c) (hc_comp c))) as [n|] eqn:Hn; intros Hs; [|discriminate].
  set (binds := r_binds (hres c)) in *.
  set (su := hc_su c) in *. set (sv := hc_sv c) in *.
  set (eu := nth su (hc_es c) 0%Z) in *. set (ev := nth sv (hc_es c) 0%Z) in *.
  set (X := xenv_R (map IZR (hc_ms c))) in *.
  set (F := fun U V => proj_val (eget n (xextend (at_angles su sv eu ev X U V) binds) Xnan)).
  change (Xreal (dsum2 (hc_Nu c) (hc_Nv c) 0 0 F))
    with (Xreal (dsum2 (hc_Nu c) (hc_Nv c) 0 0 F)).
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
    apply narrow_correct.
    unfold whrow. rewrite <- fold_seq_rsum.
    apply wsum_correct. { now rewrite !length_map, !length_seq. }
    intros j Hj. rewrite length_map, length_seq in Hj.
    rewrite (nth_map_seq_gen _ _ _ _ _ Hj), (nth_map_seq_gen _ _ _ _ _ Hj).
    unfold F. apply Integrate.contains_proj.
    exact (whpoint_ok (hc_ms c) su sv eu ev (hc_Nu c) (hc_Nv c) binds n j l HNu HNv).
  - rewrite <- xeval_hweight by assumption.
    apply ieval_correct. apply env_ok_nil.
Qed.

End WideHarm.
