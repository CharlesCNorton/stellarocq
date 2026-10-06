(** States over a box of inputs.

    Every other certificate evaluates at a point: its inputs are the exact
    images of one wout file's doubles, and the only slots with width are the
    angles or the radius a cell ranges over. Here every input slot carries a
    half-width of its own, so one interval evaluation covers every state whose
    coefficients lie in the box, and a verdict is a statement about all of
    them at once.

    That is the form a statement about a neighbourhood of an equilibrium
    takes. A floor certified over the box holds for every field the
    reconstruction can write with coefficients there, so it cannot be an
    accident of the one state a solver stopped at: the true discrete solution,
    wherever it sits inside the box, is covered with the rest.

    The interval evaluation of a box is the natural extension, so its width
    grows with the box and with the cancellation the expression carries. A
    box is therefore narrow compared with the coefficients, and how narrow is
    reported with every verdict rather than chosen here. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell.

Import ListNotations.

Open Scope Z_scope.

(* ---------------------------------------------------------------- *)
(* The interval of every slot                                        *)

(** Slot k spans the mantissas m_k - d_k .. m_k + d_k. A list of half-widths
    shorter than the list of mantissas leaves the remaining slots as points. *)
Fixpoint zipbox (prec : F.precision) (ms ds : list Z) : list I.type :=
  match ms with
  | [] => []
  | m :: mt =>
      match ds with
      | [] => slot_box prec m 0 :: zipbox prec mt []
      | d :: dt => slot_box prec m d :: zipbox prec mt dt
      end
  end.

Lemma zipbox_length :
  forall prec ms ds, length (zipbox prec ms ds) = length ms.
Proof.
  intros prec ms. induction ms as [|m mt IH]; intros ds; simpl. reflexivity.
  destruct ds; simpl; now rewrite IH.
Qed.

Lemma zipbox_nth :
  forall prec ms ds k, (k < length ms)%nat ->
  nth k (zipbox prec ms ds) I.nai = slot_box prec (nth k ms 0) (nth k ds 0).
Proof.
  intros prec ms. induction ms as [|m mt IH]; intros ds k Hk; simpl in Hk.
  - lia.
  - destruct ds as [|d dt]; destruct k as [|k]; simpl; try reflexivity.
    + rewrite IH by lia. now destruct k.
    + apply IH. lia.
Qed.

(** The interval environment of the box. *)
Definition wide_ienv (prec : F.precision) (ms ds : list Z) : env I.type :=
  of_list (zipbox prec ms ds).

(** The real environment of one state: its slot values, every one real. *)
Definition xenv_R (xs : list R) : env ExtendedR := of_list (map Xreal xs).

(** A state lies in the box when it has a value for every slot and each value
    lies between that slot's endpoints. *)
Definition in_box (ms ds : list Z) (xs : list R) : Prop :=
  length xs = length ms /\
  forall k, (k < length ms)%nat ->
    (IZR (nth k ms 0%Z - nth k ds 0%Z) <= nth k xs 0
     <= IZR (nth k ms 0%Z + nth k ds 0%Z))%R.

(** The slot values of a state. *)
Lemma eget_xenv_R :
  forall xs k, (k < length xs)%nat -> eget k (xenv_R xs) Xnan = Xreal (nth k xs 0%R).
Proof.
  intros xs k Hk. unfold xenv_R. rewrite eget_of_list.
  rewrite (nth_indep _ Xnan (Xreal 0%R)) by (rewrite length_map; lia).
  apply (map_nth Xreal xs 0%R k).
Qed.

Lemma eget_xenv_R_over :
  forall xs k, (length xs <= k)%nat -> eget k (xenv_R xs) Xnan = Xnan.
Proof.
  intros xs k Hk. unfold xenv_R. rewrite eget_of_list.
  apply nth_overflow. rewrite length_map. exact Hk.
Qed.

(** The box contains every state in it. *)
Lemma wide_env_ok :
  forall prec ms ds xs,
  in_box ms ds xs -> env_ok (wide_ienv prec ms ds) (xenv_R xs).
Proof.
  intros prec ms ds xs [Hlen Hin] n.
  unfold wide_ienv. rewrite eget_of_list.
  destruct (Nat.lt_ge_cases n (length ms)) as [Hn|Hn].
  - rewrite zipbox_nth by exact Hn.
    rewrite eget_xenv_R by lia.
    apply slot_box_correct. now apply Hin.
  - rewrite eget_xenv_R_over by lia.
    rewrite nth_overflow by (rewrite zipbox_length; lia).
    rewrite ?I.nai_correct. exact I.
Qed.

(** A state has every slot below its length real and nothing above it set,
    which is what the derivative invariants of Deriv.v start from. *)
Lemma xenv_R_inputs :
  forall xs base, length xs = base ->
  (forall k, (base <= k)%nat -> eget k (xenv_R xs) Xnan = Xnan) /\
  (forall k, (k < base)%nat -> exists v, eget k (xenv_R xs) Xnan = Xreal v).
Proof.
  intros xs base Hlen. split.
  - intros k Hk. apply eget_xenv_R_over. lia.
  - intros k Hk. exists (nth k xs 0%R). apply eget_xenv_R. lia.
Qed.

(** Setting slots of a state to real values keeps both properties. *)
Lemma eset_inputs :
  forall (X : env ExtendedR) base x t,
  (x < base)%nat ->
  (forall k, (base <= k)%nat -> eget k X Xnan = Xnan) /\
  (forall k, (k < base)%nat -> exists v, eget k X Xnan = Xreal v) ->
  (forall k, (base <= k)%nat -> eget k (eset x X (Xreal t)) Xnan = Xnan) /\
  (forall k, (k < base)%nat -> exists v, eget k (eset x X (Xreal t)) Xnan = Xreal v).
Proof.
  intros X base x t Hx [Hu Hr]. split.
  - intros k Hk. rewrite eget_eset_neq by lia. now apply Hu.
  - intros k Hk. destruct (Nat.eq_dec k x) as [->|Hkx].
    + rewrite eget_eset_eq. now exists t.
    + rewrite eget_eset_neq by exact Hkx. now apply Hr.
Qed.

(** Overwriting a slot of the box with an interval that contains the value
    written into the state keeps the two contained. *)
Lemma wide_env_ok_eset :
  forall ienv xenv x vi t,
  env_ok ienv xenv -> contains (I.convert vi) (Xreal t) ->
  env_ok (eset x ienv vi) (eset x xenv (Xreal t)).
Proof. intros. now apply env_ok_eset. Qed.

(** An enclosure of an extended real encloses its real projection, since an
    interval that contains NaN is the whole line. *)
Lemma contains_proj :
  forall xi x, contains (I.convert xi) x -> contains (I.convert xi) (Xreal (proj_val x)).
Proof.
  intros xi [|x] H.
  - revert H. destruct (I.convert xi) as [|l u]; simpl; intros H.
    + exact I.
    + contradiction.
  - exact H.
Qed.

(* ---------------------------------------------------------------- *)
(* A certificate over boxes of states                                *)

(** Each point carries its mantissas, exponents and half-widths; the bounds
    are shared, as in [Checker.cert]. *)
Record bcert := BCert {
  bc_prec : Z ;
  bc_cfg : pconfig ;
  bc_modes : list (Z * Z) ;
  bc_NS : Z ; bc_qS : Z ;
  bc_NU : Z ; bc_qU : Z ;
  bc_NV : Z ; bc_qV : Z ;
  bc_points : list (cpoint * list Z) }.

Definition bprec_of (c : bcert) : F.precision := F.PtoP (Z.to_pos (bc_prec c)).

(** The interval environment of a box after the bindings of the residual. *)
Definition box_ienv_of (c : bcert) (p : cpoint * list Z) : env I.type :=
  let prec := bprec_of c in
  iextend prec (wide_ienv prec (pt_ms (fst p)) (snd p))
          (r_binds (residual (pt_es (fst p)) (bc_cfg c) (bc_modes c))).

(** The three components are within their bounds over the box. *)
Definition check_bpoint (c : bcert) (p : cpoint * list Z) : bool :=
  let prec := bprec_of c in
  let r3 := residual (pt_es (fst p)) (bc_cfg c) (bc_modes c) in
  let ienv := box_ienv_of c p in
  check1 prec ienv (r_s r3) (bc_NS c) (bc_qS c) &&
  check1 prec ienv (r_u r3) (bc_NU c) (bc_qU c) &&
  check1 prec ienv (r_v r3) (bc_NV c) (bc_qV c).

(** Some component is bounded away from zero over the box. *)
Definition check_bpoint_lower (c : bcert) (p : cpoint * list Z) : bool :=
  let prec := bprec_of c in
  let r3 := residual (pt_es (fst p)) (bc_cfg c) (bc_modes c) in
  let ienv := box_ienv_of c p in
  check1_lower prec ienv (r_s r3) (bc_NS c) (bc_qS c) ||
  check1_lower prec ienv (r_u r3) (bc_NU c) (bc_qU c) ||
  check1_lower prec ienv (r_v r3) (bc_NV c) (bc_qV c).

Definition check_bcert (c : bcert) : bool :=
  forallb (check_bpoint c) (bc_points c).

Definition check_bcert_lower (c : bcert) : bool :=
  forallb (check_bpoint_lower c) (bc_points c).

(** The real environment of a state of the box after the bindings. *)
Definition box_env (c : bcert) (p : cpoint * list Z) (xs : list R)
    : env ExtendedR :=
  xextend (xenv_R xs) (r_binds (residual (pt_es (fst p)) (bc_cfg c) (bc_modes c))).

(** What a passing verdict says of a box: at every state in it, the three
    components are real and within their bounds. *)
Definition box_sound (c : bcert) (p : cpoint * list Z) : Prop :=
  let r3 := residual (pt_es (fst p)) (bc_cfg c) (bc_modes c) in
  forall xs, in_box (pt_ms (fst p)) (snd p) xs ->
  let env := box_env c p xs in
  (exists x, xeval env (r_s r3) = Xreal x /\
             (Rabs x <= IZR (bc_NS c) * powerRZ 2%R (bc_qS c))%R) /\
  (exists x, xeval env (r_u r3) = Xreal x /\
             (Rabs x <= IZR (bc_NU c) * powerRZ 2%R (bc_qU c))%R) /\
  (exists x, xeval env (r_v r3) = Xreal x /\
             (Rabs x <= IZR (bc_NV c) * powerRZ 2%R (bc_qV c))%R).

(** And a passing reversed verdict: at every state in the box some component
    is real and at least its bound, so no field of the box balances. *)
Definition box_not_balanced (c : bcert) (p : cpoint * list Z) : Prop :=
  let r3 := residual (pt_es (fst p)) (bc_cfg c) (bc_modes c) in
  forall xs, in_box (pt_ms (fst p)) (snd p) xs ->
  let env := box_env c p xs in
  (exists x, xeval env (r_s r3) = Xreal x /\
             (IZR (bc_NS c) * powerRZ 2%R (bc_qS c) <= Rabs x)%R) \/
  (exists x, xeval env (r_u r3) = Xreal x /\
             (IZR (bc_NU c) * powerRZ 2%R (bc_qU c) <= Rabs x)%R) \/
  (exists x, xeval env (r_v r3) = Xreal x /\
             (IZR (bc_NV c) * powerRZ 2%R (bc_qV c) <= Rabs x)%R).

Lemma box_env_ok :
  forall c p xs, in_box (pt_ms (fst p)) (snd p) xs ->
  env_ok (box_ienv_of c p) (box_env c p xs).
Proof.
  intros c p xs Hin. unfold box_ienv_of, box_env.
  apply iextend_correct. now apply wide_env_ok.
Qed.

Theorem check_bcert_correct :
  forall c, check_bcert c = true -> Forall (box_sound c) (bc_points c).
Proof.
  intros c Hchk. unfold check_bcert in Hchk. rewrite forallb_forall in Hchk.
  apply Forall_forall. intros p Hp. specialize (Hchk p Hp).
  unfold check_bpoint in Hchk.
  apply andb_prop in Hchk. destruct Hchk as [Hsu Hv].
  apply andb_prop in Hsu. destruct Hsu as [Hs Hu].
  intros xs Hin. assert (Henv := box_env_ok c p xs Hin).
  repeat split.
  - exact (check1_correct _ _ _ _ _ _ Henv Hs).
  - exact (check1_correct _ _ _ _ _ _ Henv Hu).
  - exact (check1_correct _ _ _ _ _ _ Henv Hv).
Qed.

Theorem check_bcert_lower_correct :
  forall c, check_bcert_lower c = true -> Forall (box_not_balanced c) (bc_points c).
Proof.
  intros c Hchk. unfold check_bcert_lower in Hchk. rewrite forallb_forall in Hchk.
  apply Forall_forall. intros p Hp. specialize (Hchk p Hp).
  unfold check_bpoint_lower in Hchk.
  intros xs Hin. assert (Henv := box_env_ok c p xs Hin).
  apply orb_prop in Hchk. destruct Hchk as [Hchk|Hv].
  - apply orb_prop in Hchk. destruct Hchk as [Hs|Hu].
    + left. exact (check1_lower_correct _ _ _ _ _ _ Henv Hs).
    + right; left. exact (check1_lower_correct _ _ _ _ _ _ Henv Hu).
  - right; right. exact (check1_lower_correct _ _ _ _ _ _ Henv Hv).
Qed.

(** The mantissas themselves are a state of any box with nonnegative
    half-widths, so a box verdict covers the point the file names. *)
Lemma centre_in_box :
  forall ms ds,
  (forall k, (k < length ms)%nat -> 0 <= nth k ds 0) ->
  in_box ms ds (map IZR ms).
Proof.
  intros ms ds Hd. split.
  - now rewrite length_map.
  - intros k Hk.
    rewrite (map_nth IZR ms 0 k).
    rewrite minus_IZR, plus_IZR.
    assert (H := IZR_le 0 (nth k ds 0) (Hd k Hk)). lra.
Qed.
