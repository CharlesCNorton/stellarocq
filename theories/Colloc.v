(** The force residual collocated at points, as one system for the interval
    Newton test.

    Newton.v proves that a passing test on any system of expressions gives
    exactly one zero in a box. This builds such a system from Physics.v: a
    list of points, each carrying the residual of the reconstruction in its
    own local slot layout, over the Fourier coefficients of a band of surfaces
    as the unknowns. A point names, for each of its local input slots, the
    global slot it reads, which is an unknown of the system or a parameter
    the certificate fixes, and its scratch slots are moved to a block of
    their own above every input. [assemble] renames the bindings of every
    point into one list, and [colloc_correct] reads a passing verdict back at
    the points: there is exactly one choice of the unknown coefficients in
    the box at which the collocated residual component of every point is
    zero. That is a discrete equilibrium of the reconstruction, with the
    stream function, the rotational transform, the pressure and the surfaces
    outside the band taken as given. *)

From Coq Require Import ZArith Reals List Bool Lia Lra.
From Interval Require Import Real.Xreal Interval.Interval.
From Stellarocq Require Import Expr Physics Checker Deriv Cell Newton.

Import ListNotations.
Local Open Scope nat_scope.

(* ---------------------------------------------------------------- *)
(* Renaming the slots of an expression                               *)

Fixpoint rename (f : nat -> nat) (e : expr) : expr :=
  match e with
  | Evar n     => Evar (f n)
  | EfromZ z   => EfromZ z
  | Epi        => Epi
  | Eneg a     => Eneg (rename f a)
  | Eadd a b   => Eadd (rename f a) (rename f b)
  | Esub a b   => Esub (rename f a) (rename f b)
  | Emul a b   => Emul (rename f a) (rename f b)
  | Ediv a b   => Ediv (rename f a) (rename f b)
  | Esqrt a    => Esqrt (rename f a)
  | Esin a     => Esin (rename f a)
  | Ecos a     => Ecos (rename f a)
  | Eexp a     => Eexp (rename f a)
  | Eatan a    => Eatan (rename f a)
  | Epow2 z    => Epow2 z
  end.

Definition rename_binds (f : nat -> nat) (bs : list binding) : list binding :=
  map (fun b => (f (fst b), rename f (snd b))) bs.

(** A renamed expression reads through the map what the original reads
    directly. *)
Lemma xeval_rename :
  forall f e (env env' : env ExtendedR),
  (forall k, eget k env' Xnan = eget (f k) env Xnan) ->
  xeval env (rename f e) = xeval env' e.
Proof.
  intros f e env env' H.
  induction e; simpl;
    try (now rewrite IHe); try (now rewrite IHe1, IHe2); try reflexivity.
  symmetry. apply H.
Qed.

(** Renamed bindings write through the map what the originals write, when
    the map separates every written slot from every other slot. *)
Lemma xextend_rename :
  forall f bs (env env' : env ExtendedR),
  (forall k, eget k env' Xnan = eget (f k) env Xnan) ->
  (forall b, In b bs -> forall k, f k = f (fst b) -> k = fst b) ->
  forall k,
  eget k (xextend env' bs) Xnan = eget (f k) (xextend env (rename_binds f bs)) Xnan.
Proof.
  intros f bs. induction bs as [|[k0 e] bs IH]; intros env env' Hag Hinj k.
  - simpl. apply Hag.
  - cbn [rename_binds map]. rewrite !xextend_cons. cbn [fst snd].
    apply IH.
    + intros k'. destruct (Nat.eq_dec k' k0) as [->|Hne].
      * rewrite !eget_eset_eq. symmetry. apply xeval_rename. exact Hag.
      * rewrite eget_eset_neq by exact Hne.
        rewrite eget_eset_neq.
        -- apply Hag.
        -- intros Heq. apply Hne. apply (Hinj (k0, e)). now left. exact Heq.
    + intros b Hb. apply Hinj. now right.
Qed.

(** Bindings that write none of a set of slots leave them alone. *)
Lemma xextend_out :
  forall bs (env : env ExtendedR) k,
  (forall b, In b bs -> fst b <> k) ->
  eget k (xextend env bs) Xnan = eget k env Xnan.
Proof.
  induction bs as [|b bs IH]; intros env k H. reflexivity.
  rewrite xextend_cons. rewrite IH.
  - apply eget_eset_neq. intros Heq. apply (H b). now left. now symmetry.
  - intros b' Hb'. apply H. now right.
Qed.

(** Well-formed bindings occupy the slots from their base on, in order. *)
Lemma well_formed_slots :
  forall m bs b,
  well_formed m bs = true -> In b bs -> (m <= fst b < m + length bs)%nat.
Proof.
  intros m bs. revert m.
  induction bs as [|[k e] bs IH]; intros m b Hwf Hin. inversion Hin.
  simpl in Hwf. apply andb_prop in Hwf. destruct Hwf as [Hwf Htl].
  apply andb_prop in Hwf. destruct Hwf as [Hk _]. apply Nat.eqb_eq in Hk.
  destruct Hin as [<-|Hin].
  - simpl. lia.
  - destruct (IH (S m) b Htl Hin). simpl. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The collocation points                                            *)

(** A point: where each of its local input slots reads in the global layout,
    and which component it collocates, 0 for r_s, 1 for r_u and 2 for r_v. *)
Record cpt := CPt { cp_sigma : list nat ; cp_out : nat }.

Section Assembly.

(** The width of a point's local input layout, the exponent of every global
    input slot, and what every point's residual is built from. *)
Variable base_local : nat.
Variable gexps : list Z.
Variable cfg : pconfig.
Variable modes : list (Z * Z).

(** The map of a point whose scratch block starts at next. *)
Definition sigma_of (p : cpt) (next k : nat) : nat :=
  if Nat.ltb k base_local then nth k (cp_sigma p) 0%nat else next + (k - base_local).

(** The exponents its residual reads its slots with are those of the global
    slots it is mapped to. *)
Definition local_exps (p : cpt) : list Z :=
  map (fun k => nth (nth k (cp_sigma p) 0%nat) gexps 0%Z) (seq 0 base_local).

Definition local_res (p : cpt) : residual3 := residual (local_exps p) cfg modes.

Definition local_out (p : cpt) : expr :=
  match cp_out p with
  | O => r_s (local_res p)
  | S O => r_u (local_res p)
  | _ => r_v (local_res p)
  end.

Definition out_slot (p : cpt) : nat :=
  match slot_of (local_out p) with Some o => o | None => 0 end.

(** The bindings of every point in one list, each block after the last, and
    the global slot of every point's output. *)
Fixpoint assemble (next : nat) (pts : list cpt) : list binding * list nat :=
  match pts with
  | [] => ([], [])
  | p :: tl =>
      let bs := rename_binds (sigma_of p next) (r_binds (local_res p)) in
      let rest := assemble (next + length bs) tl in
      (bs ++ fst rest, sigma_of p next (out_slot p) :: snd rest)
  end.

(** What the assembly asks of a point: a map of the local width into the
    global inputs, well-formed local bindings from the local base, and an
    output that is one of its own scratch slots. *)
Definition point_ok (nin : nat) (p : cpt) : bool :=
  Nat.eqb (length (cp_sigma p)) base_local &&
  forallb (fun g => Nat.ltb g nin) (cp_sigma p) &&
  well_formed base_local (r_binds (local_res p)) &&
  match slot_of (local_out p) with
  | Some o => Nat.leb base_local o &&
              Nat.ltb o (base_local + length (r_binds (local_res p)))
  | None => false
  end.

Definition colloc_system (prec : Z) (n : nat) (centre : list Z) (r : Z)
    (A B : list (list (Z * Z))) (KN Kq MN Mq : Z) (pts : list cpt) : system :=
  let a := assemble (length centre) pts in
  System prec n centre r (fst a) (snd a) A B KN Kq MN Mq.

Definition colloc_check (prec : Z) (n : nat) (centre : list Z) (r : Z)
    (A B : list (list (Z * Z))) (KN Kq MN Mq : Z) (pts : list cpt) : bool :=
  Nat.eqb (length pts) n &&
  Nat.eqb (length gexps) (length centre) &&
  forallb (point_ok (length centre)) pts &&
  check_newton (colloc_system prec n centre r A B KN Kq MN Mq pts).

(* ---------------------------------------------------------------- *)
(* The points read back                                              *)

(** The value of a global input slot: an unknown's coordinate, or a
    parameter's mantissa. *)
Definition gval (n : nat) (centre : list Z) (x : list R) (g : nat) : ExtendedR :=
  if Nat.ltb g n then Xreal (nth g x 0%R) else Xreal (IZR (nth g centre 0%Z)).

(** The environment of a point in its own layout, with the unknowns at x. *)
Definition local_env (n : nat) (centre : list Z) (x : list R) (p : cpt)
    : env ExtendedR :=
  of_list (map (fun k => gval n centre x (nth k (cp_sigma p) 0%nat)) (seq 0 base_local)).

(** Every slot the assembly writes from a point on lies at or above where
    that point's block starts. *)
Lemma assemble_slots :
  forall pts next nin b,
  (forall p, In p pts -> point_ok nin p = true) ->
  In b (fst (assemble next pts)) -> (next <= fst b)%nat.
Proof.
  induction pts as [|p tl IH]; intros next nin b Hok Hin. inversion Hin.
  cbn [assemble fst] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - unfold rename_binds in Hin. apply in_map_iff in Hin.
    destruct Hin as [b0 [<- Hb0]]. cbn [fst]. unfold sigma_of.
    assert (Hp := Hok p (or_introl eq_refl)). unfold point_ok in Hp.
    rewrite !andb_true_iff in Hp. destruct Hp as [[[_ _] Hwf] _].
    destruct (well_formed_slots _ _ _ Hwf Hb0) as [Hlo _].
    rewrite (proj2 (Nat.ltb_ge _ _) Hlo). lia.
  - assert (H := IH _ nin b (fun q Hq => Hok q (or_intror Hq)) Hin). lia.
Qed.

(** Output i of the assembled list is the collocated component of point i,
    read in that point's own environment. *)
Lemma assemble_bridge :
  forall pts next nin (n : nat) (centre : list Z) (x : list R) (e : env ExtendedR),
  nin = length centre ->
  (nin <= next)%nat ->
  (forall p, In p pts -> point_ok nin p = true) ->
  (forall g, (g < nin)%nat -> eget g e Xnan = gval n centre x g) ->
  (forall g, (next <= g)%nat -> eget g e Xnan = Xnan) ->
  forall i p, nth_error pts i = Some p ->
  eget (nth i (snd (assemble next pts)) 0%nat) (xextend e (fst (assemble next pts))) Xnan
  = eget (out_slot p) (xextend (local_env n centre x p) (r_binds (local_res p))) Xnan.
Proof.
  induction pts as [|q tl IH];
    intros next nin n centre x e Hnin Hnext Hok Hin Hout i p Hp.
  - destruct i; discriminate.
  - cbn [assemble fst snd].
    set (f := sigma_of q next).
    set (bs := rename_binds f (r_binds (local_res q))).
    assert (Hq := Hok q (or_introl eq_refl)).
    unfold point_ok in Hq. rewrite !andb_true_iff in Hq.
    destruct Hq as [[[Hlen Hlt] Hwf] Hslot].
    apply Nat.eqb_eq in Hlen. rewrite forallb_forall in Hlt.
    assert (Hlbs : length bs = length (r_binds (local_res q)))
      by (unfold bs, rename_binds; apply length_map).
    (* the block of q writes its own slots and nothing else *)
    assert (Hblock : forall b, In b bs -> (next <= fst b < next + length bs)%nat).
    { intros b Hb. unfold bs, rename_binds in Hb. apply in_map_iff in Hb.
      destruct Hb as [b0 [<- Hb0]]. cbn [fst].
      destruct (well_formed_slots _ _ _ Hwf Hb0) as [Hlo Hhi].
      unfold f, sigma_of. rewrite (proj2 (Nat.ltb_ge _ _) Hlo). lia. }
    rewrite xextend_app.
    destruct i as [|i].
    + injection Hp as <-. cbn [nth].
      (* the output sits in the block *)
      unfold out_slot in *. destruct (slot_of (local_out q)) as [o|] eqn:Ho.
      2: discriminate.
      apply andb_true_iff in Hslot. destruct Hslot as [Hlo Hhi].
      apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
      assert (Hfo : f o = (next + (o - base_local))%nat).
      { unfold f, sigma_of. rewrite (proj2 (Nat.ltb_ge _ _) Hlo). reflexivity. }
      (* the blocks after it write above it *)
      rewrite xextend_out.
      2:{ intros b Hb.
          assert (H := assemble_slots tl (next + length bs) nin b
                         (fun q' Hq' => Hok q' (or_intror Hq')) Hb).
          rewrite Hfo. lia. }
      symmetry. apply xextend_rename.
      * (* the local environment reads through the map *)
        intros k. unfold local_env. rewrite eget_of_list.
        destruct (lt_dec k base_local) as [Hk|Hk].
        -- rewrite (nth_map_in _ _ _ _ _ 0%nat) by (rewrite length_seq; lia).
           rewrite seq_nth by lia. cbn [Nat.add].
           unfold f, sigma_of. rewrite (proj2 (Nat.ltb_lt _ _) Hk).
           symmetry. apply Hin. apply Nat.ltb_lt. apply Hlt. apply nth_In. lia.
        -- rewrite nth_overflow by (rewrite length_map, length_seq; lia).
           unfold f, sigma_of. rewrite (proj2 (Nat.ltb_ge _ _)) by lia.
           symmetry. apply Hout. lia.
      * (* the map separates every written slot from every other *)
        intros b Hb k Hk.
        destruct (well_formed_slots _ _ _ Hwf Hb) as [Hlo' _].
        unfold f, sigma_of in Hk. rewrite (proj2 (Nat.ltb_ge _ _) Hlo') in Hk.
        destruct (Nat.ltb k base_local) eqn:Hkb.
        -- exfalso. apply Nat.ltb_lt in Hkb.
           assert (Hin' : In (nth k (cp_sigma q) 0%nat) (cp_sigma q))
             by (apply nth_In; lia).
           assert (Hg := Hlt _ Hin'). apply Nat.ltb_lt in Hg. lia.
        -- apply Nat.ltb_ge in Hkb. lia.
    + cbn [nth]. simpl in Hp.
      apply (IH (next + length bs) nin n centre x); try assumption.
      * lia.
      * intros q' Hq'. apply Hok. now right.
      * intros g Hg. rewrite xextend_out. now apply Hin.
        intros b Hb. destruct (Hblock b Hb). lia.
      * intros g Hg. rewrite xextend_out. apply Hout. lia.
        intros b Hb. destruct (Hblock b Hb). lia.
Qed.

(** A passing check gives exactly one choice of the unknowns in the box at
    which the collocated component of every point is zero. *)
Theorem colloc_correct :
  forall prec n centre r A B KN Kq MN Mq pts,
  colloc_check prec n centre r A B KN Kq MN Mq pts = true ->
  exists x : list R,
    in_box (colloc_system prec n centre r A B KN Kq MN Mq pts) x /\
    (forall p, In p pts ->
       xeval (xextend (local_env n centre x p) (r_binds (local_res p)))
             (local_out p) = Xreal 0) /\
    (forall y, in_box (colloc_system prec n centre r A B KN Kq MN Mq pts) y ->
       (forall p, In p pts ->
          xeval (xextend (local_env n centre y p) (r_binds (local_res p)))
                (local_out p) = Xreal 0) ->
       y = x).
Proof.
  intros prec n centre r A B KN Kq MN Mq pts Hchk.
  unfold colloc_check in Hchk. rewrite !andb_true_iff in Hchk.
  destruct Hchk as [[[Hlen _] Hok] Hnew].
  apply Nat.eqb_eq in Hlen. rewrite forallb_forall in Hok.
  set (s := colloc_system prec n centre r A B KN Kq MN Mq pts) in *.
  assert (Hcn : sy_centre s = centre) by reflexivity.
  assert (Hnn : sy_n s = n) by reflexivity.
  assert (Hbs : sy_binds s = fst (assemble (length centre) pts)) by reflexivity.
  assert (Hos : sy_out s = snd (assemble (length centre) pts)) by reflexivity.
  assert (Hnb : (n <= length centre)%nat).
  { assert (H := c_nb s Hnew). unfold sbase in H. rewrite Hcn, Hnn in H. exact H. }
  (* the output of the system at a point is the residual at that point *)
  assert (Hbridge : forall (z : list R) i p,
            length z = n -> nth_error pts i = Some p ->
            Fx s (E (sy_centre s) (sy_n s) z) i
            = xeval (xextend (local_env n centre z p) (r_binds (local_res p)))
                    (local_out p)).
  { intros z i p Hz Hp.
    assert (Hq := Hok p (nth_error_In _ _ Hp)). unfold point_ok in Hq.
    rewrite !andb_true_iff in Hq. destruct Hq as [_ Hslot].
    destruct (slot_of (local_out p)) as [o|] eqn:Ho. 2: discriminate.
    assert (Heo : local_out p = Evar o).
    { destruct (local_out p); simpl in Ho; try discriminate. now injection Ho as ->. }
    rewrite Heo. unfold Fx, oslot. cbn [xeval]. rewrite Hcn, Hnn, Hbs, Hos.
    assert (Hspec := E_spec centre n z Hz Hnb).
    destruct Hspec as [Hu [Hpar Hz']].
    assert (HG1 : forall g, (g < length centre)%nat ->
              eget g (E centre n z) Xnan = gval n centre z g).
    { intros g Hg. unfold gval. destruct (Nat.ltb g n) eqn:Hgn.
      - apply Nat.ltb_lt in Hgn. now apply Hu.
      - apply Nat.ltb_ge in Hgn. apply Hpar; lia. }
    assert (HG2 : forall g, (length centre <= g)%nat ->
              eget g (E centre n z) Xnan = Xnan).
    { intros g Hg. now apply Hz'. }
    rewrite (assemble_bridge pts (length centre) (length centre) n centre z
               (E centre n z) eq_refl (Nat.le_refl _) Hok HG1 HG2 i p Hp).
    unfold out_slot. rewrite Ho. reflexivity. }
  destruct (newton_correct s Hnew) as [x [Hbox [Hzero Huniq]]].
  exists x. split. exact Hbox. split.
  - intros p Hp. destruct (In_nth_error _ _ Hp) as [i Hi].
    assert (Hi' : (i < n)%nat).
    { rewrite <- Hlen. apply nth_error_Some. rewrite Hi. discriminate. }
    assert (Hx : length x = n) by (rewrite <- Hnn; apply Hbox).
    rewrite <- (Hbridge x i p Hx Hi). apply Hzero. rewrite Hnn. exact Hi'.
  - intros y Hy Hall. apply Huniq. exact Hy.
    intros k Hk. rewrite Hnn in Hk.
    assert (Hy' : length y = n) by (rewrite <- Hnn; apply Hy).
    destruct (nth_error pts k) as [p|] eqn:Hp.
    + rewrite (Hbridge y k p Hy' Hp). apply Hall. eapply nth_error_In. exact Hp.
    + exfalso. apply nth_error_None in Hp. lia.
Qed.

End Assembly.
