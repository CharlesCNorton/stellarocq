(** Grids of enclosed values: a dense family on a grid, and grids combined
    point by point.

    A grid is a list of rows, one per poloidal angle t_a = 2 pi a / N1, each a
    list over the toroidal angles p_b. The values of a dense finite family
    are formed from the row sums at each p_b, computed once, and the table
    of cos(k t_a) and sin(k t_a) of each row ([gvals], [gvals_ok]). Grids of
    the same shape combine entry by entry under any interval operation that
    encloses a real one ([gzip2_ok]), and a grid combines with a list indexed
    by the toroidal angle, such as cos p_b and sin p_b, the same way
    ([gcol_ok]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Stellarocq Require Import KAMScalar Fourier FourierEval FourierDFT FourierList KFix KCheckKern KEngine.
Import ListNotations.
Local Open Scope R_scope.

Module GridOps (J : RI).

Module EN := Engine J.
Import EN EN.KO.

(** A grid of enclosures of the values of f at (t_a, p_b). *)
Definition ggrid (G : list (list J.t)) (N1 N2 : nat) (f : R -> R -> R) (ta pb : nat -> R) : Prop :=
  Forall2 (fun Row a => encl Row (map (fun b => f (ta a) (pb b)) (seq 0 N2))) G (seq 0 N1).

(** The values of a dense family. *)
Definition gvals (F : list (Z * list (Z * (J.t * J.t)))) (TTs Ts : list (list (J.t * J.t))) : list (list J.t) :=
  let ABs := pmap (iABs F) Ts in pmap (fun TT => map (ival TT) ABs) TTs.

Theorem gvals_ok (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) (ns : list Z)
    (TTs Ts : list (list (J.t * J.t))) (N1 N2 : nat) (ta pb : nat -> R) :
  fam_in F f -> Forall (fun kr => map fst (snd kr) = ns) f ->
  Forall2 (fun T b => tab_in T ns (pb b)) Ts (seq 0 N2) ->
  Forall2 (fun TT a => tab_in TT (map fst f) (ta a)) TTs (seq 0 N1) ->
  ggrid (gvals F TTs Ts) N1 N2 (fun t p => feval (flist (dents f)) t p) ta pb.
Proof.
  intros HF Hns HT HTT. unfold ggrid, gvals, pmap. apply forall2_map_l.
  eapply Forall2_impl; [| exact HTT]. intros TT a Ha.
  unfold encl. rewrite map_map. apply forall2_map_l. apply forall2_map_r.
  eapply Forall2_impl; [| exact HT]. intros T b Hb. exact (ival_ok _ _ TT F f T ns HF Hns Hb Ha).
Qed.

(** Grids combined entry by entry. *)
Fixpoint zipw {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
  match la, lb with a :: la', b :: lb' => f a b :: zipw f la' lb' | _, _ => [] end.

Definition gzip2 (op : J.t -> J.t -> J.t) (G1 G2 : list (list J.t)) : list (list J.t) :=
  zipw (zipw op) G1 G2.

Lemma zipw_encl {A : Type} (op : J.t -> J.t -> J.t) (h : R -> R -> R) (f1 f2 : A -> R) (bs : list A)
    (L1 L2 : list J.t) :
  (forall X Y x y, inR X x -> inR Y y -> inR (op X Y) (h x y)) ->
  encl L1 (map f1 bs) -> encl L2 (map f2 bs) -> encl (zipw op L1 L2) (map (fun b => h (f1 b) (f2 b)) bs).
Proof.
  intros Hop. revert L1 L2. induction bs as [| b bs IH]; intros L1 L2 H1 H2.
  - inversion H1; subst. constructor.
  - inversion H1 as [| X x L1' xs HX H1']; subst. inversion H2 as [| Y y L2' ys HY H2']; subst.
    cbn [zipw map]. constructor; [apply Hop; assumption | apply IH; assumption].
Qed.

Theorem gzip2_ok (op : J.t -> J.t -> J.t) (h : R -> R -> R) (G1 G2 : list (list J.t)) (N1 N2 : nat)
    (f1 f2 : R -> R -> R) (ta pb : nat -> R) :
  (forall X Y x y, inR X x -> inR Y y -> inR (op X Y) (h x y)) ->
  ggrid G1 N1 N2 f1 ta pb -> ggrid G2 N1 N2 f2 ta pb ->
  ggrid (gzip2 op G1 G2) N1 N2 (fun t p => h (f1 t p) (f2 t p)) ta pb.
Proof.
  intros Hop. unfold ggrid, gzip2. generalize (seq 0 N1). intros as_. revert G1 G2.
  induction as_ as [| a as_ IH]; intros G1 G2 H1 H2.
  - inversion H1; subst. constructor.
  - inversion H1 as [| R1 x G1' xs HR1 H1']; subst. inversion H2 as [| R2 y G2' ys HR2 H2']; subst.
    cbn [zipw]. constructor; [| apply IH; assumption].
    apply (zipw_encl op h (fun b => f1 (ta a) (pb b)) (fun b => f2 (ta a) (pb b))); assumption.
Qed.

(** A grid combined with a list over the toroidal angles. *)
Definition gcol {C : Type} (op : C -> J.t -> J.t) (cols : list C) (G : list (list J.t)) : list (list J.t) :=
  map (zipw op cols) G.

Theorem gcol_ok {C : Type} (op : C -> J.t -> J.t) (h : R -> R -> R) (cols : list C) (G : list (list J.t))
    (N1 N2 : nat) (f : R -> R -> R) (rel : C -> R -> Prop) (ta pb : nat -> R) :
  (forall c X p x, rel c p -> inR X x -> inR (op c X) (h p x)) ->
  Forall2 (fun c b => rel c (pb b)) cols (seq 0 N2) ->
  ggrid G N1 N2 f ta pb -> ggrid (gcol op cols G) N1 N2 (fun t p => h p (f t p)) ta pb.
Proof.
  intros Hop Hc HG. unfold ggrid, gcol. apply forall2_map_l.
  eapply Forall2_impl; [| exact HG]. intros Row a HR. clear HG.
  generalize (seq 0 N2) Hc HR. clear Hc HR. intros bs Hc. revert Row.
  induction Hc as [| c b cols bs Hcb _ IH]; intros Row HR.
  - inversion HR; subst. constructor.
  - inversion HR as [| X x Row' xs HX HR']; subst. cbn [zipw map]. constructor; [| apply IH; assumption].
    apply Hop; assumption.
Qed.

End GridOps.
