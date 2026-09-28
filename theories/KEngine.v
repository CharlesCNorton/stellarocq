(** Values, transforms and norms of families on a grid, over enclosures, with
    lists read in order.

    Every table and every array of values is a list traversed from its head,
    so the checks never index into a structure. Sums and dot products of
    lists of intervals enclose the sums and dot products of the lists of
    reals they enclose ([isuml_ok], [idot_ok]). The modes of a box are listed
    in the order in which [zsum] adds them ([zrange], [bsum_zrange]).

    A finite family given densely, a row of cosine and sine coefficients over
    the toroidal modes ns for each poloidal mode of ks ([dents]), has at
    (t, p) the value sum_k cos(k t) A_k(p) + sin(k t) B_k(p) with
    A_k(p) = sum c cos(n p) + s sin(n p) and B_k(p) = sum s cos(n p) - c sin(n p)
    ([feval_dents]). From tables of cos(n p) and sin(n p) at one toroidal
    angle the row sums are enclosed once ([iAB_ok]), and from tables of
    cos(k t) and sin(k t) at one poloidal angle the value ([ival_ok]).

    On a grid of N1 poloidal angles and M toroidal angles of one period, the
    row transforms at each mode l are dot products of a row of values with a
    row of the table of cos(l 2 pi b / M), and the transforms at (k, l) are
    dot products of a column of cos(k 2 pi a / N1) with the row transforms,
    divided by N1 M ([idft_ok]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul FourierAlg
  FourierMulEval FourierMulSem FourierMulLim FourierLim FourierInv FourierSqrt
  FourierDFT FourierCanon FourierModel FourierPer FourierList FourierSupp KCheckDFT FourierModelPer KFix KCheckKern.
Import ListNotations.
Local Open Scope R_scope.

(** * Real sums over lists *)

(** [map] under another name: the extraction of the checks maps the lists
    whose elements are costly to compute through a parallel map, which is
    trusted to return what [map] returns. *)
Definition pmap {A B : Type} (f : A -> B) (l : list A) : list B := map f l.

Definition rsuml (xs : list R) : R := fold_right Rplus 0 xs.

Fixpoint rdot (xs ys : list R) : R :=
  match xs, ys with x :: xs', y :: ys' => x * y + rdot xs' ys' | _, _ => 0 end.

Lemma fsum_shift_front (h : nat -> R) (n : nat) : fsum h (S n) = h O + fsum (fun i => h (S i)) n.
Proof. induction n as [| n IH]; cbn [fsum] in *; [ring | rewrite IH; ring]. Qed.

Lemma rsuml_map_seq (f : nat -> R) (s n : nat) : rsuml (map f (seq s n)) = fsum (fun i => f (s + i)%nat) n.
Proof.
  revert s. induction n as [| n IH]; intros s; [reflexivity |].
  cbn [seq map]. unfold rsuml. cbn [fold_right]. fold (rsuml (map f (seq (S s) n))). rewrite IH.
  rewrite (fsum_shift_front (fun i => f (s + i)%nat) n). rewrite Nat.add_0_r. f_equal.
  apply fsum_ext. intros i. f_equal. lia.
Qed.

Lemma rdot_map_seq (f g : nat -> R) (s n : nat) :
  rdot (map f (seq s n)) (map g (seq s n)) = fsum (fun i => f (s + i)%nat * g (s + i)%nat) n.
Proof.
  revert s. induction n as [| n IH]; intros s; [reflexivity |].
  cbn [seq map rdot]. rewrite IH. rewrite (fsum_shift_front (fun i => f (s + i)%nat * g (s + i)%nat) n).
  rewrite Nat.add_0_r. f_equal. apply fsum_ext. intros i. f_equal; f_equal; lia.
Qed.

(** * The modes of a box in the order of zsum *)

Fixpoint zrange (K : nat) : list Z :=
  match K with
  | O => [0%Z]
  | S K' => Z.of_nat (S K') :: (- Z.of_nat (S K'))%Z :: zrange K'
  end.

Lemma zsum_zrange (f : Z -> R) (K : nat) : zsum f K = rsuml (map f (zrange K)).
Proof.
  induction K as [| K IH]; [simpl; unfold rsuml; simpl; ring |].
  rewrite zsum_S, IH. cbn [zrange map]. unfold rsuml. simpl. ring.
Qed.

Lemma bsum_zrange (K1 K2 : nat) (f : Z -> Z -> R) :
  bsum K1 K2 f = rsuml (map (fun k => rsuml (map (fun l => f k l) (zrange K2))) (zrange K1)).
Proof.
  unfold bsum. rewrite zsum_zrange. f_equal. apply map_ext. intros k. apply zsum_zrange.
Qed.

Lemma in_zrange (K : nat) (k : Z) : In k (zrange K) -> (Z.abs k <= Z.of_nat K)%Z.
Proof.
  induction K as [| K IH]; simpl.
  - intros [E | []]. subst. simpl. lia.
  - intros [E | [E | H]]; [subst; lia | subst; lia | specialize (IH H); lia].
Qed.

(** * A dense finite family *)

Definition rA (row : list (Z * (R * R))) (p : R) : R :=
  rsuml (map (fun e => let '(n, (c, s)) := e in c * cos (IZR n * p) + s * sin (IZR n * p)) row).
Definition rB (row : list (Z * (R * R))) (p : R) : R :=
  rsuml (map (fun e => let '(n, (c, s)) := e in s * cos (IZR n * p) - c * sin (IZR n * p)) row).

Definition dents (fam : list (Z * list (Z * (R * R)))) : list fent :=
  flat_map (fun kr => map (fun e => let '(n, (c, s)) := e in mkfent (fst kr) n c s) (snd kr)) fam.

Definition dval (fam : list (Z * list (Z * (R * R)))) (t p : R) : R :=
  rsuml (map (fun kr => cos (IZR (fst kr) * t) * rA (snd kr) p + sin (IZR (fst kr) * t) * rB (snd kr) p) fam).

Lemma esum_app' (f : fent -> R) (l1 l2 : list fent) : esum f (l1 ++ l2) = esum f l1 + esum f l2.
Proof. induction l1 as [| e l1 IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma esum_cons (f : fent -> R) (e : fent) (l : list fent) : esum f (e :: l) = f e + esum f l.
Proof. reflexivity. Qed.

Lemma rA_cons (n : Z) (c s : R) (row : list (Z * (R * R))) (p : R) :
  rA ((n, (c, s)) :: row) p = c * cos (IZR n * p) + s * sin (IZR n * p) + rA row p.
Proof. reflexivity. Qed.

Lemma rB_cons (n : Z) (c s : R) (row : list (Z * (R * R))) (p : R) :
  rB ((n, (c, s)) :: row) p = s * cos (IZR n * p) - c * sin (IZR n * p) + rB row p.
Proof. reflexivity. Qed.

Lemma esum_row (k : Z) (row : list (Z * (R * R))) (t p : R) :
  esum (eterm t p) (map (fun e => let '(n, (c, s)) := e in mkfent k n c s) row)
  = cos (IZR k * t) * rA row p + sin (IZR k * t) * rB row p.
Proof.
  induction row as [| [n [c s]] row IH].
  - unfold rA, rB, rsuml. simpl. ring.
  - cbn [map]. rewrite esum_cons, IH, rA_cons, rB_cons. unfold eterm, mode. simpl.
    rewrite cos_plus, sin_plus. ring.
Qed.

Theorem feval_dents (fam : list (Z * list (Z * (R * R)))) (t p : R) :
  feval (flist (dents fam)) t p = dval fam t p.
Proof.
  rewrite feval_flist. unfold dents, dval. induction fam as [| [k row] fam IH]; [reflexivity |].
  cbn [flat_map map fst snd]. rewrite esum_app', IH, esum_row. reflexivity.
Qed.

(** * The exact norm of a finitely supported family of period P

    On a grid of N1 poloidal and P M toroidal points past its support, the
    weighted sum of the transforms of such a family bounds its norm. *)

Definition rexact (Pn N1 M K1 K2 : nat) (u : fser) (rho : R) : R :=
  bsum K1 K2 (fun k l => (Rabs (dftc N1 (Pn * M) u k (Z.of_nat Pn * l)) + Rabs (dfts N1 (Pn * M) u k (Z.of_nat Pn * l)))
                        * wt rho k (Z.of_nat Pn * l)).

Theorem exact_nbound (Pn N1 M K1 K2 : nat) (u : fser) (rho : R) :
  (0 < Pn)%nat -> (2 * K1 < N1)%nat -> (2 * Kfull (Z.of_nat Pn) K2 < Pn * M)%nat ->
  supp K1 (Kfull (Z.of_nat Pn) K2) u -> is_canon u -> FourierPer.is_per (Z.of_nat Pn) u ->
  nbound rho (rexact Pn N1 M K1 K2 u rho) u.
Proof.
  intros HPn HN1x HN2x Hs Cu Qu. assert (HPz : (0 < Z.of_nat Pn)%Z) by lia.
  exact (nbound_exact_per (Z.of_nat Pn) HPz N1 (Pn * M) K1 K2 u rho HN1x HN2x Hs Cu Qu).
Qed.

(** * Enclosures *)

Module Engine (J : RI).

Module KO := KernOps J.
Import KO.

Definition encl (Xs : list J.t) (xs : list R) : Prop := Forall2 inR Xs xs.

Fixpoint isuml_acc (acc : J.t) (Xs : list J.t) : J.t :=
  match Xs with [] => acc | X :: Xs' => isuml_acc (J.add acc X) Xs' end.
Definition isuml (Xs : list J.t) : J.t := isuml_acc J.zero Xs.

Lemma isuml_acc_ok (A : J.t) (a : R) (Xs : list J.t) (xs : list R) :
  inR A a -> encl Xs xs -> inR (isuml_acc A Xs) (a + rsuml xs).
Proof.
  intros HA H. revert A a HA. induction H as [| X x Xs xs Hx _ IH]; intros A a HA.
  - simpl. unfold rsuml. simpl. rewrite Rplus_0_r. exact HA.
  - cbn [isuml_acc]. replace (a + rsuml (x :: xs)) with ((a + x) + rsuml xs) by (unfold rsuml; simpl; ring).
    apply IH. apply inR_add; assumption.
Qed.

Lemma isuml_ok (Xs : list J.t) (xs : list R) : encl Xs xs -> inR (isuml Xs) (rsuml xs).
Proof. intros H. unfold isuml. rewrite <- (Rplus_0_l (rsuml xs)). apply isuml_acc_ok; [exact inR_zero | exact H]. Qed.

Fixpoint idot_acc (acc : J.t) (Xs Ys : list J.t) : J.t :=
  match Xs, Ys with X :: Xs', Y :: Ys' => idot_acc (J.add acc (J.mul X Y)) Xs' Ys' | _, _ => acc end.
Definition idot (Xs Ys : list J.t) : J.t := idot_acc J.zero Xs Ys.

Lemma idot_acc_ok (A : J.t) (a : R) (Xs Ys : list J.t) (xs ys : list R) :
  inR A a -> encl Xs xs -> encl Ys ys -> inR (idot_acc A Xs Ys) (a + rdot xs ys).
Proof.
  intros HA H. revert A a Ys ys HA. induction H as [| X x Xs xs Hx _ IH]; intros A a Ys ys HA HY.
  - simpl. rewrite Rplus_0_r. exact HA.
  - destruct HY as [| Y y Ys ys Hy HY'].
    + simpl. rewrite Rplus_0_r. exact HA.
    + simpl. replace (a + (x * y + rdot xs ys)) with ((a + x * y) + rdot xs ys) by ring.
      apply IH; [apply inR_add; [exact HA | apply inR_mul; assumption] | exact HY'].
Qed.

Lemma idot_ok (Xs Ys : list J.t) (xs ys : list R) : encl Xs xs -> encl Ys ys -> inR (idot Xs Ys) (rdot xs ys).
Proof.
  intros HX HY. unfold idot. rewrite <- (Rplus_0_l (rdot xs ys)). apply idot_acc_ok; [exact inR_zero | exact HX | exact HY].
Qed.

(** * Values of a dense family *)

(** An interval family holds a real one: the same modes, coefficients enclosed. *)
Definition row_in (Is : list (Z * (J.t * J.t))) (rs : list (Z * (R * R))) : Prop :=
  Forall2 (fun I r => fst I = fst r /\ inR (fst (snd I)) (fst (snd r)) /\ inR (snd (snd I)) (snd (snd r))) Is rs.

Definition fam_in (Fs : list (Z * list (Z * (J.t * J.t)))) (fs : list (Z * list (Z * (R * R)))) : Prop :=
  Forall2 (fun F f => fst F = fst f /\ row_in (snd F) (snd f)) Fs fs.

(** A table of cos(n p) and sin(n p) aligned with a row. *)
Definition tab_in (T : list (J.t * J.t)) (ns : list Z) (p : R) : Prop :=
  Forall2 (fun CS n => inR (fst CS) (cos (IZR n * p)) /\ inR (snd CS) (sin (IZR n * p))) T ns.

(** The row sums, over the table read along the row. *)
Fixpoint iAB_acc (A B : J.t) (row : list (Z * (J.t * J.t))) (T : list (J.t * J.t)) : J.t * J.t :=
  match row, T with
  | e :: row', CS :: T' =>
      let '(c, s) := snd e in let '(Co, Si) := CS in
      iAB_acc (J.add A (J.add (J.mul c Co) (J.mul s Si))) (J.add B (J.sub (J.mul s Co) (J.mul c Si))) row' T'
  | _, _ => (A, B)
  end.

Definition iAB (row : list (Z * (J.t * J.t))) (T : list (J.t * J.t)) : J.t * J.t := iAB_acc J.zero J.zero row T.

Lemma iAB_acc_ok (A B : J.t) (a b p : R) (row : list (Z * (J.t * J.t))) (r : list (Z * (R * R)))
    (T : list (J.t * J.t)) :
  inR A a -> inR B b -> row_in row r -> tab_in T (map fst r) p ->
  inR (fst (iAB_acc A B row T)) (a + rA r p) /\ inR (snd (iAB_acc A B row T)) (b + rB r p).
Proof.
  intros HA HB H. revert A B a b T HA HB. induction H as [| I e row r [E [HC HS]] _ IH];
    intros A B a b T HA HB HT.
  - unfold rA, rB, rsuml. simpl. rewrite !Rplus_0_r. destruct T as [| CS T]; simpl; split; assumption.
  - destruct T as [| [Co Si] T]; [inversion HT |].
    inversion HT as [| CS n T' ns' [HCo HSi] HT']. subst.
    destruct I as [n [c s]]. destruct e as [n' [c' s']]. simpl in E, HC, HS, HCo, HSi. subst n'.
    cbn [iAB_acc snd]. unfold rA, rB. cbn [map rsuml fold_right].
    fold (rsuml (map (fun e => let '(n, (c, s)) := e in c * cos (IZR n * p) + s * sin (IZR n * p)) r)).
    fold (rsuml (map (fun e => let '(n, (c, s)) := e in s * cos (IZR n * p) - c * sin (IZR n * p)) r)).
    fold (rA r p). fold (rB r p).
    replace (a + (c' * cos (IZR n * p) + s' * sin (IZR n * p) + rA r p))
      with ((a + (c' * cos (IZR n * p) + s' * sin (IZR n * p))) + rA r p) by ring.
    replace (b + (s' * cos (IZR n * p) - c' * sin (IZR n * p) + rB r p))
      with ((b + (s' * cos (IZR n * p) - c' * sin (IZR n * p))) + rB r p) by ring.
    apply IH; [| | exact HT'].
    + apply inR_add; [exact HA | apply inR_add; apply inR_mul; assumption].
    + apply inR_add; [exact HB | apply inR_sub; apply inR_mul; assumption].
Qed.

Lemma iAB_ok (row : list (Z * (J.t * J.t))) (r : list (Z * (R * R))) (T : list (J.t * J.t)) (p : R) :
  row_in row r -> tab_in T (map fst r) p -> inR (fst (iAB row T)) (rA r p) /\ inR (snd (iAB row T)) (rB r p).
Proof.
  intros H HT. rewrite <- (Rplus_0_l (rA r p)), <- (Rplus_0_l (rB r p)).
  apply iAB_acc_ok; [exact inR_zero | exact inR_zero | exact H | exact HT].
Qed.

(** The value at a point from the row sums at its toroidal angle and a table of
    cos(k t) and sin(k t) at its poloidal angle, aligned with the rows. *)
Fixpoint ival_acc (V : J.t) (TT : list (J.t * J.t)) (AB : list (J.t * J.t)) : J.t :=
  match TT, AB with
  | CS :: TT', ab :: AB' =>
      ival_acc (J.add V (J.add (J.mul (fst CS) (fst ab)) (J.mul (snd CS) (snd ab)))) TT' AB'
  | _, _ => V
  end.

Definition ival (TT AB : list (J.t * J.t)) : J.t := ival_acc J.zero TT AB.

(** The row sums of a family at one toroidal angle. *)
Definition iABs (F : list (Z * list (Z * (J.t * J.t)))) (T : list (J.t * J.t)) : list (J.t * J.t) :=
  map (fun kr => iAB (snd kr) T) F.

Lemma ival_acc_ok (V : J.t) (v t p : R) (TT : list (J.t * J.t)) (F : list (Z * list (Z * (J.t * J.t))))
    (f : list (Z * list (Z * (R * R)))) (T : list (J.t * J.t)) (ns : list Z) :
  inR V v -> fam_in F f -> Forall (fun kr => map fst (snd kr) = ns) f -> tab_in T ns p ->
  tab_in TT (map fst f) t ->
  inR (ival_acc V TT (iABs F T)) (v + dval f t p).
Proof.
  intros HV H. revert V v TT HV. induction H as [| I e F f [E HR] _ IH]; intros V v TT HV Hns HT HTT.
  - unfold dval, rsuml. simpl. rewrite Rplus_0_r. destruct TT; exact HV.
  - destruct TT as [| [Co Si] TT]; [inversion HTT |].
    inversion HTT as [| CS k TT' ks' [HCo HSi] HTT']. subst.
    apply Forall_cons_iff in Hns. destruct Hns as [Hn Hns'].
    pose proof (iAB_ok (snd I) (snd e) T p HR) as HAB. rewrite Hn in HAB. specialize (HAB HT).
    destruct HAB as [HA HB].
    cbn [iABs map ival_acc fst snd] in *.
    unfold dval. cbn [map rsuml fold_right]. fold (rsuml (map (fun kr => cos (IZR (fst kr) * t) * rA (snd kr) p
                                                  + sin (IZR (fst kr) * t) * rB (snd kr) p) f)).
    fold (dval f t p).
    replace (v + (cos (IZR (fst e) * t) * rA (snd e) p + sin (IZR (fst e) * t) * rB (snd e) p + dval f t p))
      with ((v + (cos (IZR (fst e) * t) * rA (snd e) p + sin (IZR (fst e) * t) * rB (snd e) p)) + dval f t p)
      by ring.
    apply IH; [| exact Hns' | exact HT | exact HTT'].
    apply inR_add; [exact HV | apply inR_add; apply inR_mul; assumption].
Qed.

Theorem ival_ok (t p : R) (TT : list (J.t * J.t)) (F : list (Z * list (Z * (J.t * J.t))))
    (f : list (Z * list (Z * (R * R)))) (T : list (J.t * J.t)) (ns : list Z) :
  fam_in F f -> Forall (fun kr => map fst (snd kr) = ns) f -> tab_in T ns p -> tab_in TT (map fst f) t ->
  inR (ival TT (iABs F T)) (feval (flist (dents f)) t p).
Proof.
  intros H Hns HT HTT. rewrite feval_dents. rewrite <- (Rplus_0_l (dval f t p)).
  apply (ival_acc_ok J.zero 0 t p TT F f T ns inR_zero H Hns HT HTT).
Qed.

(** * Transposing a table *)

Fixpoint tr {A : Type} (d : A) (n : nat) (rows : list (list A)) : list (list A) :=
  match n with O => [] | S n' => map (hd d) rows :: tr d n' (map (@tl A) rows) end.

Lemma tr_encl {A B : Type} (d : A) (rel : A -> B -> Prop) (g : nat -> Z -> B) (ls : list Z) :
  forall (Rows : list (list A)) (as_ : list nat),
  Forall2 (fun Row a => Forall2 rel Row (map (g a) ls)) Rows as_ ->
  Forall2 (fun Col l => Forall2 rel Col (map (fun a => g a l) as_)) (tr d (length ls) Rows) ls.
Proof.
  induction ls as [| l ls IH]; intros Rows as_ H; [constructor |].
  cbn [length tr]. constructor.
  - induction H as [| Row a Rows as_ HR _ IHH]; [constructor |].
    cbn [map]. constructor; [| exact IHH].
    cbn [map] in HR. inversion HR; subst. reflexivity || (simpl; assumption).
  - apply IH. induction H as [| Row a Rows as_ HR _ IHH]; [constructor |].
    cbn [map]. constructor; [| exact IHH].
    cbn [map] in HR. inversion HR; subst. simpl. assumption.
Qed.

Lemma forall2_map_r {A B C : Type} (Rel : A -> C -> Prop) (f : B -> C) (l1 : list A) (l2 : list B) :
  Forall2 (fun x y => Rel x (f y)) l1 l2 -> Forall2 Rel l1 (map f l2).
Proof. intros H. induction H; constructor; assumption. Qed.

Lemma forall2_map_r' {A B C : Type} (Rel : A -> C -> Prop) (f : B -> C) (l1 : list A) (l2 : list B) :
  Forall2 Rel l1 (map f l2) -> Forall2 (fun x y => Rel x (f y)) l1 l2.
Proof.
  revert l1. induction l2 as [| y l2 IH]; intros l1 H; inversion H; subst; constructor; [assumption |].
  apply IH. assumption.
Qed.

Lemma forall2_map_l {A B C : Type} (Rel : C -> B -> Prop) (f : A -> C) (l1 : list A) (l2 : list B) :
  Forall2 (fun x y => Rel (f x) y) l1 l2 -> Forall2 Rel (map f l1) l2.
Proof. intros H. induction H; constructor; assumption. Qed.

Lemma encl_pair {A : Type} (T : list (J.t * J.t)) (f1 f2 : A -> R) (bs : list A) :
  Forall2 (fun CS b => inR (fst CS) (f1 b) /\ inR (snd CS) (f2 b)) T bs ->
  encl (map fst T) (map f1 bs) /\ encl (map snd T) (map f2 bs).
Proof.
  intros H. induction H as [| CS b T' bs' Hb _ [IH1 IH2]]; [split; constructor |].
  split; cbn [map]; constructor; [exact (proj1 Hb) | exact IH1 | exact (proj2 Hb) | exact IH2].
Qed.

(** * Transforms over one period and the norm they bound *)

Lemma forall2_zip4 {A1 A2 A3 TB : Type} (R1 : A1 -> TB -> Prop) (R2 : A2 -> TB -> Prop) (R3 : A3 -> TB -> Prop)
    (L1 : list A1) (L2 : list A2) (L3 : list A3) (bs : list TB) :
  Forall2 R1 L1 bs -> Forall2 R2 L2 bs -> Forall2 R3 L3 bs ->
  Forall2 (fun x b => fst x = b /\ R1 (fst (snd x)) b /\ R2 (fst (snd (snd x))) b /\ R3 (snd (snd (snd x))) b)
          (combine bs (combine L1 (combine L2 L3))) bs.
Proof.
  intros H1. revert L2 L3. induction H1 as [| x1 b L1 bs H1b _ IH]; intros L2 L3 H2 H3; [constructor |].
  inversion H2 as [| x2 b2 L2' bs2 H2b H2']; subst. inversion H3 as [| x3 b3 L3' bs3 H3b H3']; subst.
  cbn [combine]. constructor; [| apply IH; assumption]. cbn [fst snd]. auto.
Qed.

Lemma forall2_zip2 {A1 TB : Type} (R1 : A1 -> TB -> Prop) (L1 : list A1) (bs : list TB) :
  Forall2 R1 L1 bs -> Forall2 (fun x b => fst x = b /\ R1 (snd x) b) (combine bs L1) bs.
Proof. intros H. induction H as [| x b L bs Hx _ IH]; [constructor |]. cbn [combine]. constructor; auto. Qed.

Section Grid.

Variables (Pn N1 M K1 K2 : nat) (u : fser).
Hypothesis HPn : (0 < Pn)%nat.
Hypothesis HN1 : (0 < N1)%nat.
Hypothesis HM : (0 < M)%nat.
(** The values repeat after one period of M points. *)
Hypothesis Hper : forall a c b, (b < M)%nat ->
  feval u (gpt N1 a) (gpt (Pn * M) (c * M + b)) = feval u (gpt N1 a) (gpt (Pn * M) b).

Let P : Z := Z.of_nat Pn.
Let g (a b : nat) : R := feval u (gpt N1 a) (gpt (Pn * M) b).

(** Grid values, one row per poloidal angle over one period of toroidal angles. *)
Variable Vs : list (list J.t).
Hypothesis HV : Forall2 (fun Row a => encl Row (map (g a) (seq 0 M))) Vs (seq 0 N1).

(** Tables of cos and sin of l 2 pi b / M per mode l of the box and of k 2 pi a / N1 per
    mode k, and an enclosure of 1 / (N1 M). *)
Variables (CT TK : list (list (J.t * J.t))) (INV : J.t).
Hypothesis HCT : Forall2 (fun row l => Forall2 (fun CS b => inR (fst CS) (cos (IZR l * gpt M b)) /\
                                                         inR (snd CS) (sin (IZR l * gpt M b))) row (seq 0 M))
                         CT (zrange K2).
Hypothesis HTK : Forall2 (fun row k => Forall2 (fun CS a => inR (fst CS) (cos (IZR k * gpt N1 a)) /\
                                                          inR (snd CS) (sin (IZR k * gpt N1 a))) row (seq 0 N1))
                         TK (zrange K1).
Hypothesis HINV : inR INV (/ (INR N1 * INR M)).

(** Row transforms: per row, per mode l, the pair (G, H). *)
Definition rowGH (Row : list J.t) : list (J.t * J.t) :=
  map (fun crow => (idot Row (map fst crow), idot Row (map snd crow))) CT.

Definition GHt : list (list (J.t * J.t)) := tr (J.zero, J.zero) (length (zrange K2)) (pmap rowGH Vs).

(** The transforms at (k, P l), from a column of the poloidal table and the
    row transforms at l. *)
Definition iC (tk : list (J.t * J.t)) (gh : list (J.t * J.t)) : J.t :=
  J.mul (J.sub (idot (map fst tk) (map fst gh)) (idot (map snd tk) (map snd gh))) INV.
Definition iS (tk : list (J.t * J.t)) (gh : list (J.t * J.t)) : J.t :=
  J.mul (J.add (idot (map snd tk) (map fst gh)) (idot (map fst tk) (map snd gh))) INV.

(** The real quantities the intervals enclose. *)
Definition rG (l : Z) (a : nat) : R := rowG g M l a.
Definition rH (l : Z) (a : nat) : R := rowH g M l a.
Definition rC (k l : Z) : R :=
  / (INR N1 * INR M) * (fsum (fun a => cos (IZR k * gpt N1 a) * rG l a) N1
                        - fsum (fun a => sin (IZR k * gpt N1 a) * rH l a) N1).
Definition rS (k l : Z) : R :=
  / (INR N1 * INR M) * (fsum (fun a => sin (IZR k * gpt N1 a) * rG l a) N1
                        + fsum (fun a => cos (IZR k * gpt N1 a) * rH l a) N1).

Lemma rowGH_gen (CT' : list (list (J.t * J.t))) (ls : list Z) (Row : list J.t) (a : nat) :
  Forall2 (fun row l => Forall2 (fun CS b => inR (fst CS) (cos (IZR l * gpt M b)) /\
                                            inR (snd CS) (sin (IZR l * gpt M b))) row (seq 0 M)) CT' ls ->
  encl Row (map (g a) (seq 0 M)) ->
  Forall2 (fun GH l => inR (fst GH) (rG l a) /\ inR (snd GH) (rH l a))
          (map (fun crow => (idot Row (map fst crow), idot Row (map snd crow))) CT') ls.
Proof.
  intros HC0 HR. induction HC0 as [| crow l CT' ls' Hc _ IH]; [constructor |].
  cbn [map]. constructor; [| exact IH]. cbn [fst snd]. unfold rG, rH, rowG, rowH.
  destruct (encl_pair crow (fun b => cos (IZR l * gpt M b)) (fun b => sin (IZR l * gpt M b)) (seq 0 M) Hc)
    as [Ec Es].
  pose proof (idot_ok _ _ _ _ HR Ec) as G1. pose proof (idot_ok _ _ _ _ HR Es) as G2.
  rewrite rdot_map_seq in G1, G2. cbn [plus] in G1, G2. split; assumption.
Qed.

Lemma GHt_ok :
  Forall2 (fun Col l => Forall2 (fun GH a => inR (fst GH) (rG l a) /\ inR (snd GH) (rH l a)) Col (seq 0 N1))
          GHt (zrange K2).
Proof.
  unfold GHt, pmap.
  assert (Hrows : Forall2 (fun Row a => Forall2 (fun GH (x : R * R) => inR (fst GH) (fst x) /\ inR (snd GH) (snd x))
                                                Row (map (fun l => (rG l a, rH l a)) (zrange K2)))
                          (map rowGH Vs) (seq 0 N1)).
  { apply forall2_map_l. eapply Forall2_impl; [| exact HV]. intros Row a HR.
    apply forall2_map_r. exact (rowGH_gen CT (zrange K2) Row a HCT HR). }
  pose proof (tr_encl (J.zero, J.zero) (fun GH (x : R * R) => inR (fst GH) (fst x) /\ inR (snd GH) (snd x))
                (fun a l => (rG l a, rH l a)) (zrange K2) (map rowGH Vs) (seq 0 N1) Hrows) as T.
  eapply Forall2_impl; [| exact T]. intros Col l H.
  exact (forall2_map_r' (fun GH (x : R * R) => inR (fst GH) (fst x) /\ inR (snd GH) (snd x))
           (fun a => (rG l a, rH l a)) Col (seq 0 N1) H).
Qed.

Lemma iCS_ok (tk gh : list (J.t * J.t)) (k l : Z) :
  Forall2 (fun CS a => inR (fst CS) (cos (IZR k * gpt N1 a)) /\ inR (snd CS) (sin (IZR k * gpt N1 a))) tk
          (seq 0 N1) ->
  Forall2 (fun GH a => inR (fst GH) (rG l a) /\ inR (snd GH) (rH l a)) gh (seq 0 N1) ->
  inR (iC tk gh) (rC k l) /\ inR (iS tk gh) (rS k l).
Proof.
  intros Ht Hg.
  destruct (encl_pair tk _ _ _ Ht) as [Tc Ts]. destruct (encl_pair gh _ _ _ Hg) as [Gc Gs].
  pose proof (idot_ok _ _ _ _ Tc Gc) as D1. pose proof (idot_ok _ _ _ _ Ts Gs) as D2.
  pose proof (idot_ok _ _ _ _ Ts Gc) as D3. pose proof (idot_ok _ _ _ _ Tc Gs) as D4.
  rewrite rdot_map_seq in D1, D2, D3, D4. cbn [plus] in D1, D2, D3, D4.
  unfold iC, iS, rC, rS. split; rewrite Rmult_comm; apply inR_mul; try exact HINV.
  - apply inR_sub; assumption.
  - apply inR_add; assumption.
Qed.

(** The transforms over one period are the transforms over the whole grid. *)
Lemma rCS_dft (k l : Z) : rC k l = dftc N1 (Pn * M) u k (P * l) /\ rS k l = dfts N1 (Pn * M) u k (P * l).
Proof.
  assert (Hfg : forall a c b, (b < M)%nat ->
            (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) a (c * M + b)%nat = g a b)
    by (intros a c b Hb; apply Hper, Hb).
  assert (EG : forall a, rowG (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) (Pn * M) (P * l) a = INR Pn * rG l a)
    by (intros a; exact (rowG_per Pn M _ g a HPn HM (Hfg a) l)).
  assert (EH : forall a, rowH (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) (Pn * M) (P * l) a = INR Pn * rH l a)
    by (intros a; exact (rowH_per Pn M _ g a HPn HM (Hfg a) l)).
  assert (HP0 : INR Pn <> 0) by (apply not_0_INR; lia).
  assert (HN0 : INR N1 <> 0) by (apply not_0_INR; lia).
  assert (HM0 : INR M <> 0) by (apply not_0_INR; lia).
  assert (E1 : fsum (fun a => cos (IZR k * gpt N1 a)
                             * rowG (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) (Pn * M) (P * l) a
                             - sin (IZR k * gpt N1 a)
                             * rowH (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) (Pn * M) (P * l) a) N1
               = INR Pn * (fsum (fun a => cos (IZR k * gpt N1 a) * rG l a) N1
                           - fsum (fun a => sin (IZR k * gpt N1 a) * rH l a) N1)).
  { rewrite <- fsum_minus', <- fsum_scal. apply fsum_ext. intros a. rewrite EG, EH. ring. }
  assert (E2 : fsum (fun a => sin (IZR k * gpt N1 a)
                             * rowG (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) (Pn * M) (P * l) a
                             + cos (IZR k * gpt N1 a)
                             * rowH (fun a b => feval u (gpt N1 a) (gpt (Pn * M) b)) (Pn * M) (P * l) a) N1
               = INR Pn * (fsum (fun a => sin (IZR k * gpt N1 a) * rG l a) N1
                           + fsum (fun a => cos (IZR k * gpt N1 a) * rH l a) N1)).
  { rewrite <- fsum_plus, <- fsum_scal. apply fsum_ext. intros a. rewrite EG, EH. ring. }
  rewrite dftc_rows, dfts_rows, E1, E2. unfold rC, rS. rewrite mult_INR. split; field; auto.
Qed.

(** ** The norm of a family of period P from a crude norm on a wider strip *)

Section Model.

Variables (D : nat) (w w' Mw B : R).
Hypothesis Hw : 0 <= w.
Hypothesis Hww : w <= w'.
Hypothesis HD1 : (D < 10 * S K1)%nat.
Hypothesis HD2 : (D < Pn * S K2)%nat.
Hypothesis Cu : is_canon u.
Hypothesis Qu : FourierPer.is_per (Z.of_nat Pn) u.
Hypothesis Hu : nbound w' Mw u.

(** The weights and aliasing factors per mode, and the constants. *)
Variables (WA EA WB EB : list J.t) (IM IT IB I2 : J.t).
Hypothesis HWA : Forall2 (fun X k => inR X (exp (w * Rabs (IZR k)))) WA (zrange K1).
Hypothesis HEA : Forall2 (fun X k => inR X (exp (- (w' * (INR N1 - Rabs (IZR k)))))) EA (zrange K1).
Hypothesis HWB : Forall2 (fun X l => inR X (exp (w * (kappa * Rabs (IZR (P * l)))))) WB (zrange K2).
Hypothesis HEB : Forall2 (fun X l => inR X (exp (- (w' * (kappa * (INR (Pn * M) - Rabs (IZR (P * l)))))))) EB
                   (zrange K2).
Hypothesis HIM : inR IM Mw.
Hypothesis HIT : inR IT (exp (- ((w' - w) * (kappa * INR (S D))))).
Hypothesis HIB : inR IB B.
Hypothesis HI2 : inR I2 2.

Definition iterm (k l : Z) (tk gh : list (J.t * J.t)) (wa ea wb eb : J.t) : J.t :=
  if in_dq D k (P * l)
  then J.mul (J.add (J.add (J.abs (iC tk gh)) (J.abs (iS tk gh))) (J.mul I2 (J.mul IM (J.add ea eb))))
             (J.mul wa wb)
  else J.zero.

Definition ibox : J.t :=
  isuml (pmap (fun x => let '(k, (tk, (wa, ea))) := x in
              isuml (map (fun y => let '(l, (gh, (wb, eb))) := y in iterm k l tk gh wa ea wb eb)
                         (combine (zrange K2) (combine GHt (combine WB EB)))))
             (combine (zrange K1) (combine TK (combine WA EA)))).

(** The bound the model gives, and its comparison with the claim. *)
Definition bnd_model : J.t := J.add ibox (J.mul IT IM).

Definition check_model : bool := ile bnd_model IB.

(** The real box the intervals enclose. *)
Definition ea (k : Z) : R := exp (- (w' * (INR N1 - Rabs (IZR k)))).
Definition eb (l : Z) : R := exp (- (w' * (kappa * (INR (Pn * M) - Rabs (IZR (P * l)))))).

Definition rterm (k l : Z) : R :=
  if in_dq D k (P * l)
  then (Rabs (rC k l) + Rabs (rS k l) + 2 * (Mw * (ea k + eb l)))
       * (exp (w * Rabs (IZR k)) * exp (w * (kappa * Rabs (IZR (P * l)))))
  else 0.

Lemma iterm_ok (k l : Z) (tk gh : list (J.t * J.t)) (wa ea' wb eb' : J.t) :
  Forall2 (fun CS a => inR (fst CS) (cos (IZR k * gpt N1 a)) /\ inR (snd CS) (sin (IZR k * gpt N1 a))) tk
          (seq 0 N1) ->
  Forall2 (fun GH a => inR (fst GH) (rG l a) /\ inR (snd GH) (rH l a)) gh (seq 0 N1) ->
  inR wa (exp (w * Rabs (IZR k))) -> inR ea' (ea k) ->
  inR wb (exp (w * (kappa * Rabs (IZR (P * l))))) -> inR eb' (eb l) ->
  inR (iterm k l tk gh wa ea' wb eb') (rterm k l).
Proof.
  intros Ht Hg Hwa Hea Hwb Heb. unfold iterm, rterm.
  destruct (in_dq D k (P * l)); [| exact inR_zero].
  destruct (iCS_ok tk gh k l Ht Hg) as [HC HS].
  apply inR_mul; [| apply inR_mul; assumption].
  apply inR_add; [apply inR_add; apply inR_abs; assumption |].
  apply inR_mul; [exact HI2 | apply inR_mul; [exact HIM | apply inR_add; assumption]].
Qed.

Lemma ibox_ok : inR ibox (bsum K1 K2 rterm).
Proof.
  rewrite bsum_zrange. unfold ibox, pmap. apply isuml_ok. apply forall2_map_l. apply forall2_map_r.
  eapply Forall2_impl; [| exact (forall2_zip4 _ _ _ _ _ _ _ HTK HWA HEA)].
  intros [k [tk [wa ea']]] k' [Ek [Ht [Hwa Hea]]]. cbn [fst snd] in *. subst k'.
  apply isuml_ok. apply forall2_map_l. apply forall2_map_r.
  eapply Forall2_impl; [| exact (forall2_zip4 _ _ _ _ _ _ _ GHt_ok HWB HEB)].
  intros [l [gh [wb eb']]] l' [El [Hg [Hwb Heb]]]. cbn [fst snd] in *. subst l'.
  apply iterm_ok; assumption.
Qed.

Lemma exp_min_le (x y : R) : exp (- (w' * Rmin x y)) <= exp (- (w' * x)) + exp (- (w' * y)).
Proof.
  pose proof (exp_pos (- (w' * x))). pose proof (exp_pos (- (w' * y))).
  destruct (Rle_dec x y) as [Hxy | Hxy]; [rewrite Rmin_left by exact Hxy | rewrite Rmin_right by lra]; lra.
Qed.

Theorem check_model_ok : check_model = true -> nbound w B u.
Proof.
  intros Hc.
  assert (HPz : (0 < P)%Z) by (unfold P; lia).
  assert (HN2 : (0 < Pn * M)%nat) by lia.
  assert (HD2' : (D < Z.to_nat P * S K2)%nat) by (unfold P; rewrite Nat2Z.id; exact HD2).
  pose proof (nbound_model_dia P HPz N1 (Pn * M) K1 K2 D u w w' Mw HN1 HN2 Hw Hww HD1 HD2' Cu Qu Hu) as HM0.
  assert (HMw : 0 <= Mw) by exact (nbound_nonneg _ _ _ Hu).
  apply (nbound_le _ (bsum K1 K2 rterm + exp (- ((w' - w) * (kappa * INR (S D)))) * Mw)).
  - apply ile_correct with (1 := Hc); [| exact HIB].
    apply inR_add; [exact ibox_ok | apply inR_mul; assumption].
  - eapply nbound_le; [| exact HM0]. apply Rplus_le_compat_r. apply bsum_le. intros k l _.
    unfold rterm. destruct (in_dq D k (P * l)); [| lra].
    destruct (rCS_dft k l) as [E1 E2]. rewrite E1, E2.
    assert (Ew : wt w k (P * l) = exp (w * Rabs (IZR k)) * exp (w * (kappa * Rabs (IZR (P * l)))))
      by (unfold wt, msize; rewrite <- exp_plus; f_equal; ring).
    rewrite Ew.
    assert (Ee : exp (- (w' * dmode N1 (Pn * M) k (P * l))) <= ea k + eb l) by (unfold dmode, ea, eb; apply exp_min_le).
    pose proof (Rabs_pos (dftc N1 (Pn * M) u k (P * l))). pose proof (Rabs_pos (dfts N1 (Pn * M) u k (P * l))).
    pose proof (exp_pos (w * Rabs (IZR k))). pose proof (exp_pos (w * (kappa * Rabs (IZR (P * l))))).
    apply Rmult_le_compat_r; [apply Rmult_le_pos; lra |]. nra.
Qed.

(** The mean of the family lies within the aliasing factor of the transform at
    the origin. *)
Theorem model_mean (tk gh : list (J.t * J.t)) :
  Forall2 (fun CS a => inR (fst CS) (cos (IZR 0 * gpt N1 a)) /\ inR (snd CS) (sin (IZR 0 * gpt N1 a))) tk
          (seq 0 N1) ->
  Forall2 (fun GH a => inR (fst GH) (rG 0 a) /\ inR (snd GH) (rH 0 a)) gh (seq 0 N1) ->
  exists c, inR (iC tk gh) c /\ Rabs (c - fc u 0 0) <= Mw * exp (- (w' * dmode N1 (Pn * M) 0 0)).
Proof.
  intros Ht Hg. destruct (iCS_ok tk gh 0 0 Ht Hg) as [HC _].
  exists (rC 0 0). split; [exact HC |].
  destruct (rCS_dft 0 0) as [E _]. rewrite E. replace (P * 0)%Z with 0%Z by ring.
  apply mean_err; [lia | lia | lra | exact Cu | exact Hu].
Qed.

End Model.

(** ** The exact norm of a finitely supported family of period P *)

Section Exact.

Variables (rho B : R).
Hypothesis HN1x : (2 * K1 < N1)%nat.
Hypothesis HN2x : (2 * Kfull P K2 < Pn * M)%nat.
Hypothesis Hs : supp K1 (Kfull P K2) u.
Hypothesis Cu : is_canon u.
Hypothesis Qu : FourierPer.is_per P u.

Variables (WA WB : list J.t) (IB : J.t).
Hypothesis HWA : Forall2 (fun X k => inR X (exp (rho * Rabs (IZR k)))) WA (zrange K1).
Hypothesis HWB : Forall2 (fun X l => inR X (exp (rho * (kappa * Rabs (IZR (P * l)))))) WB (zrange K2).
Hypothesis HIB : inR IB B.

Definition iterm_x (tk gh : list (J.t * J.t)) (wa wb : J.t) : J.t :=
  J.mul (J.add (J.abs (iC tk gh)) (J.abs (iS tk gh))) (J.mul wa wb).

(** The weighted sum over the box from the row transforms GH, which several
    weights may share. *)
Definition ibox_xt (GH : list (list (J.t * J.t))) : J.t :=
  isuml (pmap (fun x => let '(k, (tk, wa)) := x in
              isuml (map (fun y => let '(l, (gh, wb)) := y in iterm_x tk gh wa wb)
                         (combine (zrange K2) (combine GH WB))))
             (combine (zrange K1) (combine TK WA))).

Definition check_exact_t (GH : list (list (J.t * J.t))) : bool := ile (ibox_xt GH) IB.

Definition ibox_x : J.t := ibox_xt GHt.

Definition check_exact : bool := check_exact_t GHt.

Definition rterm_x (k l : Z) : R :=
  (Rabs (rC k l) + Rabs (rS k l)) * (exp (rho * Rabs (IZR k)) * exp (rho * (kappa * Rabs (IZR (P * l))))).

Lemma forall2_zip3' {A1 A2 TB : Type} (R1 : A1 -> TB -> Prop) (R2 : A2 -> TB -> Prop)
    (L1 : list A1) (L2 : list A2) (bs : list TB) :
  Forall2 R1 L1 bs -> Forall2 R2 L2 bs ->
  Forall2 (fun x b => fst x = b /\ R1 (fst (snd x)) b /\ R2 (snd (snd x)) b) (combine bs (combine L1 L2)) bs.
Proof.
  intros H1. revert L2. induction H1 as [| x1 b L1 bs H1b _ IH]; intros L2 H2; [constructor |].
  inversion H2 as [| x2 b2 L2' bs2 H2b H2']; subst.
  cbn [combine]. constructor; [| apply IH; assumption]. cbn [fst snd]. auto.
Qed.

Lemma ibox_x_ok : inR ibox_x (bsum K1 K2 rterm_x).
Proof.
  rewrite bsum_zrange. unfold ibox_x, ibox_xt, pmap. apply isuml_ok. apply forall2_map_l. apply forall2_map_r.
  eapply Forall2_impl; [| exact (forall2_zip3' _ _ _ _ _ HTK HWA)].
  intros [k [tk wa]] k' [Ek [Ht Hwa]]. cbn [fst snd] in *. subst k'.
  apply isuml_ok. apply forall2_map_l. apply forall2_map_r.
  eapply Forall2_impl; [| exact (forall2_zip3' _ _ _ _ _ GHt_ok HWB)].
  intros [l [gh wb]] l' [El [Hg Hwb]]. cbn [fst snd] in *. subst l'.
  destruct (iCS_ok tk gh k l Ht Hg) as [HC HS]. unfold iterm_x, rterm_x.
  apply inR_mul; [apply inR_add; apply inR_abs; assumption | apply inR_mul; assumption].
Qed.

(** The interval sum encloses the weighted sum of the transforms, which
    bounds the norm ([exact_nbound]). *)
Theorem ibox_x_rexact : inR ibox_x (rexact Pn N1 M K1 K2 u rho).
Proof.
  replace (rexact Pn N1 M K1 K2 u rho) with (bsum K1 K2 rterm_x); [exact ibox_x_ok |].
  unfold rexact. apply bsum_ext_in. intros k l _. unfold rterm_x. destruct (rCS_dft k l) as [E1 E2].
  rewrite E1, E2. unfold P, wt, msize. rewrite <- exp_plus. f_equal. f_equal. ring.
Qed.

Theorem check_exact_ok : check_exact = true -> nbound rho B u.
Proof.
  intros Hc.
  assert (HPz : (0 < P)%Z) by (unfold P; lia).
  pose proof (nbound_exact_per P HPz N1 (Pn * M) K1 K2 u rho HN1x HN2x Hs Cu Qu) as HE.
  apply (nbound_le _ (bsum K1 K2 rterm_x)).
  - exact (ile_correct _ _ _ _ Hc ibox_x_ok HIB).
  - eapply nbound_le; [| exact HE]. apply bsum_le. intros k l _.
    unfold rterm_x. destruct (rCS_dft k l) as [E1 E2]. rewrite E1, E2.
    assert (Ew : wt rho k (P * l) = exp (rho * Rabs (IZR k)) * exp (rho * (kappa * Rabs (IZR (P * l)))))
      by (unfold wt, msize; rewrite <- exp_plus; f_equal; ring).
    rewrite Ew. lra.
Qed.

End Exact.

End Grid.

End Engine.
