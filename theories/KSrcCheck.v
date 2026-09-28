(** The check of one source's seed along a finite torus.

    On a grid of N1 x N2 points of the whole torus, the values of the
    reference torus (R, Z) and of the seed Y come from their dense
    coefficients ([gvals_ok] of KGrid.v); at each point the defect is
    1 - q Y^2 with q the squared distance to the source ([dgrid_ok]). Its
    exact norm is read from its transforms ([check_exact_ok] of KEngine.v).
    The norm of a dense family is the weighted sum of its coefficients
    ([iesum_ok]), and its value at the origin is read with the tables of
    angle zero ([ival0_ok]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Stellarocq Require Import KAMScalar Fourier FourierEval FourierDFT FourierList FourierCanon
  Hypotheses Invariance CoilSym FieldKern FieldFam FieldModel KFix KCheckKern KEngine KGrid.
Import ListNotations.
Local Open Scope R_scope.

Lemma qk_dot (sc : src) (R0 phi Z0 : R) :
  qk sc (kx1 R0 phi) (kx2 R0 phi) Z0 = dot3 (v3sub (cyl R0 phi Z0) (spt sc)) (v3sub (cyl R0 phi Z0) (spt sc)).
Proof. unfold qk, kx1, kx2, cyl, spt, v3sub, dot3. simpl. ring. Qed.

Module SrcCheck (J : RI).

Module G := GridOps J.
Import G G.EN G.EN.KO.

Definition cst (m : Z) : J.t := J.of_q m 0.
Definition one : J.t := J.of_q 1 0.

(** * The defect on a grid *)

Definition dpt (p : i3) (CS : J.t * J.t) (Rr Zz Y : J.t) : J.t :=
  J.sub one (J.mul (iqk p (icyl Rr (fst CS) (snd CS) Zz)) (J.mul Y Y)).

Fixpoint drow (p : i3) (CSs : list (J.t * J.t)) (Rs Zs Ys : list J.t) : list J.t :=
  match CSs, Rs, Zs, Ys with
  | CS :: CSs', Rr :: Rs', Zz :: Zs', Y :: Ys' => dpt p CS Rr Zz Y :: drow p CSs' Rs' Zs' Ys'
  | _, _, _, _ => []
  end.

Fixpoint dgrid (p : i3) (CSs : list (J.t * J.t)) (GR GZ GY : list (list J.t)) : list (list J.t) :=
  match GR, GZ, GY with
  | Rs :: GR', Zs :: GZ', Ys :: GY' => drow p CSs Rs Zs Ys :: dgrid p CSs GR' GZ' GY'
  | _, _, _ => []
  end.

Definition rdef (sc : src) (fR fZ fY : R -> R -> R) (t p : R) : R :=
  1 - qk sc (kx1 (fR t p) p) (kx2 (fR t p) p) (fZ t p) * (fY t p * fY t p).

Lemma dpt_ok (p : i3) (sc : src) (CS : J.t * J.t) (Rr Zz Y : J.t) (R0 phi Z0 y : R) :
  inR3 p (spt sc) -> inR (fst CS) (cos phi) -> inR (snd CS) (sin phi) -> inR Rr R0 -> inR Zz Z0 -> inR Y y ->
  inR (dpt p CS Rr Zz Y) (1 - qk sc (kx1 R0 phi) (kx2 R0 phi) Z0 * (y * y)).
Proof.
  intros Hp HC HS HR HZ HY. unfold dpt. apply inR_sub; [apply inR_Z |].
  apply inR_mul; [| apply inR_mul; assumption].
  rewrite qk_dot. apply inR_iqk; [exact Hp | apply inR3_cyl; assumption].
Qed.

Theorem dgrid_ok (p : i3) (sc : src) (CSs : list (J.t * J.t)) (GR GZ GY : list (list J.t)) (N1 N2 : nat)
    (fR fZ fY : R -> R -> R) (ta pb : nat -> R) :
  inR3 p (spt sc) ->
  Forall2 (fun CS b => inR (fst CS) (cos (pb b)) /\ inR (snd CS) (sin (pb b))) CSs (seq 0 N2) ->
  ggrid GR N1 N2 fR ta pb -> ggrid GZ N1 N2 fZ ta pb -> ggrid GY N1 N2 fY ta pb ->
  ggrid (dgrid p CSs GR GZ GY) N1 N2 (rdef sc fR fZ fY) ta pb.
Proof.
  intros Hp HCS. unfold ggrid. generalize (seq 0 N1). intros as_. revert GR GZ GY.
  induction as_ as [| a as_ IH]; intros GR GZ GY HR HZ HY.
  - inversion HR; subst. constructor.
  - inversion HR as [| Rs x GR' xs HRs HR']; subst. inversion HZ as [| Zs y GZ' ys HZs HZ']; subst.
    inversion HY as [| Ys z GY' zs HYs HY']; subst.
    cbn [dgrid]. constructor; [| apply IH; assumption].
    clear -Hp HCS HRs HZs HYs. revert Rs Zs Ys HRs HZs HYs.
    induction HCS as [| CS b CSs bs [HC HS] _ IHb]; intros Rs Zs Ys HRs HZs HYs.
    + inversion HRs; subst. constructor.
    + inversion HRs as [| Rr r Rs' rs Hr HRs']; subst. inversion HZs as [| Zz z Zs' zs' Hz HZs']; subst.
      inversion HYs as [| Y y Ys' ys' Hy HYs']; subst.
      cbn [drow map]. constructor; [| apply IHb; assumption].
      unfold rdef. apply dpt_ok; assumption.
Qed.

(** * Norms and values of a dense family *)

(** The weighted sum of the coefficients, with tables of e^(w |k|) aligned
    with the rows and of e^(w kappa |n|) aligned with the entries. *)
Definition iesum (F : list (Z * list (Z * (J.t * J.t)))) (WK : list J.t) (WN : list J.t) : J.t :=
  isuml (zipw (fun kr wk => isuml (zipw (fun e wn => J.mul (J.add (J.abs (fst (snd e))) (J.abs (snd (snd e))))
                                                         (J.mul wk wn)) (snd kr) WN)) F WK).

Lemma esum_flat_map (f : fent -> R) (g : Z * list (Z * (R * R)) -> list fent) (l : list (Z * list (Z * (R * R)))) :
  esum f (flat_map g l) = rsuml (map (fun x => esum f (g x)) l).
Proof. induction l as [| x l IH]; [reflexivity |]. cbn [flat_map map]. rewrite esum_app', IH. reflexivity. Qed.

Lemma esum_map_row (w : R) (k : Z) (row : list (Z * (R * R))) :
  esum (ewt w) (map (fun e => let '(n, (c, s)) := e in mkfent k n c s) row)
  = rsuml (map (fun e => (Rabs (fst (snd e)) + Rabs (snd (snd e))) * (exp (w * Rabs (IZR k))
                                                                         * exp (w * (kappa * Rabs (IZR (fst e)))))) row).
Proof.
  induction row as [| [n [c s]] row IH]; [reflexivity |].
  cbn [map]. rewrite esum_cons, IH. unfold ewt, wt, msize. simpl. rewrite <- exp_plus.
  unfold rsuml. simpl. f_equal. f_equal. f_equal. ring.
Qed.

Theorem iesum_ok (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) (ns : list Z)
    (WK WN : list J.t) (w : R) :
  fam_in F f -> Forall (fun kr => map fst (snd kr) = ns) f ->
  Forall2 (fun X k => inR X (exp (w * Rabs (IZR k)))) WK (map fst f) ->
  Forall2 (fun X n => inR X (exp (w * (kappa * Rabs (IZR n))))) WN ns ->
  inR (iesum F WK WN) (esum (ewt w) (dents f)).
Proof.
  intros HF Hns HWK HWN. unfold iesum, dents. rewrite esum_flat_map. apply isuml_ok.
  revert WK HWK. induction HF as [| I e F f [Ek HR] _ IH]; intros WK HWK; [inversion HWK; subst; constructor |].
  inversion HWK as [| wk k WK' ks Hwk HWK']; subst.
  apply Forall_cons_iff in Hns. destruct Hns as [Hn Hns'].
  cbn [zipw map]. constructor; [| apply IH; assumption].
  destruct e as [k row]. cbn [fst snd] in *. rewrite esum_map_row. apply isuml_ok.
  subst ns. clear -HR Hwk HWN. revert WN HWN. induction HR as [| Ie re row' rs [En [HC HS]] _ IHr];
    intros WN HWN; [inversion HWN; subst; constructor |].
  inversion HWN as [| wn n WN' ns' Hwn HWN']; subst.
  cbn [zipw map]. constructor; [| apply IHr; assumption].
  apply inR_mul; [apply inR_add; apply inR_abs; assumption | apply inR_mul; [exact Hwk | exact Hwn]].
Qed.

(** The value at the origin: every table entry is (1, 0). *)
Definition t0 (n : nat) : list (J.t * J.t) := repeat (cst 1, J.zero) n.

Lemma t0_ok (ns : list Z) : tab_in (t0 (length ns)) ns 0.
Proof.
  induction ns as [| n ns IH]; [constructor |]. cbn [length t0 repeat]. constructor; [| exact IH].
  cbn [fst snd]. rewrite Rmult_0_r, cos_0, sin_0. split; [apply inR_Z | apply inR_zero].
Qed.

Theorem ival0_ok (F : list (Z * list (Z * (J.t * J.t)))) (f : list (Z * list (Z * (R * R)))) (ns : list Z) :
  fam_in F f -> Forall (fun kr => map fst (snd kr) = ns) f ->
  inR (ival (t0 (length (map fst f))) (iABs F (t0 (length ns)))) (feval (flist (dents f)) 0 0).
Proof. intros HF Hns. apply (ival_ok 0 0 _ F f _ ns HF Hns (t0_ok ns) (t0_ok (map fst f))). Qed.

End SrcCheck.
