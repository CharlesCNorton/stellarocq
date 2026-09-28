(** Families given by finite lists of modes.

    A certificate carries a torus, the seeds of its Newton inverses and the
    normal of its frame as finite lists of modes (m, n) with a cosine and a
    sine coefficient ([fent]); [flist] is the family they sum to. Its
    function at a point is the finite trigonometric sum ([feval_flist]), its
    norm on a strip is at most the weighted sum of the absolute values of the
    coefficients ([nbound_flist]), its derivatives are the lists of the
    differentiated modes ([dt_flist], [dp_flist]), and it is even, odd or of
    one field period when every entry is ([flist_even], [flist_odd],
    [flist_per]). Symmetrised by [canon] it keeps its function, its norm
    bound and those classes ([canon_per]). *)

From Coq Require Import ZArith Reals Lra Lia List Bool.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierSum FourierEval FourierProd FourierMul
  FourierAlg FourierMulEval FourierParity FourierDFT FourierCanon FourierPer.
Import ListNotations.
Local Open Scope R_scope.

Record fent := mkfent { fe_m : Z ; fe_n : Z ; fe_c : R ; fe_s : R }.

Definition flist (l : list fent) : fser :=
  fold_right (fun e acc => fadd (fsingle (fe_m e) (fe_n e) (fe_c e) (fe_s e)) acc) fzero l.

Definition esum (f : fent -> R) (l : list fent) : R := fold_right (fun e acc => f e + acc) 0 l.

Lemma flist_cons (e : fent) (l : list fent) :
  flist (e :: l) = fadd (fsingle (fe_m e) (fe_n e) (fe_c e) (fe_s e)) (flist l).
Proof. reflexivity. Qed.

Lemma esum_nonneg (f : fent -> R) (l : list fent) : (forall e, 0 <= f e) -> 0 <= esum f l.
Proof. intros H. induction l as [| e l IH]; simpl; [lra | pose proof (H e); lra]. Qed.

(** * Norm and function *)

Definition ewt (rho : R) (e : fent) : R := (Rabs (fe_c e) + Rabs (fe_s e)) * wt rho (fe_m e) (fe_n e).

Theorem nbound_flist (rho : R) (l : list fent) : nbound rho (esum (ewt rho) l) (flist l).
Proof.
  induction l as [| e l IH].
  - simpl. apply nbound_fzero.
  - rewrite flist_cons. simpl. apply nbound_fadd; [apply nbound_fsingle | exact IH].
Qed.

Lemma fin_flist (rho : R) (l : list fent) : exists M, nbound rho M (flist l).
Proof. exists (esum (ewt rho) l). apply nbound_flist. Qed.

Definition eterm (t p : R) (e : fent) : R :=
  fe_c e * cos (mode (fe_m e) (fe_n e) t p) + fe_s e * sin (mode (fe_m e) (fe_n e) t p).

Theorem feval_flist (l : list fent) (t p : R) : feval (flist l) t p = esum (eterm t p) l.
Proof.
  induction l as [| e l IH].
  - simpl. unfold feval. rewrite (zz_sum_ext _ (fun _ _ => 0)); [apply zz_sum_const0 |].
    intros m n. unfold term. simpl. ring.
  - rewrite flist_cons. simpl.
    rewrite (feval_fadd _ _ _ _ t p (nbound_fsingle 0 (fe_m e) (fe_n e) (fe_c e) (fe_s e))
               (nbound_flist 0 l)).
    rewrite feval_fsingle, IH. reflexivity.
Qed.

(** * Derivatives *)

Definition edt (e : fent) : fent := mkfent (fe_m e) (fe_n e) (IZR (fe_m e) * fe_s e) (- (IZR (fe_m e) * fe_c e)).
Definition edp (e : fent) : fent := mkfent (fe_m e) (fe_n e) (IZR (fe_n e) * fe_s e) (- (IZR (fe_n e) * fe_c e)).

Lemma dt_fadd (u v : fser) : feq (dt (fadd u v)) (fadd (dt u) (dt v)).
Proof. intros m n. simpl. split; ring. Qed.

Lemma dp_fadd (u v : fser) : feq (dp (fadd u v)) (fadd (dp u) (dp v)).
Proof. intros m n. simpl. split; ring. Qed.

Lemma dt_fsingle (k1 k2 : Z) (c s : R) : feq (dt (fsingle k1 k2 c s)) (fsingle k1 k2 (IZR k1 * s) (- (IZR k1 * c))).
Proof.
  intros m n. unfold fsingle, at2. simpl.
  destruct (Z.eqb_spec m k1) as [-> |]; destruct (Z.eqb_spec n k2) as [-> |]; simpl; split; ring.
Qed.

Lemma dp_fsingle (k1 k2 : Z) (c s : R) : feq (dp (fsingle k1 k2 c s)) (fsingle k1 k2 (IZR k2 * s) (- (IZR k2 * c))).
Proof.
  intros m n. unfold fsingle, at2. simpl.
  destruct (Z.eqb_spec m k1) as [-> |]; destruct (Z.eqb_spec n k2) as [-> |]; simpl; split; ring.
Qed.

Theorem dt_flist (l : list fent) : feq (dt (flist l)) (flist (map edt l)).
Proof.
  induction l as [| e l IH].
  - intros m n. simpl. split; ring.
  - intros m n. rewrite flist_cons. simpl map. rewrite flist_cons.
    destruct (dt_fadd (fsingle (fe_m e) (fe_n e) (fe_c e) (fe_s e)) (flist l) m n) as [A1 A2].
    destruct (dt_fsingle (fe_m e) (fe_n e) (fe_c e) (fe_s e) m n) as [B1 B2].
    destruct (IH m n) as [C1 C2].
    rewrite A1, A2. cbn [fc fs fadd]. rewrite B1, B2, C1, C2. unfold edt. simpl. split; reflexivity.
Qed.

Theorem dp_flist (l : list fent) : feq (dp (flist l)) (flist (map edp l)).
Proof.
  induction l as [| e l IH].
  - intros m n. simpl. split; ring.
  - intros m n. rewrite flist_cons. simpl map. rewrite flist_cons.
    destruct (dp_fadd (fsingle (fe_m e) (fe_n e) (fe_c e) (fe_s e)) (flist l) m n) as [A1 A2].
    destruct (dp_fsingle (fe_m e) (fe_n e) (fe_c e) (fe_s e) m n) as [B1 B2].
    destruct (IH m n) as [C1 C2].
    rewrite A1, A2. cbn [fc fs fadd]. rewrite B1, B2, C1, C2. unfold edp. simpl. split; reflexivity.
Qed.

(** * Classes *)

Lemma flist_even (l : list fent) : List.Forall (fun e => fe_s e = 0) l -> is_even (flist l).
Proof.
  intros H. induction H as [| e l He _ IH]; intros m n; simpl; [reflexivity |].
  unfold at2. rewrite (IH m n), He. destruct (_ && _)%bool; ring.
Qed.

Lemma flist_odd (l : list fent) : List.Forall (fun e => fe_c e = 0) l -> is_odd (flist l).
Proof.
  intros H. induction H as [| e l He _ IH]; intros m n; simpl; [reflexivity |].
  unfold at2. rewrite (IH m n), He. destruct (_ && _)%bool; ring.
Qed.

Lemma flist_per (P : Z) (l : list fent) :
  List.Forall (fun e => (fe_n e mod P = 0)%Z) l -> is_per P (flist l).
Proof.
  intros H. induction H as [| e l He _ IH]; intros m n Hn; simpl; [split; reflexivity |].
  destruct (IH m n Hn) as [A B]. rewrite A, B. unfold at2.
  destruct (Z.eqb_spec n (fe_n e)) as [-> | Hne].
  - exfalso. apply Hn. exact He.
  - rewrite andb_false_r. split; ring.
Qed.

Lemma canon_per (P : Z) (u : fser) : is_per P u -> is_per P (canon u).
Proof.
  intros H m n Hn. unfold canon, ccan, scan. simpl.
  assert (Hn' : off P (- n)).
  { unfold off in *. intros E. apply Hn.
    destruct (Z.eq_dec P 0) as [HP0 | HP0].
    - subst P. rewrite Zmod_0_r in E |- *. lia.
    - apply Z.mod_divide in E; [| exact HP0]. apply Z.mod_divide; [exact HP0 |].
      destruct E as [k Hk]. exists (- k)%Z. lia. }
  destruct (H m n Hn) as [A B]. destruct (H (- m)%Z (- n)%Z Hn') as [C D].
  rewrite A, B, C, D. split; ring.
Qed.
