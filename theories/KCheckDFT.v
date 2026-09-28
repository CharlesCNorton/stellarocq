(** Discrete transforms of the values of a family on a grid, row by row.

    [dftc] and [dfts] are averages over the grid of the values times
    cos(k t + l p) and sin(k t + l p). Splitting the angle, they are sums over
    the poloidal points of cos(k t_a) and sin(k t_a) against the transforms
    of each row in the toroidal angle, G_a(l) = sum_b f_ab cos(l p_b) and
    H_a(l) = sum_b f_ab sin(l p_b) ([dftc_rows], [dfts_rows]). *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier FourierEval FourierDFT.
Local Open Scope R_scope.

Definition rowG (f : nat -> nat -> R) (N2 : nat) (l : Z) (a : nat) : R :=
  fsum (fun b => f a b * cos (IZR l * gpt N2 b)) N2.
Definition rowH (f : nat -> nat -> R) (N2 : nat) (l : Z) (a : nat) : R :=
  fsum (fun b => f a b * sin (IZR l * gpt N2 b)) N2.

Lemma fsum_minus' (f g : nat -> R) (n : nat) : fsum (fun k => f k - g k) n = fsum f n - fsum g n.
Proof. induction n as [| n IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fsum_ext_lt (f g : nat -> R) (n : nat) :
  (forall k, (k < n)%nat -> f k = g k) -> fsum f n = fsum g n.
Proof.
  induction n as [| n IH]; intros H; simpl; [reflexivity |].
  rewrite IH, H; [reflexivity | lia |]. intros k Hk. apply H. lia.
Qed.

Theorem dftc_rows (N1 N2 : nat) (u : fser) (k l : Z) :
  dftc N1 N2 u k l =
  / (INR N1 * INR N2) *
  fsum (fun a => cos (IZR k * gpt N1 a) * rowG (fun a b => feval u (gpt N1 a) (gpt N2 b)) N2 l a
                 - sin (IZR k * gpt N1 a) * rowH (fun a b => feval u (gpt N1 a) (gpt N2 b)) N2 l a) N1.
Proof.
  unfold dftc, gsum2. f_equal. apply fsum_ext. intros a. unfold rowG, rowH.
  rewrite <- !fsum_scal, <- fsum_minus'. apply fsum_ext. intros b.
  rewrite cos_plus. ring.
Qed.

Theorem dfts_rows (N1 N2 : nat) (u : fser) (k l : Z) :
  dfts N1 N2 u k l =
  / (INR N1 * INR N2) *
  fsum (fun a => sin (IZR k * gpt N1 a) * rowG (fun a b => feval u (gpt N1 a) (gpt N2 b)) N2 l a
                 + cos (IZR k * gpt N1 a) * rowH (fun a b => feval u (gpt N1 a) (gpt N2 b)) N2 l a) N1.
Proof.
  unfold dfts, gsum2. f_equal. apply fsum_ext. intros a. unfold rowG, rowH.
  rewrite <- !fsum_scal, <- fsum_plus. apply fsum_ext. intros b.
  rewrite sin_plus. ring.
Qed.
