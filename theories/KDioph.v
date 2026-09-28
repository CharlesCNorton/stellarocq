(** The Diophantine constants of the rotation number of the certified torus.

    The torus turns by omega = 5 beta per field period, with
    beta = (337 + sqrt 5) / 1958 the root of 979 x^2 - 337 x + 29 of
    discriminant 5, a noble number. [noble_diophantine] of DiophQ.v, with a
    rational check over q < 200, gives |q beta - p| >= (17/100) / |q|
    ([beta_dioph]); the constants the KAM theorem reads follow for the
    modes of period 5 ([om_dioph_per]) and for all modes ([om_dioph]). *)

From Coq Require Import ZArith QArith Reals Lra Lia.
From Stellarocq Require Import Dioph DiophQ FourierPer.
Local Open Scope R_scope.

Definition beta_w7x : R := nw 979 (-337).
Definition om_w7x : R := IZR 5 * beta_w7x.

Theorem beta_dioph : diophantine1 beta_w7x (Q2R (17 # 100)).
Proof.
  apply (noble_diophantine 979 (-337) 29 (2236067977 # 1000000000) (2236067978 # 1000000000) (17 # 100) 200).
  - lia.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma Q2R_17 : Q2R (17 # 100) = 17 / 100.
Proof. unfold Q2R. simpl. field. Qed.

Theorem om_dioph_per : dioph_per 5 om_w7x (IZR 5 * (17 / 100)).
Proof. rewrite <- Q2R_17. apply dioph_per_of; [lia | exact beta_dioph]. Qed.

(** A multiple of a Diophantine number is Diophantine, with the constant
    divided by the multiple. *)
Lemma dioph_scale (w g : R) (n : Z) : (0 < n)%Z -> diophantine1 w g -> diophantine1 (IZR n * w) (g / IZR n).
Proof.
  intros Hn Hd p q Hq. assert (Hnq : (n * q)%Z <> 0%Z) by lia.
  pose proof (Hd p (n * q)%Z Hnq) as H. rewrite mult_IZR in H.
  assert (HN : 0 < IZR n) by (apply IZR_lt; exact Hn).
  replace (IZR q * (IZR n * w) - IZR p) with (IZR n * IZR q * w - IZR p) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq (IZR n)) in H by lra.
  assert (Hq' : 0 < Rabs (IZR q)) by (apply Rabs_pos_lt, not_0_IZR, Hq).
  replace (g / IZR n / Rabs (IZR q)) with (g / (IZR n * Rabs (IZR q))) by (field; lra). exact H.
Qed.

Theorem om_dioph : diophantine1 om_w7x (17 / 100 / IZR 5).
Proof. unfold om_w7x. rewrite <- Q2R_17. apply dioph_scale; [lia | exact beta_dioph]. Qed.
