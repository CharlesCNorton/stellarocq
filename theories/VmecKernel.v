(** VMEC's half-grid Jacobian and metric against the reconstruction's.

    At a half point VMEC++ forms R, Z and their angular and radial derivatives
    from the full-grid values of the two nodes around it by the parity rule of
    Physics.v, and those agree with the reconstruction term for term. The
    Jacobian and the metric elements are products. VMEC++ forms them from
    averages of products of node values (jacobian_kernel.h for the sqrt(s) part
    of tau, metric_kernel.h for guu, guv and gvv), where the reconstruction
    multiplies the interpolated series. The theorems give the differences
    exactly: each is a sum of products of two differences between the nodes,
    so it is of order h^2 wherever those differences are of order h.

    The variables are values at one angle point. For R, Z and their u- and
    v-derivatives, e is the even-m part and o the odd-m part divided by
    sqrt(s), at the inner node (i) and the outer node (o); si and so are the
    nodes' s, h = so - si the radial step, and sh = sqrt(s_h) with
    s_h = (si + so) / 2 the half point's s. *)

From Coq Require Import Reals Lra.
Open Scope R_scope.

Section Kernels.

Variables rei reo roi roo zei zeo zoi zoo : R.
Variables ruei rueo ruoi ruoo zuei zueo zuoi zuoo : R.
Variables rvei rveo rvoi rvoo zvei zveo zvoi zvoo : R.
Variables si so h sh : R.
Hypothesis Hh : h <> 0.
Hypothesis Hsh : sh <> 0.
Hypothesis Hsh2 : sh * sh = (si + so) / 2.

(** VMEC++'s kernels, with its constant dSHalfDsInterp = 1/4. *)

Definition r12 : R := / 2 * ((rei + reo) + sh * (roi + roo)).
Definition ru12 : R := / 2 * ((ruei + rueo) + sh * (ruoi + ruoo)).
Definition zu12 : R := / 2 * ((zuei + zueo) + sh * (zuoi + zuoo)).
Definition rv12 : R := / 2 * ((rvei + rveo) + sh * (rvoi + rvoo)).
Definition zv12 : R := / 2 * ((zvei + zveo) + sh * (zvoi + zvoo)).
Definition rs : R := ((reo - rei) + sh * (roo - roi)) / h.
Definition zs : R := ((zeo - zei) + sh * (zoo - zoi)) / h.

Definition tau2 : R :=
  ruoo * zoo + ruoi * zoi - zuoo * roo - zuoi * roi
  + (rueo * zoo + ruei * zoi - zueo * roo - zuei * roi) / sh.

Definition tau : R := ru12 * zs - rs * zu12 + / 4 * tau2.

Definition gsqrt : R := tau * r12.

Definition guu : R :=
  / 2 * ((ruei * ruei + zuei * zuei) + (rueo * rueo + zueo * zueo)
         + si * (ruoi * ruoi + zuoi * zuoi) + so * (ruoo * ruoo + zuoo * zuoo))
  + sh * ((ruei * ruoi + zuei * zuoi) + (rueo * ruoo + zueo * zuoo)).

Definition guv : R :=
  / 2 * ((ruei * rvei + zuei * zvei) + (rueo * rveo + zueo * zveo)
         + si * (ruoi * rvoi + zuoi * zvoi) + so * (ruoo * rvoo + zuoo * zvoo)
         + sh * ((ruei * rvoi + zuei * zvoi) + (rueo * rvoo + zueo * zvoo)
                 + (rvei * ruoi + zvei * zuoi) + (rveo * ruoo + zveo * zuoo))).

Definition gvv : R :=
  / 2 * (rei * rei + reo * reo + si * (roi * roi) + so * (roo * roo))
  + sh * (rei * roi + reo * roo)
  + / 2 * ((rvei * rvei + zvei * zvei) + (rveo * rveo + zveo * zveo)
           + si * (rvoi * rvoi + zvoi * zvoi) + so * (rvoo * rvoo + zvoo * zvoo))
  + sh * ((rvei * rvoi + zvei * zvoi) + (rveo * rvoo + zveo * zvoo)).

(** The reconstruction of Physics.v at the same point: the same series, the
    derivative c_k(h) / (2 s_h) of the sqrt(s) factor added to the radial
    derivatives of R and Z, and the Jacobian and metric of the interpolated
    geometry, the cylindrical g_vv carrying R^2. *)

Definition rs_rec : R := rs + sh * (/ 2 * (roi + roo)) / (2 * (sh * sh)).
Definition zs_rec : R := zs + sh * (/ 2 * (zoi + zoo)) / (2 * (sh * sh)).
Definition jac_rec : R := ru12 * zs_rec - rs_rec * zu12.
Definition sqrtg_rec : R := r12 * jac_rec.
Definition guu_rec : R := ru12 * ru12 + zu12 * zu12.
Definition guv_rec : R := ru12 * rv12 + zu12 * zv12.
Definition gvv_rec : R := r12 * r12 + rv12 * rv12 + zv12 * zv12.

Theorem vmec_jacobian_difference :
  jac_rec - tau =
  - / 8 * ((ruoo - ruoi) * (zoo - zoi) - (zuoo - zuoi) * (roo - roi))
  - / 8 * ((rueo - ruei) * (zoo - zoi) - (zueo - zuei) * (roo - roi)) / sh.
Proof.
  unfold jac_rec, rs_rec, zs_rec, tau, tau2, ru12, zu12, rs, zs.
  field; repeat split; auto.
Qed.

Theorem vmec_sqrtg_difference : sqrtg_rec - gsqrt = r12 * (jac_rec - tau).
Proof. unfold sqrtg_rec, gsqrt. ring. Qed.

Theorem vmec_metric_difference :
  guu - guu_rec =
    / 4 * ((rueo - ruei) ^ 2 + (zueo - zuei) ^ 2)
  + / 4 * (so - si) * ((ruoo ^ 2 - ruoi ^ 2) + (zuoo ^ 2 - zuoi ^ 2))
  + / 4 * (sh * sh) * ((ruoo - ruoi) ^ 2 + (zuoo - zuoi) ^ 2)
  + / 2 * sh * ((rueo - ruei) * (ruoo - ruoi) + (zueo - zuei) * (zuoo - zuoi))
  /\
  guv - guv_rec =
    / 4 * ((rueo - ruei) * (rveo - rvei) + (zueo - zuei) * (zveo - zvei))
  + / 4 * (so - si) * ((ruoo * rvoo - ruoi * rvoi) + (zuoo * zvoo - zuoi * zvoi))
  + / 4 * (sh * sh) * ((ruoo - ruoi) * (rvoo - rvoi) + (zuoo - zuoi) * (zvoo - zvoi))
  + / 4 * sh * ((rueo - ruei) * (rvoo - rvoi) + (zueo - zuei) * (zvoo - zvoi)
                + (rveo - rvei) * (ruoo - ruoi) + (zveo - zvei) * (zuoo - zuoi))
  /\
  gvv - gvv_rec =
    / 4 * ((reo - rei) ^ 2 + (rveo - rvei) ^ 2 + (zveo - zvei) ^ 2)
  + / 4 * (so - si)
      * ((roo ^ 2 - roi ^ 2) + (rvoo ^ 2 - rvoi ^ 2) + (zvoo ^ 2 - zvoi ^ 2))
  + / 4 * (sh * sh) * ((roo - roi) ^ 2 + (rvoo - rvoi) ^ 2 + (zvoo - zvoi) ^ 2)
  + / 2 * sh * ((reo - rei) * (roo - roi) + (rveo - rvei) * (rvoo - rvoi)
                + (zveo - zvei) * (zvoo - zvoi)).
Proof.
  assert (Hsi : si = 2 * (sh * sh) - so) by lra.
  unfold guu, guu_rec, guv, guv_rec, gvv, gvv_rec, ru12, zu12, rv12, zv12, r12.
  rewrite Hsi.
  split; [| split]; field.
Qed.

(** The Jacobians differ at second order: when the six differences in the
    identity are at most K |h|, the difference is at most (K h)^2 (1 + 1/|sh|) / 4. *)
Theorem vmec_jacobian_second_order (K : R) :
  Rabs (ruoo - ruoi) <= K * Rabs h -> Rabs (zoo - zoi) <= K * Rabs h ->
  Rabs (zuoo - zuoi) <= K * Rabs h -> Rabs (roo - roi) <= K * Rabs h ->
  Rabs (rueo - ruei) <= K * Rabs h -> Rabs (zueo - zuei) <= K * Rabs h ->
  Rabs (jac_rec - tau) <= / 4 * (K * h) ^ 2 * (1 + / Rabs sh).
Proof.
  intros H1 H2 H3 H4 H5 H6.
  rewrite vmec_jacobian_difference.
  set (a := ruoo - ruoi) in *. set (b := zoo - zoi) in *.
  set (c := zuoo - zuoi) in *. set (d := roo - roi) in *.
  set (e := rueo - ruei) in *. set (f := zueo - zuei) in *.
  assert (HK : 0 <= K * Rabs h) by (apply Rle_trans with (Rabs a); [apply Rabs_pos | exact H1]).
  assert (Pab : Rabs (a * b) <= (K * Rabs h) * (K * Rabs h))
    by (rewrite Rabs_mult; apply Rmult_le_compat; auto using Rabs_pos).
  assert (Pcd : Rabs (c * d) <= (K * Rabs h) * (K * Rabs h))
    by (rewrite Rabs_mult; apply Rmult_le_compat; auto using Rabs_pos).
  assert (Peb : Rabs (e * b) <= (K * Rabs h) * (K * Rabs h))
    by (rewrite Rabs_mult; apply Rmult_le_compat; auto using Rabs_pos).
  assert (Pfd : Rabs (f * d) <= (K * Rabs h) * (K * Rabs h))
    by (rewrite Rabs_mult; apply Rmult_le_compat; auto using Rabs_pos).
  assert (Q : (K * Rabs h) * (K * Rabs h) = (K * h) ^ 2).
  { assert (Hq : Rabs h * Rabs h = h * h).
    { rewrite <- Rabs_mult. apply Rabs_pos_eq. nra. }
    transitivity (K * K * (Rabs h * Rabs h)); [ring | rewrite Hq; ring]. }
  assert (Hs : 0 < Rabs sh) by (apply Rabs_pos_lt; exact Hsh).
  assert (T1 : Rabs (a * b - c * d) <= 2 * (K * h) ^ 2).
  { apply Rle_trans with (Rabs (a * b) + Rabs (c * d)).
    - unfold Rminus. rewrite <- (Rabs_Ropp (c * d)). apply Rabs_triang.
    - lra. }
  assert (T2 : Rabs (e * b - f * d) <= 2 * (K * h) ^ 2).
  { apply Rle_trans with (Rabs (e * b) + Rabs (f * d)).
    - unfold Rminus. rewrite <- (Rabs_Ropp (f * d)). apply Rabs_triang.
    - lra. }
  replace (- / 8 * (a * b - c * d) - / 8 * (e * b - f * d) / sh)
    with (- (/ 8 * (a * b - c * d)) + - (/ 8 * (e * b - f * d) * / sh))
    by (field; exact Hsh).
  apply Rle_trans with
    (Rabs (/ 8 * (a * b - c * d)) + Rabs (/ 8 * (e * b - f * d) * / sh)).
  { rewrite <- (Rabs_Ropp (/ 8 * (a * b - c * d))).
    rewrite <- (Rabs_Ropp (/ 8 * (e * b - f * d) * / sh)).
    apply Rabs_triang. }
  rewrite !Rabs_mult, (Rabs_inv sh).
  rewrite (Rabs_right (/ 8)) by lra.
  assert (I1 : / 8 * Rabs (a * b - c * d) <= / 4 * (K * h) ^ 2) by lra.
  assert (I2 : / 8 * Rabs (e * b - f * d) * / Rabs sh
               <= / 4 * (K * h) ^ 2 * / Rabs sh).
  { apply Rmult_le_compat_r.
    - left. apply Rinv_0_lt_compat. exact Hs.
    - lra. }
  lra.
Qed.

End Kernels.
