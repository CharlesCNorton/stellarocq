(** The force is the gradient of the energy.

    VMEC's equilibrium is the stationary point of

      W = integral of (B^2 / 2 - mu0 p) sqrt(g)  ds du dv,

    the magnetic energy with the pressure term of gamma = 0, over the
    geometry R(s,u,v), Z(s,u,v) at fixed stream function, rotational
    transform, flux and pressure profile, so that sqrt(g) B^u = phip (iota -
    lambda_v) and sqrt(g) B^v = phip (1 + lambda_u) are held: the flux
    through the coordinate surfaces is fixed by their labels, which is the
    ideal deformation. Its Euler-Lagrange expressions are what the solver
    calls the forces on R and on Z.

    Hypotheses.v takes it as a premise that those forces are the ideal-MHD
    force J x B - grad p. Here that is a theorem, pointwise and exact: with
    E_R = dL/dR - D_s dL/dR_s - D_u dL/dR_u - D_v dL/dR_v and E_Z likewise,
    and with f_s, f_u the covariant components of the residual as Physics.v
    writes them, (J x B - mu0 grad p)_i = (d_j B_i - d_i B_j) B^j - mu0 d_i p,

      E_R = 2 R (f_s Z_u - f_u Z_s),   E_Z = 2 R (f_u R_s - f_s R_u),

    which is -2 sqrt(g) times the cylindrical components of the force, since
    grad s . R^ = -Z_u / tau and grad u . R^ = Z_s / tau with tau = R_u Z_s -
    R_s Z_u. The factor two is because the Lagrangian carried below is twice
    the density above, which keeps every coefficient an integer.

    Everything is written in the expression language over the jet of the
    geometry at a point: R, Z, lambda and the profiles with their derivatives
    to second order in the angles and the radius, each in a slot. The
    partial derivatives with respect to a jet variable and the total
    derivatives along s, u and v are all taken by [Deriv.deriv], whose
    soundness is [Deriv.xderive_deriv], and the reciprocals of R and of tau
    sit in slots of their own so that every expression stays polynomial and
    every derivative map carries them along. The identity is then an
    equality of two real numbers, decided by field arithmetic.

    Slots: 0 R, 1 R_s, 2 R_u, 3 R_v, 4 Z_s, 5 Z_u, 6 Z_v, 7 lambda_u,
    8 lambda_v, 9 p, 10 iota, 11 phip, 12 mu0, 13..18 R_ss R_su R_sv R_uu
    R_uv R_vv, 19..24 the same for Z, 25..29 lambda_su lambda_sv lambda_uu
    lambda_uv lambda_vv, 30 p', 31 iota', 32 1/R, 33 1/tau. Only the mixed
    second derivative of lambda is shared between D_u of lambda_v and D_v of
    lambda_u, which is div B = 0 and the one identity the proof uses. *)

From Coq Require Import ZArith Reals List Lia Lra.
From Interval Require Import Real.Xreal Real.Xreal_derive.
From Stellarocq Require Import Expr Physics Deriv.

Import ListNotations.
Local Open Scope nat_scope.

(* ---------------------------------------------------------------- *)
(* The jet                                                           *)

Definition x (k : nat) : expr := Evar k.
Definition sq (e : expr) : expr := Emul e e.

Definition tau_e : expr := Esub (Emul (x 2) (x 4)) (Emul (x 1) (x 5)).
Definition U_e : expr := Emul (x 11) (Esub (x 10) (x 8)).
Definition V_e : expr := Emul (x 11) (Eadd e1 (x 7)).
Definition guu_e : expr := Eadd (sq (x 2)) (sq (x 5)).
Definition guv_e : expr := Eadd (Emul (x 2) (x 3)) (Emul (x 5) (x 6)).
Definition gvv_e : expr := Eadd (Eadd (sq (x 3)) (sq (x 6))) (sq (x 0)).
Definition gsu_e : expr := Eadd (Emul (x 1) (x 2)) (Emul (x 4) (x 5)).
Definition gsv_e : expr := Eadd (Emul (x 1) (x 3)) (Emul (x 4) (x 6)).

(** B^2 sqrt(g) as sqrt(g)^2 B^2 / sqrt(g): the metric against the
    flux-weighted components, over R tau. *)
Definition Nq_e : expr :=
  Eadd (Eadd (Emul guu_e (Emul U_e U_e))
             (Emul e2 (Emul guv_e (Emul U_e V_e))))
       (Emul gvv_e (Emul V_e V_e)).

(** Twice the Lagrangian density: B^2 sqrt(g) - 2 mu0 p sqrt(g). *)
Definition L2_e : expr :=
  Esub (Emul Nq_e (Emul (x 32) (x 33)))
       (Emul e2 (Emul (x 12) (Emul (x 9) (Emul (x 0) tau_e)))).

(* ---------------------------------------------------------------- *)
(* Derivatives                                                       *)

(** The partial derivative maps: one for each variable of the Lagrangian,
    carrying the reciprocal slots. d(1/R)/dR = -1/R^2, and d(1/tau)/dR_s =
    Z_u / tau^2 since dtau/dR_s = -Z_u, and so on. *)
Definition dR (k : nat) : expr :=
  match k with 0 => e1 | 32 => Eneg (sq (x 32)) | _ => e0 end.
Definition dRs (k : nat) : expr :=
  match k with 1 => e1 | 33 => Emul (sq (x 33)) (x 5) | _ => e0 end.
Definition dRu (k : nat) : expr :=
  match k with 2 => e1 | 33 => Eneg (Emul (sq (x 33)) (x 4)) | _ => e0 end.
Definition dRv (k : nat) : expr :=
  match k with 3 => e1 | _ => e0 end.
Definition dZs (k : nat) : expr :=
  match k with 4 => e1 | 33 => Eneg (Emul (sq (x 33)) (x 2)) | _ => e0 end.
Definition dZu (k : nat) : expr :=
  match k with 5 => e1 | 33 => Emul (sq (x 33)) (x 1) | _ => e0 end.
Definition dZv (k : nat) : expr :=
  match k with 6 => e1 | _ => e0 end.

(** The derivatives of tau along the three coordinates. *)
Definition tau_s : expr :=
  Esub (Eadd (Emul (x 14) (x 4)) (Emul (x 2) (x 19)))
       (Eadd (Emul (x 13) (x 5)) (Emul (x 1) (x 20))).
Definition tau_u : expr :=
  Esub (Eadd (Emul (x 16) (x 4)) (Emul (x 2) (x 20)))
       (Eadd (Emul (x 14) (x 5)) (Emul (x 1) (x 22))).
Definition tau_v : expr :=
  Esub (Eadd (Emul (x 17) (x 4)) (Emul (x 2) (x 21)))
       (Eadd (Emul (x 15) (x 5)) (Emul (x 1) (x 23))).

(** The total derivative maps along s, u and v: each first-order slot goes
    to its second-order one, the profiles to their radial derivatives, the
    constants to zero and the reciprocals to minus themselves squared times
    the derivative of what they invert. *)
Definition Ds (k : nat) : expr :=
  match k with
  | 0 => x 1 | 1 => x 13 | 2 => x 14 | 3 => x 15
  | 4 => x 19 | 5 => x 20 | 6 => x 21
  | 7 => x 25 | 8 => x 26 | 9 => x 30 | 10 => x 31
  | 32 => Eneg (Emul (sq (x 32)) (x 1))
  | 33 => Eneg (Emul (sq (x 33)) tau_s)
  | _ => e0
  end.
Definition Du (k : nat) : expr :=
  match k with
  | 0 => x 2 | 1 => x 14 | 2 => x 16 | 3 => x 17
  | 4 => x 20 | 5 => x 22 | 6 => x 23
  | 7 => x 27 | 8 => x 28
  | 32 => Eneg (Emul (sq (x 32)) (x 2))
  | 33 => Eneg (Emul (sq (x 33)) tau_u)
  | _ => e0
  end.
Definition Dv (k : nat) : expr :=
  match k with
  | 0 => x 3 | 1 => x 15 | 2 => x 17 | 3 => x 18
  | 4 => x 21 | 5 => x 23 | 6 => x 24
  | 7 => x 28 | 8 => x 29
  | 32 => Eneg (Emul (sq (x 32)) (x 3))
  | 33 => Eneg (Emul (sq (x 33)) tau_v)
  | _ => e0
  end.

(** The Euler-Lagrange expressions of the Lagrangian on R and on Z. *)
Definition EL_R : expr :=
  Esub (Esub (Esub (deriv dR L2_e) (deriv Ds (deriv dRs L2_e)))
             (deriv Du (deriv dRu L2_e)))
       (deriv Dv (deriv dRv L2_e)).
Definition EL_Z : expr :=
  Eneg (Eadd (Eadd (deriv Ds (deriv dZs L2_e)) (deriv Du (deriv dZu L2_e)))
             (deriv Dv (deriv dZv L2_e))).

(* ---------------------------------------------------------------- *)
(* The residual                                                      *)

(** B^u = U / sqrt(g), B^v = V / sqrt(g), the covariant components through
    the metric, and the two components of (J x B - mu0 grad p) the geometry
    is varied against, as Physics.v writes them. *)
Definition Bup : expr := Emul U_e (Emul (x 32) (x 33)).
Definition Bvp : expr := Emul V_e (Emul (x 32) (x 33)).
Definition Bs_e : expr := Eadd (Emul gsu_e Bup) (Emul gsv_e Bvp).
Definition Bu_e : expr := Eadd (Emul guu_e Bup) (Emul guv_e Bvp).
Definition Bv_e : expr := Eadd (Emul guv_e Bup) (Emul gvv_e Bvp).
Definition fs_e : expr :=
  Esub (Esub (Emul (Esub (deriv Dv Bs_e) (deriv Ds Bv_e)) Bvp)
             (Emul (Esub (deriv Ds Bu_e) (deriv Du Bs_e)) Bup))
       (Emul (x 12) (x 30)).
Definition fu_e : expr :=
  Eneg (Emul (Esub (deriv Du Bv_e) (deriv Dv Bu_e)) Bvp).

(* ---------------------------------------------------------------- *)
(* The theorem                                                       *)

(** The environment of a jet: the thirty-two values, then 1/R and 1/tau. *)
Definition jet_env (R Rs Ru Rv Zs Zu Zv lu lv p io ph mu
                    Rss Rsu Rsv Ruu Ruv Rvv Zss Zsu Zsv Zuu Zuv Zvv
                    lsu lsv luu luv lvv ps ios : R) : env ExtendedR :=
  of_list (map Xreal
             [R; Rs; Ru; Rv; Zs; Zu; Zv; lu; lv; p; io; ph; mu;
              Rss; Rsu; Rsv; Ruu; Ruv; Rvv; Zss; Zsu; Zsv; Zuu; Zuv; Zvv;
              lsu; lsv; luu; luv; lvv; ps; ios;
              / R; / (Ru * Zs - Rs * Zu)])%R.

Theorem energy_gradient_is_force :
  forall R Rs Ru Rv Zs Zu Zv lu lv p io ph mu
         Rss Rsu Rsv Ruu Ruv Rvv Zss Zsu Zsv Zuu Zuv Zvv
         lsu lsv luu luv lvv ps ios : R,
  (R <> 0)%R -> (Ru * Zs - Rs * Zu <> 0)%R ->
  let env := jet_env R Rs Ru Rv Zs Zu Zv lu lv p io ph mu
               Rss Rsu Rsv Ruu Ruv Rvv Zss Zsu Zsv Zuu Zuv Zvv
               lsu lsv luu luv lvv ps ios in
  xeval env EL_R
  = xeval env (Emul e2 (Emul (x 0) (Esub (Emul fs_e (x 5)) (Emul fu_e (x 4)))))
  /\ xeval env EL_Z
     = xeval env (Emul e2 (Emul (x 0) (Esub (Emul fu_e (x 1)) (Emul fs_e (x 2))))).
Proof.
  intros R Rs Ru Rv Zs Zu Zv lu lv p io ph mu
         Rss Rsu Rsv Ruu Ruv Rvv Zss Zsu Zsv Zuu Zuv Zvv
         lsu lsv luu luv lvv ps ios HR Htau env.
  unfold env, jet_env.
  (* the two expressions, differentiated, then read as real numbers *)
  cbv beta iota delta [EL_R EL_Z fs_e fu_e L2_e Nq_e Bs_e Bu_e Bv_e Bup Bvp
    tau_e tau_s tau_u tau_v U_e V_e guu_e guv_e gvv_e gsu_e gsv_e
    sq x e0 e1 e2 deriv dR dRs dRu dRv dZs dZu dZv Ds Du Dv].
  cbv beta iota delta [xeval].
  rewrite !eget_of_list.
  cbv beta iota delta [nth map].
  cbv beta iota delta [Xadd Xsub Xmul Xneg].
  split; apply f_equal; field; repeat split; assumption.
Qed.

(** What the total derivative maps mean. Along a curve through the jet whose
    slots move as [Ds] says, the value of [deriv Ds e] is the derivative of
    the value of e; the same holds of [Du] and [Dv] along their angles, and
    of each partial map along its variable. This is [Deriv.xderive_deriv]
    read at the map, and it is what makes [EL_R] and [EL_Z] the
    Euler-Lagrange expressions and [fs_e], [fu_e] the residual, rather than
    expressions that happen to be equal. *)
Corollary total_derivative_along :
  forall (dvar : nat -> expr) (E : R -> env ExtendedR) e t,
  (forall k t, Xderive_pt (slot_along E k) (Xreal t) (xeval (E t) (dvar k))) ->
  Xderive_pt (along E e) (Xreal t) (xeval (E t) (deriv dvar e)).
Proof.
  intros dvar E e t H. exact (xderive_deriv dvar E H e t).
Qed.
