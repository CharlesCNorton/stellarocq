(** The field-line velocity of the coil field along a path.

    The velocity with the toroidal angle as time is TorusLine.flR =
    R B_R / B_phi and TorusLine.flZ = R B_Z / B_phi. [VR_R] ... [VZ_P] are
    its partial derivatives in R, Z and phi, written through the field and
    FieldPath.v's total partial derivatives, and [vel_path_R], [vel_path_Z]
    differentiate the velocity along a path (R(t), phi(t), Z(t)) at a point
    apart from every source where B_phi is not zero. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier Hypotheses CoilSym FieldKern FieldModel Invariance TorusLine
  FieldPath.
Local Open Scope R_scope.

Section Vel.

Variables (P : nat) (l : list (src * fser)).

Notation BB := (coilB (Z.of_nat P) l).

Definition VR_R (R0 phi Z0 : R) : R :=
  B_R BB R0 phi Z0 / B_phi BB R0 phi Z0
  + R0 * (BR_R P l R0 phi Z0 * B_phi BB R0 phi Z0 - B_R BB R0 phi Z0 * BP_R P l R0 phi Z0)
    / (B_phi BB R0 phi Z0 * B_phi BB R0 phi Z0).
Definition VR_Z (R0 phi Z0 : R) : R :=
  R0 * (BR_Z P l R0 phi Z0 * B_phi BB R0 phi Z0 - B_R BB R0 phi Z0 * BP_Z P l R0 phi Z0)
    / (B_phi BB R0 phi Z0 * B_phi BB R0 phi Z0).
Definition VR_P (R0 phi Z0 : R) : R :=
  R0 * (BR_P P l R0 phi Z0 * B_phi BB R0 phi Z0 - B_R BB R0 phi Z0 * BP_P P l R0 phi Z0)
    / (B_phi BB R0 phi Z0 * B_phi BB R0 phi Z0).
Definition VZ_R (R0 phi Z0 : R) : R :=
  B_Z BB R0 phi Z0 / B_phi BB R0 phi Z0
  + R0 * (BZ_R P l R0 phi Z0 * B_phi BB R0 phi Z0 - B_Z BB R0 phi Z0 * BP_R P l R0 phi Z0)
    / (B_phi BB R0 phi Z0 * B_phi BB R0 phi Z0).
Definition VZ_Z (R0 phi Z0 : R) : R :=
  R0 * (BZ_Z P l R0 phi Z0 * B_phi BB R0 phi Z0 - B_Z BB R0 phi Z0 * BP_Z P l R0 phi Z0)
    / (B_phi BB R0 phi Z0 * B_phi BB R0 phi Z0).
Definition VZ_P (R0 phi Z0 : R) : R :=
  R0 * (BZ_P P l R0 phi Z0 * B_phi BB R0 phi Z0 - B_Z BB R0 phi Z0 * BP_P P l R0 phi Z0)
    / (B_phi BB R0 phi Z0 * B_phi BB R0 phi Z0).

Section Path.

Variables (Rp Pp Zp : R -> R) (s vR vP vZ : R).
Hypothesis DR : is_derive Rp s vR.
Hypothesis DP : is_derive Pp s vP.
Hypothesis DZ : is_derive Zp s vZ.
Hypothesis Hap : apart P l (Rp s) (Pp s) (Zp s).
Hypothesis Hb : B_phi BB (Rp s) (Pp s) (Zp s) <> 0.

(** R B / B_phi along the path, for one component B of the field. *)
Lemma quot_path (Bc : R -> R -> R -> R) (dR dZ dP : R) :
  is_derive (fun t => Bc (Rp t) (Pp t) (Zp t)) s (dR * vR + dZ * vZ + dP * vP) ->
  is_derive (fun t => Rp t * Bc (Rp t) (Pp t) (Zp t) / B_phi BB (Rp t) (Pp t) (Zp t)) s
    ((Bc (Rp s) (Pp s) (Zp s) / B_phi BB (Rp s) (Pp s) (Zp s)
      + Rp s * (dR * B_phi BB (Rp s) (Pp s) (Zp s) - Bc (Rp s) (Pp s) (Zp s) * BP_R P l (Rp s) (Pp s) (Zp s))
        / (B_phi BB (Rp s) (Pp s) (Zp s) * B_phi BB (Rp s) (Pp s) (Zp s))) * vR
     + (Rp s * (dZ * B_phi BB (Rp s) (Pp s) (Zp s) - Bc (Rp s) (Pp s) (Zp s) * BP_Z P l (Rp s) (Pp s) (Zp s))
        / (B_phi BB (Rp s) (Pp s) (Zp s) * B_phi BB (Rp s) (Pp s) (Zp s))) * vZ
     + (Rp s * (dP * B_phi BB (Rp s) (Pp s) (Zp s) - Bc (Rp s) (Pp s) (Zp s) * BP_P P l (Rp s) (Pp s) (Zp s))
        / (B_phi BB (Rp s) (Pp s) (Zp s) * B_phi BB (Rp s) (Pp s) (Zp s))) * vP).
Proof.
  intros DB.
  pose proof (coil_path_P P l Rp Pp Zp s vR vP vZ DR DP DZ Hap) as DBP.
  set (b := Bc (Rp s) (Pp s) (Zp s)) in *. set (p := B_phi BB (Rp s) (Pp s) (Zp s)) in *.
  set (pR := BP_R P l (Rp s) (Pp s) (Zp s)) in *. set (pZ := BP_Z P l (Rp s) (Pp s) (Zp s)) in *.
  set (pP := BP_P P l (Rp s) (Pp s) (Zp s)) in *.
  pose proof (is_derive_mult Rp (fun t => Bc (Rp t) (Pp t) (Zp t)) s vR _ DR DB ltac:(intros; apply Rmult_comm)) as DM.
  pose proof (is_derive_div (fun t => Rp t * Bc (Rp t) (Pp t) (Zp t)) (fun t => B_phi BB (Rp t) (Pp t) (Zp t)) s
                _ _ DM DBP Hb) as DQ.
  cbv beta in DQ. fold b p in DQ.
  match type of DQ with is_derive _ _ ?d =>
    match goal with |- is_derive _ _ ?l => replace l with d; [exact DQ |] end end.
  unfold plus, mult; simpl. field. exact Hb.
Qed.

Theorem vel_path_R :
  is_derive (fun t => flR BB (Rp t) (Pp t) (Zp t)) s
    (VR_R (Rp s) (Pp s) (Zp s) * vR + VR_Z (Rp s) (Pp s) (Zp s) * vZ + VR_P (Rp s) (Pp s) (Zp s) * vP).
Proof.
  unfold flR, VR_R, VR_Z, VR_P.
  exact (quot_path (B_R BB) _ _ _ (coil_path_R P l Rp Pp Zp s vR vP vZ DR DP DZ Hap)).
Qed.

Theorem vel_path_Z :
  is_derive (fun t => flZ BB (Rp t) (Pp t) (Zp t)) s
    (VZ_R (Rp s) (Pp s) (Zp s) * vR + VZ_Z (Rp s) (Pp s) (Zp s) * vZ + VZ_P (Rp s) (Pp s) (Zp s) * vP).
Proof.
  unfold flZ, VZ_R, VZ_Z, VZ_P.
  exact (quot_path (B_Z BB) _ _ _ (coil_path_Z P l Rp Pp Zp s vR vP vZ DR DP DZ Hap)).
Qed.

End Path.

End Vel.
