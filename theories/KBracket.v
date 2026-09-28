(** * The outermost invariant torus of the coil field, bracketed

    The KAM certificate [KFinal.cert_ok] gives an invariant torus of the
    coil field of W7-X near its first torus; the escape certificate
    [KLohner.check_lescape], run on the same sources, gives a segment of the
    outboard midplane of the plane phi = 0 that no invariant torus lying in
    its region meets. Together they place the outermost invariant torus of
    the region, where it crosses that half-line, between the certified torus
    and the start R1 of the segment. *)

From Stdlib Require Import ZArith Reals Lra Lia List.
From Stellarocq Require Import KFix KEngine KFinal KLohner TorusLine FieldModel KSrcReal KDioph FourierEval KAMVec.
Local Open Scope R_scope.

Module Bracket (J : RI).
Module F := Final J.
Import F.FS.SC.SR.

(** The escape data of a source data: its field period, scale and sources,
    with the steps, the region and the boxes. *)
Definition lesc_of (sd : srcdata) (M Jh : nat) (sb R1 RD RD2 : Z) (bs : list (Z * Z * nat)) : lescdata :=
  mklesc (sd_P sd) M Jh (sd_ssrc sd) (sd_srcs sd) sb R1 RD RD2 bs.

Definition coils (sd : srcdata) : list (FieldKern.src * Fourier.fser) :=
  srcl (sd_ssrc sd) (sd_sY sd) (sd_Ky1 sd) (sd_Ky2 sd) (sd_srcs sd) (sd_seeds sd).

(** An invariant torus within delta of the first torus of the data. *)
Definition kam_torus (sd : srcdata) (delta : R) : Prop :=
  exists KR KZ : R -> R -> R, fourier_torus (coilB 5 (coils sd)) KR KZ om_w7x /\
    forall theta phi,
      Rabs (KR theta phi - feval (vR (K0v (Z.of_nat (sd_P sd)) (sd_Km sd) (sd_Kn sd) (sd_s0 sd) (sd_rowsR sd)
                                          (sd_rowsZ sd))) theta phi) <= delta /\
      Rabs (KZ theta phi - feval (vZ (K0v (Z.of_nat (sd_P sd)) (sd_Km sd) (sd_Kn sd) (sd_s0 sd) (sd_rowsR sd)
                                          (sd_rowsZ sd))) theta phi) <= delta.

(** No invariant torus lying in the region of d meets the segment
    R1 <= R <= R_D of the line Z = 0 of the plane phi = 0. *)
Definition torus_free (sd : srcdata) (d : lescdata) : Prop :=
  forall (KR KZ : R -> R -> R) (om : R), fourier_torus (coilB 5 (coils sd)) KR KZ om ->
    (forall t p, KR t p <= region d p) ->
    forall theta, KZ theta 0 = 0 -> ~ (R1r d <= KR theta 0 <= RDr d).

Theorem lcfs_bracket (ed : E.e0data) (sd : srcdata) (jd : F.JC.jetsdata) (fd : findata) (fs : fscal)
    (O TR : list J.t) (M Jh : nat) (sb R1 RD RD2 : Z) (bs : list (Z * Z * nat)) :
  F.cert_ok ed sd jd fd fs O TR = true -> check_lescape (lesc_of sd M Jh sb R1 RD RD2 bs) = true ->
  kam_torus sd (qr (fs_delta fs)) /\ torus_free sd (lesc_of sd M Jh sb R1 RD RD2 bs).
Proof.
  intros Hc He. split.
  - exact (F.cert_ok_torus ed sd jd fd fs O TR Hc).
  - destruct (F.cons_facts ed sd jd fd fs O TR Hc) as [HP _].
    destruct (F.src_facts ed sd jd fd fs O TR Hc) as [HL _].
    pose proof (F.shape_facts ed sd jd fd fs O TR Hc) as SF. cbv zeta in SF.
    destruct SF as [[_ [_ [Hs _]]] _].
    intros KR KZ om HT.
    assert (E5 : coilB 5 (coils sd) = coilB (Z.of_nat (le_P (lesc_of sd M Jh sb R1 RD RD2 bs))) (coils sd)).
    { unfold lesc_of. cbn [le_P]. rewrite HP. reflexivity. }
    rewrite E5 in HT.
    exact (lescape_no_torus _ (coils sd) He
             (src_i_srcl (sd_ssrc sd) (sd_sY sd) (sd_Ky1 sd) (sd_Ky2 sd) (sd_srcs sd) (sd_seeds sd) Hs HL)
             KR KZ om HT).
Qed.

End Bracket.
