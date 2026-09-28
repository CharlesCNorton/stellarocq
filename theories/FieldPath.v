(** Taylor's formula to second order, and the coil field along a path.

    [taylor2] is Taylor's formula with Lagrange's remainder at second order,
    from Rolle's theorem applied twice. [coil_path_R], [coil_path_P] and
    [coil_path_Z] differentiate the cylindrical components of the symmetric
    coil field along a path (R(t), phi(t), Z(t)) at a point where every
    source's squared distance is positive, for the shifted points and their
    stellarator images: the derivative is the path's velocity against the
    total partial derivatives [BR_R] ... [BZ_P], the sums over the shifts and
    the sources of FieldKern.v's partial derivatives, each image entering
    with the sign the reflection (R, phi, Z) -> (R, -phi, -Z) gives it. *)

From Coq Require Import ZArith Reals Lra Lia List.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import KAMScalar Fourier Hypotheses CoilSym FieldKern FieldModel Invariance.
Import ListNotations.
Local Open Scope R_scope.

(** * Taylor's formula to second order *)

Lemma taylor2 (f f1 f2 : R -> R) (a b : R) :
  a < b -> (forall t, a <= t <= b -> is_derive f t (f1 t)) -> (forall t, a <= t <= b -> is_derive f1 t (f2 t)) ->
  exists z, a < z < b /\ f b = f a + (b - a) * f1 a + (b - a) * (b - a) / 2 * f2 z.
Proof.
  intros Hab H1 H2.
  assert (Hba : b - a <> 0) by lra.
  destruct (exist (fun K => K = (f b - f a - (b - a) * f1 a) * 2 / ((b - a) * (b - a))) _ eq_refl) as [K EK].
  set (g := fun t => f t - (f a + (t - a) * f1 a + K * ((t - a) * (t - a)) / 2)).
  set (g1 := fun t => f1 t - (f1 a + K * (t - a))).
  assert (Hg : forall t, a <= t <= b -> derivable_pt_lim g t (g1 t)).
  { intros t Ht. apply is_derive_Reals. unfold g, g1.
    assert (Hp : is_derive (fun t => f a + (t - a) * f1 a + K * ((t - a) * (t - a)) / 2) t (f1 a + K * (t - a)))
      by (auto_derive; [exact I | field]).
    exact (is_derive_minus f _ t (f1 t) _ (H1 t Ht) Hp). }
  destruct (MVT_cor2 g g1 a b Hab Hg) as [t1 [E1 Ht1]].
  assert (Ega : g a = 0) by (unfold g; field).
  assert (Egb : g b = 0).
  { unfold g. rewrite EK. field. exact Hba. }
  assert (Z1 : g1 t1 = 0).
  { rewrite Ega, Egb in E1. apply (Rmult_eq_reg_r (b - a)); [| exact Hba]. lra. }
  assert (Hg1 : forall t, a <= t <= t1 -> derivable_pt_lim g1 t (f2 t - K)).
  { intros t Ht. apply is_derive_Reals. unfold g1.
    assert (Hp : is_derive (fun t => f1 a + K * (t - a)) t K) by (auto_derive; [exact I | ring]).
    exact (is_derive_minus f1 _ t (f2 t) _ (H2 t ltac:(lra)) Hp). }
  destruct (MVT_cor2 g1 (fun t => f2 t - K) a t1 ltac:(lra) Hg1) as [z [E2 Hz]].
  assert (Eg1a : g1 a = 0) by (unfold g1; ring).
  rewrite Z1, Eg1a in E2.
  assert (Fz : f2 z = K).
  { assert (t1 - a <> 0) by lra. apply (Rmult_eq_reg_r (t1 - a)); [| assumption]. lra. }
  exists z. split; [lra |]. rewrite Fz, EK. field. exact Hba.
Qed.

(** * The total partial derivatives of the coil field *)

Section Partials.

Variables (P : nat) (l : list (src * fser)).

Definition shiftsP (phi : R) : list R := map (fun j => phi + INR j * (2 * PI / INR P)) (seq 0 P).

(** The sum over the shifts of phi and the sources of g applied to the source
    at the shifted angle. *)
Definition ssum (g : src -> R -> R) (phi : R) : R :=
  fold_right Rplus 0 (map (fun ph => fold_right Rplus 0 (map (fun sy => g (fst sy) ph) l)) (shiftsP phi)).

Lemma ssum_ext (g1 g2 : src -> R -> R) (phi : R) :
  (forall sc ph, g1 sc ph = g2 sc ph) -> ssum g1 phi = ssum g2 phi.
Proof.
  intros H. unfold ssum. f_equal. apply map_ext. intros ph. f_equal. apply map_ext. intros sy. apply H.
Qed.

Definition BR_R (R0 phi Z0 : R) := ssum (fun sc ph => fR_R sc R0 ph Z0 - fR_R sc R0 (- ph) (- Z0)) phi.
Definition BR_Z (R0 phi Z0 : R) := ssum (fun sc ph => fR_Z sc R0 ph Z0 + fR_Z sc R0 (- ph) (- Z0)) phi.
Definition BR_P (R0 phi Z0 : R) := ssum (fun sc ph => fR_phi sc R0 ph Z0 + fR_phi sc R0 (- ph) (- Z0)) phi.
Definition BP_R (R0 phi Z0 : R) := ssum (fun sc ph => fP_R sc R0 ph Z0 + fP_R sc R0 (- ph) (- Z0)) phi.
Definition BP_Z (R0 phi Z0 : R) := ssum (fun sc ph => fP_Z sc R0 ph Z0 - fP_Z sc R0 (- ph) (- Z0)) phi.
Definition BP_P (R0 phi Z0 : R) := ssum (fun sc ph => fP_phi sc R0 ph Z0 - fP_phi sc R0 (- ph) (- Z0)) phi.
Definition BZ_R (R0 phi Z0 : R) := ssum (fun sc ph => fZ_R sc R0 ph Z0 + fZ_R sc R0 (- ph) (- Z0)) phi.
Definition BZ_Z (R0 phi Z0 : R) := ssum (fun sc ph => fZ_Z sc R0 ph Z0 - fZ_Z sc R0 (- ph) (- Z0)) phi.
Definition BZ_P (R0 phi Z0 : R) := ssum (fun sc ph => fZ_phi sc R0 ph Z0 - fZ_phi sc R0 (- ph) (- Z0)) phi.

(** Every source at a shifted point and at its image is away from the point. *)
Definition apart (R0 phi Z0 : R) : Prop :=
  List.Forall (fun ph => List.Forall (fun sy => 0 < qk (fst sy) (kx1 R0 ph) (kx2 R0 ph) Z0 /\
                                      0 < qk (fst sy) (kx1 R0 (- ph)) (kx2 R0 (- ph)) (- Z0)) l)
    (shiftsP phi).

(** The components of the coil field as sums over the shifts and the sources. *)
Lemma coil_sum (R0 phi Z0 : R) :
  B_R (coilB (Z.of_nat P) l) R0 phi Z0 = ssum (fun sc ph => fR sc R0 ph Z0 - fR sc R0 (- ph) (- Z0)) phi /\
  B_phi (coilB (Z.of_nat P) l) R0 phi Z0 = ssum (fun sc ph => fP sc R0 ph Z0 + fP sc R0 (- ph) (- Z0)) phi /\
  B_Z (coilB (Z.of_nat P) l) R0 phi Z0 = ssum (fun sc ph => fZ sc R0 ph Z0 + fZ sc R0 (- ph) (- Z0)) phi.
Proof.
  assert (EP : Z.to_nat (Z.of_nat P) = P) by apply Nat2Z.id.
  destruct (fold_map_cyl' (fun s => images P (fst s) (snd s) (cyl R0 phi Z0)) (srcs3 l) phi) as [CR [CP CZ]].
  unfold B_R, B_phi, B_Z, coilB, symfield. rewrite EP.
  change (coord1 ?v * cos phi + coord2 ?v * sin phi) with (cylR phi v).
  change (- coord1 ?v * sin phi + coord2 ?v * cos phi) with (cylP phi v).
  change (coord3 ?v) with (cylZ v).
  rewrite CR, CP, CZ. unfold ssum, shiftsP.
  rewrite !map_map, !seq_fsum.
  refine (conj _ (conj _ _)).
  - rewrite (lsum_ext _ (fun s => fsum (fun k => srcR (fst s) (snd s) R0 (phi + theta P k) Z0) P)).
    + rewrite <- (lsum_fsum (fun k s => srcR (fst s) (snd s) R0 (phi + theta P k) Z0)).
      apply fsum_ext. intros k. unfold lsum, srcs3. rewrite map_map. f_equal. apply map_ext. intros sy.
      unfold srcR, theta. cbn [fst snd]. rewrite !fR_kern. reflexivity.
    + intros s. destruct (images_cyl P (fst s) (snd s) R0 phi Z0) as [I _]. cbv zeta in I.
      rewrite I, seq_fsum. reflexivity.
  - rewrite (lsum_ext _ (fun s => fsum (fun k => srcP (fst s) (snd s) R0 (phi + theta P k) Z0) P)).
    + rewrite <- (lsum_fsum (fun k s => srcP (fst s) (snd s) R0 (phi + theta P k) Z0)).
      apply fsum_ext. intros k. unfold lsum, srcs3. rewrite map_map. f_equal. apply map_ext. intros sy.
      unfold srcP, theta. cbn [fst snd]. rewrite !fP_kern. reflexivity.
    + intros s. destruct (images_cyl P (fst s) (snd s) R0 phi Z0) as [_ [I _]]. cbv zeta in I.
      rewrite I, seq_fsum. reflexivity.
  - rewrite (lsum_ext _ (fun s => fsum (fun k => srcZ (fst s) (snd s) R0 (phi + theta P k) Z0) P)).
    + rewrite <- (lsum_fsum (fun k s => srcZ (fst s) (snd s) R0 (phi + theta P k) Z0)).
      apply fsum_ext. intros k. unfold lsum, srcs3. rewrite map_map. f_equal. apply map_ext. intros sy.
      unfold srcZ, theta. cbn [fst snd]. rewrite !fZ_kern. reflexivity.
    + intros s. destruct (images_cyl P (fst s) (snd s) R0 phi Z0) as [_ [_ I]]. cbv zeta in I.
      rewrite I, seq_fsum. reflexivity.
Qed.

End Partials.

(** * Along a path *)

Lemma is_derive_fold {A : Type} (xs : list A) (F : A -> R -> R) (dF : A -> R) (s : R) :
  List.Forall (fun a => is_derive (F a) s (dF a)) xs ->
  is_derive (fun t => fold_right Rplus 0 (map (fun a => F a t) xs)) s (fold_right Rplus 0 (map dF xs)).
Proof.
  induction 1 as [| a xs' Ha _ IH]; cbn [map fold_right].
  - exact (is_derive_const 0 s).
  - exact (is_derive_plus (F a) (fun t => fold_right Rplus 0 (map (fun a => F a t) xs')) s _ _ Ha IH).
Qed.

Lemma is_derive_add_const (f : R -> R) (x df c : R) : is_derive f x df -> is_derive (fun t => f t + c) x df.
Proof.
  intros H. pose proof (is_derive_plus f (fun _ => c) x df zero H (is_derive_const c x)) as H'.
  unfold plus, zero in H'. simpl in H'. rewrite Rplus_0_r in H'. exact H'.
Qed.

Lemma fold_lin {A : Type} (xs : list A) (f g k : A -> R) (u v w : R) :
  fold_right Rplus 0 (map (fun a => f a * u + g a * v + k a * w) xs)
  = fold_right Rplus 0 (map f xs) * u + fold_right Rplus 0 (map g xs) * v + fold_right Rplus 0 (map k xs) * w.
Proof. induction xs as [| a xs IH]; cbn [map fold_right]; [ring | rewrite IH; ring]. Qed.

(** The chain rule of one cylindrical component of one source, as
    FieldKern.cyl_chain_R and its siblings give it. *)
Definition chain_ok (f f_R f_Z f_phi : src -> R -> R -> R -> R) : Prop :=
  forall (sc : src) (Rq Pq Zq : R -> R) (s vR vP vZ : R),
    is_derive Rq s vR -> is_derive Pq s vP -> is_derive Zq s vZ ->
    0 < qk sc (kx1 (Rq s) (Pq s)) (kx2 (Rq s) (Pq s)) (Zq s) ->
    is_derive (fun t => f sc (Rq t) (Pq t) (Zq t)) s
      (f_R sc (Rq s) (Pq s) (Zq s) * vR + f_Z sc (Rq s) (Pq s) (Zq s) * vZ + f_phi sc (Rq s) (Pq s) (Zq s) * vP).

Lemma chain_R : chain_ok fR fR_R fR_Z fR_phi.
Proof. intros sc Rq Pq Zq s vR vP vZ H1 H2 H3 Hq. exact (cyl_chain_R sc Rq Pq Zq s vR vP vZ H1 H2 H3 Hq). Qed.
Lemma chain_P : chain_ok fP fP_R fP_Z fP_phi.
Proof. intros sc Rq Pq Zq s vR vP vZ H1 H2 H3 Hq. exact (cyl_chain_P sc Rq Pq Zq s vR vP vZ H1 H2 H3 Hq). Qed.
Lemma chain_Z : chain_ok fZ fZ_R fZ_Z fZ_phi.
Proof. intros sc Rq Pq Zq s vR vP vZ H1 H2 H3 Hq. exact (cyl_chain_Z sc Rq Pq Zq s vR vP vZ H1 H2 H3 Hq). Qed.

Section Path.

Variables (P : nat) (l : list (src * fser)) (Rp Pp Zp : R -> R) (s vR vP vZ : R).
Hypothesis DR : is_derive Rp s vR.
Hypothesis DP : is_derive Pp s vP.
Hypothesis DZ : is_derive Zp s vZ.
Hypothesis Hap : apart P l (Rp s) (Pp s) (Zp s).

(** One source at one shift, with its image weighted by sg. *)
Lemma term_derive (f f_R f_Z f_phi : src -> R -> R -> R -> R) (C : chain_ok f f_R f_Z f_phi) (sg : R)
    (sc : src) (c : R) :
  0 < qk sc (kx1 (Rp s) (Pp s + c)) (kx2 (Rp s) (Pp s + c)) (Zp s) ->
  0 < qk sc (kx1 (Rp s) (- (Pp s + c))) (kx2 (Rp s) (- (Pp s + c))) (- Zp s) ->
  is_derive (fun t => f sc (Rp t) (Pp t + c) (Zp t) + sg * f sc (Rp t) (- (Pp t + c)) (- Zp t)) s
    ((f_R sc (Rp s) (Pp s + c) (Zp s) + sg * f_R sc (Rp s) (- (Pp s + c)) (- Zp s)) * vR
     + (f_Z sc (Rp s) (Pp s + c) (Zp s) - sg * f_Z sc (Rp s) (- (Pp s + c)) (- Zp s)) * vZ
     + (f_phi sc (Rp s) (Pp s + c) (Zp s) - sg * f_phi sc (Rp s) (- (Pp s + c)) (- Zp s)) * vP).
Proof.
  intros Q1 Q2.
  assert (DPc : is_derive (fun t => Pp t + c) s vP) by exact (is_derive_add_const Pp s vP c DP).
  assert (DPm : is_derive (fun t => - (Pp t + c)) s (- vP)) by (apply (is_derive_opp (fun t => Pp t + c)), DPc).
  assert (DZm : is_derive (fun t => - Zp t) s (- vZ)) by (apply (is_derive_opp Zp), DZ).
  pose proof (C sc Rp (fun t => Pp t + c) Zp s vR vP vZ DR DPc DZ Q1) as T1.
  pose proof (C sc Rp (fun t => - (Pp t + c)) (fun t => - Zp t) s vR (- vP) (- vZ) DR DPm DZm Q2) as T2.
  pose proof (is_derive_scal (fun t => f sc (Rp t) (- (Pp t + c)) (- Zp t)) s sg _ T2) as T3.
  pose proof (is_derive_plus _ _ s _ _ T1 T3) as T4. cbv beta in T4.
  match goal with |- is_derive _ _ ?l => replace l with
    (plus (f_R sc (Rp s) (Pp s + c) (Zp s) * vR + f_Z sc (Rp s) (Pp s + c) (Zp s) * vZ
           + f_phi sc (Rp s) (Pp s + c) (Zp s) * vP)
          (scal sg (f_R sc (Rp s) (- (Pp s + c)) (- Zp s) * vR + f_Z sc (Rp s) (- (Pp s + c)) (- Zp s) * - vZ
                    + f_phi sc (Rp s) (- (Pp s + c)) (- Zp s) * - vP))) end.
  - exact T4.
  - unfold plus, scal; simpl; unfold mult; simpl. ring.
Qed.

(** The shifted angle and its image are apart from every source. *)
Lemma apart_at (j : nat) (sy : src * fser) :
  In j (seq 0 P) -> In sy l ->
  0 < qk (fst sy) (kx1 (Rp s) (Pp s + INR j * (2 * PI / INR P))) (kx2 (Rp s) (Pp s + INR j * (2 * PI / INR P))) (Zp s) /\
  0 < qk (fst sy) (kx1 (Rp s) (- (Pp s + INR j * (2 * PI / INR P))))
         (kx2 (Rp s) (- (Pp s + INR j * (2 * PI / INR P)))) (- Zp s).
Proof.
  intros Hj Hs. unfold apart, shiftsP in Hap. rewrite Forall_forall in Hap.
  assert (H1 : In (Pp s + INR j * (2 * PI / INR P)) (map (fun j => Pp s + INR j * (2 * PI / INR P)) (seq 0 P)))
    by (apply in_map_iff; exists j; split; [reflexivity | exact Hj]).
  specialize (Hap _ H1). rewrite Forall_forall in Hap. exact (Hap sy Hs).
Qed.

Lemma ssum_path (f f_R f_Z f_phi : src -> R -> R -> R -> R) (C : chain_ok f f_R f_Z f_phi) (sg : R) :
  is_derive (fun t => ssum P l (fun sc ph => f sc (Rp t) ph (Zp t) + sg * f sc (Rp t) (- ph) (- Zp t)) (Pp t)) s
    (ssum P l (fun sc ph => f_R sc (Rp s) ph (Zp s) + sg * f_R sc (Rp s) (- ph) (- Zp s)) (Pp s) * vR
     + ssum P l (fun sc ph => f_Z sc (Rp s) ph (Zp s) - sg * f_Z sc (Rp s) (- ph) (- Zp s)) (Pp s) * vZ
     + ssum P l (fun sc ph => f_phi sc (Rp s) ph (Zp s) - sg * f_phi sc (Rp s) (- ph) (- Zp s)) (Pp s) * vP).
Proof.
  unfold ssum, shiftsP. rewrite !map_map.
  set (c := fun j : nat => INR j * (2 * PI / INR P)).
  apply (is_derive_ext (fun t => fold_right Rplus 0 (map (fun j => fold_right Rplus 0
           (map (fun sy => f (fst sy) (Rp t) (Pp t + c j) (Zp t) + sg * f (fst sy) (Rp t) (- (Pp t + c j)) (- Zp t)) l))
           (seq 0 P)))); [intros t; rewrite map_map; reflexivity |].
  rewrite <- !fold_lin.
  apply (is_derive_fold (seq 0 P) (fun j t => fold_right Rplus 0
           (map (fun sy => f (fst sy) (Rp t) (Pp t + c j) (Zp t) + sg * f (fst sy) (Rp t) (- (Pp t + c j)) (- Zp t)) l))).
  apply Forall_forall. intros j Hj. rewrite <- fold_lin.
  apply (is_derive_fold l (fun sy t => f (fst sy) (Rp t) (Pp t + c j) (Zp t) + sg * f (fst sy) (Rp t) (- (Pp t + c j)) (- Zp t))).
  apply Forall_forall. intros sy Hs. destruct (apart_at j sy Hj Hs) as [Q1 Q2].
  exact (term_derive f f_R f_Z f_phi C sg (fst sy) (c j) Q1 Q2).
Qed.

Theorem coil_path_R :
  is_derive (fun t => B_R (coilB (Z.of_nat P) l) (Rp t) (Pp t) (Zp t)) s
    (BR_R P l (Rp s) (Pp s) (Zp s) * vR + BR_Z P l (Rp s) (Pp s) (Zp s) * vZ + BR_P P l (Rp s) (Pp s) (Zp s) * vP).
Proof.
  apply (is_derive_ext (fun t => ssum P l (fun sc ph => fR sc (Rp t) ph (Zp t) + -1 * fR sc (Rp t) (- ph) (- Zp t)) (Pp t))).
  { intros t. rewrite (proj1 (coil_sum P l (Rp t) (Pp t) (Zp t))). unfold ssum. f_equal. apply map_ext. intros ph.
    f_equal. apply map_ext. intros sy. ring. }
  pose proof (ssum_path fR fR_R fR_Z fR_phi chain_R (-1)) as H.
  unfold BR_R, BR_Z, BR_P.
  rewrite (ssum_ext P l (fun sc ph => fR_R sc (Rp s) ph (Zp s) + -1 * fR_R sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fR_R sc (Rp s) ph (Zp s) - fR_R sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  rewrite (ssum_ext P l (fun sc ph => fR_Z sc (Rp s) ph (Zp s) - -1 * fR_Z sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fR_Z sc (Rp s) ph (Zp s) + fR_Z sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  rewrite (ssum_ext P l (fun sc ph => fR_phi sc (Rp s) ph (Zp s) - -1 * fR_phi sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fR_phi sc (Rp s) ph (Zp s) + fR_phi sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  exact H.
Qed.

Theorem coil_path_P :
  is_derive (fun t => B_phi (coilB (Z.of_nat P) l) (Rp t) (Pp t) (Zp t)) s
    (BP_R P l (Rp s) (Pp s) (Zp s) * vR + BP_Z P l (Rp s) (Pp s) (Zp s) * vZ + BP_P P l (Rp s) (Pp s) (Zp s) * vP).
Proof.
  apply (is_derive_ext (fun t => ssum P l (fun sc ph => fP sc (Rp t) ph (Zp t) + 1 * fP sc (Rp t) (- ph) (- Zp t)) (Pp t))).
  { intros t. rewrite (proj1 (proj2 (coil_sum P l (Rp t) (Pp t) (Zp t)))). unfold ssum. f_equal. apply map_ext.
    intros ph. f_equal. apply map_ext. intros sy. ring. }
  pose proof (ssum_path fP fP_R fP_Z fP_phi chain_P 1) as H.
  unfold BP_R, BP_Z, BP_P.
  rewrite (ssum_ext P l (fun sc ph => fP_R sc (Rp s) ph (Zp s) + 1 * fP_R sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fP_R sc (Rp s) ph (Zp s) + fP_R sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  rewrite (ssum_ext P l (fun sc ph => fP_Z sc (Rp s) ph (Zp s) - 1 * fP_Z sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fP_Z sc (Rp s) ph (Zp s) - fP_Z sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  rewrite (ssum_ext P l (fun sc ph => fP_phi sc (Rp s) ph (Zp s) - 1 * fP_phi sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fP_phi sc (Rp s) ph (Zp s) - fP_phi sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  exact H.
Qed.

Theorem coil_path_Z :
  is_derive (fun t => B_Z (coilB (Z.of_nat P) l) (Rp t) (Pp t) (Zp t)) s
    (BZ_R P l (Rp s) (Pp s) (Zp s) * vR + BZ_Z P l (Rp s) (Pp s) (Zp s) * vZ + BZ_P P l (Rp s) (Pp s) (Zp s) * vP).
Proof.
  apply (is_derive_ext (fun t => ssum P l (fun sc ph => fZ sc (Rp t) ph (Zp t) + 1 * fZ sc (Rp t) (- ph) (- Zp t)) (Pp t))).
  { intros t. rewrite (proj2 (proj2 (coil_sum P l (Rp t) (Pp t) (Zp t)))). unfold ssum. f_equal. apply map_ext.
    intros ph. f_equal. apply map_ext. intros sy. ring. }
  pose proof (ssum_path fZ fZ_R fZ_Z fZ_phi chain_Z 1) as H.
  unfold BZ_R, BZ_Z, BZ_P.
  rewrite (ssum_ext P l (fun sc ph => fZ_R sc (Rp s) ph (Zp s) + 1 * fZ_R sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fZ_R sc (Rp s) ph (Zp s) + fZ_R sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  rewrite (ssum_ext P l (fun sc ph => fZ_Z sc (Rp s) ph (Zp s) - 1 * fZ_Z sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fZ_Z sc (Rp s) ph (Zp s) - fZ_Z sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  rewrite (ssum_ext P l (fun sc ph => fZ_phi sc (Rp s) ph (Zp s) - 1 * fZ_phi sc (Rp s) (- ph) (- Zp s))
             (fun sc ph => fZ_phi sc (Rp s) ph (Zp s) - fZ_phi sc (Rp s) (- ph) (- Zp s))) in H
    by (intros; cbv beta; ring).
  exact H.
Qed.

End Path.
