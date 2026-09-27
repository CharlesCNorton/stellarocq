(** The exactly symmetric coil field.

    A coil set of P field periods with stellarator symmetry is fixed by the
    sources of its base coils: a source point p with its weighted tangent d
    stands for the 2 P sources R_k p, R_k d and R_k S p, - R_k S d, with R_k
    the rotation by - 2 pi k / P about the z axis and S the reflection
    (x, y, z) -> (x, -y, -z), a rotation by pi about the x axis
    ([images]). Each source contributes d x (x - p) / |x - p|^3 ([kern]), and
    [symfield] is the field of all the images of a list of base sources.

    In cylindrical components at the angle phi, the image under R_k gives the
    source's own field at phi + 2 pi k / P ([kern_rot_cyl]), and the image
    under S gives the source's field at (R, - phi, - Z) with its radial
    component reversed ([kern_refl_cyl]). [symfield_cyl] writes the field of
    all the images at a point through the base sources alone. *)

From Coq Require Import Reals Lra List.
From Stellarocq Require Import KAMScalar Hypotheses Invariance.
Import ListNotations.
Local Open Scope R_scope.

Definition v3add (a b : vec3) : vec3 :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in (a1 + b1, a2 + b2, a3 + b3).
Definition v3sub (a b : vec3) : vec3 :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in (a1 - b1, a2 - b2, a3 - b3).
Definition v3scal (c : R) (a : vec3) : vec3 := let '(a1, a2, a3) := a in (c * a1, c * a2, c * a3).
Definition v3neg (a : vec3) : vec3 := let '(a1, a2, a3) := a in (- a1, - a2, - a3).
Definition v3zero : vec3 := (0, 0, 0).

Definition rotz (a : R) (v : vec3) : vec3 :=
  let '(x, y, z) := v in (x * cos a - y * sin a, x * sin a + y * cos a, z).
Definition refl (v : vec3) : vec3 := let '(x, y, z) := v in (x, - y, - z).

(** The field of one source: d x (x - p) / |x - p|^3. *)
Definition kern (p d x : vec3) : vec3 :=
  let r := v3sub x p in
  let q := dot3 r r in
  v3scal (/ (q * sqrt q)) (cross3r d r).

(** Cylindrical components of a vector at the angle phi. *)
Definition cylR (phi : R) (v : vec3) : R := coord1 v * cos phi + coord2 v * sin phi.
Definition cylP (phi : R) (v : vec3) : R := - coord1 v * sin phi + coord2 v * cos phi.
Definition cylZ (v : vec3) : R := coord3 v.

Section Periods.

Variable P : nat.

Definition theta (k : nat) : R := INR k * (2 * PI / INR P).

(** The images of one base source, at a point. *)
Definition images (p d x : vec3) : vec3 :=
  fold_right v3add v3zero
    (map (fun k => v3add (kern (rotz (- theta k) p) (rotz (- theta k) d) x)
                         (kern (rotz (- theta k) (refl p)) (v3neg (rotz (- theta k) (refl d))) x))
         (seq 0 P)).

Definition symfield (srcs : list (vec3 * vec3)) (x : vec3) : vec3 :=
  fold_right v3add v3zero (map (fun s => images (fst s) (snd s) x) srcs).

End Periods.

(** * Rotations about the z axis *)

Lemma v3_eq (a1 a2 a3 b1 b2 b3 : R) : a1 = b1 -> a2 = b2 -> a3 = b3 -> (a1, a2, a3) = (b1, b2, b3).
Proof. intros -> -> ->. reflexivity. Qed.

Lemma cs1 (a : R) : cos a * cos a + sin a * sin a = 1.
Proof. rewrite <- (sin2_cos2 a). unfold Rsqr. ring. Qed.

Lemma rotz_sub (a : R) (u v : vec3) : v3sub (rotz a u) (rotz a v) = rotz a (v3sub u v).
Proof. destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. simpl. apply v3_eq; ring. Qed.

Lemma rotz_dot (a : R) (u : vec3) : dot3 (rotz a u) (rotz a u) = dot3 u u.
Proof.
  destruct u as [[u1 u2] u3]. simpl. pose proof (cs1 a).
  replace ((u1 * cos a - u2 * sin a) * (u1 * cos a - u2 * sin a)
           + (u1 * sin a + u2 * cos a) * (u1 * sin a + u2 * cos a) + u3 * u3)
    with ((u1 * u1 + u2 * u2) * (cos a * cos a + sin a * sin a) + u3 * u3) by ring.
  rewrite H. ring.
Qed.

Lemma rotz_cross (a : R) (u v : vec3) : cross3r (rotz a u) (rotz a v) = rotz a (cross3r u v).
Proof.
  destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. simpl. pose proof (cs1 a) as H.
  apply v3_eq.
  - replace ((u1 * sin a + u2 * cos a) * v3 - u3 * (v1 * sin a + v2 * cos a))
      with ((u2 * v3 - u3 * v2) * cos a - (u3 * v1 - u1 * v3) * sin a) by ring. reflexivity.
  - replace (u3 * (v1 * cos a - v2 * sin a) - (u1 * cos a - u2 * sin a) * v3)
      with ((u2 * v3 - u3 * v2) * sin a + (u3 * v1 - u1 * v3) * cos a) by ring. reflexivity.
  - replace ((u1 * cos a - u2 * sin a) * (v1 * sin a + v2 * cos a)
             - (u1 * sin a + u2 * cos a) * (v1 * cos a - v2 * sin a))
      with ((u1 * v2 - u2 * v1) * (cos a * cos a + sin a * sin a)) by ring.
    rewrite H. ring.
Qed.

Lemma rotz_scal (a c : R) (u : vec3) : v3scal c (rotz a u) = rotz a (v3scal c u).
Proof. destruct u as [[u1 u2] u3]. simpl. apply v3_eq; ring. Qed.

Lemma kern_rotz (a : R) (p d y : vec3) : kern (rotz a p) (rotz a d) (rotz a y) = rotz a (kern p d y).
Proof. unfold kern. rewrite rotz_sub, rotz_dot, rotz_cross, rotz_scal. reflexivity. Qed.

Lemma cyl_rotz (a R0 phi Z0 : R) : cyl R0 phi Z0 = rotz a (cyl R0 (phi - a) Z0).
Proof.
  unfold cyl, rotz. apply v3_eq.
  - replace phi with ((phi - a) + a) at 1 by ring. rewrite cos_plus. ring.
  - replace phi with ((phi - a) + a) at 1 by ring. rewrite sin_plus. ring.
  - reflexivity.
Qed.

Lemma cylR_rotz (a phi : R) (v : vec3) : cylR phi (rotz a v) = cylR (phi - a) v.
Proof. destruct v as [[v1 v2] v3]. unfold cylR, rotz. simpl. rewrite cos_minus, sin_minus. ring. Qed.

Lemma cylP_rotz (a phi : R) (v : vec3) : cylP phi (rotz a v) = cylP (phi - a) v.
Proof. destruct v as [[v1 v2] v3]. unfold cylP, rotz. simpl. rewrite cos_minus, sin_minus. ring. Qed.

Lemma cylZ_rotz (a : R) (v : vec3) : cylZ (rotz a v) = cylZ v.
Proof. destruct v as [[v1 v2] v3]. reflexivity. Qed.

(** The image under a rotation, in cylindrical components: the source's own
    field turned back by the rotation. *)
Theorem kern_rot_cyl (a R0 phi Z0 : R) (p d : vec3) :
  let v := kern (rotz a p) (rotz a d) (cyl R0 phi Z0) in
  let w := kern p d (cyl R0 (phi - a) Z0) in
  cylR phi v = cylR (phi - a) w /\ cylP phi v = cylP (phi - a) w /\ cylZ v = cylZ w.
Proof.
  intros v w. unfold v, w. rewrite (cyl_rotz a R0 phi Z0), kern_rotz.
  rewrite cylR_rotz, cylP_rotz, cylZ_rotz. auto.
Qed.

(** * The reflection *)

Lemma refl_sub (u v : vec3) : v3sub (refl u) (refl v) = refl (v3sub u v).
Proof. destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. simpl. apply v3_eq; ring. Qed.

Lemma refl_dot (u : vec3) : dot3 (refl u) (refl u) = dot3 u u.
Proof. destruct u as [[u1 u2] u3]. simpl. ring. Qed.

Lemma refl_cross_neg (u v : vec3) : cross3r (v3neg (refl u)) (refl v) = v3neg (refl (cross3r u v)).
Proof. destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. simpl. apply v3_eq; ring. Qed.

Lemma refl_scal_neg (c : R) (u : vec3) : v3scal c (v3neg (refl u)) = v3neg (refl (v3scal c u)).
Proof. destruct u as [[u1 u2] u3]. simpl. apply v3_eq; ring. Qed.

Lemma kern_refl (p d y : vec3) : kern (refl p) (v3neg (refl d)) (refl y) = v3neg (refl (kern p d y)).
Proof. unfold kern. rewrite refl_sub, refl_dot, refl_cross_neg, refl_scal_neg. reflexivity. Qed.

Lemma cyl_refl (R0 phi Z0 : R) : cyl R0 phi Z0 = refl (cyl R0 (- phi) (- Z0)).
Proof. unfold cyl, refl. rewrite cos_neg, sin_neg. apply v3_eq; ring. Qed.

(** The image under the reflection, in cylindrical components: the source's
    field at (R, - phi, - Z) with its radial component reversed. *)
Theorem kern_refl_cyl (R0 phi Z0 : R) (p d : vec3) :
  let v := kern (refl p) (v3neg (refl d)) (cyl R0 phi Z0) in
  let w := kern p d (cyl R0 (- phi) (- Z0)) in
  cylR phi v = - cylR (- phi) w /\ cylP phi v = cylP (- phi) w /\ cylZ v = cylZ w.
Proof.
  intros v w. unfold v, w. rewrite (cyl_refl R0 phi Z0), kern_refl.
  destruct (kern p d (cyl R0 (- phi) (- Z0))) as [[w1 w2] w3].
  unfold cylR, cylP, cylZ. simpl. rewrite cos_neg, sin_neg.
  refine (conj _ (conj _ _)); ring.
Qed.

(** Rotating the reflected source: the reflected source's field turned back. *)
Lemma kern_rot_refl_cyl (a R0 phi Z0 : R) (p d : vec3) :
  let v := kern (rotz a (refl p)) (v3neg (rotz a (refl d))) (cyl R0 phi Z0) in
  let w := kern p d (cyl R0 (- (phi - a)) (- Z0)) in
  cylR phi v = - cylR (- (phi - a)) w /\ cylP phi v = cylP (- (phi - a)) w /\ cylZ v = cylZ w.
Proof.
  intros v w.
  assert (E : v3neg (rotz a (refl d)) = rotz a (v3neg (refl d))).
  { destruct d as [[d1 d2] d3]. simpl. apply v3_eq; ring. }
  unfold v. rewrite E.
  destruct (kern_rot_cyl a R0 phi Z0 (refl p) (v3neg (refl d))) as [A [B C]].
  destruct (kern_refl_cyl R0 (phi - a) Z0 p d) as [A' [B' C']].
  cbv zeta in A, B, C, A', B', C'.
  refine (conj _ (conj _ _)).
  - rewrite A, A'. reflexivity.
  - rewrite B, B'. reflexivity.
  - rewrite C, C'. reflexivity.
Qed.

(** * The field of all images through the base sources *)

Lemma cylR_add (phi : R) (u v : vec3) : cylR phi (v3add u v) = cylR phi u + cylR phi v.
Proof. destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. unfold cylR. simpl. ring. Qed.
Lemma cylP_add (phi : R) (u v : vec3) : cylP phi (v3add u v) = cylP phi u + cylP phi v.
Proof. destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. unfold cylP. simpl. ring. Qed.
Lemma cylZ_add (u v : vec3) : cylZ (v3add u v) = cylZ u + cylZ v.
Proof. destruct u as [[u1 u2] u3], v as [[v1 v2] v3]. reflexivity. Qed.
Lemma cyl_zero (phi : R) : cylR phi v3zero = 0 /\ cylP phi v3zero = 0 /\ cylZ v3zero = 0.
Proof. unfold cylR, cylP, cylZ, v3zero. simpl. refine (conj _ (conj _ _)); ring. Qed.

(** The contribution of one base source at (R, phi, Z), in each cylindrical
    component, as a sum over the rotations of the source's own field and of
    its reflection. *)
Definition srcR (p d : vec3) (R0 phi Z0 : R) : R :=
  cylR phi (kern p d (cyl R0 phi Z0)) - cylR (- phi) (kern p d (cyl R0 (- phi) (- Z0))).
Definition srcP (p d : vec3) (R0 phi Z0 : R) : R :=
  cylP phi (kern p d (cyl R0 phi Z0)) + cylP (- phi) (kern p d (cyl R0 (- phi) (- Z0))).
Definition srcZ (p d : vec3) (R0 phi Z0 : R) : R :=
  cylZ (kern p d (cyl R0 phi Z0)) + cylZ (kern p d (cyl R0 (- phi) (- Z0))).

Lemma fold_map_cyl (f : nat -> vec3) (l : list nat) (phi : R) :
  cylR phi (fold_right v3add v3zero (map f l)) = fold_right Rplus 0 (map (fun k => cylR phi (f k)) l) /\
  cylP phi (fold_right v3add v3zero (map f l)) = fold_right Rplus 0 (map (fun k => cylP phi (f k)) l) /\
  cylZ (fold_right v3add v3zero (map f l)) = fold_right Rplus 0 (map (fun k => cylZ (f k)) l).
Proof.
  induction l as [| k l [IR [IP IZ]]]; simpl.
  - apply cyl_zero.
  - rewrite cylR_add, cylP_add, cylZ_add, IR, IP, IZ. auto.
Qed.

Theorem images_cyl (P : nat) (p d : vec3) (R0 phi Z0 : R) :
  let v := images P p d (cyl R0 phi Z0) in
  cylR phi v = fold_right Rplus 0 (map (fun k => srcR p d R0 (phi + theta P k) Z0) (seq 0 P)) /\
  cylP phi v = fold_right Rplus 0 (map (fun k => srcP p d R0 (phi + theta P k) Z0) (seq 0 P)) /\
  cylZ v = fold_right Rplus 0 (map (fun k => srcZ p d R0 (phi + theta P k) Z0) (seq 0 P)).
Proof.
  intros v. unfold v, images.
  destruct (fold_map_cyl (fun k => v3add (kern (rotz (- theta P k) p) (rotz (- theta P k) d) (cyl R0 phi Z0))
                            (kern (rotz (- theta P k) (refl p)) (v3neg (rotz (- theta P k) (refl d)))
                               (cyl R0 phi Z0))) (seq 0 P) phi) as [ER [EP EZ]].
  rewrite ER, EP, EZ.
  refine (conj _ (conj _ _)); f_equal; apply map_ext; intros k;
    destruct (kern_rot_cyl (- theta P k) R0 phi Z0 p d) as [A [B C]];
    destruct (kern_rot_refl_cyl (- theta P k) R0 phi Z0 p d) as [A' [B' C']];
    cbv zeta in A, B, C, A', B', C';
    replace (phi - - theta P k) with (phi + theta P k) in A, B, C, A', B', C' by ring.
  - rewrite cylR_add, A, A'. unfold srcR. ring.
  - rewrite cylP_add, B, B'. unfold srcP. ring.
  - rewrite cylZ_add, C, C'. unfold srcZ. ring.
Qed.
