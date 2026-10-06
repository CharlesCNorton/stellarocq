(** The symmetric coil field as the field of one list of sources.

    [symfield P srcs] sums, for every base source, the fields of its 2 P
    images. [img_list P srcs] lists those images in the same order, and the
    symmetric field is the field of that list ([symfield_rsum]), which is the
    form the interval enclosures of KCheckKern.v evaluate. *)

From Coq Require Import Reals Lra List.
From Stellarocq Require Import Hypotheses CoilSym.
Import ListNotations.
Local Open Scope R_scope.

(** The field of a list of sources. *)
Fixpoint rsum (srcs : list (vec3 * vec3)) (x : vec3) : vec3 :=
  match srcs with
  | [] => v3zero
  | s :: l => v3add (kern (fst s) (snd s) x) (rsum l x)
  end.

Definition img2 (P k : nat) (s : vec3 * vec3) : list (vec3 * vec3) :=
  [(rotz (- theta P k) (fst s), rotz (- theta P k) (snd s));
   (rotz (- theta P k) (refl (fst s)), v3neg (rotz (- theta P k) (refl (snd s))))].

Definition img_list (P : nat) (srcs : list (vec3 * vec3)) : list (vec3 * vec3) :=
  flat_map (fun s => flat_map (fun k => img2 P k s) (seq 0 P)) srcs.

Lemma v3add_assoc (a b c : vec3) : v3add (v3add a b) c = v3add a (v3add b c).
Proof.
  destruct a as [[a1 a2] a3], b as [[b1 b2] b3], c as [[c1 c2] c3]. simpl.
  apply v3_eq; ring.
Qed.

Lemma v3add_zero_l (a : vec3) : v3add v3zero a = a.
Proof. destruct a as [[a1 a2] a3]. simpl. apply v3_eq; ring. Qed.

Lemma rsum_app (l1 l2 : list (vec3 * vec3)) (x : vec3) :
  rsum (l1 ++ l2) x = v3add (rsum l1 x) (rsum l2 x).
Proof.
  induction l1 as [| s l1 IH]; cbn [rsum app].
  - rewrite v3add_zero_l. reflexivity.
  - rewrite IH, v3add_assoc. reflexivity.
Qed.

Lemma images_rsum (P : nat) (p d x : vec3) :
  images P p d x = rsum (flat_map (fun k => img2 P k (p, d)) (seq 0 P)) x.
Proof.
  unfold images. generalize (seq 0 P) as ks. intros ks.
  induction ks as [| k ks IH]; cbn [map fold_right flat_map].
  - reflexivity.
  - rewrite IH. unfold img2. cbn [app rsum fst snd].
    rewrite v3add_assoc. reflexivity.
Qed.

Theorem symfield_rsum (P : nat) (srcs : list (vec3 * vec3)) (x : vec3) :
  symfield P srcs x = rsum (img_list P srcs) x.
Proof.
  unfold symfield, img_list. induction srcs as [| s srcs IH]; cbn [map fold_right flat_map].
  - reflexivity.
  - rewrite rsum_app, <- IH. destruct s as [p d]. rewrite images_rsum. reflexivity.
Qed.
