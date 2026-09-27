(** The field of one source and its derivatives, as real functions.

    At a point x of space, with r = x - p and q = |r|^2, a source p with
    weighted tangent d contributes b(x) = d x r / q^(3/2) ([bk]). Its
    Jacobian is J_ik = (d x e_k)_i / q^(3/2) - 3 (d x r)_i r_k / q^(5/2)
    ([Jk]); the chain rule along any differentiable path x(s) holds with it
    ([bk_chain]), and its trace vanishes ([Jk_trace]). In cylindrical
    components at a point (R, phi, Z) of a path the derivatives split into
    the parts along R, along Z and the explicit part along phi
    ([cyl_chain_R], [cyl_chain_P], [cyl_chain_Z]), and the vanishing trace
    reads d_phi b_phi + b_R + R (d_R b_R + d_Z b_Z) = 0 ([src_liouville]).
    [bk_kern] identifies b with CoilSym.kern. *)

From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
From Stellarocq Require Import Hypotheses Invariance CoilSym.
Local Open Scope R_scope.

(** A source: its point and its weighted tangent. *)
Record src := mksrc { sp1 : R ; sp2 : R ; sp3 : R ; sd1 : R ; sd2 : R ; sd3 : R }.

Section Source.

Variable sc : src.
Let p1 := sp1 sc. Let p2 := sp2 sc. Let p3 := sp3 sc.
Let d1 := sd1 sc. Let d2 := sd2 sc. Let d3 := sd3 sc.

Definition qk (x1 x2 x3 : R) : R :=
  (x1 - p1) * (x1 - p1) + (x2 - p2) * (x2 - p2) + (x3 - p3) * (x3 - p3).

Definition ck1 (x1 x2 x3 : R) : R := d2 * (x3 - p3) - d3 * (x2 - p2).
Definition ck2 (x1 x2 x3 : R) : R := d3 * (x1 - p1) - d1 * (x3 - p3).
Definition ck3 (x1 x2 x3 : R) : R := d1 * (x2 - p2) - d2 * (x1 - p1).

(** q^(-3/2) and q^(-5/2). *)
Definition h3 (x1 x2 x3 : R) : R := / (qk x1 x2 x3 * sqrt (qk x1 x2 x3)).
Definition h5 (x1 x2 x3 : R) : R := / (qk x1 x2 x3 * qk x1 x2 x3 * sqrt (qk x1 x2 x3)).

Definition bk1 (x1 x2 x3 : R) : R := ck1 x1 x2 x3 * h3 x1 x2 x3.
Definition bk2 (x1 x2 x3 : R) : R := ck2 x1 x2 x3 * h3 x1 x2 x3.
Definition bk3 (x1 x2 x3 : R) : R := ck3 x1 x2 x3 * h3 x1 x2 x3.

(** The Jacobian, row by row: the entry (i, k) is
    (d x e_k)_i h3 - 3 c_i r_k h5. *)
Definition J11 x1 x2 x3 := - 3 * ck1 x1 x2 x3 * (x1 - p1) * h5 x1 x2 x3.
Definition J12 x1 x2 x3 := - d3 * h3 x1 x2 x3 - 3 * ck1 x1 x2 x3 * (x2 - p2) * h5 x1 x2 x3.
Definition J13 x1 x2 x3 := d2 * h3 x1 x2 x3 - 3 * ck1 x1 x2 x3 * (x3 - p3) * h5 x1 x2 x3.
Definition J21 x1 x2 x3 := d3 * h3 x1 x2 x3 - 3 * ck2 x1 x2 x3 * (x1 - p1) * h5 x1 x2 x3.
Definition J22 x1 x2 x3 := - 3 * ck2 x1 x2 x3 * (x2 - p2) * h5 x1 x2 x3.
Definition J23 x1 x2 x3 := - d1 * h3 x1 x2 x3 - 3 * ck2 x1 x2 x3 * (x3 - p3) * h5 x1 x2 x3.
Definition J31 x1 x2 x3 := - d2 * h3 x1 x2 x3 - 3 * ck3 x1 x2 x3 * (x1 - p1) * h5 x1 x2 x3.
Definition J32 x1 x2 x3 := d1 * h3 x1 x2 x3 - 3 * ck3 x1 x2 x3 * (x2 - p2) * h5 x1 x2 x3.
Definition J33 x1 x2 x3 := - 3 * ck3 x1 x2 x3 * (x3 - p3) * h5 x1 x2 x3.

Lemma Jk_trace (x1 x2 x3 : R) : J11 x1 x2 x3 + J22 x1 x2 x3 + J33 x1 x2 x3 = 0.
Proof. unfold J11, J22, J33, ck1, ck2, ck3. ring. Qed.

(** * The chain rule along a path *)

Section Path.

Variables X1 X2 X3 : R -> R.
Variables s v1 v2 v3 : R.
Hypothesis D1 : is_derive X1 s v1.
Hypothesis D2 : is_derive X2 s v2.
Hypothesis D3 : is_derive X3 s v3.
Hypothesis Hq : 0 < qk (X1 s) (X2 s) (X3 s).

Let y1 := X1 s. Let y2 := X2 s. Let y3 := X3 s.

Lemma d_mul (f g : R -> R) (x df dg : R) :
  is_derive f x df -> is_derive g x dg -> is_derive (fun t => f t * g t) x (df * g x + f x * dg).
Proof. apply is_derive_mul. Qed.

Lemma d_const (c x : R) : is_derive (fun _ : R => c) x 0.
Proof. auto_derive; [exact I | reflexivity]. Qed.

Lemma d_sub_const (f : R -> R) (x df c : R) : is_derive f x df -> is_derive (fun t => f t - c) x df.
Proof.
  intros H. replace df with (df - 0) by ring.
  apply (is_derive_minus f (fun _ => c)); [exact H | apply d_const].
Qed.

Lemma d_add (f g : R -> R) (x df dg : R) :
  is_derive f x df -> is_derive g x dg -> is_derive (fun t => f t + g t) x (df + dg).
Proof. intros Hf Hg. apply (is_derive_plus f g); assumption. Qed.

Lemma d_sub (f g : R -> R) (x df dg : R) :
  is_derive f x df -> is_derive g x dg -> is_derive (fun t => f t - g t) x (df - dg).
Proof. intros Hf Hg. apply (is_derive_minus f g); assumption. Qed.

Lemma d_q : is_derive (fun t => qk (X1 t) (X2 t) (X3 t)) s
  (2 * ((y1 - p1) * v1 + (y2 - p2) * v2 + (y3 - p3) * v3)).
Proof.
  unfold qk.
  assert (E1 := d_sub_const X1 s v1 p1 D1).
  assert (E2 := d_sub_const X2 s v2 p2 D2).
  assert (E3 := d_sub_const X3 s v3 p3 D3).
  pose proof (d_add _ _ s _ _ (d_add _ _ s _ _ (d_mul _ _ s _ _ E1 E1) (d_mul _ _ s _ _ E2 E2))
                (d_mul _ _ s _ _ E3 E3)) as H.
  cbv beta in H. unfold y1, y2, y3.
  match goal with |- is_derive _ _ ?l => replace l with (v1 * (X1 s - p1) + (X1 s - p1) * v1 +
    (v2 * (X2 s - p2) + (X2 s - p2) * v2) + (v3 * (X3 s - p3) + (X3 s - p3) * v3)) by ring end.
  exact H.
Qed.

Let Q := qk y1 y2 y3.
Let S := sqrt Q.

Lemma HS : S * S = Q. Proof. unfold S. apply sqrt_sqrt. unfold Q, y1, y2, y3. lra. Qed.
Lemma HSpos : 0 < S. Proof. unfold S. apply sqrt_lt_R0. unfold Q, y1, y2, y3. lra. Qed.

Lemma d_h3 : is_derive (fun t => h3 (X1 t) (X2 t) (X3 t)) s
  (- 3 * ((y1 - p1) * v1 + (y2 - p2) * v2 + (y3 - p3) * v3) * h5 y1 y2 y3).
Proof.
  pose proof d_q as Dq.
  pose proof (is_derive_sqrt _ s _ Dq Hq) as Ds.
  pose proof (d_mul _ _ s _ _ Dq Ds) as Dp. cbv beta in Dp.
  assert (Hnz : qk (X1 s) (X2 s) (X3 s) * sqrt (qk (X1 s) (X2 s) (X3 s)) <> 0).
  { fold y1 y2 y3. fold Q S. pose proof HSpos. apply Rgt_not_eq. unfold Q, y1, y2, y3 in *. nra. }
  pose proof (is_derive_inv _ s _ Dp Hnz) as Di. cbv beta in Di.
  unfold h3. eapply is_derive_ext; [intros; reflexivity |].
  match goal with Di : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact Di |] end.
  fold y1 y2 y3. fold Q S. unfold h5. fold Q S.
  pose proof HS as E. pose proof HSpos as P.
  rewrite <- E. field. lra.
Qed.

Lemma d_c1 : is_derive (fun t => ck1 (X1 t) (X2 t) (X3 t)) s (d2 * v3 - d3 * v2).
Proof.
  unfold ck1. apply d_sub; apply is_derive_scal; apply d_sub_const; assumption.
Qed.
Lemma d_c2 : is_derive (fun t => ck2 (X1 t) (X2 t) (X3 t)) s (d3 * v1 - d1 * v3).
Proof.
  unfold ck2. apply d_sub; apply is_derive_scal; apply d_sub_const; assumption.
Qed.
Lemma d_c3 : is_derive (fun t => ck3 (X1 t) (X2 t) (X3 t)) s (d1 * v2 - d2 * v1).
Proof.
  unfold ck3. apply d_sub; apply is_derive_scal; apply d_sub_const; assumption.
Qed.

Theorem bk1_chain : is_derive (fun t => bk1 (X1 t) (X2 t) (X3 t)) s
  (J11 y1 y2 y3 * v1 + J12 y1 y2 y3 * v2 + J13 y1 y2 y3 * v3).
Proof.
  pose proof (d_mul _ _ s _ _ d_c1 d_h3) as H. cbv beta in H. unfold bk1.
  match goal with H : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact H |] end.
  unfold J11, J12, J13. fold y1 y2 y3. ring.
Qed.

Theorem bk2_chain : is_derive (fun t => bk2 (X1 t) (X2 t) (X3 t)) s
  (J21 y1 y2 y3 * v1 + J22 y1 y2 y3 * v2 + J23 y1 y2 y3 * v3).
Proof.
  pose proof (d_mul _ _ s _ _ d_c2 d_h3) as H. cbv beta in H. unfold bk2.
  match goal with H : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact H |] end.
  unfold J21, J22, J23. fold y1 y2 y3. ring.
Qed.

Theorem bk3_chain : is_derive (fun t => bk3 (X1 t) (X2 t) (X3 t)) s
  (J31 y1 y2 y3 * v1 + J32 y1 y2 y3 * v2 + J33 y1 y2 y3 * v3).
Proof.
  pose proof (d_mul _ _ s _ _ d_c3 d_h3) as H. cbv beta in H. unfold bk3.
  match goal with H : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact H |] end.
  unfold J31, J32, J33. fold y1 y2 y3. ring.
Qed.

End Path.

(** * Cylindrical components at (R, phi, Z) *)

Definition kx1 (R0 phi : R) : R := R0 * cos phi.
Definition kx2 (R0 phi : R) : R := R0 * sin phi.

Definition fR (R0 phi Z0 : R) : R :=
  bk1 (kx1 R0 phi) (kx2 R0 phi) Z0 * cos phi + bk2 (kx1 R0 phi) (kx2 R0 phi) Z0 * sin phi.
Definition fP (R0 phi Z0 : R) : R :=
  - bk1 (kx1 R0 phi) (kx2 R0 phi) Z0 * sin phi + bk2 (kx1 R0 phi) (kx2 R0 phi) Z0 * cos phi.
Definition fZ (R0 phi Z0 : R) : R := bk3 (kx1 R0 phi) (kx2 R0 phi) Z0.

(** The Jacobian applied to e_R, e_phi and e_z, with the rows read in e_R and
    e_phi. *)
Section Frame.
Variables R0 phi Z0 : R.
Let x1 := kx1 R0 phi. Let x2 := kx2 R0 phi. Let x3 := Z0.
Let c := cos phi. Let s := sin phi.
Definition JeR1 := J11 x1 x2 x3 * c + J12 x1 x2 x3 * s.
Definition JeR2 := J21 x1 x2 x3 * c + J22 x1 x2 x3 * s.
Definition JeR3 := J31 x1 x2 x3 * c + J32 x1 x2 x3 * s.
Definition JeP1 := - J11 x1 x2 x3 * s + J12 x1 x2 x3 * c.
Definition JeP2 := - J21 x1 x2 x3 * s + J22 x1 x2 x3 * c.
Definition JeP3 := - J31 x1 x2 x3 * s + J32 x1 x2 x3 * c.

(** Partial derivatives in R and Z at fixed phi, and the explicit derivative
    in phi at fixed R and Z. *)
Definition fR_R := JeR1 * c + JeR2 * s.
Definition fR_Z := J13 x1 x2 x3 * c + J23 x1 x2 x3 * s.
Definition fR_phi := R0 * (JeP1 * c + JeP2 * s) + fP R0 phi Z0.
Definition fP_R := - JeR1 * s + JeR2 * c.
Definition fP_Z := - J13 x1 x2 x3 * s + J23 x1 x2 x3 * c.
Definition fP_phi := R0 * (- JeP1 * s + JeP2 * c) - fR R0 phi Z0.
Definition fZ_R := JeR3.
Definition fZ_Z := J33 x1 x2 x3.
Definition fZ_phi := R0 * JeP3.
End Frame.

(** The vanishing trace in cylindrical components. *)
Theorem src_liouville (R0 phi Z0 : R) :
  fP_phi R0 phi Z0 + fR R0 phi Z0 + R0 * (fR_R R0 phi Z0 + fZ_Z R0 phi Z0) = 0.
Proof.
  unfold fP_phi, fR_R, fZ_Z, JeR1, JeR2, JeP1, JeP2.
  set (x1 := kx1 R0 phi). set (x2 := kx2 R0 phi).
  pose proof (Jk_trace x1 x2 Z0) as T.
  pose proof (cs1 phi) as C.
  replace (R0 * (- (- J11 x1 x2 Z0 * sin phi + J12 x1 x2 Z0 * cos phi) * sin phi
                 + (- J21 x1 x2 Z0 * sin phi + J22 x1 x2 Z0 * cos phi) * cos phi) - fR R0 phi Z0
           + fR R0 phi Z0
           + R0 * ((J11 x1 x2 Z0 * cos phi + J12 x1 x2 Z0 * sin phi) * cos phi
                   + (J21 x1 x2 Z0 * cos phi + J22 x1 x2 Z0 * sin phi) * sin phi + J33 x1 x2 Z0))
    with (R0 * ((J11 x1 x2 Z0 + J22 x1 x2 Z0) * (cos phi * cos phi + sin phi * sin phi) + J33 x1 x2 Z0))
    by ring.
  rewrite C. rewrite Rmult_1_r. rewrite T. ring.
Qed.

(** The chain rule for the cylindrical components along a path
    (R(s), phi(s), Z(s)). *)
Section CylPath.

Variables Rp Pp Zp : R -> R.
Variables s vR vP vZ : R.
Hypothesis DR : is_derive Rp s vR.
Hypothesis DP : is_derive Pp s vP.
Hypothesis DZ : is_derive Zp s vZ.
Hypothesis Hq : 0 < qk (kx1 (Rp s) (Pp s)) (kx2 (Rp s) (Pp s)) (Zp s).

Let r := Rp s. Let ph := Pp s. Let z := Zp s.

Lemma d_cos : is_derive (fun t => cos (Pp t)) s (- sin ph * vP).
Proof.
  pose proof (is_derive_comp cos Pp s (- sin (Pp s)) vP) as H.
  eapply is_derive_ext; [intros; reflexivity |].
  replace (- sin ph * vP) with (scal vP (- sin (Pp s))) by (unfold scal; simpl; unfold mult; simpl; unfold ph; ring).
  apply H; [| exact DP]. auto_derive; [exact I | ring].
Qed.

Lemma d_sin : is_derive (fun t => sin (Pp t)) s (cos ph * vP).
Proof.
  pose proof (is_derive_comp sin Pp s (cos (Pp s)) vP) as H.
  eapply is_derive_ext; [intros; reflexivity |].
  replace (cos ph * vP) with (scal vP (cos (Pp s))) by (unfold scal; simpl; unfold mult; simpl; unfold ph; ring).
  apply H; [| exact DP]. auto_derive; [exact I | ring].
Qed.

Lemma d_x1 : is_derive (fun t => kx1 (Rp t) (Pp t)) s (vR * cos ph + r * (- sin ph * vP)).
Proof. unfold kx1. exact (d_mul _ _ s _ _ DR d_cos). Qed.
Lemma d_x2 : is_derive (fun t => kx2 (Rp t) (Pp t)) s (vR * sin ph + r * (cos ph * vP)).
Proof. unfold kx2. exact (d_mul _ _ s _ _ DR d_sin). Qed.

Let X1 := fun t => kx1 (Rp t) (Pp t).
Let X2 := fun t => kx2 (Rp t) (Pp t).

Theorem cyl_chain_R : is_derive (fun t => fR (Rp t) (Pp t) (Zp t)) s
  (fR_R r ph z * vR + fR_Z r ph z * vZ + fR_phi r ph z * vP).
Proof.
  pose proof (bk1_chain X1 X2 Zp s _ _ _ d_x1 d_x2 DZ Hq) as B1.
  pose proof (bk2_chain X1 X2 Zp s _ _ _ d_x1 d_x2 DZ Hq) as B2.
  pose proof (d_add _ _ s _ _ (d_mul _ _ s _ _ B1 d_cos) (d_mul _ _ s _ _ B2 d_sin)) as H.
  cbv beta in H. unfold fR. unfold X1, X2 in H.
  match goal with H : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact H |] end.
  unfold fR_R, fR_Z, fR_phi, fP, JeR1, JeR2, JeP1, JeP2. fold r ph z.
  pose proof (cs1 ph) as C. unfold kx1, kx2. fold r ph.
  nra.
Qed.

Theorem cyl_chain_P : is_derive (fun t => fP (Rp t) (Pp t) (Zp t)) s
  (fP_R r ph z * vR + fP_Z r ph z * vZ + fP_phi r ph z * vP).
Proof.
  pose proof (bk1_chain X1 X2 Zp s _ _ _ d_x1 d_x2 DZ Hq) as B1.
  pose proof (bk2_chain X1 X2 Zp s _ _ _ d_x1 d_x2 DZ Hq) as B2.
  pose proof (d_add _ _ s _ _ (d_mul _ _ s _ _ (is_derive_opp _ s _ B1) d_sin) (d_mul _ _ s _ _ B2 d_cos)) as H.
  cbv beta in H. unfold fP. unfold X1, X2 in H.
  eapply is_derive_ext; [intros; unfold opp; simpl; reflexivity |].
  match goal with H : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact H |] end.
  unfold fP_R, fP_Z, fP_phi, fR, JeR1, JeR2, JeP1, JeP2, opp. simpl. fold r ph z.
  pose proof (cs1 ph) as C. unfold kx1, kx2. fold r ph.
  nra.
Qed.

Theorem cyl_chain_Z : is_derive (fun t => fZ (Rp t) (Pp t) (Zp t)) s
  (fZ_R r ph z * vR + fZ_Z r ph z * vZ + fZ_phi r ph z * vP).
Proof.
  pose proof (bk3_chain X1 X2 Zp s _ _ _ d_x1 d_x2 DZ Hq) as B3.
  unfold fZ. unfold X1, X2 in B3.
  match goal with H : is_derive _ _ ?l |- is_derive _ _ ?l' => replace l' with l; [exact H |] end.
  unfold fZ_R, fZ_Z, fZ_phi, JeR3, JeP3. fold r ph z. unfold kx1, kx2. fold r ph. ring.
Qed.

End CylPath.

End Source.

(** CoilSym.kern is bk. *)
Lemma bk_kern (sc : src) (x1 x2 x3 : R) :
  kern (sp1 sc, sp2 sc, sp3 sc) (sd1 sc, sd2 sc, sd3 sc) (x1, x2, x3)
  = (bk1 sc x1 x2 x3, bk2 sc x1 x2 x3, bk3 sc x1 x2 x3).
Proof.
  unfold kern, v3sub, dot3, cross3r, v3scal, bk1, bk2, bk3, ck1, ck2, ck3, h3, qk.
  apply v3_eq; ring.
Qed.
