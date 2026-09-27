(** The ideal-MHD force residual as expression trees, on VMEC's own grid.

    Every definition here builds [expr] values. Their extended-real meaning
    (through [xeval]) is the force residual of the equilibrium reconstructed
    from a wout file by the rule below; their interval meaning (through
    [ieval]) is what the extracted checker computes. Evaluation is sound by
    Expr.ieval_correct and Expr.iextend_correct, so this file needs no
    proofs: it is the statement of the physics.

   Reconstruction rule (the certified object). VMEC keeps R and Z on the
   full radial grid s_j = j h and lambda, iota and every field quantity on
   the half grid s_{j+1/2}. A certificate point is a full-grid node j
   together with its two half points; the rule is VMEC's own:

     R(h)   = sum_k c_k(h) cos(m_k u - n_k v)      on a half point h between
     Z(h)   = sum_k z_k(h) sin(m_k u - n_k v)      the nodes a (inner) and
                                                    b (outer),
       c_k(h)  = (c_k(a) + c_k(b)) / 2                             m_k even
       c_k(h)  = sqrt(s_h) (c_k(a)/sqrt(s_a) + c_k(b)/sqrt(s_b)) / 2  m_k odd
     dR/ds(h) = sum_k c'_k(h) cos(...)
       c'_k(h) = (c_k(b) - c_k(a)) / h                              m_k even
       c'_k(h) = sqrt(s_h) (c_k(b)/sqrt(s_b) - c_k(a)/sqrt(s_a)) / h
                 + c_k(h) / (2 s_h)                                 m_k odd
     lambda(h) = sum_k l_k(h) sin(...)   with the wout's half-grid lmns
     iota(h)   = the wout's half-grid iotas
     p(s)      = sum_j am_j s^j,   phip constant

   The even/odd rule is VMEC's parity-aware half-grid average (r12, rs in its
   Jacobian kernel; the wout's lmns from lmns_full); the c_k(h)/(2 s_h) term
   is the derivative of the sqrt(s) factor that VMEC folds into its Jacobian
   correction. Angular derivatives are exact derivatives of the series.

   Field and residual, all in flux coordinates (s,u,v), cylindrical embedding
   (R, phi=v, Z), at a half point:
     sqrtg = R (R_u Z_s - R_s Z_u)
     B^u = phip (iota - lambda_v) / sqrtg
     B^v = phip (1 + lambda_u) / sqrtg
     B_i = g_iu B^u + g_iv B^v
     mu0 sqrtg J^s = d_u B_v - d_v B_u
     r_u = - mu0 sqrtg J^s B^v            (at the outer half point)
     r_v =   mu0 sqrtg J^s B^u            (at the outer half point)
   and at the node, with radial derivatives as VMEC's centered differences of
   the half-grid values and node values as their averages:
     r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds

   Environment layout for one certificate point, K = number of modes:
     0            s_j     (the node)
     1            u
     2            v
     3            phip
     4, 5, 6      s_a, s_j, s_b    (nodes j-1, j, j+1)
     7, 8         s_h-, s_h+       (half points j-1/2, j+1/2)
     9, 10        iota at h-, h+
     11..31       am_0..am_20  (pressure power series, Pa)
     32+0K..      R nodes: 3 rows (j-1, j, j+1) of K values, row-major
     32+3K..      Z nodes: 3 rows
     32+6K..      lambda: 2 rows (h-, h+)
     32+8K..      the three antisymmetric blocks, when lasym
     then         the Boozer stream function's K coefficients and the two
                  flux functions I and G, for the two outputs that read them
     then         scratch slots filled by the bindings of [residual]

   Sharing: every quantity used more than once is allocated as a binding and
   referred to by its slot. [residual] returns the bindings in evaluation
   order together with the three components, each a slot reference. *)

From Coq Require Import ZArith List.
From Stellarocq Require Import Expr.

Import ListNotations.

Open Scope nat_scope.

(* ---------------------------------------------------------------- *)
(* Exact powers of two, as expressions                               *)

(** 2^e as a single node, which the interval evaluator computes with one
    power operation. Every read of an input carries this factor, since the
    inputs are integer mantissas. *)
Definition epow2 (e : Z) : expr := Epow2 e.

(* ---------------------------------------------------------------- *)
(* Builder: allocation of scratch slots                              *)

(** Allocation state: the next free slot and the bindings so far, newest
    first. *)
Record builder := Builder { b_next : nat ; b_binds : list binding }.

(** Store e in the next free slot; return the state and the slot reference. *)
Definition alloc (b : builder) (e : expr) : builder * expr :=
  (Builder (S (b_next b)) ((b_next b, e) :: b_binds b), Evar (b_next b)).

(** The bindings in evaluation order. *)
Definition bindings_of (b : builder) : list binding := rev (b_binds b).

Section WithExponents.

(** Exponent of each environment entry; entries are integer mantissas. *)
Variable exps : list Z.

(** Environment variable n scaled by its power-of-two exponent. *)
Definition evar (n : nat) : expr :=
  Emul (Evar n) (epow2 (nth n exps 0%Z)).

(** The node radius s_j. *)
Definition vS := evar 0.
(** Poloidal angle u. *)
Definition vU := evar 1.
(** Toroidal angle v. *)
Definition vV := evar 2.
(** Radial derivative of the toroidal flux over 2 pi. *)
Definition vPhip := evar 3.
(** Node radii s_a, s_j, s_b. *)
Definition slot_s_a := evar 4.
Definition slot_s_j := evar 5.
Definition slot_s_b := evar 6.
(** Half-point radii s_h-, s_h+. *)
Definition slot_s_hm := evar 7.
Definition slot_s_hp := evar 8.
(** Iota at the half points. *)
Definition slot_iota_m := evar 9.
Definition slot_iota_p := evar 10.
(** Pressure power-series coefficient j, in Pascal. *)
Definition slot_am (j : nat) := evar (11 + j).
(** Number of pressure coefficients in the environment. *)
Definition n_am : nat := 21.
(** First slot of the R cosine nodes (rows: j-1, j, j+1). *)
Definition base_R (K : nat) := 32.
(** First slot of the Z sine nodes. *)
Definition base_Z (K : nat) := 32 + 3*K.
(** First slot of the lambda sine half-point rows (h-, h+). *)
Definition base_L (K : nat) := 32 + 6*K.
(** The three antisymmetric blocks: R sine nodes, Z cosine nodes, lambda
    cosine half-point rows. Present only when lasym. *)
Definition base_Ra (K : nat) := 32 + 8*K.
Definition base_Za (K : nat) := 32 + 11*K.
Definition base_La (K : nat) := 32 + 14*K.
(** First slot of the stream function block, which is where the scratch slots
    begin for every output that carries no such block. *)
Definition base_W (lasym : bool) (K : nat) : nat :=
  if lasym then 32 + 16*K else 32 + 8*K.

Definition base_scratch (lasym : bool) (K : nat) : nat :=
  base_W lasym K.
(** Coefficient node: row j, mode k, in a block of K modes. *)
Definition slot_node (base K j k : nat) := evar (base + j*K + k).

(** Coefficient k of the stream function, and the two flux functions after
    it. *)
Definition slot_wcoef (lasym : bool) (K k : nat) :=
  evar (base_W lasym K + k).
Definition slot_Itor (lasym : bool) (K : nat) := evar (base_W lasym K + K).
Definition slot_Gpol (lasym : bool) (K : nat) := evar (base_W lasym K + K + 1).

(* ---------------------------------------------------------------- *)
(* Small expression helpers                                          *)

(** The constant 0. *)
Definition e0 := EfromZ 0.
(** The constant 1. *)
Definition e1 := EfromZ 1.
(** The constant 2. *)
Definition e2 := EfromZ 2.
(** The constant 4. *)
Definition e4 := EfromZ 4.

(** The square of an expression. *)
Definition esq (a : expr) := Emul a a.

(** mu0 = 4 pi 10^-7, built from the verified pi enclosure. *)
Definition mu0 : expr :=
  Ediv (Emul e4 Epi) (EfromZ 10000000).

(** The sum of a list of expressions; the empty sum is 0. *)
Fixpoint esum (l : list expr) : expr :=
  match l with
  | [] => e0
  | [a] => a
  | a :: tl => Eadd a (esum tl)
  end.

(** Multiplication by an integer constant. *)
Definition zmul (z : Z) (a : expr) := Emul (EfromZ z) a.

(* ---------------------------------------------------------------- *)
(* Pressure gradient dp/ds from the am power series                  *)

(** b^j by repeated multiplication. *)
Fixpoint ppow (b : expr) (j : nat) : expr :=
  match j with
  | O => e1
  | S j' => Emul b (ppow b j')
  end.

(** Which closed form the pressure takes. Anything piecewise is resolved by
    the generator, which selects the piece containing the node's s and emits
    its local cubic, so no comparison is needed here: the Akima and cubic
    spline families both arrive as [PCubic]. *)
Inductive pprofile : Type :=
  | PPower                       (* sum_j am_j s^j                        *)
  | PTwoPower (p q : nat)        (* am0 (1 - s^p)^q                       *)
  | PCubic                       (* am0 + am1 t + am2 t^2 + am3 t^3,
                                    t = s - am4                           *)
  | PRational (nn nd : nat)      (* (sum_{j<nn} am_j s^j)
                                    / (sum_{j<nd} am_{10+j} s^j)          *)
  | PGaussTrunc                  (* am0 (exp(-(s/am1)^2) - E1)/(1 - E1),
                                    E1 = exp(-(1/am1)^2)                  *)
  | PTwoPowerGs (p q g : nat)    (* am0 (1 - s^p)^q times
                                    1 + sum_{j<g} am_{3+3j}
                                          exp(-((s - am_{4+3j})/am_{5+3j})^2) *)
  | PPedestal                    (* sum_{i<16} am_i s^i + N am17
                                      (tanh(2(am18 - sqrt s)/am19)
                                       - tanh(2(am18 - 1)/am19)),
                                    N = 1/(tanh(2 am18/am19)
                                           - tanh(2(am18 - 1)/am19))      *)
  | PTwoLorentz (p q r t : nat). (* am0 (am1 (A - A1)/(1 - A1)
                                          + (1 - am1) (B - B1)/(1 - B1)),
                                    A = 1/(1 + (s/am2^2)^p)^q,
                                    B = 1/(1 + (s/am5^2)^r)^t,
                                    A1 and B1 the same at s = 1           *)

(** The derivative of a power series over the am slots offset by [off]. *)
Definition dpoly (off n : nat) : expr :=
  esum (map (fun j => Emul (EfromZ (Z.of_nat j))
                           (Emul (slot_am (off + j)) (ppow vS (j - 1))))
            (seq 1 (n - 1))).

(** The power series itself. *)
Definition poly (off n : nat) : expr :=
  esum (map (fun j => Emul (slot_am (off + j)) (ppow vS j)) (seq 0 n)).

(** The hyperbolic tangent, from the exponential. The denominator is
    exp(2x) + 1, which is positive for every real x, so this is total
    wherever exp is, and the quotient rule differentiates it without a
    guard. *)
Definition etanh (a : expr) : expr :=
  let e := Eexp (Emul e2 a) in
  Ediv (Esub e e1) (Eadd e e1).

(** Bump j of a two_power_gs profile: am_{3+3j} exp(-x^2) with
    x = (s - am_{4+3j})/am_{5+3j}. *)
Definition gs_bump (j : nat) : expr :=
  let x := Ediv (Esub vS (slot_am (4 + 3*j))) (slot_am (5 + 3*j)) in
  Emul (slot_am (3 + 3*j)) (Eexp (Eneg (esq x))).

(** Its derivative. *)
Definition gs_bump_d (j : nat) : expr :=
  let w := slot_am (5 + 3*j) in
  let x := Ediv (Esub vS (slot_am (4 + 3*j))) w in
  Emul (slot_am (3 + 3*j))
       (Emul (Eexp (Eneg (esq x))) (Eneg (Ediv (Emul e2 x) w))).

(** The Gaussian factor over the first g bumps, and its derivative. The
    generator sets g from the coefficients it finds, so a slot whose width
    is zero is never read. *)
Fixpoint gs_val (g : nat) : expr :=
  match g with O => e1 | S g' => Eadd (gs_val g') (gs_bump g') end.

Fixpoint gs_der (g : nat) : expr :=
  match g with O => e0 | S g' => Eadd (gs_der g') (gs_bump_d g') end.

(** d/ds of one Lorentz factor 1/(1 + (s/a^2)^p)^q. The p*q factor kills the
    degenerate p = 0 and q = 0 cases, where the factor is constant. *)
Definition lorentz_d (a : expr) (p q : nat) : expr :=
  let z := Ediv vS (esq a) in
  let d := Eadd e1 (ppow z p) in
  Eneg (Ediv (Emul (EfromZ (Z.of_nat (p * q)))
                   (Ediv (ppow z (p - 1)) (esq a)))
             (ppow d (S q))).

(** The same factor at the edge, s = 1. *)
Definition lorentz_edge (a : expr) (p q : nat) : expr :=
  let z := Ediv e1 (esq a) in
  Ediv e1 (ppow (Eadd e1 (ppow z p)) q).

(** dp/ds of the pressure at the node, in Pascal. *)
Definition pprime (prof : pprofile) : expr :=
  match prof with
  | PPower => dpoly 0 n_am
  | PTwoPower p q =>
      (* -a0 p q s^(p-1) (1 - s^p)^(q-1); the p*q factor kills the
         degenerate p = 0 and q = 0 cases, where the profile is constant *)
      Eneg (Emul (Emul (slot_am 0) (EfromZ (Z.of_nat (p * q))))
                 (Emul (ppow vS (p - 1))
                       (ppow (Esub e1 (ppow vS p)) (q - 1))))
  | PCubic =>
      let t := Esub vS (slot_am 4) in
      esum [slot_am 1;
            Emul e2 (Emul (slot_am 2) t);
            Emul (EfromZ 3) (Emul (slot_am 3) (esq t))]
  | PRational nn nd =>
      let nu := poly 0 nn in let de := poly 10 nd in
      Ediv (Esub (Emul (dpoly 0 nn) de) (Emul nu (dpoly 10 nd))) (esq de)
  | PGaussTrunc =>
      let inv1 := Ediv e1 (slot_am 1) in
      let x := Emul vS inv1 in
      Ediv (Emul (slot_am 0)
                 (Emul (Eexp (Eneg (esq x)))
                       (Eneg (Emul e2 (Emul vS (esq inv1))))))
           (Esub e1 (Eexp (Eneg (esq inv1))))
  | PTwoPowerGs p q g =>
      let tp := Emul (slot_am 0) (ppow (Esub e1 (ppow vS p)) q) in
      let tpd := Eneg (Emul (Emul (slot_am 0) (EfromZ (Z.of_nat (p * q))))
                            (Emul (ppow vS (p - 1))
                                  (ppow (Esub e1 (ppow vS p)) (q - 1)))) in
      Eadd (Emul tpd (gs_val g)) (Emul tp (gs_der g))
  | PPedestal =>
      (* d/ds tanh(2(c - sqrt s)/w) = (1 - T^2) * (-1/(w sqrt s)) *)
      let w := slot_am 19 in
      let c := slot_am 18 in
      let arg x := Ediv (Emul e2 (Esub c x)) w in
      let t1 := etanh (arg (Esqrt vS)) in
      let te := etanh (arg e1) in
      let t0 := etanh (Ediv (Emul e2 c) w) in
      let nn := Ediv e1 (Esub t0 te) in
      Eadd (dpoly 0 16)
           (Emul (Emul nn (slot_am 17))
                 (Emul (Esub e1 (esq t1))
                       (Eneg (Ediv e1 (Emul w (Esqrt vS))))))
  | PTwoLorentz p q r t =>
      let a1 := slot_am 1 in
      Emul (slot_am 0)
           (Eadd (Emul a1 (Ediv (lorentz_d (slot_am 2) p q)
                                (Esub e1 (lorentz_edge (slot_am 2) p q))))
                 (Emul (Esub e1 a1)
                       (Ediv (lorentz_d (slot_am 5) r t)
                             (Esub e1 (lorentz_edge (slot_am 5) r t)))))
  end.

(** The pressure itself at a radius x, in Pascal, for the outputs that read
    it at the half points rather than its derivative at the node. Each case
    is the profile whose derivative [pprime] is. *)
Definition poly_at (off n : nat) (x : expr) : expr :=
  esum (map (fun j => Emul (slot_am (off + j)) (ppow x j)) (seq 0 n)).

Definition gs_bump_at (j : nat) (x : expr) : expr :=
  let y := Ediv (Esub x (slot_am (4 + 3*j))) (slot_am (5 + 3*j)) in
  Emul (slot_am (3 + 3*j)) (Eexp (Eneg (esq y))).

Fixpoint gs_val_at (g : nat) (x : expr) : expr :=
  match g with O => e1 | S g' => Eadd (gs_val_at g' x) (gs_bump_at g' x) end.

Definition lorentz_at (a : expr) (p q : nat) (x : expr) : expr :=
  Ediv e1 (ppow (Eadd e1 (ppow (Ediv x (esq a)) p)) q).

Definition pvalue (prof : pprofile) (x : expr) : expr :=
  match prof with
  | PPower => poly_at 0 n_am x
  | PTwoPower p q => Emul (slot_am 0) (ppow (Esub e1 (ppow x p)) q)
  | PCubic =>
      let t := Esub x (slot_am 4) in
      esum [slot_am 0; Emul (slot_am 1) t; Emul (slot_am 2) (esq t);
            Emul (slot_am 3) (Emul t (esq t))]
  | PRational nn nd => Ediv (poly_at 0 nn x) (poly_at 10 nd x)
  | PGaussTrunc =>
      let inv1 := Ediv e1 (slot_am 1) in
      let ee := Eexp (Eneg (esq inv1)) in
      Emul (slot_am 0)
           (Ediv (Esub (Eexp (Eneg (esq (Emul x inv1)))) ee) (Esub e1 ee))
  | PTwoPowerGs p q g =>
      Emul (Emul (slot_am 0) (ppow (Esub e1 (ppow x p)) q)) (gs_val_at g x)
  | PPedestal =>
      let w := slot_am 19 in
      let c := slot_am 18 in
      let arg y := Ediv (Emul e2 (Esub c y)) w in
      let t1 := etanh (arg (Esqrt x)) in
      let te := etanh (arg e1) in
      let t0 := etanh (Ediv (Emul e2 c) w) in
      Eadd (poly_at 0 16 x) (Emul (slot_am 17) (Ediv (Esub t1 te) (Esub t0 te)))
  | PTwoLorentz p q r t =>
      let a1 := slot_am 1 in
      let A := lorentz_at (slot_am 2) p q x in
      let A1 := lorentz_edge (slot_am 2) p q in
      let B := lorentz_at (slot_am 5) r t x in
      let B1 := lorentz_edge (slot_am 5) r t in
      Emul (slot_am 0)
           (Eadd (Emul a1 (Ediv (Esub A A1) (Esub e1 A1)))
                 (Emul (Esub e1 a1) (Ediv (Esub B B1) (Esub e1 B1))))
  end.

(** What a certificate fixes about the equilibrium besides its coefficients:
    whether the reconstruction carries the antisymmetric half, and which
    closed form the pressure takes. *)
(** What the three components of a certificate carry.

    [RResidual] is the force residual itself. [RHarmonic m n] multiplies each
    component by cos(m u - n v), so that the integral over a surface is the
    resonant Fourier harmonic of the residual at that mode, which is what a
    rational surface leaves behind when the nested-surface ansatz cannot be
    satisfied there. [RGeometry] carries the integrands of the flux-surface
    averages instead: the Jacobian, the Jacobian-weighted square field, and
    the covariant B_u whose average is the enclosed toroidal current. *)
Inductive rout : Type :=
  | RResidual
  | RHarmonic (m n : Z)
  | RGeometry
  | RMercierA
  | RMercierB
  | RRadial
  | RRadialGeom
  | RRadialShear
  | RRadialAxis
  | RCovHarm (m n : Z)
  | RCovHarmS (m n : Z)
  | RStreamDefect
  | RBoozer (m n : Z)
  | RTerms
  | RRadialTerms
  | RJsTerms
  | RRadialJsTerms
  | RQuasiSym
  | RQuasiTwo
  | RWeighted (m n : Z)
  | RJump (vm : list (Z * Z))
  | RNewcomb (m n : Z)
  | RIota (m n : Z)
  | RForced
  | REnergy
  | RCoil (P : nat).

(** [REnergy] is the energy density on a straight line of states x + t xi,
    at the free radius of slot 0. The certificate carries, after the state, a
    block of its own: the parameter t, the sign of the Jacobian, and the node
    rows of the direction xi in the layout of the state's (R, Z and lambda,
    then the antisymmetric ones). The first bindings are the coefficients of
    the line, each state slot plus t times the matching slot of xi, and
    everything after them reads those and never the state directly. With
    gamma = 0 the mu0-scaled energy density of the Hermite reconstruction is

      w = |sqrt(g)| (B^2 / 2 - mu0 p),

    the first component; |sqrt(g)| and B^2 sqrt(g) are the other two. Its
    derivatives in t are those of Deriv.v along the slot of t, so the second
    one at t = 0 is the density of the second variation of the energy along
    xi. *)

(** [RCoil P] is a coil field against a torus. The first node row of the R
    and Z blocks is the torus,

      R(u, v) = sum R_mn cos(m u - n v),   Z(u, v) = sum Z_mn sin(m u - n v),

    read at the angles of slots 1 and 2, v the geometric toroidal angle. The
    block after the state holds P source points of the coils, six slots each
    in Cartesian coordinates: the point, then its weighted tangent, which is
    mu0 I dt / (4 pi) times the tangent of the coil there. The field at x is
    the sum over the points of the weighted tangent crossed with (x - point),
    over |x - point|^3: the trapezoidal rule of the Biot-Savart law, which is
    how the coil set is given. With n = x_u x x_v the components are
    B.n / sqrt(|B|^2 |n|^2), the sine of the angle between the field and the
    torus, then B.n and |B|^2. A torus on which the first vanishes is
    invariant under the field-line flow. *)

(** [RForced] is the node residual of [RResidual] less a source the
    certificate carries, one input slot per component: r_s - f_s, r_u - f_u
    and r_v - f_v. A zero of it at every collocation point is a discrete
    solution of the problem whose right-hand side is the source, which is
    what a manufactured solution poses: the source is the continuum residual
    of a chosen mapping, and the discrete solution's distance from that
    mapping is the discretization error. *)

(** [RNewcomb m n] reads a state in straight-field-line angles, whose lambda
    is zero, at the free radius of slot 0 between the node's two half points:
    the Jacobian sqrt(g) = R (R_u Z_s - R_s Z_u) of the Hermite
    reconstruction against cos(m u - n v) and against sin(m u - n v), whose
    integrals over the angles are the harmonic of sqrt(g) resonant on a
    surface where iota = n/m, and mu0 dp/ds there. [RIota m n] carries
    m iota - n at the free radius, with iota linear between the half points as
    [full_point_b] reads it, then iota and its radial derivative. *)

(** [RJump vm] is free-boundary balance: the jump of the total pressure
    p + B^2/2 across the plasma boundary against a vacuum pressure B_vac^2/2
    the certificate carries. The plasma side is the total pressure of the two
    half points extrapolated linearly to s = 1, which at the last interior
    node of VMEC's grid is its own 3/2, -1/2 rule for the edge pressure. The
    vacuum side is a trigonometric series over the modes vm,

      P_vac = sum_k (a_k cos(m_k u - n_k v) + b_k sin(m_k u - n_k v))
            + t sum_k (c_k cos(m_k u - n_k v) + d_k sin(m_k u - n_k v)),

    so that one scalar t sweeps the segment between two vacuum answers: with
    a and b the mean of their series and c and d half their difference, t = 1
    is the one and t = -1 the other. Each kernel is assembled from cos(m u),
    sin(m u), cos(n v) and sin(n v) by the angle-difference identities, which
    is the same function. The three components are the jump, the
    extrapolated plasma-side pressure and the vacuum pressure; [jump_b]
    builds them. *)

(** True when the output is read from the reconstruction at a free radius. *)
Definition is_radial (o : rout) : bool :=
  match o with
  | RRadial | RRadialGeom | RRadialShear | RRadialAxis | RRadialTerms
  | RRadialJsTerms => true
  | _ => false
  end.

(** The same for the surface current, mu0 sqrt(g) J^s = d_u B_v - d_v B_u,
    which r_u and r_v are built from and which has to vanish for a Boozer
    stream function to exist: [RJsTerms] carries d_u B_v, d_v B_u and their
    difference as the three components. *)

(** The three terms the radial residual is the difference of:

      r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds.

    A verdict reports r_s and says nothing about how it was arrived at, and
    for a converged equilibrium it is a difference of far larger numbers. How
    much larger is what decides how fine a covering has to be, since an
    interval evaluation loses the cancellation and pays for it in cells, and
    it decides which inputs the bound answers to at all: a term orders of
    magnitude below the others contributes nothing that a bound could see.
    [RTerms] carries the three as the three components, so the same machinery
    that bounds the residual bounds each of them, and their sizes are read off
    the same covering. Nothing is approximated: they are the very expressions
    the residual is assembled from, so their difference is it exactly. *)

(** The Boozer angles differ from VMEC's by a stream function w with

      B_u = I(s) + d_u w,   B_v = G(s) + d_v w,

    and w exists on a surface exactly when the covariant components have no
    curl there, which is to say when the surface current vanishes:

      d_u B_v - d_v B_u = mu0 sqrt(g) J^s.

    That quantity is what [r_u] and [r_v] already bound, so the precondition
    of the transformation is certified by the same machinery that certifies
    force balance. Given w, the transformation is explicit,

      p = (w - I lambda) / (G + iota I),  theta_B = u + lambda + iota p,
      zeta_B = v + p,

    so what is needed from a covering is the Fourier coefficients of w. Those
    follow from the coefficients of the covariant components, which are
    angular integrals of the components against a kernel, and

      [RCovHarm m n]   carries B_u cos(mu - nv), B_v cos(mu - nv) and
                       mu0 sqrt(g) J^s cos(mu - nv)
      [RCovHarmS m n]  carries the same three against sin(mu - nv)

    so that one covering per mode gives every projection either symmetry class
    needs, and the third component bounds the defect of the relation the two
    others have to satisfy. *)

(** True for the innermost interval, where the reconstruction cannot be the
    Hermite through two half points because the inner one does not exist.

    VMEC's parity rule reads a half point as the average of the two nodes
    around it, odd-m coefficients rescaled by sqrt(s). At the innermost half
    point one of those nodes is the axis, where that rescaling divides by
    zero, so no half point sits below 1.5 h and the Hermite has nothing to
    interpolate between.

    What is defined there is the rule the average is an instance of: the
    coefficient is linear in s for even m and sqrt(s) times a linear function
    for odd m, between two nodes. Read at the midpoint that is VMEC's own half
    point, coefficient for coefficient; read anywhere else it is the same
    interpolant off the midpoint. Taking the two innermost nodes as its knots
    covers the interval between the first two half points, which is the
    innermost interval any reconstruction of this kind can reach: below the
    first half point the Jacobian's 1/(4 s^2) has no bound. *)
Definition is_axis (o : rout) : bool :=
  match o with RRadialAxis => true | _ => false end.

(** An output that reads a Boozer stream function carries one more input
    block: its K coefficients, then the two flux functions I and G. Nothing
    else reads those slots, so the layout every other certificate uses is
    unchanged. *)
Definition n_extra (o : rout) : nat :=
  match o with RStreamDefect | RBoozer _ _ => 1 | _ => 0 end.

(** How many input slots that block holds. A stream function carries its K
    coefficients and the two flux functions beside them; the two-term
    quasisymmetry residual carries one flux function and nothing else. *)
Definition n_extra_slots (o : rout) (K : nat) : nat :=
  match o with
  | RStreamDefect | RBoozer _ _ => K + 2
  | RQuasiTwo => 1
  | RJump vm => 4 * length vm + 1
  | RForced => 3
  | REnergy => 16 * K + 2
  | RCoil P => 6 * P
  | _ => 0
  end.

(** First scratch slot, which depends on whether that block is there. *)
Definition base_scratch_of (lasym : bool) (o : rout) (K : nat) : nat :=
  base_W lasym K + n_extra_slots o K.

(** The flux function a two-term certificate carries. *)
Definition slot_F0 (lasym : bool) (K : nat) := evar (base_W lasym K).

(** Slot i of a jump certificate's vacuum block: the cosine and sine
    coefficients of the mean series mode by mode, then those of the half
    difference, then t. *)
Definition slot_vac (lasym : bool) (K i : nat) := evar (base_W lasym K + i).

(** Component i of a forced certificate's source. *)
Definition slot_src (lasym : bool) (K i : nat) := evar (base_W lasym K + i).

Record pconfig := PConfig {
  pc_lasym : bool ;
  pc_prof : pprofile ;
  pc_out : rout
}.

(* ---------------------------------------------------------------- *)
(* Per-mode angular kernels                                          *)

(** Kernel argument m*u - n*v of one Fourier mode. *)
Definition kern_arg (m n : Z) : expr :=
  Esub (Emul (EfromZ m) vU) (Emul (EfromZ n) vV).

(** One mode: its numbers and its cosine and sine kernels. *)
Record mode_kernels := MKer {
  mk_m : Z ; mk_n : Z ;
  mk_cos : expr ; mk_sin : expr }.

(** The cosine and sine of m a for each integer m of a list, allocated once
    each, and the lookup of one of them. A lookup that misses builds the pair
    in place, so what it returns is cos(m a) and sin(m a) either way. *)
Fixpoint zkernels_b (b : builder) (a : expr) (ms : list Z)
    : builder * list (Z * (expr * expr)) :=
  match ms with
  | [] => (b, [])
  | m :: tl =>
      let (b, c) := alloc b (Ecos (Emul (EfromZ m) a)) in
      let (b, s) := alloc b (Esin (Emul (EfromZ m) a)) in
      let (b, rest) := zkernels_b b a tl in
      (b, (m, (c, s)) :: rest)
  end.

Fixpoint zlook (m : Z) (a : expr) (l : list (Z * (expr * expr))) : expr * expr :=
  match l with
  | [] => (Ecos (Emul (EfromZ m) a), Esin (Emul (EfromZ m) a))
  | (k, cs) :: tl => if Z.eqb k m then cs else zlook m a tl
  end.

(** Allocate the kernels of every mode. *)
Fixpoint kernels_b (b : builder) (modes : list (Z * Z))
    : builder * list mode_kernels :=
  match modes with
  | [] => (b, [])
  | mn :: tl =>
      let (m, n) := mn in
      let (b, c) := alloc b (Ecos (kern_arg m n)) in
      let (b, s) := alloc b (Esin (kern_arg m n)) in
      let (b, rest) := kernels_b b tl in
      (b, MKer m n c s :: rest)
  end.

(* ---------------------------------------------------------------- *)
(* Half-point coefficients by VMEC's parity-aware rule               *)

(** Scalars of one half point shared by every mode. *)
Record half_scalars := HScal {
  hs_half : expr ;        (* 1/2 *)
  hs_inv_h : expr ;       (* 1 / (s_b - s_a) *)
  hs_sqrt_h : expr ;      (* sqrt(s_h) *)
  hs_inv_sqrt_a : expr ;  (* 1 / sqrt(s_a) *)
  hs_inv_sqrt_b : expr ;  (* 1 / sqrt(s_b) *)
  hs_inv_2s : expr }.     (* 1 / (2 s_h) *)

(** Allocate the scalars of the half point s_h between s_a and s_b. *)
Definition half_scalars_b (b : builder) (s_a s_b s_h : expr)
    : builder * half_scalars :=
  let (b, half) := alloc b (Ediv e1 e2) in
  let (b, inv_h) := alloc b (Ediv e1 (Esub s_b s_a)) in
  let (b, sqrt_h) := alloc b (Esqrt s_h) in
  let (b, inv_sqrt_a) := alloc b (Ediv e1 (Esqrt s_a)) in
  let (b, inv_sqrt_b) := alloc b (Ediv e1 (Esqrt s_b)) in
  let (b, inv_2s) := alloc b (Ediv e1 (Emul e2 s_h)) in
  (b, HScal half inv_h sqrt_h inv_sqrt_a inv_sqrt_b inv_2s).

(** A coefficient at the half point: value and radial derivative. *)
Record coef2 := Coef2 { c_val : expr ; c_ds : expr }.

(** Allocate c(h) and c'(h) of one mode of poloidal number m from its node
    values ya (inner) and yb (outer). *)
Definition halfcoef_b (b : builder) (hs : half_scalars) (m : Z)
    (ya yb : expr) : builder * coef2 :=
  if Z.even m then
    let (b, c) := alloc b (Emul (hs_half hs) (Eadd ya yb)) in
    let (b, cs) := alloc b (Emul (Esub yb ya) (hs_inv_h hs)) in
    (b, Coef2 c cs)
  else
    let (b, qa) := alloc b (Emul ya (hs_inv_sqrt_a hs)) in
    let (b, qb) := alloc b (Emul yb (hs_inv_sqrt_b hs)) in
    let (b, c) := alloc b (Emul (hs_sqrt_h hs)
                                (Emul (hs_half hs) (Eadd qa qb))) in
    let (b, cs) := alloc b (Eadd (Emul (hs_sqrt_h hs)
                                       (Emul (Esub qb qa) (hs_inv_h hs)))
                                 (Emul c (hs_inv_2s hs))) in
    (b, Coef2 c cs).

(** Allocate the half-point coefficients of modes 0..K-1 of a node block:
    rows ra (inner node) and rb (outer node). *)
Fixpoint halfcoefs_b (b : builder) (hs : half_scalars) (base K ra rb : nat)
    (modes : list (Z * Z)) (k : nat) : builder * list coef2 :=
  match modes with
  | [] => (b, [])
  | mn :: tl =>
      let (b, c) := halfcoef_b b hs (fst mn)
                      (slot_node base K ra k) (slot_node base K rb k) in
      let (b, rest) := halfcoefs_b b hs base K ra rb tl (S k) in
      (b, c :: rest)
  end.

(** The lambda coefficients of a half-point row, as slot references. *)
Fixpoint lambdacoefs_b (b : builder) (base K row : nat) (modes : list (Z * Z))
    (k : nat) : builder * list expr :=
  match modes with
  | [] => (b, [])
  | _ :: tl =>
      let (b, l) := alloc b (slot_node base K row k) in
      let (b, rest) := lambdacoefs_b b base K row tl (S k) in
      (b, l :: rest)
  end.

(* ---------------------------------------------------------------- *)
(* Fourier assembly at a half point                                  *)
(* For F = sum c_k cos(a_k):                                         *)
(*   F    = sum c cos      F_s  = sum c' cos                          *)
(*   F_u  = sum -m c sin   F_v  = sum  n c sin                       *)
(*   F_su = sum -m c' sin  F_sv = sum  n c' sin                      *)
(*   F_uu = sum -m^2 c cos F_uv = sum m n c cos  F_vv = sum -n^2 c cos *)
(* For F = sum c_k sin(a_k): swap cos<->sin and negate where the     *)
(* derivative of sin gives cos:                                      *)
(*   F    = sum c sin      F_s  = sum c' sin                          *)
(*   F_u  = sum  m c cos   F_v  = sum -n c cos                       *)
(*   F_su = sum  m c' cos  F_sv = sum -n c' cos                      *)
(*   F_uu = sum -m^2 c sin F_uv = sum m n c sin  F_vv = sum -n^2 c sin *)

(** A Fourier series and its partial derivatives at the half point. *)
Record partials := Partials {
  p_0 : expr ; p_s : expr ;
  p_u : expr ; p_v : expr ;
  p_su : expr ; p_sv : expr ;
  p_uu : expr ; p_uv : expr ; p_vv : expr }.

(** Sum a cos series (even = true) or a sin series with its derivatives. *)
Definition assemble (kers : list mode_kernels) (coefs : list coef2)
    (even : bool) : partials :=
  let pair := combine kers coefs in
  let sum f := esum (map f pair) in
  let k0 kc := if even then mk_cos (fst kc) else mk_sin (fst kc) in
  let k1 kc := if even then mk_sin (fst kc) else mk_cos (fst kc) in
  let su kc := if even then Z.opp (mk_m (fst kc)) else mk_m (fst kc) in
  let sv kc := if even then mk_n (fst kc) else Z.opp (mk_n (fst kc)) in
  Partials
    (sum (fun kc => Emul (c_val (snd kc)) (k0 kc)))
    (sum (fun kc => Emul (c_ds  (snd kc)) (k0 kc)))
    (sum (fun kc => zmul (su kc) (Emul (c_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (c_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (su kc) (Emul (c_ds (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (c_ds (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (Z.opp (mk_m (fst kc) * mk_m (fst kc)))
                         (Emul (c_val (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (mk_m (fst kc) * mk_n (fst kc))
                         (Emul (c_val (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (Z.opp (mk_n (fst kc) * mk_n (fst kc)))
                         (Emul (c_val (snd kc)) (k0 kc)))).

(** Sum two series termwise. A lasym reconstruction adds the antisymmetric
    parity to the symmetric one before either is allocated, so each of the
    nine sums still occupies exactly one slot. *)
Definition padd (p q : partials) : partials :=
  Partials (Eadd (p_0 p) (p_0 q)) (Eadd (p_s p) (p_s q))
           (Eadd (p_u p) (p_u q)) (Eadd (p_v p) (p_v q))
           (Eadd (p_su p) (p_su q)) (Eadd (p_sv p) (p_sv q))
           (Eadd (p_uu p) (p_uu q)) (Eadd (p_uv p) (p_uv q))
           (Eadd (p_vv p) (p_vv q)).

(** Allocate the partials of a series, so that each sum is evaluated once. *)
Definition partials_b (b : builder) (p : partials) : builder * partials :=
  let (b, a0)  := alloc b (p_0 p) in
  let (b, as_) := alloc b (p_s p) in
  let (b, au)  := alloc b (p_u p) in
  let (b, av)  := alloc b (p_v p) in
  let (b, asu) := alloc b (p_su p) in
  let (b, asv) := alloc b (p_sv p) in
  let (b, auu) := alloc b (p_uu p) in
  let (b, auv) := alloc b (p_uv p) in
  let (b, avv) := alloc b (p_vv p) in
  (b, Partials a0 as_ au av asu asv auu auv avv).

(** The lambda series at a half point: angular derivatives only. *)
Record lpartials := LPartials {
  l_u : expr ; l_v : expr ; l_uu : expr ; l_uv : expr ; l_vv : expr }.

(** The angular derivatives of a lambda series, sine (even = false) or
    cosine (even = true), with the same sign convention as [assemble]. *)
Definition lambda_terms (kers : list mode_kernels) (coefs : list expr)
    (even : bool) : lpartials :=
  let pair := combine kers coefs in
  let sum f := esum (map f pair) in
  let k0 kc := if even then mk_cos (fst kc) else mk_sin (fst kc) in
  let k1 kc := if even then mk_sin (fst kc) else mk_cos (fst kc) in
  let su kc := if even then Z.opp (mk_m (fst kc)) else mk_m (fst kc) in
  let sv kc := if even then mk_n (fst kc) else Z.opp (mk_n (fst kc)) in
  LPartials
    (sum (fun kc => zmul (su kc) (Emul (snd kc) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (snd kc) (k1 kc))))
    (sum (fun kc => zmul (Z.opp (mk_m (fst kc) * mk_m (fst kc)))
                         (Emul (snd kc) (k0 kc))))
    (sum (fun kc => zmul (mk_m (fst kc) * mk_n (fst kc))
                         (Emul (snd kc) (k0 kc))))
    (sum (fun kc => zmul (Z.opp (mk_n (fst kc) * mk_n (fst kc)))
                         (Emul (snd kc) (k0 kc)))).

(** Sum two lambda series termwise. *)
Definition ladd (p q : lpartials) : lpartials :=
  LPartials (Eadd (l_u p) (l_u q)) (Eadd (l_v p) (l_v q))
            (Eadd (l_uu p) (l_uu q)) (Eadd (l_uv p) (l_uv q))
            (Eadd (l_vv p) (l_vv q)).

(** Allocate the angular derivatives of a lambda series. *)
Definition lambda_partials_b (b : builder) (l : lpartials)
    : builder * lpartials :=
  let (b, lu) := alloc b (l_u l) in
  let (b, lv) := alloc b (l_v l) in
  let (b, luu) := alloc b (l_uu l) in
  let (b, luv) := alloc b (l_uv l) in
  let (b, lvv) := alloc b (l_vv l) in
  (b, LPartials lu lv luu luv lvv).

(* ---------------------------------------------------------------- *)
(* Third angular derivatives, for the quasisymmetry residual        *)

(** The quasisymmetry residual reads second angular derivatives of the
    field, and the field reads first derivatives of the Jacobian, so the
    series are carried to third order in the angles and to second order in
    the angles beside a radial derivative. Nothing on the residual path reads
    these, so they live in their own records and are allocated only for the
    output that asks for them; every other certificate keeps the bindings it
    had. Continuing the table above, for F = sum c cos(a):
      F_uuu = sum  m^3 c sin      F_uuv = sum -m^2 n c sin
      F_uvv = sum  m n^2 c sin    F_vvv = sum -n^3 c sin
      F_suu = sum -m^2 c' cos     F_suv = sum  m n c' cos    F_svv = sum -n^2 c' cos
    and for F = sum c sin(a) the third derivatives take cos with the opposite
    signs. Each third-order factor is the first-order factor of that angle
    times the second-order factor of the other two, which is how they are
    written below, so the same two switches [su] and [sv] serve both
    parities. *)
Record partials3 := Partials3 {
  p3_uuu : expr ; p3_uuv : expr ; p3_uvv : expr ; p3_vvv : expr ;
  p3_suu : expr ; p3_suv : expr ; p3_svv : expr }.

Definition assemble3 (kers : list mode_kernels) (coefs : list coef2)
    (even : bool) : partials3 :=
  let pair := combine kers coefs in
  let sum f := esum (map f pair) in
  let k0 kc := if even then mk_cos (fst kc) else mk_sin (fst kc) in
  let k1 kc := if even then mk_sin (fst kc) else mk_cos (fst kc) in
  let su kc := if even then Z.opp (mk_m (fst kc)) else mk_m (fst kc) in
  let sv kc := if even then mk_n (fst kc) else Z.opp (mk_n (fst kc)) in
  let mm kc := (mk_m (fst kc) * mk_m (fst kc))%Z in
  let nn kc := (mk_n (fst kc) * mk_n (fst kc))%Z in
  Partials3
    (sum (fun kc => zmul (su kc * Z.opp (mm kc))%Z
                         (Emul (c_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc * Z.opp (mm kc))%Z
                         (Emul (c_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (su kc * Z.opp (nn kc))%Z
                         (Emul (c_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc * Z.opp (nn kc))%Z
                         (Emul (c_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (Z.opp (mm kc)) (Emul (c_ds (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (mk_m (fst kc) * mk_n (fst kc))%Z
                         (Emul (c_ds (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (Z.opp (nn kc)) (Emul (c_ds (snd kc)) (k0 kc)))).

(** Sum two third-order series termwise, as [padd] does. *)
Definition padd3 (p q : partials3) : partials3 :=
  Partials3 (Eadd (p3_uuu p) (p3_uuu q)) (Eadd (p3_uuv p) (p3_uuv q))
            (Eadd (p3_uvv p) (p3_uvv q)) (Eadd (p3_vvv p) (p3_vvv q))
            (Eadd (p3_suu p) (p3_suu q)) (Eadd (p3_suv p) (p3_suv q))
            (Eadd (p3_svv p) (p3_svv q)).

(** Allocate each of the seven sums. *)
Definition partials3_b (b : builder) (p : partials3) : builder * partials3 :=
  let (b, a1) := alloc b (p3_uuu p) in
  let (b, a2) := alloc b (p3_uuv p) in
  let (b, a3) := alloc b (p3_uvv p) in
  let (b, a4) := alloc b (p3_vvv p) in
  let (b, a5) := alloc b (p3_suu p) in
  let (b, a6) := alloc b (p3_suv p) in
  let (b, a7) := alloc b (p3_svv p) in
  (b, Partials3 a1 a2 a3 a4 a5 a6 a7).

(** The stream function's third angular derivatives. *)
Record lpartials3 := LPartials3 {
  l3_uuu : expr ; l3_uuv : expr ; l3_uvv : expr ; l3_vvv : expr }.

Definition lambda_terms3 (kers : list mode_kernels) (coefs : list expr)
    (even : bool) : lpartials3 :=
  let pair := combine kers coefs in
  let sum f := esum (map f pair) in
  let k1 kc := if even then mk_sin (fst kc) else mk_cos (fst kc) in
  let su kc := if even then Z.opp (mk_m (fst kc)) else mk_m (fst kc) in
  let sv kc := if even then mk_n (fst kc) else Z.opp (mk_n (fst kc)) in
  let mm kc := (mk_m (fst kc) * mk_m (fst kc))%Z in
  let nn kc := (mk_n (fst kc) * mk_n (fst kc))%Z in
  LPartials3
    (sum (fun kc => zmul (su kc * Z.opp (mm kc))%Z (Emul (snd kc) (k1 kc))))
    (sum (fun kc => zmul (sv kc * Z.opp (mm kc))%Z (Emul (snd kc) (k1 kc))))
    (sum (fun kc => zmul (su kc * Z.opp (nn kc))%Z (Emul (snd kc) (k1 kc))))
    (sum (fun kc => zmul (sv kc * Z.opp (nn kc))%Z (Emul (snd kc) (k1 kc)))).

Definition ladd3 (p q : lpartials3) : lpartials3 :=
  LPartials3 (Eadd (l3_uuu p) (l3_uuu q)) (Eadd (l3_uuv p) (l3_uuv q))
             (Eadd (l3_uvv p) (l3_uvv q)) (Eadd (l3_vvv p) (l3_vvv q)).

Definition lambda_partials3_b (b : builder) (l : lpartials3)
    : builder * lpartials3 :=
  let (b, a1) := alloc b (l3_uuu l) in
  let (b, a2) := alloc b (l3_uuv l) in
  let (b, a3) := alloc b (l3_uvv l) in
  let (b, a4) := alloc b (l3_vvv l) in
  (b, LPartials3 a1 a2 a3 a4).

(* ---------------------------------------------------------------- *)
(* The divergence of the Jacobian-weighted field                     *)

(** VMEC's ansatz sets sqrt(g) B^u = phip (iota - lambda_v),
    sqrt(g) B^v = phip (1 + lambda_u) and sqrt(g) B^s = 0. In flux
    coordinates

      div B = (1/sqrt(g)) [ d_s(sqrt(g) B^s) + d_u(sqrt(g) B^u)
                                             + d_v(sqrt(g) B^v) ],

    whose first term is absent because the field has no radial component,
    and whose other two are phip times -lambda_uv and +lambda_uv, since
    iota is a flux function and the 1 is a constant. This builds that sum;
    Identities.v proves it is exactly zero. *)
Definition div_angular (pL : lpartials) : expr :=
  Eadd (Emul vPhip (Eneg (l_uv pL))) (Emul vPhip (l_uv pL)).

(* ---------------------------------------------------------------- *)
(* Field quantities of one half point                                *)

(** What the residual needs from a half point, and the Jacobian, which the
    surface averages need. *)
Record halfq := HalfQ {
  q_Bu : expr ; q_Bv : expr ;          (* contravariant B^u, B^v *)
  q_B_u : expr ; q_B_v : expr ;        (* covariant B_u, B_v *)
  q_B_s : expr ;                       (* covariant B_s *)
  q_B_s_u : expr ; q_B_s_v : expr ;    (* angular derivatives of B_s *)
  q_B_v_u : expr ; q_B_u_v : expr ;    (* d_u B_v and d_v B_u, whose
                                          difference is the surface current *)
  q_mu0Js : expr ;                     (* mu0 sqrtg J^s = d_u B_v - d_v B_u *)
  q_sqrtg : expr ;                     (* the Jacobian sqrt(g) = R tau *)
  q_R : expr ; q_Ru : expr ; q_Rv : expr ;   (* the cylindrical embedding *)
  q_Zu : expr ; q_Zv : expr ;
  q_guu : expr ;                       (* the metric element g_uu *)
  q_L : expr ; q_Lu : expr ; q_Lv : expr ;   (* the stream function *)
  (* The rest of what the half point allocates, exposed so that a later
     stage can build on it without allocating it again. The quasisymmetry
     residual reads the series, the Jacobian, the metric and the field with
     their first angular derivatives from here and adds only what sits above
     them. Nothing is allocated for these; they are the slots already bound
     above, returned by name. *)
  q_Rs : expr ; q_Rsu : expr ; q_Rsv : expr ;
  q_Ruu : expr ; q_Ruv : expr ; q_Rvv : expr ;
  q_Zs : expr ; q_Zsu : expr ; q_Zsv : expr ;
  q_Zuu : expr ; q_Zuv : expr ; q_Zvv : expr ;
  q_Luu : expr ; q_Luv : expr ; q_Lvv : expr ;
  q_tau : expr ; q_tau_u : expr ; q_tau_v : expr ;
  q_g_u : expr ; q_g_v : expr ;
  q_guv : expr ; q_gvv : expr ;
  q_guu_v : expr ; q_guv_u : expr ; q_guv_v : expr ; q_gvv_u : expr ;
  q_bu_num : expr ; q_bv_num : expr ; q_g2 : expr ;
  q_Bu_u : expr ; q_Bv_u : expr ; q_Bu_v : expr ; q_Bv_v : expr }.

(* ---------------------------------------------------------------- *)
(* Integrands of the flux-surface averages                           *)

(** The quantities below are angular integrands: their integral over a
    surface, which Quad.v encloses by summing over cells that tile the
    angular torus, is the physics. None allocates, so the residual path
    pays nothing for them.

      dV/ds   = int sqrt(g) du dv
      2 pi I  = int B_u du            the enclosed toroidal current
      2 pi G  = int B_v dv            the enclosed poloidal current
      <B^2>   the Jacobian-weighted square field

    Written against the slots [half_point_b] already allocated. *)

(** The square of the field strength at a half point. *)
Definition q_B2 (q : halfq) : expr :=
  Eadd (Emul (q_Bu q) (q_B_u q)) (Emul (q_Bv q) (q_B_v q)).

(** The integrand of the Jacobian-weighted mean square field. *)
Definition q_sqrtg_B2 (q : halfq) : expr := Emul (q_sqrtg q) (q_B2 q).

(** The coefficients of the half point s_h between the node rows ra and rb
    (R and Z), with the lambda row rl. They read the knots and the wout's own
    numbers and no angle, and they are allocated before the kernels so that
    every cell of a node shares them: the driver evaluates the leading run of
    bindings that read neither varied slot once per node, and for a covering
    of a surface this stage is most of the bindings. *)
Record half_coefs := HCoefs {
  hc_R : list coef2 ; hc_Z : list coef2 ; hc_L : list expr ;
  hc_Ra : list coef2 ; hc_Za : list coef2 ; hc_La : list expr }.

Definition half_coefs_b (b : builder) (lasym : bool)
    (modes : list (Z * Z)) (K ra rb rl : nat) (s_a s_b s_h : expr)
    : builder * half_coefs :=
  let (b, hs) := half_scalars_b b s_a s_b s_h in
  let (b, cR) := halfcoefs_b b hs (base_R K) K ra rb modes 0 in
  let (b, cZ) := halfcoefs_b b hs (base_Z K) K ra rb modes 0 in
  let (b, cL) := lambdacoefs_b b (base_L K) K rl modes 0 in
  (* The antisymmetric halves: R gains a sine series, Z and lambda a cosine
     series, over the same modes and the same parity-aware half-grid rule.
     Nothing is allocated for them under stellarator symmetry, so that path
     keeps the slot numbering and the expressions it had. *)
  let (b, cRa) := if lasym then halfcoefs_b b hs (base_Ra K) K ra rb modes 0
                  else (b, @nil coef2) in
  let (b, cZa) := if lasym then halfcoefs_b b hs (base_Za K) K ra rb modes 0
                  else (b, @nil coef2) in
  let (b, cLa) := if lasym then lambdacoefs_b b (base_La K) K rl modes 0
                  else (b, @nil expr) in
  (b, HCoefs cR cZ cL cRa cZa cLa).

(** The field of a half point from its coefficients, the kernels and iota. *)
Definition half_point_b (b : builder) (lasym : bool)
    (kers : list mode_kernels) (hc : half_coefs) (iota : expr)
    : builder * halfq :=
  let cR := hc_R hc in let cZ := hc_Z hc in let cL := hc_L hc in
  let cRa := hc_Ra hc in let cZa := hc_Za hc in let cLa := hc_La hc in
  let (b, pR) := partials_b b
      (if lasym then padd (assemble kers cR true) (assemble kers cRa false)
       else assemble kers cR true) in
  let (b, pZ) := partials_b b
      (if lasym then padd (assemble kers cZ false) (assemble kers cZa true)
       else assemble kers cZ false) in
  let (b, pL) := lambda_partials_b b
      (if lasym then ladd (lambda_terms kers cL false)
                          (lambda_terms kers cLa true)
       else lambda_terms kers cL false) in
  let R    := p_0 pR in  let R_s  := p_s pR in
  let R_u  := p_u pR in  let R_v  := p_v pR in
  let R_su := p_su pR in let R_sv := p_sv pR in
  let R_uu := p_uu pR in let R_uv := p_uv pR in let R_vv := p_vv pR in
  let Z_s  := p_s pZ in
  let Z_u  := p_u pZ in  let Z_v  := p_v pZ in
  let Z_su := p_su pZ in let Z_sv := p_sv pZ in
  let Z_uu := p_uu pZ in let Z_uv := p_uv pZ in let Z_vv := p_vv pZ in
  let L_u  := l_u pL in  let L_v  := l_v pL in
  let L_uu := l_uu pL in let L_uv := l_uv pL in let L_vv := l_vv pL in
  let (b, tau)   := alloc b (Esub (Emul R_u Z_s) (Emul R_s Z_u)) in
  let (b, sqrtg) := alloc b (Emul R tau) in
  let (b, tau_u) := alloc b (Esub (Eadd (Emul R_uu Z_s) (Emul R_u Z_su))
                                  (Eadd (Emul R_su Z_u) (Emul R_s Z_uu))) in
  let (b, tau_v) := alloc b (Esub (Eadd (Emul R_uv Z_s) (Emul R_u Z_sv))
                                  (Eadd (Emul R_sv Z_u) (Emul R_s Z_uv))) in
  let (b, g_u) := alloc b (Eadd (Emul R_u tau) (Emul R tau_u)) in
  let (b, g_v) := alloc b (Eadd (Emul R_v tau) (Emul R tau_v)) in
  let (b, guu) := alloc b (Eadd (esq R_u) (esq Z_u)) in
  let (b, guv) := alloc b (Eadd (Emul R_u R_v) (Emul Z_u Z_v)) in
  let (b, gvv) := alloc b (Eadd (Eadd (esq R_v) (esq Z_v)) (esq R)) in
  let (b, gsu) := alloc b (Eadd (Emul R_s R_u) (Emul Z_s Z_u)) in
  let (b, gsv) := alloc b (Eadd (Emul R_s R_v) (Emul Z_s Z_v)) in
  let (b, gsu_u) := alloc b (Eadd (Eadd (Emul R_su R_u) (Emul R_s R_uu))
                                  (Eadd (Emul Z_su Z_u) (Emul Z_s Z_uu))) in
  let (b, gsu_v) := alloc b (Eadd (Eadd (Emul R_sv R_u) (Emul R_s R_uv))
                                  (Eadd (Emul Z_sv Z_u) (Emul Z_s Z_uv))) in
  let (b, gsv_u) := alloc b (Eadd (Eadd (Emul R_su R_v) (Emul R_s R_uv))
                                  (Eadd (Emul Z_su Z_v) (Emul Z_s Z_uv))) in
  let (b, gsv_v) := alloc b (Eadd (Eadd (Emul R_sv R_v) (Emul R_s R_vv))
                                  (Eadd (Emul Z_sv Z_v) (Emul Z_s Z_vv))) in
  let (b, guu_v) := alloc b (zmul 2 (Eadd (Emul R_u R_uv) (Emul Z_u Z_uv))) in
  let (b, guv_u) := alloc b (Eadd (Eadd (Emul R_uu R_v) (Emul R_u R_uv))
                                  (Eadd (Emul Z_uu Z_v) (Emul Z_u Z_uv))) in
  let (b, guv_v) := alloc b (Eadd (Eadd (Emul R_uv R_v) (Emul R_u R_vv))
                                  (Eadd (Emul Z_uv Z_v) (Emul Z_u Z_vv))) in
  let (b, gvv_u) := alloc b (zmul 2 (Eadd (Eadd (Emul R_v R_uv) (Emul Z_v Z_uv))
                                          (Emul R R_u))) in
  let (b, bu_num) := alloc b (Esub iota L_v) in
  let (b, bv_num) := alloc b (Eadd e1 L_u) in
  let (b, Bu) := alloc b (Ediv (Emul vPhip bu_num) sqrtg) in
  let (b, Bv) := alloc b (Ediv (Emul vPhip bv_num) sqrtg) in
  let (b, g2) := alloc b (esq sqrtg) in
  let dB nums gd := Ediv (Emul vPhip (Esub (Emul nums sqrtg) gd)) g2 in
  let (b, Bu_u) := alloc b (dB (Eneg L_uv) (Emul bu_num g_u)) in
  let (b, Bv_u) := alloc b (dB L_uu (Emul bv_num g_u)) in
  let (b, Bu_v) := alloc b (dB (Eneg L_vv) (Emul bu_num g_v)) in
  let (b, Bv_v) := alloc b (dB L_uv (Emul bv_num g_v)) in
  let dcov gu gud gv gvd bud bvd :=
      Eadd (Eadd (Emul gud Bu) (Emul gu bud))
           (Eadd (Emul gvd Bv) (Emul gv bvd)) in
  let (b, B_u) := alloc b (Eadd (Emul guu Bu) (Emul guv Bv)) in
  let (b, B_v) := alloc b (Eadd (Emul guv Bu) (Emul gvv Bv)) in
  let (b, B_s_u) := alloc b (dcov gsu gsu_u gsv gsv_u Bu_u Bv_u) in
  let (b, B_s_v) := alloc b (dcov gsu gsu_v gsv gsv_v Bu_v Bv_v) in
  let (b, B_u_v) := alloc b (dcov guu guu_v guv guv_v Bu_v Bv_v) in
  let (b, B_v_u) := alloc b (dcov guv guv_u gvv gvv_u Bu_u Bv_u) in
  let (b, mu0Js) := alloc b (Esub B_v_u B_u_v) in
  let (b, B_s) := alloc b (Eadd (Emul gsu Bu) (Emul gsv Bv)) in
  (* lambda itself, which the field never reads and the Boozer angle does *)
  let (b, lam) :=
    alloc b (esum (map (fun kc => Emul (snd kc) (mk_sin (fst kc)))
                       (combine kers cL))) in
  (b, HalfQ Bu Bv B_u B_v B_s B_s_u B_s_v B_v_u B_u_v mu0Js sqrtg
        R R_u R_v Z_u Z_v guu lam L_u L_v
        R_s R_su R_sv R_uu R_uv R_vv
        Z_s Z_su Z_sv Z_uu Z_uv Z_vv
        L_uu L_uv L_vv
        tau tau_u tau_v g_u g_v guv gvv
        guu_v guv_u guv_v gvv_u
        bu_num bv_num g2 Bu_u Bv_u Bu_v Bv_v).

(* ---------------------------------------------------------------- *)
(* The quasisymmetry residual                                        *)

(** A field is quasisymmetric when its strength depends on the angles only
    through one combination M theta_B - N zeta_B of the Boozer angles. The
    coordinate-free form of that condition (Helander 2014; Rodriguez, Paul
    and Bhattacharjee 2020) is the vanishing of the triple product

      grad psi . (grad B x grad(B . grad B)),

    with B the field strength and B . grad B its variation along the field
    line. It needs no Boozer transform and no choice of helicity: it is a
    scalar of the field at a point, and it vanishes for quasisymmetry of
    every helicity at once.

    In flux coordinates the radial gradient kills the radial row of the
    determinant, so the triple product is the (u, v)-Jacobian of the two
    surface functions over the coordinate Jacobian,

      grad s . (grad B x grad W) = (d_u B d_v W - d_v B d_u W) / sqrt(g),

    with W = B . grad B. And since B = sqrt(B^2), the Jacobian of (B, W) is
    the Jacobian of (B^2, W2) over 4 B^2, with W2 = B . grad(B^2), so the
    square root never enters:

      T = (d_u B^2 d_v W2 - d_v B^2 d_u W2) / (4 B^2 sqrt(g)),
      W2 = B^u d_u B^2 + B^v d_v B^2.

    T is the quasisymmetry residual a certificate carries, written against
    grad s rather than grad psi, which differ by the constant dpsi/ds. It
    reads second angular derivatives of the field, hence third derivatives
    of the series, which the records above supply; the field's radial
    contravariant component is zero by the ansatz, which is why W2 has two
    terms.

    For an axisymmetric reconstruction every v-derivative in the Jacobian
    carries the integer factor n = 0, so T is exactly zero wherever its
    pieces are real: an axisymmetric field is quasisymmetric, which
    Identities.v proves from the series, and which the interval evaluator
    reproduces as an enclosure of exactly zero at any resolution. *)

(** The triple product from the four Jacobian ingredients and a denominator,
    as the difference of the two products it is made of.
    [Identities.qs_triple_zero] is stated on this combinator, so it holds
    whatever the four are: what the arguments mean is fixed by [qs_b] below,
    and what the theorem needs is only that the two carrying a toroidal
    derivative vanish. *)
Definition qs_triple_e (num_u num_v den_u den_v den : expr) : expr :=
  Esub (Ediv (Emul num_u den_v) den) (Ediv (Emul num_v den_u) den).

(** The two angular components of the residual: the surface current against
    the contravariant field, r_u = - mu0 sqrt(g) J^s B^v and
    r_v = mu0 sqrt(g) J^s B^u. [Identities.force_along_field] is stated on
    these combinators, so it holds whatever the arguments are; what they mean
    is fixed where [residual] and [full_point_b] allocate them. *)
Definition r_u_e (js bv : expr) : expr := Eneg (Emul js bv).
Definition r_v_e (js bu : expr) : expr := Emul js bu.

(* ---------------------------------------------------------------- *)
(* A surface quantity carried with its angular derivatives           *)

(** A scalar on the surface together with its first and second angular
    derivatives, so that a product rule composes two of them and the
    residual can be assembled from the reconstruction rather than by
    expanding every derivative by hand. The float reference of
    proto/continuum_ref.py is written against the same three rules, which is
    what lets the two be compared line for line.

    Every component is a slot reference once [q2_mul_b] has run, so the
    expression stays a shallow directed graph rather than a tree that
    doubles with each product. *)
Record q2 := Q2 {
  q2_0 : expr ; q2_u : expr ; q2_v : expr ;
  q2_uu : expr ; q2_uv : expr ; q2_vv : expr }.

(** The product rule to second order, with each of the six allocated. *)
Definition q2_mul_b (b : builder) (x y : q2) : builder * q2 :=
  let (b, w0) := alloc b (Emul (q2_0 x) (q2_0 y)) in
  let (b, wu) := alloc b (Eadd (Emul (q2_u x) (q2_0 y))
                               (Emul (q2_0 x) (q2_u y))) in
  let (b, wv) := alloc b (Eadd (Emul (q2_v x) (q2_0 y))
                               (Emul (q2_0 x) (q2_v y))) in
  let (b, wuu) :=
    alloc b (Eadd (Eadd (Emul (q2_uu x) (q2_0 y))
                        (zmul 2 (Emul (q2_u x) (q2_u y))))
                  (Emul (q2_0 x) (q2_uu y))) in
  let (b, wuv) :=
    alloc b (Eadd (Eadd (Emul (q2_uv x) (q2_0 y))
                        (Emul (q2_u x) (q2_v y)))
                  (Eadd (Emul (q2_v x) (q2_u y))
                        (Emul (q2_0 x) (q2_uv y)))) in
  let (b, wvv) :=
    alloc b (Eadd (Eadd (Emul (q2_vv x) (q2_0 y))
                        (zmul 2 (Emul (q2_v x) (q2_v y))))
                  (Emul (q2_0 x) (q2_vv y))) in
  (b, Q2 w0 wu wv wuu wuv wvv).

(** Termwise sum, and sum with one side scaled by an integer. Sums are
    linear and cost one node each, so they are not allocated. *)
Definition q2_add3 (z : Z) (x y w : q2) : q2 :=
  let f fx fy fw := Eadd (Eadd fx (zmul z fy)) fw in
  Q2 (f (q2_0 x) (q2_0 y) (q2_0 w))
     (f (q2_u x) (q2_u y) (q2_u w))
     (f (q2_v x) (q2_v y) (q2_v w))
     (f (q2_uu x) (q2_uu y) (q2_uu w))
     (f (q2_uv x) (q2_uv y) (q2_uv w))
     (f (q2_vv x) (q2_vv y) (q2_vv w)).

(** The residual at a half point, from the coefficients and kernels the
    point was built from and the slots it exposes. Everything below the
    third-order series is a product rule applied to what [half_point_b]
    already holds; nothing here is approximated. The three results are the
    triple product and the two products it is the difference of, so that a
    certificate carries the cancellation between them as a number. *)
Definition qs_b (b : builder) (lasym : bool) (kers : list mode_kernels)
    (hc : half_coefs) (q : halfq) : builder * (expr * expr * expr) :=
  let cR := hc_R hc in let cZ := hc_Z hc in let cL := hc_L hc in
  let cRa := hc_Ra hc in let cZa := hc_Za hc in let cLa := hc_La hc in
  let (b, r3) := partials3_b b
      (if lasym then padd3 (assemble3 kers cR true) (assemble3 kers cRa false)
       else assemble3 kers cR true) in
  let (b, z3) := partials3_b b
      (if lasym then padd3 (assemble3 kers cZ false) (assemble3 kers cZa true)
       else assemble3 kers cZ false) in
  let (b, l3) := lambda_partials3_b b
      (if lasym then ladd3 (lambda_terms3 kers cL false)
                           (lambda_terms3 kers cLa true)
       else lambda_terms3 kers cL false) in
  let R := q_R q in let R_s := q_Rs q in
  let R_u := q_Ru q in let R_v := q_Rv q in
  let R_su := q_Rsu q in let R_sv := q_Rsv q in
  let R_uu := q_Ruu q in let R_uv := q_Ruv q in let R_vv := q_Rvv q in
  let R_uuu := p3_uuu r3 in let R_uuv := p3_uuv r3 in
  let R_uvv := p3_uvv r3 in let R_vvv := p3_vvv r3 in
  let R_suu := p3_suu r3 in let R_suv := p3_suv r3 in let R_svv := p3_svv r3 in
  let Z_s := q_Zs q in let Z_u := q_Zu q in let Z_v := q_Zv q in
  let Z_su := q_Zsu q in let Z_sv := q_Zsv q in
  let Z_uu := q_Zuu q in let Z_uv := q_Zuv q in let Z_vv := q_Zvv q in
  let Z_uuu := p3_uuu z3 in let Z_uuv := p3_uuv z3 in
  let Z_uvv := p3_uvv z3 in let Z_vvv := p3_vvv z3 in
  let Z_suu := p3_suu z3 in let Z_suv := p3_suv z3 in let Z_svv := p3_svv z3 in
  let L_uu := q_Luu q in let L_uv := q_Luv q in let L_vv := q_Lvv q in
  let L_uuu := l3_uuu l3 in let L_uuv := l3_uuv l3 in
  let L_uvv := l3_uvv l3 in let L_vvv := l3_vvv l3 in
  let tau := q_tau q in let sqrtg := q_sqrtg q in
  let tau_u := q_tau_u q in let tau_v := q_tau_v q in
  let g_u := q_g_u q in let g_v := q_g_v q in
  let guu := q_guu q in let guv := q_guv q in let gvv := q_gvv q in
  let guu_v := q_guu_v q in let guv_u := q_guv_u q in
  let guv_v := q_guv_v q in let gvv_u := q_gvv_u q in
  let bu := q_bu_num q in let bv := q_bv_num q in
  (* the two first derivatives of the metric the field never needed *)
  let (b, guu_u) := alloc b (zmul 2 (Eadd (Emul R_u R_uu) (Emul Z_u Z_uu))) in
  let (b, gvv_v) := alloc b (zmul 2 (Eadd (Eadd (Emul R_v R_vv) (Emul Z_v Z_vv))
                                          (Emul R R_v))) in
  (* second derivatives of tau = R_u Z_s - R_s Z_u and of the Jacobian R tau *)
  let (b, tau_uu) :=
    alloc b (Esub (Eadd (Eadd (Emul R_uuu Z_s) (zmul 2 (Emul R_uu Z_su)))
                        (Emul R_u Z_suu))
                  (Eadd (Eadd (Emul R_suu Z_u) (zmul 2 (Emul R_su Z_uu)))
                        (Emul R_s Z_uuu))) in
  let (b, tau_uv) :=
    alloc b (Esub (Eadd (Eadd (Emul R_uuv Z_s) (Emul R_uu Z_sv))
                        (Eadd (Emul R_uv Z_su) (Emul R_u Z_suv)))
                  (Eadd (Eadd (Emul R_suv Z_u) (Emul R_su Z_uv))
                        (Eadd (Emul R_sv Z_uu) (Emul R_s Z_uuv)))) in
  let (b, tau_vv) :=
    alloc b (Esub (Eadd (Eadd (Emul R_uvv Z_s) (zmul 2 (Emul R_uv Z_sv)))
                        (Emul R_u Z_svv))
                  (Eadd (Eadd (Emul R_svv Z_u) (zmul 2 (Emul R_sv Z_uv)))
                        (Emul R_s Z_uvv))) in
  let (b, g_uu) := alloc b (Eadd (Eadd (Emul R_uu tau) (zmul 2 (Emul R_u tau_u)))
                                 (Emul R tau_uu)) in
  let (b, g_uv) := alloc b (Eadd (Eadd (Emul R_uv tau) (Emul R_u tau_v))
                                 (Eadd (Emul R_v tau_u) (Emul R tau_uv))) in
  let (b, g_vv) := alloc b (Eadd (Eadd (Emul R_vv tau) (zmul 2 (Emul R_v tau_v)))
                                 (Emul R tau_vv)) in
  (* second derivatives of the metric *)
  let (b, guu_uu) :=
    alloc b (zmul 2 (Eadd (Eadd (esq R_uu) (Emul R_u R_uuu))
                          (Eadd (esq Z_uu) (Emul Z_u Z_uuu)))) in
  let (b, guu_uv) :=
    alloc b (zmul 2 (Eadd (Eadd (Emul R_uv R_uu) (Emul R_u R_uuv))
                          (Eadd (Emul Z_uv Z_uu) (Emul Z_u Z_uuv)))) in
  let (b, guu_vv) :=
    alloc b (zmul 2 (Eadd (Eadd (esq R_uv) (Emul R_u R_uvv))
                          (Eadd (esq Z_uv) (Emul Z_u Z_uvv)))) in
  let (b, guv_uu) :=
    alloc b (Eadd (Eadd (Eadd (Emul R_uuu R_v) (zmul 2 (Emul R_uu R_uv)))
                        (Emul R_u R_uuv))
                  (Eadd (Eadd (Emul Z_uuu Z_v) (zmul 2 (Emul Z_uu Z_uv)))
                        (Emul Z_u Z_uuv))) in
  let (b, guv_uv) :=
    alloc b (Eadd (Eadd (Eadd (Emul R_uuv R_v) (Emul R_uu R_vv))
                        (Eadd (esq R_uv) (Emul R_u R_uvv)))
                  (Eadd (Eadd (Emul Z_uuv Z_v) (Emul Z_uu Z_vv))
                        (Eadd (esq Z_uv) (Emul Z_u Z_uvv)))) in
  let (b, guv_vv) :=
    alloc b (Eadd (Eadd (Eadd (Emul R_uvv R_v) (zmul 2 (Emul R_uv R_vv)))
                        (Emul R_u R_vvv))
                  (Eadd (Eadd (Emul Z_uvv Z_v) (zmul 2 (Emul Z_uv Z_vv)))
                        (Emul Z_u Z_vvv))) in
  let (b, gvv_uu) :=
    alloc b (zmul 2 (Eadd (Eadd (Eadd (esq R_uv) (Emul R_v R_uuv))
                                (Eadd (esq Z_uv) (Emul Z_v Z_uuv)))
                          (Eadd (esq R_u) (Emul R R_uu)))) in
  let (b, gvv_uv) :=
    alloc b (zmul 2 (Eadd (Eadd (Eadd (Emul R_vv R_uv) (Emul R_v R_uvv))
                                (Eadd (Emul Z_vv Z_uv) (Emul Z_v Z_uvv)))
                          (Eadd (Emul R_v R_u) (Emul R R_uv)))) in
  let (b, gvv_vv) :=
    alloc b (zmul 2 (Eadd (Eadd (Eadd (esq R_vv) (Emul R_v R_vvv))
                                (Eadd (esq Z_vv) (Emul Z_v Z_vvv)))
                          (Eadd (esq R_v) (Emul R R_vv)))) in
  (* The metric and the two field numerators, each with its angular
     derivatives, so that the product rule assembles what follows. The
     stream function enters only through these: bu = iota - lambda_v and
     bv = 1 + lambda_u, whose derivatives are the lambda series with one
     more angle each. *)
  let Guu := Q2 guu guu_u guu_v guu_uu guu_uv guu_vv in
  let Guv := Q2 guv guv_u guv_v guv_uu guv_uv guv_vv in
  let Gvv := Q2 gvv gvv_u gvv_v gvv_uu gvv_uv gvv_vv in
  let Nu := Q2 bu (Eneg L_uv) (Eneg L_vv)
               (Eneg L_uuv) (Eneg L_uvv) (Eneg L_vvv) in
  let Nv := Q2 bv L_uu L_uv L_uuu L_uuv L_uvv in
  (* Everything below is scaled by the Jacobian so that no reciprocal enters
     the chain. The covariant components and the square field each carry one
     factor of sqrt(g), and

       M = J^2 B^2 = guu U^2 + 2 guv U V + gvv V^2 = phip^2 S,
       U = J B^u = phip bu,   V = J B^v = phip bv,

     with S polynomial in the series. Writing the derivatives of B^2 and of
     W2 = B . grad(B^2) against powers of J rather than dividing by it is
     what keeps an interval evaluation of the whole residual bounded: a form
     that carries 1/sqrt(g) and its second derivatives encloses to the order
     of that reciprocal however narrow the cell, which is the same reason
     the radial Hermite is written against its slope defects. *)
  let (b, Puu) := q2_mul_b b Nu Nu in
  let (b, Puv) := q2_mul_b b Nu Nv in
  let (b, Pvv) := q2_mul_b b Nv Nv in
  let (b, Suu) := q2_mul_b b Guu Puu in
  let (b, Suv) := q2_mul_b b Guv Puv in
  let (b, Svv) := q2_mul_b b Gvv Pvv in
  let S := q2_add3 2 Suu Suv Svv in
  let (b, P2) := alloc b (esq vPhip) in
  let (b, M) := alloc b (Emul P2 (q2_0 S)) in
  let (b, M_u) := alloc b (Emul P2 (q2_u S)) in
  let (b, M_v) := alloc b (Emul P2 (q2_v S)) in
  let (b, M_uu) := alloc b (Emul P2 (q2_uu S)) in
  let (b, M_uv) := alloc b (Emul P2 (q2_uv S)) in
  let (b, M_vv) := alloc b (Emul P2 (q2_vv S)) in
  (* B^2 = M / J^2, so d_i B^2 = A_i / J^3 with A_i = M_i J - 2 M J_i, and
     the second derivatives of A follow by the same rule *)
  let (b, A_u) := alloc b (Esub (Emul M_u sqrtg) (zmul 2 (Emul M g_u))) in
  let (b, A_v) := alloc b (Esub (Emul M_v sqrtg) (zmul 2 (Emul M g_v))) in
  let (b, A_uu) :=
    alloc b (Esub (Esub (Emul M_uu sqrtg) (Emul M_u g_u))
                  (zmul 2 (Emul M g_uu))) in
  let (b, A_uv) :=
    alloc b (Esub (Eadd (Emul M_uv sqrtg) (Emul M_u g_v))
                  (zmul 2 (Eadd (Emul M_v g_u) (Emul M g_uv)))) in
  let (b, A_vu) :=
    alloc b (Esub (Eadd (Emul M_uv sqrtg) (Emul M_v g_u))
                  (zmul 2 (Eadd (Emul M_u g_v) (Emul M g_uv)))) in
  let (b, A_vv) :=
    alloc b (Esub (Esub (Emul M_vv sqrtg) (Emul M_v g_v))
                  (zmul 2 (Emul M g_vv))) in
  (* W2 = B . grad(B^2) = C / J^4 with C = U A_u + V A_v *)
  let (b, U) := alloc b (Emul vPhip bu) in
  let (b, V) := alloc b (Emul vPhip bv) in
  let (b, U_u) := alloc b (Emul vPhip (Eneg L_uv)) in
  let (b, U_v) := alloc b (Emul vPhip (Eneg L_vv)) in
  let (b, V_u) := alloc b (Emul vPhip L_uu) in
  let (b, V_v) := alloc b (Emul vPhip L_uv) in
  let (b, C) := alloc b (Eadd (Emul U A_u) (Emul V A_v)) in
  let (b, C_u) := alloc b (Eadd (Eadd (Emul U_u A_u) (Emul U A_uu))
                                (Eadd (Emul V_u A_v) (Emul V A_vu))) in
  let (b, C_v) := alloc b (Eadd (Eadd (Emul U_v A_u) (Emul U A_uv))
                                (Eadd (Emul V_v A_v) (Emul V A_vv))) in
  (* d_i W2 = D_i / J^5 with D_i = C_i J - 4 C J_i *)
  let (b, D_u) := alloc b (Esub (Emul C_u sqrtg) (zmul 4 (Emul C g_u))) in
  let (b, D_v) := alloc b (Esub (Emul C_v sqrtg) (zmul 4 (Emul C g_v))) in
  (* The Jacobian of B^2 and W2 over the angles is
     (A_u D_v - A_v D_u) / J^8, and the triple product divides it by
     4 B^2 J = 4 M / J, which leaves 4 M J^7 beneath the difference. Both
     products are carried beside it, so a certificate says how nearly the
     two are the same number, which is what quasisymmetry asks of them. *)
  let (b, J2) := alloc b (esq sqrtg) in
  let (b, J3) := alloc b (Emul J2 sqrtg) in
  let (b, J6) := alloc b (esq J3) in
  let (b, J7) := alloc b (Emul J6 sqrtg) in
  let (b, den) := alloc b (Emul e4 (Emul M J7)) in
  let (b, t1) := alloc b (Ediv (Emul A_u D_v) den) in
  let (b, t2) := alloc b (Ediv (Emul A_v D_u) den) in
  let (b, qs) := alloc b (qs_triple_e A_u A_v D_u D_v den) in
  (b, (qs, t1, t2)).

(* ---------------------------------------------------------------- *)
(* Quasisymmetry as a flux function: the two-term form               *)

(** The triple product above names no helicity and needs no data, and it is
    third order in the angles, which a covering of a three-dimensional
    surface cannot afford: the enclosure of a third derivative over a box
    exceeds the quantity by orders of magnitude until the cells are far
    narrower than a surface integrand needs.

    There is a lower-order statement of the same property. Because
    B x grad(psi) is tangent to the surface and perpendicular to grad(psi),
    the radial part of grad B drops out of the numerator, and with
    (B x grad s) . grad u = B_v / J and (B x grad s) . grad v = - B_u / J,

      B x grad(s) . grad B = (B_v d_u B - B_u d_v B) / J,
      B . grad B           = B^u d_u B + B^v d_v B,

    and the field is quasisymmetric exactly when the ratio of the two is a
    flux function (Helander 2014). The factor 1/(2B) relating d_i B to
    d_i B^2 is common to both, so no square root enters and only first
    angular derivatives of the square field are read, which is the order the
    force residual already carries.

    Scaled by the Jacobian, with L_u = J B_u = guu U + guv V and
    L_v = J B_v = guv U + gvv V and the A and C of [qs_b], the ratio taken
    against grad s is F = (L_v A_u - L_u A_v) / (J C), so the defect of the
    claim that F is the flux function F0 the certificate carries is

      Q = (L_v A_u - L_u A_v) - F0 J C,

    a polynomial with no division anywhere. The two products are returned
    beside it, so a verdict says how nearly they are the same number.

    No helicity is named here either. A surface whose F is constant is
    quasisymmetric, and which helicity it has is read off the value of F
    afterwards rather than assumed before. What the certificate adds over
    the triple product is one datum, in the way a Boozer stream function is
    carried as data and its defect bounded. *)
Definition qs2_b (b : builder) (q : halfq) (F0 : expr)
    : builder * (expr * expr * expr) :=
  let R := q_R q in let R_u := q_Ru q in let R_v := q_Rv q in
  let R_uu := q_Ruu q in let R_uv := q_Ruv q in let R_vv := q_Rvv q in
  let Z_u := q_Zu q in let Z_v := q_Zv q in
  let Z_uu := q_Zuu q in let Z_uv := q_Zuv q in let Z_vv := q_Zvv q in
  let L_uu := q_Luu q in let L_uv := q_Luv q in let L_vv := q_Lvv q in
  let J := q_sqrtg q in let J_u := q_g_u q in let J_v := q_g_v q in
  let guu := q_guu q in let guv := q_guv q in let gvv := q_gvv q in
  let guu_v := q_guu_v q in let guv_u := q_guv_u q in
  let guv_v := q_guv_v q in let gvv_u := q_gvv_u q in
  let bu := q_bu_num q in let bv := q_bv_num q in
  (* the two first derivatives of the metric the field never needed *)
  let (b, guu_u) := alloc b (zmul 2 (Eadd (Emul R_u R_uu) (Emul Z_u Z_uu))) in
  let (b, gvv_v) := alloc b (zmul 2 (Eadd (Eadd (Emul R_v R_vv) (Emul Z_v Z_vv))
                                          (Emul R R_v))) in
  (* the Jacobian-weighted contravariant components and their derivatives *)
  let (b, U) := alloc b (Emul vPhip bu) in
  let (b, V) := alloc b (Emul vPhip bv) in
  let (b, U_u) := alloc b (Emul vPhip (Eneg L_uv)) in
  let (b, U_v) := alloc b (Emul vPhip (Eneg L_vv)) in
  let (b, V_u) := alloc b (Emul vPhip L_uu) in
  let (b, V_v) := alloc b (Emul vPhip L_uv) in
  (* the Jacobian-weighted covariant components L_i = J B_i *)
  let (b, Lu) := alloc b (Eadd (Emul guu U) (Emul guv V)) in
  let (b, Lv) := alloc b (Eadd (Emul guv U) (Emul gvv V)) in
  let (b, Lu_u) := alloc b (Eadd (Eadd (Emul guu_u U) (Emul guu U_u))
                                 (Eadd (Emul guv_u V) (Emul guv V_u))) in
  let (b, Lu_v) := alloc b (Eadd (Eadd (Emul guu_v U) (Emul guu U_v))
                                 (Eadd (Emul guv_v V) (Emul guv V_v))) in
  let (b, Lv_u) := alloc b (Eadd (Eadd (Emul guv_u U) (Emul guv U_u))
                                 (Eadd (Emul gvv_u V) (Emul gvv V_u))) in
  let (b, Lv_v) := alloc b (Eadd (Eadd (Emul guv_v U) (Emul guv U_v))
                                 (Eadd (Emul gvv_v V) (Emul gvv V_v))) in
  (* M = J^2 B^2 = U L_u + V L_v, and its first derivatives *)
  let (b, M) := alloc b (Eadd (Emul U Lu) (Emul V Lv)) in
  let (b, M_u) := alloc b (Eadd (Eadd (Emul U_u Lu) (Emul U Lu_u))
                                (Eadd (Emul V_u Lv) (Emul V Lv_u))) in
  let (b, M_v) := alloc b (Eadd (Eadd (Emul U_v Lu) (Emul U Lu_v))
                                (Eadd (Emul V_v Lv) (Emul V Lv_v))) in
  (* d_i B^2 = A_i / J^3, and B . grad(B^2) = C / J^4 *)
  let (b, A_u) := alloc b (Esub (Emul M_u J) (zmul 2 (Emul M J_u))) in
  let (b, A_v) := alloc b (Esub (Emul M_v J) (zmul 2 (Emul M J_v))) in
  let (b, C) := alloc b (Eadd (Emul U A_u) (Emul V A_v)) in
  (* the two terms of the defect, and the defect *)
  let (b, t1) := alloc b (Esub (Emul Lv A_u) (Emul Lu A_v)) in
  let (b, t2) := alloc b (Emul F0 (Emul J C)) in
  let (b, qq) := alloc b (Esub t1 t2) in
  (b, (qq, t1, t2)).

(* ---------------------------------------------------------------- *)
(* Geometry at the node, and the Mercier integrands                  *)

(** R and its angular derivatives at the node itself, from row 1 of the
    coefficient blocks with no half-grid rule. The Mercier terms of
    `mercier.f90` are written against the full-grid geometry, not against a
    half-point average, so they are built here directly. Under lasym the
    antisymmetric halves are added first, R gaining a sine series and Z a
    cosine one, over the same modes; the symmetric path keeps exactly the
    expressions it had. *)
(** The node-row coefficients the Mercier geometry reads, allocated before the
    kernels for the same reason the half-point coefficients are. *)
Record node_coefs := NCoefs {
  ncf_R : list expr ; ncf_Z : list expr ;
  ncf_Ra : list expr ; ncf_Za : list expr }.

Definition node_coefs_b (b : builder) (lasym : bool)
    (modes : list (Z * Z)) (K : nat) : builder * node_coefs :=
  let (b, cR) := lambdacoefs_b b (base_R K) K 1 modes 0 in
  let (b, cZ) := lambdacoefs_b b (base_Z K) K 1 modes 0 in
  let (b, cRa) := if lasym then lambdacoefs_b b (base_Ra K) K 1 modes 0
                  else (b, @nil expr) in
  let (b, cZa) := if lasym then lambdacoefs_b b (base_Za K) K 1 modes 0
                  else (b, @nil expr) in
  (b, NCoefs cR cZ cRa cZa).

Definition node_geom_b (b : builder) (lasym : bool) (kers : list mode_kernels)
    (nc : node_coefs)
    : builder * (expr * expr * expr * expr * expr) :=
  let cR := ncf_R nc in let cZ := ncf_Z nc in
  let cRa := ncf_Ra nc in let cZa := ncf_Za nc in
  let pR := combine kers cR in
  let pZ := combine kers cZ in
  let pRa := combine kers cRa in
  let pZa := combine kers cZa in
  let sum l f := esum (map f l) in
  let both x y := if lasym then Eadd x y else x in
  let (b, r) :=
    alloc b (both (sum pR (fun kc => Emul (snd kc) (mk_cos (fst kc))))
                  (sum pRa (fun kc => Emul (snd kc) (mk_sin (fst kc))))) in
  let (b, ru) :=
    alloc b (both (sum pR (fun kc => zmul (Z.opp (mk_m (fst kc)))
                                          (Emul (snd kc) (mk_sin (fst kc)))))
                  (sum pRa (fun kc => zmul (mk_m (fst kc))
                                           (Emul (snd kc) (mk_cos (fst kc)))))) in
  let (b, rv) :=
    alloc b (both (sum pR (fun kc => zmul (mk_n (fst kc))
                                          (Emul (snd kc) (mk_sin (fst kc)))))
                  (sum pRa (fun kc => zmul (Z.opp (mk_n (fst kc)))
                                           (Emul (snd kc) (mk_cos (fst kc)))))) in
  let (b, zu) :=
    alloc b (both (sum pZ (fun kc => zmul (mk_m (fst kc))
                                          (Emul (snd kc) (mk_cos (fst kc)))))
                  (sum pZa (fun kc => zmul (Z.opp (mk_m (fst kc)))
                                           (Emul (snd kc) (mk_sin (fst kc)))))) in
  let (b, zv) :=
    alloc b (both (sum pZ (fun kc => zmul (Z.opp (mk_n (fst kc)))
                                          (Emul (snd kc) (mk_cos (fst kc)))))
                  (sum pZa (fun kc => zmul (mk_n (fst kc))
                                           (Emul (snd kc) (mk_sin (fst kc)))))) in
  (b, (r, ru, rv, zu, zv)).

(** The four angular integrands whose integrals over the angular torus are
    the Mercier terms of `mercier.f90`, in its notation and its
    normalization:

      gf   = |sqrt(g)| at the node / (2 pi phip)      its gsqrt_full
      gpp  = gf^2 / (g_uu R^2 + (R_u Z_v - R_v Z_u)^2)
      tpp  integrand  gf / B^2
      tbb  integrand  B^2 gf gpp
      tjb  integrand  (mu0 J.B) gpp gf
      tjj  integrand  (mu0 J.B)^2 gpp gf / B^2

    VMEC divides the Jacobian by phip_real = 2 pi phip signgs and averages
    with weights that sum to one, then multiplies by 4 pi^2; that product is
    the integral over u and v of the same integrand, so tpp through tjj are
    the integrals of these four. The sign is carried without a signgs input:
    signgs is sqrt(g)/|sqrt(g)|, so sqrt(g)/(2 pi phip signgs) is
    |sqrt(g)|/(2 pi phip), and the square root of a square supplies the
    modulus.

    J.B is taken at the node from the same centred differences the residual
    uses, so mu0 sqrt(g) (J.B) is

      (d_v B_s - d_s B_v) B_u + (d_s B_u - d_u B_s) B_v
        + (d_u B_v - d_v B_u) B_s,

    and dividing by sqrt(g) alone leaves mu0 J.B, which is VMEC's bdotj.

    The geometry is the full-grid one of [node_geom_b], not a half-point
    average, which is what those terms are written against. *)
Record mercq := MercQ {
  m_tpp : expr ; m_tbb : expr ; m_tjb : expr ; m_tjj : expr ;
  m_gf : expr ; m_b2 : expr }.

Definition merc_b (b : builder) (lasym : bool) (kers : list mode_kernels)
    (nc : node_coefs) (qm qp : halfq)
    (dBsv dBvs dBus dBsu half : expr) : builder * mercq :=
  let avg x y := Emul half (Eadd x y) in
  let (b, geo) := node_geom_b b lasym kers nc in
  let rr := fst (fst (fst (fst geo))) in
  let ru := snd (fst (fst (fst geo))) in
  let rv := snd (fst (fst geo)) in
  let zu := snd (fst geo) in
  let zv := snd geo in
  let (b, sgn) := alloc b (avg (q_sqrtg qm) (q_sqrtg qp)) in
  let (b, gf) :=
    alloc b (Ediv (Esqrt (esq sgn)) (Emul (Emul e2 Epi) vPhip)) in
  let (b, b2n) := alloc b (avg (q_B2 qm) (q_B2 qp)) in
  let (b, cross) := alloc b (Esub (Emul ru zv) (Emul rv zu)) in
  let (b, gppd) :=
    alloc b (Eadd (Emul (Eadd (esq ru) (esq zu)) (esq rr)) (esq cross)) in
  let (b, gpp) := alloc b (Ediv (esq gf) gppd) in
  let (b, B_u_n) := alloc b (avg (q_B_u qm) (q_B_u qp)) in
  let (b, B_v_n) := alloc b (avg (q_B_v qm) (q_B_v qp)) in
  let (b, B_s_n) := alloc b (avg (q_B_s qm) (q_B_s qp)) in
  let (b, Js_n) := alloc b (avg (q_mu0Js qm) (q_mu0Js qp)) in
  let (b, jb) :=
    alloc b (Ediv (Eadd (Eadd (Emul (Esub dBsv dBvs) B_u_n)
                              (Emul (Esub dBus dBsu) B_v_n))
                        (Emul Js_n B_s_n))
                  sgn) in
  let (b, i_tpp) := alloc b (Ediv gf b2n) in
  let (b, i_tbb) := alloc b (Emul b2n (Emul gf gpp)) in
  let (b, i_tjb) := alloc b (Emul jb (Emul gpp gf)) in
  let (b, i_tjj) := alloc b (Ediv (Emul (esq jb) (Emul gpp gf)) b2n) in
  (b, MercQ i_tpp i_tbb i_tjb i_tjj gf b2n).

(* ---------------------------------------------------------------- *)
(* The residual                                                      *)

(** The bindings of a point in evaluation order and the three covariant
    components of the mu0-scaled force residual, each a slot reference. *)
Record residual3 := Residual3 {
  r_binds : list binding ; r_s : expr ; r_u : expr ; r_v : expr }.

(* ---------------------------------------------------------------- *)
(* The reconstruction at a free radius                               *)

(** VMEC's parity-aware half-grid rule is linear interpolation in s: of the
    coefficient itself when m is even, and of c/sqrt(s) when m is odd. At
    the midpoint of two nodes the first gives (c_a + c_b)/2 and the second
    sqrt(s_h) (c_a/sqrt(s_a) + c_b/sqrt(s_b))/2, which is the rule, and the
    derivatives of those two interpolants are the difference quotients the
    rule uses for c'. Reading the same interpolant at a free s therefore
    carries the reconstruction off the half grid without choosing anything:
    at s = s_h it is VMEC's own rule, coefficient for coefficient.

    The radius is slot 0, the same slot the pressure reads, so a cell of
    Cell.v ranging over slots 0 and 1 covers a rectangle of radius and
    poloidal angle. The residual built here is the continuum one: every
    radial derivative is an exact derivative of the interpolant rather than
    a difference quotient across the node, so nothing in it is discrete.

    Which pair of full-grid rows brackets the radius is the caller's
    choice. The low piece takes rows j-1 and j and the high piece rows j
    and j+1, while lambda and iota take the two half-grid rows either way,
    so the low piece is valid on [s_{j-1/2}, s_j] and the high piece on
    [s_j, s_{j+1/2}]. Consecutive nodes tile the radius with these pieces,
    and the environment layout is the one every other certificate uses. *)

(** A coefficient at a free radius: value and its two radial derivatives. *)
Record coef3 := Coef3 { t_val : expr ; t_ds : expr ; t_dss : expr }.

(** Scalars of the radius s between the knots s_a and s_b, shared by every
    mode. *)
Record rad_scalars := RScal {
  rs_w : expr ;           (* (s - s_a) / (s_b - s_a) *)
  rs_inv_h : expr ;       (* 1 / (s_b - s_a) *)
  rs_sqrt : expr ;        (* sqrt(s) *)
  rs_inv_sqrt : expr ;    (* 1 / sqrt(s) *)
  rs_inv_sqrt_a : expr ;  (* 1 / sqrt(s_a) *)
  rs_inv_sqrt_b : expr ;  (* 1 / sqrt(s_b) *)
  rs_inv_2s : expr ;      (* 1 / (2 s) *)
  rs_inv_4s2 : expr }.    (* 1 / (4 s^2) *)

Definition rad_scalars_b (b : builder) (s_a s_b s : expr)
    : builder * rad_scalars :=
  let (b, inv_h) := alloc b (Ediv e1 (Esub s_b s_a)) in
  let (b, w) := alloc b (Emul (Esub s s_a) inv_h) in
  let (b, sq) := alloc b (Esqrt s) in
  let (b, isq) := alloc b (Ediv e1 sq) in
  let (b, isa) := alloc b (Ediv e1 (Esqrt s_a)) in
  let (b, isb) := alloc b (Ediv e1 (Esqrt s_b)) in
  let (b, i2s) := alloc b (Ediv e1 (Emul e2 s)) in
  let (b, i4s2) := alloc b (Ediv e1 (Emul e4 (esq s))) in
  (b, RScal w inv_h sq isq isa isb i2s i4s2).

(** c(s), c'(s) and c''(s) of one mode of poloidal number m from its knot
    values ya (inner) and yb (outer). An even mode interpolates linearly in
    s, so its second derivative is exactly zero; an odd one interpolates
    q = c/sqrt(s) and carries the derivatives of sqrt(s) q. *)
Definition radcoef_b (b : builder) (rs : rad_scalars) (m : Z)
    (ya yb : expr) : builder * coef3 :=
  if Z.even m then
    let (b, d) := alloc b (Esub yb ya) in
    let (b, c) := alloc b (Eadd ya (Emul (rs_w rs) d)) in
    let (b, cs) := alloc b (Emul d (rs_inv_h rs)) in
    (b, Coef3 c cs e0)
  else
    let (b, qa) := alloc b (Emul ya (rs_inv_sqrt_a rs)) in
    let (b, qb) := alloc b (Emul yb (rs_inv_sqrt_b rs)) in
    let (b, dq) := alloc b (Esub qb qa) in
    let (b, q) := alloc b (Eadd qa (Emul (rs_w rs) dq)) in
    let (b, qs) := alloc b (Emul dq (rs_inv_h rs)) in
    let (b, c) := alloc b (Emul (rs_sqrt rs) q) in
    let (b, cs) := alloc b (Eadd (Emul (rs_sqrt rs) qs)
                                 (Emul c (rs_inv_2s rs))) in
    let (b, css) := alloc b (Esub (Emul (rs_inv_sqrt rs) qs)
                                  (Emul c (rs_inv_4s2 rs))) in
    (b, Coef3 c cs css).

(** The coefficients of modes 0..K-1 of a node block between rows ra and
    rb. *)
Fixpoint radcoefs_b (b : builder) (rs : rad_scalars) (base K ra rb : nat)
    (modes : list (Z * Z)) (k : nat) : builder * list coef3 :=
  match modes with
  | [] => (b, [])
  | mn :: tl =>
      let (b, c) := radcoef_b b rs (fst mn)
                      (slot_node base K ra k) (slot_node base K rb k) in
      let (b, rest) := radcoefs_b b rs base K ra rb tl (S k) in
      (b, c :: rest)
  end.

(** VMEC defines both a value and a radial derivative for every coefficient
    at every half point. The cubic Hermite through those two pieces of data
    at the two half points bracketing a node reproduces them exactly at both
    ends, is continuously differentiable across half points, and unlike the
    linear rule has a second radial derivative that approximates rather than
    vanishes. The residual reads second radial derivatives through tau_s, so
    that difference is what decides whether a volume bound measures the
    discretization or an artefact of the interpolation.

    The basis is written so that the cancellations survive an interval
    evaluation. In the textbook basis the second derivative is
    (k00 ya + k01 yb) / H^2 with k01 = -k00, and an interval evaluation adds
    the two terms independently: the enclosure comes out of order |y| / H^2
    however narrow the cell, which is no bound at all. Against the secant
    S = (yb - ya)/H and the slope defects a = da - S, b = db - S, the
    identities h01 + h10 + h11 = t, g01 + g10 + g11 = 1 and
    k01 + k10 + k11 = 0 collapse the same polynomial to

      c   = ya + t (yb - ya) + H (h10 a + h11 b)
      c'  = S + g10 a + g11 b
      c'' = ((6t - 4) a + (6t - 2) b) / H,

    the linear interpolant plus corrections that are small term by term, so
    the enclosure is of the size of the quantity it encloses. *)
Record herm_scalars := HermS {
  hm_H : expr ; hm_invH : expr ; hm_t : expr ;
  hm_h10 : expr ; hm_h11 : expr ;
  hm_g10 : expr ; hm_g11 : expr ;
  hm_m0 : expr ; hm_m1 : expr }.

Definition herm_scalars_b (b : builder) (s_a s_b s : expr)
    : builder * herm_scalars :=
  let (b, H) := alloc b (Esub s_b s_a) in
  let (b, invH) := alloc b (Ediv e1 H) in
  let (b, t) := alloc b (Emul (Esub s s_a) invH) in
  let (b, t2) := alloc b (esq t) in
  let (b, t3) := alloc b (Emul t t2) in
  let (b, h10) := alloc b (Eadd (Esub t3 (zmul 2 t2)) t) in
  let (b, h11) := alloc b (Esub t3 t2) in
  let (b, g10) := alloc b (Eadd (Esub (zmul 3 t2) (zmul 4 t)) e1) in
  let (b, g11) := alloc b (Esub (zmul 3 t2) (zmul 2 t)) in
  let (b, m0) := alloc b (Esub (zmul 6 t) (EfromZ 4)) in
  let (b, m1) := alloc b (Esub (zmul 6 t) (EfromZ 2)) in
  (b, HermS H invH t h10 h11 g10 g11 m0 m1).

(** One mode's coefficient at a free radius, from its value and radial
    derivative at the two half points. *)
Definition hermcoef_b (b : builder) (hm : herm_scalars) (ca cb : coef2)
    : builder * coef3 :=
  let ya := c_val ca in let da := c_ds ca in
  let yb := c_val cb in let db := c_ds cb in
  let (b, dy) := alloc b (Esub yb ya) in
  let (b, sec) := alloc b (Emul dy (hm_invH hm)) in
  let (b, al) := alloc b (Esub da sec) in
  let (b, be) := alloc b (Esub db sec) in
  let (b, c) :=
    alloc b (Eadd (Eadd ya (Emul (hm_t hm) dy))
                  (Emul (hm_H hm)
                        (Eadd (Emul (hm_h10 hm) al) (Emul (hm_h11 hm) be)))) in
  let (b, cs) :=
    alloc b (Eadd sec (Eadd (Emul (hm_g10 hm) al) (Emul (hm_g11 hm) be))) in
  let (b, css) :=
    alloc b (Emul (Eadd (Emul (hm_m0 hm) al) (Emul (hm_m1 hm) be))
                  (hm_invH hm)) in
  (b, Coef3 c cs css).

(** The Hermite of every mode, from the two half-point coefficient lists. *)
Fixpoint hermcoefs_b (b : builder) (hm : herm_scalars)
    (cas cbs : list coef2) : builder * list coef3 :=
  match cas, cbs with
  | ca :: ta, cb :: tb =>
      let (b, c) := hermcoef_b b hm ca cb in
      let (b, rest) := hermcoefs_b b hm ta tb in
      (b, c :: rest)
  | _, _ => (b, [])
  end.

(** A Fourier series at a free radius, with the derivatives the continuum
    residual needs: two in the radius, two in each angle, and the mixed
    radial-angular pair. *)
Record fpartials := FPartials {
  fp_0 : expr ; fp_s : expr ; fp_ss : expr ;
  fp_u : expr ; fp_v : expr ;
  fp_su : expr ; fp_sv : expr ;
  fp_uu : expr ; fp_uv : expr ; fp_vv : expr }.

(** Sum a cos series (even = true) or a sin series, with the same sign
    convention as [assemble]. *)
Definition fassemble (kers : list mode_kernels) (coefs : list coef3)
    (even : bool) : fpartials :=
  let pair := combine kers coefs in
  let sum f := esum (map f pair) in
  let k0 kc := if even then mk_cos (fst kc) else mk_sin (fst kc) in
  let k1 kc := if even then mk_sin (fst kc) else mk_cos (fst kc) in
  let su kc := if even then Z.opp (mk_m (fst kc)) else mk_m (fst kc) in
  let sv kc := if even then mk_n (fst kc) else Z.opp (mk_n (fst kc)) in
  FPartials
    (sum (fun kc => Emul (t_val (snd kc)) (k0 kc)))
    (sum (fun kc => Emul (t_ds  (snd kc)) (k0 kc)))
    (sum (fun kc => Emul (t_dss (snd kc)) (k0 kc)))
    (sum (fun kc => zmul (su kc) (Emul (t_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (t_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (su kc) (Emul (t_ds (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (t_ds (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (Z.opp (mk_m (fst kc) * mk_m (fst kc)))
                         (Emul (t_val (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (mk_m (fst kc) * mk_n (fst kc))
                         (Emul (t_val (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (Z.opp (mk_n (fst kc) * mk_n (fst kc)))
                         (Emul (t_val (snd kc)) (k0 kc)))).

(** Sum two series termwise, as [padd] does. *)
Definition fadd (p q : fpartials) : fpartials :=
  FPartials (Eadd (fp_0 p) (fp_0 q)) (Eadd (fp_s p) (fp_s q))
            (Eadd (fp_ss p) (fp_ss q))
            (Eadd (fp_u p) (fp_u q)) (Eadd (fp_v p) (fp_v q))
            (Eadd (fp_su p) (fp_su q)) (Eadd (fp_sv p) (fp_sv q))
            (Eadd (fp_uu p) (fp_uu q)) (Eadd (fp_uv p) (fp_uv q))
            (Eadd (fp_vv p) (fp_vv q)).

(** Allocate each of the ten sums, so that it is evaluated once. *)
Definition fpartials_b (b : builder) (p : fpartials) : builder * fpartials :=
  let (b, a0)  := alloc b (fp_0 p) in
  let (b, as_) := alloc b (fp_s p) in
  let (b, ass) := alloc b (fp_ss p) in
  let (b, au)  := alloc b (fp_u p) in
  let (b, av)  := alloc b (fp_v p) in
  let (b, asu) := alloc b (fp_su p) in
  let (b, asv) := alloc b (fp_sv p) in
  let (b, auu) := alloc b (fp_uu p) in
  let (b, auv) := alloc b (fp_uv p) in
  let (b, avv) := alloc b (fp_vv p) in
  (b, FPartials a0 as_ ass au av asu asv auu auv avv).

(** The stream function at a free radius. Its value never enters the field,
    only these derivatives. *)
Record flpartials := FLPartials {
  flp_u : expr ; flp_v : expr ;
  flp_su : expr ; flp_sv : expr ;
  flp_uu : expr ; flp_uv : expr ; flp_vv : expr }.

Definition flambda_terms (kers : list mode_kernels) (coefs : list coef3)
    (even : bool) : flpartials :=
  let pair := combine kers coefs in
  let sum f := esum (map f pair) in
  let k0 kc := if even then mk_cos (fst kc) else mk_sin (fst kc) in
  let k1 kc := if even then mk_sin (fst kc) else mk_cos (fst kc) in
  let su kc := if even then Z.opp (mk_m (fst kc)) else mk_m (fst kc) in
  let sv kc := if even then mk_n (fst kc) else Z.opp (mk_n (fst kc)) in
  FLPartials
    (sum (fun kc => zmul (su kc) (Emul (t_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (t_val (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (su kc) (Emul (t_ds (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (sv kc) (Emul (t_ds (snd kc)) (k1 kc))))
    (sum (fun kc => zmul (Z.opp (mk_m (fst kc) * mk_m (fst kc)))
                         (Emul (t_val (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (mk_m (fst kc) * mk_n (fst kc))
                         (Emul (t_val (snd kc)) (k0 kc))))
    (sum (fun kc => zmul (Z.opp (mk_n (fst kc) * mk_n (fst kc)))
                         (Emul (t_val (snd kc)) (k0 kc)))).

Definition fladd (p q : flpartials) : flpartials :=
  FLPartials (Eadd (flp_u p) (flp_u q)) (Eadd (flp_v p) (flp_v q))
             (Eadd (flp_su p) (flp_su q)) (Eadd (flp_sv p) (flp_sv q))
             (Eadd (flp_uu p) (flp_uu q)) (Eadd (flp_uv p) (flp_uv q))
             (Eadd (flp_vv p) (flp_vv q)).

Definition flambda_partials_b (b : builder) (l : flpartials)
    : builder * flpartials :=
  let (b, lu) := alloc b (flp_u l) in
  let (b, lv) := alloc b (flp_v l) in
  let (b, lsu) := alloc b (flp_su l) in
  let (b, lsv) := alloc b (flp_sv l) in
  let (b, luu) := alloc b (flp_uu l) in
  let (b, luv) := alloc b (flp_uv l) in
  let (b, lvv) := alloc b (flp_vv l) in
  (b, FLPartials lu lv lsu lsv luu luv lvv).

(** The continuum force residual at a free radius.

    Every quantity is taken at the one point (s, u, v): there is no half
    point, no average across a node and no difference quotient. With
    sqrt(g) = R (R_u Z_s - R_s Z_u), the ansatz sqrt(g) B^u = phip
    (iota - lambda_v) and sqrt(g) B^v = phip (1 + lambda_u), and B_i =
    g_iu B^u + g_iv B^v, the three covariant components of J x B - grad p,
    scaled by mu0, are

      r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds
      r_u = - (d_u B_v - d_v B_u) B^v
      r_v =   (d_u B_v - d_v B_u) B^u

    which is what the node residual computes with centred differences and
    what this computes exactly. *)
Definition full_point_b (b : builder) (lasym : bool)
    (modes : list (Z * Z)) (K : nat)
    (prof : pprofile) (out : rout) : builder * residual3 :=
  (* VMEC's own value and radial derivative at each of the two half points,
     by the parity-aware rule of half_point_b, then the Hermite through
     them; lambda and iota, which VMEC gives on the half grid with no
     derivative, stay linear, and only their first radial derivative ever
     enters the field. *)
  (* The half-point scalars and coefficients read the knots and the wout's
     own numbers and no angle or radius, so they are allocated first: a
     contiguous run of bindings that every cell of a node shares, which the
     driver evaluates once for the node instead of once per cell. What
     follows reads the radius through vS and cannot be shared. *)
  let (b, hm_) := half_scalars_b b slot_s_a slot_s_j slot_s_hm in
  let (b, hp_) := half_scalars_b b slot_s_j slot_s_b slot_s_hp in
  let (b, cRm) := halfcoefs_b b hm_ (base_R K) K 0 1 modes 0 in
  let (b, cRp) := halfcoefs_b b hp_ (base_R K) K 1 2 modes 0 in
  let (b, cZm) := halfcoefs_b b hm_ (base_Z K) K 0 1 modes 0 in
  let (b, cZp) := halfcoefs_b b hp_ (base_Z K) K 1 2 modes 0 in
  let (b, cRam0) := if lasym then halfcoefs_b b hm_ (base_Ra K) K 0 1 modes 0
                    else (b, @nil coef2) in
  let (b, cRap0) := if lasym then halfcoefs_b b hp_ (base_Ra K) K 1 2 modes 0
                    else (b, @nil coef2) in
  let (b, cZam0) := if lasym then halfcoefs_b b hm_ (base_Za K) K 0 1 modes 0
                    else (b, @nil coef2) in
  let (b, cZap0) := if lasym then halfcoefs_b b hp_ (base_Za K) K 1 2 modes 0
                    else (b, @nil coef2) in
  (* everything above reads the knots and the file's own numbers; the angles
     enter here and the radius on the next line *)
  let (b, kers) := kernels_b b modes in
  let (b, hs) := herm_scalars_b b slot_s_hm slot_s_hp vS in
  let (b, rl) := rad_scalars_b b slot_s_hm slot_s_hp vS in
  (* Between two half points the coefficients are the Hermite through the
     value and radial derivative VMEC gives at each. On the innermost interval
     there is no inner half point, and the coefficients are read from the two
     innermost nodes by the parity-scaled linear rule instead, which is the
     rule VMEC's own half-point average is an instance of. Only this stage
     differs; everything downstream is the same reconstruction. *)
  let (b, cRZ) :=
    if is_axis out
    then
      let (b, rn) := rad_scalars_b b slot_s_j slot_s_b vS in
      let (b, cR) := radcoefs_b b rn (base_R K) K 1 2 modes 0 in
      let (b, cZ) := radcoefs_b b rn (base_Z K) K 1 2 modes 0 in
      let (b, cRa) := if lasym then radcoefs_b b rn (base_Ra K) K 1 2 modes 0
                      else (b, @nil coef3) in
      let (b, cZa) := if lasym then radcoefs_b b rn (base_Za K) K 1 2 modes 0
                      else (b, @nil coef3) in
      (b, (cR, cZ, cRa, cZa))
    else
      let (b, cR) := hermcoefs_b b hs cRm cRp in
      let (b, cZ) := hermcoefs_b b hs cZm cZp in
      let (b, cRa) := hermcoefs_b b hs cRam0 cRap0 in
      let (b, cZa) := hermcoefs_b b hs cZam0 cZap0 in
      (b, (cR, cZ, cRa, cZa)) in
  let cR := fst (fst (fst cRZ)) in
  let cZ := snd (fst (fst cRZ)) in
  let cRa := snd (fst cRZ) in
  let cZa := snd cRZ in
  let (b, cL) := radcoefs_b b rl (base_L K) K 0 1 modes 0 in
  let (b, cLa) := if lasym then radcoefs_b b rl (base_La K) K 0 1 modes 0
                  else (b, @nil coef3) in
  let (b, pR) := fpartials_b b
      (if lasym then fadd (fassemble kers cR true) (fassemble kers cRa false)
       else fassemble kers cR true) in
  let (b, pZ) := fpartials_b b
      (if lasym then fadd (fassemble kers cZ false) (fassemble kers cZa true)
       else fassemble kers cZ false) in
  let (b, pL) := flambda_partials_b b
      (if lasym then fladd (flambda_terms kers cL false)
                           (flambda_terms kers cLa true)
       else flambda_terms kers cL false) in
  (* iota is a flux function, carried on the half grid and read here by the
     same linear rule, so its radial derivative is the difference quotient
     of the two half-grid values, exactly *)
  let (b, iotap) :=
    alloc b (Emul (Esub slot_iota_p slot_iota_m) (rs_inv_h rl)) in
  let (b, iota) :=
    alloc b (Eadd slot_iota_m (Emul (rs_w rl)
                                    (Esub slot_iota_p slot_iota_m))) in
  let R    := fp_0 pR in  let R_s  := fp_s pR in  let R_ss := fp_ss pR in
  let R_u  := fp_u pR in  let R_v  := fp_v pR in
  let R_su := fp_su pR in let R_sv := fp_sv pR in
  let R_uu := fp_uu pR in let R_uv := fp_uv pR in let R_vv := fp_vv pR in
  let Z_s  := fp_s pZ in  let Z_ss := fp_ss pZ in
  let Z_u  := fp_u pZ in  let Z_v  := fp_v pZ in
  let Z_su := fp_su pZ in let Z_sv := fp_sv pZ in
  let Z_uu := fp_uu pZ in let Z_uv := fp_uv pZ in let Z_vv := fp_vv pZ in
  let L_u  := flp_u pL in  let L_v  := flp_v pL in
  let L_su := flp_su pL in let L_sv := flp_sv pL in
  let L_uu := flp_uu pL in let L_uv := flp_uv pL in let L_vv := flp_vv pL in
  let (b, tau)   := alloc b (Esub (Emul R_u Z_s) (Emul R_s Z_u)) in
  let (b, sqrtg) := alloc b (Emul R tau) in
  let (b, tau_s) := alloc b (Esub (Eadd (Emul R_su Z_s) (Emul R_u Z_ss))
                                  (Eadd (Emul R_ss Z_u) (Emul R_s Z_su))) in
  let (b, tau_u) := alloc b (Esub (Eadd (Emul R_uu Z_s) (Emul R_u Z_su))
                                  (Eadd (Emul R_su Z_u) (Emul R_s Z_uu))) in
  let (b, tau_v) := alloc b (Esub (Eadd (Emul R_uv Z_s) (Emul R_u Z_sv))
                                  (Eadd (Emul R_sv Z_u) (Emul R_s Z_uv))) in
  let (b, g_s) := alloc b (Eadd (Emul R_s tau) (Emul R tau_s)) in
  let (b, g_u) := alloc b (Eadd (Emul R_u tau) (Emul R tau_u)) in
  let (b, g_v) := alloc b (Eadd (Emul R_v tau) (Emul R tau_v)) in
  let (b, guu) := alloc b (Eadd (esq R_u) (esq Z_u)) in
  let (b, guv) := alloc b (Eadd (Emul R_u R_v) (Emul Z_u Z_v)) in
  let (b, gvv) := alloc b (Eadd (Eadd (esq R_v) (esq Z_v)) (esq R)) in
  let (b, gsu) := alloc b (Eadd (Emul R_s R_u) (Emul Z_s Z_u)) in
  let (b, gsv) := alloc b (Eadd (Emul R_s R_v) (Emul Z_s Z_v)) in
  let (b, guu_s) := alloc b (zmul 2 (Eadd (Emul R_u R_su) (Emul Z_u Z_su))) in
  let (b, guv_s) := alloc b (Eadd (Eadd (Emul R_su R_v) (Emul R_u R_sv))
                                  (Eadd (Emul Z_su Z_v) (Emul Z_u Z_sv))) in
  let (b, gvv_s) := alloc b (zmul 2 (Eadd (Eadd (Emul R_v R_sv) (Emul Z_v Z_sv))
                                          (Emul R R_s))) in
  let (b, gsu_u) := alloc b (Eadd (Eadd (Emul R_su R_u) (Emul R_s R_uu))
                                  (Eadd (Emul Z_su Z_u) (Emul Z_s Z_uu))) in
  let (b, gsu_v) := alloc b (Eadd (Eadd (Emul R_sv R_u) (Emul R_s R_uv))
                                  (Eadd (Emul Z_sv Z_u) (Emul Z_s Z_uv))) in
  let (b, gsv_u) := alloc b (Eadd (Eadd (Emul R_su R_v) (Emul R_s R_uv))
                                  (Eadd (Emul Z_su Z_v) (Emul Z_s Z_uv))) in
  let (b, gsv_v) := alloc b (Eadd (Eadd (Emul R_sv R_v) (Emul R_s R_vv))
                                  (Eadd (Emul Z_sv Z_v) (Emul Z_s Z_vv))) in
  let (b, guu_v) := alloc b (zmul 2 (Eadd (Emul R_u R_uv) (Emul Z_u Z_uv))) in
  let (b, guv_u) := alloc b (Eadd (Eadd (Emul R_uu R_v) (Emul R_u R_uv))
                                  (Eadd (Emul Z_uu Z_v) (Emul Z_u Z_uv))) in
  let (b, guv_v) := alloc b (Eadd (Eadd (Emul R_uv R_v) (Emul R_u R_vv))
                                  (Eadd (Emul Z_uv Z_v) (Emul Z_u Z_vv))) in
  let (b, gvv_u) := alloc b (zmul 2 (Eadd (Eadd (Emul R_v R_uv) (Emul Z_v Z_uv))
                                          (Emul R R_u))) in
  let (b, bu_num) := alloc b (Esub iota L_v) in
  let (b, bv_num) := alloc b (Eadd e1 L_u) in
  let (b, Bu) := alloc b (Ediv (Emul vPhip bu_num) sqrtg) in
  let (b, Bv) := alloc b (Ediv (Emul vPhip bv_num) sqrtg) in
  let (b, g2) := alloc b (esq sqrtg) in
  let dB nums gd := Ediv (Emul vPhip (Esub (Emul nums sqrtg) gd)) g2 in
  let (b, Bu_s) := alloc b (dB (Esub iotap L_sv) (Emul bu_num g_s)) in
  let (b, Bv_s) := alloc b (dB L_su (Emul bv_num g_s)) in
  let (b, Bu_u) := alloc b (dB (Eneg L_uv) (Emul bu_num g_u)) in
  let (b, Bv_u) := alloc b (dB L_uu (Emul bv_num g_u)) in
  let (b, Bu_v) := alloc b (dB (Eneg L_vv) (Emul bu_num g_v)) in
  let (b, Bv_v) := alloc b (dB L_uv (Emul bv_num g_v)) in
  let dcov gu gud gv gvd bud bvd :=
      Eadd (Eadd (Emul gud Bu) (Emul gu bud))
           (Eadd (Emul gvd Bv) (Emul gv bvd)) in
  let (b, B_u_s) := alloc b (dcov guu guu_s guv guv_s Bu_s Bv_s) in
  let (b, B_v_s) := alloc b (dcov guv guv_s gvv gvv_s Bu_s Bv_s) in
  let (b, B_s_u) := alloc b (dcov gsu gsu_u gsv gsv_u Bu_u Bv_u) in
  let (b, B_s_v) := alloc b (dcov gsu gsu_v gsv gsv_v Bu_v Bv_v) in
  let (b, B_u_v) := alloc b (dcov guu guu_v guv guv_v Bu_v Bv_v) in
  let (b, B_v_u) := alloc b (dcov guv guv_u gvv gvv_u Bu_u Bv_u) in
  let (b, mu0Js) := alloc b (Esub B_v_u B_u_v) in
  let (b, mu0pp) := alloc b (Emul mu0 (pprime prof)) in
  let (b, rs_) := alloc b (Esub (Esub (Emul (Esub B_s_v B_v_s) Bv)
                                      (Emul (Esub B_u_s B_s_u) Bu))
                                mu0pp) in
  (* The two magnetic terms of that difference, allocated only when they are
     asked for, so every other covering keeps the bindings it had. The third
     term is mu0pp, which already occupies a slot. *)
  let (b, tt) :=
    match out with
    | RRadialTerms =>
        let (b, t1) := alloc b (Emul (Esub B_s_v B_v_s) Bv) in
        let (b, t2) := alloc b (Emul (Esub B_u_s B_s_u) Bu) in
        (b, (t1, t2))
    | _ => (b, (e0, e0))
    end in
  let (b, ru) := alloc b (r_u_e mu0Js Bv) in
  let (b, rv) := alloc b (r_v_e mu0Js Bu) in
  (* The Jacobian and its radial derivative, which are what a magnetic well
     needs. Integrating the first over the angles is dV/ds and integrating the
     second is V'', by Quad.diff_under_integral: the average is differentiable
     in the radius and its derivative is the integral of the derivative, so
     the enclosure of one integral is an enclosure of the other quantity. The
     covariant B_u rides along, since its angular integral is the enclosed
     toroidal current and its radial derivative the current gradient. *)
  let (b, B_u_cov) := alloc b (Eadd (Emul guu Bu) (Emul guv Bv)) in
  (b, match out with
      | RRadialShear =>
          (* the shear, the current gradient and the pressure gradient, the
             three flux functions the Mercier criterion needs beside the four
             angular integrands. Each is constant over a surface, so its
             angular integral is four pi squared times its value; carrying
             them as integrands lets one machinery certify all of them. *)
          Residual3 (bindings_of b) iotap B_u_s mu0pp
      | RRadialGeom => Residual3 (bindings_of b) sqrtg g_s B_u_cov
      | RRadialTerms => Residual3 (bindings_of b) (fst tt) (snd tt) mu0pp
      | RRadialJsTerms =>
          (* the two terms of the surface current and their difference; both
             terms already occupy slots, so this allocates nothing *)
          Residual3 (bindings_of b) B_v_u B_u_v mu0Js
      | _ => Residual3 (bindings_of b) rs_ ru rv
      end).

(** The innermost interval reads the same three components as any other radial
    covering; what differs is only where its coefficients came from. *)

(* ---------------------------------------------------------------- *)
(* The radial residual cleared of the Jacobian                       *)

(** The residual divides by the Jacobian at both half points: the
    contravariant field is phip times a numerator over sqrt(g), the covariant
    components carry the same denominator, and their angular derivatives its
    square. With G the Jacobian of a half point, bu = iota - lambda_v and
    bv = 1 + lambda_u,

      B_u   = phip Cu / G,     Cu  = g_uu bu + g_uv bv
      B_v   = phip Cv / G,     Cv  = g_uv bu + g_vv bv
      d_u B_s = phip Dsu / G^2,  d_v B_s = phip Dsv / G^2,

    and the radial residual at the node, built from averages and differences
    of those across the two half points, is

      r_s = phip^2 (N1 Av - N2 Au) / (4 Delta Gm^3 Gp^3) - mu0 p'

    with Delta = s_h+ - s_h- and

      N1 = Delta (Dsv- Gp^2 + Dsv+ Gm^2) - 2 Gm Gp (Cv+ Gm - Cv- Gp)
      Av = bv- Gp + bv+ Gm
      N2 = 2 Gm Gp (Cu+ Gm - Cu- Gp) - Delta (Dsu- Gp^2 + Dsu+ Gm^2)
      Au = bu- Gp + bu+ Gm.

    So (Gm Gp)^3 r_s has no division by anything that depends on the angles:
    it is a polynomial in the finite Fourier series of R, Z and lambda, which
    TrigExpr.v recognises and Harmonic.v integrates exactly. The weight is
    positive wherever the two Jacobians share a sign, which is where the
    reconstruction is a valid coordinate system, so the weighted residual
    vanishes exactly where the residual does. *)
Record hnum := HNum {
  hn_G : expr ; hn_bu : expr ; hn_bv : expr ;
  hn_cu : expr ; hn_cv : expr ; hn_dsu : expr ; hn_dsv : expr }.

Definition hnum_b (b : builder) (q : halfq) : builder * hnum :=
  let R_s := q_Rs q in let R_u := q_Ru q in let R_v := q_Rv q in
  let Z_s := q_Zs q in let Z_u := q_Zu q in let Z_v := q_Zv q in
  let R_su := q_Rsu q in let R_sv := q_Rsv q in
  let R_uu := q_Ruu q in let R_uv := q_Ruv q in let R_vv := q_Rvv q in
  let Z_su := q_Zsu q in let Z_sv := q_Zsv q in
  let Z_uu := q_Zuu q in let Z_uv := q_Zuv q in let Z_vv := q_Zvv q in
  let G := q_sqrtg q in let bu := q_bu_num q in let bv := q_bv_num q in
  (* the metric elements against the radius and their angular derivatives,
     as half_point_b writes them *)
  let (b, gsu) := alloc b (Eadd (Emul R_s R_u) (Emul Z_s Z_u)) in
  let (b, gsv) := alloc b (Eadd (Emul R_s R_v) (Emul Z_s Z_v)) in
  let (b, gsu_u) := alloc b (Eadd (Eadd (Emul R_su R_u) (Emul R_s R_uu))
                                  (Eadd (Emul Z_su Z_u) (Emul Z_s Z_uu))) in
  let (b, gsu_v) := alloc b (Eadd (Eadd (Emul R_sv R_u) (Emul R_s R_uv))
                                  (Eadd (Emul Z_sv Z_u) (Emul Z_s Z_uv))) in
  let (b, gsv_u) := alloc b (Eadd (Eadd (Emul R_su R_v) (Emul R_s R_uv))
                                  (Eadd (Emul Z_su Z_v) (Emul Z_s Z_uv))) in
  let (b, gsv_v) := alloc b (Eadd (Eadd (Emul R_sv R_v) (Emul R_s R_vv))
                                  (Eadd (Emul Z_sv Z_v) (Emul Z_s Z_vv))) in
  let (b, cu) := alloc b (Eadd (Emul (q_guu q) bu) (Emul (q_guv q) bv)) in
  let (b, cv) := alloc b (Eadd (Emul (q_guv q) bu) (Emul (q_gvv q) bv)) in
  let (b, dsu) :=
    alloc b (Eadd (Emul (Eadd (Emul gsu_u bu) (Emul gsv_u bv)) G)
                  (Eadd (Emul gsu (Esub (Emul (Eneg (q_Luv q)) G) (Emul bu (q_g_u q))))
                        (Emul gsv (Esub (Emul (q_Luu q) G) (Emul bv (q_g_u q)))))) in
  let (b, dsv) :=
    alloc b (Eadd (Emul (Eadd (Emul gsu_v bu) (Emul gsv_v bv)) G)
                  (Eadd (Emul gsu (Esub (Emul (Eneg (q_Lvv q)) G) (Emul bu (q_g_v q))))
                        (Emul gsv (Esub (Emul (q_Luv q) G) (Emul bv (q_g_v q)))))) in
  (b, HNum G bu bv cu cv dsu dsv).

(** (Gm Gp)^3 r_s and the weight (Gm Gp)^3, from the two half points. *)
Definition weighted_b (b : builder) (qm qp : halfq) (inv_h mu0pp : expr)
    : builder * (expr * expr) :=
  let (b, m) := hnum_b b qm in
  let (b, p) := hnum_b b qp in
  let Gm := hn_G m in let Gp := hn_G p in
  let (b, delta) := alloc b (Esub slot_s_hp slot_s_hm) in
  let (b, gmgp) := alloc b (Emul Gm Gp) in
  let (b, gm2) := alloc b (esq Gm) in
  let (b, gp2) := alloc b (esq Gp) in
  let (b, n1) :=
    alloc b (Esub (Emul delta (Eadd (Emul (hn_dsv m) gp2) (Emul (hn_dsv p) gm2)))
                  (Emul (zmul 2 gmgp) (Esub (Emul (hn_cv p) Gm) (Emul (hn_cv m) Gp)))) in
  let (b, av) := alloc b (Eadd (Emul (hn_bv m) Gp) (Emul (hn_bv p) Gm)) in
  let (b, n2) :=
    alloc b (Esub (Emul (zmul 2 gmgp) (Esub (Emul (hn_cu p) Gm) (Emul (hn_cu m) Gp)))
                  (Emul delta (Eadd (Emul (hn_dsu m) gp2) (Emul (hn_dsu p) gm2)))) in
  let (b, au) := alloc b (Eadd (Emul (hn_bu m) Gp) (Emul (hn_bu p) Gm)) in
  let (b, w) := alloc b (Emul gmgp (Emul gmgp gmgp)) in
  let (b, pw) :=
    alloc b (Esub (Emul (Emul (esq vPhip) (Esub (Emul n1 av) (Emul n2 au)))
                        (Ediv inv_h e4))
                  (Emul w mu0pp)) in
  (b, (pw, w)).

(* ---------------------------------------------------------------- *)
(* The free-boundary jump                                            *)

(** The jump reads the field strength and nothing of the residual, so it has
    a path of its own. Every binding on it is a few operations on slots: a
    sum is a chain of two-term additions and a power a chain of products,
    since the derivative families of Deriv.v differentiate each binding's
    expression as written, and the derivative of one long expression is far
    longer than the derivatives of the short ones it is a chain of. *)

(** A sum as a chain of two-term additions, one binding each; the slot of the
    total. *)
Fixpoint chain_b (b : builder) (acc : expr) (l : list expr) : builder * expr :=
  match l with
  | [] => (b, acc)
  | x :: tl => let (b, s) := alloc b (Eadd acc x) in chain_b b s tl
  end.

Definition sum_b (b : builder) (l : list expr) : builder * expr :=
  match l with
  | [] => (b, e0)
  | x :: tl => let (b, s) := alloc b x in chain_b b s tl
  end.

(** acc x^j, one binding per factor. *)
Fixpoint pow_b (b : builder) (x acc : expr) (j : nat) : builder * expr :=
  match j with
  | O => (b, acc)
  | S j' => let (b, y) := alloc b (Emul acc x) in pow_b b x y j'
  end.

(** x, x^2, ..., x^n. *)
Fixpoint powers_b (b : builder) (x prev : expr) (n : nat) : builder * list expr :=
  match n with
  | O => (b, [])
  | S n' =>
      let (b, y) := alloc b (Emul prev x) in
      let (b, rest) := powers_b b x y n' in
      (b, y :: rest)
  end.

(** The pressure at a radius, as [pvalue] gives it, with the power series and
    the two-power profile built from chained bindings. *)
Definition pvalue_b (b : builder) (prof : pprofile) (x : expr) : builder * expr :=
  match prof with
  | PTwoPower p q =>
      let (b, xp) := pow_b b x e1 p in
      let (b, w) := alloc b (Esub e1 xp) in
      let (b, wq) := pow_b b w e1 q in
      alloc b (Emul (slot_am 0) wq)
  | PPower =>
      let (b, pw) := powers_b b x e1 (n_am - 1) in
      sum_b b (slot_am 0 :: map (fun jp => Emul (slot_am (fst jp)) (snd jp))
                               (combine (seq 1 (n_am - 1)) pw))
  | _ => alloc b (pvalue prof x)
  end.

(** The kernel pair cos(m u - n v), sin(m u - n v) of every mode, from the
    cosines and sines of m u and n v by the angle-difference identities. *)
Fixpoint modek_b (b : builder) (ku kv : list (Z * (expr * expr)))
    (l : list (Z * Z)) : builder * list (Z * Z * (expr * expr)) :=
  match l with
  | [] => (b, [])
  | (m, n) :: tl =>
      let (cm, sm) := zlook m vU ku in
      let (cn, sn) := zlook n vV kv in
      let (b, k) := alloc b (Eadd (Emul cm cn) (Emul sm sn)) in
      let (b, s) := alloc b (Esub (Emul sm cn) (Emul cm sn)) in
      let (b, rest) := modek_b b ku kv tl in
      (b, ((m, n), (k, s)) :: rest)
  end.

(** What the field strength reads at a half point: R, R_u, R_v, R_s,
    Z_u, Z_v, Z_s, lambda_u and lambda_v, each a chained sum over the modes of
    the symmetric series and, when lasym, the antisymmetric one. With
    K = cos(m u - n v) and S = sin(m u - n v) these are the sums of [assemble]
    and [lambda_terms]. *)
Record jpart := JPart {
  jp_R : expr ; jp_Ru : expr ; jp_Rv : expr ; jp_Rs : expr ;
  jp_Zu : expr ; jp_Zv : expr ; jp_Zs : expr ;
  jp_Lu : expr ; jp_Lv : expr }.

Definition jpart_b (b : builder) (lasym : bool) (mk : list (Z * Z * (expr * expr)))
    (hc : half_coefs) : builder * jpart :=
  let tz (z : Z) (c k : expr) := Emul (EfromZ z) (Emul c k) in
  let mm (x : Z * Z * (expr * expr)) := fst (fst x) in
  let nn (x : Z * Z * (expr * expr)) := snd (fst x) in
  let KK (x : Z * Z * (expr * expr)) := fst (snd x) in
  let SS (x : Z * Z * (expr * expr)) := snd (snd x) in
  let over {A : Type} (l : list A) (f : Z * Z * (expr * expr) -> A -> expr) :=
    map (fun p => f (fst p) (snd p)) (combine mk l) in
  let asym {A : Type} (l : list A) (f : Z * Z * (expr * expr) -> A -> expr) :=
    if lasym then over l f else [] in
  let cR := hc_R hc in let cZ := hc_Z hc in let cL := hc_L hc in
  let cRa := hc_Ra hc in let cZa := hc_Za hc in let cLa := hc_La hc in
  let (b, R) := sum_b b (over cR (fun x c => Emul (c_val c) (KK x))
                         ++ asym cRa (fun x c => Emul (c_val c) (SS x))) in
  let (b, Ru) := sum_b b (over cR (fun x c => tz (Z.opp (mm x)) (c_val c) (SS x))
                          ++ asym cRa (fun x c => tz (mm x) (c_val c) (KK x))) in
  let (b, Rv) := sum_b b (over cR (fun x c => tz (nn x) (c_val c) (SS x))
                          ++ asym cRa (fun x c => tz (Z.opp (nn x)) (c_val c) (KK x))) in
  let (b, Rs) := sum_b b (over cR (fun x c => Emul (c_ds c) (KK x))
                          ++ asym cRa (fun x c => Emul (c_ds c) (SS x))) in
  let (b, Zu) := sum_b b (over cZ (fun x c => tz (mm x) (c_val c) (KK x))
                          ++ asym cZa (fun x c => tz (Z.opp (mm x)) (c_val c) (SS x))) in
  let (b, Zv) := sum_b b (over cZ (fun x c => tz (Z.opp (nn x)) (c_val c) (KK x))
                          ++ asym cZa (fun x c => tz (nn x) (c_val c) (SS x))) in
  let (b, Zs) := sum_b b (over cZ (fun x c => Emul (c_ds c) (SS x))
                          ++ asym cZa (fun x c => Emul (c_ds c) (KK x))) in
  let (b, Lu) := sum_b b (over cL (fun x l => tz (mm x) l (KK x))
                          ++ asym cLa (fun x l => tz (Z.opp (mm x)) l (SS x))) in
  let (b, Lv) := sum_b b (over cL (fun x l => tz (Z.opp (nn x)) l (KK x))
                          ++ asym cLa (fun x l => tz (nn x) l (SS x))) in
  (b, JPart R Ru Rv Rs Zu Zv Zs Lu Lv).

(** The mu0-scaled total pressure p + B^2/2 at a half point, with
    B^2 = phip^2 (bu (g_uu bu + g_uv bv) + bv (g_uv bu + g_vv bv)) / g,
    which is B^u B_u + B^v B_v of [half_point_b]. *)
Definition jhalf_b (b : builder) (jp : jpart) (iota p : expr) : builder * expr :=
  let (b, tau) := alloc b (Esub (Emul (jp_Ru jp) (jp_Zs jp))
                                (Emul (jp_Rs jp) (jp_Zu jp))) in
  let (b, sg) := alloc b (Emul (jp_R jp) tau) in
  let (b, guu) := alloc b (Eadd (esq (jp_Ru jp)) (esq (jp_Zu jp))) in
  let (b, guv) := alloc b (Eadd (Emul (jp_Ru jp) (jp_Rv jp))
                                (Emul (jp_Zu jp) (jp_Zv jp))) in
  let (b, gvv) := alloc b (Eadd (Eadd (esq (jp_Rv jp)) (esq (jp_Zv jp)))
                                (esq (jp_R jp))) in
  let (b, bu) := alloc b (Esub iota (jp_Lv jp)) in
  let (b, bv) := alloc b (Eadd e1 (jp_Lu jp)) in
  let (b, cu) := alloc b (Eadd (Emul guu bu) (Emul guv bv)) in
  let (b, cv) := alloc b (Eadd (Emul guv bu) (Emul gvv bv)) in
  let (b, num) := alloc b (Eadd (Emul bu cu) (Emul bv cv)) in
  let (b, g2) := alloc b (esq sg) in
  let (b, b2) := alloc b (Ediv (Emul (esq vPhip) num) g2) in
  alloc b (Eadd (Emul (Ediv e1 e2) b2) (Emul mu0 p)).

(** The jump: the total pressure of the two half points extrapolated
    linearly to s = 1, against the vacuum pressure of the block. With the node
    the last interior one, the half points sit at 1 - 3h/2 and 1 - h/2 and the
    extrapolation is 3/2 of the outer less 1/2 of the inner. *)
Definition jump_b (b : builder) (lasym : bool) (modes : list (Z * Z)) (K : nat)
    (prof : pprofile) (vm : list (Z * Z)) : residual3 :=
  let (b, hcm) := half_coefs_b b lasym modes K 0 1 0 slot_s_a slot_s_j slot_s_hm in
  let (b, hcp) := half_coefs_b b lasym modes K 1 2 1 slot_s_j slot_s_b slot_s_hp in
  let (b, pm) := pvalue_b b prof slot_s_hm in
  let (b, pp) := pvalue_b b prof slot_s_hp in
  let (b, ku) := zkernels_b b vU (nodup Z.eq_dec (map fst modes ++ map fst vm)) in
  let (b, kv) := zkernels_b b vV (nodup Z.eq_dec (map snd modes ++ map snd vm)) in
  let (b, mk) := modek_b b ku kv modes in
  let (b, vk) := modek_b b ku kv vm in
  let (b, jm) := jpart_b b lasym mk hcm in
  let (b, jp) := jpart_b b lasym mk hcp in
  let (b, tm) := jhalf_b b jm slot_iota_m pm in
  let (b, tp) := jhalf_b b jp slot_iota_p pp in
  let (b, te) := alloc b (Eadd tp (Emul (Esub e1 slot_s_hp)
                                        (Ediv (Esub tp tm)
                                              (Esub slot_s_hp slot_s_hm)))) in
  let V := length vm in
  let vterms off :=
    map (fun ik => Eadd (Emul (slot_vac lasym K (off + 2 * fst ik)) (fst (snd (snd ik))))
                        (Emul (slot_vac lasym K (off + 2 * fst ik + 1)) (snd (snd (snd ik)))))
        (combine (seq 0 V) vk) in
  let (b, pmid) := sum_b b (vterms 0) in
  let (b, pdif) := sum_b b (vterms (2 * V)) in
  let (b, pv) := alloc b (Eadd pmid (Emul (slot_vac lasym K (4 * V)) pdif)) in
  let (b, jmp) := alloc b (Esub te pv) in
  Residual3 (bindings_of b) jmp te pv.

(* ---------------------------------------------------------------- *)
(* The resonant harmonic of the Jacobian                             *)

(** The cosine and sine of m u and of n v in the shape [kern_arg] writes, so
    that TrigExpr.tdeg reads them as kernels of degree m and n. *)
Fixpoint ukernels_b (b : builder) (ms : list Z) : builder * list (Z * (expr * expr)) :=
  match ms with
  | [] => (b, [])
  | m :: tl =>
      let (b, c) := alloc b (Ecos (kern_arg m 0)) in
      let (b, s) := alloc b (Esin (kern_arg m 0)) in
      let (b, rest) := ukernels_b b tl in
      (b, (m, (c, s)) :: rest)
  end.

Fixpoint vkernels_b (b : builder) (ns : list Z) : builder * list (Z * (expr * expr)) :=
  match ns with
  | [] => (b, [])
  | n :: tl =>
      let (b, c) := alloc b (Ecos (kern_arg 0 (Z.opp n))) in
      let (b, s) := alloc b (Esin (kern_arg 0 (Z.opp n))) in
      let (b, rest) := vkernels_b b tl in
      (b, (n, (c, s)) :: rest)
  end.

(** The Jacobian of the Hermite reconstruction at the free radius, with R,
    R_u, R_s, Z_u and Z_s chained sums over the modes. *)
Definition fjacobian_b (b : builder) (lasym : bool) (mk : list (Z * Z * (expr * expr)))
    (cR cZ cRa cZa : list coef3) : builder * expr :=
  let tz (z : Z) (c k : expr) := Emul (EfromZ z) (Emul c k) in
  let mm (x : Z * Z * (expr * expr)) := fst (fst x) in
  let KK (x : Z * Z * (expr * expr)) := fst (snd x) in
  let SS (x : Z * Z * (expr * expr)) := snd (snd x) in
  let over (l : list coef3) (f : Z * Z * (expr * expr) -> coef3 -> expr) :=
    map (fun p => f (fst p) (snd p)) (combine mk l) in
  let asym (l : list coef3) (f : Z * Z * (expr * expr) -> coef3 -> expr) :=
    if lasym then over l f else [] in
  let (b, R) := sum_b b (over cR (fun x c => Emul (t_val c) (KK x))
                         ++ asym cRa (fun x c => Emul (t_val c) (SS x))) in
  let (b, Ru) := sum_b b (over cR (fun x c => tz (Z.opp (mm x)) (t_val c) (SS x))
                          ++ asym cRa (fun x c => tz (mm x) (t_val c) (KK x))) in
  let (b, Rs) := sum_b b (over cR (fun x c => Emul (t_ds c) (KK x))
                          ++ asym cRa (fun x c => Emul (t_ds c) (SS x))) in
  let (b, Zu) := sum_b b (over cZ (fun x c => tz (mm x) (t_val c) (KK x))
                          ++ asym cZa (fun x c => tz (Z.opp (mm x)) (t_val c) (SS x))) in
  let (b, Zs) := sum_b b (over cZ (fun x c => Emul (t_ds c) (SS x))
                          ++ asym cZa (fun x c => Emul (t_ds c) (KK x))) in
  let (b, tau) := alloc b (Esub (Emul Ru Zs) (Emul Rs Zu)) in
  alloc b (Emul R tau).

Definition newcomb_b (b : builder) (lasym : bool) (modes : list (Z * Z)) (K : nat)
    (prof : pprofile) (hm hn : Z) : residual3 :=
  (* the half-point coefficients and the pressure gradient read no angle *)
  let (b, hsm) := half_scalars_b b slot_s_a slot_s_j slot_s_hm in
  let (b, hsp) := half_scalars_b b slot_s_j slot_s_b slot_s_hp in
  let (b, cRm) := halfcoefs_b b hsm (base_R K) K 0 1 modes 0 in
  let (b, cRp) := halfcoefs_b b hsp (base_R K) K 1 2 modes 0 in
  let (b, cZm) := halfcoefs_b b hsm (base_Z K) K 0 1 modes 0 in
  let (b, cZp) := halfcoefs_b b hsp (base_Z K) K 1 2 modes 0 in
  let (b, cRam) := if lasym then halfcoefs_b b hsm (base_Ra K) K 0 1 modes 0
                   else (b, @nil coef2) in
  let (b, cRap) := if lasym then halfcoefs_b b hsp (base_Ra K) K 1 2 modes 0
                   else (b, @nil coef2) in
  let (b, cZam) := if lasym then halfcoefs_b b hsm (base_Za K) K 0 1 modes 0
                   else (b, @nil coef2) in
  let (b, cZap) := if lasym then halfcoefs_b b hsp (base_Za K) K 1 2 modes 0
                   else (b, @nil coef2) in
  let (b, mu0pp) := alloc b (Emul mu0 (pprime prof)) in
  let (b, hs) := herm_scalars_b b slot_s_hm slot_s_hp vS in
  let (b, cR) := hermcoefs_b b hs cRm cRp in
  let (b, cZ) := hermcoefs_b b hs cZm cZp in
  let (b, cRa) := hermcoefs_b b hs cRam cRap in
  let (b, cZa) := hermcoefs_b b hs cZam cZap in
  let (b, ku) := ukernels_b b (nodup Z.eq_dec (map fst modes)) in
  let (b, kv) := vkernels_b b (nodup Z.eq_dec (map snd modes)) in
  let (b, mk) := modek_b b ku kv modes in
  let (b, sg) := fjacobian_b b lasym mk cR cZ cRa cZa in
  let (b, hc) := alloc b (Emul sg (Ecos (kern_arg hm hn))) in
  let (b, hsn) := alloc b (Emul sg (Esin (kern_arg hm hn))) in
  Residual3 (bindings_of b) hc hsn mu0pp.

Definition iota_b (b : builder) (hm hn : Z) : residual3 :=
  let (b, w) := alloc b (Ediv (Esub vS slot_s_hm) (Esub slot_s_hp slot_s_hm)) in
  let (b, io) := alloc b (Eadd slot_iota_m (Emul w (Esub slot_iota_p slot_iota_m))) in
  let (b, gap) := alloc b (Esub (Emul (EfromZ hm) io) (EfromZ hn)) in
  let (b, dio) := alloc b (Ediv (Esub slot_iota_p slot_iota_m)
                                (Esub slot_s_hp slot_s_hm)) in
  Residual3 (bindings_of b) gap io dio.

(* ---------------------------------------------------------------- *)
(* The energy on a line of states                                    *)

(** Row [row] of a node block along the line: the state slot of mode k plus
    t times the slot of the direction's block, for modes k .. k + n - 1. *)
Fixpoint line_b (b : builder) (t : expr) (base xbase K row k n : nat)
    : builder * list expr :=
  match n with
  | O => (b, [])
  | S n' =>
      let (b, y) := alloc b (Eadd (slot_node base K row k)
                                  (Emul t (slot_node xbase K row k))) in
      let (b, rest) := line_b b t base xbase K row (S k) n' in
      (b, y :: rest)
  end.

(** [halfcoefs_b] and [radcoefs_b] over rows given as expressions. *)
Fixpoint halfcoefs_l_b (b : builder) (hs : half_scalars) (modes : list (Z * Z))
    (ya yb : list expr) : builder * list coef2 :=
  match modes, ya, yb with
  | mn :: tl, a :: ta, c :: tc =>
      let (b, h) := halfcoef_b b hs (fst mn) a c in
      let (b, rest) := halfcoefs_l_b b hs tl ta tc in
      (b, h :: rest)
  | _, _, _ => (b, [])
  end.

Fixpoint radcoefs_l_b (b : builder) (rs : rad_scalars) (modes : list (Z * Z))
    (ya yb : list expr) : builder * list coef3 :=
  match modes, ya, yb with
  | mn :: tl, a :: ta, c :: tc =>
      let (b, h) := radcoef_b b rs (fst mn) a c in
      let (b, rest) := radcoefs_l_b b rs tl ta tc in
      (b, h :: rest)
  | _, _, _ => (b, [])
  end.

(** What the energy density reads at the free radius, as [jpart_b] reads it at
    a half point, from the coefficients of the reconstruction there. *)
Definition fpart_b (b : builder) (lasym : bool) (mk : list (Z * Z * (expr * expr)))
    (cR cZ cL cRa cZa cLa : list coef3) : builder * jpart :=
  let tz (z : Z) (c k : expr) := Emul (EfromZ z) (Emul c k) in
  let mm (x : Z * Z * (expr * expr)) := fst (fst x) in
  let nn (x : Z * Z * (expr * expr)) := snd (fst x) in
  let KK (x : Z * Z * (expr * expr)) := fst (snd x) in
  let SS (x : Z * Z * (expr * expr)) := snd (snd x) in
  let over (l : list coef3) (f : Z * Z * (expr * expr) -> coef3 -> expr) :=
    map (fun p => f (fst p) (snd p)) (combine mk l) in
  let asym (l : list coef3) (f : Z * Z * (expr * expr) -> coef3 -> expr) :=
    if lasym then over l f else [] in
  let (b, R) := sum_b b (over cR (fun x c => Emul (t_val c) (KK x))
                         ++ asym cRa (fun x c => Emul (t_val c) (SS x))) in
  let (b, Ru) := sum_b b (over cR (fun x c => tz (Z.opp (mm x)) (t_val c) (SS x))
                          ++ asym cRa (fun x c => tz (mm x) (t_val c) (KK x))) in
  let (b, Rv) := sum_b b (over cR (fun x c => tz (nn x) (t_val c) (SS x))
                          ++ asym cRa (fun x c => tz (Z.opp (nn x)) (t_val c) (KK x))) in
  let (b, Rs) := sum_b b (over cR (fun x c => Emul (t_ds c) (KK x))
                          ++ asym cRa (fun x c => Emul (t_ds c) (SS x))) in
  let (b, Zu) := sum_b b (over cZ (fun x c => tz (mm x) (t_val c) (KK x))
                          ++ asym cZa (fun x c => tz (Z.opp (mm x)) (t_val c) (SS x))) in
  let (b, Zv) := sum_b b (over cZ (fun x c => tz (Z.opp (nn x)) (t_val c) (KK x))
                          ++ asym cZa (fun x c => tz (nn x) (t_val c) (SS x))) in
  let (b, Zs) := sum_b b (over cZ (fun x c => Emul (t_ds c) (SS x))
                          ++ asym cZa (fun x c => Emul (t_ds c) (KK x))) in
  let (b, Lu) := sum_b b (over cL (fun x l => tz (mm x) (t_val l) (KK x))
                          ++ asym cLa (fun x l => tz (Z.opp (mm x)) (t_val l) (SS x))) in
  let (b, Lv) := sum_b b (over cL (fun x l => tz (Z.opp (nn x)) (t_val l) (KK x))
                          ++ asym cLa (fun x l => tz (nn x) (t_val l) (SS x))) in
  (b, JPart R Ru Rv Rs Zu Zv Zs Lu Lv).

(** The energy density on the line. The block after the state holds t, the
    sign of the Jacobian, then xi's rows at the offsets of the state's. *)
Definition energy_b (b : builder) (lasym : bool) (modes : list (Z * Z)) (K : nat)
    (prof : pprofile) : residual3 :=
  let xb := base_W lasym K in
  let t := evar xb in
  let sgn := evar (S xb) in
  let xR := xb + 2 in
  let xZ := xR + 3 * K in
  let xL := xZ + 3 * K in
  let xRa := xL + 2 * K in
  let xZa := xRa + 3 * K in
  let xLa := xZa + 3 * K in
  (* the coefficients of the line come first *)
  let (b, R0) := line_b b t (base_R K) xR K 0 0 K in
  let (b, R1) := line_b b t (base_R K) xR K 1 0 K in
  let (b, R2) := line_b b t (base_R K) xR K 2 0 K in
  let (b, Z0) := line_b b t (base_Z K) xZ K 0 0 K in
  let (b, Z1) := line_b b t (base_Z K) xZ K 1 0 K in
  let (b, Z2) := line_b b t (base_Z K) xZ K 2 0 K in
  let (b, L0) := line_b b t (base_L K) xL K 0 0 K in
  let (b, L1) := line_b b t (base_L K) xL K 1 0 K in
  let (b, Ra0) := if lasym then line_b b t (base_Ra K) xRa K 0 0 K else (b, []) in
  let (b, Ra1) := if lasym then line_b b t (base_Ra K) xRa K 1 0 K else (b, []) in
  let (b, Ra2) := if lasym then line_b b t (base_Ra K) xRa K 2 0 K else (b, []) in
  let (b, Za0) := if lasym then line_b b t (base_Za K) xZa K 0 0 K else (b, []) in
  let (b, Za1) := if lasym then line_b b t (base_Za K) xZa K 1 0 K else (b, []) in
  let (b, Za2) := if lasym then line_b b t (base_Za K) xZa K 2 0 K else (b, []) in
  let (b, La0) := if lasym then line_b b t (base_La K) xLa K 0 0 K else (b, []) in
  let (b, La1) := if lasym then line_b b t (base_La K) xLa K 1 0 K else (b, []) in
  (* the two half points, then the reconstruction at the free radius *)
  let (b, hsm) := half_scalars_b b slot_s_a slot_s_j slot_s_hm in
  let (b, hsp) := half_scalars_b b slot_s_j slot_s_b slot_s_hp in
  let (b, cRm) := halfcoefs_l_b b hsm modes R0 R1 in
  let (b, cRp) := halfcoefs_l_b b hsp modes R1 R2 in
  let (b, cZm) := halfcoefs_l_b b hsm modes Z0 Z1 in
  let (b, cZp) := halfcoefs_l_b b hsp modes Z1 Z2 in
  let (b, cRam) := halfcoefs_l_b b hsm modes Ra0 Ra1 in
  let (b, cRap) := halfcoefs_l_b b hsp modes Ra1 Ra2 in
  let (b, cZam) := halfcoefs_l_b b hsm modes Za0 Za1 in
  let (b, cZap) := halfcoefs_l_b b hsp modes Za1 Za2 in
  let (b, hs) := herm_scalars_b b slot_s_hm slot_s_hp vS in
  let (b, rl) := rad_scalars_b b slot_s_hm slot_s_hp vS in
  let (b, cR) := hermcoefs_b b hs cRm cRp in
  let (b, cZ) := hermcoefs_b b hs cZm cZp in
  let (b, cRa) := hermcoefs_b b hs cRam cRap in
  let (b, cZa) := hermcoefs_b b hs cZam cZap in
  let (b, cL) := radcoefs_l_b b rl modes L0 L1 in
  let (b, cLa) := radcoefs_l_b b rl modes La0 La1 in
  let (b, io) := alloc b (Eadd slot_iota_m (Emul (rs_w rl) (Esub slot_iota_p slot_iota_m))) in
  let (b, p) := pvalue_b b prof vS in
  let (b, ku) := zkernels_b b vU (nodup Z.eq_dec (map fst modes)) in
  let (b, kv) := zkernels_b b vV (nodup Z.eq_dec (map snd modes)) in
  let (b, mk) := modek_b b ku kv modes in
  let (b, jp) := fpart_b b lasym mk cR cZ cL cRa cZa cLa in
  (* the density *)
  let (b, tau) := alloc b (Esub (Emul (jp_Ru jp) (jp_Zs jp)) (Emul (jp_Rs jp) (jp_Zu jp))) in
  let (b, sg) := alloc b (Emul (jp_R jp) tau) in
  let (b, guu) := alloc b (Eadd (esq (jp_Ru jp)) (esq (jp_Zu jp))) in
  let (b, guv) := alloc b (Eadd (Emul (jp_Ru jp) (jp_Rv jp)) (Emul (jp_Zu jp) (jp_Zv jp))) in
  let (b, gvv) := alloc b (Eadd (Eadd (esq (jp_Rv jp)) (esq (jp_Zv jp))) (esq (jp_R jp))) in
  let (b, bu) := alloc b (Esub io (jp_Lv jp)) in
  let (b, bv) := alloc b (Eadd e1 (jp_Lu jp)) in
  let (b, num) := alloc b (Eadd (Emul bu (Eadd (Emul guu bu) (Emul guv bv)))
                                (Emul bv (Eadd (Emul guv bu) (Emul gvv bv)))) in
  let (b, b2g) := alloc b (Ediv (Emul (esq vPhip) num) sg) in
  let (b, w) := alloc b (Emul sgn (Esub (Emul (Ediv e1 e2) b2g) (Emul (Emul mu0 p) sg))) in
  let (b, vol) := alloc b (Emul sgn sg) in
  Residual3 (bindings_of b) w vol b2g.

(* ---------------------------------------------------------------- *)
(* A coil field against a torus                                      *)

(** The three components of a cross product. *)
Definition cross3 (a1 a2 a3 b1 b2 b3 : expr) : expr * expr * expr :=
  (Esub (Emul a2 b3) (Emul a3 b2),
   Esub (Emul a3 b1) (Emul a1 b3),
   Esub (Emul a1 b2) (Emul a2 b1)).

(** The contribution of source points i .. i + P - 1 at the point (x, y, z),
    each as three slots of the field it adds. *)
Fixpoint coil_terms_b (b : builder) (lasym : bool) (K : nat) (x y z : expr)
    (i P : nat) : builder * list (expr * expr * expr) :=
  match P with
  | O => (b, [])
  | S P' =>
      let px := slot_vac lasym K (6 * i) in
      let py := slot_vac lasym K (6 * i + 1) in
      let pz := slot_vac lasym K (6 * i + 2) in
      let dx := slot_vac lasym K (6 * i + 3) in
      let dy := slot_vac lasym K (6 * i + 4) in
      let dz := slot_vac lasym K (6 * i + 5) in
      let (b, rx) := alloc b (Esub x px) in
      let (b, ry) := alloc b (Esub y py) in
      let (b, rz) := alloc b (Esub z pz) in
      let (b, r2) := alloc b (Eadd (Eadd (esq rx) (esq ry)) (esq rz)) in
      let (b, r3) := alloc b (Emul r2 (Esqrt r2)) in
      let '(c1, c2, c3) := cross3 dx dy dz rx ry rz in
      let (b, t1) := alloc b (Ediv c1 r3) in
      let (b, t2) := alloc b (Ediv c2 r3) in
      let (b, t3) := alloc b (Ediv c3 r3) in
      let (b, rest) := coil_terms_b b lasym K x y z (S i) P' in
      (b, (t1, t2, t3) :: rest)
  end.

Definition coil_b (b : builder) (lasym : bool) (modes : list (Z * Z)) (K P : nat)
    : residual3 :=
  let tz (z : Z) (c k : expr) := Emul (EfromZ z) (Emul c k) in
  let (b, ku) := zkernels_b b vU (nodup Z.eq_dec (map fst modes)) in
  let (b, kv) := zkernels_b b vV (nodup Z.eq_dec (map snd modes)) in
  let (b, mk) := modek_b b ku kv modes in
  let rows (base : nat) := map (fun k => slot_node base K 0 k) (seq 0 K) in
  let over (f : Z * Z * (expr * expr) -> expr -> expr) (base : nat) :=
    map (fun p => f (fst p) (snd p)) (combine mk (rows base)) in
  (* the torus and its two tangents, from the cosine series of R and the
     sine series of Z *)
  let (b, Rt) := sum_b b (over (fun x c => Emul c (fst (snd x))) (base_R K)) in
  let (b, Ru) := sum_b b (over (fun x c => tz (Z.opp (fst (fst x))) c (snd (snd x))) (base_R K)) in
  let (b, Rv) := sum_b b (over (fun x c => tz (snd (fst x)) c (snd (snd x))) (base_R K)) in
  let (b, Zt) := sum_b b (over (fun x c => Emul c (snd (snd x))) (base_Z K)) in
  let (b, Zu) := sum_b b (over (fun x c => tz (fst (fst x)) c (fst (snd x))) (base_Z K)) in
  let (b, Zv) := sum_b b (over (fun x c => tz (Z.opp (snd (fst x))) c (fst (snd x))) (base_Z K)) in
  let (b, cv) := alloc b (Ecos vV) in
  let (b, sv) := alloc b (Esin vV) in
  let (b, X) := alloc b (Emul Rt cv) in
  let (b, Y) := alloc b (Emul Rt sv) in
  let (b, Xu) := alloc b (Emul Ru cv) in
  let (b, Yu) := alloc b (Emul Ru sv) in
  let (b, Xv) := alloc b (Esub (Emul Rv cv) Y) in
  let (b, Yv) := alloc b (Eadd (Emul Rv sv) X) in
  let '(n1, n2, n3) := cross3 Xu Yu Zu Xv Yv Zv in
  let (b, n1) := alloc b n1 in
  let (b, n2) := alloc b n2 in
  let (b, n3) := alloc b n3 in
  (* the field, as the sum over the source points *)
  let (b, ts) := coil_terms_b b lasym K X Y Zt 0 P in
  let (b, B1) := sum_b b (map (fun t => fst (fst t)) ts) in
  let (b, B2) := sum_b b (map (fun t => snd (fst t)) ts) in
  let (b, B3) := sum_b b (map (fun t => snd t) ts) in
  let (b, bn) := alloc b (Eadd (Eadd (Emul B1 n1) (Emul B2 n2)) (Emul B3 n3)) in
  let (b, b2) := alloc b (Eadd (Eadd (esq B1) (esq B2)) (esq B3)) in
  let (b, nn) := alloc b (Eadd (Eadd (esq n1) (esq n2)) (esq n3)) in
  let (b, sn) := alloc b (Ediv bn (Esqrt (Emul b2 nn))) in
  Residual3 (bindings_of b) sn bn b2.

(** The mu0-scaled force residual: r_s at the node from the centered
    differences and averages of its two half points, r_u and r_v at the
    outer half point. *)
(** The state of the surface residual once everything but its two angular
    components is allocated: the builder, and what the outputs read from it.
    A theorem about those components reads this as one value instead of
    unfolding the builder, which is what keeps Identities.v cheap. *)
Record rstate := RState {
  st_b : builder ;
  st_kers : list mode_kernels ;
  st_hcp : half_coefs ;
  st_qp : halfq ;
  st_mq : mercq ;
  st_mu0pp : expr ;
  st_rs : expr ;
  st_tt : expr * expr }.

Definition residual_pre (cfg : pconfig) (modes : list (Z * Z)) : rstate :=
  let K := length modes in
  let lasym := pc_lasym cfg in
  let b := Builder (base_scratch_of lasym (pc_out cfg) K) [] in
  (* The bindings that read no angle come first: the coefficients of both
     half points, and the node-row coefficients the Mercier geometry reads.
     The driver evaluates that leading run once per node and shares it across
     the node's cells, deciding where the run ends with the extracted
     var_free rather than by trusting this order. Rows of the R/Z node
     blocks: 0 = j-1, 1 = j, 2 = j+1; rows of the lambda block: 0 = h-,
     1 = h+. *)
  let (b, hcm) := half_coefs_b b lasym modes K 0 1 0
                    slot_s_a slot_s_j slot_s_hm in
  let (b, hcp) := half_coefs_b b lasym modes K 1 2 1
                    slot_s_j slot_s_b slot_s_hp in
  let want_merc :=
    match pc_out cfg with
    | RMercierA => true | RMercierB => true | _ => false
    end in
  let (b, ncf) :=
    if want_merc then node_coefs_b b lasym modes K
    else (b, NCoefs [] [] [] []) in
  (* the angles enter here *)
  let (b, kers) := kernels_b b modes in
  let (b, qm) := half_point_b b lasym kers hcm slot_iota_m in
  let (b, qp) := half_point_b b lasym kers hcp slot_iota_p in
  let (b, half) := alloc b (Ediv e1 e2) in
  let (b, inv_h) := alloc b (Ediv e1 (Esub slot_s_hp slot_s_hm)) in
  let avg x y := Emul half (Eadd x y) in
  let dif x y := Emul (Esub y x) inv_h in
  let (b, Bu) := alloc b (avg (q_Bu qm) (q_Bu qp)) in
  let (b, Bv) := alloc b (avg (q_Bv qm) (q_Bv qp)) in
  let (b, B_s_u) := alloc b (avg (q_B_s_u qm) (q_B_s_u qp)) in
  let (b, B_s_v) := alloc b (avg (q_B_s_v qm) (q_B_s_v qp)) in
  let (b, B_u_s) := alloc b (dif (q_B_u qm) (q_B_u qp)) in
  let (b, B_v_s) := alloc b (dif (q_B_v qm) (q_B_v qp)) in
  let (b, mu0pp) := alloc b (Emul mu0 (pprime (pc_prof cfg))) in
  let (b, mq) :=
    if want_merc
    then merc_b b lasym kers ncf qm qp B_s_v B_v_s B_u_s B_s_u half
    else (b, MercQ e0 e0 e0 e0 e0 e0) in
  let (b, rs) := alloc b (Esub (Esub (Emul (Esub B_s_v B_v_s) Bv)
                                     (Emul (Esub B_u_s B_s_u) Bu))
                               mu0pp) in
  (* the two magnetic terms of that difference, as above; for a weighted
     output, the residual cleared of the Jacobian and its weight *)
  let (b, tt) :=
    match pc_out cfg with
    | RTerms =>
        let (b, t1) := alloc b (Emul (Esub B_s_v B_v_s) Bv) in
        let (b, t2) := alloc b (Emul (Esub B_u_s B_s_u) Bu) in
        (b, (t1, t2))
    | RWeighted _ _ => weighted_b b qm qp inv_h mu0pp
    | _ => (b, (e0, e0))
    end in
  RState b kers hcp qp mq mu0pp rs tt.

(** The two angular components, then the output the certificate asks for. *)
Definition residual_tail (cfg : pconfig) (modes : list (Z * Z)) (st : rstate)
    : residual3 :=
  let K := length modes in
  let lasym := pc_lasym cfg in
  let kers := st_kers st in let hcp := st_hcp st in let qp := st_qp st in
  let mq := st_mq st in let mu0pp := st_mu0pp st in
  let rs := st_rs st in let tt := st_tt st in
  let (b, ru) := alloc (st_b st) (r_u_e (q_mu0Js qp) (q_Bv qp)) in
  let (b, rv) := alloc b (r_v_e (q_mu0Js qp) (q_Bu qp)) in
  (* With a harmonic requested, each component is multiplied by the kernel
     of that mode. Every downstream check is unchanged: the same cell
     machinery then bounds the integrand of the harmonic, and Quad.v turns
     the per-cell bounds into an enclosure of the harmonic itself. *)
  match pc_out cfg with
  | RResidual => Residual3 (bindings_of b) rs ru rv
  | RJsTerms =>
      (* d_u B_v and d_v B_u at the outer half point, and their difference the
         surface current. q_mu0Js is that difference, and the two terms are
         allocated here since the half point exposes only the difference. *)
      let (b, j1) := alloc b (q_B_v_u qp) in
      let (b, j2) := alloc b (q_B_u_v qp) in
      let (b, js) := alloc b (q_mu0Js qp) in
      Residual3 (bindings_of b) j1 j2 js
  | RHarmonic hm hn =>
      let (b, k) := alloc b (Ecos (kern_arg hm hn)) in
      let (b, hs) := alloc b (Emul rs k) in
      let (b, hu) := alloc b (Emul ru k) in
      let (b, hv) := alloc b (Emul rv k) in
      Residual3 (bindings_of b) hs hu hv
  | RGeometry =>
      let (b, g) := alloc b (q_sqrtg qp) in
      let (b, gb) := alloc b (q_sqrtg_B2 qp) in
      let (b, bu) := alloc b (q_B_u qp) in
      Residual3 (bindings_of b) g gb bu
  | RMercierA => Residual3 (bindings_of b) (m_tpp mq) (m_tbb mq) (m_tjb mq)
  | RMercierB => Residual3 (bindings_of b) (m_tjj mq) (m_gf mq) (m_b2 mq)
  | RStreamDefect =>
      (* w is carried as data, so what says it is a stream function of this
         field is the defect of the two relations it has to satisfy. Both are
         bounded over the same covering as everything else, and the third
         component is the surface current, which is what has to vanish for any
         w to exist at all. *)
      let wpair := combine kers (map (fun k => slot_wcoef lasym K k)
                                     (seq 0 K)) in
      let (b, wu) :=
        alloc b (esum (map (fun kc => zmul (mk_m (fst kc))
                                        (Emul (snd kc) (mk_cos (fst kc))))
                           wpair)) in
      let (b, wv) :=
        alloc b (esum (map (fun kc => zmul (Z.opp (mk_n (fst kc)))
                                        (Emul (snd kc) (mk_cos (fst kc))))
                           wpair)) in
      let (b, du) :=
        alloc b (Esub wu (Esub (q_B_u qp) (slot_Itor lasym K))) in
      let (b, dv) :=
        alloc b (Esub wv (Esub (q_B_v qp) (slot_Gpol lasym K))) in
      let (b, js) := alloc b (q_mu0Js qp) in
      Residual3 (bindings_of b) du dv js
  | RBoozer hm hn =>
      (* the harmonic of |B| in the Boozer angles, as an integral over the
         VMEC angles with the Jacobian of the angle map. Every piece is
         explicit once w is given: the angles are u + lambda + iota p and
         v + p with p = (w - I lambda) / (G + iota I), and that denominator
         is a flux function, so it is constant over the surface and its
         reciprocal is allocated once. *)
      let wpair := combine kers (map (fun k => slot_wcoef lasym K k)
                                     (seq 0 K)) in
      let (b, w) :=
        alloc b (esum (map (fun kc => Emul (snd kc) (mk_sin (fst kc)))
                           wpair)) in
      let (b, wu) :=
        alloc b (esum (map (fun kc => zmul (mk_m (fst kc))
                                        (Emul (snd kc) (mk_cos (fst kc))))
                           wpair)) in
      let (b, wv) :=
        alloc b (esum (map (fun kc => zmul (Z.opp (mk_n (fst kc)))
                                        (Emul (snd kc) (mk_cos (fst kc))))
                           wpair)) in
      let (b, denom) :=
        alloc b (Eadd (slot_Gpol lasym K)
                      (Emul slot_iota_p (slot_Itor lasym K))) in
      let (b, ip) := alloc b (Ediv e1 denom) in
      (* p = (w - I lambda) / (G + iota I). The covariant components
         transform with the map, so B_u = I (1 + lambda_u + iota p_u) + G p_u
         has to equal I + w_u, which is what fixes p_u, and likewise p_v. *)
      let itor := slot_Itor lasym K in
      let (b, p) := alloc b (Emul (Esub w (Emul itor (q_L qp))) ip) in
      let (b, pu) := alloc b (Emul (Esub wu (Emul itor (q_Lu qp))) ip) in
      let (b, pv) := alloc b (Emul (Esub wv (Emul itor (q_Lv qp))) ip) in
      let (b, thb) :=
        alloc b (Eadd (Eadd vU (q_L qp)) (Emul slot_iota_p p)) in
      let (b, zeb) := alloc b (Eadd vV p) in
      let (b, thu) :=
        alloc b (Eadd (Eadd e1 (q_Lu qp)) (Emul slot_iota_p pu)) in
      let (b, thv) := alloc b (Eadd (q_Lv qp) (Emul slot_iota_p pv)) in
      let (b, zev) := alloc b (Eadd e1 pv) in
      let (b, jac) := alloc b (Esub (Emul thu zev) (Emul thv pu)) in
      let (b, bmod) := alloc b (Esqrt (q_B2 qp)) in
      let (b, arg) :=
        alloc b (Esub (Emul (EfromZ hm) thb) (Emul (EfromZ hn) zeb)) in
      let (b, hc) := alloc b (Emul bmod (Emul (Ecos arg) jac)) in
      let (b, hsn) := alloc b (Emul bmod (Emul (Esin arg) jac)) in
      let (b, jj) := alloc b jac in
      Residual3 (bindings_of b) hc hsn jj
  | RCovHarm hm hn =>
      let (b, k) := alloc b (Ecos (kern_arg hm hn)) in
      let (b, hu) := alloc b (Emul (q_B_u qp) k) in
      let (b, hv) := alloc b (Emul (q_B_v qp) k) in
      let (b, hj) := alloc b (Emul (q_mu0Js qp) k) in
      Residual3 (bindings_of b) hu hv hj
  | RCovHarmS hm hn =>
      let (b, k) := alloc b (Esin (kern_arg hm hn)) in
      let (b, hu) := alloc b (Emul (q_B_u qp) k) in
      let (b, hv) := alloc b (Emul (q_B_v qp) k) in
      let (b, hj) := alloc b (Emul (q_mu0Js qp) k) in
      Residual3 (bindings_of b) hu hv hj
  | RTerms => Residual3 (bindings_of b) (fst tt) (snd tt) mu0pp
  | RQuasiSym =>
      (* the triple product at the outer half point, from the coefficients
         and kernels that point was built from; nothing above is read *)
      let (b, t) := qs_b b lasym kers hcp qp in
      let '(qs, t1, t2) := t in
      Residual3 (bindings_of b) qs t1 t2
  | RQuasiTwo =>
      (* the two-term defect at the outer half point, against the flux
         function the certificate carries *)
      let (b, t) := qs2_b b qp (slot_F0 lasym K) in
      let '(qq, t1, t2) := t in
      Residual3 (bindings_of b) qq t1 t2
  | RWeighted hm hn =>
      (* the weighted radial residual against the kernel of one mode: its
         integral over the surface is the resonant harmonic of (Gm Gp)^3 r_s,
         which Harmonic.v computes exactly *)
      let (b, k) := alloc b (Ecos (kern_arg hm hn)) in
      let (b, ks) := alloc b (Esin (kern_arg hm hn)) in
      let (b, hc) := alloc b (Emul (fst tt) k) in
      let (b, hs) := alloc b (Emul (fst tt) ks) in
      let (b, pw) := alloc b (fst tt) in
      Residual3 (bindings_of b) hc hs pw
  | RJump _ => Residual3 (bindings_of b) rs ru rv
  | RNewcomb _ _ => Residual3 (bindings_of b) rs ru rv
  | RIota _ _ => Residual3 (bindings_of b) rs ru rv
  | REnergy => Residual3 (bindings_of b) rs ru rv
  | RCoil _ => Residual3 (bindings_of b) rs ru rv
  | RForced =>
      let (b, fs) := alloc b (Esub rs (slot_src lasym K 0)) in
      let (b, fu) := alloc b (Esub ru (slot_src lasym K 1)) in
      let (b, fv) := alloc b (Esub rv (slot_src lasym K 2)) in
      Residual3 (bindings_of b) fs fu fv
  | RRadial => Residual3 (bindings_of b) rs ru rv
  | RRadialGeom => Residual3 (bindings_of b) rs ru rv
  | RRadialShear => Residual3 (bindings_of b) rs ru rv
  | RRadialAxis => Residual3 (bindings_of b) rs ru rv
  | RRadialTerms => Residual3 (bindings_of b) rs ru rv
  | RRadialJsTerms => Residual3 (bindings_of b) rs ru rv
  end.


Definition residual (cfg : pconfig) (modes : list (Z * Z)) : residual3 :=
  let K := length modes in
  let lasym := pc_lasym cfg in
  let b := Builder (base_scratch_of lasym (pc_out cfg) K) [] in
  if is_radial (pc_out cfg) then
      (* the continuum residual at the free radius of slot 0, over the
         interval the node's two half points bracket. It allocates its own
         kernels, after the stage no angle or radius reaches. *)
      snd (full_point_b b lasym modes K (pc_prof cfg) (pc_out cfg))
  else match pc_out cfg with
       | RJump vm => jump_b b lasym modes K (pc_prof cfg) vm
       | RNewcomb hm hn => newcomb_b b lasym modes K (pc_prof cfg) hm hn
       | RIota hm hn => iota_b b hm hn
       | REnergy => energy_b b lasym modes K (pc_prof cfg)
       | RCoil P => coil_b b lasym modes K P
       | _ => residual_tail cfg modes (residual_pre cfg modes)
       end.

End WithExponents.
