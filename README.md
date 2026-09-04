# Stellarocq

Machine-checked plasma physics. A converged [VMEC++](https://github.com/proximafusion/vmecpp) equilibrium ships with a certificate, and a checker extracted from a [Rocq](https://rocq-prover.org) proof validates it: a VALID verdict is a machine-checked theorem about the exact numbers in the wout file. The covering runs over a continuum of angles, and with the radius among the varied coordinates over the volume between surfaces. Alongside the certificates the development proves identities the reconstruction satisfies, encloses the integrals a flux-surface average is built from, settles by inequality what no enclosure can decide, and states the physical assumptions it rests on.

The certificates are the visible half. The other half is a way of doing plasma
physics in which the arithmetic is carried by a proof rather than by a
convention: the checker is the proof, since it is extracted from one, so a
quantity is either enclosed by machinery whose soundness the kernel checked or
it is not claimed. What that buys is not confidence in one wout file. It is
that a physical statement about an equilibrium, a magnetic well, a stability
criterion, an obstruction to force balance over a family of fields, can be put
on the same footing as the residual bound, computed by the same evaluator, and
audited by the same command. The assumptions that remain are written down as
propositions in [theories/Hypotheses.v](theories/Hypotheses.v), each with what
would falsify it, and two of them turn out to be theorems about the
reconstruction rather than assumptions about the plasma.

It also buys something a solver cannot report at all. Because every quantity
arrives with an enclosure and an explicit definition, the same run says which
of its numbers the equilibrium determines and which are set by how a
derivative was defined. On one surface below, a stability criterion changes
sign between two equally defensible definitions of the same radial
derivative.

## What the method is for

A solver reports numbers. This reports theorems about them, and the difference
buys several things a floating-point code cannot do at all.

An equilibrium can be certified over a continuum instead of at samples. A cell
covers every point between the sampled ones, and because a cell ranges over any
two input slots rather than specifically over angles, putting the radius among
them covers the volume between surfaces as readily as the angles on one. The
same theorem serves both.

An equilibrium can be certified *not* to balance. `check1_lower` proves a
residual component bounded away from zero over a whole cell, so a passing
verdict is an obstruction: no field of the certified form is in equilibrium
anywhere in that region. A float code can report that a residual looks large;
it cannot rule out that the region contains a solution.

Flux-surface averages arrive with enclosures. The quadrature of
[theories/Quad.v](theories/Quad.v) turns per-cell bounds into rigorous
intervals for any angular integral, which covers `dV/ds`, the enclosed
currents, the mean square field and the four Mercier integrands. These are
quantities VMEC computes and nothing independently checks.

Some questions no enclosure can settle, and those become inequalities instead.
`Dgeod = tjb^2 - tbb tjj` is a difference of two numbers that agree to ten
digits, so no covering however fine decides its sign;
`mercier_geodesic_nonpositive` proves it is never positive, once and for every
equilibrium, by Cauchy-Schwarz.

A stability criterion can be assembled inside the checker rather than beside
it. [theories/Mercier.v](theories/Mercier.v) combines the four angular
integrals and the flux functions into DShear, DCurr, DWell and DGeod with the
same interval arithmetic, so what a run establishes is a bound on the Mercier
criterion and not on its ingredients.

A number can be reported as undetermined. Every term of the Mercier criterion
is a difference of larger numbers, and the run says by what factor a relative
error in each input is amplified into the result. Where that factor is a
hundred, the number is a property of the discretization rather than of the
plasma, and saying so is more useful than reporting it.

An obstruction can range over a family of fields. A cell varies any two input
slots, so one of them may be a Fourier coefficient: a floor verdict then
excludes every field whose coefficient lies in that interval, at every angle
the cells cover, rather than the one field the file names.

A bound can be told apart from what it bounds. The residual is a difference of
three terms, and `--terms` certifies each of them over the same cells, so a run
says whether a bound is a cancellation defect a finer covering reaches or an
imbalance it does not. On solovev the two magnetic terms agree to four digits;
on the three stellarators and li383 they do not cancel at all, and on two of
them the residual exceeds every term it is built from, which is what a floor
flat in every refinement means. The solver's own `fsqr` does not predict that
ratio, in either direction.

Run against a solver rather than against a file, the same machinery is a
differential oracle. A stellarator-symmetric equilibrium pushed through the
antisymmetric reconstruction with its antisymmetric coefficients set to zero
has to reproduce the symmetric run exactly, and that reduction is what found
proximafusion/vmecpp#788 and jonathanschilling/educational_VMEC#27. The
checker shares no code with either solver, so a disagreement localizes a bug
instead of raising a discrepancy.

## The claim

A certificate lists evaluation points: full-grid nodes of the wout's radial grid, each with a set of angles. Each point carries the integer mantissas and power-of-two exponents of every input (exact images of the IEEE doubles in the wout), and per-component bounds `N * 2^q`.

The theorem (`check_cert_correct`, [theories/Checker.v](theories/Checker.v)) states: if `check_cert` returns `true`, then at every listed point the three components of the mu0-scaled ideal-MHD force residual

```
r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds   at the node
r_u = -(d_u B_v - d_v B_u) B^v                                         at the outer half point
r_v =  (d_u B_v - d_v B_u) B^u                                         at the outer half point
```

of the field reconstructed from the certificate's coefficients evaluate to genuine real numbers whose absolute values obey the claimed bounds. "Genuine real number" is part of the theorem: a division by zero or an invalid square root anywhere in the evaluation makes the verdict INVALID.

A cell certificate replaces the list of angles with a list of cells. Each cell carries the mantissa half-widths of its two angles and, per component, a bound on the value at the centre, bounds on the two angular derivatives over the cell, and the cell bound they combine to. The theorem (`check_ccert_correct`, [theories/Cell.v](theories/Cell.v)) states: if `check_ccert` returns `true`, then at every real point of every cell, not only at its centre, the three components evaluate to genuine real numbers whose absolute values obey the cell bound. Successive cells abut, so their union is a continuum of angles rather than a sample of them; what that union covers in each case is under Results.

A cell ranges over any two distinct input slots, not specifically over the two angles, and the radius is one of the slots the reconstruction reads. A cell certificate whose two slots are the radius and the poloidal angle therefore covers a rectangle of the poloidal cross-section, and `check_ccert_correct` is the same theorem read at a different pair of slots. What that needs from the physics is a reconstruction defined and twice differentiable between the grid points, which is under Over the volume.

The bounds of a cell certificate are written by the checker rather than chosen by the generator. The width of an interval enclosure is a property of the arithmetic and not of the function: the residual of a converged equilibrium is a difference of terms that can agree to four digits, measured under What the residual is made of, interval arithmetic over a box loses that cancellation, and no float sample of the function predicts what is lost. `main --tighten in out` reads the enclosure the extracted code computes for each cell and emits the smallest claim that code accepts. The tightening chooses the number; an ordinary run of the checker over the result establishes it.

The reconstruction rule is VMEC's own, fixed in [theories/Physics.v](theories/Physics.v): R and Z on a half point are the parity-aware average of the two enclosing full-grid nodes (even m plain, odd m as coefficient over sqrt(s) rescaled by sqrt(s) of the half point), their radial derivatives the matching difference quotients with the derivative of the sqrt(s) factor, lambda and iota the wout's half-grid values, `B^u = phip (iota - lambda_v)/sqrtg`, `B^v = phip (1 + lambda_u)/sqrtg`, angular derivatives exact from the Fourier series, radial derivatives of the covariant field the centered differences of the two half points across the node, pressure from whichever closed form the wout's `pmass_type` names. The certificate is a statement about that object, not about VMEC++'s internals.

## Why this is different

"This wout satisfies force balance" normally means "the solver says so." The checker shares no code with VMEC++ or Fortran VMEC and does not trust the generator that wrote the certificate: it re-evaluates everything from the coefficients with interval arithmetic whose soundness is proven ([CoqInterval](https://coqinterval.gitlabpages.inria.fr/) over the [Flocq](https://flocq.gitlabpages.inria.fr/) IEEE-754 formalization). A wout that passes cannot misstate its residual, whatever bugs either solver contains.

## Results

53-bit intervals, 20 worker processes on a 20-core machine.

Points, six nodes per case at 8 poloidal by 4 toroidal angles (8 by 1 when axisymmetric):

| case | points | worst bound, of the field scale | verdict |
|---|---|---|---|
| `wout_solovev` (ns=55, axisymmetric, power series) | 48 | 7.3e-5 | VALID, 0.0 s |
| `wout_cma` (ns=51, 3D, nfp=2, 59 modes) | 192 | 2.9e-2 | VALID, 0.3 s |
| `wout_cth_like_fixed_bdy` (ns=25, 3D, nfp=5, 41 modes, two-power pressure) | 192 | 7.9e-3 | VALID, 0.2 s |
| `up_down_asym` (ns=17, non-stellarator-symmetric) | 48 | 6.0e-3 | VALID, 0.0 s |
| solovev, one `rmnc` node of a certified stencil perturbed by 0.1% | 48 | same claim | INVALID, 0.0 s |

Every stellarator-symmetric case above also certifies through the
non-stellarator-symmetric reconstruction with its antisymmetric coefficients
set to zero, at the same bounds. That reduction is the oracle that found
proximafusion/vmecpp#788 and jonathanschilling/educational_VMEC#27.

Pressure parameterizations. VMEC++ allows ten closed forms for the pressure
and the certificate covers all of them. Two are exercised by test files, the
power series of solovev and the two-power of cth_like; the other eight were
certified against equilibria run for the purpose, each a solovev with
`pmass_type` and its coefficients replaced:

| `pmass_type` | how the certificate carries it | verdict |
|---|---|---|
| `power_series` | `sum_j am_j s^j` | VALID |
| `two_power` | `am0 (1 - s^p)^q`, integral exponents | VALID |
| `two_power_gs` | the same times a sum of Gaussian bumps | VALID |
| `gauss_trunc` | truncated Gaussian | VALID |
| `two_lorentz` | two Lorentz factors, integral exponents | VALID |
| `pedestal` | polynomial plus a tanh pedestal, tanh from the exponential | VALID |
| `rational` | ratio of two power series | VALID |
| `cubic_spline`, `akima_spline` | the local cubic of the node's piece | VALID |
| `line_segment` | the local linear piece of the node's segment | VALID |

The same machinery reversed. `check1_lower` proves a component at least the
claimed size instead of at most, and `check_cert_lower_correct` states that a
passing verdict puts every point out of force balance by that margin. At one
node of solovev, over eight poloidal angles:

| case | proven floor | of the field scale |
|---|---|---|
| `wout_solovev` as converged, node 22 | 3.5e-8 | 6.0e-7 |
| the same node with one `rmnc` of its stencil raised by 0.1% | 4.7e-6 | 7.5e-5 |

The first is the discretization residual, proven nonzero. The second is a
proof that no field of this form balances at that node. Run it with
`main --lower`.

Over cells the same reversal is an obstruction. `check_ccert_lower_correct`
states that at every real point of a cell, not only at its centre, some
component is a real number at least the cell floor, so no field of this form
is in force balance anywhere in that cell. At node 22 of solovev, over 512
cells tiling the poloidal angle:

| case | cells proven out of balance | best floor |
|---|---|---|
| `wout_solovev` as converged | 0 of 512 | none provable |
| the same node with one `rmnc` of its stencil raised by 0.1% | 508 of 512 | 2.5e-1, against a field scale of 6.3e-2 |

The four that do not certify are where the residual passes through zero, so
no floor exists there. `main --tighten --lower --filter` drops those cells and
writes a certificate carrying only the ones that hold a claim, over which an
ordinary run returns VALID rather than a count: 508 of 508.

Cells:

| case | cells | worst cell bound | of the field scale | verdict |
|---|---|---|---|---|
| `wout_solovev` (ns=55, axisymmetric) | 49152 | 1.3e-5 | 1.9e-4 | VALID |
| `wout_circular_tokamak_reference` (ns=17, axisymmetric) | 49152 | 1.5e-2 | 2.5e-4 | VALID |
| `wout_cma` (ns=51, 3D, nfp=2, 59 modes) | 24576 | 1.3e-2 | 4.3e-2 | VALID |
| `wout_li383_low_res` (ns=16, 3D, nfp=3, 25 modes) | 24576 | 8.7e-1 | 2.4e-1 | VALID |
| `wout_li383` at 98 modes (ns=31) | 24576 | 3.1e-2 | 8.9e-3 | VALID |
| solovev cells, one `rmnc` coefficient perturbed by 0.1% | 49152 | same claim | | INVALID |

The `wout_circular_tokamak_reference` row is from an equilibrium that is not in the test data directory; every other number in this file is a case the suite runs and compares. The equilibria the convergence study needs are produced by [gen/families.py](gen/families.py), which runs VMEC++ at several radial and spectral resolutions.

The two axisymmetric cases carry six nodes of 8192 poloidal cells covering the whole angular torus; the two three-dimensional ones carry three nodes of 4096 poloidal cells at each of two toroidal angles. Normalized the same way, the pointwise bounds are 7.3e-5 for solovev, 3.4e-4 for the circular tokamak, 2.9e-2 for cma and 9.6e-2 for li383, so covering the continuum costs a factor of a few.

The solovev row is 49152 cells tightened in 35 s and checked in 39 s on twenty
cores. Most of a cell's cost is building the interval environments it needs,
and their size grows with the number of Fourier modes: the value environment
at the centre, and one derivative environment for each angle that has width.
A covering by curves therefore pays for two and a covering of a surface for
three. At forty-one modes the same twenty cores tighten 24576 cells of
`wout_cth_like_fixed_bdy` in 44 s and check them in 54 s.

## Over the volume

A cell of [theories/Cell.v](theories/Cell.v) ranges over any two distinct input
slots, and slot 0 is the radius the whole reconstruction reads, so a cell whose
two slots are the radius and the poloidal angle is a rectangle of the poloidal
cross-section rather than an arc drawn on one surface. The cell theorem does
not change and gains no hypothesis: `check_ccert_correct` already says the
bound holds at every real point of the rectangle a cell spans, whichever two
slots those are.

What had to change is the reconstruction, which was defined only on the grid.
VMEC gives every coefficient both a value and a radial derivative at every half
point, and the cubic Hermite through those four numbers reproduces both at both
ends of a node's half-grid interval, is continuously differentiable across half
points, and carries the second radial derivative the residual reads through
`tau_s`. Interpolating the coefficient linearly instead sets that second
derivative to zero for every even mode, and the certified residual then stops
falling at `6.3e-4` however fine the cells become, which measures the
interpolation rather than the equilibrium.

The Hermite is written against the secant and the two slope defects rather than
in the usual basis. The identities that make the four blending polynomials sum
to `t`, to `1` and to `0` turn the second derivative into
`((6t-4) a + (6t-2) b) / H` with `a` and `b` the defects, where the textbook
form is `(k00 ya + k01 yb) / H^2` with `k01 = -k00`. The two are the same
polynomial, but an interval evaluation adds the second form's terms
independently and encloses it to order `|y| / H^2` whatever the width of the
cell, which is no bound at all.

What a volume certificate bounds is the discretization error. The discrete
solution satisfies VMEC's discrete force balance, so the continuum residual of
a reconstruction of it measures how far that field sits from a true continuum
equilibrium, which is the content that `discretization_is_consistent` of
[theories/Hypotheses.v](theories/Hypotheses.v) otherwise has to assume.

Whole plasma, `wout_solovev` at ns=55, every interior node interval, 416 radial
by 128 poloidal cells covering the full poloidal angle, 53248 cells tightened
in 42 s and checked in 50 s, VALID:

| s | worst cell bound |
|---|---|
| 0.045 | 5.6e-1 |
| 0.12 | 1.8e-2 |
| 0.50 | 4.5e-3 |
| 0.95 | 3.1e-3 |

Cells are worth spending radially and not angularly. At node 22 the poloidal
bound is nearly flat, the worst cell only 1.7 times the median with 384 of 512
cells within a factor of two of the worst, so refining angles where the bound
is worst would buy almost nothing. Radially the spread is a factor of two
hundred, which is what `--adapt` is for.

The result is a bound as a function of radius rather than a single number. The
median cell sits at `2.8e-3` and fewer than half a percent of the cells lie
within a factor of two of the worst, all of them against the axis. Refining a
mid-radius interval keeps buying accuracy, `1.05e-3` at eight radial cells
against `1.53e-4` at a hundred and twenty-eight, while the innermost intervals
stop at `1.5e-2` however fine the covering. That plateau is the reconstruction
and not the arithmetic: the flux coordinates are singular on the axis, the
Jacobian vanishes there and the odd-m coefficients carry `sqrt(s)`, so the
region where VMEC's discretization is weakest is the region where the certified
residual is largest.

The bound over the whole plasma is set by the innermost few percent of the
flux. Excluding the region inside s = 0.10 leaves a worst case of `3.1e-2`,
and inside s = 0.14 leaves `1.9e-2`. Doubling the poloidal resolution to 256
cells, 106496 in all, tightens in 74 s and checks in 84 s and halves both
figures, to `1.5e-2` and `8.8e-3`.

Cells are worth spending against the axis. The worst cell of a whole plasma
is always an inner one, because the parity rule divides by `sqrt(s)` and the
field carries `1/(2s)` and `1/(4s^2)`, so a radial box of a given width
encloses far more loosely there. `--adapt` gives each node its own radial
resolution on that basis, four times the base count inside `s = 0.1` and twice
inside `s = 0.25`:

| covering | cells | worst bound |
|---|---|---|
| uniform, 8 radial per node | 53248 | 5.6e-01 |
| adaptive, base 8 | 73728 | 8.1e-02 |
| adaptive, base 16 | 147456 | 6.8e-02 |

which is a factor of seven off the worst bound for under half again the cells.
Spending them the other way is worse than useless: a profile four times
coarser against the axis and finer outside took the worst bound to 3.6e+02,
because refining where the bound is already the reconstruction buys nothing
while coarsening where it is the enclosure costs everything.

The thresholds `--adapt` uses were read off one equilibrium, which is the kind
of number that is right until it is not.
[gen/nrad_profile.py](gen/nrad_profile.py) measures what they stand in for, by
running a node at two resolutions and reporting how far its bound falls, and
`--adapt-from` reads that back, so the resolution can follow a measurement
instead.

The innermost interval needs a different reconstruction, and it has one. The
parity rule reads a half point as the average of the two nodes around it, odd-m
coefficients rescaled by `sqrt(s)`, so at the innermost half point one of those
nodes is the axis and the rescaling divides by zero: no half point sits below
`1.5 h` and the Hermite has nothing to interpolate between. What is defined
there is the rule that average is an instance of, the coefficient linear in `s`
for even m and `sqrt(s)` times a linear function for odd m, between two nodes.
Read at the midpoint it reproduces VMEC's half point coefficient for
coefficient; read anywhere else it is the same interpolant off the midpoint.
`--axis` takes the two innermost nodes as its knots and covers
`[0.5 h, 1.5 h]`, which is where the Jacobian's `1/(4 s^2)` stops having a
bound at all.

That interval is radially limited rather than angularly, as the factors of
`1/(2s)` and `1/(4 s^2)` say it should be:

| radial cells | worst cell bound |
|---|---|
| 8 | 7.678411e+00 |
| 32 | 2.619739e-01 |
| 128 | 5.284583e-02 |

against `4.9e+00` and `4.4e+00` for four and sixteen times the poloidal cells
at eight radial ones.

The same two-node rule reaches the other end. A covering built on half points
stops half a grid step short of `s = 1`, and the boundary is where a
free-boundary condition would be read, so `--edge` tiles between the last two
nodes instead:

```
  radius: 32 cells cover [0.981481, 1.000000] with no gap
```

at a worst cell bound of `2.2e-03`. So `wout_solovev` is certified over

| interval | covering | worst cell bound |
|---|---|---|
| [0.0093, 0.0278] | `--axis`, 128 radial cells | 5.3e-02 |
| [0.0278, 0.9907] | `--adapt`, 73728 cells | 8.1e-02 |
| [0.9815, 1.0000] | `--edge`, 32 radial cells | 2.2e-03 |

three files because the reconstruction differs between them, covering the
plasma from `s = 0.0093` to the boundary. That the three make one covering is
`covers_app` of [theories/Cover.v](theories/Cover.v), which says that coverings
meeting at a point concatenate, so the union of the three ranges is an interval
and not an assertion about three files. What is left is the innermost 0.93 per
cent of the flux, where `1/(4 s^2)` has no enclosure and the coordinates
themselves are singular.

A piecewise pressure is one cubic on each piece, so a covering that crosses a
knot needs the coefficients to change with the radius. A node block may carry
its own, and the generator splits each node's interval at the knots inside it
and gives every segment the cubic that is exact on it, so no cell ever spans
two pieces. A cubic-spline profile covered over twenty nodes, 160 radial by
128 poloidal cells, comes out VALID at a worst cell bound of `5.6e-01`, which
is the axis cell as always.

The covering is of a poloidal cross-section until a third slot is added.
`check_ccert3_correct` bounds a component at every point of a cell in three
coordinates at once, proven by composing the two-slot walk of `component_legs`
with one more mean-value leg, so no part of `Cell.v` is rebuilt. A certificate
carries the third slot on a `SLOT3` line and two more numbers per component,
the bound on the derivative along it, which `main --tighten` writes and an
ordinary run establishes:

```
the file carries a third slot 2 of half-width 3537118876014220
verdict: VALID   over three coordinates at every point of every cell
```

at a worst cell bound of `2.170772e-03`, unchanged from the two-slot covering
of the same cells. That is what an axisymmetric equilibrium should give:
`toroidal_terms_vanish` makes the toroidal derivative the zero expression, so a
cell spanning the whole torus adds nothing to the bound however wide it is, and
the covering of a cross-section becomes a covering of the volume inside the
verdict rather than beside it. A three-dimensional equilibrium pays for the
third direction in cells, since there its derivative is small rather than zero.

`--slot3 W DW` does the same widening in one run against a two-slot file, which
is quicker to try and produces a verdict rather than a certificate. The file
form is the one another party can re-check.

## The cost of a continuum bound

The bound over a cell is the value at its centre plus, for each angle, the enclosure of the angular derivative over the whole cell times the half-width. That enclosure is where the cost sits.

That enclosure does not see the cancellation that makes the residual small, so it exceeds the true derivative by orders of magnitude and comes down only as the cell narrows, at one node of solovev:

| poloidal cells per surface | half-width | worst cell bound |
|---|---|---|
| 128 | 2.5e-2 rad | 3.7e-2 |
| 512 | 6.1e-3 rad | 2.2e-3 |
| 2048 | 1.5e-3 rad | 1.3e-4 |
| 8192 | 3.8e-4 rad | 8.6e-6 |

Each refinement by four divides the bound by sixteen: the mean-value step contributes the width once and the enclosure narrows with it, so the bound falls as the square.

`check_ccert_t_correct` of [theories/Cell.v](theories/Cell.v) charges the first
varied slot differently, against the derivative at the centre, which is a thin
evaluation with no box in it, with the box paying only for a second derivative
against the square of the half-width. `main --taylor` recomputes the bounds
that way and establishes them with the extracted check. It is worth less than
the ratio of the two derivative enclosures suggests, because the
second-derivative remainder is not small at the half-widths a covering uses.
At node 22 of solovev over 256 poloidal cells:

| radial cells | mean value | Taylor |
|---|---|---|
| 8 | 2.170772e-03 | 1.826411e-03 |
| 32 | 7.289692e-04 | 7.033770e-04 |
| 128 | 4.557615e-04 | 4.527612e-04 |
| 512 | 3.997311e-04 | 3.991530e-04 |

Sixteen per cent at the coarse end, three and a half at 32, and nothing by 128,
where the ratio of the enclosures alone would have predicted a factor of five.
The remainder term is what eats it, and it is the reason to reach for more
cells rather than for a better inequality.

The other cost is building the environments, which is most of the work and
grows with the number of modes. The bindings that read neither varied slot are
the same for every cell of a node, so they are evaluated once and shared, which
the driver decides with the extracted `var_free` rather than by trusting the
order Physics.v allocates in: sharing a binding that did read a varied slot
would be wrong, and the check is what rules it out. On a 41-mode radial
covering of 8192 cells that is 124.0 s against 100.5 s, with the bounds
byte-identical.

What is left grows close to linearly in the mode count. Tightening the same
2048 cells on twenty cores:

| modes | 6 | 12 | 25 | 41 | 98 |
|---|---|---|---|---|---|
| seconds | 3.2 | 4.9 | 20.7 | 32.5 | 66.3 |

so the cost of a covering is about the cell count times the mode count. That
is what makes a three-dimensional surface expensive rather than any one step
being slow: the cells go as the product of the two angular resolutions, and the
resolutions a three-dimensional integrand needs are the ones under Integrals
over a surface. A hundred-mode stellarator surface at the resolution its
integrands resolve at is tens of minutes, and a volume of them is not reachable
this way.

An axisymmetric equilibrium has every `n` zero, so every toroidal derivative of its reconstruction is the zero expression rather than a small one, which `toroidal_terms_vanish` proves. A single cell then spans the whole toroidal angle at no cost and the covering is one-dimensional. A three-dimensional equilibrium has to resolve the toroidal direction as finely as the poloidal, which squares the count.

## What the residual is made of

The residual is a difference of three terms,

```
r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds,
```

and a verdict reports the difference and says nothing about the terms. How much
larger they are decides two things. It decides what a covering costs, since an
interval evaluation over a box encloses each term separately and loses the
difference, so the bound comes down only as the cells narrow. And it decides
which inputs the bound answers to, since a term orders of magnitude below the
others is one no bound could register.

`--terms` carries the three as the three components of a certificate, so the
same machinery that bounds the residual bounds each of them, over the same
cells at the same precision, and [gen/cancellation.py](gen/cancellation.py)
reads them at the cell where the residual is worst, which is the cell the
covering has to certify. Solovev, over 256 poloidal cells, with the half-grid
residual a point certificate carries:

| s | `(d_v B_s - d_s B_v) B^v` | `(d_s B_u - d_u B_s) B^u` | `mu0 p'` | `r_s` | cancels by | share of `p'` |
|---|---|---|---|---|---|---|
| 0.037 | 4.113684e-03 | 4.109447e-03 | 1.5712e-07 | 4.394405e-06 | 9.4e+02 | 3.6% |
| 0.167 | 5.483887e-03 | 5.484483e-03 | 1.5712e-07 | 4.388571e-07 | 1.2e+04 | 36% |
| 0.426 | 6.241478e-03 | 6.241920e-03 | 1.5712e-07 | 2.849802e-07 | 2.2e+04 | 55% |
| 0.704 | 6.928330e-03 | 6.929406e-03 | 1.5712e-07 | 9.191160e-07 | 7.5e+03 | 17% |
| 0.981 | 7.588650e-03 | 7.590921e-03 | 1.5712e-07 | 2.114136e-06 | 3.6e+03 | 7.4% |

The two magnetic terms agree to four digits and the residual is what is left.
At mid-radius the pressure gradient is more than half of it, so the certified
residual there is of the same order as the pressure the equilibrium is
balancing.

The other four equilibria do not read that way at all. At the node whose
residual is worst, solovev over the eight above and the others over five nodes
at 128 poloidal cells:

| | s | largest term | `r_s` | ratio |
|---|---|---|---|---|
| `wout_solovev` | 0.037 | 4.113684e-03 | 4.394405e-06 | 9.4e+02 |
| `wout_cth_like_fixed_bdy` | 0.083 | 1.387026e-02 | 2.827408e-03 | 4.9 |
| `wout_cma` | 0.740 | 6.538591e-03 | 6.411076e-03 | 1.02 |
| `wout_up_down_asym` | 0.938 | 1.758375e-01 | 1.887487e-01 | 0.93 |
| `wout_li383_low_res` | 0.733 | 1.570100e-01 | 2.206994e-01 | 0.71 |

For the last four there is no cancellation to lose, and for two of them the
three terms add rather than subtract: a ratio below one means the residual
exceeds every term it is built from. `wout_cma` is the clearest of the four.
Its second magnetic term runs 1.3e-04 to 2.3e-04 against a first of 4.3e-03 to
6.5e-03, a factor of twenty-five to forty, and its pressure gradient is exactly
zero, so the residual is the first term alone to within four per cent at every
node. Nothing there is a difference of anything. `wout_li383_low_res` reads
further still: at its worst cell the largest of the three terms is the pressure
gradient, and the residual is forty per cent larger again, so that
reconstruction, at twenty-five modes on sixteen surfaces, is out of balance by
more than the pressure it is meant to be balancing. What restores it is under
the mode sets below.

That is what the convergence study met as a floor flat in the radial grid. A
reconstruction whose terms are not close to each other is not near pointwise
force balance, and no refinement of the covering reaches that. What a covering
can still do there is bound it, which is the difference between suspecting the
reconstruction and having a number for how far out it is.

Adding modes does two different things to that, and the terms tell them apart.
For `wout_cth_like_fixed_bdy` at ns = 51 with the radial grid held fixed, over
three mode sets:

| s | | 5 by 4 modes | 7 by 6 | 9 by 8 |
|---|---|---|---|---|
| 0.04 | larger term | 1.79e-02 | 1.77e-02 | 1.77e-02 |
| | `r_s` | 2.678e-03 | 2.460e-03 | 2.316e-03 |
| | cancels by | 6.7 | 7.2 | 7.6 |
| 0.34 | larger term | 1.26e-02 | 1.82e-02 | 1.29e-02 |
| | `r_s` | 1.146e-03 | 6.947e-04 | 4.647e-04 |
| | cancels by | 11 | 26 | 28 |
| 0.98 | larger term | 2.23e-03 | 3.65e-04 | 6.48e-04 |
| | `r_s` | 1.879e-03 | 3.950e-04 | 3.620e-04 |
| | cancels by | 1.2 | 0.9 | 1.8 |

At the edge the terms themselves fall by a factor of three to six and the
residual falls with them, and no cancellation ever appears. In the middle the
terms stay the size they were and the cancellation sharpens from eleven to
twenty-eight, which is where the residual's factor of two and a half comes
from. Near the axis neither moves much. So the two halves of the mode scan below, a factor of ten
at the edge and almost nothing near the axis, are not one effect at two
strengths: at the edge the spectrum is resolving the boundary shaping and the
terms come down, while in the middle it is sharpening a difference that was
already being taken.

For `wout_li383` at ns = 31 the same experiment says the imbalance is spectral
outright:

| s | | 25 modes | 50 | 98 |
|---|---|---|---|---|
| 0.37 | `r_s` | 1.929803e-01 | 2.826110e-02 | 4.765804e-03 |
| | cancels by | 1.5 | 3.2 | 19 |
| 0.67 | `r_s` | 2.398645e-01 | 4.410154e-02 | 9.133677e-03 |
| | cancels by | 1.7 | 3.6 | 17 |

At twenty-five modes nothing cancels anywhere and the residual is the size of
the largest term it is built from; at ninety-eight the mid-radius cancellation
is a factor of nearly twenty and the residual has fallen by twenty-six to
forty. So the ratio is a resolution indicator in its own right, and a
scale-free one: it says how nearly the two magnetic terms are the same number,
where the residual alone says only how large their difference is. Solovev sits
at 1e+03 to 1e+04, li383 at ninety-eight modes at seventeen to nineteen,
li383 at twenty-five modes and `wout_cma` at one.

What the solver reports about itself does not predict any of that. `fsqr` is
VMEC's own force residual in its own discrete norm, the quantity the iteration
drives down to `ftol` and stops:

| | modes | `fsqr` | cancels by |
|---|---|---|---|
| `wout_solovev` | 6 | 9.4e-13 | 9.4e+02 to 2.2e+04 |
| `wout_up_down_asym` | 5 | 9.5e-12 | 0.57 to 3.5 |
| `wout_cth_like_fixed_bdy` | 41 | 9.3e-07 | 0.98 to 13 |
| `wout_cma` | 59 | 9.9e-07 | 1.02 to 1.05 |
| `wout_li383_low_res` | 25 | 8.8e-07 | 0.65 to 1.6 |

`wout_up_down_asym` stopped six orders further down than the three below it and
still has no cancellation; `wout_cth_like_fixed_bdy` and `wout_cma` stopped at
the same place and differ by a factor of ten. The two numbers are measuring
different things. `fsqr` says the iteration stopped moving in the discrete
equations it was given; the cancellation says how nearly the field those
equations produced satisfies the continuum equation they stand in for. A wout
carries the first and not the second, and a covering supplies the second.

`wout_cma` is worth one more line, since it is the flattest of them. It carries
no pressure and no net toroidal current at all: its `presf` is identically zero
and `max|buco|` is 1.1e-17, against a `bvco` of 0.48. So there is nothing in it
for the two magnetic terms to be balanced against each other by, and the
certified residual is the first of them alone.

Read as one number per equilibrium, over four nodes each at 128 poloidal cells,
the ranking is:

| | median cancellation |
|---|---|
| `wout_solovev` | 6.6e+03 |
| `wout_li383` at 98 modes | 9.5 |
| `wout_cth_like` at 9 by 8 modes | 4.7 |
| `wout_cth_like_fixed_bdy` at 41 modes | 3.2 |
| `wout_up_down_asym` | 1.4 |
| `wout_li383_low_res` at 25 modes | 1.2 |
| `wout_cma` | 1.0 |

The median rather than the worst, because the axis and the edge cancel least on
every stellarator here and a minimum would report those and nothing else. That
column is a certified statement about each reconstruction, in the same units
for all of them, and it is the thing a wout does not carry.

Going off the grid moves the cancellation and not the terms. At node 22 of
solovev, at the same angular resolution, over the eight radial cells of the
free-radius reconstruction:

| | the two terms | `r_s` | cancels by | share of `p'` |
|---|---|---|---|---|
| half grid, s = 0.4074 | 6.24e-03 | 2.85e-07 | 2.2e+04 | 55% |
| free radius, s = 0.399 to 0.416 | 6.17e-03 to 6.25e-03 | 5.1e-06 to 3.4e-05 | 1.8e+02 to 1.2e+03 | 0.5% to 3% |

The terms are the same size either way; what the Hermite costs is two orders of
magnitude of cancellation, which is the two orders the residual gains. And
because the residual grows while the pressure does not, a volume covering is
nearly blind to the pressure: at these radii the pressure gradient is under
three per cent of the bound.

`discretization_is_consistent` of
[theories/Hypotheses.v](theories/Hypotheses.v) is the premise every statement
about the continuum problem rests on, and it is stated there as a property of a
function of the grid spacing. That function is one this development computes:
the discrete solution satisfies VMEC's discrete equations exactly, so the
continuum residual of a reconstruction of it is the truncation error, and
running the same equilibrium at several resolutions measures the order instead
of assuming it. [gen/convergence.py](gen/convergence.py) does that, against the
value at a cell centre rather than the cell bound, since the cell bound also
carries an enclosure width that narrows on its own and would flatter the
result.

Solovev at twelve poloidal modes, at s = 0.5, with the residual a point
certificate carries, which uses VMEC's own centred differences and no
interpolant:

| ns | h | residual | order |
|---|---|---|---|
| 13 | 8.3e-02 | 2.725491e-06 | |
| 25 | 4.2e-02 | 7.023493e-07 | 1.96 |
| 51 | 2.0e-02 | 1.697439e-07 | 1.93 |
| 101 | 1.0e-02 | 6.100972e-08 | 1.48 |
| 201 | 5.0e-03 | 5.452347e-08 | 0.16 |

Second order, until it stops. What it stops at is the spectral floor, which no
radial refinement reaches below: at six modes the same family flattens at
`2.9e-07` by ns = 51, and holding ns = 101 while adding modes takes the
residual from `1.0e-05` at four modes to `2.9e-07` at six, `1.4e-07` at ten and
`6.1e-08` at twelve. A family that flattens is at its floor rather than out of
order, and the two are told apart by holding one resolution and moving the
other.

That makes the certified residual a diagnostic and not only a bound, and the
two equilibria answer differently. `wout_li383_low_res` carries the weakest
bound in the results table, and refining its radial grid does nothing at all:

| | ns 16 | ns 31 | ns 61 | ns 121 |
|---|---|---|---|---|
| residual at s = 0.5 | 3.846650e-01 | 4.104654e-01 | 4.104946e-01 | 4.174291e-01 |

while holding ns = 31 and enlarging the mode set takes it from `4.10e-01` at 25
modes to `8.39e-02` at 50 and `1.82e-02` at 98. The weakest certificate in this
file is weak because the equilibrium is spectrally under-resolved, and the
residual says so rather than leaving it to be guessed.

The two stellarators in the test set read like li383 and not like solovev. At
`s = 0.5`, with the mode set fixed:

| | coarsest | ns 25 | ns 51 | ns 101 | order |
|---|---|---|---|---|---|
| `wout_cma`, 59 modes | 5.294495e-03 | 5.280118e-03 | 5.180345e-03 | 5.030916e-03 | 0.03 |
| `wout_cth_like`, 41 modes | 3.646375e-03 | 3.334345e-03 | 3.175774e-03 | 3.109791e-03 | 0.07 |

Flat, from the coarsest grid the case runs on to a hundred surfaces. Adding
modes moves cth_like, but not far: 41 to 85 modes buys 1.74, and 85 to 145
another 1.21, leaving it at `1.5e-03` against a field scale of `4.8e-01`. So
neither knob reduces the certified residual of a reconstruction of these
equilibria by an order of magnitude over the ranges tried, where the same
machinery on solovev reaches `6.1e-08` against a scale of `5.8e-02`. All three
components carry it, the radial one largest by two to three times, so it is not
one equation failing.

A single number for an equilibrium hides where it comes from, so
[gen/radial_scan.py](gen/radial_scan.py) certifies it surface by surface. For
cth_like at ns = 51, against two mode sets:

| s | 41 modes | 145 modes | what modes buy |
|---|---|---|---|
| 0.04 | 2.678e-03 | 2.316e-03 | 1.2 |
| 0.16 | 6.390e-04 | 2.014e-04 | 3.2 |
| 0.44 | 2.665e-03 | 1.074e-03 | 2.5 |
| 0.70 | 4.608e-03 | 1.587e-03 | 2.9 |
| 0.84 | 5.850e-03 | 5.495e-04 | 10.6 |
| 0.98 | 7.484e-03 | 8.923e-04 | 8.4 |

The residual grows outward, and modes buy an order of magnitude at the edge
and almost nothing at the axis. So the stellarator floor is the edge, where the
shaping is sharpest and the mode set is what resolves it, while the innermost
surface is the near-axis reconstruction and answers to neither knob, which is
what the mode scan at `s = 0.03` said as well. The advice a plasma physicist
would take from it is to spend modes rather than surfaces, and that the edge is
where they land.

It is not an island. The residual takes no notice of the surfaces where iota
crosses 5/4 or 1, both of which are resonances of a five-period device and both
of which lie inside this equilibrium: it rises smoothly through them. Had it
peaked there, `resonance_and_island_width` of
[theories/Hypotheses.v](theories/Hypotheses.v) is the reading that would apply,
and the scan prints the distance to the nearest resonance beside each surface
so that the question can be asked of any equilibrium.

Near the axis the answer is the third one. At s = 0.03 the free-radius residual
is `1.74e-02` at four, six, eight and twelve modes alike, unmoved to three
digits, so the plateau there is neither the grid nor the spectrum but the
reconstruction, which is what the parity rule's `sqrt(s)` and the `1/(2s)` and
`1/(4s^2)` of the field make it.

The reconstruction has a price of its own away from the grid. At the same
equilibrium, resolution and radius, the residual of the free-radius
reconstruction is `8.5e-06` against `6.1e-08` for the half-grid one at the
node. The Hermite reproduces VMEC's value and radial derivative at the half
points and interpolates between them, and its second radial derivative is built
from slope defects divided by the spacing, so an error of order `h^2` in the
endpoint slopes arrives as order `h`. Going off the grid costs two orders of
magnitude here, and that is a property of the interpolant rather than of the
equilibrium.

## Integrals over a surface

A cell certificate tiles the angular torus, so the same per-cell data encloses
an angular integral. `midpoint_sharp` bounds the error of the midpoint rule
over one cell by `2 M2 h^3`, with `M2` the second derivative enclosed over the
cell, and `tiling_encloses` adds the cells up. The linear part of the Taylor
step integrates to zero over a centred cell, which is what makes the bound one
order sharper than the first-derivative form. Measured on one node of solovev:

| poloidal cells | quadrature error |
|---|---|
| 32 | 2.7e+0 |
| 64 | 1.5e-1 |
| 128 | 1.2e-2 |
| 256 | 1.3e-3 |
| 512 | 1.5e-4 |

The ratios settle near eight per doubling: the cube of the half-width, with
the second-derivative enclosure narrowing alongside it.

When both angles of a cell carry width the rule is the iterated one.
`cell_iterated_encloses` bounds the error over one cell by
`4 Muu hu^3 hv + 4 Mvv hu hv^3`, and `tiling2_encloses` sums a rectangle of
them. The two directions are separated before either is estimated, so no mixed
partial derivative enters and the error stays second order in each half-width;
what the separation costs is the integrability of the inner integral in the
outer angle, which `lipschitz_ex_RInt` supplies from the first derivative the
cell already bounds. This is what makes an integral a statement about a
surface rather than about one curve drawn on it.

The averages come out where the wout says they should. At node 22 of solovev,
over 512 poloidal cells and one toroidal cell covering the whole torus:

| quantity | certified interval | wout |
|---|---|---|
| `dV/ds` = integral of sqrt(g) du dv | [-1.2622140e+02, -1.2622027e+02] | -1.2622084e+02 |
| integral of B_u du dv, four pi squared times the enclosed current | [1.4419077e+00, 1.4420428e+00] | 1.4419870e+00 |

The Jacobian is negative because `signgs` is -1. The wout column is
`4 pi^2 signgs vp` and `4 pi^2 buco` from the same file, which the proof
brackets to six and five significant digits.

A three-dimensional surface costs far more, since the toroidal direction has
to be resolved as finely as the poloidal. At node 12 of
`wout_cth_like_fixed_bdy`, over the whole angular torus:

| quantity | 128 by 80 cells | 256 by 160 cells | wout |
|---|---|---|---|
| `dV/ds` | [-3.3531084e-01, -3.0267062e-01] | [-3.2135415e-01, -3.1662730e-01] | -3.1899044e-01 |
| `int sqrt(g) B^2` | straddles zero | [-1.1807642e-01, -8.4862011e-02] | |
| `int B_u` | straddles zero | [-3.5629855e-01, -2.2848687e-01] | -2.7439e-01 |

Four times the cells takes the Jacobian from about five per cent of the file's
own `4 pi^2 signgs vp` to under one, and it is what the two integrands carrying
the field need to resolve at all: at the coarse resolution their enclosures
straddle zero, which is what a covering too coarse for the cancellation looks
like, and at the fine one they are bounded away from it. The cost is 40960
cells at 41 modes.

## Mercier

`OUTPUT mercier-a` and `mercier-b` carry the four angular integrands whose
integrals over the torus are the Mercier terms `tpp`, `tbb`, `tjb` and `tjj`
of `mercier.f90`, in its normalization: the Jacobian divided by
`2 pi phip signgs`, the current as `mu0 J.B`, and the weights that VMEC sums
with folded into the integral. The sign is carried without a `signgs` input,
since `signgs` is `sqrt(g)/|sqrt(g)|` and the square root of a square supplies
the modulus.

At node 22 of solovev over 512 cells covering the torus:

| term | certified interval |
|---|---|
| `tpp` | [-3.2877096e+03, -3.2875073e+03] |
| `tbb` | [-5.0854798e+00, -5.0845371e+00] |
| `tjb` | [ 2.8065041e+00,  2.8130834e+00] |
| `tjj` | [-1.5697052e+00, -1.5354778e+00] |

### The magnetic well, and DMerc

`V''` used to be out of reach, since it is a radial derivative of a surface
average and no single surface holds one. With the radius a varied slot the
average is a function of it, and `diff_under_integral` of
[theories/Quad.v](theories/Quad.v) says that function is differentiable with
derivative the integral of the derivative, licensed by a second derivative
bounded over the cell. So the integral of `d(sqrt g)/ds`, which the free-radius
reconstruction supplies, is `V''`.

At node 22 of solovev, over 512 angular cells:

| quantity | certified interval | wout |
|---|---|---|
| `dV/ds` | [-1.2615392e+02, -1.2615279e+02] | -1.2615340e+02 |
| `V''` | [-7.2359141e+00, -7.2336213e+00] | -7.2836761e+00 |
| `mu0 p'` | -6.2012553e-06 | -6.2012553e-06 |
| `iota'` | [-7.1e-13, 7.1e-13] | 0 |

`dV/ds` lands on the file's own number. `V''` does not, and the gap is the
point rather than a discrepancy: the certified figure is the exact radial
derivative of the reconstruction, while VMEC's is a centred difference quotient
across a grid spacing. Differencing the certified `dV/ds` at nodes 21 and 23
gives -7.28366, which reproduces the file's -7.2836761 to six digits, so the
two agree wherever they compute the same thing and the 0.68 per cent between
them is that quotient's own discretization error, now measurable because both
quantities are in hand.

`mu0 p'` and `iota'` are flux functions rather than integrals, and the
machinery that certifies them integrates them over the angles like everything
else, so what comes back is four pi squared times the value. That factor is
where it belongs, in the assembly below, rather than hidden in the generator.

With `V''` certified, every term of the Mercier criterion is, and the
combination is inside the checker rather than beside it.
[theories/Mercier.v](theories/Mercier.v) takes the ten enclosures a covering
produces, evaluates `mercier.f90`'s own formulas with the same sound interval
arithmetic, and `mercier_encloses` states that the result contains the
criterion of any reals inside those enclosures. `gen/mercier.py` runs the four
coverings, transfers the endpoints in hexadecimal, which round-trips exactly,
and hands them over; no arithmetic between the certified integrals and the
verdict happens outside the extracted code.

The normalization is `mercier.f90`'s. It works in the flux variable, so every
radial derivative is divided by `phip_real = 2 pi phips signgs`, and the
surface quantities are averages times four pi squared, which is the integral
over the torus a cell certificate encloses. What a covering reports carries one
more factor for the flux functions, as above. The result is checked against the
file's own `DShear`, `DCurr`, `DWell` and `DMerc` rather than argued from the
source.

At node 22 of solovev, flat iota and finite pressure:

| term | certified interval | wout |
|---|---|---|
| `DShear` | [-8.09e-29, 8.09e-29] | 0 |
| `DCurr` | [-7.48e-17, 7.48e-17] | 0 |
| `DWell` | [-5.780644e-06, -5.777741e-06] | -5.8182772e-06 |
| `DGeod` | [-1.062392e-01, 1.062447e-01], and at most 0 | -8.5683e-10 |

```
verdict: UNSTABLE   DMerc <= -5.776330e-06 on this surface
```

The enclosure of `DGeod` straddles zero however fine the covering, for the
reason below, so a two-sided bracket on `DMerc` is worthless.
`mercier_geodesic_nonpositive` supplies the sign the arithmetic cannot, and
what the checker then proves is one-sided: `DMerc` is at most the margin
printed. That is the statement the criterion needs, and it is machine-checked
rather than computed. The 0.65 per cent between the certified `DWell` and the
file's is the `V''` difference above, carried through.

At node 8 of `wout_up_down_asym`, strong shear and no pressure, where the terms
solovev cannot exercise are the ones that decide it:

| term | certified interval | wout |
|---|---|---|
| `DShear` | [2.934028e-03, 2.934028e-03] | 2.934028e-03 |
| `DCurr` | [-6.581545e-04, -4.994278e-04] | -5.358950e-04 |
| `DWell` | [-8.79e-295, 8.79e-295] | 0 |
| `DGeod` | [-1.650933e-03, 1.215395e-03] | -1.916086e-04 |

```
verdict: STABLE   DMerc >= 6.247875e-04 on this surface
```

with the file's `DMerc` of 2.206524e-03 inside the certified
[6.249401e-04, 3.649995e-03]. `DShear` reproduces the file exactly at the
printed precision, which is the check that the normalization is VMEC's own and
not one that happens to work at flat iota. A proof of stability is harder to
come by than a proof of instability, since the geodesic term has to be enclosed
rather than signed, and here the covering was fine enough.

### A profile, and what it exposes

The four coverings carry every surface at once, so a whole profile costs four
runs rather than four per surface. `--profile N` does that and assembles the
criterion at each. Solovev over twenty surfaces at 256 poloidal cells:

```
18 surfaces proven unstable, 0 proven stable, 2 undecided by this covering
```

with the margins tracking the file's own `DMerc` to under half a per cent from
`s = 0.28` outward, and the two undecided surfaces the innermost, where the
free-radius reconstruction is weakest. `wout_up_down_asym`, which has shear and
no pressure, needs four times the cells before anything can be proven at all,
since a verdict of stability has to enclose the geodesic term rather than sign
it: at 256 cells every surface is undecided, and at 1024 seven of eight are
proven stable.

The eighth is worth the space. At `s = 0.125` the certified criterion says
`DMerc <= -7.678595e-04` while the file says `+1.805619e-03`, and both are
right about the object they describe.

Every term of the criterion is a difference of larger numbers, so the profile
reports what a relative error in each input does to the result: a one per cent
error in that input moves `DMerc` by that many per cent of itself. For
`wout_up_down_asym`, which has shear and no pressure:

| s | verdict | `V''` | current gradient | averages |
|---|---|---|---|---|
| 0.125 | `DMerc <= -7.68e-04` | 0.0 | 181.8 | 2.1e+03 |
| 0.188 | `DMerc >= +6.30e-04` | 0.0 | 64.1 | 4.6e+02 |
| 0.438 | `DMerc >= +1.93e-03` | 0.0 | 11.8 | 25.7 |
| 0.688 | `DMerc >= +2.35e-03` | 0.0 | 4.2 | 3.8 |
| 0.938 | `DMerc >= +4.27e-03` | 0.0 | 0.8 | 0.6 |

At the innermost surface a one per cent error in the current gradient is 182
per cent of the criterion. The gradient behind it is an exact radial derivative
of the reconstruction here and a difference quotient across a grid spacing in
the file, and at that surface of a seventeen-surface equilibrium the two differ
by 2.2 per cent. Substituting the file's value for ours in the assembly, and
changing nothing else, moves the verdict:

| current gradient | verdict |
|---|---|
| exact derivative of the reconstruction, 1.2109e+01 | `DMerc <= -7.678595e-04` |
| the file's difference quotient, 1.1848e+01 | `DMerc >= +1.268904e-03` |

So the sign of `DMerc` at that surface is not a property of the equilibrium at
that resolution; it is a property of which radial derivative is meant. Solovev
reads the other way: flat iota puts the current gradient's factor at zero, the
`V''` factor is 1.0, and the criterion there is as well determined as `V''` is.
The averages carry factors of a million on that equilibrium, which is the
quantitative form of the statement below that no enclosure of them decides
`DGeod`.

A floating-point code computes one of these numbers and reports it. What a
certified one can say is which of them the data determines.

A stellarator is out of reach at this scale, and the run says where the wall
is rather than leaving it to be guessed. At node 12 of
`wout_cth_like_fixed_bdy`, a covering of 128 by 64 cells leaves the surface
averages straddling zero; at 192 by 96 the tightening refuses outright, since
a cell that wide lets the Jacobian straddle zero and no bound follows; at 256
by 160 it succeeds, taking about half an hour for one of the four coverings and
running into hours for the integral, whose integrands carry `gpp` and `J.B` and
so need second derivatives in both angles of a far heavier expression than a
geometry integrand. Four coverings like that is a day's work for one surface.
The criterion of a stellarator is reachable by this machinery and not
affordable by it.

`Dgeod = tjb^2 - tbb tjj` is a different matter. Its two terms both sit near
7.895 and their difference is ten orders smaller, so no enclosure of the three
averages decides its sign however fine the covering. The sign follows from an
inequality instead. With `w = gpp gf`, `f = mu0 (J.B)/|B|` and `g = |B|`, the
three integrals are `<f g w>`, `<g^2 w>` and `<f^2 w>`, so `Dgeod` is exactly
the Cauchy-Schwarz defect, and `mercier_geodesic_nonpositive` proves it is
never positive for a weight of either constant sign. The wout agrees, with
`DGeod` at -8.6e-10 on that surface.

## Toward Boozer coordinates

The Boozer angles differ from VMEC's by a stream function w with

```
B_u = I(s) + d_u w,   B_v = G(s) + d_v w,
p = w / (G + iota I),   theta_B = u + lambda + iota p,   zeta_B = v + p
```

and two things have to hold before any of that means anything. The first is
that w exists at all, which needs the covariant components to have no curl on
the surface, `d_u B_v - d_v B_u = mu0 sqrt(g) J^s = 0`. That is the same
quantity `r_u` and `r_v` already bound, so the precondition of the
transformation is certified by the machinery that certifies force balance. The
second is the coefficients themselves, which are angular integrals of the
covariant components against a kernel. `--covariant m,n` carries `B_u`, `B_v`
and the surface current against `cos(mu - nv)`, `--covariant-sin` against the
sine, and [gen/boozer.py](gen/boozer.py) turns the enclosures into the flux
functions and w.

At node 22 of solovev, over 512 poloidal cells:

| quantity | certified interval | wout |
|---|---|---|
| `I(s)` | [3.652394960e-02, 3.652737132e-02] | `buco` 0.03652596 |
| `G(s)` | [7.746387749e-01, 7.746458875e-01] | `bvco` 0.77464241 |
| `w` at (1, 0) | [-5.906405371e-03, -5.897881614e-03] | |
| `w` at (2, 0) | [7.669562333e-03, 7.679174168e-03] | |

Both flux functions bracket the file's own numbers. Every mode also carries the
defect `n a + m c`, which vanishes exactly when the surface current harmonic
does, and every certified enclosure of it brackets zero; for an axisymmetric
equilibrium that reads as the `B_v` harmonics vanishing at every `m`, which is
what the enclosures say.

w has no closed form as an expression, since `B_u` is not a finite Fourier sum,
so it is computed in floating point and written into the certificate as data.
What makes that usable is that the two relations defining it are then bounded
over the surface. At the same node, over 512 cells:

| | at most |
|---|---|
| `d_u w - (B_u - I)` | 2.196122e-05 |
| `d_v w - (B_v - G)` | 2.597591e-04 |
| `mu0 sqrt(g) J^s` | 8.391989e-04 |

The third is what has to vanish for any stream function to exist at all, so a
defect at that level is as close as the surface allows, not as close as the
float pass managed.

With w in hand the angles are explicit, and the harmonics of `|B|` in them are
angular integrals of `|B| cos(m theta_B - n zeta_B)` against the Jacobian of
the angle map. `--boozer m,n` carries that integrand:

| (m, n) | certified harmonic |
|---|---|
| (0, 0) | [2.053361982e-01, 2.053437394e-01] |
| (1, 0) | [-3.419773053e-02, -3.416280432e-02] |
| (2, 0) | [1.722968111e-03, 1.827496726e-03] |

with every sine component bracketing zero, as stellarator symmetry says they
must. The run checks itself as it goes: the Jacobian of the angle map is
carried as a third component and its integral has to be `4 pi^2`, because the
map is a bijection of the torus, and the certified enclosure
[3.947814393e+01, 3.947869128e+01] brackets it.

There is a cost in the way of doing this for a stellarator. A
three-dimensional surface needs a far finer covering for these than a residual
bound does, because the integrands do not cancel: at node 12 of
`wout_cth_like_fixed_bdy` a 128 by 64 covering leaves `G` enclosed as
[-2.8e+00, 1.9e+00], which says nothing at all, while 256 by 160 gives
[-4.7e-01, -4.3e-01] and puts the (1, 0) coefficient of `B_u` at
[2.36e-03, 6.84e-03], away from zero. A quasi-symmetry residual is that again
for every symmetry-breaking mode.

## What a floor verdict excludes

`check_ccert_lower` proves some component bounded away from zero at every point
of a cell, which is an obstruction: no field of the certified form is in force
balance anywhere there. A cell varies any two input slots and nothing in
`Cell.v` is about angles, so one of them may be a Fourier coefficient. The
floor is then proven over a rectangle of coefficient and angle, and what it
excludes is every field whose coefficient lies in that interval.

At node 22 of solovev, over one `rmnc` coefficient displaced by 0.1 per cent
and given a half-width of 0.05 per cent, and the whole poloidal angle in 256
cells:

```
231 of 231 cells proven out of force balance at every angle they cover
```

The box has to exclude the converged value, since a box containing it contains
a field that does balance, and the twenty-five cells that carry no floor are
where the residual passes through zero. This is as far as the obstruction goes:
it excludes a family of reconstructions, not a family of equilibria, since a
true solution near those coefficients need not be of this form.

## What the reconstruction satisfies

These are properties of the assembled series rather than claims about a
particular file, so they hold at every point at once and a floating-point code
can only test them at samples.

| theorem | statement |
|---|---|
| `divergence_free` | div B is exactly zero, not small |
| `pressure_is_a_flux_function` | dp/ds reads neither angle, for every parameterization the checker admits |
| `toroidal_terms_vanish` | with every n zero, every toroidal derivative of an assembled series is exactly zero |
| `lambda_gauge` | the m = 0, n = 0 coefficient of lambda drives nothing, so adding a function of s to lambda leaves the field where it was |
| `assemble_value_zero` | a series whose coefficients vanish contributes nothing, which is the lasym reduction |
| `mercier_geodesic_nonpositive` | the geodesic-curvature term of the Mercier criterion is never positive |

## Correspondence

A verdict is a theorem about the mantissas and exponents the checker was
handed. Two questions sit between that and a statement about a wout file, and
they have different answers.

Whether the cells the file lists leave a gap is now decided rather than
argued. [theories/Cover.v](theories/Cover.v) defines `covers`, a boolean over
the centres and half-widths a certificate already carries, and proves that a
true verdict puts every real of the range inside one of the cells;
`check_ccert_over_range` combines it with the cell theorem, so a certificate
that claims a range and leaves a hole in it is rejected the way one with a
bound that is too small is rejected. The checker prints what it establishes,
and a certificate covering scattered node intervals rather than a contiguous
plasma says so:

```
  radius: 208 cells cover [0.027778, 0.990741] with no gap
  poloidal angle: 64 cells cover [0.000000, 6.283185] with no gap
```

An integral is a statement about a tiling, so `--integrate` checks for one
rather than assuming it, and which theorem it appeals to depends on the
covering. `tiling_var_encloses` sums cells that tile a range with each cell
carrying its own width, which is what a covering by curves is and what lets one
refine where it needs to; `tiling2_encloses` sums a rectangle of cells of a
common width in each angle, which is what a surface covering is and which does
need them uniform. A covering that leaves a gap is refused either way, and a
surface covering whose cells differ in width is refused as well. An angle of no
width at all is not refused: the run then reports an integral per plane rather
than one over a surface, which is a different statement and an honest one.

The generator lays its cells out in integer mantissa units, cell k centred at
(2k+1)d with half-width d, so the tiling the quadrature theorems assume is the
tiling the file contains. Choosing the centres in radians and rounding them
onto the dyadic grid afterwards leaves consecutive cells a fraction of an ulp
apart, far too little to matter numerically and enough to put them outside the
theorem.

Whether the numbers are the ones in the wout is the second question, and the
proof does not answer it. The theorem quantifies over the mantissas it is
given, so nothing in it ties slot 4 to the wout's `s_{j-1}`, the coefficient
rows to the modes on the `MODES` line, or the `SLOTS` line to the slots the
generator meant. A generator that transposed an array would certify a
different object and the checker would pass it, correctly.

[gen/verify_cert.py](gen/verify_cert.py) answers it from the other side. It
reads the wout and the certificate with its own parser and its own indexing
and compares every input slot: the radii, iota, phip, the pressure
coefficients, the mode list, and every coefficient of every block. Swapping
two entries of one `RNODES` row is reported as

```
node 22 RNODES row 21 mode 0: certificate 0.6326663853742209, wout 3.9930499170572427
node 22 RNODES row 21 mode 1: certificate 3.9930499170572427, wout 0.6326663853742209
```

and a genuine solovev certificate, which the checker calls VALID because it
is, is rejected when asked whether it describes `wout_cma`.

Every form the generator writes is read, which is what makes the guard cover
the verdicts rather than a subset of them: a radial covering repeats a node
with `SAME` and carries its own pressure piece on an `AMLOCAL` line, a stream
function arrives with its two flux functions beside it, a third slot adds two
numbers to every bound line, and four of the outputs put a mode pair on the
`OUTPUT` line. Two of those blocks the wout constrains only indirectly, and
both are read against it anyway. A node's local pressure cubic comes from a
reimplementation of VMEC's spline, so it is evaluated at the node's radius and
compared with the file's own `presf`, which VMEC computed from its own; the two
flux functions beside a stream function are compared with `buco` and `bvco`.

The suite runs the guard in both directions and in three adversarial ones. It
takes a certificate the guard accepts and swaps two entries of one coefficient
row, in a surface covering and in a radial one where the coefficients are
written once and repeated; and it rescales a node's pressure cubic. Those are
the errors a transposed array and a calibration read from the wrong quantity
would make, and they are the ones no verdict of the checker could ever notice.
What the guard does not do is verify the generator: it verifies the artifact,
which is what a reader of a certificate has in hand, and it is unverified
Python whose mistakes would correlate with the generator's.

Three more guards sit beside it. The physics of the reconstruction is written
twice, once as expression builders in `Physics.v` and once as ordinary floating
point in [proto/continuum_ref.py](proto/continuum_ref.py), for the free-radius
residual and for the half-grid one a point certificate carries; the suite
requires the checker to accept a bound a hair above what the reference says and
to reject one just below it, which brackets the certified enclosure against a
number nothing in the development produced twice.

Both of those are by the same hand, so a third reaches outside it. At a half
point the wout stores `B^u`, `B^v` and `sqrt(g)` as Nyquist series that VMEC
computed itself, and the reconstruction has to reproduce them:

| | worst relative difference |
|---|---|
| `wout_solovev` | 8.9e-07 |
| `wout_cth_like_fixed_bdy` | 7.9e-06 |
| `wout_cma` | 8.9e-05 |
| `wout_up_down_asym` | 1.8e-04 |
| `wout_li383_low_res` | 1.8e-02 |

across both symmetry classes and both dimensionalities, which is where an
encoding slip would hide. What is left over is the difference between an exact
product of series and the Nyquist fit VMEC stores for it, and it grows with how
badly the mode set resolves the equilibrium, which is why li383 is last. And a converged equilibrium
is not much of an adversary, so the suite perturbs one coefficient of `rmnc`,
`zmns` or `lmns` and reads the perturbed coefficients against the unperturbed
claim, down to a part in a hundred thousand, where the verdict has to be
INVALID.

## Trust base

- the Rocq proof kernel (rocq-core 9.1.1 with coq-stdlib 9.2.0), checked with `Print Assumptions` over every theorem of [theories/Audit.v](theories/Audit.v). `make audit` prints that, and [test/audit_summary.py](test/audit_summary.py) reads it rather than leaving it to be counted by hand: it reports what stands behind each theorem and fails on any axiom outside the families named here, which are the classical real axioms of the standard library and the primitive integer and float specifications, and nothing else. The counts are not quoted in this file, because a number here would be a copy of one the audit already prints and would go stale the first time a theorem is added;
- CoqInterval 4.11.4 and Flocq 4.2.2, whose proofs the kernel checks like ours;
- Coquelicot 3.4.5 for the integrals of [theories/Quad.v](theories/Quad.v);
- the two OCaml runtime shims for primitive integers and floats (`uint63.ml`, `float64.ml` from rocq-runtime, the same realization the Rocq kernel itself trusts) and the C stubs archive they bind to;
- the extraction mechanism and the OCaml compiler;
- the unverified driver ([driver/main.ml](driver/main.ml)) and generator ([gen/make_cert.py](gen/make_cert.py)). The parse is read twice by two implementations in two languages, since gen/verify_cert.py reads the same file with its own parser and compares it against the wout, and the split of the work over processes is checked rather than trusted: each shard reports how many cells it visited and the total has to be the cell count, so a split that lost cells is a failed run rather than a passing verdict. These divide into two parts with different consequences. The bounds the driver writes under `--tighten`, and the split of the work over processes, are claims the checker then has to establish, so an error there costs a rejected certificate and not a wrong theorem. The construction of the environment is the other part and carries more weight: the theorem quantifies over the mantissas and exponents it is given, so nothing inside the proof ties slot 4 to the wout's `s_{j-1}`, the coefficient rows to the modes named on the `MODES` line, or the `SLOTS` line to the slots the generator meant. A generator that transposes an array certifies a different object and still returns VALID. What guards that correspondence is stated under Correspondence;
- a post-extraction patch ([gen/patch_extract.py](gen/patch_extract.py)) that replaces the bodies of the spec-only classical-real constants with poison values and adds one `open`; the diff is part of the audit surface, and the suite checks it, requiring every stub and every branch extraction itself marked unreachable to lie inside the classical-real modules the checker never enters.

## Layout

- `theories/Expr.v` - expression language, extended-real semantics, interval interpreter, the soundness proof, and bindings (shared subexpressions stored in environment slots, with the proof that extending both environments by the same bindings preserves containment)
- `theories/Physics.v` - the residual as expression builders on VMEC's grid (definitional; the auditable physics), the ten pressure parameterizations, the flux-surface integrands, the Mercier integrands, and the reconstruction at a free radius that carries the residual off the grid
- `theories/Checker.v` - certificates, `check_cert`, `check_cert_correct`
- `theories/Deriv.v` - symbolic differentiation of expressions with its soundness (the chain rule over extended reals, and derivative bindings that carry the first and second derivative of every shared subexpression)
- `theories/Cell.v` - cells over any two distinct input slots, `check_ccert`, `check_ccert_correct`: the bound at every real point of a cell, by a mean-value step in each varied slot from the centre. A certificate names the two slots: 1 and 2 are the poloidal and toroidal angle, and 0 and 1 the radius and the poloidal angle. A cell with no width in the second slot is checked by `check_component_flat`, which asks for no bound on that derivative, since the step there covers no distance
- `theories/Hypotheses.v` - the physical assumptions, each as a proposition about explicit objects rather than a name, with what would falsify it; two of them are theorems about the reconstruction and are proven there, and the limits no further work removes are stated in the same file
- `theories/Mercier.v` - the Mercier criterion assembled from certified enclosures inside the checker, with the sign of its geodesic term supplied by the inequality of `Quad.v` rather than by an enclosure
- `theories/Kantorovich.v` - the step from a small residual to a nearby equilibrium, in the abstract: the contraction mapping theorem on a ball, the Newton map, and the theorem that says why neither can be applied here without fixing the gauge first
- `theories/Identities.v` - what the reconstruction satisfies rather than assumes
- `theories/Cover.v` - that a list of cells leaves no gap, as a boolean the checker evaluates, with the exact tiling a generator emits and the concatenation of two coverings that meet
- `theories/Cell.v` also carries a third varied slot, `check_ccert3_correct`: the bound at every point of a cell in three coordinates at once, proven by composing the two-slot walk with one more mean-value leg
- `theories/Quad.v` - quadrature over a cell, over a tiling of equal cells and over one whose cells each carry their own width, over a rectangle of cells in both angles, differentiation of an average in the radius, and Cauchy-Schwarz for a weighted integral
- `gen/make_cert.py` - wout -> certificate (point bounds from a float reference; cell bounds left to `--tighten`)
- `gen/verify_cert.py` - a certificate against the wout it claims to describe, read independently, which is what ties a verdict to an equilibrium
- `gen/mercier.py` - runs the four coverings a Mercier verdict needs and hands their enclosures to the checker, which does the arithmetic
- `gen/nrad_profile.py` - how much refining each node interval still buys, so that `--adapt-from` follows a measurement rather than a threshold picked by hand
- `gen/boozer.py` - the Boozer stream function of a surface, from certified harmonics of the covariant components, with the defect of the relation between them
- `gen/convergence.py` - the certified residual against the grid spacing and against the mode set, which is what turns `discretization_is_consistent` into a measurement
- `gen/radial_scan.py` - the certified residual surface by surface, beside the transform and the nearest resonance, which is where a single number for an equilibrium comes from
- `gen/cancellation.py` - the residual against the three terms it is the difference of, which says whether a bound is a cancellation defect a finer covering reaches or an imbalance it does not
- `gen/families.py` - runs VMEC++ over a family of resolutions, the only tool here that runs a solver
- `gen/patch_extract.py` - post-extraction stubs
- `driver/main.ml` - parse, expand, run in parallel, report; `--tighten` writes the bounds of a cell certificate and `--integrate` sums them
- `proto/continuum_ref.py` - a float reference of the certified free-radius reconstruction, written from the rule rather than from the expression builders, so an encoding mistake shows up as a disagreement
- `proto/residual_proto.py` - the early prototype, which interpolates differently and checks the reconstructed field against the wout's own `bsupumnc`, `bsupvmnc` and `gmnc`
- `test/run_tests.py` - the regression suite: every verdict, every published number, the correspondence guards and the adversarial cases
- `test/audit_summary.py` - what `make audit` printed, read rather than counted by hand

## Build

```sh
opam switch create stellarocq ocaml-base-compiler.4.14.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover.9.0.0 rocq-core.9.1.1 coq-stdlib.9.2.0 \
             coq-mathcomp-ssreflect.2.4.0 coq-coquelicot.3.4.5 \
             coq-interval.4.11.4 coq-flocq.4.2.2 dune.3.23.1
make versions   # the installed toolchain against what the trust base claims
make            # proofs, extraction, patch, checker binary
make audit      # Print Assumptions of every theorem
```

The versions are pinned because the trust base names them. `make versions`
compares what is installed against that list and fails on a difference, so a
switch that would make the audit's axiom count mean something else is caught
before the proofs are built rather than after they are believed.

```sh
python gen/make_cert.py wout_solovev.nc cert.txt   # --nodes 6 --nu 8 --nv 4 --prec 53
./extract/_build/default/main.exe cert.txt          # STELLAROCQ_JOBS=n selects the worker count
```

A cell certificate is generated, tightened, then checked:

```sh
python gen/make_cert.py wout_solovev.nc cells.txt --cells --nodes 6 --nu 8192
./extract/_build/default/main.exe --tighten cells.txt cert.txt
./extract/_build/default/main.exe cert.txt
```

The same file read the other way. `--lower` proves a component bounded away
from zero instead of close to it, `--tighten --lower` reads the floors back
and `--filter` keeps only the cells that carry one; `--integrate` sums the
per-cell midpoint rules into an enclosure of the angular integral, over a
patch of the surface when `--surface` gave the toroidal angle real width.

A radial certificate covers the volume rather than a surface. Its cells range
over the radius and the poloidal angle, and a node's cells tile the interval
between its two half points, so consecutive nodes tile the plasma.

```sh
python gen/make_cert.py wout_solovev.nc vol.txt --radial --adapt --nodes 52 --nu 128 --nrad 8
./extract/_build/default/main.exe --tighten --verify vol.txt volc.txt
```

`--verify` hands the file just written to a fresh process, which reads it
knowing nothing of the run that produced it, so the two passes stay two passes.
They are not merged, and the reason is the design rather than the effort: the
tightening chooses the numbers and an independent run establishes them, which
is what makes the bounds worth anything.

The certificate stays text. Consecutive radial cells of one node differ only
in where they sit, so a node block may say `SAME` and take the coefficients of
the one before it, which halves a volume certificate: the 53248-cell covering
above is 2.6 MB rather than 5.6 MB. What remains is mostly the per-cell bounds,
which are the claims themselves. A binary encoding would shrink that and add a
parser to the surface that has to be trusted.

The magnetic well and the Mercier criterion come off the same reconstruction,
in one command that runs the four coverings and hands their enclosures to the
checker:

```sh
python gen/mercier.py wout.nc --node 22 --nu 512 [--write merc.txt]
./extract/_build/default/main.exe --mercier merc.txt
```

What the residual is a difference of, over the same cells that bound it:

```sh
python gen/cancellation.py wout.nc --nodes 8 --nu 256 [--radial]
```

A third varied slot, and a floor over a box of coefficients rather than at one
field:

```sh
python gen/make_cert.py wout.nc vol.txt --radial --node 22 --nu 256 --slot3 2
./extract/_build/default/main.exe --tighten vol.txt volc.txt
./extract/_build/default/main.exe volc.txt

python gen/make_cert.py wout.nc box.txt --cells --node 22 --nu 256 \
       --coefbox rmnc,1,1,0.0005 --perturb rmnc,22,1,0.001
./extract/_build/default/main.exe --tighten --lower --filter box.txt boxc.txt
./extract/_build/default/main.exe --lower boxc.txt
```

The regression suite runs every verdict this file quotes:

```sh
python test/run_tests.py --data DIR [--slow]
```

with `--data` naming a directory of wout files. Without it the suite still runs
the certificates committed under `test/data`, so a fresh clone exercises the
checker with no equilibria to hand.

```sh
python gen/make_cert.py wout.nc cells.txt --cells --node 18 --nu 2048 --harmonic 5,5
./extract/_build/default/main.exe --tighten --lower --filter cells.txt floors.txt
./extract/_build/default/main.exe --lower floors.txt
python gen/make_cert.py wout.nc surf.txt --cells --node 12 --nu 128 --nv 80 --surface --geometry
./extract/_build/default/main.exe --integrate surf.txt
```

The certificate's `PREC` line sets the working precision of the interval arithmetic; with the primitive-float carrier the arithmetic is binary64 whatever the value, and the value steers the transcendental functions only, so 53 is the default.

## Scope

Certification pointwise in the angles, or over cells covering a continuum of
them, or over cells covering the radius as well. Every pressure
parameterization VMEC++ allows is covered, the piecewise ones through the local
piece the node falls in, except under a radial covering, where a cell spanning
a knot would cross from one piece to the next. Both symmetry classes are
covered, and the generator reads a VMEC netCDF wout or a VMEC++ output file.

A radial covering resolves the radius and the poloidal angle, and its cells
are checked to leave no gap. A third slot is carried by the file and checked by
`check_ccert3_correct`, so for an axisymmetric equilibrium the cross-section is
the volume inside the verdict rather than beside it. A fourth would be the same
construction again, one mean-value leg per varied slot, and not a new theorem.

Every pressure parameterization is covered radially, the piecewise ones by
splitting the covering at their knots and giving each segment the cubic that is
exact on it.

Radial derivatives of surface averages are certified. `diff_under_integral`
makes an average a differentiable function of the radius whose derivative is
the integral of the derivative, which gives `V''`, and with the four Mercier
integrands and the flux functions beside them the whole criterion follows.
What that leaves is not the well but the axis: nothing below `s = 1.5 h` is
covered, because VMEC's parity rule divides odd-m coefficients by `sqrt(s)`
and no half point sits below it.

A free-boundary equilibrium needs the vacuum field and the total-pressure jump
at the plasma-vacuum interface. `free_boundary_balanced` in
[theories/Hypotheses.v](theories/Hypotheses.v) is that condition written as a
proposition about the reconstruction and a vacuum field, and `--edge` now
covers the boundary itself, so the plasma side of the jump is a quantity a
covering reaches. What is missing is the other side: the wout of a
free-boundary run carries no vacuum field, only the iteration history of the
jump, so the field outside would have to come from the coils through the mgrid
and a Biot-Savart evaluation that nothing here does.

Quasi-symmetry needs the Boozer angles, and the transformation to them is in
hand. The stream function's coefficients are certified from the covariant
harmonics, the condition for it to exist at all is the surface current the
residual already bounds, and the harmonics of `|B|` in the Boozer angles are
certified integrals over the VMEC angles, Jacobian of the angle map included.
What is not explicit is w itself: `B_u` is a rational function of the series
and not a finite Fourier sum, so w has no closed form as an expression and is
carried as data, and what makes that usable is the certified defect of the two
relations defining it. What stands between this and a quasi-symmetry residual
is the cost: one covering per symmetry-breaking mode, at the resolution a
three-dimensional surface needs for integrands that do not cancel, which is
under Toward Boozer coordinates.

What a certificate does not say is that a true equilibrium sits nearby. That
step is Newton-Kantorovich, and [theories/Kantorovich.v](theories/Kantorovich.v)
carries it in the abstract: the contraction mapping theorem on a ball, proven
from the metric axioms and completeness, and the Newton map, whose fixed point
is a zero of the operator. What it also carries is the reason the argument
cannot be made here as it stands. Poloidal relabelling is a gauge symmetry, so
the residual is constant along a gauge orbit, and
`kantorovich_is_gauge_fixed` proves that a ball carrying the Kantorovich
condition meets each orbit at most once. A ball around a reconstruction
contains points of its own orbit, so no such ball exists and the argument has
to be made on the gauge-fixed quotient. `lambda_gauge` of `Identities.v`
exhibits one exact direction of that orbit. The missing piece is therefore one
named hypothesis at a concrete operator, on a quotient that has still to be
built, rather than a theory.
