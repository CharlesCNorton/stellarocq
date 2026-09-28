# The certificate format

A certificate is a text file naming an equilibrium's coefficients and the
claims made about the field reconstructed from them. Two kinds exist: a point
certificate, which claims bounds at listed angles, and a cell certificate,
which claims them over rectangles of two varied input slots.

This file is the grammar. It was implicit in one writer
([gen/make_cert.py](gen/make_cert.py)) and three readers
([driver/main.ml](driver/main.ml), [gen/verify_cert.py](gen/verify_cert.py),
and the bound-line scanners of the analysis tools), which is how the scanners
came to disagree with the writer about how wide a bound line is.

## Lexical structure

The file is a sequence of whitespace-separated tokens. Newlines are
whitespace, so the line breaks shown below are advisory to a reader and are
not enforced by the parser, with one exception: `main --tighten` and
`main --tighten --lower --filter` rewrite a file line by line, replacing the
`3 * m` bound lines that follow a `CELLS m` line and rewriting the entries
that follow `NANGLES`. A file those commands are to be run on must therefore
put each bound line and each angle entry on a line of its own, and must put
`CELLS` and `NANGLES` at the start of theirs.

Every numeric token is a decimal integer, possibly negative. A quantity that
denotes a real number is written as a *dyadic pair* of two integers `m e`
denoting `m * 2^e` exactly. Every input a certificate carries is an exact
image of an IEEE double, so every such value is representable and no rounding
happens between the wout and the file.

Integers that are not dyadic pairs appear as counts, slot indices, mode
numbers, profile exponents, and cell half-widths. A half-width is in units of
the exponent its centre carries, not in radians.

## Header

Each kind begins with its magic token.

```
STELLAROCQ-CERT            a point certificate
STELLAROCQ-CCERT           a cell certificate
```

The header continues the same way for both, except where noted.

```
PREC <bits>                working precision, at least 2
LASYM <0|1>                whether the antisymmetric half is carried
PROFILE <name> <ints...>   the pressure's closed form
SLOTS <xu> <xv>            the two input slots a cell ranges over
SLOT3 <xw> <dw>            optional, cell certificates only
TAYLOR                     optional, cell certificates only
OUTPUT <name> <ints...>    what the three components carry
MODES <K>                  followed by K pairs of plain integers, m and n
PHIP <m> <e>
AM 21                      followed by 21 dyadic pairs
```

`SLOTS` names two distinct input slots. Slot 0 is the radius, slot 1 the
poloidal angle and slot 2 the toroidal angle, and any other input slot is
legal: a certificate written by `--coefbox` varies a Fourier coefficient's
slot against an angle.

`SLOT3` names a third varied slot and its half-width, in units of that slot's
own exponent. `TAYLOR` marks a file whose first varied slot is charged against
its derivative at the cell centre. Both widen every bound line from eight
numbers to ten, with different meanings, so a file may carry at most one of
them; see **Bound lines** below.

A point certificate then carries its three claimed bounds, which a cell
certificate does not, since a cell's bounds are per cell.

```
EPS_S <m> <e>
EPS_U <m> <e>
EPS_V <m> <e>
```

### PROFILE names

The name is followed by that many plain integers, which are the integral
exponents the closed form needs. The coefficients themselves are in the `AM`
block.

| name | trailing integers | meaning |
|---|---|---|
| `POWER` | none | `sum_j am_j s^j` |
| `TWOPOWER` | `p q` | `am0 (1 - s^p)^q` |
| `TWOPOWERGS` | `p q g` | the same times `g` Gaussian bumps |
| `GAUSSTRUNC` | none | truncated Gaussian |
| `TWOLORENTZ` | `p q r t` | two Lorentz factors |
| `PEDESTAL` | none | polynomial plus a tanh pedestal |
| `RATIONAL` | `nn nd` | ratio of two power series |
| `CUBIC` | none | `am0 + am1 t + am2 t^2 + am3 t^3`, `t = s - am4` |

A piecewise profile in the wout (`cubic_spline`, `akima_spline`,
`line_segment`) never reaches the file as such: the generator resolves it to
the local `CUBIC` of the piece each node falls in, either once for the file or
per node on an `AMLOCAL` line.

### OUTPUT names

The name is followed by two plain integers for those that carry a mode pair,
by a count and that many pairs for `jump`, by the number of source points for
`coil`, and by nothing otherwise.

| name | mode pair | components |
|---|---|---|
| `residual` | no | `r_s`, `r_u`, `r_v` at the node and outer half point |
| `radial` | no | the same at a free radius |
| `radial-axis` | no | the same on the innermost interval |
| `geometry` | no | `sqrt(g)`, `sqrt(g) B^2`, `B_u` |
| `radial-geometry` | no | `sqrt(g)`, `d(sqrt g)/ds`, `B_u` |
| `radial-shear` | no | `iota'`, `dB_u/ds`, `mu0 p'` |
| `mercier-a` | no | `tpp`, `tbb`, `tjb` integrands |
| `mercier-b` | no | `tjj` integrand, `gf`, `B^2` |
| `terms` | no | the three terms `r_s` is the difference of |
| `radial-terms` | no | the same at a free radius |
| `current-terms` | no | `d_u B_v`, `d_v B_u`, `mu0 sqrt(g) J^s` |
| `radial-current-terms` | no | the same at a free radius |
| `quasisym` | no | the triple product and its two products |
| `quasisym-two` | no | the two-term defect and its two products |
| `stream-defect` | no | the two stream-function defects and `mu0 sqrt(g) J^s` |
| `harmonic` | `m n` | each residual component times `cos(mu - nv)` |
| `covariant` | `m n` | `B_u`, `B_v`, `mu0 sqrt(g) J^s` against `cos(mu - nv)` |
| `covariant-sin` | `m n` | the same three against `sin(mu - nv)` |
| `boozer` | `m n` | `|B| cos`, `|B| sin`, and the angle map's Jacobian |
| `weighted` | `m n` | `(Gm Gp)^3 r_s` against `cos(mu - nv)` and `sin(mu - nv)`, and `(Gm Gp)^3 r_s` |
| `jump` | `V`, then `V` pairs | the jump of `p + B^2/2` against the vacuum pressure, the plasma side extrapolated to `s = 1`, the vacuum pressure |
| `newcomb` | `m n` | `sqrt(g)` against `cos(mu - nv)` and `sin(mu - nv)` at a free radius, and `mu0 p'` |
| `iota` | `m n` | `m iota - n`, `iota` and `iota'` at a free radius |
| `forced` | no | `r_s - f_s`, `r_u - f_u`, `r_v - f_v` |
| `coil` | `P` | `B.n / (|B| |n|)`, `B.n` and `|B|^2` of a coil field on a torus |

`stream-defect` and `boozer` require a `WCOEF` block in every node.
`quasisym-two` requires an `FZERO` line in every node. `weighted` is the radial
residual multiplied by the cube of the two half-point Jacobians, which leaves
no division by anything that reads an angle. `newcomb` reads a state in
straight-field-line angles, whose lambda is zero. `jump`, `forced` and `coil`
read slots after the state, laid out under **Environment layout** below.
`forced` is the output of a collocation system of the interval Newton
certificate, and the other six are outputs of the certificates over a box of
states.

## Angles

```
NANGLES <na>
```

followed by `na` entries. A point certificate writes four integers per entry,
the dyadic pair of the poloidal angle and that of the toroidal angle:

```
<mu> <eu> <mv> <ev>
```

A cell certificate writes six, adding the half-widths of the two varied slots
in units of `eu` and `ev` respectively:

```
<mu> <eu> <mv> <ev> <du> <dv>
```

A half-width of zero means that slot has no width, and the mean-value step
along it covers no distance, so the checker asks for no bound on that
derivative and never builds its environment: `check_component_flat` when `dv`
is zero and `check_component_flat_u` when `du` is. The angle list is shared by
every node block.

The generator lays the cells out in integer mantissa units, cell `k` centred
at `(2k+1)d` with half-width `d`, which is exactly the tiling
[theories/Cover.v](theories/Cover.v) reasons about. Choosing centres in
radians and rounding them onto the grid afterwards leaves consecutive cells a
fraction of an ulp apart, which is far too little to matter numerically and
enough to put them outside the theorem.

## Node blocks

```
NNODES <nb>
```

followed by `nb` blocks. Within a block the lines appear in this order, the
bracketed ones optional:

```
NODE [SAME]
S <m> <e>
[DU <du>]
[AMLOCAL 21]                    followed by 21 dyadic pairs
SNODES <m> <e> x3               s_{j-1}, s_j, s_{j+1}
SHALF  <m> <e> x2               s_{j-1/2}, s_{j+1/2}
IOTA   <m> <e> x2               iota at the two half points
RNODES                          3 rows of K dyadic pairs
ZNODES                          3 rows of K
LHALF                           2 rows of K
[RNODES_A]                      3 rows of K, when LASYM 1
[ZNODES_A]                      3 rows of K, when LASYM 1
[LHALF_A]                       2 rows of K, when LASYM 1
[WCOEF <K>]                     K dyadic pairs, then I and G
[FZERO]                         one dyadic pair
[CELLS <m>]                     cell certificates only, 3*m bound lines
```

`NODE SAME` takes the coefficient blocks of the preceding block, which is what
keeps a volume certificate from repeating the same few thousand numbers once
per radial cell. A `SAME` block carries no `SNODES` through `LHALF_A`, and the
first block of a file may not be `SAME`. `S`, `DU` and `AMLOCAL` are read
before the branch and so are present on a `SAME` block when they apply.

`S` is the radius at which the block is evaluated. For every output but the
volume ones it is a full-grid node. For `radial`, `radial-axis` and
`radial-terms` it is a point inside the node's interval, which is the
half-grid interval `[s_{j-1/2}, s_{j+1/2}]` except under `--axis` and
`--edge`, where the two-node rule tiles between the nodes themselves.

`DU` gives the block its own half-width in the first varied slot, overriding
the one the shared angle list carries. This is what lets a volume covering
give each node its own radial resolution.

`AMLOCAL` gives the block its own pressure coefficients, which a covering
crossing a knot of a piecewise profile needs, since no single cubic is exact
across a knot.

`WCOEF` carries the Boozer stream function's `K` coefficients followed by the
two flux functions `I` and `G`. The count must equal `MODES`.

`FZERO` carries the flux function a two-term quasisymmetry certificate claims
the ratio equals.

## Bound lines

A cell certificate carries `3 * m` bound lines after `CELLS m`, three per
cell, in component order `r_s`, `r_u`, `r_v`. Each is a run of plain integers
read as dyadic pairs `N q` denoting `N * 2^q`.

Without `SLOT3` or `TAYLOR` a bound line is eight numbers:

```
N0 q0  NDu qDu  NDv qDv  Nc qc
```

`N0` is the bound on the component at the cell centre, `NDu` and `NDv` the
bounds on its derivatives along the two varied slots over the whole cell, and
`Nc` the cell bound they combine to. The checker requires

```
N0 2^q0 + du (NDu 2^qDu) + dv (NDv 2^qDv) <= Nc 2^qc
```

which is the mean-value combination of
[theories/Cell.v](theories/Cell.v).

With `SLOT3` a bound line is ten numbers, the two extra being the bound on the
derivative along the third slot:

```
N0 q0  NDu qDu  NDv qDv  Nc qc  Ndw qdw
```

and the combination gains the term `dw (Ndw 2^qdw)`.

With `TAYLOR` a bound line is also ten numbers, and they mean something else:

```
N0 q0  Nu qu  Nuu quu  Nv qv  Nc qc
```

Here `Nu` is the derivative along the first slot at the cell centre, a thin
evaluation, `Nuu` a bound on the second derivative over the box, and `Nv` the
mean-value step in the second slot. The combination is

```
N0 2^q0 + du (Nu 2^qu) + du^2 (Nuu 2^quu) + dv (Nv 2^qv) <= Nc 2^qc
```

The cell bound therefore sits at field index 6 in an eight-number line and in
a `SLOT3` line, and at index 8 in a `TAYLOR` line. A reader that assumes eight
fields will take `Nc qc` from the wrong place in a ten-field file, and one
that distinguishes the two ten-field forms by width alone cannot: the `TAYLOR`
token in the header is what tells them apart.

A file written by the generator before `main --tighten` carries placeholder
bound lines, `1 0 1 0 1 0 4 0` and its wider forms, which the tightening
replaces with the enclosures the extracted code computes.

## Environment layout

The checker builds one environment per evaluation point, in the slot order
[theories/Physics.v](theories/Physics.v) fixes. With `K` the mode count:

| slots | contents |
|---|---|
| 0 | `s`, the radius the block is evaluated at |
| 1, 2 | poloidal and toroidal angle |
| 3 | `phip` |
| 4, 5, 6 | `s_{j-1}`, `s_j`, `s_{j+1}` |
| 7, 8 | `s_{j-1/2}`, `s_{j+1/2}` |
| 9, 10 | iota at the two half points |
| 11..31 | the 21 pressure coefficients |
| 32 .. 32+3K-1 | `RNODES`, three rows of K, row-major |
| 32+3K .. 32+6K-1 | `ZNODES` |
| 32+6K .. 32+8K-1 | `LHALF`, two rows of K |
| 32+8K .. 32+11K-1 | `RNODES_A`, when `LASYM 1` |
| 32+11K .. 32+14K-1 | `ZNODES_A`, when `LASYM 1` |
| 32+14K .. 32+16K-1 | `LHALF_A`, when `LASYM 1` |

The first slot after those is `base_W`, which is `32 + 8K` under stellarator
symmetry and `32 + 16K` otherwise. A `stream-defect` or `boozer` output places
its `K` stream coefficients there followed by `I` and `G`, and a
`quasisym-two` output places its one flux function there. A `jump` output over
`V` vacuum modes places `4V + 1` slots there: the cosine and sine coefficients
of the mean of the two vacuum series mode by mode, those of half their
difference, and the sweep `t`, so that `t = 1` is the one series and `t = -1`
the other. A `forced` output places the three source components there. A
`coil` output over `P` source points places six slots per point, the point and
its weighted tangent `mu0 I dt / (4 pi)` times the coil's tangent, in Cartesian
coordinates, and reads its torus from the first node row of the R and Z
blocks. Everything above that is scratch, filled by the bindings the residual
allocates.

Each entry contributes its mantissa to the mantissa list and its exponent to
the exponent list, in this order, which is what `env_of` of
[driver/main.ml](driver/main.ml) assembles and what
[gen/verify_cert.py](gen/verify_cert.py) reads back against the wout.

## What the format does not carry

The dyadic grid the angles and radii are written on is a property of the
generator, not of the file: `ANGLE_EXP` and `RAD_EXP` of
[gen/make_cert.py](gen/make_cert.py) are both `-50`, and a reader recovers the
grid from the exponents the entries happen to carry rather than from a
declaration.

Nothing in the file names the wout it was made from. A verdict is a theorem
about the numbers the file carries, and tying those numbers to an equilibrium
is what [gen/verify_cert.py](gen/verify_cert.py) does, by reading the wout
with its own parser and comparing every input slot.

## The interval Newton certificate

`main --newton FILE` reads a third kind of file, which names a system of
expressions defined in [theories/Newton.v](theories/Newton.v) rather than a
reconstruction, and the box and matrices the test needs.

```
STELLAROCQ-NEWTON
PREC <bits>
SYSTEM <name>              a system Newton.v defines; `circle` is the one it carries
N <n>                      the number of unknowns
EXP <e> x n                the exponent of each unknown
CENTRE <m> x n             the mantissa of each unknown at the centre
R <r>                      the radius of the box, in mantissa units
K <m> <e>                  the claimed contraction constant
M <m> <e>                  a claimed bound on every Jacobian entry over the box
A <m> <e> x n*n            an approximate inverse of the Jacobian, row-major
B <m> <e> x n*n            an approximate inverse of A
ANORM <m> <e>              optional: a bound on the row sums of |A|
```

A VALID verdict is `newton_correct`: the system has exactly one zero in the
box. The unknowns are the mantissas, so the Jacobian and both matrices are in
mantissa units, and [gen/newton_circle.py](gen/newton_circle.py) writes the
file for the circle.

A `PREC` above 53 reads the system's outputs at the centre of the box through
[theories/Wide.v](theories/Wide.v) at that precision (`Newton.centre_tab`),
and the rest of the test in binary64. `main --newton-centre FILE` prints those
outputs, and `main --newton-eval FILE` the enclosures a generator places the
centre and chooses `K` and `R` from. `main --stability FILE` runs the Jacobian
half of the test with the `ANORM` bound and asks for no zero: a STABLE verdict
is `Newton.stability`, or `Colloc.colloc_stability` for a collocation, which
bounds how far apart any two states of the box are by `ANORM / (1 - K)` times
how far apart their outputs are.

A `colloc` system ([theories/Colloc.v](theories/Colloc.v)) is the force
residual of Physics.v collocated at points. It carries its parameters after
`CENTRE` and the residual's configuration and its points after the matrices:

```
NPARAM <q>                 the parameters, which follow the unknowns in the
PARAM <m> <e> x q          global layout as slots n .. n+q-1
...
LASYM <0|1>
PROFILE <name> <ints...>
MODES <K>                  followed by K pairs of plain integers, m and n
NPOINTS <P>
POINT <out> <g> x L        one line per point
```

`out` is 0 for `r_s`, 1 for `r_u` and 2 for `r_v`, and the `L` integers that
follow name the global slot each of the point's local input slots reads, in
the environment layout above, `L` being `32 + 8K` under `LASYM 0` and
`32 + 16K` under `LASYM 1`. A global slot below `n` is an unknown and one at
or above it a parameter. A VALID verdict is `colloc_correct`: with the
parameters fixed, exactly one choice of the unknowns in the box makes the
collocated component of every point zero.
[gen/newton_colloc.py](gen/newton_colloc.py) writes the file for a band of
surfaces of a wout, with the R and Z coefficients of those surfaces as the
unknowns and the stream function, the rotational transform, the pressure and
the surfaces beside the band as parameters.

An `OUTPUT forced` line after `PROFILE` collocates the node residual less a
source (`Physics.RForced`) instead of the node residual, and every `POINT`
line then names three more global slots, the source of the three components.
A zero of that system is the discrete solution of a problem whose right-hand
side is the source, and [gen/mms_colloc.py](gen/mms_colloc.py) writes it for a
manufactured solution, with the continuum residual of the mapping as the
source.

## Certificates over a box of states

Five more kinds read a state whose every input slot carries a half-width, so
that a verdict holds for every state in the box ([theories/Box.v](theories/Box.v)).
They share a header:

```
PREC <bits>
LASYM <0|1>
PROFILE <name> <ints...>
OUTPUT <name> <ints...>    absent from STELLAROCQ-QCERT
MODES <K>                  followed by K pairs of plain integers, m and n
NSLOTS <n>
STATE                      n triples: mantissa, exponent, half-width
SLOTS <su> <sv>            the two angle slots
```

Slot `k` of the state spans the mantissas `m_k - d_k` to `m_k + d_k` at the
exponent `e_k`, in the layout of **Environment layout** above. The grid, the
cells or the points set the two angle slots, of which only the exponents are
read. What follows `SLOTS` depends on the kind.

```
STELLAROCQ-HCERT           COMP <k>, GRID <Nu> <Nv>
STELLAROCQ-ICERT           COMP <k>, U <au> <du> <NU>, V <av> <dv> <NV>,
                           CELLS, then NU * NV lines of six integers
                           Nuu quu Nvv qvv Ndv qdv
STELLAROCQ-BTCERT          COMP <k>, HALF <du> <dv>, GRID <au> <av> <NU> <NV> <NFP>,
                           CELLS <N>, then N lines of twelve integers
                           mu mv NDu qDu NDuu qDuu NDv qDv NDvv qDvv Nc qc
STELLAROCQ-BPCERT          COMP <k>, POINTS <N>, then N lines mu mv N q mode
STELLAROCQ-QCERT           KERNELS <k>, then k triples s m n (s 1 for sine),
                           NPOINTS <P>, then P pairs of angle mantissas
```

`main --harm` establishes an HCERT by `Harmonic.check_harm`: the degree
analysis of [theories/TrigExpr.v](theories/TrigExpr.v) puts the component
below the grid, so the equispaced sum is its integral over the angular torus,
enclosed at every state of the box (`harm_correct`). `main --dharm` reads the
same file without the degree bound, and what it encloses is the equispaced
rule's discrete harmonic (`dharm_correct`).

`main --int` establishes an ICERT by `Integral.check_int`: every cell carries
bounds on the component's second derivative along each slot and its first
derivative along the second over the cell and the box, and the enclosure of
the integral over the tiled rectangle is `int_total` (`check_int_correct`).
`main --int-tighten IN OUT` fills in the bounds.

`main --bt` establishes a BTCERT by `BoxCell.check_btcert`, `bt_tiles` and
`bt_period`: every cell is bounded by two Taylor steps from its centre, the
cells are the grid the file names, and the grid spans `2 pi` in the first
angle and `2 pi / NFP` in the second, so the largest cell bound holds at every
point of a field period of the surface (`bt_surface`). `main --bt-tighten IN
OUT` fills in the bounds from the cell centres.

`main --bp` establishes a BPCERT by `BoxCell.check_bpcert`, a claim at each
pair of angle mantissas: mode 0 bounds the component's magnitude above by
`N 2^q`, mode 1 bounds it below, mode 2 claims the component at least `N 2^q`
and mode 3 at most `-N 2^q` (`check_bpcert_correct`). `main --bp-tighten IN
OUT` sets each claim from the enclosure.

`main --qs` establishes a QCERT, whose output is always the two-term
quasisymmetry residual, by `QSFloor.check_qcert`, and prints the enclosures
of the harmonics of its two terms at every kernel, which `QSFloor.qs_floor`
turns into a floor on the defect. [gen/qs_floor.py](gen/qs_floor.py) writes the
file and reads the floor off the harmonics.

## The KAM certificate

`make kam` builds `kam/_ext/_build/default/main.exe`: the six parts of
`KFinal.cert_ok`, extracted over intervals of 192 fractional bits
(`KFix.FX`) with Zarith integers, and the driver [kam/main.ml](kam/main.ml).

```
main.exe MODE E0 SRC JETS FD FS WORKERS O TR
```

Every file is integers separated by white space. A rational is a numerator
and a positive denominator, an enclosure two integers, its ends times 2^192.
Rows run over `zrange K = K, -K, K-1, -(K-1), ..., 1, -1, 0` in the poloidal
mode and the same order in the second index `l`, the toroidal mode being `P l`;
a block of rows `(K1, K2)` is `2 K1 + 1` lines of `2 K2 + 1` mantissas. A source
is six mantissas, its point and its weighted tangent `mu0 I gamma' dt / (4 pi)`.

```
E0      KE0.e0data, gen/kam_e0.py
        P N1 M K1 K2 D Km Kn Kmu Knu Kmg Kng / s0 / cosine rows of R and sine rows
        of Z (Km, Kn), cosine rows of the seeds Ub (Kmu, Knu) and gs (Kmg, Kng),
        at 2^-s0 / ssrc / the count of base sources and the sources at 2^-ssrc /
        a b / 6 + 7 + 8 enclosures, not read
SRC     KSrcRun.srcdata, gen/kam_src.py
        P Km Kn Kr1 Kr2 N1s N2s Ky1 Ky2 Kmu Knu Kmg Kng / s0 sY ssrc / the rows
        of R, Z, Ub, gs / the count and the sources / per source its seed, rows
        (Ky1, Ky2) of cosine and sine mantissa pairs at 2^-sY / a b /
        4 + 6 + 4 enclosures, not read
JETS    KJets.jetsdata, gen/kam_jets.py
        P N1 M K1 K2 D Km Kn Kj1 Kj2 / s0 sJ / the rows of R and Z / nine
        blocks (Kj1, Kj2) at 2^-sJ, the approximants of B_R, B_phi, B_Z and of
        their R and Z derivatives, sine rows for the odd ones / ssrc, the count
        and the sources / 6 + 7 + 9 + 9 enclosures, not read
FD      KFinal.findata, gen/kam_params.py
        w0 d0 w1 / the claims Mw (4), B (4), JM (9), JB (9) / Kmb Knb and the
        sine rows of b at 2^-s0 / N1t Mt NP NT NE
FS      KFinal.fscal, gen/kam_params.py
        r eps0 delta A0 G0 N0 T0 tau0 xA xG xN xB xTm xtau
O, TR   a count, then one enclosure per line
```

`a` and `b` give the rotation number `P (-b + sqrt 5) / (2 a)`. The checks
compute every trigonometric and exponential seed from FD (`NP`, `NT` and
`NE` terms of the series for pi, for cos and sin, and for exp) and take every
claim from FD. `head` prints `cert_head`, which checks that the three grid
records describe the same torus, sources and field period and that the
parameters are admissible. `src` runs `run_src`, writes the enclosures it
returns to O, reads them back and prints `check_src_with`. `e0` and `jets` print
`run_E0` and `run_jets`. `twist` runs `run_twist`, writes it to TR, reads it
back and prints `check_twist_with`. `fin` prints `check_fin` on O and TR and
each scalar condition. Only `head` and `fin` read FS. `KFinal.cert_ok_torus`
turns the six verdicts, true on the same files, into an invariant torus of the
coil field within `delta` of the torus of E0, a pair of Fourier series on a strip
that carries the field lines at the rotation number of `a` and `b`
(`TorusLine.fourier_torus`).
