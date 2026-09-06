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

Both kinds begin with a magic token and a version.

```
STELLAROCQ-CERT 6          a point certificate
STELLAROCQ-CCERT 7         a cell certificate
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

The name is followed by two plain integers for the four that carry a mode
pair, and by none otherwise.

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

`stream-defect` and `boozer` require a `WCOEF` block in every node.
`quasisym-two` requires an `FZERO` line in every node.

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

A `dv` of zero means the second slot has no width; the checker then uses
`check_component_flat`, which asks for no bound on that derivative. The angle
list is shared by every node block.

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
`quasisym-two` output places its one flux function there. Everything above
that is scratch, filled by the bindings the residual allocates.

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
