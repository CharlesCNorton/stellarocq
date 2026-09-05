"""Check that a certificate is about the wout it claims to be about.

A VALID verdict is a theorem about the mantissas and exponents the checker was
handed. It says nothing about where those numbers came from: a generator that
transposed a Fourier array would produce a certificate about a different
equilibrium and the checker would still pass it, because the theorem quantifies
over whatever it is given.

This closes that from the other side. It reads the wout and the certificate
separately, with its own parser and its own indexing, and checks every input
slot against the file: the radii, iota, phip, the pressure coefficients, the
mode list, and every coefficient of every block. A disagreement means the
certificate is not about this equilibrium, whatever the checker says of it.

Every form the generator writes is read here, which is what makes the guard
cover the verdicts rather than a subset of them: a node block that says SAME
and takes the coefficients of the one before it, a node's own pressure piece on
an AMLOCAL line, the Boozer stream function on a WCOEF line, a third varied
slot on a SLOT3 line and the two extra numbers per bound line it brings, and
the outputs whose OUTPUT line carries a mode pair. The quasisymmetry output is
a surface covering at a node, laid out as the residual's is, with no mode pair.

Two blocks the wout constrains only indirectly are checked against it anyway. A
node's local pressure cubic is evaluated at the node's radius and read against
the wout's own presf, which VMEC computed from its own spline, so a
reimplementation of that spline that drifted would show up here. The two flux
functions beside a stream function are read against buco and bvco.

The slot layout is the one theories/Physics.v fixes:

  0 s | 1 u | 2 v | 3 phip | 4..6 s_{j-1} s_j s_{j+1} | 7..8 half radii
  9..10 iota at the half points | 11..31 am | 32 + 0K.. R rows (j-1, j, j+1)
  + 3K Z rows | + 6K lambda rows (h-, h+) | and under lasym three more blocks
  | and after those, for a stream-function output, K coefficients then I and G

Usage:  python gen/verify_cert.py wout.nc cert.txt
"""

import argparse
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "proto"))
from pressure_ref import Profile  # noqa: E402

# The coefficients that carry a profile's amplitude, per closed form. VMEC
# multiplies the profile by PRES_SCALE and does not write that to the wout, so
# the generator puts it back into these; every other coefficient is an
# exponent, a position, a width or a mixing fraction and has to be the file's
# own exactly. The pressure itself is then read back against the file's `pres`.
AMPLITUDE_SLOTS = {
    "POWER": set(range(21)),
    "TWOPOWER": {0},
    "TWOPOWERGS": {0},
    "GAUSSTRUNC": {0},
    "TWOLORENTZ": {0},
    "PEDESTAL": set(range(16)) | {17},
    "RATIONAL": set(range(10)),
}

# The OUTPUT names whose line carries a mode pair after the name.
OUTPUT_WITH_MODE = ("harmonic", "covariant", "covariant-sin", "boozer")

# The OUTPUT names of a volume covering, whose node blocks carry a radius
# inside the node's interval rather than the node itself. The other outputs
# read off the free-radius reconstruction hold the radius at the node and vary
# the angles, so their S line is a grid value.
OUTPUT_OFF_GRID = ("radial", "radial-axis", "radial-terms")


def tokens(path):
    with open(path) as f:
        return f.read().split()


class Reader:
    """A token reader that fails loudly rather than drifting."""

    def __init__(self, toks):
        self.t, self.i = toks, 0

    def next(self):
        v = self.t[self.i]
        self.i += 1
        return v

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def expect(self, w):
        got = self.next()
        if got != w:
            raise SystemExit(f"expected {w!r}, found {got!r} at token {self.i}")

    def int(self):
        return int(self.next())

    def dyadic(self):
        m, e = self.int(), self.int()
        return m * 2.0**e


def close(a, b, tol=0.0):
    """Exactly equal, or within tol when a tolerance is allowed."""
    if tol == 0.0:
        return float(a) == float(b)
    return abs(float(a) - float(b)) <= tol * max(1.0, abs(float(b)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("cert")
    ap.add_argument("--radius-tol", type=float, default=1e-12,
                    help="the varied radius is written on a fine dyadic grid, "
                    "so it is checked to lie in the node's interval rather "
                    "than to equal a grid value")
    ap.add_argument("--pressure-tol", type=float, default=1e-3,
                    help="relative agreement required between a node's local "
                    "pressure cubic and the wout's own presf at that radius. "
                    "The slack is the linear interpolation of presf onto an "
                    "off-grid radius, which is a part in ten thousand here")
    ap.add_argument("--flux-tol", type=float, default=1e-2,
                    help="relative agreement required between the flux "
                    "functions beside a stream function and buco and bvco")
    a = ap.parse_args()

    import netCDF4
    d = netCDF4.Dataset(a.wout)
    d.set_auto_mask(False)
    v = d.variables
    g = lambda k: np.asarray(v[k][:], dtype=float)  # noqa: E731
    ns = int(v["ns"][:])
    xm, xn = g("xm").astype(int), g("xn").astype(int)
    rmnc, zmns, lmns = g("rmnc"), g("zmns"), g("lmns")
    iotas, phips, am = g("iotas"), g("phips"), g("am")
    pmass = (v["pmass_type"][:].tobytes().decode().replace(chr(0), "").strip()
             if "pmass_type" in v else "")
    presf = g("presf") if "presf" in v else None
    pres = g("pres") if "pres" in v else None
    buco = g("buco") if "buco" in v else None
    bvco = g("bvco") if "bvco" in v else None
    lasym_w = bool(int(v["lasym__logical__"][:])) if "lasym__logical__" in v else False
    if lasym_w:
        rmns, zmnc, lmnc = g("rmns"), g("zmnc"), g("lmnc")
    h = 1.0 / (ns - 1)
    s_full = np.arange(ns) * h
    s_half = (np.arange(ns) - 0.5) * h

    r = Reader(tokens(a.cert))
    kind = r.next()
    if kind not in ("STELLAROCQ-CERT", "STELLAROCQ-CCERT"):
        raise SystemExit(f"not a certificate: {kind!r}")
    cells = kind.endswith("CCERT")
    r.next()  # version
    r.expect("PREC"); r.int()
    r.expect("LASYM"); lasym = r.next() == "1"
    r.expect("PROFILE")
    prof = r.next()
    # a profile carries its integral exponents inline
    extra = {"TWOPOWER": 2, "RATIONAL": 2, "TWOPOWERGS": 3, "TWOLORENTZ": 4}
    for _ in range(extra.get(prof, 0)):
        r.int()
    r.expect("SLOTS"); xu, xv = r.int(), r.int()
    # A third varied slot is carried by the file, and each bound line then
    # holds two more numbers: the bound on the derivative along it.
    slot3 = None
    if r.peek() == "SLOT3":
        r.next()
        slot3 = (r.int(), r.int())
    # a Taylor file marks that every bound line carries ten numbers rather
    # than eight, the first slot's value and its first two derivatives
    taylor = r.peek() == "TAYLOR"
    if taylor:
        r.next()
    n_bound = 10 if (slot3 or taylor) else 8
    r.expect("OUTPUT")
    out = r.next()
    if out in OUTPUT_WITH_MODE:
        r.int(); r.int()

    problems = []

    def check(name, got, want, tol=0.0):
        if not close(got, want, tol):
            problems.append(f"{name}: certificate {got!r}, wout {want!r}")

    if slot3 is not None:
        if slot3[0] in (xu, xv):
            problems.append(
                f"SLOT3 names slot {slot3[0]}, which the cells already vary")
        if slot3[1] < 0:
            problems.append(f"SLOT3 half-width {slot3[1]} is negative")
    # The OUTPUT name has to match the covering the rest of the file lays out.
    # A volume covering varies slot 0, which is the radius the free-radius
    # reconstruction reads; every other covering pins that slot at a grid node,
    # and the S line below is checked to be one. A file whose name and layout
    # disagree is a sound theorem about the wrong statement, which is the one
    # thing a verdict cannot report.
    on_grid = out not in OUTPUT_OFF_GRID
    if not on_grid and 0 not in (xu, xv):
        problems.append(
            f"OUTPUT {out} covers the radius, and the cells vary slots "
            f"{xu} and {xv}")

    r.expect("MODES")
    K = r.int()
    if K != len(xm):
        problems.append(f"MODES {K}, wout has {len(xm)} modes")
    for k in range(K):
        m, n = r.int(), r.int()
        if k < len(xm):
            check(f"mode {k} m", m, xm[k])
            check(f"mode {k} n", n, xn[k])

    r.expect("PHIP")
    check("phip", r.dyadic(), phips[1])
    r.expect("AM"); r.expect("21")
    # A pedestal of nonpositive width has no tanh term, and the generator
    # carries what is left, which is the sixteen-term polynomial. So the tail
    # of that block is zero by construction rather than the file's own.
    pedestal_off = prof == "POWER" and pmass == "pedestal"
    file_am = []
    shape = set(range(21)) - AMPLITUDE_SLOTS.get(prof, set(range(21)))
    for j in range(21):
        want = am[j] if j < len(am) else 0.0
        if pedestal_off and j >= 16:
            want = 0.0
        got = r.dyadic()
        file_am.append(got)
        if j in shape:
            check(f"am[{j}]", got, want)
        # the amplitude coefficients carry PRES_SCALE, which the wout does
        # not, so they are read back as a pressure against `pres` per node
        # below; a piecewise profile is resolved into a cubic, which is read
        # against presf the same way
    file_profile = (Profile(pmass, file_am) if prof in AMPLITUDE_SLOTS
                    else None)

    if not cells:
        for tag in ("EPS_S", "EPS_U", "EPS_V"):
            r.expect(tag); r.dyadic()

    r.expect("NANGLES")
    na = r.int()
    for _ in range(na):
        r.dyadic(); r.dyadic()          # u and v
        if cells:
            r.int(); r.int()            # the two half-widths

    r.expect("NNODES")
    nb = r.int()
    nodes_seen = 0
    prev = None
    for _ in range(nb):
        r.expect("NODE")
        # Consecutive radial cells of one node repeat its coefficients, so a
        # block may say SAME and take the ones before it. Reading it as a fresh
        # block would desynchronize; taking the previous block's node index is
        # what lets the radius still be placed.
        same = r.peek() == "SAME"
        if same:
            r.next()
        r.expect("S")
        s_here = r.dyadic()
        if r.peek() == "DU":
            r.next(); r.int()
        # A node's own pressure piece, for a covering that crosses a knot.
        local_am = None
        if r.peek() == "AMLOCAL":
            r.next(); r.expect("21")
            local_am = [r.dyadic() for _ in range(21)]

        if same:
            if prev is None:
                problems.append("the first node block says SAME")
                continue
            j, sn, sh = prev
        else:
            r.expect("SNODES")
            sn = [r.dyadic() for _ in range(3)]
            r.expect("SHALF")
            sh = [r.dyadic() for _ in range(2)]
            r.expect("IOTA")
            io = [r.dyadic() for _ in range(2)]

            # which node of the wout this block is, from its own radii
            j = int(round(sn[1] / h))
            if not (1 <= j < ns - 1):
                problems.append(f"node radius {sn[1]} is not a grid node")
                continue
            check(f"node {j} s_(j-1)", sn[0], s_full[j - 1])
            check(f"node {j} s_j", sn[1], s_full[j])
            check(f"node {j} s_(j+1)", sn[2], s_full[j + 1])
            check(f"node {j} s_(j-1/2)", sh[0], s_half[j])
            check(f"node {j} s_(j+1/2)", sh[1], s_half[j + 1])
            check(f"node {j} iota-", io[0], iotas[j])
            check(f"node {j} iota+", io[1], iotas[j + 1])

            # The pressure the certificate's coefficients give at the two half
            # points around the node, against the pressure the wout stores
            # there. VMEC evaluated its profile at exactly those radii with
            # PRES_SCALE in, so this is an equality and not an interpolation.
            if file_profile is not None:
                if pres is None:
                    problems.append("the wout carries no pres to read the "
                                    "pressure against")
                else:
                    for row in (j, j + 1):
                        got_p = file_profile.raw(float(s_half[row]))[0]
                        want_p = float(pres[row])
                        if not close(got_p, want_p, 1e-9):
                            problems.append(
                                f"node {j}: the certificate's pressure at "
                                f"s={s_half[row]:.6f} is {got_p!r}, the "
                                f"wout's pres {want_p!r}")

            blocks = [("RNODES", rmnc, (j - 1, j, j + 1)),
                      ("ZNODES", zmns, (j - 1, j, j + 1)),
                      ("LHALF", lmns, (j, j + 1))]
            if lasym:
                if not lasym_w:
                    # the antisymmetric halves are certified as zero
                    blocks += [("RNODES_A", None, (j - 1, j, j + 1)),
                               ("ZNODES_A", None, (j - 1, j, j + 1)),
                               ("LHALF_A", None, (j, j + 1))]
                else:
                    blocks += [("RNODES_A", rmns, (j - 1, j, j + 1)),
                               ("ZNODES_A", zmnc, (j - 1, j, j + 1)),
                               ("LHALF_A", lmnc, (j, j + 1))]
            for tag, arr, rows in blocks:
                r.expect(tag)
                for row in rows:
                    for k in range(K):
                        got = r.dyadic()
                        want = 0.0 if arr is None else arr[row][k]
                        check(f"node {j} {tag} row {row} mode {k}", got, want)
            prev = (j, sn, sh)

        nodes_seen += 1
        # The evaluated radius has to sit in the interval this node's
        # reconstruction is built on. That is the node's half-grid interval
        # everywhere except the two ends, where the two-node rule tiles between
        # the nodes themselves and so reaches the axis side and the boundary.
        if on_grid:
            check(f"node {j} evaluated radius", s_here, s_full[j])
        else:
            lo, hi = sh[0], sh[1]
            if out == "radial-axis":
                lo, hi = min(lo, sn[1]), max(hi, sn[2])
            if not (lo - a.radius_tol <= s_here <= hi + a.radius_tol):
                problems.append(
                    f"node {j}: the radius {s_here} lies outside [{lo}, {hi}]")

        # The pressure cubic of a piecewise profile against the wout's own
        # pressure. That cubic came from a reimplementation of VMEC's spline
        # and presf did not, so this is what says the two agree. A radial
        # covering carries one per node on an AMLOCAL line; a covering of one
        # surface resolves the piece once into the AM block.
        cubic = local_am if local_am is not None else (
            file_am if prof == "CUBIC" else None)
        if cubic is not None:
            if presf is None:
                problems.append(
                    f"node {j} carries a pressure cubic and the wout has no presf")
            else:
                t = float(s_here) - cubic[4]
                p = cubic[0] + t * (cubic[1] + t * (cubic[2] + t * cubic[3]))
                want = float(np.interp(float(s_here), s_full, presf))
                if abs(p - want) > a.pressure_tol * max(abs(want), 1e-30):
                    problems.append(
                        f"node {j}: the local pressure cubic gives {p!r} at "
                        f"s={s_here}, the wout's presf {want!r}")

        # The Boozer stream function, and the two flux functions beside it.
        # The coefficients are a float projection with nothing in the wout to
        # read them against, which is what --stream-defect bounds instead; the
        # flux functions are buco and bvco.
        if r.peek() == "WCOEF":
            r.next()
            m = r.int()
            if m != K:
                problems.append(f"WCOEF {m}, the certificate has {K} modes")
            for _ in range(K):
                r.dyadic()
            I_, G_ = r.dyadic(), r.dyadic()
            for nm, got, arr in (("I", I_, buco), ("G", G_, bvco)):
                if arr is None:
                    problems.append(f"node {j} carries {nm} and the wout has none")
                elif not close(got, arr[j + 1], a.flux_tol):
                    problems.append(
                        f"node {j} {nm}: certificate {got!r}, wout "
                        f"{arr[j + 1]!r}")

        # The flux function a two-term quasisymmetry certificate claims the
        # ratio equals. Nothing in the wout holds it, since it is a property
        # of the reconstruction the covering bounds the departure from, so
        # what is checked is that it is present and finite.
        if r.peek() == "FZERO":
            r.next()
            f0 = r.dyadic()
            if not (f0 == f0 and abs(f0) < float("inf")):
                problems.append(f"node {j}: FZERO is not a finite number")

        if cells:
            r.expect("CELLS")
            m = r.int()
            if m != na:
                problems.append(f"node {j}: CELLS {m}, NANGLES {na}")
            for _ in range(3 * m):
                for _ in range(n_bound):
                    r.int()

    if r.i != len(r.t):
        problems.append(f"{len(r.t) - r.i} tokens left unread")

    print(f"{a.cert}")
    third = f", third slot {slot3[0]}" if slot3 else ""
    print(f"  {kind}, {K} modes, {nb} node blocks, {na} cells per node, "
          f"slots {xu} and {xv}{third}, output {out}")
    print(f"  checked against {a.wout}: ns={ns}, "
          f"{'non-' if lasym_w else ''}stellarator-symmetric")
    if problems:
        print(f"\n  {len(problems)} disagreement(s) with the wout:")
        for p in problems[:20]:
            print(f"    {p}")
        if len(problems) > 20:
            print(f"    and {len(problems) - 20} more")
        return 1
    print("  every input slot matches the wout")
    return 0


if __name__ == "__main__":
    sys.exit(main())
