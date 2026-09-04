"""Regression suite for the checker.

Each case generates a certificate from a wout, runs the checker over it, and
compares the verdict and, where a certificate carries numbers, the numbers
themselves against values recorded here. A case that reproduces a published
figure is marked with the section of README.md it appears in, so a change that
moves a published number fails rather than passing quietly.

  python test/run_tests.py --data DIR [--main PATH] [--python PATH] [--slow]

DIR holds the wout files named below. Cases whose files are absent are skipped
and reported as such, so a partial data directory still exercises the rest,
and --data may be omitted entirely: test/data holds committed certificates, so
a fresh clone with no wout files still runs the checker over a verdict of each
kind. What those cases cannot exercise is the generator, which needs a wout.
"""

import argparse
import os
import pathlib
import re
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
GEN = ROOT / "gen" / "make_cert.py"


class Case:
    """One certificate: how to build it, how to run it, what to expect."""

    def __init__(self, name, wout, gen_args, expect="VALID", run_args=(),
                 tighten=False, integrate=None, worst=None, slow=False,
                 published=None):
        self.name = name
        self.wout = wout
        self.gen_args = gen_args
        self.expect = expect
        self.run_args = list(run_args)
        self.tighten = tighten
        self.integrate = integrate
        self.worst = worst
        self.slow = slow
        self.published = published


# Pointwise certificates over the two symmetry classes and four equilibria.
POINT = [
    Case("point/solovev", "wout_solovev.nc", "--nodes 6 --nu 8 --nv 4"),
    Case("point/cma", "wout_cma.nc", "--nodes 6 --nu 8 --nv 4"),
    Case("point/cth_like", "wout_cth_like_fixed_bdy.nc", "--nodes 6 --nu 8 --nv 4"),
    Case("point/up_down_asym", "wout_up_down_asym.nc", "--nodes 6 --nu 8 --nv 4"),
    # the antisymmetric path with zero antisymmetric coefficients has to
    # reproduce the symmetric one; this reduction is the solver oracle
    Case("point/solovev_lasym", "wout_solovev.nc",
         "--nodes 6 --nu 8 --nv 4 --force-lasym"),
    # the working precision steers the transcendental functions only, since
    # the carrier is binary64 whatever it says, so both ends have to pass
    Case("point/solovev_prec30", "wout_solovev.nc",
         "--nodes 6 --nu 8 --nv 4 --prec 30"),
    Case("point/solovev_prec100", "wout_solovev.nc",
         "--nodes 6 --nu 8 --nv 4 --prec 100"),
    # a denser sample than the six nodes the results table uses
    Case("point/cma_dense", "wout_cma.nc", "--nodes 20 --nu 32 --nv 8",
         slow=True),
]

# One perturbed coefficient has to break the verdict, in every block the
# reconstruction reads and at magnitudes down to a part in ten thousand. The
# claim is the unperturbed one: the bounds come from the converged file and
# the coefficients from the perturbed one, since a generator that recomputes
# its bounds from the perturbation would certify the perturbed equilibrium
# and prove nothing. A check that only ever sees converged equilibria is not
# being tested against the physics, only against the arithmetic.
PERTURB = [
    ("adversarial/rmnc_1e-3", "rmnc,22,1,0.001"),
    ("adversarial/rmnc_1e-4", "rmnc,22,1,0.0001"),
    ("adversarial/rmnc_1e-5", "rmnc,22,1,0.00001"),
    ("adversarial/zmns_1e-3", "zmns,22,1,0.001"),
    ("adversarial/lmns_1e-3", "lmns,22,1,0.001"),
    ("adversarial/rmnc_m0_1e-4", "rmnc,22,0,0.0001"),
]

# Every pressure parameterization VMEC++ admits.
FAMILIES = [
    ("power_series", "wout_solovev.nc", "--nodes 6 --nu 8 --nv 4"),
    ("two_power", "wout_cth_like_fixed_bdy.nc", "--nodes 6 --nu 8 --nv 4"),
    ("two_power_gs", "wout_solovev_two_power_gs.nc", "--nodes 6 --nu 8 --nv 4"),
    ("gauss_trunc", "wout_solovev_gauss_trunc.nc", "--nodes 6 --nu 8 --nv 4"),
    ("two_lorentz", "wout_solovev_two_lorentz.nc", "--nodes 6 --nu 8 --nv 4"),
    ("pedestal", "wout_solovev_pedestal.nc", "--nodes 6 --nu 8 --nv 4"),
    ("rational", "wout_solovev_rational.nc", "--nodes 6 --nu 8 --nv 4"),
    ("cubic_spline", "wout_solovev_cubic_spline.nc", "--node 22 --nu 8 --nv 4"),
    ("akima_spline", "wout_solovev_akima_spline.nc", "--node 22 --nu 8 --nv 4"),
    ("line_segment", "wout_solovev_line_segment.nc", "--node 22 --nu 8 --nv 4"),
]
POINT += [Case("pressure/" + n, w, a) for n, w, a in FAMILIES]

# Cell certificates: the bound holds between the sampled angles.
CELLS = [
    Case("cell/solovev_512", "wout_solovev.nc", "--cells --node 22 --nu 512",
         tighten=True),
    Case("cell/solovev_8192", "wout_solovev.nc",
         "--cells --nodes 6 --nu 8192", tighten=True, worst=1.323648e-05,
         slow=True, published="Results, cells table"),
    # the three terms the residual is the difference of, carried as the three
    # components. They are far larger than it, which is what the covering pays
    # for, so their cell bounds are far larger too.
    Case("cell/solovev_terms", "wout_solovev.nc",
         "--cells --node 22 --nu 256 --terms", tighten=True,
         worst=1.291589e-02),
    Case("cell/solovev_terms_radial", "wout_solovev.nc",
         "--radial --node 22 --nu 128 --nrad 4 --terms", tighten=True,
         worst=1.686738e-02),
]

# Angular integrals, against the intervals quoted in the README.
INTEGRALS = [
    Case("integral/geometry", "wout_solovev.nc",
         "--cells --node 22 --nu 512 --geometry", tighten=True,
         integrate={"sqrt(g)": (-1.262214040e+02, -1.262202659e+02),
                    "B_u": (1.441907735e+00, 1.442042819e+00)},
         published="Integrals over a surface"),
    Case("integral/mercier_a", "wout_solovev.nc",
         "--cells --node 22 --nu 512 --mercier a", tighten=True,
         integrate={"tpp": (-3.287709630e+03, -3.287507349e+03),
                    "tbb": (-5.085479847e+00, -5.084537113e+00),
                    "tjb": (2.806504072e+00, 2.813083414e+00)},
         published="Mercier"),
    Case("integral/mercier_b", "wout_solovev.nc",
         "--cells --node 22 --nu 512 --mercier b", tighten=True,
         integrate={"tjj": (-1.569705226e+00, -1.535477750e+00)},
         published="Mercier"),
]

# The radius as a varied slot: the bound holds between surfaces.
RADIAL = [
    Case("radial/solovev_node22", "wout_solovev.nc",
         "--radial --node 22 --nu 512 --nrad 8", tighten=True,
         worst=1.050222e-03),
    # widened to the toroidal angle: for an axisymmetric case the bound must
    # not move, since that derivative is the zero expression
    Case("radial/three_slots", "wout_solovev.nc",
         "--radial --node 22 --nu 256 --nrad 8", tighten=True,
         run_args=("--slot3", "2", "3600000000000000")),
    Case("radial/solovev_volume", "wout_solovev.nc",
         "--radial --nodes 52 --nu 128 --nrad 8", tighten=True,
         worst=5.606857e-01, slow=True, published="Over the volume"),
    # the third slot carried by the file rather than by the command line, so
    # what the run produces is a certificate another party re-checks. The
    # bound has to be the one the two-slot covering gave, since the toroidal
    # derivative of an axisymmetric reconstruction is the zero expression
    Case("radial/slot3_file", "wout_solovev.nc",
         "--radial --node 22 --nu 256 --nrad 8 --slot3 2", tighten=True,
         worst=2.170772e-03),
    # a piecewise pressure covered radially across its knots: the covering is
    # split at each knot and every node block carries the cubic of its piece
    Case("radial/spline_pieces", "wout_solovev_cubic_spline.nc",
         "--radial --nodes 20 --nu 128 --nrad 8", tighten=True,
         worst=5.606854e-01),
    # the innermost interval, between the first two half points, where the
    # coefficients come from the two innermost nodes because no inner half
    # point exists
    Case("radial/axis_piece", "wout_solovev.nc",
         "--radial --axis --node 1 --nu 128 --nrad 128", tighten=True,
         worst=5.284583e-02),
    # the outermost interval, between the last two nodes, which is where a
    # covering built on half points stops short of the boundary
    Case("radial/edge_piece", "wout_solovev.nc",
         "--radial --edge --nu 128 --nrad 32", tighten=True,
         worst=2.247683e-03),
]

# The reconstruction against VMEC's own field arrays. Physics.v is
# definitional, and its float reference is by the same hand, so this is the
# check that reaches outside the development: at a half point the wout stores
# B^u, B^v and sqrt(g), and the reconstruction has to reproduce them. Both
# symmetry classes and both dimensionalities are here, since the antisymmetric
# half and the toroidal one are where an encoding slip would hide.
FIELD = [
    ("field/solovev", "wout_solovev.nc", 2.0e-06),
    ("field/cth_like", "wout_cth_like_fixed_bdy.nc", 2.0e-05),
    ("field/cma", "wout_cma.nc", 2.0e-04),
    ("field/up_down_asym", "wout_up_down_asym.nc", 5.0e-04),
    # the worst of the published table, where what is left over is the
    # difference between an exact product of series and the Nyquist fit VMEC
    # stores for it, and the mode set barely resolves the equilibrium
    ("field/li383_low_res", "wout_li383_low_res.nc", 2.5e-02),
]


# What the checker refuses. An integral is a statement about a tiling, so a
# covering that leaves gaps has to be turned away rather than summed, and a
# three-dimensional surface covered by curves is not covered. Both are checks
# on the gap between what a theorem assumes and what the driver does, which is
# the gap this whole development exists to close.
REFUSALS = [
    ("refuses/gapped_integral", "wout_solovev.nc",
     "--cells --node 22 --nu 64 --geometry --wscale 0.5", True,
     "--integrate", "leave a gap"),
]


# The criterion over a profile rather than one surface, which is where it says
# something about an equilibrium rather than about a flux surface.
PROFILE = [
    ("mercier/solovev_profile", "wout_solovev.nc", 4, 256, 3),
]


# The Boozer angles. The stream function is float data the certificate
# carries, so what makes it usable is the certified defect of the two
# relations that define it, and the harmonics computed from it carry the
# Jacobian of the angle map, whose integral has to be 4 pi^2 because the map
# is a bijection of the torus.
BOOZER = [
    ("boozer/solovev_node22", "wout_solovev.nc", 22, 512,
     # the defect of each relation, at most
     (5.0e-05, 5.0e-04),
     # B_00 of |B| in the Boozer angles
     (2.053361982e-01, 2.053437394e-01)),
]


# The certified residual against resolution. These need a family of the same
# equilibrium at several resolutions, which gen/families.py produces with
# VMEC++; without them the cases skip. The first requires the measured order in
# the grid spacing to be second, which is what discretization_is_consistent
# assumes, and the second requires each enlargement of the mode set to buy a
# factor, which is what says a flat radial family is at its spectral floor.
CONVERGENCE = [
    ("convergence/solovev_order",
     ["wout_solovev_m12_ns13.nc", "wout_solovev_m12_ns25.nc",
      "wout_solovev_m12_ns51.nc"],
     "--half-grid", "order", (1.7, 2.2)),
    ("convergence/li383_spectral",
     ["wout_li383_m4n3.nc", "wout_li383_m6n4.nc", "wout_li383_m8n6.nc"],
     "--half-grid --nu 256", "ratio", (3.0, 1.0e9)),
    # a stellarator whose radial grid does nothing: every ratio near one
    ("convergence/cma_flat",
     ["wout_cma_ns15.nc", "wout_cma_ns25.nc", "wout_cma_ns51.nc",
      "wout_cma_ns101.nc"],
     "--half-grid --nu 256", "ratio", (0.9, 1.2)),
]


# How far the residual is from the three terms it is the difference of. Where
# they agree to several digits the bound is a cancellation defect and a finer
# covering reaches it; where they do not, the reconstruction is out of balance
# by something of its own size and no refinement of the arithmetic does. The
# separation between solovev and the rest is the published figure, so each case
# requires the measured factor to stay in its band.
CANCEL = [
    ("cancel/solovev", "wout_solovev.nc", "--nodes 8 --nu 256", (5.0e2, 5.0e4)),
    ("cancel/cth_like", "wout_cth_like_fixed_bdy.nc", "--nodes 5 --nu 128",
     (0.5, 30.0)),
    ("cancel/cma", "wout_cma.nc", "--nodes 5 --nu 128", (0.9, 1.2)),
    ("cancel/up_down_asym", "wout_up_down_asym.nc", "--nodes 5 --nu 128",
     (0.4, 6.0)),
    ("cancel/li383", "wout_li383_low_res.nc", "--nodes 5 --nu 128", (0.4, 3.0)),
]


# The claim itself, that enlarging the mode set raises the cancellation: the
# largest ratio over the profile at the largest mode set has to exceed the one
# at the smallest by the recorded factor.
MODESETS = [
    ("modes/cth_like_rises", "wout_cthS_ns51_m5n4.nc", "wout_cthS_ns51_m9n8.nc",
     "--nodes 4 --nu 128", 2.0),
    ("modes/li383_rises", "wout_li383_m4n3.nc", "wout_li383_m8n6.nc",
     "--nodes 4 --nu 128", 5.0),
]


# A floor over a box of coefficients rather than at one field. The cells range
# over one rmnc coefficient and the poloidal angle, so a passing verdict
# excludes every field whose coefficient lies in that interval, at every angle
# the cells cover. The box is offset from the converged value, since a box
# containing it contains a field that does balance.
COEFBOX = [
    ("obstruction/coefbox_rmnc", "wout_solovev.nc",
     "--cells --node 22 --nu 256 --coefbox rmnc,1,1,0.0005 "
     "--perturb rmnc,22,1,0.001", 231),
]

# The certified enclosure at a cell centre against an independently written
# float implementation of the same reconstruction. A disagreement means the
# physics was encoded into `expr` wrongly, which no amount of interval
# soundness would catch, so this is the case that guards the correspondence
# between theories/Physics.v and the rule it is supposed to state.
REFERENCE = [
    ("reference/solovev_node22", "wout_solovev.nc", 22,
     "--radial --node 22 --nu 512 --nrad 8", 0.39930555555555625),
]

# Certificates carry their inputs, and nothing inside the proof ties those
# inputs to a wout. gen/verify_cert.py reads both and compares; these cases
# check that it passes what belongs together and rejects what does not, which
# is the only guard against a certificate that is sound about the wrong
# equilibrium.
#
# Every form the generator writes is here, because a guard that reads only
# some of them leaves the rest tied to nothing. A radial covering repeats a
# node with SAME and carries its own pressure piece; a stream function arrives
# with two flux functions beside it; a third slot adds two numbers to every
# bound line; and four of the outputs put a mode pair on the OUTPUT line.
CORRESPOND = [
    ("correspond/solovev", "wout_solovev.nc", "wout_solovev.nc",
     "--cells --node 22 --nu 64", True),
    ("correspond/wrong_wout", "wout_solovev.nc", "wout_cma.nc",
     "--cells --node 22 --nu 64", False),
    ("correspond/radial", "wout_solovev.nc", "wout_solovev.nc",
     "--radial --node 22 --nu 32 --nrad 4", True),
    ("correspond/radial_wrong", "wout_solovev.nc", "wout_cma.nc",
     "--radial --node 22 --nu 32 --nrad 4", False),
    ("correspond/slot3", "wout_solovev.nc", "wout_solovev.nc",
     "--radial --node 22 --nu 32 --nrad 4 --slot3 2", True),
    ("correspond/axis_piece", "wout_solovev.nc", "wout_solovev.nc",
     "--radial --axis --node 1 --nu 32 --nrad 4", True),
    ("correspond/edge_piece", "wout_solovev.nc", "wout_solovev.nc",
     "--radial --edge --nu 32 --nrad 4", True),
    ("correspond/stream", "wout_solovev.nc", "wout_solovev.nc",
     "--cells --node 22 --nu 32 --stream-defect", True),
    ("correspond/covariant", "wout_solovev.nc", "wout_solovev.nc",
     "--cells --node 22 --nu 32 --covariant 1,0", True),
    ("correspond/lasym", "wout_up_down_asym.nc", "wout_up_down_asym.nc",
     "--cells --node 8 --nu 32 --nv 4 --surface", True),
    ("correspond/terms", "wout_solovev.nc", "wout_solovev.nc",
     "--cells --node 22 --nu 32 --terms", True),
    ("correspond/terms_radial", "wout_solovev.nc", "wout_solovev.nc",
     "--radial --node 22 --nu 32 --nrad 4 --terms", True),
    # the piecewise pressures, whose cubic is the one block a wout constrains
    # only through presf: once per node under a radial covering, and once for
    # the file when a single surface resolves it
    ("correspond/spline_pieces", "wout_solovev_cubic_spline.nc",
     "wout_solovev_cubic_spline.nc", "--radial --nodes 6 --nu 16 --nrad 4",
     True),
    ("correspond/spline_node", "wout_solovev_cubic_spline.nc",
     "wout_solovev_cubic_spline.nc", "--node 22 --nu 8 --nv 4", True),
    ("correspond/akima_node", "wout_solovev_akima_spline.nc",
     "wout_solovev_akima_spline.nc", "--node 22 --nu 8 --nv 4", True),
    ("correspond/segment_node", "wout_solovev_line_segment.nc",
     "wout_solovev_line_segment.nc", "--node 22 --nu 8 --nv 4", True),
    # a pedestal, whose am block the generator carries whole when the tanh
    # term is on and truncates to its polynomial when the width switches it off
    ("correspond/pedestal", "wout_solovev_pedestal.nc",
     "wout_solovev_pedestal.nc", "--node 22 --nu 8 --nv 4", True),
    # a profile run with PRES_SCALE, which the wout does not carry: the
    # certificate's amplitude differs from the file's am by that factor and
    # the guard reads the pressure back against pres instead
    ("correspond/pres_scale", "wout_cth_like_fixed_bdy.nc",
     "wout_cth_like_fixed_bdy.nc", "--node 12 --nu 8 --nv 4", True),
]

# The Mercier criterion, assembled inside the checker by theories/Mercier.v.
# Each case runs the four coverings, hands the enclosures to `main --mercier`,
# and compares the verdict and the assembled terms with the wout's own D*
# arrays. The file's number has to lie inside the certified enclosure of every
# term, which is the statement the assembly makes, and the verdict has to be
# the one recorded.
MERCIER = [
    # flat iota and finite pressure: the well decides it
    ("mercier/solovev_node22", "wout_solovev.nc", 22, 512, "UNSTABLE"),
    # strong shear, no pressure, non-stellarator-symmetric: DShear, DCurr and
    # DGeod all contribute and DWell is zero
    ("mercier/up_down_asym_node8", "wout_up_down_asym.nc", 8, 512, "STABLE"),
]


# Certificates committed beside the suite, so a clone with no wout files can
# still run the checker over a verdict of each kind.
STANDALONE = [
    ("standalone/points", "cert_solovev_points.txt", (), "VALID"),
    ("standalone/cells", "cert_solovev_cells.txt", (), "VALID"),
    ("standalone/cells_taylor", "cert_solovev_cells.txt", ("--taylor",), "VALID"),
]

# The Taylor bound carried in a certificate file, which another party
# re-checks with check_ccert_t rather than trusting the run that wrote it, the
# way a SLOT3 file is re-checked. The generator marks the file, --tighten
# --taylor writes the ten-number bounds, and an ordinary run establishes them.
TAYLORFILE = [
    Case("taylor/solovev_file", "wout_solovev.nc",
         "--cells --node 22 --nu 256 --taylor", tighten=True,
         run_args=("--taylor",), worst=3.706373e-04),
]

ALL = POINT + CELLS + INTEGRALS + RADIAL + TAYLORFILE


def run(cmd, cwd=None):
    """Run a command and return (returncode, combined output)."""
    p = subprocess.run(cmd, shell=True, cwd=cwd, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def check_case(c, data, main, python, tmp):
    """Build, run and compare one case. Returns (status, detail)."""
    wout = data / c.wout
    if not wout.exists():
        return "skip", f"{c.wout} absent"
    src = tmp / (c.name.replace("/", "_") + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" {c.gen_args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]

    target = src
    if c.tighten:
        target = tmp / (src.stem + "_c.txt")
        rc, out = run(f'"{main}" --tighten "{src}" "{target}"')
        if rc != 0:
            return "fail", "tighten: " + out.strip().splitlines()[-1]
        if c.worst is not None:
            m = re.search(r"worst cell bound ([0-9.e+-]+)", out)
            if not m:
                return "fail", "tighten printed no worst bound"
            got = float(m.group(1))
            if abs(got - c.worst) > 1e-9 * abs(c.worst):
                return "fail", f"worst bound {got:.6e}, recorded {c.worst:.6e}"

    if c.integrate is not None:
        rc, out = run(f'"{main}" --integrate "{target}"')
        if rc != 0:
            return "fail", "integrate: " + out.strip().splitlines()[-1]
        for label, (lo, hi) in c.integrate.items():
            m = re.search(re.escape(label) + r"\s+\[([0-9.e+-]+), ([0-9.e+-]+)\]", out)
            if not m:
                return "fail", f"integrate printed no {label}"
            glo, ghi = float(m.group(1)), float(m.group(2))
            if abs(glo - lo) > 1e-9 * abs(lo) or abs(ghi - hi) > 1e-9 * abs(hi):
                return "fail", (f"{label} [{glo:.9e}, {ghi:.9e}], recorded "
                                f"[{lo:.9e}, {hi:.9e}]")
        return "ok", "integrals match"

    rc, out = run(f'"{main}" {" ".join(c.run_args)} "{target}"')
    m = re.search(r"verdict: (\w+)", out)
    got = m.group(1) if m else "NONE"
    if got != c.expect:
        return "fail", f"verdict {got}, expected {c.expect}"
    return "ok", got


def check_mercier(name, wout, node, nu, expect, main, python):
    """The assembled criterion against the wout's own Mercier arrays."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    tool = ROOT / "gen" / "mercier.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}" --node {node} --nu {nu} '
                  f'--main "{main}"')
    if rc != 0 and "verdict" not in out:
        return "fail", "mercier: " + out.strip().splitlines()[-1]
    m = re.search(r"verdict: (\w+)", out)
    got = m.group(1) if m else "NONE"
    if got != expect:
        return "fail", f"verdict {got}, expected {expect}"
    # every term of the file has to sit inside the certified enclosure
    terms = {}
    for label in ("DShear", "DCurr", "DWell", "DGeod", "DMerc"):
        m = re.search(r"  " + label + r"\s+\[([0-9.e+-]+), ([0-9.e+-]+)\]", out)
        if not m:
            return "fail", f"no enclosure for {label}"
        terms[label] = (float(m.group(1)), float(m.group(2)))
    theirs = {}
    for label in ("DShear", "DCurr", "DWell", "DGeod", "DMerc"):
        m = re.search(r"  " + label + r"\s+([0-9.e+-]+)\n", out)
        if m:
            theirs[label] = float(m.group(1))
    for label, v in theirs.items():
        lo, hi = terms[label]
        # the enclosures are of the reconstruction's own criterion, and V''
        # differs from the file's difference quotient by a fraction of a
        # percent, so DWell and the terms carrying it are allowed that much
        pad = 0.02 * max(abs(lo), abs(hi))
        if not (lo - pad <= v <= hi + pad):
            return "fail", (f"{label} {v:.6e} outside the certified "
                            f"[{lo:.6e}, {hi:.6e}]")
    return "ok", f"{got}, all five terms bracket the file"


def check_correspondence(name, made_from, checked_against, gen_args, agree,
                         python, tmp):
    """A certificate against the wout it is claimed to describe."""
    for w in (made_from, checked_against):
        if not w.exists():
            return "skip", f"{w.name} absent"
    src = tmp / (name.replace("/", "_") + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{made_from}" "{src}" {gen_args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    ver = ROOT / "gen" / "verify_cert.py"
    rc, out = run(f'"{python}" "{ver}" "{checked_against}" "{src}"')
    matched = rc == 0
    if matched != agree:
        return "fail", ("accepted a certificate about a different wout"
                        if matched else
                        "rejected a certificate about its own wout")
    return "ok", ("inputs match the wout" if agree else
                  "rejected, as it describes a different equilibrium")


def check_field(name, wout, tol, python):
    """The reconstructed field against the wout's own arrays."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    tool = ROOT / "proto" / "field_check.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}"')
    if rc != 0:
        return "fail", "field_check: " + out.strip().splitlines()[-1]
    m = re.search(r"worst relative difference from the wout's own field: "
                  r"([0-9.e+-]+)", out)
    if not m:
        return "fail", "no worst difference reported"
    got = float(m.group(1))
    if got > tol:
        return "fail", f"{got:.3e} from the wout's own field, over {tol:.0e}"
    return "ok", f"{got:.3e} from the wout's own field"


def check_refusal(name, wout, gen_args, tighten, run_args, expect, main,
                  python, tmp):
    """A run that has to fail, with the reason it has to give."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    src = tmp / (name.replace("/", "_") + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" {gen_args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    target = src
    if tighten:
        target = tmp / (src.stem + "_c.txt")
        rc, out = run(f'"{main}" --tighten "{src}" "{target}"')
        if rc != 0:
            return "fail", "tighten: " + out.strip().splitlines()[-1]
    rc, out = run(f'"{main}" {run_args} "{target}"')
    if rc == 0:
        return "fail", "the run was accepted when it had to be refused"
    if expect not in out:
        return "fail", f"refused, but not for {expect!r}"
    return "ok", f"refused: {expect}"


def check_profile(name, wout, nodes, nu, least_unstable, main, python):
    """The criterion at every surface of one equilibrium."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    tool = ROOT / "gen" / "mercier.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}" --profile {nodes} --nu {nu} '
                  f'--main "{main}"')
    if rc != 0 and "surfaces proven" not in out:
        return "fail", "profile: " + out.strip().splitlines()[-1]
    m = re.search(r"(\d+) surfaces proven unstable, (\d+) proven stable, "
                  r"(\d+) undecided", out)
    if not m:
        return "fail", "no profile summary"
    uns, sta, opn = (int(m.group(i)) for i in (1, 2, 3))
    if uns < least_unstable:
        return "fail", f"{uns} surfaces proven unstable, wanted "\
                       f"{least_unstable}"
    # every surface carries what a relative error in each input does to the
    # criterion, which is what says whether the data determines it
    if not re.search(r"averages", out):
        return "fail", "no sensitivity columns"
    return "ok", f"{uns} unstable, {sta} stable, {opn} undecided"


def check_boozer(name, wout, node, nu, defect_max, b00, main, python):
    """The stream function's defect, and the spectrum it gives."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    tool = ROOT / "gen" / "boozer.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}" --node {node} --nu {nu} '
                  f'--defect --spectrum 0,0')
    if rc != 0:
        return "fail", "boozer: " + out.strip().splitlines()[-1]
    du = re.search(r"d_u w - \(B_u - I\)\s+at most ([0-9.e+-]+)", out)
    dv = re.search(r"d_v w - \(B_v - G\)\s+at most ([0-9.e+-]+)", out)
    if not du or not dv:
        return "fail", "no defect bounds"
    if float(du.group(1)) > defect_max[0] or float(dv.group(1)) > defect_max[1]:
        return "fail", (f"defect {du.group(1)}, {dv.group(1)} above "
                        f"{defect_max}")
    if "DOES NOT bracket" in out:
        return "fail", "the Jacobian of the angle map does not integrate to "\
                       "4 pi^2"
    m = re.search(r"B cos\s+\[([0-9.e+-]+), ([0-9.e+-]+)\]", out)
    if not m:
        return "fail", "no B_00"
    lo, hi = float(m.group(1)), float(m.group(2))
    if abs(lo - b00[0]) > 1e-9 * abs(b00[0]) or \
       abs(hi - b00[1]) > 1e-9 * abs(b00[1]):
        return "fail", (f"B_00 [{lo:.9e}, {hi:.9e}], recorded "
                        f"[{b00[0]:.9e}, {b00[1]:.9e}]")
    return "ok", f"defect {du.group(1)}, B_00 [{lo:.6e}, {hi:.6e}]"


def check_convergence(name, wouts, args, column, bounds, data, main, python):
    """The measured order, or the gain per mode set, inside its bounds."""
    missing = [w for w in wouts if not (data / w).exists()]
    if missing:
        return "skip", f"{missing[0]} absent"
    tool = ROOT / "gen" / "convergence.py"
    rc, out = run(f'"{python}" "{tool}" {args} --data "{data}" --main "{main}" '
                  + " ".join(wouts))
    if rc != 0:
        return "fail", "convergence: " + out.strip().splitlines()[-1]
    got = []
    for line in out.splitlines():
        f = line.split()
        # ns modes h s residual ratio [order]
        if len(f) >= 6 and f[0].isdigit() and f[1].isdigit():
            if column == "ratio" and len(f) >= 6:
                got.append(float(f[5]))
            elif column == "order" and len(f) >= 7:
                got.append(float(f[6]))
    if not got:
        return "fail", f"no {column} column in the output"
    lo, hi = bounds
    bad = [x for x in got if not (lo <= x <= hi)]
    if bad:
        return "fail", f"{column} {bad[0]:.2f} outside [{lo}, {hi}]"
    shown = ", ".join(f"{x:.2f}" for x in got)
    return "ok", f"{column} {shown}"


def check_coefbox(name, wout, gen_args, expect_cells, main, python, tmp):
    """A floor proven over an interval of one coefficient."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    src = tmp / (name.replace("/", "_") + ".txt")
    dst = tmp / (name.replace("/", "_") + "_c.txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" {gen_args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    rc, out = run(f'"{main}" --tighten --lower --filter "{src}" "{dst}"')
    if rc != 0:
        return "fail", "tighten: " + out.strip().splitlines()[-1]
    rc, out = run(f'"{main}" --lower "{dst}"')
    m = re.search(r"(\d+) of (\d+) cells proven out of force balance", out)
    if not m:
        return "fail", "no count of cells out of balance"
    got, total = int(m.group(1)), int(m.group(2))
    if got != total:
        return "fail", f"{got} of {total} cells carried a floor"
    if got != expect_cells:
        return "fail", f"{got} cells kept, recorded {expect_cells}"
    return "ok", f"{got} cells, every field in the box out of balance"


def check_perturbed(name, wout, perturb, main, python, tmp):
    """The unperturbed claim, read against perturbed coefficients."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    good = tmp / (name.replace("/", "_") + "_good.txt")
    bad = tmp / (name.replace("/", "_") + "_bad.txt")
    args = "--node 22 --nu 8 --nv 1"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{good}" {args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{bad}" {args} '
                  f'--perturb {perturb}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    claim = {}
    for line in good.read_text().splitlines():
        if line.startswith(("EPS_S", "EPS_U", "EPS_V")):
            claim[line.split()[0]] = line
    spliced = []
    for line in bad.read_text().splitlines():
        tag = line.split()[0] if line else ""
        spliced.append(claim[tag] if tag in claim else line)
    mixed = tmp / (name.replace("/", "_") + "_mixed.txt")
    mixed.write_text("\n".join(spliced) + "\n")
    rc, out = run(f'"{main}" "{mixed}"')
    m = re.search(r"verdict: (\w+)", out)
    got = m.group(1) if m else "NONE"
    if got != "INVALID":
        return "fail", f"the perturbed coefficients still pass: {got}"
    return "ok", "INVALID against the converged claim"


def check_halfgrid(name, wout, node, main, python, tmp):
    """The pointwise residual against an implementation that shares no code.

    proto/continuum_ref.py --half-grid writes VMEC's parity rule out again,
    from the rule rather than from the expression builders, so a disagreement
    means one of the two has the physics wrong. The reference has to agree
    with the generator's own float pass, and the checker has to accept a bound
    a hair above what the reference says and reject one just below it, which
    brackets the certified enclosure against a number nothing in the
    development produced twice.
    """
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    ref = ROOT / "proto" / "continuum_ref.py"
    rc, out = run(f'"{python}" "{ref}" "{wout}" --node {node} --nu 8 '
                  f'--half-grid')
    if rc != 0:
        return "fail", "reference: " + out.strip().splitlines()[-1]
    m = re.search(r"worst per component: ([0-9.e+-]+) ([0-9.e+-]+) "
                  r"([0-9.e+-]+)", out)
    if not m:
        return "fail", "the reference printed no value"
    want = [float(m.group(i)) for i in (1, 2, 3)]

    src = tmp / (name.replace("/", "_") + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" --node {node} '
                  f'--nu 8 --nv 1 --slack 1.0001')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    m = re.search(r"\|r\|max = ([0-9.e+-]+) ([0-9.e+-]+) ([0-9.e+-]+)", out)
    if not m:
        return "fail", "the generator printed no maximum"
    got = [float(m.group(i)) for i in (1, 2, 3)]
    # the generator prints three decimals, which is what limits this
    for k, (g, w_) in enumerate(zip(got, want, strict=True)):
        if abs(g - w_) > 1e-3 * abs(w_):
            return "fail", (f"component {k}: the generator says {g:.9e}, the "
                            f"reference {w_:.9e}")
    rc, out = run(f'"{main}" "{src}"')
    if "verdict: VALID" not in out:
        return "fail", "a bound a hair above the reference was rejected"

    tight = tmp / (name.replace("/", "_") + "_tight.txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{tight}" --node {node} '
                  f'--nu 8 --nv 1 --slack 0.99')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    rc, out = run(f'"{main}" "{tight}"')
    if "verdict: INVALID" not in out:
        return "fail", "a bound below the reference was accepted"
    return "ok", f"brackets the reference {want[0]:.6e} from both sides"


def check_terms_reference(name, wout, node, nu, main, python):
    """The three certified terms against a float reference of the same three.

    Nothing about a verdict says the components of a terms certificate are the
    terms the residual is assembled from: they are three more expressions the
    checker bounds, and it would bound the wrong three as readily. The
    reference is written from the rule rather than from the expression
    builders, and it also reports its own difference of the three against its
    own residual, so a mis-wiring shows up as a disagreement rather than as a
    plausible table.
    """
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    ref = ROOT / "proto" / "continuum_ref.py"
    rc, out = run(f'"{python}" "{ref}" "{wout}" --node {node} --nu {nu} '
                  f'--half-grid --cells')
    if rc != 0:
        return "fail", "reference: " + out.strip().splitlines()[-1]
    m = re.search(r"terms\s+([0-9.e+-]+)\s+([0-9.e+-]+)\s+([0-9.e+-]+)", out)
    d = re.search(r"their difference ([0-9.e+-]+) against r_s ([0-9.e+-]+)",
                  out)
    if not m or not d:
        return "fail", "the reference printed no terms"
    want = [float(m.group(i)) for i in (1, 2, 3)]
    if abs(float(d.group(1)) - float(d.group(2))) > 1e-12 * abs(want[0]):
        return "fail", "the reference's own three terms do not give its r_s"

    tool = ROOT / "gen" / "cancellation.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}" --node {node} --nu {nu} '
                  f'--main "{main}"')
    if rc != 0:
        return "fail", "cancellation: " + out.strip().splitlines()[-1]
    row = None
    for line in out.splitlines():
        f = line.split()
        # s u t1 t2 t3 r_s ratio share
        if len(f) == 8:
            try:
                s = float(f[0])
            except ValueError:
                continue
            if 0.0 <= s <= 1.0:
                row = [float(x) for x in f[2:5]]
    if row is None:
        return "fail", "no terms row in the output"
    # each certified magnitude is an upper bound grown until the check passed,
    # so it sits a hair above the reference and never below it
    for k, (got, w) in enumerate(zip(row, want, strict=True)):
        if got < w * (1 - 1e-9):
            return "fail", (f"term {k} certified {got:.9e} below the "
                            f"reference {w:.9e}")
        if got > w * 1.001:
            return "fail", (f"term {k} certified {got:.9e} far above the "
                            f"reference {w:.9e}")
    return "ok", ("the three terms bracket the reference, whose own "
                  "difference is its r_s")


def cancellation_ratios(wout, args, main, python):
    """The per-node cancellation factors gen/cancellation.py prints."""
    tool = ROOT / "gen" / "cancellation.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}" {args} --main "{main}"')
    if rc != 0:
        return None, "cancellation: " + out.strip().splitlines()[-1]
    got = []
    for line in out.splitlines():
        f = line.split()
        # s u t1 t2 t3 r_s ratio share
        if len(f) == 8:
            try:
                s, ratio = float(f[0]), float(f[6])
            except ValueError:
                continue
            if 0.0 <= s <= 1.0:
                got.append(ratio)
    if not got:
        return None, "no cancellation column in the output"
    return got, None


def check_terms_reference_radial(name, wout, node, nu, nrad, main, python):
    """The three certified terms of the free-radius residual against the float
    reference at the same point.

    A volume covering's worst cell sits at a radius between the half points and
    an angle between the samples, so the reference is read at exactly that
    point rather than on a grid of its own.
    """
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    tool = ROOT / "gen" / "cancellation.py"
    rc, out = run(f'"{python}" "{tool}" "{wout}" --radial --node {node} '
                  f'--nu {nu} --nrad {nrad} --exact --main "{main}"')
    if rc != 0:
        return "fail", "cancellation: " + out.strip().splitlines()[-1]
    rows = []
    lines = out.splitlines()
    for i, line in enumerate(lines):
        f = line.split()
        if len(f) == 8:
            try:
                s = float(f[0])
            except ValueError:
                continue
            if 0.0 <= s <= 1.0 and i + 1 < len(lines):
                m = re.search(r"exact s=([0-9.e+-]+) u=([0-9.e+-]+)",
                              lines[i + 1])
                if m:
                    rows.append((float(m.group(1)), float(m.group(2)),
                                 [float(x) for x in f[2:5]]))
    if not rows:
        return "fail", "no worst cell with an exact position"
    ref = ROOT / "proto" / "continuum_ref.py"
    for s, u, got in rows:
        rc, out = run(f'"{python}" "{ref}" "{wout}" --node {node} --nu 1 '
                      f'--at {s!r} --u {u!r}')
        if rc != 0:
            return "fail", "reference: " + out.strip().splitlines()[-1]
        m = re.search(r"terms\s+([0-9.e+-]+)\s+([0-9.e+-]+)\s+([0-9.e+-]+)",
                      out)
        if not m:
            return "fail", "the reference printed no terms"
        want = [float(m.group(i)) for i in (1, 2, 3)]
        for k, (g, w) in enumerate(zip(got, want, strict=True)):
            if g < w * (1 - 1e-9):
                return "fail", (f"term {k} certified {g:.9e} below the "
                                f"reference {w:.9e} at s={s:.5f}")
            if g > w * 1.001:
                return "fail", (f"term {k} certified {g:.9e} far above the "
                                f"reference {w:.9e} at s={s:.5f}")
    return "ok", (f"{len(rows)} radial cells, the three terms bracket the "
                  f"reference at each")


def check_cancellation(name, wout, args, band, main, python):
    """The residual against the terms it is the difference of."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    got, why = cancellation_ratios(wout, args, main, python)
    if got is None:
        return "fail", why
    lo, hi = band
    bad = [x for x in got if not (lo <= x <= hi)]
    if bad:
        return "fail", f"a factor of {bad[0]:.3g} outside [{lo:g}, {hi:g}]"
    return "ok", f"{min(got):.3g} to {max(got):.3g}"


def check_modesets(name, coarse, fine, args, factor, main, python):
    """Adding modes has to raise the cancellation by the recorded factor."""
    for w in (coarse, fine):
        if not w.exists():
            return "skip", f"{w.name} absent"
    lo, why = cancellation_ratios(coarse, args, main, python)
    if lo is None:
        return "fail", why
    hi, why = cancellation_ratios(fine, args, main, python)
    if hi is None:
        return "fail", why
    gain = max(hi) / max(lo)
    if gain < factor:
        return "fail", (f"the largest factor rose from {max(lo):.3g} to "
                        f"{max(hi):.3g}, under the recorded {factor:g}")
    return "ok", f"the largest factor rises from {max(lo):.3g} to {max(hi):.3g}"


def swap_coefficients(lines):
    """Two entries of one coefficient row exchanged, which is what a
    transposed array would do to a whole block."""
    idx = next((i for i, l in enumerate(lines) if l.strip() == "RNODES"), None)
    if idx is None:
        return None, "no RNODES block in the certificate"
    row = lines[idx + 1].split()
    if len(row) < 4:
        return None, "the coefficient row is too short to permute"
    row[0], row[1], row[2], row[3] = row[2], row[3], row[0], row[1]
    lines[idx + 1] = " ".join(row)
    return lines, None


def rescale_pressure_piece(lines):
    """A node's pressure cubic halved, which is what a calibration read from
    the wrong quantity would do to every piece of a covering."""
    idx = next((i for i, l in enumerate(lines) if l.startswith("AMLOCAL")),
               None)
    if idx is None:
        return None, "no AMLOCAL block in the certificate"
    for k in range(1, 5):
        f = lines[idx + k].split()
        lines[idx + k] = f"{f[0]} {int(f[1]) - 1}"
    return lines, None


def unscale_amplitude(lines):
    """The profile's amplitude halved, which is a certificate about a
    pressure the equilibrium does not balance, with every other coefficient
    the file's own."""
    idx = next((i for i, l in enumerate(lines) if l.startswith("AM ")), None)
    if idx is None:
        return None, "no AM block in the certificate"
    f = lines[idx + 1].split()
    lines[idx + 1] = f"{f[0]} {int(f[1]) - 1}"
    return lines, None


def relabel_output(lines):
    """A volume covering called a surface one. Every number stays where it is
    and the statement the file makes changes, which is the one error a verdict
    reports nothing about."""
    idx = next((i for i, l in enumerate(lines) if l == "OUTPUT radial"), None)
    if idx is None:
        return None, "no radial OUTPUT line in the certificate"
    lines[idx] = "OUTPUT residual"
    return lines, None


# Each entry damages a certificate the guard accepts, in a way a generator
# could plausibly produce, and requires the guard to catch it and to name the
# right reason.
MUTATE = [
    ("correspond/swapped_row", "wout_solovev.nc",
     "--cells --node 22 --nu 64", swap_coefficients, "RNODES row"),
    ("correspond/swapped_radial", "wout_solovev.nc",
     "--radial --node 22 --nu 32 --nrad 4", swap_coefficients, "RNODES row"),
    ("correspond/rescaled_piece", "wout_solovev_cubic_spline.nc",
     "--radial --nodes 6 --nu 16 --nrad 4", rescale_pressure_piece,
     "local pressure cubic"),
    ("correspond/relabelled", "wout_solovev.nc",
     "--radial --node 22 --nu 32 --nrad 4", relabel_output,
     "evaluated radius"),
    ("correspond/unscaled_pressure", "wout_cth_like_fixed_bdy.nc",
     "--node 12 --nu 8 --nv 4", unscale_amplitude, "certificate's pressure"),
]


def check_mutation(name, wout, gen_args, mutate, reason, python, tmp):
    """A certificate the guard accepts, damaged, has to be rejected.

    gen/verify_cert.py is the only thing tying a slot to a wout field, so it
    has to be exercised against the failures it exists for rather than only
    against files that match.
    """
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    src = tmp / (name.replace("/", "_") + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" {gen_args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    lines, why = mutate(src.read_text().splitlines())
    if lines is None:
        return "fail", why
    bad = tmp / (name.replace("/", "_") + "_damaged.txt")
    bad.write_text("\n".join(lines) + "\n")
    ver = ROOT / "gen" / "verify_cert.py"
    rc, out = run(f'"{python}" "{ver}" "{wout}" "{bad}"')
    if rc == 0:
        return "fail", "the damaged certificate passed"
    if reason not in out:
        return "fail", f"rejected, but not for the {reason}"
    rc2, _ = run(f'"{python}" "{ver}" "{wout}" "{src}"')
    if rc2 != 0:
        return "fail", "the undamaged certificate was rejected"
    return "ok", f"caught at the {reason}, the original passes"


def check_patch_surface(main):
    """The post-extraction patch touched what it says and nothing else.

    gen/patch_extract.py replaces the bodies of the spec-only classical-real
    constants with a poison value. That patch is part of the audit surface, so
    the built extraction is checked to carry exactly those stubs and no other
    unreachable body.
    """
    extract = pathlib.Path(main).resolve().parent.parent.parent
    if not extract.exists():
        return "skip", "no extraction directory"
    poison = "assert false (* spec-only: classical real *)"
    # the modules of the classical-real layer, which the checker never enters
    spec_only = {"ClassicalDedekindReals.ml", "Rdefinitions.ml",
                 "ConstructiveCauchyReals.ml", "ConstructiveRcomplete.ml",
                 "ConstructiveEpsilon.ml"}
    stubs, absurd, stray = [], [], []
    for f in sorted(extract.glob("*.ml")):
        for i, line in enumerate(f.read_text(errors="replace").splitlines()):
            if poison in line:
                stubs.append(f"{f.name}:{i + 1}")
            elif "assert false" in line:
                # extraction writes one of these for a branch it has proven
                # cannot be taken
                if f.name in spec_only and "absurd case" in line:
                    absurd.append(f"{f.name}:{i + 1}")
                else:
                    stray.append(f"{f.name}:{i + 1}")
    if not stubs:
        return "skip", "the extraction is not patched"
    if stray:
        return "fail", f"an unexplained assert false at {stray[0]}"
    outside = [x for x in stubs if x.split(":")[0] not in spec_only]
    if outside:
        return "fail", f"a stub outside the classical-real layer at {outside[0]}"
    return "ok", (f"{len(stubs)} stubbed bodies and {len(absurd)} absurd "
                  f"branches, all inside the classical-real layer")


def check_reference(name, wout, node, gen_args, radius, main, python, tmp):
    """The certified enclosure at a cell centre against the float reference."""
    if not wout.exists():
        return "skip", f"{wout.name} absent"
    ref = ROOT / "proto" / "continuum_ref.py"
    rc, out = run(f'"{python}" "{ref}" "{wout}" --node {node} --nu 1 '
                  f'--at {radius!r}')
    if rc != 0:
        return "fail", "reference: " + out.strip().splitlines()[-1]
    m = re.search(r"worst \|r\| over 1 angles: ([0-9.e+-]+)", out)
    if not m:
        return "fail", "the reference printed no value"
    want = float(m.group(1))

    src = tmp / (name.replace("/", "_") + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" {gen_args}')
    if rc != 0:
        return "fail", "generator: " + out.strip().splitlines()[-1]
    env = dict(os.environ, STELLAROCQ_JOBS="1", STELLAROCQ_DEBUG="1")
    p = subprocess.run(f'"{main}" "{src}"', shell=True, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True)
    m = re.search(r"component r_s: needed centre=([0-9.e+-]+)", p.stdout)
    if not m:
        return "fail", "the checker printed no centre enclosure"
    got = float(m.group(1))
    # the enclosure of |r_s| has to contain the reference and sit close to it
    if got < abs(want) * (1 - 1e-9):
        return "fail", (f"enclosure {got:.9e} below the reference "
                        f"{abs(want):.9e}")
    if got > abs(want) * 1.001:
        return "fail", (f"enclosure {got:.9e} far above the reference "
                        f"{abs(want):.9e}")
    return "ok", (f"enclosure {got:.6e} against reference {abs(want):.6e}, "
                  f"{(got / abs(want) - 1) * 1e6:.1f} ppm wider")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default=None,
                    help="directory holding the wout files; without it only "
                    "the committed certificates are checked")
    ap.add_argument("--main", default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--tmp", default=None)
    ap.add_argument("--slow", action="store_true", help="include the long cases")
    ap.add_argument("--only", default=None, help="substring filter on case names")
    a = ap.parse_args()

    data = pathlib.Path(a.data) if a.data else HERE / "_absent"
    tmp = pathlib.Path(a.tmp) if a.tmp else HERE / "_work"
    tmp.mkdir(parents=True, exist_ok=True)
    if not pathlib.Path(a.main).exists():
        print(f"checker not found at {a.main}; run make first")
        return 2

    cases = [c for c in ALL if a.slow or not c.slow]
    if a.only:
        cases = [c for c in cases if a.only in c.name]

    width = max([len(c.name) for c in cases]
                + [len(r[0]) for r in REFERENCE]
                + [len(r[0]) for r in CORRESPOND]
                + [len(r[0]) for r in STANDALONE]
                + [len(r[0]) for r in MERCIER]
                + [len(r[0]) for r in PERTURB]
                + [len(r[0]) for r in COEFBOX]
                + [len(r[0]) for r in CONVERGENCE]
                + [len(r[0]) for r in BOOZER]
                + [len(r[0]) for r in PROFILE]
                + [len(r[0]) for r in REFUSALS]
                + [len(r[0]) for r in FIELD]
                + [len(r[0]) for r in CANCEL]
                + [len(r[0]) for r in MODESETS]
                + [len("reference/terms_node22"),
                   len("reference/halfgrid_node22"),
                   len("correspond/swapped_radial"),
                   len("correspond/rescaled_piece"),
                   len("audit/patch_surface")])
    counts = {"ok": 0, "fail": 0, "skip": 0}
    failures = []
    t0 = time.time()
    for c in cases:
        t = time.time()
        status, detail = check_case(c, data, a.main, a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {c.name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)
        if status == "fail":
            failures.append((c, detail))
    for name, cert, run_args, expect in STANDALONE:
        if a.only and a.only not in name:
            continue
        t = time.time()
        src = HERE / "data" / cert
        if not src.exists():
            status, detail = "skip", f"{cert} absent"
        else:
            rc, out = run(f'"{a.main}" {" ".join(run_args)} "{src}"')
            m = re.search(r"verdict: (\w+)", out)
            got = m.group(1) if m else "NONE"
            status = "ok" if got == expect else "fail"
            detail = got if status == "ok" else f"verdict {got}, expected {expect}"
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, node, nu, expect in MERCIER:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_mercier(name, data / wout, node, nu, expect,
                                       a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, made_from, checked_against, gen_args, agree in CORRESPOND:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_correspondence(
            name, data / made_from, data / checked_against, gen_args, agree,
            a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, tol in FIELD:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_field(name, data / wout, tol, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, gen_args, tg, run_args, expect in REFUSALS:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_refusal(name, data / wout, gen_args, tg,
                                       run_args, expect, a.main, a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, nodes, nu, least in PROFILE:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_profile(name, data / wout, nodes, nu, least,
                                       a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, node, nu, dmax, b00 in BOOZER:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_boozer(name, data / wout, node, nu, dmax, b00,
                                      a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wouts, args, column, bounds in CONVERGENCE:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_convergence(name, wouts, args, column, bounds,
                                           data, a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, node, nu in [("reference/terms_node22",
                                  "wout_solovev.nc", 22, 64)]:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_terms_reference(name, data / wout, node, nu,
                                               a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, node, nu, nrad in [("reference/terms_radial",
                                        "wout_solovev.nc", 22, 32, 4)]:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_terms_reference_radial(
            name, data / wout, node, nu, nrad, a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, args, band in CANCEL:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_cancellation(name, data / wout, args, band,
                                            a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, coarse, fine, args, factor in MODESETS:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_modesets(name, data / coarse, data / fine, args,
                                        factor, a.main, a.python)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, gen_args, cells in COEFBOX:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_coefbox(name, data / wout, gen_args, cells,
                                       a.main, a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, perturb in PERTURB:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_perturbed(name, data / "wout_solovev.nc",
                                         perturb, a.main, a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    # every pressure parameterization, since the pressure gradient is the one
    # term of the residual that differs between them and the one the wout
    # constrains only through its stored pressure
    for name, wout, node in (
            [("reference/halfgrid_node22", "wout_solovev.nc", 22)]
            + [(f"reference/halfgrid_{n}", w, 22) for n, w, _ in FAMILIES
               if n != "power_series"]):
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_halfgrid(name, data / wout, node, a.main,
                                        a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    for name, wout, gen_args, mutate, reason in MUTATE:
        if a.only and a.only not in name:
            continue
        t = time.time()
        status, detail = check_mutation(name, data / wout, gen_args, mutate,
                                        reason, a.python, tmp)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {name:<{width}}  {detail}  ({time.time() - t:.1f} s)",
              flush=True)

    if not a.only or a.only in "audit/patch_surface":
        t = time.time()
        status, detail = check_patch_surface(a.main)
        counts[status] += 1
        mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
        print(f"{mark} {'audit/patch_surface':<{width}}  {detail}  "
              f"({time.time() - t:.1f} s)", flush=True)

    if not a.only or any(a.only in r[0] for r in REFERENCE):
        for name, wout, node, gen_args, radius in REFERENCE:
            t = time.time()
            status, detail = check_reference(
                name, data / wout, node, gen_args, radius, a.main, a.python, tmp)
            counts[status] += 1
            mark = {"ok": "ok  ", "fail": "FAIL", "skip": "skip"}[status]
            print(f"{mark} {name:<{width}}  {detail}  "
                  f"({time.time() - t:.1f} s)", flush=True)

    print(f"\n{counts['ok']} passed, {counts['fail']} failed, "
          f"{counts['skip']} skipped in {time.time() - t0:.1f} s")
    for c, detail in failures:
        if c.published:
            print(f"  {c.name} carries a figure published under "
                  f"\"{c.published}\" in README.md")
    return 1 if counts["fail"] else 0


if __name__ == "__main__":
    sys.exit(main())
