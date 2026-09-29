"""Discretization error of the collocated node residual, by manufactured
solution, established by the interval Newton test.

The node residual of Physics.v at node j reads R and Z on the three nodes
j-1, j, j+1, lambda and iota on the two half points between them, and the
pressure, and assembles the radial force r_s at the node and the surface
current component r_u at the outer half point by VMEC's half-grid rule. With
lambda among the given data the unknowns are R and Z alone, which is the
problem on the quotient by the poloidal gauge. A manufactured mapping (R, Z,
lambda) is not an equilibrium; the source f is its continuum residual at the
collocation points, r_s at the node and r_u at the outer half point, and the
forced residual (Physics.RForced) is r - f. Its zero x_h on the interior nodes,
with the two outermost rows held at the mapping, is the discrete solution of
the manufactured problem, and x_h - x* its discretization error, x* the
mapping sampled on the nodes.

Every datum of the problem, the coefficients it holds fixed, lambda, the
transform, phip, the pressure coefficients and the sources, is the mapping's
own value at HP_DPS digits, with mu0 = 4 pi 1e-7 as Physics.v has it, carried
as a dyadic with a 120-bit mantissa; x* is read the same way. The certified
problem is then the manufactured one to about 1e-35 rather than the problem
its binary64 rounding defines, which lies up to 1e-14 away in x_h.
`--binary64` writes the binary64 data alone.

Two certificates per resolution, both on Colloc.v's assembled system:

  exist   centred at the discrete solution with a radius a few units of its
          last digit: `main --newton` (Colloc.colloc_correct) puts exactly
          one zero x_h in that box, so |x_h - x*| is known to the box's width.
          With --prec above 53 (the default is 128) the certificate's
          outputs at the centre are read through Wide.v, and the centre,
          carried in 58-bit mantissas, is refined by Newton steps on those
          outputs, so neither the centre nor the radius is limited by the
          binary64 rounding of a residual that cancels large terms.
  stable  centred at x* with a radius that holds x_h: `main --stability`
          (Colloc.colloc_stability) bounds every two states of the box by
          ANORM / (1 - K) times the difference of their residuals, so
          |x_h - x*| <= ANORM / (1 - K) max |r(x*) - f|, the Lax bound, whose
          right side is the stability constant times the consistency error
          HalfGrid.node_consistent charges.

The mappings are those of VMEC++'s examples/manufactured_solution.py restricted
to m <= 1: the three-dimensional one, the same with non-stellarator-symmetric
content, and that at five times the pressure.

  python gen/mms_colloc.py data CASE --ns 9,17,33 --out DIR --examples PATH
  python gen/mms_colloc.py certs DIR/CASE_ns17.json --main PATH
"""

import argparse
import json
import math
import pathlib
import re
import subprocess
import sys
import time
from fractions import Fraction

import numpy as np

MU0 = 4.0e-7 * math.pi
N_AM = 21


def dyadic(x):
    """x = m 2^e exactly, m an integer of at most 53 bits."""
    x = float(x)
    if x == 0.0:
        return (0, 0)
    m, e = math.frexp(x)
    mi = int(m * 2**53)
    e -= 53
    while mi % 2 == 0:
        mi //= 2
        e += 1
    return (mi, e)


HP_BITS = 120
HP_DPS = 60


def hp(x):
    """An mpmath real rounded to the nearest m 2^e with |m| < 2^HP_BITS, as
    the exact pair (m, e)."""
    import mpmath  # noqa: PLC0415

    x = mpmath.mpf(x)
    if x == 0:
        return (0, 0)
    e = int(mpmath.floor(mpmath.log(abs(x), 2))) - (HP_BITS - 1)
    m = int(mpmath.nint(x * mpmath.mpf(2) ** (-e)))
    while m % 2 == 0:
        m //= 2
        e += 1
    return (m, e)


def dyadic_of(x):
    """(m, e) of a float, or of a pair already (m, e)."""
    if isinstance(x, (list, tuple)):
        return (int(x[0]), int(x[1]))
    return dyadic(x)


def frac(me):
    m, e = me
    return Fraction(m) * Fraction(2) ** e


def down(q):
    """The largest float at or below the rational q."""
    f = float(q)
    return f if Fraction(f) <= q else math.nextafter(f, -math.inf)


def up(q):
    """The smallest float at or above the rational q."""
    f = float(q)
    return f if Fraction(f) >= q else math.nextafter(f, math.inf)


# ---------------------------------------------------------------------------
# Stage 1: the mapping, the collocation points and the sources


def cases(mms):
    """The mappings and the largest poloidal number each carries. The first
    three are restricted to m <= 1 and drop lambda's m = 2 mode, so that five
    Fourier modes carry R, Z and lambda; "fitted" is the three-dimensional
    mapping VMEC++'s own tests use, with its m = 2 shaping, which lies close to
    force balance."""
    p = list(mms.FITTED_P)
    p[11] = 0.0
    sym = mms.build_case(p, m2=False)
    asym = mms.build_case(p, m2=False, asym=mms.ASYM)
    high = mms.build_case(p, base=dict(mms.FITTED_BASE, pres_scale=5 * 160000.0),
                          m2=False, asym=mms.ASYM)
    fitted = mms.build_case(mms.FITTED_P)
    return {"3d": (sym, 1), "asymmetric": (asym, 1), "high-beta": (high, 1),
            "fitted": (fitted, 2)}


def physics_modes(nfp, mmax=1):
    return [(0, 0), (0, nfp)] + [(m, j * nfp) for m in range(1, mmax + 1)
                                 for j in (-1, 0, 1)]


def coefficient_rows(mms, case, svals, nfp, modes):
    """R cos, Z sin, lambda sin (and R sin, Z cos, lambda cos) on the radii
    given, in the modes of Physics.v: cos(m u - n v) with n in units of the
    geometric angle."""
    # lambda's m = 2 entry is present with a zero coefficient, so the table
    # is read at mpol 3 and only the five modes are kept
    c = mms.combined_coefficients(case, np.asarray(svals, float), 3, 1)
    order = mms.mode_order(3, 1)
    idx = {(m, n * nfp): i for i, (m, n) in enumerate(order)}
    out = {}
    for key in ("rmnc", "zmns", "lmns", "rmns", "zmnc", "lmnc"):
        out[key] = np.array([[c[key][idx[mn], j] for mn in modes]
                             for j in range(len(svals))])
    return out


def coefficient_rows_hp(mms, case, svals, modes):
    """The same rows at HP_DPS digits, as exact (m, e) pairs: the mapping's
    sympy expressions read at the exact radii, with the parameters the exact
    binary64 numbers the example carries."""
    import mpmath  # noqa: PLC0415
    import sympy as sp  # noqa: PLC0415

    nfp = case.nfp
    phip = case.sign_jacobian * mpmath.mpf(case.phiedge) / (2 * mpmath.pi)
    prod = {}
    for (kind, m, n), expr in case.mode_table().items():
        f = sp.lambdify(mms.S, expr, "mpmath")
        vals = [mpmath.mpf(f(mpmath.mpf(s.numerator) / s.denominator)) for s in svals]
        if mms.BASIS[kind][0] == "L":
            vals = [v / phip for v in vals]
        prod[(kind, m, n)] = vals

    def p(kind, m, q):
        return prod.get((kind, m, q), [mpmath.mpf(0)] * len(svals))

    out = {k: [] for k in ("rmnc", "zmns", "lmns", "rmns", "zmnc", "lmnc")}
    for m, nn in modes:
        n = nn // nfp
        q = abs(n)
        if m == 0:
            col = {"rmnc": p("rcc", 0, q), "zmns": [-x for x in p("zcs", 0, q)],
                   "lmns": [-x for x in p("lcs", 0, q)], "rmns": [-x for x in p("rcs", 0, q)],
                   "zmnc": p("zcc", 0, q), "lmnc": p("lcc", 0, q)}
        elif n == 0:
            col = {"rmnc": p("rcc", m, 0), "zmns": p("zsc", m, 0), "lmns": p("lsc", m, 0),
                   "rmns": p("rsc", m, 0), "zmnc": p("zcc", m, 0), "lmnc": p("lcc", m, 0)}
        else:
            sg = 1 if n > 0 else -1
            half = mpmath.mpf(1) / 2

            def comb(a, b, t):
                return [half * (x + t * y) for x, y in zip(p(a, m, q), p(b, m, q))]

            col = {"rmnc": comb("rcc", "rss", sg), "zmns": comb("zsc", "zcs", -sg),
                   "lmns": comb("lsc", "lcs", -sg), "rmns": comb("rsc", "rcs", -sg),
                   "zmnc": comb("zcc", "zss", sg), "lmnc": comb("lcc", "lss", sg)}
        for k in out:
            out[k].append(col[k])
    # rows by radius, columns by mode, as coefficient_rows returns them
    return {k: [[hp(v[j]) for v in out[k]] for j in range(len(svals))] for k in out}


class ContinuumHP:
    """The continuum field and residual of a mapping at HP_DPS digits, with
    complex steps in mpmath and mu0 = 4 pi 1e-7 as Physics.v has it."""

    def __init__(self, mms, case):
        import mpmath  # noqa: PLC0415
        import sympy as sp  # noqa: PLC0415

        self.mp = mpmath
        self.nfp = case.nfp
        self.phip = case.sign_jacobian * mpmath.mpf(case.phiedge) / (2 * mpmath.pi)
        self.iota = [mpmath.mpf(c) for c in case.iota_coeff]
        self.am = [mpmath.mpf(c) for c in case.am]
        self.pres_scale = mpmath.mpf(case.pres_scale)
        self.mu0 = 4 * mpmath.pi / 10**7
        R, Z, L = case.expressions()
        self.fn = {}
        for name, expr in (("R", R), ("Z", Z), ("L", L)):
            for key in ("", "s", "u", "v"):
                e = expr
                for ch in key:
                    if ch == "s":
                        e = sp.diff(e, mms.S)
                    elif ch == "u":
                        e = sp.diff(e, mms.U)
                    else:
                        e = self.nfp * sp.diff(e, mms.W)
                self.fn[name + "|" + key] = sp.lambdify((mms.S, mms.U, mms.W), e, "mpmath")

    def cov(self, s, u, v):
        q = lambda name, key: self.fn[name + "|" + key](s, u, v * self.nfp)  # noqa: E731
        R, Rs, Ru, Rv = (q("R", k) for k in ("", "s", "u", "v"))
        Zs, Zu, Zv = (q("Z", k) for k in ("s", "u", "v"))
        Lu, Lv = q("L", "u"), q("L", "v")
        g = R * (Ru * Zs - Rs * Zu)
        chip = self.phip * sum(c * s**i for i, c in enumerate(self.iota))
        Bu = (chip - Lv) / g
        Bv = (self.phip + Lu) / g
        guu, guv = Ru**2 + Zu**2, Ru * Rv + Zu * Zv
        gvv = Rv**2 + Zv**2 + R**2
        gsu, gsv = Rs * Ru + Zs * Zu, Rs * Rv + Zs * Zv
        return {"Bu": Bu, "Bv": Bv, "B_u": guu * Bu + guv * Bv,
                "B_v": guv * Bu + gvv * Bv, "B_s": gsu * Bu + gsv * Bv}

    def mu0_dpds(self, s):
        return self.mu0 * self.pres_scale * sum(
            i * c * s ** (i - 1) for i, c in enumerate(self.am) if i > 0)

    def _steps(self, s, u, v):
        mp = self.mp
        h = mp.mpf(10) ** (-(HP_DPS // 2))
        s, u, v = mp.mpf(s), mp.mpf(u), mp.mpf(v)
        return (h, self.cov(s, u, v), self.cov(mp.mpc(s, h), u, v),
                self.cov(s, mp.mpc(u, h), v), self.cov(s, u, mp.mpc(v, h)))

    def rs(self, s, u, v):
        """(d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 p'."""
        mp = self.mp
        h, q, ds, du, dv = self._steps(s, u, v)
        d = lambda z, k: mp.im(z[k]) / h  # noqa: E731
        re = {k: mp.re(x) for k, x in q.items()}
        return ((d(dv, "B_s") - d(ds, "B_v")) * re["Bv"]
                - (d(ds, "B_u") - d(du, "B_s")) * re["Bu"] - self.mu0_dpds(mp.mpf(s)))

    def ru(self, s, u, v):
        """- mu0 sqrt(g) J^s B^v, with mu0 sqrt(g) J^s = d_u B_v - d_v B_u."""
        mp = self.mp
        h, q, _, du, dv = self._steps(s, u, v)
        js = mp.im(du["B_v"]) / h - mp.im(dv["B_u"]) / h
        return -js * mp.re(q["Bv"])


def select_points(points, funcs, count):
    """Greedy row pivoting on the basis matrix (as gen/newton_colloc.py)."""
    A = np.array([[f(u, v) for f in funcs] for (u, v) in points])
    R = A.copy()
    chosen = []
    for _ in range(count):
        norms = np.linalg.norm(R, axis=1)
        for i in chosen:
            norms[i] = -1.0
        i = int(np.argmax(norms))
        chosen.append(i)
        q = R[i] / norms[i]
        R = R - np.outer(R @ q, q)
    return [points[i] for i in chosen], float(np.linalg.cond(A[chosen]))


def collocation(modes, nfp, lasym, gauge=False):
    """Angles of r_s and of r_u: as many as R, and as Z, has unknown
    coefficients on a row. With the gauge fixed, the m = 1 cosine
    coefficients of Z are tied to the sine ones of R and are not unknowns,
    and r_u is collocated for the remaining cosine modes only."""
    cosf = [(lambda u, v, a=a, b=b: math.cos(a * u - b * v)) for a, b in modes]
    sinf = [(lambda u, v, a=a, b=b: math.sin(a * u - b * v))
            for a, b in modes if (a, b) != (0, 0)]
    cosz = [(lambda u, v, a=a, b=b: math.cos(a * u - b * v))
            for a, b in modes if not (gauge and a == 1)]
    mpol = max(m for m, _ in modes) + 1
    ntor = max(abs(n) for _, n in modes) // nfp
    nv = 2 * ntor + 3
    if lasym:
        nu = 2 * (mpol + 1)
        grid = [((i + 0.5) * 2 * math.pi / nu, 2 * math.pi * k / (nfp * nv))
                for i in range(nu) for k in range(nv)]
        fs, fu = cosf + sinf, sinf + cosz
    else:
        nu = mpol + 1
        grid = [((i + 0.5) * math.pi / nu, 2 * math.pi * k / (nfp * nv))
                for i in range(nu) for k in range(nv)]
        fs, fu = cosf, sinf
    ps, cs = select_points(grid, fs, len(fs))
    pu, cu = select_points(grid, fu, len(fu))
    return ps, pu, cs, cu


class Continuum:
    """The continuum field of a mapping at complex radius and angles, in the
    conventions of Physics.v: sqrt(g) B^u = phip (iota - lambda_v),
    sqrt(g) B^v = phip (1 + lambda_u), v the geometric angle."""

    def __init__(self, mms, case):
        self.model = mms.Model(case)
        self.nfp = case.nfp
        self.phip = float(case.phip)
        self.iota = case.iota_coeff
        self.am = case.am
        self.pres_scale = case.pres_scale

    def _q(self, name, key, s, u, v):
        return self.model.fn[name + "|" + key](s, u, v * self.nfp) + 0.0 * (u + v)

    def cov(self, s, u, v):
        """B^u, B^v and the covariant B_u, B_v, B_s at (s, u, v)."""
        q = self._q
        R, Rs, Ru, Rv = (q("R", k, s, u, v) for k in ("", "s", "u", "v"))
        Zs, Zu, Zv = (q("Z", k, s, u, v) for k in ("s", "u", "v"))
        Lu, Lv = q("L", "u", s, u, v), q("L", "v", s, u, v)
        g = R * (Ru * Zs - Rs * Zu)
        chip = self.phip * sum(c * s**i for i, c in enumerate(self.iota))
        Bu = (chip - Lv) / g
        Bv = (self.phip + Lu) / g
        guu, guv = Ru**2 + Zu**2, Ru * Rv + Zu * Zv
        gvv = Rv**2 + Zv**2 + R**2
        gsu, gsv = Rs * Ru + Zs * Zu, Rs * Rv + Zs * Zv
        return {"Bu": Bu, "Bv": Bv, "B_u": guu * Bu + guv * Bv,
                "B_v": guv * Bu + gvv * Bv, "B_s": gsu * Bu + gsv * Bv}

    def mu0_dpds(self, s):
        return MU0 * self.pres_scale * sum(
            i * c * s ** (i - 1) for i, c in enumerate(self.am) if i > 0)

    def rs(self, s, u, v, h=1e-30):
        """(d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 p'."""
        q = self.cov(complex(s), u, v)
        ds = self.cov(s + 1j * h, u, v)
        du = self.cov(complex(s), u + 1j * h, v)
        dv = self.cov(complex(s), u, v + 1j * h)
        re = {k: np.real(x) for k, x in q.items()}
        d = lambda z, k: np.imag(z[k]) / h  # noqa: E731
        return ((d(dv, "B_s") - d(ds, "B_v")) * re["Bv"]
                - (d(ds, "B_u") - d(du, "B_s")) * re["Bu"] - self.mu0_dpds(s))

    def ru(self, s, u, v, h=1e-30):
        """- mu0 sqrt(g) J^s B^v, with mu0 sqrt(g) J^s = d_u B_v - d_v B_u."""
        q = self.cov(complex(s), u, v)
        du = self.cov(complex(s), u + 1j * h, v)
        dv = self.cov(complex(s), u, v + 1j * h)
        js = np.imag(du["B_v"]) / h - np.imag(dv["B_u"]) / h
        return -js * np.real(q["Bv"])


def data_hp(mms, case, ns, sf, rows, ps, pu, modes):
    """Every datum of the discrete problem at HP_DPS digits, as exact pairs
    (m, e): the coefficients on the nodes and lambda on the half points, the
    transform on the half points, phip, the pressure coefficients and the
    sources, so that the certified problem is the manufactured one rather than
    its binary64 rounding."""
    import mpmath  # noqa: PLC0415

    mpmath.mp.dps = HP_DPS
    sfq = [Fraction(j, ns - 1) for j in range(ns)]
    if any(Fraction(float(x)) != q for x, q in zip(sf, sfq)):
        raise SystemExit("the radii are not the exact j/(ns - 1) in binary64")
    shq = [(sfq[j] + sfq[j + 1]) / 2 for j in range(ns - 1)]

    def mpq(q):
        return mpmath.mpf(q.numerator) / q.denominator

    full = coefficient_rows_hp(mms, case, sfq, modes)
    half = coefficient_rows_hp(mms, case, shq, modes)
    cont = ContinuumHP(mms, case)
    iota = [hp(sum(mpmath.mpf(c) * mpq(s) ** i for i, c in enumerate(case.iota_coeff)))
            for s in shq]
    am = [Fraction(case.pres_scale) * Fraction(c) for c in case.am]
    am = [(q.numerator, -(q.denominator.bit_length() - 1)) for q in am]
    am += [(0, 0)] * (N_AM - len(am))
    src_s = [[hp(cont.rs(mpq(sfq[j]), u, v)) for u, v in ps] for j in rows]
    src_u = [[hp(cont.ru(mpq(shq[j]), u, v)) for u, v in pu] for j in rows]
    return {"rmnc": full["rmnc"], "zmns": full["zmns"], "rmns": full["rmns"],
            "zmnc": full["zmnc"], "lmns": half["lmns"], "lmnc": half["lmnc"],
            "iota_half": iota, "phip": hp(cont.phip), "am": am,
            "src_s": src_s, "src_u": src_u}


def cmd_data(a):
    sys.path.insert(0, a.examples)
    import manufactured_solution as mms  # noqa: PLC0415

    case, mmax = cases(mms)[a.case]
    lasym = bool(case.lasym)
    nfp = case.nfp
    modes = physics_modes(nfp, mmax)
    cont = Continuum(mms, case)
    gauge = bool(a.gauge and lasym)
    ps, pu, cs, cu = collocation(modes, nfp, lasym, gauge)
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for ns in (int(x) for x in a.ns.split(",")):
        sf = np.linspace(0.0, 1.0, ns)
        sh = 0.5 * (sf[1:] + sf[:-1])
        full = coefficient_rows(mms, case, sf, nfp, modes)
        half = coefficient_rows(mms, case, sh, nfp, modes)
        iota_h = [sum(c * s**i for i, c in enumerate(case.iota_coeff)) for s in sh]
        # the unknown rows lie strictly inside (smin, 1); the row at smin and
        # the boundary row are held at the mapping
        rows = [j for j in range(2, ns - 1) if sf[j] > a.smin + 1e-12]
        src_s, src_u = [], []
        for j in rows:
            us = np.array([u for u, _ in ps]); vs = np.array([v for _, v in ps])
            src_s.append([float(x) for x in cont.rs(sf[j], us, vs)])
            uu = np.array([u for u, _ in pu]); vu = np.array([v for _, v in pu])
            src_u.append([float(x) for x in cont.ru(sh[j], uu, vu)])
        am = [case.pres_scale * c for c in case.am] + [0.0] * (N_AM - len(case.am))
        d = {
            "case": a.case, "ns": ns, "nfp": nfp, "lasym": lasym, "gauge": gauge,
            "modes": modes,
            "phip": float(case.phip), "am": am,
            "s_full": sf.tolist(), "s_half": sh.tolist(), "iota_half": iota_h,
            "rmnc": full["rmnc"].tolist(), "zmns": full["zmns"].tolist(),
            "rmns": full["rmns"].tolist(), "zmnc": full["zmnc"].tolist(),
            "lmns": half["lmns"].tolist(), "lmnc": half["lmnc"].tolist(),
            "rows": rows, "points_s": ps, "points_u": pu,
            "cond_s": cs, "cond_u": cu, "src_s": src_s, "src_u": src_u,
        }
        if a.hp:
            d["hp"] = data_hp(mms, case, ns, sf, rows, ps, pu, modes)
        path = out / f"{a.case}_ns{ns}{a.tag}.json"
        path.write_text(json.dumps(d))
        print(f"{path.name}: {len(rows)} unknown rows, {len(ps)} + {len(pu)} "
              f"points per row (conditions {cs:.1f}, {cu:.1f}); max |f_s| "
              f"{max(max(map(abs, r)) for r in src_s):.3e}, max |f_u| "
              f"{max(max(map(abs, r)) for r in src_u):.3e}")


# ---------------------------------------------------------------------------
# Stage 2: the discrete problem in floating point, and the certificates


class Problem:
    """The forced node residual over the unknown rows, in floating point, in
    the exact order and form Physics.v assembles it."""

    def __init__(self, d):
        self.d = d
        self.lasym = d["lasym"]
        self.modes = [tuple(x) for x in d["modes"]]
        self.K = len(self.modes)
        self.mm = np.array([m for m, _ in self.modes], float)
        self.nn = np.array([n for _, n in self.modes], float)
        self.sf = np.array(d["s_full"])
        self.sh = np.array(d["s_half"])
        self.rows = d["rows"]
        self.blocks = ["R", "Z"] + (["Ra", "Za"] if self.lasym else [])
        # every coefficient, rows by modes; the unknowns are views into it
        self.coef = {"R": np.array(d["rmnc"]), "Z": np.array(d["zmns"]),
                     "Ra": np.array(d["rmns"]), "Za": np.array(d["zmnc"])}
        self.lam = np.array(d["lmns"])
        self.lama = np.array(d["lmnc"])
        # an unknown is (row, block, mode); sine blocks skip the (0, 0) mode,
        # and with the gauge fixed the m = 1 cosine coefficients of Z are the
        # sine coefficients of R rather than unknowns of their own
        self.gauge = bool(d.get("gauge", False))
        self.tied = [k for k, (m, _) in enumerate(self.modes) if self.gauge and m == 1]
        self.unknowns = []
        for j in self.rows:
            for blk in self.blocks:
                for k, mn in enumerate(self.modes):
                    if blk in ("Z", "Ra") and mn == (0, 0):
                        continue
                    if blk == "Za" and k in self.tied:
                        continue
                    self.unknowns.append((j, blk, k))
        self.n = len(self.unknowns)
        self.xstar = np.array([self.coef[b][j, k] for j, b, k in self.unknowns])
        self.points = []
        for r, j in enumerate(self.rows):
            for i, (u, v) in enumerate(d["points_s"]):
                self.points.append((j, 0, u, v, d["src_s"][r][i]))
            for i, (u, v) in enumerate(d["points_u"]):
                self.points.append((j, 1, u, v, d["src_u"][r][i]))
        if len(self.points) != self.n:
            raise SystemExit(f"{len(self.points)} points against {self.n} unknowns")
        # the same data at HP_DPS digits, as exact pairs, when the file has
        # them: the certificates carry these, and x* is read from them
        self.hp = d.get("hp")
        if self.hp is not None:
            h = self.hp
            self.hcoef = {"R": h["rmnc"], "Z": h["zmns"], "Ra": h["rmns"], "Za": h["zmnc"]}
            self.xstar_hp = [tuple(self.hcoef[b][j][k]) for j, b, k in self.unknowns]
            self.src_hp = []
            for r in range(len(self.rows)):
                self.src_hp += [tuple(x) for x in h["src_s"][r]]
                self.src_hp += [tuple(x) for x in h["src_u"][r]]

    def with_x(self, x):
        c = {b: self.coef[b].astype(complex) for b in self.coef}
        for (j, b, k), val in zip(self.unknowns, x, strict=True):
            c[b][j, k] = val
            if b == "Ra" and k in self.tied:
                c["Za"][j, k] = val
        return c

    def half(self, c, blk, ra, rb, sa, sb, sh):
        ya, yb = c[blk][ra], c[blk][rb]
        odd = (self.mm % 2) == 1
        ev, ed = 0.5 * (ya + yb), (yb - ya) / (sb - sa)
        qa, qb = ya / math.sqrt(sa), yb / math.sqrt(sb)
        ov = math.sqrt(sh) * 0.5 * (qa + qb)
        od = math.sqrt(sh) * (qb - qa) / (sb - sa) + ov / (2.0 * sh)
        return np.where(odd, ov, ev), np.where(odd, od, ed)

    @staticmethod
    def series(val, ds, cosk, sink, m, n, even):
        k0, k1 = (cosk, sink) if even else (sink, cosk)
        su, sv = (-m, n) if even else (m, -n)
        return {"0": val @ k0, "s": ds @ k0, "u": (su * val) @ k1, "v": (sv * val) @ k1,
                "su": (su * ds) @ k1, "sv": (sv * ds) @ k1,
                "uu": (-m * m * val) @ k0, "uv": (m * n * val) @ k0,
                "vv": (-n * n * val) @ k0}

    @staticmethod
    def lseries(l, cosk, sink, m, n, even):
        k0, k1 = (cosk, sink) if even else (sink, cosk)
        su, sv = (-m, n) if even else (m, -n)
        return {"u": (su * l) @ k1, "v": (sv * l) @ k1, "uu": (-m * m * l) @ k0,
                "uv": (m * n * l) @ k0, "vv": (-n * n * l) @ k0}

    def half_point(self, c, j, side, u, v):
        """The field of the half point below (side 0) or above (side 1) node j."""
        ra, rb = (j - 1, j) if side == 0 else (j, j + 1)
        hrow = j - 1 if side == 0 else j
        sa, sb, sh = self.sf[ra], self.sf[rb], self.sh[hrow]
        iota = self.d["iota_half"][hrow]
        phip = self.d["phip"]
        arg = self.mm * u - self.nn * v
        cosk, sink = np.cos(arg), np.sin(arg)
        m, n = self.mm, self.nn
        R = self.series(*self.half(c, "R", ra, rb, sa, sb, sh), cosk, sink, m, n, True)
        Z = self.series(*self.half(c, "Z", ra, rb, sa, sb, sh), cosk, sink, m, n, False)
        L = self.lseries(self.lam[hrow], cosk, sink, m, n, False)
        if self.lasym:
            Ra = self.series(*self.half(c, "Ra", ra, rb, sa, sb, sh), cosk, sink, m, n, False)
            Za = self.series(*self.half(c, "Za", ra, rb, sa, sb, sh), cosk, sink, m, n, True)
            La = self.lseries(self.lama[hrow], cosk, sink, m, n, True)
            R = {k: R[k] + Ra[k] for k in R}
            Z = {k: Z[k] + Za[k] for k in Z}
            L = {k: L[k] + La[k] for k in L}
        tau = R["u"] * Z["s"] - R["s"] * Z["u"]
        g = R["0"] * tau
        tau_u = R["uu"] * Z["s"] + R["u"] * Z["su"] - (R["su"] * Z["u"] + R["s"] * Z["uu"])
        tau_v = R["uv"] * Z["s"] + R["u"] * Z["sv"] - (R["sv"] * Z["u"] + R["s"] * Z["uv"])
        g_u = R["u"] * tau + R["0"] * tau_u
        g_v = R["v"] * tau + R["0"] * tau_v
        guu = R["u"] ** 2 + Z["u"] ** 2
        guv = R["u"] * R["v"] + Z["u"] * Z["v"]
        gvv = R["v"] ** 2 + Z["v"] ** 2 + R["0"] ** 2
        gsu = R["s"] * R["u"] + Z["s"] * Z["u"]
        gsv = R["s"] * R["v"] + Z["s"] * Z["v"]
        gsu_u = R["su"] * R["u"] + R["s"] * R["uu"] + Z["su"] * Z["u"] + Z["s"] * Z["uu"]
        gsu_v = R["sv"] * R["u"] + R["s"] * R["uv"] + Z["sv"] * Z["u"] + Z["s"] * Z["uv"]
        gsv_u = R["su"] * R["v"] + R["s"] * R["uv"] + Z["su"] * Z["v"] + Z["s"] * Z["uv"]
        gsv_v = R["sv"] * R["v"] + R["s"] * R["vv"] + Z["sv"] * Z["v"] + Z["s"] * Z["vv"]
        guu_v = 2 * (R["u"] * R["uv"] + Z["u"] * Z["uv"])
        guv_u = R["uu"] * R["v"] + R["u"] * R["uv"] + Z["uu"] * Z["v"] + Z["u"] * Z["uv"]
        guv_v = R["uv"] * R["v"] + R["u"] * R["vv"] + Z["uv"] * Z["v"] + Z["u"] * Z["vv"]
        gvv_u = 2 * (R["v"] * R["uv"] + Z["v"] * Z["uv"] + R["0"] * R["u"])
        bu_num = iota - L["v"]
        bv_num = 1.0 + L["u"]
        Bu = phip * bu_num / g
        Bv = phip * bv_num / g
        g2 = g * g
        Bu_u = phip * (-L["uv"] * g - bu_num * g_u) / g2
        Bv_u = phip * (L["uu"] * g - bv_num * g_u) / g2
        Bu_v = phip * (-L["vv"] * g - bu_num * g_v) / g2
        Bv_v = phip * (L["uv"] * g - bv_num * g_v) / g2
        B_u = guu * Bu + guv * Bv
        B_v = guv * Bu + gvv * Bv
        B_s_u = gsu_u * Bu + gsu * Bu_u + (gsv_u * Bv + gsv * Bv_u)
        B_s_v = gsu_v * Bu + gsu * Bu_v + (gsv_v * Bv + gsv * Bv_v)
        B_u_v = guu_v * Bu + guu * Bu_v + (guv_v * Bv + guv * Bv_v)
        B_v_u = guv_u * Bu + guv * Bu_u + (gvv_u * Bv + gvv * Bv_u)
        return {"Bu": Bu, "Bv": Bv, "B_u": B_u, "B_v": B_v, "B_s_u": B_s_u,
                "B_s_v": B_s_v, "Js": B_v_u - B_u_v}

    def mu0pp(self, s):
        return MU0 * sum(i * a * s ** (i - 1) for i, a in enumerate(self.d["am"]) if i > 0)

    def residual(self, x, forced=True):
        c = self.with_x(x)
        out = np.zeros(self.n, dtype=complex)
        for i, (j, comp, u, v, f) in enumerate(self.points):
            qp = self.half_point(c, j, 1, u, v)
            if comp == 0:
                qm = self.half_point(c, j, 0, u, v)
                inv_h = 1.0 / (self.sh[j] - self.sh[j - 1])
                avg = lambda k: 0.5 * (qm[k] + qp[k])  # noqa: E731
                dif = lambda k: (qp[k] - qm[k]) * inv_h  # noqa: E731
                r = ((avg("B_s_v") - dif("B_v")) * avg("Bv")
                     - (dif("B_u") - avg("B_s_u")) * avg("Bu") - self.mu0pp(self.sf[j]))
            else:
                r = -(qp["Js"] * qp["Bv"])
            out[i] = r - (f if forced else 0.0)
        return out

    def jacobian(self, x, h=1e-30):
        J = np.zeros((self.n, self.n))
        for k in range(self.n):
            xx = x.astype(complex)
            xx[k] += 1j * h
            J[:, k] = np.imag(self.residual(xx)) / h
        return J


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


class Layout:
    """Global slots: the unknowns, each on its own exponent, then each
    parameter once."""

    def __init__(self, pb, exp):
        self.pb = pb
        self.exps = list(exp) if isinstance(exp, (list, tuple, np.ndarray)) else [exp] * pb.n
        self.params, self.pidx = [], {}
        self.uidx = {u: i for i, u in enumerate(pb.unknowns)}

    def param(self, x):
        me = dyadic_of(x)
        if me not in self.pidx:
            self.pidx[me] = self.pb.n + len(self.params)
            self.params.append(me)
        return self.pidx[me]

    def sigma(self, i, j, comp, u, v, f):
        """The slots of point i, row j: the data at HP_DPS digits when the
        problem carries them, and its binary64 data otherwise."""
        pb, d, K = self.pb, self.pb.d, self.pb.K
        h = pb.hp
        s = [self.param(pb.sf[j]), self.param(u), self.param(v),
             self.param(h["phip"] if h else d["phip"])]
        s += [self.param(x) for x in pb.sf[j - 1:j + 2]]
        s += [self.param(x) for x in pb.sh[j - 1:j + 1]]
        s += [self.param(x) for x in (h["iota_half"] if h else d["iota_half"])[j - 1:j + 1]]
        s += [self.param(a) for a in (h["am"] if h else d["am"])]
        coef = pb.hcoef if h else pb.coef

        def block(blk):
            out = []
            for rr in (j - 1, j, j + 1):
                for k in range(K):
                    key = (rr, blk, k)
                    tie = (rr, "Ra", k)
                    if key in self.uidx:
                        out.append(self.uidx[key])
                    elif blk == "Za" and k in pb.tied and tie in self.uidx:
                        out.append(self.uidx[tie])  # the gauge: Z_c(1, n) = R_s(1, n)
                    else:
                        out.append(self.param(coef[blk][rr][k]))
            return out

        lam = h["lmns"] if h else pb.lam
        s += block("R") + block("Z")
        s += [self.param(lam[rr][k]) for rr in (j - 1, j) for k in range(K)]
        if pb.lasym:
            lama = h["lmnc"] if h else pb.lama
            s += block("Ra") + block("Za")
            s += [self.param(lama[rr][k]) for rr in (j - 1, j) for k in range(K)]
        src = [0.0, 0.0, 0.0]
        src[comp] = pb.src_hp[i] if h else f
        s += [self.param(x) for x in src]
        return s


def write_cert(path, pb, lay, centre, r, K, M, A, B, anorm=None, prec=53):
    n = pb.n
    pts = [(comp, lay.sigma(i, j, comp, u, v, f))
           for i, (j, comp, u, v, f) in enumerate(pb.points)]
    L = ["STELLAROCQ-NEWTON", f"PREC {prec}", "SYSTEM colloc", f"N {n}",
         "EXP " + " ".join(str(int(e)) for e in lay.exps),
         "CENTRE " + " ".join(str(int(c)) for c in centre),
         f"NPARAM {len(lay.params)}",
         "PARAM " + " ".join(f"{m} {e}" for m, e in lay.params),
         f"R {int(r)}", "K {} {}".format(*dyadic(K)), "M {} {}".format(*dyadic(M)),
         "A " + " ".join("{} {}".format(*dyadic(v)) for row in A for v in row),
         "B " + " ".join("{} {}".format(*dyadic(v)) for row in B for v in row)]
    if anorm is not None:
        L.append("ANORM {} {}".format(*dyadic(anorm)))
    L += [f"LASYM {1 if pb.lasym else 0}", "PROFILE POWER", "OUTPUT forced",
          f"MODES {pb.K}"] + [f"{m} {nn}" for m, nn in pb.modes]
    L.append(f"NPOINTS {len(pts)}")
    L += [f"POINT {comp} " + " ".join(str(g) for g in sig) for comp, sig in pts]
    pathlib.Path(path).write_text("\n".join(L) + "\n")


def evaluate(main, path, n):
    rc, out = run(f'"{main}" --newton-eval "{path}"')
    if rc != 0 or "NEWTON-EVAL" not in out:
        raise SystemExit(f"the evaluation failed:\n{out[-3000:]}")
    F = np.zeros((n, 2))
    for m in re.finditer(r"^F (\d+) (\S+) (\S+)$", out, re.M):
        F[int(m.group(1))] = (float.fromhex(m.group(2)), float.fromhex(m.group(3)))
    st = {k: float.fromhex(re.search(rf"^{k} (\S+)$", out, re.M).group(1))
          for k in ("ROWG", "ROWH", "VMAX", "JMAX")}
    return F, st


def verdict(main, flag, path):
    rc, out = run(f'"{main}" {flag} "{path}"')
    m = re.search(r"verdict: (\w+)", out)
    return (m.group(1) if m else "NONE"), out


def centre_outputs(main, path, n):
    """The enclosures of the outputs at the centre, as the check reads them
    (through Wide.v when the certificate's PREC exceeds 53)."""
    rc, out = run(f'"{main}" --newton-centre "{path}"')
    if rc != 0 or "NEWTON-CENTRE" not in out:
        raise SystemExit(f"the centre evaluation failed:\n{out[-3000:]}")
    F = np.zeros((n, 2))
    for m in re.finditer(r"^F (\d+) (\S+) (\S+)$", out, re.M):
        F[int(m.group(1))] = (float.fromhex(m.group(2)), float.fromhex(m.group(3)))
    return F


def cmd_certs(a):
    d = json.loads(pathlib.Path(a.data).read_text())
    pb = Problem(d)
    tag = pathlib.Path(a.data).stem
    outdir = pathlib.Path(a.data).parent
    t0 = time.time()
    F0 = np.real(pb.residual(pb.xstar))
    print(f"{tag}: {pb.n} unknowns on rows {pb.rows[0]}..{pb.rows[-1]}, "
          f"max |r(x*) - f| {np.abs(F0).max():.3e} in floating point")
    # the discrete solution by Newton's method in floating point
    x = pb.xstar.copy()
    J = pb.jacobian(x)
    for it in range(8):
        F = np.real(pb.residual(x))
        step = np.linalg.solve(J, -F)
        x = x + step
        if np.abs(step).max() < 1e-15 * np.abs(x).max():
            break
        J = pb.jacobian(x)
    F = np.real(pb.residual(x))
    err = np.abs(x - pb.xstar)
    print(f"  Newton: {it + 1} steps, max |F| {np.abs(F).max():.2e}, "
          f"|x_h - x*| max {err.max():.6e}, condition {np.linalg.cond(J):.3e}, "
          f"{time.time() - t0:.0f} s", flush=True)
    # --- existence of x_h in a thin box around the float solution. The
    # radius and K are read off the checker's own enclosures, since the
    # interval residual at the centre is far wider than its float value; with
    # --shape each unknown gets the exponent that puts its share of that width
    # near 2^16 mantissa units, so the box has the shape of the uncertainty.
    Aphys = np.linalg.inv(J)
    path_e = outdir / f"{tag}_exist.txt"

    def setup(exps):
        D = 2.0 ** np.asarray(exps, dtype=float)
        lay = Layout(pb, [int(v) for v in exps])
        Jm = J * D[None, :]  # the Jacobian in mantissa units of each unknown
        A = np.linalg.inv(Jm)
        an = float(np.abs(A).sum(axis=1).max()) * (1 + 2.0**-20)
        centre = np.round(x / D).astype(np.int64)
        M = 4.0 * float(np.abs(Jm).max()) + 2.0**-40
        return D, lay, Jm, A, an, centre, M

    prec = a.prec
    if prec > 53:
        # Each unknown gets the exponent that gives its centre a mantissa of
        # about 2^58, and the centre is refined in those mantissas by Newton
        # steps on the outputs read through Wide.v, which see past binary64's
        # rounding of the residual; the box then only has to hold the
        # centre's last digits.
        mag = np.maximum(np.abs(x), 1e-3 * float(np.abs(x).max()))
        exps = [int(math.floor(math.log2(v))) - 58 for v in mag]
        D, lay, Jm, A, anorm, centre, M = setup(exps)
        for it in range(a.refine):
            write_cert(path_e, pb, lay, centre, 1, 0.5, M, A, Jm, anorm=anorm, prec=prec)
            Fw = centre_outputs(a.main, path_e, pb.n)
            fmid = 0.5 * (Fw[:, 0] + Fw[:, 1])
            step = Aphys @ fmid
            centre = centre - np.round(step / D).astype(np.int64)
            print(f"  refine {it + 1}: max |F(c)| {np.abs(fmid).max():.3e} "
                  f"(width {float(np.max(Fw[:, 1] - Fw[:, 0])):.1e}), step "
                  f"{np.abs(step).max():.3e}, {time.time() - t0:.0f} s", flush=True)
    else:
        exps = [a.exp] * pb.n
        D, lay, Jm, A, anorm, centre, M = setup(exps)
    write_cert(path_e, pb, lay, centre, 1, 0.5, M, A, Jm, anorm=anorm, prec=prec)
    Fc, st = evaluate(a.main, path_e, pb.n)
    if a.shape and prec <= 53:
        wF = np.abs(Fc).max(axis=1)
        need = np.abs(Aphys) @ wF
        exps = [int(max(a.exp - 30, min(a.exp + 30, math.floor(math.log2(max(v, 1e-300))) - 16)))
                for v in need]
        D, lay, Jm, A, anorm, centre, M = setup(exps)
        write_cert(path_e, pb, lay, centre, 1, 0.5, M, A, Jm, anorm=anorm, prec=prec)
        Fc, st = evaluate(a.main, path_e, pb.n)
    K = min(0.5, 2.0 * st["ROWG"] + 2.0**-30)
    r = int(math.ceil(1.05 * st["VMAX"] / (1.0 - K))) + 2
    for _ in range(3):
        write_cert(path_e, pb, lay, centre, r, K, M, A, Jm, anorm=anorm, prec=prec)
        v_e, out_e = verdict(a.main, "--newton", path_e)
        if v_e == "VALID":
            break
        _, st = evaluate(a.main, path_e, pb.n)
        K = min(0.9, 2.0 * st["ROWG"] + 2.0**-30)
        r = int(math.ceil(1.2 * st["VMAX"] / (1.0 - K))) + 2
    # the centre in exact rationals, since its mantissas can carry more bits
    # than a float
    xc = np.array([float(Fraction(int(c)) * Fraction(2) ** int(e))
                   for c, e in zip(centre, lay.exps)])
    xstar = ([frac(me) for me in pb.xstar_hp] if pb.hp is not None
             else [Fraction(float(xs)) for xs in pb.xstar])
    dev_exact = [abs(Fraction(int(c)) * Fraction(2) ** int(e) - xs)
                 for c, e, xs in zip(centre, lay.exps, xstar)]
    print(f"  exist: {v_e}, radius {r} mantissa units, {float((r * D).min()):.3e} to "
          f"{float((r * D).max()):.3e}, K {K:.3e}, {time.time() - t0:.0f} s", flush=True)
    # stability on the same box: in the max norm over mantissas every state
    # there is within ANORM/(1 - K) of x_h per unit of residual, so in the
    # reconstruction's units unknown i is within D_i ANORM/(1 - K)
    v_s, _ = verdict(a.main, "--stability", path_e)
    S = anorm / (1.0 - K) * float(D.max())
    print(f"  stable: {v_s}, S {S:.4e} per force unit on that box, "
          f"{time.time() - t0:.0f} s", flush=True)
    # the error, as an interval, from the box that holds x_h: over every
    # unknown row, and over the rows at s >= 0.2, in exact rationals and
    # rounded outward
    rad = [Fraction(int(r)) * Fraction(2) ** int(e) for e in lay.exps]
    bulk = [pb.sf[j] >= 0.2 for j, _, _ in pb.unknowns]
    lo = [dv - rd for dv, rd in zip(dev_exact, rad)]
    hi = [dv + rd for dv, rd in zip(dev_exact, rad)]
    e_lo = down(max(Fraction(0), max(lo)))
    e_hi = up(max(hi))
    b_lo = down(max(Fraction(0), max(v for v, b in zip(lo, bulk) if b)))
    b_hi = up(max(v for v, b in zip(hi, bulk) if b))
    scale = float(D.max())
    res = {"tag": tag, "ns": d["ns"], "n": pb.n, "exist": v_e, "stable": v_s,
           "err_lo": e_lo, "err_hi": e_hi, "bulk_lo": b_lo, "bulk_hi": b_hi,
           "err_float": float(err.max()), "S": S, "K": K,
           "tau_float": float(np.abs(F0).max()), "radius_exist": r * scale}
    (outdir / f"{tag}_result.json").write_text(json.dumps(res, indent=1))
    print(f"  error in [{e_lo:.6e}, {e_hi:.6e}], over s >= 0.2 in "
          f"[{b_lo:.6e}, {b_hi:.6e}]")
    return 0 if v_e == "VALID" and v_s == "STABLE" else 1


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("data")
    p.add_argument("case", choices=["3d", "asymmetric", "high-beta", "fitted"])
    p.add_argument("--ns", default="9,17,33")
    p.add_argument("--out", required=True)
    p.add_argument("--examples", required=True,
                   help="VMEC++'s examples directory, for manufactured_solution.py")
    p.add_argument("--smin", type=float, default=0.0,
                   help="the inner radius, held at the mapping with the boundary")
    p.add_argument("--tag", default="", help="appended to the file names")
    p.add_argument("--gauge", action="store_true",
                   help="fix the m = 1 poloidal gauge of a non-symmetric mapping "
                   "by tying the m = 1 cosine coefficients of Z to the sine ones of R")
    p.add_argument("--binary64", dest="hp", action="store_false",
                   help="write the problem's data as binary64 numbers only, rather "
                   "than beside their values at HP_DPS digits, which the "
                   "certificates then carry")
    p.set_defaults(fn=cmd_data)
    c = sub.add_parser("certs")
    c.add_argument("data")
    c.add_argument("--main", required=True)
    c.add_argument("--exp", type=int, default=-50)
    c.add_argument("--shape", action="store_true",
                   help="give each unknown the exponent its share of the "
                   "residual's enclosure width calls for (at PREC 53)")
    c.add_argument("--prec", type=int, default=128,
                   help="the certificate's PREC; above 53 the outputs at the "
                   "centre are read through Wide.v and the centre is refined "
                   "with them")
    c.add_argument("--refine", type=int, default=3,
                   help="Newton steps on the wide outputs at the centre")
    c.set_defaults(fn=cmd_certs)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
