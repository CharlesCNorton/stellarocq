"""A discrete equilibrium of the reconstruction near a VMEC++ solution, by
the interval Newton test.

theories/Colloc.v collocates the force residual of Physics.v at points over
a band of surfaces, with the Fourier coefficients of R and Z on those
surfaces as the unknowns and everything else the wout says taken as given:
the stream function, the rotational transform, the pressure, and the surfaces
outside the band. Two components carry force balance, since the third
vanishes with r_u wherever B^v does not (Identities.residual_along_field,
which is F . B = 0 on the reconstruction): r_s, even under stellarator
symmetry, is collocated at as many angles as R has modes, and r_u, odd, at
as many as Z has, so the system is square. Newton's method in floating point moves the
centre from the wout's coefficients to a zero of the system, and the checker
establishes it: `main --newton` on the certificate this writes is
Colloc.colloc_correct, exactly one zero of the collocated residual in the box
around the centre.

  python gen/newton_colloc.py wout.nc cert.txt --rows 20:24 [--main PATH]

The unknowns are mantissas, each against its own exponent: the box is
shaped to the coefficients, since the sensitivity of the residual to a
coefficient varies by orders of magnitude across the modes and a cube in one
exponent contracts for no radius once three surfaces are unknown. The
Jacobian, its inverse A, the contraction constant K, the entry bound M and the
radius R are read off what the checker reports through `main --newton-eval`,
and the run ends with the verdict of `main --newton` on the file it wrote.
`--cube` keeps every unknown on the one exponent of --exp.
"""

import argparse
import math
import pathlib
import re
import subprocess
import sys
import time

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from make_cert import Wout, calibrate_pressure, dyadic  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def select_points(points, funcs, count):
    """A square, well-conditioned selection of collocation points.

    Rows of the basis matrix are chosen greedily, each the one of largest
    norm after the chosen rows are projected out, which is Gram-Schmidt with
    row pivoting.
    """
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
    sub = A[chosen]
    return [points[i] for i in chosen], float(np.linalg.cond(sub))


def collocation(w):
    """The angles of the even and the odd component, one set per parity."""
    m, n = w.xm, w.xn
    even = [(int(a), int(b)) for a, b in zip(m, n, strict=True)]
    odd = [(a, b) for a, b in even if not (a == 0 and b == 0)]
    three_d = bool((n != 0).any())
    mpol = int(m.max()) + 1
    if not three_d:
        # the DCT and DST nodes, at which the cosine and sine interpolants
        # of these modes are invertible
        ue = [(i + 0.5) * np.pi / mpol for i in range(mpol)]
        uo = [i * np.pi / mpol for i in range(1, mpol)]
        return ([(u, 0.0) for u in ue], [(u, 0.0) for u in uo], 1.0, 1.0)
    nfp = int(np.gcd.reduce(np.abs(n[n != 0])))
    ntor = int(np.abs(n).max()) // nfp
    nu, nv = mpol + 1, 2 * ntor + 3
    grid = [((i + 0.5) * np.pi / nu, 2.0 * np.pi * k / (nfp * nv))
            for i in range(nu) for k in range(nv)]
    fe = [(lambda u, v, a=a, b=b: math.cos(a * u - b * v)) for a, b in even]
    fo = [(lambda u, v, a=a, b=b: math.sin(a * u - b * v)) for a, b in odd]
    pe, ce = select_points(grid, fe, len(even))
    po, co = select_points(grid, fo, len(odd))
    return pe, po, ce, co


class Layout:
    """The global slot layout: unknowns first, then every parameter once."""

    def __init__(self, w, rows, exp_u):
        self.w, self.rows = w, rows
        K = len(w.xm)
        self.K = K
        self.base_local = 32 + 8 * K
        self.unknowns = []
        self.uidx = {}
        for j in rows:
            for k in range(K):
                self.uidx[(j, "R", k)] = len(self.unknowns)
                self.unknowns.append((j, "R", k))
            for k in range(K):
                if not (w.xm[k] == 0 and w.xn[k] == 0):
                    self.uidx[(j, "Z", k)] = len(self.unknowns)
                    self.unknowns.append((j, "Z", k))
        self.n = len(self.unknowns)
        self.exps = [exp_u] * self.n
        self.params = []
        self.pidx = {}

    def param(self, x):
        me = dyadic(x)
        if me not in self.pidx:
            self.pidx[me] = self.n + len(self.params)
            self.params.append(me)
        return self.pidx[me]

    def value(self, j, block, k):
        arr = {"R": self.w.rmnc, "Z": self.w.zmns}[block]
        return float(arr[j][k])

    def centre(self):
        return [round(self.value(j, b, k) / 2.0 ** e)
                for (j, b, k), e in zip(self.unknowns, self.exps, strict=True)]

    def rescale(self, centre, need, target):
        """Give each unknown the exponent that puts its needed radius near the
        target, in mantissa units, so the box is shaped like the uncertainty;
        the centre is carried over to the new grid."""
        phys = [c * 2.0 ** e for c, e in zip(centre, self.exps, strict=True)]
        for j in range(self.n):
            shift = int(round(math.log2(max(need[j], 1.0) / target)))
            self.exps[j] = max(-60, self.exps[j] + max(-12, min(12, shift)))
        return [round(x / 2.0 ** e) for x, e in zip(phys, self.exps, strict=True)]

    def point(self, j, out, u, v):
        """The map of one point's local slots, in the layout of Physics.v."""
        w, K = self.w, self.K
        phip = float(w.phips[1])
        s = []
        s += [self.param(w.s_full[j]), self.param(u), self.param(v), self.param(phip)]
        s += [self.param(x) for x in w.s_full[j - 1:j + 2]]
        s += [self.param(x) for x in w.s_half[j:j + 2]]
        s += [self.param(x) for x in w.iotas[j:j + 2]]
        s += [self.param(w.am[i] if i < len(w.am) else 0.0) for i in range(21)]
        for block, arr in (("R", w.rmnc), ("Z", w.zmns)):
            for rr in (j - 1, j, j + 1):
                for k in range(K):
                    key = (rr, block, k)
                    s.append(self.uidx[key] if key in self.uidx
                             else self.param(arr[rr][k]))
        for rr in (j, j + 1):
            for k in range(K):
                s.append(self.param(w.lmns[rr][k]))
        if len(s) != self.base_local:
            raise SystemExit("the local layout has the wrong width")
        return (out, s)


def write_cert(path, w, lay, points, centre, r, K, M, A, B):
    n = lay.n
    L = []
    P = L.append
    P("STELLAROCQ-NEWTON")
    P("PREC 53")
    P("SYSTEM colloc")
    P(f"N {n}")
    P("EXP " + " ".join(str(e) for e in lay.exps))
    P("CENTRE " + " ".join(str(c) for c in centre))
    P(f"NPARAM {len(lay.params)}")
    P("PARAM " + " ".join(f"{m} {e}" for m, e in lay.params))
    P(f"R {r}")
    P("K {} {}".format(*dyadic(K)))
    P("M {} {}".format(*dyadic(M)))
    P("A " + " ".join("{} {}".format(*dyadic(v)) for row in A for v in row))
    P("B " + " ".join("{} {}".format(*dyadic(v)) for row in B for v in row))
    P("LASYM 0")
    P(f"PROFILE {w.profile}")
    P(f"MODES {lay.K}")
    for m, nn in zip(w.xm, w.xn, strict=True):
        P(f"{m} {nn}")
    P(f"NPOINTS {len(points)}")
    for out, sigma in points:
        P(f"POINT {out} " + " ".join(str(g) for g in sigma))
    pathlib.Path(path).write_text("\n".join(L) + "\n")


def evaluate(main, path, n):
    """The centre's outputs, the Jacobian and the row sums, from the checker."""
    rc, out = run(f'"{main}" --newton-eval "{path}"')
    if rc != 0 or "NEWTON-EVAL" not in out:
        raise SystemExit(f"the evaluation failed:\n{out[-2000:]}")
    F = np.zeros(n)
    J = np.zeros((n, n))
    width = 0.0
    for m in re.finditer(r"^F (\d+) (\S+) (\S+)$", out, re.M):
        lo, hi = float.fromhex(m.group(2)), float.fromhex(m.group(3))
        F[int(m.group(1))] = 0.5 * (lo + hi)
        width = max(width, hi - lo)
    for m in re.finditer(r"^J (\d+) (\d+) (\S+) (\S+)$", out, re.M):
        lo, hi = float.fromhex(m.group(3)), float.fromhex(m.group(4))
        J[int(m.group(1)), int(m.group(2))] = 0.5 * (lo + hi)
    stats = {k: float.fromhex(re.search(rf"^{k} (\S+)$", out, re.M).group(1))
             for k in ("ROWG", "ROWH", "VMAX", "JMAX")}
    need = np.zeros(n)
    for m in re.finditer(r"^V (\d+) (\S+) (\S+) (\S+)$", out, re.M):
        need[int(m.group(1))] = float.fromhex(m.group(2))
    stats["need"] = need
    return F, J, width, stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("out")
    ap.add_argument("--rows", required=True, metavar="J0:J1",
                    help="the unknown surfaces, inclusive; the residual is "
                    "collocated at the same nodes, so each reads one surface "
                    "beyond the band on either side")
    ap.add_argument("--exp", type=int, default=-50,
                    help="the exponent of every unknown")
    ap.add_argument("--iters", type=int, default=6,
                    help="Newton steps in floating point before the test")
    ap.add_argument("--cube", action="store_true",
                    help="keep every unknown on the exponent of --exp, a cube "
                    "in mantissa units, instead of giving each its own")
    ap.add_argument("--main",
                    default=str(ROOT / "extract" / "_build" / "default"
                                / "main.exe"))
    a = ap.parse_args()

    w = Wout(a.wout)
    if w.lasym:
        raise SystemExit("the collocation is written for the stellarator-"
                         "symmetric layout")
    if w.profile in ("SPLINE", "AKIMA", "SEGMENT", "PEDESTAL_OFF"):
        raise SystemExit(f"a {w.profile} pressure is not carried here")
    calibrate_pressure(w)
    j0, j1 = (int(x) for x in a.rows.split(":"))
    if not (2 <= j0 <= j1 <= w.ns - 2):
        raise SystemExit(f"--rows must lie in [2, {w.ns - 2}]")
    rows = list(range(j0, j1 + 1))
    pe, po, ce, co = collocation(w)
    lay = Layout(w, rows, a.exp)
    points = []
    for j in rows:
        for (u, v) in pe:
            points.append(lay.point(j, 0, u, v))
        for (u, v) in po:
            points.append(lay.point(j, 1, u, v))
    n = lay.n
    if len(points) != n:
        raise SystemExit(f"{len(points)} points against {n} unknowns")
    print(f"{pathlib.Path(a.wout).name}: surfaces {j0}..{j1} at "
          f"s = {w.s_full[j0]:.4f}..{w.s_full[j1]:.4f}, {lay.K} modes, "
          f"{n} unknowns, {len(points)} collocation points "
          f"({len(pe)} even and {len(po)} odd per surface), "
          f"{len(lay.params)} parameters")
    if ce != 1.0:
        print(f"  interpolation condition numbers {ce:.1f} (even) and "
              f"{co:.1f} (odd)")
    zero = np.zeros((n, n))
    centre = lay.centre()
    best = None
    t0 = time.time()
    for it in range(a.iters + 1):
        write_cert(a.out, w, lay, points, centre, 0, 0.5, 1.0, zero, zero)
        F, J, width, _ = evaluate(a.main, a.out, n)
        fmax = float(np.abs(F).max())
        print(f"  Newton {it}: |F|max {fmax:.3e}, centre enclosure width "
              f"{width:.1e}, {time.time() - t0:.0f} s", flush=True)
        if best is None or fmax < best[0]:
            best = (fmax, list(centre), J.copy())
        if it == a.iters or fmax <= 4.0 * width:
            break
        step = np.linalg.solve(J, -F)
        centre = [int(c + round(float(d))) for c, d in zip(centre, step, strict=True)]
    fmax, centre, J = best
    cond = float(np.linalg.cond(J))
    A = np.linalg.inv(J)
    anorm = float(np.abs(A).sum(axis=1).max())
    print(f"  Jacobian condition number {cond:.3e}; row sums of |A| at most "
          f"{anorm:.3e} mantissa units per force unit, "
          f"{anorm * 2.0 ** a.exp:.3e} in the reconstruction's units")
    # the box: the first step needs |A F(c)| <= (1 - K) r, and the row sums
    # of I - A J over the box set K, so the two are settled together
    K = 0.5
    r = 1
    M = 1.0
    verdict = "INVALID"
    if not a.cube:
        # the needed radius of each unknown from a thin box, then every
        # unknown on its own grid so that the box is that shape
        write_cert(a.out, w, lay, points, centre, r, K, M, A, J)
        _, _, _, st = evaluate(a.main, a.out, n)
        centre = lay.rescale(centre, st["need"], 2.0 ** 16)
        write_cert(a.out, w, lay, points, centre, 0, K, M, zero, zero)
        F, J, width, _ = evaluate(a.main, a.out, n)
        A = np.linalg.inv(J)
        print(f"  reshaped: exponents {min(lay.exps)}..{max(lay.exps)}, "
              f"|F|max {float(np.abs(F).max()):.3e}, condition number "
              f"{float(np.linalg.cond(J)):.3e}", flush=True)
    # The row sums of |I - A J| grow with the radius, since the enclosures of
    # the Jacobian widen over the box, and the first step needs
    # |A F(c)| <= (1 - K) r. With the growth read off two radii the radius
    # that balances the two is chosen, and K is the row sum there.
    write_cert(a.out, w, lay, points, centre, 1, K, M, A, J)
    _, _, _, s0 = evaluate(a.main, a.out, n)
    g0, vmax = max(s0["ROWG"], s0["ROWH"]), s0["VMAX"]
    r1 = int(math.ceil(2.0 * vmax)) + 1
    write_cert(a.out, w, lay, points, centre, r1, K, M, A, J)
    _, _, _, s1 = evaluate(a.main, a.out, n)
    g1 = max(s1["ROWG"], s1["ROWH"])
    slope = max((g1 - g0) / r1, 1e-300)
    print(f"  row sums {g0:.3e} at r 1 and {g1:.3e} at r {r1}, |A F(c)| "
          f"{vmax:.3e}, entries {s1['JMAX']:.3e}", flush=True)
    best = g0 + 2.0 * math.sqrt(slope * vmax)
    if best >= 0.98:
        print(f"  no radius contracts: the row sums and the first step add to "
              f"at least {best:.3f}")
    for round_ in range(3):
        r = int(math.ceil(math.sqrt(vmax / slope)))
        K = g0 + slope * r
        r = max(r, int(math.ceil(vmax / (1.0 - K) * 1.01)) + 1)
        K = min(0.99, (g0 + slope * r) * 1.02 + 2.0 ** -12)
        M = 2.0 * s1["JMAX"] + 2.0 ** -40
        write_cert(a.out, w, lay, points, centre, r, K, M, A, J)
        rc, out = run(f'"{a.main}" --newton "{a.out}"')
        m = re.search(r"verdict: (\w+)", out)
        verdict = m.group(1) if m else "NONE"
        print(f"  check: {verdict} with K {K:.3e}, r {r} "
              f"({r * 2.0 ** min(lay.exps):.3e} to {r * 2.0 ** max(lay.exps):.3e} "
              f"in the reconstruction's units)", flush=True)
        if verdict == "VALID":
            break
        # the growth is not linear: read it again at the radius that failed
        _, _, _, s1 = evaluate(a.main, a.out, n)
        g1 = max(s1["ROWG"], s1["ROWH"])
        if g1 >= 0.98:
            print(f"  the row sums reach {g1:.3f} at that radius")
            break
        slope = max((g1 - g0) / r, 1e-300)
    print(f"wrote {a.out}: {verdict}, {time.time() - t0:.0f} s")
    return 0 if verdict == "VALID" else 1


if __name__ == "__main__":
    sys.exit(main())
