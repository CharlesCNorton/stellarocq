"""A floor on the two-term quasisymmetry defect of a surface over a box of
states (theories/QSFloor.v).

The surface is the outer half point of node j, where Physics.RQuasiTwo reads
the two terms t1 = L_v A_u - L_u A_v and t2 = F0 J C of the criterion that
t1 / (J C) be a flux function; F0 = 1 here, so the claim is t1 = lam t2 with
lam constant on the surface. The box widens every R, Z and lambda coefficient
of the node's stencil by a relative half-width of the largest coefficient of
its row, and iota on its two half points by the same relative half-width of
its own value. `main --qs` establishes
QSFloor.check_qcert and prints, for every kernel listed, the enclosures of the
harmonics of t1 and t2 over the box. This picks the pair of kernels whose
ratio boxes are furthest apart and checks the premises of QSFloor.qs_floor in
exact rational arithmetic: the harmonics of t2 keep one sign, e is the least
of their magnitudes, and g the gap between the ratio boxes. The theorem then
says that at every state of the box and for every lam some point has
|t1 - lam t2| >= e g / (2 N).

  python gen/qs_floor.py WOUT OUT --node J --rel 1e-8 --nu 32 --nv 16 --main PATH
"""

import argparse
import json
import math
import pathlib
import re
import subprocess
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from forced_sheet import box_block, state  # noqa: E402
from make_cert import ANGLE_EXP, Wout, calibrate_pressure, dyadic_at  # noqa: E402


def field_periods(w):
    xn = np.abs(np.asarray(w.xn, dtype=int))
    return int(np.gcd.reduce(xn[xn != 0])) if (xn != 0).any() else 1


def row_block(values, rel):
    """A row of coefficients on the exponent of its largest, each widened by
    rel times that largest: a solver's run-to-run spread is absolute, of the
    order of its largest coefficient's rounding, so a small coefficient needs
    the same absolute width as a large one."""
    big = max((abs(float(v)) for v in values), default=0.0)
    if big == 0.0:
        return [(0, 0, 0) for _ in values]
    e = int(np.frexp(big)[1]) - 53
    d = int(math.ceil(rel * 2.0**53)) + 1
    return [(round(float(v) / 2.0**e), e, d) for v in values]


def write_qcert(path, w, j, rel, nu, nv, kernels, rel_rz=None, rel_l=None):
    phip = float(w.phips[1])
    st = state(w, j, phip, rel) + [(1, 0, 0)]  # F0 = 1
    # iota on the two half points is widened too, since a run that holds the
    # enclosed current rather than iota moves it with the boundary
    st[9:11] = box_block([w.iotas[j], w.iotas[j + 1]], rel)
    # with --rel-rz or --rel-l, every coefficient row on the width of its
    # largest coefficient, R and Z rows at one relative width and lambda rows
    # at another; otherwise each coefficient at rel of its own size
    if rel_rz is None and rel_l is None:
        pts = [(dyadic_at(2 * math.pi * i / nu)[0],
                dyadic_at(2 * math.pi * k / (field_periods(w) * nv))[0])
               for i in range(nu) for k in range(nv)]
        return _emit(path, w, st, kernels, pts)
    rel_rz = rel if rel_rz is None else rel_rz
    rel_l = rel if rel_l is None else rel_l
    K = len(w.xm)
    rows = [(w.rmnc[j - 1], rel_rz), (w.rmnc[j], rel_rz), (w.rmnc[j + 1], rel_rz),
            (w.zmns[j - 1], rel_rz), (w.zmns[j], rel_rz), (w.zmns[j + 1], rel_rz),
            (w.lmns[j], rel_l), (w.lmns[j + 1], rel_l)]
    if w.lasym:
        rows += [(w.rmns[j - 1], rel_rz), (w.rmns[j], rel_rz), (w.rmns[j + 1], rel_rz),
                 (w.zmnc[j - 1], rel_rz), (w.zmnc[j], rel_rz), (w.zmnc[j + 1], rel_rz),
                 (w.lmnc[j], rel_l), (w.lmnc[j + 1], rel_l)]
    for i, (r, rr) in enumerate(rows):
        st[32 + i * K: 32 + (i + 1) * K] = row_block(r, rr)
    nfp = field_periods(w)
    pts = [(dyadic_at(2 * math.pi * i / nu)[0], dyadic_at(2 * math.pi * k / (nfp * nv))[0])
           for i in range(nu) for k in range(nv)]
    return _emit(path, w, st, kernels, pts)


def _emit(path, w, st, kernels, pts):
    modes = [(int(m), int(n)) for m, n in zip(w.xm, w.xn, strict=True)]
    L = ["STELLAROCQ-QCERT", "PREC 53", f"LASYM {1 if w.lasym else 0}",
         f"PROFILE {w.profile}", f"MODES {len(modes)}"]
    L += [f"{m} {n}" for m, n in modes]
    L += [f"NSLOTS {len(st)}", "STATE"] + [f"{m} {e} {d}" for m, e, d in st]
    L += ["SLOTS 1 2", f"KERNELS {len(kernels)}"]
    L += [f"{1 if s else 0} {m} {n}" for s, m, n in kernels]
    L += [f"NPOINTS {len(pts)}"] + [f"{a} {b}" for a, b in pts]
    pathlib.Path(path).write_text("\n".join(L) + "\n")
    return len(pts)


def ratio_box(a, b, c, d):
    q = [a / c, a / d, b / c, b / d]
    return min(q), max(q)


def down(x):
    """The largest double not above the rational x."""
    f = float(x)
    return f if Fraction(f) <= x else math.nextafter(f, -math.inf)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("out")
    ap.add_argument("--node", type=int, required=True)
    ap.add_argument("--rel", type=float, default=1e-8,
                    help="relative half-width of iota, and of every row by default")
    ap.add_argument("--rel-rz", type=float, default=None,
                    help="relative half-width of the R and Z rows, of each row's largest")
    ap.add_argument("--rel-l", type=float, default=None,
                    help="relative half-width of the lambda rows, of each row's largest")
    ap.add_argument("--nu", type=int, default=32)
    ap.add_argument("--nv", type=int, default=16)
    ap.add_argument("--mmax", type=int, default=6)
    ap.add_argument("--nmax", type=int, default=3)
    ap.add_argument("--main", required=True)
    a = ap.parse_args()
    w = Wout(a.wout)
    calibrate_pressure(w)
    nfp = field_periods(w)
    kernels = [(s, m, n * nfp) for m in range(a.mmax + 1) for n in range(-a.nmax, a.nmax + 1)
               for s in (False, True) if not (m == 0 and n < 0) and not (s and m == 0 and n == 0)]
    npts = write_qcert(a.out, w, a.node, a.rel, a.nu, a.nv, kernels, a.rel_rz, a.rel_l)
    s = (a.node + 0.5) / (w.ns - 1)
    print(f"{pathlib.Path(a.wout).name}: node {a.node}, surface s = {s:.4f}, "
          f"box {a.rel:g}, {npts} points, {len(kernels)} kernels", flush=True)
    p = subprocess.run([a.main, "--qs", a.out], stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    print(p.stdout.splitlines()[0] if p.stdout else "(no output)")
    if "verdict: VALID" not in p.stdout:
        print(p.stdout[-2000:])
        return 1
    rows = []
    for m in re.finditer(r"^H (\d+) (\d) (-?\d+) (-?\d+) (\S+) (\S+) (\S+) (\S+)$",
                         p.stdout, re.M):
        vals = [Fraction(float.fromhex(m.group(i))) for i in range(5, 9)]
        rows.append((int(m.group(2)), int(m.group(3)), int(m.group(4)), *vals))
    # kernels at which the harmonic of t2 keeps one sign
    good = [r for r in rows if r[5] > 0 or r[6] < 0]
    best = None
    for i in range(len(good)):
        for k in range(i + 1, len(good)):
            s1, m1, n1, a1, b1, c1, d1 = good[i]
            s2, m2, n2, a2, b2, c2, d2 = good[k]
            lo1, hi1 = ratio_box(a1, b1, c1, d1)
            lo2, hi2 = ratio_box(a2, b2, c2, d2)
            g = max(lo2 - hi1, lo1 - hi2)
            if g <= 0:
                continue
            e = min(abs(c1), abs(d1), abs(c2), abs(d2))
            floor = e * g / (2 * npts)
            if best is None or floor > best[0]:
                best = (floor, e, g, good[i], good[k], (lo1, hi1), (lo2, hi2))
    if best is None:
        print("no two kernels have disjoint ratio boxes over this box of states")
        res = {"wout": a.wout, "node": a.node, "rel": a.rel, "floor": None}
    else:
        floor, e, g, k1, k2, r1, r2 = best
        name = lambda r: f"{'sin' if r[0] else 'cos'}({r[1]} u - {r[2]} v)"  # noqa: E731
        print(f"kernels {name(k1)} and {name(k2)}: ratio boxes [{float(r1[0]):+.6e}, "
              f"{float(r1[1]):+.6e}] and [{float(r2[0]):+.6e}, {float(r2[1]):+.6e}], "
              f"gap g = {float(g):.6e}, |harmonic of t2| >= e = {float(e):.6e}")
        print(f"floor: at every state of the box and for every lam, some point has "
              f"|t1 - lam t2| >= {down(floor):.17e}")
        res = {"wout": a.wout, "node": a.node, "rel": a.rel, "points": npts,
               "kernels": [list(k1[:3]), list(k2[:3])], "gap": down(g), "e": down(e),
               "floor": down(floor)}
    pathlib.Path(a.out + ".json").write_text(json.dumps(res, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
