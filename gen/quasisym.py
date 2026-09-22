"""Quasisymmetry decided from certified harmonics, surface by surface.

A field is quasisymmetric exactly when (B x grad s . grad B) / (B . grad B)
is a flux function (Helander 2014). The two-term certificate carries, at each
point, the defect Q = t1 - t2 of the claim that this ratio equals the number
F0 the certificate names, beside the two terms t1 = J C F and t2 = F0 J C
themselves. For a quasisymmetric field t1 = F* J C at every point for one
constant F*, so Q = (F* / F0 - 1) t2 pointwise, and every discrete harmonic of
Q over the angles of a point certificate is that one number times the
matching harmonic of t2. Project.harm_encloses certifies both harmonics, so
two ratios Q_mn / t2_mn whose enclosures are disjoint prove that no such F*
exists: the ratio is not a flux function of the reconstructed field. The one
step outside the checker is that a pointwise proportionality carries to the
discrete sums, which is the distributive law. The identity behind the
criterion holds of an exact equilibrium, and a reconstruction carries a
residual, so the ratios of an axisymmetric field, which is quasisymmetric,
spread by that much: 2e-4 on wout_solovev. The span of the ratios is what
the tool reports, and a span of order one is the field's own.

  python gen/quasisym.py wout.nc --nodes 5,12,24,37,44 [--nu 64] [--nv 32]

The harmonics are printed for the modes at which t2 is largest, with the
ratio of each, and the ratio is reported as not one constant when two of
those ratios are disjoint.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def spectrum(out):
    """Every harmonic line of a `--project --spectrum` run, keyed by mode."""
    got = {}
    for m in re.finditer(
            r"^\s+\((-?\d+),(-?\d+)\) (cos|sin)  r_s \[(\S+), (\S+)\]  "
            r"r_u \[(\S+), (\S+)\]  r_v \[(\S+), (\S+)\]", out, re.M):
        got[(int(m.group(1)), int(m.group(2)), m.group(3))] = tuple(
            float(m.group(i)) for i in range(4, 10))
    return got


def divide(a, b):
    """The quotient of two intervals, or None when the divisor holds zero."""
    lo, hi = a
    c, d = b
    if c <= 0.0 <= d:
        return None
    q = (lo / c, lo / d, hi / c, hi / d)
    return (min(q), max(q))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--nodes", default="5,12,24,37,44")
    ap.add_argument("--nu", type=int, default=64)
    ap.add_argument("--nv", type=int, default=32)
    ap.add_argument("--top", type=int, default=6,
                    help="how many modes to compare, the largest in t2")
    ap.add_argument("--main",
                    default=str(ROOT / "extract" / "_build" / "default"
                                / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    a = ap.parse_args()

    import netCDF4
    with netCDF4.Dataset(a.wout) as d:
        d.set_auto_mask(False)
        ns = int(d.variables["ns"][:])
        iotaf = [float(x) for x in d.variables["iotaf"][:]]
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="qs_"))
    print(f"{a.wout}: the two-term quasisymmetry ratio, {a.nu} by {a.nv} "
          f"angles per surface")
    proven = 0
    nodes = [int(x) for x in a.nodes.split(",")]
    for j in nodes:
        cert = tmp / f"q_{j}.txt"
        rc, out = run(f'"{a.python}" "{GEN}" "{a.wout}" "{cert}" --node {j} '
                      f'--nu {a.nu} --nv {a.nv} --quasisym-two')
        if rc != 0:
            raise SystemExit(f"generator failed:\n{out}")
        f0 = float(re.search(r"F0 = (\S+)", out).group(1))
        rc, out = run(f'"{a.main}" --project --spectrum "{cert}"')
        if rc != 0 or "verdict: VALID" not in out:
            raise SystemExit(f"the certificate was not established:\n{out}")
        sp = spectrum(out)
        rows = []
        for (m, n, k), v in sp.items():
            t2 = (v[4], v[5])
            if max(abs(t2[0]), abs(t2[1])) < 1e-300:
                continue
            r = divide((v[0], v[1]), t2)
            if r is not None:
                rows.append((abs(0.5 * (t2[0] + t2[1])), m, n, k, (v[0], v[1]),
                             t2, r))
        rows.sort(reverse=True)
        rows = rows[:a.top]
        print(f"\n  s = {j / (ns - 1):.3f}, iota = {iotaf[j]:.4f}, F0 = {f0:.6e}")
        for _, m, n, k, q, t2, r in rows:
            print(f"    ({m:2d},{n:3d}) {k}  Q [{q[0]:+.4e}, {q[1]:+.4e}]  "
                  f"t2 [{t2[0]:+.4e}, {t2[1]:+.4e}]  "
                  f"Q/t2 [{r[0]:+.6f}, {r[1]:+.6f}]")
        pairs = [(x, y) for i, x in enumerate(rows) for y in rows[i + 1:]]
        disjoint = [(x, y) for x, y in pairs
                    if x[6][1] < y[6][0] or y[6][1] < x[6][0]]
        spread = max(r[6][1] for r in rows) - min(r[6][0] for r in rows)
        if disjoint:
            proven += 1
            print(f"    the ratio is not one constant: {len(disjoint)} of "
                  f"{len(pairs)} pairs of ratios are disjoint, and the ratios "
                  f"span {spread:.3e}")
        else:
            print("    undecided: every pair of ratios overlaps")
    print(f"\n{proven} of {len(nodes)} surfaces carry a ratio that is not one "
          "constant. A quasisymmetric field in exact force balance spans zero;\n"
          "what the discretization alone leaves is the span of an axisymmetric "
          "reconstruction, 2e-4 on wout_solovev, so a span of order one is\n"
          "the field's own departure from quasisymmetry.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
