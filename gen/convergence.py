"""The certified residual against the grid spacing.

`discretization_is_consistent` of theories/Hypotheses.v assumes the discrete
force operator approximates the continuum one at second order, which is the
premise every statement about the continuum problem rests on. It is stated
there as a property of a function of the grid spacing:

  bound h <= C h^2  for all small h,

and `bound h` is a quantity this development computes. The discrete solution
satisfies VMEC's discrete equations exactly; the continuum residual of a
reconstruction of it is the truncation error, so running the same equilibrium
at several radial resolutions and certifying the residual at the same physical
radius measures the order of the scheme rather than assuming it.

What is measured is the value at the centre of each cell, not the cell bound.
The cell bound also carries the width of the enclosure over the box, which
narrows on its own as the grid refines, and would flatter the result; the
centre value is a thin evaluation and is the residual itself.

Two residuals are worth measuring and they are not the same. `--half-grid`
certifies the one a point certificate carries, where every radial derivative is
VMEC's own centred difference of half points and no interpolant appears, so
what falls is the scheme's truncation error. Without it the free-radius
residual is measured instead, which adds the cubic Hermite: its second radial
derivative is built from slope defects divided by the grid spacing, so an
error of order h^2 in the endpoint slopes arrives as order h in the second
derivative. Running both separates the scheme from the reconstruction.

  python gen/convergence.py --data DIR --main PATH wout_a.nc wout_b.nc ...
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def node_near(path, s_target):
    """The interior full-grid node closest to s_target, with ns and mnmax."""
    import netCDF4

    d = netCDF4.Dataset(path)
    d.set_auto_mask(False)
    ns = int(d.variables["ns"][:])
    mnmax = int(d.variables["mnmax"][:])
    d.close()
    h = 1.0 / (ns - 1)
    s = np.arange(ns) * h
    lo, hi = 2, ns - 2
    j = int(np.clip(np.argmin(np.abs(s - s_target)), lo, hi))
    return j, ns, mnmax, h, float(s[j])


def worst_centre(cert):
    """The largest centre bound over every cell of a tightened certificate."""
    worst = 0.0
    inside = False
    for line in pathlib.Path(cert).read_text().splitlines():
        if line.startswith("CELLS"):
            inside = True
            continue
        if inside:
            f = line.split()
            if len(f) >= 8 and all(x.lstrip("-").isdigit() for x in f[:8]):
                worst = max(worst, float(f[0]) * 2.0 ** float(f[1]))
            else:
                inside = line.startswith(("NODE", "S ", "DU ")) or inside
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wouts", nargs="+")
    ap.add_argument("--data", default=".")
    ap.add_argument(
        "--main",
        default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--s", type=float, default=0.5,
                    help="the physical radius to certify at")
    ap.add_argument("--nu", type=int, default=256)
    ap.add_argument("--nrad", type=int, default=4)
    ap.add_argument("--half-grid", action="store_true",
                    help="the residual of a point certificate, which carries "
                    "no interpolant, instead of the free-radius one")
    a = ap.parse_args()

    data = pathlib.Path(a.data)
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="conv_"))
    kind = "half-grid" if a.half_grid else "free-radius"
    print(f"the certified {kind} residual at s = {a.s}, {a.nu} poloidal cells")
    print(f"{'ns':>5} {'modes':>6} {'h':>10} {'s':>9} {'residual':>13} "
          f"{'ratio':>7} {'order':>7}")
    rows = []
    for name in a.wouts:
        w = data / name
        if not w.exists():
            print(f"{name}: absent")
            continue
        j, ns, mnmax, h, s_j = node_near(w, a.s)
        src = tmp / f"{name}.txt"
        dst = tmp / f"{name}_c.txt"
        args = (f"--cells --node {j} --nu {a.nu}" if a.half_grid
                else f"--radial --node {j} --nu {a.nu} --nrad {a.nrad}")
        rc, out = run(f'"{a.python}" "{GEN}" "{w}" "{src}" {args}')
        if rc != 0:
            print(f"{ns:>5} generator failed: {out.strip().splitlines()[-1]}")
            continue
        rc, out = run(f'"{a.main}" --tighten "{src}" "{dst}"')
        if rc != 0:
            print(f"{ns:>5} tighten failed: {out.strip().splitlines()[-1]}")
            continue
        r = worst_centre(dst)
        if rows:
            h0, r0 = rows[-1][0], rows[-1][2]
            ratio = r0 / r if r else float("inf")
            # the order in h is meaningless when the family varies the modes
            order = (np.log(ratio) / np.log(h0 / h)
                     if r and abs(h0 - h) > 1e-15 else float("nan"))
            ostr = f"{order:>7.2f}" if order == order else f"{'':>7}"
            print(f"{ns:>5} {mnmax:>6} {h:>10.3e} {s_j:>9.5f} {r:>13.6e} "
                  f"{ratio:>7.2f} {ostr}")
        else:
            print(f"{ns:>5} {mnmax:>6} {h:>10.3e} {s_j:>9.5f} {r:>13.6e} "
                  f"{'':>7} {'':>7}")
        rows.append((h, mnmax, r))
    if len(rows) > 1:
        hs = np.array([x[0] for x in rows])
        rs = np.array([x[2] for x in rows])
        if hs.max() > hs.min():
            fit = np.polyfit(np.log(hs), np.log(rs), 1)[0]
            print(f"\nfitted order in the grid spacing: {fit:.2f}")
            print("Second order is what discretization_is_consistent assumes. "
                  "A family that\nflattens is at its spectral floor rather "
                  "than out of order: hold the grid and\nadd modes to see "
                  "which of the two is binding.")
        else:
            print("\nthe grid is fixed, so what varies is the mode set; the "
                  "ratios above are\nwhat adding modes buys at this "
                  "resolution")


if __name__ == "__main__":
    main()
