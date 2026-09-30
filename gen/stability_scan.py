"""The stability constant of the collocated manufactured problem against the
resolution, in floating point.

HalfGrid.lax_second_order derives the second-order bound from consistency and
a stability hypothesis: a constant S, the same at every radial step h, with
|x_h - x*| <= S |r(x*) - f|. For the collocated problem of mms_colloc.py this
prints, at each resolution, S_h = ||J_h^{-1}||_inf with J_h the Jacobian of
the forced node residual at x*, the smallest singular value of J_h, the
consistency residual max |r(x*) - f| and the product of the two, the Lax
bound on |x_h - x*|.

The residual at a node reads its own row and the two beside it, so J_h comes
from three complex-step sweeps per unknown of a row, each perturbing every
third row at once, whatever the resolution.

  python gen/stability_scan.py 3d 9,17,33,65,129,257,513,1025 --out DIR

writes each resolution's problem with `mms_colloc.py data CASE --smin 0.25
--gauge` into DIR when it is not there yet.
"""

import argparse
import json
import pathlib
import subprocess
import sys
import time

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import mms_colloc as mc  # noqa: E402


def jacobian(pb, x, h=1e-30):
    """The Jacobian of pb.residual at x by complex steps, three sweeps per
    unknown of a row."""
    rows = list(pb.rows)
    pos = {j: r for r, j in enumerate(rows)}
    per = pb.n // len(rows)
    J = np.zeros((pb.n, pb.n))
    point_row = [pos[p[0]] for p in pb.points]
    for color in range(3):
        for k in range(per):
            xx = x.astype(complex)
            xx[[r * per + k for r in range(len(rows)) if r % 3 == color]] += 1j * h
            d = np.imag(pb.residual(xx)) / h
            for i, r in enumerate(point_row):
                for rr in (r - 1, r, r + 1):
                    if 0 <= rr < len(rows) and rr % 3 == color:
                        J[i, rr * per + k] = d[i]
    return J


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("case")
    ap.add_argument("ns", help="comma-separated surface counts")
    ap.add_argument("--out", required=True, help="directory of the problems' data files")
    a = ap.parse_args()
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    gen = pathlib.Path(__file__).resolve().parent / "mms_colloc.py"
    for ns in (int(v) for v in a.ns.split(",")):
        t0 = time.time()
        path = out / f"{a.case}_ns{ns}.json"
        if not path.exists():
            subprocess.run([sys.executable, str(gen), "data", a.case, "--ns", str(ns), "--out",
                            str(out), "--smin", "0.25", "--gauge"], check=True,
                           stdout=subprocess.DEVNULL)
        pb = mc.Problem(json.loads(path.read_text()))
        F0 = np.real(pb.residual(pb.xstar))
        J = jacobian(pb, pb.xstar)
        S = float(np.abs(np.linalg.inv(J)).sum(axis=1).max())
        smin = float(np.linalg.svd(J, compute_uv=False).min())
        cons = float(np.abs(F0).max())
        print(f"{a.case} ns {ns:5d}: {pb.n:6d} unknowns, S_h = ||J^-1||_inf {S:.6e}, "
              f"1/sigma_min {1 / smin:.6e}, max |r(x*) - f| {cons:.3e}, Lax bound {S * cons:.3e} "
              f"({time.time() - t0:.0f} s)", flush=True)


if __name__ == "__main__":
    main()
