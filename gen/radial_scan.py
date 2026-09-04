"""The certified residual surface by surface, against the transform.

A single number for an equilibrium hides where it comes from. This certifies
the residual at every surface of one covering and prints it beside the
rotational transform and the nearest resonance, so that what limits the
equilibrium can be read off rather than guessed.

Two things it has been used to settle. For `wout_cth_like_fixed_bdy` the
residual grows smoothly from the axis outward and takes no notice of the
surfaces where iota crosses 5/4 or 1, so the reconstruction is not resolving an
island chain there. And comparing two mode sets surface by surface says where
modes are worth spending: at the edge they buy an order of magnitude, near the
axis almost nothing, which is the near-axis reconstruction rather than the
spectrum.

  python gen/radial_scan.py wout.nc [--nodes 24] [--nu 128] [--nv 4]
"""

import argparse
import pathlib
import subprocess
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def per_node(cert):
    """The worst centre bound of each node block, in file order."""
    out, cur, inside = [], 0.0, False
    for line in pathlib.Path(cert).read_text().splitlines():
        if line.startswith("NODE"):
            if inside:
                out.append(cur)
            cur, inside = 0.0, False
            continue
        if line.startswith("CELLS"):
            inside = True
            continue
        if inside:
            f = line.split()
            if len(f) >= 8 and all(x.lstrip("-").isdigit() for x in f[:8]):
                cur = max(cur, float(f[0]) * 2.0 ** float(f[1]))
    if inside:
        out.append(cur)
    return out


def nearest_resonance(iota, nfp, mmax=12):
    """The closest k nfp / m to iota, and how far it is.

    A field-periodic device resonates where iota is a ratio with the field
    period in the numerator, so those are the surfaces an island chain would
    sit on.
    """
    best = (1e9, 0, 1)
    for m in range(1, mmax + 1):
        k = round(iota * m / nfp)
        if k <= 0:
            continue
        d = abs(iota - k * nfp / m)
        if d < best[0]:
            best = (d, k * nfp, m)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--nodes", type=int, default=24)
    ap.add_argument("--nu", type=int, default=128)
    ap.add_argument("--nv", type=int, default=4)
    ap.add_argument(
        "--main",
        default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    a = ap.parse_args()

    import netCDF4

    d = netCDF4.Dataset(a.wout)
    d.set_auto_mask(False)
    ns = int(d.variables["ns"][:])
    iotas = np.asarray(d.variables["iotas"][:])
    xn = np.asarray(d.variables["xn"][:]).astype(int)
    mnmax = int(d.variables["mnmax"][:])
    d.close()
    nfp = int(np.gcd.reduce(np.abs(xn[xn != 0]))) if (xn != 0).any() else 1

    src = "/tmp/radial_scan.txt"
    dst = "/tmp/radial_scan_c.txt"
    rc, out = run(f'"{a.python}" "{GEN}" "{a.wout}" "{src}" --cells '
                  f'--nodes {a.nodes} --nu {a.nu} --nv {a.nv}')
    if rc != 0:
        raise SystemExit(out)
    rc, out = run(f'"{a.main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        raise SystemExit(out)
    vals = per_node(dst)
    idx = np.unique(np.linspace(2, ns - 2, a.nodes).astype(int))

    print(f"{pathlib.Path(a.wout).name}  ns={ns}  modes={mnmax}  nfp={nfp}")
    print(f"{'s':>8} {'iota':>8} {'residual':>12} {'resonance':>11} "
          f"{'distance':>10}")
    for j, v in zip(idx, vals, strict=False):
        io = float(iotas[j + 1])
        dist, kn, m = nearest_resonance(io, nfp)
        print(f"{j / (ns - 1):>8.4f} {io:>8.4f} {v:>12.4e} "
              f"{kn:>5}/{m:<5} {dist:>10.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
