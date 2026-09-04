"""Measure how much refining each node interval still buys.

`--adapt` gives a node its own radial resolution. The thresholds it uses were
picked by hand from one equilibrium, which is exactly the kind of number that
is right until it is not. This measures the thing the thresholds stand in for:
run a node at two resolutions and see how far the bound falls.

A node whose bound halves when the cells halve is enclosure-limited and worth
refining. One whose bound barely moves has reached the reconstruction, and
cells spent there do nothing.

  python gen/nrad_profile.py wout.nc --main PATH [--nodes 2,8,22,40] [--nu 128]

It prints the ratio per node and a profile the generator can be given, so the
resolution follows a measurement rather than a guess.
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


def worst_at(wout, node, nu, nrad, main, python, tmp):
    """The worst cell bound for one node at one radial resolution."""
    src = tmp / f"p{node}_{nrad}.txt"
    dst = tmp / f"p{node}_{nrad}_c.txt"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" --radial '
                  f'--node {node} --nu {nu} --nrad {nrad}')
    if rc != 0:
        return None
    rc, out = run(f'"{main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        return None
    m = re.search(r"worst cell bound ([0-9.e+-]+)", out)
    return float(m.group(1)) if m else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--main",
                    default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--nodes", default="3,6,12,22,40")
    ap.add_argument("--nu", type=int, default=128)
    ap.add_argument("--coarse", type=int, default=8)
    a = ap.parse_args()

    nodes = [int(x) for x in a.nodes.split(",")]
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="nrad_"))
    print(f"{'node':>5} {'coarse':>12} {'fine':>12} {'ratio':>7}  refining")
    rows = []
    for nd in nodes:
        c = worst_at(a.wout, nd, a.nu, a.coarse, a.main, a.python, tmp)
        f = worst_at(a.wout, nd, a.nu, 4 * a.coarse, a.main, a.python, tmp)
        if c is None or f is None:
            print(f"{nd:>5} {'skipped':>12}")
            continue
        ratio = c / f if f > 0 else float("inf")
        verdict = ("still pays" if ratio > 2.5 else
                   "little left" if ratio > 1.3 else "spent")
        rows.append((nd, ratio))
        print(f"{nd:>5} {c:>12.4e} {f:>12.4e} {ratio:>7.2f}  {verdict}")

    if rows:
        print("\na profile from that, as multiples of the base resolution.")
        print("gen/make_cert.py --adapt-from reads these lines, so the "
              "resolution\nfollows the measurement rather than a threshold "
              "picked by hand:")
        for nd, ratio in rows:
            mult = 4 if ratio > 2.5 else 2 if ratio > 1.3 else 1
            print(f"  node {nd}: {mult}x")
        print("\nRefining four times buys a factor of sixteen where the bound "
              "is the enclosure\nand nothing where it is the reconstruction, "
              "so a ratio near one says to stop.")


if __name__ == "__main__":
    main()
