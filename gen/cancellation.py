"""How much the force residual cancels, as a certified number.

The radial residual is a difference of three terms,

  r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds,

and for a converged equilibrium it is far smaller than any of them. How much
smaller is not a curiosity. It is what decides the cost of a covering, since an
interval evaluation over a box does not see the cancellation and pays for the
loss in cells; and it decides which inputs the bound answers to, since a term
orders of magnitude below the others contributes nothing a bound could
register. A solver reports r_s and says nothing about either.

`--terms` carries the three terms as the three components of a certificate, so
the same machinery that bounds the residual bounds each of them, over the same
cells, at the same precision. This runs both coverings and reports the ratio.

  python gen/cancellation.py wout.nc --nodes 6 --nu 256
  python gen/cancellation.py wout.nc --node 22 --nu 512 --radial

The magnitudes are the certified value at each cell centre, worst over the
cells of a node, not the cell bound: a cell bound also carries the width of the
enclosure over the box, which narrows on its own as the cells shrink and would
flatter the cancellation.
"""

import argparse
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def per_node_cells(cert):
    """The centre magnitude of each component of each cell, per node block.

    A tightened bound line is `n0 q0 ndu qdu ndv qdv nc qc`, three lines per
    cell in component order, and the first pair is the enclosure at the cell
    centre. Keeping the cells rather than their maximum is what lets the terms
    and the residual be read at the same cell: a maximum of one taken at one
    angle and a maximum of the other taken at another compares nothing.
    """
    out, cur, inside, k = [], [], False, 0
    for line in pathlib.Path(cert).read_text().splitlines():
        if line.startswith("NODE"):
            if inside:
                out.append(cur)
            cur, inside, k = [], False, 0
            continue
        if line.startswith("CELLS"):
            inside = True
            continue
        if inside:
            f = line.split()
            if len(f) >= 8 and all(x.lstrip("-").isdigit() for x in f[:8]):
                v = float(f[0]) * 2.0 ** float(f[1])
                if k % 3 == 0:
                    cur.append([0.0, 0.0, 0.0])
                cur[-1][k % 3] = v
                k += 1
    if inside:
        out.append(cur)
    return out


def covering(wout, args, tag, main, python, tmp):
    """Generate and tighten one covering; return its per-cell magnitudes."""
    src = tmp / f"{tag}.txt"
    dst = tmp / f"{tag}_c.txt"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" {args}')
    if rc != 0:
        raise SystemExit(f"generator failed for {tag}:\n{out}")
    rc, out = run(f'"{main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        raise SystemExit(f"tighten failed for {tag}:\n{out}")
    return per_node_cells(dst), src


def certified_radii(cert):
    """The radius of each node block, from its own S line."""
    radii = []
    for line in pathlib.Path(cert).read_text().splitlines():
        if line.startswith("S "):
            f = line.split()
            radii.append(int(f[1]) * 2.0 ** int(f[2]))
    return radii


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--nodes", type=int, default=6)
    ap.add_argument("--node", type=int, default=None)
    ap.add_argument("--nu", type=int, default=256)
    ap.add_argument("--nv", type=int, default=None,
                    help="toroidal cells, which a three-dimensional "
                    "equilibrium needs to cover a surface")
    ap.add_argument("--radial", action="store_true",
                    help="the free-radius residual over a volume covering, "
                    "instead of the half-grid one on a surface")
    ap.add_argument("--nrad", type=int, default=4)
    ap.add_argument(
        "--main",
        default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    a = ap.parse_args()

    where = f"--node {a.node}" if a.node is not None else f"--nodes {a.nodes}"
    if a.radial:
        base = f"--radial {where} --nu {a.nu} --nrad {a.nrad}"
    else:
        surf = f" --nv {a.nv} --surface" if a.nv else ""
        base = f"--cells {where} --nu {a.nu}{surf}"

    tmp = pathlib.Path(tempfile.mkdtemp(prefix="cancel_"))
    terms, src = covering(a.wout, base + " --terms", "terms", a.main,
                          a.python, tmp)
    resid, _ = covering(a.wout, base, "resid", a.main, a.python, tmp)
    radii = certified_radii(src)

    kind = "free-radius" if a.radial else "half-grid"
    print(f"{pathlib.Path(a.wout).name}: the {kind} residual against the three "
          f"terms it is the difference of,")
    print(f"{a.nu} poloidal cells"
          + (f" by {a.nv} toroidal" if a.nv else "")
          + (f", {a.nrad} radial per node" if a.radial else ""))
    print("Everything is read at the cell where the residual is worst, which "
          "is the cell\nthe covering has to certify.")
    print(f"\n{'s':>8} {'(dvBs-dsBv)Bv':>15} {'(dsBu-duBs)Bu':>15} "
          f"{'mu0 p':>12} {'r_s':>13} {'cancels by':>11} {'p share':>9}")
    n = min(len(terms), len(resid), len(radii))
    if n == 0:
        raise SystemExit("no node blocks were tightened")
    ratios = []
    for i in range(n):
        cells = min(len(terms[i]), len(resid[i]))
        if cells == 0:
            continue
        # the cell whose residual is largest: that is the one the worst cell
        # bound of the node comes from
        k = max(range(cells), key=lambda j: resid[i][j][0])
        t1, t2, t3 = terms[i][k]
        rs = resid[i][k][0]
        big = max(t1, t2, t3)
        ratio = big / rs if rs > 0 else float("inf")
        share = t3 / rs if rs > 0 else float("inf")
        ratios.append(ratio)
        print(f"{radii[i]:>8.4f} {t1:>15.6e} {t2:>15.6e} {t3:>12.4e} "
              f"{rs:>13.6e} {ratio:>11.3g} {share:>9.2e}")

    # One reading for the equilibrium. The median rather than the worst,
    # because the axis and the edge cancel least on every stellarator here and
    # a minimum reports those and nothing else.
    srt = sorted(ratios)
    mid = (srt[len(srt) // 2] if len(srt) % 2
           else 0.5 * (srt[len(srt) // 2 - 1] + srt[len(srt) // 2]))
    reading = ("the terms cancel everywhere covered" if srt[0] >= 100.0
               else "the terms cancel over part of the covering and not the "
                    "rest" if mid >= 3.0
               else "the terms do not cancel anywhere covered")
    print(f"\ncancellation over the covering: {srt[0]:.3g} to {srt[-1]:.3g}, "
          f"median {mid:.3g}, so {reading}.")

    print("\nWhere the terms are far larger than their difference the residual "
          "is a\ncancellation defect, and a covering pays for it in cells: an "
          "interval\nevaluation over a box encloses each term separately and "
          "loses the difference,\nso the bound falls only as the cells narrow. "
          "Where they are not, the\nreconstruction is out of balance by "
          "something of its own size and no\nrefinement of the arithmetic "
          "reaches it. The last column is the pressure\nagainst the residual, "
          "and where it is small the bound does not answer to the\npressure at "
          "all.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
