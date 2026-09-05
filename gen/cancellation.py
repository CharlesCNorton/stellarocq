"""How much the force residual cancels, as a certified number.

The residual is a difference of three terms,

  r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds,

and for a converged equilibrium it is far smaller than any of them. That ratio
decides the cost of a covering, since an interval evaluation loses the
cancellation and pays for it in cells, and it decides which inputs the bound
answers to, since a term far below the others is one no bound registers.

--terms carries the three terms as the three components, so the same machinery
bounds each over the same cells at the same precision; this runs both coverings
and reports the ratio.

  python gen/cancellation.py wout.nc --nodes 6 --nu 256
  python gen/cancellation.py wout.nc --node 22 --nu 512 --radial

The magnitudes are the certified value at each cell centre, not the cell bound,
which also carries an enclosure width that narrows on its own and would flatter
the cancellation.
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
    """Centre magnitude of each component of each cell, per node block.

    A tightened bound line is n0 q0 ndu qdu ndv qdv nc qc, three lines per cell
    in component order, the first pair the enclosure at the centre. Keeping the
    cells rather than their maximum lets the terms and the residual be read at
    the same cell.
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


def certified_angles(cert):
    """Centre angles of the shared cells, in radians, in listed order."""
    lines = pathlib.Path(cert).read_text().splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("NANGLES"))
    n = int(lines[i].split()[1])
    out = []
    for l in lines[i + 1:i + 1 + n]:
        f = l.split()
        out.append((int(f[0]) * 2.0 ** int(f[1]), int(f[2]) * 2.0 ** int(f[3])))
    return out


def current_terms(a, base, tmp):
    """The two terms of the surface current against their difference, at the worst cell."""
    cells, src = covering(a.wout, base + " --current", "current", a.main,
                          a.python, tmp)
    radii = certified_radii(src)
    angles = certified_angles(src)
    kind = "free-radius" if a.radial else "half-grid"
    print(f"{pathlib.Path(a.wout).name}: the {kind} surface current against "
          f"the two terms it is the difference of,")
    print(f"{a.nu} poloidal cells"
          + (f" by {a.nv} toroidal" if a.nv else "")
          + (f", {a.nrad} radial per node" if a.radial else ""))
    print("Everything is read at the cell where the current is worst.")
    print(f"\n{'s':>8} {'u':>7} {'d_u B_v':>15} {'d_v B_u':>15} "
          f"{'mu0 sqrtg J^s':>15} {'cancels by':>11}")
    ratios = []
    for i in range(min(len(cells), len(radii))):
        if not cells[i]:
            continue
        k = max(range(len(cells[i])), key=lambda j: cells[i][j][2])
        t1, t2, js = cells[i][k]
        ratio = max(t1, t2) / js if js > 0 else float("inf")
        ratios.append(ratio)
        u = angles[k][0] if k < len(angles) else float("nan")
        print(f"{radii[i]:>8.4f} {u:>7.4f} {t1:>15.6e} {t2:>15.6e} "
              f"{js:>15.6e} {ratio:>11.3g}")
        if a.exact:
            print(f"  exact s={radii[i]!r} u={u!r}")
    if not ratios:
        raise SystemExit("no node blocks were tightened")
    srt = sorted(ratios)
    mid = (srt[len(srt) // 2] if len(srt) % 2
           else 0.5 * (srt[len(srt) // 2 - 1] + srt[len(srt) // 2]))
    print(f"\ncancellation of the surface current over the covering: "
          f"{srt[0]:.3g} to {srt[-1]:.3g}, median {mid:.3g}")
    print("For an axisymmetric equilibrium d_v B_u is the zero expression and "
          "the current is\nd_u B_v alone, so the ratio there is one by "
          "construction and says nothing; it is\nthe three-dimensional cases "
          "where the two have to cancel.")
    return 0


def quasisym_terms(a, base, tmp):
    """The quasisymmetry residual against the two products it is the
    difference of, at the worst cell of each node.

    The triple product is d_u B^2 d_v W2 - d_v B^2 d_u W2 over 4 B^2 sqrt(g),
    and a quasisymmetric field is one where the two products are the same
    number, so the ratio of the larger to their difference is how nearly the
    surface is quasisymmetric, as a certified number: a field far from
    quasisymmetry has a ratio near one, and an axisymmetric one has no
    difference at all, since both products carry an exact zero.
    """
    cells, src = covering(a.wout, base + " --quasisym", "quasisym", a.main,
                          a.python, tmp)
    radii = certified_radii(src)
    angles = certified_angles(src)
    print(f"{pathlib.Path(a.wout).name}: the quasisymmetry residual against "
          f"the two products it is the difference of,")
    print(f"{a.nu} poloidal cells" + (f" by {a.nv} toroidal" if a.nv else ""))
    print("Everything is read at the cell where the residual is worst.")
    print(f"\n{'s':>8} {'u':>7} {'v':>7} {'d_uB2 d_vW2':>15} {'d_vB2 d_uW2':>15} "
          f"{'triple':>15} {'cancels by':>11}")
    ratios = []
    for i in range(min(len(cells), len(radii))):
        if not cells[i]:
            continue
        k = max(range(len(cells[i])), key=lambda j: cells[i][j][0])
        qs, t1, t2 = cells[i][k]
        ratio = max(t1, t2) / qs if qs > 0 else float("inf")
        ratios.append(ratio)
        u, vv = angles[k] if k < len(angles) else (float("nan"),) * 2
        print(f"{radii[i]:>8.4f} {u:>7.4f} {vv:>7.4f} {t1:>15.6e} {t2:>15.6e} "
              f"{qs:>15.6e} {ratio:>11.3g}")
    if not ratios:
        raise SystemExit("no node blocks were tightened")
    srt = sorted(ratios)
    mid = (srt[len(srt) // 2] if len(srt) % 2
           else 0.5 * (srt[len(srt) // 2 - 1] + srt[len(srt) // 2]))
    print(f"\nquasisymmetry over the covering: the products exceed their "
          f"difference by {srt[0]:.3g} to {srt[-1]:.3g}, median {mid:.3g}")
    print("For an axisymmetric equilibrium both products are exactly zero and "
          "the ratio is\nundefined; for a three-dimensional one the ratio "
          "says how nearly the two are the\nsame number, which is what "
          "quasisymmetry asks of them.")
    return 0


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
    ap.add_argument("--cells-of", type=int, default=None, metavar="I",
                    help="print every cell of node block I rather than the "
                    "worst cell of each block, so where on the surface the "
                    "terms cancel is visible")
    ap.add_argument("--exact", action="store_true",
                    help="print the radius and angle of each worst cell to "
                    "full precision, so a reference can be read at the same "
                    "point")
    ap.add_argument("--current", action="store_true",
                    help="the surface current instead of the radial "
                    "residual: d_u B_v and d_v B_u against their difference "
                    "mu0 sqrt(g) J^s, which r_u and r_v are built from and "
                    "which has to vanish for a Boozer stream function to "
                    "exist")
    ap.add_argument("--quasisym", action="store_true",
                    help="the quasisymmetry residual instead: the two "
                    "products of the triple product against their "
                    "difference, which is how nearly the surface is "
                    "quasisymmetric as a certified number")
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
    if a.quasisym:
        return quasisym_terms(a, base, tmp)
    if a.current:
        return current_terms(a, base, tmp)
    terms, src = covering(a.wout, base + " --terms", "terms", a.main,
                          a.python, tmp)
    resid, _ = covering(a.wout, base, "resid", a.main, a.python, tmp)
    radii = certified_radii(src)
    angles = certified_angles(src)

    kind = "free-radius" if a.radial else "half-grid"
    print(f"{pathlib.Path(a.wout).name}: the {kind} residual against the three "
          f"terms it is the difference of,")
    print(f"{a.nu} poloidal cells"
          + (f" by {a.nv} toroidal" if a.nv else "")
          + (f", {a.nrad} radial per node" if a.radial else ""))
    n = min(len(terms), len(resid), len(radii))
    if n == 0:
        raise SystemExit("no node blocks were tightened")

    if a.cells_of is not None:
        # every cell of one node, against the poloidal angle
        i = a.cells_of
        if not 0 <= i < n:
            raise SystemExit(f"--cells-of must be below {n}")
        print(f"every cell of node block {i}, at s = {radii[i]:.4f}")
        print(f"\n{'u':>8} {'v':>8} {'(dvBs-dsBv)Bv':>15} {'(dsBu-duBs)Bu':>15} "
              f"{'mu0 p':>12} {'r_s':>13} {'cancels by':>11}")
        for k in range(min(len(terms[i]), len(resid[i]))):
            t1, t2, t3 = terms[i][k]
            rs = resid[i][k][0]
            ratio = max(t1, t2, t3) / rs if rs > 0 else float("inf")
            u, vv = angles[k] if k < len(angles) else (float("nan"),) * 2
            print(f"{u:>8.4f} {vv:>8.4f} {t1:>15.6e} {t2:>15.6e} {t3:>12.4e} "
                  f"{rs:>13.6e} {ratio:>11.3g}")
        return 0

    print("Everything is read at the cell where the residual is worst, which "
          "is the cell\nthe covering has to certify.")
    print(f"\n{'s':>8} {'u':>7} {'(dvBs-dsBv)Bv':>15} {'(dsBu-duBs)Bu':>15} "
          f"{'mu0 p':>12} {'r_s':>13} {'cancels by':>11} {'p share':>9}")
    ratios = []
    for i in range(n):
        cells = min(len(terms[i]), len(resid[i]))
        if cells == 0:
            continue
        # the cell whose residual is largest, which the node's worst bound comes from
        k = max(range(cells), key=lambda j: resid[i][j][0])
        t1, t2, t3 = terms[i][k]
        rs = resid[i][k][0]
        big = max(t1, t2, t3)
        ratio = big / rs if rs > 0 else float("inf")
        share = t3 / rs if rs > 0 else float("inf")
        ratios.append(ratio)
        u = angles[k][0] if k < len(angles) else float("nan")
        print(f"{radii[i]:>8.4f} {u:>7.4f} {t1:>15.6e} {t2:>15.6e} {t3:>12.4e} "
              f"{rs:>13.6e} {ratio:>11.3g} {share:>9.2e}")
        if a.exact:
            print(f"  exact s={radii[i]!r} u={u!r}")

    # the median, since the axis and edge cancel least and a minimum reports only those
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
