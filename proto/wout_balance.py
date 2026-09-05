"""Force balance read off VMEC's own covariant field arrays.

The node residual of theories/Physics.v,

  r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds,

assembled from the file's own bsubumnc, bsubvmnc, bsubsmns, bsupumnc, bsupvmnc
and presf rather than from a reconstruction: angular derivatives exact from
VMEC's series, radial ones the centred differences the certified residual uses,
pressure a centred difference of presf. Nothing from rmnc, zmns or lmns enters.

The three terms and their difference are the solver's own, and their ratio is
directly comparable with the certified one of gen/cancellation.py: agreement
means the covering reports what the solver's field already says, and a
non-cancelling ratio at zero pressure means the field VMEC wrote is not in
pointwise force balance.

  python proto/wout_balance.py wout.nc [--nodes 6] [--nu 64] [--nv 16]
"""

import argparse
import sys

import netCDF4
import numpy as np

MU0 = 4e-7 * np.pi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--nodes", type=int, default=6)
    ap.add_argument("--nu", type=int, default=64)
    ap.add_argument("--nv", type=int, default=16)
    a = ap.parse_args()

    d = netCDF4.Dataset(a.wout)
    d.set_auto_mask(False)
    v = d.variables
    g = lambda k: np.asarray(v[k][:], dtype=float)  # noqa: E731
    ns = int(v["ns"][:])
    h = 1.0 / (ns - 1)
    xm, xn = g("xm_nyq"), g("xn_nyq")
    bs, bu, bv = g("bsubsmns"), g("bsubumnc"), g("bsubvmnc")
    cu, cv = g("bsupumnc"), g("bsupvmnc")
    presf = g("presf")
    lasym = "lasym__logical__" in v and bool(int(v["lasym__logical__"][:]))
    if lasym:
        bsc, bus, bvs = g("bsubsmnc"), g("bsubumns"), g("bsubvmns")
        cus, cvs = g("bsupumns"), g("bsupvmns")
    nfp = int(v["nfp"][:])
    three_d = bool((xn != 0).any())
    nv = a.nv if three_d else 1
    d.close()

    nodes = np.unique(np.linspace(2, ns - 2, a.nodes).astype(int))
    print(f"{a.wout}: the node residual assembled from the file's own "
          f"covariant field")
    print(f"{a.nu} poloidal by {nv} toroidal sample points per node, read at "
          f"the point where the residual is worst\n")
    print(f"{'s':>8} {'(dvBs-dsBv)Bv':>15} {'(dsBu-duBs)Bu':>15} "
          f"{'mu0 p':>12} {'r_s':>13} {'cancels by':>11}")
    ratios = []
    for j in nodes:
        pp = MU0 * (presf[j + 1] - presf[j - 1]) / (2 * h)
        worst = None
        for k in range(a.nu):
            u = 2 * np.pi * k / a.nu
            for l in range(nv):
                vv = 2 * np.pi * l / (nfp * nv)
                ang = xm * u - xn * vv
                co, si = np.cos(ang), np.sin(ang)
                # B_s on the full grid at the node, and its angular derivatives
                bs_u = float(bs[j] @ (xm * co))
                bs_v = float(bs[j] @ (-xn * co))
                # the half-point values of B_u and B_v either side of the node
                bu_m, bu_p = float(bu[j] @ co), float(bu[j + 1] @ co)
                bv_m, bv_p = float(bv[j] @ co), float(bv[j + 1] @ co)
                b_u = 0.5 * float((cu[j] + cu[j + 1]) @ co)
                b_v = 0.5 * float((cv[j] + cv[j + 1]) @ co)
                if lasym:
                    bs_u += float(bsc[j] @ (-xm * si))
                    bs_v += float(bsc[j] @ (xn * si))
                    bu_m += float(bus[j] @ si)
                    bu_p += float(bus[j + 1] @ si)
                    bv_m += float(bvs[j] @ si)
                    bv_p += float(bvs[j + 1] @ si)
                    b_u += 0.5 * float((cus[j] + cus[j + 1]) @ si)
                    b_v += 0.5 * float((cvs[j] + cvs[j + 1]) @ si)
                bu_s = (bu_p - bu_m) / h
                bv_s = (bv_p - bv_m) / h
                t1 = (bs_v - bv_s) * b_v
                t2 = (bu_s - bs_u) * b_u
                r = t1 - t2 - pp
                if worst is None or abs(r) > abs(worst[2]):
                    worst = (t1, t2, r)
        t1, t2, r = worst
        big = max(abs(t1), abs(t2), abs(pp))
        ratio = big / abs(r) if r != 0 else float("inf")
        ratios.append(ratio)
        print(f"{j / (ns - 1):>8.4f} {t1:>15.6e} {t2:>15.6e} {pp:>12.4e} "
              f"{r:>13.6e} {ratio:>11.3g}")
    srt = sorted(ratios)
    mid = (srt[len(srt) // 2] if len(srt) % 2
           else 0.5 * (srt[len(srt) // 2 - 1] + srt[len(srt) // 2]))
    print(f"\ncancellation in the file's own field: {srt[0]:.3g} to "
          f"{srt[-1]:.3g}, median {mid:.3g}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
