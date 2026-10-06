"""How far VMEC's half-grid Jacobian lies from the reconstruction's, in floating point.

theories/VmecKernel.v writes VMEC++'s jacobian kernel as tau, the
reconstruction's factor R_u Z_s - R_s Z_u at the same half point as jac_rec,
and proves (vmec_jacobian_difference)

  jac_rec - tau = -1/8 [(ruoo - ruoi)(zoo - zoi) - (zuoo - zuoi)(roo - roi)]
                  -1/8 [(rueo - ruei)(zoo - zoi) - (zueo - zuei)(roo - roi)] / sqrt(s_h),

with e the even-m part and o the odd-m part divided by sqrt(s) of each node
value, i the inner and o the outer node. This evaluates tau and jac_rec from a
stellarator-symmetric wout by those definitions on a grid of angles over one
field period, at every half point whose two nodes lie off the axis, checks
their difference against the right side above, and prints the largest
|jac_rec - tau| / |jac_rec| over the grid, on every such surface and on those
with s_h >= 1/4. The same ratio bounds the relative difference of sqrt(g),
which is r12 times each factor (vmec_sqrtg_difference).

  python gen/jacobian_gap.py wout_a.nc [wout_b.nc ...] [--nu 64 --nv 32]
"""
import argparse
import pathlib

import netCDF4
import numpy as np


def parts(c, xm, cosine, u, v, xn, s):
    """Even-m part, odd-m part over sqrt(s), and their u-derivatives, of one node's
    series on the angle grid: sum c_k cos(m u - n v) or sum c_k sin(m u - n v)."""
    arg = xm[:, None, None] * u[None, :, None] - xn[:, None, None] * v[None, None, :]
    if cosine:
        f, fu = np.cos(arg), -xm[:, None, None] * np.sin(arg)
    else:
        f, fu = np.sin(arg), xm[:, None, None] * np.cos(arg)
    even = (xm % 2 == 0)[:, None, None]
    cc = c[:, None, None]
    e = (cc * f * even).sum(0)
    o = (cc * f * ~even).sum(0) / np.sqrt(s)
    eu = (cc * fu * even).sum(0)
    ou = (cc * fu * ~even).sum(0) / np.sqrt(s)
    return e, o, eu, ou


def gap(path, nu, nv):
    d = netCDF4.Dataset(path)
    d.set_auto_mask(False)
    if int(np.asarray(d.variables["lasym__logical__"][:])) != 0:
        raise SystemExit(f"{path}: written for the stellarator-symmetric layout")
    ns = int(d.variables["ns"][:])
    nfp = int(d.variables["nfp"][:])
    xm = np.asarray(d.variables["xm"][:], dtype=float)
    xn = np.asarray(d.variables["xn"][:], dtype=float)
    rmnc = np.asarray(d.variables["rmnc"][:])
    zmns = np.asarray(d.variables["zmns"][:])
    d.close()
    s = np.linspace(0.0, 1.0, ns)
    u = 2 * np.pi * np.arange(nu) / nu
    v = 2 * np.pi / nfp * np.arange(nv) / nv
    worst, worst_bulk, check = 0.0, 0.0, 0.0
    for j in range(2, ns):
        si, so = s[j - 1], s[j]
        h, sh = so - si, np.sqrt(0.5 * (si + so))
        rei, roi, ruei, ruoi = parts(rmnc[j - 1], xm, True, u, v, xn, si)
        reo, roo, rueo, ruoo = parts(rmnc[j], xm, True, u, v, xn, so)
        zei, zoi, zuei, zuoi = parts(zmns[j - 1], xm, False, u, v, xn, si)
        zeo, zoo, zueo, zuoo = parts(zmns[j], xm, False, u, v, xn, so)
        ru12 = 0.5 * ((ruei + rueo) + sh * (ruoi + ruoo))
        zu12 = 0.5 * ((zuei + zueo) + sh * (zuoi + zuoo))
        rs = ((reo - rei) + sh * (roo - roi)) / h
        zs = ((zeo - zei) + sh * (zoo - zoi)) / h
        tau2 = (ruoo * zoo + ruoi * zoi - zuoo * roo - zuoi * roi
                + (rueo * zoo + ruei * zoi - zueo * roo - zuei * roi) / sh)
        tau = ru12 * zs - rs * zu12 + 0.25 * tau2
        rs_rec = rs + (roi + roo) / (4 * sh)
        zs_rec = zs + (zoi + zoo) / (4 * sh)
        jac = ru12 * zs_rec - rs_rec * zu12
        rhs = (-0.125 * ((ruoo - ruoi) * (zoo - zoi) - (zuoo - zuoi) * (roo - roi))
               - 0.125 * ((rueo - ruei) * (zoo - zoi) - (zueo - zuei) * (roo - roi)) / sh)
        check = max(check, float(np.abs((jac - tau) - rhs).max() / np.abs(jac).max()))
        rel = float((np.abs(jac - tau) / np.abs(jac)).max())
        worst = max(worst, rel)
        if sh * sh >= 0.25:
            worst_bulk = max(worst_bulk, rel)
    return ns, worst, worst_bulk, check


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout", nargs="+")
    ap.add_argument("--nu", type=int, default=64)
    ap.add_argument("--nv", type=int, default=32)
    a = ap.parse_args()
    for w in a.wout:
        ns, worst, bulk, check = gap(w, a.nu, a.nv)
        print(f"{pathlib.Path(w).name}: ns {ns}, max |jac_rec - tau| / |jac_rec| "
              f"{worst:.3e} off the axis, {bulk:.3e} at s_h >= 1/4; "
              f"identity residual {check:.1e}")


if __name__ == "__main__":
    main()
