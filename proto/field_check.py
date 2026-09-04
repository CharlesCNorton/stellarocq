"""The reconstructed field against the wout's own field arrays.

Physics.v is definitional: that its expression trees are the ideal-MHD
residual is a claim about the encoding, and the kernel checks the arithmetic
rather than the physics. proto/continuum_ref.py writes the same reconstruction
a second time in floating point, which catches a transcription slip, but both
implementations are by the same hand and would agree on a shared
misunderstanding.

This compares against VMEC instead. At a half point the wout stores B^u, B^v
and sqrt(g) as Nyquist Fourier series, computed by the solver from the same
coefficients. The reconstruction has to reproduce them, and where it does not
the disagreement is between this development and VMEC rather than between two
of its own files.

The residual quantities are not stored anywhere, so this reaches the field and
not the force balance. What it rules out is an error in the assembly the
residual is built from, which is most of the encoding.

  python proto/field_check.py wout.nc [--nodes 4,10,16] [--nu 8] [--nv 4]
"""

import argparse
import pathlib
import sys

import netCDF4
import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from continuum_ref import Wout, half_coef  # noqa: E402


def half_block(w, arr, j):
    """One coefficient block at the outer half point, value and derivative."""
    s_a, s_b = w.s_full[j], w.s_full[j + 1]
    s_h = w.s_half[j + 1]
    val, der = [], []
    for k in range(len(w.xm)):
        a, b = half_coef(w.xm[k], arr[j][k], arr[j + 1][k], s_a, s_b, s_h)
        val.append(a), der.append(b)
    return np.array(val), np.array(der)


def reconstructed(w, j, u, vv):
    """B^u, B^v and sqrt(g) at the outer half point of node j.

    VMEC's parity-aware rule for the coefficients, then the ansatz
    sqrt(g) B^u = phip (iota - lambda_v) and sqrt(g) B^v = phip (1 + lambda_u),
    which is what theories/Physics.v builds. A non-stellarator-symmetric
    equilibrium carries a second series in each block, R gaining a sine series
    and Z and lambda a cosine one, with the sign convention of [assemble].
    """
    m, n = w.xm, w.xn
    phip = float(w.phips[1])
    cR, cRs = half_block(w, w.rmnc, j)
    cZ, cZs = half_block(w, w.zmns, j)
    cL = w.lmns[j + 1]
    iota = float(w.iotas[j + 1])
    ang = m * u - n * vv
    co, si = np.cos(ang), np.sin(ang)
    S = lambda cf, kern: float(np.dot(cf, kern))  # noqa: E731

    R, R_s = S(cR, co), S(cRs, co)
    R_u = S(cR, -m * si)
    Z_s, Z_u = S(cZs, si), S(cZ, m * co)
    L_u, L_v = S(cL, m * co), S(cL, -n * co)

    if getattr(w, "lasym", False):
        cRa, cRas = half_block(w, w.rmns, j)
        cZa, cZas = half_block(w, w.zmnc, j)
        cLa = w.lmnc[j + 1]
        R += S(cRa, si)
        R_s += S(cRas, si)
        R_u += S(cRa, m * co)
        Z_s += S(cZas, co)
        Z_u += S(cZa, -m * si)
        L_u += S(cLa, -m * si)
        L_v += S(cLa, n * si)

    sqrtg = R * (R_u * Z_s - R_s * Z_u)
    return (phip * (iota - L_v) / sqrtg, phip * (1.0 + L_u) / sqrtg, sqrtg)


def stored(d, j, u, vv):
    """The same three from the wout's own half-grid Nyquist series."""
    v = d.variables
    mn, nn = np.asarray(v["xm_nyq"][:]), np.asarray(v["xn_nyq"][:])
    ang = mn * u - nn * vv
    co, si = np.cos(ang), np.sin(ang)

    def g(kc, ks):
        x = float(np.dot(np.asarray(v[kc][:])[j + 1], co))
        if ks in v:
            x += float(np.dot(np.asarray(v[ks][:])[j + 1], si))
        return x

    return (g("bsupumnc", "bsupumns"), g("bsupvmnc", "bsupvmns"),
            g("gmnc", "gmns"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--nodes", default=None,
                    help="comma-separated nodes, default a spread of them")
    ap.add_argument("--nu", type=int, default=8)
    ap.add_argument("--nv", type=int, default=4)
    a = ap.parse_args()

    w = Wout(a.wout)
    d = netCDF4.Dataset(a.wout)
    d.set_auto_mask(False)
    if a.nodes:
        nodes = [int(x) for x in a.nodes.split(",")]
    else:
        nodes = [int(x) for x in np.linspace(2, w.ns - 3, 5).astype(int)]
    names = ("B^u", "B^v", "sqrt(g)")
    overall = 0.0
    for j in nodes:
        worst = [0.0, 0.0, 0.0]
        for k in range(a.nu):
            u = 2 * np.pi * k / a.nu
            for l in range(a.nv):
                vv = 2 * np.pi * l / a.nv
                mine = reconstructed(w, j, u, vv)
                theirs = stored(d, j, u, vv)
                for i in range(3):
                    den = max(abs(theirs[i]), 1e-30)
                    worst[i] = max(worst[i], abs(mine[i] - theirs[i]) / den)
        overall = max(overall, max(worst))
        print(f"  node {j:>3}  " + "  ".join(
            f"{nm} {v:.3e}" for nm, v in zip(names, worst, strict=True)))
    d.close()
    print(f"worst relative difference from the wout's own field: {overall:.3e}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
