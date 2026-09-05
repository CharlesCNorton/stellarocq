"""The two sides of the free-boundary jump, read at the certified boundary.

free_boundary_balanced of theories/Hypotheses.v is continuity of the total
pressure across the interface, p + B^2/2 against B_vac^2/2 in mu0-scaled units.
The plasma side a covering reaches through --edge; the vacuum side is the coil
field the mgrid tabulates plus the field of the plasma's own surface current,
which VMEC's Nestor computes and the wout does not store.

This reads the coil half: the mgrid coil field per group on a cylindrical grid,
scaled by the wout's currents, trilinearly interpolated at each boundary point,
against the plasma side's p + B^2/2. The gap is the plasma current's own
contribution, which nothing here produces, so it measures what is missing
rather than the jump.

The plasma side is the wout's own |B| series extrapolated to the boundary and
presf there, in floating point: a reading of the data, not a certificate.

  python proto/vacuum_jump.py wout_free.nc mgrid.nc [--nu 64] [--nv 16]
"""

import argparse
import sys

import netCDF4
import numpy as np

MU0 = 4e-7 * np.pi


class Mgrid:
    """The coil field of an mgrid file, scaled by the wout's currents."""

    def __init__(self, path, extcur):
        d = netCDF4.Dataset(path)
        d.set_auto_mask(False)
        v = d.variables
        self.nr, self.nz, self.kp = int(v["ir"][:]), int(v["jz"][:]), int(v["kp"][:])
        self.nfp = int(v["nfp"][:])
        self.rmin, self.rmax = float(v["rmin"][:]), float(v["rmax"][:])
        self.zmin, self.zmax = float(v["zmin"][:]), float(v["zmax"][:])
        n = int(v["nextcur"][:])
        mode = v["mgrid_mode"][:].tobytes().decode().strip(chr(0)).strip()
        if len(extcur) < n:
            raise SystemExit(f"the wout carries {len(extcur)} currents, the "
                             f"mgrid {n} coil groups")
        # arrays are (phi, z, r); in raw mode each group is per unit current
        self.br = sum(extcur[g] * np.asarray(v[f"br_{g + 1:03d}"][:])
                      for g in range(n))
        self.bp = sum(extcur[g] * np.asarray(v[f"bp_{g + 1:03d}"][:])
                      for g in range(n))
        self.bz = sum(extcur[g] * np.asarray(v[f"bz_{g + 1:03d}"][:])
                      for g in range(n))
        self.mode = mode
        d.close()

    def field(self, r, phi, z):
        """Trilinear interpolation, periodic in the toroidal angle."""
        fr = (r - self.rmin) / (self.rmax - self.rmin) * (self.nr - 1)
        fz = (z - self.zmin) / (self.zmax - self.zmin) * (self.nz - 1)
        period = 2 * np.pi / self.nfp
        fp = (phi % period) / period * self.kp
        if not (0 <= fr <= self.nr - 1 and 0 <= fz <= self.nz - 1):
            raise SystemExit(f"the boundary point (R, Z) = ({r:.4f}, {z:.4f}) "
                             f"lies outside the mgrid box")
        i0, j0, k0 = int(np.floor(fr)), int(np.floor(fz)), int(np.floor(fp))
        i0, j0 = min(i0, self.nr - 2), min(j0, self.nz - 2)
        tr, tz, tp = fr - i0, fz - j0, fp - k0
        k1 = (k0 + 1) % self.kp
        out = []
        for arr in (self.br, self.bp, self.bz):
            c = 0.0
            for dk, wk in ((k0, 1 - tp), (k1, tp)):
                for dj, wj in ((j0, 1 - tz), (j0 + 1, tz)):
                    for di, wi in ((i0, 1 - tr), (i0 + 1, tr)):
                        c += wk * wj * wi * arr[dk % self.kp, dj, di]
            out.append(c)
        return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("mgrid")
    ap.add_argument("--nu", type=int, default=64)
    ap.add_argument("--nv", type=int, default=16)
    a = ap.parse_args()

    d = netCDF4.Dataset(a.wout)
    d.set_auto_mask(False)
    v = d.variables
    g = lambda k: np.asarray(v[k][:], dtype=float)  # noqa: E731
    ns = int(v["ns"][:])
    nfp = int(v["nfp"][:])
    xm, xn = g("xm").astype(int), g("xn").astype(int)
    xmn, xnn = g("xm_nyq"), g("xn_nyq")
    rmnc, zmns = g("rmnc"), g("zmns")
    bmnc = g("bmnc")
    presf = g("presf")
    extcur = g("extcur")
    lasym = "lasym__logical__" in v and bool(int(v["lasym__logical__"][:]))
    if lasym:
        rmns, zmnc, bmns = g("rmns"), g("zmnc"), g("bmns")
    lfreeb = "lfreeb__logical__" in v and bool(int(v["lfreeb__logical__"][:]))
    d.close()
    if not lfreeb:
        print("this wout was run with the boundary fixed, so the condition "
              "is not one it was asked to satisfy")

    mg = Mgrid(a.mgrid, extcur)
    # |B| at the boundary, extrapolated from the last two half surfaces
    b_edge = 1.5 * bmnc[ns - 1] - 0.5 * bmnc[ns - 2]
    if lasym:
        bs_edge = 1.5 * bmns[ns - 1] - 0.5 * bmns[ns - 2]
    p_edge = float(presf[-1])

    print(f"{a.wout} against {a.mgrid}: the total pressure on the plasma side "
          f"of the boundary\nagainst the coil field's B^2/2 on the other, "
          f"over {a.nu} by {a.nv} points")
    print(f"currents {extcur.tolist()}, mgrid mode {mg.mode!r}, "
          f"p at the edge {p_edge:.4e} Pa\n")
    worst, mean, n = 0.0, 0.0, 0
    ratios = []
    for k in range(a.nu):
        u = 2 * np.pi * k / a.nu
        for l in range(a.nv):
            vv = 2 * np.pi * l / (nfp * a.nv)
            ang = xm * u - xn * vv
            co, si = np.cos(ang), np.sin(ang)
            R = float(rmnc[-1] @ co)
            Z = float(zmns[-1] @ si)
            angn = xmn * u - xnn * vv
            B = float(b_edge @ np.cos(angn))
            if lasym:
                R += float(rmns[-1] @ si)
                Z += float(zmnc[-1] @ co)
                B += float(bs_edge @ np.sin(angn))
            br, bp, bz = mg.field(R, vv, Z)
            bvac2 = br * br + bp * bp + bz * bz
            plasma = MU0 * p_edge + 0.5 * B * B
            vac = 0.5 * bvac2
            gap = plasma - vac
            ratios.append(vac / plasma if plasma else float("inf"))
            worst = max(worst, abs(gap) / max(plasma, 1e-30))
            mean += gap
            n += 1
    ratios = np.array(ratios)
    print(f"  B_coil^2 / (2 mu0 p + B^2) over the boundary: "
          f"{ratios.min():.4f} to {ratios.max():.4f}, mean {ratios.mean():.4f}")
    print(f"  worst relative gap {worst:.3e}, mean gap {mean / n:+.4e} "
          f"(mu0-scaled)")
    print("\nThe gap is the plasma's own contribution to the vacuum field at "
          "its boundary,\nwhich VMEC's Nestor computes from the surface "
          "current and the wout does not\nstore. What is read here is the "
          "coil field alone, so the jump is not expected\nto close and this "
          "is the size of what would close it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
