"""NESTOR's and BIEST's vacuum field on a free boundary, for gen/free_boundary.py.

`run` solves the CTH-like free-boundary case of the VMEC++ test data at a radial
resolution with `return_vacuum_field` set and keeps the wout and NESTOR's
boundary field (VMEC++'s `threed1_free_boundary`).

`answers` computes the second vacuum field. BIEST's virtual casing
(the `virtual_casing` package) recovers from the plasma-side field B_in the
field B_ext of the currents outside the boundary; the field of the plasma
currents just outside is then B_in - B_ext, and the full vacuum field there is

    B_vac = B_coil + B_in - B_ext,

with B_coil the coil field VMEC++ itself reads, the mgrid interpolated by the
same four-node Lagrange rule. Both pressures B_vac^2/2 are written on NESTOR's
grid, extended from the half poloidal range by stellarator symmetry (B_R odd,
B_phi and B_Z even), beside VMEC++'s edge pressure.

  python gen/vacuum_answers.py run DIR --ns 25,49,97
  python gen/vacuum_answers.py answers DIR --tags ns25,ns49,ns97
"""

import argparse
import pathlib
import time

import numpy as np


def cth_input(ns, mpol=None, ntor=None):
    import vmecpp

    td = pathlib.Path(vmecpp.__file__).parent / "cpp" / "vmecpp" / "test_data"
    base = vmecpp.VmecInput.from_file(td / "cth_like_free_bdy.json")
    update = {"mgrid_file": str(td / pathlib.Path(base.mgrid_file).name),
              "return_vacuum_field": True}
    steps = [x for x in (9, 17, 25, 33, 49, 65, 97, 129, 193) if x < ns] + [ns]
    update.update(ns_array=np.array(steps), ftol_array=np.full(len(steps), 1e-14),
                  niter_array=np.full(len(steps), 40000))
    return base.model_copy(update=update, deep=True), td


def cmd_run(a):
    import vmecpp

    out_dir = pathlib.Path(a.dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    for ns in (int(x) for x in a.ns.split(",")):
        vi, _ = cth_input(ns)
        t0 = time.time()
        out = vmecpp.run(vi, verbose=False)
        fb = out.threed1_free_boundary
        jmp = np.asarray(fb.bsqmhdf) - np.asarray(fb.bsqvacf)
        print(f"ns{ns}: fsq {out.wout.fsqr:.1e} {out.wout.fsqz:.1e} {out.wout.fsql:.1e}, "
              f"max |jump| {np.abs(jmp).max():.4e}, {time.time() - t0:.0f} s", flush=True)
        out.wout.save(str(out_dir / f"wout_cth_ns{ns}.nc"))
        np.savez(out_dir / f"fb_cth_ns{ns}.npz", **{k: np.asarray(getattr(fb, k)) for k in
                 ("rb", "zb", "phib", "bsqmhdf", "bsqvacf", "brv", "bphiv", "bzv",
                  "bredge", "bpedge", "bzedge")})


class MGrid:
    """The coil field of an mgrid file, weighted by the circuit currents."""

    def __init__(self, path, currents):
        from scipy.io import netcdf_file

        d = netcdf_file(path, "r", mmap=False)
        v = d.variables
        self.ir, self.jz = int(v["ir"].data), int(v["jz"].data)
        self.rmin, self.rmax = float(v["rmin"].data), float(v["rmax"].data)
        self.zmin, self.zmax = float(v["zmin"].data), float(v["zmax"].data)
        self.dr = (self.rmax - self.rmin) / (self.ir - 1)
        self.dz = (self.zmax - self.zmin) / (self.jz - 1)
        n = int(v["nextcur"].data)
        self.b = [sum(currents[i] * np.array(v[f"{c}_{i + 1:03d}"].data) for i in range(n))
                  for c in ("br", "bp", "bz")]

    @staticmethod
    def _weights(t):
        return np.array([-(t - 1) * (t - 2) * (t - 3) / 6, t * (t - 2) * (t - 3) / 2,
                         -t * (t - 1) * (t - 3) / 2, t * (t - 1) * (t - 2) / 6])

    def at(self, k, r, z):
        """VMEC++'s four-node Lagrange interpolation on plane k."""
        ri = (r - self.rmin) / self.dr
        zi = (z - self.zmin) / self.dz
        r0 = min(max(int(np.floor(ri)) - 1, 0), self.ir - 4)
        z0 = min(max(int(np.floor(zi)) - 1, 0), self.jz - 4)
        wr, wz = self._weights(ri - r0), self._weights(zi - z0)
        return np.array([wz @ b[k, z0:z0 + 4, r0:r0 + 4] @ wr for b in self.b])


def surface(wout, theta, phi):
    """Boundary position, tangents and plasma-side field, cylindrical, on a
    grid [phi, theta]; the field is the half-grid B^u, B^v extrapolated to
    the boundary and carried by the boundary's own tangents."""
    xm, xn = wout.xm.astype(float), wout.xn.astype(float)
    xmn, xnn = wout.xm_nyq.astype(float), wout.xn_nyq.astype(float)
    rc, zs = wout.rmnc[:, -1], wout.zmns[:, -1]
    bu_c = 1.5 * wout.bsupumnc[:, -1] - 0.5 * wout.bsupumnc[:, -2]
    bv_c = 1.5 * wout.bsupvmnc[:, -1] - 0.5 * wout.bsupvmnc[:, -2]
    T, P = np.meshgrid(theta, phi)
    ang = xm[:, None, None] * T[None] - xn[:, None, None] * P[None]
    c, s = np.cos(ang), np.sin(ang)
    R = np.tensordot(rc, c, 1)
    Ru, Rv = -np.tensordot(rc * xm, s, 1), np.tensordot(rc * xn, s, 1)
    Z = np.tensordot(zs, s, 1)
    Zu, Zv = np.tensordot(zs * xm, c, 1), -np.tensordot(zs * xn, c, 1)
    cn = np.cos(xmn[:, None, None] * T[None] - xnn[:, None, None] * P[None])
    Bu, Bv = np.tensordot(bu_c, cn, 1), np.tensordot(bv_c, cn, 1)
    return {"R": R, "Z": Z, "P": P,
            "BR": Bu * Ru + Bv * Rv, "BP": Bv * R, "BZ": Bu * Zu + Bv * Zv}


def cartesian(sf):
    c, s = np.cos(sf["P"]), np.sin(sf["P"])
    X = np.stack([sf["R"] * c, sf["R"] * s, sf["Z"]])
    B = np.stack([sf["BR"] * c - sf["BP"] * s, sf["BR"] * s + sf["BP"] * c, sf["BZ"]])
    return X, B


def external_field(wout, nfp, src, trg, digits):
    """BIEST's virtual casing: the external-current field on the target grid,
    cylindrical, from the boundary and B_in on a full-period source grid."""
    import virtual_casing as vcm

    nt, npol = src
    th = 2 * np.pi * np.arange(npol) / npol
    ph = 2 * np.pi * np.arange(nt) / (nfp * nt)
    X, B = cartesian(surface(wout, th, ph))
    vc = vcm.VirtualCasing()
    vc.setup(digits, nfp, False, nt, npol, X.reshape(-1).tolist(), nt, npol, trg[0], trg[1])
    return np.array(vc.compute_external_B(B.reshape(-1).tolist())).reshape(3, trg[0], trg[1])


def full_theta(a, nth, odd=False):
    """A (nzeta, nth/2 + 1) stellarator-symmetric array on the whole
    poloidal range: the value at (-theta, -phi), negated when odd."""
    nz, nh = a.shape
    out = np.zeros((nz, nth))
    out[:, :nh] = a
    for l in range(nh, nth):
        for k in range(nz):
            x = a[(nz - k) % nz, nth - l]
            out[k, l] = -x if odd else x
    return out


def cmd_answers(a):
    import vmecpp

    d = pathlib.Path(a.dir)
    vi, td = cth_input(25)
    mg = MGrid(td / pathlib.Path(vi.mgrid_file).name, np.asarray(vi.extcur, dtype=float))
    for tag in a.tags.split(","):
        wout = vmecpp.VmecWOut.from_wout_file(d / f"wout_cth_{tag}.nc")
        fb = np.load(d / f"fb_cth_{tag}.npz")
        nzeta, nh = fb["bsqvacf"].shape
        nth = 2 * (nh - 1)
        nfp = int(wout.nfp)
        th = 2 * np.pi * np.arange(nth) / nth
        ph = 2 * np.pi * np.arange(nzeta) / (nfp * nzeta)
        sf = surface(wout, th, ph)
        b_in = np.stack([sf["BR"], sf["BP"], sf["BZ"]])
        b_coil = np.zeros((3, nzeta, nth))
        for k in range(nzeta):
            for l in range(nth):
                b_coil[:, k, l] = mg.at(k, sf["R"][k, l], sf["Z"][k, l])
        ext = [external_field(wout, nfp, (s, s), (nzeta, nth), dg)
               for s, dg in ((48, 8), (96, 10))]
        c, s = np.cos(sf["P"]), np.sin(sf["P"])
        b_ext = np.stack([ext[1][0] * c + ext[1][1] * s, -ext[1][0] * s + ext[1][1] * c,
                          ext[1][2]])
        b_vac = b_coil + b_in - b_ext
        pb = 0.5 * (b_vac**2).sum(0)
        pn = full_theta(fb["bsqvacf"], nth)
        tp = full_theta(fb["bsqmhdf"], nth)
        print(f"{tag}: virtual casing change with resolution {np.abs(ext[0] - ext[1]).max():.1e}; "
              f"|B_coil - B_ext| {np.abs(b_coil - b_ext).max():.2e}; "
              f"pressures differ by at most {np.abs(pn - pb).max():.3e}; "
              f"max |jump| NESTOR {np.abs(tp - pn).max():.4e} BIEST {np.abs(tp - pb).max():.4e}",
              flush=True)
        np.savez(d / f"vac_cth_{tag}.npz", pn=pn, pb=pb, tp=tp, b_in=b_in, b_coil=b_coil,
                 b_ext=b_ext, theta=th, phi=ph)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("dir")
    r.add_argument("--ns", default="25,49,97")
    r.set_defaults(fn=cmd_run)
    v = sub.add_parser("answers")
    v.add_argument("dir")
    v.add_argument("--tags", default="ns25,ns49,ns97")
    v.set_defaults(fn=cmd_answers)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    main()
