"""Float reference for the residual at a free radius.

theories/Physics.v builds the continuum force residual of the reconstruction
as expression trees, and the checker encloses it in interval arithmetic. This
computes the same quantity in ordinary floating point, written from the
reconstruction rule rather than transcribed from the expression builders, so
that a mistake in encoding the physics into `expr` shows up as a disagreement
rather than as a certificate about the wrong object.

The rule, which is the one theories/Physics.v states:

  At a half point between full-grid nodes a and b, VMEC's parity-aware rule
  gives every coefficient a value and a radial derivative,

    even m:  c = (ya + yb)/2                  c' = (yb - ya)/(sb - sa)
    odd  m:  q = y/sqrt(s) interpolated,      c  = sqrt(s_h) (qa + qb)/2
             c' = sqrt(s_h)(qb - qa)/(sb - sa) + c/(2 s_h)

  Between the two half points bracketing a node, R and Z follow the cubic
  Hermite through those four numbers, so both the value and the radial
  derivative are VMEC's at each end and a second radial derivative exists.
  Lambda and iota, which VMEC gives on the half grid with no derivative, are
  linear in s under the same parity rule.

  The field and the residual are then the usual ones,

    sqrtg = R (R_u Z_s - R_s Z_u)
    B^u = phip (iota - lambda_v)/sqrtg      B^v = phip (1 + lambda_u)/sqrtg
    B_i = g_iu B^u + g_iv B^v
    r_s = (d_v B_s - d_s B_v) B^v - (d_s B_u - d_u B_s) B^u - mu0 dp/ds
    r_u = -(d_u B_v - d_v B_u) B^v          r_v = (d_u B_v - d_v B_u) B^u

`--half-grid` computes the other residual instead: the one a point
certificate carries, at a full-grid node, with the radial derivatives VMEC's
own centred differences of the two half points rather than derivatives of an
interpolant. It is written here from the same rule and shares no code with
gen/make_cert.py, so the two disagreeing means one of them has the physics
wrong.

The pressure comes from proto/pressure_ref.py, which writes every
parameterization VMEC++ admits from its definition, and which recovers the
scale VMEC applied from the file's own half-grid pressure, since PRES_SCALE is
not written to a wout.

Usage:  python proto/continuum_ref.py wout.nc --node 22 --nu 8
        python proto/continuum_ref.py wout.nc --node 22 --nu 8 --half-grid
"""

import argparse
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from pressure_ref import Profile  # noqa: E402

MU0 = 4e-7 * np.pi


class Wout:
    """The wout fields the reconstruction needs."""

    def __init__(self, path):
        import netCDF4
        d = netCDF4.Dataset(path)
        d.set_auto_mask(False)
        v = d.variables

        def g(k):
            return np.asarray(v[k][:], dtype=float)

        self.ns = int(v["ns"][:])
        self.xm = g("xm").astype(int)
        self.xn = g("xn").astype(int)
        self.rmnc, self.zmns, self.lmns = g("rmnc"), g("zmns"), g("lmns")
        self.iotas, self.phips, self.am = g("iotas"), g("phips"), g("am")
        self.lasym = ("lasym__logical__" in v
                      and bool(int(v["lasym__logical__"][:])))
        if self.lasym:
            self.rmns, self.zmnc, self.lmnc = g("rmns"), g("zmnc"), g("lmnc")
        self.pmass_type = (
            v["pmass_type"][:].tobytes().decode().replace(chr(0), "").strip()
            if "pmass_type" in v else "")
        self.pres_half = g("pres")
        self.aux_s = g("am_aux_s") if "am_aux_s" in v else None
        self.aux_f = g("am_aux_f") if "am_aux_f" in v else None
        self.h = 1.0 / (self.ns - 1)
        self.s_full = np.arange(self.ns) * self.h
        self.s_half = (np.arange(self.ns) - 0.5) * self.h
        d.close()
        self.profile = Profile.from_wout(self)


def pressure_gradient(w, s):
    """dp/ds of the wout's profile, from proto/pressure_ref.py.

    That module writes every parameterization from its definition rather than
    from the expression builders of theories/Physics.v or the float pass of
    gen/make_cert.py, and it carries the scale VMEC applied, recovered from the
    file's own half-grid pressure.
    """
    return w.profile.derivative(s)


def half_coef(m, ya, yb, s_a, s_b, s_h):
    """Value and radial derivative of one coefficient at a half point."""
    odd = (m % 2) == 1
    if not odd:
        return 0.5 * (ya + yb), (yb - ya) / (s_b - s_a)
    qa, qb = ya / np.sqrt(s_a), yb / np.sqrt(s_b)
    c = np.sqrt(s_h) * 0.5 * (qa + qb)
    cs = np.sqrt(s_h) * (qb - qa) / (s_b - s_a) + c / (2.0 * s_h)
    return c, cs


def hermite(ya, da, yb, db, s_lo, s_hi, s):
    """Value and the two radial derivatives of the cubic Hermite."""
    H = s_hi - s_lo
    t = (s - s_lo) / H
    sec = (yb - ya) / H
    al, be = da - sec, db - sec
    h10 = t**3 - 2 * t**2 + t
    h11 = t**3 - t**2
    g10 = 3 * t**2 - 4 * t + 1
    g11 = 3 * t**2 - 2 * t
    c = ya + t * (yb - ya) + H * (h10 * al + h11 * be)
    cs = sec + g10 * al + g11 * be
    css = ((6 * t - 4) * al + (6 * t - 2) * be) / H
    return c, cs, css


def linear_parity(m, ya, yb, s_lo, s_hi, s):
    """Lambda's rule: linear in s under the same parity rescaling."""
    H = s_hi - s_lo
    w = (s - s_lo) / H
    if (m % 2) == 0:
        return ya + w * (yb - ya), (yb - ya) / H
    qa, qb = ya / np.sqrt(s_lo), yb / np.sqrt(s_hi)
    q = qa + w * (qb - qa)
    c = np.sqrt(s) * q
    cs = np.sqrt(s) * (qb - qa) / H + c / (2.0 * s)
    return c, cs


def residual_at(w, j, s, u, vv):
    """The three components at (s, u, v), with s inside node j's interval."""
    m, n = w.xm, w.xn
    s_a, s_j, s_b = w.s_full[j - 1], w.s_full[j], w.s_full[j + 1]
    s_hm, s_hp = w.s_half[j], w.s_half[j + 1]
    phip = float(w.phips[1])

    def block(coefs):
        """Value and two radial derivatives of every mode of one block."""
        c, cs, css = [], [], []
        for k in range(len(m)):
            ym, dm = half_coef(m[k], coefs[j - 1][k], coefs[j][k], s_a, s_j, s_hm)
            yp, dp = half_coef(m[k], coefs[j][k], coefs[j + 1][k], s_j, s_b, s_hp)
            a, b, cc = hermite(ym, dm, yp, dp, s_hm, s_hp, s)
            c.append(a), cs.append(b), css.append(cc)
        return np.array(c), np.array(cs), np.array(css)

    cR, cRs, cRss = block(w.rmnc)
    cZ, cZs, cZss = block(w.zmns)
    cL, cLs = np.zeros(len(m)), np.zeros(len(m))
    for k in range(len(m)):
        cL[k], cLs[k] = linear_parity(m[k], w.lmns[j][k], w.lmns[j + 1][k],
                                      s_hm, s_hp, s)
    wgt = (s - s_hm) / (s_hp - s_hm)
    iota = w.iotas[j] + wgt * (w.iotas[j + 1] - w.iotas[j])
    iotap = (w.iotas[j + 1] - w.iotas[j]) / (s_hp - s_hm)

    ang = m * u - n * vv
    co, si = np.cos(ang), np.sin(ang)
    S = lambda cf, kern: float(np.dot(cf, kern))  # noqa: E731

    R, R_s, R_ss = S(cR, co), S(cRs, co), S(cRss, co)
    R_u, R_v = S(cR, -m * si), S(cR, n * si)
    R_su, R_sv = S(cRs, -m * si), S(cRs, n * si)
    R_uu, R_uv, R_vv = S(cR, -m * m * co), S(cR, m * n * co), S(cR, -n * n * co)
    Z_s, Z_ss = S(cZs, si), S(cZss, si)
    Z_u, Z_v = S(cZ, m * co), S(cZ, -n * co)
    Z_su, Z_sv = S(cZs, m * co), S(cZs, -n * co)
    Z_uu, Z_uv, Z_vv = S(cZ, -m * m * si), S(cZ, m * n * si), S(cZ, -n * n * si)
    L_u, L_v = S(cL, m * co), S(cL, -n * co)
    L_su, L_sv = S(cLs, m * co), S(cLs, -n * co)
    L_uu, L_uv, L_vv = S(cL, -m * m * si), S(cL, m * n * si), S(cL, -n * n * si)

    tau = R_u * Z_s - R_s * Z_u
    sqrtg = R * tau
    tau_s = R_su * Z_s + R_u * Z_ss - R_ss * Z_u - R_s * Z_su
    tau_u = R_uu * Z_s + R_u * Z_su - R_su * Z_u - R_s * Z_uu
    tau_v = R_uv * Z_s + R_u * Z_sv - R_sv * Z_u - R_s * Z_uv
    g_s = R_s * tau + R * tau_s
    g_u = R_u * tau + R * tau_u
    g_v = R_v * tau + R * tau_v
    guu = R_u**2 + Z_u**2
    guv = R_u * R_v + Z_u * Z_v
    gvv = R_v**2 + Z_v**2 + R**2
    gsu = R_s * R_u + Z_s * Z_u
    gsv = R_s * R_v + Z_s * Z_v
    guu_s = 2 * (R_u * R_su + Z_u * Z_su)
    guv_s = R_su * R_v + R_u * R_sv + Z_su * Z_v + Z_u * Z_sv
    gvv_s = 2 * (R_v * R_sv + Z_v * Z_sv + R * R_s)
    gsu_u = R_su * R_u + R_s * R_uu + Z_su * Z_u + Z_s * Z_uu
    gsu_v = R_sv * R_u + R_s * R_uv + Z_sv * Z_u + Z_s * Z_uv
    gsv_u = R_su * R_v + R_s * R_uv + Z_su * Z_v + Z_s * Z_uv
    gsv_v = R_sv * R_v + R_s * R_vv + Z_sv * Z_v + Z_s * Z_vv
    guu_v = 2 * (R_u * R_uv + Z_u * Z_uv)
    guv_u = R_uu * R_v + R_u * R_uv + Z_uu * Z_v + Z_u * Z_uv
    guv_v = R_uv * R_v + R_u * R_vv + Z_uv * Z_v + Z_u * Z_vv
    gvv_u = 2 * (R_v * R_uv + Z_v * Z_uv + R * R_u)

    bu, bv = iota - L_v, 1.0 + L_u
    Bu, Bv = phip * bu / sqrtg, phip * bv / sqrtg
    g2 = sqrtg**2
    dB = lambda num, gd: phip * (num * sqrtg - gd) / g2  # noqa: E731
    Bu_s = dB(iotap - L_sv, bu * g_s)
    Bv_s = dB(L_su, bv * g_s)
    Bu_u, Bv_u = dB(-L_uv, bu * g_u), dB(L_uu, bv * g_u)
    Bu_v, Bv_v = dB(-L_vv, bu * g_v), dB(L_uv, bv * g_v)

    def dcov(gu, gud, gv, gvd, bud, bvd):
        return gud * Bu + gu * bud + gvd * Bv + gv * bvd

    B_u_s = dcov(guu, guu_s, guv, guv_s, Bu_s, Bv_s)
    B_v_s = dcov(guv, guv_s, gvv, gvv_s, Bu_s, Bv_s)
    B_s_u = dcov(gsu, gsu_u, gsv, gsv_u, Bu_u, Bv_u)
    B_s_v = dcov(gsu, gsu_v, gsv, gsv_v, Bu_v, Bv_v)
    B_u_v = dcov(guu, guu_v, guv, guv_v, Bu_v, Bv_v)
    B_v_u = dcov(guv, guv_u, gvv, gvv_u, Bu_u, Bv_u)
    mu0Js = B_v_u - B_u_v

    pp = pressure_gradient(w, s)
    t1 = (B_s_v - B_v_s) * Bv
    t2 = (B_u_s - B_s_u) * Bu
    t3 = MU0 * pp
    r_s = t1 - t2 - t3
    return r_s, -mu0Js * Bv, mu0Js * Bu, sqrtg, g_s, (t1, t2, t3)


def half_point_fields(w, j_in, j_out, row_l, u, vv):
    """Every field quantity at one half point, by VMEC's parity rule.

    This is the reconstruction a point certificate carries. Nothing is
    interpolated off the grid: the half-point coefficients are the parity-aware
    averages and their radial derivatives the matching difference quotients.
    """
    m, n = w.xm, w.xn
    s_a, s_b = w.s_full[j_in], w.s_full[j_out]
    s_h = w.s_half[row_l]
    phip = float(w.phips[1])
    cR, cRs, cZ, cZs = [], [], [], []
    for k in range(len(m)):
        a, b = half_coef(m[k], w.rmnc[j_in][k], w.rmnc[j_out][k], s_a, s_b, s_h)
        cR.append(a), cRs.append(b)
        a, b = half_coef(m[k], w.zmns[j_in][k], w.zmns[j_out][k], s_a, s_b, s_h)
        cZ.append(a), cZs.append(b)
    cR, cRs = np.array(cR), np.array(cRs)
    cZ, cZs = np.array(cZ), np.array(cZs)
    cL = w.lmns[row_l]
    iota = float(w.iotas[row_l])

    ang = m * u - n * vv
    co, si = np.cos(ang), np.sin(ang)
    S = lambda cf, kern: float(np.dot(cf, kern))  # noqa: E731

    R, R_s = S(cR, co), S(cRs, co)
    R_u, R_v = S(cR, -m * si), S(cR, n * si)
    R_su, R_sv = S(cRs, -m * si), S(cRs, n * si)
    R_uu, R_uv, R_vv = S(cR, -m * m * co), S(cR, m * n * co), S(cR, -n * n * co)
    Z_s = S(cZs, si)
    Z_u, Z_v = S(cZ, m * co), S(cZ, -n * co)
    Z_su, Z_sv = S(cZs, m * co), S(cZs, -n * co)
    Z_uu, Z_uv, Z_vv = S(cZ, -m * m * si), S(cZ, m * n * si), S(cZ, -n * n * si)
    L_u, L_v = S(cL, m * co), S(cL, -n * co)
    L_uu, L_uv, L_vv = S(cL, -m * m * si), S(cL, m * n * si), S(cL, -n * n * si)

    tau = R_u * Z_s - R_s * Z_u
    sqrtg = R * tau
    tau_u = R_uu * Z_s + R_u * Z_su - R_su * Z_u - R_s * Z_uu
    tau_v = R_uv * Z_s + R_u * Z_sv - R_sv * Z_u - R_s * Z_uv
    g_u = R_u * tau + R * tau_u
    g_v = R_v * tau + R * tau_v
    guu = R_u**2 + Z_u**2
    guv = R_u * R_v + Z_u * Z_v
    gvv = R_v**2 + Z_v**2 + R**2
    gsu = R_s * R_u + Z_s * Z_u
    gsv = R_s * R_v + Z_s * Z_v
    gsu_u = R_su * R_u + R_s * R_uu + Z_su * Z_u + Z_s * Z_uu
    gsu_v = R_sv * R_u + R_s * R_uv + Z_sv * Z_u + Z_s * Z_uv
    gsv_u = R_su * R_v + R_s * R_uv + Z_su * Z_v + Z_s * Z_uv
    gsv_v = R_sv * R_v + R_s * R_vv + Z_sv * Z_v + Z_s * Z_vv
    guu_v = 2 * (R_u * R_uv + Z_u * Z_uv)
    guv_u = R_uu * R_v + R_u * R_uv + Z_uu * Z_v + Z_u * Z_uv
    guv_v = R_uv * R_v + R_u * R_vv + Z_uv * Z_v + Z_u * Z_vv
    gvv_u = 2 * (R_v * R_uv + Z_v * Z_uv + R * R_u)

    bu, bv = iota - L_v, 1.0 + L_u
    Bu, Bv = phip * bu / sqrtg, phip * bv / sqrtg
    g2 = sqrtg**2
    dB = lambda num, gd: phip * (num * sqrtg - gd) / g2  # noqa: E731
    Bu_u, Bv_u = dB(-L_uv, bu * g_u), dB(L_uu, bv * g_u)
    Bu_v, Bv_v = dB(-L_vv, bu * g_v), dB(L_uv, bv * g_v)

    def dcov(gu, gud, gv, gvd, bud, bvd):
        return gud * Bu + gu * bud + gvd * Bv + gv * bvd

    B_u = guu * Bu + guv * Bv
    B_v = guv * Bu + gvv * Bv
    B_s_u = dcov(gsu, gsu_u, gsv, gsv_u, Bu_u, Bv_u)
    B_s_v = dcov(gsu, gsu_v, gsv, gsv_v, Bu_v, Bv_v)
    B_u_v = dcov(guu, guu_v, guv, guv_v, Bu_v, Bv_v)
    B_v_u = dcov(guv, guv_u, gvv, gvv_u, Bu_u, Bv_u)
    return {"Bu": Bu, "Bv": Bv, "B_u": B_u, "B_v": B_v,
            "B_s_u": B_s_u, "B_s_v": B_s_v, "mu0Js": B_v_u - B_u_v}


def residual_half_grid(w, j, u, vv):
    """The three components a point certificate claims, at node j."""
    qm = half_point_fields(w, j - 1, j, j, u, vv)
    qp = half_point_fields(w, j, j + 1, j + 1, u, vv)
    h = w.s_half[j + 1] - w.s_half[j]
    avg = lambda k: 0.5 * (qm[k] + qp[k])  # noqa: E731
    dif = lambda k: (qp[k] - qm[k]) / h  # noqa: E731
    s = float(w.s_full[j])
    pp = pressure_gradient(w, s)
    t1 = (avg("B_s_v") - dif("B_v")) * avg("Bv")
    t2 = (dif("B_u") - avg("B_s_u")) * avg("Bu")
    t3 = MU0 * pp
    r_s = t1 - t2 - t3
    return r_s, -qp["mu0Js"] * qp["Bv"], qp["mu0Js"] * qp["Bu"], (t1, t2, t3)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--node", type=int, required=True)
    ap.add_argument("--nu", type=int, default=8)
    ap.add_argument("--v", type=float, default=0.0)
    ap.add_argument("--at", type=float, default=None,
                    help="the radius, default the node itself")
    ap.add_argument("--half-grid", action="store_true",
                    help="the residual of a point certificate instead")
    ap.add_argument("--cells", action="store_true",
                    help="sample at the centres of the cells a covering of "
                    "this many lays out, (2k+1) pi / nu, rather than at "
                    "2 pi k / nu, so the two can be read against each other")
    ap.add_argument("--u", type=float, default=None,
                    help="one poloidal angle in radians instead of a sweep, "
                    "which with --at reads the reconstruction at the centre "
                    "of one cell of a volume covering")
    a = ap.parse_args()
    w = Wout(a.wout)
    j = a.node
    if a.half_grid:
        print(f"ns={w.ns} node={j} s={float(w.s_full[j]):.9f} half grid")
        worst = 0.0
        per = [0.0, 0.0, 0.0]
        best = None
        for k in range(a.nu):
            u = ((2 * k + 1) * np.pi / a.nu if a.cells
                 else 2 * np.pi * k / a.nu)
            rs, ru, rv, terms = residual_half_grid(w, j, u, a.v)
            worst = max(worst, abs(rs), abs(ru), abs(rv))
            per = [max(per[0], abs(rs)), max(per[1], abs(ru)),
                   max(per[2], abs(rv))]
            if best is None or abs(rs) > abs(best[0]):
                best = (rs, terms)
            if k < 4:
                print(f"  u={u:.6f}  r_s={rs:+.9e}  r_u={ru:+.9e}  "
                      f"r_v={rv:+.9e}")
        print(f"worst |r| over {a.nu} angles: {worst:.9e}")
        print(f"worst per component: {per[0]:.9e} {per[1]:.9e} {per[2]:.9e}")
        # the three terms the radial component is the difference of, at the
        # angle where it is largest, which is where a covering reads them
        t1, t2, t3 = best[1]
        print(f"worst r_s over {a.nu} angles: {abs(best[0]):.9e}")
        print(f"  terms  {abs(t1):.9e}  {abs(t2):.9e}  {abs(t3):.9e}")
        print(f"  their difference {t1 - t2 - t3:+.9e} against "
              f"r_s {best[0]:+.9e}")
        return
    s = a.at if a.at is not None else float(w.s_full[j])
    print(f"ns={w.ns} node={j} s={s:.9f} "
          f"inside [{w.s_half[j]:.9f}, {w.s_half[j + 1]:.9f}]")
    worst = 0.0
    best = None
    for k in range(a.nu):
        if a.u is not None:
            u = a.u
        elif a.cells:
            u = (2 * k + 1) * np.pi / a.nu
        else:
            u = 2 * np.pi * k / a.nu
        rs, ru, rv, sg, gs, terms = residual_at(w, j, s, u, a.v)
        worst = max(worst, abs(rs), abs(ru), abs(rv))
        if best is None or abs(rs) > abs(best[0]):
            best = (rs, terms)
        if k < 4:
            print(f"  u={u:.6f}  r_s={rs:+.9e}  r_u={ru:+.9e}  r_v={rv:+.9e}")
        if a.u is not None:
            break
    print(f"worst |r| over {a.nu} angles: {worst:.9e}")
    t1, t2, t3 = best[1]
    print(f"worst r_s over {a.nu} angles: {abs(best[0]):.9e}")
    print(f"  terms  {abs(t1):.9e}  {abs(t2):.9e}  {abs(t3):.9e}")
    print(f"  their difference {t1 - t2 - t3:+.9e} against "
          f"r_s {best[0]:+.9e}")


if __name__ == "__main__":
    main()
