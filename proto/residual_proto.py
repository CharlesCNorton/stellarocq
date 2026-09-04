"""Field quantities of a wout, checked against the arrays the file carries.

This is the early prototype, and its radial interpolation is piecewise-cubic
Hermite in rho = sqrt(s), which is not the rule the certificates use: those
follow VMEC's parity-aware half-grid rule, and off the grid the cubic Hermite
through the value and the radial derivative VMEC gives at each half point.
proto/continuum_ref.py is the float reference of the certified reconstruction.

What this does, and nothing else does, is compare the reconstructed B^u, B^v
and sqrt(g) against the wout's own bsupumnc, bsupvmnc and gmnc, which checks
the field rather than the residual.

The reconstruction rule used here:
  R(s,u,v)   = sum_mn rmnc_mn(s) cos(m u - n v)
  Z(s,u,v)   = sum_mn zmns_mn(s) sin(m u - n v)
  lambda     = sum_mn lmns_mn(s) sin(m u - n v)
with coefficient profiles interpolated radially by piecewise-cubic Hermite
(centered-difference slopes; one-sided at the ends).  rmnc/zmns live on the
full grid s_j = j/(ns-1); lmns and iotas on the half grid s_{j-1/2}.

B^u = phip (iota - dlam/dv) / sqrtg,  B^v = phip (1 + dlam/du) / sqrtg
sqrtg = R (R_u Z_s - R_s Z_u)
B_i = g_iu B^u + g_iv B^v
mu0 J^u = (d_v B_s - d_s B_v)/sqrtg ; mu0 J^v = (d_s B_u - d_u B_s)/sqrtg
mu0 J^s = (d_u B_v - d_v B_u)/sqrtg
r_s = sqrtg (J^u B^v - J^v B^u) - dp/ds
r_u = -sqrtg J^s B^v ;  r_v = sqrtg J^s B^u
"""
import numpy as np, netCDF4, sys

MU0 = 4e-7 * np.pi

class Hermite:
    """Piecewise-cubic Hermite through (nodes, values), FD slopes."""
    def __init__(self, s_nodes, y):
        """Store nodes and centered-difference slopes; y has shape (n, ...)."""
        self.s = np.asarray(s_nodes); self.y = np.asarray(y, dtype=float)
        d = np.empty_like(self.y)
        ds = np.diff(self.s)
        d[1:-1] = (self.y[2:] - self.y[:-2]) / (self.s[2:] - self.s[:-2])[:, None]
        d[0]    = (self.y[1] - self.y[0]) / ds[0]
        d[-1]   = (self.y[-1] - self.y[-2]) / ds[-1]
        self.d = d
    def eval(self, s):
        """Value, first, and second derivative at s."""
        i = int(np.clip(np.searchsorted(self.s, s) - 1, 0, len(self.s) - 2))
        h = self.s[i+1] - self.s[i]; t = (s - self.s[i]) / h
        y0, y1, d0, d1 = self.y[i], self.y[i+1], self.d[i], self.d[i+1]
        h00 = 2*t**3 - 3*t**2 + 1; h10 = t**3 - 2*t**2 + t
        h01 = -2*t**3 + 3*t**2;    h11 = t**3 - t**2
        val = h00*y0 + h10*h*d0 + h01*y1 + h11*h*d1
        dh00 = (6*t**2 - 6*t)/h; dh10 = (3*t**2 - 4*t + 1)
        dh01 = (-6*t**2 + 6*t)/h; dh11 = (3*t**2 - 2*t)
        der = dh00*y0 + dh10*d0 + dh01*y1 + dh11*d1
        d2h00 = (12*t - 6)/h**2; d2h10 = (6*t - 4)/h
        d2h01 = (-12*t + 6)/h**2; d2h11 = (6*t - 2)/h
        der2 = d2h00*y0 + d2h10*d0 + d2h01*y1 + d2h11*d1
        return val, der, der2

class RhoHermite:
    """Hermite in rho = sqrt(s); returns d/ds and d2/ds2 via the chain rule."""
    def __init__(self, s_nodes, y):
        """Wrap a Hermite interpolant built over rho = sqrt(s)."""
        self.h = Hermite(np.sqrt(np.asarray(s_nodes)), y)
    def eval(self, s):
        """Value, d/ds, d2/ds2 at s via the chain rule."""
        rho = np.sqrt(s)
        val, dr, d2r = self.h.eval(rho)
        ds  = dr / (2.0*rho)
        d2s = d2r/(4.0*rho*rho) - dr/(4.0*rho**3)
        return val, ds, d2s

class Wout:
    """The wout fields the reference evaluation needs."""

    def __init__(self, path):
        """Load the fields and build the radial interpolants."""
        d = netCDF4.Dataset(path); d.set_auto_mask(False); v = d.variables
        g = lambda k: np.asarray(v[k][:], dtype=float)
        self.ns = int(v['ns'][:]); self.signgs = int(v['signgs'][:])
        self.xm = g('xm').astype(int); self.xn = g('xn').astype(int)
        self.rmnc = g('rmnc'); self.zmns = g('zmns'); self.lmns = g('lmns')
        self.iotas = g('iotas'); self.phips = g('phips'); self.phipf = g('phipf')
        self.am = g('am'); self.presf = g('presf')
        self.bsupumnc = g('bsupumnc'); self.bsupvmnc = g('bsupvmnc')
        self.gmnc = g('gmnc')
        self.xm_nyq = g('xm_nyq').astype(int); self.xn_nyq = g('xn_nyq').astype(int)
        h = 1.0/(self.ns-1)
        self.s_full = np.arange(self.ns)*h
        self.s_half = (np.arange(1, self.ns)-0.5)*h
        self.R = RhoHermite(self.s_full, self.rmnc)
        self.Z = RhoHermite(self.s_full, self.zmns)
        self.L = RhoHermite(self.s_half, self.lmns[1:])
        self.I = RhoHermite(self.s_half, self.iotas[1:].reshape(-1, 1))
        d.close()

def fields(w, s, u, vv, phip_val):
    """All field quantities and derivatives at one point."""
    """All needed quantities at one point. phip_val: signed dPhi/ds/(2pi)."""
    m = w.xm; n = w.xn
    ang = m*u - n*vv
    c = np.cos(ang); sn = np.sin(ang)
    rv_, rd_, rdd_ = w.R.eval(s)
    zv_, zd_, zdd_ = w.Z.eval(s)
    lv_, ld_, _    = w.L.eval(s)
    iot, iotp, _   = w.I.eval(s); iot = float(np.ravel(iot)[0]); iotp = float(np.ravel(iotp)[0])
    def S(coef, kern): return float(np.dot(coef, kern))
    R    = S(rv_,  c);    Z_s  = S(zd_,  sn);  lam_u = S(lv_,  m*c)
    R_s  = S(rd_,  c);    Z_ss = S(zdd_, sn);  lam_v = S(lv_, -n*c)
    R_ss = S(rdd_, c);    Z_u  = S(zv_,  m*c); lam_su= S(ld_,  m*c)
    R_u  = S(rv_, -m*sn); Z_v  = S(zv_, -n*c); lam_sv= S(ld_, -n*c)
    R_v  = S(rv_,  n*sn); Z_su = S(zd_,  m*c); lam_uu= S(lv_, -m*m*sn)
    R_su = S(rd_, -m*sn); Z_sv = S(zd_, -n*c); lam_uv= S(lv_,  m*n*sn)
    R_sv = S(rd_,  n*sn); Z_uu = S(zv_, -m*m*sn); lam_vv= S(lv_, -n*n*sn)
    R_uu = S(rv_, -m*m*c); Z_uv = S(zv_,  m*n*sn)
    R_uv = S(rv_,  m*n*c); Z_vv = S(zv_, -n*n*sn)
    R_vv = S(rv_, -n*n*c)
    tau   = R_u*Z_s - R_s*Z_u
    sqrtg = R*tau
    tau_s = R_su*Z_s + R_u*Z_ss - R_ss*Z_u - R_s*Z_su
    tau_u = R_uu*Z_s + R_u*Z_su - R_su*Z_u - R_s*Z_uu
    tau_v = R_uv*Z_s + R_u*Z_sv - R_sv*Z_u - R_s*Z_uv
    g_s = R_s*tau + R*tau_s; g_u = R_u*tau + R*tau_u; g_v = R_v*tau + R*tau_v
    guu = R_u*R_u + Z_u*Z_u
    guv = R_u*R_v + Z_u*Z_v
    gvv = R_v*R_v + Z_v*Z_v + R*R
    gsu = R_s*R_u + Z_s*Z_u
    gsv = R_s*R_v + Z_s*Z_v
    guu_s = 2*(R_u*R_su + Z_u*Z_su)
    guv_s = R_su*R_v + R_u*R_sv + Z_su*Z_v + Z_u*Z_sv
    gvv_s = 2*(R_v*R_sv + Z_v*Z_sv + R*R_s)
    gsu_u = R_su*R_u + R_s*R_uu + Z_su*Z_u + Z_s*Z_uu
    gsu_v = R_sv*R_u + R_s*R_uv + Z_sv*Z_u + Z_s*Z_uv
    gsv_u = R_su*R_v + R_s*R_uv + Z_su*Z_v + Z_s*Z_uv
    gsv_v = R_sv*R_v + R_s*R_vv + Z_sv*Z_v + Z_s*Z_vv
    guu_u = 2*(R_u*R_uu + Z_u*Z_uu); guu_v = 2*(R_u*R_uv + Z_u*Z_uv)
    guv_u = R_uu*R_v + R_u*R_uv + Z_uu*Z_v + Z_u*Z_uv
    guv_v = R_uv*R_v + R_u*R_vv + Z_uv*Z_v + Z_u*Z_vv
    gvv_u = 2*(R_v*R_uv + Z_v*Z_uv + R*R_u)
    gvv_v = 2*(R_v*R_vv + Z_v*Z_vv + R*R_v)
    bu_num = iot - lam_v; bv_num = 1.0 + lam_u
    Bu = phip_val*bu_num/sqrtg; Bv = phip_val*bv_num/sqrtg
    bu_num_s = iotp - lam_sv; bv_num_s = lam_su
    bu_num_u = -lam_uv;       bv_num_u = lam_uu
    bu_num_v = -lam_vv;       bv_num_v = lam_uv
    Bu_s = phip_val*(bu_num_s*sqrtg - bu_num*g_s)/sqrtg**2
    Bv_s = phip_val*(bv_num_s*sqrtg - bv_num*g_s)/sqrtg**2
    Bu_u = phip_val*(bu_num_u*sqrtg - bu_num*g_u)/sqrtg**2
    Bv_u = phip_val*(bv_num_u*sqrtg - bv_num*g_u)/sqrtg**2
    Bu_v = phip_val*(bu_num_v*sqrtg - bu_num*g_v)/sqrtg**2
    Bv_v = phip_val*(bv_num_v*sqrtg - bv_num*g_v)/sqrtg**2
    B_u_s = guu_s*Bu + guu*Bu_s + guv_s*Bv + guv*Bv_s
    B_v_s = guv_s*Bu + guv*Bu_s + gvv_s*Bv + gvv*Bv_s
    B_s_u = gsu_u*Bu + gsu*Bu_u + gsv_u*Bv + gsv*Bv_u
    B_s_v = gsu_v*Bu + gsu*Bu_v + gsv_v*Bv + gsv*Bv_v
    B_u_u = guu_u*Bu + guu*Bu_u + guv_u*Bv + guv*Bv_u
    B_u_v = guu_v*Bu + guu*Bu_v + guv_v*Bv + guv*Bv_v
    B_v_u = guv_u*Bu + guv*Bu_u + gvv_u*Bv + gvv*Bv_u
    B_v_v = guv_v*Bu + guv*Bu_v + gvv_v*Bv + gvv*Bv_v
    B_u_cov = guu*Bu + guv*Bv
    B_v_cov = guv*Bu + gvv*Bv
    B2 = Bu*B_u_cov + Bv*B_v_cov
    return dict(R=R, sqrtg=sqrtg, Bu=Bu, Bv=Bv, B2=B2,
                B_s_v=B_s_v, B_v_s=B_v_s, B_u_s=B_u_s, B_s_u=B_s_u,
                B_v_u=B_v_u, B_u_v=B_u_v)

def main(path):
    """Validate the reconstruction against the wout, print residuals."""
    w = Wout(path)
    print(f"ns={w.ns} mnmax={len(w.xm)} signgs={w.signgs}")
    am = w.am
    pp = lambda s: sum(k*a*s**(k-1) for k, a in enumerate(am) if k > 0)
    phiedge_ps = w.phips[1]
    cands = {
        "phips":        phiedge_ps,
        "-phips":      -phiedge_ps,
        "phipf/2pi":    w.phipf[0]/(2*np.pi),
        "-phipf/2pi":  -w.phipf[0]/(2*np.pi),
    }
    jtest = w.ns//2
    s0 = w.s_half[jtest-1]
    us = np.linspace(0, 2*np.pi, 7, endpoint=False)
    def nyq_eval(row, u, vv):
        ang = w.xm_nyq*u - w.xn_nyq*vv
        return float(np.dot(row, np.cos(ang)))
    best = None
    for name, pv in cands.items():
        err_u = err_v = err_g = 0.0
        for u in us:
            f = fields(w, s0, u, 0.3, pv)
            bu_ref = nyq_eval(w.bsupumnc[jtest], u, 0.3)
            bv_ref = nyq_eval(w.bsupvmnc[jtest], u, 0.3)
            g_ref  = nyq_eval(w.gmnc[jtest],     u, 0.3)
            err_u = max(err_u, abs(f["Bu"]-bu_ref)/max(1e-30, abs(bv_ref)))
            err_v = max(err_v, abs(f["Bv"]-bv_ref)/max(1e-30, abs(bv_ref)))
            err_g = max(err_g, abs(f["sqrtg"]-g_ref)/max(1e-30, abs(g_ref)))
        print(f"  phip={name:>11}: relerr Bu {err_u:.3e}  Bv {err_v:.3e}  sqrtg {err_g:.3e}")
        if best is None or err_v < best[1]:
            best = (name, err_v, pv)
    name, _, pv = best
    print(f"  -> using phip = {name}")
    stests = w.s_half[2:-2:4]
    NU = 12
    NV = 1 if (w.xn == 0).all() else 8
    print(f"{'s':>8} {'max|r_s|/scale':>15} {'max|r_u|/sc':>12} {'max|r_v|/sc':>12}")
    worst = 0.0
    for s0 in stests:
        mrs = mru = mrv = scale = 0.0
        for u in np.linspace(0, 2*np.pi, NU, endpoint=False):
            for vv in np.linspace(0, 2*np.pi, NV, endpoint=False):
                f = fields(w, s0, u, vv, pv)
                t1 = (f["B_s_v"] - f["B_v_s"])*f["Bv"]
                t2 = (f["B_u_s"] - f["B_s_u"])*f["Bu"]
                r_s = (t1 - t2)/MU0 - pp(s0)
                Js  = (f["B_v_u"] - f["B_u_v"])/MU0
                r_u = -Js*f["Bv"]; r_v = Js*f["Bu"]
                sc  = max(abs(t1/MU0), abs(t2/MU0), abs(pp(s0)), f["B2"]/MU0)
                mrs = max(mrs, abs(r_s)); mru = max(mru, abs(r_u)); mrv = max(mrv, abs(r_v))
                scale = max(scale, sc)
        print(f"{s0:8.4f} {mrs/scale:15.3e} {mru/scale:12.3e} {mrv/scale:12.3e}")
        worst = max(worst, mrs/scale, mru/scale, mrv/scale)
    print(f"worst normalized residual over grid: {worst:.3e}")

if __name__ == "__main__":
    main(sys.argv[1])
