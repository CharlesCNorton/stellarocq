"""Newton's method for an invariant torus of the symmetric W7-X coil field, with
the field and the error of the torus in double-double arithmetic.

The coil set is the 480 base sources of the first five live coils and their
2 P images (rotations by -2 pi k / 5 and the stellarator reflection), built
in double-double from the base points. The torus is stored in the canonical
form of Fourier.v: R = sum_{k,l} c_kl cos(k t + 5 l p), Z = sum s_kl sin(k t + 5 l p)
over |k| <= M, |l| <= N, with c symmetric and s antisymmetric under (k,l) -> -(k,l).
Each step computes E = L K - V(K) on the grid in double-double, rounds it to
double, and takes the correction of KAMStep.v in double.

    python gen/kam_dd_newton.py START.npz COILS.npz OUT.npz --omega-num 337 --omega-den 1958 ...
"""
import argparse
import math
import time

import numpy as np
from mpmath import mp, mpf, sqrt as msqrt, cos as mcos, sin as msin, pi as mpi

NFP = 5

# ---------------------------------------------------------------- double-double
SPLIT = 134217729.0


def two_sum(a, b):
    s = a + b
    bb = s - a
    return s, (a - (s - bb)) + (b - bb)


def qts(a, b):
    s = a + b
    return s, b - (s - a)


def split(a):
    t = SPLIT * a
    hi = t - (t - a)
    return hi, a - hi


def two_prod(a, b):
    p = a * b
    ah, al = split(a)
    bh, bl = split(b)
    return p, ((ah * bh - p) + ah * bl + al * bh) + al * bl


def dadd(xh, xl, yh, yl):
    s, e = two_sum(xh, yh)
    t, f = two_sum(xl, yl)
    e = e + t
    s, e = qts(s, e)
    e = e + f
    return qts(s, e)


def dsub(xh, xl, yh, yl):
    return dadd(xh, xl, -yh, -yl)


def dmul(xh, xl, yh, yl):
    p, e = two_prod(xh, yh)
    e = e + (xh * yl + xl * yh)
    return qts(p, e)


def dmulf(xh, xl, y):
    p, e = two_prod(xh, y)
    e = e + xl * y
    return qts(p, e)


def ddiv(xh, xl, yh, yl):
    q1 = xh / yh
    rh, rl = dsub(xh, xl, *dmulf(yh, yl, q1))
    q2 = rh / yh
    rh, rl = dsub(rh, rl, *dmulf(yh, yl, q2))
    q3 = rh / yh
    s, e = qts(q1, q2)
    return dadd(s, e, q3, np.zeros_like(q3))


def dsqrt(xh, xl):
    s = np.sqrt(xh)
    p, e = two_prod(s, s)
    rh, rl = dsub(xh, xl, p, e)
    return qts(s, rh / (2 * s))


def dsum_last(h, l):
    """Pairwise double-double sum along the last axis."""
    while h.shape[-1] > 1:
        if h.shape[-1] % 2:
            pad = [(0, 0)] * (h.ndim - 1) + [(0, 1)]
            h = np.pad(h, pad)
            l = np.pad(l, pad)
        h, l = dadd(h[..., 0::2], l[..., 0::2], h[..., 1::2], l[..., 1::2])
    return h[..., 0], l[..., 0]


def dmatmul(Ah, Al, Bh, Bl):
    """(p x q) times (q x r) in double-double, summing pairwise over q."""
    ph, pl = dmul(Ah[:, :, None], Al[:, :, None], Bh[None, :, :], Bl[None, :, :])
    ph = np.moveaxis(ph, 1, 2)
    pl = np.moveaxis(pl, 1, 2)
    return dsum_last(np.ascontiguousarray(ph), np.ascontiguousarray(pl))


def mp_dd(x):
    h = float(x)
    return h, float(x - mpf(h))


# ---------------------------------------------------------------- the coil set
def base_sources(coilfile):
    c = np.load(coilfile)
    P, D = c["points"], c["tangents"]
    nb = len(P) // 96
    live = [i for i in range(nb) if np.linalg.norm(D[i * 96:(i + 1) * 96]) > 0]
    base = live[:5]
    Pb = np.concatenate([P[i * 96:(i + 1) * 96] for i in base])
    Db = np.concatenate([D[i * 96:(i + 1) * 96] for i in base])
    keep = np.linalg.norm(Db, axis=1) > 0
    return Pb[keep], Db[keep]


def images_dd(Pb, Db):
    """The 2 P images of every base source, in double-double."""
    mp.dps = 40
    Ph, Pl, Dh, Dl = [], [], [], []
    for k in range(NFP):
        a = -2 * mpi * k / NFP
        ch, cl = mp_dd(mcos(a))
        sh, sl = mp_dd(msin(a))
        for refl in (False, True):
            p = Pb.copy()
            d = Db.copy()
            if refl:
                p = p * np.array([1.0, -1.0, -1.0])
                d = -d * np.array([1.0, -1.0, -1.0])
            z0 = np.zeros(len(p))
            # rotation by a: (x c - y s, x s + y c, z)
            for arr, H, L in ((p, Ph, Pl), (d, Dh, Dl)):
                x, y, z = arr[:, 0], arr[:, 1], arr[:, 2]
                xc = dmul(x, z0, ch * np.ones_like(x), cl * np.ones_like(x))
                ys = dmul(y, z0, sh * np.ones_like(x), sl * np.ones_like(x))
                xs = dmul(x, z0, sh * np.ones_like(x), sl * np.ones_like(x))
                yc = dmul(y, z0, ch * np.ones_like(x), cl * np.ones_like(x))
                X = dsub(*xc, *ys)
                Yv = dadd(*xs, *yc)
                H.append(np.stack([X[0], Yv[0], z], 1))
                L.append(np.stack([X[1], Yv[1], z0], 1))
    return (np.concatenate(Ph), np.concatenate(Pl), np.concatenate(Dh), np.concatenate(Dl))


# ---------------------------------------------------------------- field in double-double
SRC = None


def init_worker(src):
    global SRC
    SRC = src


def field_chunk(X):
    """B at the points X = (xh, xl) of shape (n, 3), in double-double, from SRC."""
    xh, xl = X
    Ph, Pl, Dh, Dl = SRC
    r = [dsub(xh[:, None, k], xl[:, None, k], Ph[None, :, k], Pl[None, :, k]) for k in range(3)]
    q = dmul(*r[0], *r[0])
    q = dadd(*q, *dmul(*r[1], *r[1]))
    q = dadd(*q, *dmul(*r[2], *r[2]))
    s = dsqrt(*q)
    one = np.ones_like(s[0])
    y = ddiv(one, 0 * one, *s)
    y3 = dmul(*dmul(*y, *y), *y)
    d = [(Dh[None, :, k] * one, Dl[None, :, k] * one) for k in range(3)]
    c1 = dsub(*dmul(*d[1], *r[2]), *dmul(*d[2], *r[1]))
    c2 = dsub(*dmul(*d[2], *r[0]), *dmul(*d[0], *r[2]))
    c3 = dsub(*dmul(*d[0], *r[1]), *dmul(*d[1], *r[0]))
    out = [dsum_last(*dmul(*c, *y3)) for c in (c1, c2, c3)]
    return np.stack([o[0] for o in out], 1), np.stack([o[1] for o in out], 1)


def field_dd(pool, Xh, Xl, chunk=32):
    parts = [(Xh[i:i + chunk], Xl[i:i + chunk]) for i in range(0, len(Xh), chunk)]
    res = pool.map(field_chunk, parts)
    return np.concatenate([r[0] for r in res]), np.concatenate([r[1] for r in res])


# ---------------------------------------------------------------- the main program
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("start")
    ap.add_argument("coils")
    ap.add_argument("out")
    ap.add_argument("--omega-num", type=int, default=337)
    ap.add_argument("--omega-den", type=int, default=1958)
    ap.add_argument("--M", type=int, default=40)
    ap.add_argument("--N", type=int, default=85)
    ap.add_argument("--nth", type=int, default=128)
    ap.add_argument("--nph", type=int, default=256)
    ap.add_argument("--steps", type=int, default=3)
    ap.add_argument("--procs", type=int, default=24)
    ap.add_argument("--w", type=float, nargs="+", default=[0.05])
    ap.add_argument("--kappa", type=float, default=0.1)
    a = ap.parse_args()
    from multiprocessing import Pool

    mp.dps = 40
    beta = (a.omega_num + msqrt(5)) / a.omega_den
    omh, oml = mp_dd(NFP * beta)
    om = omh + oml
    print(f"omega = {NFP * beta} (double {om!r})", flush=True)

    Pb, Db = base_sources(a.coils)
    src = images_dd(Pb, Db)
    print(f"{len(Pb)} base sources, {len(src[0])} with the images", flush=True)
    src64 = (src[0] + src[1], src[2] + src[3])

    M, N, Nt, Nf = a.M, a.N, a.nth, a.nph
    ks = np.arange(-M, M + 1)
    ls = np.arange(-N, N + 1)
    # tables in double-double: cos/sin(k t_i), cos/sin(5 l p_j), cos/sin(p_j)
    def table(n, idx, grid):
        C = np.zeros((2, len(grid), len(idx)))
        S = np.zeros((2, len(grid), len(idx)))
        for i, g in enumerate(grid):
            for j, k in enumerate(idx):
                ang = 2 * mpi * ((int(k) * int(g)) % n) / n
                C[0, i, j], C[1, i, j] = mp_dd(mcos(ang))
                S[0, i, j], S[1, i, j] = mp_dd(msin(ang))
        return C, S
    Ct, St = table(Nt, ks, np.arange(Nt))            # (Nt, 2M+1)
    Cf, Sf = table(Nf, ls, np.arange(Nf))            # (Nf, 2N+1): cos(2 pi l j / Nf) = cos(5 l p_j)
    cpj = np.array([mp_dd(mcos(2 * mpi * j / (NFP * Nf))) for j in range(Nf)]).T
    spj = np.array([mp_dd(msin(2 * mpi * j / (NFP * Nf))) for j in range(Nf)]).T

    # the starting torus: from a double grid, or from double-double coefficients
    st = np.load(a.start)
    if "ch" in st:
        c = (st["ch"], st["cl"])
        s = (st["sh"], st["sl"])
    else:
        R0, Z0 = st["R"], st["Z"]
        n0t, n0f = R0.shape
        F = np.fft.fft2(R0) / R0.size
        G = np.fft.fft2(Z0) / Z0.size
        c0 = np.zeros((2 * M + 1, 2 * N + 1))
        s0 = np.zeros((2 * M + 1, 2 * N + 1))
        for ii, k in enumerate(ks):
            for jj, l in enumerate(ls):
                if abs(k) < n0t // 2 and abs(l) < n0f // 2:
                    c0[ii, jj] = F[k % n0t, l % n0f].real
                    s0[ii, jj] = -G[k % n0t, l % n0f].imag
        c = (c0, np.zeros_like(c0))
        s = (s0, np.zeros_like(s0))

    def grid_cos(cc):
        """sum c_kl cos(k t + 5 l p) on the grid, double-double."""
        A = dmatmul(Ct[0], Ct[1], *cc)                       # (Nt, 2N+1)
        B = dmatmul(St[0], St[1], *cc)
        X = dmatmul(*A, Cf[0].T.copy(), Cf[1].T.copy())      # (Nt, Nf)
        Y = dmatmul(*B, Sf[0].T.copy(), Sf[1].T.copy())
        return dsub(*X, *Y)

    def grid_sin(ss):
        """sum s_kl sin(k t + 5 l p) on the grid: sin(A+B) = sin A cos B + cos A sin B."""
        A = dmatmul(St[0], St[1], *ss)
        B = dmatmul(Ct[0], Ct[1], *ss)
        X = dmatmul(*A, Cf[0].T.copy(), Cf[1].T.copy())
        Y = dmatmul(*B, Sf[0].T.copy(), Sf[1].T.copy())
        return dadd(*X, *Y)

    kk = ks[:, None] * np.ones((1, 2 * N + 1))
    ll = np.ones((2 * M + 1, 1)) * ls[None, :]
    rate = (om * kk + NFP * ll)  # (om k + 5 l) in double; the double-double part below
    rate_h, rate_l = dadd(*dmulf(omh * np.ones_like(kk), oml * np.ones_like(kk), 1.0), 0 * kk, 0 * kk)
    rate_h, rate_l = dmul(rate_h, rate_l, kk, 0 * kk)
    rate_h, rate_l = dadd(rate_h, rate_l, NFP * ll, 0 * ll)

    kt = np.fft.fftfreq(Nt, 1.0 / Nt)[:, None]
    kp = (np.fft.fftfreq(Nf, 1.0 / Nf) * NFP)[None, :]
    wtk = np.exp(np.abs(kt))
    TH = 2 * np.pi * np.arange(Nt) / Nt
    PH = (2 * np.pi / NFP) * np.arange(Nf) / Nf
    cp = np.cos(PH)[None, :] * np.ones((Nt, 1))
    sp = np.sin(PH)[None, :] * np.ones((Nt, 1))

    def spec(f):
        return np.fft.fft2(f)

    def real(F):
        return np.real(np.fft.ifft2(F))

    def dth(f):
        return real(1j * kt * spec(f))

    def dph(f):
        return real(1j * kp * spec(f))

    def Lop(f):
        return real(1j * (om * kt + kp) * spec(f))

    def Linv(f):
        F = spec(f)
        dv = 1j * (om * kt + kp)
        dv[0, 0] = 1.0
        F = F / dv
        F[0, 0] = 0.0
        return real(F)

    def wnorm(f, w):
        F = np.fft.fft2(f) / f.size
        wt = np.exp(w * (np.abs(kt) + a.kappa * np.abs(kp)))
        return float(np.sum((np.abs(F.real) + np.abs(F.imag)) * wt))

    def to_coef(f, odd):
        """Canonical coefficients in the box from a double grid."""
        F = np.fft.fft2(f) / f.size
        out = np.zeros((2 * M + 1, 2 * N + 1))
        for ii, k in enumerate(ks):
            for jj, l in enumerate(ls):
                out[ii, jj] = -F[k % Nt, l % Nf].imag if odd else F[k % Nt, l % Nf].real
        return out

    def field64(R, Z):
        """B and its Jacobian in double at the grid points."""
        X = np.stack([(R * cp).ravel(), (R * sp).ravel(), Z.ravel()], 1)
        P64, D64 = src64
        B = np.zeros((len(X), 3))
        J = np.zeros((len(X), 3, 3))
        eye = np.eye(3)
        dxe = np.transpose(np.cross(D64[:, None, :], eye[None, :, :]), (0, 2, 1))
        for i0 in range(0, len(X), 64):
            x = X[i0:i0 + 64]
            r = x[:, None, :] - P64[None]
            q = np.einsum("nsk,nsk->ns", r, r)
            q32, q52 = q ** -1.5, q ** -2.5
            dxr = np.cross(D64[None], r)
            B[i0:i0 + 64] = np.einsum("nsa,ns->na", dxr, q32)
            J[i0:i0 + 64] = (np.einsum("sab,ns->nab", dxe, q32) - 3 * np.einsum("nsa,nsb,ns->nab", dxr, r, q52))
        return B, J

    with Pool(a.procs, initializer=init_worker, initargs=(src,)) as pool:
        t0 = time.time()
        for it in range(a.steps + 1):
            Rg = grid_cos(c)
            Zg = grid_sin(s)
            # L K from the coefficients: d/dt cos -> -k sin, so L R = sum -(om k + 5 l) c sin
            LRc = dmul(-rate_h, -rate_l, *c)
            LZc = dmul(rate_h, rate_l, *s)
            LR = grid_sin(LRc)
            LZ = grid_cos(LZc)
            # the field in double-double
            cph = np.broadcast_to(cpj[0][None, :], (Nt, Nf)).copy()
            cpl = np.broadcast_to(cpj[1][None, :], (Nt, Nf)).copy()
            sph = np.broadcast_to(spj[0][None, :], (Nt, Nf)).copy()
            spl = np.broadcast_to(spj[1][None, :], (Nt, Nf)).copy()
            x1 = dmul(*Rg, cph, cpl)
            x2 = dmul(*Rg, sph, spl)
            Xh = np.stack([x1[0].ravel(), x2[0].ravel(), Zg[0].ravel()], 1)
            Xl = np.stack([x1[1].ravel(), x2[1].ravel(), Zg[1].ravel()], 1)
            Bh, Bl = field_dd(pool, Xh, Xl)
            b = [(Bh[:, k].reshape(Nt, Nf), Bl[:, k].reshape(Nt, Nf)) for k in range(3)]
            BR = dadd(*dmul(*b[0], cph, cpl), *dmul(*b[1], sph, spl))
            BP = dsub(*dmul(*b[1], cph, cpl), *dmul(*b[0], sph, spl))
            BZ = b[2]
            VR = ddiv(*dmul(*Rg, *BR), *BP)
            VZ = ddiv(*dmul(*Rg, *BZ), *BP)
            ERd = dsub(*LR, *VR)
            EZd = dsub(*LZ, *VZ)
            ER = ERd[0] + ERd[1]
            EZ = EZd[0] + EZd[1]
            Ew = [max(wnorm(ER, w), wnorm(EZ, w)) for w in a.w]
            print(f"iter {it}: sup|E| {max(np.abs(ER).max(), np.abs(EZ).max()):.3e}, "
                  f"|E|_w {' '.join(f'{x:.3e}' for x in Ew)} ({time.time() - t0:.0f} s)", flush=True)
            if it == a.steps:
                break
            # the correction of KAMStep.v in double
            R = Rg[0] + Rg[1]
            Z = Zg[0] + Zg[1]
            B64, J64 = field64(R, Z)
            eR = np.stack([cp.ravel(), sp.ravel(), 0 * cp.ravel()], 1)
            eP = np.stack([-sp.ravel(), cp.ravel(), 0 * cp.ravel()], 1)
            eZ = np.tile([0.0, 0.0, 1.0], (len(eR), 1))
            comp = lambda v, e: np.einsum("na,na->n", v, e).reshape(Nt, Nf)          # noqa: E731
            dB = lambda eo, ei: np.einsum("na,nab,nb->n", eo, J64, ei).reshape(Nt, Nf)  # noqa: E731
            br, bp, bz = comp(B64, eR), comp(B64, eP), comp(B64, eZ)
            sig = bp
            gs = [dB(eP, e) for e in (eR, eZ)]
            Vn = [R * br, R * bz]
            dVn = [[dB(eR, e) * R + (br if k == 0 else 0) for k, e in enumerate((eR, eZ))],
                   [dB(eZ, e) * R + (bz if k == 0 else 0) for k, e in enumerate((eR, eZ))]]
            DV = [[(dVn[i][k] * sig - Vn[i] * gs[k]) / sig ** 2 for k in range(2)] for i in range(2)]
            aR, aZ = dth(R), dth(Z)
            g = 1.0 / (sig * (aR ** 2 + aZ ** 2))
            NR, NZ = -aZ * g, aR * g
            eta1 = sig * (ER * NZ - EZ * NR)
            eta2 = sig * (aR * EZ - aZ * ER)
            LNR = Lop(NR) - (DV[0][0] * NR + DV[0][1] * NZ)
            LNZ = Lop(NZ) - (DV[1][0] * NR + DV[1][1] * NZ)
            T = sig * (LNR * NZ - LNZ * NR)
            tau = T.mean()
            w2 = -Linv(eta2)
            xi20 = -(eta1.mean() + (T * w2).mean()) / tau
            xi2 = w2 + xi20
            rhs = eta1 + T * xi2
            xi1 = -Linv(rhs - rhs.mean())
            dR = xi1 * aR + xi2 * NR
            dZ = xi1 * aZ + xi2 * NZ
            c = dadd(*c, to_coef(dR, False), np.zeros((2 * M + 1, 2 * N + 1)))
            s = dadd(*s, to_coef(dZ, True), np.zeros((2 * M + 1, 2 * N + 1)))
            print(f"   tau {tau:+.6e}, |xi| {max(np.abs(xi1).max(), np.abs(xi2).max()):.3e}", flush=True)
    np.savez(a.out, ch=c[0], cl=c[1], sh=s[0], sl=s[1], M=M, N=N, omh=omh, oml=oml,
             Pb=Pb, Db=Db, nth=Nt, nph=Nf)
    print("saved", a.out, flush=True)


if __name__ == "__main__":
    main()
