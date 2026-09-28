"""Write the integer data of the check of the first torus (KE0.e0data).

    python gen/kam_e0.py dd_noble_0.100.npz OUT --N1 513 --M 1025 --K1 246 --K2 493 --D 2467

The torus is the double-double Newton torus: cosine mantissas of R and sine
mantissas of Z over zrange Km x zrange Kn (the order K, -K, K-1, ..., 0 of zsum),
toroidal modes n = P l, at scale 2^-s0. The seeds Ub of 1 / B_phi and gs of
1 / (B_phi |a|^2), a = d_t K, are the truncated transforms of those functions on
a grid of one period, in cosine mantissas at the same scale. The sources are the
base sources at scale 2^-ssrc. The trigonometric and exponential seeds are
outward-rounded enclosures at the checker's 2^-192; the claims are the crude
norms on the wide strip (estimated here, verified by the crude check) times a
margin, and the bounds claimed at w.
"""
import argparse
import math
import time

import mpmath as mp
import numpy as np

KFX = 192
NFP = 5
KAPPA = 0.1
mp.mp.dps = 120

ap = argparse.ArgumentParser()
ap.add_argument("torus")
ap.add_argument("out")
ap.add_argument("--N1", type=int, required=True)
ap.add_argument("--M", type=int, required=True)
ap.add_argument("--K1", type=int, required=True)
ap.add_argument("--K2", type=int, required=True)
ap.add_argument("--D", type=int, required=True)
ap.add_argument("--w", default="1/20")
ap.add_argument("--wc", default="3/10")
ap.add_argument("--s0", type=int, default=120)
ap.add_argument("--ssrc", type=int, default=80)
ap.add_argument("--kub", type=int, nargs=2, default=[16, 50])
ap.add_argument("--kg", type=int, nargs=2, default=[120, 60])
ap.add_argument("--thr", type=float, nargs=2, default=[5e-18, 3e-16],
                help="coefficients of the seeds below these are float noise and set to zero")
ap.add_argument("--nt", type=int, default=320, help="poloidal points of the seed grid")
ap.add_argument("--nf", type=int, default=512, help="toroidal points of one period of the seed grid")
ap.add_argument("--crude", type=float, nargs=3, default=[7.634e3, 7.634e3, 4.867e3],
                help="crude |B_R|, |B_phi|, |B_Z| on the wide strip, as the source check bounds them")
ap.add_argument("--margin", type=float, default=3.0)
ap.add_argument("--B", type=float, nargs=4, default=[1e-20, 1e-20, 3e-9, 5e-9])
a = ap.parse_args()
t0 = time.time()

d = np.load(a.torus)
M0, N0 = int(d["M"]), int(d["N"])
Ch, Cl, Sh, Sl = d["ch"], d["cl"], d["sh"], d["sl"]
C, S = Ch + Cl, Sh + Sl
om = float(d["omh"]) + float(d["oml"])
Pb, Db = d["Pb"], d["Db"]
ks = np.arange(-M0, M0 + 1)
ls = np.arange(-N0, N0 + 1)
w = float(mp.mpf(mp.fraction(*map(int, a.w.split("/")))))
wc = float(mp.mpf(mp.fraction(*map(int, a.wc.split("/")))))


def zrange(K):
    out = []
    for j in range(K, 0, -1):
        out += [j, -j]
    return out + [0]


def wt(w_, k, n):
    return np.exp(w_ * (np.abs(k) + KAPPA * np.abs(n)))


def cnorm(c, kk, nn, w_):
    return float(np.sum(np.abs(c) * wt(w_, kk[:, None], nn[None, :])))


# ------------------------------------------------------------------ the field and a along K0 on one period
Nt, Nf = a.nt, a.nf
th = 2 * np.pi * np.arange(Nt) / Nt
ph = (2 * np.pi / NFP) * np.arange(Nf) / Nf


def synth(Cc, Ss, dt=0):
    k = ks[:, None].astype(float)
    coef = (Cc - 1j * Ss) * (1j * k) ** dt
    Et = np.exp(1j * np.outer(th, ks))
    Ep = np.exp(1j * np.outer(NFP * ls, ph))
    return np.real(Et @ coef @ Ep)


R = synth(C, 0 * C)
Z = synth(0 * S, S)
Rt, Zt = synth(C, 0 * C, 1), synth(0 * S, S, 1)


def images(P_, D_):
    Ps, Ds = [], []
    for k in range(NFP):
        ang = -2 * np.pi * k / NFP
        Rz = np.array([[np.cos(ang), -np.sin(ang), 0], [np.sin(ang), np.cos(ang), 0], [0, 0, 1]])
        Ps.append(P_ @ Rz.T)
        Ds.append(D_ @ Rz.T)
        Sm = np.diag([1.0, -1.0, -1.0])
        Ps.append((P_ @ Sm.T) @ Rz.T)
        Ds.append(-(D_ @ Sm.T) @ Rz.T)
    return np.concatenate(Ps), np.concatenate(Ds)


Pall, Dall = images(Pb, Db)
cph, sph = np.cos(ph)[None, :], np.sin(ph)[None, :]
X = np.stack([R * cph, R * sph, Z], -1)
B = np.zeros((Nt, Nf, 3))
for j0 in range(0, len(Pall), 100):
    r = X[:, :, None, :] - Pall[None, None, j0:j0 + 100, :]
    q = np.sum(r * r, -1)
    B += np.sum(np.cross(Dall[None, None, j0:j0 + 100], r) * (q ** -1.5)[..., None], 2)
BP = -B[..., 0] * sph + B[..., 1] * cph
a2 = Rt * Rt + Zt * Zt
print(f"field on {Nt} x {Nf} ({time.time() - t0:.0f} s): B_phi in [{BP.min():.4f}, {BP.max():.4f}]", flush=True)

kt = np.fft.fftfreq(Nt, 1.0 / Nt).astype(int)
lp = np.fft.fftfreq(Nf, 1.0 / Nf).astype(int)


def seed_rows(f, K1_, L1_, thr):
    """cosine coefficients of the even function f over zrange K1_ x zrange L1_ (n = 5 l), those below thr
    set to zero"""
    F = np.fft.fft2(f) / f.size
    rows = []
    for k in zrange(K1_):
        rows.append([c if abs(c) >= thr else 0.0 for c in (float(F[k % Nt, l % Nf].real) for l in zrange(L1_))])
    return rows


def rows_grid(rows, K1_, L1_):
    cc = np.zeros((2 * K1_ + 1, 2 * L1_ + 1))
    for i, k in enumerate(zrange(K1_)):
        for j, l in enumerate(zrange(L1_)):
            cc[k + K1_, l + L1_] = rows[i][j]
    kk, ll = np.arange(-K1_, K1_ + 1), np.arange(-L1_, L1_ + 1)
    Et = np.exp(1j * np.outer(th, kk))
    Ep = np.exp(1j * np.outer(NFP * ll, ph))
    return np.real(Et @ cc.astype(complex) @ Ep), cc, kk, ll


def gnorm(f, w_):
    F = np.fft.fft2(f) / f.size
    return float(np.sum((np.abs(F.real) + np.abs(F.imag)) * wt(w_, kt[:, None], NFP * lp[None, :])))


rowsU = seed_rows(1.0 / BP, *a.kub, a.thr[0])
Ubg, cU, kU, lU = rows_grid(rowsU, *a.kub)
rowsG = seed_rows(1.0 / (BP * a2), *a.kg, a.thr[1])
gsg, cG, kG, lG = rows_grid(rowsG, *a.kg)
def gnorm_low(f, w_, kmax, lmax):
    """the norm over |k| <= kmax, |l| <= lmax, below the float noise of the grid values"""
    F = np.fft.fft2(f) / f.size
    m = (np.abs(kt)[:, None] <= kmax) & (np.abs(lp)[None, :] <= lmax)
    return float(np.sum(((np.abs(F.real) + np.abs(F.imag)) * wt(w_, kt[:, None], NFP * lp[None, :]))[m]))


thU = gnorm(1 - BP * Ubg, w)
thG = gnorm(1 - BP * a2 * gsg, w)
print(f"defects below the noise: U {gnorm_low(1 - BP * Ubg, w, 80, 120):.2e}, "
      f"g {gnorm_low(1 - BP * a2 * gsg, w, 140, 120):.2e}", flush=True)
nU = cnorm(cU, kU, NFP * lU, wc)
nG = cnorm(cG, kG, NFP * lG, wc)
print(f"seeds: Ub {a.kub} defect {thU:.2e} |Ub|(w') {nU:.4f}; gs {a.kg} defect {thG:.2e} |gs|(w') {nG:.4e}",
      flush=True)

# ------------------------------------------------------------------ the claims on the wide strip
nfull = NFP * ls
kk = ks[:, None].astype(float)
KR = cnorm(C, ks, nfull, wc)
tR = cnorm(kk * C, ks, nfull, wc)
tZ = cnorm(kk * S, ks, nfull, wc)
pR = cnorm(nfull[None, :] * C, ks, nfull, wc)
pZ = cnorm(nfull[None, :] * S, ks, nfull, wc)
LR, LZ = abs(om) * tR + pR, abs(om) * tZ + pZ
cBR, cBP, cBZ = a.crude
Mw = [a.margin * (cBP * LR + KR * cBR), a.margin * (cBP * LZ + KR * cBZ),
      a.margin * (1 + cBP * nU), a.margin * (1 + cBP * (tR * tR + tZ * tZ) * nG)]
print(f"wide strip: |K_R| {KR:.3f} |L K_R| <= {LR:.3f} |L K_Z| <= {LZ:.3f} |d_t R| {tR:.3f} |d_t Z| {tZ:.3f}; "
      f"claims Mw {[f'{x:.3e}' for x in Mw]}", flush=True)


# ------------------------------------------------------------------ the data
def mant_dd(hi, lo, s):
    return int(mp.nint((mp.mpf(float(hi)) + mp.mpf(float(lo))) * mp.mpf(2) ** s))


def mant(x, s):
    return int(mp.nint(mp.mpf(x) * mp.mpf(2) ** s))


def encl(x):
    y = x * mp.mpf(2) ** KFX
    return int(mp.floor(y)) - 1, int(mp.ceil(y)) + 1


def dyad(x):
    m = int(mp.nint(mp.mpf(x) * mp.mpf(2) ** KFX))
    return m, m


wq = mp.mpf(mp.fraction(*map(int, a.w.split("/"))))
wcq = mp.mpf(mp.fraction(*map(int, a.wc.split("/"))))
kap = mp.mpf(1) / 10
P, N1, M, K1, K2, D = NFP, a.N1, a.M, a.K1, a.K2, a.D
trig = []
for Nn in (N1, M, P * M):
    trig += [encl(mp.cos(2 * mp.pi / Nn)), encl(mp.sin(2 * mp.pi / Nn))]
exps = [encl(mp.exp(wq)), encl(mp.exp(-wcq)), encl(mp.exp(-(wcq * (N1 - K1)))), encl(mp.exp(wq * (kap * P))),
        encl(mp.exp(-(wcq * (kap * P)))), encl(mp.exp(-(wcq * (kap * (P * M - P * K2))))),
        encl(mp.exp(-((wcq - wq) * (kap * (D + 1)))))]
bounds = [dyad(x) for x in Mw] + [dyad(x) for x in a.B]
Kmu, Knu = a.kub
Kmg, Kng = a.kg
with open(a.out, "w") as f:
    f.write(f"{P} {N1} {M} {K1} {K2} {D} {M0} {N0} {Kmu} {Knu} {Kmg} {Kng}\n{a.s0}\n")
    for k in zrange(M0):
        f.write(" ".join(str(mant_dd(Ch[k + M0, l + N0], Cl[k + M0, l + N0], a.s0)) for l in zrange(N0)) + "\n")
    for k in zrange(M0):
        f.write(" ".join(str(mant_dd(Sh[k + M0, l + N0], Sl[k + M0, l + N0], a.s0)) for l in zrange(N0)) + "\n")
    for rows in (rowsU, rowsG):
        for row in rows:
            f.write(" ".join(str(mant(x, a.s0)) for x in row) + "\n")
    f.write(f"{a.ssrc}\n{len(Pb)}\n")
    for j in range(len(Pb)):
        vals = [int(round(float(x) * 2 ** a.ssrc)) for x in list(Pb[j]) + list(Db[j])]
        f.write(" ".join(map(str, vals)) + "\n")
    f.write("979 -337\n")
    for lo, hi in trig + exps + bounds:
        f.write(f"{lo} {hi}\n")
print(f"wrote {a.out}: torus {2 * M0 + 1} x {2 * N0 + 1}, {len(Pb)} sources, grid {N1} x {M}, box {K1} x {K2}, "
      f"D {D} ({time.time() - t0:.0f} s)")
