"""Float prototype of the KAM certificate of FieldKAM.field_kam for the W7-X torus.

Evaluates, in double precision at the double-double torus, every number that
field_kam's hypotheses name: the frame and twist data at K0 (A0 G0 N0 T0 tau0, the
straightening normal b with L b = tau - T), the per-source data of the base sources
(r10 r20 r30 MY MD0 th0 y00, seeds truncated from q^(-1/2) along K0), the jet norms of the
total field along K0, the model constants of FieldConst (bBP bS1 bDV bMV bM2 bLD LBP) and the
smallness inequalities of KAMIter, with the formulas of the Rocq files.

    python gen/kam_design.py dd_noble_0.100.npz coils_w7x.npz [--w0 0.05 --d0frac ... --eps0 ...]
"""
import argparse
import math
import time

import numpy as np

NFP = 5
KAPPA = 0.1
E1 = math.e

ap = argparse.ArgumentParser()
ap.add_argument("torus")
ap.add_argument("coils")
ap.add_argument("--w0", type=float, default=0.05)
ap.add_argument("--d0frac", type=float, default=1 / 7)
ap.add_argument("--eps0", type=float, default=1e-20)
ap.add_argument("--nth", type=int, default=160)
ap.add_argument("--nph", type=int, default=360, help="points per field period")
ap.add_argument("--ky1", type=int, default=16, help="seed |m| cutoff")
ap.add_argument("--ky2", type=int, default=300, help="seed |n| cutoff (full period)")
ap.add_argument("--nphs", type=int, default=2048, help="full-period points for sources")
ap.add_argument("--nths", type=int, default=128)
ap.add_argument("--kub", type=int, nargs=2, default=[12, 40], help="Ub seed box (m, l)")
ap.add_argument("--kg", type=int, nargs=2, default=[12, 40], help="g seed box (m, l)")
ap.add_argument("--kb", type=int, nargs=2, default=[30, 80], help="b box (m, l)")
ap.add_argument("--kj", type=int, nargs=2, default=[12, 36], help="jet approximant box (m, l)")
ap.add_argument("--wc", type=float, default=0.3, help="crude strip")
ap.add_argument("--kr", type=int, nargs=2, default=[8, 80], help="K_ref box (m, full n)")
a = ap.parse_args()
t0 = time.time()

# ------------------------------------------------------------------ torus
d = np.load(a.torus)
C = d["ch"] + d["cl"]
S = d["sh"] + d["sl"]
M, N = int(d["M"]), int(d["N"])
om = float(d["omh"]) + float(d["oml"])
Pb, Db = d["Pb"], d["Db"]
ks = np.arange(-M, M + 1)
ls = np.arange(-N, N + 1)


def wtn(w, k, n):
    """weight of mode (k, n), n the full-period toroidal mode"""
    return np.exp(w * (np.abs(k) + KAPPA * np.abs(n)))


def canon_norm(Cc, Ss, kk, nn, w):
    return float(np.sum((np.abs(Cc) + np.abs(Ss)) * wtn(w, kk[:, None], nn[None, :])))


# grid over one field period
Nt, Nf = a.nth, a.nph
th = 2 * np.pi * np.arange(Nt) / Nt
ph = (2 * np.pi / NFP) * np.arange(Nf) / Nf


def synth(Cc, Ss, kk, ll, dt=0, dp=0, tt=None, pp=None):
    """values on the grid tt x pp (default the one-period grid) of
    sum Cc cos(k t + 5 l p) + Ss sin(k t + 5 l p), differentiated dt times in t and dp in p:
    the real part of sum (Cc - i Ss) (i k)^dt (i 5 l)^dp e^(i (k t + 5 l p))"""
    tt = th if tt is None else tt
    pp = ph if pp is None else pp
    k = kk[:, None].astype(float)
    n = (NFP * ll[None, :]).astype(float)
    coef = (Cc - 1j * Ss) * (1j * k) ** dt * (1j * n) ** dp
    Et = np.exp(1j * np.outer(tt, kk))
    Ep = np.exp(1j * np.outer(NFP * ll, pp))
    return np.real(Et @ coef @ Ep)


def spec(f):
    """canonical (c, s) of one-period grid values, over |k| < Nt/2, |l| < Nf/2"""
    F = np.fft.fft2(f) / f.size
    kt = np.fft.fftfreq(f.shape[0], 1.0 / f.shape[0]).astype(int)
    lp = np.fft.fftfreq(f.shape[1], 1.0 / f.shape[1]).astype(int)
    return F.real, -F.imag, kt, NFP * lp


def gnorm(f, w):
    c, s, kt, n = spec(f)
    return canon_norm(c, s, kt, n, w)


def gmean(f):
    return float(np.mean(f))


def Lop(f):
    """L f = om d_t f + d_phi f on one-period grid values"""
    F = np.fft.fft2(f)
    kt = np.fft.fftfreq(f.shape[0], 1.0 / f.shape[0])
    lp = np.fft.fftfreq(f.shape[1], 1.0 / f.shape[1]) * NFP
    return np.real(np.fft.ifft2(1j * (om * kt[:, None] + lp[None, :]) * F))


def dtop(f):
    F = np.fft.fft2(f)
    kt = np.fft.fftfreq(f.shape[0], 1.0 / f.shape[0])
    return np.real(np.fft.ifft2(1j * kt[:, None] * F))


def Linv(f):
    F = np.fft.fft2(f)
    kt = np.fft.fftfreq(f.shape[0], 1.0 / f.shape[0])
    lp = np.fft.fftfreq(f.shape[1], 1.0 / f.shape[1]) * NFP
    dv = om * kt[:, None] + lp[None, :]
    dv[0, 0] = 1.0
    G = F / (1j * dv)
    G[0, 0] = 0.0
    return np.real(np.fft.ifft2(G))


def trunc(f, K1, L1):
    """truncate one-period grid values to |k| <= K1, |l| <= L1"""
    F = np.fft.fft2(f)
    kt = np.abs(np.fft.fftfreq(f.shape[0], 1.0 / f.shape[0]))
    lp = np.abs(np.fft.fftfreq(f.shape[1], 1.0 / f.shape[1]))
    F[(kt[:, None] > K1) | (lp[None, :] > L1)] = 0
    return np.real(np.fft.ifft2(F))


R = synth(C, np.zeros_like(C), ks, ls)
Z = synth(np.zeros_like(S), S, ks, ls)
Rt, Zt = synth(C, 0 * C, ks, ls, dt=1), synth(0 * S, S, ks, ls, dt=1)
Rp, Zp = synth(C, 0 * C, ks, ls, dp=1), synth(0 * S, S, ks, ls, dp=1)
print(f"torus on {Nt}x{Nf} ({time.time() - t0:.0f} s); omega {om:.16f}", flush=True)

# ------------------------------------------------------------------ total field and jets along K0
# all 4800 sources: base, rotations by -2 pi k / 5, stellarator images
def images(Pb, Db):
    Ps, Ds = [], []
    for k in range(NFP):
        a_ = -2 * np.pi * k / NFP
        Rz = np.array([[np.cos(a_), -np.sin(a_), 0], [np.sin(a_), np.cos(a_), 0], [0, 0, 1]])
        Ps.append(Pb @ Rz.T)
        Ds.append(Db @ Rz.T)
        Sm = np.diag([1.0, -1.0, -1.0])
        Ps.append((Pb @ Sm.T) @ Rz.T)
        Ds.append(-(Db @ Sm.T) @ Rz.T)
    return np.concatenate(Ps), np.concatenate(Ds)


Pall, Dall = images(Pb, Db)
cph, sph = np.cos(ph)[None, :], np.sin(ph)[None, :]
X = np.stack([R * cph, R * sph, Z], -1)            # (Nt, Nf, 3)
B = np.zeros((Nt, Nf, 3))
J = np.zeros((Nt, Nf, 3, 3))                         # J[..., i, k] = d B_i / d x_k
for j0 in range(0, len(Pall), 200):
    p = Pall[j0:j0 + 200]
    dd = Dall[j0:j0 + 200]
    r = X[:, :, None, :] - p[None, None, :, :]      # (Nt, Nf, s, 3)
    q = np.sum(r * r, -1)
    y = q ** -0.5
    y3, y5 = y ** 3, y ** 5
    dxr = np.cross(dd[None, None], r)
    B += np.sum(dxr * y3[..., None], 2)
    for kk in range(3):
        e = np.zeros(3)
        e[kk] = 1
        dxe = np.cross(dd, e)                          # (s, 3)
        J[:, :, :, kk] += np.sum(dxe[None, None] * y3[..., None] - 3 * dxr * (r[..., kk] * y5)[..., None], 2)
# cylindrical components and derivatives in R and Z at fixed phi
eR = np.stack([np.broadcast_to(cph, R.shape), np.broadcast_to(sph, R.shape), 0 * R], -1)
eP = np.stack([np.broadcast_to(-sph, R.shape), np.broadcast_to(cph, R.shape), 0 * R], -1)
eZ = np.stack([0 * R, 0 * R, 1 + 0 * R], -1)
BR, BP, BZ = [np.sum(B * e, -1) for e in (eR, eP, eZ)]
dB_dR = np.einsum("tpik,tpk->tpi", J, eR)
dB_dZ = np.einsum("tpik,tpk->tpi", J, eZ)
BR_R, BP_R, BZ_R = [np.sum(dB_dR * e, -1) for e in (eR, eP, eZ)]
BR_Z, BP_Z, BZ_Z = [np.sum(dB_dZ * e, -1) for e in (eR, eP, eZ)]
print(f"field along K0 ({time.time() - t0:.0f} s): |B_phi| in [{np.abs(BP).min():.3f}, {np.abs(BP).max():.3f}]",
      flush=True)

w0 = a.w0
d0 = a.d0frac * w0
jets = dict(bR0=BR, bP0=BP, bZ0=BZ, dRR0=BR_R, dRZ0=BR_Z, dPR0=BP_R, dPZ0=BP_Z, dZR0=BZ_R, dZZ0=BZ_Z)
J0 = {k: gnorm(v, w0) for k, v in jets.items()}
print("jet norms at w0:", {k: round(v, 3) for k, v in J0.items()}, flush=True)
kR0 = canon_norm(C, 0 * C, ks, NFP * ls, w0)

# ------------------------------------------------------------------ the field-line model at K0
U = 1.0 / BP
Wf = R * U
VR, VZ = Wf * BR, Wf * BZ
# DV = d(R B / B_phi)/d(R, Z) at fixed phi
WR = U - Wf * U * BP_R
WZ = -Wf * U * BP_Z
DV = np.array([[WR * BR + Wf * BR_R, WZ * BR + Wf * BR_Z], [WR * BZ + Wf * BZ_R, WZ * BZ + Wf * BZ_Z]])
sig = BP
gsig = (BP_R, BP_Z)
ER = om * Rt + Rp - VR
EZ = om * Zt + Zp - VZ
print(f"float residual of the dd torus: sup|E| {max(np.abs(ER).max(), np.abs(EZ).max()):.2e} (float floor)",
      flush=True)

# Ub: seed for 1/B_phi; its defect along K0
Ubg = trunc(U, *a.kub)
MU = gnorm(Ubg, w0)
thU0 = gnorm(1 - BP * Ubg, w0)

# frame: a, g = 1 / (sigma |a|^2) with seed gs
aR, aZ = Rt, Zt
a2 = aR * aR + aZ * aZ
g = 1.0 / (sig * a2)
gs = trunc(g, *a.kg)
qg = gnorm(1 - sig * a2 * gs, w0)
MGs = gnorm(gs, w0)
G0 = MGs + 2 * MGs * qg / (1 - qg) ** 2
A0 = max(gnorm(aR, w0), gnorm(aZ, w0))


def twist(bgrid):
    NR = -aZ * g + bgrid * aR
    NZ = aR * g + bgrid * aZ
    LNR, LNZ = Lop(NR), Lop(NZ)
    MR = LNR - (DV[0, 0] * NR + DV[0, 1] * NZ)
    MZ = LNZ - (DV[1, 0] * NR + DV[1, 1] * NZ)
    return sig * (MR * NZ - MZ * NR), NR, NZ


T0g, _, _ = twist(0 * g)
tau_raw = gmean(T0g)
bg = trunc(Linv(tau_raw - T0g), *a.kb)
Tg, NR, NZ = twist(bg)
tau0 = abs(gmean(Tg))
T0 = gnorm(Tg, w0 - d0)
N0 = max(gnorm(NR, w0), gnorm(NZ, w0))
xB = gnorm(bg, w0)
print(f"frame: A0 {A0:.3f} G0 {G0:.3f} (seed {MGs:.3f}, defect {qg:.2e}) N0 {N0:.3f} |b| {xB:.3f}", flush=True)
print(f"twist: raw mean {tau_raw:.5f}, raw |T| {gnorm(T0g, w0 - d0):.2f}; straightened mean {gmean(Tg):.5f}, "
      f"|T| {T0:.4f}, |T - tau| {gnorm(Tg - gmean(Tg), w0 - d0):.2e}", flush=True)
print(f"Ub: |Ub| {MU:.4f}, defect {thU0:.2e}", flush=True)

# ------------------------------------------------------------------ per-source data along K_ref (small seeds), moved to K0
Nts, Nfs = a.nths, a.nphs
ths = 2 * np.pi * np.arange(Nts) / Nts
phs = 2 * np.pi * np.arange(Nfs) / Nfs
kr1, kr2 = a.kr
keep = (np.abs(ks)[:, None] <= kr1) & (np.abs(NFP * ls)[None, :] <= kr2)
Cr = np.where(keep, C, 0.0)
Sr = np.where(keep, S, 0.0)
rref = max(canon_norm(C - Cr, 0 * C, ks, NFP * ls, w0), canon_norm(0 * S, S - Sr, ks, NFP * ls, w0))
Rs = synth(Cr, 0 * Cr, ks, ls, tt=ths, pp=phs)
Zs_ = synth(0 * Sr, Sr, ks, ls, tt=ths, pp=phs)
Xs = np.stack([Rs * np.cos(phs)[None], Rs * np.sin(phs)[None], Zs_], 0)
kts = np.fft.fftfreq(Nts, 1.0 / Nts)
nps = np.fft.fftfreq(Nfs, 1.0 / Nfs)
WTs = np.exp(w0 * (np.abs(kts)[:, None] + KAPPA * np.abs(nps)[None, :]))
mask = (np.abs(kts)[:, None] <= a.ky1) & (np.abs(nps)[None, :] <= a.ky2)


def fnorm(f):
    F = np.fft.fft2(f) / f.size
    return float(np.sum((np.abs(F.real) + np.abs(F.imag)) * WTs))


csw0 = math.exp(w0 * KAPPA)
srcdata = []
for j in range(len(Pb)):
    r = Xs - Pb[j][:, None, None]
    q = np.sum(r * r, 0)
    y = q ** -0.5
    F = np.fft.fft2(y)
    F[~mask] = 0
    Y = np.real(np.fft.ifft2(F))
    n1, n2, n3, MY = fnorm(r[0]), fnorm(r[1]), fnorm(r[2]), fnorm(Y)
    th_ref = fnorm(1 - q * Y * Y)
    bE1 = 2 * (n1 * csw0 + n2 * csw0 + n3) + rref * (2 * csw0 * csw0 + 1)
    srcdata.append(dict(r10=n1 + rref * csw0, r20=n2 + rref * csw0, r30=n3 + rref, MY=MY,
                        MD0=fnorm(q) + rref * bE1, th0=th_ref + rref * bE1 * MY * MY, y00=float(Y[0, 0]), d=Db[j]))
th0s = np.array([s["th0"] for s in srcdata])
print(f"sources along K_ref {a.kr} (r_ref {rref:.2e}), seeds {a.ky1} x {a.ky2}: th0 at K0 max {th0s.max():.3e}; "
      f"MY max {max(s['MY'] for s in srcdata):.3f} ({time.time() - t0:.0f} s)", flush=True)


# ------------------------------------------------------------------ the constants of FieldTaylor / FieldConst
def inv_eps(Y0, q):
    return 2 * Y0 * q / (1 - q) ** 2


def src_consts(s, r, hm, cs):
    """per-source constants of FieldBall / FieldTaylor at radius r (hm the step bound)"""
    rho1, rho2, rho3 = s["r10"] + r * cs, s["r20"] + r * cs, s["r30"] + r
    tE1b = 2 * (s["r10"] * cs + s["r20"] * cs + s["r30"]) + r * (2 * cs * cs + 1)
    bth = s["th0"] + r * tE1b * s["MY"] ** 2
    if bth >= 1:
        return None
    yb = s["MY"] + inv_eps(s["MY"], bth)
    ok_pos = inv_eps(s["MY"], bth) < s["y00"]
    tE1 = 2 * (rho1 * cs + rho2 * cs + rho3) + hm * (2 * cs * cs + 1)
    tP1 = tE1 * yb * yb
    tS2 = 1 + hm * tP1 / 2
    tT1 = 0.75 * tP1 ** 2 + 0.25 * hm * tP1 ** 3
    if hm * hm * tT1 >= 1:
        return None
    tRB = 2 * tS2 * tT1 / (1 - hm * hm * tT1) ** 2
    tA1 = (0.75 * tP1 ** 2 + hm * tP1 ** 3 / 8 + 3 * tS2 * tS2 * tRB + 3 * tS2 * hm * hm * tRB ** 2
           + hm ** 4 * tRB ** 3)
    tB1 = 1.5 * tP1 + hm * tA1
    d1, d2, d3 = np.abs(s["d"])
    tC = [d2 * rho3 + d3 * rho2, d3 * rho1 + d1 * rho3, d1 * rho2 + d2 * rho1]
    tD = [d2 + d3 * cs, d3 * cs + d1, d1 * cs + d2 * cs]
    y3 = yb ** 3

    def tXb(Cc, Dc):
        return Cc * y3 * tA1 + Dc * y3 * tB1 + 1.5 * Cc * (2 * cs * cs + 1) * y3 * yb * yb

    tRRb = (tXb(tC[0], tD[0]) + tXb(tC[1], tD[1])) * cs
    tRZb = tXb(tC[2], tD[2])
    tZb = tS2 + hm * hm * tRB
    tZ1 = tP1 / 2 + hm * tRB
    tZ5 = tZ1 * (1 + tZb + tZb ** 2 + tZb ** 3 + tZb ** 4)
    tZb5 = tZb ** 5

    def tJb(DVv, Cc, Dc, RE, DE):
        return DVv * y3 * tB1 + 3 * (y3 * yb * yb * (Cc * RE * tZ5 + (Cc * DE + Dc * RE + hm * Dc * DE) * tZb5))

    tDVR1, tDVR2, tDVR3 = d3 * cs, d3 * cs, d1 * cs + d2 * cs
    tRER, tDER = rho1 * cs + rho2 * cs, 2 * cs * cs
    tLRRb = (tJb(tDVR1, tC[0], tD[0], tRER, tDER) + tJb(tDVR2, tC[1], tD[1], tRER, tDER)) * cs
    tLRZb = (tJb(d2, tC[0], tD[0], rho3, 1) + tJb(d1, tC[1], tD[1], rho3, 1)) * cs
    tLZRb = tJb(tDVR3, tC[2], tD[2], tRER, tDER)
    tLZZb = tJb(0.0, tC[2], tD[2], rho3, 1)
    smallT = (hm * hm * tT1 < 1) and (hm * tP1 / 2 + hm * hm * tRB < 1)
    return dict(tRRb=tRRb, tRZb=tRZb, tLRRb=tLRRb, tLRZb=tLRZb, tLZRb=tLZRb, tLZZb=tLZZb, ok=ok_pos and smallT,
                bth=bth)


def model_consts(r):
    hm = 2 * r
    cs = math.exp(w0 * KAPPA * 1)
    per = [src_consts(s, r, hm, cs) for s in srcdata]
    if any(p is None or not p["ok"] for p in per):
        return None
    P2 = abs(NFP) * 2
    cR2R = P2 * sum(p["tRRb"] for p in per)
    cR2Z = P2 * sum(p["tRZb"] for p in per)
    cLRR = P2 * sum(p["tLRRb"] for p in per)
    cLRZ = P2 * sum(p["tLRZb"] for p in per)
    cLZR = P2 * sum(p["tLZRb"] for p in per)
    cLZZ = P2 * sum(p["tLZZb"] for p in per)
    bRR, bRZ = J0["dRR0"] + r * cLRR, J0["dRZ0"] + r * cLRZ
    bPR, bPZ = J0["dPR0"] + r * cLRR, J0["dPZ0"] + r * cLRZ
    bZR, bZZ = J0["dZR0"] + r * cLZR, J0["dZZ0"] + r * cLZZ
    dBR = (J0["dRR0"] + J0["dRZ0"]) * r + r * r * cR2R
    dBP = (J0["dPR0"] + J0["dPZ0"]) * r + r * r * cR2R
    dBZ = (J0["dZR0"] + J0["dZZ0"]) * r + r * r * cR2Z
    bBR, bBP, bBZ = J0["bR0"] + dBR, J0["bP0"] + dBP, J0["bZ0"] + dBZ
    kRb = kR0 + r
    thU = thU0 + dBP * MU
    if thU >= 1:
        return None
    Ubb = MU + inv_eps(MU, thU)
    LBR = bRR + bRZ + hm * cR2R
    LBP = bPR + bPZ + hm * cR2R
    LBZ = bZR + bZZ + hm * cR2Z
    LU = Ubb * Ubb * LBP
    cW = kRb * Ubb
    LW = Ubb + kRb * LU
    cUPR, LUPR = Ubb * bPR, LU * bPR + Ubb * cLRR
    cUPZ, LUPZ = Ubb * bPZ, LU * bPZ + Ubb * cLRZ
    cWR, LWR = Ubb + cW * cUPR, LU + (LW * cUPR + cW * LUPR)
    cWZ, LWZ = cW * cUPZ, LW * cUPZ + cW * LUPZ
    cmRR, LmRR = cWR * bBR + cW * bRR, LWR * bBR + cWR * LBR + (LW * bRR + cW * cLRR)
    cmRZ, LmRZ = cWZ * bBR + cW * bRZ, LWZ * bBR + cWZ * LBR + (LW * bRZ + cW * cLRZ)
    cmZR, LmZR = cWR * bBZ + cW * bZR, LWR * bBZ + cWR * LBZ + (LW * bZR + cW * cLZR)
    cmZZ, LmZZ = cWZ * bBZ + cW * bZZ, LWZ * bBZ + cWZ * LBZ + (LW * bZZ + cW * cLZZ)
    TMR = (kRb * Ubb * cR2R + kRb * bBR * (Ubb ** 3 * LBP ** 2 + Ubb ** 2 * cR2R)
           + LU * bBR + Ubb * LBR + kRb * LU * LBR + hm * LU * LBR)
    TMZ = (kRb * Ubb * cR2Z + kRb * bBZ * (Ubb ** 3 * LBP ** 2 + Ubb ** 2 * cR2R)
           + LU * bBZ + Ubb * LBZ + kRb * LU * LBZ + hm * LU * LBZ)
    return dict(kS=bBP, kS1=max(bPR, bPZ), kDV=max(cmRR, cmRZ, cmZR, cmZZ), kMV=max(cW * bBR, cW * bBZ),
                kM2=max(TMR, TMZ), kLD=max(LmRR, LmRZ, LmZR, LmZZ), kLS=LBP, cR2R=cR2R, cLRR=cLRR, thU=thU)


# ------------------------------------------------------------------ Diophantine constants of om
def dioph(om, P, qmax=20000):
    g = 1.0
    for q in range(1, qmax + 1):
        x = q * om / P
        g = min(g, q * P * abs(x - round(x)))
    gA = 1.0
    for q in range(1, qmax + 1):
        x = q * om
        gA = min(gA, q * abs(x - round(x)))
    return g, gA


gamma, gammaA = dioph(om, NFP)
print(f"Diophantine: gamma_5 {gamma:.4f}, gamma_all {gammaA:.4f}", flush=True)


# ------------------------------------------------------------------ the KAM inequalities
def kam(eps0, r, xA, xG, xN, xB_, xTm, xtau, mc):
    c = dict(cA=xA, cG=xG, cN=xN, cB=xB_, cS=mc["kS"], cS1=mc["kS1"], cD=mc["kDV"], cMV=mc["kMV"],
             cM2=mc["kM2"], cTm=xTm, ctau=xtau, cLS=mc["kLS"], cLD=mc["kLD"])
    d = d0
    lc = (1 + 1 / (E1 * d)) / gamma
    kdE = 1 / (E1 * d)
    kN = c["cN"]
    kH1 = c["cS"] * 2 * kN
    kH2 = c["cS"] * 2 * c["cA"]
    kW2 = lc * kH2
    kZ = (kH1 + c["cTm"] * kW2) / c["ctau"]
    kX2 = kW2 + kZ
    kR1 = kH1 + (c["cTm"] * kW2 + kZ * c["cTm"])
    kX1 = lc * kR1
    kP = kX1 * c["cA"] + kX2 * kN
    kAl = c["cS"] * 2 * kdE * kN
    kBe = c["cS"] * 2 * c["cA"] * kdE
    kC = 2 * c["cS1"] * 2 * c["cA"] ** 2 * c["cG"] + kAl
    kE = kAl * kX1 * c["cA"] + (kBe * kX1 + kC * kX2) * kN + c["cM2"] * kP * kP
    kdA = kdE * kP
    kU = c["cLS"] * kP * 2 * c["cA"] ** 2 + c["cS"] * 6 * c["cA"] * kdA
    kdG = 8 * c["cG"] ** 2 * kU
    kdN = kdG * 2 * c["cA"] + c["cG"] * kdA + c["cB"] * kdA
    kLd = (abs(om) + 1 / KAPPA) * (1 / (E1 * d / 2))
    kM = kLd * c["cN"] + 2 * c["cD"] * c["cN"]
    kdM = kLd * kdN + 2 * (c["cLD"] * kP * 2 * c["cN"] + c["cD"] * kdN)
    kW = 2 * kM * c["cN"]
    kdW = 2 * (kdM * 2 * c["cN"] + kM * kdN)
    kT = c["cLS"] * kP * 2 * kW + c["cS"] * kdW
    itA = kE
    conds = {
        "Hsmall itA*16*eps0<=1/2": itA * 16 * eps0 <= 0.5,
        "HcA": A0 + 2 * kdA * eps0 <= xA, "HcG": G0 + 2 * kdG * eps0 <= xG,
        "HcN": N0 + 2 * kdN * eps0 <= xN, "HcT": T0 + 2 * kT * eps0 <= xTm,
        "Hrr": 2 * kP * eps0 <= r, "Hctau2": xtau <= tau0 - 2 * kT * eps0,
        "Hsm_q0": xG * kU * eps0 <= 0.5, "Hsm_w0": kdW * eps0 <= kW,
    }
    return conds, dict(kE=kE, kP=kP, kT=kT, kU=kU, threshold=0.5 / (16 * itA))


print(f"\n==== w0 {w0}, d0 {d0:.5f}, eps0 target {a.eps0:g}", flush=True)
for r in [1e-12, 1e-10, 1e-8, 1e-6]:
    mc = model_consts(r)
    if mc is None:
        print(f"r {r:g}: source or Ub conditions fail")
        continue
    xA, xG, xN, xB_, xTm, xtau = 1.01 * A0, 1.01 * G0, 1.01 * N0, xB, 1.01 * T0, 0.99 * tau0
    conds, k = kam(a.eps0, r, xA, xG, xN, xB_, xTm, xtau, mc)
    print(f"r {r:g}: kS {mc['kS']:.3g} kS1 {mc['kS1']:.3g} kDV {mc['kDV']:.3g} kMV {mc['kMV']:.3g} "
          f"kM2 {mc['kM2']:.3g} kLD {mc['kLD']:.3g} kLS {mc['kLS']:.3g} | kE {k['kE']:.3g} kP {k['kP']:.3g} "
          f"threshold eps0 <= {k['threshold']:.3g}; 2 kP eps0 = {2 * k['kP'] * a.eps0:.2e}")
    print("   ", {kk: v for kk, v in conds.items() if not v} or "all conditions hold")
print(f"[done {time.time() - t0:.0f} s]")


# ================================================================== certified quantities (design estimates)
print("\n==== certificate design", flush=True)
wc = a.wc
# crude norms of the field and its R, Z derivatives along K0 at the crude strip (the source check, K_ref 8x80,
# seeds 8x70, w' = 0.3): B_R, B_phi, B_Z, dR B_R, dZ B_R, dR B_phi, dZ B_phi, dR B_Z, dZ B_Z
CR = dict(bR0=7.634e3, bP0=7.634e3, bZ0=4.867e3, dRR0=2.651e6, dRZ0=1.800e5, dPR0=2.651e6, dPZ0=1.800e5,
          dZR0=1.774e6, dZZ0=1.240e5)
LOG = math.log


def model_size(Mw, w, wcr, delta):
    """diamond D, grid N1 x M per period, modes, sum of weights, and the value accuracy the model needs, for a
    period-5 family with crude norm Mw at wcr certified to delta at strip w"""
    S = 10 * LOG(4 * Mw / delta) / (wcr - w) / 10  # size cut: e^(-(wcr-w) S) Mw <= delta/4
    D = int(math.ceil(10 * S))
    K1 = D // 10
    K2 = D // NFP
    # modes of the diamond and their weights
    kk = np.arange(-K1, K1 + 1)[:, None]
    ll = np.arange(-K2, K2 + 1)[None, :]
    inside = (10 * np.abs(kk) + NFP * np.abs(ll)) <= D
    wtd = np.exp(w * (np.abs(kk) + KAPPA * NFP * np.abs(ll))) * inside
    swt = float(wtd.sum())
    nmod = int(inside.sum())
    # aliasing: sum 2 Mw (e^(-wcr (N1-|k|)) + e^(-wcr kappa (5M - 5|l|))) wt <= delta/4
    N1 = K1 + 1
    while True:
        ea = np.exp(-wcr * (N1 - np.abs(kk)))
        if 2 * Mw * float((ea * wtd).sum()) <= delta / 8:
            break
        N1 += 1
    Mg = K2 + 1
    while True:
        eb = np.exp(-wcr * KAPPA * NFP * (Mg - np.abs(ll)))
        if 2 * Mw * float((eb * wtd).sum()) <= delta / 8:
            break
        Mg += 1
    return dict(D=D, K1=K1, K2=K2, N1=N1, M=Mg, pts=N1 * Mg, modes=nmod, swt=swt, eps_val=delta / 4 / swt)


# jet approximants
kj1, kj2 = a.kj
Jfin = {k: trunc(v, kj1, kj2) for k, v in jets.items()}
eJ = {k: gnorm(jets[k] - Jfin[k], w0) for k in jets}
nJfin = {k: gnorm(Jfin[k], w0) for k in jets}
nJfin_c = {k: gnorm(Jfin[k], wc) for k in jets}
print("jet approximants", a.kj, ": e_J(w0) max", f"{max(eJ.values()):.2e}",
      "| |J_fin|(w0)", {k: round(v, 3) for k, v in nJfin.items()}, flush=True)
for k in ("bP0", "dRR0"):
    ms = model_size(CR[k] + nJfin_c[k], w0, wc, max(1e-7, 0.1 * eJ[k]))
    print(f"  model of {k} - J_fin: {ms}", flush=True)

# U and g
thU_true = thU0
eU = MU * thU_true / (1 - thU_true)
ms = model_size(1 + CR["bP0"] * gnorm(Ubg, wc), w0, wc, 1e-9)
print(f"U: Ub box {a.kub}, theta_U {thU_true:.2e}, |U - Ub| <= {eU:.2e}; model {ms}", flush=True)
a2c = gnorm(a2, wc)
eg_true = gnorm(g - gs, w0)
eg_cert = MGs * qg / (1 - qg)
ms = model_size(1 + CR["bP0"] * a2c * gnorm(gs, wc), w0, wc, 0.1 * qg)
print(f"g: gs box {a.kg}, theta_g {qg:.2e}, |g - gs| true {eg_true:.2e} cert {eg_cert:.2e}; model {ms}", flush=True)

# E0
# exact norms of L K_R and K_R at the crude strip, from the coefficients
nfull = NFP * ls
LKn = float(np.sum(np.abs((om * ks[:, None] + nfull[None, :]) * C) * wtn(wc, ks[:, None], nfull[None, :])))
KRn = canon_norm(C, 0 * C, ks, nfull, wc)
MwF = CR["bP0"] * LKn + KRn * CR["bR0"]
print(f"  |L K_R|(w') {LKn:.3f}, |K_R|(w') {KRn:.3f}", flush=True)
ms = model_size(MwF, w0, wc, 1e-21)
print(f"E0: Mw_F {MwF:.3e}; model {ms}; kernel evaluations (half grid x 4800) {ms['pts'] * 2400:.3e}", flush=True)

# twist decomposition: T_fin from the approximants
UbG = Ubg
WfF = R * UbG
WRF = UbG - WfF * UbG * Jfin["dPR0"]
WZF = -WfF * UbG * Jfin["dPZ0"]
DVF = np.array([[WRF * Jfin["bR0"] + WfF * Jfin["dRR0"], WZF * Jfin["bR0"] + WfF * Jfin["dRZ0"]],
                [WRF * Jfin["bZ0"] + WfF * Jfin["dZR0"], WZF * Jfin["bZ0"] + WfF * Jfin["dZZ0"]]])
sigF = Jfin["bP0"]
NRF = -aZ * gs + bg * aR
NZF = aR * gs + bg * aZ
LNRF, LNZF = Lop(NRF), Lop(NZF)
MRF = LNRF - (DVF[0, 0] * NRF + DVF[0, 1] * NZF)
MZF = LNZF - (DVF[1, 0] * NRF + DVF[1, 1] * NZF)
TF = sigF * (MRF * NZF - MZF * NRF)
wd = w0 - d0
nTF, mTF = gnorm(TF, wd), gmean(TF)
nN, nNF = max(gnorm(NR, w0), gnorm(NZ, w0)), max(gnorm(NRF, w0), gnorm(NZF, w0))
nkm = max(gnorm(Lop(NR) - (DV[0, 0] * NR + DV[0, 1] * NZ), wd), gnorm(Lop(NZ) - (DV[1, 0] * NR + DV[1, 1] * NZ), wd))
nkmF = max(gnorm(MRF, wd), gnorm(MZF, wd))
nDVF = max(gnorm(DVF[i, j], w0) for i in range(2) for j in range(2))
nsigF = gnorm(sigF, w0)
Acomp = max(gnorm(aR, w0), gnorm(aZ, w0))
cL = (abs(om) + 1 / KAPPA) / (E1 * d0)
eS = eJ["bP0"]
# |DV - DV_F| from e_J and e_U through the products of lDV (norms at w0)
nKR = gnorm(R, w0)
nU = MU + eU
nW = nKR * nU
nJ = {k: nJfin[k] + eJ[k] for k in jets}
eW = nKR * eU
eUPR = eU * nJ["dPR0"] + MU * eJ["dPR0"]
eUPZ = eU * nJ["dPZ0"] + MU * eJ["dPZ0"]
eWR = eU + eW * nU * nJ["dPR0"] + nKR * MU * eUPR
eWZ = eW * nU * nJ["dPZ0"] + nKR * MU * eUPZ
nWR = nU + nW * nU * nJ["dPR0"]
nWZ = nW * nU * nJ["dPZ0"]
eDV = max(eWR * nJ["bR0"] + nWR * eJ["bR0"] + eW * nJ["dRR0"] + nW * eJ["dRR0"],
          eWZ * nJ["bR0"] + nWZ * eJ["bR0"] + eW * nJ["dRZ0"] + nW * eJ["dRZ0"],
          eWR * nJ["bZ0"] + nWR * eJ["bZ0"] + eW * nJ["dZR0"] + nW * eJ["dZR0"],
          eWZ * nJ["bZ0"] + nWZ * eJ["bZ0"] + eW * nJ["dZZ0"] + nW * eJ["dZZ0"])
eN = eg_cert * Acomp
ekm = cL * 2 * eN + 2 * eDV * nN + 2 * nDVF * eN
eT = eS * 2 * nkm * nN + nsigF * 2 * (ekm * nN + nkmF * eN)
T0c, tau0c = nTF + eT, abs(mTF) - eT
print(f"twist: |T_fin| {nTF:.4f} mean {mTF:.5f}; bound |T - T_fin| <= {eT:.3e} "
      f"(eS {eS:.1e}, eDV {eDV:.1e}, eN {eN:.1e}, cL {cL:.0f}, |kmln| {nkm:.1f}, |kmln_F| {nkmF:.1f}) "
      f"=> T0 {T0c:.4f}, tau0 {tau0c:.4f}; true |T| {T0:.4f}, tau {tau0:.5f}", flush=True)
ms = model_size(1e6, wd, wc, 1e-4)
print(f"  T_fin model at w0 - d0 from a crude 1e6 at w': {ms}", flush=True)

# the KAM inequalities with the certified numbers
J0c = {k: nJfin[k] + eJ[k] for k in jets}
N0c = nNF + eN
G0c = MGs + eg_cert
print(f"certified: N0 {N0c:.3f} (true {N0:.3f}), G0 {G0c:.3f} (true {G0:.3f}), jets {J0c}", flush=True)
J0.update(J0c)
N0, G0, T0, tau0 = N0c, G0c, T0c, tau0c
for r in [1e-12, 1e-10, 1e-8, 1e-6]:
    mc = model_consts(r)
    if mc is None:
        print(f"r {r:g}: source or Ub conditions fail")
        continue
    xA, xG, xN, xB_, xTm, xtau = 1.01 * A0, 1.01 * G0, 1.01 * N0, xB, 1.01 * T0, 0.99 * tau0
    conds, k = kam(a.eps0, r, xA, xG, xN, xB_, xTm, xtau, mc)
    print(f"r {r:g}: kM2 {mc['kM2']:.3g} kLD {mc['kLD']:.3g} | kE {k['kE']:.3g} kP {k['kP']:.3g} "
          f"threshold eps0 <= {k['threshold']:.3g}")
    print("   ", {kk: v for kk, v in conds.items() if not v} or "all conditions hold")
print(f"[design done {time.time() - t0:.0f} s]")
