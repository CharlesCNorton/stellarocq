"""The Newton step of KAMStep.v, run in floating point on a W7-X torus of the
discrete coil field: frame a = d_t K, N = g J a + b a (b straightens the twist),
eta = sigma (E ^ N, a ^ E), torsion T = sigma (L N - DV N) ^ N, xi2 = -L^-1 eta2 +
xi20, xi1 = -L^-1 (eta1 + T xi2), K' = K + xi1 a + xi2 N. Prints the error after
each step and, at the end, the constants of KAMBound at the given strips.

    python gen/kam_newton.py TORUS.npz COILS.npz OUT.npz [--omega W] [--nth 64 --nph 128]
"""
import argparse
import math
import time

import numpy as np

NFP = 5
ap = argparse.ArgumentParser()
ap.add_argument("torus")
ap.add_argument("coils")
ap.add_argument("out")
ap.add_argument("--omega", type=float, default=None)
ap.add_argument("--nth", type=int, default=64)
ap.add_argument("--nph", type=int, default=128)
ap.add_argument("--steps", type=int, default=6)
ap.add_argument("--kappa", type=float, default=0.1)
ap.add_argument("--w", type=float, nargs="+", default=[0.03, 0.05, 0.08])
a = ap.parse_args()

t = np.load(a.torus)
modes, Rc, Zs = t["modes"], t["Rc"], t["Zs"]
om = float(t["omega"]) if a.omega is None else a.omega
c = np.load(a.coils)
P, D = c["points"], c["tangents"]
keep = np.linalg.norm(D, axis=1) > 0
P, D = P[keep], D[keep]
Nt, Nf = a.nth, a.nph
th = 2 * np.pi * np.arange(Nt) / Nt
ph = (2 * np.pi / NFP) * np.arange(Nf) / Nf
TH, PH = np.meshgrid(th, ph, indexing="ij")
kt = np.fft.fftfreq(Nt, 1.0 / Nt)[:, None]
kp = (np.fft.fftfreq(Nf, 1.0 / Nf) * NFP)[None, :]
cp, sp = np.cos(PH), np.sin(PH)

# the initial torus on the grid
ang = modes[:, 0][:, None, None] * TH[None] - modes[:, 1][:, None, None] * PH[None]
R = np.tensordot(Rc, np.cos(ang), 1)
Z = np.tensordot(Zs, np.sin(ang), 1)
del ang


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


def dealias(f, frac=2 / 3):
    """Drop the top third of the modes in both angles."""
    F = spec(f)
    F[np.abs(kt[:, 0]) > frac * Nt / 2, :] = 0
    F[:, np.abs(kp[0]) > frac * NFP * Nf / 2] = 0
    return real(F)


def field(X, second=False):
    N = len(X)
    B = np.zeros((N, 3))
    J = np.zeros((N, 3, 3))
    H = np.zeros((N, 3, 3, 3)) if second else None
    eye = np.eye(3)
    dxe = np.transpose(np.cross(D[:, None, :], eye[None, :, :]), (0, 2, 1))  # (S, a, b)
    for i0 in range(0, N, 48):
        x = X[i0:i0 + 48]
        r = x[:, None, :] - P[None]
        q = np.einsum("nsk,nsk->ns", r, r)
        q32, q52 = q ** -1.5, q ** -2.5
        dxr = np.cross(D[None], r)
        B[i0:i0 + 48] = np.einsum("nsa,ns->na", dxr, q32)
        J[i0:i0 + 48] = (np.einsum("sab,ns->nab", dxe, q32)
                         - 3 * np.einsum("nsa,nsb,ns->nab", dxr, r, q52))
        if second:
            q72 = q ** -3.5
            H[i0:i0 + 48] = (-3 * np.einsum("sab,nsc,ns->nabc", dxe, r, q52)
                             - 3 * np.einsum("sac,nsb,ns->nabc", dxe, r, q52)
                             - 3 * np.einsum("nsa,bc,ns->nabc", dxr, eye, q52)
                             + 15 * np.einsum("nsa,nsb,nsc,ns->nabc", dxr, r, r, q72))
    return B, J, H


def fields_at(R, Z, second=False):
    X = np.stack([(R * cp).ravel(), (R * sp).ravel(), Z.ravel()], 1)
    B, J, H = field(X, second)
    eR = np.stack([cp.ravel(), sp.ravel(), 0 * cp.ravel()], 1)
    eP = np.stack([-sp.ravel(), cp.ravel(), 0 * cp.ravel()], 1)
    eZ = np.tile([0.0, 0.0, 1.0], (len(X), 1))
    E = [eR, eZ]
    sh = R.shape
    comp = lambda v, e: np.einsum("na,na->n", v, e).reshape(sh)            # noqa: E731
    dB = lambda eo, ei: np.einsum("na,nab,nb->n", eo, J, ei).reshape(sh)   # noqa: E731
    BR, BP, BZ = comp(B, eR), comp(B, eP), comp(B, eZ)
    sig = BP
    gs = [dB(eP, e) for e in E]
    Vn = [R * BR, R * BZ]
    dVn = [[dB(eR, e) * R + (BR if k == 0 else 0) for k, e in enumerate(E)],
           [dB(eZ, e) * R + (BZ if k == 0 else 0) for k, e in enumerate(E)]]
    V = [v / sig for v in Vn]
    DV = [[(dVn[i][k] * sig - Vn[i] * gs[k]) / sig ** 2 for k in range(2)] for i in range(2)]
    out = dict(sig=sig, gs=gs, V=V, DV=DV)
    if second:
        # second derivatives of V in R and Z by the quotient rule
        dd = lambda eo, e1, e2: np.einsum("na,nabc,nb,nc->n", eo, H, e1, e2).reshape(sh)  # noqa
        d2B = {(i, j, k): dd(eo, E[j], E[k]) for i, eo in enumerate([eR, eZ, eP])
               for j in range(2) for k in range(2)}
        d2V = [[[None] * 2 for _ in range(2)] for _ in range(2)]
        for i in range(2):
            Bi = [BR, BZ][i]
            dBi = [dB([eR, eZ][i], e) for e in E]
            for j in range(2):
                for k in range(2):
                    # N = R B_i, S = B_phi; V = N / S
                    Nj = dBi[j] * R + (Bi if j == 0 else 0)
                    Nk = dBi[k] * R + (Bi if k == 0 else 0)
                    Njk = d2B[(i, j, k)] * R + (dBi[k] if j == 0 else 0) + (dBi[j] if k == 0 else 0)
                    S, Sj, Sk, Sjk = sig, gs[j], gs[k], d2B[(2, j, k)]
                    Nn = Vn[i]
                    d2V[i][j][k] = (Njk / S - (Nj * Sk + Nk * Sj) / S ** 2
                                    - Nn * Sjk / S ** 2 + 2 * Nn * Sj * Sk / S ** 3)
        out["d2V"] = d2V
    return out


def wedge(u, v):
    return u[0] * v[1] - u[1] * v[0]


def wnorm(f, w, kap=a.kappa):
    F = np.fft.fft2(f) / f.size
    wt = np.exp(w * (np.abs(kt) + kap * np.abs(kp)))
    return float(np.sum((np.abs(F.real) + np.abs(F.imag)) * wt))


def step(R, Z, b=None, report=False):
    aR, aZ = dth(R), dth(Z)
    fz = fields_at(R, Z, second=report)
    sig, V, DV = fz["sig"], fz["V"], fz["DV"]
    ER = om * aR + dph(R) - V[0]
    EZ = om * aZ + dph(Z) - V[1]
    g = 1.0 / (sig * (aR ** 2 + aZ ** 2))
    if b is None:
        b = np.zeros_like(R)
    NR = -aZ * g + b * aR
    NZ = aR * g + b * aZ
    eta1 = sig * wedge((ER, EZ), (NR, NZ))
    eta2 = sig * wedge((aR, aZ), (ER, EZ))
    LNR = Lop(NR) - (DV[0][0] * NR + DV[0][1] * NZ)
    LNZ = Lop(NZ) - (DV[1][0] * NR + DV[1][1] * NZ)
    T = sig * wedge((LNR, LNZ), (NR, NZ))
    tau = T.mean()
    w2 = -Linv(eta2)
    xi20 = -(eta1.mean() + (T * w2).mean()) / tau
    xi2 = w2 + xi20
    rhs = eta1 + T * xi2
    xi1 = -Linv(rhs - rhs.mean())
    info = dict(E=max(np.abs(ER).max(), np.abs(EZ).max()), tau=tau,
                eta2mean=eta2.mean(), Tdev=np.abs(T - tau).max(),
                Ew=[max(wnorm(ER, w), wnorm(EZ, w)) for w in a.w])
    if report:
        info.update(aR=aR, aZ=aZ, sig=sig, g=g, NR=NR, NZ=NZ, T=T, DV=DV,
                    gs=fz["gs"], d2V=fz["d2V"], ER=ER, EZ=EZ)
    return R + xi1 * aR + xi2 * NR, Z + xi1 * aZ + xi2 * NZ, T, tau, info


t0 = time.time()
for k in range(a.steps):
    Rn, Zn, T, tau, info = step(R, Z)
    print(f"step {k}: sup|E| {info['E']:.3e}, |E|_w {' '.join(f'{x:.2e}' for x in info['Ew'])}, "
          f"tau {tau:+.6e}, <eta2> {info['eta2mean']:+.1e}, sup|T - tau| {info['Tdev']:.3e} "
          f"({time.time() - t0:.0f} s)", flush=True)
    R, Z = dealias(Rn), dealias(Zn)

# the normal that straightens the twist at the final torus, held fixed
_, _, T, tau, info = step(R, Z)
b = dealias(-Linv(T - tau))
_, _, T, tau, info = step(R, Z, b, report=True)
print(f"final: sup|E| {info['E']:.3e}, |E|_w {' '.join(f'{x:.2e}' for x in info['Ew'])}, "
      f"tau {tau:+.6e}, sup|T - tau| {info['Tdev']:.3e}")
np.savez(a.out, R=R, Z=Z, b=b, omega=om, nth=Nt, nph=Nf)


def gamma_of(x, qmax=100000):
    q = np.arange(1, qmax + 1)
    d = np.abs(q * x - np.round(q * x))
    return float((q * d).min())


gam = gamma_of(om)
gam5 = 5 * gamma_of(om / 5)
print(f"gamma: all n {gam:.4f}, n in 5Z {gam5:.4f}")
aR, aZ, sig, g = info["aR"], info["aZ"], info["sig"], info["g"]
NR, NZ, DV, d2V, gs = info["NR"], info["NZ"], info["DV"], info["d2V"], info["gs"]
e1 = math.e
for w in a.w:
    cA = max(wnorm(aR, w), wnorm(aZ, w))
    cS = wnorm(sig, w)
    cS1 = max(wnorm(gs[0], w), wnorm(gs[1], w))
    cG = wnorm(g, w)
    cN = max(wnorm(NR, w), wnorm(NZ, w))
    cD = max(wnorm(DV[i][k], w) for i in range(2) for k in range(2))
    cM2 = 2 * max(wnorm(d2V[i][j][k], w) for i in range(2) for j in range(2) for k in range(2))
    cB = wnorm(b, w)
    for dfrac in (7, 10):
        d = w / dfrac
        cT = abs(tau) + wnorm(T - tau, w - d)
        kdE = 1 / (e1 * d)
        for gm, gl in ((gam, "all n"), (gam5, "5Z")):
            lc = (1 + kdE) / gm
            kH1 = cS * 2 * cN
            kH2 = cS * 2 * cA
            kW2 = lc * kH2
            kZ = (kH1 + cT * kW2) / abs(tau)
            kX2 = kW2 + kZ
            kR1 = kH1 + cT * kW2 + kZ * cT
            kX1 = lc * kR1
            kP = kX1 * cA + kX2 * cN
            kAl = cS * 2 * kdE * cN
            kBe = cS * 2 * cA * kdE
            kC = 2 * cS1 * 2 * cA * cA * cG + kAl
            kE = kAl * kX1 * cA + (kBe * kX1 + kC * kX2) * cN + cM2 * kP * kP
            print(f"w {w} d {d:.4f} [{gl}]: cA {cA:.3g} cS {cS:.3g} cG {cG:.3g} cB {cB:.3g} "
                  f"cN {cN:.3g} cT {cT:.3g} tau {abs(tau):.3g} cD {cD:.3g} cM2 {cM2:.3g} | "
                  f"kP {kP:.3g} kE {kE:.3g} -> eps0 <= {1 / (32 * kE):.2e}")
