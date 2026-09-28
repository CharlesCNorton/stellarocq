"""Draw Figure 1 of the paper: python paper/fig_convergence.py writes paper/fig_convergence.pdf.

(a) The certified error max |x_h - x*| of the half-grid scheme on the manufactured
mappings (gen/mms_colloc.py). (b) The harmonics of the radial force r_s on the
surface iota = 1/2 of the rippled tokamak: the certified enclosures of the (2,1)
harmonic (Harmonic.dharm_correct, gen/forced_sheet.py) and the floating-point values
of the others that examples/forced_current_sheet.py of the VMEC++ branch prints.
"""
import pathlib

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

MMS_3D = {9: 2.73432936716e-6, 17: 7.16912169671e-7, 33: 1.83032584737e-7, 65: 4.60748183004e-8}
MMS_ASYM = {9: 2.69073057006e-5, 17: 7.20667052904e-6, 33: 1.86266877275e-6}
NS = [65, 129, 257]
H21 = [(8.3484e-5, 8.4498e-5), (8.6749e-5, 9.0712e-5), (6.1921e-5, 7.7586e-5)]
OTHERS = {
    "(2,0)": [3.0753e-3, 7.7319e-4, 1.9271e-4],
    "(1,0)": [8.1449e-4, 2.1161e-4, 3.9903e-5],
    "(3,1)": [8.3394e-5, 6.6957e-5, 5.0873e-5],
}

plt.rcParams.update({"font.family": "serif", "mathtext.fontset": "cm", "font.size": 9})
fig, (a, b) = plt.subplots(1, 2, figsize=(6.5, 2.6), constrained_layout=True)

for data, mark, label in ((MMS_3D, "o", "three-dimensional"), (MMS_ASYM, "s", "asymmetric")):
    ns = np.array(list(data))
    a.loglog(ns - 1, list(data.values()), mark + "-", ms=4, lw=1, label=label)
x = np.array([8, 64])
a.loglog(x, 2.4e-6 * (x / 8.0) ** -2, "k--", lw=0.8, label=r"$\propto h^2$")
a.set_xticks([8, 16, 32, 64])
a.set_xticklabels(["9", "17", "33", "65"])
a.minorticks_off()
a.set_xlabel("surfaces")
a.set_ylabel(r"$\max|x_h - x^*|$")
a.set_title("(a) manufactured mappings", fontsize=9)
a.legend(frameon=False, fontsize=8)

ns = np.array(NS) - 1
lo = np.array([p[0] for p in H21])
hi = np.array([p[1] for p in H21])
b.fill_between(ns, lo, hi, color="C3", alpha=0.35, lw=0)
b.loglog(ns, 0.5 * (lo + hi), "D-", color="C3", ms=4, lw=1, label="(2,1), certified")
for (name, vals), mark in zip(OTHERS.items(), ("o", "s", "^")):
    b.loglog(ns, vals, mark + ":", ms=4, lw=1, label=name)
b.set_xticks(list(ns))
b.set_xticklabels([str(n) for n in NS])
b.minorticks_off()
b.set_xlabel("surfaces")
b.set_ylabel(r"$|$harmonic of $r_s|$")
b.set_title(r"(b) rippled tokamak, $\iota = 1/2$", fontsize=9)
b.legend(frameon=False, fontsize=7, ncol=2)

fig.savefig(pathlib.Path(__file__).with_name("fig_convergence.pdf"))
