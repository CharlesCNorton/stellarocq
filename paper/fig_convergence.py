"""Write Figure 1 of the paper as LaTeX picture-mode code:

    python paper/fig_convergence.py > figure.tex

stellarocq.tex carries the output inline, drawn with the picture environment of
the LaTeX kernel alone. (a) The certified error max |x_h - x*| of the half-grid
scheme on the manufactured mappings (gen/mms_colloc.py). (b) The harmonics of the
radial force r_s on the surface iota = 1/2 of the rippled tokamak: the (2,1)
harmonic certified with its rows at 256 bits (WideHarm.wdharm_b_correct,
gen/forced_sheet.py hcert, main --dharm-wide 256) and the floating-point values
of the others that gen/forced_sheet.py spectrum prints for the same files.
(c) The (2,1) harmonic on a linear scale: its binary64 enclosures
(Harmonic.dharm_correct, main --dharm) and its 256-bit enclosures.
"""
import math

MMS_3D = {9: 2.73432936829e-6, 17: 7.16912170772e-7, 33: 1.83032585742e-7, 65: 4.6074819334e-8}
MMS_ASYM = {9: 2.69073057043e-5, 17: 7.20667053290e-6, 33: 1.86266877703e-6}
NS = [65, 129, 257, 513, 1025]
H21_WIDE = [(8.920812481048862e-05, 8.920812481066525e-05),
            (8.931013968774432e-05, 8.931013968779015e-05),
            (7.456678235767228e-05, 7.456678235768514e-05),
            (5.3557117409117485e-05, 5.3557117409122974e-05),
            (3.808406728292835e-05, 3.808406728293221e-05)]
H21_B64 = [(8.87010886598797477e-05, 8.97151939439499611e-05),
           (8.73273640978774438e-05, 9.12929283797295302e-05),
           (6.67393171125321417e-05, 8.23942478145557795e-05)]
OTHERS = {
    "(2,0)": [3.070877e-3, 7.704611e-4, 1.934922e-4, 4.887547e-5, 1.274317e-5],
    "(1,0)": [8.162769e-4, 2.041000e-4, 4.926426e-5, 1.326267e-5, 5.875867e-6],
    "(3,1)": [8.633027e-5, 6.979149e-5, 5.337462e-5, 3.814427e-5, 2.646110e-5],
}

H = 110.0     # height of every plot box, in pt
Y0 = 30.0     # its lower edge within the picture
LEFT = 34.0   # room for the tick labels left of a box
out = []


def f(v):
    return f"{v:.1f}".rstrip("0").rstrip(".")


def put(x, y, what):
    out.append(f"\\put({f(x)},{f(y)}){{{what}}}")


def seg(a, b, dots=None):
    """A straight segment as a quadratic Bezier with its control point midway."""
    (x1, y1), (x2, y2) = a, b
    n = "" if dots is None else f"[{dots}]"
    out.append(f"\\qbezier{n}({f(x1)},{f(y1)})({f((x1 + x2) / 2)},{f((y1 + y2) / 2)})({f(x2)},{f(y2)})")


def dotted(a, b):
    seg(a, b, max(2, int(math.dist(a, b) / 2.5)))


def dashed(a, b, on=4.0, off=3.0):
    d = math.dist(a, b)
    t = 0.0
    while t < d:
        s = min(t + on, d)
        p = (a[0] + (b[0] - a[0]) * t / d, a[1] + (b[1] - a[1]) * t / d)
        q = (a[0] + (b[0] - a[0]) * s / d, a[1] + (b[1] - a[1]) * s / d)
        seg(p, q)
        t = s + off


LINES = {"solid": seg, "dotted": dotted, "dashed": dashed}


def marker(kind, x, y):
    if kind == "disc":
        put(x, y, "\\circle*{3}")
    elif kind == "ring":
        put(x, y, "\\circle{3.5}")
    elif kind == "square":
        put(x - 1.5, y - 1.5, "\\rule{3pt}{3pt}")
    elif kind == "diamond":
        put(x, y, "\\makebox(0,0){$\\scriptstyle\\diamond$}")
    elif kind == "triangle":
        put(x, y, "\\makebox(0,0){$\\scriptscriptstyle\\triangle$}")


def frame(x0, w, title, ylabel):
    put(x0, Y0, f"\\line(1,0){{{f(w)}}}")
    put(x0, Y0 + H, f"\\line(1,0){{{f(w)}}}")
    put(x0, Y0, f"\\line(0,1){{{f(H)}}}")
    put(x0 + w, Y0, f"\\line(0,1){{{f(H)}}}")
    put(x0 + w / 2, 4, "\\makebox(0,0)[b]{\\footnotesize surfaces}")
    put(x0 + w / 2, Y0 + H + 20, f"\\makebox(0,0)[b]{{\\footnotesize {title}}}")
    put(x0, Y0 + H + 5, f"\\makebox(0,0)[bl]{{\\scriptsize {ylabel}}}")


def xticks(x0, w, X, xs, labels):
    for v, lab in zip(xs, labels):
        put(X(v), Y0, "\\line(0,1){3}")
        put(X(v), Y0 + H - 3, "\\line(0,1){3}")
        put(X(v), Y0 - 4, f"\\makebox(0,0)[t]{{\\scriptsize {lab}}}")


def yticks(x0, w, Y, values, labels):
    for v, lab in zip(values, labels):
        y = Y(v)
        put(x0, y, "\\line(1,0){3}")
        put(x0 + w - 3, y, "\\line(1,0){3}")
        put(x0 - 3, y, f"\\makebox(0,0)[r]{{\\scriptsize {lab}}}")


def legend(x0, w, entries, width):
    lx, ly = x0 + w - width, Y0 + H - 9
    for label, style, mark in entries:
        LINES[style]((lx, ly), (lx + 12, ly))
        if mark:
            marker(mark, lx + 6, ly)
        put(lx + 15, ly, f"\\makebox(0,0)[l]{{\\scriptsize {label}}}")
        ly -= 10


def logpanel(x0, w, xlo, xhi, xs, xlabels, ylo, yhi, decades, title, ylabel, series, entries, width):
    X = lambda v: x0 + (v - xlo) / (xhi - xlo) * w
    Y = lambda v: Y0 + (math.log10(v) - ylo) / (yhi - ylo) * H
    frame(x0, w, title, ylabel)
    xticks(x0, w, X, xs, xlabels)
    yticks(x0, w, Y, [10.0 ** e for e in decades], [f"$10^{{{e}}}$" for e in decades])
    for pts, style, mark in series:
        pts = [(X(x), Y(y)) for x, y in pts]
        for a, b in zip(pts, pts[1:]):
            LINES[style](a, b)
        for x, y in pts:
            marker(mark, x, y)
    legend(x0, w, entries, width)


lg = lambda n: math.log2(n - 1)
xb = [lg(n) for n in NS]
mid = [0.5 * (lo + hi) for lo, hi in H21_WIDE]

# (a) the certified error of the scheme on the manufactured mappings
xa = LEFT
logpanel(xa, 120.0, lg(9) - 0.25, lg(65) + 0.25, [lg(n) for n in MMS_3D], list(MMS_3D), -7.9, -4.2, [-7, -6, -5],
         "(a) manufactured mappings", "$\\max|x_h-x^*|$",
         [([(lg(n), v) for n, v in MMS_3D.items()], "solid", "disc"),
          ([(lg(n), v) for n, v in MMS_ASYM.items()], "solid", "square"),
          ([(lg(9), 1.3e-6), (lg(65), 1.3e-6 / 64)], "dashed", None)],
         [("3D", "solid", "disc"), ("asymmetric", "solid", "square"), ("$\\propto h^2$", "dashed", None)], 62.0)

# (b) the harmonics of r_s on the rational surface, with a line falling as h^(1/2)
xb0 = xa + 120.0 + 12.0 + LEFT
ref = 1.7 * mid[-1]
logpanel(xb0, 120.0, xb[0] - 0.3, xb[-1] + 0.3, xb, NS, -5.6, -2.2, [-5, -4, -3],
         "(b) rippled tokamak, $\\iota=1/2$", "harmonic of $r_s$",
         [(list(zip(xb, mid)), "solid", "diamond")]
         + [(list(zip(xb, vals)), "dotted", mark)
            for vals, mark in zip(OTHERS.values(), ("ring", "square", "triangle"))]
         + [([(xb[2], ref * 2 ** ((xb[-1] - xb[2]) / 2)), (xb[-1], ref)], "dashed", None)],
         [("(2,1)", "solid", "diamond"), ("(2,0)", "dotted", "ring"),
          ("(1,0)", "dotted", "square"), ("(3,1)", "dotted", "triangle"),
          ("$\\propto h^{1/2}$", "dashed", None)], 44.0)

# (c) the (2,1) harmonic on a linear scale: binary64 enclosures and 256-bit values
xc0 = xb0 + 120.0 + 12.0 + LEFT
wc = 465.0 - xc0
Xc = lambda v: xc0 + (v - xb[0] + 0.5) / (xb[-1] - xb[0] + 1.0) * wc
Yc = lambda v: Y0 + (v - 3.2e-5) / (9.6e-5 - 3.2e-5) * H
frame(xc0, wc, "(c) certified $(2,1)$", "$10^{-5}$")
xticks(xc0, wc, Xc, xb, NS)
yticks(xc0, wc, Yc, [4e-5, 5e-5, 6e-5, 7e-5, 8e-5, 9e-5], ["4", "5", "6", "7", "8", "9"])
out.append("\\linethickness{0.8pt}")
for x, (lo, hi) in zip(xb, H21_B64):
    put(Xc(x), Yc(lo), f"\\line(0,1){{{f(Yc(hi) - Yc(lo))}}}")
    put(Xc(x) - 3, Yc(lo), "\\line(1,0){6}")
    put(Xc(x) - 3, Yc(hi), "\\line(1,0){6}")
out.append("\\thinlines")
for x, v in zip(xb, mid):
    marker("disc", Xc(x), Yc(v))

print("\\setlength{\\unitlength}{1pt}")
print(f"\\begin{{picture}}(465,{f(Y0 + H + 32)})")
print("\n".join(out))
print("\\end{picture}")
