"""Write the data of the escape certificate (KLohner.lescdata) past its sources.

    python gen/kam_escape.py OUT --R1 6.46 --RD 6.54 --RD2 6.33 --width 4e-4 [--M 40000 --J 6 --sb 40 --fuel 6000]

The field period and the sources are those of the source data of the KAM
certificate, which esc/main.ml reads. The file holds M, J, the scale sb, R1,
R_D and R_D2 at 2^-sb, the number of boxes, and per box its ends at 2^-sb and
its fuel. The boxes tile [R1, R_D] in steps of the width, each sharing its
ends with its neighbours, the first starting at R1 and the last ending past R_D.
"""
import argparse
from fractions import Fraction

ap = argparse.ArgumentParser()
ap.add_argument("out")
ap.add_argument("--R1", default="6.46")
ap.add_argument("--RD", default="6.54")
ap.add_argument("--RD2", default="6.33")
ap.add_argument("--width", default="4e-4")
ap.add_argument("--M", type=int, default=40000)
ap.add_argument("--J", type=int, default=6)
ap.add_argument("--sb", type=int, default=40)
ap.add_argument("--fuel", type=int, default=6000)
ap.add_argument("--only", type=int, nargs=2, default=None, help="write boxes [a, b) of the tiling alone")
a = ap.parse_args()

sc = 2 ** a.sb
q = lambda s: int(Fraction(s) * sc)
r1, rd, rd2, w = q(a.R1), q(a.RD), q(a.RD2), q(a.width)
edges = [r1]
while edges[-1] <= rd:
    edges.append(edges[-1] + w)
boxes = list(zip(edges[:-1], edges[1:]))
if a.only:
    boxes = boxes[a.only[0]:a.only[1]]
with open(a.out, "w") as f:
    f.write(f"{a.M} {a.J} {a.sb} {r1} {rd} {rd2}\n{len(boxes)}\n")
    for ra, rb in boxes:
        f.write(f"{ra} {rb} {a.fuel}\n")
print(f"{len(boxes)} boxes of width {a.width} over [{a.R1}, {a.RD}] to {a.out}")
