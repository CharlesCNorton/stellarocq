"""Post-extraction stub of the spec-only classical-real layer.

The extracted checker never computes with real numbers: the correctness
theorem speaks about them, the code decides everything over integers and
floats.  Extraction nevertheless emits the classical constructions behind
Rocq's R as module-level values, and two of them run at link time (the
axiom sig_forall_dec extracts as an eager `failwith`, and R0/R1 eagerly
build Dedekind cuts through it).

This script replaces exactly those bindings with poison closures: linking
becomes free, and any attempt to actually consult a classical real at
runtime fails loudly instead of computing.  Nothing the soundness theorem
depends on is touched; a diff of the patch is part of the audit surface.

Usage: python3 patch_extract.py <extract-dir>
"""
import re, sys, pathlib

POISON = "Obj.magic (fun _ -> assert false (* spec-only: classical real *))"

def patch(path, names):
    """Replace the bodies of the named bindings with the poison value."""
    p = pathlib.Path(path)
    t = p.read_text()
    changed = []
    for name in names:
        # match:  let <name> =\n    <one-line body>
        pat = re.compile(r"(let %s =\n)(    .*?)(\n)" % re.escape(name))
        m = pat.search(t)
        if not m:
            pat = re.compile(r"(let %s =\n)(  .*?)(\n)" % re.escape(name))
            m = pat.search(t)
        if m:
            t = t[:m.start(2)] + "    " + POISON + t[m.end(2):]
            changed.append(name)
    p.write_text(t)
    return changed

def main(d):
    """Stub the classical-real layer in the extraction directory d."""
    d = pathlib.Path(d)
    done = []
    done += [("ClassicalDedekindReals.ml", n) for n in
             patch(d/"ClassicalDedekindReals.ml",
                   ["sig_forall_dec", "sig_not_dec"])]
    done += [("Rdefinitions.ml", n) for n in
             patch(d/"Rdefinitions.ml",
                   ["coq_R0", "coq_R1", "coq_R0_def", "coq_R1_def"])]
    # ExtrOCamlFloats maps float_comparison / float_class constructors
    # to bare names from the Float64 shim; open it where they are used.
    po = d / "Primitive_ops.ml"
    s = po.read_text()
    if "open Float64" not in s:
        s = s.replace("open Basic", "open Basic" + chr(10) + "open Float64", 1)
        po.write_text(s)
        done.append(("Primitive_ops.ml", "open Float64"))

    for f, n in done:
        print(f"stubbed {f}: {n}")
    if not done:
        print("nothing to patch (already stubbed?)")

if __name__ == "__main__":
    main(sys.argv[1])
