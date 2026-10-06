"""Make the classical-real layer of an extraction inert at module initialisation.

The checks never compute with real numbers; the reals appear in specifications
only. Extraction nevertheless emits module-level values built from them (kappa,
PI, R0, R1, the excluded middle of Coquelicot's Markov module, ...) whose
evaluation at program start would run the classical constructions, and the two
axioms of ClassicalDedekindReals. This pass replaces by an inert value
  - every module-level value whose extracted type mentions coq_R or a type of
    real families (fser, vf, mf, cjet, src, fent, fmodel, kcon) and is not a
    function, in any module;
  - every module-level value that is not a function, in the modules of the
    real-number libraries (Reals, Coquelicot, the constructive reals);
and turns the two axioms into inert functions.
"""
import pathlib
import re
import sys

SPEC = re.compile(r"^(R(?!egResidual$)[A-Za-z0-9_]*|Rtrigo\w*|Alembert|SeqProp|Lim_seq|Lub|Markov|Rbar|Hierarchy|Continuity|"
                  r"ClassicalDedekindReals|Constructive\w*|Ranalysis\w*|Rsqrt_def|R_sqrt|Rpow_def|Rbasic_fun|"
                  r"Raxioms|RIneq|Rdefinitions)$")

d = pathlib.Path(sys.argv[1])
total = 0
for p in sorted(d.glob("*.ml")):
    if p.name == "main.ml":
        continue
    spec = bool(SPEC.match(p.stem))
    lines = p.read_text().split("\n")
    out, i, n = [], 0, 0
    typ = None
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^(\s*)\(\*\* val (\w+) :(.*)$", line)
        if m:
            j, t = i, m.group(3)
            while "**)" not in lines[j]:
                j += 1
                t += " " + lines[j]
            typ = (m.group(2), t.replace("**)", ""))
            out.extend(lines[i:j + 1])
            i = j + 1
            continue
        b = re.match(r"^(\s*)let (rec )?([\w']+) =\s*$", line)
        if b:
            name = b.group(3)
            body = next((x for x in lines[i + 1:] if x.strip()), "")
            is_fun = body.strip().startswith(("fun ", "function", "(fun "))
            by_type = (typ is not None and typ[0] == name and "->" not in typ[1]
                       and re.search(r"\b(coq_R|fser|vf|mf|cjet|src|fent|fmodel|kcon)\b", typ[1]) is not None)
            if not is_fun and (by_type or (spec and name != "__")):
                out.append(line)
                out.append(b.group(1) + "  Obj.magic 0")
                i += 1
                while i < len(lines) and lines[i].strip() and (len(lines[i]) - len(lines[i].lstrip())) > len(b.group(1)):
                    i += 1
                n += 1
                typ = None
                continue
        out.append(line)
        i += 1
    text = "\n".join(out)
    t2 = text.replace('failwith "AXIOM TO BE REALIZED (Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec)"',
                      'Obj.magic (fun _ -> assert false)')
    t2 = t2.replace('failwith "AXIOM TO BE REALIZED (Stdlib.Reals.ClassicalDedekindReals.sig_not_dec)"',
                    'Obj.magic false')
    if n or t2 != text:
        p.write_text(t2)
    total += n
print(f"stubbed {total} module-level values of the real-number layer")
