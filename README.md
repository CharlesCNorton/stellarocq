# Stellarocq

Machine-checked plasma physics in [Rocq](https://rocq-prover.org). Force balance, flux-surface averages, Mercier stability and quasisymmetry of a [VMEC++](https://github.com/proximafusion/vmecpp) equilibrium are stated as theorems about the exact numbers in its wout file, and each is proven or decided by a checker extracted from a proof.

[Expr.v](theories/Expr.v) defines expressions with a real-number meaning and an interval evaluator proven to enclose it, over CoqInterval and Flocq, and [Physics.v](theories/Physics.v) writes in them the ideal-MHD residual `J x B - grad p` of the field reconstructed from a wout by VMEC's half-grid rule. [Checker.v](theories/Checker.v), [Cell.v](theories/Cell.v) and [Cover.v](theories/Cover.v) bound that residual at points, over cells covering a continuum of angles and over the volume between surfaces, and reversed they bound it away from zero. [Project.v](theories/Project.v) encloses the discrete Fourier harmonics of the residual at the modes a solver retains, which is the form of force balance a spectral solution converges. [Quad.v](theories/Quad.v) encloses flux-surface integrals over the same cells, [Mercier.v](theories/Mercier.v) assembles the Mercier criterion from them, and the quasisymmetry residual is bounded the same way. [Identities.v](theories/Identities.v) proves what the reconstruction satisfies exactly, [Hypotheses.v](theories/Hypotheses.v) states the physical assumptions, [Kantorovich.v](theories/Kantorovich.v) carries the Newton-Kantorovich argument in the abstract, and [FORMAT.md](FORMAT.md) is the certificate grammar.

Certifying a stellarator-symmetric equilibrium through the asymmetric reconstruction found [proximafusion/vmecpp#788](https://github.com/proximafusion/vmecpp/issues/788) and [jonathanschilling/educational_VMEC#27](https://github.com/jonathanschilling/educational_VMEC/issues/27). At `s = 0.125` of `wout_up_down_asym` the sign of `DMerc` depends on whether the current gradient is the exact radial derivative of the reconstruction or VMEC's difference quotient. The certified residual of `wout_li383_low_res` does not fall as the radial grid is refined from 16 to 121 surfaces and falls more than twentyfold as the mode set grows from 25 to 98.

## Build

```sh
opam switch create stellarocq ocaml-base-compiler.4.14.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover.9.0.0 rocq-core.9.1.1 coq-stdlib.9.2.0 \
             coq-mathcomp-ssreflect.2.4.0 coq-coquelicot.3.4.5 \
             coq-interval.4.11.4 coq-flocq.4.2.2 dune.3.23.1
make versions   # the installed toolchain against the pinned versions
make all        # proofs, extraction, checker binary
make audit      # Print Assumptions of every theorem
```

`make static` links the same checker statically, and the [releases](https://github.com/CharlesCNorton/stellarocq/releases) carry that build for x86_64 Linux.

## Use

```sh
python gen/make_cert.py wout.nc cells.txt --cells --nodes 6 --nu 8192    # write a cell certificate
./extract/_build/default/main.exe --tighten --verify cells.txt cert.txt  # write its bounds and check them
python gen/verify_cert.py wout.nc cert.txt                               # compare the certificate with the wout
python test/run_tests.py --data DIR                                      # regression suite
```

The checker also takes `--project`, `--lower`, `--integrate`, `--taylor`, `--slot3` and `--mercier`, and `gen/` holds the drivers for the Mercier profile, the Boozer stream function, the convergence study and the radial scan. The Python tools need `numpy` and `netCDF4`, and `h5py` for a VMEC++ HDF5 output.
