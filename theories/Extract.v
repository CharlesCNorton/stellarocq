(** Extract the checker and its certificate types to OCaml. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.
From Coq Require Import ExtrOCamlInt63 ExtrOCamlFloats.
From Stellarocq Require Import Physics Checker Cell Cover Deriv Quad Mercier.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Separate Extraction check_cert check_cert_lower Cert CPoint check_ccert check_ccert_lower CCert CCell CBounds covers check_ccert3 CCert3 CCell3 check_ccert_t TCert TCell TBounds var_free isum
  MBox merc_i menv check_unstable check_stable
  e_dshear e_dcurr e_dwell e_dgeod e_dmerc e_dstable
  with_derivs2 PConfig RResidual RHarmonic RGeometry RMercierA RMercierB PPower PTwoPower PCubic PRational PGaussTrunc
  PTwoPowerGs PPedestal PTwoLorentz RRadialAxis RCovHarm RCovHarmS
  RStreamDefect RBoozer RTerms RRadialTerms base_scratch_of.
