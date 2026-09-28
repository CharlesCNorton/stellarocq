From Stdlib Require Import ZArith List Lia.
From Stellarocq Require Import KEngine KLohner.
Definition check := check_lescape.
Definition box := box_ok.
Definition mk := mklesc.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt ExtrOCamlInt63 ExtrOCamlFloats.
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".
Extract Constant pmap => "Par.pmap".
Extraction Language OCaml.
Separate Extraction check box mk.
