From Stdlib Require Import ZArith List Lia.
From Stellarocq Require Import KEngine KLohner.
Definition check := check_lescape.
Definition box := box_ok.
Definition mk := mklesc.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt ExtrOCamlInt63 ExtrOCamlFloats.
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".
Extract Constant pmap => "Par.pmap".
Extract Inductive FloatClass.float_class =>
  "Float64.float_class"
  [ "Float64.PNormal" "Float64.NNormal" "Float64.PSubn" "Float64.NSubn" "Float64.PZero"
    "Float64.NZero" "Float64.PInf" "Float64.NInf" "Float64.NaN" ].
Extract Inductive PrimFloat.float_comparison =>
  "Float64.float_comparison" [ "Float64.FEq" "Float64.FLt" "Float64.FGt" "Float64.FNotComparable" ].
Extraction Language OCaml.
Separate Extraction check box mk.
