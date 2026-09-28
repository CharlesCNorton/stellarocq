From Stdlib Require Import ZArith List Lia.
From Stellarocq Require Import KFix KEngine KFinal.
Module P192 <: Prec. Definition k : Z := 192%Z. Lemma k_nonneg : (0 <= k)%Z. Proof. unfold k. lia. Qed. End P192.
Module FX192 := FX P192.
Module FF := Final FX192.
Definition head := FF.cert_head.
Definition src := FF.run_src.
Definition src_with := FF.check_src_with.
Definition e0 := FF.run_E0.
Definition jets := FF.run_jets.
Definition twist := FF.run_twist.
Definition twist_with := FF.check_twist_with.
Definition fin := FF.check_fin.
Definition fin_diag := FF.fin_diag.
Definition mke0 := FF.E.mke0.
Definition mksd := FF.FS.SC.SR.mksrcd.
Definition mkjd := FF.JC.mkjd.
Definition mkfd := mkfd.
Definition mkfs := mkfs.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt.
Extract Constant Z.sqrt => "(fun x -> if Big_int_Z.sign_big_int x <= 0 then Big_int_Z.zero_big_int else Big_int_Z.sqrt_big_int x)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".
Extract Constant pmap => "Par.pmap".
Extraction Language OCaml.
Separate Extraction head src src_with e0 jets twist twist_with fin fin_diag mke0 mksd mkjd mkfd mkfs.
