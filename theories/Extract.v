(** Extract the checker and its certificate types to OCaml. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.
From Coq Require Import ExtrOCamlInt63 ExtrOCamlFloats.
From Stellarocq Require Import Physics Checker Cell Cover Deriv Quad Mercier
     Project Newton Colloc Box Integral TrigExpr Harmonic BoxCell QSFloor.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Separate Extraction check_cert check_cert_lower Cert CPoint check_ccert check_ccert_lower CCert CCell CBounds covers check_ccert3 CCert3 CCell3 check_ccert_t check_ccert_t_lower TCert TCell TBounds var_free isum
  MBox merc_i menv check_unstable check_stable
  e_dshear e_dcurr e_dwell e_dgeod e_dmerc e_dstable
  with_derivs2 PConfig RResidual RHarmonic RGeometry RMercierA RMercierB PPower PTwoPower PCubic PRational PGaussTrunc
  base_R base_Z base_L base_Ra base_Za base_La base_W
  PTwoPowerGs PPedestal PTwoLorentz RRadialAxis RCovHarm RCovHarmS
  RStreamDefect RBoozer RTerms RRadialTerms RJsTerms RRadialJsTerms
  RQuasiSym RQuasiTwo base_scratch_of
  kern_at kern_ok_at harm_i
  check_newton check_core check_anorm System circle_binds circle_out
  Jtab Fctab Fwtab centre_tab Jt Ft Giv Hiv Viv rowsum Kiv Riv Miv entry_ok
  CPt colloc_check colloc_core colloc_system point_ok local_res out_slot sigma_of
  RForced
  wide_ienv BCert check_bcert check_bcert_lower box_ienv_of
  ICert IBounds check_int int_total rows_check rows_contribs icell_box
  icell_centre icentre ires ibase icomp inu
  RWeighted HCert check_harm harm_total harm_rows harm_struct harm_first
  hrow hpoint tdeg_binds hres hbase hcomp hprec_of bounded check_dharm
  RJump BTCert BTCellC check_btcert check_btcell btcell_comb_e btres btbase
  btprec_of bt_tiles bt_period BPCert BPt check_bpcert check_bpt bpres bpprec_of
  QCert check_qcert qharm_i qharm_vals qcomp_i qres qenv_i qprec REnergy.
