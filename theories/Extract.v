(** Extract the checker and its certificate types to OCaml. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.
From Coq Require Import ExtrOCamlInt63 ExtrOCamlFloats.
From Stellarocq Require Import Physics Checker Cell Cover Deriv Quad Mercier
     Project Newton Colloc Box Integral TrigExpr Harmonic BoxCell QSFloor Cover2 Integrate
     MercierRun WideHarm.
Extraction Language OCaml.
Set Extraction Output Directory ".".

(** The float types with their constructors named in the module that defines
    them, so no extracted file has to open it. *)
Extract Inductive FloatClass.float_class =>
  "Float64.float_class"
  [ "Float64.PNormal" "Float64.NNormal" "Float64.PSubn" "Float64.NSubn" "Float64.PZero"
    "Float64.NZero" "Float64.PInf" "Float64.NInf" "Float64.NaN" ].
Extract Inductive PrimFloat.float_comparison =>
  "Float64.float_comparison" [ "Float64.FEq" "Float64.FLt" "Float64.FGt" "Float64.FNotComparable" ].

(** The classical reals appear only in specifications. The axiom they are
    built on and the reals 0 and 1 built from it are extracted as values that
    fail when consulted, so nothing of them runs when the checker starts. *)
Extract Constant ClassicalDedekindReals.sig_forall_dec => "(fun _ -> assert false)".
Extract Constant Rdefinitions.RbaseSymbolsImpl.R0 => "(Obj.magic (fun _ -> assert false))".
Extract Constant Rdefinitions.RbaseSymbolsImpl.R1 => "(Obj.magic (fun _ -> assert false))".
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
  hrow hpoint tdeg_binds hres hbase hcomp hprec_of bounded check_dharm wharm_row
  RJump BTCert BTCellC check_btcert check_btcell btcell_comb_e btres btbase
  btprec_of bt_tiles bt_period BPCert BPt check_bpcert check_bpt bpres bpprec_of
  QCert check_qcert qharm_i qharm_vals qcomp_i qres qenv_i qprec REnergy
  cover2 cover_lines cell_exts cell_exts_vu fu_of fv_of lo_at hi_at mid_at
  integ2 integ1 integ2_torus
  Block merc_run torus below above RRadialGeom RRadialShear.
