theory Register_Access
  imports
    Main
    "HOL-Library.Word"
    "AArch64_Registers"
    "Word_Utils"
    "RegProt_State"
begin

subsection \<open> System Control Registers \<close>

subsubsection \<open> SCTLTR_EL1 \<close>

definition sctlr_el1_to_word64 ::
  "SCTLR_EL1 \<Rightarrow> 64 word"
  where
    "sctlr_el1_to_word64 r =
  or_list [
  (bool_to_word64 (TIDCP r))     << 63,
  (bool_to_word64 (SPINTMASK r)) << 62,
  (bool_to_word64 (SCTLR_EL1.NMI r))       << 61,
  (bool_to_word64 (EnTP2 r))     << 60,
  (bool_to_word64 (TCSO r))      << 59,
  (bool_to_word64 (TCSO0 r))     << 58,
  (bool_to_word64 (EPAN r))      << 57,
  (bool_to_word64 (EnAlS r))     << 56,
  (bool_to_word64 (EnAS0 r))     << 55,
  (bool_to_word64 (EnASR r))     << 54,
  (bool_to_word64 (SCTLR_EL1.TME r))       << 53,
  (bool_to_word64 (TME0 r))      << 52,
  (bool_to_word64 (TMT r))       << 51,
  (bool_to_word64 (TMT0 r))      << 50,
  (unsigned (TWEDEL r))          << 46,
  (bool_to_word64 (TWEDEn r))    << 45,
  (bool_to_word64 (DSSBS r))     << 44,
  (bool_to_word64 (ATA r))       << 43,
  (bool_to_word64 (ATA0 r))      << 42,
  (unsigned (tcf_mode_to_bits (TCF r)))   << 40,
  (unsigned (tcf_mode_to_bits (TCF0 r)))  << 38,
  (bool_to_word64 (ITFSB r))     << 37,
  (bool_to_word64 (BT1 r))       << 36,
  (bool_to_word64 (BT0 r))       << 35,
  (bool_to_word64 (EnFPM r))     << 34,
  (bool_to_word64 (MSCEn r))     << 33,
  (bool_to_word64 (SCTLR_EL1.CMOW r))      << 32,
  (bool_to_word64 (EnIA r))      << 31,
  (bool_to_word64 (EnIB r))      << 30,
  (bool_to_word64 (LSMAOE r))    << 29,
  (bool_to_word64 (nTLSMD r))    << 28,
  (bool_to_word64 (EnDA r))      << 27,
  (bool_to_word64 (UCI r))       << 26,
  (bool_to_word64 (EE r))        << 25,
  (bool_to_word64 (E0E r))       << 24,
  (bool_to_word64 (SPAN r))      << 23,
  (bool_to_word64 (EIS r))       << 22,
  (bool_to_word64 (SCTLR_EL1.IESB r))      << 21,
  (bool_to_word64 (TSCXT r))     << 20,
  (bool_to_word64 (WXN r))       << 19,
  (bool_to_word64 (nTWE r))      << 18,
  (ucast (B17RES0 r))            << 18,
  (bool_to_word64 (nTWI r))      << 16,
  (bool_to_word64 (UCT r))       << 15,
  (bool_to_word64 (DZE r))       << 14,
  (bool_to_word64 (EnDB r))      << 13,
  (bool_to_word64 (I r))         << 12,
  (bool_to_word64 (EOS r))       << 11,
  (bool_to_word64 (EnRCTX r))    << 10,
  (bool_to_word64 (UMA r))       << 9,
  (bool_to_word64 (SED r))       << 8,
  (bool_to_word64 (ITD r))       << 7,
  (bool_to_word64 (nAA r))       << 6,
  (bool_to_word64 (CP15BEN r))   << 5,
  (bool_to_word64 (SA0 r))       << 4,
  (bool_to_word64 (SA r))        << 3,
  (bool_to_word64 (C r))         << 2,
  (bool_to_word64 (A r))         << 1,
  (bool_to_word64 (M r))         << 0
  ]"

definition word64_to_sctlr_el1 ::
  "64 word \<Rightarrow> SCTLR_EL1"
  where
  "word64_to_sctlr_el1 w \<equiv>
    \<lparr> TIDCP = test_bit w 63,
      SPINTMASK = test_bit w 62,
      NMI = test_bit w 61,
      EnTP2 = test_bit w 60,
      TCSO = test_bit w 59,
      TCSO0 = test_bit w 58,
      EPAN = test_bit w 57,
      EnAlS = test_bit w 56,
      EnAS0 = test_bit w 55,
      EnASR = test_bit w 54,
      TME = test_bit w 53,
      TME0 = test_bit w 52,
      TMT = test_bit w 51,
      TMT0 = test_bit w 50,
      TWEDEL = ucast (and (w >> 46) 0xF),
      TWEDEn = test_bit w 45,
      DSSBS = test_bit w 44,
      ATA = test_bit w 43,
      ATA0 = test_bit w 42,
      TCF = bits_to_tcf_mode (ucast (and (w >> 40) 0x3)),
      TCF0 = bits_to_tcf_mode (ucast (and (w >> 38) 0x3)),
      ITFSB = test_bit w 37,
      BT1 = test_bit w 36,
      BT0 = test_bit w 35,
      EnFPM = test_bit w 34,
      MSCEn = test_bit w 33,
      CMOW = test_bit w 32,
      EnIA = test_bit w 31,
      EnIB = test_bit w 30,
      LSMAOE = test_bit w 29,
      nTLSMD = test_bit w 28,
      EnDA = test_bit w 27,
      UCI = test_bit w 26,
      EE = test_bit w 25,
      E0E = test_bit w 24,
      SPAN = test_bit w 23,
      EIS = test_bit w 22,
      IESB = test_bit w 21,
      TSCXT = test_bit w 20,
      WXN = test_bit w 19,
      nTWE = test_bit w 18,
      B17RES0 = ucast (and (w>>17)  0x1),
      nTWI = test_bit w 16,
      UCT = test_bit w 15,
      DZE = test_bit w 14,
      EnDB = test_bit w 13,
      I = test_bit w 12,
      EOS = test_bit w 11,
      EnRCTX = test_bit w 10,
      UMA = test_bit w 9,
      SED = test_bit w 8,
      ITD = test_bit w 7,
      nAA = test_bit w 6,
      CP15BEN = test_bit w 5,
      SA0 = test_bit w 4,
      SA = test_bit w 3,
      C = test_bit w 2,
      A = test_bit w 1,
      M = test_bit w 0 \<rparr>"

subsection \<open> TCR_EL1 \<close>

definition word64_to_tcr_el1 :: "64 word \<Rightarrow> TCR_EL1" where
  "word64_to_tcr_el1 w \<equiv>
    \<lparr> B6362RES0 = (ucast (and (w>>62) 0x3)),
      MTX1 = test_bit w 61,
      MTX0 = test_bit w 60,
      DS = test_bit w 59,
      TCMA1 = test_bit w 58,
      TCMA0 = test_bit w 57,
      E0PD1 = test_bit w 56,
      E0PD0 = test_bit w 55,
      NFD1 = test_bit w 54,
      NFD0 = test_bit w 53,
      TBID1 = test_bit w 52,
      TBID0 = test_bit w 51,
      HWU162 = test_bit w 50,
      HWU161 = test_bit w 49,
      HWU160 = test_bit w 48,
      HWU159 = test_bit w 47,
      HWU062 = test_bit w 46,
      HWU061 = test_bit w 45,
      HWU060 = test_bit w 44,
      HWU059 = test_bit w 43,
      HPD1 = test_bit w 42,
      HPD0 = test_bit w 41,
      HD = test_bit w 40,
      HA = test_bit w 39,
      TBI1 = test_bit w 38,
      TBI0 = test_bit w 37,
      AS = test_bit w 36,
      B35RES0 = ucast (and (w>>35)  0x1),
      IPS = bits_to_ips (ucast (and (w >> 32) 0x7)),
      TG1 = bits_to_granule (ucast (and (w >> 30) 0x3)),
      SH1 = bits_to_domain (ucast (and (w >> 28) 0x3)),
      ORGN1 = bits_to_cacheability_word (ucast (and (w >> 26) 0x3)),
      IRGN1 = bits_to_cacheability_word (ucast (and (w >> 24) 0x3)),
      EPD1 = test_bit w 23,
      A1 = test_bit w 22,
      T1SZ = ucast (and (w >> 16) 0x3F),
      TG0 = bits_to_granule (ucast (and (w >> 14) 0x3)),
      SH0 = bits_to_domain (ucast (and (w >> 12) 0x3)),
      ORGN0 = bits_to_cacheability_word (ucast (and (w >> 10) 0x3)),
      IRGN0 = bits_to_cacheability_word (ucast (and (w >> 8) 0x3)),
      EPD0 = test_bit w 7,
      B06RES0 = ucast (and (w>>6)  0x1),
      T0SZ = ucast (and w 0x3F) \<rparr>"

subsection \<open> MAIR_EL1 \<close>

definition word64_to_mair_el1 :: "64 word \<Rightarrow> MAIR_EL1" where
  "word64_to_mair_el1 w \<equiv>
    \<lparr> Attr0 = ucast (and w 0xFF),
      Attr1 = ucast (and (w >> 8) 0xFF),
      Attr2 = ucast (and (w >> 16) 0xFF),
      Attr3 = ucast (and (w >> 24) 0xFF),
      Attr4 = ucast (and (w >> 32) 0xFF),
      Attr5 = ucast (and (w >> 40) 0xFF),
      Attr6 = ucast (and (w >> 48) 0xFF),
      Attr7 = ucast (and (w >> 56) 0xFF) \<rparr>"

subsection \<open> TTBRx_EL1 \<close>

definition word64_to_ttbr0_el1 :: "64 word \<Rightarrow> TTBR0_EL1" where
  "word64_to_ttbr0_el1 w \<equiv>
    \<lparr> ASID = ucast (and (w >> 48) 0xFFFF),
      BADDR = ucast (and (w >> 1) 0x7FFFFFFFFFFF),
      CnP = test_bit w 0 \<rparr>"

definition word64_to_ttbr1_el1 :: "64 word \<Rightarrow> TTBR1_EL1" where
  "word64_to_ttbr1_el1 w \<equiv>
    \<lparr> ASID = ucast (and (w >> 48) 0xFFFF),
      BADDR = ucast (and (w >> 1) 0x7FFFFFFFFFFF),
      CnP = test_bit w 0 \<rparr>"

subsection \<open> ESR_EL1 \<close>

definition word64_to_esr_el1 :: "64 word \<Rightarrow> ESR_EL1" where
  "word64_to_esr_el1 w \<equiv>
    \<lparr> ISS2 = ucast (and (w >> 32) 0xFFFFFF),
      EC = ucast (and (w >> 26) 0x3F),
      IL = bits_to_instruction_length (ucast (and (w >> 25) 0x1)),
      ISS = ucast (and w 0x1FFFFFF) \<rparr>"

subsection \<open> FAR_EL1 \<close>

definition word64_to_far_el1 :: "64 word \<Rightarrow> FAR_EL1" where
  "word64_to_far_el1 w \<equiv> \<lparr> FaultingVA = w \<rparr>"

subsection \<open> CONTEXTIDR_EL1 \<close>

definition word64_to_contextidr_el1 :: "64 word \<Rightarrow> CONTEXTIDR_EL1" where
  "word64_to_contextidr_el1 w \<equiv> \<lparr> PROCID = ucast (and w 0xffffffff)\<rparr>"

subsection \<open> AFSR0_EL1 \<close>

definition word64_to_afsr0_el1 :: "64 word \<Rightarrow> AFSR0_EL1" where
  "word64_to_afsr0_el1 w \<equiv> \<lparr> Value = w \<rparr>"

subsection \<open> AFSR1_EL1 \<close>

definition word64_to_afsr1_el1 :: "64 word \<Rightarrow> AFSR1_EL1" where
  "word64_to_afsr1_el1 w \<equiv> \<lparr> Value = w \<rparr>"

subsection \<open> AMAIR_EL1 \<close>

definition word64_to_amair_el1 :: "64 word \<Rightarrow> AMAIR_EL1" where
  "word64_to_amair_el1 w \<equiv> \<lparr> Value = w \<rparr>"

subsection \<open> ACTLR_EL1 \<close>

definition word64_to_actlr_el1 :: "64 word \<Rightarrow> ACTLR_EL1" where
  "word64_to_actlr_el1 w \<equiv> \<lparr> Value = w \<rparr>"


section \<open> Registers Interface \<close>

subsection \<open> System Registers \<close>


subsubsection \<open> Fields Definition \<close>

definition check_res0 ::
  "Reg_Value \<Rightarrow> Reg_Value \<Rightarrow> bool"
  where
    "check_res0 v m \<equiv> ((and v m) = (0 :: 64 word))"

definition check_res1 ::
  "Reg_Value \<Rightarrow> Reg_Value \<Rightarrow> bool"
  where
    "check_res1 v m \<equiv> ((and v m) = m)"


definition M_BIT_INDEX :: nat where "M_BIT_INDEX \<equiv> 0"

definition WXN_BIT_INDEX :: nat where "WXN_BIT_INDEX \<equiv> 19"

definition SPAN_BIT_INDEX :: nat where "SPAN_BIT_INDEX \<equiv> 23"

definition E0E_BIT_INDEX :: nat where "E0E_BIT_INDEX \<equiv> 24"

definition EE_BIT_INDEX :: nat where "EE_BIT_INDEX \<equiv> 25"

definition EPAN_BIT_INDEX :: nat where "EPAN_BIT_INDEX \<equiv> 57"

definition SCTLR_EL1_RES0_MASK :: "64 word"
  where "SCTLR_EL1_RES0_MASK \<equiv> 0xf000000800000040"


definition HPD0_BIT_INDEX :: nat where "HPD0_BIT_INDEX \<equiv> 41"
definition HPD1_BIT_INDEX :: nat where "HPD1_BIT_INDEX \<equiv> 42"
definition HWU_MASK :: "64 word"
  where "HWU_MASK \<equiv> 0x0007f80000000000"

definition TCR_EL1_RES0_MASK :: "64 word"
  where "TCR_EL1_RES0_MASK \<equiv> 0xf0000000800000040"
definition EAE_BIT_INDEX :: nat where "EAE_BIT_INDEX \<equiv> 31"
definition T2E_BIT_INDEX :: nat where "T2E_BIT_INDEX \<equiv> 6"
definition TBID_MASK :: "64 word"
  where "TBID_MASK \<equiv> 0x0018000000000000"
definition AS_BIT_INDEX :: nat where "AS_BIT_INDEX \<equiv> 36"
definition HA_BIT_INDEX :: nat where "HA_BIT_INDEX \<equiv> 39"
definition HD_BIT_INDEX :: nat where "HD_BIT_INDEX \<equiv> 40"
definition E0PD_MASK :: "64 word"
  where "E0PD_MASK \<equiv> 0x0180000000000000"
definition TCMA_MASK :: "64 word"
  where "TCMA_MASK \<equiv> 0x0600000000000000"


definition CNP_BIT_INDEX :: nat where "CNP_BIT_INDEX \<equiv> 0"
definition BADDR_MASK :: "64 word"
  where "BADDR_MASK \<equiv> 0x0000fffffffffffe"


definition AA64MMFR2_CNP_MASK :: "64 word"
  where "AA64MMFR2_CNP_MASK \<equiv> 0x000000000000000f"
definition AA64MMFR2_CNP_En :: "64 word"
  where "AA64MMFR2_CNP_En \<equiv> 0x0000000000000001"


definition MMFR4_CNP_MASK :: "64 word"
  where "MMFR4_CNP_MASK \<equiv> 0x000000000000f000"
definition MMFR4_CNP_En :: "64 word"
  where "MMFR4_CNP_En \<equiv> 0x0000000000001000"


definition AA64MMFR0_BigEnd_MASK :: "64 word"
  where "AA64MMFR0_BigEnd_MASK \<equiv> 0x0000000000000f00"
definition AA64MMFR0_BigEndEl0_MASK :: "64 word"
  where "AA64MMFR0_BigEndEl0_MASK \<equiv> 0x00000000000f0000"
definition AA64MMFR0_BigEnd_NotSupported :: "64 word"
  where "AA64MMFR0_BigEnd_NotSupported \<equiv> 0x0000000000000000"
definition AA64MMFR0_BigEndEl0_NotSupported :: "64 word"
  where "AA64MMFR0_BigEndEl0_NotSupported \<equiv> 0x0000000000000000"


definition AA64MMFR1_PAN_MASK :: "64 word"
  where "AA64MMFR1_PAN_MASK \<equiv> 0x0000000000f00000"
definition AA64MMFR1_PAN_NotSupported :: "64 word"
  where "AA64MMFR1_PAN_NotSupported \<equiv> 0x0000000000000000"
definition AA64MMFR1_PAN_Supported3 :: "64 word"
  where "AA64MMFR1_PAN_Supported3 \<equiv> 0x0000000000030000"


definition MMF3_PAN_MASK :: "64 word"
  where "MMF3_PAN_MASK \<equiv> 0x00000000000f0000"
definition MMF3_PAN_NotSupported :: "64 word"
  where "MMF3_PAN_NotSupported \<equiv> 0x0000000000000000"

subsubsection \<open> SysReg State \<close>

definition get_MAIR_EL1_state ::
  "State \<Rightarrow> Sys_Reg_State"
  where
    "get_MAIR_EL1_state s =
      (MAIR_EL1_State (protected_reg_state (regs_state s)))"

definition set_MAIR_EL1_state ::
  "State \<Rightarrow> Sys_Reg_State \<Rightarrow> State"
  where
    "set_MAIR_EL1_state s srs =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> protected_reg_state :=
          (protected_reg_state (regs_state s))\<lparr> MAIR_EL1_State := srs\<rparr> \<rparr> \<rparr>"

definition get_TCR_EL1_state ::
  "State \<Rightarrow> Sys_Reg_State"
  where
    "get_TCR_EL1_state s =
      (TCR_EL1_State (protected_reg_state (regs_state s)))"

definition set_TCR_EL1_state ::
  "State \<Rightarrow> Sys_Reg_State \<Rightarrow> State"
  where
    "set_TCR_EL1_state s srs =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> protected_reg_state :=
          (protected_reg_state (regs_state s))\<lparr> TCR_EL1_State := srs\<rparr> \<rparr> \<rparr>"

definition get_TTBR1_EL1_state ::
  "State \<Rightarrow> Sys_Reg_State"
  where
    "get_TTBR1_EL1_state s =
      (TTBR1_EL1_State (protected_reg_state (regs_state s)))"

definition set_TTBR1_EL1_state ::
  "State \<Rightarrow> Sys_Reg_State \<Rightarrow> State"
  where
    "set_TTBR1_EL1_state s srs =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> protected_reg_state :=
          (protected_reg_state (regs_state s))\<lparr> TTBR1_EL1_State := srs\<rparr> \<rparr> \<rparr>"

definition get_TTBR1_EL1_saved ::
  "State \<Rightarrow> TTBR1_EL1 option"
  where
    "get_TTBR1_EL1_saved s =
      (TTBR1_EL1_Saved (protected_reg_state (regs_state s)))"

definition set_TTBR1_EL1_saved ::
  "State \<Rightarrow> TTBR1_EL1 option \<Rightarrow> State"
  where
    "set_TTBR1_EL1_saved s saved =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> protected_reg_state :=
          (protected_reg_state (regs_state s))\<lparr> TTBR1_EL1_Saved := saved\<rparr> \<rparr> \<rparr>"

subsubsection \<open> read \<close>

definition read_SCTLR_EL1 ::
    "State \<Rightarrow> SCTLR_EL1"
  where
    "read_SCTLR_EL1 s =
      (SCTLR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_TTBR0_EL1 ::
    "State \<Rightarrow> TTBR0_EL1"
  where
    "read_TTBR0_EL1 s =
      (TTBR0_EL1 (sys_regs_el1 (regs_state s)))"

definition read_TTBR1_EL1 ::
    "State \<Rightarrow> TTBR1_EL1"
  where
    "read_TTBR1_EL1 s =
     (TTBR1_EL1 (sys_regs_el1 (regs_state s)))"

definition read_TCR_EL1 ::
    "State \<Rightarrow> TCR_EL1"
  where
    "read_TCR_EL1 s =
      (TCR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_ESR_EL1 ::
    "State \<Rightarrow> ESR_EL1"
  where
    "read_ESR_EL1 s =
      (ESR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_FAR_EL1 ::
    "State \<Rightarrow> FAR_EL1"
  where
    "read_FAR_EL1 s =
      (FAR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_AFSR0_EL1 ::
    "State \<Rightarrow> AFSR0_EL1"
  where
    "read_AFSR0_EL1 s =
      (AFSR0_EL1 (sys_regs_el1 (regs_state s)))"

definition read_AFSR1_EL1 ::
    "State \<Rightarrow> AFSR1_EL1"
  where
    "read_AFSR1_EL1 s =
      (AFSR1_EL1 (sys_regs_el1 (regs_state s)))"

definition read_MAIR_EL1 ::
    "State \<Rightarrow> MAIR_EL1"
  where
    "read_MAIR_EL1 s =
      (MAIR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_AMAIR_EL1 ::
    "State \<Rightarrow> AMAIR_EL1"
  where
    "read_AMAIR_EL1 s =
      (AMAIR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_CONTEXTIDR_EL1 ::
    "State \<Rightarrow> CONTEXTIDR_EL1"
  where
    "read_CONTEXTIDR_EL1 s =
      (CONTEXTIDR_EL1 (sys_regs_el1 (regs_state s)))"

definition read_ACTLR_EL1 ::
    "State \<Rightarrow> ACTLR_EL1"
  where
    "read_ACTLR_EL1 s =
      (ACTLR_EL1 (sys_regs_el1 (regs_state s)))"

subsubsection \<open> write \<close>

definition write_SCTLR_EL1 ::
    "State \<Rightarrow> SCTLR_EL1 \<Rightarrow> State"
  where
    "write_SCTLR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> SCTLR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_TTBR0_EL1 ::
    "State \<Rightarrow> TTBR0_EL1 \<Rightarrow> State"
  where
    "write_TTBR0_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> TTBR0_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_TTBR1_EL1 ::
    "State \<Rightarrow> TTBR1_EL1 \<Rightarrow> State"
  where
    "write_TTBR1_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> TTBR1_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_TCR_EL1 ::
    "State \<Rightarrow> TCR_EL1 \<Rightarrow> State"
  where
    "write_TCR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> TCR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_ESR_EL1 ::
    "State \<Rightarrow> ESR_EL1 \<Rightarrow> State"
  where
    "write_ESR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> ESR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_FAR_EL1 ::
    "State \<Rightarrow> FAR_EL1 \<Rightarrow> State"
  where
    "write_FAR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> FAR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_AFSR0_EL1 ::
    "State \<Rightarrow> AFSR0_EL1 \<Rightarrow> State"
  where
    "write_AFSR0_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> AFSR0_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_AFSR1_EL1 ::
    "State \<Rightarrow> AFSR1_EL1 \<Rightarrow> State"
  where
    "write_AFSR1_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> AFSR1_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_MAIR_EL1 ::
    "State \<Rightarrow> MAIR_EL1 \<Rightarrow> State"
  where
    "write_MAIR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> MAIR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_AMAIR_EL1 ::
    "State \<Rightarrow> AMAIR_EL1 \<Rightarrow> State"
  where
    "write_AMAIR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> AMAIR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_CONTEXTIDR_EL1 ::
    "State \<Rightarrow> CONTEXTIDR_EL1 \<Rightarrow> State"
  where
    "write_CONTEXTIDR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> CONTEXTIDR_EL1 := v \<rparr> \<rparr> \<rparr>"

definition write_ACTLR_EL1 ::
    "State \<Rightarrow> ACTLR_EL1 \<Rightarrow> State"
  where
    "write_ACTLR_EL1 s v =
      s\<lparr> regs_state :=
        (regs_state s)\<lparr> sys_regs_el1 :=
          (sys_regs_el1 (regs_state s))\<lparr> ACTLR_EL1 := v \<rparr> \<rparr> \<rparr>"

subsection \<open> Identifier Register \<close>

definition read_ID_AA64PFR0_EL1 ::
    "State \<Rightarrow> ID_AA64PFR0_EL1"
  where
    "read_ID_AA64PFR0_EL1 s =
      (ID_AA64PFR0_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64PFR1_EL1 ::
    "State \<Rightarrow> ID_AA64PFR1_EL1"
  where
    "read_ID_AA64PFR1_EL1 s =
      (ID_AA64PFR1_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64ZFR0_EL1 ::
    "State \<Rightarrow> ID_AA64ZFR0_EL1"
  where
    "read_ID_AA64ZFR0_EL1 s =
      (ID_AA64ZFR0_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64DFR0_EL1 ::
    "State \<Rightarrow> ID_AA64DFR0_EL1"
  where
    "read_ID_AA64DFR0_EL1 s =
      (ID_AA64DFR0_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64DFR1_EL1 ::
    "State \<Rightarrow> ID_AA64DFR1_EL1"
  where
    "read_ID_AA64DFR1_EL1 s =
      (ID_AA64DFR1_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64AFR0_EL1 ::
    "State \<Rightarrow> ID_AA64AFR0_EL1"
  where
    "read_ID_AA64AFR0_EL1 s =
      (ID_AA64AFR0_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64AFR1_EL1 ::
    "State \<Rightarrow> ID_AA64AFR1_EL1"
  where
    "read_ID_AA64AFR1_EL1 s =
      (ID_AA64AFR1_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64ISAR0_EL1 ::
    "State \<Rightarrow> ID_AA64ISAR0_EL1"
  where
    "read_ID_AA64ISAR0_EL1 s =
      (ID_AA64ISAR0_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64ISAR1_EL1 ::
    "State \<Rightarrow> ID_AA64ISAR1_EL1"
  where
    "read_ID_AA64ISAR1_EL1 s =
      (ID_AA64ISAR1_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64ISAR2_EL1 ::
    "State \<Rightarrow> ID_AA64ISAR2_EL1"
  where
    "read_ID_AA64ISAR2_EL1 s =
      (ID_AA64ISAR2_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64MMFR0_EL1 ::
    "State \<Rightarrow> ID_AA64MMFR0_EL1"
  where
    "read_ID_AA64MMFR0_EL1 s =
      (ID_AA64MMFR0_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64MMFR1_EL1 ::
    "State \<Rightarrow> ID_AA64MMFR1_EL1"
  where
    "read_ID_AA64MMFR1_EL1 s =
      (ID_AA64MMFR1_EL1 (ID_regs (regs_state s)))"

definition read_ID_AA64MMFR2_EL1 ::
    "State \<Rightarrow> ID_AA64MMFR2_EL1"
  where
    "read_ID_AA64MMFR2_EL1 s =
      (ID_AA64MMFR2_EL1 (ID_regs (regs_state s)))"

end
