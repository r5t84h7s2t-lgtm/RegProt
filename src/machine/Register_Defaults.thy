theory Register_Defaults
  imports
    Main
    "Register_Access"
begin

definition default_sys_regs_el1 :: "Sys_Regs_EL1"
  where "default_sys_regs_el1 \<equiv>
    \<lparr>
      SCTLR_EL1 = word64_to_sctlr_el1 0,
      TTBR0_EL1 = word64_to_ttbr0_el1 0,
      TTBR1_EL1 = word64_to_ttbr1_el1 0,
      TCR_EL1 = word64_to_tcr_el1 0,
      ESR_EL1 = word64_to_esr_el1 0,
      FAR_EL1 = word64_to_far_el1 0,
      AFSR0_EL1 = word64_to_afsr0_el1 0,
      AFSR1_EL1 = word64_to_afsr1_el1 0,
      MAIR_EL1 = word64_to_mair_el1 0,
      AMAIR_EL1 = word64_to_amair_el1 0,
      CONTEXTIDR_EL1 = word64_to_contextidr_el1 0,
      ACTLR_EL1 = word64_to_actlr_el1 0
    \<rparr>"

definition default_sys_regs_el2 :: "Sys_Regs_EL2" where
"default_sys_regs_el2 \<equiv>
  \<lparr>
    HCR_EL2 = \<lparr>Value = 0\<rparr>
  \<rparr>"

definition default_ID_AA64PFR0_EL1 :: "ID_AA64PFR0_EL1"
  where "default_ID_AA64PFR0_EL1 \<equiv> \<lparr>
CSV3 = CSV3_Undisclosed,
CSV2 = CSV2_Undisclosed,
RME = RME_None,
DIT = DIT_AArch64_Unsupported,
AMU = AMU_None,
MPAM = MPAM_v0,
SEL2 = SEL2_Unsupported,
SVE = SVE_Unsupported,
RAS = RAS_None,
GIC = GIC_None,
AdvSIMD = AdvSIMD_None,
FP = FP_None,
EL3 = EL3_None,
EL2 = EL2_None,
EL1 = EL1_AArch64_Only,
EL0 = EL0_AArch64_Only
  \<rparr>"

definition default_ID_AA64PFR1_EL1 :: "ID_AA64PFR1_EL1"
  where "default_ID_AA64PFR1_EL1 \<equiv> \<lparr>
PFAR = PFAR_Unsupported,
DF2 = DF2_Unsupported,
MTEX = MTEX_Unsupported,
ID_AA64PFR1_EL1.THE = THE_Unsupported,
GCS = GCS_Unsupported,
MTE_frac = MTE_Async_Unsupported,
NMI = NMI_Unsupported,
CSV2_frac = CSV2_frac_Undisclosed_v1p1,
RNDR_trap = RNDR_trap_Unsupported,
SME = SME_None,
MPAM_frac = MPAM_Minor_v0,
RAS_frac = RAS_frac_v1p0,
MTE = MTE_None,
SSBS = SSBS_None,
BT = BT_Unsupported
  \<rparr>"


definition default_ID_AA64ZFR0_EL1 :: "ID_AA64ZFR0_EL1"
  where "default_ID_AA64ZFR0_EL1 \<equiv> \<lparr>
F64MM = F64MM_Unsupported,
F32MM = F32MM_Unsupported,
I8MM = I8MM_Unsupported,
SM4 = SM4_Unsupported,
SHA3 = SHA3_Unsupported,
B16B16 = B16B16_Unsupported,
BF16 = BF16_None,
BitPerm = BitPerm_Unsupported,
EltPerm = EltPerm_Unsupported,
AES = SVE_AES,
SVEver = FEAT_SVE2
  \<rparr>"


definition default_ID_AA64DFR0_EL1 :: "ID_AA64DFR0_EL1"
  where "default_ID_AA64DFR0_EL1 \<equiv> \<lparr>
HPMN0 = HPMN0_Unpredictable,
ExtTrcBuff = ExtTrcBuff_Unsupported,
BRBE = BRBE_None,
MTPMU = MTPMU_None_ImpDef,
TraceBuffer = TraceBuffer_Unsupported,
TraceFilt = TraceFilt_Unsupported,
DoubleLock = DoubleLock_Supported,
PMSVer = PMS_None,
CTX_CMPs = 0b0000,
SEBEP = SEBEP_Unsupported,
WRPs = 0b0000,
PMSS = PMSS_Unsupported,
BRPs = 0b0000,
PMUVer = PMU_None,
TraceVer = TraceVer_Unsupported,
DebugVer = Debug_v8p0
  \<rparr>"


definition default_ID_AA64DFR1_EL1 :: "ID_AA64DFR1_EL1"
  where "default_ID_AA64DFR1_EL1 \<equiv> \<lparr>
ABL_CMPs = 0b0000,
DPFZS = DPFZS_Unaffected,
EBEP = EBEP_Unsupported,
ITE = ITE_Unsupported,
ABLE = ABLE_Unsupported,
PMICNTR = PMICNTR_Unsupported,
SPMU = SPMU_None,
CTX_CMPs = 0b000000,
WRPs = 0b000000,
BRPs = 0b000000,
SYSPMUID = 0b00000
  \<rparr>"


definition default_ID_AA64AFR0_EL1 :: "ID_AA64AFR0_EL1"
  where "default_ID_AA64AFR0_EL1 \<equiv> \<lparr>
UNDEFINED = 0x00000000
  \<rparr>"

definition default_ID_AA64AFR1_EL1 :: "ID_AA64AFR1_EL1"
  where "default_ID_AA64AFR1_EL1 \<equiv> \<lparr>
RES0 = 0x0000000000000000
  \<rparr>"

definition default_ID_AA64ISAR0_EL1 :: "ID_AA64ISAR0_EL1"
  where "default_ID_AA64ISAR0_EL1 \<equiv> \<lparr>
RNDR = RNDR_Unsupported,
TLB = TLB_None,
TS = TS_None,
FHM = FHM_Unsupported,
DP = DP_Unsupported,
SM4 = SM4_Unsupported,
SM3 = SM3_Unsupported,
SHA3 = SHA3_Unsupported,
RDM = RDM_Unsupported,
TME = TME_Unsupported,
Atomic = Atomic_None,
CRC32 = CRC32_Unsupported,
SHA2 = SHA2_None,
SHA1 = SHA1_Unsupported,
AES = AES_None
  \<rparr>"

definition default_ID_AA64ISAR1_EL1 :: "ID_AA64ISAR1_EL1"
  where "default_ID_AA64ISAR1_EL1 \<equiv> \<lparr>
LS64 = LS64_None,
XS = XS_Unsupported,
I8MM = I8MM_Unsupported,
DGH = DGH_Unsupported,
BF16 = BF16_None,
SPECRES = SPECRES_None,
SB = SB_Unsupported,
FRINTTS = FRINTTS_Unsupported,
GPI = GPI_Unsupported,
GPA = GPA_Unsupported,
LRCPC = LRCPC_None,
FCMA = FCMA_Unsupported,
JSCVT = JSCVT_Unsupported,
API = \<lparr> address_auth = False, epac = False, pauth2 = False,
       fpac = False, fpac_combine = False, pauth_lr = False \<rparr>,
APA = \<lparr> address_auth = False, epac = False, pauth2 = False,
       fpac = False, fpac_combine = False, pauth_lr = False \<rparr>,
DPB = DPB_None
  \<rparr>"

definition default_ID_AA64ISAR2_EL1 :: "ID_AA64ISAR2_EL1"
  where "default_ID_AA64ISAR2_EL1 \<equiv> \<lparr>
ATS1A = ATS1A_Unsupported,
LUT = LUT_Unsupported,
CSSC = CSSC_Unsupported,
RPRFM = RPRFM_Unsupported,
PRFMSLC = PRFMSLC_Unsupported,
SYSINSTR_128 = SYSINSTR_128_Unsupported,
SYSREG_128 = SYSREG_128_Unsupported,
CLRBHB = CLRBHB_Unsupported,
PAC_frac = PAC_frac_Dependent,
BC = BC_Unsupported,
MOPS = MOPS_Unsupported,
APA3 = \<lparr> address_auth_qarma3 = False, epac = False, pauth2 = False,
        fpac = False, fpac_combine = False, pauth_lr = False \<rparr>,
GPA3 = GPA3_Unsupported,
RPRES = RPRES_8bit,
WFxT = WFxT_Unsupported
  \<rparr>"

definition default_ID_AA64MMFR0_EL1 :: "ID_AA64MMFR0_EL1"
  where "default_ID_AA64MMFR0_EL1 \<equiv> \<lparr>
ECV = ECV_None,
FGT = FGT_None,
ExS = ExS_AlwaysSync,
TGran4_2 = TGran4_2_Delegated,
TGran64_2 = TGran64_2_Delegated,
TGran16_2 = TGran16_2_Delegated,
TGran4 = TGran4_Supported,
TGran64 = TGran64_Supported,
TGran16 = TGran16_Unsupported,
BigEndEL0 = BigEndEL0_Unsupported,
SNSMem = SNSMem_Unsupported,
BigEnd = BigEnd_Unsupported,
ASIDBits = ASID_8bit,
PARange = PA_48bit
  \<rparr>"

definition default_ID_AA64MMFR1_EL1 :: "ID_AA64MMFR1_EL1"
  where "default_ID_AA64MMFR1_EL1 \<equiv> \<lparr>
ECBHB = ECBHB_Undisclosed,
CMOW = CMOW_Unsupported,
TIDCP1 = TIDCP1_Unsupported,
nTLBPA = nTLBPA_NonCoherent,
AFP = AFP_Unsupported,
HCX = HCX_Unsupported,
ETS = ETS_Unsupported,
TWED = TWED_Unsupported,
XNX = XNX_Unsupported,
SpecSEI = SpecSEI_Never,
PAN = PAN_None,
LO = LO_Unsupported,
HPDS = HPDS_None,
VH = VH_Unsupported,
VMIDBits = VMID_8bit,
HAFDBS = HAFDBS_None
  \<rparr>"

definition default_ID_AA64MMFR2_EL1 :: "ID_AA64MMFR2_EL1"
  where "default_ID_AA64MMFR2_EL1 \<equiv> \<lparr>
E0PD = E0PD_Unsupported,
EVT = EVT_None,
BBM = BBM_Level0,
TTL = TTL_RES0,
FWB = FWB_Unsupported,
IDS = IDS_EC_0x0,
AT = AT_Unsupported,
ST = ST_MaxTSZ_39,
NV = NV_Delegated,
CCIDX = CCIDX_32bit,
VARange = VA_48bit,
IESB = IESB_Unsupported,
LSM = LSM_Unsupported,
UAO = UAO_Unsupported,
CnP = CnP_Unsupported
  \<rparr>"

definition default_ID_regs :: "ID_Regs_EL1"
  where "default_ID_regs \<equiv>
    \<lparr>
      ID_AA64PFR0_EL1 = default_ID_AA64PFR0_EL1,
      ID_AA64PFR1_EL1 = default_ID_AA64PFR1_EL1,
      ID_AA64ZFR0_EL1 = default_ID_AA64ZFR0_EL1,
      ID_AA64DFR0_EL1 = default_ID_AA64DFR0_EL1,
      ID_AA64DFR1_EL1 = default_ID_AA64DFR1_EL1,
      ID_AA64AFR0_EL1 = default_ID_AA64AFR0_EL1,
      ID_AA64AFR1_EL1 = default_ID_AA64AFR1_EL1,
      ID_AA64ISAR0_EL1 = default_ID_AA64ISAR0_EL1,
      ID_AA64ISAR1_EL1 = default_ID_AA64ISAR1_EL1,
      ID_AA64ISAR2_EL1 = default_ID_AA64ISAR2_EL1,
      ID_AA64MMFR0_EL1 = default_ID_AA64MMFR0_EL1,
      ID_AA64MMFR1_EL1 = default_ID_AA64MMFR1_EL1,
      ID_AA64MMFR2_EL1 = default_ID_AA64MMFR2_EL1
    \<rparr>"

definition default_protected_reg_state :: "Protected_Reg_State"
  where "default_protected_reg_state \<equiv> \<lparr>
    TCR_EL1_State = Unset,
    MAIR_EL1_State = Unset,
    TTBR1_EL1_State = Unset,
    TTBR1_EL1_Saved = None
  \<rparr>"

end
