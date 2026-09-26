theory RegProt_State
  imports
    Main
    "HOL-Library.Word"
    "AArch64_Registers"
begin

section \<open> System State \<close>

subsection \<open> Register State \<close>

record Protected_Reg_State =
TCR_EL1_State :: Sys_Reg_State
MAIR_EL1_State :: Sys_Reg_State
TTBR1_EL1_State :: Sys_Reg_State
TTBR1_EL1_Saved :: "TTBR1_EL1 option"

record Sys_Regs_EL1 =
SCTLR_EL1 :: SCTLR_EL1
TTBR0_EL1 :: TTBR0_EL1
TTBR1_EL1 :: TTBR1_EL1
TCR_EL1 :: TCR_EL1
ESR_EL1 :: ESR_EL1
FAR_EL1 :: FAR_EL1
AFSR0_EL1 :: AFSR0_EL1
AFSR1_EL1 :: AFSR1_EL1
MAIR_EL1 :: MAIR_EL1
AMAIR_EL1 :: AMAIR_EL1
CONTEXTIDR_EL1 :: CONTEXTIDR_EL1
ACTLR_EL1 :: ACTLR_EL1

record Sys_Regs_EL2 =
HCR_EL2 :: HCR_EL2

datatype Reg_Syndrome =
SCTLR_EL1_Syndrome |
TTBR0_EL1_Syndrome |
TTBR1_EL1_Syndrome |
TCR_EL1_Syndrome |
ESR_EL1_Syndrome |
FAR_EL1_Syndrome |
AFSR0_EL1_Syndrome |
AFSR1_EL1_Syndrome |
MAIR_EL1_Syndrome |
AMAIR_EL1_Syndrome |
CONTEXTIDR_EL1_Syndrome |
ACTLR_EL1_Syndrome |
ID_AA64PFR0_EL1_Syndrome |
ID_AA64PFR1_EL1_Syndrome |
ID_AA64ZFR0_EL1_Syndrome |
ID_AA64DFR0_EL1_Syndrome |
ID_AA64DFR1_EL1_Syndrome |
ID_AA64AFR0_EL1_Syndrome |
ID_AA64AFR1_EL1_Syndrome |
ID_AA64ISAR0_EL1_Syndrome |
ID_AA64ISAR1_EL1_Syndrome |
ID_AA64ISAR2_EL1_Syndrome |
ID_AA64MMFR0_EL1_Syndrome |
ID_AA64MMFR1_EL1_Syndrome |
ID_AA64MMFR2_EL1_Syndrome |
Other_Syndrome

record ID_Regs_EL1 =
ID_AA64PFR0_EL1 :: ID_AA64PFR0_EL1
ID_AA64PFR1_EL1 :: ID_AA64PFR1_EL1
ID_AA64ZFR0_EL1 :: ID_AA64ZFR0_EL1
ID_AA64DFR0_EL1 :: ID_AA64DFR0_EL1
ID_AA64DFR1_EL1 :: ID_AA64DFR1_EL1
ID_AA64AFR0_EL1 :: ID_AA64AFR0_EL1
ID_AA64AFR1_EL1 :: ID_AA64AFR1_EL1
ID_AA64ISAR0_EL1 :: ID_AA64ISAR0_EL1
ID_AA64ISAR1_EL1 :: ID_AA64ISAR1_EL1
ID_AA64ISAR2_EL1 :: ID_AA64ISAR2_EL1
ID_AA64MMFR0_EL1 :: ID_AA64MMFR0_EL1
ID_AA64MMFR1_EL1 :: ID_AA64MMFR1_EL1
ID_AA64MMFR2_EL1 :: ID_AA64MMFR2_EL1

record Regs =
sys_regs_el1 :: Sys_Regs_EL1
sys_regs_el2 :: Sys_Regs_EL2
ID_regs :: ID_Regs_EL1
protected_reg_state :: Protected_Reg_State

type_synonym Regs_State = Regs

record Sys_Config =
is_aarch64_config :: bool
use_LPAE_config :: bool

record State=
regs_state :: Regs_State
sys_config :: Sys_Config

section \<open> Events \<close>

datatype Event =
WRITE_SYSREG Reg_Syndrome Reg_Value |
READ_SYSREG Reg_Syndrome |
READ_IDREG Reg_Syndrome

end
