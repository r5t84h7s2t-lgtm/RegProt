theory AArch64_Registers
  imports
    Main
    "HOL-Library.Word"
begin

datatype Sys_Reg_State = Unset | LockDown

type_synonym Reg_Value = "64 word"

section \<open> Bits Spec \<close>

subsection \<open> SCTLR_EL1 \<close>


datatype tcf_mode =
  TCF_NoEffect        
| TCF_Sync            
| TCF_Async           
| TCF_SyncReadAsyncWrite 


definition tcf_mode_to_bits :: "tcf_mode \<Rightarrow> 2 word" where
  "tcf_mode_to_bits mode \<equiv> case mode of
     TCF_NoEffect         \<Rightarrow> 0b00
   | TCF_Sync             \<Rightarrow> 0b01
   | TCF_Async            \<Rightarrow> 0b10
   | TCF_SyncReadAsyncWrite \<Rightarrow> 0b11"


definition bits_to_tcf_mode :: "2 word \<Rightarrow> tcf_mode" where
  "bits_to_tcf_mode w \<equiv>
     if w = 0b00 then TCF_NoEffect else
     if w = 0b01 then TCF_Sync else
     if w = 0b10 then TCF_Async else
     TCF_SyncReadAsyncWrite"

subsection \<open> TCR_EL1 \<close>

datatype ips_val =
  IPS_32b  
| IPS_36b  
| IPS_40b  
| IPS_42b  
| IPS_44b  
| IPS_48b  
| IPS_52b  
| IPS_56b  

fun ips_to_bits :: "ips_val \<Rightarrow> 3 word" where
  "ips_to_bits IPS_32b = 0b000"
| "ips_to_bits IPS_36b = 0b001"
| "ips_to_bits IPS_40b = 0b010"
| "ips_to_bits IPS_42b = 0b011"
| "ips_to_bits IPS_44b = 0b100"
| "ips_to_bits IPS_48b = 0b101"
| "ips_to_bits IPS_52b = 0b110"
| "ips_to_bits IPS_56b = 0b111"

definition bits_to_ips :: "3 word \<Rightarrow> ips_val" where
  "bits_to_ips w \<equiv>
     if w = 0b000 then IPS_32b else
     if w = 0b001 then IPS_36b else
     if w = 0b010 then IPS_40b else
     if w = 0b011 then IPS_42b else
     if w = 0b100 then IPS_44b else
     if w = 0b101 then IPS_48b else
     if w = 0b110 then IPS_52b else
     IPS_56b"


datatype tg_granule =
  TG_4KB
| TG_16KB
| TG_64KB

fun granule_to_bits :: "tg_granule \<Rightarrow> 2 word" where
  "granule_to_bits TG_4KB  = 0b10"
| "granule_to_bits TG_16KB = 0b01"
| "granule_to_bits TG_64KB = 0b11"


definition bits_to_granule :: "2 word \<Rightarrow> tg_granule" where
  "bits_to_granule w \<equiv>
     if w = 0b01 then TG_16KB else
     if w = 0b10 then TG_4KB else
     TG_64KB"

datatype shareability_domain =
  NonShareable
| OuterShareable
| InnerShareable

fun domain_to_bits :: "shareability_domain \<Rightarrow> 2 word" where
  "domain_to_bits NonShareable    = 0b00"
| "domain_to_bits OuterShareable  = 0b10"
| "domain_to_bits InnerShareable  = 0b11"

definition bits_to_domain :: "2 word \<Rightarrow> shareability_domain" where
  "bits_to_domain w \<equiv>
     if w = 0b00 then NonShareable else
     if w = 0b10 then OuterShareable else
     InnerShareable"

datatype cacheability =
  NC        
| WB_RA_WA  
| WT_RA_nWA 
| WB_RA_nWA 

fun cacheability_to_bits :: "cacheability \<Rightarrow> 2 word" where
  "cacheability_to_bits NC        = 0b00"
| "cacheability_to_bits WB_RA_WA  = 0b01"
| "cacheability_to_bits WT_RA_nWA = 0b10"
| "cacheability_to_bits WB_RA_nWA = 0b11"

definition bits_to_cacheability_word :: "2 word \<Rightarrow> cacheability" where
  "bits_to_cacheability_word w \<equiv>
     if w = 0b00 then NC else
     if w = 0b01 then WB_RA_WA else
     if w = 0b10 then WT_RA_nWA else
     WB_RA_nWA"

subsection \<open> MAIR_EL1 \<close>

datatype allocate_policy = NoAllocate | Allocate

datatype device_memory_type =
  Device_nGnRnE
| Device_nGnRE
| Device_nGRE
| Device_GRE

type_synonym read_policy = "allocate_policy"
type_synonym write_policy = "allocate_policy"

datatype cacheability_policy =
  Non_Cacheable
| Write_Through_Transient
| Write_Back_Transient
| Write_Through_Non_Transient
| Write_Back_Non_Transient

record normal_cacheability =
  policy :: cacheability_policy
  read_alloc :: read_policy
  write_alloc :: write_policy

type_synonym outer = normal_cacheability
type_synonym inner = normal_cacheability

datatype mair_attribute =
    
    Device device_memory_type

    
  | Normal outer inner

  | Device_XS0 device_memory_type 
  | Normal_NC_XS0                 
  | Normal_WT_XS0                 
  | Tagged_Normal_MTE2            

subsection \<open> ESR_EL1 \<close>

datatype instruction_length =
  Instr_16bit
  | Instr_32bit

fun instruction_length_to_bits :: "instruction_length \<Rightarrow> 1 word" where
  "instruction_length_to_bits Instr_16bit = 0b0"
| "instruction_length_to_bits Instr_32bit = 0b1"

definition bits_to_instruction_length :: "1 word \<Rightarrow> instruction_length" where
  "bits_to_instruction_length w \<equiv>
     if w = 0b0 then Instr_16bit else
     Instr_32bit"

subsection \<open> ID_PFR0_EL1 \<close>

datatype ras_level =
  RAS_None      
| RAS_v1        
| RAS_v1_1      
| RAS_v2        

datatype dit_support =
  DIT_Unsupported  
  | DIT_Supported    

datatype csv2_version =
  CSV2_Undisclosed  
| CSV2_v1           
| CSV2_v1p1         

definition csv2_version_to_bits :: "csv2_version \<Rightarrow> 4 word" where
  "csv2_version_to_bits ver \<equiv> case ver of
     CSV2_Undisclosed \<Rightarrow> 0b0000
   | CSV2_v1          \<Rightarrow> 0b0001
   | CSV2_v1p1        \<Rightarrow> 0b0010"


definition bits_to_csv2_version :: "4 word \<Rightarrow> csv2_version option" where
  "bits_to_csv2_version w \<equiv>
if w = 0b0000 then Some CSV2_Undisclosed
else if w = 0b0001 then Some CSV2_v1
else if w = 0b0010 then Some CSV2_v1p1
else None "

datatype t32ee_support =
  T32EE_None          
| T32EE_Implemented   


definition t32ee_support_to_bits :: "t32ee_support \<Rightarrow> 4 word" where
  "t32ee_support_to_bits support \<equiv> case support of
     T32EE_None        \<Rightarrow> 0b0000
   | T32EE_Implemented \<Rightarrow> 0b0001"

datatype jazelle_support =
  Jazelle_None      
| Jazelle_Basic     
| Jazelle_ClearCV   


definition bits_to_jazelle_support_alt :: "4 word \<Rightarrow> jazelle_support option" where
  "bits_to_jazelle_support_alt w \<equiv>
     if w = 0b0000 then Some Jazelle_None else
     if w = 0b0001 then Some Jazelle_Basic else
     if w = 0b0010 then Some Jazelle_ClearCV else
     None" 

datatype t32_support =
  T32_None          
| T32_pre_Thumb2    
| T32_with_Thumb2   


definition t32_support_to_bits :: "t32_support \<Rightarrow> 4 word" where
  "t32_support_to_bits support \<equiv> case support of
     T32_None        \<Rightarrow> 0b0000
   | T32_pre_Thumb2  \<Rightarrow> 0b0001
   | T32_with_Thumb2 \<Rightarrow> 0b0011"


definition bits_to_t32_support :: "4 word \<Rightarrow> t32_support option" where
  "bits_to_t32_support w \<equiv>
     if w = 0b0000 then Some T32_None else
     if w = 0b0001 then Some T32_pre_Thumb2 else
     if w = 0b0011 then Some T32_with_Thumb2 else
     None" 

datatype a32_support =
  A32_None          
| A32_Implemented   




definition a32_support_to_bits :: "a32_support \<Rightarrow> 4 word" where
  "a32_support_to_bits support \<equiv> case support of
     A32_None        \<Rightarrow> 0b0000
   | A32_Implemented \<Rightarrow> 0b0001"


definition bits_to_a32_support :: "4 word \<Rightarrow> a32_support option" where
  "bits_to_a32_support w \<equiv>
     if w = 0b0000 then Some A32_None else
     if w = 0b0001 then Some A32_Implemented else
     None" 

subsection \<open> ID_PFR1_EL1 \<close>


datatype virt_ext_support =
  VirtExt_None        
| VirtExt_Supported   


definition virt_ext_support_to_bits :: "virt_ext_support \<Rightarrow> 4 word" where
  "virt_ext_support_to_bits support \<equiv> case support of
     VirtExt_None      \<Rightarrow> 0b0000
   | VirtExt_Supported \<Rightarrow> 0b0001"


definition bits_to_virt_ext_support :: "4 word \<Rightarrow> virt_ext_support option" where
  "bits_to_virt_ext_support w \<equiv>
     if w = 0b0000 then Some VirtExt_None else
     if w = 0b0001 then Some VirtExt_Supported else
     None" 


datatype sec_ext_support =
  SecExt_None        
| SecExt_Base        
| SecExt_MemAccess   


definition sec_ext_support_to_bits :: "sec_ext_support \<Rightarrow> 4 word" where
  "sec_ext_support_to_bits support \<equiv> case support of
     SecExt_None      \<Rightarrow> 0b0000
   | SecExt_Base      \<Rightarrow> 0b0001
   | SecExt_MemAccess \<Rightarrow> 0b0010"


definition bits_to_sec_ext_support :: "4 word \<Rightarrow> sec_ext_support option" where
  "bits_to_sec_ext_support w \<equiv>
     if w = 0b0000 then Some SecExt_None else
     if w = 0b0001 then Some SecExt_Base else
     if w = 0b0010 then Some SecExt_MemAccess else
     None" 


datatype gen_timer_support =
  GenTimer_None   
| GenTimer_Base   
| GenTimer_Ext    


definition gen_timer_support_to_bits :: "gen_timer_support \<Rightarrow> 4 word" where
  "gen_timer_support_to_bits support \<equiv> case support of
     GenTimer_None \<Rightarrow> 0b0000
   | GenTimer_Base \<Rightarrow> 0b0001
   | GenTimer_Ext  \<Rightarrow> 0b0010"


definition bits_to_gen_timer_support :: "4 word \<Rightarrow> gen_timer_support option" where
  "bits_to_gen_timer_support w \<equiv>
     if w = 0b0000 then Some GenTimer_None else
     if w = 0b0001 then Some GenTimer_Base else
     if w = 0b0010 then Some GenTimer_Ext else
     None" 


datatype virtualization_support =
  Virt_None   
| Virt_Full   


definition virtualization_support_to_bits :: "virtualization_support \<Rightarrow> 4 word" where
  "virtualization_support_to_bits support \<equiv> case support of
     Virt_None \<Rightarrow> 0b0000
   | Virt_Full \<Rightarrow> 0b0001"


definition bits_to_virtualization_support :: "4 word \<Rightarrow> virtualization_support option" where
  "bits_to_virtualization_support w \<equiv>
     if w = 0b0000 then Some Virt_None else
     if w = 0b0001 then Some Virt_Full else
     None" 


datatype mprog_model =
  MProg_Unsupported  
| MProg_TwoStack     


definition mprog_model_to_bits :: "mprog_model \<Rightarrow> 4 word" where
  "mprog_model_to_bits model \<equiv> case model of
     MProg_Unsupported \<Rightarrow> 0b0000
   | MProg_TwoStack      \<Rightarrow> 0b0010"


definition bits_to_mprog_model :: "4 word \<Rightarrow> mprog_model option" where
  "bits_to_mprog_model w \<equiv>
     if w = 0b0000 then Some MProg_Unsupported else
     if w = 0b0010 then Some MProg_TwoStack else
     None" 

datatype security_support =
  Sec_None       
| Sec_Base       
| Sec_Base_RFR   


definition security_support_to_bits :: "security_support \<Rightarrow> 4 word" where
  "security_support_to_bits support \<equiv> case support of
     Sec_None       \<Rightarrow> 0b0000
   | Sec_Base       \<Rightarrow> 0b0001
   | Sec_Base_RFR   \<Rightarrow> 0b0010"


definition bits_to_security_support :: "4 word \<Rightarrow> security_support option" where
  "bits_to_security_support w \<equiv>
     if w = 0b0000 then Some Sec_None else
     if w = 0b0001 then Some Sec_Base else
     None"


datatype prog_model_support =
  ProgMod_Unsupported
| ProgMod_Supported


definition prog_model_support_to_bits :: "prog_model_support \<Rightarrow> 4 word" where
  "prog_model_support_to_bits support \<equiv> case support of
     ProgMod_Unsupported \<Rightarrow> 0b0000
   | ProgMod_Supported   \<Rightarrow> 0b0001"


definition bits_to_prog_model_support :: "4 word \<Rightarrow> prog_model_support option" where
  "bits_to_prog_model_support w \<equiv>
     if w = 0b0000 then Some ProgMod_Unsupported else
     if w = 0b0001 then Some ProgMod_Supported else
     None" 


subsection \<open> ID_DFR0_EL1 \<close>



subsection \<open> ID_AFR0_EL1 \<close>

subsection \<open> ID_MMFR0_EL1 \<close>

subsection \<open> ID_MMFR1_EL1 \<close>

subsection \<open> ID_MMFR2_EL1 \<close>

subsection \<open> ID_MMFR3_EL1 \<close>

subsection \<open> ID_ISAR0_EL1 \<close>

subsection \<open> ID_ISAR1_EL1 \<close>

subsection \<open> ID_ISAR2_EL1 \<close>

subsection \<open> ID_ISAR3_EL1 \<close>

subsection \<open> ID_ISAR4_EL1 \<close>

subsection \<open> ID_ISAR5_EL1 \<close>

subsection \<open> ID_MMFR4_EL1 \<close>

subsection \<open> ID_ISAR6_EL1 \<close>

subsection \<open> MVFR0_EL1 \<close>

subsection \<open> MVFR1_EL1 \<close>

subsection \<open> MVFR2_EL1 \<close>

subsection \<open> ID_PFR2_EL1 \<close>

subsection \<open> ID_DFR1_EL1 \<close>

subsection \<open> ID_MMFR5_EL1 \<close>

subsection \<open> ID_AA64PFR0_EL1 \<close>

datatype csv3_behavior =
  CSV3_Undisclosed  
| CSV3_Guaranteed   


definition csv3_behavior_to_bits :: "csv3_behavior \<Rightarrow> 4 word" where
  "csv3_behavior_to_bits behavior \<equiv> case behavior of
     CSV3_Undisclosed \<Rightarrow> 0b0000
   | CSV3_Guaranteed  \<Rightarrow> 0b0001"


definition bits_to_csv3_behavior :: "4 word \<Rightarrow> csv3_behavior option" where
  "bits_to_csv3_behavior w \<equiv>
     if w = 0b0000 then Some CSV3_Undisclosed else
     if w = 0b0001 then Some CSV3_Guaranteed else
     None" 


datatype csv2_level =
  CSV2_Undisclosed 
| CSV2_Base        
| CSV2_v2          
| CSV2_v3          


definition csv2_level_to_bits :: "csv2_level \<Rightarrow> 4 word" where
  "csv2_level_to_bits lvl \<equiv> case lvl of
     CSV2_Undisclosed \<Rightarrow> 0b0000
   | CSV2_Base        \<Rightarrow> 0b0001
   | CSV2_v2          \<Rightarrow> 0b0010
   | CSV2_v3          \<Rightarrow> 0b0011"


definition bits_to_csv2_level :: "4 word \<Rightarrow> csv2_level option" where
  "bits_to_csv2_level w \<equiv>
     if w = 0b0000 then Some CSV2_Undisclosed else
     if w = 0b0001 then Some CSV2_Base else
     if w = 0b0010 then Some CSV2_v2 else
     if w = 0b0011 then Some CSV2_v3 else
     None" 



datatype rme_version =
  RME_None       
| RME_v1         
| RME_v1_GPC2    


definition rme_version_to_bits :: "rme_version \<Rightarrow> 4 word" where
  "rme_version_to_bits ver \<equiv> case ver of
     RME_None      \<Rightarrow> 0b0000
   | RME_v1        \<Rightarrow> 0b0001
   | RME_v1_GPC2   \<Rightarrow> 0b0010"


definition bits_to_rme_version :: "4 word \<Rightarrow> rme_version option" where
  "bits_to_rme_version w \<equiv>
     if w = 0b0000 then Some RME_None else
     if w = 0b0001 then Some RME_v1 else
     if w = 0b0010 then Some RME_v1_GPC2 else
     None" 


datatype dit_aarch64_support =
  DIT_AArch64_Unsupported
| DIT_AArch64_Supported


definition dit_aarch64_support_to_bits :: "dit_aarch64_support \<Rightarrow> 4 word" where
  "dit_aarch64_support_to_bits support \<equiv> case support of
     DIT_AArch64_Unsupported \<Rightarrow> 0b0000
   | DIT_AArch64_Supported   \<Rightarrow> 0b0001"


definition bits_to_dit_aarch64_support :: "4 word \<Rightarrow> dit_aarch64_support option" where
  "bits_to_dit_aarch64_support w \<equiv>
     if w = 0b0000 then Some DIT_AArch64_Unsupported else
     if w = 0b0001 then Some DIT_AArch64_Supported else
     None" 


datatype amu_version =
  AMU_None   
| AMU_v1     
| AMU_v1p1   


definition amu_version_to_bits :: "amu_version \<Rightarrow> 4 word" where
  "amu_version_to_bits ver \<equiv> case ver of
     AMU_None   \<Rightarrow> 0b0000
   | AMU_v1     \<Rightarrow> 0b0001
   | AMU_v1p1   \<Rightarrow> 0b0010"


definition bits_to_amu_version :: "4 word \<Rightarrow> amu_version option" where
  "bits_to_amu_version w \<equiv>
     if w = 0b0000 then Some AMU_None else
     if w = 0b0001 then Some AMU_v1 else
     if w = 0b0010 then Some AMU_v1p1 else
     None" 


datatype mpam_major_version =
  MPAM_v0  
| MPAM_v1  


definition mpam_version_to_bits :: "mpam_major_version \<Rightarrow> 4 word" where
  "mpam_version_to_bits ver \<equiv> case ver of
     MPAM_v0 \<Rightarrow> 0b0000
   | MPAM_v1 \<Rightarrow> 0b0001"


definition bits_to_mpam_version :: "4 word \<Rightarrow> mpam_major_version option" where
  "bits_to_mpam_version w \<equiv>
     if w = 0b0000 then Some MPAM_v0 else
     if w = 0b0001 then Some MPAM_v1 else
     None" 


datatype sel2_support =
  SEL2_Unsupported
| SEL2_Supported


definition sel2_support_to_bits :: "sel2_support \<Rightarrow> 4 word" where
  "sel2_support_to_bits support \<equiv> case support of
     SEL2_Unsupported \<Rightarrow> 0b0000
   | SEL2_Supported   \<Rightarrow> 0b0001"


definition bits_to_sel2_support :: "4 word \<Rightarrow> sel2_support option" where
  "bits_to_sel2_support w \<equiv>
     if w = 0b0000 then Some SEL2_Unsupported else
     if w = 0b0001 then Some SEL2_Supported else
     None" 


datatype sve_support =
  SVE_Unsupported
| SVE_Supported


definition sve_support_to_bits :: "sve_support \<Rightarrow> 4 word" where
  "sve_support_to_bits support \<equiv> case support of
     SVE_Unsupported \<Rightarrow> 0b0000
   | SVE_Supported   \<Rightarrow> 0b0001"


definition bits_to_sve_support :: "4 word \<Rightarrow> sve_support option" where
  "bits_to_sve_support w \<equiv>
     if w = 0b0000 then Some SVE_Unsupported else
     if w = 0b0001 then Some SVE_Supported else
     None" 


datatype ras_version =
  RAS_None   
| RAS_v1     
| RAS_v1p1   
| RAS_v2     


definition ras_version_to_bits :: "ras_version \<Rightarrow> 4 word" where
  "ras_version_to_bits ver \<equiv> case ver of
     RAS_None   \<Rightarrow> 0b0000
   | RAS_v1     \<Rightarrow> 0b0001
   | RAS_v1p1   \<Rightarrow> 0b0010
   | RAS_v2     \<Rightarrow> 0b0011"


definition bits_to_ras_version :: "4 word \<Rightarrow> ras_version option" where
  "bits_to_ras_version w \<equiv>
     if w = 0b0000 then Some RAS_None else
     if w = 0b0001 then Some RAS_v1 else
     if w = 0b0010 then Some RAS_v1p1 else
     if w = 0b0011 then Some RAS_v2 else
     None" 


datatype gic_version =
  GIC_None   
| GIC_v3_v4  
| GIC_v4p1   


definition gic_version_to_bits :: "gic_version \<Rightarrow> 4 word" where
  "gic_version_to_bits ver \<equiv> case ver of
     GIC_None   \<Rightarrow> 0b0000
   | GIC_v3_v4  \<Rightarrow> 0b0001
   | GIC_v4p1   \<Rightarrow> 0b0011"


definition bits_to_gic_version :: "4 word \<Rightarrow> gic_version option" where
  "bits_to_gic_version w \<equiv>
     if w = 0b0000 then Some GIC_None else
     if w = 0b0001 then Some GIC_v3_v4 else
     if w = 0b0011 then Some GIC_v4p1 else
     None" 


datatype adv_simd_support =
  AdvSIMD_None           
| AdvSIMD_Base           
| AdvSIMD_HalfPrecision  


definition adv_simd_support_to_bits :: "adv_simd_support \<Rightarrow> 4 word" where
  "adv_simd_support_to_bits support \<equiv> case support of
     AdvSIMD_Base           \<Rightarrow> 0b0000
   | AdvSIMD_HalfPrecision  \<Rightarrow> 0b0001
   | AdvSIMD_None           \<Rightarrow> 0b1111"


definition bits_to_adv_simd_support :: "4 word \<Rightarrow> adv_simd_support option" where
  "bits_to_adv_simd_support w \<equiv>
     if w = 0b0000 then Some AdvSIMD_Base else
     if w = 0b0001 then Some AdvSIMD_HalfPrecision else
     if w = 0b1111 then Some AdvSIMD_None else
     None" 


datatype fp_support =
  FP_None           
| FP_Base           
| FP_HalfPrecision  


definition fp_support_to_bits :: "fp_support \<Rightarrow> 4 word" where
  "fp_support_to_bits support \<equiv> case support of
     FP_Base           \<Rightarrow> 0b0000
   | FP_HalfPrecision  \<Rightarrow> 0b0001
   | FP_None           \<Rightarrow> 0b1111"


definition bits_to_fp_support :: "4 word \<Rightarrow> fp_support option" where
  "bits_to_fp_support w \<equiv>
     if w = 0b0000 then Some FP_Base else
     if w = 0b0001 then Some FP_HalfPrecision else
     if w = 0b1111 then Some FP_None else
     None" 


datatype el3_support =
  EL3_None              
| EL3_AArch64_Only      
| EL3_AArch64_AArch32   


definition el3_support_to_bits :: "el3_support \<Rightarrow> 4 word" where
  "el3_support_to_bits support \<equiv> case support of
     EL3_None            \<Rightarrow> 0b0000
   | EL3_AArch64_Only    \<Rightarrow> 0b0001
   | EL3_AArch64_AArch32 \<Rightarrow> 0b0010"


definition bits_to_el3_support :: "4 word \<Rightarrow> el3_support option" where
  "bits_to_el3_support w \<equiv>
     if w = 0b0000 then Some EL3_None else
     if w = 0b0001 then Some EL3_AArch64_Only else
     if w = 0b0010 then Some EL3_AArch64_AArch32 else
     None" 


datatype el2_support =
  EL2_None              
| EL2_AArch64_Only      
| EL2_AArch64_AArch32   


definition el2_support_to_bits :: "el2_support \<Rightarrow> 4 word" where
  "el2_support_to_bits support \<equiv> case support of
     EL2_None            \<Rightarrow> 0b0000
   | EL2_AArch64_Only    \<Rightarrow> 0b0001
   | EL2_AArch64_AArch32 \<Rightarrow> 0b0010"


definition bits_to_el2_support :: "4 word \<Rightarrow> el2_support option" where
  "bits_to_el2_support w \<equiv>
     if w = 0b0000 then Some EL2_None else
     if w = 0b0001 then Some EL2_AArch64_Only else
     if w = 0b0010 then Some EL2_AArch64_AArch32 else
     None" 


datatype el1_support =
  EL1_AArch64_Only      
| EL1_AArch64_AArch32   


definition el1_support_to_bits :: "el1_support \<Rightarrow> 4 word" where
  "el1_support_to_bits support \<equiv> case support of
     EL1_AArch64_Only    \<Rightarrow> 0b0001
   | EL1_AArch64_AArch32 \<Rightarrow> 0b0010"


definition bits_to_el1_support :: "4 word \<Rightarrow> el1_support option" where
  "bits_to_el1_support w \<equiv>
     if w = 0b0001 then Some EL1_AArch64_Only else
     if w = 0b0010 then Some EL1_AArch64_AArch32 else
     None" 


datatype el0_support =
  EL0_AArch64_Only      
| EL0_AArch64_AArch32   


definition el0_support_to_bits :: "el0_support \<Rightarrow> 4 word" where
  "el0_support_to_bits support \<equiv> case support of
     EL0_AArch64_Only    \<Rightarrow> 0b0001
   | EL0_AArch64_AArch32 \<Rightarrow> 0b0010"


definition bits_to_el0_support :: "4 word \<Rightarrow> el0_support option" where
  "bits_to_el0_support w \<equiv>
     if w = 0b0001 then Some EL0_AArch64_Only else
     if w = 0b0010 then Some EL0_AArch64_AArch32 else
     None" 

subsection \<open> ID_AA64PFR1_EL1 \<close>


datatype pfar_support =
  PFAR_Unsupported
| PFAR_Supported


definition pfar_support_to_bits :: "pfar_support \<Rightarrow> 4 word" where
  "pfar_support_to_bits support \<equiv> case support of
     PFAR_Unsupported \<Rightarrow> 0b0000
   | PFAR_Supported   \<Rightarrow> 0b0001"


definition bits_to_pfar_support :: "4 word \<Rightarrow> pfar_support option" where
  "bits_to_pfar_support w \<equiv>
     if w = 0b0000 then Some PFAR_Unsupported else
     if w = 0b0001 then Some PFAR_Supported else
     None" 


datatype df2_support =
  DF2_Unsupported
| DF2_Supported


definition df2_support_to_bits :: "df2_support \<Rightarrow> 4 word" where
  "df2_support_to_bits support \<equiv> case support of
     DF2_Unsupported \<Rightarrow> 0b0000
   | DF2_Supported   \<Rightarrow> 0b0001"


definition bits_to_df2_support :: "4 word \<Rightarrow> df2_support option" where
  "bits_to_df2_support w \<equiv>
     if w = 0b0000 then Some DF2_Unsupported else
     if w = 0b0001 then Some DF2_Supported else
     None" 


datatype mtex_support =
  MTEX_Unsupported
| MTEX_Supported


definition mtex_support_to_bits :: "mtex_support \<Rightarrow> 4 word" where
  "mtex_support_to_bits support \<equiv> case support of
     MTEX_Unsupported \<Rightarrow> 0b0000
   | MTEX_Supported   \<Rightarrow> 0b0001"


definition bits_to_mtex_support :: "4 word \<Rightarrow> mtex_support option" where
  "bits_to_mtex_support w \<equiv>
     if w = 0b0000 then Some MTEX_Unsupported else
     if w = 0b0001 then Some MTEX_Supported else
     None" 


datatype the_support =
  THE_Unsupported
| THE_Supported


definition the_support_to_bits :: "the_support \<Rightarrow> 4 word" where
  "the_support_to_bits support \<equiv> case support of
     THE_Unsupported \<Rightarrow> 0b0000
   | THE_Supported   \<Rightarrow> 0b0001"


definition bits_to_the_support :: "4 word \<Rightarrow> the_support option" where
  "bits_to_the_support w \<equiv>
     if w = 0b0000 then Some THE_Unsupported else
     if w = 0b0001 then Some THE_Supported else
     None" 


datatype gcs_support =
  GCS_Unsupported
| GCS_Supported


definition gcs_support_to_bits :: "gcs_support \<Rightarrow> 4 word" where
  "gcs_support_to_bits support \<equiv> case support of
     GCS_Unsupported \<Rightarrow> 0b0000
   | GCS_Supported   \<Rightarrow> 0b0001"


definition bits_to_gcs_support :: "4 word \<Rightarrow> gcs_support option" where
  "bits_to_gcs_support w \<equiv>
     if w = 0b0000 then Some GCS_Unsupported else
     if w = 0b0001 then Some GCS_Supported else
     None" 


datatype mte_async_support =
  MTE_Async_Unsupported
| MTE_Async_Supported


definition mte_async_support_to_bits :: "mte_async_support \<Rightarrow> 4 word" where
  "mte_async_support_to_bits support \<equiv> case support of
     MTE_Async_Supported   \<Rightarrow> 0b0000
   | MTE_Async_Unsupported \<Rightarrow> 0b1111"


definition bits_to_mte_async_support :: "4 word \<Rightarrow> mte_async_support option" where
  "bits_to_mte_async_support w \<equiv>
     if w = 0b0000 then Some MTE_Async_Supported else
     if w = 0b1111 then Some MTE_Async_Unsupported else
     None" 


datatype nmi_support =
  NMI_Unsupported
| NMI_Supported


definition nmi_support_to_bits :: "nmi_support \<Rightarrow> 4 word" where
  "nmi_support_to_bits support \<equiv> case support of
     NMI_Unsupported \<Rightarrow> 0b0000
   | NMI_Supported   \<Rightarrow> 0b0001"


definition bits_to_nmi_support :: "4 word \<Rightarrow> nmi_support option" where
  "bits_to_nmi_support w \<equiv>
     if w = 0b0000 then Some NMI_Unsupported else
     if w = 0b0001 then Some NMI_Supported else
     None" 


datatype csv2_frac_level =
  CSV2_frac_Undisclosed_v1p1  
| CSV2_frac_v1p1              
| CSV2_frac_v1p2              


definition csv2_frac_level_to_bits :: "csv2_frac_level \<Rightarrow> 4 word" where
  "csv2_frac_level_to_bits lvl \<equiv> case lvl of
     CSV2_frac_Undisclosed_v1p1 \<Rightarrow> 0b0000
   | CSV2_frac_v1p1             \<Rightarrow> 0b0001
   | CSV2_frac_v1p2             \<Rightarrow> 0b0010"


definition bits_to_csv2_frac_level :: "4 word \<Rightarrow> csv2_frac_level option" where
  "bits_to_csv2_frac_level w \<equiv>
     if w = 0b0000 then Some CSV2_frac_Undisclosed_v1p1 else
     if w = 0b0001 then Some CSV2_frac_v1p1 else
     if w = 0b0010 then Some CSV2_frac_v1p2 else
     None" 


datatype rndr_trap_support =
  RNDR_trap_Unsupported
| RNDR_trap_Supported


definition rndr_trap_support_to_bits :: "rndr_trap_support \<Rightarrow> 4 word" where
  "rndr_trap_support_to_bits support \<equiv> case support of
     RNDR_trap_Unsupported \<Rightarrow> 0b0000
   | RNDR_trap_Supported   \<Rightarrow> 0b0001"


definition bits_to_rndr_trap_support :: "4 word \<Rightarrow> rndr_trap_support option" where
  "bits_to_rndr_trap_support w \<equiv>
     if w = 0b0000 then Some RNDR_trap_Unsupported else
     if w = 0b0001 then Some RNDR_trap_Supported else
     None" 


datatype sme_support =
  SME_None        
| SME_Base        
| SME_with_ZT0    


definition sme_support_to_bits :: "sme_support \<Rightarrow> 4 word" where
  "sme_support_to_bits support \<equiv> case support of
     SME_None      \<Rightarrow> 0b0000
   | SME_Base      \<Rightarrow> 0b0001
   | SME_with_ZT0  \<Rightarrow> 0b0010"


definition bits_to_sme_support :: "4 word \<Rightarrow> sme_support option" where
  "bits_to_sme_support w \<equiv>
     if w = 0b0000 then Some SME_None else
     if w = 0b0001 then Some SME_Base else
     if w = 0b0010 then Some SME_with_ZT0 else
     None" 


datatype mpam_minor_version =
  MPAM_Minor_v0  
| MPAM_Minor_v1  


definition mpam_minor_version_to_bits :: "mpam_minor_version \<Rightarrow> 4 word" where
  "mpam_minor_version_to_bits ver \<equiv> case ver of
     MPAM_Minor_v0 \<Rightarrow> 0b0000
   | MPAM_Minor_v1 \<Rightarrow> 0b0001"


definition bits_to_mpam_minor_version :: "4 word \<Rightarrow> mpam_minor_version option" where
  "bits_to_mpam_minor_version w \<equiv>
     if w = 0b0000 then Some MPAM_Minor_v0 else
     if w = 0b0001 then Some MPAM_Minor_v1 else
     None" 


datatype ras_frac_level =
  RAS_frac_v1p0  
| RAS_frac_v1p1  


definition ras_frac_level_to_bits :: "ras_frac_level \<Rightarrow> 4 word" where
  "ras_frac_level_to_bits lvl \<equiv> case lvl of
     RAS_frac_v1p0 \<Rightarrow> 0b0000
   | RAS_frac_v1p1 \<Rightarrow> 0b0001"


definition bits_to_ras_frac_level :: "4 word \<Rightarrow> ras_frac_level option" where
  "bits_to_ras_frac_level w \<equiv>
     if w = 0b0000 then Some RAS_frac_v1p0 else
     if w = 0b0001 then Some RAS_frac_v1p1 else
     None" 


datatype mte_level =
  MTE_None         
| MTE_InstrOnly    
| MTE_Sync         
| MTE_Full         


definition mte_level_to_bits :: "mte_level \<Rightarrow> 4 word" where
  "mte_level_to_bits lvl \<equiv> case lvl of
     MTE_None      \<Rightarrow> 0b0000
   | MTE_InstrOnly \<Rightarrow> 0b0001
   | MTE_Sync      \<Rightarrow> 0b0010
   | MTE_Full      \<Rightarrow> 0b0011"


definition bits_to_mte_level :: "4 word \<Rightarrow> mte_level option" where
  "bits_to_mte_level w \<equiv>
     if w = 0b0000 then Some MTE_None else
     if w = 0b0001 then Some MTE_InstrOnly else
     if w = 0b0010 then Some MTE_Sync else
     if w = 0b0011 then Some MTE_Full else
     None" 


datatype ssbs_support =
  SSBS_None         
| SSBS_PSTATE       
| SSBS_PSTATE_MSR   


definition ssbs_support_to_bits :: "ssbs_support \<Rightarrow> 4 word" where
  "ssbs_support_to_bits support \<equiv> case support of
     SSBS_None       \<Rightarrow> 0b0000
   | SSBS_PSTATE     \<Rightarrow> 0b0001
   | SSBS_PSTATE_MSR \<Rightarrow> 0b0010"


definition bits_to_ssbs_support :: "4 word \<Rightarrow> ssbs_support option" where
  "bits_to_ssbs_support w \<equiv>
     if w = 0b0000 then Some SSBS_None else
     if w = 0b0001 then Some SSBS_PSTATE else
     if w = 0b0010 then Some SSBS_PSTATE_MSR else
     None" 


datatype bt_support =
  BT_Unsupported
| BT_Supported


definition bt_support_to_bits :: "bt_support \<Rightarrow> 4 word" where
  "bt_support_to_bits support \<equiv> case support of
     BT_Unsupported \<Rightarrow> 0b0000
   | BT_Supported   \<Rightarrow> 0b0001"


definition bits_to_bt_support :: "4 word \<Rightarrow> bt_support option" where
  "bits_to_bt_support w \<equiv>
     if w = 0b0000 then Some BT_Unsupported else
     if w = 0b0001 then Some BT_Supported else
     None" 

subsection \<open> ID_AA64ZFR0_EL1 \<close>


datatype f64mm_support =
  F64MM_Unsupported
| F64MM_Supported


definition f64mm_support_to_bits :: "f64mm_support \<Rightarrow> 4 word" where
  "f64mm_support_to_bits support \<equiv> case support of
     F64MM_Unsupported \<Rightarrow> 0b0000
   | F64MM_Supported   \<Rightarrow> 0b0001"


definition bits_to_f64mm_support :: "4 word \<Rightarrow> f64mm_support option" where
  "bits_to_f64mm_support w \<equiv>
     if w = 0b0000 then Some F64MM_Unsupported else
     if w = 0b0001 then Some F64MM_Supported else
     None" 


datatype f32mm_support =
  F32MM_Unsupported
| F32MM_Supported


definition f32mm_support_to_bits :: "f32mm_support \<Rightarrow> 4 word" where
  "f32mm_support_to_bits support \<equiv> case support of
     F32MM_Unsupported \<Rightarrow> 0b0000
   | F32MM_Supported   \<Rightarrow> 0b0001"


definition bits_to_f32mm_support :: "4 word \<Rightarrow> f32mm_support option" where
  "bits_to_f32mm_support w \<equiv>
     if w = 0b0000 then Some F32MM_Unsupported else
     if w = 0b0001 then Some F32MM_Supported else
     None" 


datatype b16b16_support =
  B16B16_Unsupported
| B16B16_Supported


definition b16b16_support_to_bits :: "b16b16_support \<Rightarrow> 4 word" where
  "b16b16_support_to_bits support \<equiv> case support of
     B16B16_Unsupported \<Rightarrow> 0b0000
   | B16B16_Supported   \<Rightarrow> 0b0001"


definition bits_to_b16b16_support :: "4 word \<Rightarrow> b16b16_support option" where
  "bits_to_b16b16_support w \<equiv>
     if w = 0b0000 then Some B16B16_Unsupported else
     if w = 0b0001 then Some B16B16_Supported else
     None" 


datatype bit_perm_support =
  BitPerm_Unsupported
| BitPerm_Supported


definition bit_perm_support_to_bits :: "bit_perm_support \<Rightarrow> 4 word" where
  "bit_perm_support_to_bits support \<equiv> case support of
     BitPerm_Unsupported \<Rightarrow> 0b0000
   | BitPerm_Supported   \<Rightarrow> 0b0001"


definition bits_to_bit_perm_support :: "4 word \<Rightarrow> bit_perm_support option" where
  "bits_to_bit_perm_support w \<equiv>
     if w = 0b0000 then Some BitPerm_Unsupported else
     if w = 0b0001 then Some BitPerm_Supported else
     None" 


datatype elt_perm_support =
  EltPerm_Unsupported
| EltPerm_Supported


definition elt_perm_support_to_bits :: "elt_perm_support \<Rightarrow> 4 word" where
  "elt_perm_support_to_bits support \<equiv> case support of
     EltPerm_Unsupported \<Rightarrow> 0b0000
   | EltPerm_Supported   \<Rightarrow> 0b0001"


definition bits_to_elt_perm_support :: "4 word \<Rightarrow> elt_perm_support option" where
  "bits_to_elt_perm_support w \<equiv>
     if w = 0b0000 then Some EltPerm_Unsupported else
     if w = 0b0001 then Some EltPerm_Supported else
     None" 

datatype aes_pmull_features =
  SVE_AES
  | SVE_PMULL128



definition aes_pmull_features_to_bits :: "aes_pmull_features \<Rightarrow> 4 word" where
  "aes_pmull_features_to_bits features \<equiv> case features of
     SVE_AES \<Rightarrow> 0b0001
   | SVE_PMULL128   \<Rightarrow> 0b0010"


definition bits_to_aes_pmull_features :: "4 word \<Rightarrow> aes_pmull_features option" where
  "bits_to_aes_pmull_features w \<equiv>
     if w = 0b0001 then Some SVE_AES else
     if w = 0b0010 then Some SVE_PMULL128 else
     None" 


datatype sve_feature =
  FEAT_SVE2
| FEAT_SME
| FEAT_SVE2p1
| FEAT_SME2p1


subsection \<open> ID_AA64DFR0_EL1 \<close>


datatype hpmn0_behavior =
  HPMN0_Unpredictable  
| HPMN0_Defined        


definition hpmn0_behavior_to_bits :: "hpmn0_behavior \<Rightarrow> 4 word" where
  "hpmn0_behavior_to_bits behavior \<equiv> case behavior of
     HPMN0_Unpredictable \<Rightarrow> 0b0000
   | HPMN0_Defined       \<Rightarrow> 0b0001"


definition bits_to_hpmn0_behavior :: "4 word \<Rightarrow> hpmn0_behavior option" where
  "bits_to_hpmn0_behavior w \<equiv>
     if w = 0b0000 then Some HPMN0_Unpredictable else
     if w = 0b0001 then Some HPMN0_Defined else
     None" 


datatype ext_trc_buff_support =
  ExtTrcBuff_Unsupported
| ExtTrcBuff_Supported


definition ext_trc_buff_support_to_bits :: "ext_trc_buff_support \<Rightarrow> 4 word" where
  "ext_trc_buff_support_to_bits support \<equiv> case support of
     ExtTrcBuff_Unsupported \<Rightarrow> 0b0000
   | ExtTrcBuff_Supported   \<Rightarrow> 0b0001"


definition bits_to_ext_trc_buff_support :: "4 word \<Rightarrow> ext_trc_buff_support option" where
  "bits_to_ext_trc_buff_support w \<equiv>
     if w = 0b0000 then Some ExtTrcBuff_Unsupported else
     if w = 0b0001 then Some ExtTrcBuff_Supported else
     None" 


datatype brbe_support =
  BRBE_None       
| BRBE_Base       
| BRBE_with_EL3   


definition brbe_support_to_bits :: "brbe_support \<Rightarrow> 4 word" where
  "brbe_support_to_bits support \<equiv> case support of
     BRBE_None     \<Rightarrow> 0b0000
   | BRBE_Base     \<Rightarrow> 0b0001
   | BRBE_with_EL3 \<Rightarrow> 0b0010"


definition bits_to_brbe_support :: "4 word \<Rightarrow> brbe_support option" where
  "bits_to_brbe_support w \<equiv>
     if w = 0b0000 then Some BRBE_None else
     if w = 0b0001 then Some BRBE_Base else
     if w = 0b0010 then Some BRBE_with_EL3 else
     None" 


datatype mtpmu_support =
  MTPMU_None_ImpDef  
| MTPMU_Supported    
| MTPMU_None_RES0    


definition mtpmu_support_to_bits :: "mtpmu_support \<Rightarrow> 4 word" where
  "mtpmu_support_to_bits support \<equiv> case support of
     MTPMU_None_ImpDef \<Rightarrow> 0b0000
   | MTPMU_Supported   \<Rightarrow> 0b0001
   | MTPMU_None_RES0   \<Rightarrow> 0b1111"


definition bits_to_mtpmu_support :: "4 word \<Rightarrow> mtpmu_support option" where
  "bits_to_mtpmu_support w \<equiv>
     if w = 0b0000 then Some MTPMU_None_ImpDef else
     if w = 0b0001 then Some MTPMU_Supported else
     if w = 0b1111 then Some MTPMU_None_RES0 else
     None" 


datatype trace_buffer_support =
  TraceBuffer_Unsupported
| TraceBuffer_Supported


definition trace_buffer_support_to_bits :: "trace_buffer_support \<Rightarrow> 4 word" where
  "trace_buffer_support_to_bits support \<equiv> case support of
     TraceBuffer_Unsupported \<Rightarrow> 0b0000
   | TraceBuffer_Supported   \<Rightarrow> 0b0001"


definition bits_to_trace_buffer_support :: "4 word \<Rightarrow> trace_buffer_support option" where
  "bits_to_trace_buffer_support w \<equiv>
     if w = 0b0000 then Some TraceBuffer_Unsupported else
     if w = 0b0001 then Some TraceBuffer_Supported else
     None" 


datatype trace_filt_support =
  TraceFilt_Unsupported
| TraceFilt_Supported


definition trace_filt_support_to_bits :: "trace_filt_support \<Rightarrow> 4 word" where
  "trace_filt_support_to_bits support \<equiv> case support of
     TraceFilt_Unsupported \<Rightarrow> 0b0000
   | TraceFilt_Supported   \<Rightarrow> 0b0001"


definition bits_to_trace_filt_support :: "4 word \<Rightarrow> trace_filt_support option" where
  "bits_to_trace_filt_support w \<equiv>
     if w = 0b0000 then Some TraceFilt_Unsupported else
     if w = 0b0001 then Some TraceFilt_Supported else
     None" 


datatype double_lock_support =
  DoubleLock_Unsupported
| DoubleLock_Supported


definition double_lock_support_to_bits :: "double_lock_support \<Rightarrow> 4 word" where
  "double_lock_support_to_bits support \<equiv> case support of
     DoubleLock_Supported   \<Rightarrow> 0b0000
   | DoubleLock_Unsupported \<Rightarrow> 0b1111"


definition bits_to_double_lock_support :: "4 word \<Rightarrow> double_lock_support option" where
  "bits_to_double_lock_support w \<equiv>
     if w = 0b0000 then Some DoubleLock_Supported else
     if w = 0b1111 then Some DoubleLock_Unsupported else
     None" 


datatype pms_version =
  PMS_None  
| PMS_v1    
| PMS_v1p1  
| PMS_v1p2  
| PMS_v1p3  
| PMS_v1p4  


definition pms_version_to_bits :: "pms_version \<Rightarrow> 4 word" where
  "pms_version_to_bits ver \<equiv> case ver of
     PMS_None \<Rightarrow> 0b0000
   | PMS_v1   \<Rightarrow> 0b0001
   | PMS_v1p1 \<Rightarrow> 0b0010
   | PMS_v1p2 \<Rightarrow> 0b0011
   | PMS_v1p3 \<Rightarrow> 0b0100
   | PMS_v1p4 \<Rightarrow> 0b0101"


definition bits_to_pms_version :: "4 word \<Rightarrow> pms_version option" where
  "bits_to_pms_version w \<equiv>
     if w = 0b0000 then Some PMS_None else
     if w = 0b0001 then Some PMS_v1 else
     if w = 0b0010 then Some PMS_v1p1 else
     if w = 0b0011 then Some PMS_v1p2 else
     if w = 0b0100 then Some PMS_v1p3 else
     if w = 0b0101 then Some PMS_v1p4 else
     None" 

type_synonym ctx_cmps_val = "4 word"


datatype sebep_support =
  SEBEP_Unsupported
| SEBEP_Supported


definition sebep_support_to_bits :: "sebep_support \<Rightarrow> 4 word" where
  "sebep_support_to_bits support \<equiv> case support of
     SEBEP_Unsupported \<Rightarrow> 0b0000
   | SEBEP_Supported   \<Rightarrow> 0b0001"


definition bits_to_sebep_support :: "4 word \<Rightarrow> sebep_support option" where
  "bits_to_sebep_support w \<equiv>
     if w = 0b0000 then Some SEBEP_Unsupported else
     if w = 0b0001 then Some SEBEP_Supported else
     None" 

type_synonym wrps_val = "4 word"


datatype pmss_support =
  PMSS_Unsupported
| PMSS_Supported


definition pmss_support_to_bits :: "pmss_support \<Rightarrow> 4 word" where
  "pmss_support_to_bits support \<equiv> case support of
     PMSS_Unsupported \<Rightarrow> 0b0000
   | PMSS_Supported   \<Rightarrow> 0b0001"


definition bits_to_pmss_support :: "4 word \<Rightarrow> pmss_support option" where
  "bits_to_pmss_support w \<equiv>
     if w = 0b0000 then Some PMSS_Unsupported else
     if w = 0b0001 then Some PMSS_Supported else
     None" 

type_synonym brps_val = "4 word"


datatype pmu_version =
  PMU_None         
| PMU_v3           
| PMU_v3_Armv8p1   
| PMU_v3_Armv8p4   
| PMU_v3_Armv8p5   
| PMU_v3_Armv8p7   
| PMU_v3_Armv8p8   
| PMU_v3_Armv8p9   
| PMU_ImpDef       


definition pmu_version_to_bits :: "pmu_version \<Rightarrow> 4 word" where
  "pmu_version_to_bits ver \<equiv> case ver of
     PMU_None         \<Rightarrow> 0b0000
   | PMU_v3           \<Rightarrow> 0b0001
   | PMU_v3_Armv8p1   \<Rightarrow> 0b0100
   | PMU_v3_Armv8p4   \<Rightarrow> 0b0101
   | PMU_v3_Armv8p5   \<Rightarrow> 0b0110
   | PMU_v3_Armv8p7   \<Rightarrow> 0b0111
   | PMU_v3_Armv8p8   \<Rightarrow> 0b1000
   | PMU_v3_Armv8p9   \<Rightarrow> 0b1001
   | PMU_ImpDef       \<Rightarrow> 0b1111"


definition bits_to_pmu_version :: "4 word \<Rightarrow> pmu_version option" where
  "bits_to_pmu_version w \<equiv>
     if w = 0b0000 then Some PMU_None else
     if w = 0b0001 then Some PMU_v3 else
     if w = 0b0100 then Some PMU_v3_Armv8p1 else
     if w = 0b0101 then Some PMU_v3_Armv8p4 else
     if w = 0b0110 then Some PMU_v3_Armv8p5 else
     if w = 0b0111 then Some PMU_v3_Armv8p7 else
     if w = 0b1000 then Some PMU_v3_Armv8p8 else
     if w = 0b1001 then Some PMU_v3_Armv8p9 else
     if w = 0b1111 then Some PMU_ImpDef else
     None" 


datatype trace_ver_support =
  TraceVer_Unsupported
| TraceVer_Supported


definition trace_ver_support_to_bits :: "trace_ver_support \<Rightarrow> 4 word" where
  "trace_ver_support_to_bits support \<equiv> case support of
     TraceVer_Unsupported \<Rightarrow> 0b0000
   | TraceVer_Supported   \<Rightarrow> 0b0001"


definition bits_to_trace_ver_support :: "4 word \<Rightarrow> trace_ver_support option" where
  "bits_to_trace_ver_support w \<equiv>
     if w = 0b0000 then Some TraceVer_Unsupported else
     if w = 0b0001 then Some TraceVer_Supported else
     None" 


datatype debug_version =
  Debug_v8p0
| Debug_v8p1
| Debug_v8p2
| Debug_v8p4
| Debug_v8p8
| Debug_v8p9


definition debug_version_to_bits :: "debug_version \<Rightarrow> 4 word" where
  "debug_version_to_bits ver \<equiv> case ver of
     Debug_v8p0 \<Rightarrow> 0b0110
   | Debug_v8p1 \<Rightarrow> 0b0111
   | Debug_v8p2 \<Rightarrow> 0b1000
   | Debug_v8p4 \<Rightarrow> 0b1001
   | Debug_v8p8 \<Rightarrow> 0b1010
   | Debug_v8p9 \<Rightarrow> 0b1011"


definition bits_to_debug_version :: "4 word \<Rightarrow> debug_version option" where
  "bits_to_debug_version w \<equiv>
     if w = 0b0110 then Some Debug_v8p0 else
     if w = 0b0111 then Some Debug_v8p1 else
     if w = 0b1000 then Some Debug_v8p2 else
     if w = 0b1001 then Some Debug_v8p4 else
     if w = 0b1010 then Some Debug_v8p8 else
     if w = 0b1011 then Some Debug_v8p9 else
     None" 

subsection \<open> ID_AA64DFR1_EL1 \<close>

type_synonym abl_cmps_val = "4 word"


datatype dpfzs_behavior =
  DPFZS_Unaffected  
| DPFZS_Affected    


definition dpfzs_behavior_to_bits :: "dpfzs_behavior \<Rightarrow> 4 word" where
  "dpfzs_behavior_to_bits behavior \<equiv> case behavior of
     DPFZS_Unaffected \<Rightarrow> 0b0000
   | DPFZS_Affected   \<Rightarrow> 0b0001"


definition bits_to_dpfzs_behavior :: "4 word \<Rightarrow> dpfzs_behavior option" where
  "bits_to_dpfzs_behavior w \<equiv>
     if w = 0b0000 then Some DPFZS_Unaffected else
     if w = 0b0001 then Some DPFZS_Affected else
     None" 


datatype ebep_support =
  EBEP_Unsupported
| EBEP_Supported


definition ebep_support_to_bits :: "ebep_support \<Rightarrow> 4 word" where
  "ebep_support_to_bits support \<equiv> case support of
     EBEP_Unsupported \<Rightarrow> 0b0000
   | EBEP_Supported   \<Rightarrow> 0b0001"


definition bits_to_ebep_support :: "4 word \<Rightarrow> ebep_support option" where
  "bits_to_ebep_support w \<equiv>
     if w = 0b0000 then Some EBEP_Unsupported else
     if w = 0b0001 then Some EBEP_Supported else
     None" 


datatype ite_support =
  ITE_Unsupported
| ITE_Supported


definition ite_support_to_bits :: "ite_support \<Rightarrow> 4 word" where
  "ite_support_to_bits support \<equiv> case support of
     ITE_Unsupported \<Rightarrow> 0b0000
   | ITE_Supported   \<Rightarrow> 0b0001"


definition bits_to_ite_support :: "4 word \<Rightarrow> ite_support option" where
  "bits_to_ite_support w \<equiv>
     if w = 0b0000 then Some ITE_Unsupported else
     if w = 0b0001 then Some ITE_Supported else
     None" 


datatype able_support =
  ABLE_Unsupported
| ABLE_Supported


definition able_support_to_bits :: "able_support \<Rightarrow> 4 word" where
  "able_support_to_bits support \<equiv> case support of
     ABLE_Unsupported \<Rightarrow> 0b0000
   | ABLE_Supported   \<Rightarrow> 0b0001"


definition bits_to_able_support :: "4 word \<Rightarrow> able_support option" where
  "bits_to_able_support w \<equiv>
     if w = 0b0000 then Some ABLE_Unsupported else
     if w = 0b0001 then Some ABLE_Supported else
     None" 


datatype pmicntr_support =
  PMICNTR_Unsupported
| PMICNTR_Supported


definition pmicntr_support_to_bits :: "pmicntr_support \<Rightarrow> 4 word" where
  "pmicntr_support_to_bits support \<equiv> case support of
     PMICNTR_Unsupported \<Rightarrow> 0b0000
   | PMICNTR_Supported   \<Rightarrow> 0b0001"


definition bits_to_pmicntr_support :: "4 word \<Rightarrow> pmicntr_support option" where
  "bits_to_pmicntr_support w \<equiv>
     if w = 0b0000 then Some PMICNTR_Unsupported else
     if w = 0b0001 then Some PMICNTR_Supported else
     None" 


datatype spmu_support =
  SPMU_None         
| SPMU_Base         
| SPMU_with_SPMZR   


definition spmu_support_to_bits :: "spmu_support \<Rightarrow> 4 word" where
  "spmu_support_to_bits support \<equiv> case support of
     SPMU_None       \<Rightarrow> 0b0000
   | SPMU_Base       \<Rightarrow> 0b0001
   | SPMU_with_SPMZR \<Rightarrow> 0b0010"


definition bits_to_spmu_support :: "4 word \<Rightarrow> spmu_support option" where
  "bits_to_spmu_support w \<equiv>
     if w = 0b0000 then Some SPMU_None else
     if w = 0b0001 then Some SPMU_Base else
     if w = 0b0010 then Some SPMU_with_SPMZR else
     None" 

type_synonym ctx_cmps_val_long = "6 word"

type_synonym wrps_val_long = "6 word"

type_synonym brps_val_long = "6 word"

type_synonym syspmuid_val = "5 word"

subsection \<open> ID_AA64AFR0_EL1 \<close>

subsection \<open> ID_AA64AFR1_EL1 \<close>

subsection \<open> ID_AA64ISAR0_EL1 \<close>


datatype rndr_support =
  RNDR_Unsupported
| RNDR_Supported


definition rndr_support_to_bits :: "rndr_support \<Rightarrow> 4 word" where
  "rndr_support_to_bits support \<equiv> case support of
     RNDR_Unsupported \<Rightarrow> 0b0000
   | RNDR_Supported   \<Rightarrow> 0b0001"


definition bits_to_rndr_support :: "4 word \<Rightarrow> rndr_support option" where
  "bits_to_rndr_support w \<equiv>
     if w = 0b0000 then Some RNDR_Unsupported else
     if w = 0b0001 then Some RNDR_Supported else
     None" 


datatype tlb_support =
  TLB_None                   
| TLB_OuterShareable         
| TLB_OuterShareable_Range   


definition tlb_support_to_bits :: "tlb_support \<Rightarrow> 4 word" where
  "tlb_support_to_bits support \<equiv> case support of
     TLB_None                 \<Rightarrow> 0b0000
   | TLB_OuterShareable       \<Rightarrow> 0b0001
   | TLB_OuterShareable_Range \<Rightarrow> 0b0010"


definition bits_to_tlb_support :: "4 word \<Rightarrow> tlb_support option" where
  "bits_to_tlb_support w \<equiv>
     if w = 0b0000 then Some TLB_None else
     if w = 0b0001 then Some TLB_OuterShareable else
     if w = 0b0010 then Some TLB_OuterShareable_Range else
     None" 


datatype ts_support =
  TS_None      
| TS_Base      
| TS_Extended  


definition ts_support_to_bits :: "ts_support \<Rightarrow> 4 word" where
  "ts_support_to_bits support \<equiv> case support of
     TS_None     \<Rightarrow> 0b0000
   | TS_Base     \<Rightarrow> 0b0001
   | TS_Extended \<Rightarrow> 0b0010"


definition bits_to_ts_support :: "4 word \<Rightarrow> ts_support option" where
  "bits_to_ts_support w \<equiv>
     if w = 0b0000 then Some TS_None else
     if w = 0b0001 then Some TS_Base else
     if w = 0b0010 then Some TS_Extended else
     None" 


datatype fhm_support =
  FHM_Unsupported
| FHM_Supported


definition fhm_support_to_bits :: "fhm_support \<Rightarrow> 4 word" where
  "fhm_support_to_bits support \<equiv> case support of
     FHM_Unsupported \<Rightarrow> 0b0000
   | FHM_Supported   \<Rightarrow> 0b0001"


definition bits_to_fhm_support :: "4 word \<Rightarrow> fhm_support option" where
  "bits_to_fhm_support w \<equiv>
     if w = 0b0000 then Some FHM_Unsupported else
     if w = 0b0001 then Some FHM_Supported else
     None" 


datatype dp_support =
  DP_Unsupported
| DP_Supported


definition dp_support_to_bits :: "dp_support \<Rightarrow> 4 word" where
  "dp_support_to_bits support \<equiv> case support of
     DP_Unsupported \<Rightarrow> 0b0000
   | DP_Supported   \<Rightarrow> 0b0001"


definition bits_to_dp_support :: "4 word \<Rightarrow> dp_support option" where
  "bits_to_dp_support w \<equiv>
     if w = 0b0000 then Some DP_Unsupported else
     if w = 0b0001 then Some DP_Supported else
     None" 


datatype sm4_support =
  SM4_Unsupported
| SM4_Supported


definition sm4_support_to_bits :: "sm4_support \<Rightarrow> 4 word" where
  "sm4_support_to_bits support \<equiv> case support of
     SM4_Unsupported \<Rightarrow> 0b0000
   | SM4_Supported   \<Rightarrow> 0b0001"


definition bits_to_sm4_support :: "4 word \<Rightarrow> sm4_support option" where
  "bits_to_sm4_support w \<equiv>
     if w = 0b0000 then Some SM4_Unsupported else
     if w = 0b0001 then Some SM4_Supported else
     None" 


datatype sm3_support =
  SM3_Unsupported
| SM3_Supported


definition sm3_support_to_bits :: "sm3_support \<Rightarrow> 4 word" where
  "sm3_support_to_bits support \<equiv> case support of
     SM3_Unsupported \<Rightarrow> 0b0000
   | SM3_Supported   \<Rightarrow> 0b0001"


definition bits_to_sm3_support :: "4 word \<Rightarrow> sm3_support option" where
  "bits_to_sm3_support w \<equiv>
     if w = 0b0000 then Some SM3_Unsupported else
     if w = 0b0001 then Some SM3_Supported else
     None" 


datatype sha3_support =
  SHA3_Unsupported
| SHA3_Supported


definition sha3_support_to_bits :: "sha3_support \<Rightarrow> 4 word" where
  "sha3_support_to_bits support \<equiv> case support of
     SHA3_Unsupported \<Rightarrow> 0b0000
   | SHA3_Supported   \<Rightarrow> 0b0001"


definition bits_to_sha3_support :: "4 word \<Rightarrow> sha3_support option" where
  "bits_to_sha3_support w \<equiv>
     if w = 0b0000 then Some SHA3_Unsupported else
     if w = 0b0001 then Some SHA3_Supported else
     None" 


datatype rdm_support =
  RDM_Unsupported
| RDM_Supported


definition rdm_support_to_bits :: "rdm_support \<Rightarrow> 4 word" where
  "rdm_support_to_bits support \<equiv> case support of
     RDM_Unsupported \<Rightarrow> 0b0000
   | RDM_Supported   \<Rightarrow> 0b0001"


definition bits_to_rdm_support :: "4 word \<Rightarrow> rdm_support option" where
  "bits_to_rdm_support w \<equiv>
     if w = 0b0000 then Some RDM_Unsupported else
     if w = 0b0001 then Some RDM_Supported else
     None" 


datatype tme_support =
  TME_Unsupported
| TME_Supported


definition tme_support_to_bits :: "tme_support \<Rightarrow> 4 word" where
  "tme_support_to_bits support \<equiv> case support of
     TME_Unsupported \<Rightarrow> 0b0000
   | TME_Supported   \<Rightarrow> 0b0001"


definition bits_to_tme_support :: "4 word \<Rightarrow> tme_support option" where
  "bits_to_tme_support w \<equiv>
     if w = 0b0000 then Some TME_Unsupported else
     if w = 0b0001 then Some TME_Supported else
     None" 


datatype atomic_support =
  Atomic_None    
| Atomic_Base    
| Atomic_128bit  


definition atomic_support_to_bits :: "atomic_support \<Rightarrow> 4 word" where
  "atomic_support_to_bits support \<equiv> case support of
     Atomic_None   \<Rightarrow> 0b0000
   | Atomic_Base   \<Rightarrow> 0b0010
   | Atomic_128bit \<Rightarrow> 0b0011"


definition bits_to_atomic_support :: "4 word \<Rightarrow> atomic_support option" where
  "bits_to_atomic_support w \<equiv>
     if w = 0b0000 then Some Atomic_None else
     if w = 0b0010 then Some Atomic_Base else
     if w = 0b0011 then Some Atomic_128bit else
     None" 


datatype crc32_support =
  CRC32_Unsupported
| CRC32_Supported


definition crc32_support_to_bits :: "crc32_support \<Rightarrow> 4 word" where
  "crc32_support_to_bits support \<equiv> case support of
     CRC32_Unsupported \<Rightarrow> 0b0000
   | CRC32_Supported   \<Rightarrow> 0b0001"


definition bits_to_crc32_support :: "4 word \<Rightarrow> crc32_support option" where
  "bits_to_crc32_support w \<equiv>
     if w = 0b0000 then Some CRC32_Unsupported else
     if w = 0b0001 then Some CRC32_Supported else
     None" 


datatype sha2_support =
  SHA2_None      
| SHA2_256       
| SHA2_256_512   


definition sha2_support_to_bits :: "sha2_support \<Rightarrow> 4 word" where
  "sha2_support_to_bits support \<equiv> case support of
     SHA2_None      \<Rightarrow> 0b0000
   | SHA2_256       \<Rightarrow> 0b0001
   | SHA2_256_512   \<Rightarrow> 0b0010"


definition bits_to_sha2_support :: "4 word \<Rightarrow> sha2_support option" where
  "bits_to_sha2_support w \<equiv>
     if w = 0b0000 then Some SHA2_None else
     if w = 0b0001 then Some SHA2_256 else
     if w = 0b0010 then Some SHA2_256_512 else
     None" 


datatype sha1_support =
  SHA1_Unsupported
| SHA1_Supported


definition sha1_support_to_bits :: "sha1_support \<Rightarrow> 4 word" where
  "sha1_support_to_bits support \<equiv> case support of
     SHA1_Unsupported \<Rightarrow> 0b0000
   | SHA1_Supported   \<Rightarrow> 0b0001"


definition bits_to_sha1_support :: "4 word \<Rightarrow> sha1_support option" where
  "bits_to_sha1_support w \<equiv>
     if w = 0b0000 then Some SHA1_Unsupported else
     if w = 0b0001 then Some SHA1_Supported else
     None" 


datatype aes_support =
  AES_None        
| AES_Base        
| AES_with_PMULL  


definition aes_support_to_bits :: "aes_support \<Rightarrow> 4 word" where
  "aes_support_to_bits support \<equiv> case support of
     AES_None       \<Rightarrow> 0b0000
   | AES_Base       \<Rightarrow> 0b0001
   | AES_with_PMULL \<Rightarrow> 0b0010"


definition bits_to_aes_support :: "4 word \<Rightarrow> aes_support option" where
  "bits_to_aes_support w \<equiv>
     if w = 0b0000 then Some AES_None else
     if w = 0b0001 then Some AES_Base else
     if w = 0b0010 then Some AES_with_PMULL else
     None" 

subsection \<open> ID_AA64ISAR1_EL1 \<close>


datatype ls64_support =
  LS64_None           
| LS64_Base           
| LS64_with_ST64BV    
| LS64_with_ST64BV0   


definition ls64_support_to_bits :: "ls64_support \<Rightarrow> 4 word" where
  "ls64_support_to_bits support \<equiv> case support of
     LS64_None         \<Rightarrow> 0b0000
   | LS64_Base         \<Rightarrow> 0b0001
   | LS64_with_ST64BV  \<Rightarrow> 0b0010
   | LS64_with_ST64BV0 \<Rightarrow> 0b0011"


definition bits_to_ls64_support :: "4 word \<Rightarrow> ls64_support option" where
  "bits_to_ls64_support w \<equiv>
     if w = 0b0000 then Some LS64_None else
     if w = 0b0001 then Some LS64_Base else
     if w = 0b0010 then Some LS64_with_ST64BV else
     if w = 0b0011 then Some LS64_with_ST64BV0 else
     None" 


datatype xs_support =
  XS_Unsupported
| XS_Supported


definition xs_support_to_bits :: "xs_support \<Rightarrow> 4 word" where
  "xs_support_to_bits support \<equiv> case support of
     XS_Unsupported \<Rightarrow> 0b0000
   | XS_Supported   \<Rightarrow> 0b0001"


definition bits_to_xs_support :: "4 word \<Rightarrow> xs_support option" where
  "bits_to_xs_support w \<equiv>
     if w = 0b0000 then Some XS_Unsupported else
     if w = 0b0001 then Some XS_Supported else
     None" 


datatype i8mm_support =
  I8MM_Unsupported
| I8MM_Supported


definition i8mm_support_to_bits :: "i8mm_support \<Rightarrow> 4 word" where
  "i8mm_support_to_bits support \<equiv> case support of
     I8MM_Unsupported \<Rightarrow> 0b0000
   | I8MM_Supported   \<Rightarrow> 0b0001"


definition bits_to_i8mm_support :: "4 word \<Rightarrow> i8mm_support option" where
  "bits_to_i8mm_support w \<equiv>
     if w = 0b0000 then Some I8MM_Unsupported else
     if w = 0b0001 then Some I8MM_Supported else
     None" 


datatype dgh_support =
  DGH_Unsupported
| DGH_Supported


definition dgh_support_to_bits :: "dgh_support \<Rightarrow> 4 word" where
  "dgh_support_to_bits support \<equiv> case support of
     DGH_Unsupported \<Rightarrow> 0b0000
   | DGH_Supported   \<Rightarrow> 0b0001"


definition bits_to_dgh_support :: "4 word \<Rightarrow> dgh_support option" where
  "bits_to_dgh_support w \<equiv>
     if w = 0b0000 then Some DGH_Unsupported else
     if w = 0b0001 then Some DGH_Supported else
     None" 


datatype bf16_support =
  BF16_None       
| BF16_Base       
| BF16_With_EBF   


definition bf16_support_to_bits :: "bf16_support \<Rightarrow> 4 word" where
  "bf16_support_to_bits support \<equiv> case support of
     BF16_None     \<Rightarrow> 0b0000
   | BF16_Base     \<Rightarrow> 0b0001
   | BF16_With_EBF \<Rightarrow> 0b0010"


definition bits_to_bf16_support :: "4 word \<Rightarrow> bf16_support option" where
  "bits_to_bf16_support w \<equiv>
     if w = 0b0000 then Some BF16_None else
     if w = 0b0001 then Some BF16_Base else
     if w = 0b0010 then Some BF16_With_EBF else
     None" 


datatype specres_support =
  SPECRES_None       
| SPECRES_Base       
| SPECRES_with_COSP  


definition specres_support_to_bits :: "specres_support \<Rightarrow> 4 word" where
  "specres_support_to_bits support \<equiv> case support of
     SPECRES_None       \<Rightarrow> 0b0000
   | SPECRES_Base       \<Rightarrow> 0b0001
   | SPECRES_with_COSP  \<Rightarrow> 0b0010"


definition bits_to_specres_support :: "4 word \<Rightarrow> specres_support option" where
  "bits_to_specres_support w \<equiv>
     if w = 0b0000 then Some SPECRES_None else
     if w = 0b0001 then Some SPECRES_Base else
     if w = 0b0010 then Some SPECRES_with_COSP else
     None" 


datatype sb_support =
  SB_Unsupported
| SB_Supported


definition sb_support_to_bits :: "sb_support \<Rightarrow> 4 word" where
  "sb_support_to_bits support \<equiv> case support of
     SB_Unsupported \<Rightarrow> 0b0000
   | SB_Supported   \<Rightarrow> 0b0001"


definition bits_to_sb_support :: "4 word \<Rightarrow> sb_support option" where
  "bits_to_sb_support w \<equiv>
     if w = 0b0000 then Some SB_Unsupported else
     if w = 0b0001 then Some SB_Supported else
     None" 


datatype frintts_support =
  FRINTTS_Unsupported
| FRINTTS_Supported


definition frintts_support_to_bits :: "frintts_support \<Rightarrow> 4 word" where
  "frintts_support_to_bits support \<equiv> case support of
     FRINTTS_Unsupported \<Rightarrow> 0b0000
   | FRINTTS_Supported   \<Rightarrow> 0b0001"


definition bits_to_frintts_support :: "4 word \<Rightarrow> frintts_support option" where
  "bits_to_frintts_support w \<equiv>
     if w = 0b0000 then Some FRINTTS_Unsupported else
     if w = 0b0001 then Some FRINTTS_Supported else
     None" 


datatype gpi_support =
  GPI_Unsupported
| GPI_Supported


definition gpi_support_to_bits :: "gpi_support \<Rightarrow> 4 word" where
  "gpi_support_to_bits support \<equiv> case support of
     GPI_Unsupported \<Rightarrow> 0b0000
   | GPI_Supported   \<Rightarrow> 0b0001"


definition bits_to_gpi_support :: "4 word \<Rightarrow> gpi_support option" where
  "bits_to_gpi_support w \<equiv>
     if w = 0b0000 then Some GPI_Unsupported else
     if w = 0b0001 then Some GPI_Supported else
     None" 


datatype gpa_support =
  GPA_Unsupported
| GPA_Supported


definition gpa_support_to_bits :: "gpa_support \<Rightarrow> 4 word" where
  "gpa_support_to_bits support \<equiv> case support of
     GPA_Unsupported \<Rightarrow> 0b0000
   | GPA_Supported   \<Rightarrow> 0b0001"


definition bits_to_gpa_support :: "4 word \<Rightarrow> gpa_support option" where
  "bits_to_gpa_support w \<equiv>
     if w = 0b0000 then Some GPA_Unsupported else
     if w = 0b0001 then Some GPA_Supported else
     None" 


datatype lrcpc_support =
  LRCPC_None       
| LRCPC_Base       
| LRCPC_Immediate  
| LRCPC_Full       


definition lrcpc_support_to_bits :: "lrcpc_support \<Rightarrow> 4 word" where
  "lrcpc_support_to_bits support \<equiv> case support of
     LRCPC_None      \<Rightarrow> 0b0000
   | LRCPC_Base      \<Rightarrow> 0b0001
   | LRCPC_Immediate \<Rightarrow> 0b0010
   | LRCPC_Full      \<Rightarrow> 0b0011"


definition bits_to_lrcpc_support :: "4 word \<Rightarrow> lrcpc_support option" where
  "bits_to_lrcpc_support w \<equiv>
     if w = 0b0000 then Some LRCPC_None else
     if w = 0b0001 then Some LRCPC_Base else
     if w = 0b0010 then Some LRCPC_Immediate else
     if w = 0b0011 then Some LRCPC_Full else
     None" 


datatype fcma_support =
  FCMA_Unsupported
| FCMA_Supported


definition fcma_support_to_bits :: "fcma_support \<Rightarrow> 4 word" where
  "fcma_support_to_bits support \<equiv> case support of
     FCMA_Unsupported \<Rightarrow> 0b0000
   | FCMA_Supported   \<Rightarrow> 0b0001"


definition bits_to_fcma_support :: "4 word \<Rightarrow> fcma_support option" where
  "bits_to_fcma_support w \<equiv>
     if w = 0b0000 then Some FCMA_Unsupported else
     if w = 0b0001 then Some FCMA_Supported else
     None" 


datatype jscvt_support =
  JSCVT_Unsupported
| JSCVT_Supported


definition jscvt_support_to_bits :: "jscvt_support \<Rightarrow> 4 word" where
  "jscvt_support_to_bits support \<equiv> case support of
     JSCVT_Unsupported \<Rightarrow> 0b0000
   | JSCVT_Supported   \<Rightarrow> 0b0001"


definition bits_to_jscvt_support :: "4 word \<Rightarrow> jscvt_support option" where
  "bits_to_jscvt_support w \<equiv>
     if w = 0b0000 then Some JSCVT_Unsupported else
     if w = 0b0001 then Some JSCVT_Supported else
     None" 

record apx_features =
  address_auth :: bool
  epac         :: bool
  pauth2       :: bool
  fpac         :: bool
  fpac_combine :: bool
  pauth_lr     :: bool


type_synonym api_features = apx_features


definition bits_to_api_features :: "4 word \<Rightarrow> api_features option" where
  "bits_to_api_features w \<equiv>
     if w = 0b0000 then Some \<lparr> address_auth = False, epac = False, pauth2 = False,
                               fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0001 then Some \<lparr> address_auth = True, epac = False, pauth2 = False,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0010 then Some \<lparr> address_auth = True, epac = True, pauth2 = False,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0011 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0100 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0101 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = True, pauth_lr = False \<rparr>
     else if w = 0b0110 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = True, pauth_lr = True \<rparr>
     else None" 


definition api_features_to_bits :: "api_features \<Rightarrow> 4 word option" where
  "api_features_to_bits f \<equiv>
    if      (\<not> address_auth f) then Some 0b0000
    else if (epac f)           then Some 0b0010
    else if (pauth_lr f)       then Some 0b0110
    else if (fpac_combine f)   then Some 0b0101
    else if (fpac f)           then Some 0b0100
    else if (pauth2 f)         then Some 0b0011
    else if (address_auth f)   then Some 0b0001
    else None"


type_synonym apa_features = apx_features


definition bits_to_apa_features :: "4 word \<Rightarrow> apa_features option" where
  "bits_to_apa_features w \<equiv>
     if w = 0b0000 then Some \<lparr> address_auth = False, epac = False, pauth2 = False,
                               fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0001 then Some \<lparr> address_auth = True, epac = False, pauth2 = False,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0010 then Some \<lparr> address_auth = True, epac = True, pauth2 = False,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0011 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0100 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0101 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = True, pauth_lr = False \<rparr>
     else if w = 0b0110 then Some \<lparr> address_auth = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = True, pauth_lr = True \<rparr>
     else None" 


definition apa_features_to_bits :: "apa_features \<Rightarrow> 4 word option" where
  "apa_features_to_bits f \<equiv>
    if      (\<not> address_auth f)      then Some 0b0000
    else if (epac f)                then Some 0b0010
    else if (pauth_lr f)            then Some 0b0110
    else if (fpac_combine f)        then Some 0b0101
    else if (fpac f)                then Some 0b0100
    else if (pauth2 f)              then Some 0b0011
    else if (address_auth f)        then Some 0b0001
    else None"


datatype dpb_support =
  DPB_None          
| DPB_CVAP          
| DPB_CVAP_CVADP    


definition dpb_support_to_bits :: "dpb_support \<Rightarrow> 4 word" where
  "dpb_support_to_bits support \<equiv> case support of
     DPB_None        \<Rightarrow> 0b0000
   | DPB_CVAP        \<Rightarrow> 0b0001
   | DPB_CVAP_CVADP  \<Rightarrow> 0b0010"


definition bits_to_dpb_support :: "4 word \<Rightarrow> dpb_support option" where
  "bits_to_dpb_support w \<equiv>
     if w = 0b0000 then Some DPB_None else
     if w = 0b0001 then Some DPB_CVAP else
     if w = 0b0010 then Some DPB_CVAP_CVADP else
     None" 

subsection \<open> ID_AA64ISAR2_EL1 \<close>


datatype ats1a_support =
  ATS1A_Unsupported
| ATS1A_Supported


definition ats1a_support_to_bits :: "ats1a_support \<Rightarrow> 4 word" where
  "ats1a_support_to_bits support \<equiv> case support of
     ATS1A_Unsupported \<Rightarrow> 0b0000
   | ATS1A_Supported   \<Rightarrow> 0b0001"


definition bits_to_ats1a_support :: "4 word \<Rightarrow> ats1a_support option" where
  "bits_to_ats1a_support w \<equiv>
     if w = 0b0000 then Some ATS1A_Unsupported else
     if w = 0b0001 then Some ATS1A_Supported else
     None" 


datatype lut_support =
  LUT_Unsupported
| LUT_Supported


definition lut_support_to_bits :: "lut_support \<Rightarrow> 4 word" where
  "lut_support_to_bits support \<equiv> case support of
     LUT_Unsupported \<Rightarrow> 0b0000
   | LUT_Supported   \<Rightarrow> 0b0001"


definition bits_to_lut_support :: "4 word \<Rightarrow> lut_support option" where
  "bits_to_lut_support w \<equiv>
     if w = 0b0000 then Some LUT_Unsupported else
     if w = 0b0001 then Some LUT_Supported else
     None" 


datatype cssc_support =
  CSSC_Unsupported
| CSSC_Supported


definition cssc_support_to_bits :: "cssc_support \<Rightarrow> 4 word" where
  "cssc_support_to_bits support \<equiv> case support of
     CSSC_Unsupported \<Rightarrow> 0b0000
   | CSSC_Supported   \<Rightarrow> 0b0001"


definition bits_to_cssc_support :: "4 word \<Rightarrow> cssc_support option" where
  "bits_to_cssc_support w \<equiv>
     if w = 0b0000 then Some CSSC_Unsupported else
     if w = 0b0001 then Some CSSC_Supported else
     None" 


datatype rprfm_support =
  RPRFM_Unsupported
| RPRFM_Supported


definition rprfm_support_to_bits :: "rprfm_support \<Rightarrow> 4 word" where
  "rprfm_support_to_bits support \<equiv> case support of
     RPRFM_Unsupported \<Rightarrow> 0b0000
   | RPRFM_Supported   \<Rightarrow> 0b0001"


definition bits_to_rprfm_support :: "4 word \<Rightarrow> rprfm_support option" where
  "bits_to_rprfm_support w \<equiv>
     if w = 0b0000 then Some RPRFM_Unsupported else
     if w = 0b0001 then Some RPRFM_Supported else
     None" 


datatype prfmslc_support =
  PRFMSLC_Unsupported
| PRFMSLC_Supported


definition prfmslc_support_to_bits :: "prfmslc_support \<Rightarrow> 4 word" where
  "prfmslc_support_to_bits support \<equiv> case support of
     PRFMSLC_Unsupported \<Rightarrow> 0b0000
   | PRFMSLC_Supported   \<Rightarrow> 0b0001"


definition bits_to_prfmslc_support :: "4 word \<Rightarrow> prfmslc_support option" where
  "bits_to_prfmslc_support w \<equiv>
     if w = 0b0000 then Some PRFMSLC_Unsupported else
     if w = 0b0001 then Some PRFMSLC_Supported else
     None" 


datatype sysinstr_128_support =
  SYSINSTR_128_Unsupported
| SYSINSTR_128_Supported


definition sysinstr_128_support_to_bits :: "sysinstr_128_support \<Rightarrow> 4 word" where
  "sysinstr_128_support_to_bits support \<equiv> case support of
     SYSINSTR_128_Unsupported \<Rightarrow> 0b0000
   | SYSINSTR_128_Supported   \<Rightarrow> 0b0001"


definition bits_to_sysinstr_128_support :: "4 word \<Rightarrow> sysinstr_128_support option" where
  "bits_to_sysinstr_128_support w \<equiv>
     if w = 0b0000 then Some SYSINSTR_128_Unsupported else
     if w = 0b0001 then Some SYSINSTR_128_Supported else
     None" 


datatype sysreg_128_support =
  SYSREG_128_Unsupported
| SYSREG_128_Supported


definition sysreg_128_support_to_bits :: "sysreg_128_support \<Rightarrow> 4 word" where
  "sysreg_128_support_to_bits support \<equiv> case support of
     SYSREG_128_Unsupported \<Rightarrow> 0b0000
   | SYSREG_128_Supported   \<Rightarrow> 0b0001"


definition bits_to_sysreg_128_support :: "4 word \<Rightarrow> sysreg_128_support option" where
  "bits_to_sysreg_128_support w \<equiv>
     if w = 0b0000 then Some SYSREG_128_Unsupported else
     if w = 0b0001 then Some SYSREG_128_Supported else
     None" 


datatype clrbhb_support =
  CLRBHB_Unsupported
| CLRBHB_Supported


definition clrbhb_support_to_bits :: "clrbhb_support \<Rightarrow> 4 word" where
  "clrbhb_support_to_bits support \<equiv> case support of
     CLRBHB_Unsupported \<Rightarrow> 0b0000
   | CLRBHB_Supported   \<Rightarrow> 0b0001"


definition bits_to_clrbhb_support :: "4 word \<Rightarrow> clrbhb_support option" where
  "bits_to_clrbhb_support w \<equiv>
     if w = 0b0000 then Some CLRBHB_Unsupported else
     if w = 0b0001 then Some CLRBHB_Supported else
     None" 


datatype pac_frac_behavior =
  PAC_frac_Dependent  
| PAC_frac_Fixed      


definition pac_frac_behavior_to_bits :: "pac_frac_behavior \<Rightarrow> 4 word" where
  "pac_frac_behavior_to_bits behavior \<equiv> case behavior of
     PAC_frac_Dependent \<Rightarrow> 0b0000
   | PAC_frac_Fixed     \<Rightarrow> 0b0001"


definition bits_to_pac_frac_behavior :: "4 word \<Rightarrow> pac_frac_behavior option" where
  "bits_to_pac_frac_behavior w \<equiv>
     if w = 0b0000 then Some PAC_frac_Dependent else
     if w = 0b0001 then Some PAC_frac_Fixed else
     None" 


datatype bc_support =
  BC_Unsupported
| BC_Supported


definition bc_support_to_bits :: "bc_support \<Rightarrow> 4 word" where
  "bc_support_to_bits support \<equiv> case support of
     BC_Unsupported \<Rightarrow> 0b0000
   | BC_Supported   \<Rightarrow> 0b0001"


definition bits_to_bc_support :: "4 word \<Rightarrow> bc_support option" where
  "bits_to_bc_support w \<equiv>
     if w = 0b0000 then Some BC_Unsupported else
     if w = 0b0001 then Some BC_Supported else
     None" 


datatype mops_support =
  MOPS_Unsupported
| MOPS_Supported


definition mops_support_to_bits :: "mops_support \<Rightarrow> 4 word" where
  "mops_support_to_bits support \<equiv> case support of
     MOPS_Unsupported \<Rightarrow> 0b0000
   | MOPS_Supported   \<Rightarrow> 0b0001"


definition bits_to_mops_support :: "4 word \<Rightarrow> mops_support option" where
  "bits_to_mops_support w \<equiv>
     if w = 0b0000 then Some MOPS_Unsupported else
     if w = 0b0001 then Some MOPS_Supported else
     None" 


record apa3_features =
  address_auth_qarma3 :: bool
  epac                :: bool
  pauth2              :: bool
  fpac                :: bool
  fpac_combine        :: bool
  pauth_lr            :: bool


definition bits_to_apa3_features :: "4 word \<Rightarrow> apa3_features option" where
  "bits_to_apa3_features w \<equiv>
     if w = 0b0000 then Some \<lparr> address_auth_qarma3 = False, epac = False, pauth2 = False,
                               fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0001 then Some \<lparr> address_auth_qarma3 = True, epac = False, pauth2 = False,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0010 then Some \<lparr> address_auth_qarma3 = True, epac = True, pauth2 = False,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0011 then Some \<lparr> address_auth_qarma3 = True, epac = False, pauth2 = True,
                                   fpac = False, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0100 then Some \<lparr> address_auth_qarma3 = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = False, pauth_lr = False \<rparr>
     else if w = 0b0101 then Some \<lparr> address_auth_qarma3 = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = True, pauth_lr = False \<rparr>
     else if w = 0b0110 then Some \<lparr> address_auth_qarma3 = True, epac = False, pauth2 = True,
                                   fpac = True, fpac_combine = True, pauth_lr = True \<rparr>
     else None" 


definition apa3_features_to_bits :: "apa3_features \<Rightarrow> 4 word option" where
  "apa3_features_to_bits f \<equiv>
    if      (\<not> address_auth_qarma3 f) then Some 0b0000
    else if (epac f)                then Some 0b0010
    else if (pauth_lr f)            then Some 0b0110
    else if (fpac_combine f)        then Some 0b0101
    else if (fpac f)                then Some 0b0100
    else if (pauth2 f)              then Some 0b0011
    else if (address_auth_qarma3 f) then Some 0b0001
    else None"


datatype gpa3_support =
  GPA3_Unsupported
| GPA3_Supported


definition gpa3_support_to_bits :: "gpa3_support \<Rightarrow> 4 word" where
  "gpa3_support_to_bits support \<equiv> case support of
     GPA3_Unsupported \<Rightarrow> 0b0000
   | GPA3_Supported   \<Rightarrow> 0b0001"


definition bits_to_gpa3_support :: "4 word \<Rightarrow> gpa3_support option" where
  "bits_to_gpa3_support w \<equiv>
     if w = 0b0000 then Some GPA3_Unsupported else
     if w = 0b0001 then Some GPA3_Supported else
     None" 


datatype rpres_precision =
  RPRES_8bit   
  | RPRES_12bit  


definition rpres_precision_to_bits :: "rpres_precision \<Rightarrow> 4 word" where
  "rpres_precision_to_bits precision \<equiv> case precision of
     RPRES_8bit  \<Rightarrow> 0b0000
   | RPRES_12bit \<Rightarrow> 0b0001"


definition bits_to_rpres_precision :: "4 word \<Rightarrow> rpres_precision option" where
  "bits_to_rpres_precision w \<equiv>
     if w = 0b0000 then Some RPRES_8bit else
     if w = 0b0001 then Some RPRES_12bit else
     None" 


datatype wfxt_support =
  WFxT_Unsupported
| WFxT_Supported


definition wfxt_support_to_bits :: "wfxt_support \<Rightarrow> 4 word" where
  "wfxt_support_to_bits support \<equiv> case support of
     WFxT_Unsupported \<Rightarrow> 0b0000
   | WFxT_Supported   \<Rightarrow> 0b0010"


definition bits_to_wfxt_support :: "4 word \<Rightarrow> wfxt_support option" where
  "bits_to_wfxt_support w \<equiv>
     if w = 0b0000 then Some WFxT_Unsupported else
     if w = 0b0010 then Some WFxT_Supported else
     None" 

subsection \<open> ID_AA64MMFR0_EL1 \<close>


datatype ecv_support =
  ECV_None          
| ECV_Base          
| ECV_with_CNTPOFF  


definition ecv_support_to_bits :: "ecv_support \<Rightarrow> 4 word" where
  "ecv_support_to_bits support \<equiv> case support of
     ECV_None         \<Rightarrow> 0b0000
   | ECV_Base         \<Rightarrow> 0b0001
   | ECV_with_CNTPOFF \<Rightarrow> 0b0010"


definition bits_to_ecv_support :: "4 word \<Rightarrow> ecv_support option" where
  "bits_to_ecv_support w \<equiv>
     if w = 0b0000 then Some ECV_None else
     if w = 0b0001 then Some ECV_Base else
     if w = 0b0010 then Some ECV_with_CNTPOFF else
     None" 


datatype fgt_support =
  FGT_None  
| FGT_Base  
| FGT_Ext   


definition fgt_support_to_bits :: "fgt_support \<Rightarrow> 4 word" where
  "fgt_support_to_bits support \<equiv> case support of
     FGT_None \<Rightarrow> 0b0000
   | FGT_Base \<Rightarrow> 0b0001
   | FGT_Ext  \<Rightarrow> 0b0010"


definition bits_to_fgt_support :: "4 word \<Rightarrow> fgt_support option" where
  "bits_to_fgt_support w \<equiv>
     if w = 0b0000 then Some FGT_None else
     if w = 0b0001 then Some FGT_Base else
     if w = 0b0010 then Some FGT_Ext else
     None" 


datatype exs_behavior =
  ExS_AlwaysSync          
| ExS_NonSyncSupported    


definition exs_behavior_to_bits :: "exs_behavior \<Rightarrow> 4 word" where
  "exs_behavior_to_bits behavior \<equiv> case behavior of
     ExS_AlwaysSync       \<Rightarrow> 0b0000
   | ExS_NonSyncSupported \<Rightarrow> 0b0001"


definition bits_to_exs_behavior :: "4 word \<Rightarrow> exs_behavior option" where
  "bits_to_exs_behavior w \<equiv>
     if w = 0b0000 then Some ExS_AlwaysSync else
     if w = 0b0001 then Some ExS_NonSyncSupported else
     None" 


datatype tgran4_2_support =
  TGran4_2_Delegated        
| TGran4_2_Unsupported      
| TGran4_2_Supported        
| TGran4_2_Supported_52bit  


definition tgran4_2_support_to_bits :: "tgran4_2_support \<Rightarrow> 4 word" where
  "tgran4_2_support_to_bits support \<equiv> case support of
     TGran4_2_Delegated       \<Rightarrow> 0b0000
   | TGran4_2_Unsupported     \<Rightarrow> 0b0001
   | TGran4_2_Supported       \<Rightarrow> 0b0010
   | TGran4_2_Supported_52bit \<Rightarrow> 0b0011"


definition bits_to_tgran4_2_support :: "4 word \<Rightarrow> tgran4_2_support option" where
  "bits_to_tgran4_2_support w \<equiv>
     if w = 0b0000 then Some TGran4_2_Delegated else
     if w = 0b0001 then Some TGran4_2_Unsupported else
     if w = 0b0010 then Some TGran4_2_Supported else
     if w = 0b0011 then Some TGran4_2_Supported_52bit else
     None" 


datatype tgran64_2_support =
  TGran64_2_Delegated    
| TGran64_2_Unsupported  
| TGran64_2_Supported    


definition tgran64_2_support_to_bits :: "tgran64_2_support \<Rightarrow> 4 word" where
  "tgran64_2_support_to_bits support \<equiv> case support of
     TGran64_2_Delegated   \<Rightarrow> 0b0000
   | TGran64_2_Unsupported \<Rightarrow> 0b0001
   | TGran64_2_Supported   \<Rightarrow> 0b0010"


definition bits_to_tgran64_2_support :: "4 word \<Rightarrow> tgran64_2_support option" where
  "bits_to_tgran64_2_support w \<equiv>
     if w = 0b0000 then Some TGran64_2_Delegated else
     if w = 0b0001 then Some TGran64_2_Unsupported else
     if w = 0b0010 then Some TGran64_2_Supported else
     None" 


datatype tgran16_2_support =
  TGran16_2_Delegated       
| TGran16_2_Unsupported     
| TGran16_2_Supported       
| TGran16_2_Supported_52bit 


definition tgran16_2_support_to_bits :: "tgran16_2_support \<Rightarrow> 4 word" where
  "tgran16_2_support_to_bits support \<equiv> case support of
     TGran16_2_Delegated       \<Rightarrow> 0b0000
   | TGran16_2_Unsupported     \<Rightarrow> 0b0001
   | TGran16_2_Supported       \<Rightarrow> 0b0010
   | TGran16_2_Supported_52bit \<Rightarrow> 0b0011"


definition bits_to_tgran16_2_support :: "4 word \<Rightarrow> tgran16_2_support option" where
  "bits_to_tgran16_2_support w \<equiv>
     if w = 0b0000 then Some TGran16_2_Delegated else
     if w = 0b0001 then Some TGran16_2_Unsupported else
     if w = 0b0010 then Some TGran16_2_Supported else
     if w = 0b0011 then Some TGran16_2_Supported_52bit else
     None" 


datatype tgran4_support =
  TGran4_Unsupported
| TGran4_Supported
| TGran4_Supported_52bit  


definition tgran4_support_to_bits :: "tgran4_support \<Rightarrow> 4 word" where
  "tgran4_support_to_bits support \<equiv> case support of
     TGran4_Supported       \<Rightarrow> 0b0000
   | TGran4_Supported_52bit \<Rightarrow> 0b0001
   | TGran4_Unsupported     \<Rightarrow> 0b1111"


definition bits_to_tgran4_support :: "4 word \<Rightarrow> tgran4_support option" where
  "bits_to_tgran4_support w \<equiv>
     if w = 0b0000 then Some TGran4_Supported else
     if w = 0b1111 then Some TGran4_Unsupported else
     if w = 0b0001 then Some TGran4_Supported_52bit else
     None" 


datatype tgran64_support =
  TGran64_Unsupported
| TGran64_Supported


definition tgran64_support_to_bits :: "tgran64_support \<Rightarrow> 4 word" where
  "tgran64_support_to_bits support \<equiv> case support of
     TGran64_Supported   \<Rightarrow> 0b0000
   | TGran64_Unsupported \<Rightarrow> 0b1111"


definition bits_to_tgran64_support :: "4 word \<Rightarrow> tgran64_support option" where
  "bits_to_tgran64_support w \<equiv>
     if w = 0b0000 then Some TGran64_Supported else
     if w = 0b1111 then Some TGran64_Unsupported else
     None" 


datatype tgran16_support =
  TGran16_Unsupported
| TGran16_Supported
| TGran16_Supported_52bit  


definition tgran16_support_to_bits :: "tgran16_support \<Rightarrow> 4 word" where
  "tgran16_support_to_bits support \<equiv> case support of
     TGran16_Unsupported    \<Rightarrow> 0b0000
   | TGran16_Supported      \<Rightarrow> 0b0001
   | TGran16_Supported_52bit \<Rightarrow> 0b0010"


definition bits_to_tgran16_support :: "4 word \<Rightarrow> tgran16_support option" where
  "bits_to_tgran16_support w \<equiv>
     if w = 0b0000 then Some TGran16_Unsupported else
     if w = 0b0001 then Some TGran16_Supported else
     if w = 0b0010 then Some TGran16_Supported_52bit else
     None" 


datatype big_end_el0_support =
  BigEndEL0_Unsupported
| BigEndEL0_Supported


definition big_end_el0_support_to_bits :: "big_end_el0_support \<Rightarrow> 4 word" where
  "big_end_el0_support_to_bits support \<equiv> case support of
     BigEndEL0_Unsupported \<Rightarrow> 0b0000
   | BigEndEL0_Supported   \<Rightarrow> 0b0001"


definition bits_to_big_end_el0_support :: "4 word \<Rightarrow> big_end_el0_support option" where
  "bits_to_big_end_el0_support w \<equiv>
     if w = 0b0000 then Some BigEndEL0_Unsupported else
     if w = 0b0001 then Some BigEndEL0_Supported else
     None" 


datatype sns_mem_support =
  SNSMem_Unsupported
| SNSMem_Supported


definition sns_mem_support_to_bits :: "sns_mem_support \<Rightarrow> 4 word" where
  "sns_mem_support_to_bits support \<equiv> case support of
     SNSMem_Unsupported \<Rightarrow> 0b0000
   | SNSMem_Supported   \<Rightarrow> 0b0001"


definition bits_to_sns_mem_support :: "4 word \<Rightarrow> sns_mem_support option" where
  "bits_to_sns_mem_support w \<equiv>
     if w = 0b0000 then Some SNSMem_Unsupported else
     if w = 0b0001 then Some SNSMem_Supported else
     None" 


datatype big_end_support =
  BigEnd_Unsupported
| BigEnd_Supported


definition big_end_support_to_bits :: "big_end_support \<Rightarrow> 4 word" where
  "big_end_support_to_bits support \<equiv> case support of
     BigEnd_Unsupported \<Rightarrow> 0b0000
   | BigEnd_Supported   \<Rightarrow> 0b0001"


definition bits_to_big_end_support :: "4 word \<Rightarrow> big_end_support option" where
  "bits_to_big_end_support w \<equiv>
     if w = 0b0000 then Some BigEnd_Unsupported else
     if w = 0b0001 then Some BigEnd_Supported else
     None" 


datatype asid_bits =
  ASID_8bit
| ASID_16bit


definition asid_bits_to_bits :: "asid_bits \<Rightarrow> 4 word" where
  "asid_bits_to_bits s \<equiv> case s of
     ASID_8bit  \<Rightarrow> 0b0000
   | ASID_16bit \<Rightarrow> 0b0010"


definition bits_to_asid_bits :: "4 word \<Rightarrow> asid_bits option" where
  "bits_to_asid_bits w \<equiv>
     if w = 0b0000 then Some ASID_8bit else
     if w = 0b0010 then Some ASID_16bit else
     None" 


datatype pa_range =
  PA_32bit
| PA_36bit
| PA_40bit
| PA_42bit
| PA_44bit
| PA_48bit
| PA_52bit  
| PA_56bit  


definition pa_range_to_bits :: "pa_range \<Rightarrow> 4 word" where
  "pa_range_to_bits pa \<equiv> case pa of
     PA_32bit \<Rightarrow> 0b0000
   | PA_36bit \<Rightarrow> 0b0001
   | PA_40bit \<Rightarrow> 0b0010
   | PA_42bit \<Rightarrow> 0b0011
   | PA_44bit \<Rightarrow> 0b0100
   | PA_48bit \<Rightarrow> 0b0101
   | PA_52bit \<Rightarrow> 0b0110
   | PA_56bit \<Rightarrow> 0b0111"


definition bits_to_pa_range :: "4 word \<Rightarrow> pa_range option" where
  "bits_to_pa_range w \<equiv>
     if w = 0b0000 then Some PA_32bit else
     if w = 0b0001 then Some PA_36bit else
     if w = 0b0010 then Some PA_40bit else
     if w = 0b0011 then Some PA_42bit else
     if w = 0b0100 then Some PA_44bit else
     if w = 0b0101 then Some PA_48bit else
     if w = 0b0110 then Some PA_52bit else
     if w = 0b0111 then Some PA_56bit else
     None" 

subsection \<open> ID_AA64MMFR1_EL1 \<close>


datatype ecbhb_behavior =
  ECBHB_Undisclosed  
| ECBHB_Guaranteed   


definition ecbhb_behavior_to_bits :: "ecbhb_behavior \<Rightarrow> 4 word" where
  "ecbhb_behavior_to_bits behavior \<equiv> case behavior of
     ECBHB_Undisclosed \<Rightarrow> 0b0000
   | ECBHB_Guaranteed  \<Rightarrow> 0b0001"


definition bits_to_ecbhb_behavior :: "4 word \<Rightarrow> ecbhb_behavior option" where
  "bits_to_ecbhb_behavior w \<equiv>
     if w = 0b0000 then Some ECBHB_Undisclosed else
     if w = 0b0001 then Some ECBHB_Guaranteed else
     None" 


datatype cmow_support =
  CMOW_Unsupported
| CMOW_Supported


definition cmow_support_to_bits :: "cmow_support \<Rightarrow> 4 word" where
  "cmow_support_to_bits support \<equiv> case support of
     CMOW_Unsupported \<Rightarrow> 0b0000
   | CMOW_Supported   \<Rightarrow> 0b0001"


definition bits_to_cmow_support :: "4 word \<Rightarrow> cmow_support option" where
  "bits_to_cmow_support w \<equiv>
     if w = 0b0000 then Some CMOW_Unsupported else
     if w = 0b0001 then Some CMOW_Supported else
     None" 


datatype tidcp1_support =
  TIDCP1_Unsupported
| TIDCP1_Supported


definition tidcp1_support_to_bits :: "tidcp1_support \<Rightarrow> 4 word" where
  "tidcp1_support_to_bits support \<equiv> case support of
     TIDCP1_Unsupported \<Rightarrow> 0b0000
   | TIDCP1_Supported   \<Rightarrow> 0b0001"


definition bits_to_tidcp1_support :: "4 word \<Rightarrow> tidcp1_support option" where
  "bits_to_tidcp1_support w \<equiv>
     if w = 0b0000 then Some TIDCP1_Unsupported else
     if w = 0b0001 then Some TIDCP1_Supported else
     None" 


datatype nTLBPA_behavior =
  nTLBPA_NonCoherent  
| nTLBPA_Coherent     


definition nTLBPA_behavior_to_bits :: "nTLBPA_behavior \<Rightarrow> 4 word" where
  "nTLBPA_behavior_to_bits behavior \<equiv> case behavior of
     nTLBPA_NonCoherent \<Rightarrow> 0b0000
   | nTLBPA_Coherent    \<Rightarrow> 0b0001"


definition bits_to_nTLBPA_behavior :: "4 word \<Rightarrow> nTLBPA_behavior option" where
  "bits_to_nTLBPA_behavior w \<equiv>
     if w = 0b0000 then Some nTLBPA_NonCoherent else
     if w = 0b0001 then Some nTLBPA_Coherent else
     None" 


datatype afp_support =
  AFP_Unsupported
| AFP_Supported


definition afp_support_to_bits :: "afp_support \<Rightarrow> 4 word" where
  "afp_support_to_bits support \<equiv> case support of
     AFP_Unsupported \<Rightarrow> 0b0000
   | AFP_Supported   \<Rightarrow> 0b0001"


definition bits_to_afp_support :: "4 word \<Rightarrow> afp_support option" where
  "bits_to_afp_support w \<equiv>
     if w = 0b0000 then Some AFP_Unsupported else
     if w = 0b0001 then Some AFP_Supported else
     None" 


datatype hcx_support =
  HCX_Unsupported
| HCX_Supported


definition hcx_support_to_bits :: "hcx_support \<Rightarrow> 4 word" where
  "hcx_support_to_bits support \<equiv> case support of
     HCX_Unsupported \<Rightarrow> 0b0000
   | HCX_Supported   \<Rightarrow> 0b0001"


definition bits_to_hcx_support :: "4 word \<Rightarrow> hcx_support option" where
  "bits_to_hcx_support w \<equiv>
     if w = 0b0000 then Some HCX_Unsupported else
     if w = 0b0001 then Some HCX_Supported else
     None" 


datatype ets_support =
  ETS_Unsupported
| ETS_v2           
| ETS_v3           


definition ets_support_to_bits :: "ets_support \<Rightarrow> 4 word" where
  "ets_support_to_bits support \<equiv> case support of
     ETS_Unsupported \<Rightarrow> 0b0000
   | ETS_v2          \<Rightarrow> 0b0010
   | ETS_v3          \<Rightarrow> 0b0011"


definition bits_to_ets_support :: "4 word \<Rightarrow> ets_support option" where
  "bits_to_ets_support w \<equiv>
     if w = 0b0000 \<or> w = 0b0001 then Some ETS_Unsupported else
     if w = 0b0010 then Some ETS_v2 else
     if w = 0b0011 then Some ETS_v3 else
     None" 


datatype twed_support =
  TWED_Unsupported
| TWED_Supported


definition twed_support_to_bits :: "twed_support \<Rightarrow> 4 word" where
  "twed_support_to_bits support \<equiv> case support of
     TWED_Unsupported \<Rightarrow> 0b0000
   | TWED_Supported   \<Rightarrow> 0b0001"


definition bits_to_twed_support :: "4 word \<Rightarrow> twed_support option" where
  "bits_to_twed_support w \<equiv>
     if w = 0b0000 then Some TWED_Unsupported else
     if w = 0b0001 then Some TWED_Supported else
     None" 


datatype xnx_support =
  XNX_Unsupported
| XNX_Supported


definition xnx_support_to_bits :: "xnx_support \<Rightarrow> 4 word" where
  "xnx_support_to_bits support \<equiv> case support of
     XNX_Unsupported \<Rightarrow> 0b0000
   | XNX_Supported   \<Rightarrow> 0b0001"


definition bits_to_xnx_support :: "4 word \<Rightarrow> xnx_support option" where
  "bits_to_xnx_support w \<equiv>
     if w = 0b0000 then Some XNX_Unsupported else
     if w = 0b0001 then Some XNX_Supported else
     None" 


datatype spec_sei_behavior =
  SpecSEI_Never   
| SpecSEI_Might   


definition spec_sei_behavior_to_bits :: "spec_sei_behavior \<Rightarrow> 4 word" where
  "spec_sei_behavior_to_bits behavior \<equiv> case behavior of
     SpecSEI_Never \<Rightarrow> 0b0000
   | SpecSEI_Might \<Rightarrow> 0b0001"


definition bits_to_spec_sei_behavior :: "4 word \<Rightarrow> spec_sei_behavior option" where
  "bits_to_spec_sei_behavior w \<equiv>
     if w = 0b0000 then Some SpecSEI_Never else
     if w = 0b0001 then Some SpecSEI_Might else
     None" 


datatype pan_support =
  PAN_None       
| PAN_Base       
| PAN_with_AT    
| PAN_with_EPAN  


definition pan_support_to_bits :: "pan_support \<Rightarrow> 4 word" where
  "pan_support_to_bits support \<equiv> case support of
     PAN_None      \<Rightarrow> 0b0000
   | PAN_Base      \<Rightarrow> 0b0001
   | PAN_with_AT   \<Rightarrow> 0b0010
   | PAN_with_EPAN \<Rightarrow> 0b0011"


definition bits_to_pan_support :: "4 word \<Rightarrow> pan_support option" where
  "bits_to_pan_support w \<equiv>
     if w = 0b0000 then Some PAN_None else
     if w = 0b0001 then Some PAN_Base else
     if w = 0b0010 then Some PAN_with_AT else
     if w = 0b0011 then Some PAN_with_EPAN else
     None" 


datatype lo_support =
  LO_Unsupported
| LO_Supported


definition lo_support_to_bits :: "lo_support \<Rightarrow> 4 word" where
  "lo_support_to_bits support \<equiv> case support of
     LO_Unsupported \<Rightarrow> 0b0000
   | LO_Supported   \<Rightarrow> 0b0001"


definition bits_to_lo_support :: "4 word \<Rightarrow> lo_support option" where
  "bits_to_lo_support w \<equiv>
     if w = 0b0000 then Some LO_Unsupported else
     if w = 0b0001 then Some LO_Supported else
     None" 


datatype hpds_support =
  HPDS_None       
| HPDS_Base       
| HPDS_with_Alloc 


definition hpds_support_to_bits :: "hpds_support \<Rightarrow> 4 word" where
  "hpds_support_to_bits support \<equiv> case support of
     HPDS_None       \<Rightarrow> 0b0000
   | HPDS_Base       \<Rightarrow> 0b0001
   | HPDS_with_Alloc \<Rightarrow> 0b0010"


definition bits_to_hpds_support :: "4 word \<Rightarrow> hpds_support option" where
  "bits_to_hpds_support w \<equiv>
     if w = 0b0000 then Some HPDS_None else
     if w = 0b0001 then Some HPDS_Base else
     if w = 0b0010 then Some HPDS_with_Alloc else
     None" 


datatype vh_support =
  VH_Unsupported
| VH_Supported


definition vh_support_to_bits :: "vh_support \<Rightarrow> 4 word" where
  "vh_support_to_bits support \<equiv> case support of
     VH_Unsupported \<Rightarrow> 0b0000
   | VH_Supported   \<Rightarrow> 0b0001"


definition bits_to_vh_support :: "4 word \<Rightarrow> vh_support option" where
  "bits_to_vh_support w \<equiv>
     if w = 0b0000 then Some VH_Unsupported else
     if w = 0b0001 then Some VH_Supported else
     None" 


datatype vmid_bits =
  VMID_8bit
| VMID_16bit


definition vmid_bits_to_bits :: "vmid_bits \<Rightarrow> 4 word" where
  "vmid_bits_to_bits s \<equiv> case s of
     VMID_8bit  \<Rightarrow> 0b0000
   | VMID_16bit \<Rightarrow> 0b0010"


definition bits_to_vmid_bits :: "4 word \<Rightarrow> vmid_bits option" where
  "bits_to_vmid_bits w \<equiv>
     if w = 0b0000 then Some VMID_8bit else
     if w = 0b0010 then Some VMID_16bit else
     None" 


datatype hafdbs_support =
  HAFDBS_None          
| HAFDBS_AF_BlockPage  
| HAFDBS_AF_Dirty      
| HAFDBS_AF_Table      
| HAFDBS_DirtyStruct   


definition hafdbs_support_to_bits :: "hafdbs_support \<Rightarrow> 4 word" where
  "hafdbs_support_to_bits support \<equiv> case support of
     HAFDBS_None         \<Rightarrow> 0b0000
   | HAFDBS_AF_BlockPage \<Rightarrow> 0b0001
   | HAFDBS_AF_Dirty     \<Rightarrow> 0b0010
   | HAFDBS_AF_Table     \<Rightarrow> 0b0011
   | HAFDBS_DirtyStruct  \<Rightarrow> 0b0100"


definition bits_to_hafdbs_support :: "4 word \<Rightarrow> hafdbs_support option" where
  "bits_to_hafdbs_support w \<equiv>
     if w = 0b0000 then Some HAFDBS_None else
     if w = 0b0001 then Some HAFDBS_AF_BlockPage else
     if w = 0b0010 then Some HAFDBS_AF_Dirty else
     if w = 0b0011 then Some HAFDBS_AF_Table else
     if w = 0b0100 then Some HAFDBS_DirtyStruct else
     None" 

subsection \<open> ID_AA64MMFR2_EL1 \<close>


datatype e0pd_support =
  E0PD_Unsupported
| E0PD_Supported


definition e0pd_support_to_bits :: "e0pd_support \<Rightarrow> 4 word" where
  "e0pd_support_to_bits support \<equiv> case support of
     E0PD_Unsupported \<Rightarrow> 0b0000
   | E0PD_Supported   \<Rightarrow> 0b0001"


definition bits_to_e0pd_support :: "4 word \<Rightarrow> e0pd_support option" where
  "bits_to_e0pd_support w \<equiv>
     if w = 0b0000 then Some E0PD_Unsupported else
     if w = 0b0001 then Some E0PD_Supported else
     None" 


datatype evt_support =
  EVT_None     
| EVT_Partial  
| EVT_Full     


definition evt_support_to_bits :: "evt_support \<Rightarrow> 4 word" where
  "evt_support_to_bits support \<equiv> case support of
     EVT_None    \<Rightarrow> 0b0000
   | EVT_Partial \<Rightarrow> 0b0001
   | EVT_Full    \<Rightarrow> 0b0010"


definition bits_to_evt_support :: "4 word \<Rightarrow> evt_support option" where
  "bits_to_evt_support w \<equiv>
     if w = 0b0000 then Some EVT_None else
     if w = 0b0001 then Some EVT_Partial else
     if w = 0b0010 then Some EVT_Full else
     None" 


datatype bbm_level =
  BBM_Level0
| BBM_Level1
| BBM_Level2


definition bbm_level_to_bits :: "bbm_level \<Rightarrow> 4 word" where
  "bbm_level_to_bits lvl \<equiv> case lvl of
     BBM_Level0 \<Rightarrow> 0b0000
   | BBM_Level1 \<Rightarrow> 0b0001
   | BBM_Level2 \<Rightarrow> 0b0010"


definition bits_to_bbm_level :: "4 word \<Rightarrow> bbm_level option" where
  "bits_to_bbm_level w \<equiv>
     if w = 0b0000 then Some BBM_Level0 else
     if w = 0b0001 then Some BBM_Level1 else
     if w = 0b0010 then Some BBM_Level2 else
     None" 


datatype ttl_behavior =
  TTL_RES0      
| TTL_Supported 


definition ttl_behavior_to_bits :: "ttl_behavior \<Rightarrow> 4 word" where
  "ttl_behavior_to_bits behavior \<equiv> case behavior of
     TTL_RES0      \<Rightarrow> 0b0000
   | TTL_Supported \<Rightarrow> 0b0001"


definition bits_to_ttl_behavior :: "4 word \<Rightarrow> ttl_behavior option" where
  "bits_to_ttl_behavior w \<equiv>
     if w = 0b0000 then Some TTL_RES0 else
     if w = 0b0001 then Some TTL_Supported else
     None" 


datatype fwb_support =
  FWB_Unsupported
| FWB_Supported


definition fwb_support_to_bits :: "fwb_support \<Rightarrow> 4 word" where
  "fwb_support_to_bits support \<equiv> case support of
     FWB_Unsupported \<Rightarrow> 0b0000
   | FWB_Supported   \<Rightarrow> 0b0001"


definition bits_to_fwb_support :: "4 word \<Rightarrow> fwb_support option" where
  "bits_to_fwb_support w \<equiv>
     if w = 0b0000 then Some FWB_Unsupported else
     if w = 0b0001 then Some FWB_Supported else
     None" 


datatype ids_behavior =
  IDS_EC_0x0   
| IDS_EC_0x18  


definition ids_behavior_to_bits :: "ids_behavior \<Rightarrow> 4 word" where
  "ids_behavior_to_bits behavior \<equiv> case behavior of
     IDS_EC_0x0  \<Rightarrow> 0b0000
   | IDS_EC_0x18 \<Rightarrow> 0b0001"


definition bits_to_ids_behavior :: "4 word \<Rightarrow> ids_behavior option" where
  "bits_to_ids_behavior w \<equiv>
     if w = 0b0000 then Some IDS_EC_0x0 else
     if w = 0b0001 then Some IDS_EC_0x18 else
     None" 


datatype at_support =
  AT_Unsupported
| AT_Supported


definition at_support_to_bits :: "at_support \<Rightarrow> 4 word" where
  "at_support_to_bits support \<equiv> case support of
     AT_Unsupported \<Rightarrow> 0b0000
   | AT_Supported   \<Rightarrow> 0b0001"


definition bits_to_at_support :: "4 word \<Rightarrow> at_support option" where
  "bits_to_at_support w \<equiv>
     if w = 0b0000 then Some AT_Unsupported else
     if w = 0b0001 then Some AT_Supported else
     None" 


datatype st_level =
  ST_MaxTSZ_39      
| ST_MaxTSZ_47_48   


definition st_level_to_bits :: "st_level \<Rightarrow> 4 word" where
  "st_level_to_bits lvl \<equiv> case lvl of
     ST_MaxTSZ_39    \<Rightarrow> 0b0000
   | ST_MaxTSZ_47_48 \<Rightarrow> 0b0001"


definition bits_to_st_level :: "4 word \<Rightarrow> st_level option" where
  "bits_to_st_level w \<equiv>
     if w = 0b0000 then Some ST_MaxTSZ_39 else
     if w = 0b0001 then Some ST_MaxTSZ_47_48 else
     None" 


datatype nv_support =
  NV_Delegated    
| NV_Base         
| NV_with_VNCR    


definition nv_support_to_bits :: "nv_support \<Rightarrow> 4 word" where
  "nv_support_to_bits support \<equiv> case support of
     NV_Delegated   \<Rightarrow> 0b0000
   | NV_Base        \<Rightarrow> 0b0001
   | NV_with_VNCR   \<Rightarrow> 0b0010"


definition bits_to_nv_support :: "4 word \<Rightarrow> nv_support option" where
  "bits_to_nv_support w \<equiv>
     if w = 0b0000 then Some NV_Delegated else
     if w = 0b0001 then Some NV_Base else
     if w = 0b0010 then Some NV_with_VNCR else
     None" 


datatype ccidx_format =
  CCIDX_32bit
| CCIDX_64bit


definition ccidx_format_to_bits :: "ccidx_format \<Rightarrow> 4 word" where
  "ccidx_format_to_bits format \<equiv> case format of
     CCIDX_32bit \<Rightarrow> 0b0000
   | CCIDX_64bit \<Rightarrow> 0b0001"


definition bits_to_ccidx_format :: "4 word \<Rightarrow> ccidx_format option" where
  "bits_to_ccidx_format w \<equiv>
     if w = 0b0000 then Some CCIDX_32bit else
     if w = 0b0001 then Some CCIDX_64bit else
     None" 


datatype va_range =
  VA_48bit
| VA_52bit_Granule_Dependent  
| VA_56bit                    


definition va_range_to_bits :: "va_range \<Rightarrow> 4 word" where
  "va_range_to_bits va \<equiv> case va of
     VA_48bit                   \<Rightarrow> 0b0000
   | VA_52bit_Granule_Dependent \<Rightarrow> 0b0001
   | VA_56bit                   \<Rightarrow> 0b0010"


definition bits_to_va_range :: "4 word \<Rightarrow> va_range option" where
  "bits_to_va_range w \<equiv>
     if w = 0b0000 then Some VA_48bit else
     if w = 0b0001 then Some VA_52bit_Granule_Dependent else
     if w = 0b0010 then Some VA_56bit else
     None" 


datatype iesb_support =
  IESB_Unsupported
| IESB_Supported


definition iesb_support_to_bits :: "iesb_support \<Rightarrow> 4 word" where
  "iesb_support_to_bits support \<equiv> case support of
     IESB_Unsupported \<Rightarrow> 0b0000
   | IESB_Supported   \<Rightarrow> 0b0001"


definition bits_to_iesb_support :: "4 word \<Rightarrow> iesb_support option" where
  "bits_to_iesb_support w \<equiv>
     if w = 0b0000 then Some IESB_Unsupported else
     if w = 0b0001 then Some IESB_Supported else
     None" 


datatype lsm_support =
  LSM_Unsupported
| LSM_Supported


definition lsm_support_to_bits :: "lsm_support \<Rightarrow> 4 word" where
  "lsm_support_to_bits support \<equiv> case support of
     LSM_Unsupported \<Rightarrow> 0b0000
   | LSM_Supported   \<Rightarrow> 0b0001"


definition bits_to_lsm_support :: "4 word \<Rightarrow> lsm_support option" where
  "bits_to_lsm_support w \<equiv>
     if w = 0b0000 then Some LSM_Unsupported else
     if w = 0b0001 then Some LSM_Supported else
     None" 


datatype uao_support =
  UAO_Unsupported
| UAO_Supported


definition uao_support_to_bits :: "uao_support \<Rightarrow> 4 word" where
  "uao_support_to_bits support \<equiv> case support of
     UAO_Unsupported \<Rightarrow> 0b0000
   | UAO_Supported   \<Rightarrow> 0b0001"


definition bits_to_uao_support :: "4 word \<Rightarrow> uao_support option" where
  "bits_to_uao_support w \<equiv>
     if w = 0b0000 then Some UAO_Unsupported else
     if w = 0b0001 then Some UAO_Supported else
     None" 


datatype cnp_support =
  CnP_Unsupported
| CnP_Supported


definition cnp_support_to_bits :: "cnp_support \<Rightarrow> 4 word" where
  "cnp_support_to_bits support \<equiv> case support of
     CnP_Unsupported \<Rightarrow> 0b0000
   | CnP_Supported   \<Rightarrow> 0b0001"


definition bits_to_cnp_support :: "4 word \<Rightarrow> cnp_support option" where
  "bits_to_cnp_support w \<equiv>
     if w = 0b0000 then Some CnP_Unsupported else
     if w = 0b0001 then Some CnP_Supported else
     None" 

section \<open> Reg Spec \<close>

subsection \<open> SCTLR_EL1 \<close>

record SCTLR_EL1 =

TIDCP :: bool
SPINTMASK :: bool
NMI :: bool
EnTP2 :: bool
TCSO :: bool
TCSO0 :: bool
EPAN :: bool
EnAlS :: bool

EnAS0 :: bool
EnASR :: bool
TME :: bool
TME0 :: bool
TMT :: bool
TMT0 :: bool
TWEDEL :: "4 word"

TWEDEn :: bool
DSSBS :: bool
ATA :: bool
ATA0 :: bool
TCF :: tcf_mode

TCF0 :: tcf_mode
ITFSB :: bool
BT1 :: bool
BT0 :: bool
EnFPM :: bool
MSCEn :: bool
CMOW :: bool

EnIA :: bool
EnIB :: bool
LSMAOE :: bool
nTLSMD :: bool
EnDA :: bool
UCI :: bool
EE :: bool
E0E :: bool

SPAN :: bool
EIS :: bool
IESB :: bool
TSCXT :: bool
WXN :: bool
nTWE :: bool
B17RES0 :: "1 word"
nTWI :: bool

UCT :: bool
DZE :: bool
EnDB :: bool
I :: bool
EOS :: bool
EnRCTX :: bool
UMA :: bool
SED :: bool

ITD :: bool
nAA :: bool
CP15BEN :: bool
SA0 :: bool
SA :: bool
C :: bool
A :: bool
M :: bool

definition t1 :: "1 word" where "t1 = 1"

value "ucast (42::32 word) :: 64 word"

subsection \<open> TCR_EL1 \<close>

record TCR_EL1 =

B6362RES0 :: "2 word"
MTX1 :: bool
MTX0 :: bool
DS :: bool
TCMA1 :: bool
TCMA0 :: bool
E0PD1 :: bool

E0PD0 :: bool
NFD1 :: bool
NFD0 :: bool
TBID1 :: bool
TBID0 :: bool
HWU162 :: bool
HWU161 :: bool
HWU160 :: bool

HWU159 :: bool
HWU062 :: bool
HWU061 :: bool
HWU060 :: bool
HWU059 :: bool
HPD1 :: bool
HPD0 :: bool
HD :: bool

HA :: bool
TBI1 :: bool
TBI0 :: bool
AS :: bool
B35RES0 :: "1 word"
IPS :: ips_val

TG1 :: tg_granule
SH1 :: shareability_domain
ORGN1 :: cacheability
IRGN1 :: cacheability

EPD1 :: bool
A1 :: bool
T1SZ :: "6 word"

TG0 :: tg_granule
SH0 :: shareability_domain
ORGN0 :: cacheability
IRGN0 :: cacheability

EPD0 :: bool
B06RES0 :: "1 word"
T0SZ :: "6 word"

subsection \<open> MAIR_EL1 \<close>

record MAIR_EL1 =
Attr0 :: "8 word"
Attr1 :: "8 word"
Attr2 :: "8 word"
Attr3 :: "8 word"
Attr4 :: "8 word"
Attr5 :: "8 word"
Attr6 :: "8 word"
Attr7 :: "8 word"

subsection \<open> TTBR0_EL1 \<close>

record TTBRx_EL1 =
ASID :: "16 word"
BADDR :: "47 word"
CnP :: bool

type_synonym TTBR0_EL1 = TTBRx_EL1

subsection \<open> TTBR1_EL1 \<close>

type_synonym TTBR1_EL1 = TTBRx_EL1

subsection \<open> ESR_EL1 \<close>

record ESR_EL1 =

ISS2 :: "24 word"
EC :: "6 word"
IL :: instruction_length
ISS :: "25 word"

subsection \<open> FAR_EL1 \<close>

record FAR_EL1 =
FaultingVA :: "64 word"

subsection \<open> CONTEXTIDR_EL1 \<close>

record CONTEXTIDR_EL1 =

PROCID :: "32 word"

subsection \<open> AFSR0_EL1 \<close>

record DEFAULT_REG =
Value :: "64 word"

type_synonym AFSR0_EL1 =
DEFAULT_REG

subsection \<open> AFSR1_EL1 \<close>

type_synonym AFSR1_EL1 =
DEFAULT_REG

subsection \<open> AMAIR_EL1 \<close>

type_synonym AMAIR_EL1 =
DEFAULT_REG

subsection \<open> ACTLR_EL1 \<close>

type_synonym ACTLR_EL1 =
DEFAULT_REG

subsection \<open> HCR_EL2 \<close>

type_synonym HCR_EL2 =
DEFAULT_REG

subsection \<open> ID_PFR0_EL1 \<close>

record ID_PFR0_EL1 =

RAS :: ras_level
DIT :: dit_support
AMU :: amu_version
CSV2 :: csv2_version
State3 :: t32ee_support
State2 :: jazelle_support
State1 :: t32_support
State0 :: a32_support

subsection \<open> ID_PFR1_EL1 \<close>

record ID_PFR1_EL1 =

GIC :: gic_version
Virt_frac :: virt_ext_support
Sec_frac :: sec_ext_support
GenTimer :: gen_timer_support
Virtualization :: virtualization_support
MProgMod :: mprog_model
Security :: security_support
ProgMod :: prog_model_support

subsection \<open> ID_DFR0_EL1 \<close>

subsection \<open> ID_AFR0_EL1 \<close>

subsection \<open> ID_MMFR0_EL1 \<close>

subsection \<open> ID_MMFR1_EL1 \<close>

subsection \<open> ID_MMFR2_EL1 \<close>

subsection \<open> ID_MMFR3_EL1 \<close>

subsection \<open> ID_ISAR0_EL1 \<close>

subsection \<open> ID_ISAR1_EL1 \<close>

subsection \<open> ID_ISAR2_EL1 \<close>

subsection \<open> ID_ISAR3_EL1 \<close>

subsection \<open> ID_ISAR4_EL1 \<close>

subsection \<open> ID_ISAR5_EL1 \<close>

subsection \<open> ID_MMFR4_EL1 \<close>

subsection \<open> ID_ISAR6_EL1 \<close>

subsection \<open> MVFR0_EL1 \<close>

subsection \<open> MVFR1_EL1 \<close>

subsection \<open> MVFR2_EL1 \<close>

subsection \<open> ID_PFR2_EL1 \<close>

subsection \<open> ID_DFR1_EL1 \<close>

subsection \<open> ID_MMFR5_EL1 \<close>

subsection \<open> ID_AA64PFR0_EL1 \<close>

record ID_AA64PFR0_EL1 =
CSV3 :: csv3_behavior
CSV2 :: csv2_level
RME :: rme_version
DIT :: dit_aarch64_support
AMU :: amu_version
MPAM :: mpam_major_version
SEL2 :: sel2_support
SVE :: sve_support
RAS :: ras_version
GIC :: gic_version
AdvSIMD :: adv_simd_support
FP :: fp_support
EL3 :: el3_support
EL2 :: el2_support
EL1 :: el1_support
EL0 :: el0_support

subsection \<open> ID_AA64PFR1_EL1 \<close>

record ID_AA64PFR1_EL1 =
PFAR :: pfar_support
DF2 :: df2_support
MTEX :: mtex_support
THE :: the_support
GCS :: gcs_support
MTE_frac :: mte_async_support
NMI :: nmi_support
CSV2_frac :: csv2_frac_level
RNDR_trap :: rndr_trap_support
SME :: sme_support

MPAM_frac :: mpam_minor_version
RAS_frac :: ras_frac_level
MTE :: mte_level
SSBS :: ssbs_support
BT :: bt_support

subsection \<open> ID_AA64ZFR0_EL1 \<close>

record ID_AA64ZFR0_EL1 =

F64MM :: f64mm_support
F32MM :: f32mm_support

I8MM :: i8mm_support
SM4 :: sm4_support

SHA3 :: sha3_support

B16B16 :: b16b16_support
BF16 :: bf16_support
BitPerm :: bit_perm_support
EltPerm :: elt_perm_support

AES :: aes_pmull_features
SVEver :: sve_feature

subsection \<open> ID_AA64DFR0_EL1 \<close>

record ID_AA64DFR0_EL1 =
HPMN0 :: hpmn0_behavior
ExtTrcBuff :: ext_trc_buff_support
BRBE :: brbe_support
MTPMU :: mtpmu_support
TraceBuffer :: trace_buffer_support
TraceFilt :: trace_filt_support
DoubleLock :: double_lock_support
PMSVer :: pms_version
CTX_CMPs :: ctx_cmps_val
SEBEP :: sebep_support
WRPs :: wrps_val
PMSS :: pmss_support
BRPs :: brps_val
PMUVer :: pmu_version
TraceVer :: trace_ver_support
DebugVer :: debug_version

subsection \<open> ID_AA64DFR1_EL1 \<close>

record ID_AA64DFR1_EL1 =
ABL_CMPs :: abl_cmps_val
DPFZS :: dpfzs_behavior
EBEP :: ebep_support
ITE :: ite_support
ABLE :: able_support
PMICNTR :: pmicntr_support
SPMU :: spmu_support
CTX_CMPs :: ctx_cmps_val_long
WRPs :: wrps_val_long
BRPs :: brps_val_long
SYSPMUID :: syspmuid_val

subsection \<open> ID_AA64AFR0_EL1 \<close>

record ID_AA64AFR0_EL1 =

UNDEFINED :: "32 word"

subsection \<open> ID_AA64AFR1_EL1 \<close>

record ID_AA64AFR1_EL1 =

RES0 :: "64 word"

subsection \<open> ID_AA64ISAR0_EL1 \<close>

record ID_AA64ISAR0_EL1 =
RNDR :: rndr_support
TLB :: tlb_support
TS :: ts_support
FHM :: fhm_support
DP :: dp_support
SM4 :: sm4_support
SM3 :: sm3_support
SHA3 :: sha3_support
RDM :: rdm_support
TME :: tme_support
Atomic :: atomic_support
CRC32 :: crc32_support
SHA2 :: sha2_support
SHA1 :: sha1_support
AES :: aes_support


subsection \<open> ID_AA64ISAR1_EL1 \<close>

record ID_AA64ISAR1_EL1 =
LS64 :: ls64_support
XS :: xs_support
I8MM :: i8mm_support
DGH :: dgh_support
BF16 :: bf16_support
SPECRES :: specres_support
SB :: sb_support
FRINTTS :: frintts_support
GPI :: gpi_support
GPA :: gpa_support
LRCPC :: lrcpc_support
FCMA :: fcma_support
JSCVT :: jscvt_support
API :: api_features
APA :: apa_features
DPB :: dpb_support

subsection \<open> ID_AA64ISAR2_EL1 \<close>

record ID_AA64ISAR2_EL1 =
ATS1A :: ats1a_support
LUT :: lut_support
CSSC :: cssc_support
RPRFM :: rprfm_support

PRFMSLC :: prfmslc_support
SYSINSTR_128 :: sysinstr_128_support
SYSREG_128 :: sysreg_128_support
CLRBHB :: clrbhb_support
PAC_frac :: pac_frac_behavior
BC :: bc_support
MOPS :: mops_support
APA3 :: apa3_features
GPA3 :: gpa3_support
RPRES :: rpres_precision
WFxT :: wfxt_support

subsection \<open> ID_AA64MMFR0_EL1 \<close>

record ID_AA64MMFR0_EL1 =
ECV :: ecv_support
FGT :: fgt_support

ExS :: exs_behavior
TGran4_2 :: tgran4_2_support
TGran64_2 :: tgran64_2_support
TGran16_2 :: tgran16_2_support
TGran4 :: tgran4_support
TGran64 :: tgran64_support
TGran16 :: tgran16_support
BigEndEL0 :: big_end_el0_support
SNSMem :: sns_mem_support
BigEnd :: big_end_support
ASIDBits :: asid_bits
PARange :: pa_range

subsection \<open> ID_AA64MMFR1_EL1 \<close>

record ID_AA64MMFR1_EL1 =
ECBHB :: ecbhb_behavior
CMOW :: cmow_support
TIDCP1 :: tidcp1_support
nTLBPA :: nTLBPA_behavior
AFP :: afp_support
HCX :: hcx_support
ETS :: ets_support
TWED :: twed_support
XNX :: xnx_support
SpecSEI :: spec_sei_behavior
PAN :: pan_support
LO :: lo_support
HPDS :: hpds_support
VH :: vh_support
VMIDBits :: vmid_bits
HAFDBS :: hafdbs_support

subsection \<open> ID_AA64MMFR2_EL1 \<close>

record ID_AA64MMFR2_EL1 =
E0PD :: e0pd_support
EVT :: evt_support
BBM :: bbm_level
TTL :: ttl_behavior

FWB :: fwb_support
IDS :: ids_behavior
AT :: at_support
ST :: st_level
NV :: nv_support
CCIDX :: ccidx_format
VARange :: va_range
IESB :: iesb_support
LSM :: lsm_support
UAO :: uao_support
CnP :: cnp_support

end
