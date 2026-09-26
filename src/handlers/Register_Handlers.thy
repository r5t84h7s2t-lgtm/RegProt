theory Register_Handlers
  imports
    Main
    "../machine/Register_Access"
begin

definition is_aarch64 ::
  "State \<Rightarrow> bool"
  where
    "is_aarch64 s \<equiv> (is_aarch64_config (sys_config s))"

definition use_LPAE ::
  "State \<Rightarrow> bool"
  where
    "use_LPAE s \<equiv> (use_LPAE_config (sys_config s))"

section \<open> Events: Write System Register Event \<close>

subsection \<open> 64 bit mode \<close>

definition SCTLR_EL1_validate ::
  "State \<Rightarrow> SCTLR_EL1 \<Rightarrow> (bool \<times> SCTLR_EL1)"
  where
    "SCTLR_EL1_validate s value \<equiv>
      let
        ee = EE value;
        e0e = E0E value;
        res0 = ((B17RES0 value) = 0);
        result = (ee = False) \<and> (e0e = False) \<and> (res0 = True);
        value' = if
                  ((SPAN (SCTLR_EL1 (sys_regs_el1 (regs_state s))))
                  \<and> (SPAN value))
                 then
                   value \<lparr>SPAN := True\<rparr>
                 else
                   value \<lparr>SPAN := False\<rparr>
      in
        if result then (True, value') else (False, value)"

definition try_write_SCTLR_EL1 ::
    "State \<Rightarrow> SCTLR_EL1 \<Rightarrow> (State \<times> bool)"
  where
    "try_write_SCTLR_EL1 s value \<equiv>
      if fst (SCTLR_EL1_validate s value) then
        let
          value' = snd (SCTLR_EL1_validate s value);
          v_m = M value';
          m = M (SCTLR_EL1 (sys_regs_el1 (regs_state s)));
          v_wxn = WXN value';
          wxn = WXN (SCTLR_EL1 (sys_regs_el1 (regs_state s)));
          v_epan = EPAN value';
          epan = EPAN (SCTLR_EL1 (sys_regs_el1 (regs_state s)));
          v_ata = ATA value';
          ata = ATA (SCTLR_EL1 (sys_regs_el1 (regs_state s)));
          v_ata0 = ATA0 value';
          ata0 = ATA0 (SCTLR_EL1 (sys_regs_el1 (regs_state s)));
          v_tcf = (TCF value' \<noteq> TCF_NoEffect);
          tcf = (TCF (SCTLR_EL1 (sys_regs_el1 (regs_state s))) \<noteq> TCF_NoEffect);
          v_tcf0 = (TCF0 value' \<noteq> TCF_NoEffect);
          tcf0 = (TCF0 (SCTLR_EL1 (sys_regs_el1 (regs_state s))) \<noteq> TCF_NoEffect);
          s' = (write_SCTLR_EL1 s value')
        in
          if((m = True \<and> v_m = False) \<or>
             (wxn = True \<and> v_wxn = False) \<or>
             (epan = True \<and> v_epan = False) \<or>
             (ata = True \<and> v_ata = False) \<or>
             (ata0 = True \<and> v_ata0 = False) \<or>
             (tcf = True \<and> v_tcf = False) \<or>
             (tcf0 = True \<and> v_tcf0 = False))
          then
            (s, False)
          else
            (s', True)
      else
          (s, False)
        "

definition verify_cnp_bit ::
  "State \<Rightarrow> TTBRx_EL1 \<Rightarrow> bool"
  where
    "verify_cnp_bit s value \<equiv>
      if (TTBRx_EL1.CnP value) = False
      then True
      else
        let
          cnp = if (is_aarch64 s) then
            ((ID_AA64MMFR2_EL1.CnP (read_ID_AA64MMFR2_EL1 s)) = CnP_Supported)
            else True
        in
          if cnp = False then False else True"

definition ttbr_validate ::
  "State \<Rightarrow> TTBRx_EL1 \<Rightarrow> bool"
  where
    "ttbr_validate s value \<equiv>
      if \<not>(use_LPAE s) then True
      else
        let
          cnp_verify = verify_cnp_bit s value;
          align = and (BADDR value) 0x7ff
        in
          if (\<not>cnp_verify) \<or> (align \<noteq> 0) then False else True"

definition try_write_TTBR0_EL1 ::
  "State \<Rightarrow> TTBR0_EL1 \<Rightarrow> (State \<times> bool)"
  where
    "try_write_TTBR0_EL1 s value \<equiv>
      if ttbr_validate s value then
        let
          s' = (write_TTBR0_EL1 s value)
        in
          (s', True)
      else
        (s, False)"

definition abs_diff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "abs_diff a b = (if a \<le> b then b - a else a - b)"

lemma abs_diff_sym: "abs_diff w w' = abs_diff w' w"
  by (auto simp add: abs_diff_def)

definition pass_TTBR1_EL1 ::
  "TTBR1_EL1 \<Rightarrow> TTBR1_EL1 \<Rightarrow> bool"
  where
    "pass_TTBR1_EL1 value saved \<equiv>
      let
        val = unat (BADDR value) * 2 + (if TTBRx_EL1.CnP value then 1 else 0);
        sav = unat (BADDR saved) * 2 + (if TTBRx_EL1.CnP saved then 1 else 0);
        diff = abs_diff val sav
      in
        (diff \<le> 2 * 4096) \<and> ((diff mod 4096) = 0)"


definition try_write_TTBR1_EL1 ::
  "State \<Rightarrow> TTBR1_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_TTBR1_EL1 s value \<equiv>
    if (get_TTBR1_EL1_state s = LockDown) then
      case get_TTBR1_EL1_saved s of
        None \<Rightarrow> (s, False)
      | Some saved \<Rightarrow>
          if \<not> pass_TTBR1_EL1 value saved then (s, False)
          else (write_TTBR1_EL1 s value, True)
    else
      if ttbr_validate s value
      then
        let
          s' = set_TTBR1_EL1_saved s (Some value);
          s'' = set_TTBR1_EL1_state s' LockDown;
          s''' = write_TTBR1_EL1 s'' value
        in
          (s''', True)
      else
        (s, False)"

definition hpds_validate ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> bool"
  where
    "hpds_validate s value \<equiv>
      let
        hpds = if is_aarch64 s
                then (HPDS (read_ID_AA64MMFR1_EL1 s))
                else HPDS_None;
        h0 = HPD0 value;
        h1 = HPD1 value;
        hwu = (HWU162 value) \<or> (HWU161 value) \<or> (HWU160 value) \<or> (HWU159 value)
            \<or> (HWU062 value) \<or> (HWU061 value) \<or> (HWU060 value) \<or> (HWU059 value)
      in
        \<not>((hpds = HPDS_None) \<and> h0 = True) \<and>
        \<not>(h1 = True) \<and>
        \<not>((hwu = True) \<and> hpds \<noteq> HPDS_with_Alloc)"

definition mmfr0_validate ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> bool"
  where
    "mmfr0_validate s value \<equiv>
      let
        as = AS value;
        mmfr0 = read_ID_AA64MMFR0_EL1 s
      in
        if as = False then True
        else
          if (ASIDBits mmfr0) \<noteq> ASID_16bit then False else True"

definition mmfr1_validate ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> bool"
  where
    "mmfr1_validate s value \<equiv>
      let
        mmfr1 = read_ID_AA64MMFR1_EL1 s;
        hahd = (HA value) \<or> (HD value)
      in
        if (hahd = True) \<and> (HAFDBS mmfr1) = HAFDBS_None then
          False
        else
          True"

definition mmfr2_validate ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> bool"
  where
    "mmfr2_validate s value \<equiv>
      let
        e0pd = (E0PD1 value) \<or> (E0PD0 value);
        mmfr2 = read_ID_AA64MMFR2_EL1 s
      in
        if (e0pd = True) \<and> ((E0PD mmfr2) = E0PD_Unsupported) then False else True"

definition pfr1_validate ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> bool"
  where
    "pfr1_validate s value \<equiv>
      let
        tcma = (TCMA1 value) \<or> (TCMA0 value);
        pfr1 = read_ID_AA64PFR1_EL1 s
      in
        if (tcma = True) \<and> ((MTE pfr1) = MTE_None) then False else True"

definition TCR_EL1_validate ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> (bool \<times> TCR_EL1)"
  where
    "TCR_EL1_validate s value \<equiv>
      let hpds = (hpds_validate s value)
      in
        if \<not>(is_aarch64 s)
        then (False, value)
        else
          let
            res0_1 = (B6362RES0 value);
            res0_2 = (B35RES0 value);
            res0_3 = (B06RES0 value);
            res0 = (res0_1 \<noteq> 0) \<or> (res0_2 \<noteq> 0) \<or> (res0_3 \<noteq> 0);
            mmfr0 = mmfr0_validate s value;
            mmfr1 = mmfr1_validate s value;
            mmfr2 = mmfr2_validate s value;
            pfr1 = pfr1_validate s value;
            isar1 = read_ID_AA64ISAR1_EL1 s;
            tbid = (TBID1 value) \<or> (TBID0 value);
            value'' = value \<lparr> TBID1 := False, TBID0 := False \<rparr>
          in
            if (res0 = True) | \<not>mmfr0 | \<not>mmfr1 | \<not>mmfr2 | \<not>pfr1 | \<not>hpds
            then
              (False, value)
            else
              if tbid = True then
                if ((APA isar1 = \<lparr>address_auth = False, epac = False, pauth2 = False,
          fpac = False, fpac_combine = False, pauth_lr = False\<rparr> )\<and>
                    (API isar1 = \<lparr>address_auth = False, epac = False, pauth2 = False,
          fpac = False, fpac_combine = False, pauth_lr = False\<rparr>)) then
                  (True, value'')
                else
                  (True, value)
              else
                (True, value)"


definition try_write_TCR_EL1 ::
  "State \<Rightarrow> TCR_EL1 \<Rightarrow> (State \<times> bool)"
  where
    "try_write_TCR_EL1 s value \<equiv>
      if (get_TCR_EL1_state s = LockDown) then
        (s, False)
      else
        let
          result = TCR_EL1_validate s value;
          value' = snd result;
          pass = fst result;
          s' = set_TCR_EL1_state s LockDown;
          s'' = (write_TCR_EL1 s' value')
        in
          if pass then (s'', True) else (s, False)"

definition try_write_ESR_EL1 ::
  "State \<Rightarrow> ESR_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_ESR_EL1 s value \<equiv>
    let
      s' = (write_ESR_EL1 s value)
    in
      (s', True)"

definition try_write_FAR_EL1 ::
  "State \<Rightarrow> FAR_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_FAR_EL1 s value \<equiv>
    let
      s' = (write_FAR_EL1 s value)
    in
      (s', True)"

definition try_write_AFSR0_EL1 ::
  "State \<Rightarrow> AFSR0_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_AFSR0_EL1 s value \<equiv> (s, False)"

definition try_write_AFSR1_EL1 ::
  "State \<Rightarrow> AFSR1_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_AFSR1_EL1 s value \<equiv> (s, False)"

definition try_write_MAIR_EL1 ::
  "State \<Rightarrow> MAIR_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_MAIR_EL1 s value \<equiv>
    if (get_MAIR_EL1_state s = LockDown) then
      (s, False)
    else
      let
        s' = set_MAIR_EL1_state s LockDown;
        s'' = (write_MAIR_EL1 s' value)
      in
        (s'', True)"

definition try_write_AMAIR_EL1 ::
  "State \<Rightarrow> AMAIR_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_AMAIR_EL1 s value \<equiv> (s, False)"

definition try_write_CONTEXTIDR_EL1 ::
  "State \<Rightarrow> CONTEXTIDR_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_CONTEXTIDR_EL1 s value \<equiv>
    let
      s' = (write_CONTEXTIDR_EL1 s value)
    in
      (s', True)"

definition try_write_ACTLR_EL1 ::
  "State \<Rightarrow> ACTLR_EL1 \<Rightarrow> (State \<times> bool)"
  where "try_write_ACTLR_EL1 s value \<equiv> (s, False)"

definition try_write_sys_reg ::
  "State \<Rightarrow> Reg_Syndrome \<Rightarrow> Reg_Value \<Rightarrow> (State \<times> bool)"
  where "try_write_sys_reg s syndrome value \<equiv>
    case syndrome of
      SCTLR_EL1_Syndrome \<Rightarrow> (try_write_SCTLR_EL1 s (word64_to_sctlr_el1 value)) |
      TTBR0_EL1_Syndrome \<Rightarrow> (try_write_TTBR0_EL1 s (word64_to_ttbr0_el1 value)) |
      TTBR1_EL1_Syndrome \<Rightarrow> (try_write_TTBR1_EL1 s (word64_to_ttbr1_el1 value)) |
      TCR_EL1_Syndrome \<Rightarrow> (try_write_TCR_EL1 s (word64_to_tcr_el1 value)) |
      ESR_EL1_Syndrome \<Rightarrow> (try_write_ESR_EL1 s (word64_to_esr_el1 value)) |
      FAR_EL1_Syndrome \<Rightarrow> (try_write_FAR_EL1 s (word64_to_far_el1 value)) |
      AFSR0_EL1_Syndrome \<Rightarrow> (try_write_AFSR0_EL1 s (word64_to_afsr0_el1 value)) |
      AFSR1_EL1_Syndrome \<Rightarrow> (try_write_AFSR1_EL1 s (word64_to_afsr1_el1 value)) |
      MAIR_EL1_Syndrome \<Rightarrow> (try_write_MAIR_EL1 s (word64_to_mair_el1 value)) |
      AMAIR_EL1_Syndrome \<Rightarrow> (try_write_AMAIR_EL1 s (word64_to_amair_el1 value)) |
      CONTEXTIDR_EL1_Syndrome \<Rightarrow> (try_write_CONTEXTIDR_EL1 s (word64_to_contextidr_el1 value)) |
      ACTLR_EL1_Syndrome \<Rightarrow> (try_write_ACTLR_EL1 s (word64_to_actlr_el1 value)) |
      _ \<Rightarrow> (s, False)"


section \<open> Events: Read System Register Event \<close>

definition try_read_ACTLR_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where "try_read_ACTLR_EL1 s \<equiv> (s, 0)"

definition try_read_sys_reg ::
  "State \<Rightarrow> Reg_Syndrome \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_sys_reg s syndrome \<equiv>
      case syndrome of
        ACTLR_EL1_Syndrome \<Rightarrow> (try_read_ACTLR_EL1 s) |
        _ \<Rightarrow> (s, -1)"

section \<open> Events: Read Identifier Register Event \<close>

definition try_read_ID_AA64PFR0_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64PFR0_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64PFR1_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64PFR1_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64ZFR0_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64ZFR0_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64DFR0_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64DFR0_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64DFR1_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64DFR1_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64AFR0_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64AFR0_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64AFR1_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64AFR1_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64ISAR0_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64ISAR0_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64ISAR1_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64ISAR1_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64ISAR2_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64ISAR2_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64MMFR0_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64MMFR0_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64MMFR1_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64MMFR1_EL1 s \<equiv>
      (s, 0)"

definition try_read_ID_AA64MMFR2_EL1 ::
  "State \<Rightarrow> (State \<times> Reg_Value)"
  where
    "try_read_ID_AA64MMFR2_EL1 s \<equiv>
      (s, 0)"

definition read_id_reg ::
  "State \<Rightarrow> Reg_Syndrome \<Rightarrow> (State \<times> Reg_Value)"
  where
    "read_id_reg s syndrome \<equiv> (s, 0)"



end
