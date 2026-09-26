theory SCTLR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>SCTLR_EL1 interpretation.\<close>
  Protection pattern: \<^emph>\<open>stateless value lattice\<close>.
  Unlike TTBR1/TCR/MAIR, SCTLR_EL1 has \<^emph>\<open>no lock state\<close>
  (no corresponding field in @{typ Protected_Reg_State}).
  Every write goes through:

  \<^enum> \<^bold>\<open>Structural validation\<close> (@{const SCTLR_EL1_validate}): EE = @{term False},
    E0E = @{term False}, B17RES0 = 0; plus SPAN-bit correction
    (new SPAN := old SPAN @{text "\<and>"} requested SPAN).
  \<^enum> \<^bold>\<open>Monotonicity ratchet\<close>: M, WXN, EPAN, ATA, and ATA0 may
    only go \<^emph>\<open>up\<close>; TCF and TCF0 may not return to
    @{const TCF_NoEffect} after fault reporting has been enabled.

  Locale used: @{locale AdHocModify}. This mirrors the hand-written Isabelle
  handler: SCTLR_EL1 has a direct write path and never participates in the
  saved-value mechanism used by post-boot locked registers. Correspondence to
  the Rust handler is outside this theory's proof boundary.
\<close>


section \<open>Step 1 \<^bold>\<open>Glue accessors for SCTLR_EL1\<close>\<close>

definition get_sctlr :: "State \<Rightarrow> SCTLR_EL1" where
  "get_sctlr s = read_SCTLR_EL1 s"

definition set_sctlr :: "SCTLR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_sctlr v s = write_SCTLR_EL1 s v"

lemma get_sctlr_set_sctlr [simp]:
  "get_sctlr (set_sctlr v s) = v"
  by (simp add: get_sctlr_def set_sctlr_def read_SCTLR_EL1_def write_SCTLR_EL1_def)

lemma set_sctlr_get_sctlr [simp]:
  "set_sctlr (get_sctlr s) s = s"
  by (simp add: get_sctlr_def set_sctlr_def read_SCTLR_EL1_def write_SCTLR_EL1_def)

lemma set_sctlr_set_sctlr [simp]:
  "set_sctlr v\<^sub>2 (set_sctlr v\<^sub>1 s) = set_sctlr v\<^sub>2 s"
  by (simp add: set_sctlr_def write_SCTLR_EL1_def)


section \<open>Step 2 \<^bold>\<open>Value lattice and locale glue\<close>\<close>

definition tcf_reports_fault :: "tcf_mode \<Rightarrow> bool" where
  "tcf_reports_fault mode \<equiv> (mode \<noteq> TCF_NoEffect)"

definition sctlr_mte_protected :: "SCTLR_EL1 \<Rightarrow> bool" where
  "sctlr_mte_protected v \<equiv>
     ATA v \<and> ATA0 v \<and>
     tcf_reports_fault (TCF v) \<and> tcf_reports_fault (TCF0 v)"

text \<open>
  The security ordering protects three general hardening bits and four
  SCTLR-mediated MTE controls. TCF modes are deliberately reduced to the
  security-relevant predicate "reports faults": switching between synchronous
  and asynchronous reporting is allowed, but returning to no-effect is not.
\<close>
definition sctlr_reg_leq :: "SCTLR_EL1 \<Rightarrow> SCTLR_EL1 \<Rightarrow> bool" where
  "sctlr_reg_leq v v' \<equiv>
     (M v \<longrightarrow> M v') \<and>
     (WXN v \<longrightarrow> WXN v') \<and>
     (EPAN v \<longrightarrow> EPAN v') \<and>
     (ATA v \<longrightarrow> ATA v') \<and>
     (ATA0 v \<longrightarrow> ATA0 v') \<and>
     (tcf_reports_fault (TCF v) \<longrightarrow> tcf_reports_fault (TCF v')) \<and>
     (tcf_reports_fault (TCF0 v) \<longrightarrow> tcf_reports_fault (TCF0 v'))"

text \<open>
  @{text sctlr_validate} combines structural validation with the monotone check.
  Returns @{term "Some v'"} (corrected value) iff both pass; @{term None} otherwise.
\<close>
definition sctlr_validate :: "SCTLR_EL1 \<Rightarrow> State \<Rightarrow> SCTLR_EL1 option" where
  "sctlr_validate v s \<equiv>
     let (ok, v') = SCTLR_EL1_validate s v;
         curr     = read_SCTLR_EL1 s
     in
       if ok \<and>
          (M curr \<longrightarrow> M v') \<and>
          (WXN curr \<longrightarrow> WXN v') \<and>
          (EPAN curr \<longrightarrow> EPAN v') \<and>
          (ATA curr \<longrightarrow> ATA v') \<and>
          (ATA0 curr \<longrightarrow> ATA0 v') \<and>
          (tcf_reports_fault (TCF curr) \<longrightarrow> tcf_reports_fault (TCF v')) \<and>
          (tcf_reports_fault (TCF0 curr) \<longrightarrow> tcf_reports_fault (TCF0 v'))
       then Some v'
       else None"

text \<open>
  Key lemma: a validated result dominates the old value in @{text sctlr_reg_leq}.
  Follows directly from the monotone condition in @{const sctlr_validate}.
\<close>
lemma sctlr_validate_mono:
  "sctlr_validate v s = Some v' \<Longrightarrow> sctlr_reg_leq (get_sctlr s) v'"
  apply (simp add: sctlr_validate_def sctlr_reg_leq_def get_sctlr_def
                     split: if_splits prod.splits)
  by (smt (verit, best) not_None_eq option.sel)


section \<open>Step 3 \<^bold>\<open>The interpretation\<close>\<close>

text \<open>
  We interpret @{locale AdHocModify} because SCTLR has no lock state and
  its handler performs only structural validation plus monotone checks.

  Proof obligations:
  \<^item> RegisterAccess (3): standard record round-trips.
  \<^item> @{text reg_leq_refl}: trivial from definition.
  \<^item> @{text reg_leq_trans}: propositional transitivity of implication.
  \<^item> @{text validate_mono}: @{thm sctlr_validate_mono}.
\<close>

interpretation SCTLR: AdHocModify
  get_sctlr set_sctlr
  sctlr_validate sctlr_reg_leq
proof unfold_locales
  
  fix v s show "get_sctlr (set_sctlr v s) = v"
    by (simp add: get_sctlr_def set_sctlr_def read_SCTLR_EL1_def write_SCTLR_EL1_def)
next
  fix s show "set_sctlr (get_sctlr s) s = s"
    by (simp add: get_sctlr_def set_sctlr_def read_SCTLR_EL1_def write_SCTLR_EL1_def)
next
  fix v\<^sub>1 v\<^sub>2 s show "set_sctlr v\<^sub>2 (set_sctlr v\<^sub>1 s) = set_sctlr v\<^sub>2 s"
    by (simp add: set_sctlr_def write_SCTLR_EL1_def)
next
  
  fix v show "sctlr_reg_leq v v"
    by (simp add: sctlr_reg_leq_def)
next
  
  fix v\<^sub>1 v\<^sub>2 v\<^sub>3
  assume "sctlr_reg_leq v\<^sub>1 v\<^sub>2" "sctlr_reg_leq v\<^sub>2 v\<^sub>3"
  thus "sctlr_reg_leq v\<^sub>1 v\<^sub>3"
    by (auto simp add: sctlr_reg_leq_def)
next
  
  fix v v' s assume "sctlr_validate v s = Some v'"
  thus "sctlr_reg_leq (get_sctlr s) v'"
    by (rule sctlr_validate_mono)
qed

text \<open>Key inherited theorems:\<close>
thm SCTLR.try_write_ad_hoc_modify_reg_leq
thm SCTLR.try_write_ad_hoc_modify_preserves


section \<open>Step 4 \<^bold>\<open>Equivalence with the legacy @{const try_write_SCTLR_EL1}\<close>\<close>

text \<open>
  Helper: decompose @{const sctlr_validate} into its components.
\<close>
lemma sctlr_validate_Some_iff:
  "sctlr_validate v s = Some v' \<longleftrightarrow>
     fst (SCTLR_EL1_validate s v) \<and>
     v' = snd (SCTLR_EL1_validate s v) \<and>
     (M (read_SCTLR_EL1 s) \<longrightarrow> M v') \<and>
     (WXN (read_SCTLR_EL1 s) \<longrightarrow> WXN v') \<and>
     (EPAN (read_SCTLR_EL1 s) \<longrightarrow> EPAN v') \<and>
     (ATA (read_SCTLR_EL1 s) \<longrightarrow> ATA v') \<and>
     (ATA0 (read_SCTLR_EL1 s) \<longrightarrow> ATA0 v') \<and>
     (tcf_reports_fault (TCF (read_SCTLR_EL1 s)) \<longrightarrow> tcf_reports_fault (TCF v')) \<and>
     (tcf_reports_fault (TCF0 (read_SCTLR_EL1 s)) \<longrightarrow> tcf_reports_fault (TCF0 v'))"
  apply (simp add: sctlr_validate_def split: if_splits prod.splits)
  by (smt (verit) not_Some_eq option.sel)

lemma sctlr_validate_None_iff:
  "sctlr_validate v s = None \<longleftrightarrow>
     \<not> (fst (SCTLR_EL1_validate s v) \<and>
         (M (read_SCTLR_EL1 s) \<longrightarrow> M (snd (SCTLR_EL1_validate s v))) \<and>
         (WXN (read_SCTLR_EL1 s) \<longrightarrow> WXN (snd (SCTLR_EL1_validate s v))) \<and>
         (EPAN (read_SCTLR_EL1 s) \<longrightarrow> EPAN (snd (SCTLR_EL1_validate s v))) \<and>
         (ATA (read_SCTLR_EL1 s) \<longrightarrow> ATA (snd (SCTLR_EL1_validate s v))) \<and>
         (ATA0 (read_SCTLR_EL1 s) \<longrightarrow> ATA0 (snd (SCTLR_EL1_validate s v))) \<and>
         (tcf_reports_fault (TCF (read_SCTLR_EL1 s)) \<longrightarrow>
            tcf_reports_fault (TCF (snd (SCTLR_EL1_validate s v)))) \<and>
         (tcf_reports_fault (TCF0 (read_SCTLR_EL1 s)) \<longrightarrow>
            tcf_reports_fault (TCF0 (snd (SCTLR_EL1_validate s v)))))"
  by (auto simp add: sctlr_validate_def split: if_splits prod.splits)

lemma sctlr_legacy_state_matches:
  "fst (try_write_SCTLR_EL1 s v) = SCTLR.try_write_ad_hoc_modify v s"
proof -
  show ?thesis
  proof (cases "sctlr_validate v s")
    case (Some v')
    
    have rhs: "SCTLR.try_write_ad_hoc_modify v s = set_sctlr v' s"
      using SCTLR.try_write_ad_hoc_modify_accepted [OF Some] by blast
    from Some [unfolded sctlr_validate_Some_iff]
    have val_ok : "fst (SCTLR_EL1_validate s v)"
      and v'_def: "v' = snd (SCTLR_EL1_validate s v)"
      and mono_m : "M (read_SCTLR_EL1 s) \<longrightarrow> M v'"
      and mono_w : "WXN (read_SCTLR_EL1 s) \<longrightarrow> WXN v'"
      and mono_e : "EPAN (read_SCTLR_EL1 s) \<longrightarrow> EPAN v'"
      and mono_a : "ATA (read_SCTLR_EL1 s) \<longrightarrow> ATA v'"
      and mono_a0: "ATA0 (read_SCTLR_EL1 s) \<longrightarrow> ATA0 v'"
      and mono_t : "tcf_reports_fault (TCF (read_SCTLR_EL1 s)) \<longrightarrow> tcf_reports_fault (TCF v')"
      and mono_t0: "tcf_reports_fault (TCF0 (read_SCTLR_EL1 s)) \<longrightarrow> tcf_reports_fault (TCF0 v')"
      by blast+
    have lhs: "fst (try_write_SCTLR_EL1 s v) = write_SCTLR_EL1 s v'"
      using val_ok mono_m mono_w mono_e mono_a mono_a0 mono_t mono_t0
      apply (simp add: try_write_SCTLR_EL1_def Let_def v'_def
                       read_SCTLR_EL1_def tcf_reports_fault_def)
    by blast
    show ?thesis
      by (simp add: lhs rhs set_sctlr_def)
  next
    case None
    
    have rhs: "SCTLR.try_write_ad_hoc_modify v s = s"
      using SCTLR.try_write_ad_hoc_modify_rejected [OF None] by blast
    from None [unfolded sctlr_validate_None_iff]
    have reject: "\<not> (fst (SCTLR_EL1_validate s v) \<and>
                     (M (read_SCTLR_EL1 s) \<longrightarrow> M (snd (SCTLR_EL1_validate s v))) \<and>
                     (WXN (read_SCTLR_EL1 s) \<longrightarrow> WXN (snd (SCTLR_EL1_validate s v))) \<and>
                     (EPAN (read_SCTLR_EL1 s) \<longrightarrow> EPAN (snd (SCTLR_EL1_validate s v))) \<and>
                     (ATA (read_SCTLR_EL1 s) \<longrightarrow> ATA (snd (SCTLR_EL1_validate s v))) \<and>
                     (ATA0 (read_SCTLR_EL1 s) \<longrightarrow> ATA0 (snd (SCTLR_EL1_validate s v))) \<and>
                     (tcf_reports_fault (TCF (read_SCTLR_EL1 s)) \<longrightarrow>
                        tcf_reports_fault (TCF (snd (SCTLR_EL1_validate s v)))) \<and>
                     (tcf_reports_fault (TCF0 (read_SCTLR_EL1 s)) \<longrightarrow>
                        tcf_reports_fault (TCF0 (snd (SCTLR_EL1_validate s v)))))"
      by simp
    have lhs: "fst (try_write_SCTLR_EL1 s v) = s"
      using reject
      by (auto simp add: try_write_SCTLR_EL1_def Let_def read_SCTLR_EL1_def
                         tcf_reports_fault_def
               split: if_splits)
    show ?thesis by (simp add: lhs rhs)
  qed
qed


section \<open>Step 5 \<^bold>\<open>Security and MTE monotonicity theorems\<close>\<close>

text \<open>
  The core Security Model guarantee for SCTLR: every permitted write preserves or
  strengthens the security posture. This is an instance of the locale theorem
  @{thm SCTLR.try_write_ad_hoc_modify_reg_leq}, specialised to the concrete ordering.
\<close>

theorem sctlr_security_monotone:
  "sctlr_reg_leq (get_sctlr s) (get_sctlr (SCTLR.try_write_ad_hoc_modify v s))"
  using SCTLR.try_write_ad_hoc_modify_reg_leq .

text \<open>Corollaries: each individual hardening bit is a ratchet.\<close>

corollary sctlr_M_ratchet:
  "M (read_SCTLR_EL1 s) \<Longrightarrow> M (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

corollary sctlr_WXN_ratchet:
  "WXN (read_SCTLR_EL1 s) \<Longrightarrow> WXN (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

corollary sctlr_EPAN_ratchet:
  "EPAN (read_SCTLR_EL1 s) \<Longrightarrow> EPAN (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

corollary sctlr_ATA_ratchet:
  "ATA (read_SCTLR_EL1 s) \<Longrightarrow> ATA (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

corollary sctlr_ATA0_ratchet:
  "ATA0 (read_SCTLR_EL1 s) \<Longrightarrow> ATA0 (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

corollary sctlr_TCF_ratchet:
  "tcf_reports_fault (TCF (read_SCTLR_EL1 s)) \<Longrightarrow>
   tcf_reports_fault (TCF (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s)))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

corollary sctlr_TCF0_ratchet:
  "tcf_reports_fault (TCF0 (read_SCTLR_EL1 s)) \<Longrightarrow>
   tcf_reports_fault (TCF0 (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s)))"
  using sctlr_security_monotone
  by (simp add: sctlr_reg_leq_def get_sctlr_def)

theorem sctlr_mte_protection_preserved:
  assumes "sctlr_mte_protected (read_SCTLR_EL1 s)"
  shows "sctlr_mte_protected
           (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))"
  using sctlr_security_monotone assms
  by (auto simp add: sctlr_reg_leq_def sctlr_mte_protected_def
                     tcf_reports_fault_def get_sctlr_def)

corollary sctlr_handler_mte_protection_preserved:
  assumes "sctlr_mte_protected (read_SCTLR_EL1 s)"
  shows "sctlr_mte_protected
           (read_SCTLR_EL1 (fst (try_write_SCTLR_EL1 s v)))"
  using sctlr_mte_protection_preserved [OF assms, of v]
  by (simp add: sctlr_legacy_state_matches)

lemma sctlr_mte_downgrade_validate_none:
  assumes old: "sctlr_mte_protected (read_SCTLR_EL1 s)"
      and requested: "\<not> sctlr_mte_protected v"
  shows "sctlr_validate v s = None"
  using assms
  by (auto simp add: sctlr_validate_None_iff sctlr_mte_protected_def
                     tcf_reports_fault_def SCTLR_EL1_validate_def Let_def
           split: if_splits)

theorem sctlr_mte_downgrade_rejected:
  assumes old: "sctlr_mte_protected (read_SCTLR_EL1 s)"
      and requested: "\<not> sctlr_mte_protected v"
  shows "try_write_SCTLR_EL1 s v = (s, False)"
  using assms
  by (auto simp add: try_write_SCTLR_EL1_def SCTLR_EL1_validate_def
                     sctlr_mte_protected_def tcf_reports_fault_def
                     read_SCTLR_EL1_def Let_def
           split: if_splits)

text \<open>
  Generic state-predicate preservation: preserving an arbitrary invariant @{text P}
  requires only the @{text validate} branch.
\<close>
lemma sctlr_preserves:
  assumes inv_accept:
    "\<And>v v' s. sctlr_validate v s = Some v' \<Longrightarrow> P s \<Longrightarrow> P (set_sctlr v' s)"
  and "P s"
  shows "P (SCTLR.try_write_ad_hoc_modify v s)"
proof (rule SCTLR.try_write_ad_hoc_modify_preserves)
  fix w w' s' assume "sctlr_validate w s' = Some w'" "P s'"
  thus "P (set_sctlr w' s')"
  using inv_accept by blast
next
  show "P s" by fact
qed

end
