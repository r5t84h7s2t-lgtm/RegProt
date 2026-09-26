theory PAN_Protection
  imports
    "../system/RegProt_Model"
begin

text \<open>
  \<^bold>\<open>Scope.\<close>
  This theory proves configuration-level protection for the PAN controls
  modeled in SCTLR_EL1. A protected configuration has SPAN cleared, so
  exception entry sets PSTATE.PAN, and EPAN enabled. The proofs show that no
  RegProt trace can set an already-cleared SPAN bit or clear an already-enabled
  EPAN bit.

  The model does not include PSTATE.PAN, exception-entry semantics, memory
  accesses, or refinement to the Rust implementation. Consequently, these
  results rule out the register-state transitions required by the modeled PAN
  disable attack; they are not an end-to-end proof of PAN enforcement by the
  processor or compiled handler.
\<close>


section \<open>PAN control ordering\<close>

definition pan_reg_leq :: "SCTLR_EL1 \<Rightarrow> SCTLR_EL1 \<Rightarrow> bool" where
  "pan_reg_leq v v' \<equiv>
     (\<not> SPAN v \<longrightarrow> \<not> SPAN v') \<and>
     (EPAN v \<longrightarrow> EPAN v')"

definition pan_protected :: "SCTLR_EL1 \<Rightarrow> bool" where
  "pan_protected v \<equiv> \<not> SPAN v \<and> EPAN v"

lemma pan_reg_leq_refl [simp]: "pan_reg_leq v v"
  by (simp add: pan_reg_leq_def)

lemma pan_reg_leq_trans:
  "\<lbrakk> pan_reg_leq v1 v2; pan_reg_leq v2 v3 \<rbrakk>
   \<Longrightarrow> pan_reg_leq v1 v3"
  by (auto simp add: pan_reg_leq_def)


section \<open>Direct attack transitions\<close>

lemma span_handler_preserves_disabled:
  assumes disabled: "\<not> SPAN (read_SCTLR_EL1 s)"
  shows "\<not> SPAN (read_SCTLR_EL1 (fst (try_write_SCTLR_EL1 s v)))"
  using disabled
  by (auto simp add: try_write_SCTLR_EL1_def SCTLR_EL1_validate_def
                     read_SCTLR_EL1_def write_SCTLR_EL1_def Let_def
           split: if_splits)

theorem span_enable_attack_neutralized:
  assumes disabled: "\<not> SPAN (read_SCTLR_EL1 s)"
      and attack: "SPAN v"
  shows "\<not> SPAN (read_SCTLR_EL1 (fst (try_write_SCTLR_EL1 s v)))"
  using span_handler_preserves_disabled [OF disabled, of v] .

theorem epan_disable_attack_rejected:
  assumes enabled: "EPAN (read_SCTLR_EL1 s)"
      and downgrade: "\<not> EPAN v"
  shows "try_write_SCTLR_EL1 s v = (s, False)"
  using enabled downgrade
  by (auto simp add: try_write_SCTLR_EL1_def SCTLR_EL1_validate_def
                     read_SCTLR_EL1_def Let_def
           split: if_splits)

lemma epan_handler_preserved:
  assumes enabled: "EPAN (read_SCTLR_EL1 s)"
  shows "EPAN (read_SCTLR_EL1 (fst (try_write_SCTLR_EL1 s v)))"
proof -
  from sctlr_EPAN_ratchet [OF enabled, of v]
  have "EPAN (read_SCTLR_EL1 (SCTLR.try_write_ad_hoc_modify v s))" .
  then show ?thesis
    by (simp add: sctlr_legacy_state_matches)
qed

theorem sctlr_handler_pan_monotone:
  "pan_reg_leq (read_SCTLR_EL1 s)
               (read_SCTLR_EL1 (fst (try_write_SCTLR_EL1 s v)))"
  using span_handler_preserves_disabled [of s v]
        epan_handler_preserved [of s v]
  by (auto simp add: pan_reg_leq_def)


section \<open>System-step preservation\<close>

theorem pan_step_monotone:
  assumes step: "(s, s') \<in> regprot_step e"
  shows "pan_reg_leq (read_SCTLR_EL1 s) (read_SCTLR_EL1 s')"
proof (cases e)
  case (WRITE_SYSREG synd val)
  with step have state:
    "s' = fst (try_write_sys_reg s synd val)"
    by (auto simp add: regprot_step_def)
  show ?thesis
  proof (cases "synd = SCTLR_EL1_Syndrome")
    case True
    with state show ?thesis
      by (simp add: try_write_sys_reg_def sctlr_handler_pan_monotone)
  next
    case False
    from try_write_sys_reg_sctlr_unchanged [OF False, of s val]
    show ?thesis
      by (simp add: state)
  qed
next
  case (READ_SYSREG synd)
  with step show ?thesis
    by (simp add: regprot_step_def)
next
  case (READ_IDREG synd)
  with step show ?thesis
    by (simp add: regprot_step_def)
qed

theorem pan_step_preserves_protection:
  assumes step: "(s, s') \<in> regprot_step e"
      and established: "pan_protected (read_SCTLR_EL1 s)"
  shows "pan_protected (read_SCTLR_EL1 s')"
  using pan_step_monotone [OF step] established
  by (auto simp add: pan_reg_leq_def pan_protected_def)


section \<open>Trace-level preservation\<close>

theorem pan_run_monotone:
  assumes run: "(s, s') \<in> RegProt.run events"
  shows "pan_reg_leq (read_SCTLR_EL1 s) (read_SCTLR_EL1 s')"
  using run
proof (induction events arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e events)
  then obtain t where step: "(s, t) \<in> regprot_step e"
    and tail: "(t, s') \<in> RegProt.run events"
    by auto
  from pan_step_monotone [OF step]
  have first:
    "pan_reg_leq (read_SCTLR_EL1 s) (read_SCTLR_EL1 t)" .
  from Cons.IH [OF tail]
  have rest:
    "pan_reg_leq (read_SCTLR_EL1 t) (read_SCTLR_EL1 s')" .
  from pan_reg_leq_trans [OF first rest]
  show ?case .
qed

theorem pan_run_preserves_protection:
  assumes run: "(s, s') \<in> RegProt.run events"
      and established: "pan_protected (read_SCTLR_EL1 s)"
  shows "pan_protected (read_SCTLR_EL1 s')"
  using pan_run_monotone [OF run] established
  by (auto simp add: pan_reg_leq_def pan_protected_def)

theorem pan_trace_monotone:
  assumes reach: "RegProt.reachable s s'"
  shows "pan_reg_leq (read_SCTLR_EL1 s) (read_SCTLR_EL1 s')"
proof -
  from reach obtain events where "(s, s') \<in> RegProt.run events"
    unfolding RegProt.reachable_def by blast
  from pan_run_monotone [OF this]
  show ?thesis .
qed

theorem pan_trace_preserves_protection:
  assumes reach: "RegProt.reachable s s'"
      and established: "pan_protected (read_SCTLR_EL1 s)"
  shows "pan_protected (read_SCTLR_EL1 s')"
  using pan_trace_monotone [OF reach] established
  by (auto simp add: pan_reg_leq_def pan_protected_def)

corollary span_trace_preserves_disabled:
  assumes reach: "RegProt.reachable s s'"
      and disabled: "\<not> SPAN (read_SCTLR_EL1 s)"
  shows "\<not> SPAN (read_SCTLR_EL1 s')"
  using pan_trace_monotone [OF reach] disabled
  by (auto simp add: pan_reg_leq_def)

corollary epan_trace_preserves_enabled:
  assumes reach: "RegProt.reachable s s'"
      and enabled: "EPAN (read_SCTLR_EL1 s)"
  shows "EPAN (read_SCTLR_EL1 s')"
  using pan_trace_monotone [OF reach] enabled
  by (auto simp add: pan_reg_leq_def)

end
