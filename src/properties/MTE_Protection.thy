theory MTE_Protection
  imports
    "../system/RegProt_Model"
begin

text \<open>
  \<^bold>\<open>Scope.\<close>
  This theory proves configuration-level protection for the MTE controls
  modeled by RegProt. It covers the SCTLR_EL1 allocation-tag access bits and
  tag-check fault modes, together with the TCR_EL1 TCMA capability check. It
  does not model allocation tags in memory, tagged loads and stores, exception
  delivery, or refinement to the Rust implementation.

  The initial model state advertises @{const MTE_None} and initializes SCTLR to
  zero. Consequently the trace theorem is intentionally relative to an
  arbitrary state in which SCTLR MTE protection has already been established;
  it does not claim that @{const regprot_s0} enables MTE.
\<close>


section \<open>Direct SCTLR downgrade rejection\<close>

theorem mte_disable_attack_rejected:
  assumes established: "sctlr_mte_protected (read_SCTLR_EL1 s)"
      and downgrade: "\<not> sctlr_mte_protected v"
  shows "try_write_SCTLR_EL1 s v = (s, False)"
  using sctlr_mte_downgrade_rejected [OF established downgrade] .


section \<open>System-step preservation\<close>

theorem mte_step_preserves_protection:
  assumes step: "(s, s') \<in> regprot_step e"
      and established: "sctlr_mte_protected (read_SCTLR_EL1 s)"
  shows "sctlr_mte_protected (read_SCTLR_EL1 s')"
proof -
  from RegProt.step_preserves_mono [OF step]
  have "s \<sqsubseteq>\<^sub>R s'" .
  with established show ?thesis
    by (auto simp add: global_sec_leq_def sctlr_reg_leq_def
                       sctlr_mte_protected_def tcf_reports_fault_def
                       get_sctlr_def)
qed


section \<open>Trace-level preservation\<close>

theorem mte_run_preserves_protection:
  assumes run: "(s, s') \<in> RegProt.run events"
      and established: "sctlr_mte_protected (read_SCTLR_EL1 s)"
  shows "sctlr_mte_protected (read_SCTLR_EL1 s')"
proof -
  from RegProt.run_preserves_mono [OF run]
  have "s \<sqsubseteq>\<^sub>R s'" .
  with established show ?thesis
    by (auto simp add: global_sec_leq_def sctlr_reg_leq_def
                       sctlr_mte_protected_def tcf_reports_fault_def
                       get_sctlr_def)
qed

theorem mte_trace_preserves_protection:
  assumes reach: "RegProt.reachable s s'"
      and established: "sctlr_mte_protected (read_SCTLR_EL1 s)"
  shows "sctlr_mte_protected (read_SCTLR_EL1 s')"
proof -
  from reach obtain events where "(s, s') \<in> RegProt.run events"
    unfolding RegProt.reachable_def by blast
  from mte_run_preserves_protection [OF this established]
  show ?thesis .
qed


section \<open>TCR capability consistency in reachable states\<close>

theorem mte_reachable_tcr_capability_consistent:
  assumes "RegProt.reachable0 s"
  shows "tcr_mte_consistent s"
proof -
  from RegProt.SM_security_integrity assms
  have "regprot_wf s \<and> regprot_cons s"
    unfolding RegProt.SM_integrity_def by blast
  then show ?thesis
    by (simp add: regprot_cons_def)
qed

end
