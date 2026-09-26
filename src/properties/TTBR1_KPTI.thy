theory TTBR1_KPTI
  imports
    "../system/RegProt_Model"
begin

text \<open>
  This theory states the paper-facing KPTI guarantee for TTBR1_EL1. Lockdown
  captures one fixed trusted reference. Later writes may select the kernel page
  table or the nearby KPTI trampoline accepted by @{const pass_TTBR1_EL1}, but
  neither TTBR1 writes nor unrelated events may replace the saved reference.
\<close>


section \<open>Single-step fixed-reference preservation\<close>

theorem ttbr1_step_preserves_locked_reference:
  assumes step: "(s, s') \<in> regprot_step e"
      and locked: "ttbr1_is_locked s"
  shows "ttbr1_is_locked s' \<and>
         get_TTBR1_EL1_saved s' = get_TTBR1_EL1_saved s"
proof (cases e)
  case (WRITE_SYSREG synd val)
  with step have eq: "s' = fst (try_write_sys_reg s synd val)"
    by (auto simp add: regprot_step_def)
  from try_write_sys_reg_ttbr1_locked_reference [OF locked, of synd val]
  show ?thesis by (simp add: eq)
next
  case (READ_SYSREG synd)
  with step show ?thesis using locked
    by (simp add: regprot_step_def)
next
  case (READ_IDREG synd)
  with step show ?thesis using locked
    by (simp add: regprot_step_def)
qed


section \<open>Trace-level fixed-reference preservation\<close>

theorem ttbr1_run_preserves_locked_reference:
  assumes run: "(s, s') \<in> RegProt.run events"
      and locked: "ttbr1_is_locked s"
  shows "ttbr1_is_locked s' \<and>
         get_TTBR1_EL1_saved s' = get_TTBR1_EL1_saved s"
  using run locked
proof (induction events arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons e events)
  then obtain t where step: "(s, t) \<in> regprot_step e"
    and tail: "(t, s') \<in> RegProt.run events"
    by auto
  from ttbr1_step_preserves_locked_reference [OF step Cons.prems(2)]
  have t_locked: "ttbr1_is_locked t"
    and t_saved: "get_TTBR1_EL1_saved t = get_TTBR1_EL1_saved s"
    by auto
  from Cons.IH [OF tail t_locked]
  show ?case using t_saved by auto
qed

theorem ttbr1_trace_preserves_locked_reference:
  assumes reach: "RegProt.reachable s s'"
      and locked: "ttbr1_is_locked s"
  shows "ttbr1_is_locked s' \<and>
         get_TTBR1_EL1_saved s' = get_TTBR1_EL1_saved s"
proof -
  from reach obtain events where "(s, s') \<in> RegProt.run events"
    unfolding RegProt.reachable_def by blast
  from ttbr1_run_preserves_locked_reference [OF this locked]
  show ?thesis .
qed


section \<open>Reachable-state KPTI consistency\<close>

theorem ttbr1_reachable_consistent:
  "RegProt.reachable0 s \<Longrightarrow> ttbr1_consistent s"
  by (rule regprot_reachable_ttbr1_consistent)

theorem ttbr1_kpti_trace_integrity:
  assumes initial: "RegProt.reachable0 s"
      and reach: "RegProt.reachable s s'"
      and locked: "ttbr1_is_locked s"
  shows "ttbr1_is_locked s' \<and>
         get_TTBR1_EL1_saved s' = get_TTBR1_EL1_saved s \<and>
         ttbr1_consistent s'"
proof -
  from ttbr1_trace_preserves_locked_reference [OF reach locked]
  have fixed: "ttbr1_is_locked s' \<and>
               get_TTBR1_EL1_saved s' = get_TTBR1_EL1_saved s" .
  have "RegProt.reachable0 s'"
    using initial reach RegProt.reachable_trans
    unfolding RegProt.reachable0_def by blast
  then have "ttbr1_consistent s'"
    by (rule ttbr1_reachable_consistent)
  with fixed show ?thesis by blast
qed

end
