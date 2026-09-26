theory TTBR0
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>TTBR0_EL1 concrete Allow case.\<close>
  TTBR0 is a runtime translation-table base and may change during address-space
  switches. The Isabelle handler admits a write exactly when
  @{const ttbr_validate} accepts its CnP and alignment fields.

  The reusable @{locale Allow} locale currently models the saved-reference
  variant used by TTBR1. TTBR0 has no saved-reference state, so this theory
  records its concrete Allow behavior directly instead of manufacturing a
  fictitious lock state.
\<close>

definition get_ttbr0 :: "State \<Rightarrow> TTBR0_EL1" where
  "get_ttbr0 s = read_TTBR0_EL1 s"

definition set_ttbr0 :: "TTBR0_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_ttbr0 v s = write_TTBR0_EL1 s v"

lemma get_ttbr0_set_ttbr0 [simp]:
  "get_ttbr0 (set_ttbr0 v s) = v"
  by (simp add: get_ttbr0_def set_ttbr0_def
                read_TTBR0_EL1_def write_TTBR0_EL1_def)

lemma set_ttbr0_get_ttbr0 [simp]:
  "set_ttbr0 (get_ttbr0 s) s = s"
  by (simp add: get_ttbr0_def set_ttbr0_def
                read_TTBR0_EL1_def write_TTBR0_EL1_def)

lemma set_ttbr0_set_ttbr0 [simp]:
  "set_ttbr0 v\<^sub>2 (set_ttbr0 v\<^sub>1 s) = set_ttbr0 v\<^sub>2 s"
  by (simp add: set_ttbr0_def write_TTBR0_EL1_def)

interpretation TTBR0_Access: RegisterAccess get_ttbr0 set_ttbr0
  by unfold_locales simp_all

definition ttbr0_allow_write :: "TTBR0_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "ttbr0_allow_write v s =
     (if ttbr_validate s v then set_ttbr0 v s else s)"

lemma ttbr0_handler_state_matches:
  "fst (try_write_TTBR0_EL1 s v) = ttbr0_allow_write v s"
  by (simp add: try_write_TTBR0_EL1_def ttbr0_allow_write_def set_ttbr0_def Let_def)

lemma ttbr0_handler_accepts_iff [simp]:
  "snd (try_write_TTBR0_EL1 s v) = ttbr_validate s v"
  by (simp add: try_write_TTBR0_EL1_def Let_def)

theorem ttbr0_allow_preserves:
  assumes accepted: "\<And>s v. \<lbrakk> P s; ttbr_validate s v \<rbrakk> \<Longrightarrow> P (set_ttbr0 v s)"
      and initial: "P s"
  shows "P (fst (try_write_TTBR0_EL1 s v))"
  using assms by (auto simp add: ttbr0_handler_state_matches ttbr0_allow_write_def)

end
