theory FAR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>FAR_EL1 concrete Allow case.\<close>
  FAR records a fault address. The Isabelle model treats it as runtime status,
  so every write is accepted and does not participate in the protected
  configuration preorder.
\<close>

definition get_far :: "State \<Rightarrow> FAR_EL1" where
  "get_far s = read_FAR_EL1 s"

definition set_far :: "FAR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_far v s = write_FAR_EL1 s v"

lemma get_far_set_far [simp]: "get_far (set_far v s) = v"
  by (simp add: get_far_def set_far_def read_FAR_EL1_def write_FAR_EL1_def)

lemma set_far_get_far [simp]: "set_far (get_far s) s = s"
  by (simp add: get_far_def set_far_def read_FAR_EL1_def write_FAR_EL1_def)

lemma set_far_set_far [simp]:
  "set_far v\<^sub>2 (set_far v\<^sub>1 s) = set_far v\<^sub>2 s"
  by (simp add: set_far_def write_FAR_EL1_def)

interpretation FAR_Access: RegisterAccess get_far set_far
  by unfold_locales simp_all

lemma far_handler_state_matches:
  "fst (try_write_FAR_EL1 s v) = FAR_Access.reg_write v s"
  by (simp add: try_write_FAR_EL1_def FAR_Access.reg_write_def set_far_def Let_def)

lemma far_handler_accepts [simp]: "snd (try_write_FAR_EL1 s v)"
  by (simp add: try_write_FAR_EL1_def Let_def)

theorem far_allow_preserves:
  assumes write_preserves: "\<And>s v. P s \<Longrightarrow> P (set_far v s)"
      and initial: "P s"
  shows "P (fst (try_write_FAR_EL1 s v))"
  using assms
  by (simp add: far_handler_state_matches FAR_Access.reg_write_def)

end
