theory ESR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>ESR_EL1 concrete Allow case.\<close>
  ESR records exception syndrome information. In the Isabelle handler model it
  is not a protected configuration register: every write is accepted and only
  the ESR field is updated.
\<close>

definition get_esr :: "State \<Rightarrow> ESR_EL1" where
  "get_esr s = read_ESR_EL1 s"

definition set_esr :: "ESR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_esr v s = write_ESR_EL1 s v"

lemma get_esr_set_esr [simp]: "get_esr (set_esr v s) = v"
  by (simp add: get_esr_def set_esr_def read_ESR_EL1_def write_ESR_EL1_def)

lemma set_esr_get_esr [simp]: "set_esr (get_esr s) s = s"
  by (simp add: get_esr_def set_esr_def read_ESR_EL1_def write_ESR_EL1_def)

lemma set_esr_set_esr [simp]:
  "set_esr v\<^sub>2 (set_esr v\<^sub>1 s) = set_esr v\<^sub>2 s"
  by (simp add: set_esr_def write_ESR_EL1_def)

interpretation ESR_Access: RegisterAccess get_esr set_esr
  by unfold_locales simp_all

lemma esr_handler_state_matches:
  "fst (try_write_ESR_EL1 s v) = ESR_Access.reg_write v s"
  by (simp add: try_write_ESR_EL1_def ESR_Access.reg_write_def set_esr_def Let_def)

lemma esr_handler_accepts [simp]: "snd (try_write_ESR_EL1 s v)"
  by (simp add: try_write_ESR_EL1_def Let_def)

theorem esr_allow_preserves:
  assumes write_preserves: "\<And>s v. P s \<Longrightarrow> P (set_esr v s)"
      and initial: "P s"
  shows "P (fst (try_write_ESR_EL1 s v))"
  using assms
  by (simp add: esr_handler_state_matches ESR_Access.reg_write_def)

end
