theory CONTEXTIDR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>CONTEXTIDR_EL1 concrete Allow case.\<close>
  CONTEXTIDR carries a runtime context identifier used by debug and trace
  facilities. The Isabelle handler accepts every value and updates only this
  field. This theory states the Isabelle behavior; correspondence with the
  additional validation side effects in the Rust handler remains a modeling
  assumption outside this proof.
\<close>

definition get_contextidr :: "State \<Rightarrow> CONTEXTIDR_EL1" where
  "get_contextidr s = read_CONTEXTIDR_EL1 s"

definition set_contextidr :: "CONTEXTIDR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_contextidr v s = write_CONTEXTIDR_EL1 s v"

lemma get_contextidr_set_contextidr [simp]:
  "get_contextidr (set_contextidr v s) = v"
  by (simp add: get_contextidr_def set_contextidr_def
                read_CONTEXTIDR_EL1_def write_CONTEXTIDR_EL1_def)

lemma set_contextidr_get_contextidr [simp]:
  "set_contextidr (get_contextidr s) s = s"
  by (simp add: get_contextidr_def set_contextidr_def
                read_CONTEXTIDR_EL1_def write_CONTEXTIDR_EL1_def)

lemma set_contextidr_set_contextidr [simp]:
  "set_contextidr v\<^sub>2 (set_contextidr v\<^sub>1 s) = set_contextidr v\<^sub>2 s"
  by (simp add: set_contextidr_def write_CONTEXTIDR_EL1_def)

interpretation CONTEXTIDR_Access: RegisterAccess get_contextidr set_contextidr
  by unfold_locales simp_all

lemma contextidr_handler_state_matches:
  "fst (try_write_CONTEXTIDR_EL1 s v) = CONTEXTIDR_Access.reg_write v s"
  by (simp add: try_write_CONTEXTIDR_EL1_def CONTEXTIDR_Access.reg_write_def
                set_contextidr_def Let_def)

lemma contextidr_handler_accepts [simp]: "snd (try_write_CONTEXTIDR_EL1 s v)"
  by (simp add: try_write_CONTEXTIDR_EL1_def Let_def)

theorem contextidr_allow_preserves:
  assumes write_preserves: "\<And>s v. P s \<Longrightarrow> P (set_contextidr v s)"
      and initial: "P s"
  shows "P (fst (try_write_CONTEXTIDR_EL1 s v))"
  using assms
  by (simp add: contextidr_handler_state_matches CONTEXTIDR_Access.reg_write_def)

end
