theory AFSR0
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>AFSR0_EL1 Discard interpretation.\<close>
  AFSR0 has implementation-defined semantics. The handler ignores every guest
  write, reducing the exposed attack surface and preserving the complete model
  state.
\<close>

definition get_afsr0 :: "State \<Rightarrow> AFSR0_EL1" where
  "get_afsr0 s = read_AFSR0_EL1 s"

definition set_afsr0 :: "AFSR0_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_afsr0 v s = write_AFSR0_EL1 s v"

lemma get_afsr0_set_afsr0 [simp]: "get_afsr0 (set_afsr0 v s) = v"
  by (simp add: get_afsr0_def set_afsr0_def read_AFSR0_EL1_def write_AFSR0_EL1_def)

lemma set_afsr0_get_afsr0 [simp]: "set_afsr0 (get_afsr0 s) s = s"
  by (simp add: get_afsr0_def set_afsr0_def read_AFSR0_EL1_def write_AFSR0_EL1_def)

lemma set_afsr0_set_afsr0 [simp]:
  "set_afsr0 v\<^sub>2 (set_afsr0 v\<^sub>1 s) = set_afsr0 v\<^sub>2 s"
  by (simp add: set_afsr0_def write_AFSR0_EL1_def)

interpretation AFSR0: Discard get_afsr0 set_afsr0
  by unfold_locales simp_all

lemma afsr0_handler_state_matches:
  "fst (try_write_AFSR0_EL1 s v) = AFSR0.discard_write v s"
  by (simp add: try_write_AFSR0_EL1_def AFSR0.discard_write_def)

lemma afsr0_handler_rejects [simp]: "\<not> snd (try_write_AFSR0_EL1 s v)"
  by (simp add: try_write_AFSR0_EL1_def)

theorem afsr0_write_preserves_any:
  "P s \<Longrightarrow> P (fst (try_write_AFSR0_EL1 s v))"
  by (simp add: afsr0_handler_state_matches)

end
