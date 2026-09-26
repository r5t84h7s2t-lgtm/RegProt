theory AFSR1
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>AFSR1_EL1 Discard interpretation.\<close>
  AFSR1 has implementation-defined semantics. Its handler discards every write
  and therefore preserves every predicate over the Isabelle state.
\<close>

definition get_afsr1 :: "State \<Rightarrow> AFSR1_EL1" where
  "get_afsr1 s = read_AFSR1_EL1 s"

definition set_afsr1 :: "AFSR1_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_afsr1 v s = write_AFSR1_EL1 s v"

lemma get_afsr1_set_afsr1 [simp]: "get_afsr1 (set_afsr1 v s) = v"
  by (simp add: get_afsr1_def set_afsr1_def read_AFSR1_EL1_def write_AFSR1_EL1_def)

lemma set_afsr1_get_afsr1 [simp]: "set_afsr1 (get_afsr1 s) s = s"
  by (simp add: get_afsr1_def set_afsr1_def read_AFSR1_EL1_def write_AFSR1_EL1_def)

lemma set_afsr1_set_afsr1 [simp]:
  "set_afsr1 v\<^sub>2 (set_afsr1 v\<^sub>1 s) = set_afsr1 v\<^sub>2 s"
  by (simp add: set_afsr1_def write_AFSR1_EL1_def)

interpretation AFSR1: Discard get_afsr1 set_afsr1
  by unfold_locales simp_all

lemma afsr1_handler_state_matches:
  "fst (try_write_AFSR1_EL1 s v) = AFSR1.discard_write v s"
  by (simp add: try_write_AFSR1_EL1_def AFSR1.discard_write_def)

lemma afsr1_handler_rejects [simp]: "\<not> snd (try_write_AFSR1_EL1 s v)"
  by (simp add: try_write_AFSR1_EL1_def)

theorem afsr1_write_preserves_any:
  "P s \<Longrightarrow> P (fst (try_write_AFSR1_EL1 s v))"
  by (simp add: afsr1_handler_state_matches)

end
