theory AMAIR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>AMAIR_EL1 Discard interpretation.\<close>
  AMAIR contains implementation-defined auxiliary memory attributes. RegProt does
  not expose modifications to the guest, so the concrete handler leaves the
  entire Isabelle state unchanged.
\<close>

definition get_amair :: "State \<Rightarrow> AMAIR_EL1" where
  "get_amair s = read_AMAIR_EL1 s"

definition set_amair :: "AMAIR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_amair v s = write_AMAIR_EL1 s v"

lemma get_amair_set_amair [simp]: "get_amair (set_amair v s) = v"
  by (simp add: get_amair_def set_amair_def read_AMAIR_EL1_def write_AMAIR_EL1_def)

lemma set_amair_get_amair [simp]: "set_amair (get_amair s) s = s"
  by (simp add: get_amair_def set_amair_def read_AMAIR_EL1_def write_AMAIR_EL1_def)

lemma set_amair_set_amair [simp]:
  "set_amair v\<^sub>2 (set_amair v\<^sub>1 s) = set_amair v\<^sub>2 s"
  by (simp add: set_amair_def write_AMAIR_EL1_def)

interpretation AMAIR: Discard get_amair set_amair
  by unfold_locales simp_all

lemma amair_handler_state_matches:
  "fst (try_write_AMAIR_EL1 s v) = AMAIR.discard_write v s"
  by (simp add: try_write_AMAIR_EL1_def AMAIR.discard_write_def)

lemma amair_handler_rejects [simp]: "\<not> snd (try_write_AMAIR_EL1 s v)"
  by (simp add: try_write_AMAIR_EL1_def)

theorem amair_write_preserves_any:
  "P s \<Longrightarrow> P (fst (try_write_AMAIR_EL1 s v))"
  by (simp add: amair_handler_state_matches)

end
