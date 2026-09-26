theory ACTLR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>ACTLR_EL1 default Discard interpretation.\<close>
  ACTLR is implementation-defined. The generic RegProt Rust handler ignores its
  writes and returns zero on reads; the Isabelle handler likewise leaves the
  modeled state unchanged on writes.

  ACTLR is modeled by the functional dispatcher but is not one of the eleven
  registers listed in the paper's protection-strategy table. It is therefore
  recorded as additional implementation coverage and is not counted toward
  that table.
\<close>

definition get_actlr :: "State \<Rightarrow> ACTLR_EL1" where
  "get_actlr s = read_ACTLR_EL1 s"

definition set_actlr :: "ACTLR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_actlr v s = write_ACTLR_EL1 s v"

lemma get_actlr_set_actlr [simp]: "get_actlr (set_actlr v s) = v"
  by (simp add: get_actlr_def set_actlr_def read_ACTLR_EL1_def write_ACTLR_EL1_def)

lemma set_actlr_get_actlr [simp]: "set_actlr (get_actlr s) s = s"
  by (simp add: get_actlr_def set_actlr_def read_ACTLR_EL1_def write_ACTLR_EL1_def)

lemma set_actlr_set_actlr [simp]:
  "set_actlr v\<^sub>2 (set_actlr v\<^sub>1 s) = set_actlr v\<^sub>2 s"
  by (simp add: set_actlr_def write_ACTLR_EL1_def)

interpretation ACTLR: Discard get_actlr set_actlr
  by unfold_locales simp_all

lemma actlr_handler_state_matches:
  "fst (try_write_ACTLR_EL1 s v) = ACTLR.discard_write v s"
  by (simp add: try_write_ACTLR_EL1_def ACTLR.discard_write_def)

lemma actlr_handler_rejects [simp]: "\<not> snd (try_write_ACTLR_EL1 s v)"
  by (simp add: try_write_ACTLR_EL1_def)

theorem actlr_write_preserves_any:
  "P s \<Longrightarrow> P (fst (try_write_ACTLR_EL1 s v))"
  by (simp add: actlr_handler_state_matches)

end
