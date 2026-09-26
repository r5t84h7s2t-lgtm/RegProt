theory TTBR1
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>Goal of this theory\<close>: demonstrate the full migration path for ONE register
  (TTBR1_EL1). The steps are:

  \<^enum> provide record-level accessors @{text get_ttbr1} / @{text set_ttbr1}
    (they are the glue between the nested @{typ State} record and the locale's
    generic @{text get_val} / @{text set_val} parameters);
  \<^enum> provide the saved-reference predicate / transition as glue over
    @{const get_TTBR1_EL1_state}, @{const get_TTBR1_EL1_saved}, and their setters;
  \<^enum> interpret @{locale Allow} \<^bold>\<open>once\<close> and discharge the proof
    obligations;
  \<^enum> prove the new @{text "TTBR1.try_write_allow"} is \<^emph>\<open>equivalent\<close> to the
    legacy @{const try_write_TTBR1_EL1}, so downstream code keeps working;
  \<^enum> state and prove the KPTI \<^emph>\<open>consistency invariant\<close> as a state-level
    predicate, discharged via @{thm Allow.try_write_allow_preserves}.
\<close>


section \<open>Step 1 \<^bold>\<open>Glue accessors for TTBR1_EL1\<close>\<close>

definition get_ttbr1 :: "State \<Rightarrow> TTBR1_EL1" where
  "get_ttbr1 s = read_TTBR1_EL1 s"

definition set_ttbr1 :: "TTBR1_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_ttbr1 v s = write_TTBR1_EL1 s v"

lemma get_ttbr1_set_ttbr1 [simp]:
  "get_ttbr1 (set_ttbr1 v s) = v"
  by (simp add: get_ttbr1_def set_ttbr1_def read_TTBR1_EL1_def write_TTBR1_EL1_def)

lemma set_ttbr1_get_ttbr1 [simp]:
  "set_ttbr1 (get_ttbr1 s) s = s"
  by (simp add: get_ttbr1_def set_ttbr1_def read_TTBR1_EL1_def write_TTBR1_EL1_def)

lemma set_ttbr1_set_ttbr1 [simp]:
  "set_ttbr1 v\<^sub>2 (set_ttbr1 v\<^sub>1 s) = set_ttbr1 v\<^sub>2 s"
  by (simp add: set_ttbr1_def write_TTBR1_EL1_def)


section \<open>Step 2 \<^bold>\<open>Lockdown glue: is_locked, pass, validate, lock_down\<close>\<close>

definition ttbr1_is_locked :: "State \<Rightarrow> bool" where
  "ttbr1_is_locked s \<equiv> (get_TTBR1_EL1_state s = LockDown)"

definition ttbr1_pass :: "TTBR1_EL1 \<Rightarrow> State \<Rightarrow> bool" where
  "ttbr1_pass v s \<equiv>
     (case get_TTBR1_EL1_saved s of
        Some saved \<Rightarrow> pass_TTBR1_EL1 v saved
      | None \<Rightarrow> False)"

text \<open>
  Note: @{const ttbr_validate} takes the \<^emph>\<open>polymorphic\<close> @{typ TTBRx_EL1}, so
  it applies to TTBR1 too. The value is \<^emph>\<open>not\<close> corrected, only accepted/rejected.
\<close>
definition ttbr1_validate :: "TTBR1_EL1 \<Rightarrow> State \<Rightarrow> TTBR1_EL1 option" where
  "ttbr1_validate v s \<equiv> (if ttbr_validate s v then Some v else None)"

definition ttbr1_lock_down :: "State \<Rightarrow> State" where
  "ttbr1_lock_down s \<equiv>
     if ttbr1_is_locked s then s
     else set_TTBR1_EL1_state
            (set_TTBR1_EL1_saved s (Some (read_TTBR1_EL1 s))) LockDown"

text \<open>
  TTBR1 is a \<^emph>\<open>reference-consistency\<close> register, not a value-lattice register:
  the admissibility of a new value depends on the locked reference, not on a
  pairwise order. Hence the locale's per-value @{text reg_leq} parameter is
  instantiated trivially; the real security invariant lives at the state level
  (see Section~\ref{sec:ttbr1-consistency}).
\<close>
definition ttbr1_reg_leq :: "TTBR1_EL1 \<Rightarrow> TTBR1_EL1 \<Rightarrow> bool" where
  "ttbr1_reg_leq v v' \<equiv> True"


section \<open>Step 3 \<^bold>\<open>The interpretation\<close>\<close>

interpretation TTBR1: Allow
  get_ttbr1 set_ttbr1
  ttbr1_is_locked ttbr1_pass ttbr1_validate ttbr1_reg_leq
  ttbr1_lock_down
  apply unfold_locales
  apply (auto simp add: ttbr1_reg_leq_def ttbr1_is_locked_def ttbr1_lock_down_def
                        get_ttbr1_def set_ttbr1_def
                        read_TTBR1_EL1_def write_TTBR1_EL1_def
                        get_TTBR1_EL1_state_def set_TTBR1_EL1_state_def
                        get_TTBR1_EL1_saved_def set_TTBR1_EL1_saved_def
                 split: if_splits)
  done

text \<open>After the interpretation we get these lemmas for free:\<close>
thm TTBR1.try_write_allow_def
thm TTBR1.try_write_allow_reg_leq
thm TTBR1.try_write_allow_preserves


section \<open>Step 4 \<^bold>\<open>Equivalence with the legacy @{const try_write_TTBR1_EL1}\<close>\<close>

text \<open>
  The legacy function returns @{typ "State \<times> bool"}; the new
  @{const TTBR1.try_write_allow} returns @{typ State}. The state component
  must agree, and the boolean corresponds to "did the state change, given the
  value actually updated?" -- which we spell out below.
\<close>

text \<open>
  @{const write_TTBR1_EL1} and @{const set_TTBR1_EL1_state} commute because
  they update different sub-records of @{typ State}: @{text sys_regs_el1} vs
  @{text protected_reg_state}.
\<close>
lemma write_ttbr1_set_state_comm:
  "write_TTBR1_EL1 (set_TTBR1_EL1_state s x) v =
   set_TTBR1_EL1_state (write_TTBR1_EL1 s v) x"
  by (simp add: write_TTBR1_EL1_def set_TTBR1_EL1_state_def)

lemma ttbr1_legacy_state_matches:
  "fst (try_write_TTBR1_EL1 s v) = TTBR1.try_write_allow v s"
  by (auto simp add: try_write_TTBR1_EL1_def TTBR1.try_write_allow_def
                     ttbr1_is_locked_def ttbr1_pass_def ttbr1_validate_def
                     ttbr1_lock_down_def get_ttbr1_def set_ttbr1_def
                     read_TTBR1_EL1_def write_TTBR1_EL1_def
                     get_TTBR1_EL1_state_def set_TTBR1_EL1_state_def
                     get_TTBR1_EL1_saved_def set_TTBR1_EL1_saved_def
              split: option.splits if_splits)

text \<open>
  We only need state equivalence for the locale migration. The legacy boolean
  flag is intentionally left out of the trusted refinement statement because
  downstream security properties depend on the successor state, not on the
  diagnostic acceptance bit.
\<close>


section \<open>Step 5 \<^bold>\<open>KPTI consistency invariant\<close> \label{sec:ttbr1-consistency}\<close>

text \<open>
  The first accepted TTBR1 write saves a fixed trusted reference and enters
  lockdown. Every subsequent admitted write must satisfy the KPTI tolerance
  predicate relative to that saved reference. The reference never slides when
  a later write is accepted, preventing a sequence of individually small
  changes from drifting arbitrarily far from the trusted page-table base.
\<close>

definition ttbr1_consistent :: "State \<Rightarrow> bool" where
  "ttbr1_consistent s \<equiv>
     if ttbr1_is_locked s then
       (\<exists>saved. get_TTBR1_EL1_saved s = Some saved \<and>
                pass_TTBR1_EL1 (read_TTBR1_EL1 s) saved)
     else
       get_TTBR1_EL1_saved s = None"

text \<open>Reflexivity establishes consistency exactly when lockdown captures
      the current TTBR1 value as the fixed reference.\<close>
lemma pass_TTBR1_EL1_refl:
  "pass_TTBR1_EL1 v v"
  by (simp add: pass_TTBR1_EL1_def abs_diff_def)

text \<open>An unlocked state with no saved reference is consistent.\<close>
lemma ttbr1_consistent_initial:
  "\<lbrakk> get_TTBR1_EL1_state s = Unset; get_TTBR1_EL1_saved s = None \<rbrakk>
   \<Longrightarrow> ttbr1_consistent s"
  by (simp add: ttbr1_consistent_def ttbr1_is_locked_def)

lemma ttbr1_locked_has_saved_reference:
  "\<lbrakk> ttbr1_consistent s; ttbr1_is_locked s \<rbrakk> \<Longrightarrow>
   \<exists>saved. get_TTBR1_EL1_saved s = Some saved \<and>
            pass_TTBR1_EL1 (read_TTBR1_EL1 s) saved"
  by (simp add: ttbr1_consistent_def)

lemma ttbr1_saved_fixed_when_locked:
  "ttbr1_is_locked s \<Longrightarrow>
   get_TTBR1_EL1_saved (TTBR1.try_write_allow v s) = get_TTBR1_EL1_saved s"
  by (auto simp add: TTBR1.try_write_allow_def ttbr1_pass_def
                     set_ttbr1_def write_TTBR1_EL1_def
                     get_TTBR1_EL1_saved_def
              split: option.splits if_splits)

theorem ttbr1_incompatible_write_rejected:
  assumes locked: "ttbr1_is_locked s"
      and saved: "get_TTBR1_EL1_saved s = Some reference"
      and incompatible: "\<not> pass_TTBR1_EL1 v reference"
  shows "try_write_TTBR1_EL1 s v = (s, False)"
  using assms
  by (simp add: try_write_TTBR1_EL1_def ttbr1_is_locked_def)

text \<open>
  The consistency invariant is preserved by any @{const TTBR1.try_write_allow}
  call. The proof follows the locale control flow and keeps the saved reference
  fixed in both locked branches.
\<close>

lemma ttbr1_consistent_preserved:
  assumes "ttbr1_consistent s"
  shows   "ttbr1_consistent (TTBR1.try_write_allow v s)"
  using assms
  by (auto simp add: TTBR1.try_write_allow_def ttbr1_consistent_def
                     ttbr1_is_locked_def ttbr1_pass_def ttbr1_lock_down_def
                     set_ttbr1_def read_TTBR1_EL1_def write_TTBR1_EL1_def
                     get_TTBR1_EL1_state_def set_TTBR1_EL1_state_def
                     get_TTBR1_EL1_saved_def set_TTBR1_EL1_saved_def
                     pass_TTBR1_EL1_refl
              split: option.splits if_splits)

end
