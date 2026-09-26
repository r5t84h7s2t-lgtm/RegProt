theory MAIR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>MAIR_EL1 interpretation.\<close>
  Protection pattern: \<^emph>\<open>unconditional lock-on-first-write\<close>.
  The first write is always accepted (no structural validation); afterwards,
  every write is rejected. This is the simplest lock-on-write register:
  @{text validate} returns @{term "Some v"} unconditionally, and @{text pass}
  is always @{term False}.

  MAIR carries the memory attribute indirection table, which must be
  configured before the guest MMU is enabled. Once set, KPIP prevents
  any subsequent modification.
\<close>


section \<open>Step 1 \<^bold>\<open>Glue accessors for MAIR_EL1\<close>\<close>

definition get_mair :: "State \<Rightarrow> MAIR_EL1" where
  "get_mair s = read_MAIR_EL1 s"

definition set_mair :: "MAIR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_mair v s = write_MAIR_EL1 s v"

lemma get_mair_set_mair [simp]:
  "get_mair (set_mair v s) = v"
  by (simp add: get_mair_def set_mair_def read_MAIR_EL1_def write_MAIR_EL1_def)

lemma set_mair_get_mair [simp]:
  "set_mair (get_mair s) s = s"
  by (simp add: get_mair_def set_mair_def read_MAIR_EL1_def write_MAIR_EL1_def)

lemma set_mair_set_mair [simp]:
  "set_mair v\<^sub>2 (set_mair v\<^sub>1 s) = set_mair v\<^sub>2 s"
  by (simp add: set_mair_def write_MAIR_EL1_def)


section \<open>Step 2 \<^bold>\<open>Lockdown glue\<close>\<close>

definition mair_is_locked :: "State \<Rightarrow> bool" where
  "mair_is_locked s \<equiv> (get_MAIR_EL1_state s = LockDown)"

text \<open>Locked writes are unconditionally rejected.\<close>
definition mair_pass :: "MAIR_EL1 \<Rightarrow> State \<Rightarrow> bool" where
  "mair_pass v s \<equiv> False"

text \<open>
  MAIR values are not structurally constrained -- any 64-bit pattern is a
  valid memory attribute table. Hence @{text mair_validate} accepts every value.
\<close>
definition mair_validate :: "MAIR_EL1 \<Rightarrow> State \<Rightarrow> MAIR_EL1 option" where
  "mair_validate v s \<equiv> Some v"

definition mair_lock_down :: "State \<Rightarrow> State" where
  "mair_lock_down s \<equiv> set_MAIR_EL1_state s LockDown"

text \<open>Trivial preorder (both @{text pass} and @{text validate_mono} vacuous).\<close>
definition mair_reg_leq :: "MAIR_EL1 \<Rightarrow> MAIR_EL1 \<Rightarrow> bool" where
  "mair_reg_leq v v' \<equiv> True"


section \<open>Step 3 \<^bold>\<open>The interpretation\<close>\<close>

text \<open>
  All 10 obligations are discharged by @{method auto} after unfolding.
  The interesting ones: @{text validate_mono} holds trivially since
  @{text mair_reg_leq} = @{term True}; @{text lock_down_get} holds since
  @{const mair_lock_down} only updates @{text protected_reg_state}.
\<close>

interpretation MAIR: PostBootLock
  get_mair set_mair
  mair_is_locked mair_pass mair_validate mair_reg_leq
  mair_lock_down
  apply unfold_locales
  apply (auto simp add: mair_reg_leq_def mair_pass_def mair_is_locked_def
                        mair_lock_down_def mair_validate_def
                        get_mair_def set_mair_def
                        read_MAIR_EL1_def write_MAIR_EL1_def
                        get_MAIR_EL1_state_def set_MAIR_EL1_state_def)
  done

thm MAIR.try_write_post_boot_lock_def
thm MAIR.try_write_post_boot_lock_reg_leq
thm MAIR.try_write_post_boot_lock_preserves


section \<open>Step 4 \<^bold>\<open>Equivalence with the legacy @{const try_write_MAIR_EL1}\<close>\<close>

text \<open>
  @{const write_MAIR_EL1} and @{const set_MAIR_EL1_state} commute because they
  update different sub-records (@{text sys_regs_el1} vs @{text protected_reg_state}).
\<close>
lemma write_mair_set_state_comm:
  "write_MAIR_EL1 (set_MAIR_EL1_state s x) v = set_MAIR_EL1_state (write_MAIR_EL1 s v) x"
  by (simp add: write_MAIR_EL1_def set_MAIR_EL1_state_def)

lemma mair_legacy_state_matches:
  "fst (try_write_MAIR_EL1 s v) = MAIR.try_write_post_boot_lock v s"
proof (cases "mair_is_locked s")
  case True
  from True show ?thesis
    by (simp add: try_write_MAIR_EL1_def mair_is_locked_def
                  MAIR.try_write_post_boot_lock_locked_rejected mair_pass_def)
next
  case False
  hence unlocked: "\<not> mair_is_locked s" by simp
  hence unlocked_raw: "get_MAIR_EL1_state s \<noteq> LockDown"
    by (simp add: mair_is_locked_def)
  
  have val_some: "mair_validate v s = Some v"
    by (simp add: mair_validate_def)
  have rhs: "MAIR.try_write_post_boot_lock v s = mair_lock_down (set_mair v s)"
    using MAIR.try_write_post_boot_lock_unlocked_accepted [OF unlocked val_some] .
  have lhs: "fst (try_write_MAIR_EL1 s v) = write_MAIR_EL1 (set_MAIR_EL1_state s LockDown) v"
    using unlocked_raw
    by (simp add: try_write_MAIR_EL1_def Let_def)
  show ?thesis
    by (simp add: lhs rhs mair_lock_down_def set_mair_def write_mair_set_state_comm)
qed


section \<open>Step 5 \<^bold>\<open>Key security properties\<close>\<close>

text \<open>
  \<^bold>\<open>Property 1: immutability after lock.\<close>
  Since @{text mair_pass} = @{term False}, any locked write returns the
  state unchanged -- the memory attribute table is frozen.
\<close>
lemma mair_frozen_when_locked:
  "mair_is_locked s \<Longrightarrow> MAIR.try_write_post_boot_lock v s = s"
  using MAIR.try_write_post_boot_lock_locked_rejected [where s = s and v = v]
  by (simp add: mair_pass_def)

corollary mair_val_frozen:
  "mair_is_locked s \<Longrightarrow> get_mair (MAIR.try_write_post_boot_lock v s) = get_mair s"
  by (simp add: mair_frozen_when_locked)

text \<open>
  \<^bold>\<open>Property 2: lock monotonicity.\<close>
  Once locked, the lock flag is never cleared.
\<close>
lemma mair_lock_monotone:
  "mair_is_locked s \<Longrightarrow> mair_is_locked (MAIR.try_write_post_boot_lock v s)"
  by (simp add: mair_frozen_when_locked)

text \<open>
  \<^bold>\<open>Property 3: first write always stored.\<close>
  Before locking, any write succeeds and the value is committed.
  (There is no structural constraint on MAIR.)
\<close>
lemma mair_first_write_stores:
  "\<not> mair_is_locked s \<Longrightarrow> get_mair (MAIR.try_write_post_boot_lock v s) = v"
proof -
  assume unl: "\<not> mair_is_locked s"
  have val_some: "mair_validate v s = Some v"
    by (simp add: mair_validate_def)
  from MAIR.try_write_post_boot_lock_unlocked_accepted [OF unl val_some]
  show ?thesis
    by (simp add: MAIR.lock_down_get)
qed

end
