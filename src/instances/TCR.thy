theory TCR
  imports
    "../framework/Register_Strategies"
    "../handlers/Register_Handlers"
begin

text \<open>
  \<^bold>\<open>TCR_EL1 interpretation.\<close>
  Protection pattern: \<^emph>\<open>lock-on-first-write, then always reject\<close>.
  Once the register is locked, \<^emph>\<open>every\<close> subsequent write is silently dropped.
  This contrasts with TTBR1 (which admits writes within a tolerance window)
  and SCTLR (which has no lock state but enforces a value lattice).

  Locale used: @{locale PostBootLock} with trivial @{text reg_leq} (always
  @{term True}) and @{text pass} = @{term False} (locked branch always rejects).
\<close>


section \<open>Step 1 \<^bold>\<open>Glue accessors for TCR_EL1\<close>\<close>

definition get_tcr :: "State \<Rightarrow> TCR_EL1" where
  "get_tcr s = read_TCR_EL1 s"

definition set_tcr :: "TCR_EL1 \<Rightarrow> State \<Rightarrow> State" where
  "set_tcr v s = write_TCR_EL1 s v"

lemma get_tcr_set_tcr [simp]:
  "get_tcr (set_tcr v s) = v"
  by (simp add: get_tcr_def set_tcr_def read_TCR_EL1_def write_TCR_EL1_def)

lemma set_tcr_get_tcr [simp]:
  "set_tcr (get_tcr s) s = s"
  by (simp add: get_tcr_def set_tcr_def read_TCR_EL1_def write_TCR_EL1_def)

lemma set_tcr_set_tcr [simp]:
  "set_tcr v\<^sub>2 (set_tcr v\<^sub>1 s) = set_tcr v\<^sub>2 s"
  by (simp add: set_tcr_def write_TCR_EL1_def)


section \<open>Step 2 \<^bold>\<open>Lockdown glue\<close>\<close>

definition tcr_is_locked :: "State \<Rightarrow> bool" where
  "tcr_is_locked s \<equiv> (get_TCR_EL1_state s = LockDown)"

text \<open>
  Once locked, TCR_EL1 rejects \<^emph>\<open>every\<close> write (unlike TTBR1 which admits
  writes within a tolerance window). Hence @{text tcr_pass} is constantly
  @{term False}; @{text pass_mono} is vacuously satisfied.
\<close>
definition tcr_pass :: "TCR_EL1 \<Rightarrow> State \<Rightarrow> bool" where
  "tcr_pass v s \<equiv> False"

text \<open>
  @{const TCR_EL1_validate} returns a @{typ "bool \<times> TCR_EL1"} pair; it may
  correct (mask) the value (e.g.\ clear TBID bits when PAC is absent).
\<close>
definition tcr_validate :: "TCR_EL1 \<Rightarrow> State \<Rightarrow> TCR_EL1 option" where
  "tcr_validate v s \<equiv>
     if fst (TCR_EL1_validate s v) then Some (snd (TCR_EL1_validate s v)) else None"

definition tcr_mte_value_supported :: "State \<Rightarrow> TCR_EL1 \<Rightarrow> bool" where
  "tcr_mte_value_supported s v \<equiv>
     ((TCMA1 v \<or> TCMA0 v) \<longrightarrow>
       MTE (read_ID_AA64PFR1_EL1 s) \<noteq> MTE_None)"

definition tcr_mte_consistent :: "State \<Rightarrow> bool" where
  "tcr_mte_consistent s \<equiv> tcr_mte_value_supported s (get_tcr s)"

text \<open>
  The concrete TCR validator consults ID_AA64PFR1_EL1 before admitting TCMA0
  or TCMA1. Its optional TBID correction does not change either TCMA field.
\<close>
lemma TCR_EL1_validate_mte_supported:
  "fst (TCR_EL1_validate s v) \<Longrightarrow>
   tcr_mte_value_supported s (snd (TCR_EL1_validate s v))"
  by (auto simp add: TCR_EL1_validate_def pfr1_validate_def
                     tcr_mte_value_supported_def Let_def
           split: if_splits)

lemma tcr_validate_mte_supported:
  "tcr_validate v s = Some v' \<Longrightarrow> tcr_mte_value_supported s v'"
  using TCR_EL1_validate_mte_supported
  by (auto simp add: tcr_validate_def split: if_splits)

definition tcr_lock_down :: "State \<Rightarrow> State" where
  "tcr_lock_down s \<equiv> set_TCR_EL1_state s LockDown"

text \<open>
  A trivial per-value ordering: once locked, no writes go through, so the
  ordering carries no security content. The locale still requires a preorder.
\<close>
definition tcr_reg_leq :: "TCR_EL1 \<Rightarrow> TCR_EL1 \<Rightarrow> bool" where
  "tcr_reg_leq v v' \<equiv> True"


section \<open>Step 3 \<^bold>\<open>The interpretation\<close>\<close>

text \<open>
  Proof obligations via @{locale PostBootLock}:
  \<^item> RegisterAccess (3): get/set round-trips -- straightforward record unfolding.
  \<^item> Allow: @{text reg_leq_refl} and @{text reg_leq_trans} trivial
    since @{text tcr_reg_leq} is constantly @{term True};
    @{text pass_mono} vacuous since @{text tcr_pass} is constantly @{term False};
    @{text validate_mono} trivial.
  \<^item> PostBootLock: @{text lock_down_get} holds since @{const tcr_lock_down}
    only changes @{text protected_reg_state}, not @{text sys_regs_el1};
    @{text lock_down_is_locked}, @{text lock_down_locked_id}, and
    @{text pass_never} by unfolding.
\<close>

interpretation TCR: PostBootLock
  get_tcr set_tcr
  tcr_is_locked tcr_pass tcr_validate tcr_reg_leq
  tcr_lock_down
  apply unfold_locales
  apply (auto simp add: tcr_reg_leq_def tcr_pass_def tcr_is_locked_def
                        tcr_lock_down_def tcr_validate_def
                        get_tcr_def set_tcr_def
                        read_TCR_EL1_def write_TCR_EL1_def
                        get_TCR_EL1_state_def set_TCR_EL1_state_def)
  done

text \<open>Available locale lemmas:\<close>
thm TCR.try_write_post_boot_lock_def
thm TCR.try_write_post_boot_lock_reg_leq
thm TCR.try_write_post_boot_lock_preserves


section \<open>Step 4 \<^bold>\<open>Equivalence with the legacy @{const try_write_TCR_EL1}\<close>\<close>

text \<open>
  @{const write_TCR_EL1} and @{const set_TCR_EL1_state} commute because they
  update different sub-records of @{typ State}: @{text sys_regs_el1} vs
  @{text protected_reg_state}.
\<close>
lemma write_tcr_set_state_comm:
  "write_TCR_EL1 (set_TCR_EL1_state s x) v = set_TCR_EL1_state (write_TCR_EL1 s v) x"
  by (simp add: write_TCR_EL1_def set_TCR_EL1_state_def)

lemma tcr_legacy_state_matches:
  "fst (try_write_TCR_EL1 s v) = TCR.try_write_post_boot_lock v s"
proof (cases "tcr_is_locked s")
  case True
  
  from True show ?thesis
    by (simp add: try_write_TCR_EL1_def tcr_is_locked_def
                  TCR.try_write_post_boot_lock_locked_rejected tcr_pass_def)
next
  case False
  hence unlocked: "\<not> tcr_is_locked s"
    by simp
  hence unlocked_raw: "get_TCR_EL1_state s \<noteq> LockDown"
    by (simp add: tcr_is_locked_def)
  show ?thesis
  proof (cases "fst (TCR_EL1_validate s v)")
    case True
    
    let ?v' = "snd (TCR_EL1_validate s v)"
    have val_some: "tcr_validate v s = Some ?v'"
      by (simp add: tcr_validate_def True)
    have rhs: "TCR.try_write_post_boot_lock v s = tcr_lock_down (set_tcr ?v' s)"
      using TCR.try_write_post_boot_lock_unlocked_accepted [OF unlocked val_some] .
    have lhs: "fst (try_write_TCR_EL1 s v) =
               write_TCR_EL1 (set_TCR_EL1_state s LockDown) ?v'"
      using True unlocked_raw
      by (simp add: try_write_TCR_EL1_def Let_def)
    show ?thesis
      by (simp add: lhs rhs tcr_lock_down_def set_tcr_def write_tcr_set_state_comm)
  next
    case False
    
    have val_none: "tcr_validate v s = None"
      by (simp add: tcr_validate_def False)
    have rhs: "TCR.try_write_post_boot_lock v s = s"
      using TCR.try_write_post_boot_lock_unlocked_rejected [OF unlocked val_none] .
    have lhs: "fst (try_write_TCR_EL1 s v) = s"
      using False unlocked_raw
      by (simp add: try_write_TCR_EL1_def Let_def)
    show ?thesis by (simp add: lhs rhs)
  qed
qed


section \<open>Step 5 \<^bold>\<open>Key security properties\<close>\<close>

text \<open>
  \<^bold>\<open>Property 1: lock monotonicity.\<close>
  Once @{text tcr_is_locked} holds, every call to
  @{const TCR.try_write_post_boot_lock} leaves the lock flag set. Since
  @{text tcr_pass} = @{term False}, the locked branch always returns the
  old state unchanged.
\<close>
lemma tcr_lock_monotone:
  "tcr_is_locked s \<Longrightarrow> tcr_is_locked (TCR.try_write_post_boot_lock v s)"
proof -
  assume locked: "tcr_is_locked s"
  have "TCR.try_write_post_boot_lock v s = s"
    using TCR.try_write_post_boot_lock_locked_rejected [OF locked]
    by (simp add: tcr_pass_def)
  with locked show ?thesis by simp
qed

text \<open>
  \<^bold>\<open>Property 2: immutability after lock.\<close>
  A stronger statement: the state itself is \<^emph>\<open>unchanged\<close> after any write
  attempt once the register is locked. This is the key KPTI-hardening guarantee
  for TCR_EL1: the memory translation configuration is frozen after boot.
\<close>
lemma tcr_frozen_when_locked:
  "tcr_is_locked s \<Longrightarrow> TCR.try_write_post_boot_lock v s = s"
  using TCR.try_write_post_boot_lock_locked_rejected [where s = s and v = v]
  by (simp add: tcr_pass_def)

corollary tcr_val_frozen:
  "tcr_is_locked s \<Longrightarrow> get_tcr (TCR.try_write_post_boot_lock v s) = get_tcr s"
  by (simp add: tcr_frozen_when_locked)

text \<open>
  \<^bold>\<open>Property 3: first-write validates.\<close>
  Before locking, a write is accepted if and only if @{const TCR_EL1_validate}
  approves it; afterwards the stored value is the (possibly corrected) result
  of that validation. This connects the locale's abstract \<open>try_write_post_boot_lock\<close>
  to the concrete hardware constraint checker.
\<close>
lemma tcr_first_write_stores_validated:
  "\<lbrakk> \<not> tcr_is_locked s; fst (TCR_EL1_validate s v) \<rbrakk>
   \<Longrightarrow> get_tcr (TCR.try_write_post_boot_lock v s) = snd (TCR_EL1_validate s v)"
proof -
  assume unl: "\<not> tcr_is_locked s" and ok: "fst (TCR_EL1_validate s v)"
  let ?v' = "snd (TCR_EL1_validate s v)"
  have val_some: "tcr_validate v s = Some ?v'"
    by (simp add: tcr_validate_def ok)
  from TCR.try_write_post_boot_lock_unlocked_accepted [OF unl val_some]
  show ?thesis
    by (simp add: TCR.lock_down_get)
qed

text \<open>
  A concrete handler step preserves TCMA/MTE capability consistency. Locked or
  rejected writes are no-ops; an accepted first write stores the value returned
  by @{const TCR_EL1_validate}, which satisfies
  @{thm TCR_EL1_validate_mte_supported}.
\<close>
theorem tcr_handler_mte_consistent:
  assumes cons: "tcr_mte_consistent s"
  shows "tcr_mte_consistent (fst (try_write_TCR_EL1 s v))"
proof (cases "get_TCR_EL1_state s = LockDown")
  assume locked: "get_TCR_EL1_state s = LockDown"
  then show ?thesis using cons
    by (simp add: try_write_TCR_EL1_def)
next
  assume unlocked: "get_TCR_EL1_state s \<noteq> LockDown"
  show ?thesis
  proof (cases "fst (TCR_EL1_validate s v)")
    assume rejected: "\<not> fst (TCR_EL1_validate s v)"
    with unlocked cons show ?thesis
      by (simp add: try_write_TCR_EL1_def Let_def)
  next
    assume accepted: "fst (TCR_EL1_validate s v)"
    from TCR_EL1_validate_mte_supported [OF accepted]
    show ?thesis
      using unlocked accepted
      by (auto simp add: try_write_TCR_EL1_def tcr_mte_consistent_def
                         tcr_mte_value_supported_def get_tcr_def
                         read_TCR_EL1_def write_TCR_EL1_def
                         read_ID_AA64PFR1_EL1_def set_TCR_EL1_state_def Let_def)
  qed
qed

end
