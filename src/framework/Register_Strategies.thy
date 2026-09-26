theory Register_Strategies
  imports Main
begin

text \<open>
  This theory defines reusable Isabelle locales for register-protection
  strategies.  The public names follow the policy taxonomy used by the paper:

  \<^item> @{text AdHocModify}: writes are accepted only after register-specific
    validation and monotonicity checks.
  \<^item> @{text Allow}: writes are allowed subject to validation or a dynamic
    pass predicate.
  \<^item> @{text PostBootLock}: a specialization of @{text Allow} where the
    register becomes immutable after its first valid initialization.
  \<^item> @{text Discard}: writes are ignored and therefore preserve every
    state predicate.

  @{text RegisterAccess} is the shared read/write accessor layer used by all
  four strategies.
\<close>


section \<open>RegisterAccess: basic register accessors\<close>

locale RegisterAccess =
  fixes get_val :: "'s \<Rightarrow> 'v"
  fixes set_val :: "'v \<Rightarrow> 's \<Rightarrow> 's"
  assumes get_set : "get_val (set_val v s) = v"
  assumes set_get : "set_val (get_val s) s = s"
  assumes set_set : "set_val v\<^sub>2 (set_val v\<^sub>1 s) = set_val v\<^sub>2 s"
begin

definition reg_read :: "'s \<Rightarrow> 'v \<times> 's" where
  "reg_read s \<equiv> (get_val s, s)"

definition reg_write :: "'v \<Rightarrow> 's \<Rightarrow> 's" where
  "reg_write v s \<equiv> set_val v s"

lemma reg_read_observational: "snd (reg_read s) = s"
  by (simp add: reg_read_def)

lemma reg_write_read:
  "get_val (reg_write v s) = v"
  by (simp add: reg_write_def get_set)

end


section \<open>AdHocModify: register-specific monotone modification\<close>

text \<open>
  The Ad-hoc Modify strategy captures registers such as SCTLR_EL1 whose handler
  performs field-specific validation and rejects security-weakening updates.
\<close>

locale AdHocModify = RegisterAccess get_val set_val
  for get_val :: "'s \<Rightarrow> 'v"
  and set_val :: "'v \<Rightarrow> 's \<Rightarrow> 's" +
  fixes validate :: "'v \<Rightarrow> 's \<Rightarrow> 'v option"
  fixes reg_leq  :: "'v \<Rightarrow> 'v \<Rightarrow> bool"  ("(_ \<preceq>\<^sub>v _)" [60, 60] 59)
  assumes
    reg_leq_refl  : "v \<preceq>\<^sub>v v" and
    reg_leq_trans : "\<lbrakk> v\<^sub>1 \<preceq>\<^sub>v v\<^sub>2; v\<^sub>2 \<preceq>\<^sub>v v\<^sub>3 \<rbrakk> \<Longrightarrow> v\<^sub>1 \<preceq>\<^sub>v v\<^sub>3" and
    validate_mono : "validate v s = Some v' \<Longrightarrow> get_val s \<preceq>\<^sub>v v'"
begin

definition try_write_ad_hoc_modify :: "'v \<Rightarrow> 's \<Rightarrow> 's" where
  "try_write_ad_hoc_modify v s \<equiv>
     (case validate v s of
        Some v' \<Rightarrow> set_val v' s
      | None    \<Rightarrow> s)"

theorem try_write_ad_hoc_modify_reg_leq:
  "get_val s \<preceq>\<^sub>v get_val (try_write_ad_hoc_modify v s)"
  by (auto simp add: try_write_ad_hoc_modify_def reg_leq_refl get_set validate_mono
           split: option.splits)

lemma try_write_ad_hoc_modify_rejected:
  "validate v s = None \<Longrightarrow> try_write_ad_hoc_modify v s = s"
  by (simp add: try_write_ad_hoc_modify_def)

lemma try_write_ad_hoc_modify_accepted:
  "validate v s = Some v' \<Longrightarrow> try_write_ad_hoc_modify v s = set_val v' s"
  by (simp add: try_write_ad_hoc_modify_def)

lemma try_write_ad_hoc_modify_preserves:
  assumes inv_validate:
    "\<And>v v' s. validate v s = Some v' \<Longrightarrow> P s \<Longrightarrow> P (set_val v' s)"
  and "P s"
  shows "P (try_write_ad_hoc_modify v s)"
  using assms by (auto simp: try_write_ad_hoc_modify_def split: option.splits)

end


section \<open>Allow: validated writes are allowed\<close>

text \<open>
  The Allow strategy covers register handlers where writes may proceed if they
  pass validation or a dynamic compatibility predicate.  The optional lock
  state is part of the concrete handler interface: while unlocked, a write must
  pass @{text validate}; once locked, a write must pass @{text pass}.  The first
  successful unlocked write records the accepted value as the future reference
  by applying @{text lock_down}.
\<close>

locale Allow = RegisterAccess get_val set_val
  for get_val :: "'s \<Rightarrow> 'v"
  and set_val :: "'v \<Rightarrow> 's \<Rightarrow> 's" +
  fixes is_locked :: "'s \<Rightarrow> bool"
  fixes pass      :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  fixes validate  :: "'v \<Rightarrow> 's \<Rightarrow> 'v option"
  fixes reg_leq   :: "'v \<Rightarrow> 'v \<Rightarrow> bool"  ("(_ \<preceq>\<^sub>r _)" [60, 60] 59)
  fixes lock_down :: "'s \<Rightarrow> 's"
  assumes
    reg_leq_refl  : "v \<preceq>\<^sub>r v" and
    reg_leq_trans : "\<lbrakk> v\<^sub>1 \<preceq>\<^sub>r v\<^sub>2; v\<^sub>2 \<preceq>\<^sub>r v\<^sub>3 \<rbrakk> \<Longrightarrow> v\<^sub>1 \<preceq>\<^sub>r v\<^sub>3" and
    pass_mono     : "pass v s \<Longrightarrow> get_val s \<preceq>\<^sub>r v" and
    validate_mono : "validate v s = Some v' \<Longrightarrow> get_val s \<preceq>\<^sub>r v'" and
    lock_down_get      : "get_val (lock_down s) = get_val s" and
    lock_down_is_locked: "is_locked (lock_down s)" and
    lock_down_locked_id: "is_locked s \<Longrightarrow> lock_down s = s"
begin

definition try_write_allow :: "'v \<Rightarrow> 's \<Rightarrow> 's" where
  "try_write_allow v s \<equiv>
      if is_locked s then
        (if pass v s then set_val v s else s)
      else
        (case validate v s of
           Some v' \<Rightarrow> lock_down (set_val v' s)
         | None    \<Rightarrow> s)"

theorem try_write_allow_reg_leq:
  "get_val s \<preceq>\<^sub>r get_val (try_write_allow v s)"
  by (auto simp add: try_write_allow_def reg_leq_refl get_set
                     lock_down_get pass_mono validate_mono
           split: option.splits)

lemma try_write_allow_locked_rejected:
  "\<lbrakk> is_locked s; \<not> pass v s \<rbrakk> \<Longrightarrow> try_write_allow v s = s"
  by (simp add: try_write_allow_def)

lemma try_write_allow_locked_accepted:
  "\<lbrakk> is_locked s; pass v s \<rbrakk> \<Longrightarrow> try_write_allow v s = set_val v s"
  by (simp add: try_write_allow_def)

lemma try_write_allow_unlocked_accepted:
  "\<lbrakk> \<not> is_locked s; validate v s = Some v' \<rbrakk>
     \<Longrightarrow> try_write_allow v s = lock_down (set_val v' s)"
  by (simp add: try_write_allow_def)

lemma try_write_allow_unlocked_rejected:
  "\<lbrakk> \<not> is_locked s; validate v s = None \<rbrakk>
     \<Longrightarrow> try_write_allow v s = s"
  by (simp add: try_write_allow_def)

lemma try_write_allow_preserves:
  assumes inv_pass     : "\<And>v s. is_locked s \<Longrightarrow> pass v s \<Longrightarrow> P s \<Longrightarrow> P (set_val v s)"
  and     inv_validate : "\<And>v v' s. \<not> is_locked s \<Longrightarrow> validate v s = Some v'
                           \<Longrightarrow> P s \<Longrightarrow> P (set_val v' s)"
  and     inv_lockdown : "\<And>s. P s \<Longrightarrow> P (lock_down s)"
  and     "P s"
  shows   "P (try_write_allow v s)"
  using assms by (auto simp: try_write_allow_def split: option.splits)

end


section \<open>PostBootLock: immutable after valid initialization\<close>

text \<open>
  Post-boot Lock is the strict lock-after-initialization strategy: the first
  valid write may establish the register value, but once the register is
  locked, no later write is admitted.
\<close>

locale PostBootLock = Allow get_val set_val is_locked pass validate reg_leq lock_down
  for get_val :: "'s \<Rightarrow> 'v"
  and set_val :: "'v \<Rightarrow> 's \<Rightarrow> 's"
  and is_locked :: "'s \<Rightarrow> bool"
  and pass      :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  and validate  :: "'v \<Rightarrow> 's \<Rightarrow> 'v option"
  and reg_leq   :: "'v \<Rightarrow> 'v \<Rightarrow> bool"  ("(_ \<preceq>\<^sub>r _)" [60, 60] 59)
  and lock_down :: "'s \<Rightarrow> 's"
  +
  assumes pass_never: "\<not> pass v s"
begin

definition try_write_post_boot_lock :: "'v \<Rightarrow> 's \<Rightarrow> 's" where
  "try_write_post_boot_lock v s \<equiv> try_write_allow v s"

lemma try_write_post_boot_lock_locked_rejected:
  "is_locked s \<Longrightarrow> try_write_post_boot_lock v s = s"
  by (simp add: try_write_post_boot_lock_def try_write_allow_def pass_never)

lemma try_write_post_boot_lock_unlocked_accepted:
  "\<lbrakk> \<not> is_locked s; validate v s = Some v' \<rbrakk>
     \<Longrightarrow> try_write_post_boot_lock v s = lock_down (set_val v' s)"
  by (simp add: try_write_post_boot_lock_def try_write_allow_unlocked_accepted)

lemma try_write_post_boot_lock_unlocked_rejected:
  "\<lbrakk> \<not> is_locked s; validate v s = None \<rbrakk>
     \<Longrightarrow> try_write_post_boot_lock v s = s"
  by (simp add: try_write_post_boot_lock_def try_write_allow_unlocked_rejected)

lemma try_write_post_boot_lock_reg_leq:
  "get_val s \<preceq>\<^sub>r get_val (try_write_post_boot_lock v s)"
  by (simp add: try_write_post_boot_lock_def try_write_allow_reg_leq)

lemma try_write_post_boot_lock_preserves:
  assumes inv_validate : "\<And>v v' s. \<not> is_locked s \<Longrightarrow> validate v s = Some v'
                           \<Longrightarrow> P s \<Longrightarrow> P (set_val v' s)"
  and     inv_lockdown : "\<And>s. P s \<Longrightarrow> P (lock_down s)"
  and     "P s"
  shows   "P (try_write_post_boot_lock v s)"
  unfolding try_write_post_boot_lock_def
proof (rule try_write_allow_preserves)
  fix w s'
  assume "is_locked s'" "pass w s'" "P s'"
  thus "P (set_val w s')"
    using pass_never by blast
next
  fix w w' s'
  assume "\<not> is_locked s'" "validate w s' = Some w'" "P s'"
  thus "P (set_val w' s')"
    using inv_validate by blast
next
  fix s'
  assume "P s'"
  thus "P (lock_down s')"
    using inv_lockdown by blast
next
  show "P s" by fact
qed

end


section \<open>Discard: writes are silently discarded\<close>

locale Discard = RegisterAccess get_val set_val
  for get_val :: "'s \<Rightarrow> 'v"
  and set_val :: "'v \<Rightarrow> 's \<Rightarrow> 's"
begin

definition discard_write :: "'v \<Rightarrow> 's \<Rightarrow> 's" where
  "discard_write v s \<equiv> s"

lemma discard_write_unchanged [simp]: "discard_write v s = s"
  by (simp add: discard_write_def)

lemma discard_write_preserves_any: "P s \<Longrightarrow> P (discard_write v s)"
  by simp

end


text \<open>
  The locale hierarchy above is intentionally kept free of concrete examples so
  that importing theories only see reusable register-protection rules.
\<close>

end
