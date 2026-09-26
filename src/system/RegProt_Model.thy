theory RegProt_Model
  imports
    "../framework/Security_Model"
    "../instances/Register_Instances"
    "../machine/Register_Defaults"
begin

text \<open>
  \<^bold>\<open>Global Security Model interpretation.\<close>
  This theory completes the migration path by interpreting @{locale SecurityModel}
  for the concrete RegProt state machine.

  \<^bold>\<open>Mapping\<close>:
  \<^item> protected registers = \{SCTLR_EL1, TCR_EL1, MAIR_EL1, TTBR1_EL1\}
  \<^item> transform events = @{const WRITE_SYSREG} events
  \<^item> untrusted input = the @{typ Reg_Value} payload of @{const WRITE_SYSREG}
  \<^item> integrity predicates = @{text regprot_wf} (structural) + @{text regprot_cons} (semantic)
  \<^item> \<open>sec_leq\<close> = @{text global_sec_leq} (product of per-register orderings)
\<close>


section \<open>Global security ordering\<close>

text \<open>
  The global preorder is the product of the per-register preorders.
  Since TTBR1, TCR, MAIR all use the trivial @{text "reg_leq = True"}, the
  preorder's security content lives in SCTLR's M/WXN/EPAN and MTE-control
  ratchets. TCR's TCMA/MTE capability relation is tracked separately by
  @{text regprot_cons}.
\<close>

definition global_sec_leq :: "State \<Rightarrow> State \<Rightarrow> bool"
  (infix "\<sqsubseteq>\<^sub>R" 50)
where
  "s \<sqsubseteq>\<^sub>R s' \<equiv>
     sctlr_reg_leq (get_sctlr s) (get_sctlr s') \<and>
     ttbr1_reg_leq (get_ttbr1 s) (get_ttbr1 s') \<and>
     tcr_reg_leq   (get_tcr   s) (get_tcr   s') \<and>
     mair_reg_leq  (get_mair  s) (get_mair  s')"

lemma global_sec_leq_refl [simp]: "s \<sqsubseteq>\<^sub>R s"
  by (simp add: global_sec_leq_def sctlr_reg_leq_def
                ttbr1_reg_leq_def tcr_reg_leq_def mair_reg_leq_def)

lemma global_sec_leq_trans:
  "\<lbrakk> s \<sqsubseteq>\<^sub>R t; t \<sqsubseteq>\<^sub>R r \<rbrakk> \<Longrightarrow> s \<sqsubseteq>\<^sub>R r"
  by (auto simp add: global_sec_leq_def sctlr_reg_leq_def
                     ttbr1_reg_leq_def tcr_reg_leq_def mair_reg_leq_def)


section \<open>RegProt step relation\<close>

definition regprot_step :: "Event \<Rightarrow> (State \<times> State) set" where
  "regprot_step e \<equiv> case e of
     WRITE_SYSREG synd val \<Rightarrow>
       {(s, fst (try_write_sys_reg s synd val)) | s. True}
   | READ_SYSREG _  \<Rightarrow> Id
   | READ_IDREG  _  \<Rightarrow> Id"

definition regprot_is_transform :: "Event \<Rightarrow> bool" where
  "regprot_is_transform e \<equiv> case e of WRITE_SYSREG _ _ \<Rightarrow> True | _ \<Rightarrow> False"

lemma regprot_nontransform_readonly:
  "\<lbrakk> \<not> regprot_is_transform e; (s, s') \<in> regprot_step e \<rbrakk> \<Longrightarrow> s = s'"
  by (auto simp add: regprot_step_def regprot_is_transform_def split: Event.splits)


section \<open>Initial state\<close>

definition regprot_s0 :: State where
  "regprot_s0 \<equiv> \<lparr>
     regs_state =
       \<lparr> sys_regs_el1 = default_sys_regs_el1,
         sys_regs_el2 = default_sys_regs_el2,
         ID_regs = default_ID_regs,
         protected_reg_state = default_protected_reg_state \<rparr>,
     sys_config =
       \<lparr> is_aarch64_config = True,
         use_LPAE_config = True \<rparr> \<rparr>"


section \<open>Integrity predicates\<close>

definition regprot_wf :: "State \<Rightarrow> bool" where
  "regprot_wf s \<equiv>
     \<not> EE   (read_SCTLR_EL1 s) \<and>
     \<not> E0E  (read_SCTLR_EL1 s) \<and>
     B17RES0 (read_SCTLR_EL1 s) = 0"

definition regprot_cons :: "State \<Rightarrow> bool" where
  "regprot_cons s \<equiv> ttbr1_consistent s \<and> tcr_mte_consistent s"


section \<open>Independence lemmas: writes only touch their own register\<close>

text \<open>
  Writes to each register leave all others' @{const get_sctlr} unchanged.
  These follow by unfolding: each @{text write_X_EL1} updates only its own
  field in @{text sys_regs_el1}.
\<close>

lemma sctlr_write_others [simp]:
  "get_tcr   (fst (try_write_SCTLR_EL1 s v)) = get_tcr s"
  "get_mair  (fst (try_write_SCTLR_EL1 s v)) = get_mair s"
  "get_ttbr1 (fst (try_write_SCTLR_EL1 s v)) = get_ttbr1 s"
  by (auto simp add: try_write_SCTLR_EL1_def Let_def
                     get_tcr_def get_mair_def get_ttbr1_def
                     read_TCR_EL1_def read_MAIR_EL1_def read_TTBR1_EL1_def
                     write_SCTLR_EL1_def
           split: if_splits)

lemma tcr_write_sctlr [simp]:
  "get_sctlr (fst (try_write_TCR_EL1 s v)) = get_sctlr s"
  by (auto simp add: try_write_TCR_EL1_def Let_def
                     get_sctlr_def read_SCTLR_EL1_def
                     write_TCR_EL1_def set_TCR_EL1_state_def
           split: if_splits)

lemma mair_write_sctlr [simp]:
  "get_sctlr (fst (try_write_MAIR_EL1 s v)) = get_sctlr s"
  by (auto simp add: try_write_MAIR_EL1_def Let_def
                     get_sctlr_def read_SCTLR_EL1_def
                     write_MAIR_EL1_def set_MAIR_EL1_state_def
           split: if_splits)

lemma ttbr1_write_sctlr [simp]:
  "get_sctlr (fst (try_write_TTBR1_EL1 s v)) = get_sctlr s"
  by (auto simp add: try_write_TTBR1_EL1_def Let_def
                     get_sctlr_def read_SCTLR_EL1_def
                     write_TTBR1_EL1_def set_TTBR1_EL1_state_def
                     set_TTBR1_EL1_saved_def
           split: option.splits if_splits)

text \<open>
  All non-protected writes (@{const try_write_ESR_EL1}, @{const try_write_FAR_EL1},
  @{const try_write_CONTEXTIDR_EL1}, @{const try_write_TTBR0_EL1}) also leave
  @{const get_sctlr} unchanged (analogous proofs, omitted for brevity).
\<close>


section \<open>Transform-event monotonicity: SCTLR monotonicity is preserved globally\<close>

text \<open>
  The key monotonicity theorem: every @{const WRITE_SYSREG} event preserves
  or strengthens the @{text global_sec_leq} ordering.

  The proof decomposes by syndrome:
  \<^item> @{const SCTLR_EL1_Syndrome}: uses @{thm sctlr_legacy_state_matches} and
    @{thm sctlr_security_monotone};
  \<^item> @{const TCR_EL1_Syndrome}, @{const MAIR_EL1_Syndrome}, @{const TTBR1_EL1_Syndrome}:
    @{const get_sctlr} is unchanged by the respective @{text "write_*_EL1"};
    the trivial @{text "ttbr1/tcr/mair_reg_leq = True"} closes the remaining conjuncts;
  \<^item> All other syndromes: either discarded or write to non-protected registers;
    all four @{text "get_*"} accessors are unchanged, giving reflexivity.
\<close>

lemma sctlr_write_mono:
  "s \<sqsubseteq>\<^sub>R fst (try_write_SCTLR_EL1 s v)"
proof -
  have eq: "fst (try_write_SCTLR_EL1 s v) = SCTLR.try_write_ad_hoc_modify v s"
    by (rule sctlr_legacy_state_matches)
  
  have sctlr_m: "sctlr_reg_leq (get_sctlr s) (get_sctlr (fst (try_write_SCTLR_EL1 s v)))"
    using sctlr_security_monotone by (simp add: eq)
  show ?thesis
    unfolding global_sec_leq_def
    using sctlr_m
    by (simp add: ttbr1_reg_leq_def tcr_reg_leq_def mair_reg_leq_def)
qed

lemma non_sctlr_write_mono:
  "get_sctlr (fst (try_write_sys_reg s synd val)) = get_sctlr s \<Longrightarrow>
   s \<sqsubseteq>\<^sub>R fst (try_write_sys_reg s synd val)"
  by (simp add: global_sec_leq_def sctlr_reg_leq_def
                ttbr1_reg_leq_def tcr_reg_leq_def mair_reg_leq_def)

lemma try_write_sys_reg_mono:
  "s \<sqsubseteq>\<^sub>R fst (try_write_sys_reg s synd val)"
proof (cases "synd = SCTLR_EL1_Syndrome")
  case True
  thus ?thesis
    by (simp add: try_write_sys_reg_def sctlr_write_mono)
next
  case False
  have unchanged: "get_sctlr (fst (try_write_sys_reg s synd val)) = get_sctlr s"
    using False
    by (cases synd;
        simp add: try_write_sys_reg_def
                  try_write_TCR_EL1_def try_write_MAIR_EL1_def try_write_TTBR1_EL1_def
                  try_write_TTBR0_EL1_def try_write_ESR_EL1_def try_write_FAR_EL1_def
                  try_write_AFSR0_EL1_def try_write_AFSR1_EL1_def try_write_AMAIR_EL1_def
                  try_write_CONTEXTIDR_EL1_def try_write_ACTLR_EL1_def
                  write_TCR_EL1_def write_MAIR_EL1_def write_TTBR1_EL1_def
                  write_TTBR0_EL1_def write_ESR_EL1_def write_FAR_EL1_def
                  write_CONTEXTIDR_EL1_def
                  set_TCR_EL1_state_def set_MAIR_EL1_state_def set_TTBR1_EL1_state_def
                  set_TTBR1_EL1_saved_def
                  get_sctlr_def read_SCTLR_EL1_def Let_def
                  split: option.splits if_splits)
  from unchanged show ?thesis
    by (rule non_sctlr_write_mono)
qed

lemma regprot_transform_mono:
  "\<lbrakk> regprot_is_transform e; (s, s') \<in> regprot_step e \<rbrakk> \<Longrightarrow> s \<sqsubseteq>\<^sub>R s'"
  by (auto simp add: regprot_step_def regprot_is_transform_def try_write_sys_reg_mono
           split: Event.splits)


section \<open>Initial validity and transform event preservation\<close>

lemma regprot_initial_cons: "regprot_cons regprot_s0"
  by (simp add: regprot_cons_def regprot_s0_def ttbr1_consistent_def
                ttbr1_is_locked_def get_TTBR1_EL1_state_def
                get_TTBR1_EL1_saved_def
                tcr_mte_consistent_def tcr_mte_value_supported_def get_tcr_def
                read_TCR_EL1_def read_ID_AA64PFR1_EL1_def
                default_protected_reg_state_def default_sys_regs_el1_def
                default_ID_regs_def default_ID_AA64PFR1_EL1_def
                word64_to_tcr_el1_def test_bit_def)

text \<open>
  Wellformedness of the initial state: @{const default_sys_regs_el1} encodes
  all registers at zero, so EE = False, E0E = False, B17RES0 = 0.
  The proof unfolds @{const word64_to_sctlr_el1} applied to 0:
  @{term "test_bit (0::64 word) n = False"} for any n.
\<close>
lemma regprot_initial_wf: "regprot_wf regprot_s0"
  by (simp add: regprot_wf_def regprot_s0_def default_sys_regs_el1_def
                read_SCTLR_EL1_def word64_to_sctlr_el1_def test_bit_def)

text \<open>
  Helper: when @{const SCTLR_EL1_validate} succeeds, the result value has
  EE = False, E0E = False, and B17RES0 = 0 -- the @{text result} guard enforces this.
\<close>
lemma SCTLR_EL1_validate_structural_ok:
  "fst (SCTLR_EL1_validate s v) \<Longrightarrow>
   \<not> EE  (snd (SCTLR_EL1_validate s v)) \<and>
   \<not> E0E (snd (SCTLR_EL1_validate s v)) \<and>
   B17RES0 (snd (SCTLR_EL1_validate s v)) = 0"
  by (auto simp add: SCTLR_EL1_validate_def Let_def split: if_splits prod.splits)

text \<open>
  Helper: any write to SCTLR either leaves the state unchanged (validate/monotone
  rejects) or writes a value that satisfies @{const regprot_wf}.
\<close>
lemma regprot_wf_preserved_by_sctlr:
  "regprot_wf s \<Longrightarrow> regprot_wf (fst (try_write_SCTLR_EL1 s v))"
proof -
  assume wf: "regprot_wf s"
  show ?thesis
  proof (cases "fst (SCTLR_EL1_validate s v)")
    case False
    hence "fst (try_write_SCTLR_EL1 s v) = s"
      by (simp add: try_write_SCTLR_EL1_def)
    with wf show ?thesis by simp
  next
    case True
    from SCTLR_EL1_validate_structural_ok [OF True]
    have props:
      "\<not> EE  (snd (SCTLR_EL1_validate s v)) \<and>
       \<not> E0E (snd (SCTLR_EL1_validate s v)) \<and>
       B17RES0 (snd (SCTLR_EL1_validate s v)) = 0" .
    show ?thesis
      using True props wf
      by (auto simp add: try_write_SCTLR_EL1_def regprot_wf_def
                         read_SCTLR_EL1_def write_SCTLR_EL1_def
                         Let_def split: if_splits)
  qed
qed

text \<open>
  Independence: every non-SCTLR syndrome leaves @{const read_SCTLR_EL1} unchanged.
  Each @{text write_X_EL1} updates only the X field of @{text sys_regs_el1};
  each @{text set_X_EL1_state} updates only @{text protected_reg_state} -- neither
  touches the @{text SCTLR_EL1} field.
\<close>
lemma try_write_sys_reg_sctlr_unchanged:
  "synd \<noteq> SCTLR_EL1_Syndrome \<Longrightarrow>
   read_SCTLR_EL1 (fst (try_write_sys_reg s synd val)) = read_SCTLR_EL1 s"
  by (cases synd;
      simp add: try_write_sys_reg_def
                try_write_TCR_EL1_def try_write_MAIR_EL1_def try_write_TTBR1_EL1_def
                try_write_TTBR0_EL1_def try_write_ESR_EL1_def try_write_FAR_EL1_def
                try_write_AFSR0_EL1_def try_write_AFSR1_EL1_def try_write_AMAIR_EL1_def
                try_write_CONTEXTIDR_EL1_def try_write_ACTLR_EL1_def
                write_TCR_EL1_def write_MAIR_EL1_def write_TTBR1_EL1_def
                write_TTBR0_EL1_def write_ESR_EL1_def write_FAR_EL1_def
                write_CONTEXTIDR_EL1_def
                set_TCR_EL1_state_def set_MAIR_EL1_state_def set_TTBR1_EL1_state_def
                set_TTBR1_EL1_saved_def
                read_SCTLR_EL1_def Let_def
                split: option.splits if_splits)

text \<open>
  Independence: every non-TTBR1 syndrome leaves the TTBR1 lock state, saved
  reference, and current value unchanged.
\<close>
lemma try_write_sys_reg_ttbr1_unchanged:
  "synd \<noteq> TTBR1_EL1_Syndrome \<Longrightarrow>
   get_TTBR1_EL1_state (fst (try_write_sys_reg s synd val)) = get_TTBR1_EL1_state s \<and>
   get_TTBR1_EL1_saved (fst (try_write_sys_reg s synd val)) = get_TTBR1_EL1_saved s \<and>
   read_TTBR1_EL1 (fst (try_write_sys_reg s synd val)) = read_TTBR1_EL1 s"
  by (cases synd;
      simp add: try_write_sys_reg_def
                try_write_SCTLR_EL1_def try_write_TCR_EL1_def try_write_MAIR_EL1_def
                try_write_TTBR0_EL1_def try_write_ESR_EL1_def try_write_FAR_EL1_def
                try_write_AFSR0_EL1_def try_write_AFSR1_EL1_def try_write_AMAIR_EL1_def
                try_write_CONTEXTIDR_EL1_def try_write_ACTLR_EL1_def
                write_SCTLR_EL1_def write_TCR_EL1_def write_MAIR_EL1_def
                write_TTBR0_EL1_def write_ESR_EL1_def write_FAR_EL1_def
                write_CONTEXTIDR_EL1_def
                set_TCR_EL1_state_def set_MAIR_EL1_state_def
                get_TTBR1_EL1_state_def get_TTBR1_EL1_saved_def
                read_TTBR1_EL1_def Let_def
                split: if_splits)

lemma try_write_sys_reg_ttbr1_locked_reference:
  assumes "ttbr1_is_locked s"
  shows "ttbr1_is_locked (fst (try_write_sys_reg s synd val)) \<and>
         get_TTBR1_EL1_saved (fst (try_write_sys_reg s synd val)) =
           get_TTBR1_EL1_saved s"
  using assms
  by (cases synd;
      auto simp add: try_write_sys_reg_def ttbr1_is_locked_def
                     try_write_SCTLR_EL1_def try_write_TCR_EL1_def
                     try_write_MAIR_EL1_def try_write_TTBR1_EL1_def
                     try_write_TTBR0_EL1_def try_write_ESR_EL1_def
                     try_write_FAR_EL1_def try_write_AFSR0_EL1_def
                     try_write_AFSR1_EL1_def try_write_AMAIR_EL1_def
                     try_write_CONTEXTIDR_EL1_def try_write_ACTLR_EL1_def
                     write_SCTLR_EL1_def write_TCR_EL1_def write_MAIR_EL1_def
                     write_TTBR1_EL1_def write_TTBR0_EL1_def write_ESR_EL1_def
                     write_FAR_EL1_def write_CONTEXTIDR_EL1_def
                     set_TCR_EL1_state_def set_MAIR_EL1_state_def
                     set_TTBR1_EL1_state_def set_TTBR1_EL1_saved_def
                     get_TTBR1_EL1_state_def get_TTBR1_EL1_saved_def Let_def
              split: option.splits if_splits)

text \<open>
  Independence for the TCR MTE capability invariant: a non-TCR write changes
  neither TCR_EL1 nor the read-only ID_AA64PFR1_EL1 capability value.
\<close>
lemma try_write_sys_reg_tcr_mte_unchanged:
  "synd \<noteq> TCR_EL1_Syndrome \<Longrightarrow>
   get_tcr (fst (try_write_sys_reg s synd val)) = get_tcr s \<and>
   read_ID_AA64PFR1_EL1 (fst (try_write_sys_reg s synd val)) =
     read_ID_AA64PFR1_EL1 s"
  by (cases synd;
      simp add: try_write_sys_reg_def
                try_write_SCTLR_EL1_def try_write_MAIR_EL1_def try_write_TTBR1_EL1_def
                try_write_TTBR0_EL1_def try_write_ESR_EL1_def try_write_FAR_EL1_def
                try_write_AFSR0_EL1_def try_write_AFSR1_EL1_def try_write_AMAIR_EL1_def
                try_write_CONTEXTIDR_EL1_def try_write_ACTLR_EL1_def
                write_SCTLR_EL1_def write_MAIR_EL1_def write_TTBR1_EL1_def
                write_TTBR0_EL1_def write_ESR_EL1_def write_FAR_EL1_def
                write_CONTEXTIDR_EL1_def
                set_MAIR_EL1_state_def set_TTBR1_EL1_state_def
                set_TTBR1_EL1_saved_def
                get_tcr_def read_TCR_EL1_def read_ID_AA64PFR1_EL1_def Let_def
                split: option.splits if_splits)

text \<open>
  Integrity-predicate preservation (wellformedness): @{const regprot_wf} is preserved by every
  @{const WRITE_SYSREG} event.  For the SCTLR syndrome we use
  @{thm regprot_wf_preserved_by_sctlr}; for all other syndromes
  @{const read_SCTLR_EL1} is unchanged by @{thm try_write_sys_reg_sctlr_unchanged}.
\<close>
lemma regprot_transform_preserves_wf:
  "\<lbrakk> regprot_is_transform e; (s, s') \<in> regprot_step e; regprot_wf s \<rbrakk> \<Longrightarrow> regprot_wf s'"
proof -
  assume tp: "regprot_is_transform e" and step: "(s, s') \<in> regprot_step e" and wf: "regprot_wf s"
  from tp step obtain synd val where
    s'_eq: "s' = fst (try_write_sys_reg s synd val)"
    by (auto simp add: regprot_is_transform_def regprot_step_def split: Event.splits)
  show ?thesis
  proof (cases "synd = SCTLR_EL1_Syndrome")
    case True
    with s'_eq have eq: "s' = fst (try_write_SCTLR_EL1 s (word64_to_sctlr_el1 val))"
      by (simp add: try_write_sys_reg_def)
    with regprot_wf_preserved_by_sctlr [OF wf] show ?thesis
      by simp
  next
    case False
    from try_write_sys_reg_sctlr_unchanged [OF False]
    have "read_SCTLR_EL1 s' = read_SCTLR_EL1 s"
      by (simp add: s'_eq)
    with wf show ?thesis
      by (simp add: regprot_wf_def)
  qed
qed

text \<open>
  Integrity-predicate preservation (consistency) has two independent parts.
  TTBR1 consistency follows from its locale theorem or accessor independence.
  TCR MTE capability consistency follows from
  @{thm tcr_handler_mte_consistent}; non-TCR events preserve both TCR and the
  read-only feature register.
\<close>
lemma regprot_transform_preserves_cons:
  "\<lbrakk> regprot_is_transform e; (s, s') \<in> regprot_step e; regprot_cons s \<rbrakk> \<Longrightarrow> regprot_cons s'"
proof -
  assume tp: "regprot_is_transform e" and step: "(s, s') \<in> regprot_step e" and cons: "regprot_cons s"
  from tp step obtain synd val where
    s'_eq: "s' = fst (try_write_sys_reg s synd val)"
    by (auto simp add: regprot_is_transform_def regprot_step_def split: Event.splits)
  have ttbr1_cons: "ttbr1_consistent s'"
  proof (cases "synd = TTBR1_EL1_Syndrome")
    case True
    with s'_eq have "s' = TTBR1.try_write_allow (word64_to_ttbr1_el1 val) s"
      using ttbr1_legacy_state_matches [of s "word64_to_ttbr1_el1 val"]
      by (simp add: try_write_sys_reg_def)
    with cons show ?thesis
      by (simp add: regprot_cons_def ttbr1_consistent_preserved)
  next
    case False
    from try_write_sys_reg_ttbr1_unchanged [OF False]
    have "get_TTBR1_EL1_state s' = get_TTBR1_EL1_state s \<and>
          get_TTBR1_EL1_saved s' = get_TTBR1_EL1_saved s \<and>
          read_TTBR1_EL1 s' = read_TTBR1_EL1 s"
      by (simp add: s'_eq)
    with cons show ?thesis
      by (simp add: regprot_cons_def ttbr1_consistent_def ttbr1_is_locked_def)
  qed
  have tcr_mte_cons: "tcr_mte_consistent s'"
  proof (cases "synd = TCR_EL1_Syndrome")
    case True
    with s'_eq have
      "s' = fst (try_write_TCR_EL1 s (word64_to_tcr_el1 val))"
      by (simp add: try_write_sys_reg_def)
    with cons show ?thesis
      by (simp add: regprot_cons_def tcr_handler_mte_consistent)
  next
    case False
    from try_write_sys_reg_tcr_mte_unchanged [OF False]
    have "get_tcr s' = get_tcr s \<and>
          read_ID_AA64PFR1_EL1 s' = read_ID_AA64PFR1_EL1 s"
      by (simp add: s'_eq)
    with cons show ?thesis
      by (simp add: regprot_cons_def tcr_mte_consistent_def
                    tcr_mte_value_supported_def)
  qed
  show ?thesis
    using ttbr1_cons tcr_mte_cons
    by (simp add: regprot_cons_def)
qed


section \<open>The global interpretation\<close>

text \<open>
  With all obligations in hand, we can interpret @{locale SecurityModel}
  and obtain the Security Model theorems for the concrete RegProt system.
\<close>

interpretation RegProt: SecurityModel
  regprot_s0 regprot_step regprot_is_transform regprot_wf regprot_cons global_sec_leq
  apply unfold_locales
       apply (rule regprot_initial_wf)
      apply (rule regprot_initial_cons)
     apply (blast intro: regprot_transform_preserves_wf)
    apply (blast intro: regprot_transform_preserves_cons)
   apply (blast intro: regprot_transform_mono)
  apply (blast intro: regprot_nontransform_readonly)
  apply simp
  apply (blast intro: global_sec_leq_trans)
  done

text \<open>
  The main Security Model theorems, now instantiated for RegProt:
\<close>

thm RegProt.SM_security_integrity
thm RegProt.SM_security_monotonicity

corollary regprot_reachable_ttbr1_consistent:
  "RegProt.reachable0 s \<Longrightarrow> ttbr1_consistent s"
  using RegProt.SM_security_integrity
  by (auto simp add: RegProt.SM_integrity_def regprot_cons_def)

text \<open>
  \<^bold>\<open>Main corollary\<close>: every reachable RegProt state is monotone above @{const regprot_s0}
  in the global security ordering. In particular, M, WXN, EPAN, ATA, ATA0,
  and the two tag-check reporting predicates never regress once enabled.
\<close>

corollary regprot_security_monotone:
  "RegProt.reachable0 s \<Longrightarrow> regprot_s0 \<sqsubseteq>\<^sub>R s"
  using RegProt.SM_security_monotonicity
  unfolding RegProt.SM_monotonicity_def
  by auto

corollary regprot_M_never_cleared:
  "\<lbrakk> RegProt.reachable0 s; M (read_SCTLR_EL1 regprot_s0) \<rbrakk>
   \<Longrightarrow> M (read_SCTLR_EL1 s)"
  using regprot_security_monotone
  by (simp add: global_sec_leq_def sctlr_reg_leq_def get_sctlr_def)

end
