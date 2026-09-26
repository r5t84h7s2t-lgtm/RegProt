theory Security_Model
  imports Main
begin

text \<open>
  Register-protection security model.
  The obligation structure is inspired by the Clark-Wilson integrity model,
  but the theory exposes only project-level Security Model (SM) names.

  \<^bold>\<open>Mapping to register protection\<close>:
  \<^item> protected state: security-critical registers (SCTLR_EL1, TCR_EL1, ...)
  \<^item> untrusted input: values carried by WRITE_* events
  \<^item> integrity predicates: @{text wellformed} (structural) + @{text consistency} (semantic)
  \<^item> transform events: WRITE_* events, i.e. @{text is_transform}
  \<^item> Security lattice:                partial order @{text sec_leq} over states

  \<^bold>\<open>Core obligations\<close>:
  \<^item> initial integrity predicates:       @{text SM_initial_wf}, @{text SM_initial_cons}
  \<^item> transform events preserve integrity predicates: @{text SM_transform_preserves_wf}, @{text SM_transform_preserves_cons}
  \<^item> Transform-event monotonicity:  @{text SM_transform_mono}
  \<^item> non-transform events readonly:  @{text SM_nontransform_readonly}
\<close>

locale SecurityModel =
  fixes s0          :: 's
  fixes step        :: "'e \<Rightarrow> ('s \<times> 's) set"
  fixes is_transform       :: "'e \<Rightarrow> bool"
  fixes wellformed  :: "'s \<Rightarrow> bool"
  fixes consistency :: "'s \<Rightarrow> bool"
  fixes sec_leq     :: "'s \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sqsubseteq>\<^sub>S\<^sub>M _)" [60, 60] 59)
  assumes
    
    SM_initial_wf   : "wellformed s0" and
    SM_initial_cons : "consistency s0" and
    
    SM_transform_preserves_wf   : "\<lbrakk> is_transform e; (s, s') \<in> step e; wellformed s  \<rbrakk> \<Longrightarrow> wellformed s'"  and
    SM_transform_preserves_cons : "\<lbrakk> is_transform e; (s, s') \<in> step e; consistency s \<rbrakk> \<Longrightarrow> consistency s'" and
    
    SM_transform_mono : "\<lbrakk> is_transform e; (s, s') \<in> step e \<rbrakk> \<Longrightarrow> s \<sqsubseteq>\<^sub>S\<^sub>M s'" and
    
    SM_nontransform_readonly : "\<lbrakk> \<not> is_transform e; (s, s') \<in> step e \<rbrakk> \<Longrightarrow> s = s'" and
    
    sec_refl  : "s \<sqsubseteq>\<^sub>S\<^sub>M s" and
    sec_trans : "\<lbrakk> s \<sqsubseteq>\<^sub>S\<^sub>M t; t \<sqsubseteq>\<^sub>S\<^sub>M r \<rbrakk> \<Longrightarrow> s \<sqsubseteq>\<^sub>S\<^sub>M r"
begin

subsection \<open>Traces, reachability\<close>

primrec run :: "'e list \<Rightarrow> ('s \<times> 's) set" where
  "run []     = Id" |
  "run (a#as) = step a O run as"

definition reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<hookrightarrow> _)" [70,71] 60) where
  "reachable s s' \<equiv> \<exists>as. (s, s') \<in> run as"

definition reachable0 :: "'s \<Rightarrow> bool" where
  "reachable0 s \<equiv> reachable s0 s"

lemma reachable_refl [simp]: "reachable s s"
  using reachable_def
  using run.simps(1) by fastforce

lemma run_transitive:
  "\<lbrakk> (a,b) \<in> run xs; (b,c) \<in> run ys \<rbrakk> \<Longrightarrow> (a,c) \<in> run (xs @ ys)"
proof (induction xs arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  then obtain a' where "(a, a') \<in> step x" and "(a', b) \<in> run xs" by auto
  with Cons.IH Cons.prems(2) show ?case by auto
qed

lemma reachable_trans:
  "\<lbrakk> reachable s t; reachable t r \<rbrakk> \<Longrightarrow> reachable s r"
proof -
  assume "reachable s t" "reachable t r"
  then obtain xs ys where "(s, t) \<in> run xs" "(t, r) \<in> run ys"
    unfolding reachable_def by auto
  with run_transitive have "(s, r) \<in> run (xs @ ys)" by auto
  thus ?thesis unfolding reachable_def by auto
qed

lemma reachable0_step:
  "\<lbrakk> reachable0 s; (s, s') \<in> step e \<rbrakk> \<Longrightarrow> reachable0 s'"
proof -
  assume "reachable0 s" "(s, s') \<in> step e"
  then obtain xs where "(s0, s) \<in> run xs"
    unfolding reachable0_def reachable_def by auto
  from \<open>(s, s') \<in> step e\<close> have "(s, s') \<in> run [e]"
    by (simp add: relcomp.relcompI)
  with \<open>(s0, s) \<in> run xs\<close> run_transitive have "(s0, s') \<in> run (xs @ [e])" by auto
  thus ?thesis unfolding reachable0_def reachable_def by auto
qed

subsection \<open>A useful case-split: every step is either a no-op or a transform event\<close>

lemma step_dichotomy:
  assumes "(s, s') \<in> step e"
  shows   "(is_transform e \<and> (s, s') \<in> step e) \<or> (\<not> is_transform e \<and> s = s')"
  using assms SM_nontransform_readonly by auto

subsection \<open>Per-step preservation of integrity predicates\<close>

lemma step_preserves_wf:
  assumes "(s, s') \<in> step e" and "wellformed s"
  shows   "wellformed s'"
  using assms apply (cases "is_transform e"; simp add: SM_transform_preserves_wf SM_nontransform_readonly)
  using SM_nontransform_readonly by blast

lemma step_preserves_cons:
  assumes "(s, s') \<in> step e" and "consistency s"
  shows   "consistency s'"
  using assms apply (cases "is_transform e"; simp add: SM_transform_preserves_cons SM_nontransform_readonly)
  using SM_nontransform_readonly by blast

lemma step_preserves_mono:
  assumes "(s, s') \<in> step e"
  shows   "s \<sqsubseteq>\<^sub>S\<^sub>M s'"
  using assms apply (cases "is_transform e"; simp add: SM_transform_mono SM_nontransform_readonly sec_refl)
  using SM_nontransform_readonly sec_refl by blast

subsection \<open>Trace preservation of integrity predicates\<close>

lemma run_preserves_wf:
  "\<lbrakk> (s, s') \<in> run as; wellformed s \<rbrakk> \<Longrightarrow> wellformed s'"
proof (induction as arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a as)
  then obtain t where st: "(s, t) \<in> step a" and ts: "(t, s') \<in> run as" by auto
  from step_preserves_wf [OF st Cons.prems(2)] have "wellformed t" .
  with Cons.IH ts show ?case by auto
qed

lemma run_preserves_cons:
  "\<lbrakk> (s, s') \<in> run as; consistency s \<rbrakk> \<Longrightarrow> consistency s'"
proof (induction as arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a as)
  then obtain t where st: "(s, t) \<in> step a" and ts: "(t, s') \<in> run as" by auto
  from step_preserves_cons [OF st Cons.prems(2)] have "consistency t" .
  with Cons.IH ts show ?case by auto
qed

lemma run_preserves_mono:
  "(s, s') \<in> run as \<Longrightarrow> s \<sqsubseteq>\<^sub>S\<^sub>M s'"
proof (induction as arbitrary: s)
  case Nil thus ?case using sec_refl by auto
next
  case (Cons a as)
  then obtain t where st: "(s, t) \<in> step a" and ts: "(t, s') \<in> run as" by auto
  from step_preserves_mono [OF st] have "s \<sqsubseteq>\<^sub>S\<^sub>M t" .
  also from Cons.IH [OF ts] have "t \<sqsubseteq>\<^sub>S\<^sub>M s'" .
  then show ?case using sec_trans
  using \<open>t \<sqsubseteq>\<^sub>S\<^sub>M s'\<close> calculation by blast
qed

subsection \<open>Main Security Model theorems\<close>

definition SM_integrity :: bool where
  "SM_integrity \<equiv> \<forall>s. reachable0 s \<longrightarrow> wellformed s \<and> consistency s"

definition SM_monotonicity :: bool where
  "SM_monotonicity \<equiv> \<forall>s. reachable0 s \<longrightarrow> s0 \<sqsubseteq>\<^sub>S\<^sub>M s"

theorem SM_security_integrity: "SM_integrity"
proof (unfold SM_integrity_def, intro allI impI conjI)
  fix s assume "reachable0 s"
  then obtain as where "(s0, s) \<in> run as"
    unfolding reachable0_def reachable_def by auto
  from run_preserves_wf [OF this SM_initial_wf]
  show "wellformed s" .
next
  fix s assume "reachable0 s"
  then obtain as where "(s0, s) \<in> run as"
    unfolding reachable0_def reachable_def by auto
  from run_preserves_cons [OF this SM_initial_cons]
  show "consistency s" .
qed

theorem SM_security_monotonicity: "SM_monotonicity"
proof (unfold SM_monotonicity_def, intro allI impI)
  fix s assume "reachable0 s"
  then obtain as where "(s0, s) \<in> run as"
    unfolding reachable0_def reachable_def by auto
  from run_preserves_mono [OF this]
  show "s0 \<sqsubseteq>\<^sub>S\<^sub>M s" .
qed

text \<open>
  The paper-facing statement: the system maintains valid protected-register
  state throughout every reachable trace (integrity), and the security posture
  never regresses along any trace (monotonicity).
\<close>
theorem SM_security:
  "SM_integrity \<and> SM_monotonicity"
  by (simp add: SM_security_integrity SM_security_monotonicity)

subsection \<open>Compatibility with the legacy AbstractModel\<close>

text \<open>
  Sanity lemma: the Security Model instance induces everything the old
  @{text AbstractModel} required, so proofs phrased in the old style remain
  meaningful. This is what you use to migrate old lemmas: re-interpret them
  inside this locale.
\<close>

lemma legacy_step_monotonic:
  "\<forall>e s s'. (s, s') \<in> step e \<longrightarrow> s \<sqsubseteq>\<^sub>S\<^sub>M s'"
  using step_preserves_mono by auto

lemma legacy_step_consistency:
  "\<forall>e s s'. (s, s') \<in> step e \<and> consistency s \<longrightarrow> consistency s'"
  using step_preserves_cons by auto

lemma legacy_step_wellformed:
  "\<forall>e s s'. (s, s') \<in> step e \<and> wellformed s \<longrightarrow> wellformed s'"
  using step_preserves_wf by auto

end 

end
