theory Register_Instances
  imports
    SCTLR
    TCR
    MAIR
    TTBR0
    TTBR1
    ESR
    FAR
    CONTEXTIDR
    AFSR0
    AFSR1
    AMAIR
    ACTLR
begin

text \<open>
  \<^bold>\<open>Concrete register coverage.\<close>

  The paper's protection table contains eleven registers:

  \<^item> Ad-hoc Modify: SCTLR_EL1.
  \<^item> Post-boot Lock: TCR_EL1 and MAIR_EL1.
  \<^item> Allow: TTBR0_EL1, TTBR1_EL1, ESR_EL1, FAR_EL1, and CONTEXTIDR_EL1.
  \<^item> Discard: AFSR0_EL1, AFSR1_EL1, and AMAIR_EL1.

  ACTLR_EL1 is a twelfth register handled by the functional dispatcher. Its
  default implementation-defined behavior is covered separately by the
  Discard interpretation in @{text ACTLR}, but it is not counted as one of
  the eleven registers claimed by the paper.

  Every listed register has its own theory so its rationale, glue definitions,
  handler correspondence, and preservation result can be inspected without
  relying on a grouped proof file.
\<close>

end
