section {*FUNCTION\_\_CFG\_TRIM*}
theory
  FUNCTION__CFG_TRIM

imports
  PRJ_12_04_06_05__ENTRY

begin

definition F_CFG_TRIM__SpecInput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TRIM__SpecInput G \<equiv>
  valid_cfg G"

definition F_CFG_TRIM__SpecOutput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_CFG_TRIM__SpecOutput Gi Go \<equiv>
  case Go of
    None \<Rightarrow> cfgLM.marked_language Gi = {}
    | Some Go \<Rightarrow>
      valid_cfg Go
      \<and> cfg_sub Go Gi
      \<and> cfgLM.marked_language Go = cfgLM.marked_language Gi
      \<and> cfgLM.initial_marking_derivations Go = cfgLM.initial_marking_derivations Gi
      \<and> cfg_nonterminals Go = cfgLM_language_relevant_nonterminals Gi
      \<and> cfg_nonterminals Go = cfgLM_accessible_nonterminals Go \<inter> cfgSTD_Nonblockingness_nonterminals Go
      \<and> cfg_nonterminals Go = cfgLM_language_relevant_nonterminals Go
      \<and> cfg_productions Go = cfgLM_language_relevant_productions Go
      \<and> cfgLM.marked_language Go \<noteq> {}"

theorem F_CFG_TRIM__SOUND: "
  F_CFG_TRIM__SpecInput G
  \<Longrightarrow> F_CFG_TRIM__SpecOutput G (F_CFG_TRIM G)"
  apply(simp add: F_CFG_TRIM__SpecOutput_def F_CFG_TRIM__SpecInput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_CFG_EB__SOUND)
   apply(simp add: F_CFG_EB__SpecInput_def)
  apply(simp add: F_CFG_TRIM_def)
  apply(simp add: F_CFG_EB__SpecOutput_def)
  apply(case_tac "F_CFG_EB G")
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac G')
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G'" in SOUND_FUN_CFGLMACX_STD)
   apply(simp add: F_CFG_EASTD__SpecInput_def)
  apply(simp add: F_CFG_EASTD__SpecOutput_def)
  apply(rule conjI)
   apply(rule cfg_sub__trans)
    apply(force)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(subgoal_tac "cfgLM_accessible_nonterminals G' \<subseteq> cfg_nonterminals G'")
   prefer 2
   apply(simp add: cfgLM_accessible_nonterminals_def)
   apply(force)
  apply(subgoal_tac "cfgLM_accessible_nonterminals G \<subseteq> cfg_nonterminals G")
   prefer 2
   apply(simp add: cfgLM_accessible_nonterminals_def)
   apply(force)
  apply(subgoal_tac "cfgSTD_Nonblockingness_nonterminals G \<subseteq> cfg_nonterminals G")
   prefer 2
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(force)
  apply(subgoal_tac "cfgSTD_Nonblockingness_nonterminals G' \<subseteq> cfg_nonterminals G'")
   prefer 2
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G2.0="G" in cfg_sub_preserves_cfgLM_accessible_nonterminals)
     prefer 2
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G2.0="G'" in cfg_sub_preserves_cfgLM_accessible_nonterminals)
     prefer 2
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_CFG_EB__SOUND)
   apply(simp add: F_CFG_EB__SpecInput_def)
  apply(simp add: F_CFG_TRIM_def)
  apply(simp add: F_CFG_EB__SpecOutput_def)
  apply(clarsimp)
  apply(rule_tac t="cfgSTD_Nonblockingness_nonterminals G" and s="cfgSTD_Nonblockingness_nonterminals G'" in ssubst)
   apply(force)
  apply(rule_tac t="cfgLM_language_relevant_nonterminals G" and s="cfgLM_language_relevant_nonterminals G'" in ssubst)
   apply(rule F_CFG_EB_preserves_cfgLM_language_relevant_nonterminals)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_in_cfgSTD_Nonblockingness_nonterminals_grammar)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfg_equal_trim_by_cfg_sub_and_equal_marked_language: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_events G1 = cfg_events G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM.marked_language G1 = cfgLM.marked_language G2
  \<Longrightarrow> cfgLM.initial_marking_derivations G2 = cfgLM.initial_marking_derivations G1
  \<Longrightarrow> F_CFG_TRIM G1 = F_CFG_TRIM G2"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G1.0="G1" and ?G2.0="G2" in cfg_cfgLM_initial_marking_derivations_equal_implies_cfgLM_language_relevant_nonterminals_equal)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G1.0="G1" and ?G2.0="G2" in cfg_cfgLM_initial_marking_derivations_equal_implies_cfgLM_language_relevant_productions_equal)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "cfgLM.initial_marking_derivations G2 = cfgLM.initial_marking_derivations G1")
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G1" in F_CFG_TRIM__SOUND)
   apply(simp add: F_CFG_TRIM__SpecInput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G2" in F_CFG_TRIM__SOUND)
   apply(simp add: F_CFG_TRIM__SpecInput_def)
  apply(simp add: F_CFG_TRIM__SpecOutput_def)
  apply(case_tac "F_CFG_TRIM G1")
   apply(clarsimp)
   apply(case_tac "F_CFG_TRIM G2")
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac "F_CFG_TRIM G2")
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac GX1 GX2)
  apply(subgoal_tac "cfgLM_language_relevant_nonterminals GX2 =
       cfgLM_language_relevant_nonterminals G2")
   prefer 2
   apply(rule_tac t="cfgLM_language_relevant_nonterminals GX2" and s="cfgLM_accessible_nonterminals GX2 \<inter> cfgSTD_Nonblockingness_nonterminals GX2" in ssubst)
    apply (metis cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals)
   apply(force)
  apply(subgoal_tac "cfgLM_language_relevant_nonterminals GX1 =
       cfgLM_language_relevant_nonterminals G1")
   prefer 2
   apply(rule_tac t="cfgLM_language_relevant_nonterminals GX1" and s="cfgLM_accessible_nonterminals GX1 \<inter> cfgSTD_Nonblockingness_nonterminals GX1" in ssubst)
    apply (metis cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals)
   apply(force)
  apply(subgoal_tac "cfg_events GX1 = cfg_events GX2")
   prefer 2
   apply(simp add: F_CFG_TRIM_def)
   apply(simp add: cfg_sub_def)
   apply(case_tac "F_CFG_EB G1")
    apply(force)
   apply(clarsimp)
   apply(rename_tac GX1)
   apply(case_tac "F_CFG_EB G2")
    apply(force)
   apply(clarsimp)
   apply(rename_tac GX2)
   apply(simp add: F_CFG_EB_def F_CFG_EASTD_def Let_def)
   apply(case_tac "cfg_initial G2 \<in> F_CFG_EB__fp G1 {}")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac "cfg_initial G2 \<in> F_CFG_EB__fp G2 {}")
    prefer 2
    apply(force)
   apply(clarsimp)
  apply(thin_tac "X \<noteq> {}" for X)
  apply(thin_tac "cfgLM.marked_language X = Y" for X Y)
  apply(thin_tac "cfgLM.marked_language X = Y" for X Y)
  apply(thin_tac "cfgLM.marked_language X = Y" for X Y)
  apply(thin_tac "F_CFG_TRIM Y = Some X" for X Y)
  apply(thin_tac "F_CFG_TRIM Y = Some X" for X Y)
  apply(subgoal_tac "cfg_nonterminals GX1 = cfg_nonterminals GX2")
   prefer 2
   apply(force)
  apply(subgoal_tac "cfg_productions GX1 = cfg_productions GX2")
   apply(case_tac GX1)
   apply(case_tac GX2)
   apply(simp add: cfg_sub_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G1.0="G1" and ?G2.0="GX1" in cfg_cfgLM_initial_marking_derivations_equal_implies_cfgLM_language_relevant_productions_equal)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G1.0="G2" and ?G2.0="GX2" in cfg_cfgLM_initial_marking_derivations_equal_implies_cfgLM_language_relevant_productions_equal)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end

