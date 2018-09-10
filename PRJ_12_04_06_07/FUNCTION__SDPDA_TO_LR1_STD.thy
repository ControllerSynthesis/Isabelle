section {*FUNCTION\_\_SDPDA\_TO\_LR1\_STD*}
theory
  FUNCTION__SDPDA_TO_LR1_STD

imports
  PRJ_12_04_06_07__ENTRY

begin

definition F_SDPDA_TO_LR1_STD__SpecInput :: "
  ('nonterminal, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_LR1_STD__SpecInput G \<equiv>
  valid_simple_dpda G
  \<and> \<not> duplicate_marking G"

definition F_SDPDA_TO_LR1_STD__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_LR1_STD__SpecOutput Gi Go \<equiv>
  case Go of
    None \<Rightarrow> epdaS.marked_language Gi = {}
    | Some Go \<Rightarrow>
      valid_cfg Go
      \<and> cfgLM.marked_language Go = epdaS.marked_language Gi
      \<and> cfg_LRk Go (Suc 0)"

theorem F_SDPDA_TO_LR1_STD__SOUND: "
  F_SDPDA_TO_LR1_STD__SpecInput G
  \<Longrightarrow> F_SDPDA_TO_LR1_STD__SpecOutput G (F_SDPDA_TO_LR1_STD G)"
  apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_SDPDA_TO_CFG_STD__SOUND)
   apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="F_SDPDA_TO_CFG_STD G" in F_CFG_TRIM__SOUND)
   apply(simp add: F_CFG_TRIM__SpecInput_def F_SDPDA_TO_CFG_STD__SpecOutput_def)
  apply(case_tac "F_SDPDA_TO_LR1_STD G")
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_LR1_STD_def)
   apply(simp add: F_CFG_TRIM__SpecOutput_def F_CFG_TRIM__SpecInput_def F_SDPDA_TO_CFG_STD__SpecOutput_def)
   apply (metis CFG_lang_lm_lang_equal)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_LR1_STD_def)
  apply(simp add: F_CFG_TRIM__SpecOutput_def F_CFG_TRIM__SpecInput_def F_SDPDA_TO_CFG_STD__SpecOutput_def)
  apply(rename_tac Go)
  apply(rule conjI)
   apply (metis CFG_lang_lm_lang_equal)
  apply(rule F_SDPDA_TO_CFG_STD__enforces_cfg_LRk)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end
