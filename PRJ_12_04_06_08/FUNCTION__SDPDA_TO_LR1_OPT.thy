section {*FUNCTION\_\_SDPDA\_TO\_LR1\_OPT*}
theory
  FUNCTION__SDPDA_TO_LR1_OPT

imports
  PRJ_12_04_06_08__ENTRY

begin

theorem F_SDPDA_TO_LR1_OPT__SOUND: "
  F_SDPDA_TO_LR1_STD__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_SDPDA_TO_LR1_STD__SpecOutput G (F_SDPDA_TO_LR1_OPT G k)"
  apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def)
  apply(case_tac "F_SDPDA_TO_LR1_OPT G k")
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_LR1_OPT_def)
   apply(case_tac "F_SDPDA_TO_CFG_OPT G k")
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac G="G" in F_SDPDA_TO_CFG_OPT__SOUND2)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(force)
     apply(force)
    apply(rule_tac t="epdaS.marked_language G" and s="epdaH.marked_language G" in ssubst)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp only: valid_simple_dpda_def valid_pda_def valid_dpda_def)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in F_SDPDA_TO_CFG_OPT__SOUND)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in F_SDPDA_TO_CFG_STD__SOUND)
    apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
   apply(simp add: F_SDPDA_TO_CFG_STD__SpecOutput_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="X" for X in F_CFG_TRIM__SOUND)
    apply(simp add: F_CFG_TRIM__SpecInput_def F_SDPDA_TO_CFG_STD__SpecOutput_def)
   apply(simp add: F_CFG_TRIM__SpecOutput_def)
   apply (metis CFG_lang_lm_lang_equal)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_LR1_OPT_def)
  apply(case_tac "F_SDPDA_TO_CFG_OPT G k")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_SDPDA_TO_CFG_OPT__SOUND)
      apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_SDPDA_TO_CFG_STD__SOUND)
   apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
  apply(simp add: F_SDPDA_TO_CFG_STD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="X" for X in F_CFG_TRIM__SOUND)
   apply(simp add: F_CFG_TRIM__SpecInput_def F_SDPDA_TO_CFG_STD__SpecOutput_def)
   apply(force)
  apply(simp add: F_CFG_TRIM__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G'="a" in F_SDPDA_TO_CFG_STD__enforces_cfg_LRk)
       apply(force)
      apply(force)
     apply(simp add: cfg_sub_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply (metis CFG_lang_lm_lang_equal)
  done

theorem F_SDPDA_TO_LR1_OPT__vs__F_SDPDA_TO_LR1_STD: "
  F_SDPDA_TO_LR1_STD__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_SDPDA_TO_LR1_STD G = F_SDPDA_TO_LR1_OPT G k"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_SDPDA_TO_LR1_STD__SOUND)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_SDPDA_TO_CFG_STD__SOUND)
   apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecInput_def)
  apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecInput_def)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_LR1_STD_def F_SDPDA_TO_LR1_OPT_def)
  apply(case_tac "F_SDPDA_TO_CFG_OPT G k")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_SDPDA_TO_CFG_OPT__SOUND2)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(case_tac "F_CFG_TRIM (F_SDPDA_TO_CFG_STD G) ")
    apply(force)
   apply(clarsimp)
   apply(rename_tac G2)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="F_SDPDA_TO_CFG_STD G" in F_CFG_TRIM__SOUND)
    apply(simp add: F_CFG_TRIM__SpecInput_def)
   apply(simp add: F_CFG_TRIM__SpecOutput_def)
   apply(clarsimp)
   apply(subgoal_tac "cfgLM.marked_language G2 = {}")
    prefer 2
    apply(rule_tac t="cfgLM.marked_language G2" and s="cfgLM.marked_language (F_SDPDA_TO_CFG_STD G)" in ssubst)
     apply(force)
    apply(rule_tac t="cfgLM.marked_language (F_SDPDA_TO_CFG_STD G)" and s="epdaS.marked_language G" in ssubst)
     apply(force)
    apply(rule_tac t="epdaS.marked_language G" and s="epdaH.marked_language G" in ssubst)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp only: valid_simple_dpda_def valid_pda_def valid_dpda_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_SDPDA_TO_CFG_OPT__SOUND)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac G2)
  apply(rule sym)
  apply(rule cfg_equal_trim_by_cfg_sub_and_equal_marked_language)
       apply(force)
      apply(force)
     apply(simp add: cfg_sub_def F_SDPDA_TO_CFG_OPT_def Let_def F_SDPDA_TO_CFG_STD_def)
     apply(case_tac "cons_l2 (epda_initial G) (epda_box G)
              \<in> (case F_SDPDA_TO_CFG_OPT__nonterminals G k of
                  cons_tuple2 S2 S3 \<Rightarrow> S2)")
      prefer 2
      apply(force)
     apply(clarsimp)
    apply(force)
   apply(force)
  apply(force)
  done

theorem F_SDPDA_TO_LR1_OPT__vs__F_SDPDA_TO_LR1_STD__stronger: "
  valid_simple_dpda G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_SDPDA_TO_LR1_STD G = F_SDPDA_TO_LR1_OPT G k"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_SDPDA_TO_CFG_STD__SOUND)
   apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecInput_def)
  apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecInput_def)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_LR1_STD_def F_SDPDA_TO_LR1_OPT_def)
  apply(case_tac "F_SDPDA_TO_CFG_OPT G k")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_SDPDA_TO_CFG_OPT__SOUND2)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(case_tac "F_CFG_TRIM (F_SDPDA_TO_CFG_STD G) ")
    apply(force)
   apply(clarsimp)
   apply(rename_tac G2)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="F_SDPDA_TO_CFG_STD G" in F_CFG_TRIM__SOUND)
    apply(simp add: F_CFG_TRIM__SpecInput_def)
   apply(simp add: F_CFG_TRIM__SpecOutput_def)
   apply(clarsimp)
   apply(subgoal_tac "cfgLM.marked_language G2 = {}")
    prefer 2
    apply(rule_tac t="cfgLM.marked_language G2" and s="cfgLM.marked_language (F_SDPDA_TO_CFG_STD G)" in ssubst)
     apply(force)
    apply(rule_tac t="cfgLM.marked_language (F_SDPDA_TO_CFG_STD G)" and s="epdaS.marked_language G" in ssubst)
     apply (metis CFG_lang_lm_lang_equal)
    apply(rule_tac t="epdaS.marked_language G" and s="epdaH.marked_language G" in ssubst)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp only: valid_simple_dpda_def valid_pda_def valid_dpda_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_SDPDA_TO_CFG_OPT__SOUND)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac G2)
  apply(rule sym)
  apply(rule cfg_equal_trim_by_cfg_sub_and_equal_marked_language)
       apply(force)
      apply(force)
     apply(simp add: cfg_sub_def F_SDPDA_TO_CFG_OPT_def Let_def F_SDPDA_TO_CFG_STD_def)
     apply(case_tac "cons_l2 (epda_initial G) (epda_box G)
              \<in> (case F_SDPDA_TO_CFG_OPT__nonterminals G k of
                  cons_tuple2 S2 S3 \<Rightarrow> S2)")
      prefer 2
      apply(force)
     apply(clarsimp)
    apply(force)
   apply(force)
  apply(force)
  done

end
