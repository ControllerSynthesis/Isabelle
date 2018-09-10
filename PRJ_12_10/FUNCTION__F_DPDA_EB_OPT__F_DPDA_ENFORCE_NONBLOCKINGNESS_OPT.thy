section {*FUNCTION\_\_F\_DPDA\_EB\_OPT\_\_F\_DPDA\_ENFORCE\_NONBLOCKINGNESS\_OPT*}
theory
  FUNCTION__F_DPDA_EB_OPT__F_DPDA_ENFORCE_NONBLOCKINGNESS_OPT

imports
  PRJ_12_10__ENTRY

begin

definition F_SDPDA_TO_LR1_OPT__SpecInput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_LR1_OPT__SpecInput2 G \<equiv>
  valid_simple_dpda G
  \<and> \<not> duplicate_marking G"

definition F_SDPDA_TO_LR1_OPT__SpecOutput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_LR1_OPT__SpecOutput2 Gi Go \<equiv>
  case Go of
  None \<Rightarrow> epdaS.marked_language Gi = {}
  | Some Go' \<Rightarrow>
      valid_cfg Go'
      \<and> cfg_LRk Go' (Suc 0)
      \<and> epdaS.marked_language Gi = cfgSTD.marked_language Go'
      \<and> cfgSTD.Nonblockingness_branching Go'
      \<and> cfg_nonterminals Go' \<subseteq> cfgSTD_Nonblockingness_nonterminals Go'"

definition F_CFG_EB__SpecInput2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_EB__SpecInput2 G \<equiv>
  valid_cfg G"

definition F_CFG_EB__SpecOutput2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_CFG_EB__SpecOutput2 Gi Go \<equiv>
  case Go of
  None \<Rightarrow> cfgSTD.marked_language Gi = {}
  | Some Go' \<Rightarrow>
      valid_cfg Go'
      \<and> cfg_nonterminals Go' = cfgSTD_Nonblockingness_nonterminals Go'
      \<and> cfgSTD.marked_language Gi = cfgSTD.marked_language Go'
      \<and> cfg_sub Go' Gi
      \<and> nonblockingness_language (cfgSTD.unmarked_language Go') (cfgSTD.marked_language Go')
      \<and> cfgSTD.Nonblockingness_branching Go'"

definition F_SDPDA_TO_CFG_STD__SpecInput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_CFG_STD__SpecInput2 G \<equiv>
  valid_simple_dpda G
  \<and> \<not> duplicate_marking G"

definition F_SDPDA_TO_CFG_STD__SpecOutput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_CFG_STD__SpecOutput2 Gi Go \<equiv>
  valid_cfg Go
  \<and> Go = F_SDPDA_TO_CFG_STD Gi
  \<and> epdaS.marked_language Gi = cfgSTD.marked_language Go"

theorem F_SDPDA_TO_CFG_STD__SOUND2_OPT: "
  F_SDPDA_TO_CFG_STD__SpecInput2 G
  \<Longrightarrow> F_SDPDA_TO_CFG_STD__SpecOutput2 G (F_SDPDA_TO_CFG_STD G)"
  apply(simp add: F_SDPDA_TO_CFG_STD__SpecOutput2_def F_SDPDA_TO_CFG_STD__SpecInput2_def)
  apply(rule conjI)
   apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
   apply(force)
  apply(rule_tac
      t="cfgSTD.marked_language (F_SDPDA_TO_CFG_STD G)"
      and s="cfgRM.marked_language (F_SDPDA_TO_CFG_STD G)"
      in ssubst)
   prefer 2
   apply(rule F_SDPDA_TO_CFG_STD__preserves_lang)
   apply(force)
  apply(rule CFG_lang_rm_lang_equal)
  apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
  apply(force)
  done

theorem F_CFG_EB__SOUND2_OPT: "
  F_CFG_EB__SpecInput2 G
  \<Longrightarrow> F_CFG_EB__SpecOutput2 G (F_CFG_EB G)"
  apply(simp add: F_CFG_EB__SpecInput2_def F_CFG_EB__SpecOutput2_def)
  apply(case_tac "F_CFG_EB G")
   apply(clarsimp)
   apply (metis F_CFG_EB_None_implies_empty_lang)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac a)(*strict*)
   apply (metis F_CFG_EBSound3)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule context_conjI)
    apply(rename_tac a)(*strict*)
    apply (metis F_CFG_EB_lang_eq)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "Nonblockingness (cfgSTD.unmarked_language a) (cfgSTD.marked_language a)")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule F_CFG_EB_makes_Nonblockingness)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule conjI)
    apply(rename_tac a)(*strict*)
    apply(rule F_CFG_EB_makes_cfg_sub)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac a)(*strict*)
    apply(simp add: nonblockingness_language_def Nonblockingness_def)
   apply(rename_tac a)(*strict*)
   apply(rule F_CFG_EB_makes_Nonblockingness_id)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule F_CFG_EBSoundA)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule F_CFG_EB_idemp1)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

theorem F_SDPDA_TO_LR1_STD__SOUND2_with_no_duplicate_marking_for_OPT_spec: "
  F_SDPDA_TO_LR1_OPT__SpecInput2 G
  \<Longrightarrow> F_SDPDA_TO_LR1_OPT__SpecOutput2 G (F_SDPDA_TO_LR1_STD G)"
  apply(unfold F_SDPDA_TO_LR1_STD_def)
  apply(simp add: F_CFG_TRIM_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in F_SDPDA_TO_CFG_STD__SOUND2_OPT)
   apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput2_def F_SDPDA_TO_LR1_OPT__SpecInput2_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="F_SDPDA_TO_CFG_STD G"
      in F_CFG_EB__SOUND2_OPT)
   apply(simp add: F_CFG_EB__SpecInput2_def)
   apply(simp add: F_SDPDA_TO_CFG_STD__SpecOutput2_def)
  apply(simp add: F_SDPDA_TO_CFG_STD__SpecOutput2_def F_CFG_EB__SpecOutput2_def)
  apply(case_tac "F_CFG_EB (F_SDPDA_TO_CFG_STD G)")
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_LR1_OPT__SpecOutput2_def F_SDPDA_TO_LR1_OPT__SpecInput2_def)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      G="a"
      in SOUND_FUN_CFGLMACX_STD)
   apply(simp add: F_CFG_EASTD__SpecInput_def)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      G="a"
      in SOUND_FUN_CFGLMACX_STD)
   apply(simp add: F_CFG_EASTD__SpecInput_def)
  apply(rename_tac a)(*strict*)
  apply(simp add: F_CFG_EASTD__SpecOutput_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_SDPDA_TO_LR1_OPT__SpecInput2_def)
   apply(rule_tac
      G="G"
      in F_SDPDA_TO_CFG_STD__enforces_cfg_LRk)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      b="a"
      in cfg_sub_trans)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      t="cfgSTD.marked_language a"
      and s="cfgLM.marked_language a"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply (metis CFG_lang_lm_lang_equal)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      t="cfgLM.marked_language a"
      and s="cfgLM.marked_language (F_CFG_EASTD a)"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      t="cfgLM.marked_language (F_CFG_EASTD a)"
      and s="cfgSTD.marked_language (F_CFG_EASTD a)"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply (metis CFG_lang_lm_lang_equal)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule CFG_Nonblockingness_intro)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply (metis reachable_and_eliminiable_implies_eliminable2 reachable_and_eliminiable_implies_reachable)
  done

theorem F_SDPDA_TO_LR1_OPT__SOUND2: "
  F_SDPDA_TO_LR1_OPT__SpecInput2 G
  \<Longrightarrow> F_SDPDA_TO_LR1_OPT__SpecOutput2 G (F_SDPDA_TO_LR1_OPT G (Suc 0))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac k="Suc 0" and G="G" in F_SDPDA_TO_LR1_OPT__SOUND)
    apply(simp add: F_SDPDA_TO_LR1_OPT__SpecInput2_def F_SDPDA_TO_LR1_STD__SpecInput_def)
   apply(force)
  apply(simp add: F_SDPDA_TO_LR1_STD__SpecOutput_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
  apply(case_tac "F_SDPDA_TO_LR1_OPT G (Suc 0)")
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac GX)
  apply(rule conjI)
   apply (metis CFG_lang_lm_lang_equal)
  apply(rule conjI)
   apply (metis (no_types, lifting) F_SDPDA_TO_LR1_OPT__vs__F_SDPDA_TO_LR1_STD F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SOUND2_with_no_duplicate_marking_for_OPT_spec F_SDPDA_TO_LR1_OPT__SpecInput2_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def option.simps(5) zero_less_Suc)
  apply (metis (no_types, lifting) F_SDPDA_TO_LR1_OPT__vs__F_SDPDA_TO_LR1_STD F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SOUND2_with_no_duplicate_marking_for_OPT_spec F_SDPDA_TO_LR1_OPT__SpecInput2_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def option.simps(5) zero_less_Suc)
  done

definition F_DPDA_EB_OPT__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_EB_OPT__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda option
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__SpecOutput Gi Go \<equiv>
  case Go of
  None \<Rightarrow> epdaS.marked_language Gi = {}
  | Some Go' \<Rightarrow>
      valid_dpda Go'
      \<and> epdaS.marked_language Gi = epdaS.marked_language Go'
      \<and> nonblockingness_language (epdaS.unmarked_language Go') (epdaS.marked_language Go')
      \<and> epdaS.accessible Go'
      \<and> \<not> epdaH_livelock Go'"

definition F_DPDA_TO_SDPDA__SpecInput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_TO_SDPDA__SpecInput2 G \<equiv>
  valid_dpda G"

definition F_DPDA_TO_SDPDA__SpecOutput2 :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_TO_SDPDA__SpecOutput2 Gi Go \<equiv>
  valid_simple_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

theorem F_DPDA_TO_SDPDA__SOUND2_OPT: "
  F_DPDA_TO_SDPDA__SpecInput2 G
  \<Longrightarrow> F_DPDA_TO_SDPDA__SpecOutput2 G (F_DPDA_TO_SDPDA G)"
  apply(simp add: F_DPDA_TO_SDPDA__SpecInput2_def F_DPDA_TO_SDPDA__SpecOutput2_def)
  apply(rule conjI)
   apply (metis F_DPDA_TO_SDPDA_makes_SDPDA)
  apply (metis F_DPDA_TO_SDPDA_preserves_language)
  done

definition F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput G \<equiv>
  valid_simple_dpda G"

definition F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecOutput :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda option
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecOutput G1 G2 \<equiv>
  F_DPDA_EB_OPT__SpecOutput G1 G2"

definition F_SDPDA_EUME__SpecInput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_SDPDA_EUME__SpecInput2 G \<equiv>
  valid_simple_dpda G"

definition F_SDPDA_EUME__SpecOutput2 :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_SDPDA_EUME__SpecOutput2 Gi Go \<equiv>
  valid_simple_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> \<not> duplicate_marking Go"

definition F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput G \<equiv>
  valid_simple_dpda G
  \<and> \<not> duplicate_marking G"

definition F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda option
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput G1 G2 \<equiv>
  F_DPDA_EB_OPT__SpecOutput G1 G2"

theorem F_SDPDA_EUME__SOUND2_OPT: "
  F_SDPDA_EUME__SpecInput2 G
  \<Longrightarrow> F_SDPDA_EUME__SpecOutput2 G (F_SDPDA_EUME G)"
  apply(simp add: F_SDPDA_EUME__SpecInput2_def F_SDPDA_EUME__SpecOutput2_def)
  apply(rule conjI)
   apply (metis F_SDPDA_EUME__preserves_SDPDA)
  apply(rule conjI)
   apply(rule F_SDPDA_EUME__preserves_lang)
   apply(force)
  apply (metis F_SDPDA_EUME__no_duplicate_marking)
  done

definition F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput G \<equiv>
  valid_cfg G
  \<and> cfg_LRk G (Suc 0)
  \<and> cfgSTD.Nonblockingness_branching G
  \<and> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G"

definition F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> cfgSTD.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epdaS.accessible Go
  \<and> \<not> epdaH_livelock Go"

definition F_DPDA_EB_OPT__F_CFG_TC__SpecInput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_CFG_TC__SpecInput G \<equiv>
  valid_cfg G
  \<and> cfgSTD.Nonblockingness_branching G
  \<and> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<and> cfg_LRk G (Suc 0)"

definition F_DPDA_EB_OPT__F_CFG_TC__SpecOutput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_CFG_TC__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput Gi Go"

definition F_DPDA_EB_OPT__F_LR_PARSER__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_LR_PARSER__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> (\<forall>r\<in> parser_rules G. rule_rpop r \<noteq> [])
  \<and> parser_no_access_final_with_read G
  \<and> can_detect_parser_bottom_only_in_Nonblockingness_configurations G
  \<and> parser_initial G \<notin> parser_marking G"

definition F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('state, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> parserS.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epdaS.accessible Go
  \<and> \<not> epdaH_livelock Go"

definition F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parser_not_observes_input_terminator G
  \<and> (\<forall>r\<in> parser_rules G. rule_rpop r \<noteq> [])"

definition F_DPDA_EB_OPT__F_PARSER_RITU__SpecOutput :: "
  ('stateA, 'event, 'stackA) parser
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_RITU__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput Gi Go"

definition F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parser_not_observes_input_terminator G
  \<and> parser_no_top_rules G
  \<and> parser_no_empty_steps_from_marking_states G"

definition F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('state, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput Gi Go"

definition F_DPDA_EB_OPT__F_PARSER_TC__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_TC__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> parser_not_observes_input_terminator G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parser_no_top_rules G
  \<and> parser_no_empty_steps_from_marking_states G"

definition F_DPDA_EB_OPT__F_PARSER_TC__SpecOutput :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('state, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_TC__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput Gi Go"

definition F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput G \<equiv>
  valid_epda G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epdaS.is_forward_edge_deterministic_accessible G
  \<and> epda_no_empty_steps_from_marking_states G"

definition F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecOutput :: "
  ('state, 'event, 'stackA) epda
  \<Rightarrow> ('state, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__SpecOutput Gi (Some Go)"

definition F_EDPDA_TO_DPDA__SpecInput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_TO_DPDA__SpecInput2 G \<equiv>
  valid_epda G
  \<and> epdaS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epda_no_empty_steps_from_marking_states G"

definition F_EDPDA_TO_DPDA__SpecOutput2 :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_TO_DPDA__SpecOutput2 Gi Go \<equiv>
  valid_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epdaH_no_livelocks_from_marking_states Go"

definition F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput G \<equiv>
  valid_dpda G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epdaH_no_livelocks_from_marking_states G"

definition F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__SpecOutput Gi (Some Go)"

theorem F_EDPDA_TO_DPDA__SOUND2_OPT: "
  F_EDPDA_TO_DPDA__SpecInput2 G
  \<Longrightarrow> F_EDPDA_TO_DPDA__SpecOutput2 G (F_EDPDA_TO_DPDA G)"
  apply(simp add: F_EDPDA_TO_DPDA__SpecOutput2_def F_EDPDA_TO_DPDA__SpecInput2_def)
  apply(clarsimp)
  apply(rule conjI)
   apply (metis F_EDPDA_TO_DPDA_makesDPDA)
  apply(rule context_conjI)
   apply (metis F_EDPDA_TO_DPDA_preservesLang)
  apply(clarsimp)
  apply(rule conjI)
   apply(subgoal_tac "epdaS.unmarked_language G = epdaS.unmarked_language (F_EDPDA_TO_DPDA G)")
    apply(force)
   apply(rule F_EDPDA_TO_DPDA_preservesULang)
    apply(force)
   apply(force)
  apply(rule F_EDPDA_TO_DPDA_generates_epdaH_no_livelocks_from_marking_states)
    apply(force)
   apply(force)
  apply(force)
  done

definition F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput G \<equiv>
  valid_dpda G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epdaS.accessible G
  \<and> epdaH_no_livelocks_from_marking_states G"

definition F_DPDA_EB_OPT__F_F_DPDA_EA_OPT__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_F_DPDA_EA_OPT__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__SpecOutput Gi (Some Go)"

definition F_DPDA_EB_OPT__F_EPDA_TC__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_EPDA_TC__SpecInput G \<equiv>
  valid_dpda G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epdaS.accessible G
  \<and> epdaH_no_livelocks_from_marking_states G"

definition F_DPDA_EB_OPT__F_EPDA_TC__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EB_OPT__F_EPDA_TC__SpecOutput Gi Go \<equiv>
  F_DPDA_EB_OPT__SpecOutput Gi (Some Go)"

definition F_LR_PARSER__SpecInput2 :: "
  ('nonterminal DT_symbol, 'event DT_symbol) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event DT_symbol) cfg
    \<times> ('nonterminal DT_symbol, 'event DT_symbol) DT_first_function
    \<times> (('nonterminal DT_symbol, 'event DT_symbol) DT_cfg_item set,
        ('nonterminal DT_symbol, 'event DT_symbol) DT_two_elements,
        nat) epda
    \<times> nat
    \<times> 'event DT_symbol
  \<Rightarrow> bool"
  where
    "F_LR_PARSER__SpecInput2 G X \<equiv>
  case X of
  (G', F, M, n, Do) \<Rightarrow>
    \<exists>S'.
      valid_cfg G
      \<and> cfgSTD_first_compatible F n
      \<and> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
      \<and> cfgSTD.Nonblockingness_branching G
      \<and> Do = F_FRESH (cfg_events G)
      \<and> S' = F_FRESH (cfg_nonterminals G)
      \<and> G' = F_CFG_AUGMENT G S' Do
      \<and> n = 1
      \<and> M = F_LR_MACHINE G' F n
      \<and> cfg_LRk G n"

definition F_LR_PARSER__SpecOutput2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_LR_PARSER__SpecOutput2 Gi Go \<equiv>
  valid_parser Go
  \<and> parserFS.is_forward_edge_deterministic_accessible Go
  \<and> cfgSTD.marked_language Gi = parserS.marked_language Go
  \<and> parser_initial Go \<notin> parser_marking Go
  \<and> valid_bounded_parser Go 1
  \<and> nonblockingness_language (parserS.unmarked_language Go) (parserS.marked_language Go)
  \<and> (\<forall>r \<in> parser_rules Go. rule_rpop r \<noteq> [])
  \<and> parser_no_access_final_with_read Go
  \<and> can_detect_parser_bottom_only_in_Nonblockingness_configurations Go"

theorem F_LR_PARSER__SOUND2_OPT: "
  F_LR_PARSER__SpecInput2 G (G', F, M, Suc 0, Do)
  \<Longrightarrow> F_LR_PARSER__SpecOutput2 G ((\<lambda>G (G', F, M, k, Do). F_LR_PARSER G G' M Do) G (G', F, M, Suc 0, Do))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_LR_PARSER__SOUND)
   apply(simp add: F_LR_PARSER__SpecInput2_def F_LR_PARSER__SpecInput_def)
  apply(simp add: F_LR_PARSER__SpecOutput2_def F_LR_PARSER__SpecOutput_def)
  done

theorem F_DPDA_EB_OPT__SOUND: "
  F_DPDA_EB_OPT__SpecInput G
  \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)"
  apply(simp add: F_DPDA_EB_OPT_def)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__SpecOutput"
      and SPi_H="F_DPDA_TO_SDPDA__SpecInput2"
      and SPo_H="F_DPDA_TO_SDPDA__SpecOutput2"
      and H="F_DPDA_TO_SDPDA"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_TO_SDPDA__SpecInput2_def)
     apply(rule F_DPDA_TO_SDPDA__SOUND2_OPT)
     apply(force)
    apply(simp add: F_DPDA_TO_SDPDA__SpecOutput2_def F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecOutput_def F_DPDA_EB_OPT__SpecOutput_def F_DPDA_TO_SDPDA__SpecOutput2_def)
   apply(clarsimp)
   apply(case_tac "P")
    apply(rename_tac P)(*strict*)
    apply(force)
   apply(rename_tac P a)(*strict*)
   apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecOutput"
      and SPi_H="F_SDPDA_EUME__SpecInput2"
      and SPo_H="F_SDPDA_EUME__SpecOutput2"
      and H="F_SDPDA_EUME"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac G)(*strict*)
       apply(force)
      apply(rename_tac G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput_def F_SDPDA_EUME__SpecInput2_def)
     apply(rename_tac G)(*strict*)
     apply(rule F_SDPDA_EUME__SOUND2_OPT)
     apply(force)
    apply(rename_tac G)(*strict*)
    apply(simp add: F_SDPDA_EUME__SpecOutput2_def F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput_def)
   apply(rename_tac G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__SpecOutput_def F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecOutput_def F_SDPDA_EUME__SpecOutput2_def F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput_def)
   apply(clarsimp)
   apply(case_tac "P")
    apply(rename_tac G P)(*strict*)
    apply(force)
   apply(rename_tac G P a)(*strict*)
   apply(clarsimp)
  apply(rename_tac G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_DPDA_TO_SDPDA__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga G)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Ga G)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_SDPDA_TO_LR1_OPT__SOUND2)
   apply(simp add: F_SDPDA_TO_LR1_OPT__SpecInput2_def)
   apply(rename_tac G)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput_def)
  apply(rename_tac Ga G)(*strict*)
  apply(case_tac "F_SDPDA_TO_LR1_OPT G (Suc 0)")
   apply(rename_tac Ga G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput_def F_DPDA_EB_OPT__SpecOutput_def F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput_def)
   apply(simp add: F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
  apply(rename_tac Ga G a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G a)(*strict*)
  apply(subgoal_tac "F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput a")
   apply(rename_tac G a)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput_def)
  apply(rename_tac G a)(*strict*)
  apply(rule_tac
      ?I1.0="F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput"
      and a="a"
      and ?O1.0="F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput"
      and ?O2.0="F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and ?O3.0="F_SDPDA_TO_LR1_OPT__SpecOutput2"
      in decompose_simp)
      apply(rename_tac G a)(*strict*)
      prefer 5
      apply(simp add: Let_def)
     apply(rename_tac G a)(*strict*)
     apply(force)
    apply(rename_tac G a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G a)(*strict*)
   prefer 2
   apply(rename_tac G a aa Ga F)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__SpecOutput_def F_DPDA_EB_OPT__F_SDPDA_EUME__SpecOutput_def F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput_def Let_def F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
  apply(rename_tac G a)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_SDPDA_EUME__SpecInput G")
  apply(thin_tac "F_SDPDA_TO_LR1_OPT__SpecOutput2 G (Some a)")
  apply(thin_tac "F_SDPDA_TO_LR1_OPT G (Suc 0) = Some a")
  apply(rename_tac G)
  apply(rename_tac Ga G)(*strict*)
  apply(simp add: Let_def)
  apply(rename_tac G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_CFG_TC__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_CFG_TC__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_H="F_CFG_TC__SpecInput2"
      and SPo_H="F_CFG_TC__SpecOutput2"
      and H="F_CFG_TC"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac G)(*strict*)
       apply(force)
      apply(rename_tac G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput_def F_CFG_TC__SpecInput2_def)
     apply(rename_tac G)(*strict*)
     apply(rule F_CFG_TC__SOUND2)
     apply(force)
    apply(rename_tac G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_EB_OPT__F_CFG_TC__SpecInput_def F_CFG_TC__SpecOutput2_def)
   apply(rename_tac G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_EB_OPT__F_CFG_TC__SpecInput_def F_CFG_TC__SpecOutput2_def F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_EB_OPT__F_CFG_TC__SpecOutput_def)
  apply(rename_tac G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga G)(*strict*)
  apply(rule_tac
      t="F_LR_PARSER G (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F_CFG_FIRST (Suc 0)) (F_FRESH (cfg_events G))"
      and s=" (\<lambda>(G', F, M, n, Do). F_LR_PARSER G G' M Do) ((F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), F_CFG_FIRST, (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F_CFG_FIRST (Suc 0)), (Suc 0), (F_FRESH (cfg_events G)))"
      in ssubst)
   apply(rename_tac Ga G)(*strict*)
   apply(force)
  apply(rename_tac Ga G)(*strict*)
  apply(rule_tac
      X="G"
      and Y="((F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), F_CFG_FIRST, (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F_CFG_FIRST (Suc 0)), (Suc 0), (F_FRESH (cfg_events G)))"
      and SPi_FH="F_DPDA_EB_OPT__F_LR_PARSER__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_CFG_TC__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_CFG_TC__SpecOutput"
      and SPi_H="F_LR_PARSER__SpecInput2"
      and SPo_H="F_LR_PARSER__SpecOutput2"
      and H="\<lambda>G (G', F, M, n, Do). F_LR_PARSER G G' M Do"
      in decompose_sequential_execution_input_output_specification2_simp3)
       apply(rename_tac Ga G)(*strict*)
       apply(force)
      apply(rename_tac Ga G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_CFG_TC__SpecInput_def F_LR_PARSER__SpecInput2_def)
      apply(simp add: cfgSTD_first_compatible_def)
      apply(clarsimp)
      apply(rule sym)
      apply(rule F_CFG_FIRST__SOUND)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(rename_tac Ga G)(*strict*)
     apply(rule F_LR_PARSER__SOUND2_OPT)
     apply(force)
    apply(rename_tac Ga G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_LR_PARSER__SpecInput_def F_LR_PARSER__SpecOutput2_def)
   apply(rename_tac Ga G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_CFG_TC__SpecOutput_def F_DPDA_EB_OPT__F_SDPDA_TO_LR1_OPT__SpecOutput_def)
   apply(rename_tac G P)(*strict*)
   apply(case_tac "P")
   apply(rename_tac G P epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput_def F_LR_PARSER__SpecOutput2_def F_DPDA_EB_OPT__F_CFG_TC__SpecInput_def)
  apply(rename_tac Ga G X)(*strict*)
  apply(clarsimp)
  apply(rename_tac G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_CFG_TC__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_PARSER_RITU__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_LR_PARSER__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput"
      and SPi_H="F_PARSERRITU__SpecInput"
      and SPo_H="F_PARSERRITU__SpecOutput"
      and H="F_PARSER_RITU"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac Ga G)(*strict*)
       apply(force)
      apply(rename_tac Ga G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_LR_PARSER__SpecInput_def F_PARSERRITU__SpecInput_def)
     apply(rename_tac Ga G)(*strict*)
     apply(rule F_PARSERRITU__SOUND)
     apply(force)
    apply(rename_tac Ga G)(*strict*)
    apply(simp add: F_PARSERRITU__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput_def)
   apply(rename_tac Ga G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_RITU__SpecOutput_def F_PARSERRITU__SpecOutput_def)
  apply(rename_tac Ga G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_LR_PARSER__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga Gb G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_PARSER_RITU__SpecOutput"
      and SPi_H="F_PARSER_RTR__SpecInput"
      and SPo_H="F_PARSER_RTR__SpecOutput"
      and H="F_PARSER_RTR"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac Ga Gb G)(*strict*)
       apply(force)
      apply(rename_tac Ga Gb G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput_def F_PARSER_RTR__SpecInput_def)
     apply(rename_tac Ga Gb G)(*strict*)
     apply(rule F_PARSER_RTR__SOUND)
     apply(force)
    apply(rename_tac Ga Gb G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput_def F_PARSER_RTR__SpecOutput_def)
   apply(rename_tac Ga Gb G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_PARSER_RITU__SpecOutput_def F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput_def F_PARSER_RTR__SpecOutput_def)
  apply(rename_tac Ga Gb G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_PARSER_RITU__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga Gb Gc G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_PARSER_TC__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_PARSER_TC__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput"
      and SPi_H="F_PARSER_TC__SpecInput"
      and SPo_H="F_PARSER_TC__SpecOutput"
      and H="F_PARSER_TC"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac Ga Gb Gc G)(*strict*)
       apply(force)
      apply(rename_tac Ga Gb Gc G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput_def F_PARSER_TC__SpecInput_def)
     apply(rename_tac Ga Gb Gc G)(*strict*)
     apply(rule F_PARSER_TC__SOUND)
     apply(force)
    apply(rename_tac Ga Gb Gc G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_PARSER_TC__SpecInput_def F_PARSER_TC__SpecOutput_def)
   apply(rename_tac Ga Gb Gc G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput_def F_PARSER_TC__SpecOutput_def F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_TC__SpecOutput_def)
  apply(rename_tac Ga Gb Gc G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga Gb Gc Gd G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_PARSER_TC__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_PARSER_TC__SpecOutput"
      and SPi_H="F_PARSER_TO_EDPDA__SpecInput"
      and SPo_H="F_PARSER_TO_EDPDA__SpecOutput"
      and H="F_PARSER_TO_EDPDA"
      in decompose_sequential_execution_input_output_specification2_simp3)
       apply(rename_tac Ga Gb Gc Gd G)(*strict*)
       apply(force)
      apply(rename_tac Ga Gb Gc Gd G)(*strict*)
      apply(simp add: F_DPDA_EB_OPT__F_PARSER_TC__SpecInput_def F_PARSER_TO_EDPDA__SpecInput_def)
      apply(rename_tac G)(*strict*)
      apply(rule F_FRESH_is_fresh)
      apply(simp add: valid_bounded_parser_def valid_parser_def)
     apply(rename_tac Ga Gb Gc Gd G)(*strict*)
     apply(rule F_PARSER_TO_EDPDA__SOUND)
     apply(force)
    apply(rename_tac Ga Gb Gc Gd G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput_def F_PARSER_TO_EDPDA__SpecOutput_def)
   apply(rename_tac Ga Gb Gc Gd G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_RTR__SpecInput_def F_PARSER_TC__SpecOutput_def F_DPDA_EB_OPT__F_LR_PARSER__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_RTR__SpecOutput_def F_DPDA_EB_OPT__F_PARSER_TC__SpecOutput_def)
   apply(rename_tac G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__SpecOutput_def F_PARSER_TO_EDPDA__SpecOutput_def)
  apply(rename_tac Ga Gb Gc Gd G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_PARSER_TC__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga Gb Gc Gd Ge G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecOutput"
      and SPi_H="F_EDPDA_TO_DPDA__SpecInput2"
      and SPo_H="F_EDPDA_TO_DPDA__SpecOutput2"
      and H="F_EDPDA_TO_DPDA"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac Ga Gb Gc Gd Ge G)(*strict*)
       apply(force)
      apply(rename_tac Ga Gb Gc Gd Ge G)(*strict*)
      apply(simp add: F_EDPDA_TO_DPDA__SpecInput2_def F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput_def)
     apply(rename_tac Ga Gb Gc Gd Ge G)(*strict*)
     apply(rule F_EDPDA_TO_DPDA__SOUND2_OPT)
     apply(force)
    apply(rename_tac Ga Gb Gc Gd Ge G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput_def F_EDPDA_TO_DPDA__SpecOutput2_def)
   apply(rename_tac Ga Gb Gc Gd Ge G P)(*strict*)
   apply(simp add: F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecOutput_def F_DPDA_EB_OPT__SpecOutput_def F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput_def F_EDPDA_TO_DPDA__SpecOutput2_def F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput_def)
  apply(rename_tac Ga Gb Gc Gd Ge G X)(*strict*)
  apply(clarsimp)
  apply(rename_tac G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_PARSER_TO_EDPDA__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_F_DPDA_EA_OPT__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput"
      and SPi_H="F_DPDA_EA_OPT__SpecInput"
      and SPo_H="F_DPDA_EA_OPT__SpecOutput"
      and H="F_DPDA_EA_OPT"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac Ga G)(*strict*)
       apply(force)
      apply(rename_tac Ga G)(*strict*)
      apply(simp add: F_DPDA_EA_OPT__SpecInput_def F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput_def)
     apply(rename_tac Ga G)(*strict*)
     apply(rule F_DPDA_EA_OPT__SOUND)
     apply(force)
    apply(rename_tac Ga G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput_def F_DPDA_EA_OPT__SpecOutput_def)
   apply(rename_tac Ga G P)(*strict*)
   apply(simp add: F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput_def F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput_def F_DPDA_EB_OPT__SpecOutput_def F_DPDA_EB_OPT__F_F_DPDA_EA_OPT__SpecOutput_def)
  apply(rename_tac Ga G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga Gb G)(*strict*)
  apply(rule_tac
      X="G"
      and SPi_FH="F_DPDA_EB_OPT__F_EPDA_TC__SpecInput"
      and SPo_FH="F_DPDA_EB_OPT__F_EPDA_TC__SpecOutput"
      and SPi_F="F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput"
      and SPo_F="F_DPDA_EB_OPT__F_F_DPDA_EA_OPT__SpecOutput"
      and SPi_H="F_EPDA_TC__SpecInput2"
      and SPo_H="F_EPDA_TC__SpecOutput2"
      and H="F_EPDA_TC"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(rename_tac Ga Gb G)(*strict*)
       apply(force)
      apply(rename_tac Ga Gb G)(*strict*)
      apply(simp add: F_EPDA_TC__SpecInput2_def F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput_def)
     apply(rename_tac Ga Gb G)(*strict*)
     apply(rule F_EPDA_TC__SOUND2)
     apply(force)
    apply(rename_tac Ga Gb G)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__F_EPDA_TC__SpecInput_def F_EPDA_TC__SpecOutput2_def F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput_def)
   apply(rename_tac Ga Gb G P)(*strict*)
   apply(simp add: F_DPDA_EA_STD__SpecOutput_def F_EPDA_TC__SpecOutput2_def F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecInput_def F_DPDA_EB_OPT__F_EDPDA_TO_DPDA__SpecOutput_def F_DPDA_EB_OPT__SpecOutput_def F_DPDA_EB_OPT__F_F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EB_OPT__F_EPDA_TC__SpecOutput_def F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput_def)
  apply(rename_tac Ga Gb G X)(*strict*)
  apply(thin_tac "F_DPDA_EB_OPT__F_DPDA_EA_OPT__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac Ga Gb Gc G)(*strict*)
  apply(simp add: F_DPDA_EB_OPT__F_EPDA_TC__SpecInput_def F_DPDA_EB_OPT__F_EPDA_TC__SpecOutput_def F_DPDA_EB_OPT__SpecOutput_def)
  apply(rename_tac G)(*strict*)
  apply(rule Nonblockingness_DPDA_without_empty_steps_from_final_states_is_Livelock_free)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_EB_Nonblockingness_branching_restricted_hlp)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(force)
  apply(force)
  done

theorem F_DPDA_EB_OPT_preserves_DPDA: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = Some G'
  \<Longrightarrow> valid_dpda G'"
  apply(subgoal_tac "F_DPDA_EB_OPT__SpecInput G \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)")
   prefer 2
   apply(rule F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EB_OPT__SpecOutput_def)
  done

theorem F_DPDA_EB_OPT_preservesLang: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = Some G'
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language G'"
  apply(subgoal_tac "F_DPDA_EB_OPT__SpecInput G \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)")
   prefer 2
   apply(rule F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EB_OPT__SpecOutput_def)
  done

theorem F_DPDA_EB_OPT_enforces_langBF: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = Some G'
  \<Longrightarrow> nonblockingness_language (epdaS.unmarked_language G') (epdaS.marked_language G')"
  apply(subgoal_tac "F_DPDA_EB_OPT__SpecInput G \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)")
   prefer 2
   apply(rule F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EB_OPT__SpecOutput_def)
  done

theorem F_DPDA_EB_OPT_enforces_accessible: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = Some G'
  \<Longrightarrow> epdaS.accessible G'"
  apply(subgoal_tac "F_DPDA_EB_OPT__SpecInput G \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)")
   prefer 2
   apply(rule F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EB_OPT__SpecOutput_def)
  done

theorem F_DPDA_EB_OPT_non_on_empty_lang: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = None
  \<Longrightarrow> epdaS.marked_language G = {}"
  apply(subgoal_tac "F_DPDA_EB_OPT__SpecInput G \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)")
   prefer 2
   apply(rule F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EB_OPT__SpecOutput_def)
  done

theorem F_DPDA_EB_OPT_Nonblockingness_branching_restricted: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = Some G'
  \<Longrightarrow> epdaH.Nonblockingness_branching_restricted G'"
  apply(subgoal_tac "valid_dpda G'")
   prefer 2
   apply(rule F_DPDA_EB_OPT_preserves_DPDA)
    apply(force)
   apply(force)
  apply(rule epdaH.AX_BF_BraSBRest_DetHDB_LaOp)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
   apply(rule conjI)
    apply(simp add: epdaH.is_forward_target_deterministicHist_DB_long_def)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 n e w1 w2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
   apply (metis DPDA_to_epdaH_determinism)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G'"
      in epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G'"
      in epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G'"
      in epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_EB_OPT_enforces_langBF)
    apply(force)
   apply(force)
  apply(simp add: nonblockingness_language_def)
  done

theorem F_DPDA_EB_OPT_enforces_not_livelock: "
  valid_dpda G
  \<Longrightarrow> F_DPDA_EB_OPT G = Some G'
  \<Longrightarrow> \<not> epdaH_livelock G'"
  apply(subgoal_tac "F_DPDA_EB_OPT__SpecInput G \<Longrightarrow> F_DPDA_EB_OPT__SpecOutput G (F_DPDA_EB_OPT G)")
   prefer 2
   apply(rule F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EB_OPT__SpecOutput_def)
  done

end
