section {*FUNCTION\_\_DPDA\_DRE\_\_DPDA\_DETERMINE\_REQUIRED\_EDGES*}
theory
  FUNCTION__DPDA_DRE__DPDA_DETERMINE_REQUIRED_EDGES

imports
  PRJ_12_08_03__ENTRY

begin

definition F_SDPDA_TO_LR1_OPT__SpecInput2 :: "
  ('nonterminal, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_LR1_OPT__SpecInput2 G \<equiv>
  valid_simple_dpda G"

definition F_SDPDA_TO_LR1_OPT__SpecOutput2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_SDPDA_TO_LR1_OPT__SpecOutput2 Gi Go \<equiv>
  case Go of
    None \<Rightarrow> 
      epdaS.marked_language Gi = {}
    | Some Go \<Rightarrow>
      valid_cfg Go
      \<and> cfgLM.marked_language Go = epdaS.marked_language Gi"

theorem F_SDPDA_TO_LR1_STD__SOUND2: "
  F_SDPDA_TO_LR1_OPT__SpecInput2 G
  \<Longrightarrow> F_SDPDA_TO_LR1_OPT__SpecOutput2 G (F_SDPDA_TO_LR1_STD G)"
  apply(simp add: F_SDPDA_TO_LR1_OPT__SpecInput2_def F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
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
  apply (metis CFG_lang_lm_lang_equal)
  done

definition F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput :: "
  ('state, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput G \<equiv>
  valid_dpda G 
  \<and> neutral_edges_removed G 
  \<and> read_edges_seperated G"

definition F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda 
  \<Rightarrow> ('stateB, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput Gi Go \<equiv>
  valid_simple_dpda Go 
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SOUND: "
  F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput G (F_DPDA_RMPUE (F_DPDA_SPPE G))"
  apply(rule_tac
      X="G"
      and H="F_DPDA_SPPE"
      and SPi_F="F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput"
      and SPi_H="F_DPDA_SPPE__SpecInput"
      and SPo_H="F_DPDA_SPPE__SpecOutput"
      and SPo_FH="F_DPDA_RMPUE__SpecOutput"
      and SPi_FH="F_DPDA_RMPUE__SpecInput"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SPPE__SpecInput_def)
     apply(rule F_DPDA_SPPE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SPPE__SpecOutput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_SPPE__SpecOutput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_RMPUE__SpecOutput_def)
   apply(rule valid_sdpda2_implies_valid_simple_dpda)
   apply(simp add: valid_sdpda2_def)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_RMPUE__SOUND)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput :: "
  ('state, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput G \<equiv>
  valid_dpda G 
  \<and> read_edges_seperated G"

definition F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda 
  \<Rightarrow> ('stateB, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput Gi Go \<equiv>
  valid_simple_dpda Go 
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SOUND: "
  F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput G (F_DPDA_RMPUE (F_DPDA_SPPE (F_DPDA_RNE G (F_FRESH (epda_gamma G)))))"
  apply(rule_tac
      X="G"
      and H="F_DPDA_RNE"
      and SPi_F="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput"
      and SPi_H="\<lambda>G X. F_DPDA_RNE__SpecInput G \<and> X=F_FRESH (epda_gamma G)"
      and SPo_H="F_DPDA_RNE__SpecOutput"
      and SPo_FH="F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput"
      and SPi_FH="F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput"
      in decompose_sequential_execution_input_output_specification2_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
     apply(rule F_DPDA_RNE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_RNE__SpecOutput_def F_DPDA_RMPUE__SpecInput_def)
    apply(simp add: F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput_def  F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_SEE__SpecOutput_def F_DPDA_RMPUE__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SpecInput_def  F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_SEE__SpecOutput_def F_DPDA_RMPUE__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_DRE__F_DPDA_SPPE__TO__F_DPDA_RMPUE__SOUND)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda 
  \<Rightarrow> ('stateB, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput Gi Go \<equiv>
  valid_simple_dpda Go 
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput G 
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput G (F_DPDA_RMPUE (F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
  apply(rule_tac
      X="G"
      and SPi_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput"
      and SPi_H="F_DPDA_SEE__SpecInput"
      and SPo_H="F_DPDA_SEE__SpecOutput"
      and SPi_FH="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput"
      and SPo_FH="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput"
      and H="F_DPDA_SEE"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(clarsimp)
      apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
     apply(rule F_DPDA_SEE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
    apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def  F_DPDA_SEE__SpecOutput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_RMPUE__SOUND)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput :: "
  ('state, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput G \<equiv>
  valid_dpda G 
  \<and> read_edges_seperated G"

definition F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda 
  \<Rightarrow> ('stateB, 'event, 'stack) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput Gi Go \<equiv>
  valid_dpda Go 
  \<and> read_edges_seperated Go 
  \<and> neutral_edges_removed Go 
  \<and> pop_edges_seperated Go 
  \<and> push_and_pop_edges_seperated Go 
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SOUND: "
  F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput G (F_DPDA_SPPE (F_DPDA_RNE G (F_FRESH (epda_gamma G))))"
  apply(rule_tac
      X="G"
      and H="F_DPDA_RNE"
      and SPi_F="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput"
      and SPi_H="\<lambda>G X. F_DPDA_RNE__SpecInput G \<and> X=F_FRESH (epda_gamma G)"
      and SPo_H="F_DPDA_RNE__SpecOutput"
      and SPo_FH="F_DPDA_SPPE__SpecOutput"
      and SPi_FH="F_DPDA_SPPE__SpecInput"
      in decompose_sequential_execution_input_output_specification2_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
     apply(rule F_DPDA_RNE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_RNE__SpecOutput_def F_DPDA_SPPE__SpecInput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput_def F_DPDA_SEE__SpecOutput_def F_DPDA_SPPE__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_SPPE__SOUND)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> read_edges_seperated Go
  \<and> neutral_edges_removed Go
  \<and> pop_edges_seperated Go
  \<and> push_and_pop_edges_seperated Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput G (F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G)))))"
  apply(rule_tac
      X="G"
      and H="F_DPDA_SEE"
      and SPo_FH="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput"
      and SPi_FH="F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput"
      and SPi_H="F_DPDA_SEE__SpecInput"
      and SPo_H="F_DPDA_SEE__SpecOutput"
      and SPi_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput_def F_DPDA_SEE__SpecInput_def)
     apply(rule F_DPDA_SEE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecInput_def F_DPDA_SEE__SpecOutput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput_def F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SpecOutput_def F_DPDA_SEE__SpecOutput_def)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_DRE__F_DPDA_RNE__TO__F_DPDA_SPPE__SOUND)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> read_edges_seperated Go
  \<and> neutral_edges_removed Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput G (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))"
  apply(rule_tac
      X="G"
      and SPi_H="F_DPDA_SEE__SpecInput"
      and SPo_H="F_DPDA_SEE__SpecOutput"
      and SPi_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput"
      and SPi_FH="F_DPDA_RNE__SpecInput"
      and SPo_FH="F_DPDA_RNE__SpecOutput"
      and H="F_DPDA_SEE"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(clarsimp)
      apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
     apply(rule F_DPDA_SEE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_RNE__SOUND)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G \<equiv>
  valid_dpda G
  \<and> neutral_edges_removed G
  \<and> read_edges_seperated G
  \<and> push_and_pop_edges_seperated G
  \<and> pop_edges_seperated G"

definition F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput Gi Go \<equiv>
  case Go of 
  None \<Rightarrow> 
    epdaS.marked_language Gi = {} 
  | Some Go \<Rightarrow>
    valid_cfg Go
    \<and> epdaS.marked_language Gi = cfgSTD.marked_language Go"

theorem F_SDPDA_TO_LR1_OPT__SOUND2__for_F_SDPDA_TO_CFG_STD__SpecInput: "
  F_SDPDA_TO_CFG_STD__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_SDPDA_TO_LR1_OPT__SpecOutput2 G (F_SDPDA_TO_LR1_OPT G k)"
  apply(simp add: F_SDPDA_TO_LR1_OPT__SpecOutput2_def F_SDPDA_TO_CFG_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecInput_def F_SDPDA_TO_LR1_STD__SpecOutput_def)
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
  apply(clarsimp)
  apply (metis CFG_lang_lm_lang_equal)
  done

lemma F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SOUND: "
  F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput G (F_SDPDA_TO_LR1_OPT (F_DPDA_RMPUE G) k)"
  apply(rule_tac
      X="G"
      and H="F_DPDA_RMPUE"
      and SPi_F="F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_H="F_DPDA_RMPUE__SpecInput"
      and SPo_H="F_DPDA_RMPUE__SpecOutput"
      and SPo_FH="F_SDPDA_TO_LR1_OPT__SpecOutput2"
      and SPi_FH="F_SDPDA_TO_CFG_STD__SpecInput"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_RMPUE__SpecInput_def)
     apply(rule F_DPDA_RMPUE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_RMPUE__SpecOutput_def F_SDPDA_TO_CFG_STD__SpecInput_def)
    apply(rule valid_sdpda2_implies_valid_simple_dpda)
    apply(simp add: valid_sdpda2_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__SpecOutput_def F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_RMPUE__SpecOutput_def  F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
   apply(case_tac "P")
    apply(clarsimp)
   apply(clarsimp)
   apply (metis CFG_lang_lm_lang_equal)
  apply(rename_tac X)(*strict*)
  apply(rule F_SDPDA_TO_LR1_OPT__SOUND2__for_F_SDPDA_TO_CFG_STD__SpecInput)
   apply(simp add: F_SDPDA_TO_LR1_STD__SpecInput_def)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G \<equiv>
  valid_dpda G
  \<and> read_edges_seperated G
  \<and> neutral_edges_removed G"

definition F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput Gi Go \<equiv>
  case Go of 
  None \<Rightarrow> 
    epdaS.marked_language Gi = {} 
  | Some Go \<Rightarrow>
    valid_cfg Go
    \<and> epdaS.marked_language Gi = cfgSTD.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SOUND: "
  F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput G (F_SDPDA_TO_LR1_OPT (F_DPDA_RMPUE (F_DPDA_SPPE G)) k)"
  apply(rule_tac
      X="G"
      and H="F_DPDA_SPPE"
      and SPi_F="F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_H="F_DPDA_SPPE__SpecInput"
      and SPo_H="F_DPDA_SPPE__SpecOutput"
      and SPo_FH="F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_FH="F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_SPPE__SpecInput_def)
     apply(rule F_DPDA_SPPE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_SPPE__SpecOutput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_SPPE__SpecOutput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def)
   apply(case_tac "P")
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_DRE__F_DPDA_RMPUE__TO__F_SDPDA_TO_LR1_OPT__SOUND)
   apply(force)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G \<equiv>
  valid_dpda G
  \<and> read_edges_seperated G"

definition F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput Gi Go \<equiv>
  case Go of 
  None \<Rightarrow> 
    epdaS.marked_language Gi = {} 
  | Some Go \<Rightarrow>
    valid_cfg Go
    \<and> epdaS.marked_language Gi = cfgSTD.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SOUND: "
  F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput G (F_SDPDA_TO_LR1_OPT (F_DPDA_RMPUE (F_DPDA_SPPE (F_DPDA_RNE G (F_FRESH (epda_gamma G))))) k)"
  apply(rule_tac
      X="G"
      and H="F_DPDA_RNE"
      and SPi_F="F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_H="\<lambda>G X. F_DPDA_RNE__SpecInput G \<and> X=F_FRESH (epda_gamma G)"
      and SPo_H="F_DPDA_RNE__SpecOutput"
      and SPo_FH="F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_FH="F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      in decompose_sequential_execution_input_output_specification2_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_SEE__SpecInput_def F_DPDA_RNE__SpecInput_def)
     apply(rule F_DPDA_RNE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_SEE__SpecOutput_def F_DPDA_RNE__SpecOutput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_SEE__SpecOutput_def F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_RNE__SpecOutput_def)
   apply(case_tac "P")
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_DRE__F_DPDA_SPPE__TO__F_SDPDA_TO_LR1_OPT__SOUND)
   apply(force)
  apply(force)
  done

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput Gi Go \<equiv>
  case Go of 
  None \<Rightarrow> 
    epdaS.marked_language Gi = {} 
  | Some Go \<Rightarrow>
    valid_cfg Go
    \<and> epdaS.marked_language Gi = cfgSTD.marked_language Go"

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput G (F_SDPDA_TO_LR1_OPT (F_DPDA_RMPUE (F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G)))))) k)"
  apply(rule_tac
      X="G"
      and H="F_DPDA_SEE"
      and SPo_FH="F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      and SPi_FH="F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      and SPi_H="F_DPDA_SEE__SpecInput"
      and SPo_H="F_DPDA_SEE__SpecOutput"
      and SPi_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecInput"
      and SPo_F="F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput"
      in decompose_sequential_execution_input_output_specification_simp3)
       apply(force)
      apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_SEE__SpecInput_def)
     apply(rule F_DPDA_SEE__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecInput_def F_DPDA_SEE__SpecOutput_def)
   apply(rename_tac P)(*strict*)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SpecOutput_def F_DPDA_SEE__SpecOutput_def)
   apply(case_tac "P")
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(thin_tac "F_DPDA_DRE__F_DPDA_SEE__TO__F_SDPDA_TO_LR1_OPT__SpecInput G")
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_DRE__F_DPDA_RNE__TO__F_SDPDA_TO_LR1_OPT__SOUND)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__revert_F_DPDA_RMPE__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput G G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_RMPUE G' (epdaH_required_edges (F_DPDA_RMPUE G')) = epdaH_required_edges G'"
  apply(rule_tac
      t="epdaH_required_edges G'"
      and s="epdaS_required_edges G'"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput_def valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaH_required_edges (F_DPDA_RMPUE G')"
      and s="epdaS_required_edges (F_DPDA_RMPUE G')"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput_def valid_dpda_def valid_pda_def)
   apply(rule F_DPDA_RMPUE__preserves_epda)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput_def valid_dpda_def valid_pda_def)
  apply(rule F_DPDA_DRE__revert_F_DPDA_RMPUE_SOUND_scheduled_case_epdaS_required_edges)
  apply(simp add: F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecOutput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput_def)
  done

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__revert_F_DPDA_SPPE__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput G
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput G G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_SPPE G' (epdaH_required_edges (F_DPDA_SPPE G')) = epdaH_required_edges G'"
  apply(rule_tac
      t="epdaH_required_edges G'"
      and s="epdaS_required_edges G'"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput_def valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaH_required_edges (F_DPDA_SPPE G')"
      and s="epdaS_required_edges (F_DPDA_SPPE G')"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput_def valid_dpda_def valid_pda_def)
   apply(rule F_DPDA_SPPE__preserves_epda)
   apply(simp add: F_DPDA_SEE__SpecOutput_def valid_dpda_def valid_pda_def)
  apply(rule F_DPDA_DRE__revert_F_DPDA_SPPE_SOUND_scheduled_case_epdaS_required_edges)
  apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecOutput_def F_DPDA_SPPE__SpecInput_def)
  done

lemma F_DPDA_DRE__F_DPDA_SEE__revert_F_DPDA_RNE__SOUND: "
  F_DPDA_SEE__SpecInput G
  \<Longrightarrow> F_DPDA_SEE__SpecOutput G G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_RNE G' (F_FRESH (epda_gamma G')) (epdaH_required_edges (F_DPDA_RNE (G') (F_FRESH (epda_gamma (G'))))) = epdaH_required_edges G'"
  apply(rule_tac
      t="epdaH_required_edges G'"
      and s="epdaS_required_edges G'"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: F_DPDA_SEE__SpecOutput_def valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaH_required_edges (F_DPDA_RNE G' (F_FRESH (epda_gamma G')))"
      and s="epdaS_required_edges (F_DPDA_RNE G' (F_FRESH (epda_gamma G')))"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: F_DPDA_SEE__SpecOutput_def valid_dpda_def valid_pda_def)
   apply(rule F_DPDA_RNE__preserves_epda)
    apply(simp add: F_DPDA_SEE__SpecOutput_def valid_dpda_def valid_pda_def)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule F_DPDA_DRE__revert_F_DPDA_RNE_SOUND_scheduled_case_epdaS_required_edges)
  apply(simp add: F_DPDA_SEE__SpecOutput_def F_DPDA_RNE__SpecInput_def F_DPDA_SEE__SpecInput_def)
  done

definition F_DPDA_DRE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_DRE__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set
  \<Rightarrow> bool"
  where
    "F_DPDA_DRE__SpecOutput Gi E \<equiv>
  E = epdaH_required_edges Gi"

lemma event_stack_separation_and_proper_l3_l2_seq_ALT__contra: "
  event_stack_separation_and_proper_l3_l2_seq_ALT \<lparr>cfg_conf = liftB w @ teA (cons_l3 q1 A q2) # liftB v\<rparr> 
  \<Longrightarrow> Q"
  apply(simp add: event_stack_separation_and_proper_l3_l2_seq_ALT_def)
  apply(clarsimp)
  apply(case_tac "va")
   apply(clarsimp)
   apply (metis liftB_with_nonterminal_inside)
  apply(clarsimp)
  apply(case_tac w)
   apply(clarsimp)
   apply(case_tac w)
    apply(clarsimp)
    apply(subgoal_tac "v= [] \<and>  list=[]")
     prefer 2
     apply (metis liftB_eq_liftA_empty)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(case_tac w)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "lista=listb")
   prefer 2
   apply (metis maxTermPrefix_mixed_string)
  apply(clarsimp)
  apply(subgoal_tac "v= [] \<and>  list=[]")
   prefer 2
   apply (metis liftB_eq_liftA_empty)
  apply(force)
  done

lemma event_stack_separation_and_proper_l3_l2_seq_ALT__contra2: "
  event_stack_separation_and_proper_l3_l2_seq_ALT \<lparr>cfg_conf = liftB va @ teA (cons_l2 i A) # a # w\<rparr> 
  \<Longrightarrow> Q"
  apply(simp add: event_stack_separation_and_proper_l3_l2_seq_ALT_def)
  apply(clarsimp)
  apply(case_tac v)
   apply(clarsimp)
   apply (metis liftB_with_nonterminal_inside)
  apply(clarsimp)
  apply(subgoal_tac "va=wa")
   prefer 2
   apply (metis maxTermPrefix_mixed_string)
  apply(clarsimp)
  apply(rule_tac xs="list" in rev_cases)
   apply(clarsimp)
  apply(force)
  done

lemma THE_unique_edge_is_in_delta_prime_2_enhanced_simple_precondition: "
  valid_simple_dpda G'
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p = [] \<longrightarrow> isl3 (prod_lhs p)
  \<Longrightarrow> x \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' p
  \<Longrightarrow> y \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' p
  \<Longrightarrow> x = y"
  apply(subgoal_tac "x \<in> epda_delta G'")
   prefer 2
   apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(subgoal_tac "y \<in> epda_delta G'")
   prefer 2
   apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(subgoal_tac "(\<lambda>e. case edge_event e of None \<Rightarrow> edge_push e = [] \<or> (\<exists>x. edge_push e = x # edge_pop e) | Some a \<Rightarrow> edge_pop e = edge_push e)x")
   prefer 2
   apply(simp add: valid_simple_dpda_def)
  apply(subgoal_tac "(\<lambda>e. case edge_event e of None \<Rightarrow> edge_push e = [] \<or> (\<exists>x. edge_push e = x # edge_pop e) | Some a \<Rightarrow> edge_pop e = edge_push e)y")
   prefer 2
   apply(simp add: valid_simple_dpda_def)
  apply(subgoal_tac "\<exists>a. edge_pop x=[a]")
   prefer 2
   apply(rule_tac
      G="G'"
      in valid_pda_edge_pop_single)
    apply(simp add: valid_dpda_def valid_simple_dpda_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "\<exists>a. edge_pop y=[a]")
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in valid_pda_edge_pop_single)
    apply(rename_tac a)(*strict*)
    apply(simp add: valid_dpda_def valid_simple_dpda_def)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a aa)(*strict*)
  apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G') \<and> (\<exists>y. edge_event x = Some y)"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya yaa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
    apply(clarsimp)
    apply(rename_tac a aa ya qta)(*strict*)
    apply(case_tac x)
    apply(rename_tac a aa ya qta edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac y)
    apply(rename_tac a aa ya qta edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa ya)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa ya)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def)
   apply(rename_tac a aa ya)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya xa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(clarsimp)
   apply(rename_tac a aa ya)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya yaa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa ya xa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(clarsimp)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l3_read y (epda_states G') \<and> (\<exists>ya. edge_event y = Some ya)"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa ya)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya xa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(clarsimp)
   apply(rename_tac a aa ya)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya yb)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa ya xa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(clarsimp)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> edge_push x = []"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
    apply(clarsimp)
    apply(rename_tac aa)(*strict*)
    apply(case_tac "edge_event x")
     apply(rename_tac aa)(*strict*)
     prefer 2
     apply(rename_tac aa a)(*strict*)
     apply(clarsimp)
    apply(rename_tac aa)(*strict*)
    apply(clarsimp)
    apply(case_tac "edge_event y")
     apply(rename_tac aa)(*strict*)
     prefer 2
     apply(rename_tac aa a)(*strict*)
     apply(clarsimp)
    apply(rename_tac aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa xa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa xa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop y \<and> edge_push y = []"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa xa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa xa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states G') \<and> edge_push x \<noteq> [] \<and> edge_event x = None"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa xa xaa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(clarsimp)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa xa ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa xa xaa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(clarsimp)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l3_push y (epda_states G') \<and> edge_push y \<noteq> [] \<and> edge_event y = None"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa xa ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa xa xaa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(clarsimp)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      P="p \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x \<and> (\<exists>y. edge_event x = Some y)"
      in disjE)
   apply(rename_tac a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ya yaa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(clarsimp)
    apply(rename_tac a aa ya)(*strict*)
    apply(case_tac x)
    apply(rename_tac a aa ya edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac y)
    apply(rename_tac a aa ya edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa xa ya)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac a aa)(*strict*)
  apply(erule disjE)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a aa xa ya)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a aa xa xaa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(erule_tac
      P="p = \<lparr>prod_lhs = cons_l2 (edge_src x) a, prod_rhs = [teA (cons_l2   (edge_trg x) xa)]\<rparr>"
      in disjE)
   apply(rename_tac a aa xa xaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a aa xa xaa)(*strict*)
  apply(clarsimp)
  done

lemma F_SDPDA_TO_LR1_STD__computes__epdaH_required_edges__part1: "
  valid_simple_dpda G 
  \<Longrightarrow> F_CFG_TRIM (F_SDPDA_TO_CFG_STD G) = Some GX 
  \<Longrightarrow> valid_cfg GX 
  \<Longrightarrow> ATS_Language0.marked_language cfg_initial_configurations cfgLM_step_relation cfg_marking_condition cfg_marked_effect GX = ATS_Language0.marked_language epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition epdaS_marked_effect G 
  \<Longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfg_productions GX) \<subseteq> epdaH_required_edges G"
  apply(clarsimp)
  apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
  apply(clarsimp)
  apply(rename_tac p)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="F_SDPDA_TO_CFG_STD G" in F_CFG_TRIM__SOUND)
   apply(simp add: F_CFG_TRIM__SpecInput_def)
   apply (metis F_SDPDA_TO_CFG_STD__makes_CFG)
  apply(subgoal_tac "p \<in> cfgLM_language_relevant_productions GX")
   prefer 2
   apply(simp only: F_CFG_TRIM__SpecOutput_def)
   apply(force)
  apply(simp add: cfgLM_language_relevant_productions_def)
  apply(clarsimp)
  apply(subgoal_tac "cfgLM.derivation_initial (F_SDPDA_TO_CFG_STD G) d")
   prefer 2
   apply(simp only: F_CFG_TRIM__SpecOutput_def cfgLM.initial_marking_derivations_def)
   apply(clarsimp)
   apply (metis (mono_tags) F_SDPDA_TO_CFG_STD__makes_CFG cfg_sub_preserves_cfgLM_derivation_initial)
  apply(simp add: cfgLM_language_relevant_productions_def cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(thin_tac "ca \<in> cfg_configurations GX")
  apply(case_tac ca)
  apply(clarsimp)
  apply(rename_tac w)
  apply(subgoal_tac "\<exists>v. liftB v= w")
   prefer 2
   apply(rule_tac x="filterB w" in exI)
   apply(rule liftBDeConv2)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "n\<le> i")
   prefer 2
   apply (metis cfgLM.derivation_initial_is_derivation cfgLM_no_position_beyond_liftB_configuration)
  apply(subgoal_tac "\<exists>m. n+m=i")
   prefer 2
   apply(rule_tac x="i-n" in exI)
   apply(force)
  apply(clarsimp)
  apply(case_tac m)
   apply(clarsimp)
   apply(case_tac n)
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="nat"
      and m="Suc nat"
      in cfgLM.step_detail_before_some_position)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(case_tac c1)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      G="G" and n="nat"
      in F_SDPDA_TO_CFG_STD__reachable_conf_of_certain_form)
      apply(force)
     apply(force)
    apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
   apply(clarsimp)
   apply(erule disjE)+
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(clarsimp)
    apply (metis (erased, hide_lams) append_Cons append_Nil liftB_with_nonterminal_inside setA_liftB_exists setA_substring_prime)
   apply(erule disjE)+
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>v. liftB v= l")
     prefer 2
     apply(rule_tac x="filterB l" in exI)
     apply(rule liftBDeConv2)
     apply(force)
    apply(clarsimp)
    apply(simp add: simpY)
    apply(subgoal_tac "\<exists>v. liftB v= r")
     prefer 2
     apply(rule_tac x="filterB r" in exI)
     apply(rule liftBDeConv2)
     apply(force)
    apply(clarsimp)
    apply(rule event_stack_separation_and_proper_l3_l2_seq_ALT__contra)
    apply(force)
   apply(erule disjE)+
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>v. liftB v= l")
     prefer 2
     apply(rule_tac x="filterB l" in exI)
     apply(rule liftBDeConv2)
     apply(force)
    apply(clarsimp)
    apply(simp add: simpY)
   apply(erule disjE)+
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>v. liftB v= l")
     prefer 2
     apply(rule_tac x="filterB l" in exI)
     apply(rule liftBDeConv2)
     apply(force)
    apply(clarsimp)
    apply(simp add: simpY)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>v. liftB v= l")
    prefer 2
    apply(rule_tac x="filterB l" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(erule disjE)+
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac m)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="n+m"
      and m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac dR="d" and n="n+m" in F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_back_hlp_prime_prime)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add:  cfgLM_step_relation_def)
   apply(simp add: simpY)
   apply(clarsimp)
   apply(simp add: simpY)
  apply(clarsimp)
  apply(simp add: simpY)
  apply(erule_tac x="n" in allE')
  apply(erule_tac x="n+m" in allE)
  apply(clarsimp)
  apply(erule_tac P="setA (cfg_conf c) \<noteq> {}" in impE)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add:  cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: simpY)
  apply(clarsimp)
  apply(case_tac n)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def cfgLM.derivation_def)
  apply(simp add: simpY)
  apply(clarsimp)
  apply(rename_tac n)
  apply(erule impE)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="Suc n"
      and m="Suc (Suc(n+m))"
      in cfgLM.step_detail_before_some_position)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add:  cfgLM_step_relation_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      G="G" and n="n"
      in F_SDPDA_TO_CFG_STD__reachable_conf_of_certain_form)
      apply(force)
     apply(force)
    apply(simp add: get_configuration_def)
   apply(case_tac c1a)
   apply(case_tac c1)
   apply(case_tac c)
   apply(case_tac c2)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>v. liftB v= l")
    prefer 2
    apply(rule_tac x="filterB l" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(subgoal_tac "\<exists>v. liftB v= la")
    prefer 2
    apply(rule_tac x="filterB la" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(subgoal_tac "\<exists>v. liftB v= lb")
    prefer 2
    apply(rule_tac x="filterB lb" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(case_tac r)
    apply(clarsimp)
    apply (metis liftB_with_nonterminal_inside)
   apply(clarsimp)
   apply(rule event_stack_separation_and_proper_l3_l2_seq_ALT__contra2)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="n"
      and m="Suc ((n+m))"
      in epdaH.step_detail_before_some_position)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "x=e2a")
   prefer 2
   apply(rule THE_unique_edge_is_in_delta_prime_2_enhanced_simple_precondition)
       prefer 2
       apply(force)
      apply(force)
     prefer 2
     apply(force)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="Suc n"
      and m="Suc (Suc(n+m))"
      in cfgLM.step_detail_before_some_position)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add:  cfgLM_step_relation_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      G="G" and n="n"
      in F_SDPDA_TO_CFG_STD__reachable_conf_of_certain_form)
      apply(force)
     apply(force)
    apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(case_tac c1b)
   apply(case_tac c1)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>v. liftB v= l")
    prefer 2
    apply(rule_tac x="filterB l" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(subgoal_tac "\<exists>v. liftB v= la")
    prefer 2
    apply(rule_tac x="filterB la" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(subgoal_tac "\<exists>v. liftB v= lb")
    prefer 2
    apply(rule_tac x="filterB lb" in exI)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(case_tac r)
    apply(clarsimp)
    apply (metis liftB_with_nonterminal_inside)
   apply(clarsimp)
   apply(thin_tac "x \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p")
   apply(thin_tac "epdaH.derivation_initial
        G dL")
   apply(thin_tac "dL (Suc n) =
       Some
        (pair (Some e2a)
          (F_SDPDA_TO_CFG_STD__configuration_basic_RL
            \<lparr>cfg_conf = liftB vc @ teA (prod_lhs e2b) # rb\<rparr> w))")
   apply(thin_tac "dL (Suc (n + m)) =
       Some
        (pair eLa
          (F_SDPDA_TO_CFG_STD__configuration_basic_RL
            \<lparr>cfg_conf = liftB vb @ teA (prod_lhs e2) # ra\<rparr> wa))")
   apply(thin_tac "case e1 of None \<Rightarrow> True
       | Some eR' \<Rightarrow>
           eR'
           \<notin> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking G)
               (epda_gamma G) \<longrightarrow>
           (case eLa of None \<Rightarrow> False
            | Some eL' \<Rightarrow>
                eL' \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G eR')")
   apply(thin_tac "epdaH_step_relation G c1a e2a
        (F_SDPDA_TO_CFG_STD__configuration_basic_RL
          \<lparr>cfg_conf = liftB vc @ teA (prod_lhs e2b) # rb\<rparr> w)")
   apply(case_tac p)
   apply(clarsimp)
   apply(rename_tac A)
   apply(case_tac A)
    prefer 2
    apply(simp add: isl3_def)
   apply(clarsimp)
   apply(simp add: isl3_def)
   apply(rule event_stack_separation_and_proper_l3_l2_seq_ALT__contra2)
   apply(force)
  apply(clarsimp)
  apply(simp add: epdaH_required_edges_def)
  apply(rule conjI)
   apply(simp add: epdaH_step_relation_def)
  apply(rule_tac x="derivation_take dL (Suc(n+m))" in exI)
  apply(rule conjI)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rule_tac x="(Suc (n ))" in exI)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
  apply(rule_tac x="Suc ((n+m))" in exI)
  apply(simp add: derivation_take_def epdaH_marking_configurations_def)
  apply(rule conjI)
   prefer 2
   apply(rule_tac d="dL" in epdaH.belongs_configurations)
    apply(rule epdaH.derivation_initial_belongs)
     apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
    apply(force)
   apply(force)
  apply(erule_tac P="setA (cfg_conf c1) \<noteq> {}" in impE)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: simpY)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def cfgLM_step_relation_def)
  apply(clarsimp)
  apply(case_tac c1)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G" and n="Suc (n + m)"
      in F_SDPDA_TO_CFG_STD__reachable_conf_of_certain_form)
     apply(force)
    apply(force)
   apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>v. liftB v= l")
   prefer 2
   apply(rule_tac x="filterB l" in exI)
   apply(rule liftBDeConv2)
   apply(force)
  apply(clarsimp)
  apply(simp add: simpY)
  apply(subgoal_tac "\<exists>v. liftB v= r")
   prefer 2
   apply(rule_tac x="filterB r" in exI)
   apply(rule liftBDeConv2)
   apply (metis (no_types, hide_lams) append_Nil2 setA_decompose setA_liftB_empty)
  apply(clarsimp)
  apply(case_tac e2)
  apply(rename_tac A w)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>v. liftB v= w")
   prefer 2
   apply(rule_tac x="filterB w" in exI)
   apply(rule liftBDeConv2)
   apply (metis (no_types, hide_lams) setA_decompose setA_liftB_empty)
  apply(clarsimp)
  apply(subgoal_tac " v =  va @  vc @  vb")
   prefer 2
   apply(rule liftB_inj)
   apply(simp add: simpY)
  apply(thin_tac "liftB v = liftB va @ liftB vc @ liftB vb")
  apply(clarsimp)
  apply(case_tac A)
   prefer 2
   apply(rule event_stack_separation_and_proper_l3_l2_seq_ALT__contra)
   apply(force)
  apply(case_tac vb)
   prefer 2
   apply(rule event_stack_separation_and_proper_l3_l2_seq_ALT__contra2)
   apply(force)
  apply(clarsimp)
  apply(rule_tac t="(THE v.
                    \<exists>w. liftB va @ [teA (cons_l2 x11 x12)] =
                        liftB w @ liftA v)" and s="[ (cons_l2 x11 x12)]" in ssubst)
   apply (simp add: split1)
  apply(clarsimp)
  apply(thin_tac "epdaH_step_relation G c1a e2a
        \<lparr>epdaH_conf_state =
           case hd (THE v. \<exists>w. cfg_conf c = liftB w @ liftA v) of
           cons_l2 q A \<Rightarrow> q | cons_l3 q A q' \<Rightarrow> q,
           epdaH_conf_history = THE w. \<exists>v. cfg_conf c = liftB w @ liftA v,
           epdaH_conf_stack =
             map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A))
              (THE v. \<exists>w. cfg_conf c = liftB w @ liftA v) @
             wa\<rparr>")
  apply(thin_tac "cfgLM.derivation_initial
        (F_SDPDA_TO_CFG_STD G) d")
  apply(thin_tac "ATS_Language0.marked_language cfg_initial_configurations
        cfgLM_step_relation cfg_marking_condition cfg_marked_effect GX =
       ATS_Language0.marked_language epdaS_initial_configurations
        epdaS_step_relation epdaS_marking_condition epdaS_marked_effect G")
  apply(thin_tac "cfgLM.derivation_initial GX
        d")
  apply(thin_tac "d (Suc n) = Some (pair (Some p) c)")
  apply(thin_tac "d (Suc (Suc (n + m))) =
       Some
        (pair (Some \<lparr>prod_lhs = cons_l2 x11 x12, prod_rhs = liftB vc\<rparr>)
          \<lparr>cfg_conf = liftB va @ liftB vc\<rparr>)")
  apply(thin_tac "d (Suc (n + m)) =
       Some (pair e1 \<lparr>cfg_conf = liftB va @ [teA (cons_l2 x11 x12)]\<rparr>)")
  apply(thin_tac "epdaH.derivation_initial
        G dL")
  apply(thin_tac "dL (Suc n) =
       Some
        (pair (Some e2a)
          \<lparr>epdaH_conf_state =
             case hd (THE v. \<exists>w. cfg_conf c = liftB w @ liftA v) of
             cons_l2 q A \<Rightarrow> q | cons_l3 q A q' \<Rightarrow> q,
             epdaH_conf_history = THE w. \<exists>v. cfg_conf c = liftB w @ liftA v,
             epdaH_conf_stack =
               map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A))
                (THE v. \<exists>w. cfg_conf c = liftB w @ liftA v) @
               wa\<rparr>)")
  apply(thin_tac "dL (Suc (n + m)) =
       Some
        (pair eLa
          \<lparr>epdaH_conf_state =
             case hd (THE v.
                         \<exists>w. liftB va @ [teA (cons_l2 x11 x12)] =
                             liftB w @ liftA v) of
             cons_l2 q A \<Rightarrow> q | cons_l3 q A q' \<Rightarrow> q,
             epdaH_conf_history =
               THE w.
                  \<exists>v. liftB va @ [teA (cons_l2 x11 x12)] =
                      liftB w @ liftA v,
             epdaH_conf_stack =
               map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A))
                (THE v.
                    \<exists>w. liftB va @ [teA (cons_l2 x11 x12)] =
                        liftB w @ liftA v) @
               waa\<rparr>)")
  apply(thin_tac "case e1 of None \<Rightarrow> True
       | Some eR' \<Rightarrow>
           eR'
           \<notin> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking G)
               (epda_gamma G) \<longrightarrow>
           (case eLa of None \<Rightarrow> False
            | Some eL' \<Rightarrow>
                eL' \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G eR')")
  apply(thin_tac "e2a \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p
       ")
  apply(thin_tac "dL n = Some (pair e1a c1a)")
  apply(thin_tac "event_stack_separation_and_proper_l3_l2_seq_ALT
        \<lparr>cfg_conf = liftB va @ [teA (cons_l2 x11 x12)]\<rparr>")
  apply(thin_tac "set wa \<subseteq> epda_gamma G")
  apply(thin_tac "set waa \<subseteq> epda_gamma G")
  apply(thin_tac "p \<in> cfg_productions GX")
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>prod_lhs = cons_l2 x11 x12, prod_rhs = liftB vc\<rparr>
       \<in> cfg_productions (F_SDPDA_TO_CFG_STD G)")
   prefer 2
   apply(simp add: F_CFG_TRIM_def)
   apply(case_tac "F_CFG_EB (F_SDPDA_TO_CFG_STD G)")
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: F_CFG_EB_def)
   apply(case_tac "cfg_initial (F_SDPDA_TO_CFG_STD G)
           \<in> F_CFG_EB__fp (F_SDPDA_TO_CFG_STD G) {}")
    prefer 2
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: F_CFG_EASTD_def Let_def)
  apply(rename_tac vc state stack)
  apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule disjE)+
   apply(clarsimp)
   apply(rename_tac vc state stack e)
   apply(case_tac "edge_event e")
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule disjE)+
   apply(clarsimp)
   apply(rename_tac vc state stack e)
   apply(case_tac "edge_push e")
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule disjE)+
   apply(clarsimp)
   apply(rename_tac vc state stack e)
   apply(case_tac "edge_push e")
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac "edge_event e")
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule disjE)+
   apply(clarsimp)
   apply(rename_tac vc state stack e)
   apply(case_tac "edge_event e")
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(clarsimp)
   apply(case_tac vc)
    apply(force)
   apply(case_tac list)
    apply(force)
   apply(force)
  apply(erule disjE)+
   prefer 2
   apply(clarsimp)
   apply(rename_tac vc state stack e)
   apply(case_tac "edge_push e")
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac "edge_event e")
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def F_SDPDA_TO_CFG_STD__edges_l3_def F_SDPDA_TO_CFG_STD__edges_l2_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(erule disjE)
     apply(clarsimp)
     apply(case_tac vc)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(case_tac vc)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
  done

lemma epdaH_required_edges__subset__epdaH_accessible_edges: "
  epdaH_required_edges G \<subseteq> epdaH_accessible_edges G"
  apply(simp add:   epdaH_required_edges_def epdaH_accessible_edges_def)
  apply(force)
  done

definition PRESERVE_INNER :: "
  ('state, 'event, 'stack) epda 
  \<Rightarrow> ((('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label, (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_configuration) derivation 
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation 
  \<Rightarrow> nat 
  \<Rightarrow> nat 
  \<Rightarrow> bool"
  where
    "PRESERVE_INNER G dR d NI nX \<equiv>
  \<forall>e c. 
    d NI = Some (pair e c)
    \<longrightarrow> (\<exists>p c'. 
          dR NI = Some (pair p c') 
          \<and> setA (cfg_conf c') \<noteq> {} 
          \<and> ((\<forall>i < length (event_stack_separation (cfg_conf c')). 
                discard_font_state 
                  (event_stack_separation (cfg_conf c')) ! i 
                 = (\<lambda>s. (hd s, min_stack d (tl s) NI nX)) (drop i (epdaH_conf_stack c)))) 
          \<and> (\<exists>w. 
              c = F_SDPDA_TO_CFG_STD__configuration_basic_RL c' w 
              \<and> (\<forall>k e c. 
                  NI \<le> k 
                  \<and> d k = Some (pair e c) \<longrightarrow> (ssuffix (epdaH_conf_stack c) w))) 
          \<and> (case e of
             None \<Rightarrow> True 
             | Some e \<Rightarrow> 
                (case p of 
                None \<Rightarrow> False 
                | Some p' \<Rightarrow> e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p')))"

definition PRESERVE_INNER2 :: "
  ('state, 'event, 'stack) epda 
  \<Rightarrow> ((('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label, (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_configuration) derivation 
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation 
  \<Rightarrow> nat 
  \<Rightarrow> nat 
  \<Rightarrow> bool"
  where
    "PRESERVE_INNER2 G dR d n nX \<equiv>
  \<forall>NI \<le> n. PRESERVE_INNER G dR d NI nX"

lemma PRESERVE_INNER2_extend: "
  PRESERVE_INNER2 G dR d n nX
  \<Longrightarrow> PRESERVE_INNER G dR d (Suc n) nX
  \<Longrightarrow> PRESERVE_INNER2 G dR d (Suc n) nX"
  apply(simp add: PRESERVE_INNER2_def)
  apply(clarsimp)
  apply(case_tac "NI=Suc n")
   apply(force)
  apply(force)
  done

lemma PRESERVE_INNER_preserved_under_derivation_append: "
  NI \<le> n 
  \<Longrightarrow> PRESERVE_INNER G dR d NI nX 
  \<Longrightarrow> PRESERVE_INNER G (derivation_append dR dR' n) d NI nX"
  apply(simp add: PRESERVE_INNER_def)
  apply(clarsimp)
  apply(rule_tac x="p" in exI)
  apply(rule_tac x="c'" in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: derivation_append_def)
  apply(rule_tac x="w" in exI)
  apply(clarsimp)
  done

lemma PRESERVE_INNER2_preserved_under_derivation_append: "
  PRESERVE_INNER2 G dR d n nX 
  \<Longrightarrow> PRESERVE_INNER2 G (derivation_append dR dR' n) d n nX"
  apply(simp add: PRESERVE_INNER2_def)
  apply(clarsimp)
  apply(erule_tac x="NI" in allE)
  apply(clarsimp)
  apply(rule PRESERVE_INNER_preserved_under_derivation_append)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt2_help1_1_ENHANCED: "
  valid_simple_dpda G 
  \<Longrightarrow> epdaH.derivation_initial G d 
  \<Longrightarrow> d (Suc n) = Some (pair (Some e2) c) 
  \<Longrightarrow> maximum_of_domain d nX 
  \<Longrightarrow> d n = Some (pair e1 (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)) 
  \<Longrightarrow> epdaH_step_relation G (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa) e2 c 
  \<Longrightarrow> cfgLM.derivation_initial (F_SDPDA_TO_CFG_STD G) dR 
  \<Longrightarrow> PRESERVE_INNER2 G dR d n nX 
  \<Longrightarrow> dR n = Some (pair p c') 
  \<Longrightarrow> setA (liftB waa @ teA A # liftA w) \<noteq> {} 
  \<Longrightarrow> \<forall>i < length (event_stack_separation (liftB waa @ teA A # liftA w)) .discard_font_state (event_stack_separation (liftB waa @ teA A # liftA w)) ! i = (hd (drop i (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop i (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX) 
  \<Longrightarrow> \<forall>k e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa 
  \<Longrightarrow> e2 \<in> epda_delta G 
  \<Longrightarrow> valid_epda_step_label G e2 
  \<Longrightarrow> edge_event e2 = None 
  \<Longrightarrow> edge_pop e2 = [x] 
  \<Longrightarrow> edge_push e2 = [xa, x] 
  \<Longrightarrow> cfg_conf c' = liftB waa @ teA A # liftA w 
  \<Longrightarrow> \<forall>wa t. A # w = wa @ [t] \<longrightarrow> (\<forall>x \<in> set wa. case x of cons_l2 q y \<Rightarrow> False | cons_l3 q1 b q2 \<Rightarrow> True) \<and> (case t of cons_l2 q y \<Rightarrow> True | cons_l3 q1 b q2\<Rightarrow>False) \<and> (\<forall>i < length wa. (case (wa @ [t]) ! i of cons_l3 q1 A q2 \<Rightarrow> q2) = (case (wa @ [t]) ! Suc i of cons_l2 q1 A \<Rightarrow> q1 | cons_l3 q1 A q2 \<Rightarrow>q1)) 
  \<Longrightarrow> A = cons_l3 q1 b q2 
  \<Longrightarrow> \<exists>dR. ATS.derivation_initial cfg_initial_configurations cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) dR \<and> PRESERVE_INNER2 G dR d (Suc n) nX"
  apply(clarsimp)
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "w\<noteq>[]")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a # list")
  apply(subgoal_tac "discard_font_state (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)) ! 0 = (hd (drop 0 (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop 0 (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(erule_tac
      x="0"
      and P="\<lambda>x. x < length (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)) \<longrightarrow> discard_font_state (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)) ! x = (hd (drop x (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop x (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)"
      in allE)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(simp add: discard_font_state_def event_stack_separation_def)
   apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB x @ liftA v)=cons_l3 q1 b q2 # w")
    apply(clarsimp)
   apply (metis SPLIT_2_0 liftA.simps(2) event_stack_separation_def)
  apply(rename_tac a list)(*strict*)
  apply(simp add: discard_font_state_def event_stack_separation_def)
  apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB x @ liftA v) = cons_l3 q1 b q2 # w")
   prefer 2
   apply (metis SPLIT_2_0 liftA.simps(2) event_stack_separation_def)
  apply(clarsimp)
  apply(case_tac "min_stack d (tl (epdaH_conf_stack c)) (Suc n) nX")
   apply(rule successor_min_stack_is_not_empty)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rename_tac qs)
  apply(rename_tac qs)(*strict*)
  apply(subgoal_tac "qs \<in> epda_states G")
   apply(rename_tac qs)(*strict*)
   prefer 2
   apply(rule min_stack_is_in_states)
       apply(rename_tac qs)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac qs)(*strict*)
      apply(force)
     apply(rename_tac qs)(*strict*)
     apply(force)
    apply(rename_tac qs)(*strict*)
    apply(force)
   apply(rename_tac qs)(*strict*)
   apply(force)
  apply(rename_tac qs)(*strict*)
  apply(subgoal_tac "q2 \<in> epda_states G")
   apply(rename_tac qs)(*strict*)
   prefer 2
   apply(rule min_stack_is_in_states)
       apply(rename_tac qs)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac qs)(*strict*)
      apply(force)
     apply(rename_tac qs)(*strict*)
     apply(force)
    apply(rename_tac qs)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac qs)(*strict*)
   apply(force)
  apply(rename_tac qs)(*strict*)
  apply(subgoal_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs=cons_l3 q1 x q2,prod_rhs=[teA (cons_l3   (edge_trg e2) xa qs),teA (cons_l3   qs x q2)]\<rparr> \<lparr>cfg_conf=liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs),teA (cons_l3   qs x q2)]@liftA w\<rparr>")
   apply(rename_tac qs)(*strict*)
   prefer 2
   apply(simp add: cfgLM_step_relation_def)
   apply(rule conjI)
    apply(rename_tac qs)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD_def)
    apply(rule disjI1)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule_tac
      x="e2"
      in bexI)
     apply(rename_tac qs)(*strict*)
     apply(clarsimp)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def)
     apply(simp add: epdaH_step_relation_def)
     apply(clarify)
     apply(rename_tac qs wb)(*strict*)
     apply(simp)
     apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
    apply(rename_tac qs)(*strict*)
    apply(simp add: Let_def)
   apply(rename_tac qs)(*strict*)
   apply(rule_tac
      x="liftB waa"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac qs)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarify)
    apply(rename_tac qs wb)(*strict*)
    apply(simp)
   apply(rename_tac qs)(*strict*)
   apply (metis setA_liftB)
  apply(rename_tac qs)(*strict*)
  apply(rule_tac
      x="derivation_append dR (der2 c' \<lparr>prod_lhs = cons_l3 q1 x q2, prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l3   qs x q2)]\<rparr> \<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l3   qs x q2)] @ liftA w\<rparr>) n"
      in exI)
  apply(rename_tac qs)(*strict*)
  apply(rule conjI)
   apply(rename_tac qs)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac qs)(*strict*)
     apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
     apply(force)
    apply(rename_tac qs)(*strict*)
    apply(force)
   apply(rename_tac qs)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac qs)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac qs)(*strict*)
    apply(rule cfgLM.der2_is_derivation)
    apply(force)
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac qs)(*strict*)
  apply(rule PRESERVE_INNER2_extend)
   apply(rule PRESERVE_INNER2_preserved_under_derivation_append)
   apply(force)
  apply(simp add: PRESERVE_INNER_def)
  apply(rule_tac
      x="Some \<lparr>prod_lhs = cons_l3 q1 x q2, prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l3   qs x q2)]\<rparr>"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l3   qs x q2)] @ liftA w\<rparr>"
      in exI)
  apply(rename_tac qs)(*strict*)
  apply(rule conjI)
   apply(rename_tac qs)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac qs)(*strict*)
  apply(rule conjI)
   apply(rename_tac qs)(*strict*)
   apply(simp (no_asm))
   apply (metis elemInsetA emptyE)
  apply(rename_tac qs)(*strict*)
  apply(rule conjI)
   apply(rename_tac qs)(*strict*)
   apply(thin_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))) q2) # liftA w = liftB x @ liftA v) = cons_l3 q1 (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))) q2 # w")
   apply(rename_tac qs)(*strict*)
   apply(simp add: event_stack_separation_def discard_font_state_def)
   apply(subgoal_tac "(THE v. \<exists>xb. cfg_conf \<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l3   qs x q2)] @ liftA w\<rparr> = liftB xb @ liftA v) = [ (cons_l3   (edge_trg e2) xa qs), (cons_l3 qs x q2)] @ w")
    apply(rename_tac qs)(*strict*)
    apply(clarsimp)
    apply(rename_tac qs i)(*strict*)
    apply(thin_tac "(THE v. \<exists>xb. liftB waa @ teA (cons_l3   (edge_trg e2) xa qs) # teA (cons_l3   qs x q2) # liftA w = liftB xb @ liftA v) = cons_l3 (edge_trg e2) xa qs # cons_l3 qs x q2 # w")
    apply(rename_tac qs i)(*strict*)
    apply(case_tac i)
     apply(rename_tac qs i)(*strict*)
     apply(clarsimp)
     apply(rename_tac qs)(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(clarify)
     apply(rename_tac qs wb)(*strict*)
     apply(simp)
    apply(rename_tac qs i nat)(*strict*)
    apply(erule_tac
      x="nat"
      and P="\<lambda>nat. nat < Suc (length w) \<longrightarrow> (case (cons_l3 q1 (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))) q2 # w) ! nat of cons_l2 q A \<Rightarrow> (A, None) | cons_l3 q1 A q2 \<Rightarrow> (A, Some q2)) = (hd (drop nat (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop nat (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)"
      in allE)
    apply(rename_tac qs i nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac qs nat)(*strict*)
    apply(case_tac nat)
     apply(rename_tac qs nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac qs)(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(clarify)
     apply(rename_tac qs wb)(*strict*)
     apply(simp)
     apply(rule min_stack_preserved)
           apply(rename_tac qs wb)(*strict*)
           apply(force)
          apply(rename_tac qs wb)(*strict*)
          apply(force)
         apply(rename_tac qs wb)(*strict*)
         apply(force)
        apply(rename_tac qs wb)(*strict*)
        apply(force)
       apply(rename_tac qs wb)(*strict*)
       apply(force)
      apply(rename_tac qs wb)(*strict*)
      apply(simp add: epdaH_step_relation_def)
     apply(rename_tac qs wb)(*strict*)
     apply(clarify)
     apply(simp)
    apply(rename_tac qs nat nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac qs nata)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarify)
    apply(rename_tac qs nata wb)(*strict*)
    apply(simp)
    apply(rule min_stack_preserved)
          apply(rename_tac qs nata wb)(*strict*)
          apply(force)
         apply(rename_tac qs nata wb)(*strict*)
         apply(force)
        apply(rename_tac qs nata wb)(*strict*)
        apply(force)
       apply(rename_tac qs nata wb)(*strict*)
       apply(force)
      apply(rename_tac qs nata wb)(*strict*)
      apply(force)
     apply(rename_tac qs nata wb)(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(clarify)
     apply(simp)
     apply (metis tl_drops2)
    apply(rename_tac qs nata wb)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarify)
    apply(simp)
    apply (metis drop_Suc drop_Suc_Cons drop_tl tl_drops)
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply (metis SPLIT_2_0 liftA.simps(2))
  apply(rename_tac qs)(*strict*)
  apply(rule conjI)
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(clarify)
   apply(rename_tac qs wb)(*strict*)
   apply(simp)
   apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
   apply(simp add: Let_def)
   apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   (edge_trg e2) xa qs) # teA (cons_l3   qs x q2) # liftA w = liftB wa @ liftA v) = cons_l3 (edge_trg e2) xa qs # cons_l3 qs x q2 # w")
    apply(rename_tac qs wb)(*strict*)
    prefer 2
    apply (metis SPLIT_2_0 liftA.simps(2) event_stack_separation_def)
   apply(rename_tac qs wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac qs)(*strict*)
   apply(thin_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   (edge_trg e2) xa qs) # teA (cons_l3   qs x q2) # liftA w = liftB wa @ liftA v) = cons_l3 (edge_trg e2) xa qs # cons_l3 qs x q2 # w")
   apply(rename_tac qs)(*strict*)
   apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_trg e2) xa qs) # teA (cons_l3   qs x q2) # liftA w = liftB wa @ liftA v) = waa")
    apply(rename_tac qs)(*strict*)
    prefer 2
    apply (metis SPLIT_2_1 liftA.simps(2) )
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_trg e2) xa qs) # teA (cons_l3   qs x q2) # liftA w = liftB wa @ liftA v) = waa")
   apply(rename_tac qs)(*strict*)
   apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB wa @ liftA v) = waa")
    apply(rename_tac qs)(*strict*)
    prefer 2
    apply (metis SPLIT_2_1)
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB wa @ liftA v) = waa")
   apply(rename_tac qs)(*strict*)
   apply(subgoal_tac "(THE v. \<exists>xa. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB xa @ liftA v) = cons_l3 (edge_src e2) x q2 # w")
    apply(rename_tac qs)(*strict*)
    prefer 2
    apply (metis)
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(THE v. \<exists>xa. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB xa @ liftA v) = cons_l3 (edge_src e2) x q2 # w")
   apply(rename_tac qs)(*strict*)
   apply(rule_tac
      x="wa"
      in exI)
   apply(rule conjI)
    apply(rename_tac qs)(*strict*)
    apply(case_tac c)
    apply(rename_tac qs epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac qs)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac qs)(*strict*)
   apply(clarsimp)
   apply(rename_tac qs k e ca)(*strict*)
   apply(erule_tac
      x="k"
      and P="\<lambda>k. \<forall>e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="ca"
      in allE)
   apply(clarsimp)
  apply(rename_tac qs)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(rule disjI1)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: epdaH_step_relation_def)
  apply(clarify)
  apply(rename_tac qs wb)(*strict*)
  apply(simp)
  apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
  done

lemma F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt2_help1_prime_ENHANCED: "
  valid_simple_dpda G 
  \<Longrightarrow> epdaH.derivation_initial G d 
  \<Longrightarrow> d n = Some (pair e c) 
  \<Longrightarrow> maximum_of_domain d nX 
  \<Longrightarrow> \<exists>dR. cfgLM.derivation_initial (F_SDPDA_TO_CFG_STD G) dR \<and> (PRESERVE_INNER2 G dR d n nX)"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: PRESERVE_INNER2_def PRESERVE_INNER_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[teA (cfg_initial (F_SDPDA_TO_CFG_STD G))]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac e c)(*strict*)
    apply(rule cfgLM.derivation_initialI)
     apply(rename_tac e c)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac e c)(*strict*)
    apply(simp add: get_configuration_def der1_def cfg_initial_configurations_def cfg_configurations_def F_SDPDA_TO_CFG_STD_def)
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac e c)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(simp add: der1_def)
   apply(rule conjI)
    apply(rename_tac e c)(*strict*)
    apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
    apply(simp add: event_stack_separation_def)
    apply(rule_tac
      t="(THE v. \<exists>x. [teA (cfg_initial (F_SDPDA_TO_CFG_STD G))] = liftB x @ liftA v)"
      and s="[cfg_initial (F_SDPDA_TO_CFG_STD G)]"
      in ssubst)
     apply(rename_tac e c)(*strict*)
     apply(rule THE_split1)
    apply(rename_tac e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(simp add: discard_font_state_def)
    apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def)
    apply(simp add: min_stack_def)
    apply(clarsimp)
    apply(rename_tac c x e ca)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaH_conf_stack ca = w @ [epda_box G]")
     apply(rename_tac c x e ca)(*strict*)
     apply(force)
    apply(rename_tac c x e ca)(*strict*)
    apply(rule epda_box_stays_at_bottom_epdaH)
      apply(rename_tac c x e ca)(*strict*)
      apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
     apply(rename_tac c x e ca)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(rule conjI)
      apply(rename_tac c x e ca)(*strict*)
      apply(force)
     apply(rename_tac c x e ca)(*strict*)
     apply(clarsimp)
     apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
    apply(rename_tac c x e ca)(*strict*)
    apply(force)
   apply(rename_tac e c)(*strict*)
   apply(rule conjI)
    apply(rename_tac e c)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(case_tac c)
    apply(rename_tac c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="THE v. \<exists>w. [teA (cfg_initial (F_SDPDA_TO_CFG_STD G))] = liftB w @ liftA v"
      and s="[cfg_initial (F_SDPDA_TO_CFG_STD G)]"
      in ssubst)
     apply(rule THE_split1)
    apply(rule_tac
      t="THE w. \<exists>v. [teA (cfg_initial (F_SDPDA_TO_CFG_STD G))] = liftB w @ liftA v"
      and s="[]"
      in ssubst)
     apply(rule THE_split2)
    apply(simp add: F_SDPDA_TO_CFG_STD_def)
    prefer 2
    apply(rename_tac e c)(*strict*)
    apply(case_tac e)
     apply(rename_tac e c)(*strict*)
     apply(force)
    apply(rename_tac e c a)(*strict*)
    apply(clarsimp)
    apply(rename_tac c a)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation epdaH.initialNotEdgeSome_prime)
   apply(clarsimp)
   apply(rename_tac k e c)(*strict*)
   apply(simp add: ssuffix_def)
   apply(subgoal_tac "\<exists>w. epdaH_conf_stack c = w @ [epda_box G]")
    apply(rename_tac k e c)(*strict*)
    apply(force)
   apply(rename_tac k e c)(*strict*)
   apply(rule epda_box_stays_at_bottom_epdaH)
     apply(rename_tac k e c)(*strict*)
     apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
    apply(rename_tac k e c)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac k e c)(*strict*)
     apply(force)
    apply(rename_tac k e c)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(rename_tac k e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "PRESERVE_INNER G dR d n nX")
   prefer 2
   apply(simp add: PRESERVE_INNER2_def)
  apply(simp add: PRESERVE_INNER_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(thin_tac "case e1 of None \<Rightarrow> True | Some e \<Rightarrow> (case p of None \<Rightarrow> False | Some p' \<Rightarrow> e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p')")
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta G")
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(subgoal_tac "e2 \<in> epda_step_labels G")
    apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
    prefer 2
    apply(rule epdaH.belongs_step_labels)
     apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
      apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   apply(simp add: epda_step_labels_def)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(subgoal_tac "(\<forall>e \<in> epda_delta G. case edge_event e of None \<Rightarrow> edge_push e = [] \<or> (\<exists>x. edge_push e = x # edge_pop e) | Some a \<Rightarrow> edge_pop e = edge_push e)")
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(simp add: valid_simple_dpda_def)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(subgoal_tac "\<exists>x. edge_pop e2=[x]")
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      and P="\<lambda>e2. length (edge_pop e2) = Suc 0"
      in ballE)
    apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def)
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   apply(case_tac "edge_pop e2")
    apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' w a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac n c e1 e2 dR p c' w a list)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' w a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(subgoal_tac "event_stack_separation_and_proper_l3_l2_seq_ALT c'")
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      in F_SDPDA_TO_CFG_STD__reachable_conf_of_certain_form)
     apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(case_tac "edge_event e2")
   apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
   prefer 2
   apply(rename_tac n c e1 e2 dR p c' w a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' w a x)(*strict*)
   apply(simp add: event_stack_separation_and_proper_l3_l2_seq_ALT_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' w a x wa v)(*strict*)
   apply(case_tac v)
    apply(rename_tac n c e1 e2 dR p c' w a x wa v)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' w a x wa)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac n c e1 e2 dR p c' w a x wa v aa list)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa v A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa A w)(*strict*)
   apply(case_tac A)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa A w q b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(subgoal_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs=cons_l2 q b,prod_rhs=[teB a,teA (cons_l2   (edge_trg e2) b)]\<rparr> \<lparr>cfg_conf=liftB (waa@[a]) @ teA (cons_l2   (edge_trg e2) b) # liftA w\<rparr>")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     prefer 2
     apply(simp add: cfgLM_step_relation_def)
     apply(rule conjI)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD_def)
      apply(rule disjI2)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_def)
      apply(rule disjI1)
      apply(rule_tac
      x="e2"
      in bexI)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
       apply(clarsimp)
       apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
       apply(simp add: epdaH_step_relation_def)
       apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
       apply(clarsimp)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(simp add: Let_def)
       apply(subgoal_tac "hd (THE v. \<exists>wa. liftB waa @ teA (cons_l2   q b) # liftA w = liftB wa @ liftA v) = (cons_l2 q b)")
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        apply(clarsimp)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
        apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l2   (edge_src e2) b) # liftA w = liftB wa @ liftA v) = cons_l2 (edge_src e2) b # w")
         apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
         apply(clarsimp)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
        apply(rule_tac
      t="teA (cons_l2   (edge_src e2) b) # liftA w"
      and s="liftA (cons_l2   (edge_src e2) b # w)"
      in ssubst)
         apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
         apply(force)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
        apply(rule_tac
      P="\<lambda>X. (THE v. \<exists>wa. liftB waa @ liftA (cons_l2   (edge_src e2) b # w) = liftB wa @ liftA v) = X"
      and t="cons_l2 (edge_src e2) b # w"
      and s="filterA(liftA (cons_l2   (edge_src e2) b # w))"
      in ssubst)
         apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
         apply (simp add: liftA_vs_filterA)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
        apply(rule THE_split5)
         apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
         apply (metis setB_liftA)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w b wb)(*strict*)
        apply (metis setA_liftB)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(rule_tac
      t="teA (cons_l2   q b) # liftA w"
      and s="liftA (cons_l2 q b # w)"
      in ssubst)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(rule_tac
      t="THE v. \<exists>wa. liftB waa @ liftA (cons_l2 q b # w) = liftB wa @ liftA v"
      and s="cons_l2 q b # w"
      in ssubst)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(rule_tac
      P="\<lambda>X. (THE v. \<exists>wa. liftB waa @ liftA (cons_l2 q b # w) = liftB wa @ liftA v) = X"
      and t="cons_l2 q b # w"
      and s="filterA(liftA (cons_l2 q b # w))"
      in ssubst)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        apply (simp add: liftA_vs_filterA)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(rule THE_split5)
        apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        apply (metis setB_liftA)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply (metis setA_liftB)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(rule_tac
      x="liftB waa"
      in exI)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      apply (metis liftB_commute_one_elem_app)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(rule_tac
      x="derivation_append dR (der2 c' \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teB a, teA (cons_l2   (edge_trg e2) b)]\<rparr> \<lparr>cfg_conf = liftB (waa @ [a]) @ teA (cons_l2   (edge_trg e2) b) # liftA w\<rparr>) n"
      in exI)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation_initial)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
       apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
       apply(rule cfgLM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      apply(rule cfgLM.der2_is_derivation)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(rule PRESERVE_INNER2_extend)
     apply(rule PRESERVE_INNER2_preserved_under_derivation_append)
     apply(force)
    apply(simp add: PRESERVE_INNER_def)
    apply(rule_tac
      x="Some \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teB a, teA (cons_l2   (edge_trg e2) b)]\<rparr>"
      in exI)
    apply(rule_tac
      x="\<lparr>cfg_conf = liftB (waa @ [a]) @ teA (cons_l2   (edge_trg e2) b) # liftA w\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(simp (no_asm))
     apply (metis liftA.simps(2) filterA.simps(1) setB.simps(1) liftB_liftA_split append_Nil2 list.simps(2))
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(case_tac w)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      prefer 2
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b aa list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. w=w'@[x']")
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b aa list)(*strict*)
       prefer 2
       apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b aa list)(*strict*)
      apply(thin_tac "w=aa # list")
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b i)(*strict*)
     apply(thin_tac "setA (liftB waa @ [teA (cons_l2   q b)]) \<noteq> {}")
     apply(simp add: event_stack_separation_def)
     apply(subgoal_tac "(THE v. \<exists>x. liftB (waa @ [a]) @ [teA (cons_l2   (edge_trg e2) b)] = liftB x @ liftA v )=[cons_l2 (edge_trg e2) b]")
      apply(rename_tac n c e1 e2 dR p c' wa a x waa q b i)(*strict*)
      prefer 2
      apply(rule split1)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b i)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b)(*strict*)
     apply(thin_tac "(THE v. \<exists>x. liftB (waa @ [a]) @ [teA (cons_l2   (edge_trg e2) b)] = liftB x @ liftA v) = [cons_l2 (edge_trg e2) b]")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b)(*strict*)
     apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l2   q b)] = liftB x @ liftA v) = [cons_l2 q b]")
      apply(rename_tac n c e1 e2 dR p c' wa a x waa q b)(*strict*)
      prefer 2
      apply(rule split1)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l2   q b)] = liftB x @ liftA v) = [cons_l2 q b]")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b)(*strict*)
     apply(erule_tac
      x="0"
      in allE)
     apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def epdaH_step_relation_def Let_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q b w)(*strict*)
     apply(simp add: discard_font_state_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q w)(*strict*)
     apply(simp add: min_stack_def)
     apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> w)")
      apply(rename_tac n c e1 e2 dR p c' wa a x waa q w)(*strict*)
      prefer 2
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa q w)(*strict*)
     apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(rule_tac
      x="wa"
      in exI)
     apply(rule conjI)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
      apply(case_tac c)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
      apply(clarsimp)
      apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
      apply(subgoal_tac "(THE v. \<exists>wa. liftB (waa @ [a]) @ teA (cons_l2   (edge_trg e2) b) # liftA w = liftB wa @ liftA v) = cons_l2 (edge_trg e2) b # w")
       apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l2   q b) # liftA w = liftB wa @ liftA v) = waa")
        apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        apply(clarsimp)
        apply(subgoal_tac "(THE wa. \<exists>v. liftB (waa @ [a]) @ teA (cons_l2   (edge_trg e2) b) # liftA w = liftB wa @ liftA v) = waa@[a]")
         apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
         apply(clarsimp)
         apply(simp add: option_to_list_def)
         apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l2   q b) # liftA w = liftB wa @ liftA v) = cons_l2 q b # w")
          apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
          apply(clarsimp)
         apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
         apply(rule SPLIT_2_0)
        apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
        apply(rule SPLIT_2_1)
       apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
       apply(rule SPLIT_2_1)
      apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
      apply(rule SPLIT_2_0)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b k e ca)(*strict*)
     apply(erule_tac
      x="k"
      and P="\<lambda>k. \<forall>e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa"
      in allE)
     apply(erule_tac
      x="e"
      in allE)
     apply(erule_tac
      x="ca"
      in allE)
     apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
    apply(rule disjI2)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
    apply(case_tac c)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q b wb epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
    apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l2   q b) # liftA w = liftB wa @ liftA v) = cons_l2 q b # w")
     apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
     apply(clarsimp)
    apply(rename_tac n e1 e2 dR p c' wa a x waa w q b wb)(*strict*)
    apply(rule SPLIT_2_0)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa A w q1 b q2)(*strict*)
   apply(thin_tac "\<forall>wa t. A # w = wa @ [t] \<longrightarrow> (\<forall>x \<in> set wa. case x of cons_l2 q y \<Rightarrow> False | cons_l3 q1 b q2 \<Rightarrow> True) \<and> (case t of cons_l2 q y \<Rightarrow> True | cons_l3 q1 b q2 \<Rightarrow> False) \<and> (\<forall>i<length wa. (case (wa @ [t]) ! i of cons_l3 q1 A q2 \<Rightarrow> q2) = (case (wa @ [t]) ! Suc i of cons_l2 q1 A \<Rightarrow> q1 | cons_l3 q1 A q2 \<Rightarrow> q1))")
   apply(rename_tac n c e1 e2 dR p c' wa a x waa A w q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(subgoal_tac "q2 \<in> epda_states G")
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    prefer 2
    apply(subgoal_tac "c' \<in> cfg_configurations (F_SDPDA_TO_CFG_STD G)")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(simp add: cfg_configurations_def F_SDPDA_TO_CFG_STD_def Let_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p wa a x waa w q1 b q2)(*strict*)
     apply(subgoal_tac "cons_l3 q1 b q2 \<in> setA (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)")
      apply(rename_tac n c e1 e2 dR p wa a x waa w q1 b q2)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p wa a x waa w q1 b q2)(*strict*)
     apply (metis elemInsetA)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(subgoal_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs=cons_l3 q1 b q2,prod_rhs=[teB a,teA (cons_l3   (edge_trg e2) b q2)]\<rparr> \<lparr>cfg_conf=liftB (waa@[a]) @ teA (cons_l3   (edge_trg e2) b q2) # liftA w\<rparr>")
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    prefer 2
    apply(simp add: cfgLM_step_relation_def)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD_def)
     apply(rule disjI1)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
     apply(rule disjI1)
     apply(rule_tac
      x="e2"
      in bexI)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
      apply(clarsimp)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
      apply(simp add: epdaH_step_relation_def)
      apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
      apply(simp add: Let_def)
      apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b q2 # w")
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
      apply(rule SPLIT_2_0)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(rule_tac
      x="liftB waa"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply (metis liftB_commute_one_elem_app)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(rule_tac
      x="derivation_append dR (der2 c' \<lparr>prod_lhs = cons_l3 q1 b q2, prod_rhs = [teB a, teA (cons_l3   (edge_trg e2) b q2)]\<rparr> \<lparr>cfg_conf = liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) b q2) # liftA w\<rparr>) n"
      in exI)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(rule PRESERVE_INNER2_extend)
    apply(rule PRESERVE_INNER2_preserved_under_derivation_append)
    apply(force)
   apply(simp add: PRESERVE_INNER_def)
   apply(rule_tac
      x="Some \<lparr>prod_lhs = cons_l3 q1 b q2, prod_rhs = [teB a, teA (cons_l3   (edge_trg e2) b q2)]\<rparr>"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) b q2) # liftA w\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(simp (no_asm))
    apply (metis liftA.simps(2) filterA.simps(1) setB.simps(1) liftB_liftA_split append_Nil2 list.simps(2))
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(simp (no_asm))
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 i)(*strict*)
    apply(simp add: event_stack_separation_def)
    apply(rule_tac
      t="(THE v. \<exists>x. liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) b q2) # liftA w = liftB x @ liftA v)"
      and s="cons_l3 (edge_trg e2) b q2 # w"
      in ssubst)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 i)(*strict*)
     apply(rule SPLIT_2_0)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 i)(*strict*)
    apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length (THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB x @ liftA v) \<longrightarrow> discard_font_state (THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB x @ liftA v) ! i = (hd (drop i (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop i (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)"
      in allE)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 i)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def epdaH_step_relation_def Let_def)
    apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB wa @ liftA v)=cons_l3 q1 b q2 # w")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 i)(*strict*)
     prefer 2
     apply(rule SPLIT_2_0)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 i)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
    apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB wa @ liftA v)=waa")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
     prefer 2
     apply(rule SPLIT_2_1)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(THE v. \<exists>xa. liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) x q2) # liftA w = liftB xa @ liftA v) = cons_l3 (edge_trg e2) x q2 # w")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(THE v. \<exists>xa. liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) x q2) # liftA w = liftB xa @ liftA v) = cons_l3 (edge_trg e2) x q2 # w")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
     apply(thin_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB wa @ liftA v) = waa")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
     apply(thin_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   (edge_src e2) x q2) # liftA w = liftB wa @ liftA v) = cons_l3 (edge_src e2) x q2 # w")
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
     apply(simp add: discard_font_state_def)
     apply(rule conjI)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
      apply (rule equal_hd)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
     apply(case_tac "min_stack d (tl (drop i (x # map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) w)) @ wa) n nX")
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
      apply(clarsimp)
      apply(simp add: min_stack_def)
      apply(case_tac "\<forall>xa \<le> nX. n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> tl (drop i (x # map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) w)) @ wa)")
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
       prefer 2
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
      apply(erule_tac
      x="xa"
      and P="\<lambda>xa. xa \<le> nX \<longrightarrow> n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> tl (drop i (x # map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) w)) @ wa)"
      in allE)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
      apply(clarsimp)
      apply(rule equal_tl)
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i aa)(*strict*)
     apply(clarsimp)
     apply(simp add: min_stack_def)
     apply(case_tac "\<forall>xa \<le> nX. n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> tl (drop i (x # map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) w)) @ wa)")
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
     apply(case_tac "xa=n")
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac n c e2 dR p c' wa a x waa w q2 i e)(*strict*)
      apply(subgoal_tac "False")
       apply(rename_tac n c e2 dR p c' wa a x waa w q2 i e)(*strict*)
       apply(force)
      apply(rename_tac n c e2 dR p c' wa a x waa w q2 i e)(*strict*)
      apply(rule tl_drops)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
     apply(rule conjI)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
      apply(rule_tac
      x="xa"
      in exI)
      apply(clarsimp)
      apply(rule tl_append)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca)(*strict*)
     apply(rule impI)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb)(*strict*)
     apply(rule_tac
      f="\<lambda>x. epdaH_conf_state (the (get_configuration (d (Min x))))"
      in HOL.arg_cong)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb)(*strict*)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb xc eb cc)(*strict*)
      apply(case_tac "xc=n")
       apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb xc eb cc)(*strict*)
       apply(clarsimp)
       apply(rename_tac n c e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb eb)(*strict*)
       apply(subgoal_tac "False")
        apply(rename_tac n c e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb eb)(*strict*)
        apply(force)
       apply(rename_tac n c e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb eb)(*strict*)
       apply(rule tl_drops)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb xc eb cc)(*strict*)
      apply(clarsimp)
      apply(rule tl_append)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i xa e ca xb ea cb xc eb cc)(*strict*)
     apply(rule sym)
     apply(rule tl_append)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q2 i)(*strict*)
    apply(rule SPLIT_2_0)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(rule_tac
      x="wa"
      in exI)
    apply(rule conjI)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
     apply(case_tac c)
     apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
     apply(clarsimp)
     apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
     apply(subgoal_tac "(THE v. \<exists>wa. liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) b q2) # liftA w = liftB wa @ liftA v) = cons_l3 (edge_trg e2) b q2 # w ")
      apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB wa @ liftA v) = waa")
       apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "(THE wa. \<exists>v. liftB (waa @ [a]) @ teA (cons_l3   (edge_trg e2) b q2) # liftA w = liftB wa @ liftA v) = waa@[a]")
        apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
        apply(clarsimp)
        apply(simp add: option_to_list_def)
        apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b q2 # w")
         apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
         apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
        apply(rule SPLIT_2_0)
       apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
       apply(rule SPLIT_2_1)
      apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
      apply(rule SPLIT_2_1)
     apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
     apply(rule SPLIT_2_0)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 k e ca)(*strict*)
    apply(erule_tac
      x="k"
      and P="\<lambda>k. \<forall>e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa"
      in allE)
    apply(erule_tac
      x="e"
      in allE)
    apply(erule_tac
      x="ca"
      in allE)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
   apply(rule disjI1)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
   apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
   apply(case_tac c)
   apply(rename_tac n c e1 e2 dR p c' wa a x waa w q1 b q2 wb epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
   apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b q2 # w")
    apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 e2 dR p c' wa a x waa w q1 b q2 wb)(*strict*)
   apply(rule SPLIT_2_0)
  apply(rename_tac n c e1 e2 dR p c' w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' w x)(*strict*)
  apply(erule disjE)
   apply(rename_tac n c e1 e2 dR p c' w x)(*strict*)
   apply(simp add: event_stack_separation_and_proper_l3_l2_seq_ALT_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' w x wa v)(*strict*)
   apply(case_tac v)
    apply(rename_tac n c e1 e2 dR p c' w x wa v)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' w x wa)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac n c e1 e2 dR p c' w x wa v a list)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac n c e1 e2 dR p c' wa x waa v A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x waa A w)(*strict*)
   apply(case_tac A)
    apply(rename_tac n c e1 e2 dR p c' wa x waa A w q b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q b)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q b)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q b)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l2   q b) # liftA w = liftB wa @ liftA v) = cons_l2 q b # w")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q b)(*strict*)
     prefer 2
     apply(rule SPLIT_2_0)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
    apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l2   (edge_src e2) x) # liftA w = liftB wa @ liftA v)=waa")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
     prefer 2
     apply(rule SPLIT_2_1)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. epdaH_conf_stack c = w @ [epda_box G]")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
     prefer 2
     apply(rule epda_box_stays_at_bottom_epdaH)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w wb)(*strict*)
    apply(thin_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l2   (edge_src e2) x) # liftA w = liftB wa @ liftA v) = cons_l2 (edge_src e2) x # w")
    apply(rename_tac n c e1 e2 dR p c' wa x waa w wb)(*strict*)
    apply(thin_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l2   (edge_src e2) x) # liftA w = liftB wa @ liftA v) = waa")
    apply(rename_tac n c e1 e2 dR p c' wa x waa w wb)(*strict*)
    apply(case_tac w)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w wb)(*strict*)
     prefer 2
     apply(rename_tac n c e1 e2 dR p c' wa x waa w wb a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. w=w'@[x']")
      apply(rename_tac n c e1 e2 dR p c' wa x waa w wb a list)(*strict*)
      prefer 2
      apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w wb a list)(*strict*)
     apply(thin_tac "w=a # list")
     apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w wb)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
    apply(simp add: event_stack_separation_def)
    apply(subgoal_tac "(THE v. \<exists>xa. liftB waa @ [teA (cons_l2   (edge_src e2) x)] = liftB xa @ liftA v)=[cons_l2 (edge_src e2) x]")
     apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
     prefer 2
     apply(rule split1)
    apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
    apply(clarsimp)
    apply(thin_tac "(THE v. \<exists>xa. liftB waa @ [teA (cons_l2   (edge_src e2) x)] = liftB xa @ liftA v)=[cons_l2 (edge_src e2) x]")
    apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
    apply(thin_tac "setA (liftB waa @ [teA (cons_l2   (edge_src e2) x)]) \<noteq> {}")
    apply(simp add: discard_font_state_def)
    apply(simp add: min_stack_def)
    apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> wb @ [epda_box G])")
     apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="Suc n"
      and P="\<lambda>X. X \<le> nX \<longrightarrow> n \<le> X \<longrightarrow> (\<forall>e c. d X = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> wb @ [epda_box G])"
      in allE)
    apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
    apply(erule impE)
     apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' x waa wb)(*strict*)
    apply (metis epdaH.allPreMaxDomSome_prime epdaH.derivation_initial_is_derivation not_None_eq)
   apply(rename_tac n c e1 e2 dR p c' wa x waa A w q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(subgoal_tac "q2 \<in> epda_states G")
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    prefer 2
    apply(subgoal_tac "c' \<in> cfg_configurations (F_SDPDA_TO_CFG_STD G)")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
     apply(simp add: cfg_configurations_def F_SDPDA_TO_CFG_STD_def Let_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p wa x waa w q1 b q2)(*strict*)
     apply(subgoal_tac "cons_l3 q1 b q2 \<in> setA (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)")
      apply(rename_tac n c e1 e2 dR p wa x waa w q1 b q2)(*strict*)
      apply(thin_tac "\<forall>i<length (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)). discard_font_state (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)) ! i = (hd (drop i (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL \<lparr>cfg_conf = liftB waa @ teA (cons_l3   q1 b q2) # liftA w\<rparr> wa))), min_stack d (tl (drop i (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL \<lparr>cfg_conf = liftB waa @ teA (cons_l3   q1 b q2) # liftA w\<rparr> wa)))) n nX)")
      apply(rename_tac n c e1 e2 dR p wa x waa w q1 b q2)(*strict*)
      apply(thin_tac "\<forall>wa t. cons_l3 q1 b q2 # w = wa @ [t] \<longrightarrow> (\<forall>x \<in> set wa. case x of cons_l2 q y \<Rightarrow> False | cons_l3 q1 b q2 \<Rightarrow> True) \<and> (case t of cons_l2 q y \<Rightarrow> True | cons_l3 q1 b q2 \<Rightarrow> False) \<and> (\<forall>i<length wa. (case (wa @ [t]) ! i of cons_l3 q1 A q2 \<Rightarrow> q2) = (case (wa @ [t]) ! Suc i of cons_l2 q1 A \<Rightarrow> q1 | cons_l3 q1 A q2 \<Rightarrow> q1))")
      apply(rename_tac n c e1 e2 dR p wa x waa w q1 b q2)(*strict*)
      apply(thin_tac "\<forall>k e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa")
      apply(thin_tac "epdaH_step_relation G (F_SDPDA_TO_CFG_STD__configuration_basic_RL \<lparr>cfg_conf = liftB waa @ teA (cons_l3   q1 b q2) # liftA w\<rparr> wa) e2 c")
      apply(rename_tac n c e1 e2 dR p wa x waa w q1 b q2)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p wa x waa w q1 b q2)(*strict*)
     apply (metis elemInsetA)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(subgoal_tac "q2 = edge_trg e2")
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    prefer 2
    apply(erule_tac
      x="0"
      and P="\<lambda>x. x < length (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)) \<longrightarrow> discard_font_state (event_stack_separation (liftB waa @ teA (cons_l3   q1 b q2) # liftA w)) ! x = (hd (drop x (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop x (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)"
      in allE)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    apply(simp add: event_stack_separation_def)
    apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB x @ liftA v) = cons_l3 q1 b q2 # w")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b q2) # liftA w = liftB x @ liftA v) = cons_l3 q1 b q2 # w")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
     apply(simp add: discard_font_state_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 q2)(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
     apply(simp add: Let_def)
     apply(clarsimp)
     apply(simp add: min_stack_def)
     apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e ca. d x = Some (pair e ca) \<longrightarrow> epdaH_conf_stack ca \<noteq> epdaH_conf_stack c)")
      apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 q2)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 q2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
     apply(subgoal_tac "Min ({i. (n \<le> i \<and>i \<le> nX \<and> (\<exists>e ca. d i = Some (pair e ca) \<and> epdaH_conf_stack ca = epdaH_conf_stack c))}) = Suc n")
      apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
     apply(subgoal_tac "Min ({i. (n \<le> i \<and>i \<le> nX \<and> (\<exists>e ca. d i = Some (pair e ca) \<and> epdaH_conf_stack ca = epdaH_conf_stack c))}) = Suc n")
      apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
     apply(rule Min_is_Suc_n)
        apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
        apply(clarsimp)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
       apply(rule_tac
      B="{i. n \<le> i \<and> i \<le> nX}"
      in finite_subset)
        apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
       apply (metis finite_Collect_conjI finite_Collect_le_nat)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca k)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
     apply(clarsimp)
     apply(rule epdaH.allPreMaxDomSome_prime)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
     apply (rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 xa e ca)(*strict*)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule SPLIT_2_0)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(subgoal_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs=cons_l3 q1 b q2,prod_rhs=[]\<rparr> \<lparr>cfg_conf=liftB waa @ liftA w\<rparr>")
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  prefer 2
  apply(simp add: cfgLM_step_relation_def)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD_def)
   apply(rule disjI1)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(rule_tac
    x="e2"
    in bexI)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
    apply(simp add: epdaH_step_relation_def)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
    apply(clarsimp)
    apply(simp add: Let_def)
    apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b (edge_trg e2) # w")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
     prefer 2
     apply(rule SPLIT_2_0)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule_tac
    x="liftB waa"
    in exI)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
  apply (metis setA_liftB)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule_tac
    x="derivation_append dR (der2 c' \<lparr>prod_lhs = cons_l3 q1 b q2, prod_rhs = []\<rparr> \<lparr>cfg_conf = liftB waa @ liftA w\<rparr>) n"
    in exI)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_derivation_initial)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_derivation)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
    apply(rule cfgLM.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(rule cfgLM.der2_is_derivation)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule PRESERVE_INNER2_extend)
  apply(rule PRESERVE_INNER2_preserved_under_derivation_append)
  apply(force)
  apply(simp add: PRESERVE_INNER_def)
  apply(rule_tac
    x="Some \<lparr>prod_lhs = cons_l3 q1 b q2, prod_rhs = []\<rparr>"
    in exI)
  apply(rule_tac
    x="\<lparr>cfg_conf = liftB waa @ liftA w\<rparr>"
    in exI)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(simp (no_asm))
  apply(case_tac w)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   prefer 2
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x waa q1 b a list)(*strict*)
   apply (metis liftA.simps(2) filterA.simps(1) setB.simps(1) liftB_liftA_split append_Nil2 list.simps(2))
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(simp (no_asm))
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
  apply(erule_tac
    x="Suc i"
    and P="\<lambda>x. x < length (event_stack_separation (liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w)) \<longrightarrow> discard_font_state (event_stack_separation (liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w)) ! x = (hd (drop x (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop x (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)"
    in allE)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
  apply(simp add: event_stack_separation_def)
  apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ liftA w = liftB x @ liftA v) = w")
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB x @ liftA v) = cons_l3 q1 b (edge_trg e2) # w")
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
    apply(clarsimp)
    apply(thin_tac "(THE v. \<exists>x. liftB waa @ liftA w = liftB x @ liftA v) = w")
    apply(thin_tac "(THE v. \<exists>x. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB x @ liftA v) = cons_l3 q1 b (edge_trg e2) # w")
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
    apply(simp add: discard_font_state_def)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def epdaH_step_relation_def Let_def)
    apply(clarsimp)
    apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b (edge_trg e2) # w")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
     apply(thin_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w = liftB wa @ liftA v) = cons_l3 (edge_src e2) x (edge_trg e2) # w")
     apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
     apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w = liftB wa @ liftA v) = waa")
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
      apply(clarsimp)
      apply(thin_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w = liftB wa @ liftA v) = waa")
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
      apply(case_tac "min_stack d (tl (drop i (epdaH_conf_stack c))) n nX")
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
       apply(clarsimp)
       apply(simp add: min_stack_def)
       apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e ca. d x = Some (pair e ca) \<longrightarrow> epdaH_conf_stack ca \<noteq> tl (drop i (epdaH_conf_stack c)))")
        apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
        prefer 2
        apply(clarsimp)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i a)(*strict*)
      apply(clarsimp)
      apply(simp add: min_stack_def)
      apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e ca. d x = Some (pair e ca) \<longrightarrow> epdaH_conf_stack ca \<noteq> tl (drop i (epdaH_conf_stack c)))")
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i a)(*strict*)
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i a)(*strict*)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca)(*strict*)
      apply(case_tac "n=xa")
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca)(*strict*)
       apply(clarsimp)
       apply(rename_tac c e1 e2 dR p c' wa x waa w i xa)(*strict*)
       apply(rule tl_drops2)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca)(*strict*)
      apply(rule conjI)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca)(*strict*)
       apply(rule_tac
    x="xa"
    in exI)
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca)(*strict*)
      apply(rule impI)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb)(*strict*)
      apply(rule_tac
    f="\<lambda>x. epdaH_conf_state (the (get_configuration (d (Min x))))"
    in HOL.arg_cong)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb)(*strict*)
      apply(rule order_antisym)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb)(*strict*)
       apply(clarsimp)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb xc eb cc)(*strict*)
       apply(case_tac "xc=n")
        apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb xc eb cc)(*strict*)
        apply(clarsimp)
        apply(rename_tac n c e2 dR p c' wa x waa w i xa e ca xb ea cb eb)(*strict*)
        apply(subgoal_tac "False")
         apply(rename_tac n c e2 dR p c' wa x waa w i xa e ca xb ea cb eb)(*strict*)
         apply(force)
        apply(rename_tac n c e2 dR p c' wa x waa w i xa e ca xb ea cb eb)(*strict*)
        apply(rule tl_drops2)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb xc eb cc)(*strict*)
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' wa x waa w i xa e ca xb ea cb)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x waa w i)(*strict*)
     apply(rule SPLIT_2_1)
    apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
    apply(rule SPLIT_2_0)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
   apply(rule SPLIT_2_0)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b i)(*strict*)
  apply (metis setA_liftB liftA_vs_filterA setB_liftA THE_split5 event_stack_separation_def)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(rule_tac
    x="wa"
    in exI)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
   apply(case_tac c)
   apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
   apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ liftA w = liftB wa @ liftA v) = w")
    apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(thin_tac "(THE v. \<exists>wa. liftB waa @ liftA w = liftB wa @ liftA v) = w")
    apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB wa @ liftA v) = waa")
     apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(THE wa. \<exists>v. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB wa @ liftA v) = waa")
     apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
     apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b (edge_trg e2) # w")
      apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
      apply(clarsimp)
      apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
      apply(thin_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w = liftB wa @ liftA v) = cons_l3 (edge_src e2) x (edge_trg e2) # w")
      apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
      apply(subgoal_tac "(THE wa. \<exists>v. liftB waa @ liftA w = liftB wa @ liftA v) = waa")
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(clarsimp)
       apply(thin_tac "(THE wa. \<exists>v. liftB waa @ liftA w = liftB wa @ liftA v) = waa")
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(simp add: option_to_list_def)
       apply(thin_tac "setA (liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w) \<noteq> {}")
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(erule_tac
    x="Suc 0"
    and P="\<lambda>y. y < length (event_stack_separation (liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w)) \<longrightarrow> discard_font_state (event_stack_separation (liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w)) ! y = (hd (drop y (x # map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) w @ wa)), min_stack d (tl (drop y (x # map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) w @ wa))) n nX)"
    in allE)
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(simp add: event_stack_separation_def)
       apply(subgoal_tac "(THE v. \<exists>xa. liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w = liftB xa @ liftA v) = cons_l3 (edge_src e2) x (edge_trg e2) # w")
        apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
        apply(clarsimp)
        apply(thin_tac "(THE v. \<exists>xa. liftB waa @ teA (cons_l3   (edge_src e2) x (edge_trg e2)) # liftA w = liftB xa @ liftA v) = cons_l3 (edge_src e2) x (edge_trg e2) # w")
        apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
        apply(simp add: discard_font_state_def)
        apply(case_tac w)
         apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
         apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa w a list)(*strict*)
        apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa a list)(*strict*)
        apply(case_tac a)
         apply(rename_tac n e1 e2 dR p c' wa x waa a list q b)(*strict*)
         apply(clarsimp)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q b)(*strict*)
         apply(subgoal_tac "list=[]")
          apply(rename_tac n e1 e2 dR p c' wa x waa list q b)(*strict*)
          apply(clarsimp)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q b)(*strict*)
         apply(case_tac "list")
          apply(rename_tac n e1 e2 dR p c' wa x waa list q b)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q b a lista)(*strict*)
         apply(subgoal_tac "\<exists>w' x'. list=w'@[x']")
          apply(rename_tac n e1 e2 dR p c' wa x waa list q b a lista)(*strict*)
          prefer 2
          apply(rule_tac
    n="length lista"
    in NonEmptyListHasTailElem)
          apply(force)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q b a lista)(*strict*)
         apply(thin_tac "list=a # lista")
         apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa a list q1 b q2)(*strict*)
        apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b q2)(*strict*)
        apply(simp add: min_stack_def)
        apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) list @ wa)")
         apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b q2)(*strict*)
         apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b q2)(*strict*)
        apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c)(*strict*)
        apply(simp add: cfgLM_step_relation_def)
        apply(clarsimp)
        apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c l r)(*strict*)
        apply(subgoal_tac "liftB waa=l")
         apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c l r)(*strict*)
         apply(clarsimp)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c)(*strict*)
         apply(thin_tac "setA (liftB waa) = {}")
         apply(case_tac "list")
          apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c a lista)(*strict*)
         apply(subgoal_tac "\<exists>w' x'. list=w'@[x']")
          apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c a lista)(*strict*)
          prefer 2
          apply(rule_tac
    n="length lista"
    in NonEmptyListHasTailElem)
          apply(force)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c a lista)(*strict*)
         apply(thin_tac "list=a # lista")
         apply(clarsimp)
         apply(rename_tac n e1 e2 dR p c' wa x waa q1 b xa e c w' x')(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c l r)(*strict*)
        apply(rule split_decide1_x)
          apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c l r)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c l r)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 dR p c' wa x waa list q1 b xa e c l r)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(rule SPLIT_2_0)
      apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
      apply(rule_tac
    t="(THE wa. \<exists>v. liftB waa @ liftA w = liftB wa @ liftA v)"
    in ssubst)
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(rule THE_split6)
        apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
        apply(rule setB_liftA)
       apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac n e1 e2 dR p c' wa x waa w)(*strict*)
      apply(rule liftBDeConv1)
     apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
     apply(rule SPLIT_2_0)
    apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
    apply(rule SPLIT_2_1)
   apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
   apply (metis setA_liftB liftA_vs_filterA setB_liftA THE_split5 event_stack_separation_def)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b k e ca)(*strict*)
  apply(erule_tac
    x="k"
    and P="\<lambda>k. \<forall>e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa"
    in allE)
  apply(erule_tac
    x="e"
    in allE)
  apply(erule_tac
    x="ca"
    in allE)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b)(*strict*)
  apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
  apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac n c e1 e2 dR p c' wa x waa w q1 b epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
  apply(subgoal_tac "(THE v. \<exists>wa. liftB waa @ teA (cons_l3   q1 b (edge_trg e2)) # liftA w = liftB wa @ liftA v) = cons_l3 q1 b (edge_trg e2) # w")
  apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 dR p c' wa x waa w q1 b epdaH_conf_stacka)(*strict*)
  apply(rule SPLIT_2_0)
  apply(rename_tac n c e1 e2 dR p c' w x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' w x xa)(*strict*)
  apply(simp add: event_stack_separation_and_proper_l3_l2_seq_ALT_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' w x xa wa v)(*strict*)
  apply(case_tac v)
  apply(rename_tac n c e1 e2 dR p c' w x xa wa v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' w x xa wa)(*strict*)
  apply (metis setA_liftB)
  apply(rename_tac n c e1 e2 dR p c' w x xa wa v a list)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa v A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa A w)(*strict*)
  apply(case_tac A)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa A w q b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa w q b)(*strict*)
  apply(case_tac w)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa w q b)(*strict*)
  prefer 2
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa w q b a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w=w'@[x']")
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa w q b a list)(*strict*)
   prefer 2
   apply(rule_tac
    n="length list"
    in NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa w q b a list)(*strict*)
  apply(thin_tac "w=a # list")
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa w q b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(thin_tac "setA (liftB waa @ [teA (cons_l2   q b)]) \<noteq> {}")
  apply(case_tac "min_stack d (tl(epdaH_conf_stack c)) (Suc n) nX")
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(subgoal_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs=cons_l2 q b,prod_rhs=[teA (cons_l2   (edge_trg e2) xa)]\<rparr> \<lparr>cfg_conf=liftB waa @ [teA (cons_l2   (edge_trg e2) xa)]\<rparr>")
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   prefer 2
   apply(simp add: cfgLM_step_relation_def)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD_def)
    apply(rule disjI2)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_def)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule_tac
    x="e2"
    in bexI)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
     apply(clarsimp)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w)(*strict*)
     apply(simp add: Let_def)
     apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = [(cons_l2 q b)]")
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w)(*strict*)
     apply (metis split1 event_stack_separation_def)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(rule_tac
    x="liftB waa"
    in exI)
   apply(clarsimp)
   apply (metis setA_liftB)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(rule_tac
    x="derivation_append dR (der2 c' \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teA (cons_l2   (edge_trg e2) xa)]\<rparr> \<lparr>cfg_conf = liftB waa @ [teA (cons_l2   (edge_trg e2) xa)]\<rparr>) n"
    in exI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
     apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(rule cfgLM.der2_is_derivation)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(rule PRESERVE_INNER2_extend)
   apply(rule PRESERVE_INNER2_preserved_under_derivation_append)
   apply(force)
  apply(simp add: PRESERVE_INNER_def)
  apply(rule_tac
    x="Some \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teA (cons_l2   (edge_trg e2) xa)]\<rparr>"
    in exI)
  apply(rule_tac
    x="\<lparr>cfg_conf = liftB waa @ [teA (cons_l2   (edge_trg e2) xa)]\<rparr>"
    in exI)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(simp (no_asm))
   apply (metis elemInsetA emptyE)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(simp (no_asm))
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b i)(*strict*)
   apply(simp add: event_stack_separation_def)
   apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l2   (edge_trg e2) xa)] = liftB x @ liftA v) = [cons_l2 (edge_trg e2) xa]")
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b i)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(thin_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l2   (edge_trg e2) xa)] = liftB x @ liftA v) = [cons_l2 (edge_trg e2) xa]")
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(simp add: discard_font_state_def)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def epdaH_step_relation_def Let_def)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b i)(*strict*)
   apply (metis split1 event_stack_separation_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(rule_tac
    x="x # wa"
    in exI)
   apply(rule conjI)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w)(*strict*)
    apply(case_tac c)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
    apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   (edge_trg e2) xa)] = liftB w @ liftA v) = [ (cons_l2   (edge_trg e2) xa)]")
     apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
     prefer 2
     apply (metis split1 event_stack_separation_def)
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = waa")
     apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   (edge_trg e2) xa)] = liftB w @ liftA v) = waa")
      apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
      apply(clarsimp)
      apply(simp add: option_to_list_def)
      apply(thin_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   (edge_trg e2) xa)] = liftB w @ liftA v) = waa")
      apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
      apply(thin_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = waa")
      apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
      apply(thin_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   (edge_trg e2) xa)] = liftB w @ liftA v) = [cons_l2 (edge_trg e2) xa]")
      apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
      apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v)=[cons_l2 q b]")
       apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
       apply(clarsimp)
      apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
      apply (metis split1 event_stack_separation_def)
     apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
     apply(rule split2)
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
    apply(rule split2)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca)(*strict*)
   apply(erule_tac
    x="k"
    and P="\<lambda>k. \<forall>e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa"
    in allE)
   apply(erule_tac
    x="e"
    in allE)
   apply(erule_tac
    x="ca"
    in allE)
   apply(clarsimp)
   apply(simp add: ssuffix_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca xb)(*strict*)
   apply(case_tac xb)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca xb a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xb=w'@[x']")
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca xb a list)(*strict*)
    prefer 2
    apply(rule_tac
    n="length list"
    in NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca xb a list)(*strict*)
   apply(thin_tac "xb=a # list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca w' x')(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca w' x' w)(*strict*)
   apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = [cons_l2 q b]")
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca w' x' w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
    apply(subgoal_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   (edge_src e2) x)] = liftB w @ liftA v)=waa")
     apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   (edge_src e2) x)] = liftB w @ liftA v) = waa")
     apply(thin_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   (edge_src e2) x)] = liftB w @ liftA v) = [cons_l2 (edge_src e2) x]")
     apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
     apply(case_tac "x=x'")
      apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
      apply(simp add: min_stack_def)
      apply(case_tac "\<forall>x \<le> nX. Suc n \<le> x \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> x' # w)")
       apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
       prefer 2
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
      apply(clarsimp)
      apply(erule_tac
    x="k"
    and P="\<lambda>k. k \<le> nX \<longrightarrow> Suc n \<le> k \<longrightarrow> (\<forall>e c. d k = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> x' # w)"
    in allE)
      apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
      apply(erule impE)
       apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
       apply(rule epdaH.allPreMaxDomSome_prime)
         apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
         apply (rule epdaH.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' xa waa k e ca x' w)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
     apply(clarsimp)
     apply(simp add: min_stack_def)
     apply(case_tac "\<forall>xa \<le> nX. Suc n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> x # w)")
      apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
      prefer 2
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
     apply(subgoal_tac "(\<forall>e2 c2. d (Suc n+(k-Suc n)) = Some (pair e2 c2) \<longrightarrow> (\<exists>v2. epdaH_conf_stack c2 = v2 @ x # w))")
      apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
      prefer 2
      apply(rule_tac
    d="d"
    and n="Suc n"
    in never_not_present_implies_always_present)
           apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
           apply(force)
          apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
          apply(force)
         apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
         apply(force)
        apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 dR p c' x xa waa k e ca w' x' w)(*strict*)
    apply(rule split2)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b k e ca w' x' w)(*strict*)
   apply(rule split1)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(rule disjI2)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w)(*strict*)
  apply(case_tac c)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
  apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = [cons_l2 q b]")
   apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 e2 dR p c' wa x xa waa q b w)(*strict*)
  apply(rule split1)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b a)(*strict*)
  apply(rename_tac qs)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(subgoal_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs=cons_l2 q b,prod_rhs=[teA (cons_l3   (edge_trg e2) xa qs),teA (cons_l2   qs b)]\<rparr> \<lparr>cfg_conf=liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs),teA (cons_l2   qs b)]\<rparr>")
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  prefer 2
  apply(simp add: cfgLM_step_relation_def)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD_def)
   apply(rule disjI2)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_def)
   apply(rule disjI2)
   apply(rule disjI2)
   apply(rule_tac
    x="e2"
    in bexI)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(simp add: epdaH_step_relation_def)
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
    apply(simp add: Let_def)
    apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = [(cons_l2 q b)]")
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' x xa waa qs w)(*strict*)
     apply(subgoal_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   (edge_src e2) x)] = liftB w @ liftA v)=waa")
      apply(rename_tac n c e1 e2 dR p c' x xa waa qs w)(*strict*)
      apply(clarsimp)
      apply(simp add: min_stack_def)
      apply(case_tac "\<forall>xa \<le> nX. Suc n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> x # w)")
       apply(rename_tac n c e1 e2 dR p c' x xa waa qs w)(*strict*)
       apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' x xa waa qs w)(*strict*)
      apply(clarsimp)
      apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
      apply(subgoal_tac "\<exists>e c. d (Min ({ i. (Suc n \<le> i \<and> i \<le> nX \<and> (\<exists>e c. d i = Some (pair e c) \<and> epdaH_conf_stack c = x # w))})) = Some (pair e c)")
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
       apply(clarsimp)
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
       apply(simp add: get_configuration_def)
       apply(subgoal_tac "cb \<in> epdaH_configurations G")
        apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
        apply(simp add: epdaH_configurations_def)
        apply(clarsimp)
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
       apply(rule epdaH.belongs_configurations)
        apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
        apply(rule epdaH.derivation_initial_belongs)
         apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca ea cb)(*strict*)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
      apply(rule_tac
    m="xaa"
    in epdaH.pre_some_position_is_some_position)
        apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
        apply(rule epdaH.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
       apply(force)
      apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
      apply(rule Min_le)
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
       apply(rule_tac
    B="{i. n \<le> i \<and> i \<le> nX}"
    in finite_subset)
        apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
        apply(force)
       apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
       apply (metis finite_Collect_conjI finite_Collect_le_nat)
      apply(rename_tac n c e1 e2 dR p c' x xa waa w xaa e ca)(*strict*)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' x xa waa qs w)(*strict*)
     apply(rule split2)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
    apply(rule split1)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule_tac
    x="liftB waa"
    in exI)
  apply(clarsimp)
  apply (metis setA_liftB)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule_tac
    x="derivation_append dR (der2 c' \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]\<rparr> \<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]\<rparr>) n"
    in exI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_derivation_initial)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_derivation)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(rule cfgLM.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
   apply(rule cfgLM.der2_is_derivation)
   apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule PRESERVE_INNER2_extend)
  apply(rule PRESERVE_INNER2_preserved_under_derivation_append)
  apply(force)
  apply(simp add: PRESERVE_INNER_def)
  apply(rule_tac
    x="Some \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]\<rparr>"
    in exI)
  apply(rule_tac
    x="\<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]\<rparr>"
    in exI)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(simp (no_asm))
  apply (metis elemInsetA emptyE)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(simp (no_asm))
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i)(*strict*)
  apply(simp add: event_stack_separation_def)
  apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)] = liftB x @ liftA v) = [(cons_l3   (edge_trg e2) xa qs), (cons_l2 qs b)]")
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i)(*strict*)
   apply(clarsimp)
   apply(simp add: discard_font_state_def)
   apply(case_tac i)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(simp add: epdaH_step_relation_def F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i nat)(*strict*)
   apply(case_tac nat)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(erule_tac
    x="0"
    and P="\<lambda>y. y < length (THE v. \<exists>x. liftB waa @ [teA (cons_l2   q b)] = liftB x @ liftA v) \<longrightarrow> (case (THE v. \<exists>x. liftB waa @ [teA (cons_l2   q b)] = liftB x @ liftA v) ! y of cons_l2 q A \<Rightarrow> (A, None) | cons_l3 q1 A q2 \<Rightarrow> (A, Some q2)) = (hd (drop y (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), min_stack d (tl (drop y (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))) n nX)"
    in allE)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l2   q b)] = liftB x @ liftA v) = [cons_l2 q b]")
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs)(*strict*)
     apply(rule conjI)
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs)(*strict*)
      apply(simp add: epdaH_step_relation_def)
      apply(clarify)
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs w)(*strict*)
      apply(simp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs)(*strict*)
     apply(thin_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))] = liftB x @ liftA v) = [cons_l3 (edge_trg e2) xa qs, cons_l2 qs (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))]")
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs)(*strict*)
     apply(thin_tac "(THE v. \<exists>x. liftB waa @ [teA (cons_l2   q (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))] = liftB x @ liftA v) = [cons_l2 q (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))]")
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs)(*strict*)
     apply(thin_tac "min_stack d (tl (epdaH_conf_stack c)) (Suc n) nX = Some qs")
     apply(thin_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs = cons_l2 q (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))), prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))]\<rparr> \<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))]\<rparr>")
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q qs)(*strict*)
     apply(simp add: min_stack_def)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q)(*strict*)
     apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
     apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> tl (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))")
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
      prefer 2
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
     apply(clarsimp)
     apply(erule_tac
    x="xb"
    and P="\<lambda>xb. xb \<le> nX \<longrightarrow> n \<le> xb \<longrightarrow> (\<forall>e c. d xb = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> tl (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa)))"
    in allE)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "tl (drop (Suc 0) (epdaH_conf_stack c)) = tl (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))")
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
     apply(simp (no_asm) add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
     apply(simp (no_asm) add: Let_def)
     apply(rule_tac
    t="cfg_conf c'"
    and s="liftB waa @ [teA (cons_l2   q (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))]"
    in ssubst)
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
      apply(force)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
     apply(rule_tac
    t="(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))] = liftB w @ liftA v)"
    and s="[ (cons_l2 q (hd (epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' wa))))]"
    in ssubst)
      apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: epdaH_step_relation_def)
      apply(clarsimp)
     apply(rename_tac n c e1 e2 dR p c' wa x xa waa q xb e ca)(*strict*)
     apply(rule split1)
    apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
    apply(rule split1)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs i)(*strict*)
  apply (metis SPLIT_2_0 liftA.simps(1) liftA.simps(2) event_stack_separation_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule conjI)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(rule_tac
    x="wa"
    in exI)
  apply(rule conjI)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
   apply(case_tac c)
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
   apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)] = liftB w @ liftA v) = [ (cons_l3   (edge_trg e2) xa qs), (cons_l2 qs b)]")
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
    prefer 2
    apply (metis SPLIT_2_0 liftA.simps(1) liftA.simps(2) event_stack_separation_def)
   apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = waa")
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "(THE w. \<exists>v. liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)] = liftB w @ liftA v) = waa")
     apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = [cons_l2 q b]")
      apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
      apply(clarsimp)
     apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
     apply(rule split1)
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
    apply(thin_tac "\<forall>i<length (event_stack_separation (liftB waa @ [teA (cons_l2   q b)])). discard_font_state (event_stack_separation (liftB waa @ [teA (cons_l2   q b)])) ! i = (hd (drop i (map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) (THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v)) @ drop (i - length (THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v)) wa), min_stack d (tl (drop i (map (case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q A q'. A)) (THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v)) @ drop (i - length (THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v)) wa)) n nX)")
    apply(thin_tac "cfgLM_step_relation (F_SDPDA_TO_CFG_STD G) c' \<lparr>prod_lhs = cons_l2 q b, prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]\<rparr> \<lparr>cfg_conf = liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]\<rparr>")
    apply(thin_tac " (case hd (THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) of cons_l2 q A \<Rightarrow> q | cons_l3 q A q' \<Rightarrow> q) = edge_src e2")
    apply(thin_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)] = liftB w @ liftA v) = [cons_l3 (edge_trg e2) xa qs, cons_l2 qs b]")
    apply(rule_tac
    t="liftB waa @ [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs b)]"
    and s="liftB waa @ teA (cons_l3   (edge_trg e2) xa qs) # liftA [cons_l2 qs b]"
    in ssubst)
     apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
    apply(rule SPLIT_2_1)
   apply(rename_tac n e1 e2 dR p c' wa x xa waa q b qs w)(*strict*)
   apply (metis split2)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs k e ca)(*strict*)
  apply(erule_tac
    x="k"
    and P="\<lambda>k. \<forall>e c. n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) wa"
    in allE)
  apply(erule_tac
    x="e"
    in allE)
  apply(erule_tac
    x="ca"
    in allE)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
  apply(rule disjI2)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(simp add: epdaH_step_relation_def Let_def F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
  apply(subgoal_tac "(THE v. \<exists>w. liftB waa @ [teA (cons_l2   q b)] = liftB w @ liftA v) = [cons_l2 q b]")
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  prefer 2
  apply(rule split1)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa q b qs)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
  apply(subgoal_tac "(\<forall>e \<in> cfg_productions (F_SDPDA_TO_CFG_STD G). prod_lhs e \<in> cfg_nonterminals (F_SDPDA_TO_CFG_STD G) \<and> setA (prod_rhs e) \<subseteq> cfg_nonterminals (F_SDPDA_TO_CFG_STD G) \<and> setB (prod_rhs e) \<subseteq> cfg_events (F_SDPDA_TO_CFG_STD G))")
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
  prefer 2
  apply(subgoal_tac "valid_cfg (F_SDPDA_TO_CFG_STD G)")
   apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
   apply(simp add: valid_cfg_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
  apply(rule F_SDPDA_TO_CFG_STD__makes_CFG)
  apply(force)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
  apply(erule_tac
    x="\<lparr>prod_lhs = cons_l2 (edge_src e2) x, prod_rhs = [teA (cons_l3   (edge_trg e2) xa qs), teA (cons_l2   qs x)]\<rparr>"
    in ballE)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
  prefer 2
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa qs l r)(*strict*)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def)
  apply(rename_tac n c e1 e2 dR p c' wa x xa waa A w q1 b q2)(*strict*)
  apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt2_help1_1_ENHANCED)
                   apply(rename_tac n c e1 e2 dR p c' wa x xa waa A w q1 b q2)(*strict*)
                   apply(force)
                  apply(force)
                 apply(force)
                apply(force)
               apply(force)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  apply(force)
  apply(force)
  done

lemma F_SDPDA_TO_LR1_STD__computes__epdaH_required_edges__part2: "
  valid_simple_dpda G 
  \<Longrightarrow> F_CFG_TRIM (F_SDPDA_TO_CFG_STD G) = Some GX 
  \<Longrightarrow> valid_cfg GX 
  \<Longrightarrow> ATS_Language0.marked_language cfg_initial_configurations cfgLM_step_relation cfg_marking_condition cfg_marked_effect GX = ATS_Language0.marked_language epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition epdaS_marked_effect G 
  \<Longrightarrow> epdaH_required_edges G \<subseteq> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfg_productions GX)"
  apply(clarsimp)
  apply(simp add: epdaH_required_edges_def)
  apply(clarsimp)
  apply(simp add: epdaH_accessible_edges_def F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def cfgLM_accessible_productions_def F_SDPDA_TO_CFG_STD__SpecInput_def cfgLM.get_accessible_destinations_def)
  apply(subgoal_tac "\<exists>d. cfg_marking_condition (F_SDPDA_TO_CFG_STD G) d \<and> cfgLM.derivation_initial (F_SDPDA_TO_CFG_STD G) d \<and> (\<exists>i p c. d i = Some (pair (Some p) c) \<and> x \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p )")
   apply(clarsimp)
   apply(rule_tac
      x="p"
      in bexI)
    apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="F_SDPDA_TO_CFG_STD G" in F_CFG_TRIM__SOUND)
    apply(simp add: F_CFG_TRIM__SpecInput_def)
    apply (metis F_SDPDA_TO_CFG_STD__makes_CFG)
   apply(subgoal_tac "cfgLM.derivation_initial GX da")
    prefer 2
    apply(simp only: F_CFG_TRIM__SpecOutput_def cfgLM.initial_marking_derivations_def)
    apply(clarsimp)
    apply(force)
   apply(subgoal_tac "p \<in> cfg_step_labels (GX)")
    prefer 2
    apply(rule cfgLM.belongs_step_labels)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: cfg_step_labels_def)
  apply(thin_tac "x \<in> epda_delta G")
  apply(subgoal_tac "\<exists>m. n+m=k")
   prefer 2
   apply(rule_tac x="k-n" in exI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e d n c eX ca m)
  apply(subgoal_tac "\<exists>d. epdaH.derivation_initial
        G d \<and>
       d n = Some (pair (Some e) c) \<and>
       d (n + m) = Some (pair eX ca) \<and>
       ca \<in> epdaH_marking_configurations G
       \<and> maximum_of_domain d (n+m) ")
   prefer 2
   apply(rule_tac
      x="derivation_take d (n+m)"
      in exI)
   apply(rule conjI)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rule conjI)
    apply(simp add: derivation_take_def)
   apply(rule conjI)
    apply(simp add: derivation_take_def)
   apply(clarsimp)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(thin_tac "epdaH.derivation_initial G d")
  apply(thin_tac "d n = Some (pair (Some e) c)")
  apply(thin_tac "d (n + m) = Some (pair eX ca)")
  apply(thin_tac "ca \<in> epdaH_marking_configurations G")
  apply(clarsimp)
  apply(rename_tac d)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule_tac n="n+m" in F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt2_help1_prime_ENHANCED)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: PRESERVE_INNER2_def)
  apply(erule_tac x="n" in allE')
  apply(erule_tac x="n+m" in allE)
  apply(clarsimp)
  apply(simp add: PRESERVE_INNER_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G" and n="n+m"
      in F_SDPDA_TO_CFG_STD__reachable_conf_of_certain_form)
     apply(force)
    apply(force)
   apply(simp add: get_configuration_def)
  apply(case_tac p)
   apply(clarsimp)
  apply(clarsimp)
  apply(thin_tac "\<forall>i<length (event_stack_separation (cfg_conf c')).
          discard_font_state (event_stack_separation (cfg_conf c')) ! i =
          (hd (drop i
                (epdaH_conf_stack
                  (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' w))),
           min_stack d
            (tl (drop i
                  (epdaH_conf_stack
                    (F_SDPDA_TO_CFG_STD__configuration_basic_RL c' w))))
            n (n + m))")
  apply(thin_tac "\<forall>k e c.
          n \<le> k \<and> d k = Some (pair e c) \<longrightarrow> ssuffix (epdaH_conf_stack c) w")
  apply(thin_tac "case eX of None \<Rightarrow> True
       | Some e \<Rightarrow>
           (case pa of None \<Rightarrow> False
           | Some p' \<Rightarrow> e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p')")
  apply(erule_tac x="n+m" and P="%k. \<forall>e c.
          n + m \<le> k \<and> d k = Some (pair e c) \<longrightarrow>
          ssuffix (epdaH_conf_stack c) wa"  in allE)
  apply(clarsimp)
  apply(simp add: event_stack_separation_and_proper_l3_l2_seq_ALT_def)
  apply(clarsimp)
  apply(simp add: event_stack_separation_def)
  apply(subgoal_tac "(THE va. \<exists>x. liftB wb @ liftA v = liftB x @ liftA va) = v")
   prefer 2
   apply(rule split_XX2)
  apply(clarsimp)
  apply(simp add: simpY)
  apply(subgoal_tac "\<forall>i<length v.
          discard_font_state v ! i =
          (hd (drop i
                (epdaH_conf_stack
                  (F_SDPDA_TO_CFG_STD__configuration_basic_RL c'a wa))),
           None)")
   prefer 2
   apply(clarsimp)
   apply(erule_tac x="i" in allE)
   apply(clarsimp)
   apply(simp add: min_stack_def)
   apply(case_tac "epdaH_conf_stack (F_SDPDA_TO_CFG_STD__configuration_basic_RL c'a wa)")
    apply(simp add: F_SDPDA_TO_CFG_STD__configuration_basic_RL_def)
   apply(clarsimp)
   apply(case_tac i)
    apply(force)
   apply(metis tl_drops)
  apply(thin_tac "\<forall>i<length v.
          discard_font_state v ! i =
          (hd (drop i
                (epdaH_conf_stack
                  (F_SDPDA_TO_CFG_STD__configuration_basic_RL c'a wa))),
           min_stack d
            (tl (drop i
                  (epdaH_conf_stack
                    (F_SDPDA_TO_CFG_STD__configuration_basic_RL c'a wa))))
            (n + m) (n + m))")
  apply(rule_tac xs="v" in rev_cases)
   apply(force)
  apply(clarsimp)
  apply(case_tac c'a)
  apply(clarsimp)
  apply(rule_tac xs="ys" in rev_cases)
   prefer 2
   apply(clarsimp)
   apply(erule_tac x="length ysa" in allE)
   apply(clarsimp)
   apply(subgoal_tac "snd(discard_font_state (ysa @ [ya, y]) ! length ysa) \<noteq> None")
    apply(force)
   apply(simp only: discard_font_state_def F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def)
   apply(clarsimp)
   apply(case_tac "ysa @ [ya, y]")
    apply(force)
   apply(clarsimp)
   apply(case_tac ya)
    apply(clarsimp)
    apply(rule_tac xs="list" in rev_cases)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac ya)
     prefer 2
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac aa)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac ysa)
     apply(clarsimp)
    apply(clarsimp)
   apply(clarsimp)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(rename_tac state1 stack state2)
   apply(thin_tac "ysa @ [cons_l3 state1 stack state2, y] = aa # list")
   apply(subgoal_tac "(map (case_DT_l2_l3_nonterminals (\<lambda>q A. (A, None))
              (\<lambda>q1 A q2. (A, Some q2)))
         ysa @
        [(stack, Some state2),
         case y of cons_l2 q A \<Rightarrow> (A, None)
         | cons_l3 q1 A q2 \<Rightarrow> (A, Some q2)]) !
       length ysa = (stack, Some state2)")
    apply(force)
   apply(thin_tac "X" for X)
   apply (metis length_map nth_append_length)
  apply(clarsimp)
  apply(case_tac y)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac state stack)
  apply(thin_tac "(THE va.
           \<exists>x. liftB wb @ [teA (cons_l2 state stack)] = liftB x @ liftA va) =
       [cons_l2 state stack]")
  apply(rule_tac
      x="derivation_append dR (der2 \<lparr>cfg_conf = liftB wb @ [teA (cons_l2 state stack)]\<rparr> \<lparr>prod_lhs=cons_l2 state stack, prod_rhs=[]\<rparr> \<lparr>cfg_conf = liftB wb\<rparr>) (n+m)"
      in exI)
  apply(subgoal_tac "cfgLM.derivation_initial
        (F_SDPDA_TO_CFG_STD G)
        (derivation_append dR
          (der2 \<lparr>cfg_conf = liftB wb @ [teA (cons_l2 state stack)]\<rparr>
            \<lparr>prod_lhs = cons_l2 state stack, prod_rhs = []\<rparr>
            \<lparr>cfg_conf = liftB wb\<rparr>)
          (n + m))")
   prefer 2
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply (metis F_SDPDA_TO_CFG_STD__makes_CFG)
    apply(force)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rule cfgLM.der2_is_derivation)
    apply(simp add: cfgLM_step_relation_def)
    apply(rule conjI)
     prefer 2
     apply(rule_tac x="liftB wb" in exI)
     apply(clarsimp)
     apply (metis setA_liftB_empty)
    apply(simp add: F_SDPDA_TO_CFG_STD_def F_SDPDA_TO_CFG_STD__edges_l2_def)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_marking_configurations_def epdaH_configurations_def)
    apply(subgoal_tac "(THE v. \<exists>w. liftB wb @ [teA (cons_l2 state stack)] = liftB w @ liftA v) = [cons_l2 state stack]")
     apply(clarsimp)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(thin_tac "X" for X)
    apply(clarsimp)
    apply(rule split1)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(rule_tac
      x="n"
      in exI)
   apply(simp add: derivation_append_def)
  apply(simp add: cfg_marking_condition_def)
  apply(rule_tac
      x="Suc(n+m)"
      in exI)
  apply(simp add: derivation_append_def der2_def cfg_marking_configuration_def cfg_configurations_def simpY F_SDPDA_TO_CFG_STD__configuration_basic_RL_def Let_def epdaH_marking_configurations_def epdaH_configurations_def)
  apply(subgoal_tac "(THE w. \<exists>v. liftB wb @ [teA (cons_l2 state stack)] = liftB w @ liftA v) = wb")
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD_def Let_def)
   apply (metis subsetCE)
  apply(rule split2)
  done

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__revert_F_SDPDA_TO_CFG_STD__SOUND_hlp2: "
  valid_simple_dpda G 
  \<Longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (case F_SDPDA_TO_LR1_STD G of None \<Rightarrow> {} | Some G \<Rightarrow> cfg_productions G) = epdaH_required_edges G"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_SDPDA_TO_LR1_STD__SOUND2)
   apply(simp add: F_SDPDA_TO_LR1_OPT__SpecInput2_def)
  apply(case_tac "F_SDPDA_TO_LR1_STD G")
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
   apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
   apply(simp add: epdaH_required_edges_def)
   apply(clarsimp)
   apply(subgoal_tac "epdaH.marked_language G = epdaS.marked_language G")
    prefer 2
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
    apply (metis epdaS_to_epdaH_mlang)
   apply(simp add: epdaH_marking_condition_def)
   apply(subgoal_tac "epdaH_conf_history ca \<in> epdaH.marked_language G")
    apply(force)
   apply(simp add: epdaH.marked_language_def epdaH_marking_configurations_def)
   apply(erule_tac x="epdaH_conf_history ca" in allE)
   apply(erule_tac x="derivation_take d k" in allE)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(force)
   apply(erule impE)
    apply(rule epdaH.derivation_take_preserves_derivation)
    apply(simp add: epdaH.derivation_initial_def)
   apply(erule impE)
    apply(simp add: epdaH_marked_effect_def)
    apply(rule_tac x="k" in exI)
    apply(simp add: derivation_take_def)
    apply(simp add: epdaH_marking_configurations_def)
   apply(erule impE)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marking_condition_def)
   apply(erule_tac x="k" in allE)
   apply(simp add: derivation_take_def)
   apply(erule impE)
    apply(simp add: epdaH_marking_configurations_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_LR1_OPT__SpecOutput2_def)
  apply(rename_tac GX)
  apply(simp add: F_SDPDA_TO_LR1_STD_def)
  apply(clarsimp)
  apply(rule antisym)
   apply(rule F_SDPDA_TO_LR1_STD__computes__epdaH_required_edges__part1)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_SDPDA_TO_LR1_STD__computes__epdaH_required_edges__part2)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__revert_F_SDPDA_TO_CFG_STD__SOUND_hlp1: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput G 
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput G G' 
  \<Longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G' (case F_SDPDA_TO_LR1_STD G' of None \<Rightarrow> {} | Some G \<Rightarrow> cfg_productions G) = epdaH_required_edges G'"
  apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput_def)
  apply(clarsimp)
  apply(rule F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__revert_F_SDPDA_TO_CFG_STD__SOUND_hlp2)
  apply(force)
  done

lemma F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__revert_F_SDPDA_TO_CFG_STD__SOUND: "
  F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput G 
  \<Longrightarrow> F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput G G' 
  \<Longrightarrow> k > 0 
  \<Longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G' (case F_SDPDA_TO_LR1_OPT G' k of None \<Rightarrow> {} | Some G \<Rightarrow> cfg_productions G) = epdaH_required_edges G'"
  apply(rule_tac t="F_SDPDA_TO_LR1_OPT G' k" and s="F_SDPDA_TO_LR1_STD G'" in subst)
   apply(rule F_SDPDA_TO_LR1_OPT__vs__F_SDPDA_TO_LR1_STD__stronger)
    apply(simp add: F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecOutput_def)
   apply(force)
  apply(thin_tac "k > 0")
  apply(rule F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__revert_F_SDPDA_TO_CFG_STD__SOUND_hlp1)
   apply(force)
  apply(force)
  done

theorem F_DPDA_DRE__SOUND: "
  F_DPDA_DRE__SpecInput G 
  \<Longrightarrow> k > 0 
  \<Longrightarrow> F_DPDA_DRE__SpecOutput G (F_DPDA_DRE G k)"
  apply(simp add: F_DPDA_DRE_def Let_def)
  apply(rule_tac
      t="(F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD
               (F_DPDA_RMPUE
                 (F_DPDA_SPPE
                   (F_DPDA_RNE (F_DPDA_SEE G)
                     (F_FRESH (epda_gamma (F_DPDA_SEE G))))))
               (case F_SDPDA_TO_LR1_OPT
                      (F_DPDA_RMPUE
                        (F_DPDA_SPPE
                          (F_DPDA_RNE (F_DPDA_SEE G)
                            (F_FRESH (epda_gamma (F_DPDA_SEE G))))))
                      k of
                None \<Rightarrow> {} | Some x \<Rightarrow> cfg_productions x))"
      and s="epdaH_required_edges (F_DPDA_RMPUE
                 (F_DPDA_SPPE
                   (F_DPDA_RNE (F_DPDA_SEE G)
                     (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
      in ssubst)
   apply(rule_tac G="G" in F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__revert_F_SDPDA_TO_CFG_STD__SOUND)
     apply (metis F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def  F_DPDA_DRE__SpecInput_def)
    apply (metis F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SOUND F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RMPUE__SpecInput_def F_DPDA_DRE__SpecInput_def)
   apply(force)
  apply(rule_tac
      t="(F_DPDA_DRE__revert_F_DPDA_RMPUE
             (F_DPDA_SPPE
               (F_DPDA_RNE (F_DPDA_SEE G)
                 (F_FRESH (epda_gamma (F_DPDA_SEE G)))))
             (epdaH_required_edges
               (F_DPDA_RMPUE
                 (F_DPDA_SPPE
                   (F_DPDA_RNE (F_DPDA_SEE G)
                     (F_FRESH (epda_gamma (F_DPDA_SEE G))))))))"
      and s="epdaH_required_edges (
                 (F_DPDA_SPPE
                   (F_DPDA_RNE (F_DPDA_SEE G)
                     (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
      in ssubst)
   apply(rule_tac G="G" in F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__revert_F_DPDA_RMPE__SOUND)
    apply (metis F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput_def F_DPDA_DRE__SpecInput_def)
   apply (metis F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SOUND F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_SPPE__SpecInput_def F_DPDA_DRE__SpecInput_def)
  apply(rule_tac
      t="F_DPDA_DRE__revert_F_DPDA_SPPE
           (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))
           (epdaH_required_edges
             (F_DPDA_SPPE
               (F_DPDA_RNE (F_DPDA_SEE G)
                 (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
      and s="epdaH_required_edges (
                 (
                   (F_DPDA_RNE (F_DPDA_SEE G)
                     (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
      in ssubst)
   apply(rule_tac G="G" in F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__revert_F_DPDA_SPPE__SOUND)
    apply (metis F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput_def F_DPDA_DRE__SpecInput_def)
   apply (metis F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SOUND F_DPDA_DRE__F_DPDA_SEE__TO__F_DPDA_RNE__SpecInput_def F_DPDA_DRE__SpecInput_def)
  apply(rule_tac
      t="F_DPDA_DRE__revert_F_DPDA_RNE (F_DPDA_SEE G)
         (F_FRESH (epda_gamma (F_DPDA_SEE G)))
         (epdaH_required_edges
           (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G)))))"
      in ssubst)
   apply(rule_tac G="G" in F_DPDA_DRE__F_DPDA_SEE__revert_F_DPDA_RNE__SOUND)
    apply(simp add: F_DPDA_SEE__SpecInput_def F_DPDA_DRE__SpecInput_def)
   apply(rule F_DPDA_SEE__SOUND)
   apply(simp add: F_DPDA_SEE__SpecInput_def F_DPDA_DRE__SpecInput_def)
  apply(rule_tac
      t="F_DPDA_DRE__revert_F_DPDA_SEE G (epdaH_required_edges (F_DPDA_SEE G))"
      and s="epdaH_required_edges G"
      in ssubst)
   apply(rule_tac
      t="epdaH_required_edges G"
      and s="epdaS_required_edges G"
      in ssubst)
    apply(rule sym)
    apply(rule epdaS_required_edges__vs__epdaH_required_edges)
    apply(simp add: F_DPDA_DRE__SpecInput_def valid_dpda_def valid_pda_def)
   apply(rule_tac
      t="epdaH_required_edges (F_DPDA_SEE G)"
      and s="epdaS_required_edges (F_DPDA_SEE G)"
      in ssubst)
    apply(rule sym)
    apply(rule epdaS_required_edges__vs__epdaH_required_edges)
    apply(simp add: F_DPDA_DRE__SpecInput_def)
    apply(rule F_DPDA_SEE__preserves_epda)
    apply(force)
   apply(rule F_DPDA_DRE__revert_F_DPDA_SEE_SOUND_scheduled_case_epdaS_required_edges)
   apply(simp add: F_DPDA_DRE__SpecInput_def F_DPDA_SEE__SpecInput_def)
  apply(simp add: F_DPDA_DRE__SpecOutput_def epdaH_accessible_edges_def)
  done

lemma F_DPDA_DRE__are_precisely_reachable: "
  valid_dpda G 
  \<Longrightarrow> k > 0 
  \<Longrightarrow> F_DPDA_DRE G k = epdaH_required_edges G"
  apply(subgoal_tac "F_DPDA_DRE__SpecInput G \<Longrightarrow> k > 0 \<Longrightarrow> F_DPDA_DRE__SpecOutput G (F_DPDA_DRE G k)")
   prefer 2
   apply(rule F_DPDA_DRE__SOUND)
    apply(force)
   apply(force)
  apply(erule meta_impE)
   apply(simp add: F_DPDA_DRE__SpecInput_def)
  apply(simp add: F_DPDA_DRE__SpecOutput_def)
  done

end
