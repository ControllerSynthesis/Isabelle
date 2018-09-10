section {*FUNCTION\_CONT\_\_Enforce\_Controllability*}
theory
  FUNCTION_CONT__Enforce_Controllability

imports
  PRJ_13_06__ENTRY

begin

definition F_DPDA_EC__SpecInput :: "
  ('stateA, 'event, 'stackA) epda 
  \<Rightarrow> (('stateB, 'event, nat) epda \<times> 'event set) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__SpecInput G X \<equiv>
  case X of 
  (P, \<Sigma>UC) \<Rightarrow> 
     valid_dpda G 
     \<and> valid_dfa P 
     \<and> epdaS.marked_language G \<subseteq> epdaS.marked_language P 
     \<and> epdaS.unmarked_language G \<subseteq> epdaS.unmarked_language P 
     \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G) 
     \<and> \<not> epdaH_livelock G 
     \<and> epdaH.accessible G"

definition F_DPDA_EC__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda \<times> 'event set) 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda option \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__SpecOutput Gi X R \<equiv>
  case X of 
  (G0, P, \<Sigma>UC) \<Rightarrow> 
    (case R of 
    (None, b) \<Rightarrow> 
      des_langM 
        (Enforce_Marked_Controllable_Subset 
          \<Sigma>UC 
          (epdaH.unmarked_language P) 
          (epda_to_des Gi)) 
       = {} 
      \<and> \<not> b 
  | (Some Go, b) \<Rightarrow> 
      valid_dpda Go 
      \<and> Enforce_Marked_Controllable_Subset 
          \<Sigma>UC 
          (epdaH.unmarked_language P) 
          (epda_to_des Gi) 
         = epda_to_des Go 
      \<and> \<not> epdaH_livelock Go 
      \<and> (b \<longrightarrow> Gi = Go) 
      \<and> b = epda_operational_controllable Gi P \<Sigma>UC 
      \<and> (b \<longleftrightarrow> epda_to_des Gi = epda_to_des Go))"

definition F_DPDA_EC__F_DPDA_OTS__SpecInput :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_OTS__SpecInput G X \<equiv>
  case X of 
  (S, D) \<Rightarrow> 
      valid_dpda G 
      \<and> valid_dfa D 
      \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G) 
      \<and> epdaH_reflection_to_DFA_exists G D sel_tuple2_2 
      \<and> \<not> epdaH_livelock G 
      \<and> epda_to_des G = epda_to_des S"

definition F_DPDA_EC__F_DPDA_OTS__SpecOutput :: "
  ('stateC, 'event, 'stackC) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda \<times> 'event set) 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda option \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_OTS__SpecOutput Gi X R \<equiv>
  case X of 
  (G0, P, \<Sigma>UC) \<Rightarrow> 
    (case R of 
    (None, b) \<Rightarrow> 
        des_langM 
          (Enforce_Marked_Controllable_Subset 
            \<Sigma>UC 
            (epdaH.unmarked_language P) 
            (epda_to_des Gi)) 
         = {} 
        \<and> b = False 
  | (Some Go, b) \<Rightarrow> 
      valid_dpda Go 
      \<and> Enforce_Marked_Controllable_Subset 
          \<Sigma>UC 
          (epdaH.unmarked_language P)
          (epda_to_des Gi) 
         = (epda_to_des Go) 
      \<and> \<not> epdaH_livelock Go 
      \<and> (b \<longrightarrow> G0 = Go) 
      \<and> b = epda_operational_controllable Gi P \<Sigma>UC
      \<and> (b \<longleftrightarrow> epda_to_des Gi = epda_to_des Go))"

definition F_DPDA_EC__F_DPDA_EUML__SpecInput :: "
  ((('stateA, 'stateB) DT_tuple2, 'stackA) DT_state_and_stack_or_state, 'event, 'stackA) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_EUML__SpecInput G X \<equiv>
  case X of 
  (S, D) \<Rightarrow> 
      valid_dpda G 
      \<and> valid_dfa D 
      \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G) 
      \<and> state_stack_unique_for_marking_states G 
      \<and> state_stack_unique_for_stable_states G 
      \<and> always_applicable_for_stable_states G 
      \<and> some_edge_applicable G 
      \<and> \<not> epdaH_livelock G 
      \<and> epdaH_reflection_to_DFA_exists G D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state) 
      \<and> corresponds_to_top_stack G F_DPDA_OTS__is_auxiliary F_DPDA_OTS__get_stack 
      \<and> main_states_have_only_empty_steps G F_DPDA_OTS__is_main 
      \<and> main_states_have_all_empty_steps G F_DPDA_OTS__is_main 
      \<and> executing_edge_from_auxiliary_to_main_state G F_DPDA_OTS__is_auxiliary F_DPDA_OTS__is_main 
      \<and> always_applicable_for_auxiliary_states G F_DPDA_OTS__is_auxiliary 
      \<and> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_OTS__is_main 
      \<and> epda_to_des G = epda_to_des S"

definition F_DPDA_EC__F_DPDA_EUML__SpecOutput :: "
  ('stateC, 'event, 'stackC) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda \<times> 'event set) 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda option \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_EUML__SpecOutput \<equiv>
  F_DPDA_EC__F_DPDA_OTS__SpecOutput"

definition F_DPDA_EC__F_DPDA_EA_OPT__SpecInput :: "
  (((('stateA, 'stateB) DT_tuple2, 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_EA_OPT__SpecInput G X \<equiv>
  case X of 
  (S, D) \<Rightarrow> 
      valid_dpda G 
      \<and> valid_dfa D 
      \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G) 
      \<and> state_stack_unique_for_marking_states G 
      \<and> only_executing_edges_from_marking_states G 
      \<and> \<not> epdaH_livelock G 
      \<and> epdaH_reflection_to_DFA_exists G D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state) 
      \<and> corresponds_to_top_stack G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
      \<and> main_states_have_only_empty_steps G F_DPDA_EUML__is_main 
      \<and> main_states_have_all_empty_steps G F_DPDA_EUML__is_main 
      \<and> executing_edge_from_auxiliary_to_main_state G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
      \<and> always_applicable_for_auxiliary_states G F_DPDA_EUML__is_auxiliary 
      \<and> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_EUML__is_main 
      \<and> epda_to_des G = epda_to_des S"

definition F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput :: "
  ('stateC, 'event, 'stackC) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda \<times> 'event set) 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda option \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput \<equiv>
  F_DPDA_EC__F_DPDA_OTS__SpecOutput"

definition F_DPDA_EC__F_DPDA_RCS__SpecInput :: "
  (((('stateA, 'stateB) DT_tuple2, 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_RCS__SpecInput G X \<equiv>
  case X of 
  (S, D) \<Rightarrow> 
      valid_dpda G 
      \<and> valid_dfa D 
      \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G) 
      \<and> state_stack_unique_for_marking_states G 
      \<and> only_executing_edges_from_marking_states G 
      \<and> \<not> epdaH_livelock G 
      \<and> epdaH_reflection_to_DFA_exists G D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state) 
      \<and> corresponds_to_top_stack G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
      \<and> epdaH.accessible G 
      \<and> main_states_can_be_left_with_empty_step G F_DPDA_EUML__is_main 
      \<and> main_states_have_only_empty_steps G F_DPDA_EUML__is_main 
      \<and> executing_edge_from_auxiliary_to_main_state G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
      \<and> always_applicable_for_auxiliary_states G F_DPDA_EUML__is_auxiliary 
      \<and> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_EUML__is_main 
      \<and> epda_to_des G = epda_to_des S"

definition F_DPDA_EC__F_DPDA_RCS__SpecOutput :: "
  ('stateC, 'event, 'stackC) epda 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda \<times> ('stateB, 'event, nat) epda \<times> 'event set) 
  \<Rightarrow> (('stateA, 'event, 'stackA) epda option \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_EC__F_DPDA_RCS__SpecOutput \<equiv>
  F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput"

theorem F_DPDA_EC__SOUND: "
  F_DPDA_EC__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> R = F_DPDA_EC S P \<Sigma>UC 
  \<Longrightarrow> F_DPDA_EC__SpecOutput S (S, P, \<Sigma>UC) R"
  apply(simp add: F_DPDA_EC_def)
  apply(clarsimp)
  apply(rule_tac
      SPo_F="F_DPDA_EC__SpecOutput"
      and SPi_F="F_DPDA_EC__SpecInput"
      and X="S"
      and Y="(S, P, \<Sigma>UC)"
      and SEL_iF="\<lambda>(S, P, \<Sigma>UC). (P, \<Sigma>UC)"
      and SEL_iH="\<lambda>(S, P, \<Sigma>UC). P"
      and SEL_iFH="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_oF="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SEL_oH="\<lambda>(S, P, \<Sigma>UC). (P, \<Sigma>UC)"
      and SEL_oFH="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SPi_H="FUN_DPDA_DFA_PRODUCT__SpecInput2"
      and SPo_H="FUN_DPDA_DFA_PRODUCT__SpecOutput2"
      and SPi_FH="F_DPDA_EC__F_DPDA_OTS__SpecInput"
      and SPo_FH="F_DPDA_EC__F_DPDA_OTS__SpecOutput"
      and H="F_DPDA_DFA_PRODUCT"
      in decompose_sequential_execution_input_output_specification_args)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput2_def F_DPDA_EC__SpecInput_def)
      apply(clarsimp)
      apply(rule_tac
      t="epdaH.unmarked_language S"
      and s="epdaS.unmarked_language S"
      in ssubst)
       apply (metis valid_dpda_to_valid_pda PDA_to_epda epdaS_to_epdaH_unmarked_language)
      apply(rule_tac
      t="epdaH.marked_language S"
      and s="epdaS.marked_language S"
      in ssubst)
       apply (metis valid_dpda_to_valid_pda PDA_to_epda epdaS_to_epdaH_mlang)
      apply(rule_tac
      t="epdaH.marked_language P"
      and s="epdaS.marked_language P"
      in ssubst)
       apply(simp add: valid_dfa_def)
       apply (metis valid_dpda_to_valid_pda PDA_to_epda epdaS_to_epdaH_mlang)
      apply(rule_tac
      t="epdaH.unmarked_language P"
      and s="epdaS.unmarked_language P"
      in ssubst)
       apply(simp add: valid_dfa_def)
       apply (metis valid_dpda_to_valid_pda PDA_to_epda epdaS_to_epdaH_unmarked_language)
      apply(force)
     apply(rule_tac
      ?Gi="S"
      and P="P"
      in F_DPDA_DFA_PRODUCT__SOUND2)
     apply(force)
    apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput2_def F_DPDA_EC__SpecInput_def F_DPDA_EC__F_DPDA_OTS__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def epda_to_des_def)
    apply(clarsimp)
    apply(rule_tac
      t="epdaH.unmarked_language S"
      and s="epdaS.unmarked_language S"
      in subst)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule_tac
      t="epdaH.marked_language S"
      and s="epdaS.marked_language S"
      in subst)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule_tac
      t="epdaH.marked_language P"
      and s="epdaS.marked_language P"
      in subst)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp add: valid_dfa_def)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule_tac
      t="epdaH.unmarked_language P"
      and s="epdaS.unmarked_language P"
      in subst)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply(simp add: valid_dfa_def)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(force)
   apply(rename_tac Pa)(*strict*)
   apply(simp add: F_DPDA_EC__F_DPDA_OTS__SpecOutput_def F_DPDA_EC__SpecOutput_def)
   apply(clarsimp)
   apply(rename_tac Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.unmarked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.unmarked_language S")
    apply(rename_tac Pa x y)(*strict*)
    prefer 2
    apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput2_def F_DPDA_EC__SpecInput_def)
    apply(clarsimp)
    apply(rule_tac
      t="epdaH.unmarked_language S"
      and s="epdaS.unmarked_language S"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language S"
      and s="epdaS.marked_language S"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language P"
      and s="epdaS.marked_language P"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp add: valid_dfa_def)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language P"
      and s="epdaS.unmarked_language P"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply(simp add: valid_dfa_def)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(force)
   apply(rename_tac Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language S")
    apply(rename_tac Pa x y)(*strict*)
    prefer 2
    apply(thin_tac "epdaH.unmarked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.unmarked_language S")
    apply(unfold FUN_DPDA_DFA_PRODUCT__SpecOutput2_def F_DPDA_EC__SpecInput_def)[1]
    apply(clarsimp)
    apply(rule_tac
      t="epdaH.unmarked_language S"
      and s="epdaS.unmarked_language S"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language S"
      and s="epdaS.marked_language S"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language P"
      and s="epdaS.marked_language P"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp add: valid_dfa_def)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language P"
      and s="epdaS.unmarked_language P"
      in subst)
     apply(rename_tac Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply(simp add: valid_dfa_def)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac Pa x y)(*strict*)
    apply(force)
   apply(rename_tac Pa x y)(*strict*)
   apply(subgoal_tac "epda_to_des (F_DPDA_DFA_PRODUCT S P) = epda_to_des S")
    apply(rename_tac Pa x y)(*strict*)
    prefer 2
    apply(simp add: epda_to_des_def)
   apply(rename_tac Pa x y)(*strict*)
   apply(case_tac x)
    apply(rename_tac Pa x y)(*strict*)
    apply(clarsimp)
   apply(rename_tac Pa x y a)(*strict*)
   apply(clarsimp)
   apply(rename_tac Pa a)(*strict*)
   apply(rule_tac
      t="epda_operational_controllable S P \<Sigma>UC"
      and s="epda_operational_controllable (F_DPDA_DFA_PRODUCT S P) P \<Sigma>UC"
      in ssubst)
    apply(rename_tac Pa a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac Pa a)(*strict*)
   apply(rule epda_Cont_eq_to_epda_operational_controllable_eq2)
      apply(rename_tac Pa a)(*strict*)
      apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
     apply(rename_tac Pa a)(*strict*)
     apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
    apply(rename_tac Pa a)(*strict*)
    apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
   apply(rename_tac Pa a)(*strict*)
   apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
  apply(rename_tac X)(*strict*)
  apply(rename_tac S')
  apply(rename_tac S')(*strict*)
  apply(rule_tac
      SPo_F="F_DPDA_EC__F_DPDA_OTS__SpecOutput"
      and SPi_F="F_DPDA_EC__F_DPDA_OTS__SpecInput"
      and H="F_DPDA_OTS"
      and X="S'"
      and Y="(S, P, \<Sigma>UC)"
      and SEL_iF="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_iH="\<lambda>(S, P, \<Sigma>UC). P"
      and SEL_iFH="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_oF="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SEL_oH="\<lambda>(S, P, \<Sigma>UC). (P, \<Sigma>UC)"
      and SEL_oFH="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SPi_H="F_DPDA_OTS__SpecInput"
      and SPo_H="F_DPDA_OTS__SpecOutput"
      and SPi_FH="F_DPDA_EC__F_DPDA_EUML__SpecInput"
      and SPo_FH="F_DPDA_EC__F_DPDA_EUML__SpecOutput"
      in decompose_sequential_execution_input_output_specification_args2_noHargs)
             apply(rename_tac S')(*strict*)
             apply(force)
            apply(rename_tac S')(*strict*)
            apply(force)
           apply(rename_tac S')(*strict*)
           apply(force)
          apply(rename_tac S')(*strict*)
          apply(force)
         apply(rename_tac S')(*strict*)
         apply(force)
        apply(rename_tac S')(*strict*)
        apply(force)
       apply(rename_tac S')(*strict*)
       apply(force)
      apply(rename_tac S')(*strict*)
      apply(simp add: F_DPDA_EC__F_DPDA_OTS__SpecInput_def F_DPDA_OTS__SpecInput_def)
     apply(rename_tac S')(*strict*)
     apply(rule F_DPDA_OTS__SOUND)
     apply(force)
    apply(rename_tac S')(*strict*)
    apply(simp add: F_DPDA_EC__F_DPDA_EUML__SpecInput_def F_DPDA_OTS__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecInput_def epda_to_des_def)
   apply(rename_tac S' Pa)(*strict*)
   apply(simp add: F_DPDA_EC__F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_EUML__SpecInput_def F_DPDA_OTS__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecInput_def F_DPDA_EC__F_DPDA_OTS__SpecOutput_def)
   apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.unmarked_language (F_DPDA_OTS S') = epdaH.unmarked_language S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.marked_language (F_DPDA_OTS S') = epdaH.marked_language S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epda_to_des (F_DPDA_OTS S') = epda_to_des S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(simp add: epda_to_des_def)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(case_tac x)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(clarify)
    apply(simp (no_asm))
    apply(rename_tac S' Pa y)(*strict*)
    apply(simp (no_asm_use))
    apply(rule conjI)
     apply(rename_tac S' Pa y)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac S' Pa y)(*strict*)
    apply(rule_tac
      t="epda_to_des S'"
      and s="epda_to_des (F_DPDA_OTS S')"
      in ssubst)
     apply(rename_tac S' Pa y)(*strict*)
     apply(force)
    apply(rename_tac S' Pa y)(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language S'"
      and s="epdaH.unmarked_language (F_DPDA_OTS S')"
      in ssubst)
     apply(rename_tac S' Pa y)(*strict*)
     apply(force)
    apply(rename_tac S' Pa y)(*strict*)
    apply(force)
   apply(rename_tac S' Pa x y a)(*strict*)
   apply(clarify)
   apply(simp (no_asm))
   apply(rename_tac S' Pa y a)(*strict*)
   apply(simp (no_asm_use))
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule_tac
      t="epda_operational_controllable S' P \<Sigma>UC"
      and s="epda_operational_controllable (F_DPDA_OTS S') P \<Sigma>UC"
      in ssubst)
    apply(rename_tac S' Pa y a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule epda_Cont_eq_to_epda_operational_controllable_eq2)
      apply(rename_tac S' Pa y a)(*strict*)
      apply(force)
     apply(rename_tac S' Pa y a)(*strict*)
     apply(force)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(force)
  apply(rename_tac S' X)(*strict*)
  apply(thin_tac "F_DPDA_EC__F_DPDA_OTS__SpecInput S' (S, P)")
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(rename_tac S')
  apply(rename_tac S')(*strict*)
  apply(rule_tac
      SPo_F="F_DPDA_EC__F_DPDA_EUML__SpecOutput"
      and SPi_F="F_DPDA_EC__F_DPDA_EUML__SpecInput"
      and H="F_DPDA_EUML"
      and X="S'"
      and Y="(S, P, \<Sigma>UC)"
      and SEL_iF="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_iH="\<lambda>(S, P, \<Sigma>UC). P"
      and SEL_iFH="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_oF="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SEL_oH="\<lambda>(S, P, \<Sigma>UC). (P, \<Sigma>UC)"
      and SEL_oFH="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SPi_H="F_DPDA_EUML__SpecInput"
      and SPo_H="F_DPDA_EUML__SpecOutput"
      and SPi_FH="F_DPDA_EC__F_DPDA_EA_OPT__SpecInput"
      and SPo_FH="F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput"
      in decompose_sequential_execution_input_output_specification_args2_noHargs)
             apply(rename_tac S')(*strict*)
             apply(force)
            apply(rename_tac S')(*strict*)
            apply(force)
           apply(rename_tac S')(*strict*)
           apply(force)
          apply(rename_tac S')(*strict*)
          apply(force)
         apply(rename_tac S')(*strict*)
         apply(force)
        apply(rename_tac S')(*strict*)
        apply(force)
       apply(rename_tac S')(*strict*)
       apply(force)
      apply(rename_tac S')(*strict*)
      apply(simp add: F_DPDA_EUML__SpecInput_def F_DPDA_EC__F_DPDA_EUML__SpecInput_def)
     apply(rename_tac S')(*strict*)
     apply(rule F_DPDA_EUML__SOUND)
     apply(force)
    apply(rename_tac S')(*strict*)
    apply(simp add: F_DPDA_EC__F_DPDA_EA_OPT__SpecInput_def F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_EUML__SpecInput_def epda_to_des_def)
   apply(rename_tac S' Pa)(*strict*)
   apply(simp add: F_DPDA_EC__F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EC__F_DPDA_EUML__SpecInput_def F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecOutput_def)
   apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.unmarked_language (F_DPDA_EUML S') = epdaH.unmarked_language S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.marked_language (F_DPDA_EUML S') = epdaH.marked_language S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epda_to_des (F_DPDA_EUML S') = epda_to_des S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(simp add: epda_to_des_def)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(case_tac x)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(clarify)
    apply(simp (no_asm))
    apply(rename_tac S' Pa y)(*strict*)
    apply(simp (no_asm_use))
    apply(rule conjI)
     apply(rename_tac S' Pa y)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac S' Pa y)(*strict*)
    apply(rule_tac
      t="epda_to_des S'"
      and s="epda_to_des (F_DPDA_EUML S')"
      in ssubst)
     apply(rename_tac S' Pa y)(*strict*)
     apply(force)
    apply(rename_tac S' Pa y)(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language S'"
      and s="epdaH.unmarked_language (F_DPDA_EUML S')"
      in ssubst)
     apply(rename_tac S' Pa y)(*strict*)
     apply(force)
    apply(rename_tac S' Pa y)(*strict*)
    apply(force)
   apply(rename_tac S' Pa x y a)(*strict*)
   apply(clarify)
   apply(simp (no_asm))
   apply(rename_tac S' Pa y a)(*strict*)
   apply(simp (no_asm_use))
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S' Pa y a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule_tac
      t="epda_operational_controllable S' P \<Sigma>UC"
      and s="epda_operational_controllable (F_DPDA_EUML S') P \<Sigma>UC"
      in ssubst)
    apply(rename_tac S' Pa y a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(rule epda_Cont_eq_to_epda_operational_controllable_eq2)
      apply(rename_tac S' Pa y a)(*strict*)
      apply(force)
     apply(rename_tac S' Pa y a)(*strict*)
     apply(force)
    apply(rename_tac S' Pa y a)(*strict*)
    apply(force)
   apply(rename_tac S' Pa y a)(*strict*)
   apply(force)
  apply(rename_tac S' X)(*strict*)
  apply(thin_tac "F_DPDA_EC__F_DPDA_EUML__SpecInput S' (S, P)")
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(rename_tac S')
  apply(rename_tac S')(*strict*)
  apply(rule_tac
      SPo_F="F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput"
      and SPi_F="F_DPDA_EC__F_DPDA_EA_OPT__SpecInput"
      and H="F_DPDA_EA_OPT"
      and X="S'"
      and Y="(S, P, \<Sigma>UC)"
      and SEL_iF="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_iH="\<lambda>(S, P, \<Sigma>UC). P"
      and SEL_iFH="\<lambda>(S, P, \<Sigma>UC). (S, P)"
      and SEL_oF="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SEL_oH="\<lambda>(S, P, \<Sigma>UC). (P, \<Sigma>UC)"
      and SEL_oFH="\<lambda>(S, P, \<Sigma>UC). (S, P, \<Sigma>UC)"
      and SPi_H="F_DPDA_EA_OPT__SpecInput2"
      and SPo_H="F_DPDA_EA_OPT__SpecOutput2"
      and SPi_FH="F_DPDA_EC__F_DPDA_RCS__SpecInput"
      and SPo_FH="F_DPDA_EC__F_DPDA_RCS__SpecOutput"
      in decompose_sequential_execution_input_output_specification_args2_noHargs)
             apply(rename_tac S')(*strict*)
             apply(force)
            apply(rename_tac S')(*strict*)
            apply(force)
           apply(rename_tac S')(*strict*)
           apply(force)
          apply(rename_tac S')(*strict*)
          apply(force)
         apply(rename_tac S')(*strict*)
         apply(force)
        apply(rename_tac S')(*strict*)
        apply(force)
       apply(rename_tac S')(*strict*)
       apply(force)
      apply(rename_tac S')(*strict*)
      apply(simp add: F_DPDA_EA_OPT__SpecInput2_def F_DPDA_EC__F_DPDA_EA_OPT__SpecInput_def)
      apply(clarsimp)
      apply(rule_tac
      s="epdaH.unmarked_language S'"
      and t="epdaS.unmarked_language S'"
      in ssubst)
       apply(rename_tac S')(*strict*)
       apply(rule epdaS_to_epdaH_unmarked_language)
       apply (metis valid_dpda_to_valid_pda PDA_to_epda)
      apply(rename_tac S')(*strict*)
      apply(rule_tac
      s="epdaH.marked_language S'"
      and t="epdaS.marked_language S'"
      in ssubst)
       apply(rename_tac S')(*strict*)
       apply(rule epdaS_to_epdaH_mlang)     
       apply (metis valid_dpda_to_valid_pda PDA_to_epda)
      apply(rename_tac S')(*strict*)
      apply(force)
     apply(rename_tac S')(*strict*)
     apply(rule F_DPDA_EA_OPT__SOUND2)
     apply(force)
    apply(rename_tac S')(*strict*)
    apply(simp add: F_DPDA_EC__F_DPDA_RCS__SpecInput_def F_DPDA_EA_OPT__SpecOutput2_def F_DPDA_EC__F_DPDA_EA_OPT__SpecInput_def epda_to_des_def F_DPDA_EC__SpecInput_def)
    apply(clarsimp)
    apply(rule_tac
      t="epdaH.unmarked_language S"
      and s="epdaH.unmarked_language S'"
      in ssubst)
     apply(rename_tac S')(*strict*)
     apply(force)
    apply(rename_tac S')(*strict*)
    apply(rule_tac
      t="epdaH.marked_language S"
      and s="epdaH.marked_language S'"
      in ssubst)
     apply(rename_tac S')(*strict*)
     apply(force)
    apply(rename_tac S')(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language S'"
      and s="epdaS.unmarked_language S'"
      in subst)
     apply(rename_tac S')(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S')(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language (F_DPDA_EA_OPT S')"
      and s="epdaS.unmarked_language (F_DPDA_EA_OPT S')"
      in subst)
     apply(rename_tac S')(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S')(*strict*)
    apply(rule_tac
      t="epdaH.marked_language S'"
      and s="epdaS.marked_language S'"
      in subst)
     apply(rename_tac S')(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S')(*strict*)
    apply(rule_tac
      t="epdaH.marked_language (F_DPDA_EA_OPT S')"
      and s="epdaS.marked_language (F_DPDA_EA_OPT S')"
      in subst)
     apply(rename_tac S')(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S')(*strict*)
    apply(force)
   apply(rename_tac S' Pa)(*strict*)
   apply(simp add: F_DPDA_EC__F_DPDA_RCS__SpecOutput_def F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EC__F_DPDA_EA_OPT__SpecInput_def F_DPDA_EA_OPT__SpecOutput2_def F_DPDA_EC__SpecInput_def F_DPDA_EC__F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecOutput_def)
   apply(clarsimp)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.unmarked_language (F_DPDA_EA_OPT S') = epdaH.unmarked_language S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(rule_tac
      t="epdaH.unmarked_language S'"
      and s="epdaS.unmarked_language S'"
      in subst)
     apply(rename_tac S' Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language (F_DPDA_EA_OPT S')"
      and s="epdaS.unmarked_language (F_DPDA_EA_OPT S')"
      in subst)
     apply(rename_tac S' Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(force)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epdaH.marked_language (F_DPDA_EA_OPT S') = epdaH.marked_language S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(rule_tac
      t="epdaH.marked_language S'"
      and s="epdaS.marked_language S'"
      in subst)
     apply(rename_tac S' Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language (F_DPDA_EA_OPT S')"
      and s="epdaS.marked_language (F_DPDA_EA_OPT S')"
      in subst)
     apply(rename_tac S' Pa x y)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(force)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(subgoal_tac "epda_to_des (F_DPDA_EA_OPT S') = epda_to_des S'")
    apply(rename_tac S' Pa x y)(*strict*)
    prefer 2
    apply(simp add: epda_to_des_def)
   apply(rename_tac S' Pa x y)(*strict*)
   apply(case_tac x)
    apply(rename_tac S' Pa x y)(*strict*)
    apply(clarsimp)
   apply(rename_tac S' Pa x y a)(*strict*)
   apply(clarsimp)
   apply(rename_tac S' Pa a)(*strict*)
   apply(rule_tac
      t="epda_operational_controllable S' P \<Sigma>UC"
      and s="epda_operational_controllable (F_DPDA_EA_OPT S') P \<Sigma>UC"
      in ssubst)
    apply(rename_tac S' Pa a)(*strict*)
    apply(rule epda_Cont_eq_to_epda_operational_controllable_eq2)
       apply(rename_tac S' Pa a)(*strict*)
       apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
      apply(rename_tac S' Pa a)(*strict*)
      apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
     apply(rename_tac S' Pa a)(*strict*)
     apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
    apply(rename_tac S' Pa a)(*strict*)
    apply(simp add: F_DPDA_EC__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
   apply(rename_tac S' Pa a)(*strict*)
   apply(force)
  apply(rename_tac S' X)(*strict*)
  apply(thin_tac "F_DPDA_EC__F_DPDA_EA_OPT__SpecInput S' (S, P)")
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(rename_tac S')
  apply(rename_tac S')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac S')(*strict*)
   prefer 2
   apply(rule_tac
      S="S'"
      and P="P"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_RCS__SOUND)
   apply(simp add: F_DPDA_EC__F_DPDA_RCS__SpecInput_def F_DPDA_RCS__SpecInput_def)
  apply(rename_tac S')(*strict*)
  apply(case_tac "F_DPDA_RCS S' P \<Sigma>UC")
  apply(rename_tac S' a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac S' a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac S' b)(*strict*)
   apply(simp add: F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EC__F_DPDA_RCS__SpecOutput_def F_DPDA_RCS__SpecOutput_def F_DPDA_EC__F_DPDA_RCS__SpecInput_def F_DPDA_EC__SpecInput_def F_DPDA_EC__F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecOutput_def)
  apply(rename_tac S' a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac S' b aa)(*strict*)
  apply(thin_tac "F_DPDA_RCS S' P \<Sigma>UC = (Some aa, b)")
  apply(rename_tac S' b aa)(*strict*)
  apply(simp add: F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EC__F_DPDA_RCS__SpecOutput_def)
  apply(case_tac b)
   apply(rename_tac S' b aa)(*strict*)
   apply(clarsimp)
   apply(simp only: F_DPDA_EC__SpecInput_def F_DPDA_EC__F_DPDA_RCS__SpecInput_def F_DPDA_EC__F_DPDA_RCS__SpecOutput_def F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput_def F_DPDA_RCS__SpecOutput_def F_DPDA_EC__F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecOutput_def)
   apply(clarsimp)
  apply(rename_tac S' b aa)(*strict*)
  apply(clarsimp)
  apply(simp only: F_DPDA_EC__SpecInput_def F_DPDA_EC__F_DPDA_RCS__SpecInput_def F_DPDA_EC__F_DPDA_RCS__SpecOutput_def F_DPDA_EC__F_DPDA_EA_OPT__SpecOutput_def F_DPDA_RCS__SpecOutput_def F_DPDA_EC__F_DPDA_EUML__SpecOutput_def F_DPDA_EC__F_DPDA_OTS__SpecOutput_def)
  apply(clarsimp)
  apply(rename_tac S'')
  apply(rename_tac S' b S'')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac S' b S'')(*strict*)
   apply(rule F_EPDA_TC__preserves_DPDA)
   apply(force)
  apply(rename_tac S' b S'')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac S' b S'')(*strict*)
   apply(simp add: epda_to_des_def)
   apply(rule conjI)
    apply(rename_tac S' b S'')(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language S''"
      and s="epdaS.unmarked_language S''"
      in subst)
     apply(rename_tac S' b S'')(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S' b S'')(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language (F_EPDA_TC S'')"
      and s="epdaS.unmarked_language (F_EPDA_TC S'')"
      in subst)
     apply(rename_tac S' b S'')(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rename_tac S' b S'')(*strict*)
    apply(rule F_EPDA_TC__preserves_unmarked_language)
    apply (metis valid_dpda_to_valid_pda)
   apply(rename_tac S' b S'')(*strict*)
   apply(rule_tac
      t="epdaH.marked_language S''"
      and s="epdaS.marked_language S''"
      in subst)
    apply(rename_tac S' b S'')(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac S' b S'')(*strict*)
   apply(rule_tac
      t="epdaH.marked_language (F_EPDA_TC S'')"
      and s="epdaS.marked_language (F_EPDA_TC S'')"
      in subst)
    apply(rename_tac S' b S'')(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac S' b S'')(*strict*)
   apply(rule F_EPDA_TC__preserves_lang)
   apply (metis valid_dpda_to_valid_pda)
  apply(rename_tac S' b S'')(*strict*)
  apply(rule conjI)
   apply(rename_tac S' b S'')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac S' b S'')(*strict*)
  apply(rule F_EPDA_TC__preserves_no_livelock)
   apply(rename_tac S' b S'')(*strict*)
   apply (metis valid_dpda_to_valid_pda)
  apply(rename_tac S' b S'')(*strict*)
  apply(force)
  done

end
