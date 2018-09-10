section {*FUNCTION\_\_DPDA\_RCS\_\_DPDA\_RESTRICT\_TO\_CONTROLLABLE\_STATES*}
theory FUNCTION__DPDA_RCS__DPDA_RESTRICT_TO_CONTROLLABLE_STATES

imports
  PRJ_13_05__ENTRY

begin

definition F_DPDA_RCS__SpecInput :: "
  ((((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> (('stateB, 'event, 'stackB) epda 
      \<times> 'event set) 
  \<Rightarrow> bool"
  where
    "F_DPDA_RCS__SpecInput G X \<equiv>
  case X of 
  (P, \<Sigma>UC) \<Rightarrow> 
    valid_dpda G 
    \<and> valid_dfa P 
    \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
    \<and> state_stack_unique_for_marking_states G 
    \<and> only_executing_edges_from_marking_states G 
    \<and> \<not> epdaH_livelock G 
    \<and> epdaH_reflection_to_DFA_exists G P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state) 
    \<and> corresponds_to_top_stack G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
    \<and> epdaH.accessible G 
    \<and> main_states_can_be_left_with_empty_step G F_DPDA_EUML__is_main 
    \<and> main_states_have_only_empty_steps G F_DPDA_EUML__is_main 
    \<and> executing_edge_from_auxiliary_to_main_state G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
    \<and> always_applicable_for_auxiliary_states G F_DPDA_EUML__is_auxiliary 
    \<and> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_EUML__is_main"

definition F_DPDA_RCS__SpecOutput :: "
  ((((('stateA, 'stateB) DT_tuple2) , 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> (('stateB, 'event, 'stackB) epda 
      \<times> 'event set) 
  \<Rightarrow> ((((((('stateA, 'stateB) DT_tuple2) , 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda) option 
      \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_RCS__SpecOutput Gi X R \<equiv>
  case X of 
  (P, \<Sigma>UC) \<Rightarrow> 
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
          = epda_to_des Go 
      \<and> \<not> epdaH_livelock Go 
      \<and> (b \<longleftrightarrow> epda_operational_controllable Gi P \<Sigma>UC) 
      \<and> (b \<longleftrightarrow> epda_to_des Gi = epda_to_des Go))"

lemma F_DPDA_RCS__SOUND__for_None: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) = None 
  \<Longrightarrow> des_langM (Enforce_Marked_Controllable_Subset \<Sigma>UC (epdaH.unmarked_language P) (epda_to_des S)) = {} \<and> F_DPDA_NCS S P \<Sigma>UC \<noteq> {}"
  apply(simp add: F_EPDA_RS_def)
  apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(erule impE)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(simp add: controllable_subset_def Enforce_Marked_Controllable_Subset_def Let_def des_langM_def)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(rule is_empty)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_NCS_def epda_to_des_def)
  apply(clarsimp)
  apply(rename_tac x f pS X u eP)(*strict*)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x f pS X u eP d)(*strict*)
  apply(thin_tac "epdaH.derivation S d")
  apply(thin_tac "epdaH_marking_condition S d")
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e c)(*strict*)
  apply(simp add: epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac f pS X u eP d i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac f pS X u eP d i e q h s)(*strict*)
  apply(thin_tac "\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr> \<in> epdaH_configurations S")
  apply(rename_tac f pS X u eP d i e q h s)(*strict*)
  apply(simp add: controllable_sublanguage_def)
  apply(erule_tac
      x="[]"
      in ballE)
   apply(rename_tac f pS X u eP d i e q h s)(*strict*)
   prefer 2
   apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac f pS X u eP d i e q h s)(*strict*)
  apply(simp add: controllable_word_def)
  apply(erule_tac
      x="[u]"
      in ballE)
   apply(rename_tac f pS X u eP d i e q h s)(*strict*)
   prefer 2
   apply(simp add: alphabet_to_language_def) 
  apply(rename_tac f pS X u eP d i e q h s)(*strict*)
  apply(erule impE)
   apply(rename_tac f pS X u eP d i e q h s)(*strict*)
   apply(simp add: epdaH.unmarked_language_def)
   apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(clarsimp)
   apply(rename_tac da)
   apply(rename_tac f pS X u eP d i e q h s da)(*strict*)
   apply(simp add: epdaH_reflection_to_DFA_exists_def)
   apply(erule_tac
      x="d"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="0"
      and P="\<lambda>x. \<forall>c. get_configuration (d x) = Some c \<longrightarrow> (\<exists>d'. epdaH.derivation_initial P d' \<and> (\<exists>m. get_configuration (d' m) = Some \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state c))), epdaH_conf_history = epdaH_conf_history c, epdaH_conf_stack = [epda_box P]\<rparr>))"
      in allE)
   apply(rename_tac f pS X u eP d i e q h s da)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(rename_tac fa pS X u eP d i e q h s da)(*strict*)
    apply(clarsimp)
   apply(rename_tac fa pS X u eP d i e q h s da a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac fa pS X u eP d i e q h s da a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac fa pS X u eP d i e q h s da b)(*strict*)
   apply(erule_tac
      x="b"
      in allE)
   apply(erule impE)
    apply(rename_tac fa pS X u eP d i e q h s da b)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac fa pS X u eP d i e q h s da b)(*strict*)
   apply(clarsimp)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m)(*strict*)
   apply(case_tac "d' m")
    apply(rename_tac fa pS X u eP d i e q h s da b d' m)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m a option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m option ba)(*strict*)
   apply(subgoal_tac "ba=\<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state b))), epdaH_conf_history = epdaH_conf_history b, epdaH_conf_stack = [epda_box P]\<rparr>")
    apply(rename_tac fa pS X u eP d i e q h s da b d' m option ba)(*strict*)
    prefer 2
    apply(simp add: get_configuration_def)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m option)(*strict*)
   apply(thin_tac "get_configuration (Some (pair option \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state b))), epdaH_conf_history = epdaH_conf_history b, epdaH_conf_stack = [epda_box P]\<rparr>)) = Some \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state b))), epdaH_conf_history = epdaH_conf_history b, epdaH_conf_stack = [epda_box P]\<rparr>")
   apply(rename_tac fa pS X u eP d i e q h s da b d' m option)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac b)
   apply(rename_tac fa pS X u eP d i e q h s da b d' m option epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac fa pS X u eP d i e q h s da d' m option)(*strict*)
   apply(rename_tac e)
   apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
   apply(subgoal_tac "sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (fa (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X)))) = edge_src eP")
    apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
    prefer 2
    apply(erule disjE)
     apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
     apply(clarsimp)
     apply(rename_tac pS X u eP d i ea q h s da d' m e)(*strict*)
     apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__get_state_def sel_tuple2_2_def)
    apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
    apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__get_state_def sel_tuple2_2_def)
   apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "m=0")
    apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
    apply(clarsimp)
    apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
    apply(simp add: epdaH_initial_configurations_def)
    apply(clarsimp)
    apply(rule_tac
      x="der2 \<lparr>epdaH_conf_state = epda_initial P, epdaH_conf_history = [], epdaH_conf_stack = [epda_box P]\<rparr> eP \<lparr>epdaH_conf_state = edge_trg eP, epdaH_conf_history = [u], epdaH_conf_stack = [epda_box P]\<rparr>"
      in exI)
    apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
    apply(rule context_conjI)
     apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: option_to_list_def)
     apply(simp add: valid_dfa_def)
    apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
    apply(rule conjI)
     apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
     apply(simp add: der2_def)
     apply(simp add: epdaH_initial_configurations_def)
    apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
    apply(rule conjI)
     apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
     apply(simp add: epdaH_unmarked_effect_def der2_def)
     apply(rule_tac
      x="Suc 0"
      in exI)
     apply(force)
    apply(rename_tac fa pS X u eP d i ea q h s da d')(*strict*)
    apply(force)
   apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
    prefer 2
    apply(rule_tac
      d="d'"
      in DFA_one_symbol_per_step)
      apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
      apply(force)
     apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
    apply(force)
   apply(rename_tac fa pS X u eP d i ea q h s da d' m e)(*strict*)
   apply(force)
  apply(rename_tac f pS X u eP d i e q h s)(*strict*)
  apply(thin_tac " h \<in> ATS_Language0.unmarked_language
             epdaH_initial_configurations
             epdaH_step_relation epdaH_unmarked_effect S")
  apply(simp add: epdaH.unmarked_language_def des_langUM_def)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ia ea c)(*strict*)
  apply(case_tac ia)
   apply(rename_tac f pS X u eP d i e q h s da ia ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac f pS X u eP d i e q h s da ea c)(*strict*)
   apply(case_tac c)
   apply(rename_tac f pS X u eP d i e q h s da ea c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(clarsimp)
   apply(rename_tac f pS X u eP d i e q h s da ea epdaH_conf_state epdaH_conf_stack)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac f pS X u eP d i e q h s da ia ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat)(*strict*)
   prefer 2
   apply(rule_tac
      n="0"
      and m="Suc nat"
      and G="S"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac f pS X u eP d i e q h s da ea c nat)(*strict*)
     apply(force)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat)(*strict*)
    apply(force)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat)(*strict*)
   apply(force)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "\<exists>x. edge_pop e2 = [x]")
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 w)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      and A="epda_delta S"
      and P="\<lambda>e2. length (edge_pop e2) = Suc 0"
      in ballE)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 w)(*strict*)
   apply(case_tac e2)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat c1 c2 w edge_eventa edge_popa edge_push)(*strict*)
   apply(case_tac edge_popa)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat c1 c2 w edge_eventa edge_popa edge_push)(*strict*)
    apply(clarsimp)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat c1 c2 w edge_eventa edge_popa edge_push a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2)(*strict*)
  apply(case_tac "edge_event e2")
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_nonstable_states_def)
   apply(erule_tac
      x="e2"
      and P="\<lambda>e2. edge_src e2 = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X) \<longrightarrow> (\<exists>y. edge_event e2 = Some y)"
      in ballE)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and d="da"
      and n="Suc 0"
      and m="nat"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
      apply(force)
     apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
   apply(rule_tac
      M="S"
      and d="da"
      in epdaH.belongs_configurations)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
    apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
   apply(force)
  apply(rename_tac f pS X u eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h s da ea c nat e2 c1 c2 a)(*strict*)
  apply(case_tac c)
  apply(rename_tac f pS X eP d i e q h s da ea c nat e2 c1 c2 a epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h s da ea nat e2 c1 c2 a epdaH_conf_statea epdaH_conf_stacka)(*strict*)
  apply(rename_tac qs s)
  apply(rename_tac f pS X eP d i e q h sa da ea nat e2 c1 c2 a qs s)(*strict*)
  apply(case_tac c1)
  apply(rename_tac f pS X eP d i e q h sa da ea nat e2 c1 c2 a qs s epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat e2 c2 a qs s)(*strict*)
  apply(case_tac c2)
  apply(rename_tac f pS X eP d i e q h sa da ea nat e2 c2 a qs s epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat e2 a qs s)(*strict*)
  apply(case_tac e2)
  apply(rename_tac f pS X eP d i e q h sa da ea nat e2 a qs s edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s edge_push edge_trg)(*strict*)
  apply(rename_tac pu qt)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = Some a, edge_pop = [epda_box S], edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(simp add: corresponds_to_top_stack_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(erule_tac
      x="0"
      and P="\<lambda>n. \<forall>c. get_configuration (d n) = Some c \<longrightarrow>
             F_DPDA_EUML__is_auxiliary (epdaH_conf_state c) \<longrightarrow>
             (\<forall>X. F_DPDA_EUML__get_stack (epdaH_conf_state c) = Some X \<longrightarrow>
                  (\<exists>w. epdaH_conf_stack c = X # w))"
      in allE)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt aa)(*strict*)
  apply(case_tac aa)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt b)(*strict*)
  apply(simp add: epdaH_initial_configurations_def)
  apply(clarsimp)
  apply(case_tac b)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt b epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(simp add: add: get_configuration_def)
  apply(erule impE)
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(erule disjE)
    apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
    apply(clarsimp)
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(simp add: F_DPDA_EUML__get_stack_def F_DPDA_OTS__get_stack_def F_DPDA_EUML__get_state_def)
  apply(erule disjE)
   apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
   apply(clarsimp)
  apply(rename_tac f pS X eP d i e q h sa da ea nat a qs s pu qt)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__enforces__operational_controllable_part1_hlp1: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> epdaH.derivation_initial S d1 
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> epdaH.derivation_initial P d2 
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>) 
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2') 
  \<Longrightarrow> epdaH_conf_history c2' = h @ [u] 
  \<Longrightarrow> u \<in> \<Sigma>UC 
  \<Longrightarrow> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> epdaH.derivation S d 
  \<Longrightarrow> epdaH.belongs S d 
  \<Longrightarrow> d 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> d n = Some (pair e \<lparr>epdaH_conf_state = cons_state_or_state_old q, epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>) 
  \<Longrightarrow> \<forall>e'. Ex (epdaH_step_relation S \<lparr>epdaH_conf_state = cons_state_or_state_old q, epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> e') \<longrightarrow> (\<exists>y. edge_event e' = Some y) 
  \<Longrightarrow> \<lparr>epdaH_conf_state = cons_state_or_state_old q, epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> \<forall>pS pP X. q = cons_state_and_stack (cons_tuple2 pS pP) X \<longrightarrow> cons_state_or_state_old (cons_state_and_stack (cons_tuple2 pS pP) X) \<in> epda_nonstable_states (epda_delta S) \<or> (\<forall>u\<in> \<Sigma>UC. \<forall>eP\<in> epda_delta P. edge_event eP = Some u \<longrightarrow> edge_src eP = pP \<longrightarrow> (\<exists>eS\<in> epda_delta S. edge_event eS = Some u \<and> edge_src eS = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 pS pP) X) \<and> edge_pop eS = [X])) 
  \<Longrightarrow> q = cons_state_and_stack a X 
  \<Longrightarrow> \<exists>dc. epdaH.derivation S dc \<and> dc 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) \<and> (\<exists>nC eC cC. dc nC = Some (pair eC cC) \<and> epdaH_conf_history cC = h @ [u])"
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac aa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rename_tac p1 p2)
  apply(rename_tac p1 p2)(*strict*)
  apply(erule disjE)
   apply(rename_tac p1 p2)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac p1 p2)(*strict*)
    apply(force)
   apply(rename_tac p1 p2)(*strict*)
   apply(simp add: epda_nonstable_states_def)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea)(*strict*)
   apply(erule_tac
      x="ea"
      in allE)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "\<exists>x. edge_pop ea = [x]")
    apply(rename_tac p1 p2 ea)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="ea"
      in ballE)
     apply(rename_tac p1 p2 ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac p1 p2 ea)(*strict*)
    apply(case_tac ea)
    apply(rename_tac p1 p2 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac edge_popa)
     apply(rename_tac p1 p2 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga a list)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
    apply(rename_tac p1 p2 ea x)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(simp add: corresponds_to_top_stack_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac p1 p2 ea x)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac p1 p2 ea x)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 ea x)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac p1 p2 ea x)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(erule_tac
      x="n1+n"
      in allE) 
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      and P="\<lambda>c. get_configuration (derivation_append d1 d n1 (n1 + n)) = Some c \<longrightarrow>
           F_DPDA_EUML__is_auxiliary (epdaH_conf_state c) \<longrightarrow>
           (\<forall>X. F_DPDA_EUML__get_stack (epdaH_conf_state c) = Some X \<longrightarrow>
                (\<exists>w. epdaH_conf_stack c = X # w))"
      in allE)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(simp add: F_DPDA_EUML__get_stack_def F_DPDA_OTS__get_stack_def F_DPDA_EUML__get_state_def)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(subgoal_tac "x=X")
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(erule_tac
      x="\<lparr>epdaH_conf_state = edge_trg ea, epdaH_conf_history = h, epdaH_conf_stack = edge_push ea @ w\<rparr>"
      in allE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(subgoal_tac "always_applicable_for_auxiliary_states S F_DPDA_EUML__is_auxiliary")
    apply(rename_tac p1 p2 ea x w)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(simp add: always_applicable_for_auxiliary_states_def always_applicable_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac p1 p2 ea x w)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac p1 p2 ea x w)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 ea x w)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac p1 p2 ea x w)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule_tac
      x="if n=0 then e1 else e"
      in allE)
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = X # w\<rparr>"
      and P="\<lambda>X. (\<exists>na. derivation_append d1 d n1 na = Some (pair (if n = 0 then e1 else e) X)) \<longrightarrow> F_DPDA_EUML__is_auxiliary ( (epdaH_conf_state X)) \<longrightarrow> (\<forall>e\<in> epda_delta S. edge_src e = epdaH_conf_state X \<longrightarrow> Ex (epdaH_step_relation S X e))"
      in allE)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(rule_tac
      x="n1+n"
      in exI)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule_tac
      x="ea"
      in ballE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea x w xa)(*strict*)
   apply(simp add: epdaH_step_relation_def)
  apply(rename_tac p1 p2)(*strict*)
  apply(erule_tac
      x="u"
      in ballE)
   apply(rename_tac p1 p2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac p1 p2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac p1 p2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and n="n2"
      and m="Suc n2"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac p1 p2)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac p1 p2)(*strict*)
    apply(force)
   apply(rename_tac p1 p2)(*strict*)
   apply(clarsimp)
  apply(rename_tac p1 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 e2a)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac p1 p2 e2a w)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac p1 p2 e2a w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w edge_srca edge_eventa edge_popa edge_push)(*strict*)
  apply(rename_tac qs re po pu)
  apply(rename_tac p1 p2 w qs re po pu)(*strict*)
  apply(case_tac re)
   apply(rename_tac p1 p2 w qs re po pu)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 w qs po pu)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac p1 p2 w qs re po pu a)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu)(*strict*)
  apply(subgoal_tac "qs=p2")
   apply(rename_tac p1 p2 w qs po pu)(*strict*)
   apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = Some u, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state c2'\<rparr>"
      in ballE)
    apply(rename_tac p1 p2 w qs po pu)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac p1 p2 w qs po pu)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(simp add: corresponds_to_top_stack_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac p1 p2 w po pu eS)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac p1 p2 w po pu eS)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 w po pu eS)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac p1 p2 w po pu eS)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(erule_tac
      x="n1+n"
      in allE)
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      in allE)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(simp add: F_DPDA_EUML__get_stack_def F_DPDA_OTS__get_stack_def F_DPDA_EUML__get_state_def)
   apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = X # wa\<rparr> eS \<lparr>epdaH_conf_state = edge_trg eS, epdaH_conf_history = h@[u], epdaH_conf_stack = (edge_push eS) @ wa\<rparr>) n"
      in exI)
   apply(rule conjI)
    apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
      apply(force)
     apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: option_to_list_def)
    apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule conjI)
    apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
    apply(simp add: der2_def derivation_append_def)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule_tac
      x="Suc n"
      in exI)
   apply(simp add: der2_def derivation_append_def)
  apply(rename_tac p1 p2 w qs po pu)(*strict*)
  apply(thin_tac "\<forall>eP\<in> epda_delta P. edge_event eP = Some u \<longrightarrow> edge_src eP = p2 \<longrightarrow> (\<exists>eS\<in> epda_delta S. edge_event eS = Some u \<and> edge_src eS = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X) \<and> edge_pop eS = [X])")
  apply(rename_tac p1 p2 w qs po pu)(*strict*)
  apply(case_tac c2')
  apply(rename_tac p1 p2 w qs po pu epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu epdaH_conf_state)(*strict*)
  apply(rename_tac qsx)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
  apply(erule impE)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(erule_tac
      x="n1+n"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      in allE)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(erule impE)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx d' m)(*strict*)
  apply(case_tac "d' m")
   apply(rename_tac p1 p2 w qs po pu qsx d' m)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def get_configuration_def)
  apply(rename_tac p1 p2 w qs po pu qsx d' m a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac p1 p2 w qs po pu qsx d' m a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__get_state_def sel_tuple2_2_def)
  apply(thin_tac "epdaH.derivation_initial S d1")
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(thin_tac "d1 n1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)")
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(thin_tac "d2 (Suc n2) = Some (pair (Some \<lparr>edge_src = qs, edge_event = Some u, edge_pop = po, edge_push = pu, edge_trg = qsx\<rparr>) \<lparr>epdaH_conf_state = qsx, epdaH_conf_history = h @ [u], epdaH_conf_stack = pu @ w\<rparr>)")
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(thin_tac "valid_dpda S")
  apply(thin_tac "u \<in> \<Sigma>UC")
  apply(thin_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations S")
  apply(thin_tac "epdaH.derivation S d")
  apply(thin_tac "epdaH.belongs S d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>)")
  apply(thin_tac "\<forall>e'. Ex (epdaH_step_relation S \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> e') \<longrightarrow> (\<exists>y. edge_event e' = Some y)")
  apply(thin_tac "\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> \<in> epdaH_configurations S")
  apply(thin_tac "\<lparr>edge_src = qs, edge_event = Some u, edge_pop = po, edge_push = pu, edge_trg = qsx\<rparr> \<in> epda_delta P")
  apply(subgoal_tac "X" for X)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and d="d2"
      and n="n2"
      in DFA_one_symbol_per_step)
     apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   apply(force)
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and d="d'"
      and n="m"
      in DFA_one_symbol_per_step)
     apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   apply(force)
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(clarsimp)
  apply(rename_tac p2 w qs po d' option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac p2 w qs po d' option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and ?d1.0="d2"
      and ?d2.0="d'"
      and x="0"
      and y="0"
      and n="length h"
      and m="length h"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac p2 w qs po d' option)(*strict*)
              apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def valid_dpda_def valid_pda_def)
             apply(rename_tac p2 w qs po d' option)(*strict*)
             apply(force)
            apply(rename_tac p2 w qs po d' option)(*strict*)
            apply(force)
           apply(rename_tac p2 w qs po d' option)(*strict*)
           apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac p2 w qs po d' option)(*strict*)
          apply(simp add: epdaH.derivation_initial_def)
          apply(case_tac "d2 0")
           apply(rename_tac p2 w qs po d' option)(*strict*)
           apply(clarsimp)
          apply(rename_tac p2 w qs po d' option a)(*strict*)
          apply(case_tac "d' 0")
           apply(rename_tac p2 w qs po d' option a)(*strict*)
           apply(clarsimp)
          apply(rename_tac p2 w qs po d' option a aa)(*strict*)
          apply(case_tac a)
          apply(rename_tac p2 w qs po d' option a aa optiona b)(*strict*)
          apply(case_tac aa)
          apply(rename_tac p2 w qs po d' option a aa optiona b optionb ba)(*strict*)
          apply(clarsimp)
          apply(rename_tac p2 w qs po d' option b ba)(*strict*)
          apply(simp add: epdaH_initial_configurations_def)
         apply(rename_tac p2 w qs po d' option)(*strict*)
         apply(clarsimp)
        apply(rename_tac p2 w qs po d' option)(*strict*)
        apply(clarsimp)
       apply(rename_tac p2 w qs po d' option)(*strict*)
       apply(clarsimp)
      apply(rename_tac p2 w qs po d' option)(*strict*)
      apply(force)
     apply(rename_tac p2 w qs po d' option)(*strict*)
     apply(force)
    apply(rename_tac p2 w qs po d' option)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def epda_effects_def)
   apply(rename_tac p2 w qs po d' option)(*strict*)
   apply(force)
  apply(rename_tac p2 w qs po d' option)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__enforces__operational_controllable_part1_hlp2: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> epdaH.derivation_initial S d1 
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> epdaH.derivation_initial P d2 
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>) 
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2') 
  \<Longrightarrow> epdaH_conf_history c2' = h @ [u] 
  \<Longrightarrow> u \<in> \<Sigma>UC 
  \<Longrightarrow> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> epdaH.derivation S d 
  \<Longrightarrow> epdaH.belongs S d 
  \<Longrightarrow> d 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> d n = Some (pair e \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>) 
  \<Longrightarrow> \<forall>e'. Ex (epdaH_step_relation S \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> e') \<longrightarrow> (\<exists>y. edge_event e' = Some y) 
  \<Longrightarrow> \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> False"
  apply(subgoal_tac "main_states_can_be_left_with_empty_step S F_DPDA_EUML__is_main")
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(simp add: main_states_can_be_left_with_empty_step_def)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      in ballE)
   prefer 2
   apply(simp add: epdaH.get_accessible_configurations_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(clarsimp)
   apply(erule_tac
      x="n1+n"
      in allE)
   apply(simp add: get_configuration_def derivation_append_def)
   apply(case_tac n)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(erule impE)
   apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_state_def)
  apply(clarsimp)
  apply(rename_tac ea)(*strict*)
  apply(case_tac s3)
   apply(rename_tac ea)(*strict*)
   apply(case_tac n)
    apply(rename_tac ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac e)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac e)(*strict*)
     prefer 2
     apply(rule_tac
      d="d1"
      and i="n1"
      in epdaH_epda_stack_is_must_terminated_by_prime)
       apply(rename_tac e)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac e)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
   apply(rename_tac ea nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ea nat)(*strict*)
    prefer 2
    apply(rule_tac
      d="derivation_append d1 d n1"
      and i="n1+Suc nat"
      in epdaH_epda_stack_is_must_terminated_by_prime)
      apply(rename_tac ea nat)(*strict*)
      prefer 2
      apply(rule epdaH.derivation_append_preserves_derivation_initial)
        apply(rename_tac ea nat)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
        apply(force)
       apply(rename_tac ea nat)(*strict*)
       apply(force)
      apply(rename_tac ea nat)(*strict*)
      apply(rule epdaH.derivation_append_preserves_derivation)
        apply(rename_tac ea nat)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac ea nat)(*strict*)
       apply(force)
      apply(rename_tac ea nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac ea nat)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac ea nat)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def derivation_append_def)
   apply(rename_tac ea nat)(*strict*)
   apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac ea aa list)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="ea"
      in allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state=edge_trg ea, epdaH_conf_history=h @ option_to_list None, epdaH_conf_stack=edge_push ea @ list\<rparr>"
      in allE)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__enforces__operational_controllable_part1_hlp3: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> epdaH.derivation_initial S d1 
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> epdaH.derivation_initial P d2 
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>) 
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2') 
  \<Longrightarrow> epdaH_conf_history c2' = h @ [u] 
  \<Longrightarrow> u \<in> \<Sigma>UC 
  \<Longrightarrow> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> epdaH.derivation S d 
  \<Longrightarrow> epdaH.belongs S d 
  \<Longrightarrow> d 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> d n = Some (pair e \<lparr>epdaH_conf_state = cons_state_or_state_new q, epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>) 
  \<Longrightarrow> \<forall>e'. Ex (epdaH_step_relation S \<lparr>epdaH_conf_state = cons_state_or_state_new q, epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> e') \<longrightarrow> (\<exists>y. edge_event e' = Some y) 
  \<Longrightarrow> \<lparr>epdaH_conf_state = cons_state_or_state_new q, epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> \<forall>pS pP X. q = cons_state_and_stack (cons_tuple2 pS pP) X \<longrightarrow> cons_state_or_state_new (cons_state_and_stack (cons_tuple2 pS pP) X) \<in> epda_nonstable_states (epda_delta S) \<or> (\<forall>u\<in> \<Sigma>UC. \<forall>eP\<in> epda_delta P. edge_event eP = Some u \<longrightarrow> edge_src eP = pP \<longrightarrow> (\<exists>eS\<in> epda_delta S. edge_event eS = Some u \<and> edge_src eS = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 pS pP) X) \<and> edge_pop eS = [X])) 
  \<Longrightarrow> q = cons_state_and_stack a X 
  \<Longrightarrow> \<exists>dc. epdaH.derivation S dc \<and> dc 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) \<and> (\<exists>nC eC cC. dc nC = Some (pair eC cC) \<and> epdaH_conf_history cC = h @ [u])"
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac aa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rename_tac p1 p2)
  apply(rename_tac p1 p2)(*strict*)
  apply(erule disjE)    
   apply(rename_tac p1 p2)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac p1 p2)(*strict*)
    apply(force)
   apply(rename_tac p1 p2)(*strict*)
   apply(simp add: epda_nonstable_states_def)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea)(*strict*)
   apply(erule_tac
      x="ea"
      in allE)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "\<exists>x. edge_pop ea = [x]")
    apply(rename_tac p1 p2 ea)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="ea"
      in ballE)
     apply(rename_tac p1 p2 ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac p1 p2 ea)(*strict*)
    apply(case_tac ea)
    apply(rename_tac p1 p2 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac edge_popa)
     apply(rename_tac p1 p2 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga a list)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
    apply(rename_tac p1 p2 ea x)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(simp add: corresponds_to_top_stack_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac p1 p2 ea x)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac p1 p2 ea x)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 ea x)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac p1 p2 ea x)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(erule_tac
      x="n1+n"
      in allE)
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      and P="\<lambda>X. get_configuration (derivation_append d1 d n1 (n1 + n)) = Some X \<longrightarrow> F_DPDA_EUML__is_auxiliary ( (epdaH_conf_state X)) \<longrightarrow> (\<forall>Xa. F_DPDA_EUML__get_stack ( (epdaH_conf_state X)) = Some Xa \<longrightarrow> (\<exists>w. epdaH_conf_stack X = Xa # w))"
      in allE)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac p1 p2 ea x)(*strict*)
   apply(simp add: F_DPDA_EUML__get_stack_def F_DPDA_OTS__get_stack_def F_DPDA_EUML__get_state_def)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(subgoal_tac "x=X")
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(erule_tac
      x="\<lparr>epdaH_conf_state = edge_trg ea, epdaH_conf_history = h, epdaH_conf_stack = edge_push ea @ w\<rparr>"
      in allE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(subgoal_tac "always_applicable_for_auxiliary_states S F_DPDA_EUML__is_auxiliary")
    apply(rename_tac p1 p2 ea x w)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(simp add: always_applicable_for_auxiliary_states_def always_applicable_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac p1 p2 ea x w)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac p1 p2 ea x w)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 ea x w)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac p1 p2 ea x w)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule_tac
      x="if n=0 then e1 else e"
      in allE)
   apply(erule_tac x="\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = X # w\<rparr>" and P="\<lambda>X. (\<exists>na. derivation_append d1 d n1 na = Some (pair (if n = 0 then e1 else e) X)) \<longrightarrow> F_DPDA_EUML__is_auxiliary ((epdaH_conf_state X)) \<longrightarrow> (\<forall>e\<in> epda_delta S. edge_src e = epdaH_conf_state X \<longrightarrow> Ex (epdaH_step_relation S X e))"in allE)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(rule_tac
      x="n1+n"
      in exI)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(clarsimp)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(erule_tac
      x="ea"
      in ballE)
    apply(rename_tac p1 p2 ea x w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac p1 p2 ea x w)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 ea x w xa)(*strict*)
   apply(simp add: epdaH_step_relation_def)
  apply(rename_tac p1 p2)(*strict*)
  apply(erule_tac
      x="u"
      in ballE)
   apply(rename_tac p1 p2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac p1 p2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac p1 p2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and n="n2"
      and m="Suc n2"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac p1 p2)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac p1 p2)(*strict*)
    apply(force)
   apply(rename_tac p1 p2)(*strict*)
   apply(clarsimp)
  apply(rename_tac p1 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 e2a)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac p1 p2 e2a w)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac p1 p2 e2a w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w edge_srca edge_eventa edge_popa edge_push)(*strict*)
  apply(rename_tac qs re po pu)
  apply(rename_tac p1 p2 w qs re po pu)(*strict*)
  apply(case_tac re)
   apply(rename_tac p1 p2 w qs re po pu)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 w qs po pu)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac p1 p2 w qs re po pu a)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu)(*strict*)
  apply(subgoal_tac "qs=p2")
   apply(rename_tac p1 p2 w qs po pu)(*strict*)
   apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = Some u, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state c2'\<rparr>"
      in ballE)
    apply(rename_tac p1 p2 w qs po pu)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac p1 p2 w qs po pu)(*strict*)
   apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(simp add: corresponds_to_top_stack_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac p1 p2 w po pu eS)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac p1 p2 w po pu eS)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 w po pu eS)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac p1 p2 w po pu eS)(*strict*)
     apply(force)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(erule_tac
      x="n1+n"
      in allE)
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      in allE)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(erule impE)
    apply(rename_tac p1 p2 w po pu eS)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac p1 p2 w po pu eS)(*strict*)
   apply(simp add: F_DPDA_EUML__get_stack_def F_DPDA_OTS__get_stack_def F_DPDA_EUML__get_state_def)
   apply(clarsimp)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = X # wa\<rparr> eS \<lparr>epdaH_conf_state = edge_trg eS, epdaH_conf_history = h@[u], epdaH_conf_stack = (edge_push eS)@ wa\<rparr>) n"
      in exI)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule conjI)
    apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
      apply(force)
     apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: option_to_list_def)
    apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule conjI)
    apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
    apply(simp add: der2_def derivation_append_def)
   apply(rename_tac p1 p2 w po pu eS wa)(*strict*)
   apply(rule_tac
      x="Suc n"
      in exI)
   apply(simp add: der2_def derivation_append_def)
  apply(rename_tac p1 p2 w qs po pu)(*strict*)
  apply(thin_tac "\<forall>eP\<in> epda_delta P. edge_event eP = Some u \<longrightarrow> edge_src eP = p2 \<longrightarrow> (\<exists>eS\<in> epda_delta S. edge_event eS = Some u \<and> edge_src eS = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X) \<and> edge_pop eS = [X])")
  apply(rename_tac p1 p2 w qs po pu)(*strict*)
  apply(case_tac c2')
  apply(rename_tac p1 p2 w qs po pu epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu epdaH_conf_state)(*strict*)
  apply(rename_tac qsx)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
  apply(erule impE)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(erule_tac
      x="n1+n"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      in allE)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(erule impE)
   apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx d' m)(*strict*)
  apply(case_tac "d' m")
   apply(rename_tac p1 p2 w qs po pu qsx d' m)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def get_configuration_def)
  apply(rename_tac p1 p2 w qs po pu qsx d' m a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac p1 p2 w qs po pu qsx d' m a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__get_state_def sel_tuple2_2_def)
  apply(thin_tac "epdaH.derivation_initial S d1")
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(thin_tac "d1 n1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)")
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(thin_tac "d2 (Suc n2) = Some (pair (Some \<lparr>edge_src = qs, edge_event = Some u, edge_pop = po, edge_push = pu, edge_trg = qsx\<rparr>) \<lparr>epdaH_conf_state = qsx, epdaH_conf_history = h @ [u], epdaH_conf_stack = pu @ w\<rparr>)")
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(thin_tac "valid_dpda S")
  apply(thin_tac "u \<in> \<Sigma>UC")
  apply(thin_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations S")
  apply(thin_tac "epdaH.derivation S d")
  apply(thin_tac "epdaH.belongs S d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>)")
  apply(thin_tac "\<forall>e'. Ex (epdaH_step_relation S \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> e') \<longrightarrow> (\<exists>y. edge_event e' = Some y)")
  apply(thin_tac "\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state_and_stack (cons_tuple2 p1 p2) X), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> \<in> epdaH_configurations S")
  apply(thin_tac "\<lparr>edge_src = qs, edge_event = Some u, edge_pop = po, edge_push = pu, edge_trg = qsx\<rparr> \<in> epda_delta P")
  apply(subgoal_tac "X" for X)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and d="d2"
      and n="n2"
      in DFA_one_symbol_per_step)
     apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   apply(force)
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and d="d'"
      and n="m"
      in DFA_one_symbol_per_step)
     apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
    apply(force)
   apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
   apply(force)
  apply(rename_tac p1 p2 w qs po pu qsx d' m option)(*strict*)
  apply(clarsimp)
  apply(rename_tac p2 w qs po d' option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac p2 w qs po d' option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and ?d1.0="d2"
      and ?d2.0="d'"
      and x="0"
      and y="0"
      and n="length h"
      and m="length h"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac p2 w qs po d' option)(*strict*)
              apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def valid_dpda_def valid_pda_def)
             apply(rename_tac p2 w qs po d' option)(*strict*)
             apply(force)
            apply(rename_tac p2 w qs po d' option)(*strict*)
            apply(force)
           apply(rename_tac p2 w qs po d' option)(*strict*)
           apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac p2 w qs po d' option)(*strict*)
          apply(simp add: epdaH.derivation_initial_def)
          apply(case_tac "d2 0")
           apply(rename_tac p2 w qs po d' option)(*strict*)
           apply(clarsimp)
          apply(rename_tac p2 w qs po d' option a)(*strict*)
          apply(case_tac "d' 0")
           apply(rename_tac p2 w qs po d' option a)(*strict*)
           apply(clarsimp)
          apply(rename_tac p2 w qs po d' option a aa)(*strict*)
          apply(case_tac a)
          apply(rename_tac p2 w qs po d' option a aa optiona b)(*strict*)
          apply(case_tac aa)
          apply(rename_tac p2 w qs po d' option a aa optiona b optionb ba)(*strict*)
          apply(clarsimp)
          apply(rename_tac p2 w qs po d' option b ba)(*strict*)
          apply(simp add: epdaH_initial_configurations_def)
         apply(rename_tac p2 w qs po d' option)(*strict*)
         apply(clarsimp)
        apply(rename_tac p2 w qs po d' option)(*strict*)
        apply(clarsimp)
       apply(rename_tac p2 w qs po d' option)(*strict*)
       apply(clarsimp)
      apply(rename_tac p2 w qs po d' option)(*strict*)
      apply(force)
     apply(rename_tac p2 w qs po d' option)(*strict*)
     apply(force)
    apply(rename_tac p2 w qs po d' option)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def epda_effects_def)
   apply(rename_tac p2 w qs po d' option)(*strict*)
   apply(force)
  apply(rename_tac p2 w qs po d' option)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__enforces__operational_controllable_part1_hlp4: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> epdaH.derivation_initial S d1 
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> epdaH.derivation_initial P d2 
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>) 
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2') 
  \<Longrightarrow> epdaH_conf_history c2' = h @ [u] 
  \<Longrightarrow> u \<in> \<Sigma>UC 
  \<Longrightarrow> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> epdaH.derivation S d 
  \<Longrightarrow> epdaH.belongs S d 
  \<Longrightarrow> d 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>) 
  \<Longrightarrow> d n = Some (pair e \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>) 
  \<Longrightarrow> \<forall>e'. Ex (epdaH_step_relation S \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> e') \<longrightarrow> (\<exists>y. edge_event e' = Some y) 
  \<Longrightarrow> \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr> \<in> epdaH_configurations S 
  \<Longrightarrow> False"
  apply(subgoal_tac "main_states_can_be_left_with_empty_step S F_DPDA_EUML__is_main")
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(simp add: main_states_can_be_left_with_empty_step_def)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s3\<rparr>"
      in ballE)
   prefer 2
   apply(simp add: epdaH.get_accessible_configurations_def)
   apply(erule_tac
      x="derivation_append d1 d n1"
      in allE)
   apply(erule impE)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(clarsimp)
   apply(erule_tac
      x="n1+n"
      in allE)
   apply(simp add: get_configuration_def derivation_append_def)
   apply(case_tac n)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(erule impE)
   apply(simp add: F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
  apply(clarsimp)
  apply(rename_tac ea)(*strict*)
  apply(case_tac s3)
   apply(rename_tac ea)(*strict*)
   apply(case_tac n)
    apply(rename_tac ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac e)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac e)(*strict*)
     prefer 2
     apply(rule_tac
      d="d1"
      and i="n1"
      in epdaH_epda_stack_is_must_terminated_by_prime)
       apply(rename_tac e)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac e)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
   apply(rename_tac ea nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ea nat)(*strict*)
    prefer 2
    apply(rule_tac
      d="derivation_append d1 d n1"
      and i="n1+Suc nat"
      in epdaH_epda_stack_is_must_terminated_by_prime)
      apply(rename_tac ea nat)(*strict*)
      prefer 2
      apply(rule epdaH.derivation_append_preserves_derivation_initial)
        apply(rename_tac ea nat)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
        apply(force)
       apply(rename_tac ea nat)(*strict*)
       apply(force)
      apply(rename_tac ea nat)(*strict*)
      apply(rule epdaH.derivation_append_preserves_derivation)
        apply(rename_tac ea nat)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac ea nat)(*strict*)
       apply(force)
      apply(rename_tac ea nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac ea nat)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac ea nat)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def derivation_append_def)
   apply(rename_tac ea nat)(*strict*)
   apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac ea aa list)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="ea"
      in allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state=edge_trg ea, epdaH_conf_history=h @ option_to_list None, epdaH_conf_stack=edge_push ea @ list\<rparr>"
      in allE)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__enforces__operational_controllable_part1: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> (F_DPDA_NCS S P \<Sigma>UC = {}) = (S = G) 
  \<Longrightarrow> (S = G) \<le> epda_operational_controllable S P \<Sigma>UC"
  apply(simp (no_asm))
  apply(rule impI)
  apply(subgoal_tac "G=S")
   prefer 2
   apply(force)
  apply(thin_tac "S=G")
  apply(clarsimp)
  apply(simp add: epda_operational_controllable_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(simp add: F_DPDA_NCS_def)
  apply(subgoal_tac "c1 \<in> epdaH_configurations S")
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in epdaH.belongs_configurations)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   prefer 2
   apply(rule_tac
      c="c1"
      and G="S"
      in stable_configuration_can_be_reached)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(simp add: epdaH.get_accessible_configurations_def)
   apply(rule_tac
      x="d1"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="n1"
      in exI)
   apply(case_tac "d1 n1")
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
  apply(subgoal_tac "c' \<in> epdaH_configurations S")
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
  apply(erule_tac
      x="epdaH_conf_state c'"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
   apply(simp add: epdaH_configurations_def)
   apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c')(*strict*)
  apply(case_tac c1)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u d n e c' epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 c2 e2' c2' u d n e c' epdaH_conf_statea epdaH_conf_stack)(*strict*)
  apply(rename_tac q1 s1)
  apply(rename_tac d1 n1 e1 d2 n2 e2 c2 e2' c2' u d n e c' q1 s1)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d1 n1 e1 d2 n2 e2 c2 e2' c2' u d n e c' q1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e c' q1 s1 epdaH_conf_statea epdaH_conf_stack)(*strict*)
  apply(rename_tac q2 s2)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e c' q1 s1 q2 s2)(*strict*)
  apply(case_tac c')
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e c' q1 s1 q2 s2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q3 h s3)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 q3 h s3)(*strict*)
  apply(case_tac q3)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 q3 h s3 q)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q)(*strict*)
   apply(erule_tac
      x="cons_state_or_state_old"
      in allE)
   apply(clarsimp)
   apply(case_tac q)
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
    apply(rule F_DPDA_RCS__enforces__operational_controllable_part1_hlp1)
                     apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                     apply(force)
                    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                    apply(force)
                   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                   apply(force)
                  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                  apply(force)
                 apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                 apply(force)
                apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                apply(force)
               apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
               apply(force)
              apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
              apply(force)
             apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
             apply(force)
            apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
            apply(force)
           apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
           apply(force)
          apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
          apply(force)
         apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
         apply(force)
        apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
   apply(rule F_DPDA_RCS__enforces__operational_controllable_part1_hlp2)
                  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
                  apply(force)
                 apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
                 apply(force)
                apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
                apply(force)
               apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
               apply(force)
              apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
              apply(force)
             apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
             apply(force)
            apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
            apply(force)
           apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
           apply(force)
          apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
          apply(force)
         apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
         apply(force)
        apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 q3 h s3 q)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q)(*strict*)
  apply(erule_tac
      x="cons_state_or_state_new"
      in allE)
  apply(clarsimp)
  apply(case_tac q)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
   apply(rule F_DPDA_RCS__enforces__operational_controllable_part1_hlp3)
                    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                    apply(force)
                   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                   apply(force)
                  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                  apply(force)
                 apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                 apply(force)
                apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
                apply(force)
               apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
               apply(force)
              apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
              apply(force)
             apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
             apply(force)
            apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
            apply(force)
           apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
           apply(force)
          apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
          apply(force)
         apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
         apply(force)
        apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a b)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 q a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
  apply(rule F_DPDA_RCS__enforces__operational_controllable_part1_hlp4)
                 apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
                 apply(force)
                apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
                apply(force)
               apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
               apply(force)
              apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
              apply(force)
             apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
             apply(force)
            apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
            apply(force)
           apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
           apply(force)
          apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
          apply(force)
         apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
         apply(force)
        apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' c2' u d n e q1 s1 q2 s2 h s3 a)(*strict*)
  apply(force)
  done

lemma F_DPDA_RCS__enforces__operational_controllable_part2: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> epdaH.accessible S 
  \<Longrightarrow> (F_DPDA_NCS S P \<Sigma>UC = {}) = (S = G) 
  \<Longrightarrow> epda_operational_controllable S P \<Sigma>UC \<le> (S = G)"
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. x \<in> F_DPDA_NCS S P \<Sigma>UC")
   prefer 2
   apply(force)
  apply(thin_tac "F_DPDA_NCS S P \<Sigma>UC \<noteq> {}")
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "S \<noteq> G")
  apply(subgoal_tac "x \<in> epda_states S")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_NCS_def)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "epda_destinations.state x \<in> epdaH.get_accessible_destinations S")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: epdaH.accessible_def epda_destinations_def)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaH.get_accessible_destinations_def epdaH_get_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(erule disjE)
   apply(rename_tac x d i e c)(*strict*)
   prefer 2
   apply(case_tac e)
    apply(rename_tac x d i e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d i e c a)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s)(*strict*)
  apply(thin_tac "epdaH.accessible S")
  apply(simp add: epda_operational_controllable_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in allE)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac d i e q h s)(*strict*)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in allE)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d i e q h s)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d' m)(*strict*)
  apply(case_tac "d' m")
   apply(rename_tac d i e q h s d' m)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e q h s d' m a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac d i e q h s d' m a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d' m option)(*strict*)
  apply(simp add: F_DPDA_NCS_def)
  apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(subgoal_tac "sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X)))) = (edge_src eP)")
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
    apply(simp add: sel_tuple2_2_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_state_def)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(simp add: sel_tuple2_2_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_state_def)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="derivation_append d' (der2 \<lparr>epdaH_conf_state = edge_src eP, epdaH_conf_history = h, epdaH_conf_stack = [epda_box P]\<rparr> eP \<lparr>epdaH_conf_state = edge_trg eP, epdaH_conf_history = h@(option_to_list(edge_event eP)), epdaH_conf_stack = [epda_box P]\<rparr>) m"
      in allE)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
    apply(force)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
    apply(rule_tac epdaH.der2_is_derivation)
    apply(simp add: epdaH_step_relation_def)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule_tac
      x="m"
      in allE)
  apply(erule_tac
      x="option"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = edge_src eP, epdaH_conf_history = h, epdaH_conf_stack = [epda_box P]\<rparr>"
      in allE)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(simp add: der2_def derivation_append_def)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule_tac
      x="Some eP"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = edge_trg eP, epdaH_conf_history = h @ option_to_list (edge_event eP), epdaH_conf_stack = [epda_box P]\<rparr>"
      in allE)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(simp add: der2_def derivation_append_def)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule_tac
      x="u"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
   apply(force)
  apply(rename_tac d i e h s d' m option f pS X u eP)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP dc nC eC cC)(*strict*)
  apply(case_tac nC)
   apply(rename_tac d i e h s d' m option f pS X u eP dc nC eC cC)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP dc nC eC cC nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat)(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      and n="0"
      and m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat)(*strict*)
    apply(force)
   apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat)(*strict*)
   apply(force)
  apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat e2 c2)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat e2 c2 edge_srca edge_eventa edge_popa edge_push edge_trg)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat c2 edge_srca edge_eventa edge_popa edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d i e h s d' m option f pS X u eP dc eC cC nat c2 qs re po pu qt)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 re po pu w)(*strict*)
  apply(case_tac re)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 re po pu w)(*strict*)
   apply(simp add: epda_nonstable_states_def)
   apply(erule_tac
      x="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = None, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state c2\<rparr>"
      and P="\<lambda>x. edge_src x = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X) \<longrightarrow> (\<exists>y. edge_event x = Some y)"
      in ballE)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 re po pu w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 re po pu w)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 re po pu w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 po pu w a)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat c2 po pu w a epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
  apply(subgoal_tac "\<lparr>epdaH_conf_state = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), epdaH_conf_history = h, epdaH_conf_stack = po @ w\<rparr> \<in> epdaH_configurations S")
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def F_DPDA_RCS__SpecInput_def)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
    apply(force)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
   apply(force)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a epdaH_conf_state)(*strict*)
  apply(rename_tac qx)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      and G="S"
      and n="0"
      and m="Suc 0"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(simp add: epdaH.derivation_initial_def)
       prefer 2
       apply(clarsimp)
      apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
    apply(force)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
  apply(subgoal_tac "epdaH.belongs S dc")
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
   prefer 2
   apply(rule epdaH.derivation_belongs)
      apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
     apply(force)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
    apply(force)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
   apply(force)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      and G="S"
      and n="Suc 0"
      and m="nat"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(simp add: epdaH.derivation_initial_def)
       prefer 2
       apply(clarsimp)
      apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
    apply(rule_tac
      d="dc"
      in epdaH.belongs_configurations)
     apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
     apply(force)
    apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
    apply(force)
   apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X u eP dc eC cC nat po pu w a qx ha)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qx\<rparr>"
      in ballE)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(simp add: corresponds_to_top_stack_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), epdaH_conf_history = h, epdaH_conf_stack = po @ w\<rparr>"
      in allE)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(erule disjE)
    apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
  apply(subgoal_tac "\<exists>x. po = [x]")
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat pu w a qx x)(*strict*)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat pu w a qx x)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat pu w a qx x)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      A="epda_delta S"
      and x="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qx\<rparr>"
      and P="\<lambda>x. length (edge_pop x) = Suc 0"
      in ballE)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
  apply(clarsimp)
  apply(case_tac po)
   apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e h d' m option f pS X eP dc eC cC nat po pu w a qx aa list)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__Enforce_Marked_Controllable_Subset__unmarked_language_part1: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) = Some G 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> x \<in> epdaH.unmarked_language S 
  \<Longrightarrow> \<forall>w. strict_prefix w x \<longrightarrow> controllable_word w {w. \<exists>v\<in> \<Sigma>UC. w = [v]} (epdaH.unmarked_language P) (epdaH.unmarked_language S) 
  \<Longrightarrow> retain_edges_between_retained_states S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) G 
  \<Longrightarrow> x \<in> epdaH.unmarked_language G"
  apply(induct x rule: rev_induct)
   apply(rule epda_empty_in_epdaH_unmarked_language)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(rule_tac
      x="xs"
      in epdaH_unmarked_languageuage_prefix_closed)
    apply(rename_tac x xs)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xs)(*strict*)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x xs)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs w)(*strict*)
   apply(erule_tac
      x="w"
      in allE)
   apply(erule impE)
    apply(rename_tac x xs w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xs w)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(thin_tac "xs \<in> epdaH.unmarked_language S")
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x xs d da)(*strict*)
  apply(fold epdaH.unmarked_language_def)
  apply(thin_tac "epdaH.derivation S d")
  apply(thin_tac "epdaH.derivation G da")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d da i ia e ea c ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac ca)
  apply(rename_tac x d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d da i ia e ea epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
  apply(subgoal_tac "epdaH.derivation_initial S d2")
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
   prefer 2
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
      prefer 2
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def)
   apply(force)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and ?d1.0="d2"
      and ?d2.0="d1"
      and ?i1.0="i2"
      and ?i2.0="i1"
      in epdaH_coincide_strict_prefix)
        apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
        apply(simp add: F_DPDA_RCS__SpecInput_def)
       apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
       apply(force)
      apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
      apply(force)
     apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
   apply(simp add: strict_prefix_def)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
   prefer 2
   apply(rule_tac
      n="i1"
      and P="\<lambda>n. n\<le>i1 \<and> prefix (h2@[x]) (epdaH_conf_history (the(get_configuration(d1 n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k)(*strict*)
   prefer 2
   apply(rule_tac
      g="d1"
      and n="k"
      and m="i1"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k)(*strict*)
    apply(force)
   apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k)(*strict*)
   apply(force)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k e c)(*strict*)
  apply(thin_tac "d1 i1 = Some (pair e1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h2 @ [x], epdaH_conf_stack = s1\<rparr>)")
  apply(rename_tac x d1 d2 i1 i2 e1 e2 q1 s1 q2 h2 s2 k e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e c)(*strict*)
  apply(case_tac k)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c)(*strict*)
   apply(subgoal_tac "epdaH_conf_history c = []")
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c)(*strict*)
    apply(clarsimp)
    apply(simp add: prefix_def)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c nat)(*strict*)
  apply(rename_tac k)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c k)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c k)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and n="k"
      and m="Suc k"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c k)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c k)(*strict*)
    apply(force)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c k)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 e c k)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1)(*strict*)
  apply(rule_tac
      x="derivation_take d1 (Suc k)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def)
   apply(clarsimp)
   apply(rule_tac
      x="Suc k"
      in exI)
   apply(simp add: derivation_take_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ca)(*strict*)
   apply(case_tac c)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 ca epdaH_conf_state epdaH_conf_stack)(*strict*)
   apply(rule_tac
      xs="ca"
      in rev_cases)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 ca epdaH_conf_state epdaH_conf_stack)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 ca epdaH_conf_state epdaH_conf_stack ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 epdaH_conf_state epdaH_conf_stack ys y)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 epdaH_conf_statea epdaH_conf_stacka ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 ys y w)(*strict*)
   apply(case_tac c1)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 ys y w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a ys y w epdaH_conf_historya)(*strict*)
   apply(rename_tac h1)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a ys y w h1)(*strict*)
   apply(case_tac e2a)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a ys y w h1 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys y w h1 edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
   apply(rename_tac qs re po pu qt)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys y w h1 qs re po pu qt)(*strict*)
   apply(case_tac re)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys y w h1 qs re po pu qt)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys y w h1 qs po pu qt)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys y w qs po pu qt)(*strict*)
    apply(force)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys y w h1 qs re po pu qt a)(*strict*)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 ys w qs po pu qt a)(*strict*)
   apply(force)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1)(*strict*)
  apply(subgoal_tac "(h2 @ [x]) = epdaH_conf_history c")
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ca)(*strict*)
   apply(rule_tac
      xs="ca"
      in rev_cases)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ca ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ys y)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ys y w)(*strict*)
   apply(case_tac c1)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 ys y w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a ys y w epdaH_conf_historya)(*strict*)
   apply(rename_tac h1)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a ys y w h1)(*strict*)
   apply(case_tac e2a)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a ys y w h1 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys y w h1 edge_src edge_event edge_pop edge_push)(*strict*)
   apply(rename_tac qs re po pu)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys y w h1 qs re po pu)(*strict*)
   apply(case_tac re)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys y w h1 qs re po pu)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys y w h1 qs po pu)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys y w qs po pu)(*strict*)
    apply(force)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys y w h1 qs re po pu a)(*strict*)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 ys w qs po pu a)(*strict*)
   apply(force)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1)(*strict*)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 c k e1 e2a c1 q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
  apply(thin_tac "(h2 @ [x]) \<sqsubseteq> (h2 @ [x])")
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
   prefer 2
   apply(rule_tac
      g="d1"
      and n="k"
      and m="Suc k"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
    apply(force)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
   apply(force)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
  apply(clarsimp)
  apply(erule_tac x="k" and P="\<lambda>X. X < Suc k \<longrightarrow> \<not> (h2 @ [x]) \<sqsubseteq> epdaH_conf_history (the (case_option None (case_derivation_configuration (\<lambda>e. Some)) (d1 X)))"in allE)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s)(*strict*)
  apply(clarsimp)
  apply(case_tac c1)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a c1 q s epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a q s epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a qa sa q h s)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a h w)(*strict*)
  apply(simp add: prefix_def)
  apply(case_tac e2a)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a h w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 e2a h w qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 h w qs re po pu qt)(*strict*)
  apply(case_tac re)
   apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 h w qs re po pu qt)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 h w qs re po pu qt a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d1 d2 i1 i2 e2 q2 h2 s2 k e1 h w qs po pu qt a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 h w qs po pu qt a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 h w qs po pu qt a)(*strict*)
   prefer 2
   apply(rule_tac
      n="k"
      and P="\<lambda>n. n\<le>k \<and> h=(epdaH_conf_history (the(get_configuration(d1 n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 h w qs po pu qt a)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka)(*strict*)
   prefer 2
   apply(rule_tac
      g="d1"
      and n="ka"
      and m="k"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(subgoal_tac "ka \<le> i2")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and ?d1.0="d1"
      and ?d2.0="d1"
      in epdaH_first_time_shorter_than_some_time)
         apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
         apply(simp add: F_DPDA_RCS__SpecInput_def)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(subgoal_tac "\<forall>i. ka \<le> i \<and> i \<le> Suc k \<longrightarrow> (epdaH_conf_state (the(get_configuration(d1 i))))\<notin>F_DPDA_NCS S P \<Sigma>UC")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s c)(*strict*)
    apply(simp add: get_configuration_def epdaH.derivation_initial_def derivation_take_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(simp add: epdaH.derivation_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
   apply(case_tac i)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
    apply(simp add: get_configuration_def epdaH.derivation_initial_def derivation_take_def)
    apply(case_tac "d1 0")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s aa)(*strict*)
    apply(simp add: get_configuration_def epdaH.derivation_def epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(case_tac aa)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s aa option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i nat)(*strict*)
   apply(rename_tac kx)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx)(*strict*)
   apply(case_tac "derivation_take d1 (Suc k) (Suc kx)")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx aa)(*strict*)
   apply(subgoal_tac "Suc kx \<le> Suc k")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx aa)(*strict*)
    prefer 2
    apply(simp add: derivation_take_def)
    apply(case_tac "kx\<le>k")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx aa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx aa)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i kx aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
   apply(simp add: derivation_take_def)
   apply(rule_tac
      t="derivation_take d1 (Suc k) kx"
      and s="d1 kx"
      in ssubst)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="kx"
      and m="Suc kx"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(subgoal_tac "e2a \<in> epda_delta G")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(subgoal_tac "epdaH_conf_state c1 \<in> epda_states G")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(subgoal_tac "epdaH_conf_state c2 \<in> epda_states G")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     apply(simp only: retain_edges_between_retained_states_def)
     apply(erule_tac
      x="e2a"
      in ballE)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      prefer 2
      apply(simp add: epdaH_step_relation_def)
     apply(subgoal_tac "edge_src e2a \<in> epda_states S - F_DPDA_NCS S P \<Sigma>UC \<and>
       edge_trg e2a \<in> epda_states S - F_DPDA_NCS S P \<Sigma>UC")
      prefer 2
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def)
      apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      apply(clarsimp)
      apply(simp add: epdaH_step_relation_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(case_tac "Suc kx\<le>i2")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     apply(erule_tac
      x="Suc kx"
      and P="\<lambda>x. x \<le> i2 \<longrightarrow> d2 x = d1 x"
      in allE)
     apply(clarsimp)
     apply(subgoal_tac "c2 \<in> epdaH_configurations G")
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      prefer 2
      apply(rule_tac
      d="d2"
      in epdaH.belongs_configurations)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
       apply(rule_tac
      d="d2"
      in epdaH.derivation_initial_belongs)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     apply(simp add: epdaH_configurations_def)
     apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(subgoal_tac "i2 \<le> kx")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="Suc kx"
      and P="\<lambda>X. ka \<le> X \<and> X \<le> Suc k \<longrightarrow> epdaH_conf_state (the (get_configuration (d1 X))) \<notin> F_DPDA_NCS S P \<Sigma>UC"
      in allE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(erule impE)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2 wa)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e2a"
      and P="\<lambda>e2a. valid_epda_step_label S e2a"
      in ballE)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2 wa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2 wa)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(case_tac "kx\<le>i2")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(erule_tac
      x="kx"
      and P="\<lambda>kx. kx \<le> i2 \<longrightarrow> d2 kx = d1 kx"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "c1 \<in> epdaH_configurations G")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     prefer 2
     apply(rule_tac
      d="d2"
      in epdaH.belongs_configurations)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      apply(rule_tac
      d="d2"
      in epdaH.derivation_initial_belongs)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(simp add: epdaH_configurations_def)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(subgoal_tac "i2 < kx")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="kx"
      and P="\<lambda>kx. ka \<le> kx \<and> kx \<le> Suc k \<longrightarrow> epdaH_conf_state (the (get_configuration (d1 kx))) \<notin> F_DPDA_NCS S P \<Sigma>UC"
      in allE)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(erule impE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2 wa)(*strict*)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2a"
      and P="\<lambda>e2a. valid_epda_step_label S e2a"
      in ballE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2 wa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s kx e1a e2a c1 c2 wa)(*strict*)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(subgoal_tac "ka \<le> k")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and ?d1.0="d1"
      and ?d2.0="d1"
      in epdaH_first_time_shorter_than_some_time)
         apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
         apply(simp add: F_DPDA_RCS__SpecInput_def)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
  apply(case_tac "i<k")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
    prefer 2
    apply(rule_tac
      g="d1"
      and n="i"
      and m="k"
      in epdaH.pre_some_position_is_some_position)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i ea c)(*strict*)
   apply(case_tac c)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i ea c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(rename_tac q h s)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea c q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "q \<in> epda_nonstable_states (epda_delta S)")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
    apply(simp add: F_DPDA_NCS_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
   apply(thin_tac "q \<in> F_DPDA_NCS S P \<Sigma>UC")
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="i"
      and m="Suc k"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s e2a c2)(*strict*)
   apply(simp add: epda_nonstable_states_def)
   apply(rule_tac
      x="e2a"
      in bexI)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s e2a c2)(*strict*)
    prefer 2
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea q h s e2a c2)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea h e2a c2 wa)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea h e2a c2 wa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea h e2a wa)(*strict*)
   apply(case_tac "e2a")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e qa ha sa i ea h e2a wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(rename_tac qs re po pu qt)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h e2a wa qs re po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs re po pu qt)(*strict*)
   apply(case_tac re)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs re po pu qt)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs re po pu qt aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and G="S"
      and n="Suc i"
      and m="k - Suc i"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
        apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
     apply(rule_tac
      d="d1"
      and i="Suc i"
      in epdaH.belongs_configurations)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa ha sa i ea h wa qs po pu qt aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and G="S"
      and n="ka"
      and m="i-ka"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
        apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
     apply(rule_tac
      d="d1"
      in epdaH.belongs_configurations)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qsa poa pua qta a ka e qa sa i ea h wa qs po pu qt aa hb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
  apply(subgoal_tac "k\<le>i")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i=k")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(simp add: get_configuration_def)
   apply(erule_tac
      x="h"
      in allE)
   apply(erule impE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
    apply(simp add: strict_prefix_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(subgoal_tac " qs \<in> epda_states S \<and> (\<exists>f pS pP X. qs = f (cons_state_and_stack (cons_tuple2 pS pP) X) \<and> (f = cons_state_or_state_new \<or> f = cons_state_or_state_old) \<and> qs \<notin> epda_nonstable_states (epda_delta S) \<and> (\<exists>u\<in> \<Sigma>UC. \<exists>eP\<in> epda_delta P. edge_src eP = pP \<and> edge_event eP = Some u \<and> (\<forall>eS\<in> epda_delta S. edge_event eS = Some u \<longrightarrow> edge_src eS = qs \<longrightarrow> edge_pop eS \<noteq> [X])))")
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_NCS_def)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rule_tac x="f" in exI)
    apply(rule_tac x="pS" in exI)
    apply(rule_tac x="pP" in exI)
    apply(rule_tac x="X" in exI)
    apply(clarsimp)
    apply(rule_tac x="u" in bexI)
     prefer 2
     apply(force)
    apply(rule_tac x="eP" in bexI)
     prefer 2
     apply(force)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP)(*strict*)
   apply(simp add: controllable_word_def)
   apply(erule_tac
      x="[u]"
      in allE)
   apply(clarsimp)
   apply(erule impE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP)(*strict*)
    apply(simp add: epdaH.unmarked_language_def)
    apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP)(*strict*)
     prefer 2
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP)(*strict*)
    apply(simp add: epdaH_reflection_to_DFA_exists_def)
    apply(erule_tac
      x="d1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="k"
      and P="\<lambda>k. \<forall>c. get_configuration (d1 k) = Some c \<longrightarrow> (\<exists>d'. epdaH.derivation_initial P d' \<and> (\<exists>m. get_configuration (d' m) = Some \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state c))), epdaH_conf_history = epdaH_conf_history c, epdaH_conf_stack = [epda_box P]\<rparr>))"
      in allE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m)(*strict*)
    apply(subgoal_tac "sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X)))) = edge_src eP")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m)(*strict*)
     prefer 2
     apply(erule disjE)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m)(*strict*)
      apply(simp add: sel_tuple2_2_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_state_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m)(*strict*)
     apply(simp add: sel_tuple2_2_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_state_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m)(*strict*)
    apply(clarsimp)
    apply(case_tac "d' m")
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m aa)(*strict*)
    apply(clarsimp)
    apply(case_tac aa)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m aa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
    apply(rule_tac
      x="derivation_append d' (der2 \<lparr>epdaH_conf_state = edge_src eP, epdaH_conf_history = h, epdaH_conf_stack = [epda_box P]\<rparr> eP \<lparr>epdaH_conf_state = edge_trg eP, epdaH_conf_history = h@[u], epdaH_conf_stack = [epda_box P]\<rparr>) m"
      in exI)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation_initial)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_dfa_def valid_pda_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
      apply(rule epdaH.der2_is_derivation)
      apply(simp add: epdaH_step_relation_def)
      apply(simp add: option_to_list_def)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_dfa_def valid_pda_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def derivation_append_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d' m option)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(simp add: epdaH_unmarked_effect_def)
    apply(rule_tac
      x="Suc m"
      in exI)
    apply(simp add: der2_def derivation_append_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP)(*strict*)
   apply(simp add: epdaH.unmarked_language_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d)(*strict*)
   apply(thin_tac "epdaH.derivation S d")
   apply(simp add: epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d i ea c)(*strict*)
   apply(case_tac c)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e q h s f pS X u eP d i ea c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(rename_tac q h s)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea c q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s)(*strict*)
    prefer 2
    apply(rule_tac
      n="i"
      and P="\<lambda>n. n\<le>i \<and> ha@[u] = (epdaH_conf_history (the(get_configuration(d n)))) "
      in ex_least_nat_le_prime)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb)(*strict*)
    prefer 2
    apply(rule_tac
      g="d"
      and n="kb"
      and m="i"
      in epdaH.pre_some_position_is_some_position)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb eb c)(*strict*)
   apply(case_tac c)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea q s kb eb c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(rename_tac q h s)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb kb eb c q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb kb eb q h s)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb kb eb q s)(*strict*)
   apply(case_tac kb)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb kb eb q s)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s)(*strict*)
    apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb kb eb q s nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s nat)(*strict*)
   apply(rename_tac kb)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s kb)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s kb)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and n="kb"
      and m="Suc kb"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s kb)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s kb)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s kb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb eb q s kb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb q s kb e1a e2a c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb q s kb e1a e2a c1 epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb qc sc kb e1a e2a c1 q h s)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w po pu qt a ka e qa ha sa f pS X u eP d i ea qb sb qc sc kb e1a e2a c1 q h s edge_srca edge_eventa edge_popa edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa ha sa f pS X u eP d i ea qb sb qc sc kb e1a e2a c1 q h s qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa ha sa f pS X u eP d i ea qb sb qc sc kb e1a q h s qs re po pu qt)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa ha sa f pS X u eP d i ea qb sb kb e1a h qs re po pu qt wa)(*strict*)
  apply(case_tac re)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa ha sa f pS X u eP d i ea qb sb kb e1a h qs re po pu qt wa)(*strict*)
  apply(simp add: option_to_list_def)
  apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa ha sa f pS X u eP d i ea qb sb kb e1a h qs re po pu qt wa aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa ha sa f pS X u eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  apply(subgoal_tac "d kb = d1 k")
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
  apply(erule_tac
    x="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = Some aa, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
    in ballE)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. po = [x]")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
    x="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = Some aa, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
    and P="\<lambda>x. length (edge_pop x) = Suc 0"
    and A="epda_delta S"
    in ballE)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
   apply(clarsimp)
   apply(case_tac po)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa ab list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h pu qt wa aa x)(*strict*)
  apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h pu qt wa aa x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h pu qt wa aa x)(*strict*)
  apply(simp add: corresponds_to_top_stack_def)
  apply(erule_tac
    x="d"
    in allE)
  apply(clarsimp)
  apply(erule_tac
    x="kb"
    and P="\<lambda>kb. \<forall>c. get_configuration (d kb) = Some c \<longrightarrow> F_DPDA_EUML__is_auxiliary ((epdaH_conf_state c)) \<longrightarrow> (\<forall>X. F_DPDA_EUML__get_stack ((epdaH_conf_state c)) = Some X \<longrightarrow> (\<exists>w. epdaH_conf_stack c = X # w))"
    in allE)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h pu qt wa aa x)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(erule disjE)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h pu qt wa aa x)(*strict*)
   apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h pu qt wa aa x)(*strict*)
  apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  prefer 2
  apply(rule_tac
    G="S"
    and ?d1.0="d"
    and ?d2.0="d1"
    and ?n1.0="kb"
    and ?n2.0="k"
    in epdaH_coincide_on_stable_configurations)
         apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
         apply(simp add: F_DPDA_RCS__SpecInput_def)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
    apply(rule_tac
    ?c2.0="\<lparr>epdaH_conf_state = qt, epdaH_conf_history = h @ [aa], epdaH_conf_stack = pu @ wa\<rparr>"
    and G="S"
    and d="d"
    and n="kb"
    and ?e2.0="\<lparr>edge_src = qs, edge_event = Some aa, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
    and ?e1.0="eb"
    in DPDA_conflicting_edges)
          apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def)
         apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
         apply(force)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
        apply(force)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
      apply(simp add: epdaH_step_relation_def)
      apply(clarsimp)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h po pu qt wa aa eb c' wb)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
     apply(force)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
   apply(rule_tac
    ?c2.0="\<lparr>epdaH_conf_state = qta, epdaH_conf_history = h @ [a], epdaH_conf_stack = pua @ w\<rparr>"
    and G="S"
    and d="d1"
    and n="k"
    and ?e2.0="\<lparr>edge_src = f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X), edge_event = Some a, edge_pop = poa, edge_push = pua, edge_trg = qta\<rparr>"
    and ?e1.0="eb"
    in DPDA_conflicting_edges)
         apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
         apply(simp add: F_DPDA_RCS__SpecInput_def)
        apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
        apply(force)
       apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
       apply(force)
      apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
      apply(force)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c' wb)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
    apply(force)
   apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa eb c')(*strict*)
   apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w poa pua qta a ka e qa sa f pS X eP d i ea qb sb kb e1a h qs po pu qt wa aa)(*strict*)
  apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
  apply(subgoal_tac "i=Suc k")
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s i)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(subgoal_tac "executing_edge_from_auxiliary_to_main_state S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main")
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  prefer 2
  apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(simp add: executing_edge_from_auxiliary_to_main_state_def)
  apply(simp add: get_configuration_def)
  apply(erule_tac
    x="\<lparr>edge_src = qs, edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
    in allE)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu qt a ka e q h s)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_NCS_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu a ka e q h s f pS X u eP)(*strict*)
  apply(simp add: F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
  apply(erule disjE)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu a ka e q h s f pS X u eP)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 i1 i2 e2 q2 s2 k e1 w qs po pu a ka e q h s f pS X u eP)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__Enforce_Marked_Controllable_Subset__unmarked_language_part2: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) = Some G 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> x \<in> epdaH.unmarked_language G 
  \<Longrightarrow> x \<in> epdaH.unmarked_language S 
  \<Longrightarrow> strict_prefix w x 
  \<Longrightarrow> controllable_word w (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language P) (epdaH.unmarked_language S)"
  apply(simp add: controllable_word_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac v)(*strict*)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac v d da db)(*strict*)
  apply(thin_tac "epdaH.derivation G d")
  apply(thin_tac "epdaH.derivation P db")
  apply(thin_tac "epdaH.derivation S da")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac v d da db i ia ib e ea eb c ca cb)(*strict*)
  apply(case_tac c)
  apply(rename_tac v d da db i ia ib e ea eb c ca cb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac ca)
  apply(rename_tac v d da db i ia ib e ea eb c ca cb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(case_tac cb)
  apply(rename_tac v d da db i ia ib e ea eb c ca cb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 c1 c2 c3 q1 h1 s1 q2 h s2 q3 h3 s3)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 c1 c2 c3 q1 h1 s1 q2 h s2 q3 h3 s3)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3)(*strict*)
  apply(case_tac "dx1 0")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a)(*strict*)
  apply(case_tac "dx2 0")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa)(*strict*)
  apply(case_tac "dx3 0")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab)(*strict*)
  apply(case_tac a)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab option b optiona ba)(*strict*)
  apply(case_tac ab)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab option b optiona ba optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(case_tac option)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(case_tac optionb)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(subgoal_tac "b \<in> epdaH_initial_configurations G")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(subgoal_tac "ba \<in> epdaH_initial_configurations S")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(subgoal_tac "bb \<in> epdaH_initial_configurations P")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(rename_tac c01 c02 c03)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(subgoal_tac "i3=length(w@[v])")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
    prefer 2
    apply(rule_tac
      d="dx3"
      and G="P"
      and n="i3"
      in DFA_one_symbol_per_step)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(subgoal_tac "\<exists>a w2. h=w@a#w2")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   prefer 2
   apply(rule_tac
      xs="h"
      in rev_cases)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
    apply(simp add: strict_prefix_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 ys y)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 ys y c)(*strict*)
   apply(rule_tac
      xs="c"
      in rev_cases)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 ys y c)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 ys y c ysa ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 y ysa)(*strict*)
   apply(case_tac ysa)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 y ysa)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 y ysa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2)(*strict*)
   prefer 2
   apply(rule_tac
      n="i1"
      and P="\<lambda>n. n\<le>i1 \<and> prefix (w@[a]) (epdaH_conf_history (the(get_configuration(dx1 n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k)(*strict*)
   prefer 2
   apply(rule_tac
      g="dx1"
      and n="k"
      and m="i1"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q h s)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s c)(*strict*)
   prefer 2
   apply(case_tac k)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s c)(*strict*)
    apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c02 c03 a w2 q s c)(*strict*)
    apply(simp add: epdaH_initial_configurations_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c nat)(*strict*)
   apply(rename_tac k)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c k)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c k)(*strict*)
    prefer 2
    apply(rule_tac
      d="dx1"
      and n="k"
      and m="Suc k"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c k)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c k)(*strict*)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c k)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e q s c k)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 q s c k e1a e2a c1)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a c1 wa)(*strict*)
   apply(case_tac c1)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a c1 wa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a wa epdaH_conf_historya)(*strict*)
   apply(erule_tac
      x="k"
      in allE)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a wa epdaH_conf_history)(*strict*)
   apply(case_tac "edge_event e2a")
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a wa epdaH_conf_history)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a wa epdaH_conf_history aa)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      xs="c"
      in rev_cases)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a wa epdaH_conf_history aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 c k e1a e2a wa epdaH_conf_history aa ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s c)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s)(*strict*)
   prefer 2
   apply(rule_tac
      n="i2"
      and P="\<lambda>n. n\<le>i2 \<and> prefix (w@[a]) (epdaH_conf_history (the(get_configuration(dx2 n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka)(*strict*)
   prefer 2
   apply(rule_tac
      g="dx2"
      and n="ka"
      and m="i2"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka ea c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e q s ka ea c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q h s)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s c)(*strict*)
   prefer 2
   apply(case_tac ka)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s c)(*strict*)
    apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c03 a w2 k e qa sa q s c)(*strict*)
    apply(simp add: epdaH_initial_configurations_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c nat)(*strict*)
   apply(rename_tac ka)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c ka)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c ka)(*strict*)
    prefer 2
    apply(rule_tac
      d="dx2"
      and n="ka"
      and m="Suc ka"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c ka)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c ka)(*strict*)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c ka)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ea q s c ka)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa q s c ka e1a e2a c1)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a c1 wa)(*strict*)
   apply(case_tac c1)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a c1 wa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a wa epdaH_conf_historya)(*strict*)
   apply(erule_tac
      x="ka"
      and P="\<lambda>X. X < Suc ka \<longrightarrow> (\<forall>c. w @ a # c \<noteq> epdaH_conf_history (the (case_option None (case_derivation_configuration (\<lambda>e. Some)) (dx2 X))))"
      in allE)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a wa epdaH_conf_historya)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_event e2a")
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a wa epdaH_conf_historya)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a wa epdaH_conf_historya aa)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      xs="c"
      in rev_cases)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a wa epdaH_conf_historya aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa c ka e1a e2a wa epdaH_conf_historya aa ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s c)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
  apply(subgoal_tac "epdaH.derivation_initial S dx1")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
   prefer 2
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
      prefer 2
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
  apply(case_tac k)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c02 c03 a w2 qa sa ka ea q s)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s nat)(*strict*)
  apply(case_tac ka)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c03 a w2 e qa sa q s nat)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 k e qa sa ka ea q s nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s nat nata)(*strict*)
  apply(rename_tac k1 k2)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s k1 k2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s k1 k2)(*strict*)
   prefer 2
   apply(rule_tac
      d="dx1"
      and n="k1"
      and m="Suc k1"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s k1 k2)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s k1 k2)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s k1 k2)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 e qa sa ea q s k1 k2)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa ea q s k1 k2 e1a e2a c1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa ea q s k1 k2 e1a e2a c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="dx2"
      and n="k2"
      and m="Suc k2"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa ea q s k1 k2 e1a e2a c1)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa ea q s k1 k2 e1a e2a c1)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa ea q s k1 k2 e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa ea q s k1 k2 e1a e2a c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa q s k1 k2 e1a e2a c1 e1b e2b c1a)(*strict*)
  apply(erule_tac
      x="k1"
      and P="\<lambda>x. x < Suc k1 \<longrightarrow> (\<forall>c. w @ a # c \<noteq> epdaH_conf_history (the (case_option None (case_derivation_configuration (\<lambda>e. Some)) (dx1 x))))"
      in allE)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa q s k1 k2 e1a e2a c1 e1b e2b c1a)(*strict*)
  apply(erule_tac
      x="k2"
      in allE)
  apply(clarsimp)
  apply(case_tac c1a)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa q s k1 k2 e1a e2a c1 e1b e2b c1a epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac c1)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa q s k1 k2 e1a e2a c1 e1b e2b c1a epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 s2 q3 s3 c01 c02 c03 a w2 qa sa q s k1 k2 e1a e2a e1b e2b epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1 q2 h2 s2)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 a w2 qa sa q s k1 k2 e1a e2a e1b e2b q1 h1 s1 q2 h2 s2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 a w2 k1 k2 e1a e2a e1b e2b h1 h2 wa waa)(*strict*)
  apply(case_tac "edge_event e2b")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 a w2 k1 k2 e1a e2a e1b e2b h1 h2 wa waa)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 a w2 k1 k2 e1a e2a e1b e2b h1 h2 wa waa aa)(*strict*)
  apply(case_tac "edge_event e2a")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 a w2 k1 k2 e1a e2a e1b e2b h1 h2 wa waa aa)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 a w2 k1 k2 e1a e2a e1b e2b h1 h2 wa waa aa ab)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e2a e1b e2b wa waa aa)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e2a e1b e2b wa waa aa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs1 re1 po1 pu1 qt1)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e2a e1b e2b wa waa aa qs1 re1 po1 pu1 qt1)(*strict*)
  apply(case_tac e2b)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e2a e1b e2b wa waa aa qs1 re1 po1 pu1 qt1 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs2 re2 po2 pu2 qt2)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e2a e1b e2b wa waa aa qs1 re1 po1 pu1 qt1 qs2 re2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and ?d1.0="dx1"
      and ?d2.0="dx2"
      and ?n1.0="k1"
      and ?n2.0="k2"
      in epdaH_coincide_on_stable_configurations)
          apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def)
         apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
         apply(force)
        apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
        apply(force)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
     apply(clarsimp)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
     apply(rule_tac
      ?c2.0="\<lparr>epdaH_conf_state = qt1, epdaH_conf_history = w @ [aa], epdaH_conf_stack = pu1 @ wa\<rparr>"
      and G="S"
      and d="dx1"
      and n="k1"
      and ?e2.0="\<lparr>edge_src = qs1, edge_event = Some aa, edge_pop = po1, edge_push = pu1, edge_trg = qt1\<rparr>"
      and ?e1.0="e"
      in DPDA_conflicting_edges)
           apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
           apply(simp add: F_DPDA_RCS__SpecInput_def)
          apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
          apply(force)
         apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
         apply(force)
        apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
        apply(force)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
       apply(simp add: epdaH_step_relation_def)
       apply(clarsimp)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa po1 pu1 qt1 qs2 po2 pu2 qt2 e c' wb)(*strict*)
       apply(simp add: option_to_list_def)
       apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
       apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
        apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa po1 pu1 qt1 qs2 po2 pu2 qt2 e c' wb)(*strict*)
        apply(clarsimp)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa po1 pu1 qt1 qs2 po2 pu2 qt2 e c' wb)(*strict*)
       apply(clarsimp)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
       apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
      apply(force)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
    apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
    apply(rule_tac
      ?c2.0="\<lparr>epdaH_conf_state = qt2, epdaH_conf_history = w @ [aa], epdaH_conf_stack = pu2 @ waa\<rparr>"
      and G="S"
      and d="dx2"
      and n="k2"
      and ?e2.0="\<lparr>edge_src = qs2, edge_event = Some aa, edge_pop = po2, edge_push = pu2, edge_trg = qt2\<rparr>"
      and ?e1.0="e"
      in DPDA_conflicting_edges)
          apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def)
         apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
         apply(force)
        apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
        apply(force)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
       apply(force)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
      apply(simp add: epdaH_step_relation_def)
      apply(clarsimp)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 e c' wb)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2 e c')(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c02 c03 w2 k1 k2 e1a e1b wa waa aa qs1 po1 pu1 qt1 qs2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2)(*strict*)
  apply(subgoal_tac "executing_edge_from_auxiliary_to_main_state S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2)(*strict*)
  apply(simp add: executing_edge_from_auxiliary_to_main_state_def)
  apply(erule_tac
      x="\<lparr>edge_src = qs1, edge_event = Some aa, edge_pop = po2, edge_push = pu2, edge_trg = qt2\<rparr>"
      in allE)
  apply(clarsimp)
  apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
  apply(subgoal_tac "\<exists>q1 X. \<exists>f\<in> {cons_state_or_state_new, cons_state_or_state_old}. qs1 = f(cons_state_and_stack q1 X)")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__is_auxiliary_def)
   apply(case_tac qs1)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q)(*strict*)
    apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa po1 pu1 qt1 po2 pu2 qt2 q)(*strict*)
    apply(case_tac q)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa po1 pu1 qt1 po2 pu2 qt2 q a b)(*strict*)
     apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa po1 pu1 qt1 po2 pu2 qt2 q a)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q)(*strict*)
   apply(case_tac qs1)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q qa)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa po1 pu1 qt1 po2 pu2 qt2 q)(*strict*)
   apply(case_tac q)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa po1 pu1 qt1 po2 pu2 qt2 q a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa po1 pu1 qt1 po2 pu2 qt2 q a)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
  apply(subgoal_tac "\<exists>x. po1 = [x]")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      A="epda_delta G"
      and x="\<lparr>edge_src = qs1, edge_event = Some aa, edge_pop = po1, edge_push = pu1, edge_trg = qt1\<rparr>"
      and P="\<lambda>e. length (edge_pop e) = Suc 0"
      in ballE)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
   apply(case_tac po1)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
  apply(subgoal_tac "\<exists>x. po2 = [x]")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 pu1 qt1 po2 pu2 qt2 q1 X x)(*strict*)
   apply(erule_tac
      x="\<lparr>edge_src = qs1, edge_event = Some aa, edge_pop = po2, edge_push = pu2, edge_trg = qt2\<rparr>"
      and A="epda_delta S"
      in ballE)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 pu1 qt1 po2 pu2 qt2 q1 X x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 pu1 qt1 po2 pu2 qt2 q1 X x)(*strict*)
   apply(case_tac po2)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 pu1 qt1 po2 pu2 qt2 q1 X x)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 pu1 qt1 po2 pu2 qt2 q1 X x a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa waa aa qs1 po1 pu1 qt1 po2 pu2 qt2 q1 X)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
  apply(subgoal_tac "X = x")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
   prefer 2
   apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
   apply(simp add: corresponds_to_top_stack_def)
   apply(erule_tac
      x="dx1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="k2"
      and P="\<lambda>k2. \<forall>c. get_configuration (dx1 k2) = Some c \<longrightarrow> F_DPDA_EUML__is_auxiliary ((epdaH_conf_state c)) \<longrightarrow> (\<forall>X. F_DPDA_EUML__get_stack ((epdaH_conf_state c)) = Some X \<longrightarrow> (\<exists>w. epdaH_conf_stack c = X # w))"
      in allE)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(erule impE)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
   apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
   apply(case_tac qs1)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x q)(*strict*)
    apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x q)(*strict*)
   apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 X x)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 x)(*strict*)
  apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 x)(*strict*)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(erule_tac
      x="dx1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="k2"
      and P="\<lambda>k2. \<forall>c. get_configuration (dx1 k2) = Some c \<longrightarrow> (\<exists>d'. epdaH.derivation_initial P d' \<and> (\<exists>m. get_configuration (d' m) = Some \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state c))), epdaH_conf_history = epdaH_conf_history c, epdaH_conf_stack = [epda_box P]\<rparr>))"
      in allE)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 x)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 x d' m)(*strict*)
  apply(case_tac q1)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 q1 x d' m a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m a b)(*strict*)
  apply(rename_tac qa qb)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa qb)(*strict*)
  apply(subgoal_tac "sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1)) = qb")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa qb)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa qb)(*strict*)
    apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__get_state_def sel_tuple2_2_def)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa qb)(*strict*)
   apply(simp add: F_DPDA_EUML__get_state_def F_DPDA_OTS__get_state_def sel_tuple2_2_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa qb)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa)(*strict*)
  apply(case_tac "d' m")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option)(*strict*)
   prefer 2
   apply(rule_tac
      d="dx3"
      and n="length w"
      and m="Suc(length w)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 e3 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
  apply(subgoal_tac "m=length w")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
    prefer 2
    apply(rule_tac
      d="d'"
      and G="P"
      and n="m"
      in DFA_one_symbol_per_step)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' m qa option e1b e2a c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
  apply(subgoal_tac "(\<forall>i\<le>length w. dx3 i = d' i)")
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
    prefer 2
    apply(rule_tac
      G="P"
      and ?d1.0="dx3"
      and ?d2.0="d'"
      and ?n1.0="length w"
      and ?n2.0="length w"
      in epdaH_coincide_on_stable_configurations)
           apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
           apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
          apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
          apply(force)
         apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
         apply(force)
        apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
        apply(clarsimp)
        apply(simp add: get_configuration_def)
       apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
      apply(clarsimp)
      apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1 e c')(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
      apply(force)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
     apply(clarsimp)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1 e c')(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
     apply(force)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1 waa)(*strict*)
    apply(case_tac c1)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1 waa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a waa epdaH_conf_history)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
    apply(clarsimp)
    apply(erule_tac
      x="e2a"
      in ballE)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a waa epdaH_conf_history)(*strict*)
     apply(clarsimp)
     apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a waa epdaH_conf_history y)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a waa epdaH_conf_history)(*strict*)
    apply(force)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
   apply(force)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa option e1b e2a c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a q3 s3 c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b e2a)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b e2a waa)(*strict*)
  apply(case_tac "e2a")
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b e2a waa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b e2a waa qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa re po pu qt)(*strict*)
  apply(case_tac re)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa re po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac v dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa re po pu qt a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(subgoal_tac "qs1 \<notin> F_DPDA_NCS S P \<Sigma>UC")
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   prefer 2
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(subgoal_tac "\<lparr>epdaH_conf_state = qs1, epdaH_conf_history = w, epdaH_conf_stack = x # wa\<rparr> \<in> epdaH_configurations S")
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   prefer 2
   apply(rule_tac
      d="dx2"
      and i="k2"
      in epdaH.belongs_configurations)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(rule epdaH.derivation_initial_belongs)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(subgoal_tac "qs1 \<in> epda_states S \<longrightarrow> (\<forall>f pS pP X. qs1 = f (cons_state_and_stack (cons_tuple2 pS pP) X) \<longrightarrow> f \<noteq> cons_state_or_state_new \<and> f \<noteq> cons_state_or_state_old \<or> f (cons_state_and_stack (cons_tuple2 pS pP) X) \<in> epda_nonstable_states (epda_delta S) \<or> (\<forall>u\<in> \<Sigma>UC. \<forall>eP\<in> epda_delta P. edge_event eP = Some u \<longrightarrow> edge_src eP = pP \<longrightarrow> (\<exists>eS\<in> epda_delta S. edge_event eS = Some u \<and> edge_src eS = f (cons_state_and_stack (cons_tuple2 pS pP) X) \<and> edge_pop eS = [X])))")
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_NCS_def)
   apply(clarsimp)
   apply(erule_tac x="f" in allE)
   apply(erule_tac x="pS" in allE)
   apply(erule_tac x="edge_src eP" in allE)
   apply(erule_tac x="X" in allE)
   apply(clarsimp)
   apply(erule disjE)
    apply(force)
   apply(erule disjE)
    apply(force)
   apply(erule disjE)
    apply(force)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(simp add: epdaH_configurations_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(subgoal_tac "\<exists>f\<in> {cons_state_or_state_new, cons_state_or_state_old}. (\<exists>eS\<in> epda_delta S. qs1=f (cons_state_and_stack (cons_tuple2 qa (sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1)))) x) \<and> edge_event eS = Some a \<and> edge_src eS = f (cons_state_and_stack ((cons_tuple2 qa (sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1))))) x ) \<and> edge_pop eS = [x])")
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(rule_tac
      x="cons_state_or_state_new"
      in bexI)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
     apply(erule_tac
      x="cons_state_or_state_new"
      in allE)
     apply(erule_tac
      x="qa"
      in allE)
     apply(erule_tac
      x="sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1))"
      in allE)
     apply(erule_tac
      x="x"
      in allE)
     apply(clarsimp)
     apply(erule disjE)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(subgoal_tac "False")
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
       apply(force)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(subgoal_tac "always_applicable_for_auxiliary_states S F_DPDA_EUML__is_auxiliary")
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
       prefer 2
       apply(simp add: F_DPDA_RCS__SpecInput_def)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(simp add: always_applicable_for_auxiliary_states_def always_applicable_def)
      apply(erule_tac
      x="dx1"
      in allE)
      apply(clarsimp)
      apply(erule_tac
      x="e1a"
      in allE)
      apply(erule_tac
      x="\<lparr>epdaH_conf_state = qs1, epdaH_conf_history = w, epdaH_conf_stack = x # wa\<rparr>"
      in allE)
      apply(erule impE)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
       apply(rule_tac
      x="k2"
      in exI)
       apply(force)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(erule impE)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
       apply(clarsimp)
       apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(simp add: epda_nonstable_states_def)
      apply(erule bexE)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
      apply(erule_tac
      x="e"
      in ballE)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
      apply(erule impE)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
       apply(force)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
      apply(erule exE)+
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
      apply(rule_tac
      G="S"
      and d="dx1"
      and n="k2"
      and ?e1.0="e"
      and ?e2.0="\<lparr>edge_src = qs1, edge_event = Some aa, edge_pop = [x], edge_push = pu2, edge_trg = qt2\<rparr>"
      and ?c2.0="\<lparr>epdaH_conf_state = qt2, epdaH_conf_history = w @ [aa], epdaH_conf_stack = pu2 @ wa\<rparr>"
      in DPDA_conflicting_edges)
            apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
            apply(simp add: F_DPDA_RCS__SpecInput_def)
           apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
           apply(force)
          apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
          apply(force)
         apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
       prefer 2
       apply(simp add: epdaH_step_relation_def option_to_list_def)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
      apply(force)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
     apply(erule_tac
      x="a"
      in ballE)
      prefer 2
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(force)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
     apply(erule_tac
      x="\<lparr>edge_src = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1)), edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
      prefer 2
      apply(force)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
     apply(erule impE)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(force)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
     apply(erule impE)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
      apply(force)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
     apply(force)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(rule_tac
      x="cons_state_or_state_old"
      in bexI)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(erule_tac
      x="cons_state_or_state_old"
      in allE)
    apply(erule_tac
      x="qa"
      in allE)
    apply(erule_tac
      x="sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1))"
      in allE)
  apply(erule_tac
    x="x"
    in allE)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(subgoal_tac "always_applicable_for_auxiliary_states S F_DPDA_EUML__is_auxiliary")
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(simp add: always_applicable_for_auxiliary_states_def always_applicable_def)
   apply(erule_tac
    x="dx1"
    in allE)
   apply(clarsimp)
   apply(erule_tac
    x="e1a"
    in allE)
   apply(erule_tac
    x="\<lparr>epdaH_conf_state = qs1, epdaH_conf_history = w, epdaH_conf_stack = x # wa\<rparr>"
    in allE)
   apply(erule impE)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(rule_tac
    x="k2"
    in exI)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(erule impE)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(simp add: epda_nonstable_states_def)
   apply(erule bexE)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
   apply(erule_tac
    x="e"
    in ballE)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
   apply(erule impE)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e)(*strict*)
   apply(erule exE)+
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
   apply(rule_tac
    G="S"
    and d="dx1"
    and n="k2"
    and ?e1.0="e"
    and ?e2.0="\<lparr>edge_src = qs1, edge_event = Some aa, edge_pop = [x], edge_push = pu2, edge_trg = qt2\<rparr>"
    and ?c2.0="\<lparr>epdaH_conf_state = qt2, epdaH_conf_history = w @ [aa], epdaH_conf_stack = pu2 @ wa\<rparr>"
    in DPDA_conflicting_edges)
         apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
         apply(simp add: F_DPDA_RCS__SpecInput_def)
        apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
        apply(force)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
       apply(force)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
    prefer 2
    apply(simp add: epdaH_step_relation_def option_to_list_def)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a e xa)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(erule_tac
    x="a"
    in ballE)
   prefer 2
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(erule_tac
    x="\<lparr>edge_src = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state qs1)), edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
    in ballE)
   prefer 2
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a)(*strict*)
  apply(erule bexE)+
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule_tac
    x="derivation_append dx2 (der2 \<lparr>epdaH_conf_state = qs1, epdaH_conf_history = w, epdaH_conf_stack = x # wa\<rparr> eS \<lparr>epdaH_conf_state = edge_trg eS, epdaH_conf_history = w@[a], epdaH_conf_stack = (edge_push eS) @ wa\<rparr>) k2"
    in exI)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule epdaH.derivation_append_preserves_derivation_initial)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule epdaH.derivation_append_preserves_derivation)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule epdaH.der2_is_derivation)
  apply(simp add: epdaH_step_relation_def option_to_list_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule conjI)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(rule_tac
    x="Suc k2"
    in exI)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(simp add: der2_def derivation_append_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa qs1 pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 q1a s1a q2a s2a c01 c03 w2 k2 e1a wa aa pu1 qt1 pu2 qt2 x d' qa e1b waa po pu qt a f eS)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  done

lemma F_DPDA_RCS__Enforce_Marked_Controllable_Subset__marked_language_part1: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) = Some G 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> x \<in> epdaH.marked_language S 
  \<Longrightarrow> controllable_sublanguage (prefix_closure {x}) {w. \<exists>v\<in> \<Sigma>UC. w = [v]} (epdaH.unmarked_language P) (epdaH.unmarked_language S) 
  \<Longrightarrow> x \<in> epdaH.marked_language G"
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(thin_tac "epdaH.derivation S d")
  apply(thin_tac "epdaH_marking_condition S d")
  apply(simp add: epdaH_marked_effect_def epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s)(*strict*)
  apply(thin_tac "\<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_string_state \<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr> = epdaH_string_state c'")
  apply(rename_tac d i e q h s)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(subgoal_tac "\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr> \<in> epdaH_configurations G")
    apply(rename_tac d i e q h s)(*strict*)
    prefer 2
    apply(rule_tac
      d="derivation_take d i"
      and i="i"
      in epdaH.belongs_configurations)
     apply(rename_tac d i e q h s)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i e q h s)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d i e q h s)(*strict*)
     apply(force)
    apply(rename_tac d i e q h s)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d i e q h s)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac d i e q h s)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="e"
      in exI)
    apply(rule_tac
      x="\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d i e q h s)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac d i e q h s)(*strict*)
    apply(simp add: epdaH_configurations_def)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
     apply(rename_tac d i e q h s)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e q h s)(*strict*)
    apply(clarsimp)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(simp add: derivation_take_def)
   apply(rename_tac d i e q h s)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e q h s)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
   apply(rename_tac d i e q h s)(*strict*)
   apply(simp add: epdaH_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac d i e q s ia ea c)(*strict*)
   apply(rule_tac
      x="ia"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH_marking_configurations_def)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "\<forall>k\<le>i. epdaH_conf_state (the(get_configuration(d k))) \<in> epda_states G")
   apply(rename_tac d i e q h s)(*strict*)
   apply(simp add: epdaH.derivation_initial_def derivation_take_def)
   apply(rule context_conjI)
    apply(rename_tac d i e q h s)(*strict*)
    prefer 2
    apply(case_tac "d 0")
     apply(rename_tac d i e q h s)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e q h s a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac d i e q h s a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i e q h s b)(*strict*)
    apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def)
    apply(clarsimp)
    apply(rename_tac d i e q h s)(*strict*)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
     apply(rename_tac d i e q h s)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e q h s)(*strict*)
    apply(clarsimp)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(rename_tac d i e q h s)(*strict*)
   apply(simp (no_asm) add: epdaH.derivation_def)
   apply(clarsimp)
   apply(rename_tac d i e q h s ia)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e q h s ia)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(case_tac ia)
     apply(rename_tac d i e q h s ia)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e q h s ia nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q h s ia)(*strict*)
   apply(clarsimp)
   apply(case_tac ia)
    apply(rename_tac d i e q h s ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i e q h s)(*strict*)
    apply(case_tac "d 0")
     apply(rename_tac d i e q h s)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e q h s a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac d i e q h s a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q h s ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h s nat)(*strict*)
   apply(case_tac "d(Suc nat)")
    apply(rename_tac d i e q h s nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q h s nat a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q h s nat a)(*strict*)
    prefer 2
    apply(rule_tac
      G="S"
      and d="d"
      and n="nat"
      and m="Suc nat"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d i e q h s nat a)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d i e q h s nat a)(*strict*)
     apply(force)
    apply(rename_tac d i e q h s nat a)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h s nat e1 e2 c1 c2)(*strict*)
   apply(subgoal_tac "e2 \<in> epda_delta G")
    apply(rename_tac d i e q h s nat e1 e2 c1 c2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac d i e q h s nat e1 e2 c1 c2)(*strict*)
   apply(simp add: epdaH_configurations_def)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac d i e q h s nat e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q h s nat e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d i e q h s nat e1 e2 c1 c2 w)(*strict*)
   apply(erule_tac x="nat" in allE')
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
  apply(rename_tac d i e q h s)(*strict*)
  apply(rule universal_by_not_exists_contra)
  apply(rename_tac d i e q h s k)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s k)(*strict*)
   prefer 2
   apply(rule_tac
      g="d"
      and n="k"
      and m="i"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac d i e q h s k)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d i e q h s k)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s k)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s k)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s k ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e q h s k ea c epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
  apply(subgoal_tac "q \<notin> epda_states G")
   apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
  apply(thin_tac "epdaH_conf_state (the (get_configuration (Some (pair ea c)))) \<notin> epda_states G")
  apply(subgoal_tac "q \<in> epda_states S")
   apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
   prefer 2
   apply(subgoal_tac "SSX \<in> epdaH_configurations S" for SSX)
    apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and i="k"
      in epdaH.belongs_configurations)
     apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
     apply(force)
    apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
    apply(force)
   apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
   apply(simp add: epdaH_configurations_def)
  apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
  apply(case_tac "F_DPDA_EUML__is_auxiliary q")
   apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
   prefer 2
   apply(simp add: epdaH_configurations_def)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
   apply(simp add: F_DPDA_NCS_def)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(clarsimp)
   apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
   apply(erule disjE)
    apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
   apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
  apply(rename_tac d i e qa ha sa k ea c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
  apply(subgoal_tac "q \<in> F_DPDA_NCS S P \<Sigma>UC")
   apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
   prefer 2
   apply(simp add: epdaH_configurations_def)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
  apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
  apply(subgoal_tac "\<exists>f pS pP X. q = f (cons_state_and_stack (cons_tuple2 pS pP) X) \<and> (f = cons_state_or_state_new \<or> f = cons_state_or_state_old) \<and> q \<notin> epda_nonstable_states (epda_delta S) \<and> (\<exists>u\<in> \<Sigma>UC. \<exists>eP\<in> epda_delta P. edge_src eP = pP \<and> edge_event eP = Some u \<and> (\<forall>eS\<in> epda_delta S. edge_event eS = Some u \<longrightarrow> edge_src eS = q \<longrightarrow> edge_pop eS \<noteq> [X]))")
   apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_NCS_def)
   apply(erule exE)+
   apply(rule_tac x="f" in exI)
   apply(rule_tac x="pS" in exI)
   apply(rule_tac x="pP" in exI)
   apply(rule_tac x="X" in exI)
   apply(clarsimp)
   apply(rule_tac x="u" in bexI)
    prefer 2
    apply(force)
   apply(rule_tac x="eP" in bexI)
    prefer 2
    apply(force)
   apply(force)
  apply(rename_tac d i e qa ha sa k ea q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
  apply(thin_tac "F_DPDA_EUML__is_auxiliary ((f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X)))")
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and G="S"
      and n="k"
      and m="i-k"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
    apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
     apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
     apply(force)
    apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
    apply(force)
   apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e qa ha sa k ea h s f pS X u eP)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
  apply(simp add: controllable_sublanguage_def)
  apply(erule_tac
      x="h"
      in ballE)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   prefer 2
   apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
  apply(thin_tac "hb \<in> epda_effects S")
  apply(simp add: controllable_word_def)
  apply(erule_tac
      x="[u]"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   apply(rule_tac
      x="u"
      in bexI)
    apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
    apply(force)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   apply(force)
  apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
  apply(subgoal_tac "\<exists>w. s = X#w")
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   prefer 2
   apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
    apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   apply(simp add: corresponds_to_top_stack_def)
   apply(erule_tac
      x="d"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="k"
      and P="\<lambda>k. \<forall>c. get_configuration (d k) = Some c \<longrightarrow> F_DPDA_EUML__is_auxiliary ((epdaH_conf_state c)) \<longrightarrow> (\<forall>X. F_DPDA_EUML__get_stack ((epdaH_conf_state c)) = Some X \<longrightarrow> (\<exists>w. epdaH_conf_stack c = X # w))"
      in allE)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(erule_tac
      P="F_DPDA_EUML__is_auxiliary ((f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X)))"
      in impE)
    apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
    apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
    apply(erule disjE)
     apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   apply(simp add: F_DPDA_EUML__get_stack_def F_DPDA_OTS__get_stack_def F_DPDA_EUML__get_state_def)
   apply(erule disjE)
    apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h s f pS X u eP hb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w)(*strict*)
  apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w)(*strict*)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="k"
      and P="\<lambda>k. \<forall>c. get_configuration (d k) = Some c \<longrightarrow> (\<exists>d'. epdaH.derivation_initial P d' \<and> (\<exists>m. get_configuration (d' m) = Some \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state c))), epdaH_conf_history = epdaH_conf_history c, epdaH_conf_stack = [epda_box P]\<rparr>))"
      in allE)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m)(*strict*)
  apply(case_tac "d' m")
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m a option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
  apply(subgoal_tac "sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (f (cons_state_and_stack (cons_tuple2 pS (edge_src eP)) X)))) = edge_src eP")
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
   prefer 2
   apply(simp add: sel_tuple2_2_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_state_def)
   apply(erule disjE)
    apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
   apply(simp add: epdaH.unmarked_language_def)
   apply(rule_tac
      x="derivation_append d' (der2 \<lparr>epdaH_conf_state = edge_src eP, epdaH_conf_history = h, epdaH_conf_stack = [epda_box P]\<rparr> eP \<lparr>epdaH_conf_state = edge_trg eP, epdaH_conf_history = h@[u], epdaH_conf_stack = [epda_box P]\<rparr>) m"
      in exI)
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_dfa_def valid_pda_def)
     apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
     apply(force)
    apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: option_to_list_def)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_dfa_def valid_pda_def)
    apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def derivation_append_def)
   apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_unmarked_effect_def)
   apply(rule_tac
      x="Suc m"
      in exI)
   apply(simp add: der2_def derivation_append_def)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option)(*strict*)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option da)(*strict*)
  apply(thin_tac "epdaH.derivation S da")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option da ia eb c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e qa sa k ea h f pS X u eP hb w d' m option da ia eb c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s)(*strict*)
   prefer 2
   apply(rule_tac
      n="ia"
      and P="\<lambda>n. n\<le>ia \<and> ha@[u]= (epdaH_conf_history (the(get_configuration(da n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s ka)(*strict*)
  apply(case_tac ka)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s ka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "da 0")
    apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s b)(*strict*)
   apply(simp add: epdaH_initial_configurations_def get_configuration_def)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s ka nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n)(*strict*)
   prefer 2
   apply(rule_tac
      d="da"
      and n="n"
      and m="ia"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n)(*strict*)
    apply(force)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(erule_tac
      x="n"
      and P="\<lambda>X. X < Suc n \<longrightarrow> epdaH_conf_history c2 \<noteq> epdaH_conf_history (the (case da X of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c))"
      in allE)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(case_tac e2)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2 edge_srca edge_eventa edge_popa edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2 qs re po pu qt)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(case_tac c1)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2 qs re po pu qt epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2 qs re po pu qt q1 h1 s1)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2 qs re po pu qt q1 h1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 e2 c1 c2 qs re po pu qt q1 h1 s1 q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 qs re po pu qt h1 wa)(*strict*)
  apply(case_tac re)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 qs re po pu qt h1 wa)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 qs re po pu qt h1 wa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
   apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d i e qa sa k ea ha f pS X u eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
  apply(subgoal_tac "\<exists>x. po = [x]")
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = Some a, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      and A="epda_delta S"
      in ballE)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
   apply(case_tac po)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs po pu qt h1 wa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and ?d1.0="d"
      and ?d2.0="da"
      and ?n1.0="k"
      and ?n2.0="n"
      in epdaH_coincide_on_stable_configurations)
          apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def)
         apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
         apply(force)
        apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
        apply(force)
       apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c')(*strict*)
   apply(simp add: F_DPDA_NCS_def)
   apply(clarsimp)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
   apply(subgoal_tac "f=fa \<and> X = Xa \<and> pS = pSa \<and> (edge_src eP) = (edge_src ePa)")
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
    prefer 2
    apply(erule disjE)+
      apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
    apply(erule disjE)+
     apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e qa sa k ea eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa)(*strict*)
   apply(simp add: epdaH_step_relation_def epda_nonstable_states_def)
   apply(clarsimp)
   apply(rename_tac d i e qa sa k ea eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa wb)(*strict*)
   apply(erule_tac
      x="ec"
      and A="epda_delta S"
      and P="\<lambda>e. edge_src e = edge_src ec \<longrightarrow> (\<exists>y. edge_event e = Some y)"
      in ballE)
    apply(rename_tac d i e qa sa k ea eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa wb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i e qa sa k ea eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c' fa pSa Xa u ePa wb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 qs pu qt h1 wa a x ec c')(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pu qt h1 wa a x ec c' wb)(*strict*)
  apply(case_tac ec)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pu qt h1 wa a x ec c' wb edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x ec c' wb qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu)(*strict*)
  apply(subgoal_tac "\<exists>x. po = [x]")
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state c'\<rparr>"
      and P="\<lambda>x. length (edge_pop x) = Suc 0"
      and A="epda_delta S"
      in ballE)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu)(*strict*)
   apply(case_tac po)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 wa a x c' wb qs po pu)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
  apply(rule_tac
      G="S"
      and d="da"
      and n="n"
      and ?e1.0="\<lparr>edge_src = qs, edge_event = None, edge_pop = [xa], edge_push = pu, edge_trg = epdaH_conf_state c'\<rparr>"
      and ?e2.0="\<lparr>edge_src = qs, edge_event = Some a, edge_pop = [xa], edge_push = pua, edge_trg = qta\<rparr>"
      and ?c1.0="c'"
      and ?c2.0="\<lparr>epdaH_conf_state = qta, epdaH_conf_history = h1 @ [a], epdaH_conf_stack = pua @ wb\<rparr>"
      in DPDA_conflicting_edges)
        apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
        apply(simp add: F_DPDA_RCS__SpecInput_def )
       apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
       apply(force)
      apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
      apply(force)
     apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
     apply(simp add: epdaH_step_relation_def)
    apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
    apply(simp add: epdaH_step_relation_def option_to_list_def)
   apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e qa sa k ea f pS X eP hb w d' m option da ia eb q s n e1 pua qta h1 a c' wb qs pu xa)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_RCS__Enforce_Marked_Controllable_Subset__marked_language_part2: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) = Some G 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> w' \<in> epdaH.marked_language G 
  \<Longrightarrow> w' \<in> epdaH.marked_language S 
  \<Longrightarrow> v \<in> \<Sigma>UC 
  \<Longrightarrow> w' @ [v] \<in> epdaH.unmarked_language P 
  \<Longrightarrow> w' @ [v] \<in> epdaH.unmarked_language S"
  apply(simp add: epdaH.marked_language_def epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d da db)(*strict*)
  apply(thin_tac "epdaH.derivation G d")
  apply(thin_tac "epdaH.derivation P db")
  apply(thin_tac "epdaH.derivation S da")
  apply(thin_tac "epdaH_marking_condition G d")
  apply(thin_tac "epdaH_marking_condition S da")
  apply(simp add: epdaH_marked_effect_def epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d da db i ia ib e ea eb c ca cb)(*strict*)
  apply(case_tac c)
  apply(rename_tac d da db i ia ib e ea eb c ca cb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac ca)
  apply(rename_tac d da db i ia ib e ea eb c ca cb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(case_tac cb)
  apply(rename_tac d da db i ia ib e ea eb c ca cb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 c1 c2 c3 q1 h1 s1 q2 h s2 q3 h3 s3)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 c1 c2 c3 q1 h1 s1 q2 h s2 q3 h3 s3)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3)(*strict*)
  apply(case_tac "dx1 0")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a)(*strict*)
  apply(case_tac "dx2 0")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa)(*strict*)
  apply(case_tac "dx3 0")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab)(*strict*)
  apply(case_tac a)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab option b optiona ba)(*strict*)
  apply(case_tac ab)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 a aa ab option b optiona ba optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(case_tac option)
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(case_tac optionb)
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb a)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 option b optiona ba optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(subgoal_tac "b \<in> epdaH_initial_configurations G")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(subgoal_tac "ba \<in> epdaH_initial_configurations S")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(subgoal_tac "bb \<in> epdaH_initial_configurations P")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 b ba bb)(*strict*)
  apply(rename_tac c01 c02 c03)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(subgoal_tac "i3=length(h@[v])")
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
    prefer 2
    apply(rule_tac
      d="dx3"
      and G="P"
      and n="i3"
      in DFA_one_symbol_per_step)
      apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def)
     apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
     apply(force)
    apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i1 i2 i3 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(thin_tac "\<forall>j e' c'. i1 < j \<and> dx1 j = Some (pair e' c') \<longrightarrow> epdaH_string_state \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> = epdaH_string_state c'")
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(thin_tac "\<forall>j e' c'. i2 < j \<and> dx2 j = Some (pair e' c') \<longrightarrow> epdaH_string_state \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr> = epdaH_string_state c'")
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(subgoal_tac "q1 \<in> epda_marking G")
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   prefer 2
   apply(simp add: epdaH_marking_configurations_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(subgoal_tac "q2 \<in> epda_marking S")
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   prefer 2
   apply(simp add: epdaH_marking_configurations_def)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(thin_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_marking_configurations G")
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(thin_tac "\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr> \<in> epdaH_marking_configurations S")
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   prefer 2
   apply(rule_tac
      G="S"
      and ?d1.0="dx1"
      and ?d2.0="dx2"
      and ?n1.0="i1"
      and ?n2.0="i2"
      in epdaH_coincide_on_stable_configurations)
          apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def)
         apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
         apply(rule epda_sub_preserves_derivation_initial)
            apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
            prefer 2
            apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
           apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
           prefer 3
           apply(force)
          apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
         apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
         apply(simp add: epda_sub_def)
         apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
         apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
          apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
          apply(clarsimp)
         apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
         apply(clarsimp)
         apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
         apply(force)
        apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
        apply(force)
       apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
     apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
     apply(subgoal_tac "only_executing_edges_from_marking_states S")
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
      prefer 2
      apply(simp add: F_DPDA_RCS__SpecInput_def)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
     apply(simp add: only_executing_edges_from_marking_states_def)
     apply(erule_tac
      x="e"
      in ballE)
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
      prefer 2
      apply(simp add: epdaH_step_relation_def)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q2 h s2 q3 s3 c01 c02 c03 e c' w)(*strict*)
     apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
     apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
      apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q2 h s2 q3 s3 c01 c02 c03 e c' w)(*strict*)
      apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q2 h s2 q3 s3 c01 c02 c03 e c' w)(*strict*)
     apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
     apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(clarsimp)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
    apply(subgoal_tac "only_executing_edges_from_marking_states S")
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
     prefer 2
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
    apply(simp add: only_executing_edges_from_marking_states_def)
    apply(erule_tac
      x="e"
      in ballE)
     apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
     prefer 2
     apply(simp add: epdaH_step_relation_def)
    apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03 e c')(*strict*)
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
   apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i1 i2 e1 e2 e3 q1 s1 q2 h s2 q3 s3 c01 c02 c03)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 e3 q1 s1 h q3 s3 c01 c03)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dx1 dx2 dx3 i2 e1 e3 q1 s1 h q3 s3 c01 c03)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and d="dx3"
      and n="length h"
      and m="Suc (length h)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac dx1 dx2 dx3 i2 e1 e3 q1 s1 h q3 s3 c01 c03)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 e3 q1 s1 h q3 s3 c01 c03)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i2 e1 e3 q1 s1 h q3 s3 c01 c03)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 e3 q1 s1 h q3 s3 c01 c03)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 h q3 s3 c01 c03 e1a e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 h c01 c03 e1a e2 c1 w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 h c01 c03 e1a e2 c1 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a e2 c1 w q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a e2 w h)(*strict*)
  apply(case_tac e2)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a e2 w h edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a e2 w h qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs re po pu qt)(*strict*)
  apply(case_tac re)
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs re po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs po pu qt)(*strict*)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
    apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs po pu qt)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs po pu qt)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs re po pu qt a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 ha c01 c03 e1a w h qs po pu qt a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
  apply(subgoal_tac "q1 \<notin> F_DPDA_NCS S P \<Sigma>UC")
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
   prefer 2
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
    apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
  apply(subgoal_tac "q1 \<in> epda_states S")
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
   prefer 2
   apply(subgoal_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>\<in> epdaH_configurations S")
    apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
    prefer 2
    apply(rule_tac
      d="dx2"
      in epdaH.belongs_configurations)
     apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
     apply(force)
    apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
   apply(simp add: epdaH_configurations_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
  apply(subgoal_tac "\<exists>f qx1 qx2 X. f \<in> {cons_state_or_state_old, cons_state_or_state_new} \<and> q1 = f (cons_state_and_stack (cons_tuple2 qx1 qx2) X)")
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
   prefer 2
   apply(case_tac q1)
    apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt q)(*strict*)
    apply(clarsimp)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt q)(*strict*)
    apply(rule_tac
      x="cons_state_or_state_old"
      in exI)
    apply(clarsimp)
    apply(case_tac q)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt q a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a b)(*strict*)
     apply(case_tac a)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a b aa ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt q a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    apply(subgoal_tac "main_states_can_be_left_with_empty_step S F_DPDA_EUML__is_main")
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
     prefer 2
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    apply(simp add: main_states_can_be_left_with_empty_step_def)
    apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in ballE)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
     apply(erule impE)
      apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
      apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
     apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
     apply(subgoal_tac "only_executing_edges_from_marking_states S")
      apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
      prefer 2
      apply(simp add: F_DPDA_RCS__SpecInput_def)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
     apply(simp add: only_executing_edges_from_marking_states_def)
     apply(erule_tac
      x="e"
      in ballE)
      apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
      prefer 2
      apply(simp add: epdaH_step_relation_def)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
     apply(simp add: epdaH_step_relation_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    apply(simp add: epdaH.get_accessible_configurations_def)
    apply(erule_tac
      x="dx2"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="i2"
      and P="\<lambda>i2. get_configuration (dx2 i2) \<noteq> Some \<lparr>epdaH_conf_state = cons_state_or_state_old (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in allE)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt q)(*strict*)
   apply(rule_tac
      x="cons_state_or_state_new"
      in exI)
   apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt q)(*strict*)
   apply(case_tac q)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt q a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a b)(*strict*)
    apply(case_tac a)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a b aa ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt q a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
   apply(subgoal_tac "main_states_can_be_left_with_empty_step S F_DPDA_EUML__is_main")
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
   apply(simp add: main_states_can_be_left_with_empty_step_def)
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in ballE)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    apply(erule impE)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
     apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
    apply(subgoal_tac "only_executing_edges_from_marking_states S")
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
     prefer 2
     apply(simp add: F_DPDA_RCS__SpecInput_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
    apply(simp add: only_executing_edges_from_marking_states_def)
    apply(erule_tac
      x="e"
      in ballE)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
     prefer 2
     apply(simp add: epdaH_step_relation_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a e)(*strict*)
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
   apply(simp add: epdaH.get_accessible_configurations_def)
   apply(erule_tac
      x="dx2"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="i2"
      and P="\<lambda>i2. get_configuration (dx2 i2) \<noteq> Some \<lparr>epdaH_conf_state = cons_state_or_state_new (cons_state a), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in allE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
  apply(subgoal_tac "q1 \<in> epda_states S \<longrightarrow> (\<forall>f pS pP X. q1 = f (cons_state_and_stack (cons_tuple2 pS pP) X) \<longrightarrow> f \<noteq> cons_state_or_state_new \<and> f \<noteq> cons_state_or_state_old \<or> f (cons_state_and_stack (cons_tuple2 pS pP) X) \<in> epda_nonstable_states (epda_delta S) \<or> (\<forall>u\<in> \<Sigma>UC. \<forall>eP\<in> epda_delta P. edge_event eP = Some u \<longrightarrow> edge_src eP = pP \<longrightarrow> (\<exists>eS\<in> epda_delta S. edge_event eS = Some u \<and> edge_src eS = f (cons_state_and_stack (cons_tuple2 pS pP) X) \<and> edge_pop eS = [X])))")
   apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_NCS_def)
   apply(clarsimp)
   apply(erule_tac x="f" in allE)
   apply(erule_tac x="pS" in allE)
   apply(erule_tac x="edge_src eP" in allE)
   apply(erule_tac x="X" in allE)
   apply(erule impE)
    apply(force)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 q1 s1 c01 c03 e1a w h qs po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      x="f"
      in allE)
  apply(erule_tac
      x="qx1"
      in allE)
  apply(erule_tac
      x="qx2"
      in allE)
  apply(erule_tac
      x="X"
      in allE)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      P="f \<noteq> cons_state_or_state_new \<and> f \<noteq> cons_state_or_state_old"
      in disjE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      P="f (cons_state_and_stack (cons_tuple2 qx1 qx2) X) \<in> epda_nonstable_states (epda_delta S)"
      in disjE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   apply(subgoal_tac "only_executing_edges_from_marking_states S")
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   apply(simp add: epda_nonstable_states_def only_executing_edges_from_marking_states_def)
   apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X e)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      x="v"
      in ballE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = Some v, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(subgoal_tac "epdaH_reflection_to_DFA_exists S P (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)")
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(erule_tac
      x="dx2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="i2"
      and P="\<lambda>i2. \<forall>c. get_configuration (dx2 i2) = Some c \<longrightarrow> (\<exists>d'. epdaH.derivation_initial P d' \<and> (\<exists>m. get_configuration (d' m) = Some \<lparr>epdaH_conf_state = sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (epdaH_conf_state c))), epdaH_conf_history = epdaH_conf_history c, epdaH_conf_stack = [epda_box P]\<rparr>))"
      in allE)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = f (cons_state_and_stack (cons_tuple2 qx1 qx2) X), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in allE)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(erule_tac
      P="get_configuration (dx2 i2) = Some \<lparr>epdaH_conf_state = f (cons_state_and_stack (cons_tuple2 qx1 qx2) X), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in impE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m)(*strict*)
  apply(case_tac "d' m")
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
  apply(subgoal_tac "m=length h")
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
    prefer 2
    apply(rule_tac
      d="d'"
      and G="P"
      and n="m"
      in DFA_one_symbol_per_step)
      apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
     apply(force)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
   apply(force)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' m option)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
  apply(subgoal_tac "sel_tuple2_2 (F_DPDA_OTS__get_state (F_DPDA_EUML__get_state (f (cons_state_and_stack (cons_tuple2 qx1 qx2) X)))) = qx2")
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
   prefer 2
   apply(simp add: sel_tuple2_2_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_state_def)
   apply(erule disjE)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
    apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
   apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
   prefer 2
   apply(rule_tac
      G="P"
      and ?d1.0="dx3"
      and ?d2.0="d'"
      and ?n1.0="length h"
      and ?n2.0="length h"
      in epdaH_coincide_on_stable_configurations)
          apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
          apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
         apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
         apply(force)
        apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
        apply(force)
       apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
     apply(clarsimp)
     apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option e c')(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
     apply(force)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def valid_dfa_def)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
   apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 qx2 X d' option)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(subgoal_tac "corresponds_to_top_stack S F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack")
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RCS__SpecInput_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(simp add: corresponds_to_top_stack_def)
  apply(erule_tac
      x="dx2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="i2"
      and P="\<lambda>i2. \<forall>c. get_configuration (dx2 i2) = Some c \<longrightarrow> F_DPDA_EUML__is_auxiliary ((epdaH_conf_state c)) \<longrightarrow> (\<forall>X. F_DPDA_EUML__get_stack ((epdaH_conf_state c)) = Some X \<longrightarrow> (\<exists>w. epdaH_conf_stack c = X # w))"
      in allE)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = f (cons_state_and_stack (cons_tuple2 qx1 qs) X), epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in allE)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
   apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
   apply(erule disjE)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
    apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
   apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(erule_tac
      x="X"
      in allE)
  apply(simp add: F_DPDA_EUML__is_auxiliary_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_OTS__get_stack_def F_DPDA_OTS__get_state_def F_DPDA_EUML__get_stack_def)
  apply(erule impE)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
   apply(erule disjE)
    apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
    apply(clarsimp)
   apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
   apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 s1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS)(*strict*)
  apply(clarsimp)
  apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
  apply(rule_tac
      x="derivation_append dx2 (der2 \<lparr>epdaH_conf_state = f (cons_state_and_stack (cons_tuple2 qx1 qs) X), epdaH_conf_history = h, epdaH_conf_stack = X # wa\<rparr> eS \<lparr>epdaH_conf_state = edge_trg eS, epdaH_conf_history = h@[v], epdaH_conf_stack = (edge_push eS) @ wa\<rparr>) i2"
      in exI)
  apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_dfa_def valid_pda_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
    apply(force)
   apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(simp add: epdaH_step_relation_def)
    apply(simp add: option_to_list_def)
   apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
   apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_dfa_def valid_pda_def)
   apply(clarsimp)
   apply(simp add: der2_def derivation_append_def)
  apply(rename_tac dx1 dx2 dx3 i2 e1 c01 c03 e1a w h qs po pu qt f qx1 X d' eS wa)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  apply(rule_tac
      x="Suc i2"
      in exI)
  apply(simp add: der2_def derivation_append_def)
  done

lemma F_DPDA_RCS__Enforce_Marked_Controllable_Subset: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC) = Some G 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> Enforce_Marked_Controllable_Subset \<Sigma>UC (epdaH.unmarked_language P) (epda_to_des S) = epda_to_des G"
  apply(simp add: epda_to_des_def Enforce_Marked_Controllable_Subset_def Let_def)
  apply(rule conjI)
   apply(rule antisym)
    apply(simp add: epda_to_des_def des_langUM_def Enforce_Marked_Controllable_Subset_def Let_def alphabet_to_language_def)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule controllable_sublanguage_vs_controllable_word_strict_case1)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(thin_tac "controllable_sublanguage ((prefix_closure {x}) - {x}) {w. \<exists>v\<in> \<Sigma>UC. w = [v]} (epdaH.unmarked_language P) (epdaH.unmarked_language S)")
    apply(rule F_DPDA_RCS__Enforce_Marked_Controllable_Subset__unmarked_language_part1)
          apply(rename_tac x)(*strict*)
          apply(force)
         apply(rename_tac x)(*strict*)
         apply(force)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "F_EPDA_RS__SpecOutput S SSX (F_EPDA_RS S (epda_states S - F_DPDA_NCS S P \<Sigma>UC))" for SSX)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule F_EPDA_RS__SOUND)
     apply(simp add: F_EPDA_RS__SpecInput_def F_DPDA_RCS__SpecInput_def)
     apply(clarsimp)
     apply(rule_tac
      t="nonblockingness_language (epdaH.unmarked_language S) (epdaH.marked_language S)"
      and s="nonblockingness_language (epdaS.unmarked_language S) (epdaS.marked_language S)"
      in subst)
      apply(rename_tac x)(*strict*)
      apply(rule epdaS_to_epdaH_nonblockingness_language)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_EPDA_RS__SpecOutput_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac x)(*strict*)
    apply(simp add: epdaH.unmarked_language_def)
    apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(rule_tac
      x="d"
      in exI)
    apply(rule context_conjI)
     apply(rename_tac x d)(*strict*)
     apply(rule epda_sub_preserves_derivation_initial)
        apply(rename_tac x d)(*strict*)
        prefer 4
        apply(force)
       apply(rename_tac x d)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac x d)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac x d)(*strict*)
     apply(simp add: epda_sub_def)
     apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
     apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
      apply(rename_tac x d)(*strict*)
      apply(clarsimp)
     apply(rename_tac x d)(*strict*)
     apply(clarsimp)
     apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(simp add: epdaH_unmarked_effect_def)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="controllable_sublanguage ((prefix_closure {x}) - {x}) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language P) (epdaH.unmarked_language S)"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(rule Cont_vs_controllable_word_strict_case)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w)(*strict*)
   apply(rule F_DPDA_RCS__Enforce_Marked_Controllable_Subset__unmarked_language_part2)
         apply(rename_tac x w)(*strict*)
         apply(force)
        apply(rename_tac x w)(*strict*)
        apply(force)
       apply(rename_tac x w)(*strict*)
       apply(force)
      apply(rename_tac x w)(*strict*)
      apply(force)
     apply(rename_tac x w)(*strict*)
     apply(force)
    apply(rename_tac x w)(*strict*)
    apply(force)
   apply(rename_tac x w)(*strict*)
   apply(force)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule F_DPDA_RCS__Enforce_Marked_Controllable_Subset__marked_language_part1)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: des_langUM_def controllable_subset_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rename_tac x)(*strict*)
   apply(simp add: epdaH.marked_language_def)
   apply(clarsimp)
   apply(rename_tac x d)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac x d)(*strict*)
    apply(rule epda_sub_preserves_derivation_initial)
       apply(rename_tac x d)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac x d)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac x d)(*strict*)
     apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac x d)(*strict*)
    apply(simp add: epda_sub_def)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
     apply(rename_tac x d)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(clarsimp)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marked_effect_def epdaH_marking_condition_def)
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i ia e ea c ca)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
    apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def)
    apply(clarsimp)
    apply(rename_tac d i ia e ea q s h qa sa ha)(*strict*)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
    apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
     apply(rename_tac d i ia e ea q s h qa sa ha)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i ia e ea q s h qa sa ha)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(clarsimp)
   apply(rename_tac d i ia e ea c ca)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def)
   apply(clarsimp)
   apply(rename_tac d i ia e ea q s h qa sa ha)(*strict*)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial S \<in> epda_states S \<longrightarrow> epda_initial S \<in> F_DPDA_NCS S P \<Sigma>UC")
    apply(rename_tac d i ia e ea q s h qa sa ha)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i ia e ea q s h qa sa ha)(*strict*)
   apply(clarsimp)
   apply(simp add: epda_sub_def F_EPDA_R_def F_EPDA_RS_def Let_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: controllable_subset_def controllable_sublanguage_def prefix_closure_def prefix_def)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac w' c)(*strict*)
   apply(rule_tac
      xs="c"
      in rev_cases)
    apply(rename_tac w' c)(*strict*)
    prefer 2
    apply(rename_tac w' c ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' ys y)(*strict*)
    apply(rule_tac
      x="w'@ys@[y]"
      in F_DPDA_RCS__Enforce_Marked_Controllable_Subset__unmarked_language_part2)
          apply(rename_tac w' ys y)(*strict*)
          apply(force)
         apply(rename_tac w' ys y)(*strict*)
         apply(force)
        apply(rename_tac w' ys y)(*strict*)
        apply(force)
       apply(rename_tac w' ys y)(*strict*)
       apply(force)
      apply(rename_tac w' ys y)(*strict*)
      prefer 3
      apply(simp add: strict_prefix_def)
     apply(rename_tac w' ys y)(*strict*)
     apply(simp add: epdaH.unmarked_language_def epdaH.marked_language_def)
     apply(clarsimp)
     apply(rename_tac w' ys y d)(*strict*)
     apply(rule_tac
      x="d"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      A="epdaH_marked_effect G d"
      in set_mp)
      apply(rename_tac w' ys y d)(*strict*)
      apply(rule epdaH.AX_effect_inclusion1)
        apply(rename_tac w' ys y d)(*strict*)
        apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac w' ys y d)(*strict*)
       apply(force)
      apply(rename_tac w' ys y d)(*strict*)
      apply(force)
     apply(rename_tac w' ys y d)(*strict*)
     apply(force)
    apply(rename_tac w' ys y)(*strict*)
    apply(simp add: epdaH.unmarked_language_def epdaH.marked_language_def des_langM_def)
    apply(clarsimp)
    apply(rename_tac w' ys y d)(*strict*)
    apply(subgoal_tac "w' @ ys @ [y] \<in> {w. \<exists>d. epdaH.derivation_initial S d \<and> w \<in> epdaH_marked_effect S d \<and> epdaH.derivation S d \<and> epdaH_marking_condition S d}")
     apply(rename_tac w' ys y d)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w' ys y d)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' ys y d da)(*strict*)
    apply(simp add: epdaH_marked_effect_def)
    apply(rename_tac w' ys y d da)(*strict*)
    apply(rule_tac
      x="da"
      in exI)
    apply(clarsimp)
    apply(rename_tac w' ys y d da i ia e ea c ca)(*strict*)
    apply(rule_tac
      A="epdaH_marked_effect S da"
      in set_mp)
     apply(rename_tac w' ys y d da i ia e ea c ca)(*strict*)
     apply(rule epdaH.AX_effect_inclusion1)
       apply(rename_tac w' ys y d da i ia e ea c ca)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac w' ys y d da i ia e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac w' ys y d da i ia e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac w' ys y d da i ia e ea c ca)(*strict*)
    apply(simp add: epdaH_marking_configurations_def epdaH_marked_effect_def)
    apply(clarsimp)
    apply(rename_tac w' ys y d da i ia e ea c ca)
    apply(rule_tac
      x="ia"
      in exI)
    apply(rule_tac
      x="ea"
      in exI)
    apply(rule_tac
      x="ca"
      in exI)
    apply(clarsimp)
   apply(rename_tac w' c)(*strict*)
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply(simp add: epda_to_des_def des_langM_def Enforce_Marked_Controllable_Subset_def Let_def alphabet_to_language_def controllable_word_def)
   apply(clarsimp)
   apply(rename_tac w' v)(*strict*)
   apply(rule F_DPDA_RCS__Enforce_Marked_Controllable_Subset__marked_language_part2)
          apply(rename_tac w' v)(*strict*)
          apply(force)
         apply(rename_tac w' v)(*strict*)
         apply(force)
        apply(rename_tac w' v)(*strict*)
        apply(force)
       apply(rename_tac w' v)(*strict*)
       apply(force)
      apply(rename_tac w' v)(*strict*)
      apply(force)
     apply(rename_tac w' v)(*strict*)
     apply(force)
    apply(rename_tac w' v)(*strict*)
    apply(force)
   apply(rename_tac w' v)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      A="des_langM (DES (epdaH.unmarked_language S) (epdaH.marked_language S))"
      in set_mp)
   apply(rename_tac x)(*strict*)
   apply(simp add: des_langUM_def des_langM_def epdaH.unmarked_language_def epdaH.marked_language_def)
   apply(clarsimp)
   apply(rename_tac x xa d da)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      A="epdaH_marked_effect S da"
      in set_mp)
    apply(rename_tac x xa d da)(*strict*)
    apply(rule epdaH.AX_effect_inclusion1)
      apply(rename_tac x xa d da)(*strict*)
      apply(simp add: F_DPDA_RCS__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac x xa d da)(*strict*)
     apply(force)
    apply(rename_tac x xa d da)(*strict*)
    apply(force)
   apply(rename_tac x xa d da)(*strict*)
   apply(simp add: epdaH_marking_configurations_def epdaH_marked_effect_def)
  apply(rename_tac x)(*strict*)
  apply(simp add: des_langUM_def des_langM_def epdaH.unmarked_language_def epdaH.marked_language_def)
  apply(force)
  done

theorem F_DPDA_RCS__SOUND: "
  F_DPDA_RCS__SpecInput S (P, \<Sigma>UC) 
  \<Longrightarrow> F_DPDA_RCS__SpecOutput S (P, \<Sigma>UC) (F_DPDA_RCS S P \<Sigma>UC)"
  apply(case_tac "F_DPDA_RCS S P \<Sigma>UC")
  apply(rename_tac a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: F_DPDA_RCS__SpecOutput_def F_DPDA_RCS_def Let_def)
   apply(clarsimp)
   apply(rule F_DPDA_RCS__SOUND__for_None)
    apply(force)
   apply(force)
  apply(rename_tac a b aa)(*strict*)
  apply(simp add: F_DPDA_RCS_def Let_def)
  apply(clarsimp)
  apply(rename_tac aa)(*strict*)
  apply(rename_tac G)
  apply(rename_tac G)(*strict*)
  apply(simp add: F_DPDA_RCS__SpecOutput_def)
  apply(subgoal_tac "\<not> epdaH_livelock G \<and> valid_dpda G \<and> (F_DPDA_NCS S P \<Sigma>UC = {} \<longleftrightarrow> S = G) \<and> (F_DPDA_NCS S P \<Sigma>UC = {} \<longleftrightarrow> epda_to_des S = epda_to_des G)")
   apply(rename_tac G)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac G)(*strict*)
    prefer 2
    apply(rule_tac
      G="S"
      and Q="epda_states S - F_DPDA_NCS S P \<Sigma>UC"
      in F_EPDA_RS__SOUND)
    apply(simp add: F_EPDA_RS__SpecInput_def F_DPDA_RCS__SpecInput_def)
    apply(rule conjI)
     apply(rename_tac G)(*strict*)
     apply(force)
    apply(rename_tac G)(*strict*)
    apply(rule_tac
      t="nonblockingness_language (epdaH.unmarked_language S) (epdaH.marked_language S)"
      and s="nonblockingness_language (epdaS.unmarked_language S) (epdaS.marked_language S)"
      in subst)
     apply(rename_tac G)(*strict*)
     apply(rule epdaS_to_epdaH_nonblockingness_language)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(simp add: F_EPDA_RS__SpecOutput_def)
   apply(subgoal_tac "F_DPDA_NCS S P \<Sigma>UC \<subseteq> epda_states S")
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(simp (no_asm) add: F_DPDA_NCS_def)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(S = G) = epda_operational_controllable S P \<Sigma>UC")
   apply(rename_tac G)(*strict*)
   prefer 2
   apply(rule antisym)
    apply(rename_tac G)(*strict*)
    apply(rule F_DPDA_RCS__enforces__operational_controllable_part1)
       apply(rename_tac G)(*strict*)
       apply(simp add: F_DPDA_RCS__SpecInput_def)
      apply(rename_tac G)(*strict*)
      apply(force)
     apply(rename_tac G)(*strict*)
     apply(force)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(rule F_DPDA_RCS__enforces__operational_controllable_part2)
       apply(rename_tac G)(*strict*)
       apply(force)
      apply(rename_tac G)(*strict*)
      apply(force)
     apply(rename_tac G)(*strict*)
     apply(force)
    apply(rename_tac G)(*strict*)
    apply(simp add: F_DPDA_RCS__SpecInput_def)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule F_DPDA_RCS__Enforce_Marked_Controllable_Subset)
     apply(rename_tac G)(*strict*)
     apply(force)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(force)
  done

end
