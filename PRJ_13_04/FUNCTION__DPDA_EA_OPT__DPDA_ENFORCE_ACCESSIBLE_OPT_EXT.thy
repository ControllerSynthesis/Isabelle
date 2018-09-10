section {*FUNCTION\_\_DPDA\_EA\_OPT\_\_DPDA\_ENFORCE\_ACCESSIBLE\_OPT\_EXT*}
theory
  FUNCTION__DPDA_EA_OPT__DPDA_ENFORCE_ACCESSIBLE_OPT_EXT

imports
  PRJ_13_04__ENTRY

begin

definition F_DPDA_EA_OPT__SpecInput2 :: "
  ((((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> ('stateB, 'event, 'stackB) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_EA_OPT__SpecInput2 G D \<equiv>
  valid_dpda G 
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G) 
  \<and> state_stack_unique_for_marking_states G 
  \<and> only_executing_edges_from_marking_states G 
  \<and> \<not> epdaH_livelock G 
  \<and> epdaH_reflection_to_DFA_exists G D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state) 
  \<and> corresponds_to_top_stack G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
  \<and> main_states_have_only_empty_steps G F_DPDA_EUML__is_main 
  \<and> main_states_have_all_empty_steps G F_DPDA_EUML__is_main 
  \<and> executing_edge_from_auxiliary_to_main_state G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
  \<and> always_applicable_for_auxiliary_states G F_DPDA_EUML__is_auxiliary 
  \<and> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_EUML__is_main"

definition main_states_can_be_left_with_empty_step :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "main_states_can_be_left_with_empty_step R F \<equiv>
  \<forall>c \<in> epdaH.get_accessible_configurations R.
    F (epdaH_conf_state c)
    \<longrightarrow>
      (\<exists>e.
        e \<in> epda_delta R
        \<and> edge_src e = epdaH_conf_state c
        \<and> edge_pop e = [hd (epdaH_conf_stack c)]
        \<and> edge_event e = None)"

definition F_DPDA_EA_OPT__SpecOutput2 :: "
  ((((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda
  \<Rightarrow> (('stateB, 'event, 'stackB) epda \<times> 'event set) 
  \<Rightarrow> ((((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_EA_OPT__SpecOutput2 Gi X Go \<equiv>
  case X of 
  (D, \<Sigma>UC) \<Rightarrow> 
    valid_dpda Go 
    \<and> epdaS.marked_language Gi = epdaS.marked_language Go 
    \<and> epdaS.unmarked_language Gi = epdaS.unmarked_language Go 
    \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go) 
    \<and> state_stack_unique_for_marking_states Go 
    \<and> only_executing_edges_from_marking_states Go 
    \<and> \<not> epdaH_livelock Go 
    \<and> epdaH_reflection_to_DFA_exists Go D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state) 
    \<and> corresponds_to_top_stack Go F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
    \<and> epdaH.accessible Go 
    \<and> main_states_can_be_left_with_empty_step Go F_DPDA_EUML__is_main 
    \<and> main_states_have_only_empty_steps Go F_DPDA_EUML__is_main 
    \<and> executing_edge_from_auxiliary_to_main_state Go F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
    \<and> always_applicable_for_auxiliary_states Go F_DPDA_EUML__is_auxiliary 
    \<and> main_to_auxiliary_or_auxiliary_to_main Go F_DPDA_EUML__is_main"


lemma epda_sub_preserves_state_stack_unique_for_marking_states: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> state_stack_unique_for_marking_states G2
  \<Longrightarrow> state_stack_unique_for_marking_states G1"
  apply(simp add: state_stack_unique_for_marking_states_def state_stack_unique_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(simp add: epda_sub_def)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(force)
  done

theorem F_DPDA_EA_OPT__preserves_state_stack_unique_for_marking_states: "
  valid_epda G
  \<Longrightarrow> state_stack_unique_for_marking_states G
  \<Longrightarrow> state_stack_unique_for_marking_states (F_DPDA_EA_OPT G)"
  apply(rule epda_sub_preserves_state_stack_unique_for_marking_states)
     apply(simp add: F_DPDA_EA_OPT_def F_EPDA_RE_def)
     apply(rule F_EPDA_R_preserves_valid_epda)
       apply(force)
      prefer 2
      apply(force)
     apply(force)
    apply(force)
   apply(rule F_DPDA_EA_OPT__constructs_epda_sub)
   apply(force)
  apply(force)
  done

lemma epda_sub_preserves_only_executing_edges_from_marking_states: "
  valid_epda G
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> only_executing_edges_from_marking_states G2
  \<Longrightarrow> only_executing_edges_from_marking_states G1"
  apply(simp add: only_executing_edges_from_marking_states_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: epda_sub_def)
  apply(clarsimp)
  apply(force)
  done

theorem F_DPDA_EA_OPT__preserves_only_executing_edges_from_marking_states: "
  valid_epda G
  \<Longrightarrow> only_executing_edges_from_marking_states G
  \<Longrightarrow> only_executing_edges_from_marking_states (F_DPDA_EA_OPT G)"
  apply(rule epda_sub_preserves_only_executing_edges_from_marking_states)
    apply(force)
   apply(rule F_DPDA_EA_OPT__constructs_epda_sub)
   apply(force)
  apply(force)
  done

lemma epda_sub_preserves_epdaH_reflection_to_DFA_exists: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> epdaH_reflection_to_DFA_exists G2 D f
  \<Longrightarrow> epdaH_reflection_to_DFA_exists G1 D f"
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(clarsimp)
  apply(rename_tac d n c)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c)(*strict*)
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac d n c)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac d n c)(*strict*)
     apply(force)
    apply(rename_tac d n c)(*strict*)
    apply(force)
   apply(rename_tac d n c)(*strict*)
   apply(force)
  apply(rename_tac d n c)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d n c)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_EA_OPT__preserves_epdaH_reflection_to_DFA_exists: "
  valid_dpda M
  \<Longrightarrow> epdaH_reflection_to_DFA_exists M D f
  \<Longrightarrow> R = F_DPDA_EA_OPT M
  \<Longrightarrow> epdaH_reflection_to_DFA_exists R D f"
  apply(rule_tac
      ?G1.0="R"
      and ?G2.0="M"
      in epda_sub_preserves_epdaH_reflection_to_DFA_exists)
     apply(simp add: F_DPDA_EA_OPT_def F_EPDA_RE_def)
     apply(rule F_EPDA_R_preserves_valid_epda)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(force)
      prefer 2
      apply(force)
     apply(force)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(rule F_DPDA_EA_OPT__constructs_epda_sub)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

theorem F_DPDA_EA_OPT__preserves_corresponds_to_top_stack: "
  valid_epda G 
  \<Longrightarrow> corresponds_to_top_stack G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
  \<Longrightarrow> Go = F_DPDA_EA_OPT G 
  \<Longrightarrow> corresponds_to_top_stack Go F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack"
  apply(simp add: corresponds_to_top_stack_def)
  apply(clarsimp)
  apply(rename_tac d n c X)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c X)(*strict*)
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac d n c X)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac d n c X)(*strict*)
     apply(simp add: F_DPDA_EA_OPT_def F_EPDA_RE_def)
     apply(rule F_EPDA_R_preserves_valid_epda)
       apply(simp add: valid_dpda_def valid_pda_def)
      prefer 2
      apply(force)
     apply(force)
    apply(force)
   apply(rule F_DPDA_EA_OPT__constructs_epda_sub)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

theorem F_DPDA_EA_OPT__transforms_main_states_have_all_empty_steps_into_main_states_can_be_left_with_empty_step: "
  F_DPDA_EA_OPT__SpecInput2 G D 
  \<Longrightarrow> valid_dpda G 
  \<Longrightarrow> Go = F_DPDA_EA_OPT G 
  \<Longrightarrow> valid_dpda Go 
  \<Longrightarrow> main_states_have_all_empty_steps G F_DPDA_EUML__is_main 
  \<Longrightarrow> epdaH.accessible Go 
  \<Longrightarrow> main_states_can_be_left_with_empty_step Go F_DPDA_EUML__is_main"
  apply(simp add: F_DPDA_EUML__SpecInput_def main_states_have_all_empty_steps_def main_states_can_be_left_with_empty_step_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: epdaH.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac c d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c d i a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c d i e)(*strict*)
  apply(case_tac c)
  apply(rename_tac c d i e epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac c d i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "epdaH.derivation_initial G d")
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      ?G1.0="F_DPDA_EA_OPT G"
      in epda_sub_preserves_derivation_initial)
      apply(rename_tac d i e q h s)(*strict*)
      prefer 2
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d i e q h s)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d i e q h s)(*strict*)
    apply(rule F_DPDA_EA_OPT__constructs_epda_sub)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr> \<in> epdaH_configurations G")
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
    apply(rename_tac d i e q h s)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i e q h s)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d i e q h s)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(erule_tac
      x="q"
      in ballE)
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(simp add: epdaH_configurations_def F_DPDA_EA_OPT_def F_ALT_EPDA_RE_def Let_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and i="i"
      in epdaH_epda_stack_is_must_terminated_by_prime)
     apply(rename_tac d i e q h s)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i e q h s)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(case_tac s)
   apply(rename_tac d i e q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h)(*strict*)
   apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac d i e q h s a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h a list)(*strict*)
  apply(thin_tac "a # list \<in> must_terminated_by (epda_gamma (F_DPDA_EA_OPT G)) (epda_box (F_DPDA_EA_OPT G))")
  apply(erule_tac
      x="a"
      in ballE)
   apply(rename_tac d i e q h a list)(*strict*)
   prefer 2
   apply(simp add: epdaH_configurations_def F_DPDA_EA_OPT_def F_ALT_EPDA_RE_def Let_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d i e q h a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h a list ea)(*strict*)
  apply(simp (no_asm) add: F_DPDA_EA_OPT_def F_ALT_EPDA_RE_def Let_def)
  apply(rule_tac
      t="F_DPDA_DRE G (Suc 0)"
      and s="epdaH_required_edges G"
      in ssubst)
   apply(rename_tac d i e h a list ea)(*strict*)
   apply(rule F_DPDA_DRE__are_precisely_reachable)
    apply(force)
   apply(force)
  apply(rename_tac d i e h a list ea)(*strict*)
  apply(rule_tac
      t="epdaS_required_edges G"
      and s="epdaH_required_edges G"
      in ssubst)
   apply(rename_tac d i e h a list ea)(*strict*)
   apply(rule epdaS_required_edges__vs__epdaH_required_edges)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac d i e h a list ea)(*strict*)
  apply(rule_tac
      x="ea"
      in exI)
  apply(clarsimp)
  apply(simp add: F_EPDA_RE_def F_EPDA_R_def Let_def)
  apply(rule context_conjI)
   prefer 2
   apply(rule conjI)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def valid_epda_step_label_def)
   apply(rule conjI)
    apply(rule disjI2)
    apply(rule conjI)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def valid_epda_step_label_def)
    apply(force)
   apply(rule conjI)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def valid_epda_step_label_def)
   apply(rule disjI2)
   apply(rule conjI)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def valid_epda_step_label_def)
   apply(force)
  apply(subgoal_tac "epdaH.Nonblockingness_branching G")
   prefer 2
   apply(simp add: F_DPDA_EA_OPT__SpecInput2_def)
   apply(erule conjE)+
   apply (metis DPDA_to_epdaH_determinism epdaH.AX_is_forward_edge_deterministic_correspond_DB_SB epdaH.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long epdaH_operational_Nonblockingness_from_language_Nonblockingness epdaS_to_epdaH_nonblockingness_language valid_dpda_def valid_pda_def)
  apply(simp add: epdaH.Nonblockingness_branching_def)
  apply(erule_tac x="derivation_append d (der2 \<lparr>epdaH_conf_state = edge_src ea, epdaH_conf_history = h,
                 epdaH_conf_stack = a # list\<rparr> ea \<lparr>epdaH_conf_state = edge_trg ea, epdaH_conf_history = h,
                 epdaH_conf_stack = (edge_push ea) @ list\<rparr>) i" in allE)
  apply(subgoal_tac "epdaH.derivation_initial G
        (derivation_append d
          (der2 \<lparr>epdaH_conf_state = edge_src ea, epdaH_conf_history = h,
                   epdaH_conf_stack = a # list\<rparr>
            ea \<lparr>epdaH_conf_state = edge_trg ea, epdaH_conf_history = h,
                  epdaH_conf_stack = edge_push ea @ list\<rparr>)
          i)")
   prefer 2
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(force)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rule epdaH.der2_is_derivation)
    apply(simp add: epdaH_step_relation_def)
    apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(simp add: der2_def derivation_append_def)
  apply(erule impE)
   apply(force)
  apply(erule_tac x="Suc i" in allE)
  apply(erule impE)
   apply(simp add: der2_def derivation_append_def maximum_of_domain_def)
  apply(clarsimp)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(simp add: epdaH_required_edges_def)
  apply(rule_tac x="derivation_append
           (derivation_append d
             (der2 \<lparr>epdaH_conf_state = edge_src ea, epdaH_conf_history = h,
                      epdaH_conf_stack = a # list\<rparr>
               ea \<lparr>epdaH_conf_state = edge_trg ea, epdaH_conf_history = h,
                     epdaH_conf_stack = edge_push ea @ list\<rparr>)
             i)
           dc (Suc i)" in exI)
  apply(rule context_conjI)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(force)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(simp add: epdaH.derivation_initial_def)
    apply(force)
   apply(simp add: derivation_append_def derivation_append_fit_def der2_def)
   apply(case_tac "dc 0")
    apply(simp add: epdaH.derivation_def)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac x1 x2)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_def)
   apply(case_tac x1)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule_tac x="Suc i" in exI)
  apply(rule conjI)
   apply(simp add: derivation_append_def derivation_append_fit_def der2_def)
  apply(case_tac "ia\<ge>Suc i")
   apply(rule_tac x="ia" in exI)
   apply(simp add: derivation_append_def derivation_append_fit_def der2_def)
  apply(subgoal_tac "ia < Suc i")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(erule_tac x="Suc ia" in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="ia" and m="Suc i" and d="derivation_append d
          (der2 \<lparr>epdaH_conf_state = edge_src ea, epdaH_conf_history = h,
                   epdaH_conf_stack = a # list\<rparr>
            ea \<lparr>epdaH_conf_state = edge_trg ea, epdaH_conf_history = h,
                  epdaH_conf_stack = edge_push ea @ list\<rparr>)
          i" in epdaH.step_detail_before_some_position)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(simp add: derivation_append_def derivation_append_fit_def der2_def)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply(subgoal_tac "only_executing_edges_from_marking_states G")
   prefer 2
   apply(simp add: F_DPDA_EA_OPT__SpecInput2_def)
  apply(simp add: only_executing_edges_from_marking_states_def)
  apply(case_tac "edge_event e2")
   apply(erule_tac x="e2" in ballE)
    prefer 2
    apply(simp add: epdaH_step_relation_def)
   apply(erule impE)
    apply(clarsimp)
   apply(simp add: epdaH_marking_configurations_def epdaH_step_relation_def)
   apply(simp add: derivation_append_def derivation_append_fit_def der2_def)
  apply(simp add: derivation_append_def derivation_append_fit_def der2_def epdaH_string_state_def epdaH_step_relation_def option_to_list_def)
  done

theorem F_DPDA_EA_OPT__preserves_main_states_have_only_empty_steps: "
  valid_dpda G 
  \<Longrightarrow> Go = F_DPDA_EA_OPT G 
  \<Longrightarrow> main_states_have_only_empty_steps G F_DPDA_EUML__is_main 
  \<Longrightarrow> main_states_have_only_empty_steps Go F_DPDA_EUML__is_main"
  apply(simp add: F_DPDA_EUML__SpecInput_def main_states_have_only_empty_steps_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="edge_src e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EA_OPT_def F_ALT_EPDA_RE_def Let_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(case_tac "e")
   apply(rename_tac e edge_srca edge_eventa edge_pop edge_push edge_trg)(*strict*)
   apply(clarsimp)
   apply(rename_tac edge_srca edge_eventa edge_pop edge_push edge_trg)(*strict*)
   apply(rename_tac qs re po pu qt)
   apply(rename_tac qs re po pu qt)(*strict*)
   apply(simp add: F_DPDA_EA_OPT_def F_EPDA_R_def F_EPDA_RE_def Let_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_EA_OPT_def F_EPDA_R_def F_EPDA_RE_def Let_def)
  done

theorem F_DPDA_EA_OPT__preserves_executing_edge_from_auxiliary_to_main_state: "
  valid_dpda G 
  \<Longrightarrow> Go = F_DPDA_EA_OPT G 
  \<Longrightarrow> executing_edge_from_auxiliary_to_main_state G F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
  \<Longrightarrow> executing_edge_from_auxiliary_to_main_state Go F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main"
  apply(simp add: executing_edge_from_auxiliary_to_main_state_def)
  apply(clarsimp)
  apply(rename_tac e y)(*strict*)
  apply(erule_tac
      x="e"
      in allE)
  apply(clarsimp)
  apply(simp add: F_DPDA_EA_OPT_def F_ALT_EPDA_RE_def Let_def)
  apply(simp add: F_DPDA_EA_OPT_def F_EPDA_R_def F_EPDA_RE_def Let_def)
  done

theorem F_DPDA_EA_OPT__preserves_always_applicable_for_auxiliary_states: "
  valid_dpda G
  \<Longrightarrow> Go = F_DPDA_EA_OPT G
  \<Longrightarrow> always_applicable_for_auxiliary_states G F_DPDA_EUML__is_auxiliary
  \<Longrightarrow> always_applicable_for_auxiliary_states Go F_DPDA_EUML__is_auxiliary"
  apply(simp add: always_applicable_for_auxiliary_states_def always_applicable_def)
  apply(clarsimp)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d e c n ea)(*strict*)
   apply(rule epda_sub_preserves_derivation_initial)
      apply(rename_tac d e c n ea)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac d e c n ea)(*strict*)
     apply(simp add: F_DPDA_EA_OPT_def F_EPDA_RE_def)
     apply(rule F_EPDA_R_preserves_valid_epda)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(force)
      prefer 2
      apply(force)
     apply(force)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rule F_DPDA_EA_OPT__constructs_epda_sub)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule impE)
   apply(rename_tac d e c n ea)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule impE)
   apply(rename_tac d e c n ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule_tac
      x="ea"
      in ballE)
   apply(rename_tac d e c n ea)(*strict*)
   prefer 2
   apply(simp add: F_EPDA_R_def F_DPDA_EA_OPT_def F_EPDA_RE_def Let_def)
  apply(rename_tac d e c n ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n ea x)(*strict*)
  apply(rule_tac
      x="x"
      in exI)
  apply(simp add: epdaH_step_relation_def)
  done

theorem F_DPDA_EA_OPT__preserves__main_to_auxiliary_or_auxiliary_to_main: "
  valid_dpda G
  \<Longrightarrow> Go = F_DPDA_EA_OPT G
  \<Longrightarrow> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_EUML__is_main
  \<Longrightarrow> main_to_auxiliary_or_auxiliary_to_main Go F_DPDA_EUML__is_main"
  apply(simp add: main_to_auxiliary_or_auxiliary_to_main_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_EPDA_R_def F_DPDA_EA_OPT_def F_EPDA_RE_def Let_def)
  done

theorem F_DPDA_EA_OPT__SOUND2: "
  F_DPDA_EA_OPT__SpecInput2 G D
  \<Longrightarrow> F_DPDA_EA_OPT__SpecOutput2 G (D, \<Sigma>UC) (F_DPDA_EA_OPT G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_DPDA_EA_OPT__SOUND)
   apply(simp add: F_DPDA_EA_OPT__SpecInput_def F_DPDA_EA_OPT__SpecInput2_def)
   apply(clarsimp)
   apply(rule valid_epda__no_livelock__implies__epdaH_no_livelocks_from_marking_states)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(simp add: F_DPDA_EA_OPT__SpecOutput_def F_DPDA_EA_OPT__SpecInput2_def F_DPDA_EA_OPT__SpecOutput2_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_state_stack_unique_for_marking_states)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_only_executing_edges_from_marking_states)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_not_livelock)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_epdaH_reflection_to_DFA_exists)
     prefer 2
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_corresponds_to_top_stack)
     prefer 2
     apply(force)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(rule context_conjI)
   apply(rule epdaS_to_epdaH_accessible)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__transforms_main_states_have_all_empty_steps_into_main_states_can_be_left_with_empty_step)
        apply(simp add: F_DPDA_EA_OPT__SpecInput2_def)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_main_states_have_only_empty_steps)
     prefer 2
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_executing_edge_from_auxiliary_to_main_state)
     prefer 2
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_OPT__preserves_always_applicable_for_auxiliary_states)
     prefer 2
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_DPDA_EA_OPT__preserves__main_to_auxiliary_or_auxiliary_to_main)
    prefer 2
    apply(force)
   apply(force)
  apply(force)
  done

hide_fact epda_sub_preserves_state_stack_unique_for_marking_states
hide_fact epda_sub_preserves_only_executing_edges_from_marking_states
hide_fact epda_sub_preserves_epdaH_reflection_to_DFA_exists
hide_fact F_DPDA_EA_OPT__preserves_state_stack_unique_for_marking_states
hide_fact F_DPDA_EA_OPT__preserves_only_executing_edges_from_marking_states
hide_fact F_DPDA_EA_OPT__preserves_epdaH_reflection_to_DFA_exists
hide_fact F_DPDA_EA_OPT__preserves_corresponds_to_top_stack
hide_fact F_DPDA_EA_OPT__transforms_main_states_have_all_empty_steps_into_main_states_can_be_left_with_empty_step
hide_fact F_DPDA_EA_OPT__preserves_main_states_have_only_empty_steps
hide_fact F_DPDA_EA_OPT__preserves_executing_edge_from_auxiliary_to_main_state
hide_fact F_DPDA_EA_OPT__preserves_always_applicable_for_auxiliary_states
hide_fact F_DPDA_EA_OPT__preserves__main_to_auxiliary_or_auxiliary_to_main

end
