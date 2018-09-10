section {*FUNCTION\_\_DPDA\_EUML\_\_DPDA\_ENFORCE\_UNIQUE\_MARKING\_LATE*}
theory
  FUNCTION__DPDA_EUML__DPDA_ENFORCE_UNIQUE_MARKING_LATE

imports
  PRJ_13_03__ENTRY

begin

definition F_DPDA_EUML__get_state :: "
  'state DT_state_or_state 
  \<Rightarrow> 'state"
  where
    "F_DPDA_EUML__get_state x \<equiv>
  case x of 
  cons_state_or_state_new q \<Rightarrow> q 
  | cons_state_or_state_old q \<Rightarrow> q"

definition F_DPDA_EUML__get_stack :: "
  ('state, 'stack) DT_state_and_stack_or_state DT_state_or_state 
  \<Rightarrow> 'stack option"
  where
    "F_DPDA_EUML__get_stack \<equiv>
  F_DPDA_OTS__get_stack \<circ> F_DPDA_EUML__get_state"  

definition F_DPDA_EUML__is_main :: "
  ('state, 'stack) DT_state_and_stack_or_state DT_state_or_state
  \<Rightarrow> bool"
  where
    "F_DPDA_EUML__is_main \<equiv>
  F_DPDA_OTS__is_main \<circ> F_DPDA_EUML__get_state"

definition F_DPDA_EUML__is_auxiliary :: "
  ('state, 'stack) DT_state_and_stack_or_state DT_state_or_state
  \<Rightarrow> bool"
  where
    "F_DPDA_EUML__is_auxiliary \<equiv>
  F_DPDA_OTS__is_auxiliary \<circ> F_DPDA_EUML__get_state"    

definition F_DPDA_EUML__SpecInput :: "
  (((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state, 'event, 'stackA) epda 
  \<Rightarrow> ('stateB, 'event, 'stackB) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_EUML__SpecInput G D \<equiv>
  valid_dpda G 
  \<and> state_stack_unique_for_marking_states G 
  \<and> state_stack_unique_for_stable_states G 
  \<and> always_applicable_for_stable_states G 
  \<and> some_edge_applicable G 
  \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G) 
  \<and> \<not> epdaH_livelock G 
  \<and> epdaH_reflection_to_DFA_exists G D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state) 
  \<and> corresponds_to_top_stack G F_DPDA_OTS__is_auxiliary F_DPDA_OTS__get_stack 
  \<and> main_states_have_only_empty_steps G F_DPDA_OTS__is_main 
  \<and> main_states_have_all_empty_steps G F_DPDA_OTS__is_main 
  \<and> executing_edge_from_auxiliary_to_main_state G F_DPDA_OTS__is_auxiliary F_DPDA_OTS__is_main 
  \<and> always_applicable_for_auxiliary_states G F_DPDA_OTS__is_auxiliary 
  \<and> main_to_auxiliary_or_auxiliary_to_main G F_DPDA_OTS__is_main"

definition F_DPDA_EUML__SpecOutput :: "
  (((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state, 'event, 'stackA) epda 
  \<Rightarrow> (('stateB, 'event, 'stackB) epda \<times> 'event set) 
  \<Rightarrow> ((((('stateA, 'stateB) DT_tuple2), 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda 
  \<Rightarrow> bool"
  where
    "F_DPDA_EUML__SpecOutput Gi X Go \<equiv>
  case X of 
  (D, \<Sigma>UC) \<Rightarrow> 
    valid_dpda Go 
    \<and> epdaH.marked_language Gi = epdaH.marked_language Go 
    \<and> epdaH.unmarked_language Gi = epdaH.unmarked_language Go 
    \<and> nonblockingness_language (epdaH.unmarked_language Go) (epdaH.marked_language Go) 
    \<and> state_stack_unique_for_marking_states Go 
    \<and> only_executing_edges_from_marking_states Go 
    \<and> \<not> epdaH_livelock Go 
    \<and> epdaH_reflection_to_DFA_exists Go D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state) 
    \<and> corresponds_to_top_stack Go F_DPDA_EUML__is_auxiliary F_DPDA_EUML__get_stack 
    \<and> main_states_have_only_empty_steps Go F_DPDA_EUML__is_main 
    \<and> main_states_have_all_empty_steps Go F_DPDA_EUML__is_main 
    \<and> executing_edge_from_auxiliary_to_main_state Go F_DPDA_EUML__is_auxiliary F_DPDA_EUML__is_main 
    \<and> always_applicable_for_auxiliary_states Go F_DPDA_EUML__is_auxiliary 
    \<and> main_to_auxiliary_or_auxiliary_to_main Go F_DPDA_EUML__is_main"

theorem F_DPDA_EUML__preserves__pda: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> valid_pda Go"
  apply(simp add: F_DPDA_EUML_def Let_def)
  apply(subgoal_tac "valid_pda (F_SDPDA_EUME G)")
   prefer 2
   apply(rule F_SDPDA_EUME__preserves_PDA)
   apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def)
  apply(clarsimp)
  apply(simp add: F_SDPDA_EUME_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(clarsimp)
   apply(rename_tac a x)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="xa"
      in bexI)
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(simp add: F_DPDA_EUML__SpecInput_def F_SDPDA_EUME_def valid_pda_def valid_epda_def valid_dpda_def)
  apply(clarsimp)
  apply(force)
  done

theorem F_DPDA_EUML__enforces__only_executing_edges_from_marking_states: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> only_executing_edges_from_marking_states Go"
  apply(simp add: only_executing_edges_from_marking_states_def F_DPDA_EUML_def Let_def epda_nonstable_states_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(force)
  done

definition F_DPDA_EUME__LR__configuration :: "
  ('state, 'event, 'stack) epdaH_conf 
  \<Rightarrow> ('state \<Rightarrow> 'state DT_state_or_state) 
  \<Rightarrow> ('state DT_state_or_state, 'event, 'stack) epdaH_conf"
  where
    "F_DPDA_EUME__LR__configuration c f \<equiv>
  \<lparr>epdaH_conf_state = f (epdaH_conf_state c),
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = epdaH_conf_stack c\<rparr>"

definition F_DPDA_EUME__RL__configuration :: "
  ('state DT_state_or_state, 'event, 'stack) epdaH_conf 
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf"
  where
    "F_DPDA_EUME__RL__configuration c \<equiv>
  \<lparr>epdaH_conf_state = 
      case epdaH_conf_state c of 
      cons_state_or_state_old q \<Rightarrow> q
      | cons_state_or_state_new q \<Rightarrow> q,
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = epdaH_conf_stack c\<rparr>"

definition F_DPDA_EUME__RL__derivation :: "
  (('state DT_state_or_state, 'event, 'stack) epda_step_label, ('state DT_state_or_state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation "
  where
    "F_DPDA_EUME__RL__derivation d \<equiv>
  \<lambda>n. case d n of 
  None \<Rightarrow> None 
  | Some (pair e c) \<Rightarrow> 
      Some (pair 
              (case e of 
              None \<Rightarrow> None 
              | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)) 
              (F_DPDA_EUME__RL__configuration c))"

lemma F_DPDA_EUME__reflects__epdaH_step_relation__to__F_DPDA_EUML__RL: "
  epdaH_step_relation (F_SDPDA_EUME G) c1 e2 c2 
  \<Longrightarrow> epdaH_step_relation G (F_DPDA_EUME__RL__configuration c1) (F_DPDA_EUME__RL__edge e2) (F_DPDA_EUME__RL__configuration c2)"
  apply(simp add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_SDPDA_EUME_def)
  apply(clarsimp)
  apply(rename_tac w x)(*strict*)
  apply(simp add: F_SDPDA_EUME__edges_def)
  apply(case_tac "FB_executing_edge x")
   apply(rename_tac w x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(erule disjE)
    apply(rename_tac w x)(*strict*)
    apply(clarsimp)
    apply(case_tac x)
    apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(clarsimp)
   apply(case_tac x)
   apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
  apply(rename_tac w x)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac w x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(case_tac x)
   apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(force)
  apply(rename_tac w x)(*strict*)
  apply(case_tac "edge_src x \<in> epda_marking G")
   apply(rename_tac w x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(case_tac x)
   apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(force)
  apply(rename_tac w x)(*strict*)
  apply(clarsimp)
  apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(case_tac x)
  apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(force)
  done

lemma F_DPDA_EUML__reflects__derivation_preserves_derivation: "
  valid_epda G 
  \<Longrightarrow> epdaH.derivation (F_DPDA_EUML G) d 
  \<Longrightarrow> epdaH.derivation G (F_DPDA_EUME__RL__derivation d)"
  apply(simp (no_asm) add: epdaH.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(simp add: F_DPDA_EUME__RL__derivation_def)
   apply (metis epdaH.some_position_has_details_at_0)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__derivation_def)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaH_step_relation (F_DPDA_EUML G) c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__derivation_def)
  apply(rule F_DPDA_EUME__reflects__epdaH_step_relation__to__F_DPDA_EUML__RL)
  apply(simp add: F_DPDA_EUML_def F_SDPDA_EUME_def epdaH_step_relation_def)
  done

lemma F_DPDA_EUML__reflects__epdaH_initial_configurations: "
  valid_epda G 
  \<Longrightarrow> c \<in> epdaH_initial_configurations (F_DPDA_EUML G) 
  \<Longrightarrow> F_DPDA_EUME__RL__configuration c \<in> epdaH_initial_configurations G"
  apply(simp add: F_DPDA_EUML_def F_SDPDA_EUME_def F_DPDA_EUME__RL__configuration_def epdaH_initial_configurations_def epdaH_configurations_def)
  apply(clarsimp)
  apply(simp add: valid_epda_def)
  done

lemma F_DPDA_EUML__reflects__derivation_preserves_derivation_initial: "
  valid_epda G 
  \<Longrightarrow> epdaH.derivation_initial (F_DPDA_EUML G) d 
  \<Longrightarrow> epdaH.derivation_initial G (F_DPDA_EUME__RL__derivation d)"
  apply(simp (no_asm) add: epdaH.derivation_initial_def)
  apply(rule conjI)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation)
    apply(force)
   apply(simp add: epdaH.derivation_initial_def)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply (metis epdaH.derivation_initial_is_derivation epdaH.some_position_has_details_at_0)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__derivation_def)
  apply(simp add: epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(rule F_DPDA_EUML__reflects__epdaH_initial_configurations)
   apply(rename_tac c)(*strict*)
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma F_DPDA_EUML__preserves__unmarked_language2: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> epdaH.unmarked_language G \<supseteq> epdaH.unmarked_language (F_DPDA_EUML G)"
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="F_DPDA_EUME__RL__derivation d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply (rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac x d)(*strict*)
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def F_DPDA_EUML__SpecInput_def)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac d i e c)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(simp add: F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac x d)(*strict*)
  apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation)
   apply(rename_tac x d)(*strict*)
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def F_DPDA_EUML__SpecInput_def)
  apply(rename_tac x d)(*strict*)
  apply(force)
  done

lemma F_DPDA_EUML__preserves__derivation: "
  valid_epda G 
  \<Longrightarrow> epdaH.derivation G d 
  \<Longrightarrow> maximum_of_domain d n 
  \<Longrightarrow> \<exists>d'. epdaH.derivation (F_DPDA_EUML G) d' \<and> F_DPDA_EUME__RL__derivation d' = d \<and> (epdaH.derivation_initial G d \<longrightarrow> epdaH.derivation_initial (F_DPDA_EUML G) d')"
  apply(induct n arbitrary: d)
   apply(rename_tac d)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c)(*strict*)
    apply(rule_tac
      x="der1 (F_DPDA_EUME__LR__configuration c cons_state_or_state_old)"
      in exI)
    apply(rule context_conjI)
     apply(rename_tac d c)(*strict*)
     apply(rule epdaH.der1_is_derivation)
    apply(rename_tac d c)(*strict*)
    apply(rule conjI)
     apply(rename_tac d c)(*strict*)
     apply(simp add: F_DPDA_EUME__RL__derivation_def der1_def)
     apply(rule ext)
     apply(rename_tac d c n)(*strict*)
     apply(clarsimp)
     apply(case_tac n)
      apply(rename_tac d c n)(*strict*)
      apply(clarsimp)
      apply(rename_tac d c)(*strict*)
      apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__LR__configuration_def)
     apply(rename_tac d c n nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac d c nat)(*strict*)
     apply (metis Zero_not_Suc epdaH.derivation_take_id_prime_prime epdaH.maximum_of_domainUnique maximum_of_domain_derivation_take less_eq_nat.simps(1))
    apply(rename_tac d c)(*strict*)
    prefer 2
    apply(rename_tac d)(*strict*)
    apply (metis epdaH.some_position_has_details_at_0)
   apply(rename_tac d c)(*strict*)
   apply(clarsimp)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac d c)(*strict*)
    apply(force)
   apply(rename_tac d c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c ca)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: der1_def)
   apply(clarsimp)
   apply(rename_tac d c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def F_DPDA_EUML_def F_DPDA_EUME__LR__configuration_def F_SDPDA_EUME_def)
   apply(rule conjI)
    apply(rename_tac d c)(*strict*)
    apply(force)
   apply(rename_tac d c)(*strict*)
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n d)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="derivation_take d n"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n d)(*strict*)
   apply (metis epdaH.derivation_take_preserves_derivation)
  apply(rename_tac n d)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d)(*strict*)
   apply (metis diff_Suc_Suc diff_le_self epdaH.allPreMaxDomSome maximum_of_domain_derivation_take minus_nat.diff_0)
  apply(rename_tac n d)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d d')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac n d d')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n d d')(*strict*)
     apply(force)
    apply(rename_tac n d d')(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n d d')(*strict*)
   apply(force)
  apply(rename_tac n d d')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d d' e1 e2 c1 c2)(*strict*)
  apply(case_tac "FB_executing_edge e2")
   apply(rename_tac n d d' e1 e2 c1 c2)(*strict*)
   apply(case_tac "epdaH_conf_state (the(get_configuration(d' n)))")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule_tac
      x="derivation_append d' (der2 (the (get_configuration (d' n))) (F_SDPDA_EUME__edge_annotation e2 cons_state_or_state_old cons_state_or_state_old) (F_DPDA_EUME__LR__configuration c2 cons_state_or_state_old)) n"
      in exI)
    apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n = derivation_take d n n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule_tac
      t="the (get_configuration (d' n))"
      and s="F_DPDA_EUME__LR__configuration c1 cons_state_or_state_old"
      in ssubst)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
     apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_take_def)
     apply(case_tac "d' n")
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
     apply(case_tac a)
     apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e2 c2 q option b)(*strict*)
     apply(simp add: get_configuration_def)
     apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation)
       apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(rule epdaH.der2_is_derivation)
      apply(simp add: epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__LR__configuration_def F_SDPDA_EUME_def)
      apply(clarsimp)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(rule_tac
      x="e2"
      in bexI)
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(simp add: F_SDPDA_EUME__edges_def)
      apply(rule disjI1)
      apply(simp add: F_SDPDA_EUME__edge_annotation_def)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
     apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
     apply(case_tac "d' n")
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e2 c2 q option b)(*strict*)
     apply(simp add: der2_def)
     apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule conjI)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rule epdaH.derivation_initialI)
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(simp add: derivation_append_def)
     apply(erule impE)
      apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
      apply(rule epdaH.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(case_tac "d 0")
      apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q c a)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule ext)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' x= derivation_take d n x")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
    apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def)
    apply(rule conjI)
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_take_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
    apply(case_tac "x-n=Suc 0")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_take_def)
     apply(subgoal_tac "x=Suc n")
      apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__edge_def F_SDPDA_EUME__edge_annotation_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(case_tac "d x")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    apply(rule_tac
      m="x"
      in epdaH.no_some_beyond_maximum_of_domain)
       apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule_tac
      x="derivation_append d' (der2 (the (get_configuration (d' n))) (F_SDPDA_EUME__edge_annotation e2 cons_state_or_state_new cons_state_or_state_old) (F_DPDA_EUME__LR__configuration c2 cons_state_or_state_old)) n"
      in exI)
   apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n = derivation_take d n n")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule_tac
      t="the (get_configuration (d' n))"
      and s="F_DPDA_EUME__LR__configuration c1 cons_state_or_state_new"
      in ssubst)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
    apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_take_def)
    apply(case_tac "d' n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
    apply(case_tac a)
    apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e2 c2 q option b)(*strict*)
    apply(simp add: get_configuration_def)
    apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: F_DPDA_EUML_def epdaH_step_relation_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__LR__configuration_def F_SDPDA_EUME_def)
     apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(rule_tac
      x="e2"
      in bexI)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def)
     apply(rule disjI2)
     apply(simp add: F_SDPDA_EUME__edge_annotation_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
    apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
    apply(case_tac "d' n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e2 c2 q option b)(*strict*)
    apply(simp add: der2_def)
    apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rule epdaH.derivation_initialI)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
    apply(simp add: derivation_append_def)
    apply(erule impE)
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(case_tac "d 0")
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q c a)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule ext)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' x= derivation_take d n x")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
   apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def)
   apply(rule conjI)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
   apply(case_tac "x-n=Suc 0")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
    apply(subgoal_tac "x=Suc n")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__edge_def F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(case_tac "d x")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
   apply(rule_tac
      m="x"
      in epdaH.no_some_beyond_maximum_of_domain)
      apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
   apply(force)
  apply(rename_tac n d d' e1 e2 c1 c2)(*strict*)
  apply(case_tac "epdaH_conf_state (the(get_configuration(d' n)))")
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(case_tac "q \<in> epda_marking G")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule_tac
      x="derivation_append d' (der2 (the (get_configuration (d' n))) (F_SDPDA_EUME__edge_annotation e2 cons_state_or_state_old cons_state_or_state_new) (F_DPDA_EUME__LR__configuration c2 cons_state_or_state_new)) n"
      in exI)
    apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n = derivation_take d n n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule_tac
      t="the (get_configuration (d' n))"
      and s="F_DPDA_EUME__LR__configuration c1 cons_state_or_state_old"
      in ssubst)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
     apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_take_def)
     apply(case_tac "d' n")
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
     apply(case_tac a)
     apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e2 c2 q option b)(*strict*)
     apply(simp add: get_configuration_def)
     apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation)
       apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(rule epdaH.der2_is_derivation)
      apply(simp add: F_DPDA_EUML_def epdaH_step_relation_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__LR__configuration_def F_SDPDA_EUME_def)
      apply(clarsimp)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(rule_tac
      x="e2"
      in bexI)
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(simp add: F_SDPDA_EUME__edges_def)
      apply(rule conjI)
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       apply(rule impI)
       apply(rule disjI2)
       apply(simp add: F_SDPDA_EUME__edge_annotation_def)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(rule impI)
      apply(subgoal_tac "False")
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n= derivation_take d n n")
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
      apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
      apply(case_tac "d' n")
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac n d d' e1 e2 c1 c2 q w a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac n d d' e2 c2 q w option b)(*strict*)
      apply(simp add: get_configuration_def)
      apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n= derivation_take d n n")
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
     apply(clarsimp)
     apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
     apply(case_tac "d' n")
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e2 c2 q option b)(*strict*)
     apply(simp add: get_configuration_def)
     apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def der2_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule conjI)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rule epdaH.derivation_initialI)
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(simp add: derivation_append_def)
     apply(erule impE)
      apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
      apply(rule epdaH.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(case_tac "d 0")
      apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q c a)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule ext)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' x= derivation_take d n x")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
    apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def)
    apply(rule conjI)
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_take_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
    apply(case_tac "x-n=Suc 0")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_take_def)
     apply(subgoal_tac "x=Suc n")
      apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__edge_def F_SDPDA_EUME__edge_annotation_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(case_tac "d x")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    apply(rule_tac
      m="x"
      in epdaH.no_some_beyond_maximum_of_domain)
       apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule_tac
      x="derivation_append d' (der2 (the (get_configuration (d' n))) (F_SDPDA_EUME__edge_annotation e2 cons_state_or_state_old cons_state_or_state_old) (F_DPDA_EUME__LR__configuration c2 cons_state_or_state_old)) n"
      in exI)
   apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n = derivation_take d n n")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule_tac
      t="the (get_configuration (d' n))"
      and s="F_DPDA_EUME__LR__configuration c1 cons_state_or_state_old"
      in ssubst)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
    apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_take_def)
    apply(case_tac "d' n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
    apply(case_tac a)
    apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e2 c2 q option b)(*strict*)
    apply(simp add: get_configuration_def)
    apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: F_DPDA_EUML_def epdaH_step_relation_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__LR__configuration_def F_SDPDA_EUME_def)
     apply(clarsimp)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(rule_tac
      x="e2"
      in bexI)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def)
     apply(rule conjI)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(rule impI)
      apply(subgoal_tac "False")
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n= derivation_take d n n")
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
      apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
      apply(case_tac "d' n")
       apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
       apply(force)
      apply(rename_tac n d d' e1 e2 c1 c2 q w a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac n d d' e1 e2 c1 c2 q w a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac n d d' e2 c2 q w option b)(*strict*)
      apply(simp add: get_configuration_def)
      apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(rule impI)
     apply(rule disjI2)
     apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n= derivation_take d n n")
      apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
     apply(simp add: F_SDPDA_EUME__edge_annotation_def)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n= derivation_take d n n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
    apply(clarsimp)
    apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
    apply(case_tac "d' n")
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e2 c2 q option b)(*strict*)
    apply(simp add: get_configuration_def)
    apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def der2_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rule epdaH.derivation_initialI)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
    apply(simp add: derivation_append_def)
    apply(erule impE)
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(case_tac "d 0")
     apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q c a)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule ext)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' x= derivation_take d n x")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
   apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def)
   apply(rule conjI)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
   apply(case_tac "x-n=Suc 0")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
    apply(subgoal_tac "x=Suc n")
     apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__edge_def F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(case_tac "d x")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
   apply(rule_tac
      m="x"
      in epdaH.no_some_beyond_maximum_of_domain)
      apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
      apply(force)
     apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
   apply(force)
  apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
  apply(rule_tac
      x="derivation_append d' (der2 (the (get_configuration (d' n))) (F_SDPDA_EUME__edge_annotation e2 cons_state_or_state_new cons_state_or_state_new) (F_DPDA_EUME__LR__configuration c2 cons_state_or_state_new)) n"
      in exI)
  apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n = derivation_take d n n")
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
  apply(rule_tac
      t="the (get_configuration (d' n))"
      and s="F_DPDA_EUME__LR__configuration c1 cons_state_or_state_new"
      in ssubst)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
   apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_take_def)
   apply(case_tac "d' n")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
   apply(case_tac a)
   apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d d' e2 c2 q option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(simp add: F_DPDA_EUML_def epdaH_step_relation_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__LR__configuration_def F_SDPDA_EUME_def)
    apply(clarsimp)
    apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
    apply(rule_tac
      x="e2"
      in bexI)
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def)
    apply(subgoal_tac "\<lparr>edge_src = cons_state_or_state_new (edge_src e2), edge_event = edge_event e2, edge_pop = edge_pop e2, edge_push = edge_push e2, edge_trg = cons_state_or_state_new (edge_trg e2)\<rparr> = F_SDPDA_EUME__edge_annotation e2 cons_state_or_state_new cons_state_or_state_new")
     apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q w)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' n= derivation_take d n n")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
   apply(clarsimp)
   apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def)
   apply(case_tac "d' n")
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d d' e1 e2 c1 c2 q a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n d d' e1 e2 c1 c2 q a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d d' e2 c2 q option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__configuration_def get_configuration_def der2_def)
  apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(erule impE)
    apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac n d d' e1 e2 c1 c2 q c)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d d' e1 e2 c1 c2 q c a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
  apply(rule ext)
  apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
  apply(subgoal_tac "F_DPDA_EUME__RL__derivation d' x= derivation_take d n x")
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
  apply(thin_tac "F_DPDA_EUME__RL__derivation d' = derivation_take d n")
  apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def)
  apply(rule conjI)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(case_tac "x-n=Suc 0")
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
   apply(subgoal_tac "x=Suc n")
    apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d d' e1 e2 c1 c2 q)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__LR__configuration_def F_DPDA_EUME__RL__edge_def F_SDPDA_EUME__edge_annotation_def )
  apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
  apply(clarsimp)
  apply(case_tac "d x")
   apply(rename_tac n d d' e1 e2 c1 c2 q x)(*strict*)
   apply(force)
  apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
  apply(rule_tac
      m="x"
      in epdaH.no_some_beyond_maximum_of_domain)
     apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
     apply(force)
    apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
    apply(force)
   apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d d' e1 e2 c1 c2 q x a)(*strict*)
  apply(force)
  done

lemma F_DPDA_EUML__preserves__unmarked_language1: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language (F_DPDA_EUML G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_EUML__preserves__pda)
    apply(force)
   apply(force)
  apply(rule_tac
      t="epdaH.unmarked_language G"
      and s="epdaH.finite_unmarked_language G"
      in subst)
   apply(rule epdaH.AX_unmarked_language_finite)
   apply (simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
   apply(simp add: F_DPDA_EUML__SpecInput_def valid_simple_dpda_def valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaH.unmarked_language (F_DPDA_EUML G)"
      and s="epdaH.finite_unmarked_language (F_DPDA_EUML G)"
      in subst)
   apply(rule epdaH.AX_unmarked_language_finite)
   apply(simp add: F_DPDA_EUML__SpecInput_def valid_simple_dpda_def valid_dpda_def valid_pda_def)
  apply(simp add: epdaH.finite_unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d n)(*strict*)
  apply(subgoal_tac "\<exists>d'. epdaH.derivation (F_DPDA_EUML G) d' \<and> F_DPDA_EUME__RL__derivation d' = d \<and> (epdaH.derivation_initial G d \<longrightarrow> epdaH.derivation_initial (F_DPDA_EUML G) d')")
   apply(rename_tac x d n)(*strict*)
   prefer 2
   apply(rule F_DPDA_EUML__preserves__derivation)
     apply(rename_tac x d n)(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_simple_dpda_def valid_dpda_def valid_pda_def)
    apply(rename_tac x d n)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation)
   apply(rename_tac x d n)(*strict*)
   apply(force)
  apply(rename_tac x d n)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n d')(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(rule conjI)
   apply(rename_tac x n d')(*strict*)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac x n d')(*strict*)
    apply(force)
   apply(rename_tac x n d')(*strict*)
   apply(clarsimp)
   apply(rename_tac x n d' c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac x n d')(*strict*)
  apply(rule conjI)
   apply(rename_tac x n d')(*strict*)
   apply(simp add: epdaH_unmarked_effect_def F_DPDA_EUME__RL__derivation_def)
   apply(clarsimp)
   apply(rename_tac n d' i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(case_tac "d' i")
    apply(rename_tac n d' i e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d' i e c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n d' i e c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d' i option b)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac x n d')(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(simp add: maximum_of_domain_def F_DPDA_EUME__RL__derivation_def)
  apply(clarsimp)
  apply(rename_tac x n d' y)(*strict*)
  apply(rule conjI)
   apply(rename_tac x n d' y)(*strict*)
   prefer 2
   apply(case_tac "d'(Suc n)")
    apply(rename_tac x n d' y)(*strict*)
    apply(force)
   apply(rename_tac x n d' y a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac x n d' y a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac x n d' y)(*strict*)
  apply(case_tac "d' n")
   apply(rename_tac x n d' y)(*strict*)
   apply(force)
  apply(rename_tac x n d' y a)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_EUML__preserves__unmarked_language: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> epdaH.unmarked_language G = epdaH.unmarked_language (F_DPDA_EUML G)"
  apply(rule order_antisym)
   apply (metis F_DPDA_EUML__preserves__unmarked_language1)
  apply (metis F_DPDA_EUML__preserves__unmarked_language2)
  done

theorem F_DPDA_EUML__enforces__state_stack_unique_for_marking_states: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> state_stack_unique_for_marking_states Go"
  apply(simp add: F_DPDA_EUML__SpecInput_def F_DPDA_EUML_def Let_def epda_nonstable_states_def state_stack_unique_def )
  apply(simp (no_asm) add: state_stack_unique_for_marking_states_def)
  apply(simp add: F_DPDA_EUML__SpecInput_def F_DPDA_EUML_def Let_def epda_nonstable_states_def state_stack_unique_def )
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule disjE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(simp add: state_stack_unique_for_marking_states_def)
   apply(simp add: F_DPDA_EUML__SpecInput_def F_DPDA_EUML_def Let_def epda_nonstable_states_def state_stack_unique_def )
   apply(erule_tac
      x="(F_DPDA_EUME__RL__derivation d1)"
      in allE)
   apply(erule impE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
     apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(simp add: F_DPDA_EUML__SpecInput_def state_stack_unique_for_marking_states_def F_DPDA_EUML_def Let_def epda_nonstable_states_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(erule_tac
      x="(F_DPDA_EUME__RL__derivation d2)"
      in allE)
   apply(erule impE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
     apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(simp add: F_DPDA_EUML__SpecInput_def state_stack_unique_for_marking_states_def F_DPDA_EUML_def Let_def epda_nonstable_states_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(erule_tac
      x="case e1 of None \<Rightarrow> None | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)"
      in allE)
   apply(erule_tac
      x="case e2 of None \<Rightarrow> None | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)"
      in allE)
   apply(erule_tac
      x="F_DPDA_EUME__RL__configuration c1"
      in allE)
   apply(erule impE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(rule_tac
      x="n1"
      in exI)
    apply(simp add: F_DPDA_EUME__RL__derivation_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(erule_tac
      x="F_DPDA_EUME__RL__configuration c2"
      in allE)
   apply(erule impE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(rule_tac
      x="n2"
      in exI)
    apply(simp add: F_DPDA_EUME__RL__derivation_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(erule impE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(simp add: F_DPDA_EUME__RL__configuration_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(erule impE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(simp add: F_DPDA_EUME__RL__configuration_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(simp add: state_stack_unique_for_stable_states_def)
  apply(simp add: F_DPDA_EUML__SpecInput_def F_DPDA_EUML_def Let_def epda_nonstable_states_def state_stack_unique_def )
  apply(erule_tac
      x="(F_DPDA_EUME__RL__derivation d1)"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(simp add: F_DPDA_EUML__SpecInput_def state_stack_unique_for_marking_states_def F_DPDA_EUML_def Let_def epda_nonstable_states_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(erule_tac
      x="(F_DPDA_EUME__RL__derivation d2)"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(simp add: F_DPDA_EUML__SpecInput_def state_stack_unique_for_marking_states_def F_DPDA_EUML_def Let_def epda_nonstable_states_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(erule_tac
      x="case e1 of None \<Rightarrow> None | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)"
      in allE)
  apply(erule_tac
      x="case e2 of None \<Rightarrow> None | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)"
      in allE)
  apply(erule_tac
      x="F_DPDA_EUME__RL__configuration c1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(rule_tac
      x="n1"
      in exI)
   apply(simp add: F_DPDA_EUME__RL__derivation_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(erule_tac
      x="F_DPDA_EUME__RL__configuration c2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(rule_tac
      x="n2"
      in exI)
   apply(simp add: F_DPDA_EUME__RL__derivation_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__configuration_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
   apply(simp add: F_SDPDA_EUME_def)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
   apply(simp add: F_SDPDA_EUME__edges_def)
   apply(case_tac "FB_executing_edge e")
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
    apply(simp add: FB_executing_edge_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e \<in> epda_marking G")
    apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
    apply(clarsimp)
    prefer 2
    apply(clarsimp)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 e)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 x)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__configuration_def)
  done

theorem F_DPDA_EUML__preserves__no_livelock: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> \<not> epdaH_livelock Go"
  apply(simp add: F_DPDA_EUML__SpecInput_def epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(rule ccontr)
  apply(clarsimp)
  apply(erule_tac
      x="(F_DPDA_EUME__RL__derivation d)"
      in allE)
  apply(erule impE)
   apply(rename_tac d N)(*strict*)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d N)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d N)(*strict*)
   apply(force)
  apply(rename_tac d N)(*strict*)
  apply(erule disjE)
   apply(rename_tac d N)(*strict*)
   apply(clarsimp)
   apply(rename_tac d N n)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__derivation_def)
   apply(erule_tac
      P="\<lambda>n. \<exists>y. d n = Some y"
      and x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac d N n y)(*strict*)
   apply(case_tac y)
   apply(rename_tac d N n y option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="N"
      and P="\<lambda>N. \<exists>n\<ge>N. epdaH_conf_history (the (get_configuration (F_DPDA_EUME__RL__derivation d n))) \<noteq> epdaH_conf_history (the (get_configuration (F_DPDA_EUME__RL__derivation d N)))"
      in allE)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n)(*strict*)
  apply(erule_tac
      x="n"
      and P="\<lambda>n. N \<le> n \<longrightarrow> epdaH_conf_history (the (get_configuration (d n))) = epdaH_conf_history (the (get_configuration (d N)))"
      in allE)
  apply(rename_tac d N n)(*strict*)
  apply(clarsimp)
  apply(erule_tac x="n" in allE')
  apply(erule_tac
      x="N"
      in allE)
  apply(clarsimp)
  apply(rename_tac d N n y ya)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__derivation_def)
  apply(case_tac y)
  apply(rename_tac d N n y ya option b)(*strict*)
  apply(case_tac ya)
  apply(rename_tac d N n y ya option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n option b optiona ba)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: F_DPDA_EUME__RL__configuration_def)
  done

lemma F_DPDA_EUML__preserves__determinism: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible Go"
  apply(simp add: F_DPDA_EUML_def Let_def)
  apply(rule epda_marking_states_change_preserves_determinism)
  apply(rule F_SDPDA_EUME__preserves_DPDA)
  apply(simp add: F_DPDA_EUML__SpecInput_def)
  done

lemma F_DPDA_EUML__preserves__dpda: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> valid_dpda Go"
  apply(simp add: valid_dpda_def)
  apply(rule context_conjI)
   apply(rule F_DPDA_EUML__preserves__pda)
    apply(force)
   apply(force)
  apply(rule F_DPDA_EUML__preserves__determinism)
   apply(force)
  apply(force)
  done

lemma F_DPDA_EUML__no_leave_new_states_without_executing: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> R = F_DPDA_EUML G 
  \<Longrightarrow> valid_dpda R 
  \<Longrightarrow> epdaH.derivation R d 
  \<Longrightarrow> epdaH.belongs R d 
  \<Longrightarrow> d 0 = Some (pair None c) 
  \<Longrightarrow> d n = Some (pair e c') 
  \<Longrightarrow> epdaH_conf_history c' = epdaH_conf_history c 
  \<Longrightarrow> epdaH_conf_state c = cons_state_or_state_new q 
  \<Longrightarrow> \<exists>q'. epdaH_conf_state c' = cons_state_or_state_new q'"
  apply(induct n arbitrary: e c')
   apply(rename_tac e c')(*strict*)
   apply(clarsimp)
  apply(rename_tac n e c')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e c')(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e c')(*strict*)
     apply(force)
    apply(rename_tac n e c')(*strict*)
    apply(force)
   apply(rename_tac n e c')(*strict*)
   apply(force)
  apply(rename_tac n e c')(*strict*)
  apply(clarsimp)
  apply(rename_tac n c' e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n c' e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_EUML G"
      and d="d"
      and n="0"
      and m="n"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac n c' e1 e2 c1)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac n c' e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac n c' e1 e2 c1)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def epda_effects_def)
    apply(rename_tac n c' e1 e2 c1)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac n c' e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac n c' e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac n c' e1 e2 c1)(*strict*)
   apply(simp add: get_configuration_def epda_effects_def)
  apply(rename_tac n c' e1 e2 c1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n c' e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_EUML G"
      and d="d"
      and n="n"
      and m="Suc 0"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac n c' e1 e2 c1)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac n c' e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac n c' e1 e2 c1)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac n c' e1 e2 c1 h)(*strict*)
     apply(simp add: get_configuration_def epda_effects_def)
    apply(rename_tac n c' e1 e2 c1)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac n c' e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac n c' e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac n c' e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c' e1 e2 c1 h)(*strict*)
   apply(simp add: get_configuration_def epda_effects_def)
  apply(rename_tac n c' e1 e2 c1)(*strict*)
  apply(clarify)
  apply(rename_tac n c' e1 e2 c1 h ha)(*strict*)
  apply(subgoal_tac "h = [] \<and> ha = []")
   apply(rename_tac n c' e1 e2 c1 h ha)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n c' e1 e2 c1 h ha)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c' e1 e2 c1 q')(*strict*)
  apply(thin_tac "[] \<in> epda_effects (F_DPDA_EUML G)")
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c' e1 e2 c1 q' w)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n c' e1 e2 c1 q' w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c' e1 c1 q' w edge_event edge_pop edge_push)(*strict*)
  apply(case_tac c')
  apply(rename_tac n c' e1 c1 q' w edge_event edge_pop edge_push epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 c1 q' w edge_event edge_pop edge_push epdaH_conf_statea)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n e1 c1 q' w edge_event edge_pop edge_push epdaH_conf_statea epdaH_conf_stateaa epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 q' w edge_event edge_pop edge_push epdaH_conf_statea)(*strict*)
  apply(case_tac edge_event)
   apply(rename_tac n e1 q' w edge_event edge_pop edge_push epdaH_conf_statea)(*strict*)
   prefer 2
   apply(rename_tac n e1 q' w edge_event edge_pop edge_push epdaH_conf_statea a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac n e1 q' w edge_event edge_pop edge_push epdaH_conf_statea)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea)(*strict*)
  apply(simp add: F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_SDPDA_EUME__edges_def FB_executing_edge_def)
  apply(clarsimp)
  apply(erule disjE)+
   apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac n e1 q' w edge_popa edge_pusha epdaH_conf_statea)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea x)(*strict*)
  apply(erule disjE)+
   apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea x)(*strict*)
  apply(case_tac "edge_src x \<in> epda_marking G")
   apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac n e1 q' w edge_pop edge_push epdaH_conf_statea x)(*strict*)
  apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  done

lemma completing_derivation_exists_for_new_states: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> R = F_DPDA_EUML G 
  \<Longrightarrow> c \<in> epdaH.get_accessible_configurations R 
  \<Longrightarrow> epdaH_conf_state c = cons_state_or_state_new q 
  \<Longrightarrow> \<exists>d n e c' q'. epdaH.derivation R d \<and> d 0 = Some (pair None c) \<and> d n = Some (pair e c') \<and> epdaH_conf_history c' = epdaH_conf_history c \<and> epdaH_conf_state c' = cons_state_or_state_new q' \<and> cons_state_or_state_new q' \<in> epda_marking R"
  apply(subgoal_tac "valid_dpda R")
   prefer 2
   apply(rule F_DPDA_EUML__preserves__dpda)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule stable_configuration_can_be_reached)
     apply(force)
    apply(rule F_DPDA_EUML__preserves__no_livelock)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d n e c')(*strict*)
  apply(case_tac c)
  apply(rename_tac d n e c' epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e c' epdaH_conf_stack)(*strict*)
  apply(rename_tac s)
  apply(rename_tac d n e c' s)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(case_tac c')
  apply(rename_tac d n e c' s epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e s epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac d n e s q2 h2 s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n e s q2 h2 s2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="n"
      in F_DPDA_EUML__no_leave_new_states_without_executing)
           apply(rename_tac d n e s q2 h2 s2)(*strict*)
           apply(force)
          apply(rename_tac d n e s q2 h2 s2)(*strict*)
          apply(force)
         apply(rename_tac d n e s q2 h2 s2)(*strict*)
         apply(force)
        apply(rename_tac d n e s q2 h2 s2)(*strict*)
        apply(force)
       apply(rename_tac d n e s q2 h2 s2)(*strict*)
       apply(force)
      apply(rename_tac d n e s q2 h2 s2)(*strict*)
      apply(force)
     apply(rename_tac d n e s q2 h2 s2)(*strict*)
     apply(force)
    apply(rename_tac d n e s q2 h2 s2)(*strict*)
    apply(force)
   apply(rename_tac d n e s q2 h2 s2)(*strict*)
   apply(force)
  apply(rename_tac d n e s q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e s h2 s2 q')(*strict*)
  apply(subgoal_tac "cons_state_or_state_new q' \<notin> epda_nonstable_states (epda_delta (F_SDPDA_EUME G))")
   apply(rename_tac d n e s h2 s2 q')(*strict*)
   apply(simp add: F_DPDA_EUML_def Let_def)
   apply(rule disjI2)
   apply(rule inMap)
   apply(rule_tac
      x="q'"
      in bexI)
    apply(rename_tac d n e s h2 s2 q')(*strict*)
    apply(force)
   apply(rename_tac d n e s h2 s2 q')(*strict*)
   apply(subgoal_tac "\<lparr>epdaH_conf_state = cons_state_or_state_new q', epdaH_conf_history = h2, epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations (F_DPDA_EUML G)")
    apply(rename_tac d n e s h2 s2 q')(*strict*)
    apply(simp add: epdaH_configurations_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def)
    apply(erule disjE)
     apply(rename_tac d n e s h2 s2 q')(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e s h2 s2 q')(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e s h2 s2 q')(*strict*)
   apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
    apply(rename_tac d n e s h2 s2 q')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d n e s h2 s2 q')(*strict*)
   apply(simp add: F_DPDA_EUML_def Let_def)
  apply(rename_tac d n e s h2 s2 q')(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_EUML__SpecInput_def some_edge_applicable_def)
  apply(clarsimp)
  apply(simp add: epdaH.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d n e s h2 s2 q' da i)(*strict*)
  apply(case_tac "da i")
   apply(rename_tac d n e s h2 s2 q' da i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d n e s h2 s2 q' da i a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac d n e s h2 s2 q' da i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e s h2 s2 q' da i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
  apply(erule_tac
      x="F_DPDA_EUME__RL__derivation (derivation_append da d i)"
      in allE)
  apply(erule impE)
   apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
    apply(force)
   apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
   apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n ea s h2 s2 q' da i e)(*strict*)
  apply(erule_tac
      x="case ea of None \<Rightarrow> (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)) | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)"
      in allE)
  apply(simp add: epda_nonstable_states_def)
  apply(clarsimp)
  apply(rename_tac d n ea s h2 s2 q' da i e eb)(*strict*)
  apply(subgoal_tac "\<exists>x\<in> epda_delta G. eb \<in> F_SDPDA_EUME__edges x (epda_marking G)")
   apply(rename_tac d n ea s h2 s2 q' da i e eb)(*strict*)
   prefer 2
   apply(simp add: F_SDPDA_EUME_def)
  apply(rename_tac d n ea s h2 s2 q' da i e eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule_tac
      x="F_DPDA_EUME__RL__configuration\<lparr>epdaH_conf_state = cons_state_or_state_new q', epdaH_conf_history = h2, epdaH_conf_stack = s2\<rparr>"
      in allE)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
  apply(erule impE)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(rule_tac
      x="i+n"
      in exI)
   apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rule conjI)
    apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(clarsimp)
   apply(case_tac ea)
    apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n s h2 s2 q' da i e eb x)(*strict*)
    apply(case_tac e)
     apply(rename_tac d n s h2 s2 q' da i e eb x)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n s h2 s2 q' da i e eb x a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n s h2 s2 q' da i eb x a)(*strict*)
    apply(case_tac n)
     apply(rename_tac d n s h2 s2 q' da i eb x a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n s h2 s2 q' da i eb x a nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
     prefer 2
     apply(rule_tac
      g="d"
      and n="Suc nat"
      and m="Suc nat"
      in epdaH.pre_some_position_is_some_position_prime)
        apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
       apply(force)
      apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
      apply(force)
     apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
     apply(force)
    apply(rename_tac d s h2 s2 q' da i eb x a nat)(*strict*)
    apply(force)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
  apply(erule impE)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
  apply(erule impE)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edges_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(case_tac "FB_executing_edge x")
    apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
    apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n ea s h2 s2 q' da i e x)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(clarsimp)
   apply(erule disjE)+
    apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(case_tac "edge_src x \<in> epda_marking G")
    apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n ea s h2 s2 q' da i e x)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
  apply(subgoal_tac "edge_event eb = None \<longrightarrow> edge_event x = None")
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
   prefer 2
   apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(case_tac "FB_executing_edge x")
    apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
    apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n ea s h2 s2 q' da i e x ec xa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
   apply(clarsimp)
   apply(erule disjE)+
    apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
   apply(case_tac "edge_src x \<in> epda_marking G")
    apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n ea s h2 s2 q' da i e x ec xa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
   apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_epda_step_label G ec")
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(case_tac ec)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x xa edge_srca edge_pop edge_push edge_trg)(*strict*)
   apply(rename_tac qs po pu qt)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt)(*strict*)
   apply(subgoal_tac "\<exists>x. po = [x]")
    apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>edge_src = qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
     apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt)(*strict*)
     prefer 2
     apply(simp add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def)
    apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt)(*strict*)
    apply(clarsimp)
    apply(case_tac po)
     apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs pu qt xb)(*strict*)
   apply(subgoal_tac "prefix [xb] s2")
    apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs pu qt xb)(*strict*)
    prefer 2
    apply(simp add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def prefix_def)
    apply(clarsimp)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x xa qs pu qt xb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac d n ea s h2 q' da i e eb x xa qs pu qt xb c)(*strict*)
   apply(subgoal_tac "qs=q'")
    apply(rename_tac d n ea s h2 q' da i e eb x xa qs pu qt xb c)(*strict*)
    prefer 2
    apply(simp add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def prefix_def)
   apply(rename_tac d n ea s h2 q' da i e eb x xa qs pu qt xb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n ea s h2 q' da i e eb x xa pu qt xb c)(*strict*)
   apply(erule_tac
      x="\<lparr>edge_src = cons_state_or_state_new q', edge_event = None, edge_pop = [xb], edge_push = pu, edge_trg = cons_state_or_state_new qt\<rparr>"
      in allE)
   apply(erule impE)
    apply(rename_tac d n ea s h2 q' da i e eb x xa pu qt xb c)(*strict*)
    apply(rule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new qt, epdaH_conf_history = h2, epdaH_conf_stack = pu @ c\<rparr>"
      in exI)
    apply(rename_tac d n ea s h2 q' da i e eb x xa pu qt xb c)(*strict*)
    apply(simp (no_asm) add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def prefix_def option_to_list_def)
    apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def)
    apply(rule_tac
      x="\<lparr>edge_src = q', edge_event = None, edge_pop = [xb], edge_push = pu, edge_trg = qt\<rparr>"
      in bexI)
     apply(rename_tac d n ea s h2 q' da i e eb x xa pu qt xb c)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def)
    apply(rename_tac d n ea s h2 q' da i e eb x xa pu qt xb c)(*strict*)
    apply(simp add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def prefix_def option_to_list_def)
   apply(rename_tac d n ea s h2 q' da i e eb x xa pu qt xb c)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x="ec"
      and P="\<lambda>ec. valid_epda_step_label G ec"
      in ballE)
   apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
   apply(force)
  apply(rename_tac d n ea s h2 s2 q' da i e eb x ec xa)(*strict*)
  apply(simp add: epdaH_step_relation_def F_DPDA_EUME__RL__configuration_def prefix_def option_to_list_def)
  done

lemma F_DPDA_EUML__equal__finite_marked_language1: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> valid_dpda (F_DPDA_EUML G) 
  \<Longrightarrow> epdaH.finite_marked_language G \<subseteq> epdaH.finite_marked_language (F_DPDA_EUML G)"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaH.finite_marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d xa)(*strict*)
  apply(thin_tac "epdaH_marking_condition G d")
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac d xa i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d xa i e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d xa i e q h s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d xa i e q h s)(*strict*)
   prefer 2
   apply(rule F_DPDA_EUML__preserves__derivation)
     apply(rename_tac d xa i e q h s)(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
     apply(force)
    apply(rename_tac d xa i e q h s)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(force)
   apply(rename_tac d xa i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d xa i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q h s d')(*strict*)
  apply(subgoal_tac "\<exists>e c. d' i = Some (pair e c)")
   apply(rename_tac xa i e q h s d')(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EUME__RL__derivation_def)
   apply(case_tac "d' i")
    apply(rename_tac xa i e q h s d')(*strict*)
    apply(force)
   apply(rename_tac xa i e q h s d' a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac xa i e q h s d' a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa i e q h s d')(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q h s d' ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa i e q h s d' ea c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q h s d' ea epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac qx hx sx)
  apply(rename_tac xa i e q h s d' ea qx hx sx)(*strict*)
  apply(subgoal_tac "hx=h \<and> sx = s")
   apply(rename_tac xa i e q h s d' ea qx hx sx)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac xa i e q h s d' ea qx hx sx)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q h s d' ea qx)(*strict*)
  apply(case_tac qx)
   apply(rename_tac xa i e q h s d' ea qx qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa i e q h s d' ea qa)(*strict*)
   apply(case_tac "cons_state_or_state_old qa \<notin> epda_nonstable_states (\<Union>x\<in> epda_delta G. F_SDPDA_EUME__edges x (epda_marking G))")
    apply(rename_tac xa i e q h s d' ea qa)(*strict*)
    apply(rule_tac
      x="derivation_take d' i"
      in exI)
    apply(rule conjI)
     apply(rename_tac xa i e q h s d' ea qa)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac xa i e q h s d' ea qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac xa i e q h s d' ea qa)(*strict*)
     apply(rule_tac
      x="i"
      in exI)
     apply(simp add: epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
    apply(rename_tac xa i e q h s d' ea qa)(*strict*)
    apply(simp add: epdaH_marking_condition_def)
    apply(rule conjI)
     apply(rename_tac xa i e q h s d' ea qa)(*strict*)
     apply(rule_tac
      x="i"
      in exI)
     apply(simp add: epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
    apply(rename_tac xa i e q h s d' ea qa)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac xa i e q h s d' ea qa)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(rename_tac xa i e q h s d' ea qx qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa i e q h s d' ea qa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac xa i e q h s d' ea qa)(*strict*)
    prefer 2
    apply(rule_tac
      c="\<lparr>epdaH_conf_state = cons_state_or_state_new qa, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in completing_derivation_exists_for_new_states)
       apply(rename_tac xa i e q h s d' ea qa)(*strict*)
       apply(force)
      apply(rename_tac xa i e q h s d' ea qa)(*strict*)
      apply(force)
     apply(rename_tac xa i e q h s d' ea qa)(*strict*)
     apply(simp add: epdaH.get_accessible_configurations_def)
     apply(rule_tac
      x="d'"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="i"
      in exI)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac xa i e q h s d' ea qa)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac xa i e q h s d' ea qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
   apply(rule_tac
      x="derivation_append d' (derivation_take d n) i"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
      apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
   apply(rule context_conjI)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(rule_tac
      x="i+n"
      in exI)
    apply(rule_tac
      x="if n=0 then ea else eb"
      in exI)
    apply(simp add: derivation_append_def derivation_take_def)
    apply(rule conjI)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
     apply(clarsimp)
     apply(rename_tac xa i e q s d' ea qa d c' q')(*strict*)
     apply(simp add: epdaH_marking_configurations_def)
     apply(rule epdaH.belongs_configurations)
      apply(rename_tac xa i e q s d' ea qa d c' q')(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac xa i e q s d' ea qa d c' q')(*strict*)
       apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac xa i e q s d' ea qa d c' q')(*strict*)
      apply(force)
     apply(rename_tac xa i e q s d' ea qa d c' q')(*strict*)
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
     apply(simp add: epdaH_marking_configurations_def)
     apply(rule_tac
      d="d"
      and i="n"
      in epdaH.belongs_configurations)
      apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
      apply(rule epdaH.derivation_belongs)
         apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
         apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
        apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
        apply(clarsimp)
        apply(force)
       apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
       apply(rule_tac
      d="d'"
      and i="i"
      in epdaH.belongs_configurations)
        apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
        apply(rule epdaH.derivation_initial_belongs)
         apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
         apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
        apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
        apply(force)
       apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
       apply(force)
      apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
      apply(clarsimp)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(clarsimp)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' j c'event)(*strict*)
    apply(subgoal_tac "j\<le>n+i")
     apply(rename_tac xa i e q s d' ea qa d n eb c' q' j c'event)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' j c'event)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
   apply(rule conjI)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
    apply(simp add: epdaH_marking_condition_def)
    apply(rule_tac
      x="i+n"
      in exI)
    apply(clarsimp)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
    apply(rule_tac
      x="if n=0 then ea else eb"
      in exI)
    apply(simp add: derivation_append_def derivation_take_def)
    apply(rule conjI)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa i e q s d' ea d q' ia ec c)(*strict*)
     apply(simp add: epdaH_marking_configurations_def)
     apply(rule epdaH.belongs_configurations)
      apply(rename_tac xa i e q s d' ea d q' ia ec c)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac xa i e q s d' ea d q' ia ec c)(*strict*)
       apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac xa i e q s d' ea d q' ia ec c)(*strict*)
      apply(force)
     apply(rename_tac xa i e q s d' ea d q' ia ec c)(*strict*)
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
     apply(simp add: epdaH_marking_configurations_def)
     apply(rule_tac
      d="d"
      and i="n"
      in epdaH.belongs_configurations)
      apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
      apply(rule epdaH.derivation_belongs)
         apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
         apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
        apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
        apply(clarsimp)
        apply(force)
       apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
       apply(rule_tac
      d="d'"
      and i="i"
      in epdaH.belongs_configurations)
        apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
        apply(rule epdaH.derivation_initial_belongs)
         apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
         apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
        apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
        apply(force)
       apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
       apply(force)
      apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
      apply(clarsimp)
     apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c j c'event)(*strict*)
    apply(subgoal_tac "j\<le>n+i")
     apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c j c'event)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa i e q s d' ea qa d n eb c' q' ia ec c j c'event)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa i e q s d' ea qa d n eb c' q')(*strict*)
   apply(rule_tac
      x="i+n"
      in exI)
   apply(simp add: maximum_of_domain_def derivation_append_def derivation_take_def)
  apply(rename_tac xa i e q h s d' ea qa)(*strict*)
  apply(simp add: epda_nonstable_states_def)
  apply(clarsimp)
  apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
  apply(subgoal_tac "\<exists>x a. epdaH_step_relation G \<lparr>epdaH_conf_state = qa, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr> a x \<and> edge_event a = None")
   apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EUML__SpecInput_def some_edge_applicable_def)
   apply(clarsimp)
   apply(erule_tac
      x="F_DPDA_EUME__RL__derivation d'"
      in allE)
   apply(erule impE)
    apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
    apply(force)
   apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="a"
      in allE)
   apply(erule_tac
      x="\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in allE)
   apply(erule impE)
    apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
   apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
   apply(erule impE)
    apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
   apply(erule impE)
    apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_EUME__edges_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def)
    apply(clarsimp)
    apply(rename_tac xa i q h s d' ea a eb)(*strict*)
    apply(case_tac "FB_executing_edge a")
     apply(rename_tac xa i q h s d' ea a eb)(*strict*)
     apply(simp add: FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
     apply(erule disjE)+
      apply(rename_tac xa i q h s d' ea a eb)(*strict*)
      apply(simp add: FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)+
    apply(rename_tac xa i q h s d' ea a eb)(*strict*)
    apply(erule disjE)+
     apply(rename_tac xa i q h s d' ea a eb)(*strict*)
     apply(simp add: FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)+
    apply(rename_tac xa i q h s d' ea a eb)(*strict*)
    apply(case_tac "edge_src a \<in> epda_marking G")
     apply(rename_tac xa i q h s d' ea a eb)(*strict*)
     apply(simp add: FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)+
   apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa i q h s d' ea a eb ec x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule_tac
      x="ec"
      in exI)
   apply(clarsimp)
   apply(rename_tac xa i q h s d' ea a eb ec x y)(*strict*)
   apply(simp add: F_SDPDA_EUME__edges_def epdaH_step_relation_def FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)+
   apply(clarsimp)
   apply(rename_tac xa i h d' ea a eb ec x y w)(*strict*)
   apply(erule disjE)+
    apply(rename_tac xa i h d' ea a eb ec x y w)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def epdaH_step_relation_def FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
   apply(rename_tac xa i h d' ea a eb ec x y w)(*strict*)
   apply(simp add: F_SDPDA_EUME__edges_def epdaH_step_relation_def FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
  apply(rename_tac xa i e q h s d' ea qa a eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q h s d' ea qa a eb x aa)(*strict*)
  apply(simp (no_asm_use) add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa i e q h d' ea a eb x aa w)(*strict*)
  apply(case_tac aa)
  apply(rename_tac xa i e q h d' ea a eb x aa w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q h d' ea a eb x w edge_srca edge_pop edge_push)(*strict*)
  apply(rename_tac qs po pu)
  apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
  apply(subgoal_tac "epdaH_step_relation (F_DPDA_EUML G) \<lparr>epdaH_conf_state = cons_state_or_state_old qs, epdaH_conf_history = h, epdaH_conf_stack = po @ w\<rparr> \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> \<lparr>epdaH_conf_state = cons_state_or_state_new(epdaH_conf_state x), epdaH_conf_history = h, epdaH_conf_stack = pu @ w\<rparr>")
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def option_to_list_def)
   apply(simp add: epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
   apply(rule_tac
      x="\<lparr>edge_src = q, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state x\<rparr>"
      in bexI)
    apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
    apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
    apply(simp add: F_SDPDA_EUME__edges_def epdaH_step_relation_def FB_executing_edge_def F_SDPDA_EUME__edge_annotation_def epdaH_marking_condition_def derivation_take_def epdaH_marking_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def)
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   apply(force)
  apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
  apply(subgoal_tac "epdaH.derivation_initial (F_DPDA_EUML G) (derivation_append d' (der2 \<lparr>epdaH_conf_state = cons_state_or_state_old qs, epdaH_conf_history = h, epdaH_conf_stack = po @ w\<rparr> \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> \<lparr>epdaH_conf_state = cons_state_or_state_new (epdaH_conf_state x), epdaH_conf_history = h, epdaH_conf_stack = pu @ w\<rparr>) i)")
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   prefer 2
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
    apply(force)
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
     apply(force)
    apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(force)
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def der2_def derivation_append_def derivation_take_def)
  apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   prefer 2
   apply(rule_tac
      c="\<lparr>epdaH_conf_state = cons_state_or_state_new (epdaH_conf_state x), epdaH_conf_history = h, epdaH_conf_stack = pu @ w\<rparr>"
      in completing_derivation_exists_for_new_states)
      apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
      apply(force)
     apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
     apply(force)
    apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
    apply(simp add: epdaH.get_accessible_configurations_def)
    apply(rule_tac
      x="derivation_append d' (der2 \<lparr>epdaH_conf_state = cons_state_or_state_old qs, epdaH_conf_history = h, epdaH_conf_stack = po @ w\<rparr> \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> \<lparr>epdaH_conf_state = cons_state_or_state_new (epdaH_conf_state x), epdaH_conf_history = h, epdaH_conf_stack = pu @ w\<rparr>) i"
      in exI)
    apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="Suc i"
      in exI)
    apply(simp add: get_configuration_def derivation_append_def der2_def)
   apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac xa i e q h d' ea a eb x w qs po pu)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_append d' (der2 \<lparr>epdaH_conf_state = cons_state_or_state_old qs, epdaH_conf_history = epdaH_conf_history c', epdaH_conf_stack = po @ w\<rparr> \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> \<lparr>epdaH_conf_state = cons_state_or_state_new (epdaH_conf_state x), epdaH_conf_history = epdaH_conf_history c', epdaH_conf_stack = pu @ w\<rparr>) i) (derivation_take d n) (Suc i)"
      in exI)
  apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
  apply(rule conjI)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
    apply(force)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(simp add: derivation_take_def derivation_append_def der2_def)
  apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(rule_tac
      x="Suc i+n"
      in exI)
   apply(rule_tac
      x="if n=0 then Some \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> else ec"
      in exI)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
    apply(simp add: der2_def derivation_append_def derivation_take_def)
    apply(clarsimp)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(rule conjI)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
    apply(simp add: epdaH_marking_configurations_def)
    apply(rule_tac
      d="d"
      and i="n"
      in epdaH.belongs_configurations)
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
     apply(rule epdaH.derivation_belongs)
        apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
        apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
       apply(clarsimp)
       apply(force)
      apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
      apply(rule_tac
      d="derivation_append d' (der2 \<lparr>epdaH_conf_state = cons_state_or_state_old qs, epdaH_conf_history = epdaH_conf_history c', epdaH_conf_stack = po @ w\<rparr> \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> \<lparr>epdaH_conf_state = cons_state_or_state_new (epdaH_conf_state x), epdaH_conf_history = epdaH_conf_history c', epdaH_conf_stack = pu @ w\<rparr>) i"
      and i="Suc i"
      in epdaH.belongs_configurations)
       apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
        apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
       apply(force)
      apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
      apply(simp add: der2_def derivation_append_def derivation_take_def)
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
     apply(force)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(rule conjI)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
    apply(clarsimp)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
   apply(clarsimp)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' j e' c'event)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_take_def)
   apply(case_tac "j-Suc i\<le>n")
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' j e' c'event)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' j c'event)(*strict*)
    apply(subgoal_tac "j\<le>n+Suc i")
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' j c'event)(*strict*)
     apply(force)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' j c'event)(*strict*)
    apply(force)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' j e' c'event)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q')(*strict*)
  apply(clarsimp)
  apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
   apply(simp add: epdaH_marking_condition_def)
   apply(rule_tac
      x="Suc i+n"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="if n=0 then Some \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> else ec"
      in exI)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
    apply(simp add: der2_def derivation_append_def derivation_take_def)
    apply(clarsimp)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
    apply(simp add: epdaH_marking_configurations_def)
    apply(rule_tac
      d="d"
      and i="n"
      in epdaH.belongs_configurations)
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
     apply(rule epdaH.derivation_belongs)
        apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
        apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
       apply(clarsimp)
       apply(force)
      apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
      apply(rule_tac
      d="derivation_append d' (der2 \<lparr>epdaH_conf_state = cons_state_or_state_old qs, epdaH_conf_history = epdaH_conf_history c', epdaH_conf_stack = po @ w\<rparr> \<lparr>edge_src = cons_state_or_state_old qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_state_or_state_new (epdaH_conf_state x)\<rparr> \<lparr>epdaH_conf_state = cons_state_or_state_new (epdaH_conf_state x), epdaH_conf_history = epdaH_conf_history c', epdaH_conf_stack = pu @ w\<rparr>) i"
      and i="Suc i"
      in epdaH.belongs_configurations)
       apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
        apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
       apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
       apply(force)
      apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
      apply(simp add: der2_def derivation_append_def derivation_take_def)
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
     apply(force)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c j e' c'event)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_take_def)
   apply(case_tac "j-Suc i\<le>n")
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c j e' c'event)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c j c'event)(*strict*)
    apply(subgoal_tac "j\<le>n+Suc i")
     apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c j c'event)(*strict*)
     apply(force)
    apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c j c'event)(*strict*)
    apply(force)
   apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c j e' c'event)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa i e q d' ea a eb x w qs po pu d n ec c' q' ia ed c)(*strict*)
  apply(rule_tac
      x="Suc i+n"
      in exI)
  apply(simp add: maximum_of_domain_def der2_def derivation_append_def derivation_take_def)
  done

lemma F_DPDA_EUML__preserves__history_in_new_states: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> epdaH.derivation (F_DPDA_EUML G) d 
  \<Longrightarrow> epdaH.belongs (F_DPDA_EUML G) d 
  \<Longrightarrow> d n = Some (pair e1 c1) 
  \<Longrightarrow> d (n + m) = Some (pair e2 c2) 
  \<Longrightarrow> \<forall>k. n \<le> k \<and> k \<le> n + m \<longrightarrow> (\<forall>e c q. d k = Some (pair e c) \<longrightarrow> epdaH_conf_state c \<noteq> cons_state_or_state_old q) 
  \<Longrightarrow> epdaH_conf_history c1 = epdaH_conf_history c2"
  apply(induct m arbitrary: e2 c2)
   apply(rename_tac e2 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac m e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac m e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="n+m"
      and m="Suc (n+m)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac m e2 c2)(*strict*)
     apply(force)
    apply(rename_tac m e2 c2)(*strict*)
    apply(force)
   apply(rename_tac m e2 c2)(*strict*)
   apply(force)
  apply(rename_tac m e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac m c2 e1a e2a c1a)(*strict*)
   apply(clarsimp)
   apply(rename_tac m c2 e1a e2a c1a k e c q)(*strict*)
   apply(force)
  apply(rename_tac m c2 e1a e2a c1a)(*strict*)
  apply(subgoal_tac "epdaH_conf_history c2 = epdaH_conf_history c1a")
   apply(rename_tac m c2 e1a e2a c1a)(*strict*)
   apply(force)
  apply(rename_tac m c2 e1a e2a c1a)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(erule_tac x="n+m" in allE')
  apply(erule_tac
      x="n+m+Suc 0"
      in allE)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a w)(*strict*)
  apply(case_tac "edge_event e2a")
   apply(rename_tac m c2 e1a e2a c1a w)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(rename_tac m c2 e1a e2a c1a w a)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(case_tac c1a)
  apply(rename_tac m c2 e1a e2a c1a w a epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(case_tac c2)
  apply(rename_tac m c2 e1a e2a c1a w a epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1a e2a w a)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac m e1a e2a w a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1a w a edge_src edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs po pu qt)
  apply(rename_tac m e1a w a qs po pu qt)(*strict*)
  apply(case_tac qs)
   apply(rename_tac m e1a w a qs po pu qt q)(*strict*)
   apply(force)
  apply(rename_tac m e1a w a qs po pu qt q)(*strict*)
  apply(case_tac qt)
   apply(rename_tac m e1a w a qs po pu qt q qa)(*strict*)
   apply(force)
  apply(rename_tac m e1a w a qs po pu qt q qa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1a w a po pu q qa)(*strict*)
  apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac m e1a w a po pu q qa x)(*strict*)
  apply(case_tac "edge_src x \<in> epda_marking G")
   apply(rename_tac m e1a w a po pu q qa x)(*strict*)
   apply(clarsimp)
   apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
  apply(rename_tac m e1a w a po pu q qa x)(*strict*)
  apply(clarsimp)
  apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
  done

lemma F_DPDA_EUML__equal__finite_marked_language2: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> valid_dpda (F_DPDA_EUML G) 
  \<Longrightarrow> epdaH.finite_marked_language (F_DPDA_EUML G) \<subseteq> epdaH.finite_marked_language G"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaH.finite_marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d xa)(*strict*)
  apply(thin_tac "epdaH_marking_condition (F_DPDA_EUML G) d")
  apply(subgoal_tac "\<exists>d. epdaH.derivation_initial G d \<and> x \<in> epdaH_marked_effect G d")
   apply(rename_tac x d xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d xa da)(*strict*)
   apply(simp add: epdaH_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac d xa da i ia e ea c ca)(*strict*)
   apply(rule_tac
      x="derivation_take da ia"
      in exI)
   apply(rule conjI)
    apply(rename_tac d xa da i ia e ea c ca)(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d xa da i ia e ea c ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac d xa da i ia e ea c ca)(*strict*)
    apply(simp add: derivation_take_def)
    apply(rule_tac
      x="ia"
      in exI)
    apply(clarsimp)
   apply(rename_tac d xa da i ia e ea c ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac d xa da i ia e ea c ca)(*strict*)
    apply(simp add: epdaH_marking_condition_def)
    apply(rule_tac
      x="ia"
      in exI)
    apply(simp add: derivation_take_def)
   apply(rename_tac d xa da i ia e ea c ca)(*strict*)
   apply(rule_tac
      x="ia"
      in exI)
   apply(simp add: maximum_of_domain_def derivation_take_def)
  apply(rename_tac x d xa)(*strict*)
  apply(simp only: epdaH_marked_effect_def epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac d xa i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d xa i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d xa i e q h s)(*strict*)
  apply(subgoal_tac "(q \<in> cons_state_or_state_old ` epda_marking G \<or> q \<in> cons_state_or_state_new ` epda_states G) \<and> q \<notin> epda_nonstable_states (epda_delta (F_SDPDA_EUME G))")
   apply(rename_tac d xa i e q h s)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_EUML_def Let_def)
  apply(rename_tac d xa i e q h s)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac d xa i e q h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa i e h s x)(*strict*)
   apply(rule_tac
      x="derivation_take (F_DPDA_EUME__RL__derivation d) i"
      in exI)
   apply(rule conjI)
    apply(rename_tac d xa i e h s x)(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
     apply(rename_tac d xa i e h s x)(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac d xa i e h s x)(*strict*)
    apply(force)
   apply(rename_tac d xa i e h s x)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def)
   apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d xa i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e h s x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d xa i e h s x)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>n. \<exists>e c' q. d n = Some (pair e c') \<and> epdaH_conf_state c' = cons_state_or_state_old q"
      and x="0"
      and n="i"
      in ex_max_limited)
    apply(rename_tac d xa i e h s x)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(case_tac "d 0")
     apply(rename_tac d xa i e h s x)(*strict*)
     apply(clarsimp)
    apply(rename_tac d xa i e h s x a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac d xa i e h s x a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d xa i e h s x b)(*strict*)
    apply(simp add: epdaH_initial_configurations_def)
    apply(clarsimp)
    apply(simp add: derivation_take_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def)
   apply(rename_tac d xa i e h s x)(*strict*)
   apply(force)
  apply(rename_tac d xa i e h s x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
  apply(case_tac "k=i")
   apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
   apply(clarsimp)
  apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
  apply(subgoal_tac "k<i")
   apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="k"
      and m="i"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
    apply(force)
   apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
   apply(force)
  apply(rename_tac d xa i e h s x k ea c' q)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e h s x k ea c' q e2 c2)(*strict*)
  apply(erule_tac x="Suc k" and P="\<lambda>x. k < x \<and> x \<le> i \<longrightarrow> (\<forall>e c'. d x = Some (pair e c') \<longrightarrow> (\<forall>q. epdaH_conf_state c' \<noteq> cons_state_or_state_old q))" in allE')
  apply(rename_tac d xa i e h s x k ea c' q e2 c2)(*strict*)
  apply(clarsimp)
  apply(case_tac c')
  apply(rename_tac d xa i e h s x k ea c' q e2 c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac d xa i e h s x k ea c' q e2 c2 q2 h2 s2)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d xa i e h s x k ea c' q e2 c2 q2 h2 s2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e h s x k ea q e2 h2 s2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q3 h3 s3)
  apply(rename_tac d xa i e h s x k ea q e2 h2 s2 q3 h3 s3)(*strict*)
  apply(case_tac q3)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 q3 h3 s3 qa)(*strict*)
   apply(force)
  apply(rename_tac d xa i e h s x k ea q e2 h2 s2 q3 h3 s3 qa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
  apply(subgoal_tac "h3 = h")
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
   apply(rule_tac
      x="derivation_take (F_DPDA_EUME__RL__derivation d) k"
      in exI)
   apply(rule conjI)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
     apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    apply(force)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
   apply(rule_tac
      x="k"
      in exI)
   apply(subgoal_tac "\<lparr>epdaH_conf_state = cons_state_or_state_old q, epdaH_conf_history = h2, epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations (F_DPDA_EUML G)")
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and i="k"
      in epdaH.belongs_configurations)
     apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
      apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
     apply(force)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
   apply(simp (no_asm) add: derivation_take_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    apply(simp add: derivation_take_def F_DPDA_EUME__RL__configuration_def epdaH_configurations_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
     apply(clarsimp)
     apply(rename_tac d xa i e h s x k ea e2 h2 s2 s3 qa xb)(*strict*)
     apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(clarsimp)
     apply(simp add: epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d xa i e s x k ea e2 h2 qa xb xc w)(*strict*)
     apply(case_tac e2)
     apply(rename_tac d xa i e s x k ea e2 h2 qa xb xc w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac d xa i e s x k ea h2 qa xb xc w edge_event edge_popa edge_push)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
     apply(case_tac "FB_executing_edge xc")
      apply(rename_tac d xa i e s x k ea h2 qa xb xc w edge_event edge_popa edge_push)(*strict*)
      apply(clarsimp)
      apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
     apply(rename_tac d xa i e s x k ea h2 qa xb xc w edge_event edge_popa edge_push)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
     apply(case_tac "edge_src xc \<in> epda_marking G")
      apply(rename_tac d xa i e s x k ea h2 qa xb xc w edge_event edge_popa edge_push)(*strict*)
      apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
     apply(rename_tac d xa i e s x k ea h2 qa xb xc w edge_event edge_popa edge_push)(*strict*)
     apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
    apply(clarsimp)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
    apply(simp add: F_DPDA_EUME__RL__configuration_def)
    apply(simp add: epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def)
    apply(case_tac e2)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac d xa i e s x k ea q h2 qa edge_eventa edge_popa edge_pusha w xb)(*strict*)
    apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
    apply(erule disjE)
     apply(rename_tac d xa i e s x k ea q h2 qa edge_eventa edge_popa edge_pusha w xb)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(force)
    apply(rename_tac d xa i e s x k ea q h2 qa edge_eventa edge_popa edge_pusha w xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 s3 qa)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__configuration_def)
   apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
   apply(clarsimp)
   apply(rename_tac d xa i e s x k ea q e2 h2 qa w)(*strict*)
   apply(erule disjE)
    apply(rename_tac d xa i e s x k ea q e2 h2 qa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac d xa i e s x k ea q e2 h2 qa w xb y)(*strict*)
    apply(case_tac e2)
    apply(rename_tac d xa i e s x k ea q e2 h2 qa w xb y edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(rename_tac d xa i e s x k ea q e2 h2 qa w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa i e s x k ea q e2 h2 qa w xb)(*strict*)
   apply(case_tac e2)
   apply(rename_tac d xa i e s x k ea q e2 h2 qa w xb edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa i e s x k ea q h2 qa w xb edge_eventa edge_popa edge_pusha)(*strict*)
   apply(case_tac edge_eventa)
    apply(rename_tac d xa i e s x k ea q h2 qa w xb edge_eventa edge_popa edge_pusha)(*strict*)
    apply(clarsimp)
   apply(rename_tac d xa i e s x k ea q h2 qa w xb edge_eventa edge_popa edge_pusha a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa i e s x k ea q h2 qa w xb edge_popa edge_pusha a)(*strict*)
   apply(case_tac "edge_src xb \<in> epda_marking G")
    apply(rename_tac d xa i e s x k ea q h2 qa w xb edge_popa edge_pusha a)(*strict*)
    apply(clarsimp)
    apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
   apply(rename_tac d xa i e s x k ea q h2 qa w xb edge_popa edge_pusha a)(*strict*)
   apply(simp add: FB_executing_edge_def epdaH_step_relation_def F_DPDA_EUML_def F_SDPDA_EUME_def Let_def epdaH_configurations_def F_SDPDA_EUME__edges_def F_SDPDA_EUME__edge_annotation_def F_DPDA_EUME__RL__derivation_def derivation_append_def F_DPDA_EUME__RL__configuration_def F_DPDA_EUME__RL__edge_def option_to_list_def)
  apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="Suc k"
      and m="i-Suc k"
      in F_DPDA_EUML__preserves__history_in_new_states)
        apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
        apply(force)
       apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
       apply(simp add: F_DPDA_EUML__SpecInput_def valid_dpda_def valid_pda_def)
      apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
      apply(force)
     apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
     apply(force)
    apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
    apply(force)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa ka eb c qb)(*strict*)
   apply(erule_tac
      x="ka"
      and P="\<lambda>ka. k < ka \<and> ka \<le> i \<longrightarrow> (\<forall>e c'. d ka = Some (pair e c') \<longrightarrow> (\<forall>q. epdaH_conf_state c' \<noteq> cons_state_or_state_old q))"
      in allE)
   apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa ka eb c qb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d xa i e h s x k ea q e2 h2 s2 h3 s3 qa)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_EUML__preserves__marked_language: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> valid_dpda (F_DPDA_EUML G) 
  \<Longrightarrow> epdaH.marked_language G = epdaH.marked_language (F_DPDA_EUML G)"
  apply(rule_tac
      t="epdaH.marked_language G"
      and s="epdaH.finite_marked_language G"
      in ssubst)
   apply (metis valid_dpda_to_valid_pda valid_pda_to_valid_epda F_DPDA_EUML__SpecInput_def epdaH_inst_lang_finite)
  apply(rule_tac
      t="epdaH.marked_language (F_DPDA_EUML G)"
      and s="epdaH.finite_marked_language (F_DPDA_EUML G)"
      in ssubst)
   apply (metis valid_dpda_to_valid_pda valid_pda_to_valid_epda epdaH_inst_lang_finite)
  apply(rule order_antisym)
   apply(rule F_DPDA_EUML__equal__finite_marked_language1)
    apply(force)
   apply(force)
  apply(rule F_DPDA_EUML__equal__finite_marked_language2)
   apply(force)
  apply(force)
  done

theorem F_DPDA_EUML__preserves__epdaH_reflection_to_DFA_exists: "
  valid_dpda M 
  \<Longrightarrow> epdaH_reflection_to_DFA_exists M D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state) 
  \<Longrightarrow> R = F_DPDA_EUML M 
  \<Longrightarrow> epdaH_reflection_to_DFA_exists R D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(clarsimp)
  apply(rename_tac d n c)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac d n c)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d n c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option b)(*strict*)
  apply(subgoal_tac "b=c")
   apply(rename_tac d n c option b)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
  apply(rename_tac d n c option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option)(*strict*)
  apply(thin_tac "get_configuration (Some (pair option c)) = Some c")
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n c option)(*strict*)
   prefer 2
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d n c option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d n c option)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac d n c option)(*strict*)
  apply(erule_tac
      x="F_DPDA_EUME__RL__derivation d"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(erule_tac
      x="F_DPDA_EUME__RL__configuration c"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c option)(*strict*)
   apply(simp add: get_configuration_def F_DPDA_EUME__RL__derivation_def)
  apply(rename_tac d n c option)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option d' m)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="m"
      in exI)
  apply(clarsimp)
  apply(simp add: F_DPDA_EUML__get_state_def get_configuration_def F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def)
  done

theorem F_DPDA_EUML__preserves__corresponds_to_top_stack: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> corresponds_to_top_stack Go (F_DPDA_OTS__is_auxiliary \<circ> F_DPDA_EUML__get_state) (F_DPDA_OTS__get_stack \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: F_DPDA_EUML__SpecInput_def corresponds_to_top_stack_def)
  apply(clarsimp)
  apply(rename_tac d n c X)(*strict*)
  apply(erule_tac
      x="F_DPDA_EUME__RL__derivation d"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c X)(*strict*)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d n c X)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d n c X)(*strict*)
   apply(force)
  apply(rename_tac d n c X)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac d n c X)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n c X a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n c X a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c X option)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def get_configuration_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
  done

theorem F_DPDA_EUML__preserves__main_states_have_only_empty_steps: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> main_states_have_only_empty_steps Go (F_DPDA_OTS__is_main \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: F_DPDA_EUML__SpecInput_def main_states_have_only_empty_steps_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(case_tac "edge_src e")
   apply(rename_tac e q)(*strict*)
   apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
   prefer 2
   apply(rename_tac e q)(*strict*)
   apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
   apply(case_tac q)
    apply(rename_tac e q a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac e q a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   prefer 2
   apply(rename_tac e q)(*strict*)
   apply(case_tac q)
    apply(rename_tac e q a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac e q a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   apply(erule_tac
      x="cons_state a"
      in ballE)
    apply(rename_tac e a)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def)
    apply(erule disjE)
     apply(rename_tac e a)(*strict*)
     apply(clarsimp)
     apply(rename_tac e a xa)(*strict*)
     apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
     apply(case_tac "FB_executing_edge xa")
      apply(rename_tac e a xa)(*strict*)
      apply(clarsimp)
      apply(erule disjE)
       apply(rename_tac e a xa)(*strict*)
       apply(clarsimp)
       apply(rename_tac a xa)(*strict*)
       apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
      apply(rename_tac e a xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac a xa)(*strict*)
      apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
     apply(rename_tac e a xa)(*strict*)
     apply(clarsimp)
     apply(erule disjE)
      apply(rename_tac e a xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac a xa)(*strict*)
      apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
     apply(rename_tac e a xa)(*strict*)
     apply(case_tac "edge_src xa \<in> epda_marking G")
      apply(rename_tac e a xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac a xa)(*strict*)
      apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
     apply(rename_tac e a xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac a xa)(*strict*)
     apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
    apply(rename_tac e a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
   apply(erule_tac
      P="cons_state_or_state_old (cons_state a) \<in> cons_state_or_state_old ` epda_states G"
      in disjE)
    apply(rename_tac e a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   apply(clarsimp)
  apply(rename_tac e a)(*strict*)
  apply(erule_tac
      x="cons_state a"
      in ballE)
   apply(rename_tac e a)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def)
   apply(erule disjE)
    apply(rename_tac e a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
   apply(clarsimp)
   apply(rename_tac e a xa)(*strict*)
   apply(case_tac "FB_executing_edge xa")
    apply(rename_tac e a xa)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac e a xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac a xa)(*strict*)
     apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
    apply(rename_tac e a xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a xa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
   apply(rename_tac e a xa)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac e a xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a xa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
   apply(rename_tac e a xa)(*strict*)
   apply(case_tac "edge_src xa \<in> epda_marking G")
    apply(rename_tac e a xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a xa)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
   apply(rename_tac e a xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a xa)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
  apply(rename_tac e a)(*strict*)
  apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
  apply(erule_tac
      P="cons_state_or_state_new (cons_state a) \<in> cons_state_or_state_old ` epda_states G"
      in disjE)
   apply(rename_tac e a)(*strict*)
   apply(clarsimp)
  apply(rename_tac e a)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_EUML__preserves__main_to_auxiliary_or_auxiliary_to_main: "
  main_to_auxiliary_or_auxiliary_to_main G F_DPDA_OTS__is_main 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> main_to_auxiliary_or_auxiliary_to_main Go (F_DPDA_OTS__is_main \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: main_to_auxiliary_or_auxiliary_to_main_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(erule disjE)
    apply(rename_tac e x)(*strict*)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="x"
      in ballE)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac e x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac e x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac e x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac e x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e x)(*strict*)
  apply(erule disjE)
   apply(rename_tac e x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac e x)(*strict*)
  apply(case_tac "edge_src x \<in> epda_marking G")
   apply(rename_tac e x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac e x)(*strict*)
  apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  done

theorem F_DPDA_EUML__preserves__main_states_have_all_empty_steps: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> main_states_have_all_empty_steps Go (F_DPDA_OTS__is_main \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: F_DPDA_EUML__SpecInput_def main_states_have_all_empty_steps_def)
  apply(clarsimp)
  apply(rename_tac q X)(*strict*)
  apply(case_tac "q")
   apply(rename_tac q X qa)(*strict*)
   apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
   prefer 2
   apply(rename_tac q X state)(*strict*)
   apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
   apply(clarsimp)
   apply(rename_tac X qa)(*strict*)
   apply(case_tac qa)
    apply(rename_tac X qa a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac X qa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac X a)(*strict*)
   prefer 2
   apply(rename_tac q X qa)(*strict*)
   apply(case_tac qa)
    apply(rename_tac q X qa a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac q X qa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac X a)(*strict*)
   apply(erule_tac
      x="cons_state a"
      in ballE)
    apply(rename_tac X a)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in ballE)
     apply(rename_tac X a)(*strict*)
     apply(clarsimp)
     apply(rename_tac X a e)(*strict*)
     apply(case_tac "edge_src e\<in> epda_marking G")
      apply(rename_tac X a e)(*strict*)
      apply(rule_tac
      x="\<lparr>edge_src=cons_state_or_state_old (cons_state a),edge_event=edge_event e,edge_pop=edge_pop e,edge_push=edge_push e,edge_trg=cons_state_or_state_new (edge_trg e)\<rparr>"
      in exI)
      apply(rule conjI)
       apply(rename_tac X a e)(*strict*)
       apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
       apply(rule_tac
      x="e"
      in bexI_image_disjI2)
        apply(rename_tac X a e)(*strict*)
        apply(clarsimp)
        apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
       apply(rename_tac X a e)(*strict*)
       apply(clarsimp)
       apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
      apply(rename_tac X a e)(*strict*)
      apply(clarsimp)
     apply(rename_tac X a e)(*strict*)
     apply(rule_tac
      x="\<lparr>edge_src=cons_state_or_state_old (cons_state a),edge_event=edge_event e,edge_pop=edge_pop e,edge_push=edge_push e,edge_trg=cons_state_or_state_old (edge_trg e)\<rparr>"
      in exI)
     apply(rule conjI)
      apply(rename_tac X a e)(*strict*)
      apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
      apply(rule_tac
      x="e"
      in bexI_image_disjI2)
       apply(rename_tac X a e)(*strict*)
       apply(clarsimp)
       apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
      apply(rename_tac X a e)(*strict*)
      apply(erule disjE)
       apply(rename_tac X a e)(*strict*)
       apply(clarsimp)
       apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
      apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
     apply(rename_tac X a e)(*strict*)
     apply(clarsimp)
    apply(rename_tac X a)(*strict*)
    apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
   apply(rename_tac X a)(*strict*)
   apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
   apply(erule disjE)
    apply(rename_tac X a)(*strict*)
    apply(clarsimp)
   apply(rename_tac X a)(*strict*)
   apply(clarsimp)
  apply(rename_tac X a)(*strict*)
  apply(erule_tac
      x="cons_state a"
      in ballE)
   apply(rename_tac X a)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in ballE)
    apply(rename_tac X a)(*strict*)
    apply(clarsimp)
    apply(rename_tac X a e)(*strict*)
    apply(rule_tac
      x="\<lparr>edge_src=cons_state_or_state_new (cons_state a),edge_event=edge_event e,edge_pop=edge_pop e,edge_push=edge_push e,edge_trg=cons_state_or_state_new (edge_trg e)\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac X a e)(*strict*)
     apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
     apply(rule_tac
      x="e"
      in bexI_image_disjI2)
      apply(rename_tac X a e)(*strict*)
      apply(clarsimp)
      apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
     apply(erule disjE)
      apply(rename_tac X a e)(*strict*)
      apply(clarsimp)
     apply(rename_tac X a e)(*strict*)
     apply(clarsimp)
     apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def FB_executing_edge_def)
   apply(rename_tac X a)(*strict*)
   apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
  apply(rename_tac X a)(*strict*)
  apply(simp add: F_DPDA_EUML_def Let_def F_SDPDA_EUME_def F_SDPDA_EUME__edges_def)
  apply(erule disjE)
   apply(rename_tac X a)(*strict*)
   apply(clarsimp)
  apply(rename_tac X a)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_EUML__preserves__executing_edge_from_auxiliary_to_main_state: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> executing_edge_from_auxiliary_to_main_state Go (F_DPDA_OTS__is_auxiliary \<circ> F_DPDA_EUML__get_state) (F_DPDA_OTS__is_main \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: F_DPDA_EUML__SpecInput_def executing_edge_from_auxiliary_to_main_state_def)
  apply(clarsimp)
  apply(rename_tac e y)(*strict*)
  apply(simp add: F_SDPDA_EUME_def F_DPDA_EUML_def Let_def F_SDPDA_EUME__edges_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e y)(*strict*)
   apply(clarsimp)
   apply(rename_tac e y x)(*strict*)
   apply(erule disjE)
    apply(rename_tac e y x)(*strict*)
    apply(clarsimp)
    apply(rename_tac y x)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
   apply(rename_tac e y x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
  apply(rename_tac e y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e y x)(*strict*)
  apply(erule disjE)
   apply(rename_tac e y x)(*strict*)
   apply(clarsimp)
   apply(rename_tac y x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
  apply(rename_tac e y x)(*strict*)
  apply(case_tac "edge_src x \<in> epda_marking G")
   apply(rename_tac e y x)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
  apply(rename_tac e y x)(*strict*)
  apply(simp add: F_SDPDA_EUME__edge_annotation_def F_DPDA_OTS__is_main_def F_DPDA_EUML__get_state_def)
  done

theorem F_DPDA_EUML__preserves__always_applicable_for_auxiliary_states: "
  F_DPDA_EUML__SpecInput G D 
  \<Longrightarrow> Go = F_DPDA_EUML G 
  \<Longrightarrow> always_applicable_for_auxiliary_states Go (F_DPDA_OTS__is_auxiliary \<circ> F_DPDA_EUML__get_state)"
  apply(simp add: always_applicable_for_auxiliary_states_def F_DPDA_EUML__SpecInput_def always_applicable_def)
  apply(clarsimp)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule_tac
      x="F_DPDA_EUME__RL__derivation d"
      in allE)
  apply(erule impE)
   apply(rename_tac d e c n ea)(*strict*)
   apply(rule F_DPDA_EUML__reflects__derivation_preserves_derivation_initial)
    apply(rename_tac d e c n ea)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d e c n ea)(*strict*)
   apply(force)
  apply(rename_tac d e c n ea)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__derivation_def F_DPDA_EUME__RL__configuration_def get_configuration_def)
  apply(erule_tac
      x="case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (F_DPDA_EUME__RL__edge e)"
      in allE)
  apply(erule_tac
      x="F_DPDA_EUME__RL__configuration c"
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
   apply(simp add: F_DPDA_EUME__RL__configuration_def F_DPDA_OTS__is_auxiliary_def F_DPDA_EUML__get_state_def)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule_tac
      x="F_DPDA_EUME__RL__edge ea"
      in ballE)
   apply(rename_tac d e c n ea)(*strict*)
   prefer 2
   apply(subgoal_tac "False")
    apply(rename_tac d e c n ea)(*strict*)
    apply(force)
   apply(rename_tac d e c n ea)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__edge_def F_SDPDA_EUME_def F_DPDA_EUML_def Let_def F_SDPDA_EUME__edges_def)
   apply(case_tac c)
   apply(rename_tac d e c n ea epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e n ea epdaH_conf_history epdaH_conf_stack)(*strict*)
   apply(rename_tac h s)
   apply(rename_tac d e n ea h s)(*strict*)
   apply(erule disjE)+
    apply(rename_tac d e n ea h s)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e n ea h s x)(*strict*)
    apply(case_tac x)
    apply(rename_tac d e n ea h s x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(rename_tac qs re po pu qt)
    apply(rename_tac d e n ea h s x qs re po pu qt)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e n ea h s qs re po pu qt)(*strict*)
    apply(erule disjE)+
     apply(rename_tac d e n ea h s qs re po pu qt)(*strict*)
     apply(clarsimp)
     apply(rename_tac d e n h s qs re po pu qt)(*strict*)
     apply(simp add: F_SDPDA_EUME__edge_annotation_def)
    apply(rename_tac d e n ea h s qs re po pu qt)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac d e n ea h s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e n ea h s x)(*strict*)
   apply(case_tac x)
   apply(rename_tac d e n ea h s x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(rename_tac qs re po pu qt)
   apply(rename_tac d e n ea h s x qs re po pu qt)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(case_tac "edge_src x \<in> epda_marking G")
    apply(rename_tac d e n ea h s x qs re po pu qt)(*strict*)
    apply(erule disjE)+
     apply(rename_tac d e n ea h s x qs re po pu qt)(*strict*)
     apply(clarsimp)
    apply(rename_tac d e n ea h s x qs re po pu qt)(*strict*)
    apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(rename_tac d e n ea h s x qs re po pu qt)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
   apply(clarsimp)
   apply(rename_tac d e n ea h s qs re po pu qt)(*strict*)
   apply(erule disjE)+
    apply(rename_tac d e n ea h s qs re po pu qt)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e n ea h s qs re po pu qt)(*strict*)
   apply(simp add: F_SDPDA_EUME__edge_annotation_def)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule impE)
   apply(rename_tac d e c n ea)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__edge_def F_DPDA_EUME__RL__configuration_def)
  apply(rename_tac d e c n ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n ea x)(*strict*)
  apply(case_tac x)
  apply(rename_tac d e c n ea x epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d e c n ea x q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n ea q h s)(*strict*)
  apply(case_tac ea)
  apply(rename_tac d e c n ea q h s edge_srca edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d e c n ea q h s qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n q h s re po pu qt)(*strict*)
  apply(case_tac c)
  apply(rename_tac d e c n q h s re po pu qt epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d e c n qa ha sa re po pu qt q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n qa ha sa re po pu qt q h s)(*strict*)
  apply(case_tac qt)
   apply(rename_tac d e n qa ha sa re po pu qt q h s qb)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e n qa ha sa re po pu q h s qb)(*strict*)
   apply(simp add: F_DPDA_EUME__RL__edge_def F_DPDA_EUME__RL__configuration_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d e n re po pu q h qb w)(*strict*)
   apply(rule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_old qb, epdaH_conf_history = h@option_to_list re, epdaH_conf_stack = pu @ w\<rparr>"
      in exI)
   apply(simp add: F_DPDA_EUME__RL__edge_def F_DPDA_EUME__RL__configuration_def epdaH_step_relation_def)
  apply(rename_tac d e n qa ha sa re po pu qt q h s qb)(*strict*)
  apply(simp add: F_DPDA_EUME__RL__edge_def F_DPDA_EUME__RL__configuration_def epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d e n re po pu q h qb w)(*strict*)
  apply(rule_tac
      x="\<lparr>epdaH_conf_state = cons_state_or_state_new qb, epdaH_conf_history = h@option_to_list re, epdaH_conf_stack = pu @ w\<rparr>"
      in exI)
  apply(simp add: F_DPDA_EUME__RL__edge_def F_DPDA_EUME__RL__configuration_def epdaH_step_relation_def)
  done

theorem F_DPDA_EUML__SOUND: "
  F_DPDA_EUML__SpecInput G P 
  \<Longrightarrow> F_DPDA_EUML__SpecOutput G (P, \<Sigma>UC) (F_DPDA_EUML G)"
  apply(simp add: F_DPDA_EUML__SpecOutput_def)
  apply(rule context_conjI)
   apply (rule F_DPDA_EUML__preserves__dpda)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   prefer 2
   apply(rule context_conjI)
    apply(rule F_DPDA_EUML__preserves__unmarked_language)
    apply(force)
   apply(rule context_conjI)
    apply(simp add: nonblockingness_language_def F_DPDA_EUML__SpecInput_def)
   apply(rule context_conjI)
    apply(rule F_DPDA_EUML__enforces__state_stack_unique_for_marking_states)
     apply(force)
    apply(force)
   apply(rule context_conjI)
    apply(rule F_DPDA_EUML__enforces__only_executing_edges_from_marking_states)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(rule F_DPDA_EUML__preserves__no_livelock)
     apply(force)
    apply(force)
   apply(simp add: F_DPDA_EUML__SpecInput_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule F_DPDA_EUML__preserves__epdaH_reflection_to_DFA_exists)
      prefer 2
      apply(force)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(simp only: F_DPDA_EUML__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_stack_def)
    apply(rule F_DPDA_EUML__preserves__corresponds_to_top_stack)
     apply(simp add: F_DPDA_EUML__SpecInput_def)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(simp only: F_DPDA_EUML__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_stack_def)
    apply(rule F_DPDA_EUML__preserves__main_states_have_only_empty_steps)
     apply(simp add: F_DPDA_EUML__SpecInput_def)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(simp only: F_DPDA_EUML__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_stack_def)
    apply(rule F_DPDA_EUML__preserves__main_states_have_all_empty_steps)
     apply(simp add: F_DPDA_EUML__SpecInput_def)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(simp only: F_DPDA_EUML__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_stack_def)
    apply(rule F_DPDA_EUML__preserves__executing_edge_from_auxiliary_to_main_state)
     apply(simp add: F_DPDA_EUML__SpecInput_def)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(simp only: F_DPDA_EUML__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_stack_def)
    apply(rule F_DPDA_EUML__preserves__always_applicable_for_auxiliary_states)
     apply(simp add: F_DPDA_EUML__SpecInput_def)
     apply(force)
    apply(force)
   apply(simp only: F_DPDA_EUML__is_auxiliary_def F_DPDA_EUML__is_main_def F_DPDA_EUML__get_stack_def)
   apply(rule F_DPDA_EUML__preserves__main_to_auxiliary_or_auxiliary_to_main)
    apply(force)
   apply(force)
  apply(rule F_DPDA_EUML__preserves__marked_language)
   apply(force)
  apply(force)
  done

end

