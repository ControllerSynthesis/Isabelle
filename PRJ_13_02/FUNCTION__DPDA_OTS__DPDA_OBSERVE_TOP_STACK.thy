section {*FUNCTION\_\_DPDA\_OTS\_\_DPDA\_OBSERVE\_TOP\_STACK*}
theory
  FUNCTION__DPDA_OTS__DPDA_OBSERVE_TOP_STACK

imports
  PRJ_13_02__ENTRY

begin

definition F_DPDA_OTS__get_state :: "
  ('state, 'stack) DT_state_and_stack_or_state
  \<Rightarrow> 'state"
  where
    "F_DPDA_OTS__get_state x \<equiv>
  case x of
  cons_state_and_stack a b \<Rightarrow> a
  | cons_state a \<Rightarrow> a"

definition F_DPDA_OTS__get_stack :: "
  ('state, 'stack) DT_state_and_stack_or_state
  \<Rightarrow> 'stack option"
  where
    "F_DPDA_OTS__get_stack x \<equiv>
  case x of
  cons_state_and_stack a b \<Rightarrow> Some b
  | cons_state a \<Rightarrow> None"

definition F_DPDA_OTS__is_auxiliary :: "
  ('state, 'stack) DT_state_and_stack_or_state
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__is_auxiliary x \<equiv>
  case x of
  cons_state_and_stack a b \<Rightarrow> True
  | cons_state a \<Rightarrow> False"

definition F_DPDA_OTS__is_main :: "
  ('state, 'stack) DT_state_and_stack_or_state
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__is_main x \<equiv>
  case x of
  cons_state_and_stack a b \<Rightarrow> False
  | cons_state a \<Rightarrow> True"

lemma F_DPDA_OTS__preserves__PDA: "
  valid_pda M
  \<Longrightarrow> F_DPDA_OTS M = N
  \<Longrightarrow> valid_pda N"
  apply(simp add: F_DPDA_OTS_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_OTS__states_def)
   apply(rule conjI)
    apply(simp add: F_DPDA_OTS__states_auxiliary_def)
   apply(simp add: F_DPDA_OTS__states_main_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_OTS__edges_def)
   apply(rule conjI)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def)
   apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def)
   apply(force)
  apply(rule conjI)
   apply(simp add: F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(rule conjI)
     apply(rename_tac a b)(*strict*)
     apply(force)
    apply(rename_tac a b)(*strict*)
    apply(simp add: option_to_set_def)
    apply(simp add: may_terminated_by_def append_language_def append_alphabet_def kleene_star_def)
    apply(case_tac "b = epda_box M")
     apply(rename_tac a b)(*strict*)
     apply(rule_tac
      x="[]"
      in exI)
     apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. edge_src xa \<in> epda_states M \<and> edge_trg xa \<in> epda_states M \<and> option_to_set (edge_event xa) \<subseteq> epda_events M \<and> edge_pop xa \<in> may_terminated_by (epda_gamma M) (epda_box M) \<and> edge_push xa \<in> may_terminated_by (epda_gamma M) (epda_box M) \<and> (edge_pop xa \<in> must_terminated_by (epda_gamma M) (epda_box M)) = (edge_push xa \<in> must_terminated_by (epda_gamma M) (epda_box M))"
      in ballE)
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rule inMap)
   apply(rule_tac
      x="((edge_src xa),(hd (edge_pop xa)))"
      in bexI)
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def append_language_def append_alphabet_def kleene_star_def)
   apply(clarsimp)
   apply(rename_tac xa a aa)(*strict*)
   apply(erule_tac
      x="xa"
      in ballE)
    apply(rename_tac xa a aa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa a aa)(*strict*)
   apply(case_tac "edge_pop xa")
    apply(rename_tac xa a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa a aa ab list)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa a aa ab)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac a b)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

definition F_DPDA_OTS__epdaH_epdaH__LR__TSstructure :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2 \<equiv>
  valid_dpda G1
  \<and> G2 = F_DPDA_OTS G1"

definition F_DPDA_OTS__epdaH_epdaH__LR__configuration1 :: "
  ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__configuration1 c \<equiv>
  \<lparr>epdaH_conf_state = cons_state_and_stack (epdaH_conf_state c) (hd (epdaH_conf_stack c)),
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = epdaH_conf_stack c\<rparr>"

definition F_DPDA_OTS__epdaH_epdaH__LR__configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__configurations G1 G2 c1 c2 \<equiv>
  F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2
  \<and> c1 \<in> epdaH.get_accessible_configurations G1
  \<and> c2 = F_DPDA_OTS__epdaH_epdaH__LR__configuration1 c1"

definition F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration G1 G2 c1 c2 \<equiv>
  F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2
  \<and> c1 \<in> epdaH_initial_configurations G1
  \<and> c2 = F_DPDA_OTS__epdaH_epdaH__LR__configuration1 c1"

definition F_DPDA_OTS__epdaH_epdaH__LR__effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__effect G1 G2 w1 w2 \<equiv>
  F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2
  \<and> w1 = w2"

lemma F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

lemma F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G1)(*strict*)
   prefer 2
   apply(rule F_DPDA_OTS__preserves__PDA)
    apply(rename_tac G1)(*strict*)
    apply(simp add: valid_dpda_def)
    apply(force)
   apply(rename_tac G1)(*strict*)
   apply(force)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_pda_def)
  done

definition F_DPDA_OTS__epdaH_epdaH__LR__step_simulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ((('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label, (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  let
    ci = F_DPDA_OTS__epdaH_epdaH__LR__configuration1 c1'
  in
    d = der3
          c2
            (F_DPDA_OTS__edges_auxiliary_main_1 e)
          (ci\<lparr>epdaH_conf_state := cons_state (edge_trg e)\<rparr>)
            (F_DPDA_OTS__edges_main_auxiliary_1 (edge_trg e) (hd (epdaH_conf_stack ci)))
          ci"

definition F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ((('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label, (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_OTS__epdaH_epdaH__LR__configuration1 c1)"

lemma F_DPDA_OTS__epdaH_epdaH__LR__inst__relation_initial_simulation: "
  (\<forall>G1 G2. F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaH_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaH.derivation_initial G2 d2 \<and> F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_OTS__epdaH_epdaH__LR__configurations G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation_def F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaH.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1)(*strict*)
   apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
   apply(rule disjI1)
   apply(simp add: F_DPDA_OTS__states_auxiliary_def)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configurations_def)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation_def F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
  apply(simp add: F_DPDA_OTS__states_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(simp add: epdaH.get_accessible_configurations_def)
  apply(rule_tac
      x="der1 c1"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaH.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(simp add: F_DPDA_OTS__states_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  done

lemma F_DPDA_OTS__epdaH_epdaH__LR__inst__relation_step_simulation: "
  (\<forall>G1 G2. F_DPDA_OTS__epdaH_epdaH__LR__TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_OTS__epdaH_epdaH__LR__configurations G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaH_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaH.derivation G2 d2 \<and> epdaH.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_OTS__epdaH_epdaH__LR__step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_OTS__epdaH_epdaH__LR__configurations G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configurations_def Let_def F_DPDA_OTS__epdaH_epdaH__LR__step_simulation_def F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation_def F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule epdaH.der3_is_derivation)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply (metis F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure2_belongs F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp (no_asm) only: epdaH_step_relation_def F_DPDA_OTS__edges_auxiliary_main_1_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def)
    apply(rule conjI)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
     apply(rule disjI2)
     apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
     apply(rule inMap)
     apply(rule_tac
      x="e1"
      in bexI)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def epda_step_labels_def)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def epda_step_labels_def)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(clarsimp)
     apply(erule_tac
      x="e1"
      in ballE)
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     apply(case_tac "edge_pop e1")
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' w a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp (no_asm) only: epdaH_step_relation_def F_DPDA_OTS__edges_auxiliary_main_1_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def)
   apply(rule conjI)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
    apply(rule disjI1)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
    apply(rule inMap)
    apply(rule_tac
      x="(edge_trg e1,hd (epdaH_conf_stack c1'))"
      in bexI)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def epda_step_labels_def epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 c1 e1 c1' w)(*strict*)
    apply(case_tac "edge_pop e1")
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
     prefer 2
     apply(rule_tac
      c="c1"
      in epdaH_epda_stack_is_must_terminated_by)
      apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
    apply(simp add: valid_epda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(clarsimp)
    apply(case_tac "edge_push e1")
     apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' a)(*strict*)
     apply(case_tac "epdaH_conf_stack c1'")
      apply(rename_tac G1 c1 e1 c1' a)(*strict*)
      apply(clarsimp)
      apply(simp add: must_terminated_by_def may_terminated_by_def append_language_def append_alphabet_def kleene_star_def)
     apply(rename_tac G1 c1 e1 c1' a aa list)(*strict*)
     apply(clarsimp)
     apply(simp add: must_terminated_by_def may_terminated_by_def append_language_def append_alphabet_def kleene_star_def)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' a aa list ab)(*strict*)
     apply(case_tac ab)
      apply(rename_tac G1 c1 e1 c1' a aa list ab)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' a aa list ab ac lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' aa list ac lista)(*strict*)
     apply(case_tac lista)
      apply(rename_tac G1 c1 e1 c1' aa list ac lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' aa list ac lista a listb)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w a aa list)(*strict*)
    apply(clarsimp)
    apply(simp add: must_terminated_by_def may_terminated_by_def append_language_def append_alphabet_def kleene_star_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w a aa list ab ac ad)(*strict*)
    apply(erule_tac
      P="[] = ac \<and> (\<exists>a. set a \<subseteq> epda_gamma G1 - {epda_box G1} \<and> aa # list = a @ [epda_box G1])"
      in disjE)
     apply(rename_tac G1 c1 e1 c1' w a aa list ab ac ad)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' w aa list ab ad ae)(*strict*)
     apply(erule disjE)
      apply(rename_tac G1 c1 e1 c1' w aa list ab ad ae)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 c1 e1 c1' w aa list ab ad)(*strict*)
      apply(case_tac ad)
       apply(rename_tac G1 c1 e1 c1' w aa list ab ad)(*strict*)
       apply(clarsimp)
      apply(rename_tac G1 c1 e1 c1' w aa list ab ad a lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' w aa list ab ad ae)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' w aa list ab ae)(*strict*)
     apply(case_tac e1)
     apply(rename_tac G1 c1 e1 c1' w aa list ab ae edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w a aa list ab ac ad)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w a aa list ab ad)(*strict*)
    apply(case_tac e1)
    apply(rename_tac G1 c1 e1 c1' w a aa list ab ad edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: option_to_list_def F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS_def F_DPDA_OTS__edges_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1' w)(*strict*)
   apply(case_tac "edge_push e1 @ w")
    apply(rename_tac G1 c1 e1 c1' w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(case_tac "edge_pop e1")
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac G1 c1 e1 c1' a)(*strict*)
     prefer 2
     apply(rule_tac
      c="c1"
      in epdaH_epda_stack_is_must_terminated_by)
      apply(rename_tac G1 c1 e1 c1' a)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' a)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' a)(*strict*)
    apply(simp add: valid_epda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac G1 c1 e1 c1' a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 c1 e1 c1' a)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(clarsimp)
    apply(simp add: must_terminated_by_def may_terminated_by_def append_language_def append_alphabet_def kleene_star_def)
   apply(rename_tac G1 c1 e1 c1' w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule epdaH.der3_belongs)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply (metis F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure2_belongs F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    prefer 2
    apply(rule_tac
      G="G1"
      and c="c1"
      in epdaH_epda_stack_is_must_terminated_by)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(subgoal_tac "c1 \<in> epdaH_configurations G1")
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    prefer 2
    apply(simp add: epdaH.get_accessible_configurations_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' d i)(*strict*)
    apply(case_tac "d i")
     apply(rename_tac G1 c1 e1 c1' d i)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac G1 c1 e1 c1' d i a)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(case_tac a)
    apply(rename_tac G1 c1 e1 c1' d i a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' d i option)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac G1 c1 e1 c1' d i option)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac G1 c1 e1 c1' d i option)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac G1 c1 e1 c1' d i option)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' d i option)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 e1 c1' q s h)(*strict*)
   apply(case_tac s)
    apply(rename_tac G1 e1 c1' q s h)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 e1 c1' q h)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
   apply(rename_tac G1 e1 c1' q s h a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 e1 c1' q h a list)(*strict*)
   apply(simp add: F_DPDA_OTS__states_def)
   apply(rule disjI1)
   apply(simp add: F_DPDA_OTS__states_auxiliary_def)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: der3_def get_configuration_def)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc(Suc 0)"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule_tac der3_maximum_of_domain)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (metis F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure1_belongs F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def epdaH.der2_is_derivation epdaH.der2_preserves_get_accessible_configurations)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(simp add: der3_def get_configuration_def)
  done

lemma F_DPDA_OTS__epdaH_epdaH__LR__inst__ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaH_initial_configurations epda_step_labels epdaH_step_relation valid_epda epdaH_configurations epdaH_initial_configurations epda_step_labels epdaH_step_relation F_DPDA_OTS__epdaH_epdaH__LR__configurations F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration F_DPDA_OTS__epdaH_epdaH__LR__TSstructure F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation F_DPDA_OTS__epdaH_epdaH__LR__step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def F_DPDA_OTS__epdaH_epdaH__LR__inst__relation_initial_simulation F_DPDA_OTS__epdaH_epdaH__LR__inst__relation_step_simulation F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure1_belongs F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "F_DPDA_OTS__epdaH_epdaH__LR" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaH_configurations"
  (* initial_configurations1 *)
  "epdaH_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaH_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaH_marking_condition"
  (* marked_effect1 *)
  "epdaH_marked_effect"
  (* unmarked_effect1 *)
  "epdaH_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaH_configurations"
  (* initial_configurations2 *)
  "epdaH_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaH_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaH_marking_condition"
  (* marked_effect2 *)
  "epdaH_marked_effect"
  (* unmarked_effect2 *)
  "epdaH_unmarked_effect"
  (* relation_configuration *)
  "F_DPDA_OTS__epdaH_epdaH__LR__configurations"
  (* relation_initial_configuration *)
  "F_DPDA_OTS__epdaH_epdaH__LR__initial_configuration"
  (* relation_effect *)
  "F_DPDA_OTS__epdaH_epdaH__LR__effect"
  (* relation_TSstructure *)
  "F_DPDA_OTS__epdaH_epdaH__LR__TSstructure"
  (* relation_initial_simulation *)
  "F_DPDA_OTS__epdaH_epdaH__LR__initial_simulation"
  (* relation_step_simulation *)
  "F_DPDA_OTS__epdaH_epdaH__LR__step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__inst__ATS_Simulation_Configuration_Weak_axioms)
  done

definition F_DPDA_OTS__epdaH_epdaH__RL__TSstructure :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2 \<equiv>
  valid_dpda G2
  \<and> G1 = F_DPDA_OTS G2"

definition F_DPDA_OTS__epdaH_epdaH__LR__configuration1R :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c \<equiv>
  \<lparr>epdaH_conf_state = F_DPDA_OTS__get_state (epdaH_conf_state c),
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = epdaH_conf_stack c\<rparr>"

definition F_DPDA_OTS__epdaH_epdaH__RL__configurations :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__RL__configurations G1 G2 c1 c2 \<equiv>
  F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2
  \<and> c1 \<in> epdaH.get_accessible_configurations G1
  \<and> c2 = F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1"

definition F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration G1 G2 c1 c2 \<equiv>
  F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2
  \<and> c1 \<in> epdaH_initial_configurations G1
  \<and> c2 = F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1"

definition F_DPDA_OTS__epdaH_epdaH__RL__effect :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__RL__effect G1 G2 w1 w2 \<equiv>
  F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2
  \<and> w1 = w2"

lemma F_DPDA_OTS__epdaH_epdaH__RL__inst__AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
  apply(rename_tac G2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G2)(*strict*)
   prefer 2
   apply(rule F_DPDA_OTS__preserves__PDA)
    apply(rename_tac G2)(*strict*)
    apply(simp add: valid_dpda_def)
    apply(force)
   apply(rename_tac G2)(*strict*)
   apply(force)
  apply(rename_tac G2)(*strict*)
  apply(simp add: valid_pda_def)
  done

lemma F_DPDA_OTS__epdaH_epdaH__RL__inst__AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis valid_dpda_def valid_pda_def)
  done

definition F_DPDA_OTS__epdaH_epdaH__RL__edge :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_OTS__epdaH_epdaH__RL__edge e \<equiv>
  \<lparr>edge_src = F_DPDA_OTS__get_state (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = F_DPDA_OTS__get_state (edge_trg e)\<rparr>"

definition F_DPDA_OTS__epdaH_epdaH__LR__step_simulationRL :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__step_simulationRL G1 G2 c1 e c1' c2 d \<equiv>
  case epdaH_conf_state c1 of
  cons_state_and_stack q X \<Rightarrow>
      d = der2
            (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1)
              (F_DPDA_OTS__epdaH_epdaH__RL__edge e)
            (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1')
  | cons_state q \<Rightarrow>
      d = der1 (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1)"

definition F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL :: "
  (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1)"

lemma F_DPDA_OTS__epdaH_epdaH__RL__inst__relation_initial_simulationRL: "
  (\<forall>G1 G2. F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaH_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaH.derivation_initial G2 d2 \<and> F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_OTS__epdaH_epdaH__RL__configurations G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL_def F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration_def F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaH.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(clarsimp)
   apply(rename_tac G2)(*strict*)
   apply(simp add: F_DPDA_OTS__get_state_def)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL_def F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration_def F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_OTS__states_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
   apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: epdaH.get_accessible_configurations_def)
  apply(rule_tac
      x="der1 c1"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaH.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaH.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(simp add: F_DPDA_OTS__states_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  apply(simp add: F_DPDA_OTS__states_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def)
  done

lemma F_DPDA_OTS__epdaH_epdaH__RL__inst__relation_step_simulationRL: "
  (\<forall>G1 G2. F_DPDA_OTS__epdaH_epdaH__RL__TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_OTS__epdaH_epdaH__RL__configurations G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaH_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaH.derivation G2 d2 \<and> epdaH.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_OTS__epdaH_epdaH__LR__step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_OTS__epdaH_epdaH__RL__configurations G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__configurations_def Let_def F_DPDA_OTS__epdaH_epdaH__LR__step_simulationRL_def F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL_def F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration_def F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def epda_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(subgoal_tac "valid_epda (F_DPDA_OTS G2)")
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   prefer 2
   apply (metis F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure2_belongs F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(case_tac "epdaH_conf_state c1")
   apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(simp (no_asm) only: epdaH_step_relation_def F_DPDA_OTS__edges_auxiliary_main_1_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def)
    apply(rule conjI)
     apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
     apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__epdaH_epdaH__RL__edge_def epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' a b w)(*strict*)
     apply(erule disjE)
      apply(rename_tac G2 c1 e1 c1' a b w)(*strict*)
      apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
      apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' a b w)(*strict*)
     apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
     apply(clarsimp)
     apply(rename_tac G2 c1 c1' a b w x)(*strict*)
     apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
     apply(simp add: F_DPDA_OTS__get_state_def)
     apply(case_tac x)
     apply(rename_tac G2 c1 c1' a b w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(rule conjI)
     apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
     apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__epdaH_epdaH__RL__edge_def epdaH_step_relation_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__epdaH_epdaH__RL__edge_def epdaH_step_relation_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(rule epdaH.der2_belongs_prime)
      apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
     apply(simp add: F_DPDA_OTS__get_state_def)
     apply(subgoal_tac "X" for X)
      apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
      prefer 2
      apply(rule_tac
      G="F_DPDA_OTS G2"
      and c="c1"
      in epdaH_epda_stack_is_must_terminated_by)
       apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
       apply (metis)
      apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
     apply(subgoal_tac "c1 \<in> epdaH_configurations (F_DPDA_OTS G2)")
      apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
      prefer 2
      apply(simp add: epdaH.get_accessible_configurations_def)
      apply(clarsimp)
      apply(rename_tac G2 c1 e1 c1' a b d i)(*strict*)
      apply(case_tac "d i")
       apply(rename_tac G2 c1 e1 c1' a b d i)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac G2 c1 e1 c1' a b d i aa)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
      apply(case_tac aa)
      apply(rename_tac G2 c1 e1 c1' a b d i aa option ba)(*strict*)
      apply(clarsimp)
      apply(rename_tac G2 c1 e1 c1' a b d i option)(*strict*)
      apply(rule epdaH.belongs_configurations)
       apply(rename_tac G2 c1 e1 c1' a b d i option)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac G2 c1 e1 c1' a b d i option)(*strict*)
        apply (metis)
       apply(rename_tac G2 c1 e1 c1' a b d i option)(*strict*)
       apply(force)
      apply(rename_tac G2 c1 e1 c1' a b d i option)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_main_def)
     apply(clarsimp)
     apply(rename_tac G2 e1 c1' a b s h)(*strict*)
     apply(erule disjE)
      apply(rename_tac G2 e1 c1' a b s h)(*strict*)
      apply(clarsimp)
     apply(rename_tac G2 e1 c1' a b s h)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(simp add: der2_def get_configuration_def)
   apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply(rule_tac der2_maximum_of_domain)
   apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
    apply (metis  epdaH.der2_is_derivation epdaH.der2_preserves_get_accessible_configurations)
   apply(rename_tac G2 c1 e1 c1' a b)(*strict*)
   apply(simp add: der2_def get_configuration_def)
  apply(rename_tac G2 c1 e1 c1' a)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply(rule epdaH.der1_is_derivation)
  apply(rename_tac G2 c1 e1 c1' a)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply(rule epdaH.der1_belongs)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(simp add: F_DPDA_OTS__get_state_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac G2 c1 e1 c1' a)(*strict*)
    prefer 2
    apply(rule_tac
      G="F_DPDA_OTS G2"
      and c="c1"
      in epdaH_epda_stack_is_must_terminated_by)
     apply(rename_tac G2 c1 e1 c1' a)(*strict*)
     apply (metis)
    apply(rename_tac G2 c1 e1 c1' a)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply(subgoal_tac "c1 \<in> epdaH_configurations (F_DPDA_OTS G2)")
    apply(rename_tac G2 c1 e1 c1' a)(*strict*)
    prefer 2
    apply(simp add: epdaH.get_accessible_configurations_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' a d i)(*strict*)
    apply(case_tac "d i")
     apply(rename_tac G2 c1 e1 c1' a d i)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac G2 c1 e1 c1' a d i aa)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(case_tac aa)
    apply(rename_tac G2 c1 e1 c1' a d i aa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' a d i option)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac G2 c1 e1 c1' a d i option)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac G2 c1 e1 c1' a d i option)(*strict*)
      apply (metis)
     apply(rename_tac G2 c1 e1 c1' a d i option)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' a d i option)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_main_def)
   apply(clarsimp)
   apply(rename_tac G2 e1 c1' a s h)(*strict*)
   apply(erule disjE)
    apply(rename_tac G2 e1 c1' a s h)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 e1 c1' a s h)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' a)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply(simp add: der1_def get_configuration_def)
  apply(rename_tac G2 c1 e1 c1' a)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply(rule_tac der1_maximum_of_domain)
  apply(rename_tac G2 c1 e1 c1' a)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' a)(*strict*)
   apply (metis  epdaH.der2_is_derivation epdaH.der2_preserves_get_accessible_configurations)
  apply(rename_tac G2 c1 e1 c1' a)(*strict*)
  apply(simp add: der1_def get_configuration_def)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def epdaH_step_relation_def F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' a w)(*strict*)
  apply(erule disjE)
   apply(rename_tac G2 c1 e1 c1' a w)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' w aa b)(*strict*)
   apply(simp add: F_DPDA_OTS__get_state_def option_to_list_def)
  apply(rename_tac G2 c1 e1 c1' a w)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 c1' a w x)(*strict*)
  apply(simp add: F_DPDA_OTS__get_state_def option_to_list_def)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

lemma F_DPDA_OTS__epdaH_epdaH__RL__inst__ATS_Simulation_Configuration_WeakRL_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaH_initial_configurations epda_step_labels epdaH_step_relation valid_epda epdaH_configurations epdaH_initial_configurations epda_step_labels epdaH_step_relation F_DPDA_OTS__epdaH_epdaH__RL__configurations F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration F_DPDA_OTS__epdaH_epdaH__RL__TSstructure F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL F_DPDA_OTS__epdaH_epdaH__LR__step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def F_DPDA_OTS__epdaH_epdaH__RL__inst__relation_initial_simulationRL F_DPDA_OTS__epdaH_epdaH__RL__inst__relation_step_simulationRL F_DPDA_OTS__epdaH_epdaH__RL__inst__AX_TSstructure_relation_TSstructure1_belongs F_DPDA_OTS__epdaH_epdaH__RL__inst__AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "F_DPDA_OTS__epdaH_epdaH__RL" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaH_configurations"
  (* initial_configurations1 *)
  "epdaH_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaH_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaH_marking_condition"
  (* marked_effect1 *)
  "epdaH_marked_effect"
  (* unmarked_effect1 *)
  "epdaH_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaH_configurations"
  (* initial_configurations2 *)
  "epdaH_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaH_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaH_marking_condition"
  (* marked_effect2 *)
  "epdaH_marked_effect"
  (* unmarked_effect2 *)
  "epdaH_unmarked_effect"
  (* relation_configuration *)
  "F_DPDA_OTS__epdaH_epdaH__RL__configurations"
  (* relation_initial_configuration *)
  "F_DPDA_OTS__epdaH_epdaH__RL__initial_configuration"
  (* relation_effect *)
  "F_DPDA_OTS__epdaH_epdaH__RL__effect"
  (* relation_TSstructure *)
  "F_DPDA_OTS__epdaH_epdaH__RL__TSstructure"
  (* relation_initial_simulationRL *)
  "F_DPDA_OTS__epdaH_epdaH__LR__initial_simulationRL"
  (* relation_step_simulationRL *)
  "F_DPDA_OTS__epdaH_epdaH__LR__step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__inst__ATS_Simulation_Configuration_WeakRL_axioms)
  done

lemma F_DPDA_OTS__preserves__determinism: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> valid_pda R
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible R"
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long M")
   prefer 2
   apply(rule DPDA_to_epdaH_determinism)
   apply(force)
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long R")
   apply (metis epda_epdaS_is_forward_edge_deterministic_accessible_equal_to_epdaH_is_forward_edge_deterministicHist_DB_long valid_pda_to_valid_epda)
  apply(clarsimp)
  apply(simp add: epdaH.is_forward_edge_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(erule_tac
      x="F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    prefer 2
    apply(rule_tac
      ?G2.0="M"
      and ?G1.0="F_DPDA_OTS M"
      and ?d1.0="d"
      and x="n"
      in F_DPDA_OTS__epdaH_epdaH__RL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
      apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2)(*strict*)
   apply(rule_tac
      x="d2"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n2"
      in exI)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__configurations_def F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2)(*strict*)
    prefer 2
    apply(rule_tac
      m="n2"
      in epdaH.some_position_has_details_before_max_dom)
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e d2 n2 ea ca)(*strict*)
   apply(simp add: get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(case_tac "epdaH_conf_state c")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   prefer 2
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a)(*strict*)
   apply(thin_tac "\<forall>c1 c2 e1 e2. (\<exists>w1. w1 \<in> epda_effects M \<and> (\<exists>w2. w2 \<in> epda_effects M \<and> epdaH_step_relation M (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c) e1 c1 \<and> epdaH_step_relation M (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c) e2 c2 \<and> epdaH_conf_history c1 = epdaH_conf_history (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c) @ w1 \<and> epdaH_conf_history c2 = epdaH_conf_history (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c) @ w2 \<and> (ATS_History.history_fragment_prefixes epda_effects (@) M w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) M w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) M w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) M w1 \<or> ATS_History.history_fragment_prefixes epda_effects (@) M w2 = ATS_History.history_fragment_prefixes epda_effects (@) M w1))) \<longrightarrow> e1 = e2")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1 \<or> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n e a w wa)(*strict*)
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
   apply(erule_tac
      P="e1 \<in> F_DPDA_OTS__edges_main_auxiliary M"
      in disjE)
    apply(rename_tac c d c1 c2 e1 e2 n e a w wa)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 e2 n e a w wa x)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(case_tac e2)
    apply(rename_tac c d c1 c2 e2 n e a w wa x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 n e a w wa x edge_eventa edge_popa edge_pusha)(*strict*)
    apply(case_tac c)
    apply(rename_tac c d c1 c2 n e a w wa x edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n e a w wa)(*strict*)
   apply(erule disjE)
    apply(rename_tac c d c1 c2 e1 e2 n e a w wa)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 n e a w wa aa b x)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(rename_tac c d c1 c2 e1 e2 n e a w wa)(*strict*)
   apply(case_tac e2)
   apply(rename_tac c d c1 c2 e1 e2 n e a w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 n e a w wa edge_eventa edge_popa edge_pusha)(*strict*)
   apply(case_tac c)
   apply(rename_tac c d c1 c2 e1 n e a w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 c2 e1 n e a w wa edge_eventa edge_popa edge_pusha epdaH_conf_historya)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(erule_tac
      x="F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c1"
      in allE)
  apply(erule_tac
      x="F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c2"
      in allE)
  apply(erule_tac
      x="F_DPDA_OTS__epdaH_epdaH__RL__edge e1"
      in allE)
  apply(erule_tac
      x="F_DPDA_OTS__epdaH_epdaH__RL__edge e2"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__edge_def)
   apply(clarsimp)
   apply(case_tac e1)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac e2)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 n w1 w2 e a b edge_src edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 n e a b edge_eventa edge_popa edge_pusha w)(*strict*)
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
   apply(erule_tac
      P="\<lparr>edge_src = epdaH_conf_state c, edge_event = edge_eventa, edge_pop = edge_popa, edge_push = edge_pusha, edge_trg = epdaH_conf_state c1\<rparr> \<in> F_DPDA_OTS__edges_main_auxiliary M"
      in disjE)
    apply(rename_tac c d c1 c2 n e a b edge_eventa edge_popa edge_pusha w)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 n e a b edge_eventa edge_popa edge_pusha w)(*strict*)
   apply(erule disjE)
    apply(rename_tac c d c1 c2 n e a b edge_eventa edge_popa edge_pusha w)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 n e a b edge_eventa edge_popa edge_pusha w)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 n e a b edge_eventa edge_popa edge_pusha w x xa)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 n e w x xa)(*strict*)
   apply(case_tac c1)
   apply(rename_tac c d c1 c2 n e w x xa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac c2)
   apply(rename_tac c d c1 c2 n e w x xa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d n e w x xa)(*strict*)
   apply(case_tac x)
   apply(rename_tac c d n e w x xa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac xa)
   apply(rename_tac c d n e w x xa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d n e w edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac c)
   apply(rename_tac c d n e w edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e w edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_history)(*strict*)
   apply(simp add: F_DPDA_OTS__get_state_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp add: F_DPDA_OTS_def epda_effects_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(rule_tac
      x="w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp add: F_DPDA_OTS_def epda_effects_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1 \<or> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp add: epdaH_step_relation_def F_DPDA_OTS__epdaH_epdaH__RL__edge_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n e a b w wa)(*strict*)
   apply(erule_tac
      P="e1 \<in> F_DPDA_OTS__edges_main_auxiliary M"
      in disjE)
    apply(rename_tac c d c1 c2 e1 e2 n e a b w wa)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 e2 n e a b w wa aa ba)(*strict*)
    apply(case_tac e2)
    apply(rename_tac c d c1 c2 e2 n e a b w wa aa ba edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 n e a b w wa aa ba edge_event edge_pop edge_push)(*strict*)
    apply(simp add: F_DPDA_OTS__get_state_def)
    apply(case_tac c1)
    apply(rename_tac c d c1 c2 n e a b w wa aa ba edge_event edge_pop edge_push epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d c2 n e a b w wa aa ba edge_event edge_pop edge_push)(*strict*)
    apply(case_tac c2)
    apply(rename_tac c d c2 n e a b w wa aa ba edge_event edge_pop edge_push epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d n e a b w wa aa ba edge_event edge_pop edge_push epdaH_conf_statea)(*strict*)
    apply(case_tac c)
    apply(rename_tac c d n e a b w wa aa ba edge_event edge_pop edge_push epdaH_conf_statea epdaH_conf_stateaa epdaH_conf_history epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n e a b w wa)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e2 n e a b w wa x)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(case_tac e2)
   apply(rename_tac c d c1 c2 e2 n e a b w wa x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 n e a b w wa x edge_eventa edge_popa edge_pusha)(*strict*)
   apply(simp add: F_DPDA_OTS__get_state_def)
   apply(case_tac c1)
   apply(rename_tac c d c1 c2 n e a b w wa x edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c2 n e a b w wa x edge_eventa edge_popa edge_pusha)(*strict*)
   apply(case_tac c2)
   apply(rename_tac c d c2 n e a b w wa x edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d n e a b w wa x edge_eventa edge_popa edge_pusha epdaH_conf_statea)(*strict*)
   apply(case_tac c)
   apply(rename_tac c d n e a b w wa x edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_stateaa epdaH_conf_history epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e w wa x edge_eventa edge_popa edge_pusha epdaH_conf_state epdaH_conf_history)(*strict*)
   apply(case_tac x)
   apply(rename_tac d n e w wa x edge_eventa edge_popa edge_pusha epdaH_conf_state epdaH_conf_history edge_srca edge_eventaa edge_popaa edge_pushaa edge_trga)(*strict*)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1 \<or> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp add: epdaH_step_relation_def F_DPDA_OTS__epdaH_epdaH__RL__edge_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n e a b w wa)(*strict*)
   apply(erule_tac
      P="e2 \<in> F_DPDA_OTS__edges_main_auxiliary M"
      in disjE)
    apply(rename_tac c d c1 c2 e1 e2 n e a b w wa)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n e a b w wa)(*strict*)
   apply(case_tac e2)
   apply(rename_tac c d c1 c2 e1 e2 n e a b w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 n e a b w wa edge_eventa edge_popa edge_pusha)(*strict*)
   apply(simp add: F_DPDA_OTS__get_state_def)
   apply(case_tac c1)
   apply(rename_tac c d c1 c2 e1 n e a b w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c2 e1 n e a b w wa edge_event edge_popa edge_push)(*strict*)
   apply(case_tac c2)
   apply(rename_tac c d c2 e1 n e a b w wa edge_event edge_popa edge_push epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d e1 n e a b w wa edge_event edge_popa edge_push epdaH_conf_statea)(*strict*)
   apply(case_tac c)
   apply(rename_tac c d e1 n e a b w wa edge_event edge_popa edge_push epdaH_conf_statea epdaH_conf_stateaa epdaH_conf_history epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 n e a b w wa edge_event edge_popa edge_push epdaH_conf_state epdaH_conf_history)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac d e1 n e a b w wa edge_event edge_popa edge_push epdaH_conf_state epdaH_conf_history x)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(rename_tac d e1 n e a b w wa edge_eventa edge_popa edge_pusha epdaH_conf_state epdaH_conf_history x)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 n e w wa epdaH_conf_history x)(*strict*)
   apply(case_tac x)
   apply(rename_tac d e1 n e w wa epdaH_conf_history x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(subgoal_tac "epda_effects M = epda_effects (F_DPDA_OTS M)")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   prefer 2
   apply(rule antisym)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b x)(*strict*)
    apply(simp add: epda_effects_def F_DPDA_OTS_def)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp add: epda_effects_def F_DPDA_OTS_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes epda_effects (@) M w1"
      and s="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w1"
      in ssubst)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp (no_asm) add: epdaH.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes epda_effects (@) M w2"
      and s="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_OTS M) w2"
      in ssubst)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(simp (no_asm) add: epdaH.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e a b)(*strict*)
  apply(force)
  done

theorem F_DPDA_OTS__preserves__DPDA: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> valid_dpda R"
  apply(simp (no_asm) add: valid_dpda_def)
  apply(rule context_conjI)
   apply(rule F_DPDA_OTS__preserves__PDA)
    apply(simp add: valid_dpda_def)
    apply(force)
   apply(force)
  apply(rule F_DPDA_OTS__preserves__determinism)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DPDA_OTS__reflects__unmarked_language: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.unmarked_language R \<subseteq> epdaH.unmarked_language M"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH.derivation (F_DPDA_OTS M) d")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      ?G2.0="M"
      and ?G1.0="F_DPDA_OTS M"
      and ?d1.0="d"
      and x="i"
      in F_DPDA_OTS__epdaH_epdaH__RL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac d i e q h s)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
    apply(rename_tac d i e q h s)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n2"
      in epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac d i e q h s d2 n2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i e q h s d2 n2)(*strict*)
    apply(rule epdaH.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   apply(rule_tac
      x="n2"
      in exI)
   apply(clarsimp)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  done

lemma F_DPDA_OTS__preserves__unmarked_language: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.unmarked_language M \<subseteq> epdaH.unmarked_language R"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH.derivation M d")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      ?G1.0="M"
      and ?G2.0="F_DPDA_OTS M"
      and ?d1.0="d"
      and x="i"
      in F_DPDA_OTS__epdaH_epdaH__LR.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac d i e q h s)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
    apply(rename_tac d i e q h s)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n2"
      in epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac d i e q h s d2 n2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i e q h s d2 n2)(*strict*)
    apply(rule epdaH.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   apply(rule_tac
      x="n2"
      in exI)
   apply(clarsimp)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configurations_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  done

theorem F_DPDA_OTS__equal__unmarked_language: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.unmarked_language R = epdaH.unmarked_language M"
  apply(rule order_antisym)
   apply(rule F_DPDA_OTS__reflects__unmarked_language)
    apply(force)
   apply(force)
  apply(rule F_DPDA_OTS__preserves__unmarked_language)
   apply(force)
  apply(force)
  done

lemma F_DPDA_OTS__reflects__marked_language: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.marked_language R \<subseteq> epdaH.marked_language M"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH.derivation (F_DPDA_OTS M) d")
  apply(subgoal_tac "(\<exists>d. epdaH.derivation_initial M d \<and> x \<in> epdaH_marked_effect M d)")
   apply(rename_tac x d)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d da)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marking_condition_def epdaH_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac d da i ia ib e ea eb c ca cb)(*strict*)
   apply(rule_tac
      x="ib"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH_marking_condition (F_DPDA_OTS M) d")
  apply(simp add: epdaH_marked_effect_def epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(thin_tac "\<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_string_state c = epdaH_string_state c'")
  apply(rename_tac d i e c)(*strict*)
  apply(thin_tac "c \<in> epdaH_configurations (F_DPDA_OTS M)")
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(rule_tac
      ?G2.0="M"
      and ?G1.0="F_DPDA_OTS M"
      and ?d1.0="d"
      and x="i"
      in F_DPDA_OTS__epdaH_epdaH__RL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac d i e q h s)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
    apply(rename_tac d i e q h s)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(rule_tac
      x="derivation_take d2 n2"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n2"
      in epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac d i e q h s d2 n2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i e q h s d2 n2)(*strict*)
    apply(rule epdaH.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac d i e q h s d2 n2)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s d2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
  apply(rule_tac
      x="n2"
      in exI)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(simp add: derivation_take_def F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
  apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(simp add: derivation_take_def F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS__get_state_def get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def F_DPDA_OTS_def F_DPDA_OTS__marking_states_def)
   apply(clarsimp)
  apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS__get_state_def get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def F_DPDA_OTS_def F_DPDA_OTS__marking_states_def)
  apply(rename_tac d i e q h s d2 n2 ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s d2 n2 ea c j e' c')(*strict*)
  apply(simp add: derivation_take_def F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
  done

lemma F_DPDA_OTS__preserves__marked_language: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.marked_language M \<subseteq> epdaH.marked_language R"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH.derivation M d")
  apply(thin_tac "epdaH_marking_condition M d")
  apply(subgoal_tac "\<exists>d. epdaH.derivation_initial (F_DPDA_OTS M) d \<and> x \<in> epdaH_marked_effect (F_DPDA_OTS M) d")
   apply(rename_tac x d)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d da)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marked_effect_def epdaH_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac d da i ia e ea c ca)(*strict*)
   apply(rule_tac
      x="ia"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q s h)
  apply(rename_tac d i e q s h)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q s h)(*strict*)
   prefer 2
   apply(rule_tac
      ?G1.0="M"
      and ?G2.0="F_DPDA_OTS M"
      and ?d1.0="d"
      and x="i"
      in F_DPDA_OTS__epdaH_epdaH__LR.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac d i e q s h)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__TSstructure_def)
    apply(rename_tac d i e q s h)(*strict*)
    apply(force)
   apply(rename_tac d i e q s h)(*strict*)
   apply(force)
  apply(rename_tac d i e q s h)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q s h d2 n2)(*strict*)
  apply(rule_tac
      x="derivation_take d2 n2"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i e q s h d2 n2)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d i e q s h d2 n2)(*strict*)
  apply(rule_tac
      x="n2"
      in exI)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q s h d2 n2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n2"
      in epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac d i e q s h d2 n2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i e q s h d2 n2)(*strict*)
    apply(rule epdaH.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac d i e q s h d2 n2)(*strict*)
   apply(force)
  apply(rename_tac d i e q s h d2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
    apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configurations_def F_DPDA_OTS__marking_states_def derivation_take_def epdaH_marking_configurations_def F_DPDA_OTS_def get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def)
   apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s h d2 n2 ea c j e' c')(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configurations_def F_DPDA_OTS__marking_states_def derivation_take_def epdaH_marking_configurations_def F_DPDA_OTS_def get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def)
  apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
  apply(simp add: epdaH_marking_configurations_def)
  apply(rule conjI)
   apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
   prefer 2
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
     apply (metis F_DPDA_OTS__epdaH_epdaH__LR__inst__AX_TSstructure_relation_TSstructure2_belongs F_DPDA_OTS__epdaH_epdaH__LR__configurations_def)
    apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
    apply(force)
   apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
   apply(force)
  apply(rename_tac d i e q s h d2 n2 ea c)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configurations_def F_DPDA_OTS__marking_states_def derivation_take_def epdaH_marking_configurations_def F_DPDA_OTS_def get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def)
  apply(clarsimp)
  apply(rename_tac d i e q s h d2 n2 ea)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q s h d2 n2 ea)(*strict*)
   prefer 2
   apply(rule_tac
      G="M"
      in epdaH_epda_stack_is_must_terminated_by)
    apply(rename_tac d i e q s h d2 n2 ea)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d i e q s h d2 n2 ea)(*strict*)
   apply(force)
  apply(rename_tac d i e q s h d2 n2 ea)(*strict*)
  apply(clarsimp)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac d i e q s d2 n2 ea a)(*strict*)
  apply(rule inMap)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac d i e q s d2 n2 ea a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s d2 n2 ea)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d i e q s d2 n2 ea a aa list)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_OTS__equal__marked_language: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.marked_language R = epdaH.marked_language M"
  apply(rule order_antisym)
   apply(rule F_DPDA_OTS__reflects__marked_language)
    apply(force)
   apply(force)
  apply(rule F_DPDA_OTS__preserves__marked_language)
   apply(force)
  apply(force)
  done

lemma F_DPDA_OTS__topstack_equal_to_annotation: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH.derivation_initial R d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> epdaH_conf_state c = cons_state_and_stack q X
  \<Longrightarrow> \<exists>w. epdaH_conf_stack c = X # w"
  apply(case_tac n)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac c)
   apply(rename_tac epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS_def)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_OTS M"
      and d="d"
      and n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n e1 e2 c1 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(case_tac c)
  apply(rename_tac n e1 e2 c1 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 w epdaH_conf_history)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n e1 e2 w epdaH_conf_history edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 w epdaH_conf_history edge_src edge_event edge_pop edge_push)(*strict*)
  apply(rename_tac h src read pop push)
  apply(rename_tac n e1 w h src read pop push)(*strict*)
  apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(erule disjE)
   apply(rename_tac n e1 w h src read pop push)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
  apply(rename_tac n e1 w h src read pop push)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac n e1 w h src read pop push x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_def valid_epda_step_label_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

definition corresponds_to_top_stack :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> ('state \<Rightarrow> 'stack option)
  \<Rightarrow> bool"
  where
    "corresponds_to_top_stack M valid f \<equiv>
  \<forall>d n c X.
    epdaH.derivation_initial M d
    \<longrightarrow> get_configuration (d n) = Some c
    \<longrightarrow> valid (epdaH_conf_state c)
    \<longrightarrow> f (epdaH_conf_state c) = Some X
    \<longrightarrow> (\<exists>w. epdaH_conf_stack c = X # w)"

theorem F_DPDA_OTS__enforces__corresponds_to_top_stack: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> corresponds_to_top_stack R F_DPDA_OTS__is_auxiliary F_DPDA_OTS__get_stack"
  apply(simp add: corresponds_to_top_stack_def)
  apply(clarsimp)
  apply(rename_tac d n c X)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac d n c X)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d n c X a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac d n c X a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c X option)(*strict*)
  apply(simp add: F_DPDA_OTS__is_auxiliary_def F_DPDA_OTS__get_stack_def)
  apply(case_tac c)
  apply(rename_tac d n c X option epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n X option epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac e q h s)
  apply(rename_tac d n X e q h s)(*strict*)
  apply(case_tac q)
   apply(rename_tac d n X e q h s a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n X e h s a)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d n X e h s a)(*strict*)
    prefer 2
    apply(rule F_DPDA_OTS__topstack_equal_to_annotation)
        apply(rename_tac d n X e h s a)(*strict*)
        apply(force)
       apply(rename_tac d n X e h s a)(*strict*)
       apply(force)
      apply(rename_tac d n X e h s a)(*strict*)
      apply(force)
     apply(rename_tac d n X e h s a)(*strict*)
     apply(force)
    apply(rename_tac d n X e h s a)(*strict*)
    apply(force)
   apply(rename_tac d n X e h s a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n X e q h s a)(*strict*)
  apply(case_tac q)
   apply(rename_tac d n X e q h s a aa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n X e q h s a aa)(*strict*)
  apply(clarsimp)
  done

definition state_stack_unique :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> bool"
  where
    "state_stack_unique G Q \<equiv>
  \<forall>d1 d2 e1 e2 c1 c2 n1 n2.
    epdaH.derivation_initial G d1
    \<longrightarrow> epdaH.derivation_initial G d2
    \<longrightarrow> d1 n1 = Some (pair e1 c1)
    \<longrightarrow> d2 n2 = Some (pair e2 c2)
    \<longrightarrow> epdaH_conf_state c1 = epdaH_conf_state c2
    \<longrightarrow> epdaH_conf_state c1 \<in> Q
    \<longrightarrow> hd (epdaH_conf_stack c1) = hd (epdaH_conf_stack c2)"

lemma F_DPDA_OTS__state_stack_unique_for_annotated_states: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> state_stack_unique R (F_DPDA_OTS__states_auxiliary M)"
  apply(simp add: state_stack_unique_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2 epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historya epdaH_conf_stackaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 n1 n2 epdaH_conf_history epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac h1 s1 q h2 s2)
  apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 q h2 s2)(*strict*)
  apply(simp add: F_DPDA_OTS__states_auxiliary_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and n="n1"
      in F_DPDA_OTS__topstack_equal_to_annotation)
       apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and n="n2"
      in F_DPDA_OTS__topstack_equal_to_annotation)
       apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e1 e2 n1 n2 h1 s1 h2 s2 a b)(*strict*)
  apply(force)
  done

definition always_applicable :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> bool"
  where
    "always_applicable G Q \<equiv>
  \<forall>d e c n.
    epdaH.derivation_initial G d
    \<longrightarrow> d n = Some (pair e c)
    \<longrightarrow> epdaH_conf_state c \<in> Q
    \<longrightarrow> (\<forall>e \<in> epda_delta G.
          edge_src e = epdaH_conf_state c
          \<longrightarrow> (\<exists>c'. epdaH_step_relation G c e c'))"

lemma F_DPDA_OTS__always_applicable_for_annotated_states: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> always_applicable R (F_DPDA_OTS__states_auxiliary M)"
  apply(simp add: always_applicable_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac d e c n a b ea)(*strict*)
  apply(erule disjE)
   apply(rename_tac d e c n a b ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e c n a b ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n a b x)(*strict*)
  apply(simp add: always_applicable_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac d e c n x)(*strict*)
  apply(case_tac c)
  apply(rename_tac d e c n x epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in F_DPDA_OTS__topstack_equal_to_annotation)
       apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
       apply(force)
      apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
      apply(force)
     apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
     apply(simp add: always_applicable_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
    apply(force)
   apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
   apply(force)
  apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac d e n x epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n x epdaH_conf_history w)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac d e n x epdaH_conf_history w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d e n x epdaH_conf_history w)(*strict*)
  apply(case_tac "x")
  apply(rename_tac d e n x epdaH_conf_history w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(case_tac edge_pop)
   apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_pop edge_push edge_trg a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_push edge_trg a)(*strict*)
  apply(rule_tac
      x="\<lparr>epdaH_conf_state = cons_state edge_trg, epdaH_conf_history = epdaH_conf_history@option_to_list edge_event, epdaH_conf_stack = edge_push@w\<rparr>"
      in exI)
  apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_push edge_trg a)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(rule disjI2)
  apply(rule inMap)
  apply(rule_tac
      x="\<lparr>edge_src = edge_src, edge_event = edge_event, edge_pop = [a], edge_push = edge_push, edge_trg = edge_trg\<rparr>"
      in bexI)
   apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_push edge_trg a)(*strict*)
   apply(simp add: always_applicable_def F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS_def F_DPDA_OTS__edges_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac d e n epdaH_conf_history w edge_src edge_event edge_push edge_trg a)(*strict*)
  apply(clarsimp)
  done

definition always_applicable_for_auxiliary_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "always_applicable_for_auxiliary_states G F \<equiv>
  always_applicable G (Collect F)"

theorem F_DPDA_OTS__enforces__always_applicable_for_auxiliary_states: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> always_applicable_for_auxiliary_states R F_DPDA_OTS__is_auxiliary"
  apply(subgoal_tac "valid_pda R")
   apply(simp add: always_applicable_for_auxiliary_states_def)
   apply(subgoal_tac "always_applicable R (F_DPDA_OTS__states_auxiliary M)")
    prefer 2
    apply(rule F_DPDA_OTS__always_applicable_for_annotated_states)
     apply(force)
    apply(force)
   apply(simp add: always_applicable_def)
   apply(clarsimp)
   apply(rename_tac d e c n ea)(*strict*)
   apply(erule_tac
      x="d"
      in allE)
   apply(clarsimp)
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
    apply(case_tac c)
    apply(rename_tac d e c n ea epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e n ea epdaH_conf_history epdaH_conf_stack)(*strict*)
    apply(simp add: F_DPDA_OTS__is_auxiliary_def)
    apply(case_tac ea)
    apply(rename_tac d e n ea epdaH_conf_history epdaH_conf_stack edge_srca edge_event edge_pop edge_push edge_trg)(*strict*)
    apply(case_tac edge_srca)
     apply(rename_tac d e n ea epdaH_conf_history epdaH_conf_stack edge_srca edge_event edge_pop edge_push edge_trg a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d e n epdaH_conf_history epdaH_conf_stack edge_event edge_pop edge_push edge_trg a b)(*strict*)
     apply(simp add: valid_pda_def valid_epda_def)
     apply(rename_tac d e n epdaH_conf_history epdaH_conf_stack edge_event edge_popa edge_push edge_trg a b)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      x="\<lparr>edge_src = cons_state_and_stack a b, edge_event = edge_event, edge_pop = edge_popa, edge_push = edge_push, edge_trg = edge_trg\<rparr>"
      and P="\<lambda>a. valid_epda_step_label (F_DPDA_OTS M) a"
      in ballE)
      apply(rename_tac d e n epdaH_conf_history epdaH_conf_stack edge_event edge_popa edge_push edge_trg a b)(*strict*)
      apply(simp add: valid_epda_step_label_def)
      apply(clarsimp)
      apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__states_def F_DPDA_OTS__states_main_def)
      apply(clarsimp)
     apply(rename_tac d e n epdaH_conf_history epdaH_conf_stack edge_event edge_popa edge_push edge_trg a b)(*strict*)
     apply(clarsimp)
    apply(rename_tac d e n ea epdaH_conf_history epdaH_conf_stack edge_srca edge_event edge_pop edge_push edge_trg a)(*strict*)
    apply(force)
   apply(rename_tac d e c n ea)(*strict*)
   apply(erule_tac
      x="ea"
      in ballE)
    apply(rename_tac d e c n ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e c n ea)(*strict*)
   apply(force)
  apply (metis F_DPDA_OTS__preserves__DPDA valid_dpda_to_valid_pda)
  done

definition some_edge_applicable :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "some_edge_applicable G \<equiv>
  \<forall>d e e' c n.
    epdaH.derivation_initial G d
    \<longrightarrow> d n = Some (pair e c)
    \<longrightarrow> e' \<in> epda_delta G
    \<longrightarrow> edge_src e' = epdaH_conf_state c
    \<longrightarrow> (\<exists>e c'.
          epdaH_step_relation G c e c'
          \<and> (edge_event e' = None \<longrightarrow> edge_event e = None))"

theorem F_DPDA_OTS__enforces__some_edge_applicable: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> valid_dpda R
  \<Longrightarrow> some_edge_applicable R"
  apply(subgoal_tac "always_applicable R (F_DPDA_OTS__states_auxiliary M)")
   prefer 2
   apply(rule F_DPDA_OTS__always_applicable_for_annotated_states)
    apply(force)
   apply(force)
  apply(simp add: some_edge_applicable_def)
  apply(clarsimp)
  apply(rename_tac d e e' c n)(*strict*)
  apply(case_tac c)
  apply(rename_tac d e e' c n epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d e e' c n q h s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d e e' c n q h s)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_OTS M"
      and d="d"
      and n="n"
      in epdaH_epda_box_stays_at_bottom)
     apply(rename_tac d e e' c n q h s)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d e e' c n q h s)(*strict*)
    apply(force)
   apply(rename_tac d e e' c n q h s)(*strict*)
   apply(force)
  apply(rename_tac d e e' c n q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e e' n h s)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac d e e' n h c)(*strict*)
  apply(subgoal_tac "\<lparr>epdaH_conf_state = edge_src e', epdaH_conf_history = h, epdaH_conf_stack = c @ [epda_box (F_DPDA_OTS M)]\<rparr> \<in> epdaH_configurations (F_DPDA_OTS M)")
   apply(rename_tac d e e' n h c)(*strict*)
   prefer 2
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac d e e' n h c)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d e e' n h c)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d e e' n h c)(*strict*)
    apply(force)
   apply(rename_tac d e e' n h c)(*strict*)
   apply(force)
  apply(rename_tac d e e' n h c)(*strict*)
  apply(subgoal_tac "e' \<in> F_DPDA_OTS__edges_main_auxiliary M \<or> e' \<in> F_DPDA_OTS__edges_auxiliary_main M")
   apply(rename_tac d e e' n h c)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(rename_tac d e e' n h c)(*strict*)
  apply(erule disjE)
   apply(rename_tac d e e' n h c)(*strict*)
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(clarsimp)
   apply(rename_tac d e n h c a b)(*strict*)
   apply(rule_tac
      x="\<lparr>edge_src=cons_state a,edge_event=None,edge_pop=[hd(c @ [epda_box M])],edge_push=[hd(c @ [epda_box M])],edge_trg=cons_state_and_stack a (hd(c @ [epda_box M]))\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="\<lparr>epdaH_conf_state = cons_state_and_stack a (hd(c @ [epda_box M])), epdaH_conf_history = h, epdaH_conf_stack = c @ [epda_box M]\<rparr>"
      in exI)
   apply(simp add: epdaH_step_relation_def)
   apply(rule conjI)
    apply(rename_tac d e n h c a b)(*strict*)
    apply(rule disjI1)
    apply(rule inMap)
    apply(clarsimp)
    apply(case_tac c)
     apply(rename_tac d e n h c a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d e n h a b)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac d e n h c a b aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e n h a b aa list)(*strict*)
    apply(simp add: epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d e n h c a b)(*strict*)
   apply(simp add: option_to_list_def)
   apply(case_tac c)
    apply(rename_tac d e n h c a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e n h c a b aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e e' n h c)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def always_applicable_def)
  apply(clarsimp)
  apply(rename_tac d e n h c x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def always_applicable_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = cons_state_and_stack (edge_src x) (hd (edge_pop x)), epdaH_conf_history = h, epdaH_conf_stack = c @ [epda_box (F_DPDA_OTS M)]\<rparr>"
      in allE)
  apply(rename_tac d e n h c x)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d e n h c x)(*strict*)
   apply(force)
  apply(rename_tac d e n h c x)(*strict*)
  apply(erule impE)
   apply(rename_tac d e n h c x)(*strict*)
   apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
   apply(simp add: epdaH_configurations_def F_DPDA_OTS__states_auxiliary_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS__states_def)
   apply(simp add: epdaH_configurations_def F_DPDA_OTS__states_auxiliary_def)
   apply(clarsimp)
   apply(rule inMap)
   apply(clarsimp)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label M x"
      in ballE)
    apply(rename_tac d e n h c x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d e n h c x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac d e n h c x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d e n h c x)(*strict*)
   apply(case_tac "x")
   apply(rename_tac d e n h c x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e n h c edge_src edge_event edge_popa edge_push edge_trg)(*strict*)
   apply(case_tac edge_popa)
    apply(rename_tac d e n h c edge_src edge_event edge_popa edge_push edge_trg)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e n h c edge_src edge_event edge_popa edge_push edge_trg a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e n h c edge_src edge_event edge_push edge_trg a)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a)(*strict*)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
   apply(erule disjE)+
       apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
       apply(clarsimp)+
    apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
    apply(erule disjE)+
      apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
      apply(clarsimp)+
   apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
   apply(erule disjE)+
      apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
      apply(clarsimp)+
   apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
   apply(erule disjE)+
     apply(rename_tac d e n h c edge_srca edge_eventa edge_pusha edge_trga a aa ab)(*strict*)
     apply(clarsimp)+
  apply(rename_tac d e n h c x)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = cons_state_and_stack (edge_src x) (hd (edge_pop x)), edge_event = edge_event x, edge_pop = edge_pop x, edge_push = edge_push x, edge_trg = cons_state (edge_trg x)\<rparr>"
      in ballE)
   apply(rename_tac d e n h c x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d e n h c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n h c x xa)(*strict*)
  apply(rule_tac
      x="\<lparr>edge_src = cons_state_and_stack (edge_src x) (hd (edge_pop x)), edge_event = edge_event x, edge_pop = edge_pop x, edge_push = edge_push x, edge_trg = cons_state (edge_trg x)\<rparr>"
      in exI)
  apply(rename_tac d e n h c x xa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="xa"
      in exI)
  apply(clarsimp)
  done

definition always_applicable_for_stable_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "always_applicable_for_stable_states G \<equiv>
  always_applicable G (epda_states G - epda_nonstable_states (epda_delta G))"

lemma always_applicable__subseteq: "
  valid_dpda M
  \<Longrightarrow> Q' \<subseteq> Q
  \<Longrightarrow> always_applicable R Q
  \<Longrightarrow> always_applicable R Q'"
  apply(simp add: always_applicable_def)
  apply(clarsimp)
  apply(rename_tac d e c n ea)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(clarsimp)
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
   apply(force)
  apply(rename_tac d e c n ea)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_OTS__enforces__always_applicable_for_stable_states: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> always_applicable_for_stable_states R"
  apply(simp add: always_applicable_for_stable_states_def)
  apply(rule always_applicable__subseteq)
    apply(force)
   prefer 2
   apply(rule F_DPDA_OTS__always_applicable_for_annotated_states)
    apply(force)
   apply(force)
  apply(simp add: epda_nonstable_states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__states_def F_DPDA_OTS_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "cons_state xa \<notin> (\<lambda>(x, y). cons_state_and_stack x y) ` (epda_states M \<times> epda_gamma M)")
  apply(simp add: F_DPDA_OTS__edges_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
  apply(rule_tac
      x="\<lparr>edge_src=cons_state xa,edge_event=None,edge_pop=[epda_box M],edge_push=[epda_box M],edge_trg=cons_state_and_stack xa (epda_box M)\<rparr>"
      in bexI)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(rule inMap)
  apply(clarsimp)
  done

definition state_stack_unique_for_marking_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "state_stack_unique_for_marking_states G \<equiv>
  state_stack_unique G (epda_marking G)"

lemma state_stack_unique__subseteq: "
  valid_dpda M
  \<Longrightarrow> Q' \<subseteq> Q
  \<Longrightarrow> state_stack_unique R Q
  \<Longrightarrow> state_stack_unique R Q'"
  apply(simp add: state_stack_unique_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="d2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
   apply(rule_tac
      x="n1"
      in exI)
   apply(clarsimp)
  apply(rename_tac d1 d2 e1 e2 c1 n1 c2 n2)(*strict*)
  apply(erule_tac
      x="c2"
      in allE)
  apply(clarsimp)
  apply(force)
  done

theorem F_DPDA_OTS__enforces__state_stack_unique_for_marking_states: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> state_stack_unique_for_marking_states R"
  apply(simp add: state_stack_unique_for_marking_states_def)
  apply(rule state_stack_unique__subseteq)
    apply(force)
   prefer 2
   apply(rule F_DPDA_OTS__state_stack_unique_for_annotated_states)
    apply(force)
   apply(force)
  apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rule inMap)
  apply(force)
  done

definition state_stack_unique_for_stable_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "state_stack_unique_for_stable_states G \<equiv>
  state_stack_unique G (epda_states G - epda_nonstable_states (epda_delta G))"

theorem F_DPDA_OTS__enforces___state_stack_unique_for_stable_states: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> state_stack_unique_for_stable_states R"
  apply(simp add: state_stack_unique_for_stable_states_def)
  apply(rule state_stack_unique__subseteq)
    apply(force)
   prefer 2
   apply(rule F_DPDA_OTS__state_stack_unique_for_annotated_states)
    apply(force)
   apply(force)
  apply(simp add: epda_nonstable_states_def F_DPDA_OTS__states_main_def F_DPDA_OTS__states_def F_DPDA_OTS_def F_DPDA_OTS__marking_states_def F_DPDA_OTS__states_auxiliary_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "cons_state xa \<notin> (\<lambda>(x, y). cons_state_and_stack x y) ` (epda_states M \<times> epda_gamma M)")
  apply(simp add: F_DPDA_OTS__edges_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
  apply(rule_tac
      x="\<lparr>edge_src=cons_state xa,edge_event=None,edge_pop=[epda_box M],edge_push=[epda_box M],edge_trg=cons_state_and_stack xa (epda_box M)\<rparr>"
      in bexI)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(rule inMap)
  apply(clarsimp)
  done

lemma F_DPDA_OTS__enforces__cons_state_and_stack_cons_state_alternation: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial (F_DPDA_OTS G) d
  \<Longrightarrow> d (n + n) = Some (pair e1 c1)
  \<Longrightarrow> d (Suc (n + n)) = Some (pair e2 c2)
  \<Longrightarrow> \<exists>q1 A q2. epdaH_conf_state c1 = cons_state_and_stack q1 A \<and> epdaH_conf_state c2 = cons_state q2"
  apply(induct n arbitrary: e1 c1 e2 c2)
   apply(rename_tac e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def F_DPDA_OTS_def)
   apply(clarsimp)
   apply(rename_tac c1 e2 c2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c1 e2 c2)(*strict*)
    prefer 2
    apply(rule_tac
      n="0"
      and m="(Suc 0)"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac c1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c1 c2 e2a)(*strict*)
   apply(simp add: epdaH_step_relation_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(clarsimp)
   apply(rename_tac c2 e2a w)(*strict*)
   apply(simp add: F_DPDA_OTS__get_state_def F_DPDA_OTS__edges_def)
   apply(erule disjE)+
    apply(rename_tac c2 e2a w)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
   apply(rename_tac c2 e2a w)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac c2 w x)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac n e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 c1 e2 c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e1 c1 e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      n="(n+n)"
      and m="(Suc (Suc (Suc (n + n))))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e1 c1 e2 c2)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 c1 e2 c2 e1a e2a c1a c2a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e1 c1 e2 c2 e1a e2a c1a c2a)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc(n+n)"
      and m="(Suc (Suc (Suc (n + n))))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e1 c1 e2 c2 e1a e2a c1a c2a)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e1 c1 e2 c2 e1a e2a c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac n e1 c1 e2 c2 e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac n e1 c1 e2 c2 e1a e2a c1a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c1 e2 c2 e1a e2a c1a c2a e2b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n c1 e2 c2 e1a e2a c1a c2a e2b)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc(Suc(n+n))"
      and m="(Suc (Suc (Suc (n + n))))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n c1 e2 c2 e1a e2a c1a c2a e2b)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n c1 e2 c2 e1a e2a c1a c2a e2b)(*strict*)
    apply(force)
   apply(rename_tac n c1 e2 c2 e1a e2a c1a c2a e2b)(*strict*)
   apply(force)
  apply(rename_tac n c1 e2 c2 e1a e2a c1a c2a e2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="Some e2a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c2a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c q1 q2 A)(*strict*)
  apply(simp add: epdaH_step_relation_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(simp add: F_DPDA_OTS__get_state_def F_DPDA_OTS__edges_def)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c q1 q2 A w wa wb)(*strict*)
  apply(erule disjE)+
     apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c q1 q2 A w wa wb)(*strict*)
     apply(clarsimp)
    apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c q1 q2 A w wa wb)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c q1 q2 A w wa wb)(*strict*)
   apply(clarsimp)
  apply(rename_tac n c1 c2 e1a e2a c1a c2a e2b e2c q1 q2 A w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c1 c2 e1a c1a c2a e2b e2c q1 q2 A w wa wb x)(*strict*)
  apply(erule disjE)+
    apply(rename_tac n c1 c2 e1a c1a c2a e2b e2c q1 q2 A w wa wb x)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c1 c2 e1a c1a c2a e2b e2c q1 q2 A w wa wb x)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c1 c2 e1a c1a c2a q1 A w wa wb x a b xa)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac n c1 c2 e1a c1a c2a e2b e2c q1 q2 A w wa wb x)(*strict*)
  apply(erule disjE)+
   apply(rename_tac n c1 c2 e1a c1a c2a e2b e2c q1 q2 A w wa wb x)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c1 c2 e1a c1a c2a q1 q2 A w wa wb x xa a b)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac n c1 c2 e1a c1a c2a e2b e2c q1 q2 A w wa wb x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c1 c2 e1a c1a c2a q1 q2 A w wa wb x xa xb)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

definition DPDA_OTS__translate_back :: "
  ((('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label, (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation"
  where
    "DPDA_OTS__translate_back d \<equiv>
  \<lambda>n.
    if n = 0
    then Some (pair
                None
                (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R
                  (case d 0 of
                  Some (pair e c) \<Rightarrow> c)))
    else
      case (d ((n + n) -Suc 0)) of
      None \<Rightarrow> None
      | Some (pair e c) \<Rightarrow>
          Some (pair
                  (if n = 0
                  then None
                  else
                    (case e of
                    None \<Rightarrow> None
                    | Some e' \<Rightarrow> Some (F_DPDA_OTS__epdaH_epdaH__RL__edge e')))
                  (F_DPDA_OTS__epdaH_epdaH__LR__configuration1R c))"

lemma F_DPDA_OTS__translateB__preserves__derivation: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial (F_DPDA_OTS G) d
  \<Longrightarrow> \<forall>n. d n \<noteq> None
  \<Longrightarrow> epdaH.derivation G (DPDA_OTS__translate_back d)"
  apply(simp (no_asm) add: epdaH.derivation_def DPDA_OTS__translate_back_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="0"
      and m="Suc 0"
      in epdaH.step_detail_before_some_position)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e1 e2 c1 c2)(*strict*)
    prefer 2
    apply(rule_tac
      n="0"
      in F_DPDA_OTS__enforces__cons_state_and_stack_cons_state_alternation)
       apply(rename_tac e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 q1 q2 A)(*strict*)
   apply(simp add: epdaH_step_relation_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 q1 q2 A w)(*strict*)
   apply(case_tac c1)
   apply(rename_tac e1 e2 c1 c2 q1 q2 A w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac c2)
   apply(rename_tac e1 e2 c1 c2 q1 q2 A w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 q1 q2 A w epdaH_conf_history)(*strict*)
   apply(case_tac e1)
    apply(rename_tac e1 e2 q1 q2 A w epdaH_conf_history)(*strict*)
    apply(case_tac e2)
    apply(rename_tac e1 e2 q1 q2 A w epdaH_conf_history edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 q2 A w epdaH_conf_history edge_eventa edge_popa edge_pusha)(*strict*)
    apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__edge_def)
    apply(rename_tac q1 q2 A w epdaH_conf_history edge_event edge_pop edge_push)(*strict*)
    apply(simp add: F_DPDA_OTS__get_state_def F_DPDA_OTS__edges_def)
    apply(erule disjE)+
     apply(rename_tac q1 q2 A w epdaH_conf_history edge_event edge_pop edge_push)(*strict*)
     apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
     apply(clarsimp)
    apply(rename_tac q1 q2 A w epdaH_conf_history edge_event edge_pop edge_push)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 A w epdaH_conf_history edge_event edge_pop edge_push x)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(rename_tac q1 q2 A w epdaH_conf_history edge_eventa edge_popa edge_pusha x)(*strict*)
    apply(clarsimp)
    apply(rename_tac w epdaH_conf_history x)(*strict*)
    apply(case_tac x)
    apply(rename_tac w epdaH_conf_history x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(rename_tac e1 e2 q1 q2 A w epdaH_conf_history a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e2 q1 q2 A w epdaH_conf_history a)(*strict*)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__edge_def)
   apply(simp add: F_DPDA_OTS__get_state_def F_DPDA_OTS__edges_def)
   apply(erule disjE)+
    apply(rename_tac e2 q1 q2 A w epdaH_conf_history a)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
   apply(rename_tac e2 q1 q2 A w epdaH_conf_history a)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac q1 q2 A w epdaH_conf_history a x)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
   apply(rename_tac w epdaH_conf_history a x)(*strict*)
   apply(case_tac x)
   apply(rename_tac w epdaH_conf_history a x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac nata)(*strict*)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(case_tac "(d (Suc (Suc (Suc (n + n)))))")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc (Suc (n + n))"
      and m="(Suc (Suc (Suc (n + n))))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      n="(Suc (n + n))"
      and m="(Suc (Suc (Suc (n + n))))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc n"
      in F_DPDA_OTS__enforces__cons_state_and_stack_cons_state_alternation)
      apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
      apply(force)
     apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
     apply(force)
    apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
    apply(force)
   apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
   apply(force)
  apply(rename_tac n e1a e2 e2a c1 c1a c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1a e2 e2a c1 c1a c2 q1 q2 A)(*strict*)
  apply(simp add: epdaH_step_relation_def der1_def get_configuration_def epdaH_initial_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(clarsimp)
  apply(rename_tac n e1a e2 e2a c1 c1a c2 q1 q2 A w wa)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac n e1a e2 e2a c1 c1a c2 q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n e1a e2 e2a c1 c1a c2 q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(case_tac c2)
  apply(rename_tac n e1a e2 e2a c1 c1a c2 q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac n e1a e2 e2a c1 c1a c2 q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1a e2 q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha epdaH_conf_historyb)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n e1a e2 q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha epdaH_conf_historyb edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1a q1 q2 A w wa edge_srca edge_eventa edge_popa edge_pusha epdaH_conf_historyb edge_eventaa edge_popaa edge_pushaa)(*strict*)
  apply(rename_tac qs r po pu h qs2 r2 po2 pu2 qt2)
  apply(rename_tac n e1a q1 q2 A qs r po pu h qs2 r2 po2 pu2 qt2)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__edge_def)
  apply(simp add: F_DPDA_OTS__get_state_def F_DPDA_OTS__edges_def)
  apply(erule disjE)+
    apply(rename_tac n e1a q1 q2 A qs r po pu h qs2 r2 po2 pu2 qt2)(*strict*)
    apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
    apply(clarsimp)
   apply(rename_tac n e1a q1 q2 A qs r po pu h qs2 r2 po2 pu2 qt2)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
  apply(rename_tac n e1a q1 q2 A qs r po pu h qs2 r2 po2 pu2 qt2)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac n e1a q1 q2 A qs r po pu h qs2 r2 po2 pu2 qt2 x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac n e1a qs r po pu h qs2 r2 x)(*strict*)
  apply(erule disjE)+
   apply(rename_tac n e1a qs r po pu h qs2 r2 x)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1a qs r r2 x)(*strict*)
   apply(case_tac x)
   apply(rename_tac n e1a qs r r2 x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1a qs r r2 edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
   apply(simp add: option_to_list_def F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(rename_tac n e1a qs r po pu h qs2 r2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1a qs r po pu h qs2 r2 x xa)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

lemma F_DPDA_OTS__translateB__preserves__derivation_initial: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial (F_DPDA_OTS G) d
  \<Longrightarrow> \<forall>n. d n \<noteq> None
  \<Longrightarrow> epdaH.derivation_initial G (DPDA_OTS__translate_back d)"
  apply(simp (no_asm) add: epdaH.derivation_initial_def)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__translateB__preserves__derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: DPDA_OTS__translate_back_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="0"
      and m="Suc 0"
      in epdaH.step_detail_before_some_position)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 \<in> epdaH_configurations (F_DPDA_OTS G)")
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac e1 e2 c1 c2)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac e1 e2 c1 c2)(*strict*)
     apply(subgoal_tac "X" for X)
      apply(rename_tac e1 e2 c1 c2)(*strict*)
      prefer 2
      apply(rule F_DPDA_OTS__preserves__PDA)
       apply(rename_tac e1 e2 c1 c2)(*strict*)
       apply(simp add: valid_dpda_def)
       apply(force)
      apply(rename_tac e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c1 c2)(*strict*)
     apply(simp add: valid_pda_def)
    apply(rename_tac e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac e2 c1 c2)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def epdaH_initial_configurations_def F_DPDA_OTS_def epdaH_configurations_def F_DPDA_OTS__states_def)
  apply(clarsimp)
  apply(rename_tac e2 q s h)(*strict*)
  apply(erule_tac
      P="cons_state_and_stack (epda_initial G) (epda_box G) \<in> F_DPDA_OTS__states_auxiliary G"
      in disjE)
   apply(rename_tac e2 q s h)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_OTS__states_auxiliary_def F_DPDA_OTS__states_main_def)
   apply(clarsimp)
  apply(rename_tac e2 q s h)(*strict*)
  apply(simp add: epdaH_step_relation_def F_DPDA_OTS__edges_def)
  apply(clarsimp)
  apply(rename_tac e2 w)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_DPDA_OTS__edges_main_auxiliary G"
      in disjE)
   apply(rename_tac e2 w)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
   apply(clarsimp)
  apply(rename_tac e2 w)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac w x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_OTS__get_state_def F_DPDA_OTS__edges_def)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  done

theorem F_DPDA_OTS__preserves__no_livelock: "
  valid_dpda G
  \<Longrightarrow> \<not> epdaH_livelock G
  \<Longrightarrow> \<not> epdaH_livelock (F_DPDA_OTS G)"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(rule ccontr)
  apply(clarsimp)
  apply(erule_tac
      x="DPDA_OTS__translate_back d"
      in allE)
  apply(erule impE)
   apply(rename_tac d N)(*strict*)
   apply(rule F_DPDA_OTS__translateB__preserves__derivation_initial)
     apply(rename_tac d N)(*strict*)
     apply(force)
    apply(rename_tac d N)(*strict*)
    apply(force)
   apply(rename_tac d N)(*strict*)
   apply(force)
  apply(rename_tac d N)(*strict*)
  apply(erule disjE)
   apply(rename_tac d N)(*strict*)
   apply(clarsimp)
   apply(rename_tac d N n)(*strict*)
   apply(simp add: DPDA_OTS__translate_back_def)
   apply(case_tac n)
    apply(rename_tac d N n)(*strict*)
    apply(clarsimp)
   apply(rename_tac d N n nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d N nat)(*strict*)
   apply(case_tac "d(Suc(nat+nat))")
    apply(rename_tac d N nat)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="Suc(nat+nat)"
      and P="\<lambda>x. \<exists>y. d x = Some y"
      in allE)
    apply(force)
   apply(rename_tac d N nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d N nat a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="N"
      and P="\<lambda>N. \<exists>n\<ge>N. epdaH_conf_history (the (get_configuration (DPDA_OTS__translate_back d n))) \<noteq> epdaH_conf_history (the (get_configuration (DPDA_OTS__translate_back d N)))"
      in allE)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n)(*strict*)
  apply(simp add: DPDA_OTS__translate_back_def)
  apply(case_tac n)
   apply(rename_tac d N n)(*strict*)
   apply(clarsimp)
  apply(rename_tac d N n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N nat)(*strict*)
  apply(case_tac N)
   apply(rename_tac d N nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d nat)(*strict*)
   apply(case_tac "d 0")
    apply(rename_tac d nat)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="0"
      and P="\<lambda>x. \<exists>y. d x = Some y"
      in allE)
    apply(force)
   apply(rename_tac d nat a)(*strict*)
   apply(case_tac "d (Suc (nat + nat))")
    apply(rename_tac d nat a)(*strict*)
    apply(clarsimp)
    apply(erule_tac x="Suc (nat + nat)" and P="\<lambda>x. \<exists>y. d x = Some y"in allE)
    apply(force)
   apply(rename_tac d nat a aa)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d nat a aa option b)(*strict*)
   apply(case_tac aa)
   apply(rename_tac d nat a aa option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac d nat option b optiona ba)(*strict*)
   apply(case_tac optiona)
    apply(rename_tac d nat option b optiona ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac d nat option b ba)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d nat option b ba)(*strict*)
     prefer 2
     apply(rule_tac
      g="d"
      and n="Suc(nat+nat)"
      and m="Suc(nat+nat)"
      in epdaH.pre_some_position_is_some_position_prime)
        apply(rename_tac d nat option b ba)(*strict*)
        apply(rule epdaH.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac d nat option b ba)(*strict*)
       apply(force)
      apply(rename_tac d nat option b ba)(*strict*)
      apply(force)
     apply(rename_tac d nat option b ba)(*strict*)
     apply(force)
    apply(rename_tac d nat option b ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac d nat option b optiona ba a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d nat option b ba a)(*strict*)
   apply(simp add: get_configuration_def)
   apply(erule_tac
      x="Suc (nat+nat)"
      and P="\<lambda>x. epdaH_conf_history (the (case d x of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = epdaH_conf_history b"
      in allE)
   apply(rename_tac d nat option b ba a)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(rename_tac d N nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat nata)(*strict*)
  apply(case_tac "d (Suc (nat + nat))")
   apply(rename_tac d nat nata)(*strict*)
   apply(clarsimp)
   apply(erule_tac x="(Suc (nat + nat))" and P="\<lambda>x. \<exists>y. d x = Some y"in allE)
   apply(force)
  apply(rename_tac d nat nata a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d nat nata a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat nata option b)(*strict*)
  apply(case_tac "d (Suc (nata + nata))")
   apply(rename_tac d nat nata option b)(*strict*)
   apply(clarsimp)
   apply(erule_tac x="(Suc (nata + nata))" and P="\<lambda>x. \<exists>y. d x = Some y"in allE)
   apply(force)
  apply(rename_tac d nat nata option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d nat nata option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat nata option b optiona ba)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac d nat nata option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac d nat nata option b ba)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d nat nata option b ba)(*strict*)
    prefer 2
    apply(rule_tac
      g="d"
      and n="Suc(nata+nata)"
      and m="Suc(nata+nata)"
      in epdaH.pre_some_position_is_some_position_prime)
       apply(rename_tac d nat nata option b ba)(*strict*)
       apply(rule epdaH.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d nat nata option b ba)(*strict*)
      apply(force)
     apply(rename_tac d nat nata option b ba)(*strict*)
     apply(force)
    apply(rename_tac d nat nata option b ba)(*strict*)
    apply(force)
   apply(rename_tac d nat nata option b ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac d nat nata option b optiona ba a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat nata option b ba a)(*strict*)
  apply(case_tac option)
   apply(rename_tac d nat nata option b ba a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d nat nata b ba a)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d nat nata b ba a)(*strict*)
    prefer 2
    apply(rule_tac
      g="d"
      and n="Suc(nat+nat)"
      and m="Suc(nat+nat)"
      in epdaH.pre_some_position_is_some_position_prime)
       apply(rename_tac d nat nata b ba a)(*strict*)
       apply(rule epdaH.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d nat nata b ba a)(*strict*)
      apply(force)
     apply(rename_tac d nat nata b ba a)(*strict*)
     apply(force)
    apply(rename_tac d nat nata b ba a)(*strict*)
    apply(force)
   apply(rename_tac d nat nata b ba a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d nat nata option b ba a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat nata b ba a aa)(*strict*)
  apply(simp add: get_configuration_def)
  apply(erule_tac
      x="Suc (nat+nat)"
      and P="\<lambda>x. Suc nata \<le> x \<longrightarrow> epdaH_conf_history (the (case d x of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = epdaH_conf_history (the (case d (Suc nata) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c))"
      in allE)
  apply(rename_tac d nat nata b ba a aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d nat nata b ba a aa)(*strict*)
   prefer 2
   apply(rule_tac
      g="d"
      and n="Suc nata"
      and m="Suc(nat+nat)"
      in epdaH.pre_some_position_is_some_position_prime)
      apply(rename_tac d nat nata b ba a aa)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d nat nata b ba a aa)(*strict*)
     apply(force)
    apply(rename_tac d nat nata b ba a aa)(*strict*)
    apply(force)
   apply(rename_tac d nat nata b ba a aa)(*strict*)
   apply(force)
  apply(rename_tac d nat nata b ba a aa)(*strict*)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  apply(clarsimp)
  apply(rename_tac d nat nata b ba a aa e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d nat nata b ba a aa e c)(*strict*)
   prefer 2
   apply(rule F_DPDA_OTS__preserves__PDA)
    apply(rename_tac d nat nata b ba a aa e c)(*strict*)
    apply(simp add: valid_dpda_def)
    apply(force)
   apply(rename_tac d nat nata b ba a aa e c)(*strict*)
   apply(force)
  apply(rename_tac d nat nata b ba a aa e c)(*strict*)
  apply(simp add: valid_pda_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d nat nata b ba a aa e c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="Suc nata"
      and m="nata"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d nat nata b ba a aa e c)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(force)
      apply(rename_tac d nat nata b ba a aa e c)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d nat nata b ba a aa e c)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d nat nata b ba a aa e c)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d nat nata b ba a aa e c)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d nat nata b ba a aa e c)(*strict*)
      apply(force)
     apply(rename_tac d nat nata b ba a aa e c)(*strict*)
     apply(force)
    apply(rename_tac d nat nata b ba a aa e c)(*strict*)
    apply(force)
   apply(rename_tac d nat nata b ba a aa e c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d nat nata b ba a aa e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d nat nata b ba a aa e c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="Suc (nata + nata)"
      and m="Suc (nat + nat)-Suc (nata + nata)"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d nat nata b ba a aa e c)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(force)
      apply(rename_tac d nat nata b ba a aa e c)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d nat nata b ba a aa e c)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d nat nata b ba a aa e c)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d nat nata b ba a aa e c)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d nat nata b ba a aa e c)(*strict*)
      apply(force)
     apply(rename_tac d nat nata b ba a aa e c)(*strict*)
     apply(force)
    apply(rename_tac d nat nata b ba a aa e c)(*strict*)
    apply(force)
   apply(rename_tac d nat nata b ba a aa e c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d nat nata b ba a aa e c)(*strict*)
  apply(force)
  done

definition main_states_have_only_empty_steps :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "main_states_have_only_empty_steps R F \<equiv>
  \<forall>q \<in> epda_states R.
    F q
    \<longrightarrow>
      (\<forall>e.
        e \<in> epda_delta R
        \<longrightarrow> edge_src e = q
        \<longrightarrow> edge_event e = None)"

theorem F_DPDA_OTS__enforces__main_states_have_only_empty_steps: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> main_states_have_only_empty_steps R F_DPDA_OTS__is_main"
  apply(simp add: main_states_have_only_empty_steps_def F_DPDA_OTS__is_main_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(case_tac "edge_src e")
   apply(rename_tac e a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac e a)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(erule disjE)
   apply(rename_tac e a)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(clarsimp)
  apply(rename_tac e a)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def)
  apply(clarsimp)
  apply(rename_tac a x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

definition main_states_have_all_empty_steps :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "main_states_have_all_empty_steps R F \<equiv>
  \<forall>q \<in> epda_states R.
    F q
    \<longrightarrow>
      (\<forall>X \<in> epda_gamma R.
        \<exists>e.
          e \<in> epda_delta R
          \<and> edge_src e = q
          \<and> edge_pop e = [X]
          \<and> edge_event e = None)"

theorem F_DPDA_OTS__enforces__main_states_have_all_empty_steps: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> main_states_have_all_empty_steps R F_DPDA_OTS__is_main"
  apply(simp add: main_states_have_all_empty_steps_def F_DPDA_OTS__is_main_def)
  apply(clarsimp)
  apply(rename_tac q X)(*strict*)
  apply(case_tac q)
   apply(rename_tac q X a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac q X a)(*strict*)
  apply(clarsimp)
  apply(rename_tac X a)(*strict*)
  apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(rule_tac
      x="\<lparr>edge_src=cons_state a,edge_event=None,edge_pop=[X],edge_push=[X],edge_trg=cons_state_and_stack a X\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac X a)(*strict*)
   apply(rule disjI1)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(rule inMap)
   apply(clarsimp)
   apply(simp add: F_DPDA_OTS__states_def)
   apply(erule disjE)
    apply(rename_tac X a)(*strict*)
    apply(simp add: F_DPDA_OTS__states_auxiliary_def)
    apply(clarsimp)
   apply(rename_tac X a)(*strict*)
   apply(simp add: F_DPDA_OTS__states_main_def)
   apply(clarsimp)
  apply(rename_tac X a)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  done

definition executing_edge_from_auxiliary_to_main_state :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "executing_edge_from_auxiliary_to_main_state R F1 F2 \<equiv>
  \<forall>e.
    e \<in> epda_delta R
    \<longrightarrow> edge_event e \<noteq> None
    \<longrightarrow> (F1 (edge_src e) \<and> F2 (edge_trg e))"

theorem F_DPDA_OTS__enforces__executing_edge_from_auxiliary_to_main_state: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> executing_edge_from_auxiliary_to_main_state R F_DPDA_OTS__is_auxiliary F_DPDA_OTS__is_main"
  apply(simp add: executing_edge_from_auxiliary_to_main_state_def)
  apply(clarsimp)
  apply(rename_tac e y)(*strict*)
  apply(simp add: F_DPDA_OTS__is_main_def F_DPDA_OTS__is_auxiliary_def)
  apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(erule disjE)
   apply(rename_tac e y)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(clarsimp)
  apply(rename_tac e y)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def)
  apply(clarsimp)
  apply(rename_tac y x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_1_def)
  done

definition main_to_auxiliary_or_auxiliary_to_main :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "main_to_auxiliary_or_auxiliary_to_main R Fmain \<equiv>
  \<forall>e \<in> epda_delta R. Fmain (edge_src e) \<longleftrightarrow> \<not> Fmain (edge_trg e)"

theorem F_DPDA_OTS__enforces__main_to_auxiliary_or_auxiliary_to_main: "
  valid_dpda M
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> main_to_auxiliary_or_auxiliary_to_main R F_DPDA_OTS__is_main"
  apply(simp add: main_to_auxiliary_or_auxiliary_to_main_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_OTS_def F_DPDA_OTS__edges_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_DPDA_OTS__edges_main_auxiliary_def F_DPDA_OTS__edges_main_auxiliary_1_def)
   apply(clarsimp)
   apply(rename_tac a b)(*strict*)
   apply(simp add: F_DPDA_OTS__is_main_def)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_OTS__edges_auxiliary_main_def F_DPDA_OTS__edges_auxiliary_main_1_def)
  apply(simp add: F_DPDA_OTS__is_main_def)
  done

theorem F_DPDA_OTS__preserves__epdaH_reflection_to_DFA_exists: "
  valid_dpda M
  \<Longrightarrow> epdaH_reflection_to_DFA_exists M D F
  \<Longrightarrow> R = F_DPDA_OTS M
  \<Longrightarrow> epdaH_reflection_to_DFA_exists R D (F \<circ> F_DPDA_OTS__get_state)"
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
   apply(rule_tac
      ?G2.0="M"
      and ?G1.0="F_DPDA_OTS M"
      and ?d1.0="d"
      and x="n"
      in F_DPDA_OTS__epdaH_epdaH__RL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac d n c option)(*strict*)
     apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__TSstructure_def)
    apply(rename_tac d n c option)(*strict*)
    apply(force)
   apply(rename_tac d n c option)(*strict*)
   apply(force)
  apply(rename_tac d n c option)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option d2 n2)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="n2"
      in allE)
  apply(case_tac "d2 n2")
   apply(rename_tac d n c option d2 n2)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac d n c option d2 n2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n c option d2 n2 a optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option d2 n2 optiona b)(*strict*)
  apply(erule_tac
      x="b"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c option d2 n2 optiona b)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d n c option d2 n2 optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option d2 n2 optiona b d' m)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="m"
      in exI)
  apply(clarsimp)
  apply(simp add: F_DPDA_OTS__epdaH_epdaH__RL__configurations_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def F_DPDA_OTS__epdaH_epdaH__LR__configuration1R_def)
  done

definition F_DPDA_OTS__SpecInput :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__SpecInput G D \<equiv>
  valid_dpda G
  \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)
  \<and> \<not> epdaH_livelock G
  \<and> epdaH_reflection_to_DFA_exists G D sel_tuple2_2"

definition F_DPDA_OTS__SpecOutput :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epda
  \<Rightarrow> (('stateB, 'event, 'stackB) epda \<times> 'event set)
  \<Rightarrow> ((('stateA, 'stateB) DT_tuple2, 'stackA) DT_state_and_stack_or_state, 'event, 'stackA) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_OTS__SpecOutput Gi X Go \<equiv>
  case X of 
  (D, \<Sigma>UC) \<Rightarrow>
    valid_dpda Go
    \<and> epdaH.marked_language Gi = epdaH.marked_language Go
    \<and> epdaH.unmarked_language Gi = epdaH.unmarked_language Go
    \<and> nonblockingness_language (epdaH.unmarked_language Go) (epdaH.marked_language Go)
    \<and> state_stack_unique_for_marking_states Go
    \<and> state_stack_unique_for_stable_states Go
    \<and> always_applicable_for_stable_states Go
    \<and> some_edge_applicable Go
    \<and> \<not> epdaH_livelock Go
    \<and> epdaH_reflection_to_DFA_exists Go D (sel_tuple2_2 \<circ> F_DPDA_OTS__get_state)
    \<and> corresponds_to_top_stack Go F_DPDA_OTS__is_auxiliary F_DPDA_OTS__get_stack
    \<and> main_states_have_only_empty_steps Go F_DPDA_OTS__is_main
    \<and> main_states_have_all_empty_steps Go F_DPDA_OTS__is_main
    \<and> executing_edge_from_auxiliary_to_main_state Go F_DPDA_OTS__is_auxiliary F_DPDA_OTS__is_main
    \<and> always_applicable_for_auxiliary_states Go F_DPDA_OTS__is_auxiliary
    \<and> main_to_auxiliary_or_auxiliary_to_main Go F_DPDA_OTS__is_main" 


theorem F_DPDA_OTS__SOUND: "
  F_DPDA_OTS__SpecInput G P
  \<Longrightarrow> F_DPDA_OTS__SpecOutput G (P, \<Sigma>UC) (F_DPDA_OTS G)"
  apply(simp add: F_DPDA_OTS__SpecOutput_def F_DPDA_OTS__SpecInput_def)
  apply(rule context_conjI)
   apply (metis F_DPDA_OTS__preserves__DPDA)
  apply(rule context_conjI)
   apply (metis F_DPDA_OTS__equal__marked_language)
  apply(rule context_conjI)
   apply (metis F_DPDA_OTS__equal__unmarked_language)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply (metis F_DPDA_OTS__enforces__state_stack_unique_for_marking_states)
  apply(rule conjI)
   apply (metis F_DPDA_OTS__enforces___state_stack_unique_for_stable_states)
  apply(rule conjI)
   apply(metis F_DPDA_OTS__enforces__always_applicable_for_stable_states)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__enforces__some_edge_applicable)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__preserves__no_livelock)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__preserves__epdaH_reflection_to_DFA_exists)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__enforces__corresponds_to_top_stack)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__enforces__main_states_have_only_empty_steps)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__enforces__main_states_have_all_empty_steps)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__enforces__executing_edge_from_auxiliary_to_main_state)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_OTS__enforces__always_applicable_for_auxiliary_states)
    apply(force)
   apply(force)
  apply(rule F_DPDA_OTS__enforces__main_to_auxiliary_or_auxiliary_to_main)
   apply(force)
  apply(force)
  done

end
