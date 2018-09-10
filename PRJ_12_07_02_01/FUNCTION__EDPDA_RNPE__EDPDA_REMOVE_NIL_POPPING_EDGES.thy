section {*FUNCTION\_\_EDPDA\_RNPE\_\_EDPDA\_REMOVE\_NIL\_POPPING\_EDGES*}
theory
  FUNCTION__EDPDA_RNPE__EDPDA_REMOVE_NIL_POPPING_EDGES

imports
  PRJ_12_07_02_01__ENTRY

begin

definition F_EDPDA_RNPE__edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_EDPDA_RNPE__edge e X \<equiv>
  \<lparr>edge_src = edge_src e,
  edge_event = edge_event e,
  edge_pop = [X],
  edge_push = edge_push e @ [X],
  edge_trg = edge_trg e\<rparr>"

definition F_EDPDA_RNPE__edges_rev :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_EDPDA_RNPE__edges_rev e \<equiv>
  \<lparr>edge_src = edge_src e,
  edge_event = edge_event e,
  edge_pop = [],
  edge_push = butlast (edge_push e),
  edge_trg = edge_trg e\<rparr>"

lemma F_EDPDA_RNPE_preserves_valid_epda: "
  valid_epda M
  \<Longrightarrow> valid_epda (F_EDPDA_RNPE M)"
  apply(simp add: F_EDPDA_RNPE_def valid_epda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edges_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(clarsimp)
   apply(rename_tac xa xb)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa xb)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(case_tac "xb=epda_box M")
     apply(rename_tac xa xb)(*strict*)
     apply(rule_tac
      x="[]"
      in exI)
     apply(force)
    apply(rename_tac xa xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa xb)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa xb)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(case_tac "xb=epda_box M")
     apply(rename_tac xa xb)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa)(*strict*)
     apply(rule_tac
      x="edge_push xa"
      in exI)
     apply(force)
    apply(rename_tac xa xb)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb x)(*strict*)
    apply(force)
   apply(rename_tac xa xb)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac xa xb)(*strict*)
    apply(clarsimp)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac xa x)(*strict*)
    apply(force)
   apply(rename_tac xa xb)(*strict*)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(force)
  done

lemma F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges: "
  valid_epda M
  \<Longrightarrow> epda_no_nil_popping_edges (F_EDPDA_RNPE M)"
  apply(simp add: epda_no_nil_popping_edges_def F_EDPDA_RNPE_def F_EDPDA_RNPE__edges_def)
  apply(clarsimp)
  apply(force)
  done

definition F_EDPDA_RNPE_relation_LR_TSstructure :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<equiv>
  valid_epda G1
  \<and> G2 = F_EDPDA_RNPE G1"

definition F_EDPDA_RNPE_relation_LR_configuration :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = c1"

definition F_EDPDA_RNPE_relation_LR_initial_configuration :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = c1"

definition F_EDPDA_RNPE_relation_LR_effect :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_effect G1 G2 w1 w2 \<equiv>
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_EDPDA_RNPE_relation_LR_TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(rule F_EDPDA_RNPE_preserves_valid_epda)
  apply(force)
  done

definition F_EDPDA_RNPE_relation_LR_step_simulation :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack DT_symbol) epda_step_label, ('state, 'event, 'stack DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  d = der2
        c1
          (if edge_pop e = []
          then F_EDPDA_RNPE__edge e (epdaS_conf_stack c1 ! 0)
          else e)
        c1'"

definition F_EDPDA_RNPE_relation_LR_initial_simulation :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack DT_symbol) epda_step_label, ('state, 'event, 'stack DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 c1"

lemma F_EDPDA_RNPE_C_preserves_configurations: "
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  done

lemma F_EDPDA_RNPE_C_preserves_initial_configurations: "
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  apply(simp add: epdaS_configurations_def)
  done

lemma F_EDPDA_RNPE_C_preserves_marking_configurations: "
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  apply(simp add: epdaS_configurations_def)
  done

lemma F_EDPDA_RNPE_initial_simulation_preserves_derivation: "
  F_EDPDA_RNPE_relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> epdaS.derivation_initial G2 (der1 c1)"
  apply(rule epdaS.derivation_initialI)
   apply(rule epdaS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_EDPDA_RNPE_C_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EDPDA_RNPE_relation_LR_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_EDPDA_RNPE_initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_initial_configuration_def)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def valid_pda_def valid_dpda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RNPE_relation_LR_step_simulation_maps_to_derivation: "
  F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulation_def)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply (metis (full_types) epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
  apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
    apply(force)
   apply(rule_tac
      G="G1"
      in epda_nonempty_stack)
    apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
   apply(force)
  apply(case_tac "edge_pop e1")
   apply(clarsimp)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: F_EDPDA_RNPE__edge_def)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rule conjI)
    prefer 2
    apply(case_tac "epdaS_conf_stack c1")
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
    apply(force)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
    apply(simp add: epdaS_configurations_def)
    apply(clarsimp)
    apply(rename_tac s)(*strict*)
    apply(case_tac s)
     apply(rename_tac s)(*strict*)
     apply(force)
    apply(rename_tac s a list)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac a list w)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  apply(force)
  done

lemma F_EDPDA_RNPE_relation_LR_step_simulation_maps_to_derivation_belongs: "
  F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.belongs G2 d2"
  apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulation_def)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply (metis (full_types) epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
  apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
    apply(force)
   apply(rule_tac
      G="G1"
      in epda_nonempty_stack)
    apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
   apply(force)
  apply(subgoal_tac "e1 \<in> epda_delta G1")
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(case_tac "edge_pop e1")
   apply(clarsimp)
   apply(rule epdaS.der2_belongs)
     apply (metis F_EDPDA_RNPE_C_preserves_configurations F_EDPDA_RNPE_relation_LR_configuration_def)
    apply(simp add: F_EDPDA_RNPE__edge_def epda_step_labels_def)
    apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
    apply(clarsimp)
    apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def F_EDPDA_RNPE_def)
    apply(clarsimp)
    apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
     apply(force)
    apply(simp add: F_EDPDA_RNPE__edges_def)
    apply(case_tac "epdaS_conf_stack c1")
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaS_configurations_def)
    apply(force)
   apply (metis F_EDPDA_RNPE_C_preserves_configurations epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EDPDA_RNPE_relation_LR_configuration_def epdaS.AX_step_relation_preserves_belongs)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der2_belongs)
    apply(rename_tac a list)(*strict*)
    apply (metis F_EDPDA_RNPE_C_preserves_configurations F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(rename_tac a list)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edge_def epda_step_labels_def)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def F_EDPDA_RNPE_def)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply (metis F_EDPDA_RNPE_C_preserves_configurations epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EDPDA_RNPE_relation_LR_configuration_def epdaS.AX_step_relation_preserves_belongs)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: epda_step_labels_def)
   apply (metis (full_types)  epdaS.get_accessible_configurations_are_configurations subsetD)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule_tac
      G="G1"
      in epda_nonempty_stack)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="der2 c1 (if edge_pop e1=[] then F_EDPDA_RNPE__edge e1 (epdaS_conf_stack c1!0) else e1) c1'"
      in exI)
  apply(subgoal_tac "F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 (der2 c1 (if edge_pop e1 = [] then F_EDPDA_RNPE__edge e1 (epdaS_conf_stack c1 ! 0) else e1) c1')")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulation_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(subgoal_tac "epdaS.derivation G2 (der2 c1 (if edge_pop e1 = [] then F_EDPDA_RNPE__edge e1 (epdaS_conf_stack c1 ! 0) else e1) c1')")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(rule F_EDPDA_RNPE_relation_LR_step_simulation_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(subgoal_tac "epdaS.belongs G2 (der2 c1 (if edge_pop e1 = [] then F_EDPDA_RNPE__edge e1 (epdaS_conf_stack c1 ! 0) else e1) c1')")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(rule F_EDPDA_RNPE_relation_LR_step_simulation_maps_to_derivation_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def der2_def)
   apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulation_def)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(clarsimp)
   apply(simp add: der2_def)
   apply(simp add: maximum_of_domain_def)
   apply (rule epdaS.der2_preserves_get_accessible_configurations)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply (metis epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def der2_def)
  apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulation_def)
  apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(simp add: maximum_of_domain_def)
  apply (rule epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply (metis epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_configuration F_EDPDA_RNPE_relation_LR_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_REPZ_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_REPZ_StateSimLR": ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RNPE_relation_LR_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RNPE_relation_LR_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RNPE_relation_LR_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RNPE_relation_LR_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RNPE_relation_LR_initial_simulation"
  (* relation_step_simulation *)
  "F_EDPDA_RNPE_relation_LR_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation_marking_condition: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(rule F_EDPDA_RNPE_C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_EDPDA_RNPE_C_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RNPE_C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_configuration F_EDPDA_RNPE_relation_LR_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_REPZ_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_REPZ_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_REPZ_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_REPZ_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_LR_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_effect_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RNPE_relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation_marked_effect: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_LR_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_effect_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RNPE_relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_configuration F_EDPDA_RNPE_relation_LR_effect F_EDPDA_RNPE_relation_LR_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_REPZ_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_REPZ_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_REPZ_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_REPZ_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation_marked_effect)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation_unmarked_effect: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_LR_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(subgoal_tac "c'=c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x="c1'"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "c=ca")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def)
   apply(simp add: F_EDPDA_RNPE_relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca)(*strict*)
  apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="Suc deri1n"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca option b)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e)(*strict*)
  apply(rule_tac
      x="deri2n+n"
      in exI)
  apply(simp add: derivation_append_def)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation_unmarked_effect: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_LR_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_relation_LR_configuration_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_EDPDA_RNPE_relation_LR_configuration F_EDPDA_RNPE_relation_LR_initial_configuration F_EDPDA_RNPE_relation_LR_effect F_EDPDA_RNPE_relation_LR_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulation F_EDPDA_RNPE_relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_REPZ_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_REPZ_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_REPZ_StateSimLR_inst_relation_step_simulation_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_REPZ_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_REPZ_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_REPZ_StateSimLR_inst_relation_initial_simulation_unmarked_effect)
  done

interpretation "epdaS_epdaS_REPZ_StateSimLR": ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RNPE_relation_LR_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RNPE_relation_LR_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RNPE_relation_LR_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RNPE_relation_LR_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RNPE_relation_LR_initial_simulation"
  (* relation_step_simulation *)
  "F_EDPDA_RNPE_relation_LR_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms  epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms)
  done

lemma F_EDPDA_RNPE_preserves_lang1: "
  valid_epda G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_EDPDA_RNPE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS.AX_marked_language_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_EDPDA_RNPE G)"
      and s="epdaS.finite_marked_language (F_EDPDA_RNPE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (metis F_EDPDA_RNPE_preserves_valid_epda)
  apply(subgoal_tac "left_total_on (F_EDPDA_RNPE_relation_LR_effect SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_REPZ_StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_effect_def)
  done

lemma F_EDPDA_RNPE_preserves_unmarked_language1: "
  valid_epda G
  \<Longrightarrow> epdaS.unmarked_language G \<subseteq> epdaS.unmarked_language (F_EDPDA_RNPE G)"
  apply(rule_tac
      t="epdaS.unmarked_language G"
      and s="epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaS.AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_EDPDA_RNPE G)"
      and s="epdaS.finite_unmarked_language (F_EDPDA_RNPE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply (metis F_EDPDA_RNPE_preserves_valid_epda)
  apply(subgoal_tac "left_total_on (F_EDPDA_RNPE_relation_LR_effect SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_REPZ_StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_EDPDA_RNPE_relation_LR_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_effect_def)
  done

definition F_EDPDA_RNPE_relation_RL_TSstructure :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<equiv>
  valid_epda G2
  \<and> G1 = F_EDPDA_RNPE G2"

definition F_EDPDA_RNPE_relation_RL_configuration :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = c1"

definition F_EDPDA_RNPE_relation_RL_initial_configuration :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = c1"

definition F_EDPDA_RNPE_relation_RL_effect :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_RL_effect G1 G2 w1 w2 \<equiv>
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_REPZ_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_EDPDA_RNPE_relation_RL_TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(rule F_EDPDA_RNPE_preserves_valid_epda)
  apply(force)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  done

definition F_EDPDA_RNPE_relation_LR_step_simulationRL :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack DT_symbol) epda_step_label, ('state, 'event, 'stack DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 c1 e c1' c2 d \<equiv>
  d = der2
        c1
          (if e \<in> epda_delta G2
          then e
          else F_EDPDA_RNPE__edges_rev e)
        c1'"

definition F_EDPDA_RNPE_relation_LR_initial_simulationRL :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack DT_symbol) epda_step_label, ('state, 'event, 'stack DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_initial_simulationRL G1 G2 c1 d \<equiv>
  d = der1 c1"

lemma F_EDPDA_RNPE_C_rev_preserves_configurations: "
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  done

lemma F_EDPDA_RNPE_C_rev_preserves_initial_configurations: "
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  apply(simp add: epdaS_configurations_def)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EDPDA_RNPE_relation_LR_initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_initial_simulationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_EDPDA_RNPE_C_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_EDPDA_RNPE_relation_RL_initial_configuration_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
   apply (metis F_EDPDA_RNPE_preserves_valid_epda)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RNPE_relation_LR_step_simulationRL_maps_to_derivation: "
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<Longrightarrow> F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulationRL_def)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(clarsimp)
   apply (metis (full_types) F_EDPDA_RNPE_preserves_valid_epda F_EDPDA_RNPE_relation_RL_TSstructure_def epdaS.get_accessible_configurations_are_configurations subsetD)
  apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
   prefer 2
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(clarsimp)
   apply(subgoal_tac "epdaS_conf_stack c1 \<noteq> []")
    apply(force)
   apply(rule_tac
      G="G1"
      in epda_nonempty_stack)
    apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
    apply (metis F_EDPDA_RNPE_preserves_valid_epda)
   apply(force)
  apply(case_tac "e1 \<in> epda_delta G2")
   apply(clarsimp)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_EDPDA_RNPE__edges_rev_def)
  apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(case_tac "edge_pop e1")
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE__edges_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(case_tac e)
   apply(rename_tac w a x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulationRL_def)
  apply(case_tac "e1 \<in> epda_delta G2")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(simp add: epdaS_step_relation_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(simp add: epda_step_labels_def)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac G2 c1 e1 c1')(*strict*)
     apply(simp add: get_configuration_def der2_def)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(simp add: maximum_of_domain_def der2_def)
    apply(simp add: get_configuration_def)
    apply (metis F_EDPDA_RNPE_preserves_valid_epda epdaS.der2_is_derivation epdaS.der2_preserves_get_accessible_configurations)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac G2 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1')(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) F_EDPDA_RNPE_C_rev_preserves_configurations F_EDPDA_RNPE_preserves_valid_epda F_EDPDA_RNPE_relation_RL_TSstructure_def epdaS.get_accessible_configurations_are_configurations nset_mp)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def epda_step_labels_def)
  apply(simp add: F_EDPDA_RNPE__edges_rev_def)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w)(*strict*)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w x)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(erule disjE)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' w x xa)(*strict*)
    apply(case_tac x)
    apply(rename_tac G2 c1 c1' w x xa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac G2 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1')(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) F_EDPDA_RNPE_C_rev_preserves_configurations F_EDPDA_RNPE_preserves_valid_epda F_EDPDA_RNPE_relation_RL_TSstructure_def epdaS.get_accessible_configurations_are_configurations nset_mp)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' x w)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(erule disjE)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' x w xa)(*strict*)
    apply(case_tac w)
    apply(clarsimp)
   apply(force)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(simp add: maximum_of_domain_def der2_def get_configuration_def)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(clarsimp)
  apply(metis F_EDPDA_RNPE_preserves_valid_epda epdaS.der2_is_derivation epdaS.der2_preserves_get_accessible_configurations)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_RL_initial_configuration F_EDPDA_RNPE_relation_RL_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation epdaS_epdaS_REPZ_StateSimRL_step_relation_step_simulation epdaS_epdaS_REPZ_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs epdaS_epdaS_REPZ_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs)
  done

interpretation "epdaS_epdaS_REPZ_StateSimRL": ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  "F_EDPDA_RNPE_relation_RL_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RNPE_relation_RL_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RNPE_relation_RL_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RNPE_relation_RL_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RNPE_relation_LR_initial_simulationRL"
  (* relation_step_simulation *)
  "F_EDPDA_RNPE_relation_LR_step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_REPZ_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_EDPDA_RNPE_C_rev_preserves_marking_configurations: "
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def F_EDPDA_RNPE_def)
  apply (metis F_EDPDA_RNPE_C_rev_preserves_configurations)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_step_simulation_marking_condition: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RNPE_C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      t="ca"
      and s="the (get_configuration (derivation_append deri1 (der2 c1 e1 c1') deri1n i))"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_EDPDA_RNPE_C_rev_preserves_marking_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(simp add: epdaS.get_accessible_configurations_def)
    apply(rule_tac
      x="derivation_append deri1 (der2 c1 e1 c1') deri1n "
      in exI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation_initial)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
       apply (rule F_EDPDA_RNPE_preserves_valid_epda)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply (metis epdaS.derivation_initial_is_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(rule epdaS.der2_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c option b)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      x="Suc deri1n"
      in exI)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RNPE_C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_RL_initial_configuration F_EDPDA_RNPE_relation_RL_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_REPZ_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_REPZ_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_REPZ_StateSimRL_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_REPZ_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_REPZ_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_RL_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_effect_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RNPE_relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation_marked_effect: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_RL_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_effect_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RNPE_relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_RL_initial_configuration F_EDPDA_RNPE_relation_RL_effect F_EDPDA_RNPE_relation_RL_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_REPZ_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_REPZ_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_REPZ_StateSimRL_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_REPZ_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_REPZ_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation_marked_effect)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_step_simulation_unmarked_effect: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_RL_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(subgoal_tac "c'=c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x="c1'"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "c=ca")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def)
   apply(simp add: F_EDPDA_RNPE_relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca)(*strict*)
  apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="Suc deri1n"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca option b)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e)(*strict*)
  apply(rule_tac
      x="deri2n+n"
      in exI)
  apply(simp add: derivation_append_def)
  done

lemma epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation_unmarked_effect: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RNPE_relation_LR_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RNPE_relation_RL_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_REPZ_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RNPE_relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_EDPDA_RNPE_relation_RL_configuration F_EDPDA_RNPE_relation_RL_initial_configuration F_EDPDA_RNPE_relation_RL_effect F_EDPDA_RNPE_relation_RL_TSstructure F_EDPDA_RNPE_relation_LR_initial_simulationRL F_EDPDA_RNPE_relation_LR_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_REPZ_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_REPZ_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_REPZ_StateSimRL_inst_relation_step_simulation_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_REPZ_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_REPZ_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_REPZ_StateSimRL_inst_relation_initial_simulation_unmarked_effect)
  done

interpretation "epdaS_epdaS_REPZ_StateSimRL": ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RNPE_relation_RL_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RNPE_relation_RL_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RNPE_relation_RL_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RNPE_relation_RL_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RNPE_relation_LR_initial_simulationRL"
  (* relation_step_simulation *)
  "F_EDPDA_RNPE_relation_LR_step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_REPZ_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms epdaS_epdaS_REPZ_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms)
  done

lemma F_EDPDA_RNPE_preserves_lang2: "
  valid_epda G
  \<Longrightarrow> epdaS.marked_language G \<supseteq> epdaS.marked_language (F_EDPDA_RNPE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS_inst_lang_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_EDPDA_RNPE G)"
      and s="epdaS.finite_marked_language (F_EDPDA_RNPE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_EDPDA_RNPE_preserves_valid_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EDPDA_RNPE_relation_RL_effect SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in epdaS_epdaS_REPZ_StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_effect_def)
  done

lemma F_EDPDA_RNPE_preserves_unmarked_language2: "
  valid_epda G
  \<Longrightarrow> epdaS.unmarked_language G \<supseteq> epdaS.unmarked_language (F_EDPDA_RNPE G)"
  apply(rule_tac
      t="epdaS.unmarked_language G"
      and s="epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaS_inst_AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_EDPDA_RNPE G)"
      and s="epdaS.finite_unmarked_language (F_EDPDA_RNPE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply (rule F_EDPDA_RNPE_preserves_valid_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EDPDA_RNPE_relation_RL_effect SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in epdaS_epdaS_REPZ_StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_effect_def)
  done

theorem F_EDPDA_RNPE_preserves_lang: "
  valid_epda G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_EDPDA_RNPE G)"
  apply(rule order_antisym)
   apply (metis F_EDPDA_RNPE_preserves_lang1)
  apply (metis F_EDPDA_RNPE_preserves_lang2)
  done

theorem F_EDPDA_RNPE_preserves_unmarked_language: "
  valid_epda G
  \<Longrightarrow> epdaS.unmarked_language G = epdaS.unmarked_language (F_EDPDA_RNPE G)"
  apply(rule order_antisym)
   apply (metis F_EDPDA_RNPE_preserves_unmarked_language1)
  apply (metis F_EDPDA_RNPE_preserves_unmarked_language2)
  done

definition F_EDPDA_RNPE_relation_LR_initial_simulationRLB :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack DT_symbol) epda_step_label, ('state, 'event, 'stack DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_initial_simulationRLB G1 G2 c1 c' d \<equiv>
  d = der1 c1"

definition F_EDPDA_RNPE_relation_RL_configurationB :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_RL_configurationB G1 G2 c1 c2 \<equiv>
  F_EDPDA_RNPE_relation_RL_TSstructure G1 G2
  \<and> c1 \<in> epdaS_configurations G1
  \<and> c2 = c1"

definition F_EDPDA_RNPE_relation_LR_step_simulationRLB :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack DT_symbol) epda_step_label, ('state, 'event, 'stack DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE_relation_LR_step_simulationRLB G1 G2 c1 e c1' c2 d \<equiv>
  d = der2
        c1
          (if e \<in> epda_delta G2
          then e
          else F_EDPDA_RNPE__edges_rev e)
        c2"

lemma epdaS_epdaS_REPZ_StateSimRLB_inst_AX_initial_contained: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 c1 c2 \<longrightarrow> F_EDPDA_RNPE_relation_RL_configurationB G1 G2 c1 c2))"
  apply(simp add: F_EDPDA_RNPE_relation_RL_initial_configuration_def F_EDPDA_RNPE_relation_RL_configurationB_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply (metis epdaS_epdaS_REPZ_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_inst_AX_initial_configuration_belongs subsetD)
  done

lemma epdaS_epdaS_REPZ_StateSimRLB_inst_AX_relation_initial_simulationB: "
  (\<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>c2. F_EDPDA_RNPE_relation_RL_configurationB G1 G2 c1 c2 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EDPDA_RNPE_relation_RL_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EDPDA_RNPE_relation_LR_initial_simulationRLB G1 G2 c1 c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> get_configuration (d2 n) = Some c2)))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_initial_configuration_def F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_LR_initial_simulationRLB_def)
  apply(rule conjI)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G2 c1 c2)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply (metis F_EDPDA_RNPE_C_rev_preserves_initial_configurations F_EDPDA_RNPE_relation_RL_configurationB_def)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EDPDA_RNPE_relation_RL_configurationB_def)
  done

lemma epdaS_epdaS_REPZ_StateSimRLB_inst_AX_relation_step_simulationB: "
  \<forall>G1 G2. F_EDPDA_RNPE_relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RNPE_relation_RL_configurationB G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. c1' \<in> epdaS_configurations G1 \<longrightarrow> epdaS_step_relation G1 c1' e1 c1 \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> (\<exists>n. the (get_configuration (d2 n)) = c2 \<and> F_EDPDA_RNPE_relation_LR_step_simulationRLB G1 G2 c1' e1 c1 c2 d2 \<and> maximum_of_domain d2 n \<and> F_EDPDA_RNPE_relation_RL_configurationB G1 G2 c1' (the (get_configuration (d2 0))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RNPE_relation_RL_configurationB_def F_EDPDA_RNPE_relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(rule_tac
      x="der2 c1' (if e1 \<in> (epda_delta G2) then e1 else (F_EDPDA_RNPE__edges_rev e1)) c1"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w)(*strict*)
   apply(simp add: epda_step_labels_def)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w x)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edges_def F_EDPDA_RNPE__edges_rev_def)
   apply(erule disjE)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' w x xa)(*strict*)
    apply(case_tac x)
    apply(rename_tac G2 c1 c1' w x xa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac G2 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1')(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply(simp add: F_EDPDA_RNPE_def epdaS_configurations_def)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(rule_tac
      t="get_configuration (der2 c1' e1 c1 (Suc 0))"
      and s="Some c1"
      in ssubst)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply(simp add: der2_def get_configuration_def)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulationRLB_def)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(simp add: maximum_of_domain_def der2_def get_configuration_def)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE_relation_LR_step_simulationRLB_def)
  apply(simp add: maximum_of_domain_def der2_def get_configuration_def)
  done

theorem F_EDPDA_RNPE_preserves_is_forward_edge_deterministic_accessible: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible (F_EDPDA_RNPE G)"
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e2 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e1)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w wa)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e2)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e1) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e2) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e1 \<in> epda_delta (F_EDPDA_RNPE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (F_EDPDA_RNPE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="c1"
      in allE)
   apply(erule_tac
      x="c2"
      in allE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(subgoal_tac "c \<in> epdaS.get_accessible_configurations G")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(thin_tac "c \<notin> epdaS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(rule_tac
      ?c1.0="c"
      in epdaS_epdaS_REPZ_StateSimRL.get_accessible_configurations_transfer)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply (metis F_EDPDA_RNPE_C_rev_preserves_configurations F_EDPDA_RNPE_relation_RL_TSstructure_def epdaS.get_accessible_configurations_are_configurations2 epdaS_epdaS_REPZ_StateSimRL.AX_TSstructure_relation_TSstructure1_belongs)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
     apply(simp add: F_EDPDA_RNPE_relation_RL_TSstructure_def)
    apply(rename_tac c c1 c2 e1 e2 cA cB)(*strict*)
    apply(simp add: F_EDPDA_RNPE_relation_RL_configuration_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1=edge_src e2")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="if e1 \<in> (epda_delta G) then e1 else (F_EDPDA_RNPE__edges_rev e1)"
      in allE)
  apply(erule_tac
      x="if e2 \<in> (epda_delta G) then e2 else (F_EDPDA_RNPE__edges_rev e2)"
      in allE)
  apply(case_tac "e1 \<in> epda_delta G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(case_tac "e2 \<in> epda_delta G")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaS_step_relation_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 x)(*strict*)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(erule disjE)
    apply(erule disjE)
     apply(clarsimp)
     apply(simp add: F_EDPDA_RNPE__edges_rev_def)
     apply(case_tac e)
     apply(case_tac ea)
     apply(clarsimp)
     apply(simp add: epdaS_step_relation_def)
     apply(clarsimp)
    apply(clarsimp)
   apply(erule disjE)
    apply(clarsimp)
    apply(simp add: F_EDPDA_RNPE__edges_rev_def)
    apply(case_tac e)
    apply(case_tac ea)
    apply(clarsimp)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(case_tac "e2 \<in> epda_delta G")
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(simp add: F_EDPDA_RNPE__edges_rev_def)
   apply(case_tac e1)
   apply(case_tac e2)
   apply(clarsimp)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RNPE__edges_def)
   apply(erule disjE)
    apply(erule disjE)
     apply(clarsimp)
     apply(case_tac e)
     apply(case_tac ea)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac e)
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RNPE__edges_def F_EDPDA_RNPE__edges_rev_def F_EDPDA_RNPE_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 x xa xb xc)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(erule disjE)
    apply(clarsimp)
    apply(case_tac e)
    apply(case_tac ea)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  done

theorem F_EDPDA_RNPE_preserves_epda_no_empty_steps_from_marking_states: "
  epda_no_empty_steps_from_marking_states M
  \<Longrightarrow> R = F_EDPDA_RNPE M
  \<Longrightarrow> epda_no_empty_steps_from_marking_states R"
  apply(simp add: epda_no_empty_steps_from_marking_states_def F_EDPDA_RNPE_def F_EDPDA_RNPE__edges_def)
  apply(clarsimp)
  apply(force)
  done

definition epda_executing_edge :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epda_executing_edge M \<equiv>
  \<forall>e.
    e \<in> epda_delta M
    \<longrightarrow> edge_event e \<noteq> None
    \<longrightarrow> (\<exists>x y.
            edge_pop e = [x]
            \<and> edge_push e = [y, x])"

lemma F_EDPDA_RNPE_preserves_epda_executing_edge: "
  valid_epda M
  \<Longrightarrow> epda_executing_edge M
  \<Longrightarrow> R = F_EDPDA_RNPE M
  \<Longrightarrow> epda_executing_edge R"
  apply(simp add: epda_executing_edge_def)
  apply(clarsimp)
  apply(rename_tac e y)(*strict*)
  apply(simp add: F_EDPDA_RNPE_def F_EDPDA_RNPE__edges_def)
  apply(force)
  done

definition F_EDPDA_RNPE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE__SpecInput G \<equiv>
  valid_epda G
  \<and> epdaS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epda_no_empty_steps_from_marking_states G"

definition F_EDPDA_RNPE__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RNPE__SpecOutput Gi Go \<equiv>
  valid_epda Go
  \<and> epdaS.is_forward_edge_deterministic_accessible Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epda_no_empty_steps_from_marking_states Go
  \<and> epda_no_nil_popping_edges Go"

theorem F_EDPDA_RNPE__SOUND: "
  F_EDPDA_RNPE__SpecInput G
  \<Longrightarrow> F_EDPDA_RNPE__SpecOutput G (F_EDPDA_RNPE G)"
  apply(simp add: F_EDPDA_RNPE__SpecOutput_def F_EDPDA_RNPE__SpecInput_def)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RNPE_preserves_valid_epda)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RNPE_preserves_is_forward_edge_deterministic_accessible)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RNPE_preserves_lang)
   apply(force)
  apply(rule context_conjI)
   apply(metis F_EDPDA_RNPE_preserves_unmarked_language)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RNPE_preserves_epda_no_empty_steps_from_marking_states)
    apply(force)
   apply(force)
  apply(rule F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges)
  apply(force)
  done

end
