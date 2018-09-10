section {*FUNCTION\_\_CFG\_TC\_\_CTG\_TYPE\_CONVERSION*}
theory
  FUNCTION__CFG_TC__CTG_TYPE_CONVERSION

imports
  PRJ_12_03_03__ENTRY

begin

theorem F_CFG_TC__preserves_CFG: "
  valid_cfg G
  \<Longrightarrow> valid_cfg (F_CFG_TC G)"
  apply(simp add: valid_cfg_def F_CFG_TC_def F_CFG_TC__production_def F_CFG_TC__word_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(rename_tac p)
  apply(rename_tac p)(*strict*)
  apply(rule conjI)
   apply(rename_tac p)(*strict*)
   apply(clarsimp)
   apply(rename_tac p x)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA x]@w2 = (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) (prod_rhs p))")
    apply(rename_tac p x)(*strict*)
    apply(clarsimp)
    apply(rename_tac p x w1 w2)(*strict*)
    apply(rule inMap)
    apply(subgoal_tac "\<exists>w1' w2' x'. prod_rhs p = w1'@[x']@w2' \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w1'=w1) \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w2') = w2 \<and> ((case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) x')=teA x")
     apply(rename_tac p x w1 w2)(*strict*)
     prefer 2
     apply(rule map_decomp)
     apply(force)
    apply(rename_tac p x w1 w2)(*strict*)
    apply(erule exE)+
    apply(rename_tac p x w1 w2 w1' w2' x')(*strict*)
    apply(case_tac x')
     apply(rename_tac p x w1 w2 w1' w2' x' a)(*strict*)
     prefer 2
     apply(rename_tac p x w1 w2 w1' w2' x' b)(*strict*)
     apply(force)
    apply(rename_tac p x w1 w2 w1' w2' x' a)(*strict*)
    apply(rule_tac
      x="a"
      in bexI)
     apply(rename_tac p x w1 w2 w1' w2' x' a)(*strict*)
     apply(force)
    apply(rename_tac p x w1 w2 w1' w2' x' a)(*strict*)
    apply (metis ConsApp in_set_conv_decomp set_setA set_rev_mp)
   apply(rename_tac p x)(*strict*)
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac p)(*strict*)
  apply(clarsimp)
  apply(rename_tac p x)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teB x]@w2 = (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) (prod_rhs p))")
   apply(rename_tac p x)(*strict*)
   apply(clarsimp)
   apply(rename_tac p x w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>w1' w2' x'. prod_rhs p = w1'@[x']@w2' \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w1'=w1) \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w2') = w2 \<and> ((case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) x')=teB x")
    apply(rename_tac p x w1 w2)(*strict*)
    prefer 2
    apply(rule map_decomp)
    apply(force)
   apply(rename_tac p x w1 w2)(*strict*)
   apply(erule exE)+
   apply(rename_tac p x w1 w2 w1' w2' x')(*strict*)
   apply(case_tac x')
    apply(rename_tac p x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac p x w1 w2 w1' w2' x' b)(*strict*)
   apply (metis ConsApp DT_two_elements.simps(6) elemInsetB subsetD)
  apply(rename_tac p x)(*strict*)
  apply(rule setB_decomp)
  apply(force)
  done

definition F_CFG_TCC :: "
  ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration"
  where
    "F_CFG_TCC c \<equiv>
  \<lparr>cfg_conf = F_CFG_TC__word (cfg_conf c)\<rparr>"

definition F_CFG_TC__wordRev :: "
  ('nonterminal DT_symbol, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list"
  where
    "F_CFG_TC__wordRev w \<equiv>
  map
    (case_DT_two_elements (\<lambda>A. teA (case A of cons_symbol_base A'
  \<Rightarrow> A')) teB)
    w"

definition F_CFG_TCCRev :: "
  ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration"
  where
    "F_CFG_TCCRev c \<equiv>
  \<lparr>cfg_conf = F_CFG_TC__wordRev (cfg_conf c)\<rparr>"

definition F_CFG_TC__productionRev :: "
  ('nonterminal DT_symbol, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label"
  where
    "F_CFG_TC__productionRev p \<equiv>
  \<lparr>prod_lhs =
    case (prod_lhs p) of
    cons_symbol_base A' \<Rightarrow> A',
  prod_rhs =
    F_CFG_TC__wordRev (prod_rhs p)\<rparr>"

definition F_CFG_TC__relation_TSstructureLR :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_TSstructureLR G1 G2 \<equiv>
  valid_cfg G1
  \<and> G2 = F_CFG_TC G1"

definition F_CFG_TC__relation_configurationLR :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_configurationLR G1 G2 c1 c2 \<equiv>
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<and> c1 \<in> cfgSTD.get_accessible_configurations G1
  \<and> c2 = F_CFG_TCC c1"

definition F_CFG_TC__relation_initial_configurationLR :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_initial_configurationLR G1 G2 c1 c2 \<equiv>
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<and> c1 \<in> cfgSTD.get_accessible_configurations G1
  \<and> c2 = F_CFG_TCC c1"

definition F_CFG_TC__relation_effectLR :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_effectLR G1 G2 w1 w2 \<equiv>
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<and> w1 = w2"

definition F_CFG_TC__relation_step_simulation :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> (('nonterminal DT_symbol, 'event) cfg_step_label, ('nonterminal DT_symbol, 'event) cfg_configuration) derivation
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  d = der2 (F_CFG_TCC c1) (F_CFG_TC__production e) (F_CFG_TCC c1')"

definition F_CFG_TC__relation_initial_simulation :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> (('nonterminal DT_symbol, 'event) cfg_step_label, ('nonterminal DT_symbol, 'event) cfg_configuration) derivation
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_CFG_TCC c1)"

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_CFG_TC__relation_TSstructureLR G1) \<longrightarrow> valid_cfg G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> valid_cfg G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
  apply (metis F_CFG_TC__preserves_CFG)
  done

lemma FUN_F_CFG_TC__C_preserves_configurations: "
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> cfg_configurations G1
  \<Longrightarrow> (F_CFG_TCC c1) \<in> cfg_configurations G2"
  apply(simp add: cfg_configurations_def F_CFG_TCC_def F_CFG_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule conjI)
   apply(rename_tac c)(*strict*)
   apply(simp add: F_CFG_TC__word_def F_CFG_TC_def)
   apply(clarsimp)
   apply(rename_tac c x)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA x]@w2 = (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) c)")
    apply(rename_tac c x)(*strict*)
    apply(clarsimp)
    apply(rename_tac c x w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>w1' w2' x'. c = w1'@[x']@w2' \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w1'=w1) \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w2') = w2 \<and> ((case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) x')=teA x")
     apply(rename_tac c x w1 w2)(*strict*)
     prefer 2
     apply(rule map_decomp)
     apply(force)
    apply(rename_tac c x w1 w2)(*strict*)
    apply(erule exE)+
    apply(rename_tac c x w1 w2 w1' w2' x')(*strict*)
    apply(case_tac x')
     apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
     prefer 2
     apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
     apply(force)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(rule inMap)
    apply(clarsimp)
    apply(rename_tac w1' w2' a)(*strict*)
    apply (metis in_set_conv_decomp set_setA set_rev_mp)
   apply(rename_tac c x)(*strict*)
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(simp add: F_CFG_TC__word_def F_CFG_TC_def)
  apply(clarsimp)
  apply(rename_tac c x)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teB x]@w2 = (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) c)")
   apply(rename_tac c x)(*strict*)
   apply(clarsimp)
   apply(rename_tac c x w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>w1' w2' x'. c = w1'@[x']@w2' \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w1'=w1) \<and> (map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w2') = w2 \<and> ((case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) x')=teB x")
    apply(rename_tac c x w1 w2)(*strict*)
    prefer 2
    apply(rule map_decomp)
    apply(force)
   apply(rename_tac c x w1 w2)(*strict*)
   apply(erule exE)+
   apply(rename_tac c x w1 w2 w1' w2' x')(*strict*)
   apply(case_tac x')
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply (metis ConsApp setB_set_not DT_two_elements.inject(2) DT_two_elements.simps(6) in_set_conv_decomp insert_Nil subsetE)
  apply(rename_tac c x)(*strict*)
  apply(rule setB_decomp)
  apply(force)
  done

lemma FUN_F_CFG_TC__C_preserves_initial_configurations: "
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> cfg_initial_configurations G1
  \<Longrightarrow> (F_CFG_TCC c1) \<in> cfg_initial_configurations G2"
  apply(simp add: cfg_initial_configurations_def)
  apply(rule conjI)
   apply(simp add: F_CFG_TCC_def F_CFG_TC__word_def F_CFG_TC__relation_TSstructureLR_def F_CFG_TC_def)
  apply(rule FUN_F_CFG_TC__C_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma FUN_F_CFG_TC__initial_simulation_preserves_derivation: "
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> cfg_initial_configurations G1
  \<Longrightarrow> cfgSTD.derivation_initial G2 (der1 (F_CFG_TCC c1))"
  apply(rule cfgSTD.derivation_initialI)
   apply(rule cfgSTD.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule FUN_F_CFG_TC__C_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma F_CFG_TC__word_preserves_no_nonterms: "
  setA w = {}
  \<Longrightarrow> setA (F_CFG_TC__word w) = {}"
  apply(induct w)
   apply(clarsimp)
   apply(simp add: F_CFG_TC__word_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w b)(*strict*)
  apply(simp add: F_CFG_TC__word_def)
  done

lemma FUN_F_CFG_TC__C_preserves_marking_configurations: "
  F_CFG_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> cfg_marking_configuration G1
  \<Longrightarrow> F_CFG_TCC c1 \<in> cfg_marking_configuration G2"
  apply(simp add: cfg_marking_configuration_def)
  apply(rule conjI)
   apply(simp add: F_CFG_TCC_def)
   apply(clarsimp)
   apply(rule F_CFG_TC__word_preserves_no_nonterms)
   apply(force)
  apply(clarsimp)
  apply (metis FUN_F_CFG_TC__C_preserves_configurations)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<exists>d2. cfgSTD.derivation_initial G2 d2 \<and> F_CFG_TC__relation_initial_configurationLR G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_CFG_TC__relation_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_CFG_TC__relation_configurationLR G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_CFG_TC__relation_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule FUN_F_CFG_TC__initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_CFG_TC__relation_initial_configurationLR_def)
   apply(simp add: get_configuration_def der1_def)
   apply (metis cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs cfgSTD.initial_configurations_are_get_accessible_configurations)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_CFG_TC__relation_configurationLR_def)
  apply(rule cfgSTD.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_CFG_TC__relation_TSstructureLR_def valid_pda_def valid_dpda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_CFG_TC__relation_step_simulation_maps_to_derivation: "
  F_CFG_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_CFG_TC__relation_configurationLR G1 G2 c1 c2
  \<Longrightarrow> cfgSTD_step_relation G1 c1 e1 c1'
  \<Longrightarrow> cfgSTD.derivation G2 d2"
  apply(simp add: F_CFG_TC__relation_step_simulation_def F_CFG_TC__relation_configurationLR_def)
  apply(subgoal_tac "c1 \<in> cfg_configurations G1")
   prefer 2
   apply (metis (full_types) cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs cfgSTD.get_accessible_configurations_are_configurations subsetD)
  apply(rule cfgSTD.der2_is_derivation)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac l r)(*strict*)
   apply(simp add: F_CFG_TC__production_def F_CFG_TC__relation_TSstructureLR_def F_CFG_TC_def)
  apply(rename_tac l r)(*strict*)
  apply(rule_tac
      x="F_CFG_TC__word l"
      in exI)
  apply(rule_tac
      x="F_CFG_TC__word r"
      in exI)
  apply(simp add: F_CFG_TCC_def F_CFG_TC__production_def F_CFG_TC__word_def)
  done

lemma F_CFG_TC__relation_step_simulation_maps_to_derivation_belongs: "
  F_CFG_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_CFG_TC__relation_configurationLR G1 G2 c1 c2
  \<Longrightarrow> cfgSTD_step_relation G1 c1 e1 c1'
  \<Longrightarrow> cfgSTD.belongs G2 d2"
  apply(simp add: F_CFG_TC__relation_step_simulation_def)
  apply(subgoal_tac "c1 \<in> cfg_configurations G1")
   prefer 2
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
   apply(clarsimp)
   apply (metis (full_types) cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs cfgSTD.get_accessible_configurations_are_configurations subsetD)
  apply(subgoal_tac "(F_CFG_TCC c1) \<in> cfg_configurations G2")
   apply(rule cfgSTD.derivation_belongs)
      prefer 3
      apply(force)
     apply(simp add: F_CFG_TC__relation_step_simulation_def F_CFG_TC__relation_configurationLR_def F_CFG_TC__relation_TSstructureLR_def)
     apply(clarsimp)
     apply (metis F_CFG_TC__preserves_CFG)
    apply(simp add: der2_def)
   apply(rule F_CFG_TC__relation_step_simulation_maps_to_derivation)
     apply(simp add: F_CFG_TC__relation_step_simulation_def)
    apply(force)
   apply(force)
  apply (metis F_CFG_TC__relation_configurationLR_def FUN_F_CFG_TC__C_preserves_configurations)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. cfgSTD.derivation G2 d2 \<and> cfgLM.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_CFG_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_CFG_TC__relation_configurationLR G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="der2 (F_CFG_TCC c1) (F_CFG_TC__production e1) (F_CFG_TCC c1')"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply (metis F_CFG_TC__relation_configurationLR_def F_CFG_TC__relation_step_simulation_def F_CFG_TC__relation_step_simulation_maps_to_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply (metis F_CFG_TC__relation_configurationLR_def F_CFG_TC__relation_step_simulation_def F_CFG_TC__relation_step_simulation_maps_to_derivation_belongs)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: der2_def get_configuration_def F_CFG_TC__relation_configurationLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_CFG_TC__relation_step_simulation_def der2_def get_configuration_def F_CFG_TC__relation_configurationLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_CFG_TC__relation_step_simulation_def der2_def get_configuration_def F_CFG_TC__relation_configurationLR_def)
  apply (rule cfgSTD.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply (metis cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule cfgSTD.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_cfg cfg_initial_configurations cfg_step_labels cfgSTD_step_relation valid_cfg cfg_configurations cfg_initial_configurations cfg_step_labels cfgSTD_step_relation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "cfg_cfg_F_CFG_TC__StateSimLR" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgSTD_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgSTD_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  (* relation_configuration *)
  "F_CFG_TC__relation_configurationLR"
  (* relation_initial_configuration *)
  "F_CFG_TC__relation_initial_configurationLR"
  (* relation_effect *)
  "F_CFG_TC__relation_effectLR"
  (* relation_TSstructure *)
  "F_CFG_TC__relation_TSstructureLR"
  (* relation_initial_simulation *)
  "F_CFG_TC__relation_initial_simulation"
  (* relation_step_simulation *)
  "F_CFG_TC__relation_step_simulation"
  apply(simp add: LOCALE_DEFS CFG_interpretations)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation_preserves_marking_condition: "
  \<forall>G1 G2 d1' d2'. ATS_Simulation_Configuration_Weak.relation_step_simulation_preservation cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_initial_configurations cfgSTD_step_relation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 d1' d2' \<longrightarrow> cfg_marking_condition G1 d1' \<longrightarrow> cfg_marking_condition G2 d2'"
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "ATS_Simulation_Configuration_Weak.relation_step_simulation_preservation
        cfg_initial_configurations cfg_step_labels cfgSTD_step_relation
        cfg_initial_configurations cfgSTD_step_relation
        F_CFG_TC__relation_configurationLR
        F_CFG_TC__relation_initial_configurationLR
        F_CFG_TC__relation_TSstructureLR
        F_CFG_TC__relation_initial_simulation
        F_CFG_TC__relation_step_simulation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: cfg_marking_condition_def)
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
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
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
   apply(rule FUN_F_CFG_TC__C_preserves_marking_configurations)
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
    apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def)
    apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
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
      and s="F_CFG_TCC c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_CFG_TC__relation_configurationLR_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule FUN_F_CFG_TC__C_preserves_marking_configurations)
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

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2 d1' d2'. ATS_Simulation_Configuration_Weak.relation_initial_simulation_preservation cfg_initial_configurations cfgSTD_step_relation cfg_initial_configurations cfgSTD_step_relation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 d1' d2' \<longrightarrow> cfg_marking_condition G1 d1' \<longrightarrow> cfg_marking_condition G2 d2'"
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "ATS_Simulation_Configuration_Weak.relation_initial_simulation_preservation cfg_initial_configurations cfgSTD_step_relation cfg_initial_configurations cfgSTD_step_relation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
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
      and s="F_CFG_TCC ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule FUN_F_CFG_TC__C_preserves_marking_configurations)
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

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_marking_condition cfg_initial_configurations cfgSTD_step_relation cfg_marking_condition F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation_preserves_marking_condition
      cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation_preserves_marking_condition)
  done

lemma F_CFG_TC__word_preserves_liftB: "
  liftB a = F_CFG_TC__word (liftB a)"
  apply(induct a)
   apply(clarsimp)
   apply(simp add: F_CFG_TC__word_def)
  apply(rename_tac a1 a2)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__word_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectLR G1 G2) (cfg_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (cfg_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCC c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCC_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
    apply (metis F_CFG_TC__word_preserves_no_nonterms setA_liftB)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i)(*strict*)
   apply(rule F_CFG_TC__word_preserves_liftB)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationLR_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__relation_configurationLR_def)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c i)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c option)(*strict*)
  apply(case_tac n)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c option)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 deri1 deri1n deri2 f a e c option)(*strict*)
   apply(rule_tac
      x="f (Suc deri1n)"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c option nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 deri1 deri1n deri2 deri2n f a e c option nat)(*strict*)
  apply(rule_tac
      x="Suc nat+deri2n"
      in exI)
  apply(clarsimp)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation_marked_effect: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectLR G1 G2) (cfg_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (cfg_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectLR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCC c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCC_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
    apply (metis F_CFG_TC__word_preserves_no_nonterms setA_liftB)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i)(*strict*)
   apply(rule F_CFG_TC__word_preserves_liftB)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationLR_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der1_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c)(*strict*)
  apply(simp add: der1_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_marked_effect cfg_initial_configurations cfgSTD_step_relation cfg_marked_effect F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_effectLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule cfg_cfg_F_CFG_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "ATS_Simulation_Configuration_Weak.relation_step_simulation_preservation
        cfg_initial_configurations cfg_step_labels cfgSTD_step_relation
        cfg_initial_configurations cfgSTD_step_relation
        F_CFG_TC__relation_configurationLR
        F_CFG_TC__relation_initial_configurationLR
        F_CFG_TC__relation_TSstructureLR
        F_CFG_TC__relation_initial_simulation
        F_CFG_TC__relation_step_simulation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "ATS_Simulation_Configuration_Weak.relation_initial_simulation_preservation cfg_initial_configurations cfgSTD_step_relation cfg_initial_configurations cfgSTD_step_relation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation_marked_effect)
  done

lemma F_CFG_TC__word_distrib: "
  F_CFG_TC__word a @ F_CFG_TC__word b = F_CFG_TC__word (a @ b)"
  apply(induct a arbitrary: b)
   apply(rename_tac b)(*strict*)
   apply(clarsimp)
   apply(simp add: F_CFG_TC__word_def)
  apply(rename_tac a1 a2 b)(*strict*)
  apply(clarsimp)
  apply(case_tac a1)
   apply(rename_tac a1 a2 b a)(*strict*)
   apply(simp add: F_CFG_TC__word_def)
  apply(rename_tac a1 a2 b ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac a2 b ba)(*strict*)
  apply(simp add: F_CFG_TC__word_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectLR G1 G2) (cfg_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (cfg_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCC c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCC_def)
   apply(rule_tac
      x="F_CFG_TC__word z"
      in exI)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z)(*strict*)
   apply(rule_tac
      t="liftB a"
      and s="F_CFG_TC__word (liftB a)"
      in ssubst)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z)(*strict*)
    apply(rule F_CFG_TC__word_preserves_liftB)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z)(*strict*)
   apply(rule F_CFG_TC__word_distrib)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationLR_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__relation_configurationLR_def)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c i z)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c z y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c z y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c z option)(*strict*)
  apply(case_tac n)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c z option)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 deri1 deri1n deri2 f a e c z option)(*strict*)
   apply(rule_tac
      x="f (Suc deri1n)"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c z option nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 deri1 deri1n deri2 deri2n f a e c z option nat)(*strict*)
  apply(rule_tac
      x="Suc nat+deri2n"
      in exI)
  apply(clarsimp)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectLR G1 G2) (cfg_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (cfg_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectLR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCC c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCC_def)
   apply(rule_tac
      x="F_CFG_TC__word z"
      in exI)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z)(*strict*)
   apply(rule_tac
      t="liftB a"
      and s="F_CFG_TC__word (liftB a)"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z)(*strict*)
    apply(rule F_CFG_TC__word_preserves_liftB)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z)(*strict*)
   apply(rule F_CFG_TC__word_distrib)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationLR_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationLR_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der1_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c z)(*strict*)
  apply(simp add: der1_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_unmarked_effect cfg_initial_configurations cfgSTD_step_relation cfg_unmarked_effect F_CFG_TC__relation_configurationLR F_CFG_TC__relation_initial_configurationLR F_CFG_TC__relation_effectLR F_CFG_TC__relation_TSstructureLR F_CFG_TC__relation_initial_simulation F_CFG_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule cfg_cfg_F_CFG_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis cfg_cfg_F_CFG_TC__StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "cfg_cfg_F_CFG_TC__StateSimLR" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgSTD_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgSTD_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  (* relation_configuration *)
  "F_CFG_TC__relation_configurationLR"
  (* relation_initial_configuration *)
  "F_CFG_TC__relation_initial_configurationLR"
  (* relation_effect *)
  "F_CFG_TC__relation_effectLR"
  (* relation_TSstructure *)
  "F_CFG_TC__relation_TSstructureLR"
  (* relation_initial_simulation *)
  "F_CFG_TC__relation_initial_simulation"
  (* relation_step_simulation *)
  "F_CFG_TC__relation_step_simulation"
  apply(simp add: LOCALE_DEFS CFG_interpretations)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms )
  done

lemma F_CFG_TC__preserves_lang1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G \<subseteq> cfgSTD.marked_language (F_CFG_TC G)"
  apply(rule_tac
      t="cfgSTD.marked_language G"
      and s="cfgSTD.finite_marked_language G"
      in ssubst)
   apply (metis cfgSTD.AX_marked_language_finite)
  apply(rule_tac
      t="cfgSTD.marked_language (F_CFG_TC G)"
      and s="cfgSTD.finite_marked_language (F_CFG_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule cfgSTD.AX_marked_language_finite)
   apply (metis F_CFG_TC__preserves_CFG)
  apply(subgoal_tac "left_total_on (F_CFG_TC__relation_effectLR SSG1 SSG2) (cfgSTD.finite_marked_language SSG1) (cfgSTD.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in cfg_cfg_F_CFG_TC__StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
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
  apply(simp add: F_CFG_TC__relation_effectLR_def)
  done

lemma F_CFG_TC__preserves_unmarked_language1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.unmarked_language G \<subseteq> cfgSTD.unmarked_language (F_CFG_TC G)"
  apply(rule_tac
      t="cfgSTD.unmarked_language G"
      and s="cfgSTD.finite_unmarked_language G"
      in ssubst)
   apply (metis cfgSTD.AX_unmarked_language_finite)
  apply(rule_tac
      t="cfgSTD.unmarked_language (F_CFG_TC G)"
      and s="cfgSTD.finite_unmarked_language (F_CFG_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule cfgSTD.AX_unmarked_language_finite)
   apply (metis F_CFG_TC__preserves_CFG)
  apply(subgoal_tac "left_total_on (F_CFG_TC__relation_effectLR SSG1 SSG2) (cfgSTD.finite_unmarked_language SSG1) (cfgSTD.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in cfg_cfg_F_CFG_TC__StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
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
  apply(simp add: F_CFG_TC__relation_effectLR_def)
  done

definition F_CFG_TC__relation_TSstructureRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_TSstructureRL G1 G2 \<equiv>
  valid_cfg G2
  \<and> G1 = F_CFG_TC G2"

definition F_CFG_TC__relation_configurationRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_configurationRL G1 G2 c1 c2 \<equiv>
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<and> c1 \<in> cfgSTD.get_accessible_configurations G1
  \<and> c1 = F_CFG_TCC c2"

definition F_CFG_TC__relation_initial_configurationRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_initial_configurationRL G1 G2 c1 c2 \<equiv>
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<and> c1 \<in> cfg_initial_configurations G1
  \<and> c1 = F_CFG_TCC c2"

definition F_CFG_TC__relation_effectRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_effectRL G1 G2 w1 w2 \<equiv>
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<and> w1 = w2"

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_CFG_TC__relation_TSstructureRL G1) \<longrightarrow> valid_cfg G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis F_CFG_TC__preserves_CFG)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> valid_cfg G2)"
  apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  done

definition F_CFG_TC__relation_step_simulationRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> (('nonterminal, 'event) cfg_step_label, ('nonterminal, 'event) cfg_configuration) derivation
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_step_simulationRL G1 G2 c1 e c1' c2 d \<equiv>
  d = der2 (F_CFG_TCCRev c1) (F_CFG_TC__productionRev e) (F_CFG_TCCRev c1')"

definition F_CFG_TC__relation_initial_simulationRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> (('nonterminal, 'event) cfg_step_label, ('nonterminal, 'event) cfg_configuration) derivation
  \<Rightarrow> bool"
  where
    "F_CFG_TC__relation_initial_simulationRL G1 G2 c1 d \<equiv>
  d = der1 (F_CFG_TCCRev c1)"

lemma F_CFG_TC__C_rev_preserves_configurations: "
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> cfg_configurations G1
  \<Longrightarrow> F_CFG_TCCRev c1 \<in> cfg_configurations G2"
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(simp add: F_CFG_TC_def F_CFG_TCCRev_def)
  apply(rule conjI)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rename_tac c x)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA x] @ w2 = F_CFG_TC__wordRev c")
    apply(rename_tac c x)(*strict*)
    prefer 2
    apply(rule setA_decomp)
    apply(force)
   apply(rename_tac c x)(*strict*)
   apply(clarsimp)
   apply(rename_tac c x w1 w2)(*strict*)
   apply(simp add: F_CFG_TC__wordRev_def)
   apply(subgoal_tac "\<exists>w1' w2' x'. c=w1'@[x']@w2' \<and> map SSf w1'=w1 \<and> map SSf w2' = w2 \<and> SSf x'=teA x" for SSf)
    apply(rename_tac c x w1 w2)(*strict*)
    prefer 2
    apply(rule map_decomp)
    apply(force)
   apply(rename_tac c x w1 w2)(*strict*)
   apply(erule exE)+
   apply(rename_tac c x w1 w2 w1' w2' x')(*strict*)
   apply(case_tac x')
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    prefer 2
    apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(subgoal_tac "\<exists>y\<in> cfg_nonterminals G2. cons_symbol_base y = a")
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(clarsimp)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(subgoal_tac "a \<in> cons_symbol_base ` cfg_nonterminals G2")
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(rule_tac
      A="setA c"
      in set_mp)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(rule_tac
      A="setA(w1' @ [x'] @ w2')"
      in set_mp)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(rule_tac
      t="x'"
      and s="teA a"
      in ssubst)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply (metis ConsApp elemInsetA)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c x)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teB x] @ w2 = F_CFG_TC__wordRev c")
   apply(rename_tac c x)(*strict*)
   prefer 2
   apply(rule setB_decomp)
   apply(force)
  apply(rename_tac c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac c x w1 w2)(*strict*)
  apply(simp add: F_CFG_TC__wordRev_def)
  apply(subgoal_tac "\<exists>w1' w2' x'. c=w1'@[x']@w2' \<and> map SSf w1'=w1 \<and> map SSf w2' = w2 \<and> SSf x'=teB x" for SSf)
   apply(rename_tac c x w1 w2)(*strict*)
   prefer 2
   apply(rule map_decomp)
   apply(force)
  apply(rename_tac c x w1 w2)(*strict*)
  apply(erule exE)+
  apply(rename_tac c x w1 w2 w1' w2' x')(*strict*)
  apply(case_tac x')
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply(rule_tac
      A="setB(w1' @ [x'] @ w2')"
      in set_mp)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply(rule_tac
      t="x'"
      and s="teB b"
      in ssubst)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply(rule_tac
      t="b"
      and s="x"
      in ssubst)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply (metis ConsApp elemInsetB)
  done

lemma F_CFG_TC__C_rev_preserves_initial_configurations: "
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> cfg_initial_configurations G1
  \<Longrightarrow> F_CFG_TCCRev c1 \<in> cfg_initial_configurations G2"
  apply(subgoal_tac "F_CFG_TCCRev c1 \<in> cfg_configurations G2")
   apply(simp add: cfg_initial_configurations_def)
   apply(simp add: F_CFG_TC_def F_CFG_TC__wordRev_def F_CFG_TCCRev_def F_CFG_TC__relation_TSstructureRL_def)
  apply(rule F_CFG_TC__C_rev_preserves_configurations)
   apply(force)
  apply (metis cfgBASE_inst_AX_initial_configuration_belongs subsetE)
  done

lemma F_CFG_TC__wordRev_reverse: "
  setA w \<subseteq> cons_symbol_base ` cfg_nonterminals G2
  \<Longrightarrow> w = map (case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB \<circ> case_DT_two_elements (\<lambda>A. teA (case A of cons_symbol_base A' \<Rightarrow> A')) teB) w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_TC__wordRev_reverse2: "
  w = map (case_DT_two_elements (\<lambda>A. teA (case A of cons_symbol_base A' \<Rightarrow> A')) teB \<circ> case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB) w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_TCCrev_reverse: "
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> cfg_configurations G1
  \<Longrightarrow> c1 = F_CFG_TCC (F_CFG_TCCRev c1)"
  apply(simp add: F_CFG_TCC_def F_CFG_TCCRev_def)
  apply(case_tac c1)
  apply(rename_tac cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_CFG_TC__word_def F_CFG_TC__wordRev_def)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(simp add: F_CFG_TC_def)
  apply(rule F_CFG_TC__wordRev_reverse)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<exists>d2. cfgSTD.derivation_initial G2 d2 \<and> F_CFG_TC__relation_initial_configurationRL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_CFG_TC__relation_initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_CFG_TC__relation_configurationRL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_CFG_TC__relation_initial_simulationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule cfgSTD.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_CFG_TC__C_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_CFG_TC__relation_initial_configurationRL_def)
   apply(rule F_CFG_TCCrev_reverse)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply (metis cfgBASE_inst_AX_initial_configuration_belongs subsetE)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_CFG_TC__relation_configurationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule cfgSTD.initial_configurations_are_get_accessible_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
    apply (metis F_CFG_TC__preserves_CFG)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule F_CFG_TCCrev_reverse)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply (metis cfgBASE_inst_AX_initial_configuration_belongs subsetE)
  done

lemma F_CFG_TC__relation_step_simulationRL_maps_to_derivation: "
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> F_CFG_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_CFG_TC__relation_configurationRL G1 G2 c1 c2
  \<Longrightarrow> cfgSTD_step_relation G1 c1 e1 c1'
  \<Longrightarrow> cfgSTD.derivation G2 d2"
  apply(simp add: F_CFG_TC__relation_step_simulationRL_def)
  apply(subgoal_tac "c1 \<in> cfg_configurations G1")
   prefer 2
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(clarsimp)
   apply (metis cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_CFG_TC__relation_TSstructureLR_def F_CFG_TC__relation_TSstructureRL_def cfgSTD.get_accessible_configurations_are_configurations contra_subsetD)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__relation_configurationRL_def)
  apply(clarsimp)
  apply(rule cfgSTD.der2_is_derivation)
  apply(subgoal_tac "e1 \<in> cfg_productions G1")
   prefer 2
   apply(simp add: cfgSTD_step_relation_def)
  apply(subgoal_tac "\<exists>e \<in> cfg_productions G2. e1 = F_CFG_TC__production e")
   prefer 2
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(simp add: F_CFG_TC_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_TC__production_def)
   apply(rule_tac
      x="x"
      in bexI)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "c1' \<in> cfg_configurations G1")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply (metis F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgSTD.AX_step_relation_preserves_belongs)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "\<exists>c\<in> cfg_configurations G2. F_CFG_TCC c = c1'")
   apply(rename_tac e)(*strict*)
   apply(subgoal_tac "c2=F_CFG_TCCRev (F_CFG_TCC c2)")
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(clarsimp)
    apply(rename_tac e c)(*strict*)
    apply(case_tac c2)
    apply(rename_tac e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(subgoal_tac "c=F_CFG_TCCRev (F_CFG_TCC c)")
    apply(rename_tac e c)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac c)
    apply(rename_tac e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(F_CFG_TC__productionRev (F_CFG_TC__production e)) = e")
    apply(rename_tac e c)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TC__productionRev_def F_CFG_TC__production_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac e)
    apply(rename_tac e c prod_lhsa prod_rhsa)(*strict*)
    apply(clarsimp)
    apply(rename_tac c prod_lhs prod_rhs)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgSTD_step_relation_def)
   apply(simp add: F_CFG_TC__productionRev_def)
   apply(simp add: F_CFG_TCCRev_def)
   apply(clarsimp)
   apply(rename_tac e l r)(*strict*)
   apply(rule_tac
      x="F_CFG_TC__wordRev l"
      in exI)
   apply(rule_tac
      x="F_CFG_TC__wordRev r"
      in exI)
   apply(rule conjI)
    apply(rename_tac e l r)(*strict*)
    apply(simp add: F_CFG_TC__production_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def)
   apply(rename_tac e l r)(*strict*)
   apply(simp add: F_CFG_TC__production_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def)
   apply (metis F_CFG_TC__wordRev_def F_CFG_TC__wordRev_reverse2 F_CFG_TC__word_def List.map.compositionality)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rule_tac
      x="F_CFG_TCCRev c1'"
      in bexI)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply (metis F_CFG_TC__C_rev_preserves_configurations F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgSTD.der2_is_derivation cfgSTD.der2_preserves_get_accessible_configurations)
  apply(rename_tac e)(*strict*)
  apply (metis F_CFG_TCCrev_reverse F_CFG_TC__relation_TSstructureRL_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. cfgSTD.derivation G2 d2 \<and> cfgLM.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_CFG_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_CFG_TC__relation_configurationRL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="der2 (F_CFG_TCCRev c1) (F_CFG_TC__productionRev e1) (F_CFG_TCCRev c1')"
      in exI)
  apply(subgoal_tac "c1 \<in> cfg_configurations G1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply (metis cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_CFG_TC__relation_TSstructureLR_def F_CFG_TC__relation_TSstructureRL_def cfgSTD.get_accessible_configurations_are_configurations contra_subsetD)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_CFG_TC__relation_configurationRL_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "e1 \<in> cfg_productions G1")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: cfgSTD_step_relation_def)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>e \<in> cfg_productions G2. e1 = F_CFG_TC__production e")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(simp add: F_CFG_TC_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 c1' x)(*strict*)
   apply(simp add: F_CFG_TC__production_def)
   apply(rule_tac
      x="x"
      in bexI)
    apply(rename_tac G2 c2 c1' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G2 c2 c1' x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "c1' \<in> cfg_configurations G1")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   prefer 2
   apply (metis F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgSTD.AX_step_relation_preserves_belongs)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>c\<in> cfg_configurations G2. F_CFG_TCC c = c1'")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply(subgoal_tac "c2=F_CFG_TCCRev (F_CFG_TCC c2)")
    apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
    prefer 2
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    apply(case_tac c2)
    apply(rename_tac G1 G2 c2 e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 e c cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(subgoal_tac "c=F_CFG_TCCRev (F_CFG_TCC c)")
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac c)
    apply(rename_tac G1 G2 c2 e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(F_CFG_TC__productionRev (F_CFG_TC__production e)) = e")
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TC__productionRev_def F_CFG_TC__production_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac e)
    apply(rename_tac G1 G2 c2 e c prod_lhsa prod_rhsa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 c prod_lhs prod_rhs)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    apply(rule cfgSTD.der2_is_derivation)
    apply(clarsimp)
    apply(simp add: cfgSTD_step_relation_def)
    apply(simp add: F_CFG_TC__productionRev_def)
    apply(simp add: F_CFG_TCCRev_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 e l r)(*strict*)
    apply(rule_tac
      x="F_CFG_TC__wordRev l"
      in exI)
    apply(rule_tac
      x="F_CFG_TC__wordRev r"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 e l r)(*strict*)
     apply(simp add: F_CFG_TC__production_def F_CFG_TCC_def)
     apply(simp add: F_CFG_TC__wordRev_def)
    apply(rename_tac G1 G2 e l r)(*strict*)
    apply(simp add: F_CFG_TC__production_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def)
    apply (metis F_CFG_TC__wordRev_def F_CFG_TC__wordRev_reverse2 F_CFG_TC__word_def List.map.compositionality)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 c1' e)(*strict*)
   apply(rule_tac
      x="F_CFG_TCCRev c1'"
      in bexI)
    apply(rename_tac G2 c2 c1' e)(*strict*)
    prefer 2
    apply (metis F_CFG_TC__C_rev_preserves_configurations F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgSTD.der2_is_derivation cfgSTD.der2_preserves_get_accessible_configurations)
   apply(rename_tac G2 c2 c1' e)(*strict*)
   apply (metis F_CFG_TCCrev_reverse F_CFG_TC__relation_TSstructureRL_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac G1 G2 c2 e c)(*strict*)
      apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
     apply(rename_tac G1 G2 c2 e c)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    apply (metis F_CFG_TC__C_rev_preserves_configurations)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(simp add: der2_def get_configuration_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(simp add: F_CFG_TC__relation_step_simulationRL_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(simp add: maximum_of_domain_def der2_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply (metis F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgSTD.der2_is_derivation cfgSTD.der2_preserves_get_accessible_configurations)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(simp add: get_configuration_def der2_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_cfg cfg_initial_configurations cfg_step_labels cfgSTD_step_relation valid_cfg cfg_configurations cfg_initial_configurations cfg_step_labels cfgSTD_step_relation F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_configurationRL F_CFG_TC__relation_TSstructureRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation cfg_cfg_F_CFG_TC__StateSimRL_step_relation_step_simulation cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "cfg_cfg_F_CFG_TC__StateSimRL" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgSTD_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgSTD_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  (* relation_configuration *)
  "F_CFG_TC__relation_configurationRL"
  (* relation_initial_configuration *)
  "F_CFG_TC__relation_initial_configurationRL"
  (* relation_effect *)
  "F_CFG_TC__relation_effectRL"
  (* relation_TSstructure *)
  "F_CFG_TC__relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_CFG_TC__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_CFG_TC__relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS CFG_interpretations)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL_step_relation_step_simulation cfg_cfg_F_CFG_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_CFG_TC__C_rev_preserves_marking_configurations: "
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> cfg_marking_configuration G1
  \<Longrightarrow> F_CFG_TCCRev c1 \<in> cfg_marking_configuration G2"
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>c\<in> cfg_configurations G2. F_CFG_TCC c = c1")
   prefer 2
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rule_tac
      x="F_CFG_TCCRev c1"
      in bexI)
    apply (metis F_CFG_TCCrev_reverse F_CFG_TC__relation_TSstructureRL_def)
   apply (metis F_CFG_TC__C_rev_preserves_configurations F_CFG_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "c=F_CFG_TCCRev (F_CFG_TCC c)")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac c)
   apply(rename_tac c cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac cfg_conf)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TCC_def F_CFG_TC__word_def)
  apply(case_tac c)
  apply(rename_tac c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_confa)(*strict*)
  apply(simp add: F_CFG_TCCRev_def F_CFG_TC__wordRev_def)
  apply(rename_tac cfg_conf)(*strict*)
  apply (metis F_CFG_TC__wordRev_def F_CFG_TC__wordRev_reverse2 F_CFG_TC__word_def F_CFG_TC__word_preserves_liftB List.map.compositionality setA_liftB liftBDeConv2)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_step_simulation_marking_condition: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL (G1:: ('nonterminal DT_symbol, 'event) cfg) G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> cfg_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> cfg_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: cfg_marking_condition_def)
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
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
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
   apply(subgoal_tac "c=F_CFG_TCCRev ca")
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def get_configuration_def)
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea e c)(*strict*)
    apply(case_tac c)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea e cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(rule F_CFG_TC__C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def)
    apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
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
      and s="F_CFG_TCCRev c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_CFG_TC__relation_configurationRL_def derivation_append_def get_configuration_def)
     apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
     apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c2 e1 d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(case_tac c)
     apply(rename_tac G1 G2 c2 e1 d2 n deri1 deri1n deri2 deri2n f ea e c cfg_confa)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c2 e1 d2 n deri1 deri1n deri2 deri2n f ea e cfg_confa)(*strict*)
     apply(rule F_CFG_TC__wordRev_reverse2)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_CFG_TC__C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
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

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> cfg_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> cfg_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
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
      and s="F_CFG_TCCRev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea e c)(*strict*)
    apply(case_tac c)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea e cfg_conf)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_CFG_TC__C_rev_preserves_marking_configurations)
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

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_marking_condition cfg_initial_configurations cfgSTD_step_relation cfg_marking_condition F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_configurationRL F_CFG_TC__relation_TSstructureRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule cfg_cfg_F_CFG_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation_marking_condition)
  done

lemma F_CFG_TC__wordRev_preserves_liftB: "
  liftB a = F_CFG_TC__wordRev (liftB a)"
  apply(induct a)
   apply(clarsimp)
   apply(simp add: F_CFG_TC__wordRev_def)
  apply(rename_tac a1 a2)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__wordRev_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectRL G1 G2) (cfg_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (cfg_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationLR_def)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCCRev c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCCRev_def)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
   apply(subgoal_tac "liftB a = F_CFG_TC__wordRev (liftB a)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
   apply(rule F_CFG_TC__wordRev_preserves_liftB)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationRL_def)
    apply(simp add: get_configuration_def)
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac b)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca option b cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca option cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(simp add: get_configuration_def)
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac b)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca option b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i ca option cfg_confa)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__relation_configurationRL_def)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca option b)(*strict*)
  apply(case_tac n)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 f a e ca option b)(*strict*)
   apply(rule_tac
      x="f (Suc deri1n)"
      in exI)
   apply(clarsimp)
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac b)
   apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 f a e ca option b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 f a e ca option cfg_confa)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca option b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 deri2n f a e ca option b nat)(*strict*)
  apply(rule_tac
      x="Suc nat+deri2n"
      in exI)
  apply(clarsimp)
  apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
  apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
  apply(case_tac b)
  apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 deri2n f a e ca option b nat cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 deri2n f a e ca option nat cfg_confa)(*strict*)
  apply(rule F_CFG_TC__wordRev_reverse2)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation_marked_effect: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectRL G1 G2) (cfg_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (cfg_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectRL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCCRev c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCCRev_def)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
   apply(subgoal_tac "liftB a = F_CFG_TC__wordRev (liftB a)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca)(*strict*)
   apply(rule F_CFG_TC__wordRev_preserves_liftB)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationRL_def)
    apply(simp add: get_configuration_def)
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac b)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca option b cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca option cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(simp add: get_configuration_def)
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac b)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca option b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i ca option cfg_confa)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der1_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c ca)(*strict*)
  apply(simp add: der1_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_marked_effect cfg_initial_configurations cfgSTD_step_relation cfg_marked_effect F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_configurationRL F_CFG_TC__relation_effectRL F_CFG_TC__relation_TSstructureRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule cfg_cfg_F_CFG_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation_marked_effect)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_step_simulation_unmarked_effect: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectRL G1 G2) (cfg_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (cfg_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationLR_def)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCCRev c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCCRev_def)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
   apply(rule_tac
      x="F_CFG_TC__wordRev z"
      in exI)
   apply(subgoal_tac "liftB a = F_CFG_TC__wordRev (liftB a)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
    prefer 2
    apply(rule F_CFG_TC__wordRev_preserves_liftB)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
   apply(rule_tac
      P="\<lambda>X. X @ F_CFG_TC__wordRev z = F_CFG_TC__wordRev (liftB a @ z)"
      and t="liftB a"
      and s="F_CFG_TC__wordRev (liftB a)"
      in ssubst)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
   apply(simp add: F_CFG_TC__wordRev_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationRL_def)
    apply(simp add: get_configuration_def)
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac b)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca option cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(simp add: get_configuration_def)
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac b)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e i z ca option cfg_confa)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__relation_configurationRL_def)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c i z ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e z ca y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e z ca y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e z ca option b)(*strict*)
  apply(case_tac n)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e z ca option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 f a e z ca option b)(*strict*)
   apply(rule_tac
      x="f (Suc deri1n)"
      in exI)
   apply(clarsimp)
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac b)
   apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 f a e z ca option b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 f a e z ca option cfg_confa)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e z ca option b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 deri2n f a e z ca option b nat)(*strict*)
  apply(rule_tac
      x="Suc nat+deri2n"
      in exI)
  apply(clarsimp)
  apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
  apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
  apply(case_tac b)
  apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 deri2n f a e z ca option b nat cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1' d2 deri1 deri1n deri2 deri2n f a e z ca option nat cfg_confa)(*strict*)
  apply(rule F_CFG_TC__wordRev_reverse2)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation_unmarked_effect: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_CFG_TC__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. cfgSTD.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. cfgSTD.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_CFG_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_CFG_TC__relation_effectRL G1 G2) (cfg_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (cfg_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: F_CFG_TC__relation_effectRL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(simp add: derivation_append_def F_CFG_TC__relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   prefer 2
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z)(*strict*)
   apply(rule_tac
      M="G2"
      in cfgSTD.some_position_has_details_at_0)
   apply (metis cfgSTD.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(rule ex_swap)
  apply(rule_tac
      x="F_CFG_TCCRev c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TCCRev_def)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
   apply(rule_tac
      x="F_CFG_TC__wordRev z"
      in exI)
   apply(subgoal_tac "liftB a = F_CFG_TC__wordRev (liftB a)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
    prefer 2
    apply(rule F_CFG_TC__wordRev_preserves_liftB)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
   apply(rule_tac
      P="\<lambda>X. X @ F_CFG_TC__wordRev z = F_CFG_TC__wordRev (liftB a @ z)"
      and t="liftB a"
      and s="F_CFG_TC__wordRev (liftB a)"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca)(*strict*)
   apply(simp add: F_CFG_TC__wordRev_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(rule ex_swap)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca y)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(case_tac "f i \<le> deri2n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca y)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b)(*strict*)
    apply(simp add: F_CFG_TC__relation_configurationRL_def)
    apply(simp add: get_configuration_def)
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac b)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca option cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca y)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b)(*strict*)
   apply(simp add: F_CFG_TC__relation_configurationRL_def)
   apply(simp add: get_configuration_def)
   apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
   apply(case_tac b)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca option b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e i z ca option cfg_confa)(*strict*)
   apply(rule F_CFG_TC__wordRev_reverse2)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der1_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c i z ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a e c z ca)(*strict*)
  apply(simp add: der1_def)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_unmarked_effect cfg_initial_configurations cfgSTD_step_relation cfg_unmarked_effect F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_configurationRL F_CFG_TC__relation_effectRL F_CFG_TC__relation_TSstructureRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule cfg_cfg_F_CFG_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_step_simulation_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule cfg_cfg_F_CFG_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "cfg_cfg_F_CFG_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis cfg_cfg_F_CFG_TC__StateSimRL_inst_relation_initial_simulation_unmarked_effect)
  done

interpretation "cfg_cfg_F_CFG_TC__StateSimRL" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgSTD_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgSTD_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  (* relation_configuration *)
  "F_CFG_TC__relation_configurationRL"
  (* relation_initial_configuration *)
  "F_CFG_TC__relation_initial_configurationRL"
  (* relation_effect *)
  "F_CFG_TC__relation_effectRL"
  (* relation_TSstructure *)
  "F_CFG_TC__relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_CFG_TC__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_CFG_TC__relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS CFG_interpretations)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL_step_relation_step_simulation cfg_cfg_F_CFG_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms cfg_cfg_F_CFG_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms)
  done

lemma F_CFG_TC__preserves_lang2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G \<supseteq> cfgSTD.marked_language (F_CFG_TC G)"
  apply(rule_tac
      t="cfgSTD.marked_language G"
      and s="cfgSTD.finite_marked_language G"
      in ssubst)
   apply (metis cfgSTD_inst_lang_finite)
  apply(rule_tac
      t="cfgSTD.marked_language (F_CFG_TC G)"
      and s="cfgSTD.finite_marked_language (F_CFG_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule cfgSTD.AX_marked_language_finite)
   apply (rule F_CFG_TC__preserves_CFG)
   apply(force)
  apply(subgoal_tac "left_total_on (F_CFG_TC__relation_effectRL SSG1 SSG2) (cfgSTD.finite_marked_language SSG1) (cfgSTD.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in cfg_cfg_F_CFG_TC__StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_TC__relation_effectRL_def)
  done

lemma F_CFG_TC__preserves_unmarked_language2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.unmarked_language G \<supseteq> cfgSTD.unmarked_language (F_CFG_TC G)"
  apply(rule_tac
      t="cfgSTD.unmarked_language G"
      and s="cfgSTD.finite_unmarked_language G"
      in ssubst)
   apply (metis cfgSTD_inst_AX_unmarked_language_finite)
  apply(rule_tac
      t="cfgSTD.unmarked_language (F_CFG_TC G)"
      and s="cfgSTD.finite_unmarked_language (F_CFG_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule cfgSTD.AX_unmarked_language_finite)
   apply (rule F_CFG_TC__preserves_CFG)
   apply(force)
  apply(subgoal_tac "left_total_on (F_CFG_TC__relation_effectRL SSG1 SSG2) (cfgSTD.finite_unmarked_language SSG1) (cfgSTD.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in cfg_cfg_F_CFG_TC__StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_TC__relation_effectRL_def)
  done

theorem F_CFG_TC__preserves_lang: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G = cfgSTD.marked_language (F_CFG_TC G)"
  apply(rule order_antisym)
   apply (metis F_CFG_TC__preserves_lang1)
  apply (metis F_CFG_TC__preserves_lang2)
  done

theorem F_CFG_TC__preserves_unmarked_language: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.unmarked_language G = cfgSTD.unmarked_language (F_CFG_TC G)"
  apply(rule order_antisym)
   apply (metis F_CFG_TC__preserves_unmarked_language1)
  apply (metis F_CFG_TC__preserves_unmarked_language2)
  done

lemma F_CFG_TC__word_inj: "
  F_CFG_TC__word c1 = F_CFG_TC__word c2
  \<Longrightarrow> c1 = c2"
  apply(simp add: F_CFG_TC__word_def)
  apply(induct c1 arbitrary: c2)
   apply(rename_tac c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a c1 z zs)(*strict*)
  apply(case_tac a)
   apply(rename_tac a c1 z zs aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c1 z zs aa)(*strict*)
   apply(case_tac z)
    apply(rename_tac c1 z zs aa a)(*strict*)
    apply(clarsimp)
   apply(rename_tac c1 z zs aa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a c1 z zs b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c1 z zs b)(*strict*)
  apply(case_tac z)
   apply(rename_tac c1 z zs b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac c1 z zs b ba)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_TCC_inj: "
  F_CFG_TCC c1 = F_CFG_TCC c2
  \<Longrightarrow> c1 = c2"
  apply(simp add: cfg_configurations_def F_CFG_TCC_def)
  apply(case_tac c1)
  apply(rename_tac cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_conf cfg_confa)(*strict*)
  apply(rule F_CFG_TC__word_inj)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_relation_configuration_inverse: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c2 c1. F_CFG_TC__relation_configurationRL G2 G1 c2 c1 \<longrightarrow> F_CFG_TC__relation_configurationLR G1 G2 c1 c2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 c1)(*strict*)
  apply(simp add: F_CFG_TC__relation_configurationLR_def F_CFG_TC__relation_configurationRL_def cfgSTD.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac G1 G2 c1 d i)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G1 G2 c1 d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i option)(*strict*)
  apply(subgoal_tac "\<exists>d2 n2 f. cfgSTD.derivation_initial SSG2 d2 \<and> maximum_of_domain d2 n2 \<and> F_CFG_TC__relation_initial_configurationRL SSG1 SSG2 (the (get_configuration (SSd1 0))) (the (get_configuration (d2 0))) \<and> F_CFG_TC__relation_configurationRL SSG1 SSG2 SSc1 (the (get_configuration (d2 n2))) \<and> ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__relation_step_simulationRL SSG1 SSG2 d SSx d2 n2 f" for SSd1 SSc1 SSG1 SSG2 SSx)
   apply(rename_tac G1 G2 c1 d i option)(*strict*)
   prefer 2
   apply(rule cfg_cfg_F_CFG_TC__StateSimRL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness)
     apply(rename_tac G1 G2 c1 d i option)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 d i option)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d i option)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d i option)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i option d2 n2 x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d i option d2 n2 f)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="f i"
      in exI)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: cfg_cfg_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i option d2 f)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i option d2 f y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 d i option d2 f y optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d i option d2 f optiona b)(*strict*)
  apply(simp add: F_CFG_TC__relation_configurationRL_def get_configuration_def)
  apply(clarsimp)
  apply(rule F_CFG_TCC_inj)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_marking_condition_translation: "
  (\<forall>G2 G1. F_CFG_TC__relation_TSstructureRL G2 G1 \<longrightarrow> F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>dR. cfgSTD.derivation_initial G2 dR \<longrightarrow> (\<forall>nR. maximum_of_domain dR nR \<longrightarrow> (\<forall>enR cnR. dR nR = Some (pair enR cnR) \<longrightarrow> (\<forall>dL. cfgSTD.derivation_initial G1 dL \<longrightarrow> (\<forall>nL. maximum_of_domain dL nL \<longrightarrow> (\<forall>c0R c0L. F_CFG_TC__relation_initial_configurationRL G2 G1 c0R c0L \<longrightarrow> (\<forall>cnL. F_CFG_TC__relation_configurationRL G2 G1 cnR cnL \<longrightarrow> dR 0 = Some (pair None c0R) \<longrightarrow> dL 0 = Some (pair None c0L) \<longrightarrow> (\<exists>enL. dL nL = Some (pair enL cnL)) \<longrightarrow> (\<forall>dL2. cfgSTD.derivation G1 dL2 \<longrightarrow> cfgLM.belongs G1 dL2 \<longrightarrow> (\<forall>nL2. maximum_of_domain dL2 nL2 \<longrightarrow> cfg_marking_condition G1 (derivation_append dL dL2 nL) \<longrightarrow> dL2 0 = Some (pair None cnL) \<longrightarrow> F_CFG_TC__relation_configurationLR G1 G2 cnL cnR \<longrightarrow> (\<forall>e2nL c2nL. dL2 nL2 = Some (pair e2nL c2nL) \<longrightarrow> (\<forall>d2R. cfgSTD.derivation G2 d2R \<longrightarrow> cfgLM.belongs G2 d2R \<longrightarrow> (\<forall>n2R. maximum_of_domain d2R n2R \<longrightarrow> (\<forall>cn2R. F_CFG_TC__relation_configurationLR G1 G2 c2nL cn2R \<longrightarrow> d2R 0 = Some (pair None cnR) \<longrightarrow> (\<exists>en2R. d2R n2R = Some (pair en2R cn2R)) \<longrightarrow> cfg_marking_condition G2 (derivation_append dR d2R nR)))))))))))))))"
  apply(clarsimp)
  apply(rename_tac G2 G1 dR nR enR cnR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R cn2R en2R)(*strict*)
  apply(simp add: F_CFG_TC__relation_configurationLR_def F_CFG_TC__relation_configurationRL_def)
  apply(clarsimp)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(subgoal_tac "c2nL \<in> cfg_marking_configuration G1")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply(rule_tac
      x="nR+n2R"
      in exI)
   apply(simp add: derivation_append_def)
   apply(case_tac n2R)
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R i e c)(*strict*)
    apply (metis FUN_F_CFG_TC__C_preserves_marking_configurations)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R en2R i e c nat)(*strict*)
   apply (metis FUN_F_CFG_TC__C_preserves_marking_configurations)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(subgoal_tac "i=nL+nL2")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(case_tac nL2)
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R e c)(*strict*)
    apply(force)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R e c nat)(*strict*)
   apply(force)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_append dL dL2 nL) (nL+nL2)")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   prefer 2
   apply(rule concat_has_max_dom)
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
    apply(force)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply(force)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(subgoal_tac "cfgSTD.derivation G1 (derivation_append dL dL2 nL)")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
     apply (metis cfgSTD.derivation_initial_is_derivation)
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
    apply(force)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply(force)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(subgoal_tac "i\<le>nL+nL2")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G1"
      and d="(derivation_append dL dL2 nL)"
      in cfgSTD.allPreMaxDomSome_prime)
     apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
     apply(force)
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
    apply(force)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply(force)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(case_tac "i<nL+nL2")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(subgoal_tac "(derivation_append dL dL2 nL) (Suc i)=None")
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply(subgoal_tac "(derivation_append dL dL2 nL) (Suc i)\<noteq>None")
    apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
    apply(force)
   apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
   apply (metis Suc_le_eq cfgSTD.maximum_of_domainSmaller)
  apply(rename_tac G2 G1 dR nR enR dL nL c0R c0L cnL enL dL2 nL2 e2nL c2nL d2R n2R en2R i e c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply (metis cfg_cfg_F_CFG_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs Suc_n_not_le_n cfgSTD.allPreMaxDomSome_prime cfgSTD.derivation_initial_is_derivation cfg_no_step_without_nonterms)
  done

definition F_CFG_TC__RM_relation_configurationRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__RM_relation_configurationRL G1 G2 c1 c2 \<equiv>
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<and> c1 \<in> cfgRM.get_accessible_configurations G1
  \<and> c1 = F_CFG_TCC c2"

definition F_CFG_TC__RM_relation_step_simulationRL :: "
  ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> (('nonterminal, 'event) cfg_step_label, ('nonterminal, 'event) cfg_configuration) derivation
  \<Rightarrow> bool"
  where
    "F_CFG_TC__RM_relation_step_simulationRL G1 G2 c1 e c1' c2 d \<equiv>
  d = der2 (F_CFG_TCCRev c1) (F_CFG_TC__productionRev e) (F_CFG_TCCRev c1')"

lemma F_CFG_TC__RM_C_rev_preserves_configurations: "
  F_CFG_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> cfgRM.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> cfg_configurations G1
  \<Longrightarrow> F_CFG_TCCRev c1 \<in> cfg_configurations G2"
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(simp add: F_CFG_TC_def F_CFG_TCCRev_def)
  apply(rule conjI)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rename_tac c x)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA x] @ w2 = F_CFG_TC__wordRev c")
    apply(rename_tac c x)(*strict*)
    prefer 2
    apply(rule setA_decomp)
    apply(force)
   apply(rename_tac c x)(*strict*)
   apply(clarsimp)
   apply(rename_tac c x w1 w2)(*strict*)
   apply(simp add: F_CFG_TC__wordRev_def)
   apply(subgoal_tac "\<exists>w1' w2' x'. c=w1'@[x']@w2' \<and> map SSf w1'=w1 \<and> map SSf w2' = w2 \<and> SSf x'=teA x" for SSf)
    apply(rename_tac c x w1 w2)(*strict*)
    prefer 2
    apply(rule map_decomp)
    apply(force)
   apply(rename_tac c x w1 w2)(*strict*)
   apply(erule exE)+
   apply(rename_tac c x w1 w2 w1' w2' x')(*strict*)
   apply(case_tac x')
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    prefer 2
    apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(subgoal_tac "\<exists>y\<in> cfg_nonterminals G2. cons_symbol_base y = a")
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(clarsimp)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(subgoal_tac "a \<in> cons_symbol_base ` cfg_nonterminals G2")
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(rule_tac
      A="setA c"
      in set_mp)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(rule_tac
      A="setA(w1' @ [x'] @ w2')"
      in set_mp)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(rule_tac
      t="x'"
      and s="teA a"
      in ssubst)
    apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
    apply(force)
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply (metis ConsApp elemInsetA)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c x)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teB x] @ w2 = F_CFG_TC__wordRev c")
   apply(rename_tac c x)(*strict*)
   prefer 2
   apply(rule setB_decomp)
   apply(force)
  apply(rename_tac c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac c x w1 w2)(*strict*)
  apply(simp add: F_CFG_TC__wordRev_def)
  apply(subgoal_tac "\<exists>w1' w2' x'. c=w1'@[x']@w2' \<and> map SSf w1'=w1 \<and> map SSf w2' = w2 \<and> SSf x'=teB x" for SSf)
   apply(rename_tac c x w1 w2)(*strict*)
   prefer 2
   apply(rule map_decomp)
   apply(force)
  apply(rename_tac c x w1 w2)(*strict*)
  apply(erule exE)+
  apply(rename_tac c x w1 w2 w1' w2' x')(*strict*)
  apply(case_tac x')
   apply(rename_tac c x w1 w2 w1' w2' x' a)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply(rule_tac
      A="setB(w1' @ [x'] @ w2')"
      in set_mp)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply(rule_tac
      t="x'"
      and s="teB b"
      in ssubst)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply(rule_tac
      t="b"
      and s="x"
      in ssubst)
   apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
   apply(force)
  apply(rename_tac c x w1 w2 w1' w2' x' b)(*strict*)
  apply (metis ConsApp elemInsetB)
  done

lemma cfgRM_cfgRM_F_CFG_TC__StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__RM_relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> cfg_step_labels G1 \<longrightarrow> (\<forall>c1'. cfgRM_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. cfgRM.derivation G2 d2 \<and> cfgLM.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_CFG_TC__RM_relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_CFG_TC__RM_relation_configurationRL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="der2 (F_CFG_TCCRev c1) (F_CFG_TC__productionRev e1) (F_CFG_TCCRev c1')"
      in exI)
  apply(subgoal_tac "c1 \<in> cfg_configurations G1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_CFG_TC__RM_relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply (metis cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs cfgRM.get_accessible_configurations_are_configurations contra_subsetD)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_CFG_TC__RM_relation_configurationRL_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "e1 \<in> cfg_productions G1")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: cfgRM_step_relation_def)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>e \<in> cfg_productions G2. e1 = F_CFG_TC__production e")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(simp add: F_CFG_TC_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 c1' x)(*strict*)
   apply(simp add: F_CFG_TC__production_def)
   apply(rule_tac
      x="x"
      in bexI)
    apply(rename_tac G2 c2 c1' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G2 c2 c1' x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "c1' \<in> cfg_configurations G1")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   prefer 2
   apply (metis cfgRM_inst_AX_step_relation_preserves_belongs cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs cfgRM.get_accessible_configurations_are_configurations contra_subsetD)
  apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>c\<in> cfg_configurations G2. F_CFG_TCC c = c1'")
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply(subgoal_tac "c2=F_CFG_TCCRev (F_CFG_TCC c2)")
    apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
    prefer 2
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    apply(case_tac c2)
    apply(rename_tac G1 G2 c2 e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 e c cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(subgoal_tac "c=F_CFG_TCCRev (F_CFG_TCC c)")
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac c)
    apply(rename_tac G1 G2 c2 e c cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e cfg_confa)(*strict*)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(F_CFG_TC__productionRev (F_CFG_TC__production e)) = e")
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    prefer 2
    apply(simp add: F_CFG_TC__productionRev_def F_CFG_TC__production_def)
    apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
    apply(case_tac e)
    apply(rename_tac G1 G2 c2 e c prod_lhsa prod_rhsa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 c prod_lhs prod_rhs)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_TC__wordRev_reverse2)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(clarsimp)
    apply(simp add: cfgRM_step_relation_def)
    apply(simp add: F_CFG_TC__productionRev_def)
    apply(simp add: F_CFG_TCCRev_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 e l r)(*strict*)
    apply(rule_tac
      x="F_CFG_TC__wordRev l"
      in exI)
    apply(rule_tac
      x="F_CFG_TC__wordRev r"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 e l r)(*strict*)
     apply(simp add: F_CFG_TC__production_def F_CFG_TCC_def)
     apply(simp add: F_CFG_TC__wordRev_def)
    apply(rename_tac G1 G2 e l r)(*strict*)
    apply(simp add: F_CFG_TC__production_def F_CFG_TCC_def)
    apply(rule conjI)
     apply(rename_tac G1 G2 e l r)(*strict*)
     apply(simp add: F_CFG_TC__wordRev_def)
     apply (metis F_CFG_TC__wordRev_def F_CFG_TC__wordRev_reverse2 F_CFG_TC__word_def List.map.compositionality)
    apply(rename_tac G1 G2 e l r)(*strict*)
    apply(subgoal_tac "\<exists>l'. liftB l'=r")
     apply(rename_tac G1 G2 e l r)(*strict*)
     prefer 2
     apply(rule_tac
      x="filterB r"
      in exI)
     apply (rule liftBDeConv2)
     apply(force)
    apply(rename_tac G1 G2 e l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 e l l')(*strict*)
    apply(rule_tac
      t="F_CFG_TC__wordRev (liftB l')"
      and s="(liftB l')"
      in subst)
     apply(rename_tac G1 G2 e l l')(*strict*)
     apply(rule F_CFG_TC__wordRev_preserves_liftB)
    apply(rename_tac G1 G2 e l l')(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 c1' e)(*strict*)
   apply(rule_tac
      x="F_CFG_TCCRev c1'"
      in bexI)
    apply(rename_tac G2 c2 c1' e)(*strict*)
    prefer 2
    apply (metis F_CFG_TC__RM_C_rev_preserves_configurations F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgRM.der2_is_derivation cfgRM.der2_preserves_get_accessible_configurations)
   apply(rename_tac G2 c2 c1' e)(*strict*)
   apply (metis F_CFG_TCCrev_reverse F_CFG_TC__relation_TSstructureRL_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(rule cfgRM.derivation_belongs)
      apply(rename_tac G1 G2 c2 e c)(*strict*)
      apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
     apply(rename_tac G1 G2 c2 e c)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c2 e c)(*strict*)
    apply (metis F_CFG_TC__RM_C_rev_preserves_configurations)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(simp add: der2_def get_configuration_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(simp add: F_CFG_TC__RM_relation_step_simulationRL_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply(simp add: maximum_of_domain_def der2_def)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c2 e c)(*strict*)
   apply (metis F_CFG_TC__preserves_CFG F_CFG_TC__relation_TSstructureRL_def cfgRM.der2_is_derivation cfgRM.der2_preserves_get_accessible_configurations)
  apply(rename_tac G1 G2 c2 e c)(*strict*)
  apply(simp add: get_configuration_def der2_def)
  done

lemma cfgRM_cfgRM_F_CFG_TC__StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> cfg_initial_configurations G1 \<longrightarrow> (\<exists>d2. cfgRM.derivation_initial G2 d2 \<and> F_CFG_TC__relation_initial_configurationRL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_CFG_TC__relation_initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_CFG_TC__RM_relation_configurationRL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_CFG_TC__relation_initial_simulationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule cfgRM.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_CFG_TC__C_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_CFG_TC__relation_initial_configurationRL_def)
   apply(rule F_CFG_TCCrev_reverse)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply (metis cfgBASE_inst_AX_initial_configuration_belongs subsetE)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_CFG_TC__RM_relation_configurationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule cfgRM.initial_configurations_are_get_accessible_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
    apply (metis F_CFG_TC__preserves_CFG)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule F_CFG_TCCrev_reverse)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply (metis cfgBASE_inst_AX_initial_configuration_belongs subsetE)
  done

interpretation "cfgRM_cfgRM_F_CFG_TC__StateSimRL" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgRM_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgRM_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  (* relation_configuration *)
  "F_CFG_TC__RM_relation_configurationRL"
  (* relation_initial_configuration *)
  "F_CFG_TC__relation_initial_configurationRL"
  (* relation_effect *)
  "F_CFG_TC__relation_effectRL"
  (* relation_TSstructure *)
  "F_CFG_TC__relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_CFG_TC__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_CFG_TC__RM_relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS CFG_interpretations)
  apply(simp add:  ATS_Simulation_Configuration_Weak_axioms_def cfgRM_cfgRM_F_CFG_TC__StateSimRL_step_relation_step_simulation cfgRM_cfgRM_F_CFG_TC__StateSimRL_inst_relation_initial_simulation cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs cfg_cfg_F_CFG_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs )
  done

lemma F_CFG_TC__wordRev_F_CFG_TC__word: "
  w = F_CFG_TC__wordRev (F_CFG_TC__word w)"
  apply(induct w)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
  apply(rename_tac a w)(*strict*)
  apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_TCCRev_F_CFG_TCC: "
  F_CFG_TCC c = x
  \<Longrightarrow> c = F_CFG_TCCRev x"
  apply(simp add: F_CFG_TCCRev_def F_CFG_TCC_def)
  apply(case_tac c)
  apply(rename_tac cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac w)(*strict*)
  apply(rule F_CFG_TC__wordRev_F_CFG_TC__word)
  done

lemma F_CFG_TC__wordRev_append: "
  F_CFG_TC__wordRev (a @ b) = F_CFG_TC__wordRev a @ F_CFG_TC__wordRev b"
  apply(simp add: F_CFG_TC__wordRev_def)
  done

lemma F_CFG_TC__wordRev_Cons: "
  F_CFG_TC__wordRev (a # b) = F_CFG_TC__wordRev [a] @ F_CFG_TC__wordRev b"
  apply(simp add: F_CFG_TC__wordRev_def)
  done

lemma F_CFG_TC__wordRev_inj: "
  setA (x @ y) \<subseteq> cons_symbol_base ` cfg_nonterminals G
  \<Longrightarrow> F_CFG_TC__wordRev x = F_CFG_TC__wordRev y
  \<Longrightarrow> x = y"
  apply(induct x arbitrary: y)
   apply(rename_tac y)(*strict*)
   apply(simp add: F_CFG_TC__wordRev_def)
  apply(rename_tac a x y)(*strict*)
  apply(simp add: F_CFG_TC__wordRev_def)
  apply(clarsimp)
  apply(rename_tac a x z zs)(*strict*)
  apply(case_tac a)
   apply(rename_tac a x z zs aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x z zs xa)(*strict*)
   apply(case_tac z)
    apply(rename_tac x z zs xa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac x zs a)(*strict*)
    apply(simp add: setAConcat)
    apply(case_tac a)
     apply(rename_tac x zs a nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac x zs a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x z zs xa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x z zs b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x z zs b)(*strict*)
  apply(case_tac z)
   apply(rename_tac x z zs b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac x z zs b ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac x zs ba)(*strict*)
  apply(simp add: setAConcat)
  done

lemma F_CFG_TC__in_cons_symbol_base_preserved_by_rm_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_initial (F_CFG_TC G) d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cons_symbol_base ` cfg_nonterminals G"
  apply(induct n arbitrary: e w)
   apply(rename_tac e w)(*strict*)
   apply(clarsimp)
   apply(rename_tac e w x)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: F_CFG_TC_def valid_cfg_def)
  apply(rename_tac n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e w x)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd SSX = Some (pair (Some e2) c2) \<and> cfgRM_step_relation SSX c1 e2 c2" for SSd SSX)
   apply(rename_tac n e w x)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac n e w x)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e w x)(*strict*)
    apply(force)
   apply(rename_tac n e w x)(*strict*)
   apply(force)
  apply(rename_tac n e w x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w x e1 e2 c1)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n x e1 e2 c1 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l'=r")
   apply(rename_tac n x e1 e2 c1 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB r"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n x e1 e2 c1 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 e2 c1 l l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac c1)
  apply(rename_tac n x e1 e2 c1 l l' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 e2 l l')(*strict*)
  apply(case_tac e2)
  apply(rename_tac n x e1 e2 l l' prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n x e1 e2 l l' A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 l l' A w)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="l @ teA A # liftB l'"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(erule disjE)
   apply(rename_tac n x e1 l l' A w)(*strict*)
   apply(force)
  apply(rename_tac n x e1 l l' A w)(*strict*)
  apply(erule disjE)
   apply(rename_tac n x e1 l l' A w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n x e1 l l' A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 l l' w xa)(*strict*)
  apply(simp add: setA_liftB)
  apply(simp add: F_CFG_TC_def F_CFG_TC__production_def)
  apply(clarsimp)
  apply(rename_tac n x e1 l l' w xa xb)(*strict*)
  apply(simp add: F_CFG_TC_def F_CFG_TC__production_def F_CFG_TC__word_def)
  apply(clarsimp)
  apply(rename_tac n x e1 l l' xb)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x="xb"
      in ballE)
   apply(rename_tac n x e1 l l' xb)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n x e1 l l' xb)(*strict*)
  apply(clarsimp)
  apply(case_tac xb)
  apply(rename_tac n x e1 l l' xb prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac B v)
  apply(rename_tac n x e1 l l' xb B v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 l l' B v)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n x e1 l l' B v)(*strict*)
   prefer 2
   apply(rule setA_elem_at_nth)
   apply(force)
  apply(rename_tac n x e1 l l' B v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 l l' B v k)(*strict*)
  apply(case_tac x)
   apply(rename_tac n x e1 l l' B v k nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 l l' B v k nat)(*strict*)
   apply(case_tac "v!k")
    apply(rename_tac n e1 l l' B v k nat a)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 l l' B v k nat b)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x e1 l l' B v k a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 l l' B v k a)(*strict*)
  apply(case_tac "v!k")
   apply(rename_tac n e1 l l' B v k a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 l l' B v k a)(*strict*)
   apply(subgoal_tac "a \<in> cfg_nonterminals G")
    apply(rename_tac n e1 l l' B v k a)(*strict*)
    apply(force)
   apply(rename_tac n e1 l l' B v k a)(*strict*)
   apply(subgoal_tac "teA a \<in> set v")
    apply(rename_tac n e1 l l' B v k a)(*strict*)
    apply (metis set_setA set_mp)
   apply(rename_tac n e1 l l' B v k a)(*strict*)
   apply (metis nth_mem)
  apply(rename_tac n e1 l l' B v k a b)(*strict*)
  apply(force)
  done

theorem F_CFG_TC__preserves_LR1: "
  valid_cfg G
  \<Longrightarrow> cfg_LRk G (Suc 0)
  \<Longrightarrow> cfg_LRk (F_CFG_TC G) (Suc 0)"
  apply(subgoal_tac "F_CFG_TC__relation_TSstructureRL (F_CFG_TC G) G")
   prefer 2
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def)
  apply(simp (no_asm) add: cfg_LRk_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "setA (\<delta>1 @ teA A1 # liftB y1) \<subseteq> cons_symbol_base ` cfg_nonterminals G")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d1"
      and n="n1"
      in F_CFG_TC__in_cons_symbol_base_preserved_by_rm_derivation)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "setA (\<delta>2 @ teA A2 # liftB y2) \<subseteq> cons_symbol_base ` cfg_nonterminals G")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d2"
      and n="n2"
      in F_CFG_TC__in_cons_symbol_base_preserved_by_rm_derivation)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "setA (\<delta>1 @ \<omega>1 @ liftB y1) \<subseteq> cons_symbol_base ` cfg_nonterminals G")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d1"
      and n="Suc n1"
      in F_CFG_TC__in_cons_symbol_base_preserved_by_rm_derivation)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "setA (\<delta>2 @ \<omega>2 @ liftB y2) \<subseteq> cons_symbol_base ` cfg_nonterminals G")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d2"
      and n="Suc n2"
      in F_CFG_TC__in_cons_symbol_base_preserved_by_rm_derivation)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      x="Suc n1"
      and ?G2.0="G"
      and ?d1.0="d1"
      in cfgRM_cfgRM_F_CFG_TC__StateSimRL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(erule exE)+
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d2a n2a f)(*strict*)
  apply(rename_tac d1' n1' f1)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1)(*strict*)
   prefer 2
   apply(rule_tac
      x="Suc n2"
      and ?G2.0="G"
      and ?d1.0="d2"
      in cfgRM_cfgRM_F_CFG_TC__StateSimRL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1)(*strict*)
  apply(erule exE)+
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2a n2a f)(*strict*)
  apply(rename_tac d2' n2' f2)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "F_CFG_TC__relation_initial_configurationRL (F_CFG_TC G) G (the (get_configuration (d1 0))) (the (get_configuration (d1' 0)))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
  apply(thin_tac "F_CFG_TC__relation_initial_configurationRL (F_CFG_TC G) G (the (get_configuration (d2 0))) (the (get_configuration (d2' 0)))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
  apply(subgoal_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)) \<and> derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>) \<and> f1 (Suc n1) = Suc (f1 n1)")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
   prefer 2
   apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_def cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_S_def)
   apply(clarsimp)
   apply(erule_tac
      x="n1"
      and P="\<lambda>x. x < Suc n1 \<longrightarrow> (\<forall>ei ci ei' ci'. d1 x = Some (pair ei ci) \<and> d1 (Suc x) = Some (pair (Some ei') ci') \<longrightarrow> (\<exists>d2'. F_CFG_TC__RM_relation_step_simulationRL (F_CFG_TC G) G ci ei' ci' (the (get_configuration (d1' (f1 x)))) d2' \<and> (\<exists>n. maximum_of_domain d2' n \<and> f1 (Suc x) = f1 x + n \<and> derivation_take (derivation_drop d1' (f1 x)) n = d2')))"
      in allE)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
   apply(simp add: F_CFG_TC__RM_relation_step_simulationRL_def)
   apply(rule context_conjI)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
    apply(rule_tac
      t="der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)"
      and s="derivation_take (derivation_drop d1' (f1 n1)) n"
      in ssubst)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(rule_tac
      m="n"
      in cfgRM.derivation_drop_preserves_derivation_prime)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
    apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
   apply(subgoal_tac "n=Suc 0")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
   apply(rule_tac
      G="G"
      in cfgRM.maximum_of_domainUnique)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
    prefer 2
    apply(rule der2_maximum_of_domain)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2 n)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
  apply(subgoal_tac "Suc (f1 n1) = n1'")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
   prefer 2
   apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_def cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_S_def)
   apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' n1' f1 d2' n2' f2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2)(*strict*)
  apply(subgoal_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)) \<and> derivation_take (derivation_drop d2' (f2 n2)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>) \<and> f2 (Suc n2) = Suc (f2 n2)")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2)(*strict*)
   prefer 2
   apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_def cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_S_def)
   apply(clarsimp)
   apply(erule_tac
      x="n2"
      and P="\<lambda>i. i < Suc n2 \<longrightarrow> (\<forall>ei ci ei' ci'. d2 i = Some (pair ei ci) \<and> d2 (Suc i) = Some (pair (Some ei') ci') \<longrightarrow> (\<exists>d2'nonterminal. F_CFG_TC__RM_relation_step_simulationRL (F_CFG_TC G) G ci ei' ci' (the (get_configuration (d2' (f2 i)))) d2'nonterminal \<and> (\<exists>n. maximum_of_domain d2'nonterminal n \<and> f2 (Suc i) = f2 i + n \<and> derivation_take (derivation_drop d2' (f2 i)) n = d2'nonterminal)))"
      in allE)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
   apply(simp add: F_CFG_TC__RM_relation_step_simulationRL_def)
   apply(rule context_conjI)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
    apply(rule_tac
      t="der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)"
      and s="derivation_take (derivation_drop d2' (f2 n2)) n"
      in ssubst)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(rule_tac
      m="n"
      in cfgRM.derivation_drop_preserves_derivation_prime)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
    apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
   apply(subgoal_tac "n=Suc 0")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
   apply(rule_tac
      G="G"
      in cfgRM.maximum_of_domainUnique)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
    prefer 2
    apply(rule der2_maximum_of_domain)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2 n)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2)(*strict*)
  apply(subgoal_tac "Suc (f2 n2) = n2'")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2)(*strict*)
   prefer 2
   apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_def cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_S_def)
   apply(simp add: cfgRM_cfgRM_F_CFG_TC__StateSimRL.simulating_derivation_DEF_def)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' n2' f2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
  apply(thin_tac "ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__RM_relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__RM_relation_step_simulationRL (F_CFG_TC G) G d1 (Suc n1) d1' (Suc (f1 n1)) f1")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
  apply(thin_tac "ATS_Simulation_Configuration_Weak.simulating_derivation F_CFG_TC__RM_relation_configurationRL F_CFG_TC__relation_initial_simulationRL F_CFG_TC__RM_relation_step_simulationRL (F_CFG_TC G) G d2 (Suc n2) d2' (Suc (f2 n2)) f2")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1' (f1 n1) = Some (pair e1 c1) \<and> SSd SSX = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSX)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (f1 n1)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1a e2a c1 c2)(*strict*)
  apply(rename_tac e1x e1x' c1 c1')
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2' (f2 n2) = Some (pair e1 c1) \<and> SSd SSX = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSX)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (f2 n2)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1')(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1')(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1')(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e1a e2a c1a c2)(*strict*)
  apply(rename_tac e2x e2x' c2 c2')
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: F_CFG_TC__RM_relation_configurationRL_def)
  apply(clarsimp)
  apply(thin_tac "F_CFG_TCC c2' \<in> cfgRM.get_accessible_configurations (F_CFG_TC G)")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
  apply(thin_tac "F_CFG_TCC c1' \<in> cfgRM.get_accessible_configurations (F_CFG_TC G)")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
  apply(subgoal_tac "c1' = F_CFG_TCCRev (\<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
    prefer 2
    apply(rule_tac
      c="c1'"
      in F_CFG_TCCRev_F_CFG_TCC)
    apply(rule sym)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
   apply(rule_tac
      t="\<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>"
      and s="F_CFG_TCC c1'"
      in ssubst)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
  apply(thin_tac "\<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr> = F_CFG_TCC c1'")
  apply(subgoal_tac "c2' = F_CFG_TCCRev (\<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
    prefer 2
    apply(rule_tac
      c="c2'"
      in F_CFG_TCCRev_F_CFG_TCC)
    apply(rule sym)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
   apply(rule_tac
      t="\<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>"
      and s="F_CFG_TCC c2'"
      in ssubst)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 c1' e2x e2x' c2 c2')(*strict*)
  apply(thin_tac "\<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr> = F_CFG_TCC c2'")
  apply(clarify)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
  apply(subgoal_tac "c1 = F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   prefer 2
   apply(thin_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(thin_tac " cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(thin_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(subgoal_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) 0 = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))) 0")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(thin_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def der2_def)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
  apply(subgoal_tac "c2 = F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   prefer 2
   apply(thin_tac " cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(thin_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(thin_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(subgoal_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0)0 = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))0")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(thin_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def der2_def)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' c1 e2x e2x' c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
  apply(subgoal_tac "e1x' = (F_CFG_TC__productionRev e1')")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   prefer 2
   apply(thin_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(thin_tac " cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(thin_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(subgoal_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))) (Suc 0)")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(thin_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def der2_def)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
  apply(subgoal_tac "e2x' = (F_CFG_TC__productionRev e2')")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   prefer 2
   apply(thin_tac " cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(thin_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>))))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(thin_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(subgoal_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0)(Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))(Suc 0)")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(thin_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def der2_def)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e1x' e2x e2x')(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "cfgRM_step_relation G (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "maximum_of_domain d1' (Suc (f1 n1))")
  apply(thin_tac "maximum_of_domain d2' (Suc (f2 n2))")
  apply(thin_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>))))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "derivation_take (derivation_drop d1' (f1 n1)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>) (F_CFG_TC__productionRev e1') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "cfgRM.derivation G (der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>))))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "derivation_take (derivation_drop d2' (f2 n2)) (Suc 0) = der2 (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "cfgRM_step_relation G (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>) (F_CFG_TC__productionRev e2') (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "cfgRM.derivation_initial (F_CFG_TC G) d1")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "d1 n1 = Some (pair e1 \<lparr>cfg_conf = \<delta>1 @ teA A1 # liftB y1\<rparr>)")
  apply(thin_tac "d1 (Suc n1) = Some (pair (Some e1') (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "cfgRM.derivation_initial (F_CFG_TC G) d2")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "d2 n2 = Some (pair e2 \<lparr>cfg_conf = \<delta>2 @ teA A2 # liftB y2\<rparr>)")
  apply(thin_tac "d2 (Suc n2) = Some (pair (Some e2') (F_CFG_TCC (F_CFG_TCCRev \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)))")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "f1 (Suc n1) = Suc (f1 n1)")
  apply(thin_tac "f2 (Suc n2) = Suc (f2 n2)")
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(simp add: F_CFG_TCCRev_def F_CFG_TC__wordRev_append)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "d1' (f1 n1) = Some (pair e1x \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>1 @ F_CFG_TC__wordRev [teA A1] @ liftB y1\<rparr>)")
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac
      t="F_CFG_TC__wordRev (teA A1 # liftB y1)"
      in ssubst)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(rule F_CFG_TC__wordRev_Cons)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule F_CFG_TC__wordRev_preserves_liftB)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "d1' (f1 n1) = Some (pair e1x \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>1 @ F_CFG_TC__wordRev (teA A1 # liftB y1)\<rparr>)")
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "d2' (f2 n2) = Some (pair e2x \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>2 @ F_CFG_TC__wordRev [teA A2] @ liftB y2\<rparr>)")
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac
      t="F_CFG_TC__wordRev (teA A2 # liftB y2)"
      in ssubst)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(rule F_CFG_TC__wordRev_Cons)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule F_CFG_TC__wordRev_preserves_liftB)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "d2' (f2 n2) = Some (pair e2x \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>2 @ F_CFG_TC__wordRev (teA A2 # liftB y2)\<rparr>)")
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "d1' (Suc (f1 n1)) = Some (pair (Some (F_CFG_TC__productionRev e1')) \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>1 @ F_CFG_TC__wordRev \<omega>1 @ (liftB y1)\<rparr>)")
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule sym)
   apply(rule F_CFG_TC__wordRev_preserves_liftB)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "d1' (Suc (f1 n1)) = Some (pair (Some (F_CFG_TC__productionRev e1')) \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>1 @ F_CFG_TC__wordRev \<omega>1 @ F_CFG_TC__wordRev (liftB y1)\<rparr>)")
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "d2' (Suc (f2 n2)) = Some (pair (Some (F_CFG_TC__productionRev e2')) \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>2 @ F_CFG_TC__wordRev \<omega>2 @ (liftB y2)\<rparr>)")
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule sym)
   apply(rule F_CFG_TC__wordRev_preserves_liftB)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(thin_tac "d2' (Suc (f2 n2)) = Some (pair (Some (F_CFG_TC__productionRev e2')) \<lparr>cfg_conf = F_CFG_TC__wordRev \<delta>2 @ F_CFG_TC__wordRev \<omega>2 @ F_CFG_TC__wordRev (liftB y2)\<rparr>)")
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(simp add: cfg_LRk_def)
  apply(erule_tac
      x="d1'"
      in allE)
  apply(erule_tac
      x="f1 n1"
      in allE)
  apply(erule_tac
      x="F_CFG_TC__wordRev \<delta>1"
      in allE)
  apply(erule_tac
      x="case A1 of cons_symbol_base A' \<Rightarrow> A'"
      in allE)
  apply(erule_tac
      x="y1"
      in allE)
  apply(erule_tac
      x="e1x"
      in allE)
  apply(erule_tac
      x="F_CFG_TC__productionRev e1'"
      in allE)
  apply(erule_tac
      x="F_CFG_TC__wordRev \<omega>1"
      in allE)
  apply(erule_tac
      x="d2'"
      in allE)
  apply(erule_tac
      x="f2 n2"
      in allE)
  apply(erule_tac
      x="F_CFG_TC__wordRev \<delta>2"
      in allE)
  apply(erule_tac
      x="case A2 of cons_symbol_base A' \<Rightarrow> A'"
      in allE)
  apply(erule_tac
      x="y2"
      in allE)
  apply(erule_tac
      x="e2x"
      in allE)
  apply(erule_tac
      x="F_CFG_TC__productionRev e2'"
      in allE)
  apply(erule_tac
      x="F_CFG_TC__wordRev \<omega>2"
      in allE)
  apply(erule impE)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule conjI)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(force)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule conjI)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_TC__wordRev_def)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule conjI)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(force)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule conjI)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(force)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule conjI)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_TC__wordRev_def)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule conjI)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(force)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="F_CFG_TC__wordRev \<delta>1 @ F_CFG_TC__wordRev \<omega>1 @ liftB v"
      and s=" F_CFG_TC__wordRev (\<delta>1@\<omega>1@liftB v) "
      in ssubst)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(simp (no_asm) add: F_CFG_TC__wordRev_append)
    apply(rule F_CFG_TC__wordRev_preserves_liftB)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(rule_tac
      t="F_CFG_TC__wordRev \<delta>2 @ F_CFG_TC__wordRev \<omega>2"
      and s=" F_CFG_TC__wordRev (\<delta>2@\<omega>2) "
      in ssubst)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(simp (no_asm) add: F_CFG_TC__wordRev_append)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(force)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "\<omega>1=\<omega>2")
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(rule F_CFG_TC__wordRev_inj)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(simp add: setAConcat)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(force)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' \<omega>1 n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "\<delta>1=\<delta>2")
   apply(rename_tac n1 \<delta>1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(rule F_CFG_TC__wordRev_inj)
    apply(rename_tac n1 \<delta>1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(simp add: setAConcat)
    apply(force)
   apply(rename_tac n1 \<delta>1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(force)
  apply(rename_tac n1 \<delta>1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(subgoal_tac "[teA A1]=[teA A2]")
   apply(rename_tac n1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   prefer 2
   apply(rule F_CFG_TC__wordRev_inj)
    apply(rename_tac n1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
    apply(simp add: setAConcat)
    apply(force)
   apply(rename_tac n1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
   apply(simp add: F_CFG_TC__wordRev_def)
  apply(rename_tac n1 A1 y1 e1' n2 \<delta>2 A2 y2 e2' \<omega>2 v d1' f1 d2' f2 e1x e2x)(*strict*)
  apply(force)
  done

definition F_CFG_TC__ISOM_relation_label :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_step_label
  \<Rightarrow> bool"
  where
    "F_CFG_TC__ISOM_relation_label G1 G2 p1 p2 \<equiv>
  p1 \<in> cfg_productions G1
  \<and> p2 \<in> cfg_productions G2
  \<and> F_CFG_TC__production p1 = p2"

definition F_CFG_TC__ISOM_relation_conf :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<equiv>
  c1 \<in> cfg_configurations G1
  \<and> c2 \<in> cfg_configurations G2
  \<and> c2 = F_CFG_TCC c1"

definition F_CFG_TC__ISOM_relation_initial_conf :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "F_CFG_TC__ISOM_relation_initial_conf G1 G2 c1 c2 \<equiv>
  c1 \<in> cfg_initial_configurations G1
  \<and> c2 \<in> cfg_initial_configurations G2
  \<and> c2 = F_CFG_TCC c1"

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_TSstructure_closed1: "
  (\<forall>G1. Ex (F_CFG_TC__relation_TSstructureLR G1) \<longrightarrow> valid_cfg G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_TSstructure_closed2: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> valid_cfg G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(rule F_CFG_TC__preserves_CFG)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_closed1: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. Ex (F_CFG_TC__ISOM_relation_conf G1 G2 c1) \<longrightarrow> c1 \<in> cfg_configurations G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 x)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_conf_def F_CFG_TC__relation_TSstructureLR_def)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_closed2: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> c2 \<in> cfg_configurations G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_for_initial_closed1: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> c1 \<in> cfg_initial_configurations G1 \<longrightarrow> c2 \<in> cfg_initial_configurations G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule FUN_F_CFG_TC__C_preserves_initial_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_for_initial_closed2: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> c2 \<in> cfg_initial_configurations G2 \<longrightarrow> c1 \<in> cfg_initial_configurations G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(subgoal_tac "c1 = F_CFG_TCCRev (F_CFG_TCC c1)")
   apply(rename_tac G1 G2 c1)(*strict*)
   prefer 2
   apply (metis F_CFG_TCCRev_F_CFG_TCC)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      t="c1"
      and s="F_CFG_TCCRev (F_CFG_TCC c1)"
      in ssubst)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule F_CFG_TC__C_rev_preserves_initial_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_CFG_TC__relation_TSstructureLR_def F_CFG_TC__relation_TSstructureRL_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_label_closed1: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>e1. Ex (F_CFG_TC__ISOM_relation_label G1 G2 e1) \<longrightarrow> e1 \<in> cfg_step_labels G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2 e1 x)(*strict*)
  apply(simp add: cfg_step_labels_def F_CFG_TC__ISOM_relation_label_def)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_label_closed2: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>e1 e2. F_CFG_TC__ISOM_relation_label G1 G2 e1 e2 \<longrightarrow> e2 \<in> cfg_step_labels G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 e1 e2)(*strict*)
  apply(simp add: cfg_step_labels_def F_CFG_TC__ISOM_relation_label_def)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_bijection_on: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> bijection_on (F_CFG_TC__ISOM_relation_conf G1 G2) (cfg_configurations G1) (cfg_configurations G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(rule bijection_on_intro)
     apply(rename_tac G1 G2)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 a)(*strict*)
     apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
     apply (metis FUN_F_CFG_TC__C_preserves_configurations)
    apply(rename_tac G1 G2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 b)(*strict*)
    apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
    apply(rule_tac
      x="F_CFG_TCCRev b"
      in bexI)
     apply(rename_tac G1 G2 b)(*strict*)
     apply (metis F_CFG_TCCrev_reverse F_CFG_TC__relation_TSstructureLR_def F_CFG_TC__relation_TSstructureRL_def)
    apply(rename_tac G1 G2 b)(*strict*)
    apply (metis F_CFG_TC__C_rev_preserves_configurations F_CFG_TC__relation_TSstructureLR_def F_CFG_TC__relation_TSstructureRL_def)
   apply(rename_tac G1 G2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 a b1 b2)(*strict*)
   apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
  apply(rename_tac G1 G2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 b a1 a2)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 a1 a2)(*strict*)
  apply (metis F_CFG_TCC_inj)
  done

lemma F_CFG_TC__production_inj: "
  valid_cfg G1
  \<Longrightarrow> a1 \<in> cfg_productions G1
  \<Longrightarrow> a2 \<in> cfg_productions G1
  \<Longrightarrow> F_CFG_TC__production a1 = F_CFG_TC__production a2
  \<Longrightarrow> a1 = a2"
  apply(case_tac a1)
  apply(rename_tac prod_lhs prod_rhs)(*strict*)
  apply(case_tac a2)
  apply(rename_tac prod_lhs prod_rhs prod_lhsa prod_rhsa)(*strict*)
  apply(simp add: F_CFG_TC__production_def)
  apply(clarsimp)
  apply(rename_tac prod_rhs prod_lhsa prod_rhsa)(*strict*)
  apply(rule F_CFG_TC__word_inj)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_label_bijection_on: "
  (\<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> bijection_on (F_CFG_TC__ISOM_relation_label G1 G2) (cfg_step_labels G1) (cfg_step_labels G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(rule bijection_on_intro)
     apply(rename_tac G1 G2)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 a)(*strict*)
     apply(simp add: F_CFG_TC__ISOM_relation_label_def cfg_step_labels_def)
     apply(simp add: F_CFG_TC__relation_TSstructureLR_def F_CFG_TC_def)
    apply(rename_tac G1 G2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 b)(*strict*)
    apply(simp add: F_CFG_TC__ISOM_relation_label_def cfg_step_labels_def F_CFG_TC__relation_TSstructureLR_def F_CFG_TC_def)
    apply(clarsimp)
    apply(rename_tac G1 x)(*strict*)
    apply(rule_tac
      x="x"
      in bexI)
     apply(rename_tac G1 x)(*strict*)
     apply(force)
    apply(rename_tac G1 x)(*strict*)
    apply(force)
   apply(rename_tac G1 G2)(*strict*)
   apply(simp add: F_CFG_TC__ISOM_relation_label_def)
  apply(rename_tac G1 G2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 b a1 a2)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_label_def cfg_step_labels_def F_CFG_TC__relation_TSstructureLR_def F_CFG_TC_def)
  apply(clarsimp)
  apply(rename_tac G1 a1 a2 x)(*strict*)
  apply(rule F_CFG_TC__production_inj)
     apply(rename_tac G1 a1 a2 x)(*strict*)
     apply(force)
    apply(rename_tac G1 a1 a2 x)(*strict*)
    apply(force)
   apply(rename_tac G1 a1 a2 x)(*strict*)
   apply(force)
  apply(rename_tac G1 a1 a2 x)(*strict*)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_marking_configuration1_equivalent: "
  \<forall>G1. valid_cfg G1 \<longrightarrow> (\<forall>d1. cfgSTD.derivation_initial G1 d1 \<longrightarrow> cfg_marking_condition G1 d1 = (\<exists>i c1. get_configuration (d1 i) = Some c1 \<and> c1 \<in> cfg_marking_configuration G1))"
  apply(clarsimp)
  apply(rename_tac G1 d1)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(rule antisym)
   apply(rename_tac G1 d1)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d1 i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d1 i c1)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: get_configuration_def)
  apply(case_tac "d1 i")
   apply(rename_tac G1 d1 i c1)(*strict*)
   apply(force)
  apply(rename_tac G1 d1 i c1 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G1 d1 i c1 a option conf)(*strict*)
  apply(clarsimp)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_preserves_marking_configuration: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> (c1 \<in> cfg_marking_configuration G1) = (c2 \<in> cfg_marking_configuration G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_CFG_TC__ISOM_relation_conf_def)
  apply(rule antisym)
   apply(rename_tac G1 G2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule FUN_F_CFG_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(subgoal_tac " c1 \<in> cfg_configurations G1")
   apply(rename_tac G1 G2 c1)(*strict*)
   prefer 2
   apply (metis F_CFG_TC__relation_TSstructureLR_def cfgSTD.get_accessible_configurations_are_configurations2)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "c1 = F_CFG_TCCRev (F_CFG_TCC c1)")
   apply(rename_tac G1 G2 c1)(*strict*)
   prefer 2
   apply (metis F_CFG_TCCRev_F_CFG_TCC)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      t="c1"
      and s="F_CFG_TCCRev (F_CFG_TCC c1)"
      in ssubst)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule F_CFG_TC__C_rev_preserves_marking_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_CFG_TC__relation_TSstructureRL_def F_CFG_TC__relation_TSstructureLR_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_step_preservation1: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> (\<forall>e1 c1'. cfgSTD_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>e2. F_CFG_TC__ISOM_relation_label G1 G2 e1 e2 \<longrightarrow> (\<forall>c2'. F_CFG_TC__ISOM_relation_conf G1 G2 c1' c2' \<longrightarrow> cfgSTD_step_relation G2 c2 e2 c2'))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' e2 c2')(*strict*)
  apply(simp add: F_CFG_TC__relation_configurationLR_def F_CFG_TC__ISOM_relation_label_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' c2')(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureLR_def cfgSTD_step_relation_def F_CFG_TC__production_def F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' l r)(*strict*)
  apply(rule_tac
      x="F_CFG_TC__word l"
      in exI)
  apply(rule_tac
      x="F_CFG_TC__word r"
      in exI)
  apply(simp add: F_CFG_TCC_def F_CFG_TC__production_def F_CFG_TC__word_def)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_AX_step_preservation2: "
  \<forall>G1 G2. F_CFG_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_CFG_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> (\<forall>e2 c2'. cfgSTD_step_relation G2 c2 e2 c2' \<longrightarrow> (\<forall>e1. F_CFG_TC__ISOM_relation_label G1 G2 e1 e2 \<longrightarrow> (\<forall>c1'. F_CFG_TC__ISOM_relation_conf G1 G2 c1' c2' \<longrightarrow> cfgSTD_step_relation G1 c1 e1 c1'))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e2 c2' e1 c1')(*strict*)
  apply(simp add: F_CFG_TC__relation_configurationLR_def F_CFG_TC__ISOM_relation_label_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 c2' e1 c1')(*strict*)
  apply(simp add: F_CFG_TC__relation_TSstructureLR_def cfgSTD_step_relation_def F_CFG_TC__production_def F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' l r)(*strict*)
  apply(rule_tac
      x="F_CFG_TC__wordRev l"
      in exI)
  apply(rule_tac
      x="F_CFG_TC__wordRev r"
      in exI)
  apply(simp add: F_CFG_TCC_def cfg_configurations_def F_CFG_TC_def F_CFG_TC__production_def)
  apply(clarsimp)
  apply(rename_tac G1 e1 l r c ca)(*strict*)
  apply(thin_tac "setA A \<subseteq> C" for A C)
  apply(thin_tac "setA A \<subseteq> C" for A C)
  apply(thin_tac "setA A \<subseteq> C" for A C)
  apply(thin_tac "setA A \<subseteq> C" for A C)
  apply(thin_tac "setB A \<subseteq> C" for A C)
  apply(thin_tac "setB A \<subseteq> C" for A C)
  apply(thin_tac "setB A \<subseteq> C" for A C)
  apply(thin_tac "setB A \<subseteq> C" for A C)
  apply(simp add: F_CFG_TC__word_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G1 e1 l r c ca)(*strict*)
   prefer 2
   apply(rule_tac
      f="(case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB)"
      and w="c"
      in map_decomp)
   apply(force)
  apply(rename_tac G1 e1 l r c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 e1 ca w1' w2' x')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G1 e1 ca w1' w2' x')(*strict*)
   prefer 2
   apply(rule_tac
      f="(case_DT_two_elements (\<lambda>A. teA (cons_symbol_base A)) teB)"
      and w="ca"
      in map_decomp_three)
   apply(force)
  apply(rename_tac G1 e1 ca w1' w2' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
  apply(fold F_CFG_TC__word_def)
  apply(subgoal_tac "w1'nonterminal = w1'")
   apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
   prefer 2
   apply(rule F_CFG_TC__word_inj)
   apply(force)
  apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
  apply(subgoal_tac "w3' = w2'")
   apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
   prefer 2
   apply(rule F_CFG_TC__word_inj)
   apply(force)
  apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
  apply(subgoal_tac "w2'nonterminal = (prod_rhs e1)")
   apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
   prefer 2
   apply(rule F_CFG_TC__word_inj)
   apply(force)
  apply(rename_tac G1 e1 w1' w2' x' w1'nonterminal w2'nonterminal w3')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 e1 w1' w2' x')(*strict*)
  apply(case_tac x')
   apply(rename_tac G1 e1 w1' w2' x' \<Sigma>)(*strict*)
   prefer 2
   apply(rename_tac G1 e1 w1' w2' x' b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 e1 w1' w2' x' \<Sigma>)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 e1 w1' w2')(*strict*)
  apply (metis F_CFG_TC__wordRev_F_CFG_TC__word)
  done

lemma cfg_cfg_F_CFG_TC__ISOM_inst_ATS_Isomorphism_axioms: "
  ATS_Isomorphism_axioms valid_cfg cfg_configurations cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_marking_condition valid_cfg cfg_configurations cfg_initial_configurations cfg_step_labels cfgSTD_step_relation cfg_marking_condition (\<lambda>G c. c \<in> cfg_marking_configuration G) (\<lambda>G c. c \<in> cfg_marking_configuration G) F_CFG_TC__relation_TSstructureLR F_CFG_TC__ISOM_relation_conf F_CFG_TC__ISOM_relation_label"
  apply(simp add: ATS_Isomorphism_axioms_def)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_TSstructure_closed1)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_TSstructure_closed2)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_closed1)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_closed2)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_for_initial_closed1)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_for_initial_closed2)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_label_closed1)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_label_closed2)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_bijection_on)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_label_bijection_on)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_marking_configuration1_equivalent)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_marking_configuration1_equivalent)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_relation_configuration_preserves_marking_configuration)
  apply(rule conjI)
   apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_step_preservation1)
  apply(rule cfg_cfg_F_CFG_TC__ISOM_inst_AX_step_preservation2)
  done

interpretation "cfg_cfg_F_CFG_TC__ISOM" : ATS_Isomorphism
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgSTD_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgSTD_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  (* marking_configuration1 *)
  "(\<lambda>G c. c \<in> cfg_marking_configuration G)"
  (* marking_configuration2 *)
  "(\<lambda>G c. c \<in> cfg_marking_configuration G)"
  (* relation_TSstructure *)
  "F_CFG_TC__relation_TSstructureLR"
  (* relation_configuration *)
  "F_CFG_TC__ISOM_relation_conf"
  (* relation_label *)
  "F_CFG_TC__ISOM_relation_label"
  apply(simp add: LOCALE_DEFS CFG_interpretations)
  apply(simp add: cfg_cfg_F_CFG_TC__ISOM_inst_ATS_Isomorphism_axioms)
  done

theorem F_CFG_TC__preserves_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching (F_CFG_TC G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfg_cfg_F_CFG_TC__ISOM.Nonblockingness_branching_preservation)
    apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
   apply(force)
  apply(force)
  done

lemma F_CFG_TC__wordRev_F_CFG_TC__word_id: "
  F_CFG_TC__wordRev (F_CFG_TC__word w) = w"
  apply(induct w)
   apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
  apply(rename_tac a w)(*strict*)
  apply(simp add: F_CFG_TC__wordRev_def F_CFG_TC__word_def)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_TC__productionRev_F_CFG_TC__production_id: "
  F_CFG_TC__productionRev (F_CFG_TC__production x) = x"
  apply(simp add: F_CFG_TC__productionRev_def F_CFG_TC__production_def)
  apply(case_tac x)
  apply(rename_tac prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac prod_rhs)(*strict*)
  apply(rule F_CFG_TC__wordRev_F_CFG_TC__word_id)
  done

lemma F_CFG_TC__word_drop_liftB: "
  F_CFG_TC__word (liftB w1 @ liftA w2) = liftB w1 @ (F_CFG_TC__word (liftA w2))"
  apply(induct w1)
   apply(clarsimp)
  apply(rename_tac a w1)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__word_def)
  done

lemma F_CFG_TC__word_liftA_setB: "
  setB (F_CFG_TC__word (liftA w)) = {}"
  apply(induct w)
   apply(clarsimp)
   apply(simp add: F_CFG_TC__word_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_TC__word_def)
  done

definition cfg_productions_events_on_the_left :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "cfg_productions_events_on_the_left G \<equiv>
  \<forall>e \<in> cfg_productions G.
    \<exists>w1 w2.
      prod_rhs e = liftB w1 @ liftA w2"

theorem F_CFG_TC__preserves_cfg_productions_events_on_the_left: "
  cfg_productions_events_on_the_left G
  \<Longrightarrow> cfg_productions_events_on_the_left (F_CFG_TC G)"
  apply(simp add: cfg_productions_events_on_the_left_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="F_CFG_TC__productionRev e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: F_CFG_TC_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "F_CFG_TC__productionRev (F_CFG_TC__production x)=x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule F_CFG_TC__productionRev_F_CFG_TC__production_id)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 w2)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule_tac
      x="filterA (F_CFG_TC__word (liftA w2))"
      in exI)
  apply(simp add: F_CFG_TC__productionRev_def)
  apply(simp add: F_CFG_TC_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 x)(*strict*)
  apply(case_tac x)
  apply(rename_tac w1 w2 x prod_lhs prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 prod_lhs prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac w1 w2 A w)(*strict*)
  apply(simp add: F_CFG_TC__production_def)
  apply(subgoal_tac "F_CFG_TC__wordRev (F_CFG_TC__word w) = w")
   apply(rename_tac w1 w2 A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2 A)(*strict*)
   apply(simp add: F_CFG_TC__word_drop_liftB)
   apply(rule sym)
   apply(rule liftA_filterA)
   apply(rule F_CFG_TC__word_liftA_setB)
  apply(rename_tac w1 w2 A w)(*strict*)
  apply(rule F_CFG_TC__wordRev_F_CFG_TC__word_id)
  done

definition F_CFG_TC__SpecInput1 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TC__SpecInput1 G \<equiv>
  valid_cfg G"

definition F_CFG_TC__SpecOutput1 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TC__SpecOutput1 Gi Go \<equiv>
  valid_cfg Go
  \<and> cfgSTD.unmarked_language Gi = cfgSTD.unmarked_language Go
  \<and> cfgSTD.marked_language Gi = cfgSTD.marked_language Go
  \<and> (cfgSTD.Nonblockingness_branching Gi \<longrightarrow> cfgSTD.Nonblockingness_branching Go)
  \<and> (cfg_LRk Gi (Suc 0) \<longrightarrow> cfg_LRk Go (Suc 0))
  \<and> (cfg_productions_events_on_the_left Gi \<longrightarrow> cfg_productions_events_on_the_left Go)"

theorem F_CFG_TC__SOUND1: "
  F_CFG_TC__SpecInput1 G
  \<Longrightarrow> F_CFG_TC__SpecOutput1 G (F_CFG_TC G)"
  apply(simp add: F_CFG_TC__SpecInput1_def F_CFG_TC__SpecOutput1_def)
  apply(rule context_conjI)
   apply (metis F_CFG_TC__preserves_CFG)
  apply(rule context_conjI)
   apply (metis F_CFG_TC__preserves_unmarked_language)
  apply(rule context_conjI)
   apply (metis F_CFG_TC__preserves_lang)
  apply(rule context_conjI)
   apply(metis F_CFG_TC__preserves_Nonblockingness_branching)
  apply(rule context_conjI)
   apply(metis F_CFG_TC__preserves_LR1)
  apply(metis F_CFG_TC__preserves_cfg_productions_events_on_the_left)
  done

definition F_CFG_TC__SpecInput2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TC__SpecInput2 G \<equiv>
  valid_cfg G
  \<and> cfgSTD.Nonblockingness_branching G
  \<and> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<and> cfg_LRk G (Suc 0)"

definition F_CFG_TC__SpecOutput2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_TC__SpecOutput2 Gi Go \<equiv>
  valid_cfg Go
  \<and> cfgSTD.marked_language Gi = cfgSTD.marked_language Go
  \<and> cfgSTD.Nonblockingness_branching Go
  \<and> cfg_nonterminals Go \<subseteq> cfgSTD_Nonblockingness_nonterminals Go
  \<and> cfg_LRk Go (Suc 0)"

lemma F_CFG_TC_preserves_only_cfgSTD_Nonblockingness_nonterminals: "
  valid_cfg G \<Longrightarrow>
    valid_cfg (F_CFG_TC G) \<Longrightarrow>
    cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G \<Longrightarrow>
    cfg_nonterminals (F_CFG_TC G) \<subseteq> cfgSTD_Nonblockingness_nonterminals (F_CFG_TC G)"
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(simp add: F_CFG_TC_def)
  apply(clarsimp)
  apply(subgoal_tac "xa \<in> {A \<in> cfg_nonterminals G.
              \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>}
                      {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and>
                     setA w' = {}}")
   prefer 2
   apply(force)
  apply(thin_tac "cfg_nonterminals G
          \<subseteq> {A \<in> cfg_nonterminals G.
              \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>}
                      {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and>
                     setA w' = {}}")
  apply(clarsimp)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(case_tac "d 0")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac MAXval="Suc n" in cfg_cfg_F_CFG_TC__ISOM.preserve_derivation1)
     apply(simp add: F_CFG_TC__relation_TSstructureLR_def)
    apply(force)
   apply(rule cfgSTD.derivation_belongs)
      apply(force)
     apply(force)
    apply(simp add: cfg_configurations_def)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="d2" in exI)
  apply(rule conjI)
   apply(simp add: F_CFG_TC_def)
  apply(rule conjI)
   apply(simp add: F_CFG_TC_def)
   apply(erule_tac x="0" in allE)
   apply(clarsimp)
   apply(case_tac e2)
    apply(clarsimp)
    apply(simp add: F_CFG_TC__word_def F_CFG_TCC_def F_CFG_TC__ISOM_relation_conf_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_CFG_TC_def)
  apply(erule_tac x="n" in allE')
  apply(erule_tac x="Suc n" in allE)
  apply(clarsimp)
  apply(case_tac c2)
  apply(rule_tac x="W" for W in exI)
  apply(rule conjI)
   apply(rule_tac x="n" in exI)
   apply(rule conjI)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: F_CFG_TCC_def F_CFG_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply (metis F_CFG_TC__word_preserves_no_nonterms)
  done

theorem F_CFG_TC__SOUND2: "
  F_CFG_TC__SpecInput2 G
  \<Longrightarrow> F_CFG_TC__SpecOutput2 G (F_CFG_TC G)"
  apply(simp add: F_CFG_TC__SpecOutput2_def F_CFG_TC__SpecInput2_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply (metis F_CFG_TC__preserves_CFG)
  apply(rule context_conjI)
   apply (metis F_CFG_TC__preserves_lang)
  apply(rule conjI)
   apply(metis F_CFG_TC__preserves_Nonblockingness_branching)
  apply(rule conjI)
   apply(metis F_CFG_TC_preserves_only_cfgSTD_Nonblockingness_nonterminals)
  apply(rule F_CFG_TC__preserves_LR1)
   apply(force)
  apply(force)
  done

end
