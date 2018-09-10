section {*concrete\_supervisory\_control\_problem*}
theory concrete_supervisory_control_problem

imports
  PRJ_11__ENTRY

begin

definition epdaH_accessible_in_closed_loop :: "
  ('controller_state, 'event, 'controller_stack) epda
  \<Rightarrow> (('controller_state, 'plant_state) DT_tuple2, 'event, 'controller_stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_accessible_in_closed_loop C CL \<equiv>
    (\<forall>e \<in> epda_delta C. \<exists>d' n' e' c'. 
      epdaH.derivation_initial CL d' 
      \<and> d' n' = Some (pair (Some e') c')
      \<and> edge_src e = sel_tuple2_1 (edge_src e')
      \<and> edge_event e = edge_event e'
      \<and> edge_pop e = edge_pop e'
      \<and> edge_push e = edge_push e'
      \<and> edge_trg e = sel_tuple2_1 (edge_trg e'))
  \<and> (\<forall>q \<in> epda_states C. \<exists>d n e c. 
      epdaH.derivation_initial CL d 
      \<and> d n = Some (pair e c)
      \<and> q = sel_tuple2_1 (epdaH_conf_state c))"

lemma epdaH_accessible__implies__epdaH_accessible_in_closed_loop__for__F_DPDA_DFA_PRODUCT__if__language_inclusion: "
  valid_dpda C
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> epdaH.unmarked_language C \<subseteq> epdaH.unmarked_language P
  \<Longrightarrow> epdaH_accessible C
  \<Longrightarrow> epdaH_accessible_in_closed_loop C (F_DPDA_DFA_PRODUCT C P)"
  apply(simp add: epdaH_accessible_in_closed_loop_def epdaH_accessible_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(thin_tac "\<forall>q\<in>epda_states C.
       \<exists>d. ATS.derivation_initial epdaH_initial_configurations epdaH_step_relation C d \<and>
           (\<exists>n e c. d n = Some (pair e c) \<and> q = epdaH_conf_state c)")
   apply(clarsimp)
   apply(erule_tac x="e" in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac c)
   apply(rename_tac q1 h s)
   apply(clarsimp)
   apply(subgoal_tac "h \<in> epdaH.unmarked_language P")
    prefer 2
    apply(subgoal_tac "h \<in> epdaH.unmarked_language C")
     prefer 2
     apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def epdaH.derivation_initial_def)
     apply(rule_tac x="d" in exI)
     apply(clarsimp)
     apply(force)
    apply(force)
   apply(thin_tac "epdaH.unmarked_language C \<subseteq> epdaH.unmarked_language P")
   apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac e1 d1 n1 q1 s d2 n2 e2 c2)
   apply(case_tac c2)
   apply(clarsimp)
   apply(rename_tac e1 d1 n1 q1 s d2 n2 e2 q2 h s2)
   apply(subgoal_tac "s2 = [epda_box P]")
    prefer 2
    apply (metis DFA_stack_consists_only_of_box epdaH_conf.select_convs(3))
   apply(clarsimp)
   apply(subgoal_tac "n2 = length h")
    prefer 2
    apply (metis (mono_tags) DFA_one_symbol_per_step epdaH_conf.select_convs(2))
   apply(subgoal_tac "n1 \<ge> length h")
    prefer 2
    apply (metis epdaH_conf.select_convs(2) epda_at_most_one_symbol_per_step valid_dpda_def valid_pda_def)  
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac ints="n1-length h" in F_DPDA_DFA_PRODUCT__preserves__derivation_initial_strengthend)
            apply(force)
           apply(force)
          apply(force)
         apply (metis F_DPDA_DFA_PRODUCT__produces__PDA) 
        apply(force)
       apply(force)
      prefer 2
      apply(force)
     prefer 2
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="dR" in exI)
   apply(clarsimp)
   apply(rule_tac x="n1" in exI)
   apply(clarsimp)
   apply(case_tac n1)
    apply(clarsimp)
    apply (metis epdaH.derivation_initial_is_derivation epdaH.initialNotEdgeSome_prime)
   apply(clarsimp)
   apply(rename_tac n1)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac d="dR" and n="n1" in get_labels__seperate_last)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac d="d1" and n="n1" in get_labels__seperate_last)
    apply(force)
   apply(case_tac eR)
    apply (metis epdaH.derivation_Always_PreEdge_prime epdaH.derivation_initial_is_derivation)
   apply(clarsimp)
   apply(rename_tac eR)
   apply(simp add: strip_plant_def)
  apply(thin_tac "\<forall>e\<in>epda_delta C.
       \<exists>d. ATS.derivation_initial epdaH_initial_configurations epdaH_step_relation C d \<and>
           (\<exists>n c. d n = Some (pair (Some e) c))")
  apply(clarsimp)
  apply(erule_tac x="q" in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac q1 h s)
  apply(clarsimp)
  apply(subgoal_tac "h \<in> epdaH.unmarked_language P")
   prefer 2
   apply(subgoal_tac "h \<in> epdaH.unmarked_language C")
    prefer 2
    apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def epdaH.derivation_initial_def)
    apply(rule_tac x="d" in exI)
    apply(clarsimp)
    apply(force)
   apply(force)
  apply(thin_tac "epdaH.unmarked_language C \<subseteq> epdaH.unmarked_language P")
  apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac q2 h s2)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 q1 s1 d2 n2 e2 q2 h s2)
  apply(subgoal_tac "s2 = [epda_box P]")
   prefer 2
   apply (metis DFA_stack_consists_only_of_box epdaH_conf.select_convs(3))
  apply(clarsimp)
  apply(subgoal_tac "n2 = length h")
   prefer 2
   apply (metis (mono_tags) DFA_one_symbol_per_step epdaH_conf.select_convs(2))
  apply(subgoal_tac "n1 \<ge> length h")
   prefer 2
   apply (metis epdaH_conf.select_convs(2) epda_at_most_one_symbol_per_step valid_dpda_def valid_pda_def)  
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ints="n1-length h" in F_DPDA_DFA_PRODUCT__preserves__derivation_initial_strengthend)
           apply(force)
          apply(force)
         apply(force)
        apply (metis F_DPDA_DFA_PRODUCT__produces__PDA) 
       apply(force)
      apply(force)
     prefer 2
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="dR" in exI)
  apply(clarsimp)
  apply(rule_tac x="n1" in exI)
  apply(clarsimp)
  done

definition epdaH_specification_satisfaction :: "
  ('closed_loop_state, 'event, 'closed_loop_stack) epda
  \<Rightarrow> ('specification_state, 'event, 'specification_stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_specification_satisfaction CL S \<equiv>
  \<forall>d1 n1 e1 c1.
    epdaH.derivation_initial CL d1
    \<longrightarrow> d1 n1 = Some (pair e1 c1)
    \<longrightarrow> (\<exists>d2 n2 e2 c2.
        epdaH.derivation_initial S d2
        \<and> d2 n2 = Some (pair e2 c2)
        \<and> epdaH_conf_history c1 = epdaH_conf_history c2
        \<and> (c1 \<in> epdaH_marking_configurations CL \<longrightarrow> c2 \<in> epdaH_marking_configurations S))"

lemma DES_specification_satisfied_to_epdaH_specification_satisfaction: "
  valid_dpda S 
  \<Longrightarrow> valid_dfa P 
  \<Longrightarrow> DES_specification_satisfied (epda_to_des S) (epda_to_des SOL) 
  \<Longrightarrow> valid_dpda SOL
  \<Longrightarrow> inf (epda_to_des SOL) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)
  \<Longrightarrow> inf (epda_to_des SOL) (epda_to_des P) \<in> SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (inf (epda_to_des P) (epda_to_des S)) \<Sigma>UC 
  \<Longrightarrow> epdaH_specification_satisfaction (F_DPDA_DFA_PRODUCT SOL P) S"
  apply(simp add: epdaH_specification_satisfaction_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(simp add: DES_specification_satisfied_def)
  apply(clarsimp)
  apply(thin_tac "IsDES (epda_to_des (F_DPDA_DFA_PRODUCT SOL P))")
  apply(thin_tac "epda_to_des (F_DPDA_DFA_PRODUCT SOL P)
       \<le> epda_to_des P")
  apply(thin_tac "DES_controllability \<Sigma>UC (epda_to_des P)
        (epda_to_des (F_DPDA_DFA_PRODUCT SOL P))")
  apply(thin_tac "DES_nonblockingness
        (epda_to_des (F_DPDA_DFA_PRODUCT SOL P))")
  apply(simp add: epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def)
  apply(clarsimp)
  apply(case_tac "c1 \<in> epdaH_marking_configurations (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(subgoal_tac "epdaH_conf_history c1 \<in> ATS_Language0.unmarked_language
            epdaH_initial_configurations epdaH_step_relation
            epdaH_unmarked_effect S")
    prefer 2
    apply(rule_tac A="ATS_Language0.unmarked_language
         epdaH_initial_configurations epdaH_step_relation
         epdaH_unmarked_effect (F_DPDA_DFA_PRODUCT SOL P)" in set_mp)
     apply(force)
    apply(simp add: epdaH.unmarked_language_def)
    apply(rule_tac x="d1" in exI)
    apply(clarsimp)
    apply(simp add: epdaH_unmarked_effect_def epdaH.derivation_initial_def)
    apply(force)
   apply(simp add: epdaH.unmarked_language_def)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(clarsimp)
   apply(simp add: epdaH_unmarked_effect_def epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_conf_history c1 \<in> epdaH.marked_language S")
   prefer 2
   apply(rule_tac A="epdaH.marked_language (F_DPDA_DFA_PRODUCT SOL P)" in set_mp)
    apply(force)
   apply(simp add: epdaH.marked_language_def)
   apply(rule_tac x="derivation_take d1 n1" in exI)
   apply(subgoal_tac "epdaH.derivation_initial (F_DPDA_DFA_PRODUCT SOL P) (derivation_take d1 n1)")
    prefer 2
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(clarsimp)
   apply(simp add: epdaH_marked_effect_def epdaH.derivation_initial_def epdaH_marking_condition_def)   
   apply(rule context_conjI)
    prefer 2
    apply(blast)
   apply(rule_tac x="n1" in exI)
   apply(clarsimp)
   apply(subgoal_tac "derivation_take d1 n1 n1 = Some (pair e1 c1)")
    prefer 2
    apply(simp add: derivation_take_def)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(force)
   apply (metis (no_types, hide_lams) antisym derivation_take_def less_imp_le_nat less_not_refl option.distinct(2))
  apply(simp add: epdaH_marked_effect_def epdaH.marked_language_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(simp add: epdaH_marked_effect_def epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(rule_tac x="i" in exI)
  apply(clarsimp)
  done

definition SCP_SATISFACTORY_CONTROLLER_DPDA :: "
  ('specification_state, 'event, 'specification_stack) epda
  \<Rightarrow> ('plant_state, 'event, nat) epda
  \<Rightarrow> 'event set
  \<Rightarrow> ('controller_state, 'event, 'controller_stack) epda set" 
  where
    "SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC \<equiv>
  {C. valid_dpda C 
    \<and> epda_operational_controllable C P \<Sigma>UC
    \<and> epdaH.Nonblockingness_branching (F_DPDA_DFA_PRODUCT C P)
    \<and> epdaH_specification_satisfaction (F_DPDA_DFA_PRODUCT C P) S
    \<and> epdaH_deadlock_freedom (F_DPDA_DFA_PRODUCT C P)
    \<and> epdaH_livelock_freedom (F_DPDA_DFA_PRODUCT C P)}"

definition SCP_SATISFACTORY_CLOSED_LOOP_DPDA :: "
  ('specification_state, 'event, 'specification_stack) epda
  \<Rightarrow> ('plant_state, 'event, nat) epda
  \<Rightarrow> 'event set
  \<Rightarrow> (('controller_state, 'plant_state) DT_tuple2, 'event, 'controller_stack) epda set" 
  where
    "SCP_SATISFACTORY_CLOSED_LOOP_DPDA S P \<Sigma>UC \<equiv>
  {F_DPDA_DFA_PRODUCT C P | C. C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC}"

definition SCP_DPDA_DFA_IS_SUPREMUM :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda set
  \<Rightarrow> bool" 
  where
    "SCP_DPDA_DFA_IS_SUPREMUM G GS \<equiv>
  Sup (epda_to_des ` GS) = epda_to_des G"

definition SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY :: "
  ('specification_state, 'event, 'specification_stack) epda
  \<Rightarrow> ('plant_state, 'event, nat) epda
  \<Rightarrow> 'event set
  \<Rightarrow> ('controller_state, 'event, 'controller_stack) epda set" 
  where
    "SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY S P \<Sigma>UC \<equiv>
  {C. 
  C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC
  \<and> SCP_DPDA_DFA_IS_SUPREMUM (F_DPDA_DFA_PRODUCT C P) (SCP_SATISFACTORY_CLOSED_LOOP_DPDA S P \<Sigma>UC)
  \<and> epda_to_des (F_DPDA_DFA_PRODUCT C P) = Sup (SCP_Closed_Loop_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC)
  \<and> F_DPDA_DFA_PRODUCT C P \<in> SCP_SATISFACTORY_CLOSED_LOOP_DPDA S P \<Sigma>UC}"

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness:"
  C2 \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> inf (epda_to_des C2) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C2 P)
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> DES_nonblockingness (epda_to_des (F_DPDA_DFA_PRODUCT C2 P))"
  apply(subgoal_tac "valid_dpda C2")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "ATS_Language0.Nonblockingness_branching epdaH_configurations epdaH_initial_configurations epda_step_labels
     epdaH_step_relation epdaH_marking_condition (F_DPDA_DFA_PRODUCT C2 P)")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(simp add: DES_nonblockingness_def)
  apply(simp add: inf_DES_ext_def infDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def epda_to_des_def epdaH_specification_satisfaction_def)
  apply(subgoal_tac "valid_epda (F_DPDA_DFA_PRODUCT C2 P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__generates__DPDA valid_dpda_def valid_pda_def)
  apply(rule epdaH.AX_BF_Bra_OpLa)
   apply(force)
  apply(force)
  done

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied: "
  C2 \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> inf (epda_to_des C2) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C2 P)
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> DES_specification_satisfied (inf (epda_to_des P) (epda_to_des S)) (epda_to_des (F_DPDA_DFA_PRODUCT C2 P))"
  apply(simp add: DES_specification_satisfied_def) 
  apply(rule conjI)
   apply (metis inf.commute inf_le1)
  apply(subgoal_tac "ATS_Language0.Nonblockingness_branching epdaH_configurations epdaH_initial_configurations epda_step_labels
     epdaH_step_relation epdaH_marking_condition (F_DPDA_DFA_PRODUCT C2 P)")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "valid_dpda C2")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "epdaH_specification_satisfaction (F_DPDA_DFA_PRODUCT C2 P) S")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(thin_tac "C2 \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC")
  apply(simp add: inf_DES_ext_def infDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def epda_to_des_def epdaH_specification_satisfaction_def)
  apply(clarsimp)
  apply(rule conjI) 
   apply(thin_tac "ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect C2 \<inter>
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect P =
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect (F_DPDA_DFA_PRODUCT C2 P)")
   apply(clarsimp)
   apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(erule_tac x="d" in allE)
   apply(clarsimp)
   apply(erule_tac x="i" in allE)
   apply(clarsimp)
   apply(rule_tac x="d2" in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(force)
  apply(thin_tac "ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect C2 \<inter>
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect P =
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect (F_DPDA_DFA_PRODUCT C2 P)")
  apply(clarsimp)
  apply(simp add: epdaH.marked_language_def epdaH_marked_effect_def)
  apply(clarsimp)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(erule_tac x="i" and P="%n1. \<forall>e1 c1.
          d n1 = Some (pair e1 c1) \<longrightarrow>
          (\<exists>d2. ATS.derivation_initial epdaH_initial_configurations epdaH_step_relation S d2 \<and>
                (\<exists>n2 e2 c2.
                    d2 n2 = Some (pair e2 c2) \<and>
                    epdaH_conf_history c1 = epdaH_conf_history c2 \<and>
                    (c1 \<in> epdaH_marking_configurations (F_DPDA_DFA_PRODUCT C2 P) \<longrightarrow>
                     c2 \<in> epdaH_marking_configurations S))) " in allE)
  apply(clarsimp)
  apply(rule_tac x="derivation_take d2 n2" in exI)
  apply(subgoal_tac "epdaH.derivation_initial (S) (derivation_take d2 n2)")
   prefer 2
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(clarsimp)
  apply(simp add: epdaH_marked_effect_def epdaH.derivation_initial_def epdaH_marking_condition_def)   
  apply(rule context_conjI)
   prefer 2
   apply(blast)
  apply(rule_tac x="n2" in exI)
  apply(clarsimp)
  apply(subgoal_tac "derivation_take d2 n2 n2 = Some (pair e2 c2)")
   prefer 2
   apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply (metis (no_types, hide_lams) antisym derivation_take_def less_imp_le_nat less_not_refl option.distinct(2))
  done

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied2: "
  C2 \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> inf (epda_to_des C2) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C2 P)
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> DES_specification_satisfied (epda_to_des S) (epda_to_des (F_DPDA_DFA_PRODUCT C2 P))"
  apply(simp add: DES_specification_satisfied_def) 
  apply(subgoal_tac "ATS_Language0.Nonblockingness_branching epdaH_configurations epdaH_initial_configurations epda_step_labels
     epdaH_step_relation epdaH_marking_condition (F_DPDA_DFA_PRODUCT C2 P)")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "valid_dpda C2")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "epdaH_specification_satisfaction (F_DPDA_DFA_PRODUCT C2 P) S")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(thin_tac "C2 \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC")
  apply(simp add: inf_DES_ext_def infDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def epda_to_des_def epdaH_specification_satisfaction_def)
  apply(clarsimp)
  apply(rule conjI) 
   apply(thin_tac "ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect C2 \<inter>
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect P =
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect (F_DPDA_DFA_PRODUCT C2 P)")
   apply(clarsimp)
   apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(erule_tac x="d" in allE)
   apply(clarsimp)
   apply(erule_tac x="i" in allE)
   apply(clarsimp)
   apply(rule_tac x="d2" in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(force)
  apply(thin_tac "ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect C2 \<inter>
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect P =
    ATS_Language0.marked_language epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect (F_DPDA_DFA_PRODUCT C2 P)")
  apply(clarsimp)
  apply(simp add: epdaH.marked_language_def epdaH_marked_effect_def)
  apply(clarsimp)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(erule_tac x="i" and P="%n1. \<forall>e1 c1.
          d n1 = Some (pair e1 c1) \<longrightarrow>
          (\<exists>d2. ATS.derivation_initial epdaH_initial_configurations epdaH_step_relation S d2 \<and>
                (\<exists>n2 e2 c2.
                    d2 n2 = Some (pair e2 c2) \<and>
                    epdaH_conf_history c1 = epdaH_conf_history c2 \<and>
                    (c1 \<in> epdaH_marking_configurations (F_DPDA_DFA_PRODUCT C2 P) \<longrightarrow>
                     c2 \<in> epdaH_marking_configurations S))) " in allE)
  apply(clarsimp)
  apply(rule_tac x="derivation_take d2 n2" in exI)
  apply(subgoal_tac "epdaH.derivation_initial (S) (derivation_take d2 n2)")
   prefer 2
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(clarsimp)
  apply(simp add: epdaH_marked_effect_def epdaH.derivation_initial_def epdaH_marking_condition_def)   
  apply(rule context_conjI)
   prefer 2
   apply(blast)
  apply(rule_tac x="n2" in exI)
  apply(clarsimp)
  apply(subgoal_tac "derivation_take d2 n2 n2 = Some (pair e2 c2)")
   prefer 2
   apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply (metis (no_types, hide_lams) antisym derivation_take_def less_imp_le_nat less_not_refl option.distinct(2))
  done

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability: "
  C2 \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> inf (epda_to_des C2) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C2 P) 
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des (F_DPDA_DFA_PRODUCT C2 P))"
  apply(subgoal_tac "valid_dpda (F_DPDA_DFA_PRODUCT C2 P)")
   prefer  2
   apply (rule F_DPDA_DFA_PRODUCT__generates__DPDA)
     prefer 3
     apply(force)
    apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
   apply(force)
  apply(subgoal_tac "DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des (C2))")
   apply (metis DES_controllability_infimum inf_DES_ext_def)
  apply(subgoal_tac "epda_operational_controllable C2 P \<Sigma>UC")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="C2" and SigmaUC="\<Sigma>UC" and P="P" in epda_epda_operational_controllable_to_Cont)
      apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
     apply(force)
    apply(force)
   apply(simp add: DES_controllability_def)
   apply(simp add: inf_DES_ext_def infDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def epda_to_des_def)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac A="(ATS_Language0.unmarked_language epdaH_initial_configurations epdaH_step_relation
             epdaH_unmarked_effect (C2))" and L="(ATS_Language0.unmarked_language epdaH_initial_configurations epdaH_step_relation
             epdaH_unmarked_effect P)" in Soundness_of_Controllable_Sublanguage)
   apply(force)
  apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  done

lemma inf_preserves_IsDES: "
  IsDES P
\<Longrightarrow> IsDES P2
\<Longrightarrow> IsDES (inf P P2)"
  apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  done

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO__SCP_Closed_Loop_Satisfactory_Direct_adapted_specification: "
  C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> inf (epda_to_des C) (epda_to_des P) \<in> SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (inf (epda_to_des P) (epda_to_des S)) \<Sigma>UC"
  apply(subgoal_tac "valid_dpda C")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(subgoal_tac "inf (epda_to_des C) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__epda_to_des) 
  apply(rule conjI)
   apply(rule inf_preserves_IsDES)
    apply(rule epda_to_des_enforces_IsDES)
    apply (metis valid_dpda_def valid_pda_def)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dfa_def valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO__SCP_Closed_Loop_Satisfactory_Direct: "
  C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> inf (epda_to_des C) (epda_to_des P) \<in> SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (epda_to_des S) \<Sigma>UC"
  apply(subgoal_tac "valid_dpda C")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(subgoal_tac "inf (epda_to_des C) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__epda_to_des) 
  apply(rule conjI)
   apply(rule inf_preserves_IsDES)
    apply(rule epda_to_des_enforces_IsDES)
    apply (metis valid_dpda_def valid_pda_def)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dfa_def valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied2)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epda_to_des__F_DPDA_DFA_PRODUCT: "
  valid_dpda C
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> epda_to_des (F_DPDA_DFA_PRODUCT C P) \<le> epda_to_des P"
  apply (metis F_DPDA_DFA_PRODUCT__epda_to_des inf_le2)
  done

lemma SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability2: "
  C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des C)"
  apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="C" and SigmaUC="\<Sigma>UC" and P="P" in epda_epda_operational_controllable_to_Cont)
     apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
    apply(force)
   apply(force)
  apply(simp add: DES_controllability_def)
  apply(simp add: inf_DES_ext_def infDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def epda_to_des_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac A="(ATS_Language0.unmarked_language epdaH_initial_configurations epdaH_step_relation
             epdaH_unmarked_effect (C))" and L="(ATS_Language0.unmarked_language epdaH_initial_configurations epdaH_step_relation
             epdaH_unmarked_effect P)" in Soundness_of_Controllable_Sublanguage)
  apply(force)
  done

theorem SCP_SATISFACTORY_CONTROLLER_DPDA__TO__SCP_Controller_Satisfactory: "
  C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> epda_to_des C \<in> SCP_Controller_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC"
  apply(subgoal_tac "valid_dpda C")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(subgoal_tac "inf (epda_to_des C) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__epda_to_des) 
  apply(rule conjI)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability2)
   apply(force)
  apply(force)
  done

theorem SCP_SATISFACTORY_CLOSED_LOOP_DPDA__TO__SCP_Closed_Loop_Satisfactory: "
  CL \<in> SCP_SATISFACTORY_CLOSED_LOOP_DPDA S P \<Sigma>UC 
  \<Longrightarrow> valid_dpda S 
  \<Longrightarrow> valid_dfa P  
  \<Longrightarrow> epda_to_des CL \<in> SCP_Closed_Loop_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC"
  apply(simp add: SCP_Closed_Loop_Satisfactory_def)
  apply(simp add: SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def)
  apply(clarsimp)
  apply(rule_tac x="epda_to_des C" in exI)
  apply(rule conjI)
   apply(simp add: SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def SCP_SATISFACTORY_CONTROLLER_DPDA_def)
   apply(clarsimp)
   apply (metis F_DPDA_DFA_PRODUCT__epda_to_des inf.absorb2 inf.commute inf_le2)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(rule conjI)
   apply(rule epda_to_des_enforces_IsDES)
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
   apply (metis valid_dpda_def valid_pda_def)
  apply(subgoal_tac "valid_dpda C")
   prefer 2
   apply(simp add: SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "inf (epda_to_des C) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__epda_to_des) 
  apply(clarsimp)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability2)
   apply(force)
  apply(force)
  done

lemma SCP_Closed_Loop_Satisfactory__vs__SCP_Closed_Loop_Satisfactory_Direct: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Closed_Loop_Satisfactory_Direct P S \<Sigma>UC = SCP_Closed_Loop_Satisfactory P S \<Sigma>UC"
  apply(rule antisym)
   apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def SCP_Closed_Loop_Satisfactory_def SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rule_tac x="x" in exI) 
   apply(clarsimp)
   apply(rule context_conjI)
    apply (metis le_iff_inf)
   apply(force)
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def SCP_Closed_Loop_Satisfactory_def SCP_Controller_Satisfactory_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply (metis inf_preserves_IsDES)
  apply (metis DES_controllability_infimum)
  done

lemma SCP_Controller_Least_Restrictive__vs__SCP_Controller_Least_Restrictive_Direct: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Controller_Least_Restrictive P S \<Sigma>UC = SCP_Controller_Least_Restrictive_Direct P S \<Sigma>UC"
  apply (metis SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct)
  done

theorem SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY__vs__SCP_Controller_Least_Restrictive_Direct: "
  valid_dfa P
  \<Longrightarrow> valid_dpda S
  \<Longrightarrow> C \<in> SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY S P \<Sigma>UC
  \<Longrightarrow> P' = epda_to_des P
  \<Longrightarrow> S' = epda_to_des S
  \<Longrightarrow> C' = epda_to_des C
  \<Longrightarrow> C' \<in> SCP_Controller_Least_Restrictive P' S' \<Sigma>UC"
  apply(subgoal_tac "C' \<in> SCP_Controller_Least_Restrictive_Direct P' S' \<Sigma>UC")
   apply (metis SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct epda_to_des_enforces_IsDES valid_dfa_def valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(subgoal_tac "valid_dpda C")
   prefer 2
   apply(simp add: SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY_def SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__SCP_Closed_Loop_Satisfactory_Direct_adapted_specification)
     apply(simp add: SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY_def)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: SCP_Controller_Least_Restrictive_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(rule context_conjI)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dpda_def valid_pda_def)
  apply(subgoal_tac "SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (epda_to_des S) \<Sigma>UC = SCP_Closed_Loop_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC")
   prefer 2
   apply(rule SCP_Closed_Loop_Satisfactory__vs__SCP_Closed_Loop_Satisfactory_Direct)
    apply (metis epda_to_des_enforces_IsDES valid_dfa_def valid_dpda_def valid_pda_def)
   apply (metis epda_to_des_enforces_IsDES valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(simp add: SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY_def SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def SCP_DPDA_DFA_IS_SUPREMUM_def)
  apply(subgoal_tac "epda_to_des (F_DPDA_DFA_PRODUCT C P) = inf (epda_to_des C) (epda_to_des P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__epda_to_des)
  apply(clarsimp)
  done

end
