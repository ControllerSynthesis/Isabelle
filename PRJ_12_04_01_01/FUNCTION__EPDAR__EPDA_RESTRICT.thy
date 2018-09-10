section {*FUNCTION\_\_EPDAR\_\_EPDA\_RESTRICT*}
theory
  FUNCTION__EPDAR__EPDA_RESTRICT

imports
  PRJ_12_04_01_01__ENTRY

begin

lemma F_EPDA_R_preserves_valid_epda: "
  valid_epda G
  \<Longrightarrow> epda_initial G \<in> Q
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> valid_epda G'"
  apply(simp add: valid_epda_def F_EPDA_R_def valid_epda_step_label_def)
  apply(force)
  done

lemma F_EPDA_R_preserves_valid_pda: "
  valid_pda G
  \<Longrightarrow> epda_initial G \<in> Q
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> valid_pda G'"
  apply(simp add: valid_pda_def)
  apply(rule conjI)
   apply(rule F_EPDA_R_preserves_valid_epda)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: F_EPDA_R_def)
  apply(force)
  done

lemma F_EPDA_R_constructs_epda_sub: "
  valid_epda G
  \<Longrightarrow> epda_initial G \<in> Q
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epda_sub G' G"
  apply(simp add: epda_sub_def F_EPDA_R_def)
  apply(force)
  done

lemma F_EPDA_R_preserves_valid_dpda: "
  valid_dpda G
  \<Longrightarrow> epda_initial G \<in> Q
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> valid_dpda G'"
  apply(subgoal_tac "epda_sub G' G")
   prefer 2
   apply(rule F_EPDA_R_constructs_epda_sub)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(force)
   apply(force)
  apply(simp (no_asm) add: valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_dpda_def)
   apply(rule F_EPDA_R_preserves_valid_pda)
     apply(force)
    apply(force)
   apply(force)
  apply(rule epda_sub_preserves_is_forward_edge_deterministic_accessible)
    apply(force)
   apply(rule F_EPDA_R_preserves_valid_pda)
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_EPDA_R_preserves_valid_sdpda: "
  valid_simple_dpda G
  \<Longrightarrow> epda_initial G \<in> Q
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> valid_simple_dpda G'"
  apply(simp add: valid_simple_dpda_def)
  apply(rule conjI)
   apply(rule F_EPDA_R_preserves_valid_dpda)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: F_EPDA_R_def)
  apply(force)
  done

theorem F_EPDA_R_marked_language1: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.marked_language G' \<subseteq> epdaH.marked_language G"
  apply(subgoal_tac "epda_initial G \<in> Q")
   prefer 2
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(force)
   apply(rule epda_initial_in_epdaH_accessible_states)
   apply(force)
  apply(rule epda_sub_preserves_epdaH_marked_language)
    apply(force)
   apply(rule_tac G="G" in F_EPDA_R_preserves_valid_epda)
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(rule F_EPDA_R_constructs_epda_sub)
    apply(force)
   prefer 2
   apply(force)
  apply(force)
  done

theorem F_EPDA_R_unmarked_language1: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.unmarked_language G' \<subseteq> epdaH.unmarked_language G"
  apply(subgoal_tac "epda_initial G \<in> Q")
   prefer 2
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(force)
   apply(rule epda_initial_in_epdaH_accessible_states)
   apply(force)
  apply(rule epda_sub_preserves_epdaH_unmarked_language)
    apply(force)
   apply(rule_tac G="G" in F_EPDA_R_preserves_valid_epda)
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(rule F_EPDA_R_constructs_epda_sub)
    apply(force)
   prefer 2
   apply(force)
  apply(force)
  done

theorem F_EPDA_R_reflects_initial_derivations: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.derivation_initial G' d
  \<Longrightarrow> epdaH.derivation_initial G d"
  apply(subgoal_tac "epda_initial G \<in> Q")
   prefer 2
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(force)
   apply(rule epda_initial_in_epdaH_accessible_states)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac Q="Q" in F_EPDA_R_preserves_valid_epda)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaH.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac conf)(*strict*)
   apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_R_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(simp (no_asm) add: epdaH.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_def)
   apply(erule_tac x="0" in allE)+
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option conf)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat option conf)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="nat" and
      m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat option conf)(*strict*)
     apply(force)
    apply(rename_tac nat option conf)(*strict*)
    apply(force)
   apply(rename_tac nat option conf)(*strict*)
   apply(force)
  apply(rename_tac nat option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat conf e1 e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
  apply(simp add: F_EPDA_R_def)
  done

theorem F_EPDA_R_marked_language2: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.marked_language G \<subseteq> epdaH.marked_language G'"
  apply(subgoal_tac "epda_initial G \<in> Q")
   prefer 2
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(force)
   apply(rule epda_initial_in_epdaH_accessible_states)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac Q="Q" in F_EPDA_R_preserves_valid_epda)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(rule context_conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    prefer 2
    apply(case_tac "d 0")
     apply(rename_tac x d)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac x d a option conf)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d conf)(*strict*)
    apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def)
    apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(simp add: F_EPDA_R_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac x d)(*strict*)
   apply(simp (no_asm) add: epdaH.derivation_def)
   apply(clarsimp)
   apply(rename_tac x d i)(*strict*)
   apply(case_tac i)
    apply(rename_tac x d i)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(simp add: epdaH.derivation_def)
    apply(erule_tac x="0" in allE)+
    apply(clarsimp)
   apply(rename_tac x d i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat)(*strict*)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac x d nat)(*strict*)
    apply(force)
   apply(rename_tac x d nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac x d nat a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat option conf)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d nat option conf)(*strict*)
    prefer 2
    apply(rule_tac
      d="d" and
      n="nat" and
      m="Suc nat"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac x d nat option conf)(*strict*)
      apply(force)
     apply(rename_tac x d nat option conf)(*strict*)
     apply(force)
    apply(rename_tac x d nat option conf)(*strict*)
    apply(force)
   apply(rename_tac x d nat option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat conf e1 e2 c1)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
   apply(simp add: F_EPDA_R_def)
   apply(subgoal_tac "valid_epda_step_label G e2")
    apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
    prefer 2
    apply(simp add: valid_epda_def)
   apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
    apply(rule_tac A="epdaH_accessible_edges G" in set_mp)
     apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
     apply(force)
    apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
    apply(simp add: epdaH_accessible_edges_def)
    apply(rule_tac x="d" in exI)
    apply(simp add: epdaH.derivation_initial_def)
    apply(force)
   apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
    apply(rule_tac A="epdaH_accessible_states G" in set_mp)
     apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
     apply(force)
    apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
    apply(simp add: epdaH_accessible_states_def)
    apply(rule_tac x="d" in exI)
    apply(simp add: epdaH.derivation_initial_def)
    apply(rule_tac x="nat" in exI)
    apply(force)
   apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
    apply(force)
   apply(rename_tac x d nat conf e1 e2 c1 w)(*strict*)
   apply(simp add: epdaH_accessible_states_def)
   apply(rule_tac x="d" in exI)
   apply(simp add: epdaH.derivation_initial_def)
   apply(rule_tac x="Suc nat" in exI)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: epdaH_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac d i e c)(*strict*)
   apply(rule_tac x="i" in exI)
   apply(rule_tac x="e" in exI)
   apply(rule_tac x="c" in exI)
   apply(clarsimp)
   apply(simp add: epdaH_configurations_def epdaH_marking_configurations_def F_EPDA_R_def)
   apply(clarsimp)
   apply(rename_tac d i e q s h)(*strict*)
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(rename_tac d i e q s h)(*strict*)
    apply(force)
   apply(rename_tac d i e q s h)(*strict*)
   apply(simp add: epdaH_accessible_states_def)
   apply(rule_tac x="d" in exI)
   apply(simp add: epdaH.derivation_initial_def)
   apply(rule_tac x="i" in exI)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac x d)(*strict*)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(subgoal_tac "c \<in> epdaH_configurations (F_EPDA_R G Q E)")
   apply(rename_tac x d i e c)(*strict*)
   prefer 2
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac x d i e c)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac x d i e c)(*strict*)
     apply(force)
    apply(rename_tac x d i e c)(*strict*)
    apply(force)
   apply(rename_tac x d i e c)(*strict*)
   apply(force)
  apply(rename_tac x d i e c)(*strict*)
  apply(subgoal_tac "c \<in> epdaH_marking_configurations (F_EPDA_R G Q E)")
   apply(rename_tac x d i e c)(*strict*)
   prefer 2
   apply(simp add: F_EPDA_R_def epdaH_marking_configurations_def epdaH_configurations_def)
   apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(rule_tac x="i" in exI)
  apply(rule_tac x="e" in exI)
  apply(rule_tac x="c" in exI)
  apply(clarsimp)
  done

theorem F_EPDA_R_preserves_initial_derivations: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> epdaH.derivation_initial G' d"
  apply(subgoal_tac "epda_initial G \<in> Q")
   prefer 2
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(force)
   apply(rule epda_initial_in_epdaH_accessible_states)
   apply(force)
  apply(simp add: epdaH.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac conf)(*strict*)
   apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_R_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(simp (no_asm) add: epdaH.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_def)
   apply(erule_tac x="0" in allE)+
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option conf)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat option conf)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="nat" and
      m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat option conf)(*strict*)
     apply(force)
    apply(rename_tac nat option conf)(*strict*)
    apply(force)
   apply(rename_tac nat option conf)(*strict*)
   apply(force)
  apply(rename_tac nat option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat conf e1 e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
  apply(simp add: F_EPDA_R_def)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
   apply(rule_tac A="epdaH_accessible_edges G" in set_mp)
    apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
    apply(force)
   apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
   apply(simp add: epdaH_accessible_edges_def)
   apply(rule_tac x="d" in exI)
   apply(simp add: epdaH.derivation_initial_def)
   apply(force)
  apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
    apply(force)
   apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
   apply(simp add: epdaH_accessible_states_def)
   apply(rule_tac x="d" in exI)
   apply(simp add: epdaH.derivation_initial_def)
   apply(rule_tac x="nat" in exI)
   apply(force)
  apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
  apply(rule_tac A="epdaH_accessible_states G" in set_mp)
   apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
   apply(force)
  apply(rename_tac nat conf e1 e2 c1 w)(*strict*)
  apply(simp add: epdaH_accessible_states_def)
  apply(rule_tac x="d" in exI)
  apply(simp add: epdaH.derivation_initial_def)
  apply(rule_tac x="Suc nat" in exI)
  apply(force)
  done

theorem F_EPDA_R_unmarked_language2: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language G'"
  apply(subgoal_tac "epda_initial G \<in> Q")
   prefer 2
   apply(rule_tac A="epdaH_accessible_states G" in set_mp)
    apply(force)
   apply(rule epda_initial_in_epdaH_accessible_states)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac Q="Q" in F_EPDA_R_preserves_valid_epda)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(rule context_conjI)
   apply(rename_tac x d)(*strict*)
   apply(rule F_EPDA_R_preserves_initial_derivations)
       apply(rename_tac x d)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac x d)(*strict*)
      apply(force)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: epdaH_unmarked_effect_def)
  apply(rename_tac x d)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  done

lemma F_EPDA_R_livelock1: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH_livelock G
  \<Longrightarrow> epdaH_livelock G'"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d N)(*strict*)
   apply(rule F_EPDA_R_preserves_initial_derivations)
       apply(rename_tac d N)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac d N)(*strict*)
      apply(force)
     apply(rename_tac d N)(*strict*)
     apply(force)
    apply(rename_tac d N)(*strict*)
    apply(force)
   apply(rename_tac d N)(*strict*)
   apply(force)
  apply(rename_tac d N)(*strict*)
  apply(force)
  done

lemma F_EPDA_R_livelock2: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH_livelock G'
  \<Longrightarrow> epdaH_livelock G"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d N)(*strict*)
   apply(rule F_EPDA_R_reflects_initial_derivations)
       apply(rename_tac d N)(*strict*)
       prefer 5
       apply(force)
      apply(rename_tac d N)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac d N)(*strict*)
     apply(force)
    apply(rename_tac d N)(*strict*)
    apply(force)
   apply(rename_tac d N)(*strict*)
   apply(force)
  apply(rename_tac d N)(*strict*)
  apply(force)
  done

theorem F_EPDA_R_livelock: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH_livelock G = epdaH_livelock G'"
  apply(rule antisym)
   apply(simp add: F_EPDA_R_livelock2 F_EPDA_R_livelock1)
  apply(simp add: F_EPDA_R_livelock2 F_EPDA_R_livelock1)
  done

theorem F_EPDA_R_spec: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> Q
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> E
  \<Longrightarrow> F_EPDA_R G Q E = G'
  \<Longrightarrow> epdaH.marked_language G = epdaH.marked_language G'
  \<and> epdaH.unmarked_language G = epdaH.unmarked_language G'
  \<and> valid_epda G'
  \<and> (valid_pda G \<longrightarrow> valid_pda G')
  \<and> (valid_dpda G \<longrightarrow> valid_dpda G')
  \<and> (valid_simple_dpda G \<longrightarrow> valid_simple_dpda G')
  \<and> (epdaH_livelock G \<longleftrightarrow> epdaH_livelock G')"
  apply(rule conjI)
   apply (metis F_EPDA_R_marked_language1 F_EPDA_R_marked_language2  set_eq_from_double_subseteq)
  apply(rule conjI)
   apply (metis F_EPDA_R_unmarked_language1 F_EPDA_R_unmarked_language2 set_eq_from_double_subseteq)
  apply(rule conjI)
   apply (metis F_EPDA_R_preserves_valid_dpda F_EPDA_R_preserves_valid_epda F_EPDA_R_preserves_valid_pda F_EPDA_R_preserves_valid_sdpda contra_subsetD epda_initial_in_epdaH_accessible_states)
  apply(rule conjI)
   apply (metis F_EPDA_R_preserves_valid_dpda F_EPDA_R_preserves_valid_epda F_EPDA_R_preserves_valid_pda F_EPDA_R_preserves_valid_sdpda contra_subsetD epda_initial_in_epdaH_accessible_states)
  apply(rule conjI)
   apply (metis F_EPDA_R_preserves_valid_dpda F_EPDA_R_preserves_valid_epda F_EPDA_R_preserves_valid_pda F_EPDA_R_preserves_valid_sdpda contra_subsetD epda_initial_in_epdaH_accessible_states)
  apply(rule conjI)
   apply (metis F_EPDA_R_preserves_valid_dpda F_EPDA_R_preserves_valid_epda F_EPDA_R_preserves_valid_pda F_EPDA_R_preserves_valid_sdpda contra_subsetD epda_initial_in_epdaH_accessible_states)
  apply(metis F_EPDA_R_livelock)
  done

definition F_EPDA_R__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set
  \<Rightarrow> bool"
  where
    "F_EPDA_R__SpecInput G Q E \<equiv>
  valid_epda G
  \<and> epdaH_accessible_states G \<subseteq> Q
  \<and> epdaH_accessible_edges G \<subseteq> E"

definition F_EPDA_R__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_R__SpecOutput Gi Go \<equiv>
  epdaH.marked_language Gi = epdaH.marked_language Go
  \<and> epdaH.unmarked_language Gi = epdaH.unmarked_language Go
  \<and> valid_epda Go
  \<and> (valid_pda Gi \<longrightarrow> valid_pda Go)
  \<and> (valid_dpda Gi \<longrightarrow> valid_dpda Go)
  \<and> (valid_simple_dpda Gi \<longrightarrow> valid_simple_dpda Go)
  \<and> (epdaH_livelock Gi \<longleftrightarrow> epdaH_livelock Go)"

theorem F_EPDA_R__SOUND: "
  F_EPDA_R__SpecInput G Q E
  \<Longrightarrow> F_EPDA_R__SpecOutput G (F_EPDA_R G Q E)"
  apply(simp add: F_EPDA_R__SpecOutput_def F_EPDA_R__SpecInput_def F_EPDA_R_spec)
  apply(rule_tac Q="Q" and E="E" in F_EPDA_R_spec)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end
