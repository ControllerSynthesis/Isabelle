section {*I\_epda\_HS\_H*}
theory
  I_epda_HS_H

imports
  I_epda_H
  I_epda_HS

begin

definition epdaHvHS_Lin2BraConf :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf"
  where
    "epdaHvHS_Lin2BraConf x \<equiv>
  \<lparr>epdaH_conf_state = epdaHS_conf_state x,
  epdaH_conf_history = epdaHS_conf_history x,
  epdaH_conf_stack = epdaHS_conf_stack x\<rparr>"

definition epdaHvHS_Bra2LinConf :: "
  ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf"
  where
    "epdaHvHS_Bra2LinConf c w \<equiv>
  \<lparr>epdaHS_conf_state = epdaH_conf_state c,
  epdaHS_conf_history = epdaH_conf_history c,
  epdaHS_conf_scheduler = w,
  epdaHS_conf_stack = epdaH_conf_stack c\<rparr>"

definition epdaHvHS_Bra2LinFin :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list"
  where
    "epdaHvHS_Bra2LinFin G w \<equiv>
  w"
declare epdaHvHS_Bra2LinFin_def [simp add]

definition epdaHvHS_Bra2LinStep :: "
  ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> 'event list"
  where
    "epdaHvHS_Bra2LinStep c1 e c2 \<equiv>
  option_to_list (edge_event e)"

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_steps: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1l. c1l \<in> epdaHS_configurations G \<longrightarrow> (\<forall>e c2l. epdaHS_step_relation G c1l e c2l \<longrightarrow> epdaH_step_relation G (epdaHvHS_Lin2BraConf c1l) e (epdaHvHS_Lin2BraConf c2l))))"
  apply(clarsimp)
  apply(rename_tac G c1l e c2l)(*strict*)
  apply(simp add: epdaHS_step_relation_def epdaH_step_relation_def epdaHvHS_Lin2BraConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_initiality: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cl. cl \<in> epdaHS_initial_configurations G \<longrightarrow> epdaHvHS_Lin2BraConf cl \<in> epdaH_initial_configurations G))"
  apply(clarsimp)
  apply(rename_tac G cl)(*strict*)
  apply(simp add: epdaHS_initial_configurations_def epdaH_initial_configurations_def epdaHvHS_Lin2BraConf_def epdaH_configurations_def epdaHS_configurations_def)
  apply(clarsimp)
  done

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_configurations: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cl. cl \<in> epdaHS_configurations G \<longrightarrow> epdaHvHS_Lin2BraConf cl \<in> epdaH_configurations G))"
  apply(clarsimp)
  apply(rename_tac G cl)(*strict*)
  apply(simp add: epdaHS_initial_configurations_def epdaH_initial_configurations_def epdaHvHS_Lin2BraConf_def epdaH_configurations_def epdaHS_configurations_def)
  apply(clarsimp)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinStep_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1B. c1B \<in> epdaH_configurations G \<longrightarrow> (\<forall>e c2B. epdaH_step_relation G c1B e c2B \<longrightarrow> epdaHvHS_Bra2LinStep c1B e c2B \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G c1B e c2B)(*strict*)
  apply(simp add: option_to_list_def epdaHvHS_Bra2LinStep_def epdaH_step_relation_def epda_effects_def)
  apply(clarsimp)
  apply(rename_tac G c1B e c2B x w)(*strict*)
  apply(case_tac "edge_event e")
   apply(rename_tac G c1B e c2B x w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G c1B e c2B x w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1B e c2B w a)(*strict*)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(simp add: valid_epda_step_label_def)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(rename_tac G c1B e c2B w a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c1B e c2B w a)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_set_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinFin_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<exists>cB. cB \<in> epdaH_configurations G) \<longrightarrow> [] \<in> epda_effects G)"
  apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(simp add: epda_effects_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_schedl_get: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB sL. epdaHvHS_Bra2LinConf cB sL \<in> epdaHS_configurations G \<longrightarrow> sL \<in> epda_effects G \<longrightarrow> epdaHS_get_scheduler (epdaHvHS_Bra2LinConf cB sL) = sL)) "
  apply(clarsimp)
  apply(rename_tac G cB sL)(*strict*)
  apply(simp add: epdaHS_get_scheduler_def epdaHvHS_Bra2LinConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_schedl_get2: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>s1L. s1L \<in> epda_effects G \<longrightarrow> s1L = epdaHS_get_scheduler (epdaHvHS_Bra2LinConf cB s1L))))"
  apply(clarsimp)
  apply(rename_tac G cB s1L)(*strict*)
  apply(simp add: epdaHS_get_scheduler_def epdaHvHS_Bra2LinConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinFin_creates_proper_extension: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> epdaHvHS_Bra2LinConf cB [] \<in> epdaHS_configurations G))"
  apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_configurations_def epdaHS_configurations_def)
  apply(force)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1B. c1B \<in> epdaH_configurations G \<longrightarrow> (\<forall>e c2B. epdaH_step_relation G c1B e c2B \<longrightarrow> (\<forall>sL. epdaHvHS_Bra2LinConf c2B sL \<in> epdaHS_configurations G \<longrightarrow> epdaHvHS_Bra2LinConf c1B (epdaHvHS_Bra2LinStep c1B e c2B @ sL) \<in> epdaHS_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G c1B e c2B sL)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Bra2LinStep_def epdaHS_configurations_def)
  apply(clarsimp)
  apply(simp add: epdaH_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2B sL q s h x)(*strict*)
  apply(simp add: option_to_list_def epdaHvHS_Bra2LinStep_def epdaH_step_relation_def epda_effects_def)
  apply(clarsimp)
  apply(rename_tac G e c2B sL h x w)(*strict*)
  apply(case_tac "edge_event e")
   apply(rename_tac G e c2B sL h x w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G e c2B sL h x w a)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_vs_epdaHS_inst_AX_lin_step_relation_from_Bra2LinStep: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1B. c1B \<in> epdaH_configurations G \<longrightarrow> (\<forall>e c2B. epdaH_step_relation G c1B e c2B \<longrightarrow> (\<forall>sL. epdaHvHS_Bra2LinConf c2B sL \<in> epdaHS_configurations G \<longrightarrow> epdaHS_step_relation G (epdaHvHS_Bra2LinConf c1B (epdaHvHS_Bra2LinStep c1B e c2B @ sL)) e (epdaHvHS_Bra2LinConf c2B sL)))))"
  apply(clarsimp)
  apply(rename_tac G c1B e c2B sL)(*strict*)
  apply(simp add: epdaH_step_relation_def epdaH_configurations_def epdaHvHS_Bra2LinConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_only_modifies_lin_unfixed_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL sL. epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) sL \<in> epdaHS_configurations G \<longrightarrow> epdaHS_set_unfixed_scheduler cL (epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) sL)) = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) sL))"
  apply(clarsimp)
  apply(rename_tac G cL sL)(*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_def epdaHS_get_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_inj: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>s1L s2L. epdaHvHS_Bra2LinConf cB s1L = epdaHvHS_Bra2LinConf cB s2L \<longrightarrow> s1L = s2L)))"
  apply(clarsimp)
  apply(rename_tac G cB s1L s2L)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_equal_by_fixed_unfixed_and_nonscheduler_part: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>cL. cL \<in> epdaHS_configurations G \<longrightarrow> epdaHS_set_unfixed_scheduler (epdaHvHS_Bra2LinConf cB []) (epdaHS_get_unfixed_scheduler cL) = cL \<longrightarrow> cB = epdaHvHS_Lin2BraConf cL)))"
  apply(clarsimp)
  apply(rename_tac G cB cL)(*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def)
  apply(case_tac cB)
  apply(rename_tac G cB cL epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac G cL epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(case_tac cL)
  apply(rename_tac G cL epdaH_conf_state epdaH_conf_history epdaH_conf_stack epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_scheduler epdaHS_conf_stacka)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_preserves_initiality: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>sL. sL \<in> epda_effects G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_initial_configurations G \<longrightarrow> epdaHvHS_Bra2LinConf cB sL \<in> epdaHS_initial_configurations G)))"
  apply(clarsimp)
  apply(rename_tac G sL cB)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_initial_configurations_def epdaHS_initial_configurations_def epdaH_configurations_def epdaHS_configurations_def epda_effects_def)
  apply(clarsimp)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_preserves_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>sL. sL \<in> epda_effects G \<longrightarrow> epdaHvHS_Bra2LinConf cB sL \<in> epdaHS_configurations G \<longrightarrow> epdaHS_conf_history (epdaHvHS_Bra2LinConf cB sL) = epdaH_conf_history cB)))"
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL. cL \<in> epdaHS_configurations G \<longrightarrow> epdaHS_conf_history cL = epdaH_conf_history (epdaHvHS_Lin2BraConf cL)))"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_ATS_Branching_Versus_Linear1_axioms: "
  ATS_Branching_Versus_Linear1_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epdaHS_step_relation epda_effects
     epda_effects epdaHS_get_scheduler (@) epdaHS_get_unfixed_scheduler
     epdaHS_set_unfixed_scheduler epdaHS_conf_history epdaH_configurations
     epdaH_initial_configurations epdaH_step_relation
     epdaH_get_fixed_scheduler epdaH_conf_history epdaHvHS_Lin2BraConf
     epdaHvHS_Bra2LinConf epdaHvHS_Bra2LinStep epdaHvHS_Bra2LinFin"
  apply(simp add: ATS_Branching_Versus_Linear1_axioms_def)
  apply(simp add: epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_configurations epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_initiality epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_steps )
  apply(simp add: epdaH_vs_epdaHS_inst_AX_Bra2LinStep_closed epdaH_vs_epdaHS_inst_AX_Bra2LinFin_closed epdaH_vs_epdaHS_inst_AX_Bra2LinConf_schedl_get epdaH_vs_epdaHS_inst_AX_Bra2LinConf_schedl_get2 epdaH_vs_epdaHS_inst_AX_Bra2LinFin_creates_proper_extension epdaH_vs_epdaHS_inst_AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed epdaH_vs_epdaHS_inst_AX_lin_step_relation_from_Bra2LinStep epdaH_vs_epdaHS_inst_AX_Bra2LinConf_only_modifies_lin_unfixed_scheduler epdaH_vs_epdaHS_inst_AX_Bra2LinConf_inj epdaH_vs_epdaHS_inst_AX_equal_by_fixed_unfixed_and_nonscheduler_part epdaH_vs_epdaHS_inst_AX_Bra2LinConf_preserves_initiality )
  apply(rule conjI)
   apply(simp add: epdaH_vs_epdaHS_inst_AX_Bra2LinConf_preserves_history )
  apply(simp add: epdaH_vs_epdaHS_inst_AX_Lin2BraConf_preserves_history)
  done

interpretation "epdaH_vs_epdaHS" : ATS_Branching_Versus_Linear1
  (* TSstructure *)
  "valid_epda"
  (* lin_configurations *)
  "epdaHS_configurations"
  (* lin_initial_configurations *)
  "epdaHS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* lin_step_relation *)
  "epdaHS_step_relation"
  (* effects *)
  "epda_effects"
  (* lin_marking_condition *)
  "epdaHS_marking_condition"
  (* lin_marked_effect *)
  "epdaHS_marked_effect"
  (* lin_unmarked_effect *)
  "epdaHS_unmarked_effect"
  (* lin_fixed_schedulers *)
  epda_fixed_schedulers
  (* lin_empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* lin_fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* lin_scheduler_fragments *)
  "epda_effects"
  (* lin_empty_scheduler_fragment *)
  epda_empty_scheduler_fragment
  (* lin_join_scheduler_fragments *)
  "append"
  (* lin_unfixed_schedulers *)
  "epda_effects"
  (* lin_empty_unfixed_scheduler *)
  epda_empty_unfixed_scheduler
  (* lin_unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* lin_extend_unfixed_scheduler *)
  "append"
  (* lin_unfixed_scheduler_extendable *)
  epda_unfixed_scheduler_extendable
  (* lin_schedulers *)
  "epda_effects"
  (* lin_initial_schedulers *)
  "epda_effects"
  (* lin_empty_scheduler *)
  epda_empty_scheduler
  (* lin_get_scheduler *)
  "epdaHS_get_scheduler"
  (* lin_join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* lin_extend_scheduler *)
  "append"
  (* lin_get_unfixed_scheduler *)
  "epdaHS_get_unfixed_scheduler"
  (* lin_set_unfixed_scheduler *)
  "epdaHS_set_unfixed_scheduler"
  (* lin_get_fixed_scheduler *)
  epdaHS_get_fixed_scheduler
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  "epda_empty_history"
  (* empty_history_fragment *)
  "epda_empty_history_fragment"
  (* lin_set_history *)
  "epdaHS_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* lin_get_history *)
  "epdaHS_conf_history"
  (* bra_configurations *)
  "epdaH_configurations"
  (* bra_initial_configurations *)
  "epdaH_initial_configurations"
  (* bra_step_relation *)
  "epdaH_step_relation"
  (* bra_marking_condition *)
  "epdaH_marking_condition"
  (* bra_marked_effect *)
  "epdaH_marked_effect"
  (* bra_unmarked_effect *)
  "epdaH_unmarked_effect"
  (* bra_fixed_schedulers *)
  epda_fixed_schedulers
  (* bra_empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* bra_fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* bra_get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* bra_set_history *)
  "epdaH_set_history"
  (* bra_get_history *)
  "epdaH_conf_history"
  (* Lin2BraConf *)
  "epdaHvHS_Lin2BraConf"
  (* Bra2LinConf *)
  "epdaHvHS_Bra2LinConf"
  (* Bra2LinStep *)
  "epdaHvHS_Bra2LinStep"
  (* Bra2LinFin *)
  epdaHvHS_Bra2LinFin
  apply(simp add: LOCALE_DEFS epdaH_interpretations epdaHS_interpretations0)
  apply(simp add: epdaH_vs_epdaHS_inst_ATS_Branching_Versus_Linear1_axioms)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_triv_with_get_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL. cL \<in> epdaHS_configurations G \<longrightarrow> epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) (epdaHS_get_scheduler cL) = cL))"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHS_get_scheduler_def)
  done

lemma epdaHS_history_input_preserved: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d j = Some (pair e' c')
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> epdaHS_conf_history c' @ epdaHS_conf_scheduler c' = epdaHS_conf_history c @ epdaHS_conf_scheduler c"
  apply(induct "j-i" arbitrary: i e c)
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e c)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x = "Suc i"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2")
   apply(rename_tac x i e c)(*strict*)
   prefer 2
   apply(rule_tac
      m = "j"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac x i e c)(*strict*)
     apply(force)
    apply(rename_tac x i e c)(*strict*)
    apply(force)
   apply(rename_tac x i e c)(*strict*)
   apply(force)
  apply(rename_tac x i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(erule_tac
      x = "Some e2"
      in meta_allE)
  apply(erule_tac
      x = "c2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(subgoal_tac "epdaHS_conf_history c2 @ epdaHS_conf_scheduler c2 = epdaHS_conf_history c @ epdaHS_conf_scheduler c")
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(simp add: epdaHS_step_relation_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraDer_preserves_marking_condition: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>dl. epdaHS.derivation_initial G dl \<longrightarrow> epdaHS_marking_condition G dl \<longrightarrow> Ex (maximum_of_domain dl) \<longrightarrow> epdaH_marking_condition G (ATS_Branching_Versus_Linear1.Lin2BraDer epdaHvHS_Lin2BraConf dl)))"
  apply(clarsimp)
  apply(rename_tac G dl x)(*strict*)
  apply(simp add: epdaH_marking_condition_def epdaHS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(rule_tac
      x = "i"
      in exI)
  apply(simp add: epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def)
  apply(rule conjI)
   apply(rename_tac G dl x i e c)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G dl x i e c j e' c')(*strict*)
   apply(simp add: epdaHS_marking_configurations_def)
   apply(clarsimp)
   apply(case_tac "dl j")
    apply(rename_tac G dl x i e c j e' c')(*strict*)
    apply(force)
   apply(rename_tac G dl x i e c j e' c' a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G dl x i e c j e' c' a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl x i e c j e' b)(*strict*)
   apply(simp add: epdaHvHS_Lin2BraConf_def)
   apply(simp add: epdaH_string_state_def)
   apply(subgoal_tac "epdaHS_conf_history c @ epdaHS_conf_scheduler c = epdaHS_conf_history b @ epdaHS_conf_scheduler b")
    apply(rename_tac G dl x i e c j e' b)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state c = w @ epdaHS_string_state b")
     apply(rename_tac G dl x i e c j e' b)(*strict*)
     prefer 2
     apply(rule_tac
      d = "dl"
      and j = "j-i"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac G dl x i e c j e' b)(*strict*)
          apply(force)
         apply(rename_tac G dl x i e c j e' b)(*strict*)
         apply(force)
        apply(rename_tac G dl x i e c j e' b)(*strict*)
        apply (metis epdaHS.derivation_initial_belongs)
       apply(rename_tac G dl x i e c j e' b)(*strict*)
       apply (metis epdaHS.derivation_initial_is_derivation)
      apply(rename_tac G dl x i e c j e' b)(*strict*)
      apply(force)
     apply(rename_tac G dl x i e c j e' b)(*strict*)
     apply(force)
    apply(rename_tac G dl x i e c j e' b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G dl x i e c j e' b w)(*strict*)
    apply(simp add: epdaHS_string_state_def)
   apply(rename_tac G dl x i e c j e' b)(*strict*)
   apply(rule sym)
   apply(rule_tac
      d = "dl"
      and i = "i"
      and j = "j"
      in epdaHS_history_input_preserved)
       apply(rename_tac G dl x i e c j e' b)(*strict*)
       apply(force)+
      apply(rename_tac G dl x i e c j e' b)(*strict*)
      apply (metis epdaHS.derivation_initial_is_derivation)
     apply(rename_tac G dl x i e c j e' b)(*strict*)
     apply(force)
    apply(rename_tac G dl x i e c j e' b)(*strict*)
    apply(force)
   apply(rename_tac G dl x i e c j e' b)(*strict*)
   apply(force)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(simp add: epdaHS_marking_configurations_def epdaH_marking_configurations_def epdaHvHS_Lin2BraConf_def epdaHS_configurations_def epdaH_configurations_def)
  apply(force)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_on_empty_bra_sched_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> epdaHvHS_Bra2LinConf cB [] \<in> epdaHS_configurations G))"
  apply(rule epdaH_vs_epdaHS_inst_AX_Bra2LinFin_creates_proper_extension)
  done

lemma epdaH_vs_epdaHS_inst_set_constructed_sched_vs_set_constructed_schedUF_Fin: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL1. cL1 \<in> epdaHS_configurations G \<longrightarrow> epdaHS_set_unfixed_scheduler cL1 (epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL1) [])) = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL1) []))"
  apply(clarsimp)
  apply(rename_tac G cL1)(*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHS_set_unfixed_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL1. cL1 \<in> epdaHS_configurations G \<longrightarrow> (\<forall>e cL2. epdaH_step_relation G (epdaHvHS_Lin2BraConf cL1) e cL2 \<longrightarrow> (\<forall>s. s \<in> epda_effects G \<longrightarrow> epdaHvHS_Bra2LinConf cL2 s \<in> epdaHS_configurations G \<longrightarrow> epdaHS_set_unfixed_scheduler (epdaHvHS_Bra2LinConf cL2 []) (epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf cL2 s)) = epdaHvHS_Bra2LinConf cL2 s \<longrightarrow> epdaHS_set_unfixed_scheduler cL1 (epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL1) (epdaHvHS_Bra2LinStep (epdaHvHS_Lin2BraConf cL1) e cL2 @ s))) = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL1) (epdaHvHS_Bra2LinStep (epdaHvHS_Lin2BraConf cL1) e cL2 @ s)))))"
  apply(clarsimp)
  apply(rename_tac G cL1 e cL2 s)(*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHS_set_unfixed_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinDer_preserves_marking_condition: "
 \<forall>G. valid_epda G \<longrightarrow>
        (\<forall>db. ATS.derivation_initial epdaH_initial_configurations
               epdaH_step_relation G db \<longrightarrow>
              epdaH_marking_condition G db \<longrightarrow>
              (\<forall>n. maximum_of_domain db n \<longrightarrow>
                   epdaHS_marking_condition G
                    (ATS_Branching_Versus_Linear1.Bra2LinDer
                      epda_empty_scheduler_fragment (@) (@)
                      epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf
                      epdaHvHS_Bra2LinStep epdaHvHS_Bra2LinFin G db n)))"
  apply(clarsimp)
  apply(rename_tac G db n)(*strict*)
  apply(rename_tac G dl n)
  apply(rename_tac G dl n)(*strict*)
  apply(simp add: epdaHS_marking_condition_def epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G dl n i e c)(*strict*)
  apply(rule_tac
      x = "i"
      in exI)
  apply(rule_tac
      x = "e"
      in exI)
  apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
  apply(subgoal_tac "i\<le>n")
   apply(rename_tac G dl n i e c)(*strict*)
   prefer 2
   apply(rule epdaH.allPreMaxDomSome_prime)
     apply(rename_tac G dl n i e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac G dl n i e c)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c)(*strict*)
   apply(force)
  apply(rename_tac G dl n i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dl n = Some (pair e c)")
   apply(rename_tac G dl n i e c)(*strict*)
   prefer 2
   apply(rule epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac G dl n i e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac G dl n i e c)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c)(*strict*)
   apply(force)
  apply(rename_tac G dl n i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl n i e c ea ca)(*strict*)
  apply(simp add: epdaH_marking_configurations_def suffix_def epdaHS_marking_configurations_def)
  apply(clarsimp)
  apply(subgoal_tac "epdaHvHS_Bra2LinConf c (epdaH_vs_epdaHS.Bra2LinDer' G dl n i) \<in> epdaHS_configurations G")
   apply(rename_tac G dl n i e c ea ca)(*strict*)
   prefer 2
   apply(rule_tac n = "n" and m = "i" in epdaH_vs_epdaHS.Bra2LinDer_preserves_configurations_prime)
         apply(rename_tac G dl n i e c ea ca)(*strict*)
         apply(force)
        apply(rename_tac G dl n i e c ea ca)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
        apply(force)
       apply(rename_tac G dl n i e c ea ca)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac G dl n i e c ea ca)(*strict*)
        apply(force)
       apply(rename_tac G dl n i e c ea ca)(*strict*)
       apply(force)
      apply(rename_tac G dl n i e c ea ca)(*strict*)
      apply(force)
     apply(rename_tac G dl n i e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac G dl n i e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c ea ca)(*strict*)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
  apply(rename_tac G dl n i e c ea ca)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G dl n i e c ea ca)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(simp add: epdaHS_configurations_def)
   apply(clarsimp)
   apply(rule foldl_emptyX)
   apply(rename_tac G dl n i e c ea ca ia)(*strict*)
   apply(clarsimp)
   apply(case_tac n)
    apply(rename_tac G dl n i e c ea ca ia)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dl n i e c ea ca ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
   apply(subgoal_tac "length (nat_seq i nat) = nat + 1 - i")
    apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
   apply(rule_tac
      t = "nat_seq i nat ! ia"
      and s = "i+ia"
      in ssubst)
    apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
     apply(force)
    apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
    apply(force)
   apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. dl (i+ia) = Some (pair e1 c1) \<and> dl (Suc(i+ia)) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
    apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
    prefer 2
    apply(rule_tac
      m = "Suc nat"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
     apply(force)
    apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
    apply(force)
   apply(rename_tac G dl i e c ea ca ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
   apply(rule_tac
      t = "nat_seq i nat ! ia"
      and s = "i+ia"
      in ssubst)
    apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "epdaH_conf_history c = epdaH_conf_history c1")
    apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
    apply(simp add: epdaHvHS_Bra2LinStep_def)
    apply(simp add: option_to_list_def)
    apply(case_tac "edge_event e2")
     apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
     apply(clarsimp)
    apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2 a)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x = "Suc (i+ia)"
      in allE)
    apply(clarsimp)
    apply(simp add: epdaH_string_state_def)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2 a w)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
   apply(simp add: epdaH_string_state_def)
   apply(case_tac ia)
    apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dl i e c ea ca ia nat e1 e2 c1 c2 nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl i e c ea ca nat e1 e2 c1 c2 nata)(*strict*)
   apply(erule_tac
      x = "Suc (i+nata)"
      in allE)
   apply(clarsimp)
  apply(rename_tac G dl n i e c ea ca)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraConf_Bra2LinConf_idemp: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>s. s \<in> epda_effects G \<longrightarrow> epdaHvHS_Bra2LinConf cB s \<in> epdaHS_configurations G \<longrightarrow> cB = epdaHvHS_Lin2BraConf (epdaHvHS_Bra2LinConf cB s))))"
  apply(clarsimp)
  apply(rename_tac G cB s)(*strict*)
  apply(simp add: epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinConf_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF_prime_prime: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1L. c1L \<in> epdaHS_configurations G \<longrightarrow> (\<forall>c3L. c3L \<in> epdaHS_configurations G \<longrightarrow> (\<exists>cB. cB \<in> epdaH_configurations G) \<longrightarrow> (\<forall>e c2L. epdaHS_step_relation G c1L e c2L \<longrightarrow> (\<forall>sE3 sE2 sE1. epdaHS_set_unfixed_scheduler c2L (sE3 @ epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf c3L) sE2)) = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf c2L) (sE1 @ sE2) \<longrightarrow> epdaHS_set_unfixed_scheduler c1L (the (right_quotient_word (epdaHS_get_unfixed_scheduler c1L) (epdaHS_get_unfixed_scheduler c2L)) @ sE3 @ epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf c3L) sE2)) = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf c1L) (epdaHvHS_Bra2LinStep (epdaHvHS_Lin2BraConf c1L) e (epdaHvHS_Lin2BraConf c2L) @ sE1 @ sE2))))))"
  apply(clarsimp)
  apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_get_unfixed_scheduler_def)
  apply(case_tac "c1L")
  apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c3L cB e c2L sE3 sE2 sE1 epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka)(*strict*)
  apply(case_tac "c2L")
  apply(rename_tac G c3L cB e c2L sE3 sE2 sE1 epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka epdaHS_conf_stateaa epdaHS_conf_historyaa epdaHS_conf_scheduleraa epdaHS_conf_stackaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c3L cB e epdaHS_conf_state epdaHS_conf_history epdaHS_conf_scheduler epdaHS_conf_stack epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka)(*strict*)
  apply(simp add: epdaHS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G c3L cB e epdaHS_conf_history epdaHS_conf_schedulera w)(*strict*)
  apply (metis right_quotient_word_removes_right_addition option.sel)
  done

lemma epdaH_vs_epdaHS_inst_AX_lin_unfixed_scheduler_right_quotient_drop_proper: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL. cL \<in> epdaHS_configurations G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>sE. sE \<in> epda_effects G \<longrightarrow> epdaHvHS_Bra2LinConf cB sE \<in> epdaHS_configurations G \<longrightarrow> epdaHS_set_unfixed_scheduler (epdaHvHS_Bra2LinConf cB sE) (the (right_quotient_word (epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf cB sE)) (epdaHS_get_unfixed_scheduler (epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) []))) @ epdaHS_get_unfixed_scheduler cL) = epdaHvHS_Bra2LinConf cB (sE @ epdaHS_get_scheduler cL)))))"
  apply(clarsimp)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_get_unfixed_scheduler_def epdaHS_get_scheduler_def)
  apply (metis right_quotient_word_neutral option.sel)
  done

lemma epdaH_vs_epdaHS_inst_AX_Lin2BraConf_ignores_set_unfixed_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cB. cB \<in> epdaH_configurations G \<longrightarrow> (\<forall>s. s \<in> epda_effects G \<longrightarrow> (\<forall>sUF. cB = epdaHvHS_Lin2BraConf (epdaHS_set_unfixed_scheduler (epdaHvHS_Bra2LinConf cB s) sUF)))))"
  apply(clarsimp)
  apply(rename_tac G cB s sUF)(*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_def epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_get_unfixed_scheduler_def epdaHS_get_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_translate_proper_idemp_doulbe_transfer_on_head: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>s. s \<in> epda_effects G \<longrightarrow> (\<forall>cB2. epdaHvHS_Bra2LinConf cB2 s \<in> epdaHS_configurations G \<longrightarrow> (\<forall>cL1. cL1 \<in> epdaHS_configurations G \<longrightarrow> (\<forall>e. epdaHS_step_relation G cL1 e (epdaHvHS_Bra2LinConf cB2 s) \<longrightarrow> cL1 = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL1) (epdaHvHS_Bra2LinStep (epdaHvHS_Lin2BraConf cL1) e cB2 @ s))))))"
  apply(clarsimp)
  apply(rename_tac G s cB2 cL1 e)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL. cL \<in> epdaHS_configurations G \<longrightarrow> cL = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) (epdaHS_get_scheduler cL)))"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler_prime: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL. cL \<in> epdaHS_configurations G \<longrightarrow> (\<forall>sL. sL \<in> epda_effects G \<longrightarrow> cL = epdaHvHS_Bra2LinConf (epdaHvHS_Lin2BraConf cL) sL \<longrightarrow> sL = epdaHS_get_scheduler cL)))"
  apply(clarsimp)
  apply(rename_tac G cL sL)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  apply(case_tac cL)
  apply(rename_tac G cL sL epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_vs_epdaHS_inst_AX_proper_removal_of_scheduler_parts: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>cL1. cL1 \<in> epdaHS_configurations G \<longrightarrow> (\<forall>e cL2. epdaHS_step_relation G cL1 e cL2 \<longrightarrow> epdaHvHS_Bra2LinStep (epdaHvHS_Lin2BraConf cL1) e (epdaHvHS_Lin2BraConf cL2) @ epdaHS_get_scheduler cL2 = epdaHS_get_scheduler cL1)))"
  apply(clarsimp)
  apply(rename_tac G cL1 e cL2)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_combine_consumed_and_remaining_scheduler: "
\<forall>G. valid_epda G \<longrightarrow>
        (\<forall>s. s \<in> epda_effects G \<longrightarrow>
             (\<forall>cL1. cL1 \<in> epdaHS_configurations G \<longrightarrow>
                    (\<forall>e cB2.
                        epdaHS_step_relation G cL1 e
                         (epdaHvHS_Bra2LinConf cB2 s) \<longrightarrow>
                        epdaHvHS_Bra2LinStep (epdaHvHS_Lin2BraConf cL1) e
                         cB2 @
                        s =
                        epdaHS_get_scheduler cL1)))"
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  done

lemma epdaH_vs_epdaHS_inst_hlp_AX_bra2lin_preserves_marked_effect: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e ca)
  \<Longrightarrow> d i = Some (pair ea cb)
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> epdaH_conf_history cb = epdaH_vs_epdaHS.Bra2LinDer' G d i 0"
  apply(induct i arbitrary: ea cb)
   apply(rename_tac ea cb)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
  apply(rename_tac i ea cb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac i ea cb)(*strict*)
   prefer 2
   apply(rule_tac
      m = "n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i ea cb)(*strict*)
     apply (metis epdaH.derivation_initial_is_derivation)
    apply(rename_tac i ea cb)(*strict*)
    apply(force)
   apply(rename_tac i ea cb)(*strict*)
   apply(force)
  apply(rename_tac i ea cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_vs_epdaHS.Bra2LinDer' G d (Suc i) 0 = epdaH_vs_epdaHS.Bra2LinDer' G d i 0 @ epdaH_vs_epdaHS.Bra2LinDer' G d (Suc i) i")
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "epdaH_conf_history cb = epdaH_conf_history c1 @ epdaH_vs_epdaHS.Bra2LinDer' G d (Suc i) i")
    apply(rename_tac i cb e1 e2 c1)(*strict*)
    apply(clarsimp)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(rule_tac
      t = "nat_seq i i"
      and s = "[i]"
      in ssubst)
    apply(rename_tac i cb e1 e2 c1)(*strict*)
    apply (metis natUptTo_n_n)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHvHS_Bra2LinStep_def epdaH_step_relation_def)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(rule_tac
      t = "Suc i"
      and s = "i + (Suc 0)"
      in ssubst)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(rule epdaH_vs_epdaHS.Bra2LinDer_prime_split)
      apply(rename_tac i cb e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac i cb e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac i cb e1 e2 c1)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply (metis epdaH.derivation_initial_belongs)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(force)
  done

lemma epdaH_vs_epdaHS_inst_hlp_AX_bra2lin_preserves_unmarked_effect: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e ca)
  \<Longrightarrow> d i = Some (pair ea cb)
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> epdaH_conf_history cb @ epdaH_vs_epdaHS.Bra2LinDer' G d n i =
  epdaH_vs_epdaHS.Bra2LinDer' G d n 0"
  apply(induct i arbitrary: ea cb)
   apply(rename_tac ea cb)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac i ea cb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac i ea cb)(*strict*)
   prefer 2
   apply(rule_tac
      m = "n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i ea cb)(*strict*)
     apply (metis epdaH.derivation_initial_is_derivation)
    apply(rename_tac i ea cb)(*strict*)
    apply(force)
   apply(rename_tac i ea cb)(*strict*)
   apply(force)
  apply(rename_tac i ea cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_vs_epdaHS.Bra2LinDer' G d n i = epdaH_vs_epdaHS.Bra2LinDer' G d (Suc i) i @ epdaH_vs_epdaHS.Bra2LinDer' G d n (Suc i)")
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "epdaH_conf_history cb = epdaH_conf_history c1 @ epdaH_vs_epdaHS.Bra2LinDer' G d (Suc i) i")
    apply(rename_tac i cb e1 e2 c1)(*strict*)
    apply(clarsimp)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(rule_tac
      t = "nat_seq i i"
      and s = "[i]"
      in ssubst)
    apply(rename_tac i cb e1 e2 c1)(*strict*)
    apply (metis natUptTo_n_n)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHvHS_Bra2LinStep_def epdaH_step_relation_def)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(rule_tac
      t = "n"
      and s = "Suc i + (n-Suc i)"
      in ssubst)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(rule epdaH_vs_epdaHS.Bra2LinDer_prime_split)
      apply(rename_tac i cb e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac i cb e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac i cb e1 e2 c1)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation)
   apply(rename_tac i cb e1 e2 c1)(*strict*)
   apply (metis epdaH.derivation_initial_belongs)
  apply(rename_tac i cb e1 e2 c1)(*strict*)
  apply(force)
  done

lemma epdaH_vs_epdaHS_inst_AX_lin2bra_preserves_unmarked_effect: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>dl. epdaHS.derivation_initial G dl \<longrightarrow> (\<forall>x. x \<in> epdaHS_unmarked_effect G dl \<longrightarrow> Ex (maximum_of_domain dl) \<longrightarrow> x \<in> epdaH_unmarked_effect G (ATS_Branching_Versus_Linear1.Lin2BraDer epdaHvHS_Lin2BraConf dl))))"
  apply(clarsimp)
  apply(rename_tac G dl x xa)(*strict*)
  apply(simp add: epdaHS_unmarked_effect_def epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G dl x xa c c' i e)(*strict*)
  apply(rule_tac
      x = "i"
      in exI)
  apply(simp add: epdaH_vs_epdaHS.Lin2BraDer_def)
  apply(rule_tac
      x = "e"
      in exI)
  apply(rule_tac
      x = "\<lparr>epdaH_conf_state = epdaHS_conf_state c', epdaH_conf_history = epdaHS_conf_history c', epdaH_conf_stack = epdaHS_conf_stack c'\<rparr>"
      in exI)
  apply(rename_tac G dl x xa c c' i e)(*strict*)
  apply(rule conjI)
   apply(rename_tac G dl x xa c c' i e)(*strict*)
   apply(simp add: derivation_map_def epdaHvHS_Lin2BraConf_def)
  apply(rename_tac G dl x xa c c' i e)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "epdaHS_conf_history c' @ epdaHS_conf_scheduler c' = epdaHS_conf_history c @ epdaHS_conf_scheduler c")
   apply(rename_tac G dl x xa c c' i e)(*strict*)
   apply(subgoal_tac "epdaHS_conf_history c = []")
    apply(rename_tac G dl x xa c c' i e)(*strict*)
    apply(clarsimp)
    apply (metis append_same_eq)
   apply(rename_tac G dl x xa c c' i e)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def)
  apply(rename_tac G dl x xa c c' i e)(*strict*)
  apply (metis epdaHS.derivation_initial_is_derivation epdaHS_history_input_preserved less_eq_nat.simps(1))
  done

lemma map_eq: "
  (\<And>x. x \<in> set w \<Longrightarrow> f x = g x)
  \<Longrightarrow> map f w = map g w"
  apply(force)
  done

lemma epdaH_vs_epdaHS_inst_AX_lin2bra_preserves_marked_effect: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>dl. epdaHS.derivation_initial G dl \<longrightarrow> epdaHS_marking_condition G dl \<longrightarrow> (\<forall>x. x \<in> epdaHS_marked_effect G dl \<longrightarrow> Ex (maximum_of_domain dl) \<longrightarrow> x \<in> epdaH_marked_effect G (ATS_Branching_Versus_Linear1.Lin2BraDer epdaHvHS_Lin2BraConf dl))))"
  apply(clarsimp)
  apply(rename_tac G dl x xa)(*strict*)
  apply(simp add: epdaH_marked_effect_def epdaHS_marked_effect_def epdaHS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(rule_tac
      x = "i"
      in exI)
  apply(simp add: epdaH_vs_epdaHS.Lin2BraDer_def)
  apply(rule_tac
      x = "e"
      in exI)
  apply(rule_tac
      x = "\<lparr>epdaH_conf_state = epdaHS_conf_state ca, epdaH_conf_history = epdaHS_conf_history ca, epdaH_conf_stack = epdaHS_conf_stack ca\<rparr>"
      in exI)
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G dl xa i c e ca)(*strict*)
   apply(simp add: derivation_map_def epdaHvHS_Lin2BraConf_def)
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "epdaHS_conf_history ca @ epdaHS_conf_scheduler ca = epdaHS_conf_history c @ epdaHS_conf_scheduler c")
   apply(rename_tac G dl xa i c e ca)(*strict*)
   prefer 2
   apply (metis epdaHS.derivation_initial_is_derivation epdaHS_history_input_preserved less_eq_nat.simps(1))
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(subgoal_tac "epdaHS_conf_history c = []")
   apply(rename_tac G dl xa i c e ca)(*strict*)
   prefer 2
   apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def)
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G dl xa i c e ca)(*strict*)
   apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def epdaHS_configurations_def epdaHS_marking_configurations_def)
   apply(clarsimp)
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G dl xa i c e ca)(*strict*)
   apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def epdaHS_configurations_def epdaHS_marking_configurations_def)
  apply(rename_tac G dl xa i c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl xa i c e ca j e' c')(*strict*)
  apply(simp add: epdaH_string_state_def)
  apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def epdaHS_configurations_def epdaHS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i c e j e' c' q s)(*strict*)
  apply(subgoal_tac "\<exists>e c. dl j = Some (pair e c)")
   apply(rename_tac G dl xa i c e j e' c' q s)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def)
   apply(case_tac "dl j")
    apply(rename_tac G dl xa i c e j e' c' q s)(*strict*)
    apply(force)
   apply(rename_tac G dl xa i c e j e' c' q s a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G dl xa i c e j e' c' q s a option b)(*strict*)
   apply(force)
  apply(rename_tac G dl xa i c e j e' c' q s)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
  apply(subgoal_tac "epdaHS_conf_history \<lparr>epdaHS_conf_state = q, epdaHS_conf_history = epdaHS_conf_scheduler c, epdaHS_conf_scheduler = [], epdaHS_conf_stack = s\<rparr> @ epdaHS_conf_scheduler \<lparr>epdaHS_conf_state = q, epdaHS_conf_history = epdaHS_conf_scheduler c, epdaHS_conf_scheduler = [], epdaHS_conf_stack = s\<rparr> = epdaHS_conf_history ca @ epdaHS_conf_scheduler ca")
   apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule epdaHS_history_input_preserved)
       apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
       apply(force)
      apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
      apply (rule epdaHS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
     apply(force)
    apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
    apply(force)
   apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
   apply(force)
  apply(rename_tac G dl xa i c e j e' c' q s ea ca)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
  apply(simp add: epdaHvHS_Lin2BraConf_def)
  apply(subgoal_tac "\<exists>w. epdaHS_string_state \<lparr>epdaHS_conf_state = q, epdaHS_conf_history = epdaHS_conf_history ca @ epdaHS_conf_scheduler ca, epdaHS_conf_scheduler = [], epdaHS_conf_stack = s\<rparr> = w @ epdaHS_string_state ca")
   apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
   prefer 2
   apply(rule_tac
      d = "dl"
      and j = "j-i"
      in epdaHS.derivation_monotonically_dec)
        apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
        apply(force)
       apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
       apply(force)
      apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
      apply (metis epdaHS.derivation_initial_belongs)
     apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
     apply (metis epdaHS.derivation_initial_is_derivation)
    apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
    apply(force)
   apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
   apply(force)
  apply(rename_tac G dl xa i c e j e' q s ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl xa i c e j e' q s ca w)(*strict*)
  apply(simp add: epdaHS_string_state_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_bra2lin_preserves_unmarked_effect: "
  (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>db. ATS.derivation_initial epdaH_initial_configurations
                epdaH_step_relation G db \<longrightarrow>
               (\<forall>x. x \<in> epdaH_unmarked_effect G db \<longrightarrow>
                    (\<forall>n. maximum_of_domain db n \<longrightarrow>
                         x \<in> epdaHS_unmarked_effect G
                               (ATS_Branching_Versus_Linear1.Bra2LinDer
                                 epda_empty_scheduler_fragment (@) (@)
                                 epdaH_get_fixed_scheduler
                                 epdaHvHS_Bra2LinConf epdaHvHS_Bra2LinStep
                                 epdaHvHS_Bra2LinFin G db n)))))"
  apply(clarsimp)
  apply(rename_tac G db x n)(*strict*)
  apply(simp add: epdaHS_unmarked_effect_def epdaH_unmarked_effect_def)
  apply(subgoal_tac "\<exists>e c. db n = Some (pair e c)")
   apply(rename_tac G db x n)(*strict*)
   prefer 2
   apply(rule epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac G db x n)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac G db x n)(*strict*)
    apply(force)
   apply(rename_tac G db x n)(*strict*)
   apply(force)
  apply(rename_tac G db x n)(*strict*)
  apply(subgoal_tac "\<exists>c. db 0 = Some (pair None c)")
   apply(rename_tac G db x n)(*strict*)
   prefer 2
   apply (metis epdaH.derivation_initial_is_derivation epdaH.some_position_has_details_at_0)
  apply(rename_tac G db x n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(simp add: epdaHS_unmarked_effect_def epdaH_vs_epdaHS.Bra2LinDer_def)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
  apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = epdaH_conf_state cb, epdaHS_conf_history = epdaH_conf_history cb, epdaHS_conf_scheduler = X, epdaHS_conf_stack = epdaH_conf_stack cb\<rparr>" for X
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply(rule_tac
      x = "i"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaHvHS_Bra2LinConf_def epdaHvHS_Lin2BraConf_def epdaHvHS_Bra2LinStep_def epdaHS_step_relation_def epdaHS_get_scheduler_def)
   apply(subgoal_tac "i\<le>n")
    apply(rename_tac G db n i e c ea ca cb)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply (metis epdaH.allPreMaxDomSome_prime epdaH.derivation_initial_is_derivation not_Some_eq)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(rule epdaH_vs_epdaHS_inst_hlp_AX_bra2lin_preserves_unmarked_effect)
        apply(rename_tac G db n i e c ea ca cb)(*strict*)
        apply(force)+
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply (metis epdaH.allPreMaxDomSome_prime epdaH.derivation_initial_is_derivation not_Some_eq)
  done

lemma epdaH_vs_epdaHS_inst_AX_bra2lin_preserves_marked_effect: "
  (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>db. ATS.derivation_initial epdaH_initial_configurations
                epdaH_step_relation G db \<longrightarrow>
               epdaH_marking_condition G db \<longrightarrow>
               (\<forall>x. x \<in> epdaH_marked_effect G db \<longrightarrow>
                    (\<forall>n. maximum_of_domain db n \<longrightarrow>
                         (\<exists>i\<le>n. epdaH_marking_condition G
                                  (derivation_take db i) \<and>
                                 x \<in> epdaHS_marked_effect G
(ATS_Branching_Versus_Linear1.Bra2LinDer epda_empty_scheduler_fragment (@)
  (@) epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf epdaHvHS_Bra2LinStep
  epdaHvHS_Bra2LinFin G (derivation_take db i) i))))))"
  apply(clarsimp)
  apply(rename_tac G db x n)(*strict*)
  apply(simp add: epdaHS_marked_effect_def epdaH_marked_effect_def)
  apply(subgoal_tac "\<exists>e c. db n = Some (pair e c)")
   apply(rename_tac G db x n)(*strict*)
   prefer 2
   apply(rule epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac G db x n)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac G db x n)(*strict*)
    apply(force)
   apply(rename_tac G db x n)(*strict*)
   apply(force)
  apply(rename_tac G db x n)(*strict*)
  apply(subgoal_tac "\<exists>c. db 0 = Some (pair None c)")
   apply(rename_tac G db x n)(*strict*)
   prefer 2
   apply (metis epdaH.derivation_initial_is_derivation epdaH.some_position_has_details_at_0)
  apply(rename_tac G db x n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(simp add: epdaHS_unmarked_effect_def epdaH_vs_epdaHS.Bra2LinDer_def)
  apply(rule_tac
      x = "i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply (metis epdaH.allPreMaxDomSome_prime epdaH.derivation_initial_is_derivation not_Some_eq)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(rule conjI)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply(simp add: epdaH_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac G db n i e c ea ca cb ia eb cc)(*strict*)
   apply(rule_tac
      x = "i"
      in exI)
   apply(rule_tac
      x = "ea"
      in exI)
   apply(rule_tac
      x = "cb"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G db n i e c ea ca cb ia eb cc)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G db n i e c ea ca cb ia eb cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac G db n i e c ea ca cb ia eb cc j e' c')(*strict*)
   apply(erule_tac
      x = "j"
      and P = "\<lambda>j. \<forall>e' c'. i < j \<and> db j = Some (pair e' c') \<longrightarrow> epdaH_string_state cb = epdaH_string_state c'"
      in allE)
   apply(rename_tac G db n i e c ea ca cb ia eb cc j e' c')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x = "e'"
      in allE)
   apply(erule_tac
      x = "c'"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = epdaH_conf_state c, epdaHS_conf_history = epdaH_conf_history c, epdaHS_conf_scheduler = X, epdaHS_conf_stack = epdaH_conf_stack c\<rparr>" for X
      in exI)
  apply(rule conjI)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply(simp add: derivation_take_def epdaHvHS_Bra2LinConf_def)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(clarsimp)
  apply(fold derivation_take_def)
  apply(rule_tac
      t = "ATS_Branching_Versus_Linear1.Bra2LinDer' epda_empty_scheduler_fragment (@) epdaHvHS_Bra2LinStep G (derivation_take db i) i 0"
      and s = "ATS_Branching_Versus_Linear1.Bra2LinDer' epda_empty_scheduler_fragment (@) epdaHvHS_Bra2LinStep G db i 0"
      in ssubst)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(rule_tac
      t = "(map (\<lambda>n. case derivation_take db i n of Some (pair e1 c1) \<Rightarrow> case derivation_take db i (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> epdaHvHS_Bra2LinStep c1 e2 c2) (case i of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq 0 m'))"
      and s = "(map (\<lambda>n. case db n of Some (pair e1 c1) \<Rightarrow> case db (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> epdaHvHS_Bra2LinStep c1 e2 c2) (case i of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq 0 m'))"
      in ssubst)
    apply(rename_tac G db n i e c ea ca cb)(*strict*)
    apply(rule map_eq)
    apply(rename_tac G db n i e c ea ca cb x)(*strict*)
    apply(case_tac i)
     apply(rename_tac G db n i e c ea ca cb x)(*strict*)
     apply(clarsimp)
    apply(rename_tac G db n i e c ea ca cb x nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
    apply(subgoal_tac "0\<le>x \<and> x\<le>nat")
     apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t = "db x"
      and s = "derivation_take db (Suc nat) x"
      in ssubst)
      apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
      prefer 2
      apply(rule_tac
      t = "db (Suc x)"
      and s = "derivation_take db (Suc nat) (Suc x)"
      in ssubst)
       apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac G db n e c ea ca cb x nat)(*strict*)
    apply (metis le0 nat_seq_in_interval)
   apply(rename_tac G db n i e c ea ca cb)(*strict*)
   apply(force)
  apply(rename_tac G db n i e c ea ca cb)(*strict*)
  apply(rule epdaH_vs_epdaHS_inst_hlp_AX_bra2lin_preserves_marked_effect)
        apply(rename_tac G db n i e c ea ca cb)(*strict*)
        apply(force)+
  done

lemma epdaH_vs_epdaHS_inst_Lin2BraConf_enforces_compatible_history_fragment_SB: "
  (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>cL. cL \<in> ATS.get_accessible_configurations
                      epdaHS_initial_configurations epdaHS_step_relation G \<longrightarrow>
               (\<forall>e1 cL1.
                   epdaHS_step_relation G cL e1 cL1 \<longrightarrow>
                   (\<forall>e2 cL2.
                       epdaHS_step_relation G cL e2 cL2 \<longrightarrow>
                       ATS_determHIST_SB.compatible_history_fragment_SB
                        epda_effects (@) (@) epdaH_conf_history
                        epda_fixed_scheduler_extendable
                        epdaH_get_fixed_scheduler G (epdaHvHS_Lin2BraConf cL)
                        (epdaHvHS_Lin2BraConf cL1)
                        (epdaHvHS_Lin2BraConf cL2)))))"
  apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(simp add: epdaH.compatible_history_fragment_SB_def epdaHS_step_relation_def epdaHvHS_Lin2BraConf_def Let_def)
  apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
   apply(simp add: valid_epda_def valid_epda_step_label_def epda_effects_def option_to_list_def option_to_set_def)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
   apply(simp add: valid_epda_def valid_epda_step_label_def epda_effects_def option_to_list_def option_to_set_def)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e1)) (option_to_list (edge_event e2)) \<or> prefix (option_to_list (edge_event e2)) (option_to_list (edge_event e1))")
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
  apply(erule disjE)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
   apply(rule disjI1)
   apply(simp add: epdaH.history_fragment_prefixes_def prefix_def epda_effects_def)
   apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(rule_tac
      t = "option_to_list (edge_event e2)"
      and s = "option_to_list (edge_event e1) @ c"
      in ssubst)
    apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(rule_tac
      x = "hf''@c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
    prefer 2
    apply(thin_tac "option_to_list (edge_event e1) @ c = option_to_list (edge_event e2)")
    apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(simp add: valid_epda_def valid_epda_step_label_def epda_effects_def option_to_list_def option_to_set_def)
   apply(rule_tac
      B = "set((case edge_event e2 of None \<Rightarrow> [] | Some A \<Rightarrow> [A]))"
      in subset_trans)
    apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(rule_tac
      t = "case edge_event e2 of None \<Rightarrow> [] | Some A \<Rightarrow> [A]"
      and s = "(case edge_event e1 of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ c"
      in ssubst)
    apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(simp (no_asm))
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa)(*strict*)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(simp add: epdaH.history_fragment_prefixes_def prefix_def epda_effects_def)
  apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
  apply(rule_tac
      t = "option_to_list (edge_event e1)"
      and s = "option_to_list (edge_event e2) @ c"
      in ssubst)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
  apply(rule_tac
      x = "hf''@c"
      in exI)
  apply(rule conjI)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   prefer 2
   apply(thin_tac "option_to_list (edge_event e2) @ c = option_to_list (edge_event e1)")
   apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
  apply(simp add: valid_epda_def valid_epda_step_label_def epda_effects_def option_to_list_def option_to_set_def)
  apply(rule_tac
      B = "set((case edge_event e1 of None \<Rightarrow> [] | Some A \<Rightarrow> [A]))"
      in subset_trans)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
  apply(rule_tac
      t = "case edge_event e1 of None \<Rightarrow> [] | Some A \<Rightarrow> [A]"
      and s = "(case edge_event e2 of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ c"
      in ssubst)
   apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2 w wa x c hf'')(*strict*)
  apply(simp (no_asm))
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinDer_allows_slim_step1: "
\<forall>G. valid_epda G \<longrightarrow>
        (\<forall>d. ATS.derivation_initial epdaH_initial_configurations
              epdaH_step_relation G d \<longrightarrow>
             (\<forall>c e1 c1.
                 epdaH_step_relation G c e1 c1 \<longrightarrow>
                 (\<forall>e2 c2.
                     epdaH_step_relation G c e2 c2 \<longrightarrow>
                     (\<forall>i. (\<exists>ei. d i = Some (pair ei c)) \<longrightarrow>
                          (\<forall>hf2. epdaH_conf_history c1 =
                                 epdaH_conf_history c @ hf2 \<longrightarrow>
                                 (\<forall>hf1. epdaH_conf_history c2 =
 epdaH_conf_history c @ hf2 @ hf1 \<longrightarrow>
 epdaHS.derivation_initial G
  (ATS_Branching_Versus_Linear1.Bra2LinDer epda_empty_scheduler_fragment (@)
    (@) epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf epdaHvHS_Bra2LinStep
    epdaHvHS_Bra2LinFin G (derivation_append d (der2 c e2 c2) i)
    (Suc i)) \<longrightarrow>
 hf1 \<in> epda_effects G \<longrightarrow>
 hf2 \<in> epda_effects G \<longrightarrow>
 Ex (epdaHS_step_relation G
      (the (get_configuration
             (ATS_Branching_Versus_Linear1.Bra2LinDer
               epda_empty_scheduler_fragment (@) (@)
               epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf
               epdaHvHS_Bra2LinStep epdaHvHS_Bra2LinFin G
               (derivation_append d (der2 c e2 c2) i) (Suc i) i)))
      e1)))))))"
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa)(*strict*)
  apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer'_def epdaHvHS_Bra2LinStep_def)
  apply(rule_tac
      t = "nat_seq i i"
      and s = "[i]"
      in ssubst)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer'_def epdaHvHS_Bra2LinStep_def)
   apply(case_tac e2)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac e1)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(case_tac c1)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac c2)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(case_tac c)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i ei hf1 w wa edge_src edge_event edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
   apply(simp add: epdaHS_step_relation_def option_to_list_def)
   apply(case_tac edge_event)
    apply(rename_tac G d i ei hf1 w wa edge_src edge_event edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(case_tac edge_eventa)
     apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
     prefer 2
     apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = edge_trga, epdaHS_conf_history = epdaH_conf_historyb, epdaHS_conf_scheduler = [], epdaHS_conf_stack = edge_pusha @ w\<rparr>"
      in exI)
    apply(simp add: epdaHS_step_relation_def option_to_list_def)
   apply(rename_tac G d i ei hf1 w wa edge_src edge_event edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i ei hf1 w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
   apply(case_tac edge_eventa)
    apply(rename_tac G d i ei hf1 w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
    apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = edge_trga, epdaHS_conf_history = epdaH_conf_historyb, epdaHS_conf_scheduler = [a], epdaHS_conf_stack = edge_pusha @ w\<rparr>"
      in exI)
    apply(simp add: epdaHS_step_relation_def option_to_list_def)
   apply(rename_tac G d i ei hf1 w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
   apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = edge_trga, epdaHS_conf_history = epdaH_conf_historyb@[a], epdaHS_conf_scheduler = [], epdaHS_conf_stack = edge_pusha @ w\<rparr>"
      in exI)
   apply(simp add: epdaHS_step_relation_def option_to_list_def)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 w wa)(*strict*)
  apply (metis natUptTo_n_n)
  done

lemma epdaH_history_fragment_prefixes_simp1: "
  a \<in> epda_events G
  \<Longrightarrow> epdaH.history_fragment_prefixes G [a] = {[],[a]}"
  apply(simp add: epdaH.history_fragment_prefixes_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x hf'')(*strict*)
   apply(case_tac x)
    apply(rename_tac x hf'')(*strict*)
    apply(clarsimp)
   apply(rename_tac x hf'' aa list)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: epda_effects_def)
  done

lemma epdaH_history_fragment_prefixes_simp2: "
  epdaH.history_fragment_prefixes G [] = {[]}"
  apply(simp add: epdaH.history_fragment_prefixes_def)
  apply(rule antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: epda_effects_def)
  done

lemma epdaH_vs_epdaHS_inst_AX_Bra2LinDer_allows_slim_step2: "
\<forall>G. valid_epda G \<longrightarrow>
        (\<forall>d. ATS.derivation_initial epdaH_initial_configurations
              epdaH_step_relation G d \<longrightarrow>
             (\<forall>c e1 c1.
                 epdaH_step_relation G c e1 c1 \<longrightarrow>
                 (\<forall>e2 c2.
                     epdaH_step_relation G c e2 c2 \<longrightarrow>
                     (\<forall>i. (\<exists>ei. d i = Some (pair ei c)) \<longrightarrow>
                          (\<forall>hf1. epdaH_conf_history c1 =
                                 epdaH_conf_history c @ hf1 \<longrightarrow>
                                 (\<forall>hf2. epdaH_conf_history c2 =
  epdaH_conf_history c @ hf2 \<longrightarrow>
  ATS_History.history_fragment_prefixes epda_effects (@) G hf1 =
  ATS_History.history_fragment_prefixes epda_effects (@) G hf2 \<longrightarrow>
  epdaHS.derivation_initial
   G (ATS_Branching_Versus_Linear1.Bra2LinDer epda_empty_scheduler_fragment
       (@) (@) epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf
       epdaHvHS_Bra2LinStep epdaHvHS_Bra2LinFin G
       (derivation_append d (der2 c e2 c2) i) (Suc i)) \<longrightarrow>
  hf1 \<in> epda_effects G \<longrightarrow>
  hf2 \<in> epda_effects G \<longrightarrow>
  Ex (epdaHS_step_relation G
       (the (get_configuration
              (ATS_Branching_Versus_Linear1.Bra2LinDer
                epda_empty_scheduler_fragment (@) (@)
                epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf
                epdaHvHS_Bra2LinStep epdaHvHS_Bra2LinFin G
                (derivation_append d (der2 c e2 c2) i) (Suc i) i)))
       e1)))))))"
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 e2 c2 i ei w wa)(*strict*)
  apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer'_def epdaHvHS_Bra2LinStep_def)
  apply(rule_tac
      t = "nat_seq i i"
      and s = "[i]"
      in ssubst)
   apply(rename_tac G d c e1 c1 e2 c2 i ei w wa)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer'_def epdaHvHS_Bra2LinStep_def)
   apply(case_tac e2)
   apply(rename_tac G d c e1 c1 e2 c2 i ei w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac e1)
   apply(rename_tac G d c e1 c1 e2 c2 i ei w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(case_tac c1)
   apply(rename_tac G d c e1 c1 e2 c2 i ei w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac c2)
   apply(rename_tac G d c e1 c1 e2 c2 i ei w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(case_tac c)
   apply(rename_tac G d c e1 c1 e2 c2 i ei w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i ei w wa edge_src edge_event edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
   apply(simp add: epdaHS_step_relation_def option_to_list_def)
   apply(case_tac edge_event)
    apply(rename_tac G d i ei w wa edge_src edge_event edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(case_tac edge_eventa)
     apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
     prefer 2
     apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
     apply(subgoal_tac "a \<in> epda_events G")
      apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
      apply(simp add: epdaH_history_fragment_prefixes_simp2 epdaH_history_fragment_prefixes_simp1)
     apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
     apply(simp add: valid_epda_def epda_effects_def)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb)(*strict*)
    apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = edge_trga, epdaHS_conf_history = epdaH_conf_historyb, epdaHS_conf_scheduler = [], epdaHS_conf_stack = edge_pusha @ w\<rparr>"
      in exI)
    apply(simp add: epdaHS_step_relation_def option_to_list_def)
   apply(rename_tac G d i ei w wa edge_src edge_event edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
   apply(case_tac edge_eventa)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
    apply(subgoal_tac "a \<in> epda_events G")
     apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
     apply(simp add: epdaH_history_fragment_prefixes_simp2 epdaH_history_fragment_prefixes_simp1)
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a)(*strict*)
    apply(simp add: valid_epda_def epda_effects_def)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
   apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = edge_trga, epdaHS_conf_history = epdaH_conf_historyb@[a], epdaHS_conf_scheduler = [], epdaHS_conf_stack = edge_pusha @ w\<rparr>"
      in exI)
   apply(simp add: epdaHS_step_relation_def option_to_list_def)
   apply(subgoal_tac "a \<in> epda_events G")
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
    prefer 2
    apply(simp add: valid_epda_def epda_effects_def)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
   apply(subgoal_tac "aa \<in> epda_events G")
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
    prefer 2
    apply(simp add: valid_epda_def epda_effects_def)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
   apply(simp add: epdaH_history_fragment_prefixes_simp2 epdaH_history_fragment_prefixes_simp1)
   apply(case_tac "a=aa")
    apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G d i ei w wa edge_src edge_pop edge_push edge_trg edge_popa edge_pusha edge_trga epdaH_conf_historyb a aa)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac G d c e1 c1 e2 c2 i ei w wa)(*strict*)
  apply (metis natUptTo_n_n)
  done

lemma epdaH_vs_epdaHS_inst_ATS_Branching_Versus_Linear2_axioms: "
  ATS_Branching_Versus_Linear2_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epdaHS_step_relation epdaHS_marking_condition
     epdaHS_marked_effect epdaHS_unmarked_effect epda_fixed_scheduler_extendable
     epda_effects epda_empty_scheduler_fragment (@) right_quotient_word (@)
     epda_unfixed_scheduler_extendable epda_effects epda_empty_scheduler
     epdaHS_get_scheduler (@) epdaHS_get_unfixed_scheduler
     epdaHS_set_unfixed_scheduler epdaHS_get_fixed_scheduler epda_effects
     epda_empty_history_fragment (@) (@) epdaH_configurations
     epdaH_initial_configurations epdaH_step_relation epdaH_marking_condition
     epdaH_marked_effect epdaH_unmarked_effect epda_empty_fixed_scheduler
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler epdaH_conf_history
     epdaHvHS_Lin2BraConf epdaHvHS_Bra2LinConf epdaHvHS_Bra2LinStep
     epdaHvHS_Bra2LinFin"
  apply(simp add: ATS_Branching_Versus_Linear2_axioms_def)
  apply(simp add: epdaH_vs_epdaHS_inst_Lin2BraConf_enforces_compatible_history_fragment_SB epdaH_vs_epdaHS_inst_AX_Bra2LinDer_allows_slim_step1 epdaH_vs_epdaHS_inst_AX_Bra2LinDer_allows_slim_step2 )
  apply(simp add: epdaH_vs_epdaHS_inst_AX_Bra2LinConf_triv_with_get_scheduler epdaH_vs_epdaHS_inst_AX_Lin2BraDer_preserves_marking_condition epdaH_vs_epdaHS_inst_AX_Bra2LinConf_on_empty_bra_sched_closed epdaH_vs_epdaHS_inst_set_constructed_sched_vs_set_constructed_schedUF_Fin epdaH_vs_epdaHS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF epdaH_vs_epdaHS_inst_AX_Bra2LinDer_preserves_marking_condition )
  apply(simp add: epdaH_vs_epdaHS_inst_AX_Lin2BraConf_ignores_set_unfixed_scheduler epdaH_vs_epdaHS_inst_AX_lin_unfixed_scheduler_right_quotient_drop_proper epdaH_vs_epdaHS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF_prime_prime epdaH_vs_epdaHS_inst_AX_Lin2BraConf_Bra2LinConf_idemp )
  apply(simp add: epdaH_vs_epdaHS_inst_AX_translate_proper_idemp_doulbe_transfer_on_head epdaH_vs_epdaHS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler epdaH_vs_epdaHS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler_prime epdaH_vs_epdaHS_inst_AX_proper_removal_of_scheduler_parts epdaH_vs_epdaHS_inst_AX_combine_consumed_and_remaining_scheduler )
  apply(simp add: epdaH_vs_epdaHS_inst_AX_lin2bra_preserves_marked_effect epdaH_vs_epdaHS_inst_AX_lin2bra_preserves_unmarked_effect epdaH_vs_epdaHS_inst_AX_bra2lin_preserves_unmarked_effect epdaH_vs_epdaHS_inst_AX_bra2lin_preserves_marked_effect )
  done

interpretation "epdaH_vs_epdaHS" : ATS_Branching_Versus_Linear2
  (* TSstructure *)
  "valid_epda"
  (* lin_configurations *)
  "epdaHS_configurations"
  (* lin_initial_configurations *)
  "epdaHS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* lin_step_relation *)
  "epdaHS_step_relation"
  (* effects *)
  "epda_effects"
  (* lin_marking_condition *)
  "epdaHS_marking_condition"
  (* lin_marked_effect *)
  "epdaHS_marked_effect"
  (* lin_unmarked_effect *)
  "epdaHS_unmarked_effect"
  (* lin_fixed_schedulers *)
  epda_fixed_schedulers
  (* lin_empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* lin_fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* lin_scheduler_fragments *)
  "epda_effects"
  (* lin_empty_scheduler_fragment *)
  epda_empty_scheduler_fragment
  (* lin_join_scheduler_fragments *)
  "append"
  (* lin_unfixed_schedulers *)
  "epda_effects"
  (* lin_empty_unfixed_scheduler *)
  epda_empty_unfixed_scheduler
  (* lin_unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* lin_extend_unfixed_scheduler *)
  "append"
  (* lin_unfixed_scheduler_extendable *)
  epda_unfixed_scheduler_extendable
  (* lin_schedulers *)
  "epda_effects"
  (* lin_initial_schedulers *)
  "epda_effects"
  (* lin_empty_scheduler *)
  epda_empty_scheduler
  (* lin_get_scheduler *)
  "epdaHS_get_scheduler"
  (* lin_join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* lin_extend_scheduler *)
  "append"
  (* lin_get_unfixed_scheduler *)
  "epdaHS_get_unfixed_scheduler"
  (* lin_set_unfixed_scheduler *)
  "epdaHS_set_unfixed_scheduler"
  (* lin_get_fixed_scheduler *)
  epdaHS_get_fixed_scheduler
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  "epda_empty_history"
  (* empty_history_fragment *)
  "epda_empty_history_fragment"
  (* lin_set_history *)
  "epdaHS_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* lin_get_history *)
  "epdaHS_conf_history"
  (* bra_configurations *)
  "epdaH_configurations"
  (* bra_initial_configurations *)
  "epdaH_initial_configurations"
  (* bra_step_relation *)
  "epdaH_step_relation"
  (* bra_marking_condition *)
  "epdaH_marking_condition"
  (* bra_marked_effect *)
  "epdaH_marked_effect"
  (* bra_unmarked_effect *)
  "epdaH_unmarked_effect"
  (* bra_fixed_schedulers *)
  epda_fixed_schedulers
  (* bra_empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* bra_fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* bra_get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* bra_set_history *)
  "epdaH_set_history"
  (* bra_get_history *)
  "epdaH_conf_history"
  (* Lin2BraConf *)
  "epdaHvHS_Lin2BraConf"
  (* Bra2LinConf *)
  "epdaHvHS_Bra2LinConf"
  (* Bra2LinStep *)
  "epdaHvHS_Bra2LinStep"
  (* Bra2LinFin *)
  epdaHvHS_Bra2LinFin
  apply(simp add: LOCALE_DEFS epdaH_interpretations epdaHS_interpretations0)
  apply(simp add: epdaH_vs_epdaHS_inst_ATS_Branching_Versus_Linear1_axioms)
  apply(simp add: epdaH_vs_epdaHS_inst_ATS_Branching_Versus_Linear2_axioms)
  done

theorem epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer: "
  valid_epda G
  \<Longrightarrow> (epdaHS.Nonblockingness_linear_DB G \<longleftrightarrow> epdaH.Nonblockingness_branching G) \<and> epdaHS.unmarked_language G = epdaH.unmarked_language G \<and> epdaHS.marked_language G = epdaH.marked_language G"
  apply(rule conjI)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rule epdaH_vs_epdaHS.bflin_to_bfbra)
     apply(force)+
    apply(metis epdaHS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
   apply(clarsimp)
   apply(metis epdaH_vs_epdaHS.bfbra_to_bflin epdaHS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(rule conjI)
   apply(rule order_antisym)
    apply(rule_tac
      t = "epdaHS.unmarked_language G"
      and s = "epdaHS.finite_unmarked_language G"
      in ssubst)
     apply (metis epdaHS.AX_unmarked_language_finite)
    apply (metis epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_unmarked_language_translation2)
   apply(rule_tac
      t = "epdaH.unmarked_language G"
      and s = "epdaH.finite_unmarked_language G"
      in ssubst)
    apply (metis epdaH.AX_unmarked_language_finite)
   apply (metis epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_unmarked_language_translation1)
  apply(rule order_antisym)
   apply(rule_tac
      t = "epdaHS.marked_language G"
      and s = "epdaHS.finite_marked_language G"
      in ssubst)
    apply (metis epdaHS.AX_marked_language_finite)
   apply (metis epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_marked_language_translation2)
  apply(rule_tac
      t = "epdaH.marked_language G"
      and s = "epdaH.finite_marked_language G"
      in ssubst)
   apply (metis epdaH.AX_marked_language_finite)
  apply (metis epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_marked_language_translation1)
  done

lemma epdaHS_minimal_step_prefix_closureondition: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaHS_configurations G
  \<Longrightarrow> epdaHS_conf_state c = edge_src e
  \<Longrightarrow> prefix (option_to_list (edge_event e)) (epdaHS_conf_scheduler c)
  \<Longrightarrow> prefix (edge_pop e) (epdaHS_conf_stack c)
  \<Longrightarrow> \<exists>c'. epdaHS_step_relation G c e c'"
  apply(simp add: epdaHS_step_relation_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac ca caa)(*strict*)
  apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = X0, epdaHS_conf_history = X1, epdaHS_conf_scheduler = X2, epdaHS_conf_stack = X3\<rparr>" for X0 X1 X2 X3
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac ca caa)(*strict*)
   apply(force)
  apply(rename_tac ca caa)(*strict*)
  apply(rule conjI)
   apply(rename_tac ca caa)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac ca caa)(*strict*)
    apply(force)
   apply(rename_tac ca caa)(*strict*)
   apply(rule_tac
      x = "caa"
      in exI)
   apply(force)
  apply(rename_tac ca caa)(*strict*)
  apply(rule sym)
  apply(force)
  done

lemma prefix_to_history_fragment_prefixes: "
  w1 \<in> epda_effects G
  \<Longrightarrow> w2 \<in> epda_effects G
  \<Longrightarrow> w1 \<sqsubseteq> w2 = (ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2)"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: epdaHS.history_fragment_prefixes_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x c hf'')(*strict*)
   apply(simp add: epda_effects_def)
  apply(clarsimp)
  apply(simp add: epdaHS.history_fragment_prefixes_def prefix_def)
  apply(subgoal_tac "w1 \<in> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2}")
   apply(clarsimp)
  apply(erule_tac
      A = "{hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1}"
      in set_mp)
  apply(clarsimp)
  apply(simp add: epda_effects_def)
  done

lemma epdaH_history_in_epda_events: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaH_configurations G
  \<Longrightarrow> set (epdaH_conf_history c) \<subseteq> epda_events G"
  apply(simp add: epdaH_configurations_def)
  apply(clarsimp)
  apply(rename_tac x q s h)(*strict*)
  apply(force)
  done

lemma epdaHS2HF_DEdetermR_FEdetermHist_DB_hlp: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> epdaH_step_relation G c e1 c1
  \<Longrightarrow> epdaH_step_relation G c e2 c2
  \<Longrightarrow> epdaH_conf_history c1 = epdaH_conf_history c @ w1
  \<Longrightarrow> epdaH_conf_history c2 = epdaH_conf_history c @ w2
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> c \<in> epdaH_configurations G
  \<Longrightarrow> c1 \<in> epdaH_configurations G
  \<Longrightarrow> c2 \<in> epdaH_configurations G
  \<Longrightarrow> w1 \<sqsubseteq> w2
  \<Longrightarrow> e1 = e2"
  apply(subgoal_tac "epdaH.derivation_initial G (derivation_append d (der2 c e2 c2) n)")
   prefer 2
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(force)
    apply(force)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rule epdaH.der2_is_derivation)
    apply(force)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(simp add: prefix_def)
  apply(simp add: epdaHS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(rename_tac w2)
  apply(rename_tac w2)(*strict*)
  apply(subgoal_tac "epdaHS.derivation_initial G (epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n))")
   apply(rename_tac w2)(*strict*)
   apply(erule_tac
      x = "the(get_configuration(epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) n))"
      in ballE)
    apply(rename_tac w2)(*strict*)
    apply(subgoal_tac "\<exists>c1. epdaHS_step_relation G (the (get_configuration (epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) n))) e1 c1")
     apply(rename_tac w2)(*strict*)
     apply(clarsimp)
     apply(rename_tac w2 c1a)(*strict*)
     apply(erule_tac
      x = "c1a"
      in allE)
     apply(erule_tac
      x = "the(get_configuration(epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) (Suc n)))"
      in allE)
     apply(erule_tac
      x = "e1"
      in allE)
     apply(erule_tac
      x = "e2"
      in allE)
     apply(erule impE)
      apply(rename_tac w2 c1a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac w2 c1a)(*strict*)
     apply(rule conjI)
      apply(rename_tac w2 c1a)(*strict*)
      apply(force)
     apply(rename_tac w2 c1a)(*strict*)
     apply(case_tac "epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) n")
      apply(rename_tac w2 c1a)(*strict*)
      apply(clarsimp)
      apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def)
     apply(rename_tac w2 c1a a)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
     apply(case_tac a)
     apply(rename_tac w2 c1a a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac w2 c1a option b)(*strict*)
     apply(rule_tac
      ?e1.0 = "E"
      and n = "n"
      and d = "epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n)" for E
      in epdaHS.position_change_due_to_step_relation)
       apply(rename_tac w2 c1a option b)(*strict*)
       apply(rule epdaHS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac w2 c1a option b)(*strict*)
      apply(force)
     apply(rename_tac w2 c1a option b)(*strict*)
     apply(case_tac "epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) (Suc n)")
      apply(rename_tac w2 c1a option b)(*strict*)
      apply(clarsimp)
      apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def)
     apply(rename_tac w2 c1a option b a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac w2 c1a option b a optiona ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac w2 c1a option b optiona ba)(*strict*)
     apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def)
    apply(rename_tac w2)(*strict*)
    apply(rule epdaHS_minimal_step_prefix_closureondition)
         apply(rename_tac w2)(*strict*)
         apply(force)
        apply(rename_tac w2)(*strict*)
        apply(simp add: epdaH_step_relation_def)
       apply(rename_tac w2)(*strict*)
       apply(thin_tac "\<forall>c1 c2a e1 e2a. epdaHS_step_relation G (the (get_configuration (epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) n))) e1 c1 \<and> epdaHS_step_relation G (the (get_configuration (epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n) n))) e2a c2a \<longrightarrow> e1 = e2a")
       apply(rename_tac w2)(*strict*)
       apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
       apply(rule_tac
      t = "derivation_append d (der2 c e2 c2) n (Suc n)"
      and s = "Some (pair (Some e2) c2)"
      in ssubst)
        apply(rename_tac w2)(*strict*)
        apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def)
       apply(rename_tac w2)(*strict*)
       apply(rule_tac
      t = "derivation_append d (der2 c e2 c2) n n"
      and s = "Some (pair e c)"
      in ssubst)
        apply(rename_tac w2)(*strict*)
        apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def)
       apply(rename_tac w2)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
       apply(subgoal_tac "epdaHvHS_Bra2LinConf SSc1 (ATS_Branching_Versus_Linear1.Bra2LinDer' epda_empty_scheduler_fragment (@) epdaHvHS_Bra2LinStep SSG (derivation_append d (der2 c e2 c2) n) (Suc n) n @ epdaHvHS_Bra2LinFin SSG (epdaH_get_fixed_scheduler SScX)) \<in> epdaHS_configurations SSG" for SSc1 SScX SSG)
        apply(rename_tac w2)(*strict*)
        prefer 2
        apply(rule epdaH_vs_epdaHS.Bra2LinConf_closed_wrt_Bra2LinDer_prime)
             apply(rename_tac w2)(*strict*)
             apply(force)
            apply(rename_tac w2)(*strict*)
            apply(rule epdaH.derivation_append_preserves_derivation)
              apply(rename_tac w2)(*strict*)
              apply(rule epdaH.derivation_initial_is_derivation)
              apply(force)
             apply(rename_tac w2)(*strict*)
             apply(rule epdaH.der2_is_derivation)
             apply(force)
            apply(rename_tac w2)(*strict*)
            apply(clarsimp)
            apply(simp add: der2_def)
           apply(rename_tac w2)(*strict*)
           apply(rule epdaH.derivation_initial_belongs)
            apply(rename_tac w2)(*strict*)
            apply(force)
           apply(rename_tac w2)(*strict*)
           apply(force)
          apply(rename_tac w2)(*strict*)
          apply(simp add: der2_def)
          apply(simp add: derivation_append_def)
         apply(rename_tac w2)(*strict*)
         apply(force)
        apply(rename_tac w2)(*strict*)
        apply(simp add: derivation_append_def der2_def)
       apply(rename_tac w2)(*strict*)
       apply(force)
      apply(rename_tac w2)(*strict*)
      apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
      apply(simp add: derivation_append_def der2_def)
      apply(simp add: get_configuration_def)
      apply(simp add: epdaHvHS_Bra2LinConf_def)
      apply(simp add: epdaH_step_relation_def)
     apply(rename_tac w2)(*strict*)
     apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
     apply(simp add: derivation_append_def der2_def)
     apply(simp add: get_configuration_def)
     apply(simp add: epdaHvHS_Bra2LinConf_def)
     apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
     apply(rule_tac
      t = "nat_seq n n"
      and s = "[n]"
      in ssubst)
      apply(rename_tac w2)(*strict*)
      apply (metis natUptTo_n_n)
     apply(rename_tac w2)(*strict*)
     apply(clarsimp)
     apply(simp add: epdaHvHS_Bra2LinStep_def)
     apply(rule_tac
      t = "option_to_list (edge_event e1)"
      and s = "w1"
      in ssubst)
      apply(rename_tac w2)(*strict*)
      prefer 2
      apply(rule_tac
      t = "option_to_list (edge_event e2)"
      and s = "w1@w2"
      in ssubst)
       apply(rename_tac w2)(*strict*)
       prefer 2
       apply(simp add: prefix_def)
      apply(rename_tac w2)(*strict*)
      apply(simp add: epdaH_step_relation_def)
     apply(rename_tac w2)(*strict*)
     apply(simp add: epdaH_step_relation_def)
    apply(rename_tac w2)(*strict*)
    apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
    apply(simp add: get_configuration_def)
    apply(simp add: epdaHvHS_Bra2LinConf_def)
    apply(simp add: epdaH_step_relation_def prefix_def)
    apply(clarsimp)
   apply(rename_tac w2)(*strict*)
   apply(simp add: epdaHS.get_accessible_configurations_def)
   apply(erule_tac
      x = "epdaH_vs_epdaHS.Bra2LinDer G (derivation_append d (der2 c e2 c2) n) (Suc n)"
      in allE)
   apply(erule impE)
    apply(rename_tac w2)(*strict*)
    apply(force)
   apply(rename_tac w2)(*strict*)
   apply(erule_tac
      x = "n"
      in allE)
   apply(case_tac "ATS_Branching_Versus_Linear1.Bra2LinDer epda_empty_scheduler_fragment (@) (@) epdaH_get_fixed_scheduler epdaHvHS_Bra2LinConf epdaHvHS_Bra2LinStep epdaHvHS_Bra2LinFin G (derivation_append d (der2 c e2 c2) n) (Suc n) n")
    apply(rename_tac w2)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def derivation_append_def der2_def)
   apply(rename_tac w2 a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac w2 a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w2)(*strict*)
  apply(simp add: epdaHS.derivation_initial_def)
  apply(rule conjI)
   apply(rename_tac w2)(*strict*)
   apply(rule epdaH_vs_epdaHS.Bra2LinDer_preserves_derivation)
      apply(rename_tac w2)(*strict*)
      apply(force)
     apply(rename_tac w2)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac w2)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac w2)(*strict*)
     apply(force)
    apply(rename_tac w2)(*strict*)
    apply(force)
   apply(rename_tac w2)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac w2)(*strict*)
  apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 ca)(*strict*)
   apply(rule_tac
      t = "derivation_append d (der2 c e2 c2) n 0"
      and s = "Some (pair None ca)"
      in ssubst)
    apply(rename_tac w2 ca)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w2 ca)(*strict*)
   apply(rule_tac
      t = "derivation_append d (der2 c e2 c2) n (Suc n)"
      and s = "Some (pair (Some e2) c2)"
      in ssubst)
    apply(rename_tac w2 ca)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w2 ca)(*strict*)
   apply(clarsimp)
   apply(rule epdaH_vs_epdaHS.AX_Bra2LinConf_preserves_initiality)
     apply(rename_tac w2 ca)(*strict*)
     apply(force)
    apply(rename_tac w2 ca)(*strict*)
    apply(rule epdaH_vs_epdaHS.Bra2LinDer_prime_closed)
        apply(rename_tac w2 ca)(*strict*)
        apply(force)
       apply(rename_tac w2 ca)(*strict*)
       apply(rule epdaH.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac w2 ca)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac w2 ca)(*strict*)
       apply(force)
      apply(rename_tac w2 ca)(*strict*)
      apply(force)
     apply(rename_tac w2 ca)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac w2 ca)(*strict*)
    apply(force)
   apply(rename_tac w2 ca)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac w2)(*strict*)
  apply (metis epdaH.derivation_initial_is_derivation epdaH.some_position_has_details_at_0)
  done

lemma epdaHS2HF_DEdetermR_FEdetermHist_DB: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaH.is_forward_edge_deterministicHist_DB_long G"
  apply(simp add: epdaH.is_forward_edge_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(subgoal_tac "c \<in> epdaH_configurations G")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d"
      in epdaH.belongs_configurations)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply (metis epdaH.derivation_initial_belongs)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(subgoal_tac "c1 \<in> epdaH_configurations G")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   prefer 2
   apply (metis epdaH.AX_step_relation_preserves_belongs)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(subgoal_tac "c2 \<in> epdaH_configurations G")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   prefer 2
   apply (metis epdaH.AX_step_relation_preserves_belongs)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(subgoal_tac "prefix w1 w2 \<or> prefix w2 w1 \<or> w1 = w2")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      t = "w1 = w2"
      and s = "prefix w1 w2 \<and> prefix w2 w1"
      in ssubst)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply (metis mutual_prefix_implies_equality prefix_reflexive)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(rule_tac
      t = "prefix w1 w2"
      and s = "ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2"
      in ssubst)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply(rule prefix_to_history_fragment_prefixes)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
     apply(simp add: epdaH_configurations_def)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply(simp add: epdaH_configurations_def)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(rule_tac
      t = "prefix w2 w1"
      and s = "ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w1"
      in ssubst)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply(rule prefix_to_history_fragment_prefixes)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
     apply(simp add: epdaH_configurations_def)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply(simp add: epdaH_configurations_def)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(rule_tac
      s = "ATS_History.history_fragment_prefixes epda_effects (@) G w2 = ATS_History.history_fragment_prefixes epda_effects (@) G w1"
      and t = "ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<and> ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w1"
      in ssubst)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<or> ATS_History.history_fragment_prefixes epda_effects (@) G w2 = ATS_History.history_fragment_prefixes epda_effects (@) G w1")
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(subgoal_tac "prefix w1 w2 \<or> (prefix w2 w1)")
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(thin_tac "w1 \<sqsubseteq> w2 \<or> w2 \<sqsubseteq> w1 \<or> w1 = w2")
  apply(erule disjE)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
   apply(rule epdaHS2HF_DEdetermR_FEdetermHist_DB_hlp)
              apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
              apply(force)+
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
  apply(rule sym)
  apply(rule epdaHS2HF_DEdetermR_FEdetermHist_DB_hlp)
             apply(rename_tac c d c1 c2 e1 e2 n w1 w2 e)(*strict*)
             apply(force)+
  done

corollary epdaHS2HF_FEdetermHist: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_edge_deterministicHist_DB_long G
  \<Longrightarrow> epdaH.is_forward_edge_deterministicHist_DB_long G"
  apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_DB_SB epdaHS.AX_is_forward_edge_deterministic_correspond_SB epdaHS2HF_DEdetermR_FEdetermHist_DB)
  done

lemma epdaHS_inst_hlp_BF_LinSBRest_DetR_LaOp: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (epdaHS.unmarked_language G) (epdaHS.marked_language G)
  \<Longrightarrow> epdaHS.Nonblockingness_linear_restricted G"
  apply(rule epdaH_vs_epdaHS.bfbra_to_bflin_rest)
   apply(force)
  apply(rule epdaH.AX_BF_BraSBRest_DetHDB_LaOp)
    apply(force)
   apply(rule_tac
      t = "epdaH.is_forward_deterministicHist_SB G"
      and s = "epdaH.is_forward_deterministicHist_DB G"
      in ssubst)
    apply(rule epdaH.is_forward_deterministic_correspond_DB_SB)
    apply(force)
   apply(unfold epdaH.is_forward_deterministicHist_DB_def)
   apply(rule conjI)
    apply(rule epdaH_is_forward_target_deterministicHist_DB_long)
    apply(force)
   apply(rule epdaHS2HF_FEdetermHist)
    apply(force)
   apply(rule epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
    apply(force)
   apply(simp add: epdaHS.is_forward_deterministic_accessible_def)
  apply(rule_tac
      t = "epdaH.unmarked_language G"
      and s = "epdaHS.unmarked_language G"
      in ssubst)
   apply(metis epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(rule_tac
      t = "epdaH.marked_language G"
      and s = "epdaHS.marked_language G"
      in ssubst)
   apply(metis epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(force)
  done

lemma epdaHS_inst_hlp_BF_LinDBRest_DetR_LaOp: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (epdaHS.unmarked_language G) (epdaHS.marked_language G)
  \<Longrightarrow> epdaHS.Nonblockingness_linear_restricted_DB G"
  apply(rule_tac
      t = "epdaHS.Nonblockingness_linear_restricted_DB G"
      and s = "epdaHS.Nonblockingness_linear_restricted G"
      in ssubst)
   apply (metis epdaHS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB)
  apply (metis epdaHS_inst_hlp_BF_LinSBRest_DetR_LaOp)
  done

lemma epdaHS_inst_BF_LinDBRest_DetR_LaOp_axioms: "
  BF_LinDBRest_DetR_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_get_scheduler (@) epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB epdaHS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply (metis epdaHS_inst_hlp_BF_LinDBRest_DetR_LaOp)
  done

lemma epdaHS_inst_BF_LinDBRest_DetHDB_LaOp_axioms: "
  BF_LinDBRest_DetHDB_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_get_scheduler (@) epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinDBRest_DetR_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_get_scheduler (@) epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB epdaHS_get_fixed_scheduler_DB")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule epdaHS_inst_BF_LinDBRest_DetR_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(erule_tac
      x = "M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (epdaHS.unmarked_language M) (epdaHS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaHS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rename_tac M)(*strict*)
   apply (metis epdaHS_is_forward_target_deterministic_accessible)
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaHS.is_forward_deterministicHist_DB_def)
  apply(clarsimp)
  apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_DB_SB epdaHS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  done

lemma epdaHS_inst_BF_LinDBRest_DetHSB_LaOp_axioms: "
  BF_LinDBRest_DetHSB_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler epda_effects
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_get_scheduler (@) epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB epdaHS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetHSB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinDBRest_DetR_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_get_scheduler (@) epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB epdaHS_get_fixed_scheduler_DB")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule epdaHS_inst_BF_LinDBRest_DetR_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(erule_tac
      x = "M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (epdaHS.unmarked_language M) (epdaHS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaHS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rename_tac M)(*strict*)
   apply (metis epdaHS_is_forward_target_deterministic_accessible)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply (rule epdaHS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  apply(rename_tac M)(*strict*)
  apply(erule_tac
      x = "M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t = "epdaHS.is_forward_edge_deterministic_accessible M"
      and s = "epdaHS.is_forward_edge_deterministicHist_SB_long M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaHS.is_forward_deterministicHist_SB_def)
  done

lemma epdaHS_inst_BF_LinSBRest_DetR_LaOp_axioms: "
  BF_LinSBRest_DetR_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler"
  apply(simp add: BF_LinSBRest_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule epdaHS_inst_hlp_BF_LinSBRest_DetR_LaOp)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(force)
  done

lemma epdaHS_inst_BF_LinSBRest_DetHDB_LaOp_axioms: "
  BF_LinSBRest_DetHDB_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler"
  apply(simp add: BF_LinSBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinSBRest_DetR_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule epdaHS_inst_BF_LinSBRest_DetR_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinSBRest_DetR_LaOp_axioms_def)
  apply(erule_tac
      x = "M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (epdaHS.unmarked_language M) (epdaHS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaHS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rename_tac M)(*strict*)
   apply (metis epdaHS_is_forward_target_deterministic_accessible)
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaHS.is_forward_deterministicHist_DB_def)
  apply(clarsimp)
  apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_DB_SB epdaHS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  done

lemma epdaHS_inst_BF_LinSBRest_DetHSB_LaOp_axioms: "
  BF_LinSBRest_DetHSB_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler"
  apply(simp add: BF_LinSBRest_DetHSB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinSBRest_DetHDB_LaOp_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule epdaHS_inst_BF_LinSBRest_DetHDB_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinSBRest_DetHDB_LaOp_axioms_def)
  apply(erule_tac
      x = "M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (epdaHS.unmarked_language M) (epdaHS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      P = "\<lambda>X. X"
      in subst)
   apply(rename_tac M)(*strict*)
   apply(rule epdaHS.is_forward_deterministic_correspond_DB_SB)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(blast)
  done

lemma epdaHS_inst_BF_LinSB_OpLa_axioms: "
  BF_LinSB_OpLa_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler"
  apply(simp add: BF_LinSB_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      s = "epdaH.unmarked_language M"
      and t = "epdaHS.unmarked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply(metis epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      s = "epdaH.marked_language M"
      and t = "epdaHS.marked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply(metis epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule epdaH.AX_BF_Bra_OpLa)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply (metis epdaH_vs_epdaHS.bflin_to_bfbra)
  done

lemma epdaHS_inst_BF_LinDB_OpLa_axioms: "
  BF_LinDB_OpLa_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_get_scheduler (@) epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB epdaHS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDB_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinSB_OpLa_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule epdaHS_inst_BF_LinSB_OpLa_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinSB_OpLa_axioms_def)
  apply(erule_tac
      x = "M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac M)(*strict*)
  apply (metis epdaHS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  done

print_locale loc_autHFS_10
interpretation "epdaHS" : loc_autHFS_10
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaHS_configurations"
  (* initial_configurations *)
  "epdaHS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaHS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaHS_marking_condition"
  (* marked_effect *)
  "epdaHS_marked_effect"
  (* unmarked_effect *)
  "epdaHS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaHS_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  "epda_empty_history"
  (* empty_history_fragment *)
  "epda_empty_history_fragment"
  (* set_history *)
  "epdaHS_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaHS_conf_history"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaHS_string_state"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* scheduler_fragments *)
  "epda_effects"
  (* empty_scheduler_fragment *)
  epda_empty_scheduler_fragment
  (* join_scheduler_fragments *)
  "append"
  (* unfixed_schedulers *)
  "epda_effects"
  (* empty_unfixed_scheduler *)
  epda_empty_unfixed_scheduler
  (* unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* extend_unfixed_scheduler *)
  "append"
  (* unfixed_scheduler_extendable *)
  epda_unfixed_scheduler_extendable
  (* schedulers *)
  "epda_effects"
  (* initial_schedulers *)
  "epda_effects"
  (* empty_scheduler *)
  epda_empty_scheduler
  (* get_scheduler *)
  "epdaHS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler *)
  "epdaHS_set_unfixed_scheduler"
  (* get_unfixed_scheduler *)
  "epdaHS_get_unfixed_scheduler"
  (* get_fixed_scheduler *)
  epdaHS_get_fixed_scheduler
  (* set_unfixed_scheduler_DB *)
  "epdaHS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "epdaHS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "epdaHS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS epdaH_interpretations epdaHS_interpretations0)
  apply(simp add: epdaHS_inst_BF_LinDBRest_DetR_LaOp_axioms)
  apply(simp add: epdaHS_inst_BF_LinDBRest_DetHDB_LaOp_axioms epdaHS_inst_BF_LinDBRest_DetHSB_LaOp_axioms epdaHS_inst_BF_LinSBRest_DetR_LaOp_axioms epdaHS_inst_BF_LinSBRest_DetHDB_LaOp_axioms epdaHS_inst_BF_LinSBRest_DetHSB_LaOp_axioms epdaHS_inst_BF_LinSB_OpLa_axioms epdaHS_inst_BF_LinDB_OpLa_axioms )
  done

lemmas epdaHS_interpretations1 =
  epdaHS_inst_BF_LinDBRest_DetR_LaOp_axioms
  epdaHS_inst_BF_LinDBRest_DetHDB_LaOp_axioms
  epdaHS_inst_BF_LinDBRest_DetHSB_LaOp_axioms
  epdaHS_inst_BF_LinSBRest_DetR_LaOp_axioms
  epdaHS_inst_BF_LinSBRest_DetHDB_LaOp_axioms
  epdaHS_inst_BF_LinSBRest_DetHSB_LaOp_axioms
  epdaHS_inst_BF_LinSB_OpLa_axioms
  epdaHS_inst_BF_LinDB_OpLa_axioms

end

