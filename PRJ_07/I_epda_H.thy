section {*I\_epda\_H*}
theory
  I_epda_H

imports
  I_epda_base

begin

record ('state, 'event, 'stack) epdaH_conf =
  epdaH_conf_state :: "'state"
  epdaH_conf_history :: "'event list"
  epdaH_conf_stack :: "'stack list"

definition epdaH_get_fixed_scheduler :: "
  ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> 'event list"
  where
    "epdaH_get_fixed_scheduler c \<equiv>
  []"
declare epdaH_get_fixed_scheduler_def [simp add]

definition epdaH_get_fixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "epdaH_get_fixed_scheduler_DB G d n \<equiv>
  []"
declare epdaH_get_fixed_scheduler_DB_def [simp add]

definition epdaH_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf set"
  where
    "epdaH_configurations G \<equiv>
  {\<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr> |
  q s h.
  q \<in> epda_states G
  \<and> set s \<subseteq> epda_gamma G
  \<and> set h \<subseteq> epda_events G}"

definition epdaH_initial_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf set"
  where
    "epdaH_initial_configurations G \<equiv>
  {c.
    epdaH_conf_state c = epda_initial G
    \<and> epdaH_conf_history c = []
    \<and> epdaH_conf_stack c = [epda_box G]}
  \<inter> epdaH_configurations G"

definition epdaH_marking_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf set"
  where
    "epdaH_marking_configurations G \<equiv>
  {c. epdaH_conf_state c \<in> epda_marking G}
  \<inter> epdaH_configurations G"

definition epdaH_string_state :: "
  ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> 'event list"
  where
    "epdaH_string_state c \<equiv>
  epdaH_conf_history c"

definition epdaH_marking_condition :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> bool"
  where
    "epdaH_marking_condition G d \<equiv>
  \<exists>i e c.
  d i = Some (pair e c)
  \<and> c \<in> epdaH_marking_configurations G
  \<and> (\<forall>j e' c'.
     j > i
     \<and> d j = Some (pair e' c')
     \<longrightarrow> epdaH_string_state c = epdaH_string_state c')"

definition epdaH_step_relation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "epdaH_step_relation G c1 e c2 \<equiv>
  e \<in> epda_delta G
  \<and> epdaH_conf_state c1 = edge_src e
  \<and> epdaH_conf_state c2 = edge_trg e
  \<and> epdaH_conf_history c2
      = epdaH_conf_history c1 @ option_to_list (edge_event e)
  \<and> (\<exists>w.
     epdaH_conf_stack c1 = edge_pop e @ w
     \<and> epdaH_conf_stack c2 = edge_push e @ w)"

definition epdaH_marked_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> 'event list set"
  where
    "epdaH_marked_effect G d \<equiv>
  {w. \<exists>i e c.
      d i = Some (pair e c)
      \<and> c \<in> epdaH_marking_configurations G
      \<and> w = epdaH_conf_history c
      \<and> (\<forall>j e' c'.
         j > i
         \<and> d j = Some(pair e' c')
         \<longrightarrow> epdaH_string_state c = epdaH_string_state c')}"

definition epdaH_unmarked_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> 'event list set"
  where
    "epdaH_unmarked_effect G d \<equiv>
  {w. \<exists>i e c.
      d i = Some (pair e c)
      \<and> w = epdaH_conf_history c}"

definition epdaH_get_destinations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation_configuration
  \<Rightarrow> ('state, 'event, 'stack) epda_destinations set"
  where
    "epdaH_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    {state (epdaH_conf_state c)}
    \<union> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'})"

lemma epdaH_inst_AX_initial_configuration_belongs: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaH_initial_configurations G \<subseteq> epdaH_configurations G)"
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: epdaH_initial_configurations_def)
  done

lemma epdaH_inst_AX_step_relation_preserves_belongs: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1 e c2. epdaH_step_relation G c1 e c2 \<longrightarrow> c1 \<in> epdaH_configurations G \<longrightarrow> e \<in> epda_step_labels G \<and> c2 \<in> epdaH_configurations G))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G c1 e c2 w)(*strict*)
   apply(simp add: epda_step_labels_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: epda_step_labels_def epdaH_step_relation_def epdaH_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2 h w)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G e c2 h w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e h w)(*strict*)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac G e h w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e h w)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: option_to_set_def option_to_list_def)
  apply(clarsimp)
  apply(rename_tac G e h w x)(*strict*)
  apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac G e h w x a aa)(*strict*)
  apply(erule_tac
      P="edge_push e = aa @ [epda_box G]"
      in disjE)
   apply(rename_tac G e h w x a aa)(*strict*)
   apply(clarsimp)
   apply(blast)
  apply(rename_tac G e h w x a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e h w x a)(*strict*)
  apply(blast)
  done

interpretation "epdaH" : loc_autHF_0
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  done

lemma epdaH_inst_AX_effect_inclusion1: "
  (\<forall>M f. epdaH_marking_condition M f \<longrightarrow> epdaH_marked_effect M f \<subseteq> epdaH_unmarked_effect M f)"
  apply(clarsimp)
  apply(rename_tac M f x)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  done

lemma epdaH_inst_lang_sound: "
  (\<forall>M. valid_epda M \<longrightarrow> epdaH.unmarked_language M \<subseteq> epda_effects M)"
  apply(clarsimp)
  apply(rename_tac M x)(*strict*)
  apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def epda_effects_def)
  apply(clarsimp)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(subgoal_tac "c \<in> epdaH_configurations M")
   apply(rename_tac M xa d i e c)(*strict*)
   apply(simp add: epdaH_configurations_def)
   apply(clarsimp)
   apply(rename_tac M xa d i e q s h)(*strict*)
   apply(force)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(rule epdaH.belongs_configurations)
   apply(rename_tac M xa d i e c)(*strict*)
   apply(rule epdaH.derivation_initial_belongs)
    apply(rename_tac M xa d i e c)(*strict*)
    apply(force)
   apply(rename_tac M xa d i e c)(*strict*)
   apply(force)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(force)
  done

lemma epdaH_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_epda M \<longrightarrow> (\<forall>f. epdaH.derivation_initial M f \<longrightarrow> epdaH_marking_condition M f \<longrightarrow> epdaH_marked_effect M f \<noteq> {}))"
  apply(simp add: epdaH_marking_condition_def epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i e c)(*strict*)
  apply(force)
  done

lemma epdaH_inst_AX_unmarked_effect_persists: "
   (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial epdaH_initial_configurations
               epdaH_step_relation G d \<longrightarrow>
              (\<forall>n. epdaH_unmarked_effect G (derivation_take d n)
                   \<subseteq> epdaH_unmarked_effect G d)))"
  apply(clarsimp)
  apply(rename_tac x d n xa)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac x d n i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  apply(case_tac "i\<le>n")
   apply(rename_tac x d n i e c)(*strict*)
   apply(force)
  apply(rename_tac x d n i e c)(*strict*)
  apply(force)
  done

lemma epdaH_inst_ATS_axioms: "
  ATS_Language_axioms valid_epda epdaH_initial_configurations
     epdaH_step_relation epda_effects epdaH_marking_condition
     epdaH_marked_effect epdaH_unmarked_effect"
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: epdaH_inst_AX_effect_inclusion1 epdaH_inst_lang_sound epdaH_inst_AX_marking_condition_implies_existence_of_effect epdaH_inst_AX_unmarked_effect_persists )
  done

print_locale loc_autHF_1
interpretation "epdaH" : loc_autHF_1
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms )
  done

definition epdaH_set_history :: "
  ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf"
  where
    "epdaH_set_history c h \<equiv>
  c \<lparr>epdaH_conf_history := h\<rparr>"

lemma epdaH_inst_AX_initial_history_empty: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaH_initial_configurations G \<longrightarrow> epdaH_conf_history c = []))"
  apply(simp add: epdaH_initial_configurations_def)
  done

lemma epdaH_inst_AX_steps_extend_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaH_configurations G \<longrightarrow> (\<forall>e c'. epdaH_step_relation G c e c' \<longrightarrow> (\<exists>hf\<in> epda_effects G. epdaH_conf_history c' = epdaH_conf_history c @ hf))))"
  apply(clarsimp)
  apply(rename_tac G c e c')(*strict*)
  apply(subgoal_tac "SSe \<in> epda_step_labels SSG \<and> SSc2 \<in> epdaH_configurations SSG" for SSe SSG SSc2)
   apply(rename_tac G c e c')(*strict*)
   prefer 2
   apply(rule epdaH.AX_step_relation_preserves_belongs)
     apply(rename_tac G c e c')(*strict*)
     apply(force)
    apply(rename_tac G c e c')(*strict*)
    apply(force)
   apply(rename_tac G c e c')(*strict*)
   apply(force)
  apply(rename_tac G c e c')(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def epda_effects_def epda_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x w)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e")
   apply(rename_tac G c e c' x w)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac G c e c' x w)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def option_to_set_def)
  apply(force)
  done

lemma epdaH_inst_AX_empty_history_is_history: "
  (\<forall>G. valid_epda G \<longrightarrow> [] \<in> epda_effects G)"
  apply(simp add: epda_effects_def)
  done

lemma epdaH_inst_AX_set_get_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaH_configurations G \<longrightarrow> epdaH_set_history c (epdaH_conf_history c) = c))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: epdaH_set_history_def)
  done

lemma epdaH_inst_AX_get_set_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaH_configurations G \<longrightarrow> (\<forall>h. h \<in> epda_effects G \<longrightarrow> epdaH_conf_history (epdaH_set_history c h) = h)))"
  apply(clarsimp)
  apply(rename_tac G c h)(*strict*)
  apply(simp add: epdaH_set_history_def)
  done

lemma epdaH_inst_AX_join_history_fragments_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>hf1. hf1 \<in> epda_effects G \<longrightarrow> (\<forall>hf2. hf2 \<in> epda_effects G \<longrightarrow> hf1 @ hf2 \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2)(*strict*)
  apply(simp add: epda_effects_def)
  done

lemma epdaH_inst_AX_get_history_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaH_configurations G \<longrightarrow> epdaH_conf_history c \<in> epda_effects G))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: epda_effects_def epdaH_configurations_def)
  apply(clarsimp)
  apply(rename_tac G x q s h)(*strict*)
  apply(force)
  done

lemma epdaH_inst_AX_mutual_prefix: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>hf1. hf1 \<in> epda_effects G \<longrightarrow> (\<forall>hf2. hf2 \<in> epda_effects G \<longrightarrow> (\<forall>hf3. hf3 \<in> epda_effects G \<longrightarrow> (\<forall>hf4. hf4 \<in> epda_effects G \<longrightarrow> hf1 @ hf2 = hf3 @ hf4 \<longrightarrow> (\<exists>hf\<in> epda_effects G. hf1 @ hf = hf3) \<or> (\<exists>hf\<in> epda_effects G. hf3 @ hf = hf1))))))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(simp add: epda_effects_def epdaH_configurations_def)
  apply(subgoal_tac "prefix hf1 hf3 \<or> prefix hf3 hf1")
   apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(erule disjE)
   apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G hf2 hf3 c)(*strict*)
  apply(force)
  done

lemma epdaH_inst_ATS_History_axioms: "
  ATS_History_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epdaH_step_relation epda_effects
     epda_effects epda_empty_history epda_empty_history_fragment
     epdaH_set_history (@) (@) epdaH_conf_history"
  apply(simp add: ATS_History_axioms_def)
  apply(simp add: epdaH_inst_AX_mutual_prefix epdaH_inst_AX_initial_history_empty epdaH_inst_AX_steps_extend_history epdaH_inst_AX_empty_history_is_history epdaH_inst_AX_set_get_history epdaH_inst_AX_get_set_history epdaH_inst_AX_join_history_fragments_closed epdaH_inst_AX_get_history_closed )
  done

print_locale loc_autHF_2
interpretation "epdaH" : loc_autHF_2
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms )
  done

lemma epdaH_inst_lang_finite: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaH.finite_marked_language G = epdaH.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: epdaH.finite_marked_language_def epdaH.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(simp add: epdaH_marking_condition_def)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rename_tac G d i e c ia ea ca)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma epdaH_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaH.finite_unmarked_language G = epdaH.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: epdaH.finite_unmarked_language_def epdaH.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma epdaH_inst_ATS_SchedF_Basic_axioms: "
  ATS_SchedF_Basic_axioms valid_epda epda_fixed_schedulers
     epda_empty_fixed_scheduler"
  apply(simp add: ATS_SchedF_Basic_axioms_def)
  done

lemma epdaH_inst_ATS_SchedF_SB_axioms: "
  ATS_SchedF_SB_axioms valid_epda epdaH_configurations epdaH_step_relation
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler"
  apply(simp add: ATS_SchedF_SB_axioms_def)
  done

print_locale loc_autHF_3
interpretation "epdaH" : loc_autHF_3
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms epdaH_inst_ATS_SchedF_Basic_axioms epdaH_inst_ATS_SchedF_SB_axioms )
  done

lemma epdaH_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_epda epdaH_configurations epda_step_labels
     epdaH_step_relation epda_fixed_schedulers
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_DB_axioms_def)
  done

lemma epdaH_inst_ATS_SchedF_SDB_axioms: "
  ATS_SchedF_SDB_axioms valid_epda epdaH_initial_configurations
     epdaH_step_relation epdaH_get_fixed_scheduler
     epdaH_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_SDB_axioms_def)
  done

lemma epdaH_inst_ATS_determHIST_SB_axioms: "
  ATS_determHIST_SB_axioms valid_epda epdaH_configurations epdaH_step_relation
     epdaH_conf_history epda_fixed_scheduler_extendable
     epdaH_get_fixed_scheduler"
  apply(simp add: ATS_determHIST_SB_axioms_def)
  done

interpretation "epdaH" : loc_autHF_6
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* get_fixed_scheduler_DB *)
  epdaH_get_fixed_scheduler_DB
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms epdaH_inst_ATS_SchedF_Basic_axioms epdaH_inst_ATS_SchedF_SB_axioms epdaH_inst_ATS_SchedF_SDB_axioms epdaH_inst_ATS_determHIST_SB_axioms )
  apply(simp add: epdaH_inst_ATS_SchedF_DB_axioms)
  done

lemma epdaH_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_epda
     epdaH_initial_configurations epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: epdaH_inst_lang_finite epdaH_inst_AX_unmarked_language_finite )
  done

interpretation "epdaH" : loc_autHF_7
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* get_fixed_scheduler_DB *)
  epdaH_get_fixed_scheduler_DB
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms epdaH_inst_ATS_SchedF_Basic_axioms epdaH_inst_ATS_SchedF_SB_axioms epdaH_inst_ATS_SchedF_DB_axioms epdaH_inst_ATS_SchedF_SDB_axioms epdaH_inst_ATS_determHIST_SB_axioms epdaH_inst_ATS_Language_by_Finite_Derivations_axioms )
  done

lemma epdaH_inst_AX_is_forward_target_deterministic_correspond_SB: "
  \<forall>G. valid_epda G \<longrightarrow>
        ATS.is_forward_target_deterministic_accessible
         epdaH_initial_configurations epdaH_step_relation G =
        ATS_determHIST_SB.is_forward_target_deterministicHist_SB_long
         epdaH_initial_configurations epdaH_step_relation epda_effects (@)
         (@) epdaH_conf_history epda_fixed_scheduler_extendable
         epdaH_get_fixed_scheduler G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rule epdaH.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.is_forward_target_deterministic_accessible_def)
  apply(simp add: epdaH.is_forward_target_deterministicHist_SB_long_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac G c c1 c2 e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  done

lemma epdaH_inst_ATS_HistoryCT_SB_axioms: "
  ATS_HistoryCT_SB_axioms valid_epda epdaH_initial_configurations
     epdaH_step_relation epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler"
  apply(simp add: ATS_HistoryCT_SB_axioms_def)
  apply(simp add: epdaH_inst_AX_is_forward_target_deterministic_correspond_SB )
  done

interpretation "epdaH" : loc_autHF_8
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* get_fixed_scheduler_DB *)
  epdaH_get_fixed_scheduler_DB
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms epdaH_inst_ATS_SchedF_Basic_axioms epdaH_inst_ATS_SchedF_SB_axioms epdaH_inst_ATS_SchedF_DB_axioms epdaH_inst_ATS_SchedF_SDB_axioms epdaH_inst_ATS_determHIST_SB_axioms epdaH_inst_ATS_Language_by_Finite_Derivations_axioms epdaH_inst_ATS_HistoryCT_SB_axioms )
  done

lemma epdaH_inst_AX_is_forward_target_deterministic_correspond_DB: "
  \<forall>G. valid_epda G \<longrightarrow>
        ATS.is_forward_target_deterministic_accessible
         epdaH_initial_configurations epdaH_step_relation G =
        ATS_determHIST_DB.is_forward_target_deterministicHist_DB_long
         epdaH_initial_configurations epdaH_step_relation epda_effects (@)
         (@) epdaH_conf_history epda_fixed_scheduler_extendable
         epdaH_get_fixed_scheduler_DB G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rule epdaH.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_DB_long)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.is_forward_target_deterministic_accessible_def)
  apply(simp add: epdaH.is_forward_target_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  done

lemma epdaH_inst_ATS_HistoryCT_DB_axioms: "
  ATS_HistoryCT_DB_axioms valid_epda epdaH_initial_configurations
     epdaH_step_relation epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler_DB"
  apply(simp add: ATS_HistoryCT_DB_axioms_def)
  apply(simp add: epdaH_inst_AX_is_forward_target_deterministic_correspond_DB )
  done

interpretation "epdaH" : loc_autHF_9
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* get_fixed_scheduler_DB *)
  epdaH_get_fixed_scheduler_DB
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms epdaH_inst_ATS_SchedF_Basic_axioms epdaH_inst_ATS_SchedF_SB_axioms epdaH_inst_ATS_SchedF_DB_axioms epdaH_inst_ATS_SchedF_SDB_axioms epdaH_inst_ATS_determHIST_SB_axioms epdaH_inst_ATS_Language_by_Finite_Derivations_axioms epdaH_inst_ATS_HistoryCT_SB_axioms epdaH_inst_ATS_HistoryCT_DB_axioms )
  done

lemma equal_by_mutual_extension: "
  w = v @ h1
  \<Longrightarrow> v = w @ h2
  \<Longrightarrow> w = v"
  apply(force)
  done

lemma epdaH_inst_AX_BF_BraSBRest_DetHSB_LaOp_axioms: "
   \<forall>M. valid_epda M \<longrightarrow>
        ATS_determHIST_SB.is_forward_deterministicHist_SB
         epdaH_initial_configurations epdaH_step_relation epda_effects (@)
         (@) epdaH_conf_history epda_fixed_scheduler_extendable
         epdaH_get_fixed_scheduler M \<longrightarrow>
        nonblockingness_language
         (epdaH.unmarked_language M)
         (ATS_Language0.marked_language epdaH_initial_configurations
           epdaH_step_relation epdaH_marking_condition epdaH_marked_effect
           M) \<longrightarrow>
        ATS_SchedF_SB.Nonblockingness_branching_restricted epdaH_configurations
         epdaH_initial_configurations epda_step_labels epdaH_step_relation
         epdaH_marking_condition epda_fixed_scheduler_extendable
         epdaH_get_fixed_scheduler M"
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: epdaH.Nonblockingness_branching_restricted_def)
  apply(clarsimp)
  apply(rename_tac M dh n)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(rename_tac M dh n)(*strict*)
   prefer 2
   apply(rule_tac
      M="M"
      in epdaH.some_position_has_details_before_max_dom)
     apply(rename_tac M dh n)(*strict*)
     apply (metis epdaH.derivation_initial_is_derivation)
    apply(rename_tac M dh n)(*strict*)
    apply(force)
   apply(rename_tac M dh n)(*strict*)
   apply(force)
  apply(rename_tac M dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e c)(*strict*)
  apply(subgoal_tac "epdaH_conf_history c \<in> prefix_closure (epdaH.marked_language M)")
   apply(rename_tac M dh n e c)(*strict*)
   prefer 2
   apply(simp add: nonblockingness_language_def)
   apply(rename_tac M dh n e c)(*strict*)
   apply(rule_tac
      A=" epdaH.unmarked_language M"
      in set_mp)
    apply(rename_tac M dh n e c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c)(*strict*)
   apply(thin_tac " epdaH.unmarked_language M \<subseteq> (prefix_closure (epdaH.marked_language M))")
   apply(rename_tac M dh n e c)(*strict*)
   apply(simp add: epdaH.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac M dh n e c)(*strict*)
  apply(thin_tac "nonblockingness_language (epdaH.unmarked_language M) (epdaH.marked_language M)")
  apply(rename_tac M dh n e c)(*strict*)
  apply(simp add: prefix_closure_def epdaH.marked_language_def prefix_def)
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca)(*strict*)
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb)(*strict*)
  apply(subgoal_tac "\<exists>i e c. d i = Some (pair e c) \<and> c \<in> epdaH_marking_configurations M \<and> (\<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_conf_history c = epdaH_conf_history c' )")
   apply(rename_tac M dh n e c d ca i ea cb)(*strict*)
   prefer 2
   apply(simp add: epdaH_marking_condition_def epdaH_string_state_def)
  apply(rename_tac M dh n e c d ca i ea cb)(*strict*)
  apply(thin_tac "epdaH_marking_condition M d")
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(subgoal_tac "dh 0 = d 0")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b)(*strict*)
   apply(case_tac "dh 0")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc b)(*strict*)
    apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b a option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b ba)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
    (*
  what should dc be?
  ia \<le> i \<le> n : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; dc = []
  ia \<le> n \<le> i : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; dc = []
  n \<le> ia \<le> i : d@ia ~ d@ia \<Longrightarrow> dc = d (n\<dots>ia)
  i \<le> ia \<le> n : d@ia ~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; dc = []
  i \<le> n \<le> ia : d@n ~ dh@n; dc = d (n\<dots>ia)
  n \<le> i \<le> ia : d@n ~ dh@n; dc = d (n\<dots>ia)
  ia \<le> n \<Longrightarrow> dc = []
  n \<le> ia \<Longrightarrow> dc = d (n\<dots>ia)
*)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(case_tac "ia\<le>n")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule_tac
      x="der1 c"
      in exI)
   apply(rule_tac
      t="derivation_append dh (der1 c) n"
      and s="dh"
      in ssubst)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule ext)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc x)(*strict*)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(simp add: der1_def)
    apply(case_tac "dh x")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc x)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
    apply(rule_tac
      m="x"
      and d="dh"
      in epdaH.no_some_beyond_maximum_of_domain)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule epdaH.der1_is_derivation)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule epdaH.der1_belongs)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(simp add: derivation_append_fit_def der1_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(simp add: epdaH_marking_condition_def)
    (*
  where does it accept continuously?
  ia \<le> i \<le> n : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> d@ia=dh@ia; @ia @i
  ia \<le> n \<le> i : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; @ia
  i \<le> ia \<le> n : d@ia ~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; @ia
  *)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule_tac
      x="ia"
      in exI)
   apply(subgoal_tac "dh ia = d ia")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    prefer 2
    apply(subgoal_tac "\<exists>e c. dh ia = Some (pair e c)")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     prefer 2
     apply(rule epdaH.some_position_has_details_before_max_dom)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(erule exE)+
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(subgoal_tac "\<exists>ca'. epdaH_conf_history c @ ca' = epdaH_conf_history cc")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     prefer 2
     apply(case_tac "i\<le>ia")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      prefer 2
      apply(erule_tac
      x="i"
      and P="\<lambda>i. \<forall>e' c'. ia < i \<and> d i = Some (pair e' c') \<longrightarrow> epdaH_conf_history cc = epdaH_conf_history c'"
      in allE)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(subgoal_tac "\<exists>ca'. epdaH_conf_history cb @ ca' = epdaH_conf_history cc")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(rule_tac
      x="ca @ ca'"
      in exI)
      apply(rule_tac
      t="epdaH_conf_history cc"
      and s="epdaH_conf_history cb @ ca'"
      in ssubst)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(rule_tac
      t="epdaH_conf_history cb"
      and s="epdaH_conf_history c @ ca"
      in ssubst)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(simp (no_asm))
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history cc = epdaH_conf_history cb @ h")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in epdaH.steps_extend_history_derivation)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
         apply(simp add: epdaH.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(simp add: epdaH_marking_configurations_def)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(clarsimp)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(erule exE)+
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
    apply(rule_tac
      ?d1.0="dh"
      and n="ia"
      and m="ia"
      and ?d2.0="d"
      and x="0"
      and y="0"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
               apply(force)
              apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
              apply(simp add: epdaH.derivation_initial_def)
             apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
             apply(force)
            apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
            apply(force)
           apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
           apply(force)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(force)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
     apply(simp add: get_configuration_def)
     apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history c = epdaH_conf_history cd @ h")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      prefer 2
      apply(rule_tac
      d="dh"
      and n="ia"
      and m="n-ia"
      in epdaH.steps_extend_history_derivation)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(simp add: epdaH.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply(simp add: epdaH_marking_configurations_def)
        apply(rule epdaH.belongs_configurations)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(rule epdaH.derivation_initial_belongs)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(force)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
     apply(erule bexE)+
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(subgoal_tac "cb \<in> epdaH_configurations M")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(case_tac "ia\<le>i")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(subgoal_tac "epdaH_conf_history cc = epdaH_conf_history cb")
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       prefer 2
       apply(case_tac "ia<i")
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(erule_tac
      x="i"
      and P="\<lambda>i. \<forall>e' c'. ia < i \<and> d i = Some (pair e' c') \<longrightarrow> epdaH_conf_history cc = epdaH_conf_history c'"
      in allE)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(clarsimp)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      x="h@ca"
      in bexI)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(simp add: epda_effects_def)
      apply(simp add: epdaH_configurations_def)
      apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea ia eb cc ec "cd" h x q s)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history cc = epdaH_conf_history cb @ h")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in epdaH.steps_extend_history_derivation)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
         apply(simp add: epdaH.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(simp add: epdaH_marking_configurations_def)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h ha)(*strict*)
     apply(rule_tac
      x="h @ ca @ ha"
      in bexI)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h ha)(*strict*)
      apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h ha)(*strict*)
     apply(simp add: epda_effects_def)
     apply(simp add: epdaH_configurations_def)
     apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea ia eb cc ec "cd" h ha x q s)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history c = epdaH_conf_history cc @ h")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="ia"
      and m="n-ia"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
      apply(simp add: epdaH_marking_configurations_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(erule bexE)+
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
   apply(subgoal_tac "h@ca=[]")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
    prefer 2
    apply(case_tac "ia\<le>i")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     apply(case_tac "ia<i")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
      apply(erule_tac
      x="i"
      and P="\<lambda>i. \<forall>e' c'. ia < i \<and> d i = Some (pair e' c') \<longrightarrow> epdaH_conf_history cc = epdaH_conf_history c'"
      in allE)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
      apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     apply(clarsimp)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
    apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history cc = epdaH_conf_history cb @ h")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     prefer 2
     apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
         apply(force)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
       apply(simp add: epdaH_marking_configurations_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
    apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(erule_tac
      x="j"
      and P="\<lambda>j. \<forall>e' c'. ia < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_conf_history cb = epdaH_conf_history c'"
      in allE)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "j\<le>n")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      in epdaH.allPreMaxDomSome_prime)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history c = epdaH_conf_history c' @ h")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="j"
      and m="n-j"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(simp add: epdaH_marking_configurations_def)
      apply(rule epdaH.belongs_configurations)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history c' = epdaH_conf_history cc @ h")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="ia"
      and m="j-ia"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(simp add: epdaH_marking_configurations_def)
     apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(case_tac "d j")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(clarify)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' h ha)(*strict*)
    apply(simp add: epdaH_string_state_def)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a)(*strict*)
   apply(simp add: epdaH_string_state_def)
   apply(clarify)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a h ha)(*strict*)
   apply(case_tac a)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a h ha option b)(*strict*)
   apply(clarify)
   apply(rule_tac
      ?h2.0="ha"
      and ?h1.0="h"
      in equal_by_mutual_extension)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a h ha option b)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a h ha option b)(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(subgoal_tac "ia>n")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(thin_tac "\<not> ia \<le> n")
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   prefer 2
   apply(rule_tac
      m="ia"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(subgoal_tac "cd \<in> epdaH_configurations M")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(subgoal_tac "c \<in> epdaH_configurations M")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   prefer 2
   apply(rule_tac
      d="dh"
      in epdaH.belongs_configurations)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(subgoal_tac "d n = dh n")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   prefer 2
   apply(rule sym)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule_tac
      ?d1.0="dh"
      and n="n"
      and m="ia"
      and ?d2.0="d"
      and x="0"
      and y="0"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
              apply(force)
             apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
             apply(simp add: epdaH.derivation_initial_def)
            apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
            apply(force)
           apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
           apply(force)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
         apply(simp add: epdaH.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(case_tac "d 0")
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
         apply(clarsimp)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" a)(*strict*)
        apply(clarsimp)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
       apply(case_tac "dh 0")
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(clarsimp)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" a)(*strict*)
       apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    prefer 2
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "ia<i")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(erule_tac
      x="i"
      and P="\<lambda>j. \<forall>e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_string_state cb = epdaH_string_state c'"
      in allE)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="ca"
      in bexI)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(subgoal_tac "cb \<in> epdaH_configurations M")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(subgoal_tac "cc \<in> epdaH_configurations M")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(simp add: epdaH_configurations_def epda_effects_def)
      apply(clarsimp)
      apply(rename_tac M dh n e d ca i ea ia eb ec x q qa qb qc s sa sb sc h ha hc)(*strict*)
      apply(rule_tac
      A="set ca"
      in set_mp)
       apply(rename_tac M dh n e d ca i ea ia eb ec x q qa qb qc s sa sb sc h ha hc)(*strict*)
       apply(force)
      apply(rename_tac M dh n e d ca i ea ia eb ec x q qa qb qc s sa sb sc h ha hc)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply (metis epdaH.belongs_configurations epdaH.derivation_initial_belongs)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply (metis epdaH.belongs_configurations epdaH.derivation_initial_belongs)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(subgoal_tac "i\<le>ia")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>hf\<in> epda_effects M. epdaH_conf_history cc = epdaH_conf_history cb @ hf")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply (metis epdaH.belongs_configurations epdaH.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
   apply(rule_tac
      x="ca@hf"
      in bexI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
   apply(subgoal_tac "cb \<in> epdaH_configurations M")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
    apply(subgoal_tac "cc \<in> epdaH_configurations M")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
     apply(simp add: epdaH_configurations_def epda_effects_def)
     apply(clarsimp)
     apply(rename_tac M dh n e d ca i ea ia eb ec hf x q qa qb qc s sa sb sc h ha)(*strict*)
     apply(rule_tac
      A="set ca"
      in set_mp)
      apply(rename_tac M dh n e d ca i ea ia eb ec hf x q qa qb qc s sa sb sc h ha)(*strict*)
      apply(force)
     apply(rename_tac M dh n e d ca i ea ia eb ec hf x q qa qb qc s sa sb sc h ha)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
    apply (metis epdaH.belongs_configurations epdaH.derivation_initial_belongs)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
   apply (metis epdaH.belongs_configurations epdaH.derivation_initial_belongs)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule_tac
      x="derivation_drop (derivation_take d ia) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule_tac
      m="ia-n"
      in epdaH.derivation_drop_preserves_derivation_prime)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule epdaH.derivation_drop_preserves_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule epdaH.derivation_take_preserves_belongs)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule_tac
      x="ia-n"
      in exI)
   apply(simp add: maximum_of_domain_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_append_fit_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule_tac
      x="ia"
      in exI)
  apply(rule_tac
      x="eb"
      in exI)
  apply(rule_tac
      x="cc"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd" j e' c')(*strict*)
  apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  done

lemma epdaH_inst_BF_BraSBRest_DetHSB_LaOp_axioms: "
  BF_BraSBRest_DetHSB_LaOp_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect
     epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler"
  apply(simp add: BF_BraSBRest_DetHSB_LaOp_axioms_def)
  apply(rule epdaH_inst_AX_BF_BraSBRest_DetHSB_LaOp_axioms)
  done

lemma epdaH_inst_BF_BraSBRest_DetHDB_LaOp_axioms: "
  BF_BraSBRest_DetHDB_LaOp_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect
     epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler_DB
     epdaH_get_fixed_scheduler"
  apply(simp add: BF_BraSBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "epdaH.is_forward_deterministicHist_SB M")
   apply(rename_tac M)(*strict*)
   apply (metis epdaH_inst_AX_BF_BraSBRest_DetHSB_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (epdaH.unmarked_language M) (epdaH.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaH.is_forward_deterministicHist_SB M"
      and s="epdaH.is_forward_deterministicHist_DB M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (rule epdaH.is_forward_deterministic_correspond_DB_SB)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(force)
  done

lemma epdaH_inst_BF_BraDBRest_DetHSB_LaOp_axioms: "
  BF_BraDBRest_DetHSB_LaOp_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect
     epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler
     epdaH_get_fixed_scheduler_DB"
  apply(simp add: BF_BraDBRest_DetHSB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaH.Nonblockingness_branching_restricted_DB M"
      and s="epdaH.Nonblockingness_branching_restricted M"
      in subst)
   apply(rename_tac M)(*strict*)
   apply(rule_tac
      G="M"
      in epdaH.Nonblockingness_branching_SB_DB_restricted)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_BraSBRest_DetHDB_LaOp_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect
     epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler_DB
     epdaH_get_fixed_scheduler")
   apply(rename_tac M)(*strict*)
   apply(simp add: BF_BraSBRest_DetHDB_LaOp_axioms_def)
   apply(erule_tac
      x="M"
      in allE)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(rule_tac
      t="epdaH.is_forward_deterministicHist_DB M"
      and s="epdaH.is_forward_deterministicHist_SB M"
      in subst)
     apply(rename_tac M)(*strict*)
     apply(rule epdaH.is_forward_deterministic_correspond_DB_SB)
     apply(force)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule epdaH_inst_BF_BraSBRest_DetHDB_LaOp_axioms)
  done

lemma epdaH_inst_BF_BraDBRest_DetHDB_LaOp_axioms: "
  BF_BraDBRest_DetHDB_LaOp_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect
     epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler_DB"
  apply(simp add: BF_BraDBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_BraDBRest_DetHSB_LaOp_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect
     epda_effects (@) (@) epdaH_conf_history
     epda_fixed_scheduler_extendable epdaH_get_fixed_scheduler
     epdaH_get_fixed_scheduler_DB")
   apply(rename_tac M)(*strict*)
   apply(simp add: BF_BraDBRest_DetHSB_LaOp_axioms_def)
   apply(erule_tac
      x="M"
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
   apply (metis epdaH.is_forward_deterministic_correspond_DB_SB)
  apply(rename_tac M)(*strict*)
  apply(rule epdaH_inst_BF_BraDBRest_DetHSB_LaOp_axioms)
  done

lemma epdaH_inst_BF_Bra_OpLa_axioms: "
  BF_Bra_OpLa_axioms valid_epda epdaH_configurations
     epdaH_initial_configurations epda_step_labels epdaH_step_relation
     epdaH_marking_condition epdaH_marked_effect epdaH_unmarked_effect"
  apply(simp add: BF_Bra_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: nonblockingness_language_def)
  apply(clarsimp)
  apply(rename_tac M xa)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac M xa d)(*strict*)
  apply(simp add: epdaH.Nonblockingness_branching_def)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M d i e c)(*strict*)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rename_tac M d i e c)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac M d i e c)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac M d i e c)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac M d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac M d i e c dc x)(*strict*)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(rule_tac
      x="epdaH_conf_history ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(simp add: epdaH.marked_language_def)
   apply(rule_tac
      x="derivation_append (derivation_take d i) dc i"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(force)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(rule epdaH.derivation_take_preserves_derivation)
      apply(force)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(simp add: derivation_take_def)
    apply(simp add: derivation_append_fit_def)
    apply(case_tac "dc 0")
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac M d i e c dc x ia ea ca a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
    apply(case_tac option)
     apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac M d i e c dc x ia ea ca option b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(simp add: epdaH_marked_effect_def)
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
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marking_condition_def)
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
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(case_tac "ia<i")
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="c"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_append_def derivation_take_def)
   apply(simp add: epdaH_string_state_def)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(subgoal_tac "\<exists>h\<in> epda_effects M. epdaH_conf_history SSc' = epdaH_conf_history SSc @ h" for SSc' SSc)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_append (derivation_take d i) dc i"
      and n="i"
      and m="ia-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(rule epdaH.derivation_append_preserves_derivation)
        apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
        apply(rule epdaH.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(simp add: derivation_take_def derivation_append_fit_def)
      apply(case_tac "dc 0")
       apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac M d i e c dc x ia ea ca a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac M d i e c dc x ia ea ca a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
      apply(case_tac option)
       apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
       apply(clarsimp)
      apply(rename_tac M d i e c dc x ia ea ca option b a)(*strict*)
      apply(clarsimp)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def derivation_append_def derivation_take_def)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(force)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(force)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def derivation_take_def)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(simp add: epdaH_string_state_def)
  apply(force)
  done

print_locale loc_autHF_10

interpretation "epdaH" : loc_autHF_10
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaH_configurations"
  (* initial_configurations *)
  "epdaH_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaH_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaH_marking_condition"
  (* marked_effect *)
  "epdaH_marked_effect"
  (* unmarked_effect *)
  "epdaH_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaH_get_destinations"
  (* histories *)
  "epda_effects"
  (* history_fragments *)
  "epda_effects"
  (* empty_history *)
  epda_empty_history
  (* empty_history_fragment *)
  epda_empty_history_fragment
  (* set_history *)
  "epdaH_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "epdaH_conf_history"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* get_fixed_scheduler *)
  epdaH_get_fixed_scheduler
  (* get_fixed_scheduler_DB *)
  epdaH_get_fixed_scheduler_DB
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs epdaH_inst_ATS_axioms epdaH_inst_ATS_History_axioms epdaH_inst_ATS_SchedF_Basic_axioms epdaH_inst_ATS_SchedF_SB_axioms epdaH_inst_ATS_SchedF_DB_axioms epdaH_inst_ATS_SchedF_SDB_axioms epdaH_inst_ATS_determHIST_SB_axioms epdaH_inst_ATS_Language_by_Finite_Derivations_axioms epdaH_inst_ATS_HistoryCT_SB_axioms epdaH_inst_ATS_HistoryCT_DB_axioms
      epdaH_inst_BF_BraSBRest_DetHDB_LaOp_axioms epdaH_inst_BF_BraSBRest_DetHSB_LaOp_axioms epdaH_inst_BF_Bra_OpLa_axioms epdaH_inst_BF_BraDBRest_DetHSB_LaOp_axioms epdaH_inst_BF_BraDBRest_DetHDB_LaOp_axioms )
  done

lemma epdaH_history_prefix_makes_prefix: "
  w1 \<in> epda_effects G
  \<Longrightarrow> ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2
  \<Longrightarrow> w1 \<sqsubseteq> w2"
  apply(simp add: epdaH.history_fragment_prefixes_def)
  apply(simp add: prefix_def)
  apply(subgoal_tac "w1 \<in> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1}")
   prefer 2
   apply(clarsimp)
   apply(simp add: epda_effects_def)
  apply(subgoal_tac "w1 \<in> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2}")
   prefer 2
   apply(force)
  apply(thin_tac "{hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1} \<subseteq> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2}")
  apply(thin_tac "w1 \<in> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1}")
  apply(force)
  done

lemma epdaH_history_prefix_makes_prefix_mutual: "
  w1 \<in> epda_effects G
  \<Longrightarrow> w2 \<in> epda_effects G
  \<Longrightarrow> ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w1
  \<Longrightarrow> prefix w1 w2 \<or> prefix w2 w1"
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule epdaH_history_prefix_makes_prefix)
    apply(force)
   apply(force)
  apply(rule disjI2)
  apply(rule epdaH_history_prefix_makes_prefix)
   apply(force)
  apply(force)
  done

lemma epdaH_is_forward_target_deterministicHist_DB_long: "
  valid_epda G
  \<Longrightarrow> epdaH.is_forward_target_deterministicHist_DB_long G"
  apply(simp add: epdaH.is_forward_target_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 n e w1 w2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  done

definition epdaH_accessible_edges :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "epdaH_accessible_edges G \<equiv>
  {e \<in> epda_delta G.
    \<exists>d n c.
    epdaH.derivation_initial G d
    \<and> d n = Some (pair (Some e) c)}"

definition epdaH_required_edges :: "
  ('state, 'event, 'stack)epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "epdaH_required_edges G \<equiv>
  {e \<in> epda_delta G.
    \<exists>d n c.
    epdaH.derivation_initial G d
    \<and> d n = Some (pair (Some e) c)
    \<and> (\<exists>k\<ge>n. \<exists>e c. d k = Some (pair e c) \<and> c \<in> epdaH_marking_configurations G)}"

definition epdaH_non_ambiguous :: "
  ('state, 'event, 'stack)epda
  \<Rightarrow> bool"
  where
    "epdaH_non_ambiguous G \<equiv>
  \<forall>d1 d2 n1 n2 q1 q2 h s1 s2.
  epdaH.derivation_initial G d1
  \<longrightarrow> epdaH.derivation_initial G d2
  \<longrightarrow> get_configuration (d1 n1)
        = Some \<lparr>epdaH_conf_state=q1, epdaH_conf_history=h, epdaH_conf_stack=s1\<rparr>
  \<longrightarrow> get_configuration (d2 n2)
        = Some \<lparr>epdaH_conf_state=q2, epdaH_conf_history=h, epdaH_conf_stack=s2\<rparr>
  \<longrightarrow> q1 \<in> epda_marking G
  \<longrightarrow> q2 \<in> epda_marking G
  \<longrightarrow> (n1=n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i))"

lemma epda_at_most_one_symbol_per_step: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> length(epdaH_conf_history c)\<le>n"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 w)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac e2)
  apply(rename_tac n c e1 e2 c1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 c1 w edge_event edge_pop edge_push)(*strict*)
  apply(case_tac edge_event)
   apply(rename_tac n c e1 c1 w edge_event edge_pop edge_push)(*strict*)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 w edge_pop edge_push)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac n c e1 c1 w edge_event edge_pop edge_push a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 c1 w edge_pop edge_push a)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemmas epdaH_interpretations =
  epdaH_inst_AX_initial_configuration_belongs
  epdaH_inst_AX_step_relation_preserves_belongs
  epdaH_inst_ATS_axioms
  epdaH_inst_ATS_History_axioms
  epdaH_inst_ATS_SchedF_Basic_axioms
  epdaH_inst_ATS_SchedF_SB_axioms
  epdaH_inst_ATS_SchedF_DB_axioms
  epdaH_inst_ATS_SchedF_SDB_axioms
  epdaH_inst_ATS_determHIST_SB_axioms
  epdaH_inst_ATS_Language_by_Finite_Derivations_axioms
  epdaH_inst_ATS_HistoryCT_SB_axioms
  epdaH_inst_ATS_HistoryCT_DB_axioms
  epdaH_inst_BF_BraSBRest_DetHDB_LaOp_axioms
  epdaH_inst_BF_BraSBRest_DetHSB_LaOp_axioms
  epdaH_inst_BF_Bra_OpLa_axioms
  epdaH_inst_BF_BraDBRest_DetHSB_LaOp_axioms
  epdaH_inst_BF_BraDBRest_DetHDB_LaOp_axioms

theorem epdaH_is_forward_target_deterministic_accessible: "
  valid_epda G
  \<Longrightarrow> epdaH.is_forward_target_deterministic_accessible G"
  apply(simp add: epdaH.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e) (*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  done

definition min_stack :: "
  (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> 'stack list
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> 'state option"
  where
    "min_stack d s n nX \<equiv>
  let
    S = {i. \<exists>e c.
            n \<le> i
            \<and> i \<le> nX
            \<and> d i = Some (pair e c)
            \<and> epdaH_conf_stack c = s}
  in
    if S = {}
    then None
    else Some (epdaH_conf_state (the (get_configuration (d (Min S)))))"

definition epdaH_initial_marking_derivations_at_end :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation set"
  where
    "epdaH_initial_marking_derivations_at_end G \<equiv>
  {d. \<exists>n e c.
      epdaH.derivation_initial G d
      \<and> maximum_of_domain d n
      \<and> d n = Some (pair e c)
      \<and> c \<in> epdaH_marking_configurations G}"

definition epdaH_no_livelocks_from_marking_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_no_livelocks_from_marking_states G \<equiv>
  \<forall>d n e c.
  epdaH.derivation_initial G d
  \<and> d n = Some (pair (Some e) c)
  \<and> edge_src e \<in> epda_marking G
  \<and> edge_event e = None
  \<longrightarrow> (\<exists>m>n.
        d m = None
        \<or> (\<exists>e' c'.
            d m = Some (pair (Some e') c')
            \<and> edge_event e' \<noteq> None))"

definition epdaH_livelock :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_livelock G \<equiv>
  \<exists>d.
  epdaH.derivation_initial G d
  \<and> (\<forall>n. d n \<noteq> None)
  \<and> (\<exists>N. \<forall>n\<ge>N.
      epdaH_conf_history (the(get_configuration(d n)))
      = epdaH_conf_history (the(get_configuration(d N))))"

lemma epda_sub_preserves_derivation: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> epdaH.derivation G1 d
  \<Longrightarrow> epdaH.derivation G2 d"
  apply(simp (no_asm) add: epdaH.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(simp add: epdaH.derivation_def)
   apply(clarsimp)
   apply(erule_tac
      x = "0"
      in allE)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(case_tac "d(Suc nat)")
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i nat a)(*strict*)
   prefer 2
   apply(rule_tac
      n = "nat"
      and m = "Suc nat"
      and G = "G1"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i nat a)(*strict*)
     apply(force)
    apply(rename_tac i nat a)(*strict*)
    apply(force)
   apply(rename_tac i nat a)(*strict*)
   apply(force)
  apply(rename_tac i nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaH_step_relation_def epda_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(force)
  done

lemma epda_sub_preserves_derivation_initial: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> epdaH.derivation_initial G1 d
  \<Longrightarrow> epdaH.derivation_initial G2 d"
  apply(subgoal_tac "epdaH.derivation G2 d")
   prefer 2
   apply(rule epda_sub_preserves_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: epdaH.derivation_initial_def)
  apply(simp add: epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def epda_sub_def)
  apply(clarsimp)
  apply(force)
  done

lemma epda_sub_preserves_not_livelock: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> \<not> epdaH_livelock G2
  \<Longrightarrow> \<not> epdaH_livelock G1"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d N)(*strict*)
   apply(rule_tac
      ?G1.0="G1"
      in epda_sub_preserves_derivation_initial)
      apply(rename_tac d N)(*strict*)
      apply(force)
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
   apply(erule_tac
      x="n"
      in allE)
   apply(force)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  done

lemma valid_epda__no_livelock__implies__epdaH_no_livelocks_from_marking_states: "
   valid_epda G
   \<Longrightarrow> \<not> epdaH_livelock G
   \<Longrightarrow> epdaH_no_livelocks_from_marking_states G"
  apply(simp add: epdaH_no_livelocks_from_marking_states_def epdaH_livelock_def)
  apply(clarsimp)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(subgoal_tac "n<na")
    apply(force)
   apply (metis epdaH.derivationNoFromNone2_prime epdaH.derivation_initial_is_derivation is_none_code(1) is_none_code(2) nat_neq_iff)
  apply(erule_tac x="n" in allE)
  apply(clarsimp)
  apply(case_tac "n=na")
   apply(force)
  apply(subgoal_tac "n<na")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac P="%na. n<na \<and> epdaH_conf_history (the (get_configuration (d na))) \<noteq>
       epdaH_conf_history (the (get_configuration (Some (pair (Some e) c))))" and n="na" in ex_least_nat_le_prime)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "epdaH_conf_history (the (get_configuration (d na))) \<noteq>
       epdaH_conf_history (the (get_configuration (Some (pair (Some e) c))))")
  apply(thin_tac "k \<le> na")
  apply(thin_tac "edge_src e \<in> epda_marking G")
  apply(thin_tac "edge_event e = None")
  apply(case_tac k)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac k)
  apply(erule_tac x="k" in allE)
  apply(clarsimp)
  apply(rule_tac x="Suc k" in exI)
  apply(clarsimp)
  apply(case_tac "d (Suc k)")
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac a)
  apply(clarsimp)
  apply(rename_tac ex cx)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="k" and m="Suc k" in epdaH.step_detail_before_some_position)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaH_step_relation_def option_to_list_def)
  apply(clarsimp)
  apply(case_tac "n=k")
   apply(clarsimp)
  apply(clarsimp)
  done

lemma epdaH_epda_box_stays_at_bottom: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> suffix (epdaH_conf_stack c) [epda_box G]"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def suffix_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d"
      and n = "n"
      and m = "Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def suffix_def)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x = "e2"
      in ballE)
   apply(rename_tac n c e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac n c e1 e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n c e1 e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stacka epdaH_conf_statea epdaH_conf_historya epdaH_conf_stackaa)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n c e1 e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stacka epdaH_conf_statea epdaH_conf_historya epdaH_conf_stackaa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(simp add: epdaH_step_relation_def may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def suffix_def)
  apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
  apply(erule disjE)+
    apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
    apply(rule_tac
      xs = "w"
      in rev_cases)
     apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
     apply(clarsimp)
    apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
  apply(erule disjE)+
   apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
   apply(clarsimp)+
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
  apply(rule_tac
      xs = "w"
      in rev_cases)
   apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w ys y)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_epda_box_stays_at_bottom2: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>w. epdaH_conf_stack c = w @ [epda_box G] \<and> set w \<subseteq> epda_gamma G - {epda_box G}"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def suffix_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d"
      and n = "n"
      and m = "Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def suffix_def)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x = "e2"
      in ballE)
   apply(rename_tac n c e1 e2 c1 w)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def)
  apply(rename_tac n c e1 e2 c1 w)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac n c e1 e2 c1 w epdaH_conf_state epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n c e1 e2 c1 w epdaH_conf_state epdaH_conf_history epdaH_conf_stacka epdaH_conf_statea epdaH_conf_historya epdaH_conf_stackaa)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n c e1 e2 c1 w epdaH_conf_state epdaH_conf_history epdaH_conf_stacka epdaH_conf_statea epdaH_conf_historya epdaH_conf_stackaa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(simp add: epdaH_step_relation_def may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def suffix_def)
  apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
  apply(erule disjE)+
    apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
    apply(rule_tac
      xs = "w"
      in rev_cases)
     apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
     apply(clarsimp)
    apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
  apply(erule disjE)+
   apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg c a aa w)(*strict*)
   apply(clarsimp)+
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
  apply(rule_tac
      xs = "w"
      in rev_cases)
   apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 epdaH_conf_historya edge_src edge_event edge_trg c a aa w ys y)(*strict*)
  apply(clarsimp)
  done

definition epdaH_step_relation_explicit1 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "epdaH_step_relation_explicit1 G c1 e c2 \<equiv>
  \<exists>q1 q2 h s1 s2 s.
     c1 = \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1 @ s @ [epda_box G]\<rparr>
    \<and> e = \<lparr>edge_src = q1, edge_event = None, edge_pop = s1, edge_push = s2, edge_trg = q2\<rparr>
    \<and> c2 = \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2 @ s @ [epda_box G]\<rparr>
    \<and> set (s1 @ s2 @ s) \<subseteq> epda_gamma G - {epda_box G}"

definition epdaH_step_relation_explicit2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "epdaH_step_relation_explicit2 G c1 e c2 \<equiv>
  \<exists>q1 q2 h s1 s2 s.
     c1 = \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1 @ [epda_box G]\<rparr>
    \<and> e = \<lparr>edge_src = q1, edge_event = None, edge_pop = s1 @ [epda_box G], edge_push = s2 @ [epda_box G], edge_trg = q2\<rparr>
    \<and> c2 = \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2 @ [epda_box G]\<rparr>
    \<and> set (s1 @ s2 @ s) \<subseteq> epda_gamma G - {epda_box G}"

definition epdaH_step_relation_explicit3 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "epdaH_step_relation_explicit3 G c1 e c2 \<equiv>
  \<exists>q1 q2 h s1 s2 s a.
     c1 = \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1 @ s @ [epda_box G]\<rparr>
    \<and> e = \<lparr>edge_src = q1, edge_event = Some a, edge_pop = s1, edge_push = s2, edge_trg = q2\<rparr>
    \<and> c2 = \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h @ [a], epdaH_conf_stack = s2 @ s @ [epda_box G]\<rparr>
    \<and> set (s1 @ s2 @ s) \<subseteq> epda_gamma G - {epda_box G}"

definition epdaH_step_relation_explicit4 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "epdaH_step_relation_explicit4 G c1 e c2 \<equiv>
  \<exists>q1 q2 h s1 s2 s a.
     c1 = \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1 @ [epda_box G]\<rparr>
    \<and> e = \<lparr>edge_src = q1, edge_event = Some a, edge_pop = s1 @ [epda_box G], edge_push = s2 @ [epda_box G], edge_trg = q2\<rparr>
    \<and> c2 = \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h @ [a], epdaH_conf_stack = s2 @ [epda_box G]\<rparr>
    \<and> set (s1 @ s2 @ s) \<subseteq> epda_gamma G - {epda_box G}"

definition epdaH_step_relation_explicit :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaH_conf
  \<Rightarrow> bool"
  where
    "epdaH_step_relation_explicit G c1 e c2 \<equiv>
  e \<in> epda_delta G
  \<and> (
      epdaH_step_relation_explicit1 G c1 e c2
    \<or> epdaH_step_relation_explicit2 G c1 e c2
    \<or> epdaH_step_relation_explicit3 G c1 e c2
    \<or> epdaH_step_relation_explicit4 G c1 e c2
  )"

lemma epdaH_step_relation_explicit1__intro: "
  epdaH_step_relation_explicit1 G c1 e c2
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> epdaH_step_relation_explicit G c1 e c2"
  apply(simp add: epdaH_step_relation_explicit_def)
  done

lemma epdaH_step_relation_explicit2__intro: "
  epdaH_step_relation_explicit2 G c1 e c2
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> epdaH_step_relation_explicit G c1 e c2"
  apply(simp add: epdaH_step_relation_explicit_def)
  done

lemma epdaH_step_relation_explicit3__intro: "
  epdaH_step_relation_explicit3 G c1 e c2
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> epdaH_step_relation_explicit G c1 e c2"
  apply(simp add: epdaH_step_relation_explicit_def)
  done

lemma epdaH_step_relation_explicit4__intro: "
  epdaH_step_relation_explicit4 G c1 e c2
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> epdaH_step_relation_explicit G c1 e c2"
  apply(simp add: epdaH_step_relation_explicit_def)
  done

lemma epdaH_step_relation__vs__epdaH_step_relation_explicit: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair ex c1)
  \<Longrightarrow> epdaH_step_relation G c1 e c2 = epdaH_step_relation_explicit G c1 e c2"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule epdaH_epda_box_stays_at_bottom2)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "c1 \<in> epdaH_configurations G")
   prefer 2
   apply (metis (full_types) epdaH.derivation_initial_configurations) 
  apply(rule antisym)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(subgoal_tac "valid_epda_step_label G e")
    prefer 2
    apply(simp add: valid_epda_def)
   apply(subgoal_tac "c2 \<in> epdaH_configurations G")
    prefer 2
    apply (metis (erased, hide_lams) epdaH_inst_AX_step_relation_preserves_belongs epdaH_step_relation_def)  
   apply(case_tac c1)
   apply(case_tac c2)
   apply(clarsimp)
   apply(rename_tac h)
   apply(case_tac e)
   apply(rename_tac q1 x w1 w2 q2)
   apply(clarsimp)
   apply(case_tac x)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(case_tac "\<exists>w. w1=w@[epda_box G]")
     prefer 2
     apply(rule epdaH_step_relation_explicit1__intro)
      apply(simp add: epdaH_step_relation_explicit1_def)
      apply(rule_tac xs="wa" in rev_cases)
       apply(clarsimp)
      apply(clarsimp)
      apply(simp add: valid_epda_step_label_def epdaH_configurations_def)
      apply(clarsimp)
      apply(simp add: may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def)
      apply(clarsimp)        
      apply(force)
     apply(force)
    apply(rule epdaH_step_relation_explicit2__intro)
     apply(simp add: epdaH_step_relation_explicit2_def)
     apply(rule_tac xs="wa" in rev_cases)
      prefer 2
      apply(clarsimp)
     apply(clarsimp)
     apply(simp add: valid_epda_step_label_def epdaH_configurations_def)
     apply(clarsimp)
     apply(simp add: may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def)
     apply(clarsimp)        
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac "\<exists>w. w1=w@[epda_box G]")
    prefer 2
    apply(rule epdaH_step_relation_explicit3__intro)
     apply(simp add: epdaH_step_relation_explicit3_def)
     apply(rule_tac xs="wa" in rev_cases)
      apply(clarsimp)
     apply(clarsimp)
     apply(simp add: valid_epda_step_label_def epdaH_configurations_def)
     apply(clarsimp)
     apply(simp add: may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def)
     apply(clarsimp)        
     apply(force)
    apply(force)
   apply(rule epdaH_step_relation_explicit4__intro)
    apply(simp add: epdaH_step_relation_explicit4_def)
    apply(rule_tac xs="wa" in rev_cases)
     prefer 2
     apply(clarsimp)
    apply(clarsimp)
    apply(simp add: valid_epda_step_label_def epdaH_configurations_def)
    apply(clarsimp)
    apply(simp add: may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def)
    apply(clarsimp)        
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_explicit_def)
  apply(clarsimp)
  apply(subgoal_tac "valid_epda_step_label G e")
   prefer 2
   apply(simp add: valid_epda_def)
  apply(case_tac c1)
  apply(rename_tac q1 h1 s1)
  apply(case_tac c2)
  apply(rename_tac q2 h2 s2)
  apply(clarsimp)
  apply(case_tac e)
  apply(rename_tac qS x w1 w2 qT)
  apply(clarsimp)
  apply(erule disjE)
   apply(simp add: epdaH_step_relation_explicit1_def epdaH_step_relation_def option_to_list_def)
   apply(clarsimp)
  apply(erule disjE)
   apply(simp add: epdaH_step_relation_explicit2_def epdaH_step_relation_def option_to_list_def)
   apply(clarsimp)
  apply(erule disjE)
   apply(simp add: epdaH_step_relation_explicit3_def epdaH_step_relation_def option_to_list_def)
   apply(clarsimp)
  apply(simp add: epdaH_step_relation_explicit4_def epdaH_step_relation_def option_to_list_def)
  apply(clarsimp)
  done 

end
