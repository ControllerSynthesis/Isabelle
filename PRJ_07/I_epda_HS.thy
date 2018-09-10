section {*I\_epda\_HS*}
theory
  I_epda_HS

imports
  I_epda_base

begin

record ('state, 'event, 'stack) epdaHS_conf =
  epdaHS_conf_state :: "'state"
  epdaHS_conf_history :: "'event list"
  epdaHS_conf_scheduler :: "'event list"
  epdaHS_conf_stack :: "'stack list"

definition epdaHS_get_fixed_scheduler :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list"
  where
    "epdaHS_get_fixed_scheduler c \<equiv>
  []"
declare epdaHS_get_fixed_scheduler_def [simp add]

definition epdaHS_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf set"
  where
    "epdaHS_configurations G \<equiv>
  {\<lparr>epdaHS_conf_state = q, epdaHS_conf_history = h, epdaHS_conf_scheduler = i, epdaHS_conf_stack = s\<rparr> |
  q h i s.
  q \<in> epda_states G
  \<and> set i \<subseteq> epda_events G
  \<and> set h \<subseteq> epda_events G
  \<and> set s \<subseteq> epda_gamma G}"

definition epdaHS_initial_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf set"
  where
    "epdaHS_initial_configurations G \<equiv>
  {c.
    epdaHS_conf_state c = epda_initial G
    \<and> epdaHS_conf_history c=[]
    \<and> epdaHS_conf_stack c = [epda_box G]}
  \<inter> epdaHS_configurations G"

definition epdaHS_marking_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf set"
  where
    "epdaHS_marking_configurations G \<equiv>
  {c. epdaHS_conf_scheduler c = []
      \<and> epdaHS_conf_state c \<in> epda_marking G}
  \<inter> epdaHS_configurations G"

definition epdaHS_marking_condition :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> bool"
  where
    "epdaHS_marking_condition G d \<equiv>
  \<exists>i e c.
  d i = Some (pair e c)
  \<and> c \<in> epdaHS_marking_configurations G"

definition epdaHS_string_state :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list"
  where
    "epdaHS_string_state c \<equiv>
  epdaHS_conf_scheduler c"

definition epdaHS_step_relation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> bool"
  where
    "epdaHS_step_relation G c1 e c2 \<equiv>
  e \<in> epda_delta G
  \<and> epdaHS_conf_state c1 = edge_src e
  \<and> epdaHS_conf_state c2 = edge_trg e
  \<and> epdaHS_conf_scheduler c1
      = option_to_list (edge_event e) @ epdaHS_conf_scheduler c2
  \<and> epdaHS_conf_history c2
      = epdaHS_conf_history c1 @ option_to_list (edge_event e)
  \<and> (\<exists>w.
      epdaHS_conf_stack c1 = edge_pop e @ w
      \<and> epdaHS_conf_stack c2 = edge_push e @ w)"

definition epdaHS_get_destinations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation_configuration
  \<Rightarrow> ('state, 'event, 'stack) epda_destinations set"
  where
    "epdaHS_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    {state (epdaHS_conf_state c)}
    \<union> (case e of None \<Rightarrow> {} | Some e'\<Rightarrow> {edge e'})"

definition epdaHS_marked_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> 'event list set"
  where
    "epdaHS_marked_effect G d \<equiv>
  {w. \<exists>c. d 0 = Some (pair None c)
          \<and> w = epdaHS_conf_scheduler c}"

definition epdaHS_unmarked_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> 'event list set"
  where
    "epdaHS_unmarked_effect G d \<equiv>
  {w. \<exists>c c' i e.
      d 0 = Some (pair None c)
      \<and> d i = Some (pair e c')
      \<and> w @ epdaHS_conf_scheduler c' = epdaHS_conf_scheduler c}"

definition epdaHS_marked_configuration_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list set"
  where
    "epdaHS_marked_configuration_effect G c \<equiv>
  {epdaHS_conf_history c}"

definition epdaHS_unmarked_configuration_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list set"
  where
    "epdaHS_unmarked_configuration_effect G c \<equiv>
  {epdaHS_conf_history c}"

lemma epdaHS_inst_AX_initial_configuration_belongs: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaHS_initial_configurations G \<subseteq> epdaHS_configurations G)"
  apply(simp add: epdaHS_initial_configurations_def)
  done

lemma epdaHS_inst_AX_step_relation_preserves_belongs: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1 e c2. epdaHS_step_relation G c1 e c2 \<longrightarrow> c1 \<in> epdaHS_configurations G \<longrightarrow> e \<in> epda_step_labels G \<and> c2 \<in> epdaHS_configurations G))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2) (*strict*)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac G c1 e c2) (*strict*)
   prefer 2
   apply(simp add: epdaHS_step_relation_def)
  apply(rename_tac G c1 e c2) (*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: epdaHS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w) (*strict*)
  apply(simp add: epda_step_labels_def)
  apply(simp add: epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2 w h) (*strict*)
  apply(case_tac c2)
  apply(rename_tac G e c2 w h epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka) (*strict*)
  apply(clarsimp)
  apply(rename_tac G e w h epdaHS_conf_scheduler x) (*strict*)
  apply(simp add: option_to_set_def option_to_list_def)
  apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac G e w h epdaHS_conf_scheduler x a aa) (*strict*)
  apply(erule_tac
      P="edge_push e = aa @ [epda_box G]"
      in disjE)
   apply(rename_tac G e w h epdaHS_conf_scheduler x a aa) (*strict*)
   apply(clarsimp)
   apply(blast)
  apply(rename_tac G e w h epdaHS_conf_scheduler x a aa) (*strict*)
  apply(clarsimp)
  apply(rename_tac G e w h epdaHS_conf_scheduler x a) (*strict*)
  apply(blast)
  done

interpretation "epdaHS" : loc_autHFS_0
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  done

lemma epdaHS_inst_AX_effect_inclusion1: "
  (\<forall>M f. epdaHS_marking_condition M f \<longrightarrow> epdaHS_marked_effect M f \<subseteq> epdaHS_unmarked_effect M f)"
  apply(clarsimp)
  apply(rename_tac M f x) (*strict*)
  apply(simp add: epdaHS_marking_condition_def epdaHS_unmarked_effect_def epdaHS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i c e ca) (*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(simp add: epdaHS_marking_configurations_def)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  done

lemma epdaHS_ins_lang_sound: "
  (\<forall>M. valid_epda M \<longrightarrow> epdaHS.unmarked_language M \<subseteq> epda_effects M)"
  apply(clarsimp)
  apply(rename_tac M x) (*strict*)
  apply(simp add: epdaHS.unmarked_language_def epdaHS_unmarked_effect_def epda_effects_def)
  apply(clarsimp)
  apply(rename_tac M x xa d c c' i e) (*strict*)
  apply(subgoal_tac "c \<in> epdaHS_configurations M")
   apply(rename_tac M x xa d c c' i e) (*strict*)
   apply(simp add: epdaHS_configurations_def)
   apply(clarsimp)
   apply(rename_tac M x xa d c' i e q h s) (*strict*)
   apply(force)
  apply(rename_tac M x xa d c c' i e) (*strict*)
  apply(rule epdaHS.belongs_configurations)
   apply(rename_tac M x xa d c c' i e) (*strict*)
   apply(rule epdaHS.derivation_initial_belongs)
    apply(rename_tac M x xa d c c' i e) (*strict*)
    apply(force)
   apply(rename_tac M x xa d c c' i e) (*strict*)
   apply(force)
  apply(rename_tac M x xa d c c' i e) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_epda M \<longrightarrow> (\<forall>f. epdaHS.derivation_initial M f \<longrightarrow> epdaHS_marking_condition M f \<longrightarrow> epdaHS_marked_effect M f \<noteq> {}))"
  apply(simp add: epdaHS_marking_condition_def epdaHS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i e c) (*strict*)
  apply (metis epdaHS.derivation_initial_is_derivation epdaHS.some_position_has_details_at_0)
  done

lemma epdaHS_inst_AX_unmarked_effect_persists: "
   (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial epdaHS_initial_configurations
               epdaHS_step_relation G d \<longrightarrow>
              (\<forall>n. epdaHS_unmarked_effect G (derivation_take d n)
                   \<subseteq> epdaHS_unmarked_effect G d)))"
  apply(clarsimp)
  apply(rename_tac M d n x) (*strict*)
  apply(simp add: epdaHS_unmarked_effect_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac M d n x c c' i e) (*strict*)
  apply(rule_tac
      x="c'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(case_tac "i\<le>n")
   apply(rename_tac M d n x c c' i e) (*strict*)
   apply(clarsimp)
  apply(rename_tac M d n x c c' i e) (*strict*)
  apply(clarsimp)
  done

lemma epdaHS_inst_ATS_Language_axioms: "
  ATS_Language_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects epdaHS_marking_condition
     epdaHS_marked_effect epdaHS_unmarked_effect "
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: epdaHS_inst_AX_effect_inclusion1 epdaHS_ins_lang_sound epdaHS_inst_AX_marking_condition_implies_existence_of_effect epdaHS_inst_AX_unmarked_effect_persists )
  done

interpretation "epdaHS" : loc_autHFS_1
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms )
  done

lemma epdaHS_inst_AX_initial_history_empty: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_initial_configurations G \<longrightarrow> epdaHS_conf_history c = []))"
  apply(simp add: epdaHS_initial_configurations_def)
  done

lemma epdaHS_inst_AX_steps_extend_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> (\<forall>e c'. epdaHS_step_relation G c e c' \<longrightarrow> (\<exists>hf\<in> epda_effects G. epdaHS_conf_history c' = epdaHS_conf_history c @ hf))))"
  apply(clarsimp)
  apply(rename_tac G c e c') (*strict*)
  apply(subgoal_tac "SSe \<in> epda_step_labels SSG \<and> SSc2 \<in> epdaHS_configurations SSG" for SSe SSc2 SSG)
   apply(rename_tac G c e c') (*strict*)
   prefer 2
   apply(rule epdaHS.AX_step_relation_preserves_belongs)
     apply(rename_tac G c e c') (*strict*)
     apply(force)
    apply(rename_tac G c e c') (*strict*)
    apply(force)
   apply(rename_tac G c e c') (*strict*)
   apply(force)
  apply(rename_tac G c e c') (*strict*)
  apply(clarsimp)
  apply(simp add: epdaHS_step_relation_def epda_effects_def epda_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x w) (*strict*)
  apply(subgoal_tac "valid_epda_step_label G e")
   apply(rename_tac G c e c' x w) (*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac G c e c' x w) (*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: option_to_set_def option_to_list_def)
  apply (metis option_to_set_def only_some_in_option_to_set_prime subsetE)
  done

lemma epdaX_inst_AX_empty_history_is_history: "
  (\<forall>G. valid_epda G \<longrightarrow> [] \<in> epda_effects G)"
  apply(simp add: epda_effects_def)
  done

definition epdaHS_set_history :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf"
  where
    "epdaHS_set_history c sUF \<equiv>
  c\<lparr>epdaHS_conf_history:=sUF\<rparr>"

lemma epdaHS_inst_AX_set_get_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> epdaHS_set_history c (epdaHS_conf_history c) = c))"
  apply(clarsimp)
  apply(rename_tac G c) (*strict*)
  apply(simp add: epdaHS_set_history_def)
  done

lemma epdaHS_inst_AX_get_set_history: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> (\<forall>h. h \<in> epda_effects G \<longrightarrow> epdaHS_conf_history (epdaHS_set_history c h) = h)))"
  apply(clarsimp)
  apply(rename_tac G c h) (*strict*)
  apply(simp add: epdaHS_set_history_def)
  done

lemma epdaHS_inst_AX_join_history_fragments_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>hf1. hf1 \<in> epda_effects G \<longrightarrow> (\<forall>hf2. hf2 \<in> epda_effects G \<longrightarrow> hf1 @ hf2 \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2) (*strict*)
  apply(simp add: epda_effects_def)
  done

lemma epdaHS_inst_AX_get_history_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> epdaHS_conf_history c \<in> epda_effects G))"
  apply(clarsimp)
  apply(rename_tac G c) (*strict*)
  apply(simp add: epda_effects_def epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G x q h i s) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_AX_mutual_prefix: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>hf1. hf1 \<in> epda_effects G \<longrightarrow> (\<forall>hf2. hf2 \<in> epda_effects G \<longrightarrow> (\<forall>hf3. hf3 \<in> epda_effects G \<longrightarrow> (\<forall>hf4. hf4 \<in> epda_effects G \<longrightarrow> hf1 @ hf2 = hf3 @ hf4 \<longrightarrow> (\<exists>hf\<in> epda_effects G. hf1 @ hf = hf3) \<or> (\<exists>hf\<in> epda_effects G. hf3 @ hf = hf1))))))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4) (*strict*)
  apply(simp add: epda_effects_def epdaHS_configurations_def)
  apply(subgoal_tac "prefix hf1 hf3 \<or> prefix hf3 hf1")
   apply(rename_tac G hf1 hf2 hf3 hf4) (*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac G hf1 hf2 hf3 hf4) (*strict*)
  apply(erule disjE)
   apply(rename_tac G hf1 hf2 hf3 hf4) (*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4) (*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G hf2 hf3 c) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_ATS_History_axioms: "
  ATS_History_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epdaHS_step_relation epda_effects
     epda_effects epda_empty_history epda_empty_history_fragment
     epdaHS_set_history (@) (@) epdaHS_conf_history"
  apply(simp add: ATS_History_axioms_def)
  apply(simp add: epdaHS_inst_AX_mutual_prefix epdaHS_inst_AX_initial_history_empty epdaHS_inst_AX_steps_extend_history epdaX_inst_AX_empty_history_is_history epdaHS_inst_AX_set_get_history epdaHS_inst_AX_get_set_history epdaHS_inst_AX_join_history_fragments_closed epdaHS_inst_AX_get_history_closed )
  done

interpretation "epdaHS" : loc_autHFS_2
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms )
  done

lemma epdaHS_inst_AX_string_state_decreases: "
  \<forall>G. valid_epda G \<longrightarrow>
        (\<forall>c1. c1 \<in> epdaHS_configurations G \<longrightarrow>
              (\<forall>e c2. epdaHS_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. epdaHS_string_state c1 =
                           w @ epdaHS_string_state c2)))"
  apply(clarsimp)
  apply(rename_tac M e c1 c2) (*strict*)
  apply(simp add: epdaHS_string_state_def epdaHS_step_relation_def)
  done

lemma epdaHS_inst_AX_marking_can_not_be_disabled: "
  (\<forall>G d. (\<exists>n. epdaHS_marking_condition G (derivation_take d n)) \<longrightarrow> epdaHS_marking_condition G d)"
  apply(clarsimp)
  apply(rename_tac G d n) (*strict*)
  apply(simp add: epdaHS_marking_condition_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n i e c) (*strict*)
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
   apply(rename_tac G d n i e c) (*strict*)
   apply(force) +
  done

lemma epdaHS_inst_AX_marked_effect_persists: "
  (\<forall>G d n. epdaHS_marked_effect G (derivation_take d n) \<subseteq> epdaHS_marked_effect G d)"
  apply(clarsimp)
  apply(rename_tac G d n x) (*strict*)
  apply(simp add: epdaHS_marked_effect_def derivation_take_def)
  done

lemma epdaHS_inst_lang_finite: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaHS.finite_marked_language G = epdaHS.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(simp add: epdaHS.finite_marked_language_def epdaHS.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G) (*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n) (*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaHS.derivation_initial_def)
  apply(rename_tac G) (*strict*)
  apply(clarsimp)
  apply(rename_tac G x d) (*strict*)
  apply(simp add: epdaHS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d c) (*strict*)
  apply(simp add: epdaHS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G d c i e ca) (*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d c i e ca) (*strict*)
   apply(rule epdaHS.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d c i e ca) (*strict*)
  apply(rule conjI)
   apply(rename_tac G d c i e ca) (*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d c i e ca) (*strict*)
  apply(rule conjI)
   apply(rename_tac G d c i e ca) (*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="ca"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d c i e ca) (*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma epdaHS_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaHS.finite_unmarked_language G = epdaHS.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(simp add: epdaHS.finite_unmarked_language_def epdaHS.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G) (*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n) (*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaHS.derivation_initial_def)
  apply(rename_tac G) (*strict*)
  apply(clarsimp)
  apply(rename_tac G x d) (*strict*)
  apply(simp add: epdaHS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G x d c c' i e) (*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G x d c c' i e) (*strict*)
   apply(rule epdaHS.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G x d c c' i e) (*strict*)
  apply(rule conjI)
   apply(rename_tac G x d c c' i e) (*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G x d c c' i e) (*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G x d c c' i e) (*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G x d c c' i e) (*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="e"
      in exI)
    apply(simp add: derivation_take_def)
   apply(rename_tac G x d c c' i e) (*strict*)
   apply(force)
  apply(rename_tac G x d c c' i e) (*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma epdaHS_inst_accept: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> epdaHS_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> epdaHS_marking_configurations G))"
  apply(clarsimp)
  apply(rename_tac G d) (*strict*)
  apply(simp add: epdaHS_marking_condition_def)
  done

lemma epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_epda
     epdaHS_initial_configurations epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect "
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: epdaHS_inst_lang_finite epdaHS_inst_AX_unmarked_language_finite )
  done

lemma epdaHS_change_of_history_and_scheduler: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> d n = Some (pair en cn)
  \<Longrightarrow> d (n+m) = Some (pair em cm)
  \<Longrightarrow> epdaHS_conf_history cn@epdaHS_conf_scheduler cn = epdaHS_conf_history cm@epdaHS_conf_scheduler cm"
  apply(induct m arbitrary: em cm)
   apply(rename_tac em cm)(*strict*)
   apply(clarsimp)
  apply(rename_tac m em cm)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (n+m) = Some (pair e1 c1) \<and> SSd (Suc SSx) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2" for SSd SSx)
   apply(rename_tac m em cm)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(n+m)"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac m em cm)(*strict*)
     apply(force)
    apply(rename_tac m em cm)(*strict*)
    apply(force)
   apply(rename_tac m em cm)(*strict*)
   apply(force)
  apply(rename_tac m em cm)(*strict*)
  apply(clarsimp)
  apply(rename_tac m cm e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaHS_step_relation_def)
  done

lemma epdaHS_inst_AX_marked_configuration_effect_coincides_with_marked_effect: "
(\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial epdaHS_initial_configurations
               epdaHS_step_relation G d \<longrightarrow>
              (\<exists>n. epdaHS_marking_condition G
                    (derivation_take d n)) \<longrightarrow>
              epdaHS_marked_effect G d =
              \<Union>{epdaHS_marked_configuration_effect G c |c.
                 (\<exists>i e. d i = Some (pair e c)) \<and>
                 c \<in> epdaHS_marking_configurations G}))"
  apply(clarsimp)
  apply(rename_tac G d n)(*strict*)
  apply(rule antisym)
   apply(rename_tac G d n)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n x)(*strict*)
   apply(simp add: epdaHS_marked_effect_def epdaHS_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac G d n i c e ca)(*strict*)
   apply(rule_tac
      x="epdaHS_marked_configuration_effect G ca"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d n i c e ca)(*strict*)
    apply(rule_tac
      x="ca"
      in exI)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
    apply(case_tac "i\<le>n")
     apply(rename_tac G d n i c e ca)(*strict*)
     apply(force)
    apply(rename_tac G d n i c e ca)(*strict*)
    apply(force)
   apply(rename_tac G d n i c e ca)(*strict*)
   apply(simp add: epdaHS_marked_configuration_effect_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac G d n i c e ca)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and G="G"
      and n="0"
      and m="i"
      in epdaHS_change_of_history_and_scheduler)
       apply(rename_tac G d n i c e ca)(*strict*)
       apply(force)
      apply(rename_tac G d n i c e ca)(*strict*)
      apply(simp add: epdaHS.derivation_initial_def)
     apply(rename_tac G d n i c e ca)(*strict*)
     apply(force)
    apply(rename_tac G d n i c e ca)(*strict*)
    apply(simp add: derivation_take_def)
    apply(case_tac "i\<le>n")
     apply(rename_tac G d n i c e ca)(*strict*)
     apply(force)
    apply(rename_tac G d n i c e ca)(*strict*)
    apply(force)
   apply(rename_tac G d n i c e ca)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def epdaHS_marking_configurations_def)
  apply(rename_tac G d n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n x c i e)(*strict*)
  apply(simp add: epdaHS_marked_configuration_effect_def epdaHS_marked_effect_def epdaHS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n c i e)(*strict*)
  apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def epdaHS_marking_configurations_def)
  apply(case_tac "d 0")
   apply(rename_tac G d n c i e)(*strict*)
   apply(force)
  apply(rename_tac G d n c i e a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G d n c i e a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n c i e conf)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G d n c i e conf)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and G="G"
      and n="0"
      and m="i"
      in epdaHS_change_of_history_and_scheduler)
      apply(rename_tac G d n c i e conf)(*strict*)
      apply(force)
     apply(rename_tac G d n c i e conf)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
    apply(rename_tac G d n c i e conf)(*strict*)
    apply(force)
   apply(rename_tac G d n c i e conf)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n c i e conf)(*strict*)
  apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def epdaHS_marking_configurations_def)
  done

lemma epdaHS_inst_AX_unmarked_configuration_effect_coincides_with_unmarked_effect: "
   (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial epdaHS_initial_configurations
               epdaHS_step_relation G d \<longrightarrow>
              epdaHS_unmarked_effect G d =
              \<Union>{epdaHS_unmarked_configuration_effect G c |c.
                 \<exists>i e. d i = Some (pair e c)}))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(rule antisym)
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d x)(*strict*)
   apply(simp add: epdaHS_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac G d x c c' i e)(*strict*)
   apply(rule_tac
      x="epdaHS_unmarked_configuration_effect G c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d x c c' i e)(*strict*)
    apply(rule_tac
      x="c'"
      in exI)
    apply(clarsimp)
    apply(force)
   apply(rename_tac G d x c c' i e)(*strict*)
   apply(simp add: epdaHS_unmarked_configuration_effect_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac G d x c c' i e)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and G="G"
      and n="0"
      and m="i"
      in epdaHS_change_of_history_and_scheduler)
       apply(rename_tac G d x c c' i e)(*strict*)
       apply(force)
      apply(rename_tac G d x c c' i e)(*strict*)
      apply(simp add: epdaHS.derivation_initial_def)
     apply(rename_tac G d x c c' i e)(*strict*)
     apply(force)
    apply(rename_tac G d x c c' i e)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G d x c c' i e)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def epdaHS_marking_configurations_def)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d x c i e)(*strict*)
  apply(simp add: epdaHS_unmarked_configuration_effect_def epdaHS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d c i e)(*strict*)
  apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def epdaHS_marking_configurations_def)
  apply(case_tac "d 0")
   apply(rename_tac G d c i e)(*strict*)
   apply(force)
  apply(rename_tac G d c i e a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G d c i e a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d c i e conf)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G d c i e conf)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and G="G"
      and n="0"
      and m="i"
      in epdaHS_change_of_history_and_scheduler)
      apply(rename_tac G d c i e conf)(*strict*)
      apply(force)
     apply(rename_tac G d c i e conf)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
    apply(rename_tac G d c i e conf)(*strict*)
    apply(force)
   apply(rename_tac G d c i e conf)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d c i e conf)(*strict*)
  apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def epdaHS_marking_configurations_def)
  apply(clarsimp)
  apply(force)
  done

lemma epdaHS_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_epda epdaHS_configurations
     epdaHS_step_relation True epdaHS_string_state"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(simp add: epdaHS_inst_AX_string_state_decreases )
  done

interpretation "epdaHS" : loc_autHFS_3
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms )
  done

definition epdaHS_set_unfixed_scheduler :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf"
  where
    "epdaHS_set_unfixed_scheduler c sUF \<equiv>
  c\<lparr>epdaHS_conf_scheduler:=sUF\<rparr>"

definition epdaHS_get_unfixed_scheduler :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list"
  where
    "epdaHS_get_unfixed_scheduler c \<equiv>
  epdaHS_conf_scheduler c"

lemma epdaHS_inst_AX_set_unfixed_scheduler_set: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> (\<forall>sUF1. sUF1 \<in> epda_effects G \<longrightarrow> (\<forall>sUF2. sUF2 \<in> epda_effects G \<longrightarrow> epdaHS_set_unfixed_scheduler (epdaHS_set_unfixed_scheduler c sUF1) sUF2 = epdaHS_set_unfixed_scheduler c sUF2))))"
  apply(simp add: epdaHS_set_unfixed_scheduler_def)
  done

lemma epdaHS_inst_AX_get_set_unfixed_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaHS_get_unfixed_scheduler (epdaHS_set_unfixed_scheduler c sUF) = sUF)))"
  apply(simp add: epdaHS_get_unfixed_scheduler_def epdaHS_set_unfixed_scheduler_def)
  done

lemma epdaHS_inst_schedUF_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> epdaHS_get_unfixed_scheduler c \<in> epda_effects G))"
  apply(simp add: epdaHS_get_unfixed_scheduler_def epda_effects_def epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G x q h i s) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_AX_set_unfixed_scheduler_get: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1. c1 \<in> epdaHS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> epdaHS_configurations G \<longrightarrow> (\<exists>sUF\<in> epda_effects G. epdaHS_set_unfixed_scheduler c1 sUF = epdaHS_set_unfixed_scheduler c2 sUF) \<longrightarrow> epdaHS_set_unfixed_scheduler c1 (epdaHS_get_unfixed_scheduler c2) = c2)))"
  apply(clarsimp)
  apply(rename_tac G c1 c2 sUF) (*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_def epdaHS_get_unfixed_scheduler_def epdaHS_configurations_def prefix_def)
  apply(clarsimp)
  done

lemma epdaHS_unfixed_is_reduced_by_single_step: "
  valid_epda G
  \<Longrightarrow> c1 \<in> epdaHS_configurations G
  \<Longrightarrow> valid_epda_step_label G e
  \<Longrightarrow> c2 \<in> epdaHS_configurations G
  \<Longrightarrow> epdaHS_step_relation G c1 e c2
  \<Longrightarrow> epdaHS_get_unfixed_scheduler c1 \<sqsupseteq> epdaHS_get_unfixed_scheduler c2"
  apply(simp add: epdaHS_step_relation_def)
  apply(simp add: epdaHS_get_unfixed_scheduler_def epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac h ia w) (*strict*)
  apply(simp add: suffix_def)
  done

lemma epdaHS_unfixed_is_reduced_by_steps: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> epdaHS.belongs G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> d m = Some (pair e' c')
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> suffix (epdaHS_get_unfixed_scheduler c) (epdaHS_get_unfixed_scheduler c')"
  apply(induct "m-n" arbitrary: n m e c e' c')
   apply(rename_tac n m e c e' c') (*strict*)
   apply(clarsimp)
   apply(rename_tac n e' c') (*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x n m e c e' c') (*strict*)
  apply(erule_tac
      x="Suc n"
      in meta_allE)
  apply(erule_tac
      x="m"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2")
   apply(rename_tac x n m e c e' c') (*strict*)
   prefer 2
   apply(rule_tac
      m="m"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac x n m e c e' c') (*strict*)
     apply(force)
    apply(rename_tac x n m e c e' c') (*strict*)
    apply(force)
   apply(rename_tac x n m e c e' c') (*strict*)
   apply(force)
  apply(rename_tac x n m e c e' c') (*strict*)
  apply(clarsimp)
  apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(erule_tac
      x="e'"
      in meta_allE)
  apply(erule_tac
      x="c'"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac meta_impE)
   apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
  apply(subgoal_tac "epdaHS_get_unfixed_scheduler c \<sqsupseteq> epdaHS_get_unfixed_scheduler c2")
   apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
   apply(simp add: suffix_def)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
  apply(rule epdaHS_unfixed_is_reduced_by_single_step)
      apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
      apply(force)
     apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
     apply (metis epdaHS.belongs_configurations)
    apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
    prefer 2
    apply (metis epdaHS.belongs_configurations)
   apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2) (*strict*)
  apply(simp add: epdaHS_step_relation_def valid_epda_def)
  done

lemma epdaHS_inst_AX_unfixed_scheduler_right_quotient_split: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation G d \<longrightarrow> epdaHS.belongs G d \<longrightarrow> (\<forall>n e1 c1. d n = Some (pair e1 c1) \<longrightarrow> (\<forall>m e2 c2. d m = Some (pair e2 c2) \<longrightarrow> (\<forall>k e3 c3. d k = Some (pair e3 c3) \<longrightarrow> n \<le> m \<longrightarrow> m \<le> k \<longrightarrow> the (right_quotient_word (epdaHS_get_unfixed_scheduler c1) (epdaHS_get_unfixed_scheduler c3)) = the (right_quotient_word (epdaHS_get_unfixed_scheduler c1) (epdaHS_get_unfixed_scheduler c2)) @ the (right_quotient_word (epdaHS_get_unfixed_scheduler c2) (epdaHS_get_unfixed_scheduler c3))))))"
  apply(clarsimp)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
  apply(subgoal_tac "suffix (epdaHS_get_unfixed_scheduler c1) (epdaHS_get_unfixed_scheduler c2)")
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
   prefer 2
   apply(rule epdaHS_unfixed_is_reduced_by_steps)
        apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
        apply(force)
       apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
       apply(force)
      apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
      apply(force)
     apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
     apply(force)
    apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
    apply(force)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
  apply(subgoal_tac "suffix (epdaHS_get_unfixed_scheduler c2) (epdaHS_get_unfixed_scheduler c3)")
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
   prefer 2
   apply(rule epdaHS_unfixed_is_reduced_by_steps)
        apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
        apply(force)
       apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
       apply(force)
      apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
      apply(force)
     apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
     apply(force)
    apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
    apply(force)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3) (*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
  apply(rule_tac
      t="right_quotient_word (c @ ca @ epdaHS_get_unfixed_scheduler c3) (epdaHS_get_unfixed_scheduler c3)"
      and s="Some(c@ca)"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
  apply(rule_tac
      t="right_quotient_word (c @ ca @ epdaHS_get_unfixed_scheduler c3) (ca@epdaHS_get_unfixed_scheduler c3)"
      and s="Some c"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ epdaHS_get_unfixed_scheduler c3) (epdaHS_get_unfixed_scheduler c3)"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca) (*strict*)
  apply(clarsimp)
  done

definition epdaHS_get_scheduler :: "
  ('state, 'event, 'stack) epdaHS_conf
  \<Rightarrow> 'event list"
  where
    "epdaHS_get_scheduler c \<equiv>
  epdaHS_conf_scheduler c"

definition epdaHS_get_fixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "epdaHS_get_fixed_scheduler_DB G d n \<equiv>
  []"

definition epdaHS_set_unfixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list
  \<Rightarrow> ('state, 'event, 'stack) epdaHS_conf"
  where
    "epdaHS_set_unfixed_scheduler_DB G d n sUF \<equiv>
  (the(get_configuration(d n)))\<lparr>epdaHS_conf_scheduler:=sUF\<rparr>"

definition epdaHS_get_unfixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "epdaHS_get_unfixed_scheduler_DB G d n \<equiv> epdaHS_get_scheduler(the(get_configuration(d n)))"

lemma epdaHS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> epdaHS.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> j \<le> n
  \<Longrightarrow> suffix (epdaHS_get_unfixed_scheduler_DB G d i) (epdaHS_get_unfixed_scheduler_DB G d j)"
  apply(induct "j-i" arbitrary: i j)
   apply(rename_tac i j) (*strict*)
   apply(clarsimp)
   apply(rename_tac i y) (*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x i j) (*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y) (*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i j y) (*strict*)
   apply(force)
  apply(rename_tac x i j y) (*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i j y) (*strict*)
   apply(force)
  apply(rename_tac x i j y) (*strict*)
  apply(rule_tac
      b="epdaHS_get_unfixed_scheduler_DB G d (Suc i)"
      in suffix_trans)
   apply(rename_tac x i j y) (*strict*)
   defer
   apply(force)
  apply(rename_tac x i j y) (*strict*)
  apply(thin_tac "epdaHS_get_unfixed_scheduler_DB G d (Suc i) \<sqsupseteq> epdaHS_get_unfixed_scheduler_DB G d j")
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def suffix_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2")
   apply(rename_tac x i j y) (*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac x i j y) (*strict*)
     apply(force)
    apply(rename_tac x i j y) (*strict*)
    apply(force)
   apply(rename_tac x i j y) (*strict*)
   apply(force)
  apply(rename_tac x i j y) (*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2) (*strict*)
  apply(simp add: epdaHS_get_scheduler_def get_configuration_def epdaHS_step_relation_def)
  done

lemma epdaHS_inst_AX_get_unfixed_scheduler_DB_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation G d \<longrightarrow> epdaHS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>e c. d n = Some (pair e c)) \<longrightarrow> epdaHS_get_unfixed_scheduler_DB G d n \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G d n e c) (*strict*)
  apply(simp add: epda_effects_def epdaHS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaHS_get_scheduler_def)
  apply(subgoal_tac "c \<in> epdaHS_configurations G")
   apply(rename_tac G d n e c) (*strict*)
   prefer 2
   apply(rule epdaHS.belongs_configurations)
    apply(rename_tac G d n e c) (*strict*)
    apply(force)
   apply(rename_tac G d n e c) (*strict*)
   apply(force)
  apply(rename_tac G d n e c) (*strict*)
  apply(simp add: epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n e x q h i s) (*strict*)
  apply(force)
  done

lemma epda_HS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation G d \<longrightarrow> epdaHS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaHS_get_fixed_scheduler_DB G d n \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G d n y) (*strict*)
  apply(simp add: epda_effects_def epdaHS_get_fixed_scheduler_DB_def get_configuration_def)
  done

lemma epdaHS_inst_AX_state_based_vs_derivation_based_get_unfixed_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> epdaHS_get_unfixed_scheduler_DB G d n = epdaHS_get_unfixed_scheduler c)))"
  apply(clarsimp)
  apply(rename_tac G d n e c) (*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def get_configuration_def)
  apply (simp add: epdaHS_get_unfixed_scheduler_def epdaHS_get_scheduler_def)
  done

lemma epdaHS_inst_AX_state_based_vs_derivation_based_set_unfixed_scheduler: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> (\<forall>sUF. epdaHS_set_unfixed_scheduler_DB G d n sUF = epdaHS_set_unfixed_scheduler c sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n e c sUF) (*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_DB_def get_configuration_def epdaHS_set_unfixed_scheduler_def)
  done

lemma epdaHS_inst_AX_get_fixed_scheduler_DB_restrict: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>x n. x \<le> n \<longrightarrow> (\<forall>d1. epdaHS.derivation G d1 \<longrightarrow> (\<forall>d2. epdaHS_get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = epdaHS_get_fixed_scheduler_DB G d1 x))))"
  apply(clarsimp)
  apply(rename_tac G x n d1 d2) (*strict*)
  apply(simp add: epdaHS_get_fixed_scheduler_DB_def epdaHS_get_scheduler_def)
  done

lemma epdaHS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> epdaHS_get_unfixed_scheduler_DB G d n = epdaHS_get_unfixed_scheduler_DB G (derivation_take d m) n))"
  apply(clarsimp)
  apply(rename_tac G d n m) (*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def)
  apply(simp add: derivation_take_def)
  done

lemma epdaHS_inst_AX_join_scheduler_fragments_foldl_split: "
  (\<forall>w v. foldl (@) (foldl (@) [] w) v = foldl (@) [] w @ foldl (@) [] v)"
  apply(clarsimp)
  apply(rename_tac w v) (*strict*)
  apply (metis concat_conv_foldl foldl_append foldl_conv_concat)
  done

lemma epdaHS_inst_AX_foldl_join_scheduler_fragments: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>sE. sE \<in> epda_effects G \<longrightarrow> (\<forall>w. set w \<subseteq> epda_effects G \<longrightarrow> foldl (@) sE w = sE @ foldl (@) [] w)))"
  apply(clarsimp)
  apply(rename_tac G sE w) (*strict*)
  apply (metis concat_conv_foldl foldl_conv_concat)
  done

lemma epdaHS_inst_ATS_Scheduler_Fragment_axioms: "
  ATS_Scheduler_Fragment_axioms valid_epda epda_effects
     epda_empty_scheduler_fragment (@)"
  apply(simp add: ATS_Scheduler_Fragment_axioms_def)
  apply(simp add: epdaHS_inst_AX_foldl_join_scheduler_fragments epdaHS_inst_AX_join_scheduler_fragments_foldl_split epdaHS_inst_AX_join_history_fragments_closed )
  apply(simp add: epdaX_inst_AX_empty_history_is_history )
  done

lemma epdaHS_inst_ATS_SchedF_Basic_axioms: "
  ATS_SchedF_Basic_axioms valid_epda epda_fixed_schedulers
     epda_empty_fixed_scheduler"
  apply(simp add: ATS_SchedF_Basic_axioms_def)
  done

lemma epdaHS_inst_ATS_SchedUF_Basic_axioms: "
  ATS_SchedUF_Basic_axioms valid_epda epda_effects epda_empty_scheduler_fragment
     epda_effects epda_empty_unfixed_scheduler right_quotient_word (@)
     epda_unfixed_scheduler_extendable"
  apply(simp add: ATS_SchedUF_Basic_axioms_def)
  apply(simp add: epdaHS_inst_AX_foldl_join_scheduler_fragments epdaHS_inst_AX_join_scheduler_fragments_foldl_split epdaHS_inst_AX_join_history_fragments_closed )
  apply(simp add: epdaX_inst_AX_empty_history_is_history )
  apply(simp add: right_quotient_word_def)
  done

lemma epdaHS_inst_AX_get_scheduler_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> epdaHS_get_scheduler c \<in> epda_effects G))"
  apply(clarsimp)
  apply(rename_tac G c) (*strict*)
  apply(simp add: epdaHS_get_scheduler_def epdaHS_configurations_def epda_effects_def)
  apply(clarsimp)
  apply(rename_tac G x q h i s) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_ATS_SchedUF_SB_axioms: "
  ATS_SchedUF_SB_axioms valid_epda epdaHS_configurations epda_step_labels
     epdaHS_step_relation (@) epda_effects right_quotient_word
     epda_unfixed_scheduler_extendable epdaHS_set_unfixed_scheduler
     epdaHS_get_unfixed_scheduler"
  apply(simp add: ATS_SchedUF_SB_axioms_def)
  apply(simp add: epdaHS_inst_schedUF_closed epdaHS_inst_AX_set_unfixed_scheduler_set epdaHS_inst_AX_get_set_unfixed_scheduler epdaHS_inst_AX_set_unfixed_scheduler_get )
  apply(rule epdaHS_inst_AX_unfixed_scheduler_right_quotient_split )
  done

lemma epdaHS_inst_AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaHS_configurations G \<longrightarrow> epdaHS_get_scheduler c = epdaHS_get_unfixed_scheduler c)"
  apply(clarsimp)
  apply(rename_tac G c) (*strict*)
  apply(simp add: epdaHS_get_scheduler_def epdaHS_get_unfixed_scheduler_def)
  done

lemma epdaHS_inst_ATS_SchedF_SB_axioms: "
  ATS_SchedF_SB_axioms valid_epda epdaHS_configurations epdaHS_step_relation
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler"
  apply(simp add: ATS_SchedF_SB_axioms_def)
  done

lemma epdaHS_inst_ATS_Sched_axioms: "
  ATS_Sched_axioms valid_epda epdaHS_configurations epda_effects
     epda_empty_scheduler_fragment (@) epda_effects epda_effects
     epda_empty_scheduler epdaHS_get_scheduler (@)"
  apply(simp add: ATS_Sched_axioms_def)
  apply(simp add: epdaHS_inst_AX_join_history_fragments_closed epdaX_inst_AX_empty_history_is_history epdaHS_inst_AX_get_scheduler_closed )
  done

lemma epdaHS_inst_ATS_Sched_Basic_axioms: "
  ATS_Sched_Basic_axioms valid_epda epda_fixed_schedulers
     epda_fixed_scheduler_extendable epda_effects
     epda_unfixed_scheduler_extendable epda_effects (@)"
  apply(simp add: ATS_Sched_Basic_axioms_def)
  done

lemma epdaHS_inst_ATS_Sched_SB_axioms: "
  ATS_Sched_SB_axioms valid_epda epdaHS_configurations
     epda_fixed_scheduler_extendable epda_empty_unfixed_scheduler
     epda_unfixed_scheduler_extendable epdaHS_get_scheduler (@)
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler
     epdaHS_get_fixed_scheduler"
  apply(simp add: ATS_Sched_SB_axioms_def)
  apply(simp add: epdaHS_inst_AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler)
  done

print_locale loc_autHFS_4
interpretation "epdaHS" : loc_autHFS_4
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms epdaHS_inst_ATS_Sched_axioms epdaHS_inst_ATS_Sched_Basic_axioms )
  apply(simp add: epdaHS_inst_ATS_Sched_SB_axioms )
  done

lemma epdaHS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaHS_get_fixed_scheduler_DB G d n @ epdaHS_get_unfixed_scheduler_DB G d n = ATS_Sched.get_scheduler_nth epdaHS_get_scheduler d n)))"
  apply(clarsimp)
  apply(rename_tac G d n y) (*strict*)
  apply(simp add: epdaHS.get_scheduler_nth_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b) (*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b) (*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaHS_get_fixed_scheduler_DB_def)
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  done

lemma epdaHS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaHS_get_fixed_scheduler_DB G d n @ epdaHS_get_unfixed_scheduler_DB G d n \<in> epda_effects G))"
  apply(clarsimp)
  apply(rename_tac G d n y) (*strict*)
  apply(simp add: epdaHS_get_fixed_scheduler_DB_def epdaHS_get_scheduler_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b) (*strict*)
  apply(simp add: get_configuration_def epdaHS_get_unfixed_scheduler_DB_def epdaHS_get_scheduler_def)
  apply(subgoal_tac "b \<in> epdaHS_configurations G")
   apply(rename_tac G d n y option b) (*strict*)
   prefer 2
   apply (metis epdaHS.belongs_configurations epdaHS.derivation_initial_belongs)
  apply(rename_tac G d n y option b) (*strict*)
  apply(simp add: epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n option q h i s) (*strict*)
  apply(simp add: epda_effects_def)
  done

lemma epdaHS_inst_AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>j i. i \<le> j \<longrightarrow> j \<le> n \<longrightarrow> the (right_quotient_word (epdaHS_get_unfixed_scheduler_DB G d i) (epdaHS_get_unfixed_scheduler_DB G d j)) \<in> epda_effects G))))"
  apply(clarsimp)
  apply(rename_tac G d n y j i) (*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def epdaHS_get_scheduler_def)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac G d n y j i) (*strict*)
   apply(subgoal_tac "\<exists>e c. d j = Some (pair e c)")
    apply(rename_tac G d n y j i) (*strict*)
    apply(clarsimp)
    apply(rename_tac G d n y j i e ea c ca) (*strict*)
    apply(simp add: get_configuration_def)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state c = w @ epdaHS_string_state ca")
     apply(rename_tac G d n y j i e ea c ca) (*strict*)
     prefer 2
     apply(rule_tac
      j="j-i"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac G d n y j i e ea c ca) (*strict*)
          apply(force)
         apply(rename_tac G d n y j i e ea c ca) (*strict*)
         apply(force)
        apply(rename_tac G d n y j i e ea c ca) (*strict*)
        apply(rule epdaHS.derivation_initial_belongs)
         apply(rename_tac G d n y j i e ea c ca) (*strict*)
         apply(force)
        apply(rename_tac G d n y j i e ea c ca) (*strict*)
        apply(force)
       apply(rename_tac G d n y j i e ea c ca) (*strict*)
       apply(rule epdaHS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G d n y j i e ea c ca) (*strict*)
      apply(force)
     apply(rename_tac G d n y j i e ea c ca) (*strict*)
     apply(force)
    apply(rename_tac G d n y j i e ea c ca) (*strict*)
    apply(clarsimp)
    apply(rename_tac G d n y j i e ea c ca w) (*strict*)
    apply(rule_tac
      t="right_quotient_word (epdaHS_conf_scheduler c) (epdaHS_conf_scheduler ca)"
      and s="Some w"
      in ssubst)
     apply(rename_tac G d n y j i e ea c ca w) (*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(simp add: get_configuration_def epdaHS_string_state_def epdaHS_get_scheduler_def)
    apply(rename_tac G d n y j i e ea c ca w) (*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def epdaHS_string_state_def epdaHS_get_scheduler_def)
    apply(simp add: epda_effects_def)
    apply(rule_tac
      B="set (epdaHS_conf_scheduler c)"
      in subset_trans)
     apply(rename_tac G d n y j i e ea c ca w) (*strict*)
     apply(force)
    apply(rename_tac G d n y j i e ea c ca w) (*strict*)
    apply(subgoal_tac "c \<in> epdaHS_configurations G")
     apply(rename_tac G d n y j i e ea c ca w) (*strict*)
     apply(simp add: epdaHS_configurations_def)
     apply(clarsimp)
    apply(rename_tac G d n y j i e ea c ca w) (*strict*)
    apply(rule epdaHS.belongs_configurations)
     apply(rename_tac G d n y j i e ea c ca w) (*strict*)
     apply(rule epdaHS.derivation_initial_belongs)
      apply(rename_tac G d n y j i e ea c ca w) (*strict*)
      apply(force)
     apply(rename_tac G d n y j i e ea c ca w) (*strict*)
     apply(force)
    apply(rename_tac G d n y j i e ea c ca w) (*strict*)
    apply(force)
   apply(rename_tac G d n y j i) (*strict*)
   apply(rule_tac epdaHS.pre_some_position_is_some_position)
     apply(rename_tac G d n y j i) (*strict*)
     apply(rule epdaHS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G d n y j i) (*strict*)
    apply(force)
   apply(rename_tac G d n y j i) (*strict*)
   apply(force)
  apply(rename_tac G d n y j i) (*strict*)
  apply(rule_tac epdaHS.pre_some_position_is_some_position)
    apply(rename_tac G d n y j i) (*strict*)
    apply(rule epdaHS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G d n y j i) (*strict*)
   apply(force)
  apply(rename_tac G d n y j i) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation G d \<longrightarrow> (\<forall>c. d 0 = Some (pair None c) \<longrightarrow> c \<in> epdaHS_initial_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaHS_set_unfixed_scheduler_DB G d 0 sUF \<in> epdaHS_initial_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G d c sUF) (*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaHS_initial_configurations_def)
  apply(clarsimp)
  apply(simp add: epdaHS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d sUF i x) (*strict*)
  apply(simp add: epda_effects_def)
  apply(force)
  done

lemma epdaHS_inst_ATS_SchedUF_DB_axioms: "
  ATS_SchedUF_DB_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epda_effects epda_effects right_quotient_word
     epda_unfixed_scheduler_extendable epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_SchedUF_DB_axioms_def)
  apply(rule conjI)
   apply(simp add: epdaHS_inst_AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB)
  apply(simp add: epdaHS_inst_AX_get_unfixed_scheduler_DB_closed epdaHS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations epdaHS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take )
  done

lemma epdaHS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation G d \<longrightarrow> epdaHS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaHS_get_fixed_scheduler_DB G d n = [])))"
  apply(clarsimp)
  apply(rename_tac G d n y) (*strict*)
  apply(simp add: epdaHS_get_fixed_scheduler_DB_def)
  done

lemma epdaHS_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_epda epdaHS_configurations epda_step_labels
     epdaHS_step_relation epda_fixed_schedulers
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_DB_axioms_def)
  apply(simp add: epdaHS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers epdaHS_inst_AX_get_fixed_scheduler_DB_restrict )
  done

lemma epdaHS_inst_AX_sched_modification_preserves_steps: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>dh n. maximum_of_domain dh n \<longrightarrow> epdaHS.derivation G dh \<longrightarrow> epdaHS.belongs G dh \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> (\<forall>m e2 c2. dh (Suc m) = Some (pair (Some e2) c2) \<longrightarrow> (\<forall>e1 c1. dh m = Some (pair e1 c1) \<longrightarrow> epdaHS_step_relation G c1 e2 c2 \<longrightarrow> epdaHS_step_relation G (epdaHS_set_unfixed_scheduler_DB G dh m (the (right_quotient_word (epdaHS_get_unfixed_scheduler_DB G dh m) (epdaHS_get_unfixed_scheduler_DB G dh n)) @ sUF)) e2 (epdaHS_set_unfixed_scheduler_DB G dh (Suc m) (the (right_quotient_word (epdaHS_get_unfixed_scheduler_DB G dh (Suc m)) (epdaHS_get_unfixed_scheduler_DB G dh n)) @ sUF)))))))"
  apply(clarsimp)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1) (*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac G dh n sUF m e2 c2 e1 c1) (*strict*)
   apply(clarsimp)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
   apply(simp add: get_configuration_def epdaHS_get_scheduler_def)
   apply(simp add: epdaHS_set_unfixed_scheduler_DB_def get_configuration_def)
   apply(subgoal_tac "Suc m\<le>n")
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state c1 = w @ epdaHS_string_state c")
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
     prefer 2
     apply(rule_tac
      j="n-m"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
          apply(force)
         apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
         apply(force)
        apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
        apply(force)
       apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
       apply(force)
      apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
      apply(force)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
    apply(clarsimp)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
    apply(simp add: epdaHS_string_state_def)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state c2 = w @ epdaHS_string_state c")
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
     prefer 2
     apply(rule_tac
      j="n-Suc m"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
          apply(force)
         apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
         apply(force)
        apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
        apply(force)
       apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
       apply(force)
      apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
      apply(force)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w) (*strict*)
    apply(clarsimp)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa) (*strict*)
    apply(simp add: epdaHS_string_state_def)
    apply(rule_tac
      t="right_quotient_word (w @ epdaHS_conf_scheduler c) (epdaHS_conf_scheduler c)"
      and s="Some w"
      in ssubst)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa) (*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa) (*strict*)
    apply(rule_tac
      t="right_quotient_word (wa @ epdaHS_conf_scheduler c) (epdaHS_conf_scheduler c)"
      and s="Some wa"
      in ssubst)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa) (*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa) (*strict*)
    apply(clarsimp)
    apply(simp add: epdaHS_step_relation_def)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
   apply(rule epdaHS.allPreMaxDomSome_prime)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
    apply(force)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c) (*strict*)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1) (*strict*)
  apply(rule epdaHS.some_position_has_details_before_max_dom)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1) (*strict*)
    apply(simp add: epdaHS.derivation_initial_def)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1) (*strict*)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1) (*strict*)
  apply(force)
  done

lemma epdaHS_inst_ATS_Sched_DB0_axioms: "
  ATS_Sched_DB0_axioms valid_epda epdaHS_configurations
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epda_fixed_scheduler_extendable epda_effects right_quotient_word (@)
     epda_unfixed_scheduler_extendable epda_effects epdaHS_get_scheduler
     (@) epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB
     epdaHS_get_fixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB0_axioms_def)
  apply(rule conjI)
   apply(simp add: epdaHS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime )
  apply(rule conjI)
   apply(simp add: epdaHS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth )
  apply(rule epdaHS_inst_AX_sched_modification_preserves_steps )
  done

print_locale loc_autHFS_5
interpretation "epdaHS" : loc_autHFS_5
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms)
  apply(simp add: epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_Sched_Basic_axioms epdaHS_inst_ATS_Sched_SB_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms epdaHS_inst_ATS_Sched_axioms epdaHS_inst_ATS_SchedUF_DB_axioms)
  apply(simp add: epdaHS_inst_ATS_Sched_DB0_axioms epdaHS_inst_ATS_SchedF_DB_axioms )
  done

lemma epdaHS_inst_AX_replace_unfixed_scheduler_DB_sound: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d n. maximum_of_domain d n \<longrightarrow> epdaHS.derivation_initial G d \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaHS_get_unfixed_scheduler_DB G (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB G d sUF n) n = sUF))"
  apply(clarsimp)
  apply(rename_tac G d n sUF) (*strict*)
  apply(simp add: epdaHS.map_unfixed_scheduler_DB_def epdaHS.replace_unfixed_scheduler_DB_def epdaHS_get_unfixed_scheduler_DB_def epdaHS_get_scheduler_def)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac G d n sUF) (*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G d n sUF) (*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G d n sUF) (*strict*)
    apply(force)
   apply(rename_tac G d n sUF) (*strict*)
   apply(force)
  apply(rename_tac G d n sUF) (*strict*)
  apply(clarsimp)
  apply(rename_tac G d n sUF e c) (*strict*)
  apply(simp add: get_configuration_def epdaHS_get_scheduler_def epdaHS_get_unfixed_scheduler_DB_def)
  apply(simp add: epdaHS_set_unfixed_scheduler_DB_def)
  apply (metis right_quotient_word_full option.sel)
  done

lemma epdaHS_inst_ATS_Sched_DB_axioms: "
  ATS_Sched_DB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects right_quotient_word (@)
     epda_unfixed_scheduler_extendable epdaHS_set_unfixed_scheduler_DB
     epdaHS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB_axioms_def)
  apply(clarsimp)
  apply(rename_tac G d n sUF) (*strict*)
  apply(simp add: epdaHS_inst_AX_replace_unfixed_scheduler_DB_sound)
  done

interpretation "epdaHS" : loc_autHFS_5b
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_Sched_Basic_axioms epdaHS_inst_ATS_Sched_SB_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms epdaHS_inst_ATS_Sched_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_DB_axioms epdaHS_inst_ATS_SchedUF_DB_axioms epdaHS_inst_ATS_Sched_DB0_axioms )
  apply(simp add: epdaHS_inst_ATS_Sched_DB_axioms )
  done

lemma epdaHS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>e c. d n = Some (pair e c)) \<longrightarrow> epdaHS_get_fixed_scheduler_DB G d n = []))"
  apply(clarsimp)
  apply(rename_tac G d n e c) (*strict*)
  apply(simp add: epdaHS_get_fixed_scheduler_DB_def)
  done

lemma epdaHS_inst_ATS_SchedF_SDB_axioms: "
  ATS_SchedF_SDB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epdaHS_get_fixed_scheduler
     epdaHS_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_SDB_axioms_def)
  apply(simp add: epdaHS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler )
  done

lemma epdaHS_inst_AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaHS_get_unfixed_scheduler (epdaHS_set_unfixed_scheduler_DB G d n sUF) = sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n y sUF) (*strict*)
  apply(simp add: epdaHS_get_unfixed_scheduler_def epdaHS_set_unfixed_scheduler_DB_def)
  done

lemma epdaHS_inst_AX_set_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaHS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaHS_set_unfixed_scheduler (the (get_configuration (d n))) sUF = epdaHS_set_unfixed_scheduler_DB G d n sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n y sUF) (*strict*)
  apply(simp add: epdaHS_set_unfixed_scheduler_DB_def)
  apply(case_tac y)
  apply(rename_tac G d n y sUF option b) (*strict*)
  apply(simp add: get_configuration_def epdaHS_set_unfixed_scheduler_def)
  done

lemma epdaHS_inst_ATS_SchedUF_SDB_axioms: "
  ATS_SchedUF_SDB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler epdaHS_get_unfixed_scheduler
     epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_SchedUF_SDB_axioms_def)
  apply(simp add: epdaHS_inst_AX_state_based_vs_derivation_based_get_unfixed_scheduler epdaHS_inst_AX_state_based_vs_derivation_based_set_unfixed_scheduler epdaHS_inst_AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound epdaHS_inst_AX_set_unfixed_scheduler_set_unfixed_scheduler_DB_sound )
  done

lemma epdaHS_inst_ATS_Sched_SDB_axioms: "
  ATS_Sched_SDB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_unfixed_scheduler_extendable
     epdaHS_get_unfixed_scheduler epdaHS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_Sched_SDB_axioms_def)
  done

interpretation "epdaHS" : loc_autHFS_6
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_Sched_axioms epdaHS_inst_ATS_Sched_Basic_axioms epdaHS_inst_ATS_Sched_SB_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_DB_axioms epdaHS_inst_ATS_SchedUF_DB_axioms epdaHS_inst_ATS_Sched_DB0_axioms )
  apply(simp add: epdaHS_inst_ATS_Sched_DB_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_SDB_axioms epdaHS_inst_ATS_SchedUF_SDB_axioms epdaHS_inst_ATS_Sched_SDB_axioms )
  done

lemma epdaHS_inst_ATS_determHIST_SB_axioms: "
  ATS_determHIST_SB_axioms valid_epda epdaHS_configurations epdaHS_step_relation
     epdaHS_conf_history epda_fixed_scheduler_extendable
     epdaHS_get_fixed_scheduler"
  apply(simp add: ATS_determHIST_SB_axioms_def)
  done

interpretation "epdaHS" : loc_autHFS_7
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_Sched_Basic_axioms epdaHS_inst_ATS_Sched_SB_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms epdaHS_inst_ATS_Sched_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_DB_axioms epdaHS_inst_ATS_SchedUF_DB_axioms epdaHS_inst_ATS_Sched_DB0_axioms )
  apply(simp add: epdaHS_inst_ATS_Sched_DB_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_SDB_axioms epdaHS_inst_ATS_SchedUF_SDB_axioms epdaHS_inst_ATS_Sched_SDB_axioms )
  apply(simp add: epdaHS_inst_ATS_determHIST_SB_axioms )
  done

lemma epdaHS_mutual_history_extension_hlp: "
  valid_epda G
  \<Longrightarrow> epdaHS_step_relation G c e1 c1
  \<Longrightarrow> epdaHS_step_relation G c e2 c2
  \<Longrightarrow> epdaHS_conf_history c1 = epdaHS_conf_history c @ w1
  \<Longrightarrow> epdaHS_conf_history c2 = epdaHS_conf_history c @ w2
  \<Longrightarrow> c \<in> epdaHS_configurations G
  \<Longrightarrow> c1 \<in> epdaHS_configurations G
  \<Longrightarrow> c2 \<in> epdaHS_configurations G
  \<Longrightarrow> length w1 \<le> length w2
  \<Longrightarrow> w2 \<sqsubseteq> w1 \<or> w1 \<sqsubseteq> w2"
  apply(rule disjI2)
  apply(rule_tac
      w="epdaHS_conf_scheduler c"
      in prefix_common_max)
    apply(simp add: prefix_def epdaHS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac w wa) (*strict*)
    apply(simp add: option_to_list_def)
    apply(case_tac "edge_event e1")
     apply(rename_tac w wa) (*strict*)
     apply(clarsimp)
    apply(rename_tac w wa a) (*strict*)
    apply(clarsimp)
    apply(case_tac "edge_event e2")
     apply(rename_tac w wa a) (*strict*)
     apply(clarsimp)
    apply(rename_tac w wa a aa) (*strict*)
    apply(clarsimp)
   apply(simp add: prefix_def epdaHS_step_relation_def)
  apply(clarsimp)
  done

lemma epdaHS_mutual_history_extension: "
  valid_epda G
  \<Longrightarrow> epdaHS_step_relation G c e1 c1
  \<Longrightarrow> epdaHS_step_relation G c e2 c2
  \<Longrightarrow> epdaHS_conf_history c1 = epdaHS_conf_history c @ w1
  \<Longrightarrow> epdaHS_conf_history c2 = epdaHS_conf_history c @ w2
  \<Longrightarrow> c \<in> epdaHS_configurations G
  \<Longrightarrow> c1 \<in> epdaHS_configurations G
  \<Longrightarrow> c2 \<in> epdaHS_configurations G
  \<Longrightarrow> w2 \<sqsubseteq> w1 \<or> w1 \<sqsubseteq> w2"
  apply(case_tac "length w1 \<le> length w2")
   apply (metis epdaHS_mutual_history_extension_hlp)
  apply(subgoal_tac "w1 \<sqsubseteq> w2 \<or> w2 \<sqsubseteq> w1")
   apply(force)
  apply (metis epdaHS_mutual_history_extension_hlp linorder_le_cases)
  done

lemma epdaHS_inst_AX_is_forward_edge_deterministic_correspond_SB: "
   \<forall>G. valid_epda G \<longrightarrow>
        ATS.is_forward_edge_deterministic_accessible
         epdaHS_initial_configurations epdaHS_step_relation G =
        ATS_determHIST_SB.is_forward_edge_deterministicHist_SB_long
         epdaHS_initial_configurations epdaHS_step_relation epda_effects (@)
         (@) epdaHS_conf_history epda_fixed_scheduler_extendable
         epdaHS_get_fixed_scheduler G"
  apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(simp add: epdaHS.is_forward_edge_deterministic_accessible_def)
  apply(simp add: epdaHS.is_forward_edge_deterministicHist_SB_long_def)
  apply(rule order_antisym)
   apply(rename_tac G) (*strict*)
   apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e1 e2) (*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac G c c1 c2 e1 e2) (*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2) (*strict*)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac G c c1 c2 e1 e2) (*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2) (*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1. epdaHS_conf_history c1 = epdaHS_conf_history c @ w1")
   apply(rename_tac G c c1 c2 e1 e2) (*strict*)
   prefer 2
   apply(thin_tac "epdaHS_step_relation G c e2 c2")
   apply(subgoal_tac "X" for X)
    apply(rename_tac G c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(rule_tac
      c="c"
      in epdaHS.AX_steps_extend_history)
      apply(rename_tac G c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2)(*strict*)
     apply(rule set_mp_prime)
       apply(rename_tac G c c1 c2 e1 e2)(*strict*)
       apply(rule epdaHS.get_accessible_configurations_are_configurations)
       apply(force)
      apply(rename_tac G c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2) (*strict*)
  apply(subgoal_tac "\<exists>w2. epdaHS_conf_history c2 = epdaHS_conf_history c @ w2")
   apply(rename_tac G c c1 c2 e1 e2) (*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac G c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(rule_tac
      c="c"
      and c'="c2"
      in epdaHS.AX_steps_extend_history)
      apply(rename_tac G c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2)(*strict*)
     apply(rule set_mp_prime)
       apply(rename_tac G c c1 c2 e1 e2)(*strict*)
       apply(rule epdaHS.get_accessible_configurations_are_configurations)
       apply(force)
      apply(rename_tac G c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2) (*strict*)
  apply(erule exE) +
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(subgoal_tac "c1 \<in> epdaHS_configurations G")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    prefer 2
    apply(subgoal_tac "X" for X)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     prefer 2
     apply(rule epdaHS.get_accessible_configurations_are_configurations)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(subgoal_tac "c \<in> epdaHS_configurations G")
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule epdaHS.AX_step_relation_preserves_belongsC)
      apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: epda_effects_def epdaHS_configurations_def)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      x="w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(subgoal_tac "c2 \<in> epdaHS_configurations G")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    prefer 2
    apply(subgoal_tac "X" for X)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     prefer 2
     apply(rule epdaHS.get_accessible_configurations_are_configurations)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(subgoal_tac "c \<in> epdaHS_configurations G")
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule epdaHS.AX_step_relation_preserves_belongsC)
      apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: epda_effects_def epdaHS_configurations_def)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes epda_effects (@) G w2 = ATS_History.history_fragment_prefixes epda_effects (@) G w1"
      and s="ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<and> ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(subgoal_tac "c \<in> epdaHS_configurations G")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   prefer 2
   apply (metis (full_types) contra_subsetD epdaHS.get_accessible_configurations_are_configurations)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(subgoal_tac "c1 \<in> epdaHS_configurations G")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   prefer 2
   apply (metis epdaHS_inst_AX_step_relation_preserves_belongs)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(subgoal_tac "c2 \<in> epdaHS_configurations G")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   prefer 2
   apply (metis epdaHS_inst_AX_step_relation_preserves_belongs)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes epda_effects (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w2"
      and s="prefix w1 w2"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(rule order_antisym)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(clarsimp)
    apply(simp add: epdaHS.history_fragment_prefixes_def)
    apply(simp add: prefix_def)
    apply(subgoal_tac "w1 \<in> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2}")
     apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(rule_tac
      A="{hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1}"
      in set_mp)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(thin_tac "{hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1} \<subseteq> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2}")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(clarsimp)
    apply(simp add: epda_effects_def)
    apply(rule_tac
      B="set (epdaHS_conf_history c1)"
      in subset_trans)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(simp add: epdaHS_configurations_def)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(simp add: prefix_def)
   apply(simp add: epdaHS.history_fragment_prefixes_def)
   apply(clarsimp)
   apply(rename_tac G c c1 c2 e1 e2 x ca hf'') (*strict*)
   apply(simp add: epda_effects_def)
   apply(rule_tac
      B="set (epdaHS_conf_history c2)"
      in subset_trans)
    apply(rename_tac G c c1 c2 e1 e2 x ca hf'') (*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 x ca hf'') (*strict*)
   apply(simp add: epdaHS_configurations_def)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes epda_effects (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G w1"
      and s="prefix w2 w1"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(simp add: epdaHS.history_fragment_prefixes_def)
   apply(rule order_antisym)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(clarsimp)
    apply(simp add: prefix_def)
    apply(subgoal_tac "w2 \<in> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1}")
     apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(rule_tac
      A="{hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2}"
      in set_mp)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(thin_tac "{hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w2} \<subseteq> {hf' \<in> epda_effects G. \<exists>hf''\<in> epda_effects G. hf' @ hf'' = w1}")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(clarsimp)
    apply(simp add: epda_effects_def)
    apply(rule_tac
      B="set (epdaHS_conf_history c2)"
      in subset_trans)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
    apply(simp add: epdaHS_configurations_def)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G c c1 c2 e1 e2 x ca hf'') (*strict*)
   apply(simp add: epda_effects_def)
   apply(rule_tac
      B="set (epdaHS_conf_history c1)"
      in subset_trans)
    apply(rename_tac G c c1 c2 e1 e2 x ca hf'') (*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 x ca hf'') (*strict*)
   apply(simp add: epdaHS_configurations_def)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(rule_tac
      t="w2 \<sqsubseteq> w1 \<and> w1 \<sqsubseteq> w2"
      and s="w1=w2"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(case_tac "w1=w2")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
  apply(subgoal_tac "w2 \<sqsubseteq> w1 \<or> w1 \<sqsubseteq> w2")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
   prefer 2
   apply(rule_tac
      ?c2.0="c2"
      and ?c1.0="c1"
      in epdaHS_mutual_history_extension)
          apply(rename_tac G c c1 c2 e1 e2 w1 w2) (*strict*)
          apply(force) +
  done

lemma epdaHS_inst_ATS_HistoryCE_SB_axioms: "
  ATS_HistoryCE_SB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler"
  apply(simp add: ATS_HistoryCE_SB_axioms_def)
  apply(rule epdaHS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  done

lemma epdaHS_inst_AX_is_forward_edge_deterministic_correspond_DB: "
 \<forall>G. valid_epda G \<longrightarrow>
        ATS.is_forward_edge_deterministic_accessible
         epdaHS_initial_configurations epdaHS_step_relation G =
        ATS_determHIST_DB.is_forward_edge_deterministicHist_DB_long
         epdaHS_initial_configurations epdaHS_step_relation epda_effects (@)
         (@) epdaHS_conf_history epda_fixed_scheduler_extendable
         epdaHS_get_fixed_scheduler_DB G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule_tac
      t="ATS_determHIST_DB.is_forward_edge_deterministicHist_DB_long epdaHS_initial_configurations epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB G"
      and s="ATS_determHIST_SB.is_forward_edge_deterministicHist_SB_long epdaHS_initial_configurations epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler G"
      in subst)
   apply(rename_tac G)(*strict*)
   apply(rule epdaHS.AX_is_forward_edge_deterministic_correspond_DB_SB)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G)(*strict*)
   prefer 2
   apply(rule epdaHS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  apply(rename_tac G)(*strict*)
  apply(force)
  done

lemma epdaHS_inst_ATS_HistoryCE_DB_axioms: "
  ATS_HistoryCE_DB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB"
  apply(simp add: ATS_HistoryCE_DB_axioms_def)
  apply(rule epdaHS_inst_AX_is_forward_edge_deterministic_correspond_DB)
  done

interpretation "epdaHS" : loc_autHFS_8
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_Sched_Basic_axioms epdaHS_inst_ATS_Sched_SB_axioms epdaHS_inst_ATS_Sched_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_DB_axioms epdaHS_inst_ATS_SchedUF_DB_axioms epdaHS_inst_ATS_Sched_DB0_axioms )
  apply(simp add: epdaHS_inst_ATS_Sched_DB_axioms )
  apply(simp add: epdaHS_inst_ATS_SchedF_SDB_axioms epdaHS_inst_ATS_SchedUF_SDB_axioms epdaHS_inst_ATS_Sched_SDB_axioms )
  apply(simp add: epdaHS_inst_ATS_determHIST_SB_axioms )
  apply(simp add: epdaHS_inst_ATS_HistoryCE_SB_axioms epdaHS_inst_ATS_HistoryCE_DB_axioms )
  done

lemma epdaHS_inst_AX_is_forward_target_deterministic_correspond_DB: "
  \<forall>G. valid_epda G \<longrightarrow>
        ATS.is_forward_target_deterministic_accessible
         epdaHS_initial_configurations epdaHS_step_relation G =
        ATS_determHIST_DB.is_forward_target_deterministicHist_DB_long
         epdaHS_initial_configurations epdaHS_step_relation epda_effects (@)
         (@) epdaHS_conf_history epda_fixed_scheduler_extendable
         epdaHS_get_fixed_scheduler_DB G"
  apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(rule order_antisym)
   apply(rename_tac G) (*strict*)
   apply(clarsimp)
   apply(simp add: epdaHS.is_forward_target_deterministicHist_DB_long_def)
   apply(clarsimp)
   apply(rename_tac G c d c1 c2 n e w1 w2) (*strict*)
   apply(simp add: epdaHS_step_relation_def)
   apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(simp add: epdaHS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e) (*strict*)
  apply(simp add: epdaHS_step_relation_def)
  apply(clarsimp)
  done

lemma epdaHS_inst_AX_is_forward_target_deterministic_correspond_SB: "
   \<forall>G. valid_epda G \<longrightarrow>
        ATS.is_forward_target_deterministic_accessible
         epdaHS_initial_configurations epdaHS_step_relation G =
        ATS_determHIST_SB.is_forward_target_deterministicHist_SB_long
         epdaHS_initial_configurations epdaHS_step_relation epda_effects (@)
         (@) epdaHS_conf_history epda_fixed_scheduler_extendable
         epdaHS_get_fixed_scheduler G"
  apply(clarsimp)
  apply(rename_tac G) (*strict*)
  apply(rule order_antisym)
   apply(rename_tac G) (*strict*)
   apply(clarsimp)
   apply(metis epdaHS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long)
  apply(rename_tac G) (*strict*)
  apply(clarsimp)
  apply(simp add: epdaHS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e) (*strict*)
  apply(simp add: epdaHS.is_forward_target_deterministicHist_SB_long_def)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac G c c1 c2 e) (*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e) (*strict*)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule impE)
   apply(rename_tac G c c1 c2 e) (*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e) (*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(simp add: epdaHS_step_relation_def)
  apply(simp add: option_to_list_def epda_effects_def valid_epda_def valid_epda_step_label_def option_to_set_def)
  done

lemma epdaHS_inst_ATS_HistoryCT_DB_axioms: "
  ATS_HistoryCT_DB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler_DB"
  apply(simp add: ATS_HistoryCT_DB_axioms_def)
  apply(rule epdaHS_inst_AX_is_forward_target_deterministic_correspond_DB)
  done

lemma epdaHS_inst_ATS_HistoryCT_SB_axioms: "
  ATS_HistoryCT_SB_axioms valid_epda epdaHS_initial_configurations
     epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history
     epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler"
  apply(simp add: ATS_HistoryCT_SB_axioms_def)
  apply(rule epdaHS_inst_AX_is_forward_target_deterministic_correspond_SB)
  done

interpretation "epdaHS" : loc_autHFS_9
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
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaHS_inst_AX_initial_configuration_belongs epdaHS_inst_AX_step_relation_preserves_belongs epdaHS_inst_ATS_Language_axioms epdaHS_inst_ATS_History_axioms epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms epdaHS_inst_ATS_String_State_Modification_axioms epdaHS_inst_ATS_SchedF_Basic_axioms epdaHS_inst_ATS_Scheduler_Fragment_axioms epdaHS_inst_ATS_SchedUF_Basic_axioms epdaHS_inst_ATS_Sched_Basic_axioms epdaHS_inst_ATS_Sched_SB_axioms epdaHS_inst_ATS_Sched_axioms epdaHS_inst_ATS_SchedF_SB_axioms epdaHS_inst_ATS_SchedUF_SB_axioms epdaHS_inst_ATS_SchedF_DB_axioms epdaHS_inst_ATS_SchedUF_DB_axioms epdaHS_inst_ATS_Sched_DB0_axioms epdaHS_inst_ATS_Sched_DB_axioms epdaHS_inst_ATS_SchedF_SDB_axioms epdaHS_inst_ATS_SchedUF_SDB_axioms epdaHS_inst_ATS_Sched_SDB_axioms epdaHS_inst_ATS_determHIST_SB_axioms epdaHS_inst_ATS_HistoryCE_SB_axioms epdaHS_inst_ATS_HistoryCT_SB_axioms epdaHS_inst_ATS_HistoryCT_DB_axioms epdaHS_inst_ATS_HistoryCE_DB_axioms )
  done

lemma epdaHS_unique_step: "
  valid_epda G
  \<Longrightarrow> \<exists>c2. epdaHS_step_relation G c1 e c2
  \<Longrightarrow> \<exists>!c2. epdaHS_step_relation G c1 e c2"
  apply(rule ex_ex1I)
   apply(force)
  apply(rename_tac c2 y) (*strict*)
  apply(simp add: epdaHS_step_relation_def)
  apply(clarsimp)
  done

theorem epdaHS_is_forward_target_deterministic_accessible: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_target_deterministic_accessible G"
  apply(simp add: epdaHS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e) (*strict*)
  apply(simp add: epdaHS_step_relation_def)
  apply(clarsimp)
  done

lemmas epdaHS_interpretations0 =
  epdaHS_inst_AX_initial_configuration_belongs
  epdaHS_inst_AX_step_relation_preserves_belongs
  epdaHS_inst_ATS_Language_axioms
  epdaHS_inst_ATS_History_axioms
  epdaHS_inst_ATS_Language_by_Finite_Derivations_axioms
  epdaHS_inst_ATS_String_State_Modification_axioms
  epdaHS_inst_ATS_SchedF_Basic_axioms
  epdaHS_inst_ATS_Scheduler_Fragment_axioms
  epdaHS_inst_ATS_SchedUF_Basic_axioms
  epdaHS_inst_ATS_Sched_Basic_axioms
  epdaHS_inst_ATS_Sched_SB_axioms
  epdaHS_inst_ATS_Sched_axioms
  epdaHS_inst_ATS_SchedF_SB_axioms
  epdaHS_inst_ATS_SchedUF_SB_axioms
  epdaHS_inst_ATS_SchedF_DB_axioms
  epdaHS_inst_ATS_SchedUF_DB_axioms
  epdaHS_inst_ATS_Sched_DB0_axioms
  epdaHS_inst_ATS_Sched_DB_axioms
  epdaHS_inst_ATS_SchedF_SDB_axioms
  epdaHS_inst_ATS_SchedUF_SDB_axioms
  epdaHS_inst_ATS_Sched_SDB_axioms
  epdaHS_inst_ATS_determHIST_SB_axioms
  epdaHS_inst_ATS_HistoryCT_SB_axioms
  epdaHS_inst_ATS_HistoryCE_SB_axioms
  epdaHS_inst_ATS_HistoryCT_DB_axioms
  epdaHS_inst_ATS_HistoryCE_DB_axioms

end
