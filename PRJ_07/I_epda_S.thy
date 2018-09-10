section {*I\_epda\_S*}
theory
  I_epda_S

imports
  I_epda_base

begin

record ('state, 'event, 'stack) epdaS_conf =
  epdaS_conf_state :: "'state"
  epdaS_conf_scheduler :: "'event list"
  epdaS_conf_stack :: "'stack list"

definition epdaS_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf set"
  where
    "epdaS_configurations G \<equiv>
  {\<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = i, epdaS_conf_stack = s\<rparr> | q i s.
  q \<in> epda_states G
  \<and> set i \<subseteq> epda_events G
  \<and> set s \<subseteq> epda_gamma G}"

definition epdaS_initial_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf set"
  where
    "epdaS_initial_configurations G \<equiv>
  {c.
    epdaS_conf_stack c = [epda_box G]
    \<and> epdaS_conf_state c = epda_initial G}
  \<inter> epdaS_configurations G"

definition epdaS_marking_configurations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf set"
  where
    "epdaS_marking_configurations G \<equiv>
  {c.
    epdaS_conf_scheduler c = []
    \<and> epdaS_conf_state c \<in> epda_marking G}
  \<inter> epdaS_configurations G"

definition epdaS_marking_condition :: "
  ('state,'event, 'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "epdaS_marking_condition G d \<equiv>
  \<exists>i e c.
  d i = Some (pair e c)
  \<and> c \<in> epdaS_marking_configurations G"

definition epdaS_step_relation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "epdaS_step_relation G c1 e c2 \<equiv>
  e \<in> epda_delta G
  \<and> epdaS_conf_state c1 = edge_src e
  \<and> epdaS_conf_state c2 = edge_trg e
  \<and> epdaS_conf_scheduler c1
      = option_to_list (edge_event e) @ epdaS_conf_scheduler c2
  \<and> (\<exists>w.
     epdaS_conf_stack c1 = edge_pop e @ w
     \<and> epdaS_conf_stack c2 = edge_push e @ w)"

definition epdaS_marked_effect :: "
  ('state,'event, 'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation
  \<Rightarrow> 'event list set"
  where
    "epdaS_marked_effect G d \<equiv>
  {w. \<exists>c.
      d 0 = Some (pair None c)
      \<and> w = epdaS_conf_scheduler c}"

definition epdaS_unmarked_effect :: "
  ('state,'event, 'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation
  \<Rightarrow> 'event list set"
  where
    "epdaS_unmarked_effect G d \<equiv>
  {w. \<exists>c c' i e.
      d 0 = Some (pair None c)
      \<and> d i = Some (pair e c')
      \<and> w @ epdaS_conf_scheduler c' = epdaS_conf_scheduler c}"

definition epdaS_string_state :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> 'event list"
  where
    "epdaS_string_state c \<equiv>
  epdaS_conf_scheduler c"

definition epdaS_get_destinations :: "
  ('state,'event,'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation_configuration
  \<Rightarrow> ('state,'event,'stack) epda_destinations set"
  where
    "epdaS_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    {state (epdaS_conf_state c)}
    \<union> (case e of None \<Rightarrow> {} | Some e'\<Rightarrow> {edge e'})"

lemma epdaS_inst_AX_initial_configuration_belongs: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaS_initial_configurations G \<subseteq> epdaS_configurations G)"
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: epdaS_initial_configurations_def)
  done

lemma epdaS_inst_AX_step_relation_preserves_belongs: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c1 e c2. epdaS_step_relation G c1 e c2 \<longrightarrow> c1 \<in> epdaS_configurations G \<longrightarrow> e \<in> epda_step_labels G \<and> c2 \<in> epdaS_configurations G))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G c1 e c2 w)(*strict*)
   apply(simp add: epda_step_labels_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: epda_step_labels_def epdaS_step_relation_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2 w)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G e c2 w epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e w epdaS_conf_scheduler)(*strict*)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac G e w epdaS_conf_scheduler)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e w epdaS_conf_scheduler)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(rename_tac G e w epdaS_conf_scheduler x)(*strict*)
  apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac G e w epdaS_conf_scheduler x a aa)(*strict*)
  apply(erule_tac
      P="edge_push e = aa @ [epda_box G]"
      in disjE)
   apply(rename_tac G e w epdaS_conf_scheduler x a aa)(*strict*)
   apply(clarsimp)
   apply(blast)
  apply(rename_tac G e w epdaS_conf_scheduler x a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e w epdaS_conf_scheduler x a)(*strict*)
  apply(blast)
  done

interpretation "epdaS" : loc_autS_0
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs )
  done

lemma epdaS_inst_AX_string_state_decreases: "
   \<forall>G. valid_epda G \<longrightarrow>
        (\<forall>c1. c1 \<in> epdaS_configurations G \<longrightarrow>
              (\<forall>e c2. epdaS_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. epdaS_string_state c1 = w @ epdaS_string_state c2)))"
  apply(clarsimp)
  apply(rename_tac M c1 e c2)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(simp add: epdaS_configurations_def)
  apply(simp add: epdaS_step_relation_def)
  done

lemma epdaS_inst_lang_sound: "
  (\<forall>M. valid_epda M \<longrightarrow> epdaS.unmarked_language M \<subseteq> epda_effects M)"
  apply(simp add: epdaS.unmarked_language_def epda_effects_def epdaS_unmarked_effect_def epdaS_initial_configurations_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac M x xa d c c' i e)(*strict*)
  apply(subgoal_tac "epdaS.belongs M d")
   apply(rename_tac M x xa d c c' i e)(*strict*)
   prefer 2
   apply(rule epdaS.derivation_initial_belongs)
    apply(rename_tac M x xa d c c' i e)(*strict*)
    apply(force)
   apply(rename_tac M x xa d c c' i e)(*strict*)
   apply(force)
  apply(rename_tac M x xa d c c' i e)(*strict*)
  apply(subgoal_tac "c \<in> epdaS_configurations M")
   apply(rename_tac M x xa d c c' i e)(*strict*)
   prefer 2
   apply(rule epdaS.belongs_configurations)
    apply(rename_tac M x xa d c c' i e)(*strict*)
    apply(force)
   apply(rename_tac M x xa d c c' i e)(*strict*)
   apply(force)
  apply(rename_tac M x xa d c c' i e)(*strict*)
  apply(subgoal_tac "c' \<in> epdaS_configurations M")
   apply(rename_tac M x xa d c c' i e)(*strict*)
   prefer 2
   apply(rule epdaS.belongs_configurations)
    apply(rename_tac M x xa d c c' i e)(*strict*)
    apply(force)
   apply(rename_tac M x xa d c c' i e)(*strict*)
   apply(force)
  apply(rename_tac M x xa d c c' i e)(*strict*)
  apply(simp add: epdaS_configurations_def)
  apply(force)
  done

definition epdaS_get_scheduler :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> 'event list"
  where
    "epdaS_get_scheduler c \<equiv>
  epdaS_conf_scheduler c"

definition epdaS_get_fixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "epdaS_get_fixed_scheduler_DB G d n \<equiv>
  []"

definition epdaS_set_unfixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list
  \<Rightarrow> ('state,'event,'stack) epdaS_conf"
  where
    "epdaS_set_unfixed_scheduler_DB G d n sUF \<equiv>
  (the(get_configuration(d n)))\<lparr>epdaS_conf_scheduler := sUF\<rparr>"

definition epdaS_get_unfixed_scheduler_DB :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state,'event,'stack) epda_step_label, ('state,'event,'stack) epdaS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "epdaS_get_unfixed_scheduler_DB G d n \<equiv>
  epdaS_get_scheduler(the(get_configuration(d n)))"

lemma epdaS_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_epda M \<longrightarrow> (\<forall>f. epdaS.derivation_initial M f \<longrightarrow> epdaS_marking_condition M f \<longrightarrow> epdaS_marked_effect M f \<noteq> {}))"
  apply(clarsimp)
  apply(rename_tac M f)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M f i e c)(*strict*)
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac M f i e q s)(*strict*)
  apply(subgoal_tac "\<exists>c. f 0 = Some (pair None c)")
   apply(rename_tac M f i e q s)(*strict*)
   apply(clarsimp)
  apply(rename_tac M f i e q s)(*strict*)
  apply (metis epdaS.derivation_initial_is_derivation epdaS.some_position_has_details_at_0)
  done

lemma epdaS_inst_AX_unmarked_effect_persists: "
  (\<forall>G. valid_epda G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial epdaS_initial_configurations
               epdaS_step_relation G d \<longrightarrow>
              (\<forall>n. epdaS_unmarked_effect G (derivation_take d n)
                   \<subseteq> epdaS_unmarked_effect G d)))"
  apply(clarsimp)
  apply(rename_tac M d n x)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M d n x c c' i e)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac M d n x c c' i e)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def)
  apply(rename_tac M d n x c c' i e)(*strict*)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac M d n x c c' i e)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M d n x c c' i e)(*strict*)
  apply(rule_tac
      x="c'"
      in exI)
  apply(rule conjI)
   apply(rename_tac M d n x c c' i e)(*strict*)
   apply(simp add: derivation_take_def)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(clarsimp)
  apply(rename_tac M d n x c c' i e)(*strict*)
  apply(force)
  done

lemma epdaS_inst_AX_effect_inclusion1: "
  (\<forall>M f. epdaS_marking_condition M f \<longrightarrow> epdaS_marked_effect M f \<subseteq> epdaS_unmarked_effect M f)"
  apply(clarsimp)
  apply(rename_tac M f x)(*strict*)
  apply(simp add: epdaS_marking_condition_def epdaS_marked_effect_def epdaS_unmarked_effect_def epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac M f i c e ca)(*strict*)
  apply(force)
  done

lemma epdaS_inst_accept: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation_initial G d \<longrightarrow> epdaS_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> epdaS_marking_configurations G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: epdaS_marking_condition_def epdaS_marking_configurations_def)
  done

lemma epdaS_inst_AX_marking_can_not_be_disabled: "
  (\<forall>G d. (\<exists>n. epdaS_marking_condition G (derivation_take d n)) \<longrightarrow> epdaS_marking_condition G d)"
  apply(clarsimp)
  apply(rename_tac G d n)(*strict*)
  apply(simp add: epdaS_marking_condition_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n i e c)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G d n i e c)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(force)
  done

lemma epdaS_inst_AX_marked_effect_persists: "
  (\<forall>G d n. epdaS_marked_effect G (derivation_take d n) \<subseteq> epdaS_marked_effect G d)"
  apply(simp add: epdaS_marked_effect_def derivation_take_def)
  done

lemma epdaS_inst_lang_finite: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaS.finite_marked_language G = epdaS.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: epdaS.finite_marked_language_def epdaS.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G x d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G x d i e c)(*strict*)
   apply (metis epdaS.derivation_take_preserves_derivation_initial)
  apply(rename_tac G x d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d i e c)(*strict*)
   apply(simp add: epdaS_marked_effect_def derivation_take_def)
  apply(rename_tac G x d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(simp add: derivation_take_def)
  apply(rename_tac G x d i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply (metis not_Some_eq maximum_of_domain_derivation_take)
  done

lemma epdaS_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_epda G \<longrightarrow> epdaS.finite_unmarked_language G = epdaS.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: epdaS.finite_unmarked_language_def epdaS.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G x d c c' i e)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G x d c c' i e)(*strict*)
   apply (metis epdaS.derivation_take_preserves_derivation_initial)
  apply(rename_tac G x d c c' i e)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d c c' i e)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G x d c c' i e)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G x d c c' i e)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G x d c c' i e)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(simp add: derivation_take_def)
   apply(rename_tac G x d c c' i e)(*strict*)
   apply(force)
  apply(rename_tac G x d c c' i e)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply (metis not_Some_eq maximum_of_domain_derivation_take)
  done

lemma epdaS_inst_ATS_Language_axioms: "
  ATS_Language_axioms valid_epda epdaS_initial_configurations
     epdaS_step_relation epda_effects epdaS_marking_condition
     epdaS_marked_effect epdaS_unmarked_effect "
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: epdaS_inst_AX_marking_condition_implies_existence_of_effect epdaS_inst_lang_sound epdaS_inst_AX_effect_inclusion1 epdaS_inst_AX_unmarked_effect_persists )
  done

lemma epdaS_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_epda
     epdaS_initial_configurations epdaS_step_relation
     epdaS_marking_condition epdaS_marked_effect epdaS_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: epdaS_inst_lang_finite epdaS_inst_AX_unmarked_language_finite )
  done

lemma epdaS_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_epda epdaS_configurations
     epdaS_step_relation True epdaS_string_state"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(simp add: epdaS_inst_AX_string_state_decreases )
  done

interpretation "epdaS" : loc_autS_1
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaS_string_state"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaS_inst_ATS_Language_axioms epdaS_inst_ATS_Language_by_Finite_Derivations_axioms epdaS_inst_ATS_String_State_Modification_axioms)
  done

lemma epdaS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient: "
  valid_epda G
  \<Longrightarrow> epdaS.derivation G d
  \<Longrightarrow> epdaS.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> j \<le> n
  \<Longrightarrow> suffix (epdaS_get_unfixed_scheduler_DB G d i) (epdaS_get_unfixed_scheduler_DB G d j)"
  apply(induct "j-i" arbitrary: i j)
   apply(rename_tac i j)(*strict*)
   apply(clarsimp)
   apply(rename_tac i y)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x i j)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(rule_tac
      b="epdaS_get_unfixed_scheduler_DB G d (Suc i)"
      in suffix_trans)
   apply(rename_tac x i j y)(*strict*)
   defer
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(thin_tac "epdaS_get_unfixed_scheduler_DB G d (Suc i) \<sqsupseteq> epdaS_get_unfixed_scheduler_DB G d j")
  apply(simp add: epdaS_get_unfixed_scheduler_DB_def suffix_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac x i j y)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac x i j y)(*strict*)
     apply(force)
    apply(rename_tac x i j y)(*strict*)
    apply(force)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS_get_scheduler_def get_configuration_def epdaS_step_relation_def)
  done

lemma epdaS_inst_AX_get_scheduler_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>c. c \<in> epdaS_configurations G \<longrightarrow> epdaS_get_scheduler c \<in> epda_effects G))"
  apply(simp add: epdaS_configurations_def epda_effects_def epdaS_get_scheduler_def)
  apply(clarsimp)
  apply(rename_tac G x q i s)(*strict*)
  apply(force)
  done

lemma epdaS_inst_AX_get_fixed_scheduler_DB_restrict: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>x n. x \<le> n \<longrightarrow> (\<forall>d1. epdaS.derivation G d1 \<longrightarrow> (\<forall>d2. epdaS_get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = epdaS_get_fixed_scheduler_DB G d1 x)))"
  apply(clarsimp)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply(simp add: epdaS_get_fixed_scheduler_DB_def epdaS_get_scheduler_def)
  done

lemma epdaS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation_initial G d \<longrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> epdaS_get_unfixed_scheduler_DB G d n = epdaS_get_unfixed_scheduler_DB G (derivation_take d m) n))"
  apply(clarsimp)
  apply(rename_tac G d n m)(*strict*)
  apply(simp add: epdaS_get_unfixed_scheduler_DB_def)
  apply(simp add: derivation_take_def)
  done

lemma epdaS_inst_AX_get_unfixed_scheduler_DB_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation G d \<longrightarrow> epdaS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>e c. d n = Some (pair e c)) \<longrightarrow> epdaS_get_unfixed_scheduler_DB G d n \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: epda_effects_def epdaS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "c \<in> epdaS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply(rule epdaS.belongs_configurations)
    apply(rename_tac G d n e c)(*strict*)
    apply(force)
   apply(rename_tac G d n e c)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: epdaS_configurations_def epda_effects_def epdaS_get_scheduler_def)
  apply(clarsimp)
  apply(rename_tac G d n e x q i s)(*strict*)
  apply(force)
  done

lemma epdaS_inst_AX_empty_scheduler_in_schedulers: "
  (\<forall>G. valid_epda G \<longrightarrow> [] \<in> epda_effects G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: epda_effects_def)
  done

lemma epdaS_inst_AX_extend_scheduler_closed: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>sE. sE \<in> epda_effects G \<longrightarrow> (\<forall>s. s \<in> epda_effects G \<longrightarrow> sE @ s \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G sE s)(*strict*)
  apply(simp add: epda_effects_def)
  done

lemma epdaS_inst_AX_join_scheduler_fragments_foldl_split: "
  (\<forall>w v. foldl (@) (foldl (@) [] w) v = foldl (@) [] w @ foldl (@) [] v)"
  apply(clarsimp)
  apply(rename_tac w v)(*strict*)
  apply (metis concat_conv_foldl foldl_conv_concat)
  done

lemma epdaS_inst_AX_foldl_join_scheduler_fragments: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>sE. sE \<in> epda_effects G \<longrightarrow> (\<forall>w. set w \<subseteq> epda_effects G \<longrightarrow> foldl (@) sE w = sE @ foldl (@) [] w)))"
  apply(clarsimp)
  apply(rename_tac G sE w)(*strict*)
  apply (metis concat_conv_foldl foldl_conv_concat)
  done

lemma epdaS_inst_ATS_Scheduler_Fragment_axioms: "
  ATS_Scheduler_Fragment_axioms valid_epda epda_effects
     epda_empty_scheduler_fragment (@)"
  apply(simp add: ATS_Scheduler_Fragment_axioms_def)
  apply(simp add: epdaS_inst_AX_join_scheduler_fragments_foldl_split epdaS_inst_AX_extend_scheduler_closed epdaS_inst_AX_foldl_join_scheduler_fragments )
  apply(rule epdaS_inst_AX_empty_scheduler_in_schedulers)
  done

lemma epdaS_inst_AX_extend_unfixed_scheduler_unfixed_scheduler_right_quotient_empty: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> the (right_quotient_word sUF []) = sUF))"
  apply(clarsimp)
  apply(rename_tac G sUF)(*strict*)
  apply(simp add: right_quotient_word_def)
  done

lemma epdaS_inst_AX_unfixed_scheduler_right_quotient_all: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> right_quotient_word sUF sUF = Some []))"
  apply(clarsimp)
  apply(rename_tac G sUF)(*strict*)
  apply(simp add: right_quotient_word_def)
  done

lemma epdaS_inst_ATS_SchedUF_Basic_axioms: "
  ATS_SchedUF_Basic_axioms valid_epda epda_effects epda_empty_scheduler_fragment
     epda_effects epda_empty_unfixed_scheduler right_quotient_word (@)
     epda_unfixed_scheduler_extendable"
  apply(simp add: ATS_SchedUF_Basic_axioms_def)
  apply(simp add: epdaS_inst_AX_empty_scheduler_in_schedulers epdaS_inst_AX_extend_unfixed_scheduler_unfixed_scheduler_right_quotient_empty epdaS_inst_AX_unfixed_scheduler_right_quotient_all epdaS_inst_AX_extend_scheduler_closed )
  done

lemma epdaS_inst_AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>j i. i \<le> j \<longrightarrow> j \<le> n \<longrightarrow> the (right_quotient_word (epdaS_get_unfixed_scheduler_DB G d i) (epdaS_get_unfixed_scheduler_DB G d j)) \<in> epda_effects G))))"
  apply(clarsimp)
  apply(rename_tac G d n y j i)(*strict*)
  apply(simp add: epda_effects_def)
  apply(simp add: epdaS_get_unfixed_scheduler_DB_def epdaS_get_scheduler_def)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac G d n y j i)(*strict*)
   apply(subgoal_tac "\<exists>e c. d j = Some (pair e c)")
    apply(rename_tac G d n y j i)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d n y j i x e ea c ca)(*strict*)
    apply(simp add: get_configuration_def)
    apply(subgoal_tac "\<exists>w. epdaS_string_state c = w @ epdaS_string_state ca")
     apply(rename_tac G d n y j i x e ea c ca)(*strict*)
     prefer 2
     apply(rule_tac
      j="j-i"
      in epdaS.derivation_monotonically_dec)
          apply(rename_tac G d n y j i x e ea c ca)(*strict*)
          apply(force)
         apply(rename_tac G d n y j i x e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac G d n y j i x e ea c ca)(*strict*)
        apply(rule epdaS.derivation_initial_belongs)
         apply(rename_tac G d n y j i x e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac G d n y j i x e ea c ca)(*strict*)
        apply(force)
       apply(rename_tac G d n y j i x e ea c ca)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G d n y j i x e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i x e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac G d n y j i x e ea c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
    apply(subgoal_tac "right_quotient_word (epdaS_conf_scheduler c) (epdaS_conf_scheduler ca) = Some w")
     apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
     prefer 2
     apply(rule right_quotient_word_Some_by_append)
     apply(simp add: get_configuration_def epdaS_string_state_def epdaS_get_scheduler_def)
    apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def epdaS_string_state_def epdaS_get_scheduler_def)
    apply(rule_tac
      A="set (epdaS_conf_scheduler c)"
      in set_mp)
     apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
     apply(subgoal_tac "c \<in> epdaS_configurations G")
      apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
      apply(simp add: epdaS_configurations_def)
      apply(clarsimp)
     apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
     apply(rule epdaS.belongs_configurations)
      apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
      apply(rule epdaS.derivation_initial_belongs)
       apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
     apply(force)
    apply(rename_tac G d n y j i x e ea c ca w)(*strict*)
    apply(force)
   apply(rename_tac G d n y j i)(*strict*)
   apply(rule_tac epdaS.pre_some_position_is_some_position)
     apply(rename_tac G d n y j i)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G d n y j i)(*strict*)
    apply(force)
   apply(rename_tac G d n y j i)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i)(*strict*)
  apply(rule_tac epdaS.pre_some_position_is_some_position)
    apply(rename_tac G d n y j i)(*strict*)
    apply(rule epdaS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G d n y j i)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i)(*strict*)
  apply(force)
  done

lemma epdaS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation G d \<longrightarrow> (\<forall>c. d 0 = Some (pair None c) \<longrightarrow> c \<in> epdaS_initial_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaS_set_unfixed_scheduler_DB G d 0 sUF \<in> epdaS_initial_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G d c sUF)(*strict*)
  apply(simp add: epdaS_set_unfixed_scheduler_DB_def get_configuration_def epdaS_initial_configurations_def epdaS_configurations_def epda_effects_def)
  apply(clarsimp)
  done

lemma epdaS_inst_ATS_SchedUF_DB_axioms: "
  ATS_SchedUF_DB_axioms valid_epda epdaS_configurations
     epdaS_initial_configurations epda_step_labels epdaS_step_relation
     epda_effects epda_effects right_quotient_word
     epda_unfixed_scheduler_extendable epdaS_set_unfixed_scheduler_DB
     epdaS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_SchedUF_DB_axioms_def)
  apply(rule conjI)
   apply(rule epdaS_inst_AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB)
  apply(simp add: epdaS_inst_AX_get_unfixed_scheduler_DB_closed epdaS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations epdaS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take )
  done

lemma epdaS_inst_ATS_SchedF_Basic_axioms: "
  ATS_SchedF_Basic_axioms valid_epda epda_fixed_schedulers
     epda_empty_fixed_scheduler"
  apply(simp add: ATS_SchedF_Basic_axioms_def)
  done

lemma epdaS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation G d \<longrightarrow> epdaS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaS_get_fixed_scheduler_DB G d n = [])))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: epdaS_get_fixed_scheduler_DB_def)
  done

lemma epdaS_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_epda epdaS_configurations epda_step_labels
     epdaS_step_relation epda_fixed_schedulers
     epda_fixed_scheduler_extendable epdaS_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_DB_axioms_def)
  apply(simp add: epdaS_inst_AX_get_fixed_scheduler_DB_restrict epdaS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers )
  done

lemma epdaS_inst_ATS_Sched_axioms: "
  ATS_Sched_axioms valid_epda epdaS_configurations epda_effects
     epda_empty_scheduler_fragment (@) epda_effects epda_effects
     epda_empty_scheduler epdaS_get_scheduler (@)"
  apply(simp add: ATS_Sched_axioms_def)
  apply(simp add: epdaS_inst_AX_empty_scheduler_in_schedulers epdaS_inst_AX_get_scheduler_closed epdaS_inst_AX_extend_scheduler_closed )
  done

lemma epdaS_inst_ATS_Sched_Basic_axioms: "
  ATS_Sched_Basic_axioms valid_epda epda_fixed_schedulers
     epda_fixed_scheduler_extendable epda_effects
     epda_unfixed_scheduler_extendable epda_effects (@)"
  apply(simp add: ATS_Sched_Basic_axioms_def)
  done

interpretation "epdaS" : loc_autS_2
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaS_string_state"
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
  "epdaS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "epdaS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "epdaS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "epdaS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaS_inst_ATS_Language_by_Finite_Derivations_axioms epdaS_inst_ATS_String_State_Modification_axioms epdaS_inst_ATS_Language_axioms )
  apply(simp add: epdaS_inst_ATS_Scheduler_Fragment_axioms epdaS_inst_ATS_SchedUF_Basic_axioms epdaS_inst_ATS_SchedUF_DB_axioms epdaS_inst_ATS_SchedF_Basic_axioms epdaS_inst_ATS_SchedF_DB_axioms epdaS_inst_ATS_Sched_axioms epdaS_inst_ATS_Sched_Basic_axioms )
  done

lemma epdaS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaS_get_fixed_scheduler_DB G d n @ epdaS_get_unfixed_scheduler_DB G d n \<in> epda_effects G)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: epdaS_get_scheduler_def epdaS_get_fixed_scheduler_DB_def epdaS_get_unfixed_scheduler_DB_def epda_effects_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b x)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "b \<in> epdaS_configurations G")
   apply(rename_tac G d n option b x)(*strict*)
   apply(simp add: epdaS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G d n option x q i s)(*strict*)
   apply(force)
  apply(rename_tac G d n option b x)(*strict*)
  apply(rule epdaS.belongs_configurations)
   apply(rename_tac G d n option b x)(*strict*)
   apply(rule epdaS.derivation_initial_belongs)
    apply(rename_tac G d n option b x)(*strict*)
    apply(force)
   apply(rename_tac G d n option b x)(*strict*)
   apply(force)
  apply(rename_tac G d n option b x)(*strict*)
  apply(force)
  done

lemma epdaS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>d. epdaS.derivation G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> epdaS_get_fixed_scheduler_DB G d n @ epdaS_get_unfixed_scheduler_DB G d n = ATS_Sched.get_scheduler_nth epdaS_get_scheduler d n)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: epdaS_get_scheduler_def epdaS_get_fixed_scheduler_DB_def epdaS_get_unfixed_scheduler_DB_def epda_effects_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS.get_scheduler_nth_def)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS_get_scheduler_def epdaS_get_fixed_scheduler_DB_def epdaS_get_unfixed_scheduler_DB_def epda_effects_def)
  done

lemma epdaS_inst_AX_sched_modification_preserves_steps: "
  (\<forall>G. valid_epda G \<longrightarrow> (\<forall>dh n. maximum_of_domain dh n \<longrightarrow> epdaS.derivation G dh \<longrightarrow> epdaS.belongs G dh \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> (\<forall>m e2 c2. dh (Suc m) = Some (pair (Some e2) c2) \<longrightarrow> (\<forall>e1 c1. dh m = Some (pair e1 c1) \<longrightarrow> epdaS_step_relation G c1 e2 c2 \<longrightarrow> epdaS_step_relation G (epdaS_set_unfixed_scheduler_DB G dh m (the (right_quotient_word (epdaS_get_unfixed_scheduler_DB G dh m) (epdaS_get_unfixed_scheduler_DB G dh n)) @ sUF)) e2 (epdaS_set_unfixed_scheduler_DB G dh (Suc m) (the (right_quotient_word (epdaS_get_unfixed_scheduler_DB G dh (Suc m)) (epdaS_get_unfixed_scheduler_DB G dh n)) @ sUF)))))))"
  apply(clarsimp)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1)(*strict*)
  apply(simp add: epdaS_set_unfixed_scheduler_DB_def get_configuration_def epdaS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac G dh n sUF m e2 c2 e1 c1)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
  apply(simp add: get_configuration_def epdaS_get_scheduler_def)
  apply(subgoal_tac "Suc m\<le>n")
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
   prefer 2
   apply(rule epdaS.allPreMaxDomSome_prime)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c1 = w @ epdaS_string_state c")
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
   prefer 2
   apply(rule_tac
      j="n-m"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c2 = w @ epdaS_string_state c")
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
   prefer 2
   apply(rule_tac
      j="n-Suc m"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(rule_tac
      t="right_quotient_word (w @ epdaHS_conf_scheduler c) (epdaHS_conf_scheduler c)"
      and s="Some w"
      in ssubst)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa)(*strict*)
  apply(rule_tac
      t="right_quotient_word (wa @ epdaHS_conf_scheduler c) (epdaHS_conf_scheduler c)"
      and s="Some wa"
      in ssubst)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c w wa)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c wa wb)(*strict*)
  apply(rule_tac
      t="right_quotient_word (option_to_list (edge_event e2) @ wa @ epdaS_conf_scheduler c) (epdaS_conf_scheduler c)"
      and s="Some (option_to_list (edge_event e2) @ wa)"
      in ssubst)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c wa wb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c wa wb)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule_tac
      t="right_quotient_word (wa @ epdaS_conf_scheduler c) (epdaS_conf_scheduler c)"
      and s="Some wa"
      in ssubst)
   apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c wa wb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sUF m e2 c2 e1 c1 e c wa wb)(*strict*)
  apply(force)
  done

lemma epdaS_inst_ATS_Sched_DB0_axioms: "
  ATS_Sched_DB0_axioms valid_epda epdaS_configurations
     epdaS_initial_configurations epda_step_labels epdaS_step_relation
     epda_fixed_scheduler_extendable epda_effects right_quotient_word (@)
     epda_unfixed_scheduler_extendable epda_effects epdaS_get_scheduler (@)
     epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB
     epdaS_get_fixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB0_axioms_def)
  apply(rule conjI)
   apply(simp add: epdaS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime )
  apply(rule conjI)
   apply(simp add: epdaS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth )
  apply(rule epdaS_inst_AX_sched_modification_preserves_steps)
  done

interpretation "epdaS" : loc_autS_3
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaS_string_state"
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
  "epdaS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "epdaS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "epdaS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "epdaS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaS_inst_ATS_Language_by_Finite_Derivations_axioms epdaS_inst_ATS_String_State_Modification_axioms epdaS_inst_ATS_Language_axioms )
  apply(simp add: epdaS_inst_ATS_Sched_Basic_axioms epdaS_inst_ATS_Scheduler_Fragment_axioms epdaS_inst_ATS_SchedUF_Basic_axioms epdaS_inst_ATS_SchedUF_DB_axioms epdaS_inst_ATS_SchedF_Basic_axioms epdaS_inst_ATS_SchedF_DB_axioms epdaS_inst_ATS_Sched_axioms )
  apply(simp add: epdaS_inst_ATS_Sched_DB0_axioms )
  done

lemma epdaS_inst_AX_replace_unfixed_scheduler_DB_sound: "
  \<forall>G. valid_epda G \<longrightarrow> (\<forall>d n. maximum_of_domain d n \<longrightarrow> epdaS.derivation_initial G d \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G \<longrightarrow> epdaS_get_unfixed_scheduler_DB G (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G d sUF n) n = sUF))"
  apply(clarsimp)
  apply(rename_tac G d n sUF)(*strict*)
  apply(simp add: epdaS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac G d n sUF)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac G d n sUF)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(force)
    apply(rename_tac G d n sUF)(*strict*)
    apply(force)
   apply(rename_tac G d n sUF)(*strict*)
   apply(force)
  apply(rename_tac G d n sUF)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n sUF e c)(*strict*)
  apply(simp add: epdaS.replace_unfixed_scheduler_DB_def epdaS.map_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="right_quotient_word (epdaS_get_unfixed_scheduler_DB G d n) (epdaS_get_unfixed_scheduler_DB G d n)"
      and s="Some []"
      in ssubst)
   apply(rename_tac G d n sUF e c)(*strict*)
   apply (metis right_quotient_word_full)
  apply(rename_tac G d n sUF e c)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaS_set_unfixed_scheduler_DB_def get_configuration_def epdaS_get_scheduler_def)
  done

lemma epdaS_inst_ATS_Sched_DB_axioms: "
  ATS_Sched_DB_axioms valid_epda epdaS_initial_configurations
     epdaS_step_relation epda_effects right_quotient_word (@)
     epda_unfixed_scheduler_extendable epdaS_set_unfixed_scheduler_DB
     epdaS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB_axioms_def)
  apply(rule epdaS_inst_AX_replace_unfixed_scheduler_DB_sound)
  done

interpretation "epdaS" : loc_autS_4
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaS_string_state"
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
  "epdaS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "epdaS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "epdaS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "epdaS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs epdaS_inst_ATS_Language_by_Finite_Derivations_axioms epdaS_inst_ATS_String_State_Modification_axioms epdaS_inst_ATS_Language_axioms epdaS_inst_ATS_Sched_Basic_axioms epdaS_inst_ATS_Scheduler_Fragment_axioms epdaS_inst_ATS_SchedUF_Basic_axioms epdaS_inst_ATS_SchedUF_DB_axioms epdaS_inst_ATS_SchedF_Basic_axioms epdaS_inst_ATS_SchedF_DB_axioms epdaS_inst_ATS_Sched_axioms epdaS_inst_ATS_Sched_DB0_axioms epdaS_inst_ATS_Sched_DB_axioms )
  done

lemma epdaS_step_exists: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> epdaS_conf_state c = edge_src e
  \<Longrightarrow> prefix (option_to_list (edge_event e)) (epdaS_conf_scheduler c)
  \<Longrightarrow> prefix (edge_pop e) (epdaS_conf_stack c)
  \<Longrightarrow> \<exists>c'. epdaS_step_relation G c e c'"
  apply(rule_tac
      x="\<lparr>epdaS_conf_state=SSq,epdaS_conf_scheduler=drop(length(option_to_list (edge_event e)))(epdaS_conf_scheduler c),epdaS_conf_stack=(edge_push e)@drop(length(edge_pop e))(epdaS_conf_stack c)\<rparr>" for SSq
      in exI)
  apply(simp add: epdaS_step_relation_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(simp add: option_to_list_def)
   apply(case_tac "edge_event e")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac a ca caa)(*strict*)
   apply (metis drop1)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca caa)(*strict*)
  apply (metis append_eq_conv_conj)
  done

lemmas epdaS_interpretations =
  epdaS_inst_AX_initial_configuration_belongs
  epdaS_inst_AX_step_relation_preserves_belongs
  epdaS_inst_ATS_Language_by_Finite_Derivations_axioms
  epdaS_inst_ATS_String_State_Modification_axioms
  epdaS_inst_ATS_Language_axioms
  epdaS_inst_ATS_Sched_Basic_axioms
  epdaS_inst_ATS_Scheduler_Fragment_axioms
  epdaS_inst_ATS_SchedUF_Basic_axioms
  epdaS_inst_ATS_SchedUF_DB_axioms
  epdaS_inst_ATS_SchedF_Basic_axioms
  epdaS_inst_ATS_SchedF_DB_axioms
  epdaS_inst_ATS_Sched_axioms
  epdaS_inst_ATS_Sched_DB0_axioms
  epdaS_inst_ATS_Sched_DB_axioms

lemma valid_epda_preserves_box_at_end: "
  valid_epda G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>w. epdaS_conf_stack c = w @ [epda_box G]"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 w)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(subgoal_tac "prefix w (edge_pop e2) \<or> prefix (edge_pop e2) w")
    apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
   apply(erule disjE)
    apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 c1 w wa ca)(*strict*)
    apply(case_tac e2)
    apply(rename_tac n c e1 e2 c1 w wa ca edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 c1 w wa ca edge_event edge_push)(*strict*)
    apply(case_tac ca)
     apply(rename_tac n c e1 c1 w wa ca edge_event edge_push)(*strict*)
     apply(clarsimp)
    apply(rename_tac n c e1 c1 w wa ca edge_event edge_push a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 c1 w edge_event)(*strict*)
    apply(simp add: must_terminated_by_def may_terminated_by_def append_language_def kleene_star_def)
    apply(clarsimp)
    apply(rename_tac n c e1 c1 w edge_event a aa)(*strict*)
    apply(erule_tac
      P="epdaS_conf_stack c = aa @ [epda_box G]"
      in disjE)
     apply(rename_tac n c e1 c1 w edge_event a aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac n c e1 c1 w edge_event a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 c1 w edge_event a)(*strict*)
    apply(erule disjE)
     apply(rename_tac n c e1 c1 w edge_event a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n c e1 c1 w edge_event a)(*strict*)
    apply(clarsimp)
    apply(rename_tac n c e1 c1 w edge_event)(*strict*)
    apply(case_tac c)
    apply(rename_tac n c e1 c1 w edge_event epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
    apply(case_tac c1)
    apply(rename_tac n c e1 c1 w edge_event epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka epdaS_conf_stateaa epdaS_conf_scheduleraa epdaS_conf_stackaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
  apply(simp add: valid_epda_def)
  done

definition epdaS_produce_from_before_pop :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'stack
  \<Rightarrow> 'state
  \<Rightarrow> 'event list set"
  where
    "epdaS_produce_from_before_pop G qi A qt \<equiv>
  {w. \<exists>d q s.
    epdaS.derivation G d
    \<and> epdaS.belongs G d
    \<and> d 0 = Some (pair None
          \<lparr>epdaS_conf_state = qi,
          epdaS_conf_scheduler = w,
          epdaS_conf_stack = A # s\<rparr>)
    \<and> (\<exists>j e e'.
        d j = Some (pair e
            \<lparr>epdaS_conf_state = q,
            epdaS_conf_scheduler = [],
            epdaS_conf_stack = A # s\<rparr>)
        \<and> d (Suc j) = Some (pair e'
              \<lparr>epdaS_conf_state = qt,
              epdaS_conf_scheduler = [],
              epdaS_conf_stack = s\<rparr>)
        \<and> (\<forall>k \<le> j. \<forall>e c.
            d k = Some (pair e c)
            \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ [A] @ s)))}"

lemma epdaS_produce_from_before_popCons: "
  valid_epda G
  \<Longrightarrow> \<lparr>edge_src = src, edge_event = Some a, edge_pop = [A], edge_push = [A], edge_trg = trg\<rparr> \<in> epda_delta G
  \<Longrightarrow> w \<in> epdaS_produce_from_before_pop G trg A q
  \<Longrightarrow> a # w \<in> epdaS_produce_from_before_pop G src A q"
  apply(simp add: epdaS_produce_from_before_pop_def)
  apply(clarsimp)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = a # w, epdaS_conf_stack = A # s\<rparr> \<lparr>edge_src = src, edge_event = Some a, edge_pop = [A], edge_push = [A], edge_trg = trg\<rparr> \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = A # s\<rparr>) d (Suc 0)"
      in exI)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(rule epdaS.derivation_append_preserves_derivation)
     apply(rename_tac d qa s j e e')(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def)
     apply(simp add: option_to_list_def)
    apply(rename_tac d qa s j e e')(*strict*)
    apply(force)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(rule conjI)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(rule epdaS.derivation_append_preserves_belongs)
     apply(rename_tac d qa s j e e')(*strict*)
     apply(force)
    apply(rename_tac d qa s j e e')(*strict*)
    apply(rule epdaS.der2_belongs)
      apply(rename_tac d qa s j e e')(*strict*)
      apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = A # s\<rparr> \<in> epdaS_configurations G")
       apply(rename_tac d qa s j e e')(*strict*)
       apply(simp add: epdaS_configurations_def)
       apply(subgoal_tac "valid_epda_step_label G \<lparr>edge_src = src, edge_event = Some a, edge_pop = [A], edge_push = [A], edge_trg = trg\<rparr>")
        apply(rename_tac d qa s j e e')(*strict*)
        apply(simp add: valid_epda_step_label_def)
        apply(clarsimp)
        apply(simp add: option_to_set_def)
       apply(rename_tac d qa s j e e')(*strict*)
       apply(simp add: valid_epda_def)
      apply(rename_tac d qa s j e e')(*strict*)
      apply(rule epdaS.belongs_configurations)
       apply(rename_tac d qa s j e e')(*strict*)
       apply(force)
      apply(rename_tac d qa s j e e')(*strict*)
      apply(force)
     apply(rename_tac d qa s j e e')(*strict*)
     apply(simp add: epda_step_labels_def)
    apply(rename_tac d qa s j e e')(*strict*)
    apply(rule epdaS.belongs_configurations)
     apply(rename_tac d qa s j e e')(*strict*)
     apply(force)
    apply(rename_tac d qa s j e e')(*strict*)
    apply(force)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(force)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(rule_tac
      x="qa"
      in exI)
  apply(rule_tac
      x="s"
      in exI)
  apply(rule conjI)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(rule_tac
      x="Suc j"
      in exI)
  apply(rule conjI)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(rule conjI)
   apply(rename_tac d qa s j e e')(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d qa s j e e')(*strict*)
  apply(clarsimp)
  apply(rename_tac d qa s j e e' k ea c)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac k)
   apply(rename_tac d qa s j e e' k ea c)(*strict*)
   apply(force)
  apply(rename_tac d qa s j e e' k ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d qa s j e e' ea c nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(case_tac "nat")
   apply(rename_tac d qa s j e e' ea c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d qa s j e e' ea c nat nata)(*strict*)
  apply(clarsimp)
  done

definition epdaS_required_edges :: "
  ('state, 'event, 'stack)epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "epdaS_required_edges G \<equiv>
  {e \<in> epda_delta G.
    \<exists>d n c.
      epdaS.derivation_initial G d
      \<and> d n = Some (pair (Some e) c)
      \<and> (\<exists>k\<ge>n. \<exists>e c.
          d k = Some (pair e c)
          \<and> c \<in> epdaS_marking_configurations G)}"

lemma epdaS_is_forward_target_deterministic_accessible: "
  epdaS.is_forward_target_deterministic_accessible G"
  apply(simp add: epdaS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  done

end
