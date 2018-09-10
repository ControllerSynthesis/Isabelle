section {*I\_epda\_S\_HS*}
theory
  I_epda_S_HS

imports
  I_epda_S
  I_epda_HS

begin

definition epdaS_vs_epdaHS_TSstructure_rel :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epdaS_vs_epdaHS_TSstructure_rel G1 G2 \<equiv>
  valid_epda G1
  \<and> G1 = G2"
declare epdaS_vs_epdaHS_TSstructure_rel_def [simp add]

definition epdaS_vs_epdaHS_effect_rel :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "epdaS_vs_epdaHS_effect_rel G1 G2 o1 o2 \<equiv>
  G1 = G2
  \<and> o1 = o2"
declare epdaS_vs_epdaHS_effect_rel_def [simp add]

definition epdaS_vs_epdaHS_label_relation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "epdaS_vs_epdaHS_label_relation G1 G2 e1 e2 \<equiv>
  e1 = e2
  \<and> e1 \<in> epda_delta G1"
declare epdaS_vs_epdaHS_label_relation_def [simp add]

definition epdaHS2epdaS_derivation :: "
  (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation"
  where
    "epdaHS2epdaS_derivation d \<equiv>
  (\<lambda>n. case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
    Some (pair e
      \<lparr>epdaS_conf_state = epdaHS_conf_state c,
      epdaS_conf_scheduler = epdaHS_conf_scheduler c,
      epdaS_conf_stack = epdaHS_conf_stack c\<rparr>))"

definition epdaS_vs_epdaHS_derivation_bisimulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation
  \<Rightarrow> bool"
  where
    "epdaS_vs_epdaHS_derivation_bisimulation G1 G2 d1 d2 \<equiv>
  valid_epda G1
  \<and> G1 = G2
  \<and> epdaHS.derivation_initial G2 d2
  \<and> (\<exists>n. maximum_of_domain d2 n)
  \<and> epdaHS2epdaS_derivation d2 = d1"
declare epdaS_vs_epdaHS_derivation_bisimulation_def [simp add]

lemma epdaHS2epdaS_derivation_preserves_derivation_initial: "
  valid_epda P
  \<Longrightarrow> epdaHS.derivation_initial P d
  \<Longrightarrow> epdaS.derivation_initial P (epdaHS2epdaS_derivation d)"
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(simp add: epdaS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: epdaHS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: epdaS_initial_configurations_def epdaHS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: epdaS_configurations_def epdaHS_configurations_def)
   apply(clarsimp)
  apply(simp add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation P c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS_step_relation_def epdaHS_step_relation_def)
  done

lemma epdaHS2epdaS_derivation_preserves_step_labels: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>c. (epdaHS2epdaS_derivation d) n = Some (pair e c)"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc n"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
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
  apply(rename_tac n c e1 e2 c1 ca)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  done

lemma epdaHS2epdaS_derivation_preserves_maximum_of_domain: "
  valid_epda G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (epdaHS2epdaS_derivation d) n"
  apply(simp add: maximum_of_domain_def epdaHS2epdaS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

definition epdaS2epdaHS_derivation :: "
  ('state, 'event, 'q) epda
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaHS_conf) derivation"
  where
    "epdaS2epdaHS_derivation G d \<equiv>
  (\<lambda>n. case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
    Some (pair e
      \<lparr>epdaHS_conf_state = epdaS_conf_state c,
      epdaHS_conf_history = the(right_quotient_word
        (epdaS_conf_scheduler(the(get_configuration(d 0))))
        (epdaS_conf_scheduler c)),
      epdaHS_conf_scheduler = epdaS_conf_scheduler c,
      epdaHS_conf_stack = epdaS_conf_stack c\<rparr>))"

lemma epdaS2epdaHS_derivation_preserves_derivation_initial: "
  valid_epda P
  \<Longrightarrow> epdaS.derivation_initial P d
  \<Longrightarrow> epdaHS.derivation_initial P (epdaS2epdaHS_derivation P d)"
  apply(simp add: epdaS2epdaHS_derivation_def)
  apply(simp add: epdaHS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: epdaS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: epdaS_initial_configurations_def epdaHS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: epdaS_configurations_def epdaHS_configurations_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: right_quotient_word_def)
  apply(simp add: epdaHS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation P c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS_step_relation_def epdaHS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(simp add: epdaS.derivation_initial_def)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
  apply(subgoal_tac "valid_epda_step_label P e2")
   apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c = w @ (epdaS_string_state c1)")
   apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
   prefer 2
   apply(rule_tac
      j = "nat"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
      apply(rule epdaS.derivation_initial_belongs)
       apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c1 = w @ (epdaS_string_state c2)")
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   prefer 2
   apply(rule_tac
      j = "Suc 0"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
      apply(rule epdaS.derivation_initial_belongs)
       apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(subgoal_tac "c \<in> epdaS_configurations P")
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   prefer 2
   apply(rule epdaS.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
    apply(rule epdaS.derivation_initial_belongs)
     apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(rule_tac
      t = "right_quotient_word (wa @ option_to_list (edge_event e2) @ epdaS_conf_scheduler c2) (epdaS_conf_scheduler c2)"
      and s = "Some(wa @ option_to_list (edge_event e2))"
      in ssubst)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule_tac
      t = "right_quotient_word (wa @ option_to_list (edge_event e2) @ epdaS_conf_scheduler c2) (option_to_list (edge_event e2) @ epdaS_conf_scheduler c2)"
      and s = "Some wa"
      in ssubst)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(force)
  done

lemma epdaS2epdaHS_derivation_preserves_maximum_of_domain: "
  valid_epda G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (epdaS2epdaHS_derivation G d) n"
  apply(simp add: maximum_of_domain_def epdaS2epdaHS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma epda_S_HS_relation_coincide_hlp: "
  valid_epda G2
  \<Longrightarrow> epdaHS.derivation_initial G2 d2
  \<Longrightarrow> maximum_of_domain d2 x
  \<Longrightarrow> epdaS2epdaHS_derivation G2 (epdaHS2epdaS_derivation d2) xa = d2 xa"
  apply(induct xa)
   apply(simp add: epdaHS2epdaS_derivation_def epdaS2epdaHS_derivation_def)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(case_tac c)
    apply(rename_tac c epdaHS_conf_statea epdaHS_conf_history epdaHS_conf_schedulera epdaHS_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac epdaHS_conf_state epdaHS_conf_history epdaHS_conf_scheduler epdaHS_conf_stack)(*strict*)
    apply(simp add: epdaHS.derivation_initial_def)
    apply(clarsimp)
    apply(simp add: epdaHS_initial_configurations_def)
    apply(clarsimp)
    apply(rename_tac epdaHS_conf_scheduler)(*strict*)
    apply(simp add: get_configuration_def)
    apply(simp add: butlast_if_match_def right_quotient_word_def)
   apply(simp add: epdaHS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d2 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "d2 (Suc xa)")
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHS2epdaS_derivation_def epdaS2epdaHS_derivation_def)
  apply(rename_tac xa a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 xa = Some (pair e1 c1) \<and> d2 (Suc xa) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G2 c1 e2 c2")
   apply(rename_tac xa a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc xa"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac xa a)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
    apply(rename_tac xa a)(*strict*)
    apply(force)
   apply(rename_tac xa a)(*strict*)
   apply(force)
  apply(rename_tac xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS2epdaHS_derivation_def)
  apply(simp add: epdaHS2epdaS_derivation_def epdaS2epdaHS_derivation_def)
  apply(subgoal_tac "\<exists> c. d2 0 = Some (pair None c)")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: epdaHS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d2 0")
    apply(rename_tac xa e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa e1 e2 c1 c2 a)(*strict*)
   apply(case_tac a)
   apply(rename_tac xa e1 e2 c1 c2 a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>w. epdaHS_string_state c = w @ epdaHS_string_state c1")
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d2"
      in epdaHS.derivation_monotonically_dec)
        apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
        apply(force)
       apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
      apply(rule epdaHS.derivation_initial_belongs)
       apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
      apply(force)
     apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
    apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   apply(force)
  apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaHS_string_state c1 = w @ epdaHS_string_state c2")
   apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d2"
      and i = "xa"
      and j = "Suc 0"
      in epdaHS.derivation_monotonically_dec)
        apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
        apply(force)
       apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
      apply(rule epdaHS.derivation_initial_belongs)
       apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
      apply(force)
     apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
    apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
   apply(force)
  apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
  apply(simp add: epdaHS_string_state_def)
  apply(simp add: epdaHS_step_relation_def)
  apply(subgoal_tac "valid_epda_step_label G2 e2")
   apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c2 c w wb)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(case_tac c2)
  apply(rename_tac xa e1 e2 c2 c w wb epdaHS_conf_statea epdaHS_conf_historya epdaHS_conf_schedulera epdaHS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c w wb epdaHS_conf_schedulera)(*strict*)
  apply(rule_tac
      t = "right_quotient_word (w @ option_to_list (edge_event e2) @ epdaHS_conf_schedulera) epdaHS_conf_schedulera"
      and s = "Some(w @ option_to_list (edge_event e2))"
      in ssubst)
   apply(rename_tac xa e1 e2 c w wb epdaHS_conf_schedulera)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac xa e1 e2 c w wb epdaHS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "right_quotient_word (w @ option_to_list (edge_event e2) @ epdaHS_conf_schedulera) (option_to_list (edge_event e2) @ epdaHS_conf_schedulera)"
      and s = "Some w"
      in ssubst)
   apply(rename_tac xa e1 e2 c w wb epdaHS_conf_schedulera)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac xa e1 e2 c w wb epdaHS_conf_schedulera)(*strict*)
  apply(force)
  done

corollary epda_S_HS_relation_coincide: "
  (\<lambda>G1 G2 d1 d2. (valid_epda G1) \<and> (G1 = G2) \<and> epdaHS.derivation_initial G2 d2 \<and> (\<exists>n. maximum_of_domain d2 n) \<and> epdaHS2epdaS_derivation d2 = d1) = (\<lambda>G1 G2 d1 d2. (valid_epda G1) \<and> (G1 = G2) \<and> epdaS.derivation_initial G1 d1 \<and> (\<exists>n. maximum_of_domain d1 n) \<and> epdaS2epdaHS_derivation G1 d1 = d2)"
  apply(rule ext)+
  apply(rename_tac G1 G2 d1 d2)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G1 G2 d1 d2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 d1 x)(*strict*)
    apply (metis epdaS2epdaHS_derivation_preserves_derivation_initial)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 d1 x)(*strict*)
    apply (metis epdaS2epdaHS_derivation_preserves_maximum_of_domain)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(simp add: epdaS2epdaHS_derivation_def epdaHS2epdaS_derivation_def)
   apply(rule ext)
   apply(rename_tac G2 d1 x n)(*strict*)
   apply(case_tac "d1 n")
    apply(rename_tac G2 d1 x n)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 d1 x n a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G2 d1 x n a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 d1 d2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 d2 x)(*strict*)
   apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 d2 x)(*strict*)
   apply (metis epdaHS2epdaS_derivation_preserves_maximum_of_domain)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule ext)
  apply(rename_tac G2 d2 x xa)(*strict*)
  apply(rule epda_S_HS_relation_coincide_hlp)
    apply(rename_tac G2 d2 x xa)(*strict*)
    apply(force)+
  done

lemma epdaS_vs_epdaHS_inst_AX_AX_initial_contained1: "
  (\<forall>G1. valid_epda G1 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>c2. epdaHS.derivation_initial G1 (der1 c2) \<and> Ex (maximum_of_domain (der1 c2)) \<and> epdaHS2epdaS_derivation (der1 c2) = der1 c1)))"
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = epdaS_conf_state c1, epdaHS_conf_history = [], epdaHS_conf_scheduler = epdaS_conf_scheduler c1, epdaHS_conf_stack = epdaS_conf_stack c1\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 c1)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 c1)(*strict*)
    apply(rule epdaHS.der1_is_derivation)
   apply(rename_tac G1 c1)(*strict*)
   apply(simp add: der1_def)
   apply(simp add: epdaHS_initial_configurations_def epdaHS_configurations_def epdaS_initial_configurations_def epdaS_configurations_def)
   apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1)(*strict*)
   apply(rule_tac
      x = "0"
      in exI)
   apply (metis der1_maximum_of_domain)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule ext)
  apply(rename_tac G1 c1 x)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def der1_def der1_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_AX_initial_contained2: "
  (\<forall>G1. valid_epda G1 \<longrightarrow> (\<forall>c2. c2 \<in> epdaHS_initial_configurations G1 \<longrightarrow> epdaHS.derivation_initial G1 (der1 c2) \<and> Ex (maximum_of_domain (der1 c2)) \<and> (\<exists>c1. epdaHS2epdaS_derivation (der1 c2) = der1 c1)))"
  apply(clarsimp)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c2)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 c2)(*strict*)
    apply(rule epdaHS.der1_is_derivation)
   apply(rename_tac G1 c2)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c2)(*strict*)
   apply(rule_tac
      x = "0"
      in exI)
   apply (metis der1_maximum_of_domain)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule_tac
      x = "X" for X
      in exI)
  apply(simp add: epdaHS2epdaS_derivation_def der1_def der1_def)
  apply(rule ext)
  apply(rename_tac G1 c2 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c2)(*strict*)
  apply(force)
  done

lemma epdaS_vs_epdaHS_inst_AX_on_derivation_initial1: "
  (\<forall>G1 d1. valid_epda G1 \<and> (\<exists>d2. epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<and> epdaHS2epdaS_derivation d2 = d1) \<longrightarrow> epdaS.derivation_initial G1 d1)"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
  done

lemma epdaS_vs_epdaHS_inst_AX_on_finite1: "
  (\<forall>G1 d1. valid_epda G1 \<and> (\<exists>d2. epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<and> epdaHS2epdaS_derivation d2 = d1) \<longrightarrow> Ex (maximum_of_domain d1))"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(rule_tac
      x = "x"
      in exI)
  apply (metis epdaHS2epdaS_derivation_preserves_maximum_of_domain)
  done

lemma epdaS_vs_epdaHS_inst_AX_equal_length: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n1. maximum_of_domain (epdaHS2epdaS_derivation d2) n1 \<longrightarrow> (\<forall>n2. maximum_of_domain d2 n2 \<longrightarrow> n1 = n2)))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n1 x n2)(*strict*)
  apply (metis epdaS.derivation_initial_is_derivation epdaS.maximum_of_domainUnique epdaHS2epdaS_derivation_preserves_derivation_initial epdaHS2epdaS_derivation_preserves_maximum_of_domain)
  done

lemma epdaS_vs_epdaHS_inst_AX_simulate12: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (epdaHS2epdaS_derivation d2) n \<longrightarrow> maximum_of_domain d2 n \<longrightarrow> (\<forall>e1 c1'. epdaS_step_relation G1 (the (get_configuration (epdaHS2epdaS_derivation d2 n))) e1 c1' \<longrightarrow> (\<exists>c2'. epdaHS_step_relation G1 (the (get_configuration (d2 n))) e1 c2' \<and> e1 \<in> epda_delta G1 \<and> (let d2' = derivation_append d2 (der2 (the (get_configuration (d2 n))) e1 c2') n in epdaHS.derivation_initial G1 d2' \<and> Ex (maximum_of_domain d2') \<and> epdaHS2epdaS_derivation d2' = derivation_append (epdaHS2epdaS_derivation d2) (der2 (the (get_configuration (epdaHS2epdaS_derivation d2 n))) e1 c1') n)))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x e1 c1')(*strict*)
  apply(subgoal_tac "n = x")
   apply(rename_tac G1 d2 n x e1 c1')(*strict*)
   prefer 2
   apply (metis epdaS_vs_epdaHS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x e1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 x = Some (pair e c)")
   apply(rename_tac G1 d2 x e1 c1')(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x e1 c1')(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(rule_tac
      x = "\<lparr>epdaHS_conf_state = epdaS_conf_state c1', epdaHS_conf_history = epdaHS_conf_history c@(option_to_list(edge_event e1)), epdaHS_conf_scheduler = epdaS_conf_scheduler c1', epdaHS_conf_stack = epdaS_conf_stack c1'\<rparr>"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(simp add: epdaHS_step_relation_def epdaS_step_relation_def get_configuration_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(simp add: Let_def)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
    apply(rule epdaHS.derivation_append_preserves_derivation)
      apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
     apply (rule epdaHS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def get_configuration_def)
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(rule_tac
      x = "x+Suc 0"
      in exI)
   apply (metis Nat.add_0_right add_Suc_right concat_has_max_dom der2_maximum_of_domain)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(rule ext)
  apply(rename_tac G1 d2 x e1 c1' e c xa)(*strict*)
  apply(simp add: derivation_append_def epdaHS2epdaS_derivation_def derivation_append_def)
  apply(case_tac "xa \<le> x")
   apply(rename_tac G1 d2 x e1 c1' e c xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e c xa)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def der2_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_simulate21: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (epdaHS2epdaS_derivation d2) n \<longrightarrow> maximum_of_domain d2 n \<longrightarrow> (\<forall>e2 c2'. epdaHS_step_relation G1 (the (get_configuration (d2 n))) e2 c2' \<longrightarrow> (\<exists>c1'. epdaS_step_relation G1 (the (get_configuration (epdaHS2epdaS_derivation d2 n))) e2 c1' \<and> e2 \<in> epda_delta G1 \<and> (let d2' = derivation_append d2 (der2 (the (get_configuration (d2 n))) e2 c2') n in epdaHS.derivation_initial G1 d2' \<and> Ex (maximum_of_domain d2') \<and> epdaHS2epdaS_derivation d2' = derivation_append (epdaHS2epdaS_derivation d2) (der2 (the (get_configuration (epdaHS2epdaS_derivation d2 n))) e2 c1') n)))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x e2 c2')(*strict*)
  apply(subgoal_tac "n = x")
   apply(rename_tac G1 d2 n x e2 c2')(*strict*)
   prefer 2
   apply (metis epdaS_vs_epdaHS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x e2 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2')(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 x = Some (pair e c)")
   apply(rename_tac G1 d2 x e2 c2')(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x e2 c2')(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x e2 c2')(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e2 c2')(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e2 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule_tac
      x = "\<lparr>epdaS_conf_state = epdaHS_conf_state c2', epdaS_conf_scheduler = epdaHS_conf_scheduler c2', epdaS_conf_stack = epdaHS_conf_stack c2'\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: epdaS_step_relation_def epdaHS_step_relation_def get_configuration_def epdaHS2epdaS_derivation_def get_configuration_def)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: epdaS_step_relation_def epdaHS_step_relation_def get_configuration_def epdaHS2epdaS_derivation_def get_configuration_def)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(simp add: Let_def)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
    apply(rule epdaHS.derivation_append_preserves_derivation)
      apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
     apply (metis epdaHS.der2_is_derivation)
    apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def get_configuration_def)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(rule_tac
      x = "x+Suc 0"
      in exI)
   apply (metis Nat.add_0_right add_Suc_right concat_has_max_dom der2_maximum_of_domain)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule ext)
  apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
  apply(simp add: derivation_append_def epdaHS2epdaS_derivation_def derivation_append_def)
  apply(case_tac "xa \<le> x")
   apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def der2_def)
  done

lemma epdaS_vs_epdaHS_inst_hlp_bisimulation_compatible_with_crop: "
  valid_epda G1
  \<Longrightarrow> epdaHS.derivation_initial G1 dh
  \<Longrightarrow> maximum_of_domain dh x
  \<Longrightarrow> maximum_of_domain (epdaHS2epdaS_derivation dh) n
  \<Longrightarrow> derivation_append_fit (epdaHS2epdaS_derivation dh) dc n
  \<Longrightarrow> epdaHS.derivation_initial G1 dc'
  \<Longrightarrow> epdaHS2epdaS_derivation dc' = derivation_append (epdaHS2epdaS_derivation dh) dc n
  \<Longrightarrow> maximum_of_domain dc' xb
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> dh xa = dc' xa"
  apply(subgoal_tac "x = n")
   apply(subgoal_tac "x\<le>xb")
    apply(clarsimp)
    apply(induct xa)
     apply(clarsimp)
     apply(subgoal_tac "epdaHS2epdaS_derivation dc' 0 = derivation_append (epdaHS2epdaS_derivation dh) dc n 0")
      prefer 2
      apply(force)
     apply(thin_tac "epdaHS2epdaS_derivation dc' = derivation_append (epdaHS2epdaS_derivation dh) dc n")
     apply(simp add: epdaHS2epdaS_derivation_def derivation_append_def)
     apply(subgoal_tac "\<exists>c. dc' 0 = Some (pair None c)")
      apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
       apply(clarsimp)
       apply(rename_tac c ca)(*strict*)
       apply(simp add: epdaHS.derivation_initial_def epdaS.derivation_initial_def)
       apply(clarsimp)
       apply(simp add: epdaHS_initial_configurations_def)
      apply(clarsimp)
      apply(rename_tac c)(*strict*)
      apply(rule epdaHS.some_position_has_details_at_0)
      apply(simp add: epdaHS.derivation_initial_def)
      apply(force)
     apply(rule epdaHS.some_position_has_details_at_0)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "epdaHS2epdaS_derivation dc' xa = derivation_append (epdaHS2epdaS_derivation dh) dc n xa")
     apply(rename_tac xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(subgoal_tac "epdaHS2epdaS_derivation dc' (Suc xa) = derivation_append (epdaHS2epdaS_derivation dh) dc n (Suc xa)")
     apply(rename_tac xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(thin_tac "epdaHS2epdaS_derivation dc' = derivation_append (epdaHS2epdaS_derivation dh) dc n")
    apply(rename_tac xa)(*strict*)
    apply(subgoal_tac "\<exists>e c. dc' (Suc xa) = Some (pair e c)")
     apply(rename_tac xa)(*strict*)
     apply(subgoal_tac "\<exists>e c. dh (Suc xa) = Some (pair e c)")
      apply(rename_tac xa)(*strict*)
      apply(simp add: epdaHS2epdaS_derivation_def derivation_append_def)
      apply(clarsimp)
      apply(rename_tac xa ea c ca)(*strict*)
      apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh xa = Some (pair e1 c1) \<and> dh (Suc xa) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G1 c1 e2 c2")
       apply(rename_tac xa ea c ca)(*strict*)
       prefer 2
       apply(rule_tac
      m = "Suc xa"
      in epdaHS.step_detail_before_some_position)
         apply(rename_tac xa ea c ca)(*strict*)
         apply(simp add: epdaHS.derivation_initial_def)
        apply(rename_tac xa ea c ca)(*strict*)
        apply(force)
       apply(rename_tac xa ea c ca)(*strict*)
       apply(force)
      apply(rename_tac xa ea c ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac xa c ca e1 e2 c1)(*strict*)
      apply(subgoal_tac "\<exists>e1 e2 c1 c2. dc' xa = Some (pair e1 c1) \<and> dc' (Suc xa) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G1 c1 e2 c2")
       apply(rename_tac xa c ca e1 e2 c1)(*strict*)
       prefer 2
       apply(rule_tac
      m = "Suc xa"
      in epdaHS.step_detail_before_some_position)
         apply(rename_tac xa c ca e1 e2 c1)(*strict*)
         apply(simp add: epdaHS.derivation_initial_def)
        apply(rename_tac xa c ca e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac xa c ca e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac xa c ca e1 e2 c1)(*strict*)
      apply(clarsimp)
      apply(simp add: epdaHS_step_relation_def)
     apply(rename_tac xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa e c)(*strict*)
     apply(rule epdaHS.some_position_has_details_before_max_dom)
       apply(rename_tac xa e c)(*strict*)
       apply(simp add: epdaHS.derivation_initial_def)
       apply(force)
      apply(rename_tac xa e c)(*strict*)
      apply(force)
     apply(rename_tac xa e c)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(rule epdaHS.some_position_has_details_before_max_dom)
      apply(rename_tac xa)(*strict*)
      apply(simp add: epdaHS.derivation_initial_def)
      apply(force)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(rule_tac
      j = "n"
      in le_trans)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rule_tac
      ?d1.0 = "(epdaHS2epdaS_derivation dh)"
      and ?d2.0 = "dc"
      in epdaS.derivation_append_minimal_maximum_of_domain)
       apply(force)+
      prefer 4
      apply(force)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(rule_tac
      t = "derivation_append (epdaHS2epdaS_derivation dh) dc n"
      and s = "epdaHS2epdaS_derivation dc'"
      in ssubst)
      apply(force)
     apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
    apply(rule_tac
      t = "derivation_append (epdaHS2epdaS_derivation dh) dc n"
      and s = "epdaHS2epdaS_derivation dc'"
      in ssubst)
     apply(force)
    apply (metis epdaHS2epdaS_derivation_preserves_maximum_of_domain)
   apply(force)
  apply (metis epdaS_vs_epdaHS_inst_AX_equal_length)
  done

lemma epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_crop1: "
  (\<forall>G1. valid_epda G1 \<longrightarrow> (\<forall>dh. epdaHS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain (epdaHS2epdaS_derivation dh) n \<longrightarrow> (\<forall>dc. derivation_append_fit (epdaHS2epdaS_derivation dh) dc n \<longrightarrow> (\<forall>dc'. epdaHS.derivation_initial G1 dc' \<and> Ex (maximum_of_domain dc') \<and> epdaHS2epdaS_derivation dc' = derivation_append (epdaHS2epdaS_derivation dh) dc n \<longrightarrow> (\<forall>x\<le>n. dh x = dc' x))))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x dc dc' xa xb)(*strict*)
  apply(rule epdaS_vs_epdaHS_inst_hlp_bisimulation_compatible_with_crop)
          apply(rename_tac G1 dh n x dc dc' xa xb)(*strict*)
          apply(force)+
  done

lemma epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_crop2: "
  (\<forall>G1. valid_epda G1 \<longrightarrow> (\<forall>dh. epdaHS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain dh n \<longrightarrow> (\<forall>dc'. derivation_append_fit dh dc' n \<longrightarrow> epdaHS.derivation_initial G1 (derivation_append dh dc' n) \<and> Ex (maximum_of_domain (derivation_append dh dc' n)) \<longrightarrow> (\<forall>x\<le>n. epdaHS2epdaS_derivation dh x = epdaHS2epdaS_derivation (derivation_append dh dc' n) x)))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh n x dc' xa xb e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(subgoal_tac "x = n")
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh n dc' xa xb)(*strict*)
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh n dc' xa xb)(*strict*)
     apply(rule epdaHS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh n dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(rule epdaHS.maximum_of_domainUnique)
    apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
    apply(rule epdaHS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(force)
  done

lemma epdaS_vs_epdaHS_inst_AX_accept_id1: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> epdaS_marking_condition G1 (epdaHS2epdaS_derivation d2) \<longrightarrow> epdaHS_marking_condition G1 d2)"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x i e c)(*strict*)
   prefer 2
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(case_tac "d2 i")
    apply(rename_tac G1 d2 x i e c)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G1 d2 x i e c a option b)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(simp add: epdaHS_marking_condition_def)
  apply(rule_tac
      x = "i"
      in exI)
  apply(rule_tac
      x = "ea"
      in exI)
  apply(rule_tac
      x = "ca"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaHS_marking_configurations_def epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(force)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(rule epdaHS.belongs_configurations)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(rule epdaHS.derivation_initial_belongs)
    apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(force)
  done

lemma epdaS_vs_epdaHS_inst_AX_accept_id2: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> epdaHS_marking_condition G1 d2 \<longrightarrow> epdaS_marking_condition G1 (epdaHS2epdaS_derivation d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(simp add: epdaHS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(rule_tac
      x = "i"
      in exI)
  apply(subgoal_tac "\<exists>e c. epdaHS2epdaS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x i e c)(*strict*)
   prefer 2
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(simp add: epdaHS_marking_configurations_def epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(rule_tac
      d = "epdaHS2epdaS_derivation d2"
      in epdaS.belongs_configurations)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply(rule epdaS.derivation_initial_belongs)
    apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
   apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(force)
  done

lemma epdaHS2epdaS_derivation_reflects_string_state_delta: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> epdaS_string_state ci' = w @ epdaS_string_state cj'
  \<Longrightarrow> (epdaHS2epdaS_derivation d) i = Some (pair ei ci')
  \<Longrightarrow> (epdaHS2epdaS_derivation d) j = Some (pair ej cj')
  \<Longrightarrow> epdaHS_string_state ci = w @ epdaHS_string_state cj"
  apply(induct "j-i" arbitrary: j ej cj cj' w)
   apply(rename_tac j ej cj cj' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x j ej cj cj' w)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac x j ej cj cj' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x j ej cj cj' w nat)(*strict*)
  apply(erule_tac
      x = "nat"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2")
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac x ej cj cj' w nat)(*strict*)
     apply(rule epdaHS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x ej cj cj' w nat)(*strict*)
    apply(force)
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   apply(force)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(subgoal_tac "\<exists>e c. (epdaHS2epdaS_derivation d) nat = Some (pair e c)")
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(erule_tac
      x = "e"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x = "c1"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x = "c"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state c1 = w @ epdaHS_string_state cj")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     prefer 2
     apply(rule_tac
      j = "Suc 0"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(rule epdaHS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(rule epdaHS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state ci = w @ epdaHS_string_state c1")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     prefer 2
     apply(rule_tac
      j = "nat-i"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(rule epdaHS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(rule epdaHS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_string_state c = w @ epdaS_string_state cj'")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
     prefer 2
     apply(rule_tac
      d = "epdaHS2epdaS_derivation d"
      and j = "Suc 0"
      in epdaS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
        apply(rule epdaS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
        apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_string_state ci' = w @ epdaS_string_state c")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
     prefer 2
     apply(rule_tac
      d = "epdaHS2epdaS_derivation d"
      and j = "nat-i"
      in epdaS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
        apply(rule epdaS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
        apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
    apply(erule_tac
      x = "wd"
      in meta_allE)
    apply(clarsimp)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
     apply(simp add: epdaHS2epdaS_derivation_def)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. epdaHS2epdaS_derivation d nat = Some (pair e1 c1) \<and> epdaHS2epdaS_derivation d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
     prefer 2
     apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
       apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaS_string_state_def epdaHS_string_state_def epdaS_step_relation_def epdaHS_step_relation_def)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  done

lemma epdaHS2epdaS_derivation_preserves_string_state_delta: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> epdaHS_string_state ci = w @ epdaHS_string_state cj
  \<Longrightarrow> (epdaHS2epdaS_derivation d) i = Some (pair ei ci')
  \<Longrightarrow> (epdaHS2epdaS_derivation d) j = Some (pair ej cj')
  \<Longrightarrow> epdaS_string_state ci' = w @ epdaS_string_state cj'"
  apply(induct "j-i" arbitrary: j ej cj cj' w)
   apply(rename_tac j ej cj cj' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x j ej cj cj' w)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac x j ej cj cj' w)(*strict*)
   apply(force)
  apply(rename_tac x j ej cj cj' w nat)(*strict*)
  apply(erule_tac
      x = "nat"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaHS_step_relation G c1 e2 c2")
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaHS.step_detail_before_some_position)
     apply(rename_tac x ej cj cj' w nat)(*strict*)
     apply(rule epdaHS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x ej cj cj' w nat)(*strict*)
    apply(force)
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   apply(force)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(subgoal_tac "\<exists>e c. (epdaHS2epdaS_derivation d) nat = Some (pair e c)")
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(erule_tac
      x = "e"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x = "c1"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x = "c"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state c1 = w @ epdaHS_string_state cj")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     prefer 2
     apply(rule_tac
      j = "Suc 0"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(rule epdaHS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(rule epdaHS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaHS_string_state ci = w @ epdaHS_string_state c1")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     prefer 2
     apply(rule_tac
      j = "nat-i"
      in epdaHS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(rule epdaHS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(rule epdaHS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule_tac
      x = "wb"
      in meta_allE)
    apply(clarsimp)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(simp add: epdaHS2epdaS_derivation_def)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. epdaHS2epdaS_derivation d nat = Some (pair e1 c1) \<and> epdaHS2epdaS_derivation d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     prefer 2
     apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
       apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaS_string_state_def epdaHS_string_state_def epdaS_step_relation_def epdaHS_step_relation_def)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(rule_tac
      m = "Suc nat"
      in epdaHS.pre_some_position_is_some_position)
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(rule epdaHS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(force)
  done

lemma epdaHS_get_unfixed_scheduler_DB_with_derivation_take: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> epdaHS_get_unfixed_scheduler_DB G d n = epdaHS_get_unfixed_scheduler_DB G (derivation_take d n) n"
  apply(simp add: epdaHS_get_unfixed_scheduler_DB_def)
  apply(simp add: derivation_take_def)
  done

lemma derivation_take_distributes_over_epdaS2epdaHS_derivation: "
  derivation_take (epdaS2epdaHS_derivation G d) n = epdaS2epdaHS_derivation G (derivation_take d n)"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def epdaS2epdaHS_derivation_def derivation_take_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_unAX_marked_effect_id1: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o1. o1 \<in> epdaS_unmarked_effect G1 (epdaHS2epdaS_derivation d2) \<longrightarrow> o1 \<in> epdaHS_unmarked_effect G1 d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def epdaHS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x c c' i e)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 o1 x c c' i e)(*strict*)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 o1 x c c' i e)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 o1 x c c' i e ea ca cb)(*strict*)
    apply(rule_tac
      x = "cb"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 d2 o1 x c c' i e ea ca cb)(*strict*)
     apply(rule_tac
      x = "i"
      in exI)
     apply(rule_tac
      x = "ea"
      in exI)
     apply(clarsimp)
    apply(rename_tac G1 d2 o1 x c c' i e ea ca cb)(*strict*)
    apply(simp add: epdaHS2epdaS_derivation_def)
    apply(clarsimp)
   apply(rename_tac G1 d2 o1 x c c' i e)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 o1 x c i e ca)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac G1 d2 o1 x c i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 o1 x c i e ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 d2 o1 x c i e ca a option b)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 o1 x c c' i e)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(case_tac "d2 i")
   apply(rename_tac G1 d2 o1 x c c' i e)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 o1 x c c' i e a)(*strict*)
  apply(case_tac a)
  apply(rename_tac G1 d2 o1 x c c' i e a option b)(*strict*)
  apply(force)
  done

lemma epdaS_vs_epdaHS_inst_AX_unAX_marked_effect_id2: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o2. o2 \<in> epdaHS_unmarked_effect G1 d2 \<longrightarrow> o2 \<in> epdaS_unmarked_effect G1 (epdaHS2epdaS_derivation d2)))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def epdaHS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x c c' i e)(*strict*)
  apply(subgoal_tac "\<exists>e c. epdaHS2epdaS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 o2 x c c' i e)(*strict*)
   apply(subgoal_tac "\<exists>c. epdaHS2epdaS_derivation d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 o2 x c c' i e)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 o2 x c c' i e ea ca cb)(*strict*)
    apply(rule_tac
      x = "cb"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 d2 o2 x c c' i e ea ca cb)(*strict*)
     apply(rule_tac
      x = "i"
      in exI)
     apply(rule_tac
      x = "ea"
      in exI)
     apply(clarsimp)
    apply(rename_tac G1 d2 o2 x c c' i e ea ca cb)(*strict*)
    apply(simp add: epdaHS2epdaS_derivation_def)
    apply(clarsimp)
   apply(rename_tac G1 d2 o2 x c c' i e)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac G1 d2 o2 x c c' i e)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 o2 x c c' i e a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 d2 o2 x c c' i e a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 o2 x c c' i e ea ca)(*strict*)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 o2 x c c' i e ea ca)(*strict*)
    apply(simp add: epdaHS2epdaS_derivation_def)
   apply(rename_tac G1 d2 o2 x c c' i e ea ca)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac G1 d2 o2 x c c' i e ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 o2 x c c' i e ea ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 d2 o2 x c c' i e ea ca a option b)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 o2 x c c' i e)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_marked_effect_id1: "
  (\<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o1. o1 \<in> epdaS_marked_effect G1 (epdaHS2epdaS_derivation d2) \<longrightarrow> epdaS_marking_condition G1 (epdaHS2epdaS_derivation d2) \<longrightarrow> o1 \<in> epdaHS_marked_effect G1 d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x)(*strict*)
  apply(simp add: epdaS_marked_effect_def epdaHS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(case_tac "d2 i")
    apply(rename_tac G1 d2 x c i e ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 d2 x c i e ca a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_at_0)
   apply(rule epdaHS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(clarsimp)
  done

lemma epdaS_vs_epdaHS_inst_AX_marked_effect_id2: "
  \<forall>G1 d2. valid_epda G1 \<and> epdaHS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o2. o2 \<in> epdaHS_marked_effect G1 d2 \<longrightarrow> epdaHS_marking_condition G1 d2 \<longrightarrow> o2 \<in> epdaS_marked_effect G1 (epdaHS2epdaS_derivation d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x)(*strict*)
  apply(simp add: epdaS_marked_effect_def epdaHS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c)(*strict*)
  apply(simp add: epdaHS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. epdaHS2epdaS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_at_0)
   apply(rule epdaHS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. epdaHS2epdaS_derivation d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(clarsimp)
  done

lemma epdaS_vs_epdaHS_inst_AX_step_labels_unique1: "
  (\<forall>G1 G2 e1 e21 e22. valid_epda G1 \<and> G1 = G2 \<longrightarrow> e1 \<in> epda_step_labels G1 \<longrightarrow> e21 \<in> epda_step_labels G2 \<longrightarrow> e22 \<in> epda_step_labels G2 \<longrightarrow> e1 = e21 \<and> e1 \<in> epda_delta G1 \<longrightarrow> e1 = e22 \<and> e1 \<in> epda_delta G1 \<longrightarrow> e21 = e22)"
  apply(clarsimp)
  done

lemma epdaS_vs_epdaHS_inst_AX_step_labels_unique2: "
  (\<forall>G1 G2 e11 e12 e2. valid_epda G1 \<and> G1 = G2 \<longrightarrow> e11 \<in> epda_step_labels G1 \<longrightarrow> e12 \<in> epda_step_labels G1 \<longrightarrow> e2 \<in> epda_step_labels G2 \<longrightarrow> e11 = e2 \<and> e11 \<in> epda_delta G1 \<longrightarrow> e12 = e2 \<and> e12 \<in> epda_delta G1 \<longrightarrow> e11 = e12)"
  apply(clarsimp)
  done

lemma epdaS_vs_epdaHS_inst_AX_step_labels_exists1: "
  (\<forall>G1 G2 e1. valid_epda G1 \<and> G1 = G2 \<longrightarrow> e1 \<in> epda_step_labels G1 \<longrightarrow> (\<exists>e2\<in> epda_step_labels G2. e1 = e2 \<and> e1 \<in> epda_delta G1))"
  apply(clarsimp)
  apply(rename_tac G1 e1)(*strict*)
  apply(simp add: epda_step_labels_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_step_labels_exists2: "
  (\<forall>G1 G2 e2. valid_epda G1 \<and> G1 = G2 \<longrightarrow> e2 \<in> epda_step_labels G2 \<longrightarrow> (\<exists>e1\<in> epda_step_labels G1. e1 = e2 \<and> e1 \<in> epda_delta G1))"
  apply(clarsimp)
  apply(rename_tac G1 e2)(*strict*)
  apply(simp add: epda_step_labels_def)
  done

lemma drop_map_nat_seq: "
  drop i (map f (nat_seq x j)) = map f (nat_seq (x+i) j)"
  apply(case_tac "x\<le>j")
   apply(rule listEqI)
    apply(clarsimp)
    apply (metis diff_diff_left nat_seq_length_prime)
   apply(rename_tac ia)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq x j ! (i + ia)"
      and s = "x+(i+ia)"
      in ssubst)
    apply(rename_tac ia)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac ia)(*strict*)
     apply(force)
    apply(rename_tac ia)(*strict*)
    apply (metis Suc_eq_plus1 diff_diff_left le_diff_conv2 less_diff_conv nat_seq_length_prime add.assoc add.commute not_less_eq trivNat)
   apply(rename_tac ia)(*strict*)
   apply(rule_tac
      t = "map f (nat_seq (x + i) j) ! ia"
      and s = "f (nat_seq (x + i) j ! ia)"
      in ssubst)
    apply(rename_tac ia)(*strict*)
    apply (metis Suc_eq_plus1 diff_diff_left nat_seq_length_prime nth_map)
   apply(rename_tac ia)(*strict*)
   apply(rule_tac
      t = "nat_seq (x + i) j ! ia"
      and s = "(x+i)+ia"
      in ssubst)
    apply(rename_tac ia)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac ia)(*strict*)
     apply (metis Suc_eq_plus1 diff_diff_left diff_is_0_eq' less_eq_Suc_le less_zeroE nat_seq_length_prime trivNat)
    apply(rename_tac ia)(*strict*)
    apply (metis Suc_eq_plus1 add_leE diff_diff_left le_diff_conv2 less_diff_conv nat_seq_length_prime not_less_eq trivNat)
   apply(rename_tac ia)(*strict*)
   apply (metis add.commute add.left_commute)
  apply(rule_tac
      t = "nat_seq x j"
      and s = "[]"
      in ssubst)
   apply (metis nat_seqEmpty trivNat)
  apply(clarsimp)
  apply(metis nat_seqEmpty trans_less_add1 trivNat)
  done

lemma epdaHS_history_computation_by_folding_of_edges: "
  valid_epda G
  \<Longrightarrow> epdaHS.derivation G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d j = Some (pair e' c')
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> epdaHS_conf_history c' = epdaHS_conf_history c @ (foldl append [] (map (\<lambda>e. option_to_list(edge_event(the e))) (drop i (get_labels d j))))"
  apply(induct "j-i" arbitrary: i e c)
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "drop j (get_labels d j)"
      and s = "[]"
      in ssubst)
    apply(clarsimp)
    apply (metis get_labels_length eq_imp_le)
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
     apply(simp add: epdaHS.derivation_initial_def)
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
  apply(simp add: get_labels_def)
  apply(rule_tac
      t = "drop i (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) j))"
      and s = "map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0 + i) j)"
      in ssubst)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(rule drop_map_nat_seq)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "drop (Suc i) (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) j)) = map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0 + Suc i) j)")
   apply(rename_tac x i e c e2 c2)(*strict*)
   prefer 2
   apply(rule drop_map_nat_seq)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop (Suc i) (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) j)) = map (\<lambda>i. get_label (d i)) (nat_seq (Suc (Suc i)) j)")
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(thin_tac "epdaHS_conf_history c' = epdaHS_conf_history c2 @ foldl (@) [] (map ((\<lambda>e. option_to_list (edge_event (the e))) \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc i)) j))")
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(rule_tac
      t = "nat_seq (Suc i) j"
      and s = "[Suc i]@nat_seq (Suc (Suc i)) j"
      in ssubst)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(rule_tac
      n = "x"
      in nat_seq_drop_first)
      apply(rename_tac x i e c e2 c2)(*strict*)
      apply(force)
     apply(rename_tac x i e c e2 c2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x i e c e2 c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(rule_tac
      t = "foldl (@) [] (map ((\<lambda>e. option_to_list (edge_event (the e))) \<circ> (\<lambda>i. get_label (d i))) ([Suc i] @ nat_seq (Suc (Suc i)) j))"
      and s = "((\<lambda>e. option_to_list (edge_event (the e))) \<circ> (\<lambda>i. get_label (d i))) (Suc i) @ foldl (@) [] (map ((\<lambda>e. option_to_list (edge_event (the e))) \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc i)) j))"
      in ssubst)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply (metis ConsApp concat_conv_foldl maps_def maps_simps(1))
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(rule_tac
      t = "epdaHS_conf_history c2"
      and s = "epdaHS_conf_history c @ ((\<lambda>e. option_to_list (edge_event (the e))) \<circ> (\<lambda>i. get_label (d i))) (Suc i)"
      in ssubst)
   apply(rename_tac x i e c e2 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(simp add: epdaHS_step_relation_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_replace_and_schedF1: "
  (\<forall>G1. valid_epda G1 \<longrightarrow> (\<forall>dh. epdaHS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain (epdaHS2epdaS_derivation dh) n \<longrightarrow> (\<forall>sUF. sUF \<in> epda_effects G1 \<longrightarrow> (\<forall>dc dc'. epdaHS.derivation_initial G1 dc' \<and> Ex (maximum_of_domain dc') \<and> epdaHS2epdaS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF n) dc n \<longrightarrow> (\<forall>x\<le>n. epdaHS_get_fixed_scheduler_DB G1 dh x = epdaHS_get_fixed_scheduler_DB G1 dc' x \<and> ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB G1 dh (epdaHS_get_unfixed_scheduler_DB G1 dc' n) n x = dc' x))))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
  apply(simp add: epdaHS_get_fixed_scheduler_DB_def)
  apply(simp add: epdaHS.replace_unfixed_scheduler_DB_def epdaHS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "n = x")
   apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply (metis epdaS_vs_epdaHS_inst_AX_equal_length)
  apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh x = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(subgoal_tac "x\<le>xb")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca)(*strict*)
   apply(case_tac "xb<x")
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(\<exists>y. epdaHS2epdaS_derivation dh x = Some y) \<and>       epdaHS2epdaS_derivation dh (Suc x) = None")
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca)(*strict*)
    prefer 2
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca y)(*strict*)
   apply(subgoal_tac "epdaHS2epdaS_derivation dc' (Suc xb) = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x (Suc xb)")
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca y)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca y)(*strict*)
   apply(thin_tac "epdaHS2epdaS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea c ca y)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(simp add: derivation_append_def)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca y)(*strict*)
   apply(simp add: epdaS_set_unfixed_scheduler_DB_def epdaHS2epdaS_derivation_def epdaS.replace_unfixed_scheduler_DB_def epdaS.map_unfixed_scheduler_DB_def get_configuration_def epdaS_get_unfixed_scheduler_DB_def epdaS_get_scheduler_def)
   apply(case_tac "dh (Suc xb)")
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca y)(*strict*)
    prefer 2
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca y a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca a)(*strict*)
    apply(case_tac a)
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca a option conf)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca option conf)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca y)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
   apply(case_tac "Suc xb = x")
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
   apply(rule_tac
      M = "G1"
      and d = "dh"
      and n = "x"
      and i = "Suc xb"
      in epdaHS.derivationNoFromNone2)
      apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
      apply(rule epdaHS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea c ca)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' xb = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' x = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' xa = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   prefer 2
   apply(subgoal_tac "epdaHS2epdaS_derivation dc' xa = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x xa")
    apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   apply(thin_tac "epdaHS2epdaS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x")
   apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
   apply(simp add: epdaHS2epdaS_derivation_def)
   apply(clarsimp)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec c ca cb cc)(*strict*)
   apply(case_tac "dc' xa")
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec c ca cb cc)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
    apply(rename_tac G1 dh x sUF dc' xa xb e ea eb ec c ca cb cc)(*strict*)
    apply(simp add: epdaS_set_unfixed_scheduler_DB_def epdaHS2epdaS_derivation_def epdaS.replace_unfixed_scheduler_DB_def epdaS.map_unfixed_scheduler_DB_def get_configuration_def epdaS_get_unfixed_scheduler_DB_def epdaS_get_scheduler_def)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec c ca cb cc a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec c ca cb cc a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 dh x sUF dc dc' xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd")(*strict*)
  apply(subgoal_tac "\<exists>c. dc' 0 = Some (pair None c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd")(*strict*)
   prefer 2
   apply (metis epdaHS.derivation_initial_is_derivation epdaHS.some_position_has_details_at_0)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd")(*strict*)
  apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd")(*strict*)
   prefer 2
   apply (metis epdaHS.derivation_initial_is_derivation epdaHS.some_position_has_details_at_0)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(subgoal_tac "epdaHS_conf_history c = epdaHS_conf_history cd")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(subgoal_tac "epdaHS2epdaS_derivation dc' xa = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x xa")
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(subgoal_tac "epdaHS2epdaS_derivation dc' x = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x x")
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(thin_tac "epdaHS2epdaS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(simp add: derivation_append_def)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(simp add: epdaS_set_unfixed_scheduler_DB_def epdaHS2epdaS_derivation_def epdaS.replace_unfixed_scheduler_DB_def epdaS.map_unfixed_scheduler_DB_def get_configuration_def epdaS_get_unfixed_scheduler_DB_def epdaS_get_scheduler_def)
   apply(subgoal_tac "right_quotient_word (epdaHS_conf_scheduler ca) (epdaHS_conf_scheduler ca) = Some []")
    apply(rename_tac G1 dh x sUF dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
    prefer 2
    apply(rule right_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G1 dh x sUF dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(simp add: epdaHS_get_scheduler_def epdaHS_set_unfixed_scheduler_DB_def epdaHS_get_unfixed_scheduler_DB_def get_configuration_def)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(rule_tac
      t = "epdaHS_conf_history c"
      and s = "epdaHS_conf_history cf @ (foldl append [] (map (\<lambda>e. option_to_list(edge_event(the e))) (drop 0 (get_labels dh xa))))"
      in ssubst)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(rule epdaHS_history_computation_by_folding_of_edges)
       apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
       apply(force)
      apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
      apply(rule epdaHS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(rule_tac
      t = "epdaHS_conf_history cd"
      and s = "epdaHS_conf_history ce @ (foldl append [] (map (\<lambda>e. option_to_list(edge_event(the e))) (drop 0 (get_labels dc' xa))))"
      in ssubst)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(rule epdaHS_history_computation_by_folding_of_edges)
       apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
       apply(force)
      apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
      apply(rule epdaHS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(rule_tac
      t = "epdaHS_conf_history cf"
      and s = "[]"
      in ssubst)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(rule_tac
      t = "epdaHS_conf_history ce"
      and s = "[]"
      in ssubst)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   apply(simp add: epdaHS.derivation_initial_def epdaHS_initial_configurations_def)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "get_labels dc' xa"
      and s = "get_labels dh xa"
      in ssubst)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf)(*strict*)
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
  apply(subgoal_tac "Suc 0\<le>xc \<and> xc\<le>xa")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
   prefer 2
   apply (metis nat_seq_in_interval)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "\<exists>e c. dc' xc = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh xc = Some (pair e c)")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc ee ef cg ch)(*strict*)
  apply(subgoal_tac "epdaHS2epdaS_derivation dc' xc = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x xc")
   apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc ee ef cg ch)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc ee ef cg ch)(*strict*)
  apply(thin_tac "epdaHS2epdaS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1 (epdaHS2epdaS_derivation dh) sUF x) dc x")
  apply(rename_tac G1 dh x sUF dc dc' xa xb e ea eb ec ed c ca cb cc "cd" ce cf xc ee ef cg ch)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(simp add: derivation_append_def epdaS.replace_unfixed_scheduler_DB_def epdaS.map_unfixed_scheduler_DB_def)
  done

lemma epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_replace_and_schedF2: "
   \<forall>G1. valid_epda G1 \<longrightarrow>
         (\<forall>dh. ATS.derivation_initial epdaHS_initial_configurations
                epdaHS_step_relation G1 dh \<and>
               Ex (maximum_of_domain dh) \<longrightarrow>
               (\<forall>n. maximum_of_domain dh n \<longrightarrow>
                    (\<forall>sUF'.
                        sUF' \<in> epda_effects G1 \<longrightarrow>
                        (\<forall>dc. (\<exists>dc'. ATS.derivation_initial
                                      epdaHS_initial_configurations
                                      epdaHS_step_relation G1
                                      (derivation_append
 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
   epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB G1 dh sUF'
   n)
 dc' n) \<and>
                                     Ex (maximum_of_domain
   (derivation_append
     (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
       epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB G1 dh
       sUF' n)
     dc' n)) \<and>
                                     epdaHS2epdaS_derivation
                                      (derivation_append
 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
   epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB G1 dh sUF'
   n)
 dc' n) =
                                     dc) \<longrightarrow>
                              (\<forall>x\<le>n. epdaS_get_fixed_scheduler_DB G1
(epdaHS2epdaS_derivation dh) x =
                                      epdaS_get_fixed_scheduler_DB G1 dc x \<and>
                                      ATS_SchedUF_DB.replace_unfixed_scheduler_DB
right_quotient_word (@) epdaS_set_unfixed_scheduler_DB epdaS_get_unfixed_scheduler_DB G1
(epdaHS2epdaS_derivation dh) (epdaS_get_unfixed_scheduler_DB G1 dc n) n x =
                                      dc x)))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply(simp add: epdaS_get_fixed_scheduler_DB_def)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply(subgoal_tac "n = x")
    apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply (metis epdaHS.derivation_initial_is_derivation epdaHS.maximum_of_domainUnique)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule epdaHS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
     apply(simp add: epdaHS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply(subgoal_tac "n = x")
    apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply (metis epdaHS.derivation_initial_is_derivation epdaHS.maximum_of_domainUnique)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF' dc' xa xb e ea c ca)(*strict*)
  apply(simp add: epdaS.replace_unfixed_scheduler_DB_def)
  apply(simp add: epdaS.map_unfixed_scheduler_DB_def)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(simp add: epdaS_get_scheduler_def epdaS_get_unfixed_scheduler_DB_def epdaS_set_unfixed_scheduler_DB_def get_configuration_def derivation_append_def)
  apply(simp add: epdaHS.replace_unfixed_scheduler_DB_def)
  apply(simp add: epdaHS.map_unfixed_scheduler_DB_def epdaHS_set_unfixed_scheduler_DB_def get_configuration_def epdaHS_get_unfixed_scheduler_DB_def epdaHS_get_scheduler_def)
  apply (metis right_quotient_word_full option.sel)
  done

lemma epdaS_vs_epdaHS_inst_ATS_Bisimulation_Derivation_Strong2_axioms: "
  ATS_Bisimulation_Derivation_Strong2_axioms valid_epda epdaS_initial_configurations
     epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_marked_effect
     epdaS_unmarked_effect epda_effects right_quotient_word (@)
     epda_unfixed_scheduler_extendable epdaS_set_unfixed_scheduler_DB
     epdaS_get_unfixed_scheduler_DB epdaS_get_fixed_scheduler_DB valid_epda
     epdaHS_initial_configurations epda_step_labels epdaHS_step_relation
     epdaHS_marking_condition epdaHS_marked_effect epdaHS_unmarked_effect epda_effects
     right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaHS_set_unfixed_scheduler_DB epdaHS_get_unfixed_scheduler_DB
     epdaHS_get_fixed_scheduler_DB epdaS_vs_epdaHS_TSstructure_rel epdaS_vs_epdaHS_effect_rel
     epdaS_vs_epdaHS_label_relation epdaS_vs_epdaHS_derivation_bisimulation "
  apply(unfold ATS_Bisimulation_Derivation_Strong2_def ATS_Bisimulation_Derivation_Strong1_axioms_def ATS_Bisimulation_Derivation_Strong2_axioms_def )
  apply(simp add: epdaS_vs_epdaHS_inst_AX_AX_initial_contained1 epdaS_vs_epdaHS_inst_AX_AX_initial_contained2 epdaS_vs_epdaHS_inst_AX_on_derivation_initial1 epdaS_vs_epdaHS_inst_AX_on_finite1 epdaS_vs_epdaHS_inst_AX_equal_length epdaS_vs_epdaHS_inst_AX_simulate12 epdaS_vs_epdaHS_inst_AX_simulate21 )
  apply(simp add: epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_crop1 epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_crop2 )
  apply(simp add: epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_replace_and_schedF1 epdaS_vs_epdaHS_inst_AX_bisimulation_compatible_with_replace_and_schedF2 )
  apply(simp add: epdaS_vs_epdaHS_inst_AX_accept_id1 epdaS_vs_epdaHS_inst_AX_accept_id2 epdaS_vs_epdaHS_inst_AX_unAX_marked_effect_id1 epdaS_vs_epdaHS_inst_AX_unAX_marked_effect_id2 epdaS_vs_epdaHS_inst_AX_marked_effect_id1 epdaS_vs_epdaHS_inst_AX_marked_effect_id2 )
  apply(simp add: epdaS_vs_epdaHS_inst_AX_step_labels_exists2 epda_step_labels_def )
  done

interpretation "epdaS_vs_epdaHS" : ATS_Bisimulation_Derivation_Strong2
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
  (* fixed_schedulers1 *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler1 *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable1 *)
  epda_fixed_scheduler_extendable
  (* scheduler_fragments1 *)
  "epda_effects"
  (* empty_scheduler_fragment1 *)
  epda_empty_scheduler_fragment
  (* join_scheduler_fragments1 *)
  "append"
  (* unfixed_schedulers1 *)
  "epda_effects"
  (* empty_unfixed_scheduler1 *)
  epda_empty_unfixed_scheduler
  (* unfixed_scheduler_right_quotient1 *)
  "right_quotient_word"
  (* extend_unfixed_scheduler1 *)
  "append"
  (* unfixed_scheduler_extendable1 *)
  epda_unfixed_scheduler_extendable
  (* schedulers1 *)
  "epda_effects"
  (* initial_schedulers1 *)
  "epda_effects"
  (* empty_scheduler1 *)
  epda_empty_scheduler
  (* get_scheduler1 *)
  "epdaS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler1 *)
  "append"
  (* join_scheduler_fragments1_sched *)
  "append"
  (* set_unfixed_scheduler_DB1 *)
  "epdaS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB1 *)
  "epdaS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB1 *)
  "epdaS_get_fixed_scheduler_DB"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaHS_configurations"
  (* initial_configurations2 *)
  "epdaHS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaHS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaHS_marking_condition"
  (* marked_effect2 *)
  "epdaHS_marked_effect"
  (* unmarked_effect2 *)
  "epdaHS_unmarked_effect"
  (* fixed_schedulers2 *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler2 *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable2 *)
  epda_fixed_scheduler_extendable
  (* scheduler_fragments2 *)
  "epda_effects"
  (* empty_scheduler_fragment2 *)
  epda_empty_scheduler_fragment
  (* join_scheduler_fragments2 *)
  "append"
  (* unfixed_schedulers2 *)
  "epda_effects"
  (* empty_unfixed_scheduler2 *)
  epda_empty_unfixed_scheduler
  (* unfixed_scheduler_right_quotient2 *)
  "right_quotient_word"
  (* extend_unfixed_scheduler2 *)
  "append"
  (* unfixed_scheduler_extendable2 *)
  epda_unfixed_scheduler_extendable
  (* schedulers2 *)
  "epda_effects"
  (* initial_schedulers2 *)
  "epda_effects"
  (* empty_scheduler2 *)
  epda_empty_scheduler
  (* get_scheduler2 *)
  "epdaHS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler2 *)
  "append"
  (* extend_scheduler2 *)
  "append"
  (* set_unfixed_scheduler_DB2 *)
  "epdaHS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB2 *)
  "epdaHS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB2 *)
  "epdaHS_get_fixed_scheduler_DB"
  (* TSstructure_rel *)
  epdaS_vs_epdaHS_TSstructure_rel
  (* effect_rel *)
  epdaS_vs_epdaHS_effect_rel
  (* label_relation *)
  epdaS_vs_epdaHS_label_relation
  (* derivation_bisimulation *)
  epdaS_vs_epdaHS_derivation_bisimulation
  apply(simp add: LOCALE_DEFS epdaS_interpretations epdaHS_interpretations0 LOCALE_DEFS)
  apply(simp add: epdaS_vs_epdaHS_inst_ATS_Bisimulation_Derivation_Strong2_axioms)
  done

theorem epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer: "
  valid_epda G
  \<Longrightarrow> (epdaHS.Nonblockingness_linear_DB G \<longleftrightarrow> epdaS.Nonblockingness_linear_DB G)
  \<and> epdaHS.unmarked_language G = epdaS.unmarked_language G
  \<and> epdaHS.marked_language G = epdaS.marked_language G"
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
    apply(rule epdaS_vs_epdaHS.Nonblockingness_translation2)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule epdaS_vs_epdaHS.Nonblockingness_translation1)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule order_antisym)
    apply(rule_tac
      t = "epdaHS.unmarked_language G"
      and s = "epdaHS.finite_unmarked_language G"
      in ssubst)
     apply (metis epdaHS.AX_unmarked_language_finite)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rule_tac
      t = "epdaS.unmarked_language G"
      and s = "epdaS.finite_unmarked_language G"
      in ssubst)
    apply (metis epdaS.AX_unmarked_language_finite)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rule order_antisym)
   apply(rule_tac
      t = "epdaHS.marked_language G"
      and s = "epdaHS.finite_marked_language G"
      in ssubst)
    apply (metis epdaHS.AX_marked_language_finite)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation2)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS.AX_marked_language_finite)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation1)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

theorem epdaS_vs_epdaHS_is_forward_deterministic_accessible_preserved: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_deterministic_accessible G
  \<Longrightarrow> epdaHS.is_forward_deterministic_accessible G"
  apply(simp add: epdaS.is_forward_deterministic_accessible_def epdaHS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rule epdaHS_is_forward_target_deterministic_accessible)
   apply(force)
  apply(clarsimp)
  apply(rule epdaS_vs_epdaHS.preserve_FEdetermR1)
   apply(force)
  apply(force)
  done

end
