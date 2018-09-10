section {*I\_epda\_lemmas*}
theory
  I_epda_lemmas

imports
  I_epda_main

begin

lemma epda_read_in_epda_events: "
  valid_epda M
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> Some a = edge_event e
  \<Longrightarrow> a \<in> epda_events M"
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(auto)
  apply(simp add: valid_epda_step_label_def)
  apply(erule conjE)+
  apply(simp add: option_to_set_def)
  apply(force)
  done

lemma valid_epda_initial_in_states: "
  valid_epda M
  \<Longrightarrow> epda_initial M \<in> epda_states M"
  apply(simp add: valid_epda_def)
  done

lemma valid_epda_box_in_gamma: "
  valid_epda G
  \<Longrightarrow> epda_box G \<in> epda_gamma G"
  apply(simp add: valid_epda_def)
  done

definition valid_pda :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "valid_pda G \<equiv>
  valid_epda G
  \<and> (\<forall>e \<in> epda_delta G. length (edge_pop e) = 1)"

definition valid_dpda :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "valid_dpda G \<equiv>
  valid_pda G
  \<and> epdaS.is_forward_edge_deterministic_accessible G"

definition empty_push_edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "empty_push_edge e \<equiv>
  edge_push e = []"

definition strict_empty_push_edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "strict_empty_push_edge e \<equiv>
  edge_push e = []
  \<and> edge_event e = None"

definition multiple_push_edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "multiple_push_edge e \<equiv>
  length (edge_push e) > Suc 0"

definition strict_multiple_push_edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "strict_multiple_push_edge e \<equiv>
  suffix (edge_push e) (edge_pop e)
  \<and> edge_event e = None"

definition pop_edges_seperated :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "pop_edges_seperated G \<equiv>
  \<forall>e \<in> epda_delta G.
  empty_push_edge e
  \<longrightarrow> strict_empty_push_edge e"

definition pop_edges_seperated_ALT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "pop_edges_seperated_ALT G \<equiv>
  \<forall>e \<in> epda_delta G.
    edge_push e = [] \<longrightarrow> edge_event e = None"

lemma pop_edges_seperated_ALT_vs_pop_edges_seperated: "
  pop_edges_seperated_ALT G = pop_edges_seperated G"
  apply(simp add: pop_edges_seperated_ALT_def pop_edges_seperated_def empty_push_edge_def strict_empty_push_edge_def)
  done

definition push_edges_seperated :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "push_edges_seperated G \<equiv>
  \<forall>e \<in> epda_delta G.
  multiple_push_edge e
  \<longrightarrow> strict_multiple_push_edge e"

definition push_edges_seperated_ALT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "push_edges_seperated_ALT G \<equiv>
  \<forall>e \<in> epda_delta G.
  length (edge_push e) > Suc 0
  \<longrightarrow> (suffix (edge_push e) (edge_pop e) \<and> edge_event e = None)"

lemma push_edges_seperated_ALT_vs_push_edges_seperated: "
  push_edges_seperated_ALT G = push_edges_seperated G"
  apply(simp add: multiple_push_edge_def strict_multiple_push_edge_def push_edges_seperated_ALT_def push_edges_seperated_def)
  done

definition valid_simple_dpda :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "valid_simple_dpda G \<equiv>
  valid_dpda G
  \<and> (\<forall>e \<in> epda_delta G.
      case edge_event e of
      Some a \<Rightarrow>
          edge_pop e = edge_push e
      | None \<Rightarrow>
          edge_push e = []
          \<or> (\<exists>w. edge_push e = w # edge_pop e))"

definition valid_dfa :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "valid_dfa G \<equiv>
  valid_dpda G
  \<and> (\<forall>e \<in> epda_delta G.
      edge_event e \<noteq> None
      \<and> edge_pop e = [epda_box G]
      \<and> edge_push e = [epda_box G])"

(*prevention can occur due to stacks; designed for DFA only*)
definition some_step_from_every_configuration :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "some_step_from_every_configuration G \<equiv>
  \<forall>q \<in> epda_states G.
  \<forall>A \<in> epda_events G.
  \<exists>e \<in> epda_delta G.
    edge_src e = q
    \<and> edge_event e = Some A"

definition epdaS_accessible_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set"
  where
    "epdaS_accessible_states G \<equiv>
  {q \<in> epda_states G.
    \<exists>d n.
    epdaS.derivation G d
    \<and> (case get_configuration (d n) of
        None \<Rightarrow> False
        | Some c \<Rightarrow> epdaS_conf_state c = q)
    \<and> (case get_configuration (d 0) of
        None \<Rightarrow> False
        | Some c \<Rightarrow> c \<in> epdaS_initial_configurations G)}"

definition n_step_epdaS_accessible_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> 'state set"
  where
    "n_step_epdaS_accessible_states G n \<equiv>
  {q. \<exists>d c.
      epdaS.derivation_initial G d
      \<and> get_configuration (d n) = Some c
      \<and> epdaS_conf_state c = q}"

definition at_most_n_epdaS_accessible_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> 'state set"
  where
    "at_most_n_epdaS_accessible_states G n \<equiv>
  {q. \<exists>d c k.
      k \<le> n
      \<and> epdaS.derivation_initial G d
      \<and> get_configuration (d k) = Some c
      \<and> epdaS_conf_state c = q}"

definition all_states_accessible :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "all_states_accessible G \<equiv>
  epda_states G \<subseteq> epdaS_accessible_states G"

definition epdaS_accessible_edges :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "epdaS_accessible_edges G \<equiv>
  {e \<in> epda_delta G.
  \<exists>d n c.
  epdaS.derivation_initial G d
  \<and> d n = Some (pair (Some e) c)}"

definition all_edges_accessible :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "all_edges_accessible G \<equiv>
  epda_delta G \<subseteq> epdaS_accessible_edges G"

definition accessible :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "accessible G \<equiv>
  all_states_accessible G
  \<and> all_edges_accessible G"

lemma valid_epda_accessible_implies_accessible: "
  valid_epda G
  \<Longrightarrow> accessible G
  \<Longrightarrow> epdaS.accessible G"
  apply(simp add: epdaS.accessible_def accessible_def all_states_accessible_def all_edges_accessible_def epda_destinations_def epdaS.get_accessible_destinations_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(thin_tac "epda_delta G \<subseteq> epdaS_accessible_edges G")
   apply(subgoal_tac "xa \<in> epdaS_accessible_states G")
    apply(rename_tac xa)(*strict*)
    apply(thin_tac "epda_states G \<subseteq> epdaS_accessible_states G")
    apply(simp add: epdaS_accessible_states_def)
    apply(clarsimp)
    apply(rename_tac xa d n)(*strict*)
    apply(rule_tac
      x = "d"
      in exI)
    apply(simp add: get_configuration_def)
    apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
     apply(rename_tac xa d n)(*strict*)
     apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
      apply(rename_tac xa d n)(*strict*)
      apply(clarsimp)
      apply(rename_tac d n c e ca)(*strict*)
      apply(rule conjI)
       apply(rename_tac d n c e ca)(*strict*)
       apply(simp add: epdaS.derivation_initial_def)
      apply(rename_tac d n c e ca)(*strict*)
      apply(rule_tac
      x = "n"
      in exI)
      apply(rule_tac
      x = "e"
      in exI)
      apply(rule_tac
      x = "ca"
      in exI)
      apply(clarsimp)
      apply(simp add: epdaS_get_destinations_def)
     apply(rename_tac xa d n)(*strict*)
     apply(case_tac "d n")
      apply(rename_tac xa d n)(*strict*)
      apply(force)
     apply(rename_tac xa d n a)(*strict*)
     apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
      apply(rename_tac xa d n a)(*strict*)
      prefer 2
      apply(rule_tac
      m = "n"
      in epdaS.pre_some_position_is_some_position)
        apply(rename_tac xa d n a)(*strict*)
        apply(force)
       apply(rename_tac xa d n a)(*strict*)
       apply(force)
      apply(rename_tac xa d n a)(*strict*)
      apply(force)
     apply(rename_tac xa d n a)(*strict*)
     apply(force)
    apply(rename_tac xa d n)(*strict*)
    apply (metis epdaS.some_position_has_details_at_0)
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "epda_states G \<subseteq> epdaS_accessible_states G")
  apply(subgoal_tac "xa \<in> epdaS_accessible_edges G")
   apply(rename_tac xa)(*strict*)
   apply(thin_tac "epda_delta G \<subseteq> epdaS_accessible_edges G")
   apply(simp add: epdaS_accessible_edges_def)
   apply(clarsimp)
   apply(rename_tac xa d n c)(*strict*)
   apply(rule_tac
      x = "d"
      in exI)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x = "n"
      in exI)
   apply(rule_tac
      x = "Some xa"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaS_get_destinations_def)
  apply(rename_tac xa)(*strict*)
  apply(force)
  done

lemma at_most_n_epdaS_accessible_states_by_n_step_epdaS_accessible_states: "
  at_most_n_epdaS_accessible_states G n = \<Union>{n_step_epdaS_accessible_states G k | k. k\<le>n}"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: at_most_n_epdaS_accessible_states_def)
   apply(clarsimp)
   apply(rename_tac d c k)(*strict*)
   apply(rule_tac
      x = "n_step_epdaS_accessible_states G k"
      in exI)
   apply(rule conjI)
    apply(rename_tac d c k)(*strict*)
    apply(rule_tac
      x = "k"
      in exI)
    apply(clarsimp)
   apply(rename_tac d c k)(*strict*)
   apply(simp add: n_step_epdaS_accessible_states_def)
   apply(rule_tac
      x = "d"
      in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x k)(*strict*)
  apply(simp add: n_step_epdaS_accessible_states_def at_most_n_epdaS_accessible_states_def)
  apply(clarsimp)
  apply(rename_tac k d c)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x = "c"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x = "k"
      in exI)
  apply(clarsimp)
  done

lemma epdaS_accessible_states_by_n_step_epdaS_accessible_states: "
  valid_epda G
  \<Longrightarrow> epdaS_accessible_states G = \<Union>{n_step_epdaS_accessible_states G k | k. True}"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: n_step_epdaS_accessible_states_def)
   apply(simp add: epdaS_accessible_states_def)
   apply(clarsimp)
   apply(rename_tac x d n)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac x d n)(*strict*)
    prefer 2
    apply (metis epdaS.some_position_has_details_at_0)
   apply(rename_tac x d n)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d n")
    apply(rename_tac x d n c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d n c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac x d n c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n c option b)(*strict*)
   apply(rule_tac
      x = "n_step_epdaS_accessible_states G n"
      in exI)
   apply(rule conjI)
    apply(rename_tac d n c option b)(*strict*)
    apply(rule_tac
      x = "n"
      in exI)
    apply(rule order_antisym)
     apply(rename_tac d n c option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n c option b x)(*strict*)
     apply(simp add: n_step_epdaS_accessible_states_def)
     apply(clarsimp)
     apply(rename_tac d n c option b da ca)(*strict*)
     apply(rule_tac
      x = "da"
      in exI)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d n c option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n c option b da ca)(*strict*)
    apply(simp add: n_step_epdaS_accessible_states_def)
    apply(rule_tac
      x = "da"
      in exI)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac d n c option b)(*strict*)
   apply(simp add: n_step_epdaS_accessible_states_def)
   apply(rule_tac
      x = "d"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: epdaS.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac x k)(*strict*)
  apply(simp add: n_step_epdaS_accessible_states_def epdaS_accessible_states_def)
  apply(clarsimp)
  apply(rename_tac k d c)(*strict*)
  apply(rule conjI)
   apply(rename_tac k d c)(*strict*)
   apply(subgoal_tac "c \<in> epdaS_configurations G")
    apply(rename_tac k d c)(*strict*)
    apply(simp add: epdaS_configurations_def)
    apply(clarsimp)
   apply(rename_tac k d c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d k")
    apply(rename_tac k d c)(*strict*)
    apply(force)
   apply(rename_tac k d c a)(*strict*)
   apply(clarsimp)
   apply(case_tac "a")
   apply(rename_tac k d c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac k d c option)(*strict*)
   apply(rule epdaS.belongs_configurations)
    apply(rename_tac k d c option)(*strict*)
    apply(rule epdaS.derivation_initial_belongs)
     apply(rename_tac k d c option)(*strict*)
     apply(force)
    apply(rename_tac k d c option)(*strict*)
    apply(force)
   apply(rename_tac k d c option)(*strict*)
   apply(force)
  apply(rename_tac k d c)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(simp add: get_configuration_def)
  apply(rule conjI)
   apply(rename_tac k d c)(*strict*)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac k d c)(*strict*)
  apply(rule conjI)
   apply(rename_tac k d c)(*strict*)
   apply(rule_tac
      x = "k"
      in exI)
   apply(clarsimp)
  apply(rename_tac k d c)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac k d c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac k d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac k d c ca)(*strict*)
  apply(simp add: epdaS.derivation_initial_def)
  done

lemma n_step_epdaS_accessible_states_are_states: "
  valid_epda G
  \<Longrightarrow> n_step_epdaS_accessible_states G n \<subseteq> epda_states G"
  apply(simp add: n_step_epdaS_accessible_states_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(subgoal_tac "c \<in> epdaS_configurations G")
   apply(rename_tac d c)(*strict*)
   apply(simp add: epdaS_configurations_def)
   apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac d c)(*strict*)
   apply(force)
  apply(rename_tac d c a)(*strict*)
  apply(clarsimp)
  apply(case_tac "a")
  apply(rename_tac d c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c option)(*strict*)
  apply(rule epdaS.belongs_configurations)
   apply(rename_tac d c option)(*strict*)
   apply(rule epdaS.derivation_initial_belongs)
    apply(rename_tac d c option)(*strict*)
    apply(force)
   apply(rename_tac d c option)(*strict*)
   apply(force)
  apply(rename_tac d c option)(*strict*)
  apply(force)
  done

lemma at_most_n_epdaS_accessible_states_are_states: "
  valid_epda G
  \<Longrightarrow> at_most_n_epdaS_accessible_states G n \<subseteq> epda_states G"
  apply(simp add: at_most_n_epdaS_accessible_states_def)
  apply(clarsimp)
  apply(rename_tac d c k)(*strict*)
  apply(subgoal_tac "c \<in> epdaS_configurations G")
   apply(rename_tac d c k)(*strict*)
   apply(simp add: epdaS_configurations_def)
   apply(clarsimp)
  apply(rename_tac d c k)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d k")
   apply(rename_tac d c k)(*strict*)
   apply(force)
  apply(rename_tac d c k a)(*strict*)
  apply(clarsimp)
  apply(case_tac "a")
  apply(rename_tac d c k a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c k option)(*strict*)
  apply(rule epdaS.belongs_configurations)
   apply(rename_tac d c k option)(*strict*)
   apply(rule epdaS.derivation_initial_belongs)
    apply(rename_tac d c k option)(*strict*)
    apply(force)
   apply(rename_tac d c k option)(*strict*)
   apply(force)
  apply(rename_tac d c k option)(*strict*)
  apply(force)
  done

lemma derivation_stays_in_states: "
  valid_epda M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> set s \<subseteq> epda_gamma M
  \<Longrightarrow> set h1 \<subseteq> epda_events M
  \<Longrightarrow> epdaS.derivation M d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = w, epdaS_conf_stack = s\<rparr>)
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> d i = Some (pair e1 \<lparr>epdaS_conf_state = qi, epdaS_conf_scheduler = wi, epdaS_conf_stack = si\<rparr>)
  \<Longrightarrow> qi\<in> epda_states M"
  apply(subgoal_tac "\<lparr>epdaS_conf_state = qi, epdaS_conf_scheduler = wi, epdaS_conf_stack = si\<rparr> \<in> epdaS_configurations M")
   prefer 2
   apply(rule epdaS.stays_in_configuration)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: epdaS_configurations_def)
    apply(force)
   apply(force)
  apply(simp add: epdaS_configurations_def)
  done

lemma epda_is_is_forward_target_deterministic_accessible: "
  valid_epda M
  \<Longrightarrow> epdaS.is_forward_target_deterministic_accessible M"
  apply(simp add: epdaS.is_forward_target_deterministic_accessible_def)
  apply(auto)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(auto)
  done

lemma epda_is_is_forward_target_deterministic: "
  valid_epda M
  \<Longrightarrow> epdaS.is_forward_target_deterministic M"
  apply(simp add: epdaS.is_forward_target_deterministic_def)
  apply(auto)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(auto)
  done

lemma epda_is_backward_target_deterministic: "
  valid_epda M
  \<Longrightarrow> epdaS.is_backward_target_deterministic M"
  apply(simp add: epdaS.is_backward_target_deterministic_def)
  apply(auto)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(unfold epdaS_step_relation_def)
  apply(force)
  done

lemma DFA_derivation_drops_stepwise: "
  valid_dfa M
  \<Longrightarrow> epdaS.derivation M d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d n = Some (pair e c2)
  \<Longrightarrow> (epdaS_conf_scheduler c2 = drop n (epdaS_conf_scheduler c1))
  \<and> (length (epdaS_conf_scheduler c1) = n + (length (epdaS_conf_scheduler c2)))"
  apply(subgoal_tac "\<forall>d c1 e c2 m. epdaS.derivation M d \<and> maximum_of_domain d m \<and> n\<le>m \<and> d 0 = Some (pair None c1) \<and> d n = Some (pair e c2) \<longrightarrow> ((epdaS_conf_scheduler c2 = drop n (epdaS_conf_scheduler c1)) \<and>(length (epdaS_conf_scheduler c1) = n + (length (epdaS_conf_scheduler c2))))")
   apply(force)
  apply(thin_tac "epdaS.derivation M d")
  apply(thin_tac "maximum_of_domain d m")
  apply(thin_tac "n\<le>m")
  apply(thin_tac "d 0 = Some (pair None c1)")
  apply(thin_tac "d n = Some (pair e c2)")
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d c1 e c2 m)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac n d c1 e c2 m)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac n d c1 e c2 m)(*strict*)
     apply(blast)
    apply(rename_tac n d c1 e c2 m)(*strict*)
    apply(blast)
   apply(rename_tac n d c1 e c2 m)(*strict*)
   apply(arith)
  apply(rename_tac n d c1 e c2 m)(*strict*)
  apply(erule exE)+
  apply(rename_tac n d c1 e c2 m ea c)(*strict*)
  apply(erule_tac
      x = "derivation_take d n"
      in allE)
  apply(erule_tac
      x = "c1"
      in allE)
  apply(erule_tac
      x = "ea"
      in allE)
  apply(erule_tac
      x = "c"
      in allE)
  apply(erule impE)
   apply(rename_tac n d c1 e c2 m ea c)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d c1 e c2 m ea c)(*strict*)
    apply(rule_tac epdaS.derivation_take_preserves_derivation)
    apply(blast)
   apply(rename_tac n d c1 e c2 m ea c)(*strict*)
   apply(rule_tac
      x = "n"
      in exI)
   apply(rule conjI)
    apply(rename_tac n d c1 e c2 m ea c)(*strict*)
    apply(rule_tac
      m = "m-n"
      in epdaS.derivation_take_preserves_generates_maximum_of_domain)
     apply(rename_tac n d c1 e c2 m ea c)(*strict*)
     apply(blast)
    apply(rename_tac n d c1 e c2 m ea c)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d c1 e c2 m ea c)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n d c1 e c2 m ea c)(*strict*)
  apply(erule conjE)+
  apply(rename_tac n d c1 e c2 m ea c)(*strict*)
  apply(subgoal_tac "\<exists>e'. e = Some e'")
   apply(rename_tac n d c1 e c2 m ea c)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
    apply(rename_tac n d c1 e c2 m ea c)(*strict*)
    prefer 2
    apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n d c1 e c2 m ea c)(*strict*)
      apply(blast)+
   apply(rename_tac n d c1 e c2 m ea c)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d c1 e c2 m ea c)(*strict*)
  apply(erule exE)+
  apply(rename_tac n d c1 e c2 m ea c e')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d c1 c2 m ea c e')(*strict*)
  apply(subgoal_tac "epdaS_step_relation M c e' c2")
   apply(rename_tac n d c1 c2 m ea c e')(*strict*)
   prefer 2
   apply(rule epdaS.position_change_due_to_step_relation)
     apply(rename_tac n d c1 c2 m ea c e')(*strict*)
     apply(blast)+
  apply(rename_tac n d c1 c2 m ea c e')(*strict*)
  apply(subgoal_tac "\<exists>a. edge_event e' = Some a")
   apply(rename_tac n d c1 c2 m ea c e')(*strict*)
   prefer 2
   apply(simp add: valid_dfa_def)
   apply(clarsimp)
   apply(erule_tac
      x = "e'"
      in ballE)
    apply(rename_tac n d c1 c2 m ea c e')(*strict*)
    apply(clarsimp)
   apply(rename_tac n d c1 c2 m ea c e')(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac n d c1 c2 m ea c e')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d c1 c2 m ea c e' a)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d c1 c2 m ea c e' a)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n d c1 c2 m ea c e' a w)(*strict*)
   apply(case_tac c2)
   apply(rename_tac n d c1 c2 m ea c e' a w epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d c1 m ea c e' a w epdaS_conf_schedulera)(*strict*)
   apply(case_tac c)
   apply(rename_tac n d c1 m ea c e' a w epdaS_conf_schedulera epdaS_conf_statea epdaS_conf_scheduleraa epdaS_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d c1 m ea e' a w epdaS_conf_schedulera)(*strict*)
   apply(case_tac e')
   apply(rename_tac n d c1 m ea e' a w epdaS_conf_schedulera edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d c1 m ea a w epdaS_conf_schedulera edge_src edge_pop edge_push edge_trg)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      t = "drop (Suc n) (epdaS_conf_scheduler c1)"
      and s = "drop (Suc 0) (drop n (epdaS_conf_scheduler c1))"
      in ssubst)
    apply(rename_tac n d c1 m ea a w epdaS_conf_schedulera edge_src edge_pop edge_push edge_trg)(*strict*)
    apply(rule sym)
    apply(rule_tac
      t = "Suc n"
      and s = "Suc 0+n"
      in ssubst)
     apply(rename_tac n d c1 m ea a w epdaS_conf_schedulera edge_src edge_pop edge_push edge_trg)(*strict*)
     apply(arith)
    apply(rename_tac n d c1 m ea a w epdaS_conf_schedulera edge_src edge_pop edge_push edge_trg)(*strict*)
    apply(rule drop_drop)
   apply(rename_tac n d c1 m ea a w epdaS_conf_schedulera edge_src edge_pop edge_push edge_trg)(*strict*)
   apply(force)
  apply(rename_tac n d c1 c2 m ea c e' a)(*strict*)
  apply(subgoal_tac "length (epdaS_conf_scheduler c) = Suc (length(epdaS_conf_scheduler c2))")
   apply(rename_tac n d c1 c2 m ea c e' a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d c1 c2 m ea c e' a)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n d c1 c2 m ea c e' a w)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemma InductOverReachables: "
  valid_epda M
  \<Longrightarrow> P (epda_initial M)
  \<Longrightarrow> (\<forall>p e q cp cq. cp \<in> epdaS_configurations M \<longrightarrow> cq \<in> epdaS_configurations M \<longrightarrow> p\<in> (epdaS_accessible_states M) \<longrightarrow> P p \<longrightarrow> epdaS_conf_state cp = p \<longrightarrow> epdaS_conf_state cq = q \<longrightarrow> epdaS_step_relation M cp e cq \<longrightarrow> e \<in> epda_step_labels M \<longrightarrow> P q)
  \<Longrightarrow> p \<in> (epdaS_accessible_states M)
  \<Longrightarrow> P p"
  apply(subgoal_tac "\<exists>n. p\<in> (epda_states M) \<and> (\<exists>d. epdaS.derivation M d \<and> (case get_configuration (d n) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = p)\<and> (case get_configuration (d 0) of None \<Rightarrow> False | Some c \<Rightarrow> c \<in> epdaS_initial_configurations M))")
   prefer 2
   apply(simp add: epdaS_accessible_states_def)
   apply(force)
  apply(erule exE)
  apply(rename_tac n)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n d)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      n = "n"
      and f = "\<lambda>n. {q\<in> (epda_states M). \<exists>d. epdaS.derivation M d \<and> (case get_configuration (d n) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = q)\<and> (case get_configuration (d 0) of None \<Rightarrow> False | Some c \<Rightarrow> c \<in> epdaS_initial_configurations M)}"
      in BEST_INDUCT2)
   apply(rename_tac n d)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(force)
  apply(rename_tac n d)(*strict*)
  apply(rule allI)
  apply(rename_tac n d k)(*strict*)
  apply(rule impI)+
  apply(rule allI)+
  apply(rename_tac n d k x l)(*strict*)
  apply(rule impI)+
  apply(clarsimp)
  apply(rename_tac n d k x l da)(*strict*)
  apply(case_tac "l<k")
   apply(rename_tac n d k x l da)(*strict*)
   apply(erule_tac
      x = "x"
      and P = "\<lambda>x. \<forall>l<k. x \<in> epda_states M \<and> (\<exists>d. epdaS.derivation M d \<and> (case get_configuration (d l) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = x) \<and> (case get_configuration (d 0) of None \<Rightarrow> False | Some c \<Rightarrow> c \<in> epdaS_initial_configurations M)) \<longrightarrow> P x"
      in allE)
   apply(rename_tac n d k x l da)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x = "l"
      and P = "\<lambda>l. l < k \<longrightarrow> (\<exists>d. epdaS.derivation M d \<and> (case get_configuration (d l) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = x) \<and> (case get_configuration (d 0) of None \<Rightarrow> False | Some c \<Rightarrow> c \<in> epdaS_initial_configurations M)) \<longrightarrow> P x"
      in allE)
   apply(rename_tac n d k x l da)(*strict*)
   apply(erule impE)
    apply(rename_tac n d k x l da)(*strict*)
    apply(arith)
   apply(rename_tac n d k x l da)(*strict*)
   apply(force)
  apply(rename_tac n d k x l da)(*strict*)
  apply(subgoal_tac "l = k")
   apply(rename_tac n d k x l da)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d k x l da)(*strict*)
  apply(thin_tac "\<not> l < k")
  apply(thin_tac "l \<le> k")
  apply(clarsimp)
  apply(rename_tac n d k x da)(*strict*)
  apply(case_tac k)
   apply(rename_tac n d k x da)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d x da)(*strict*)
   apply(subgoal_tac "x = epda_initial M")
    apply(rename_tac n d x da)(*strict*)
    apply(force)
   apply(rename_tac n d x da)(*strict*)
   apply(case_tac "get_configuration (da 0)")
    apply(rename_tac n d x da)(*strict*)
    apply(force)
   apply(rename_tac n d x da a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d da a)(*strict*)
   apply(simp add: epdaS_initial_configurations_def)
  apply(rename_tac n d k x da nat)(*strict*)
  apply(subgoal_tac "\<exists>ek ck. da k = Some (pair (Some ek) ck)")
   apply(rename_tac n d k x da nat)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
   apply(case_tac "da k")
    apply(rename_tac n d k x da nat)(*strict*)
    apply(force)
   apply(rename_tac n d k x da nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d x da nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac n d x da nat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d da nat option b)(*strict*)
   apply(case_tac option)
    apply(rename_tac n d da nat option b)(*strict*)
    apply(rule_tac
      d = "da"
      in epdaS.derivation_Always_PreEdge_prime)
     apply(rename_tac n d da nat option b)(*strict*)
     apply(force)
    apply(rename_tac n d da nat option b)(*strict*)
    apply(force)
   apply(rename_tac n d da nat option b a)(*strict*)
   apply(force)
  apply(rename_tac n d k x da nat)(*strict*)
  apply(subgoal_tac "\<exists>enat cnat. da nat = Some (pair enat cnat)")
   apply(rename_tac n d k x da nat)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac n d x da nat ek ck)(*strict*)
   apply(case_tac "da nat")
    apply(rename_tac n d x da nat ek ck)(*strict*)
    apply(rule_tac
      d = "da"
      and n = "nat"
      in epdaS.derivationNoFromNone)
      apply(rename_tac n d x da nat ek ck)(*strict*)
      apply(force)
     apply(rename_tac n d x da nat ek ck)(*strict*)
     apply(force)
    apply(rename_tac n d x da nat ek ck)(*strict*)
    apply(force)
   apply(rename_tac n d x da nat ek ck a)(*strict*)
   apply(case_tac a)
   apply(rename_tac n d x da nat ek ck a option b)(*strict*)
   apply(force)
  apply(rename_tac n d k x da nat)(*strict*)
  apply(erule exE)+
  apply(rename_tac n d k x da nat ek enat ck cnat)(*strict*)
  apply(subgoal_tac "\<exists>q. q \<in> epda_states M \<and> (epdaS.derivation M da \<and> (case get_configuration (da nat) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = q)\<and> (case get_configuration (da 0) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = epda_initial M))")
   apply(rename_tac n d k x da nat ek enat ck cnat)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
   apply(case_tac "da 0")
    apply(rename_tac n d k x da nat ek enat ck cnat)(*strict*)
    apply(force)
   apply(rename_tac n d k x da nat ek enat ck cnat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d da nat ek enat ck cnat a)(*strict*)
   apply(case_tac "da nat")
    apply(rename_tac n d da nat ek enat ck cnat a)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d da nat ek enat ck cnat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac n d da nat ek enat ck cnat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
    apply(subgoal_tac "cnat \<in> epdaS_configurations M")
     apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
     prefer 2
     apply(rule_tac
      d = "da"
      and m = "0"
      in epdaS.stays_in_configuration)
          apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
          apply(force)
         apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
         apply(force)
        apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
        apply(force)
       apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
       apply(subgoal_tac "epdaS_initial_configurations M \<subseteq> epdaS_configurations M")
        apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
        apply(force)
       apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
       apply(rule epdaS.AX_initial_configuration_belongs)
       apply(force)
      apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
      apply(force)
     apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
     apply(simp add: epdaS_configurations_def)
    apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
    apply(case_tac cnat)
    apply(rename_tac n d da nat ek enat ck cnat option b epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d da nat ek enat ck option b epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
    apply(simp add: epdaS_configurations_def)
   apply(rename_tac n d da nat ek enat ck cnat option b)(*strict*)
   apply(simp add: epdaS_initial_configurations_def)
  apply(rename_tac n d k x da nat ek enat ck cnat)(*strict*)
  apply(erule exE)+
  apply(rename_tac n d k x da nat ek enat ck cnat q)(*strict*)
  apply(erule conjE)+
  apply(simp add: get_configuration_def)
  apply(case_tac "d 0")
   apply(rename_tac n d k x da nat ek enat ck cnat q)(*strict*)
   apply(force)
  apply(rename_tac n d k x da nat ek enat ck cnat q a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d da nat ek enat ck cnat a)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac n d da nat ek enat ck cnat a)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat a aa)(*strict*)
  apply(clarsimp)
  apply(case_tac "a")
  apply(rename_tac n d da nat ek enat ck cnat a aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d da nat ek enat ck cnat aa option b)(*strict*)
  apply(case_tac "aa")
  apply(rename_tac n d da nat ek enat ck cnat aa option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba)(*strict*)
  apply(case_tac "da 0")
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba a)(*strict*)
  apply(clarsimp)
  apply(case_tac "da nat")
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba a)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba a)(*strict*)
  apply(case_tac "a")
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba a optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule_tac
      x = "epdaS_conf_state cnat"
      and P = "\<lambda>x. \<forall>l<Suc nat. x \<in> epda_states M \<and> (\<exists>d. epdaS.derivation M d \<and> (case case_option None (case_derivation_configuration (\<lambda>e. Some)) (d l) of None \<Rightarrow> False | Some c \<Rightarrow> epdaS_conf_state c = x) \<and> (case case_option None (case_derivation_configuration (\<lambda>e. Some)) (d 0) of None \<Rightarrow> False | Some c \<Rightarrow> c \<in> epdaS_initial_configurations M)) \<longrightarrow> P x"
      in allE)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule_tac
      x = "nat"
      in allE)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x = "da"
      in exI)
   apply(clarsimp)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule_tac
      x = "epdaS_conf_state cnat"
      in allE)
  apply(erule_tac
      x = "ek"
      in allE)
  apply(erule_tac
      x = "epdaS_conf_state ck"
      in allE)
  apply(erule_tac
      x = "cnat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "cnat \<in> epdaS_configurations M")
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rule_tac
      d = "da"
      and m = "0"
      in epdaS.stays_in_configuration)
        apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
        apply(force)
       apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
       apply(force)
      apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
      apply(force)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(subgoal_tac "epdaS_initial_configurations M \<subseteq> epdaS_configurations M")
      apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
      apply(force)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(rule epdaS.AX_initial_configuration_belongs)
     apply(force)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(erule impE)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(rule_tac
      d = "da"
      in epdaS.belongs_configurations)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(rule epdaS.derivation_initial_belongs)
      apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
      apply(force)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(simp add: epdaS.derivation_def)
     apply(erule_tac
      x = "0"
      and P = "\<lambda>x. case x of 0 \<Rightarrow> case da 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case da x of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case da i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> epdaS_step_relation M i'2 i1v i2"
      in allE)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(clarsimp)
     apply(case_tac "optionb")
      apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule_tac
      x = "ck"
      in allE)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(rule_tac
      d = "da"
      and m = "0"
      in epdaS.stays_in_configuration)
        apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
        apply(force)
       apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
       apply(force)
      apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
      apply(force)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(subgoal_tac "epdaS_initial_configurations M \<subseteq> epdaS_configurations M")
      apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
      apply(force)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(rule epdaS.AX_initial_configuration_belongs)
     apply(force)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(simp add: epdaS_accessible_states_def)
   apply(rule_tac
      x = "da"
      in exI)
   apply(rule conjI)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(rule_tac
      x = "nat"
      in exI)
    apply(simp add: get_configuration_def)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(subgoal_tac "epdaS_step_relation M cnat ek ck")
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   prefer 2
   apply(rule_tac
      d = "da"
      in epdaS.position_change_due_to_step_relation)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(force)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(erule impE)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(subgoal_tac "ek \<in> epda_step_labels M \<and> ck \<in> epdaS_configurations M")
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(rule epdaS.AX_step_relation_preserves_belongs)
     apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
     apply(force)
    apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
   apply(force)
  apply(rename_tac n d da nat ek enat ck cnat option b optiona ba optionb bb)(*strict*)
  apply(force)
  done

lemma epda_earliest_word_removal_position: "
  epdaS.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e cn)
  \<Longrightarrow> \<not> P c
  \<Longrightarrow> P cn
  \<Longrightarrow> P = (\<lambda>c. \<not>(\<exists>z. w@z = epdaS_conf_scheduler c))
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)) \<and>
                  (case d k of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)"
  apply(rule epdaS.existence_of_earliest_satisfaction_point)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epda_drop_terminals: "
  valid_epda G
  \<Longrightarrow> epdaS.derivation G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> case d (i+j) of None \<Rightarrow> True | Some (pair e' c') \<Rightarrow> \<exists>w. w@(epdaS_conf_scheduler c') = (epdaS_conf_scheduler c)"
  apply(rule_tac
      m = "i"
      and n = "j"
      in epdaS.property_preseved_under_steps_is_invariant2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(case_tac "d (Suc ia)")
   apply(rename_tac ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac ia a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac ia option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia b)(*strict*)
   apply(rule epdaS.derivation_Always_PreEdge_prime)
    apply(rename_tac ia b)(*strict*)
    apply(force)
   apply(rename_tac ia b)(*strict*)
   apply(force)
  apply(rename_tac ia option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia b a)(*strict*)
  apply(case_tac "d ia")
   apply(rename_tac ia b a)(*strict*)
   apply(rule epdaS.derivationNoFromNone)
     apply(rename_tac ia b a)(*strict*)
     apply(force)
    apply(rename_tac ia b a)(*strict*)
    apply(force)
   apply(rename_tac ia b a)(*strict*)
   apply(force)
  apply(rename_tac ia b a aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac ia b a aa option ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia b a option ba w)(*strict*)
  apply(subgoal_tac "epdaS_step_relation G ba a b")
   apply(rename_tac ia b a option ba w)(*strict*)
   prefer 2
   apply(rule epdaS.position_change_due_to_step_relation)
     apply(rename_tac ia b a option ba w)(*strict*)
     apply(force)
    apply(rename_tac ia b a option ba w)(*strict*)
    apply(force)
   apply(rename_tac ia b a option ba w)(*strict*)
   apply(force)
  apply(rename_tac ia b a option ba w)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ia b a option ba w wa)(*strict*)
  apply(rule_tac
      t = "epdaS_conf_scheduler c"
      and s = "w @ option_to_list (edge_event a) @ epdaS_conf_scheduler b"
      in ssubst)
   apply(rename_tac ia b a option ba w wa)(*strict*)
   apply(force)
  apply(rename_tac ia b a option ba w wa)(*strict*)
  apply(simp (no_asm))
  done

lemma epda_Nonblockingness2: "
  valid_epda G
  \<Longrightarrow> Nonblockingness2 (epdaS.unmarked_language G) (epdaS.marked_language G)"
  apply(simp add: Nonblockingness2_def)
  apply(simp add: epdaS.marked_language_def epdaS.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(simp add: epdaS_initial_configurations_def epdaS_marked_effect_def epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb)(*strict*)
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(case_tac "x")
   apply(rename_tac x d c ca i e cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ca i e cb)(*strict*)
   apply(rule_tac
      x = "der1 (ca\<lparr>epdaS_conf_scheduler:= []\<rparr>)"
      in exI)
   apply(rename_tac d ca i e cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d ca i e cb)(*strict*)
    apply(simp add: epdaS.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac d ca i e cb)(*strict*)
     apply(rule epdaS.der1_is_derivation)
    apply(rename_tac d ca i e cb)(*strict*)
    apply(simp add: der1_def)
    apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
    apply(clarsimp)
   apply(rename_tac d ca i e cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d ca i e cb)(*strict*)
    apply(simp add: epdaS_unmarked_effect_def)
    apply(simp add: der1_def)
   apply(rename_tac d ca i e cb)(*strict*)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac x d c ca i e cb a list)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>i. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c') \<Rightarrow> (\<lambda>x. length (epdaS_conf_scheduler x) \<le> length c)c')) \<and> (case d k of None \<Rightarrow> False | Some (pair e c') \<Rightarrow> (\<lambda>x. length (epdaS_conf_scheduler x) \<le> length c) c')")
   apply(rename_tac x d c ca i e cb a list)(*strict*)
   prefer 2
   apply(rule epdaS.existence_of_earliest_satisfaction_point)
     apply(rename_tac x d c ca i e cb a list)(*strict*)
     apply(force)
    apply(rename_tac x d c ca i e cb a list)(*strict*)
    apply(force)
   apply(rename_tac x d c ca i e cb a list)(*strict*)
   apply(force)
  apply(rename_tac x d c ca i e cb a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c ca i e cb a list k)(*strict*)
  apply(case_tac "d k")
   apply(rename_tac d c ca i e cb a list k)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c ca i e cb a list k aa)(*strict*)
  apply(case_tac aa)
  apply(rename_tac d c ca i e cb a list k aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c ca i e cb a list k option b)(*strict*)
  apply(rule_tac
      x = "\<lambda>n. (case (derivation_take d k) n of None \<Rightarrow> None | Some (pair e c') \<Rightarrow> Some (pair e (c'\<lparr>epdaS_conf_scheduler:= take (length (epdaS_conf_scheduler c') - length c) (epdaS_conf_scheduler c')\<rparr>)))"
      in exI)
  apply(rename_tac d c ca i e cb a list k option b)(*strict*)
  apply(subgoal_tac "epdaS.derivation G (\<lambda>n. case_option None (case_derivation_configuration (\<lambda>e c'. Some (pair e (c'\<lparr>epdaS_conf_scheduler := take (length (epdaS_conf_scheduler c') - length c) (epdaS_conf_scheduler c')\<rparr>)))) (derivation_take d k n)) \<and> (case case_option None (case_derivation_configuration (\<lambda>e c'. Some (pair e (c'\<lparr>epdaS_conf_scheduler := take (length (epdaS_conf_scheduler c') - length c) (epdaS_conf_scheduler c')\<rparr>)))) (derivation_take d k 0) of None \<Rightarrow> False | Some (pair a b) \<Rightarrow> b \<in> epdaS_initial_configurations G \<and> a = None)")
   apply(rename_tac d c ca i e cb a list k option b)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c ca i e cb a list k option b)(*strict*)
    apply(simp add: epdaS.derivation_initial_def)
   apply(rename_tac d c ca i e cb a list k option b)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c ca i e cb a list k option b)(*strict*)
    apply(simp add: epdaS_unmarked_effect_def)
    apply(rule_tac
      x = "ca\<lparr>epdaS_conf_scheduler:= a#list\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d c ca i e cb a list k option b)(*strict*)
     apply(simp add: derivation_take_def)
     apply(case_tac ca)
     apply(rename_tac d c ca i e cb a list k option b epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stack)(*strict*)
     apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b)(*strict*)
    apply(rule_tac
      x = "b\<lparr>epdaS_conf_scheduler:= []\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x = "k"
      in exI)
    apply(rule_tac
      x = "option"
      in exI)
    apply(simp add: derivation_take_def)
   apply(rename_tac d c ca i e cb a list k option b)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d c ca i e cb a list k option b)(*strict*)
  apply(simp add: derivation_take_def)
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(rule conjI)
   apply(rename_tac d c ca i e cb a list k option b)(*strict*)
   prefer 2
   apply(case_tac ca)
   apply(rename_tac d c ca i e cb a list k option b epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stack)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c i e cb a list k option b epdaS_conf_statea epdaS_conf_stack)(*strict*)
   apply(simp add: epdaS.derivation_initial_def)
   apply(simp add: epdaS_initial_configurations_def)
   apply(simp add: epdaS_configurations_def)
   apply(rule conjI)
    apply(rename_tac d c i e cb a list k option b epdaS_conf_statea epdaS_conf_stack)(*strict*)
    apply(rule valid_epda_initial_in_states)
    apply(force)
   apply(rename_tac d c i e cb a list k option b epdaS_conf_statea epdaS_conf_stack)(*strict*)
   apply(rule valid_epda_box_in_gamma)
   apply(force)
  apply(rename_tac d c ca i e cb a list k option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c ca i e cb a list k option b ia)(*strict*)
  apply(rule conjI)
   apply(rename_tac d c ca i e cb a list k option b ia)(*strict*)
   apply(clarsimp)
   apply(case_tac ia)
    apply(rename_tac d c ca i e cb a list k option b ia)(*strict*)
    apply(clarsimp)
   apply(rename_tac d c ca i e cb a list k option b ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
    apply(case_tac "Suc nat = k")
     apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
    apply(rule_tac
      M = "G"
      and d = "d"
      and n = "k"
      and i = "Suc nat"
      in epdaS.derivationNoFromNone2)
       apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
       apply(force)
      apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
      apply(force)
     apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat)(*strict*)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat aa)(*strict*)
   apply(case_tac "d nat")
    apply(rename_tac d c ca i e cb a list k option b nat aa)(*strict*)
    apply(rule_tac
      M = "G"
      and d = "d"
      and n = "k"
      and i = "nat"
      in epdaS.derivationNoFromNone2)
       apply(rename_tac d c ca i e cb a list k option b nat aa)(*strict*)
       apply(force)
      apply(rename_tac d c ca i e cb a list k option b nat aa)(*strict*)
      apply(force)
     apply(rename_tac d c ca i e cb a list k option b nat aa)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat aa)(*strict*)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat aa ab)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac d c ca i e cb a list k option b nat aa ab optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c ca i e cb a list k option b nat ab optiona ba)(*strict*)
   apply(case_tac ab)
   apply(rename_tac d c ca i e cb a list k option b nat ab optiona ba optionb bb)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c ca i e cb a list k option b nat optiona ba optionb bb)(*strict*)
   apply(case_tac optiona)
    apply(rename_tac d c ca i e cb a list k option b nat optiona ba optionb bb)(*strict*)
    apply(rule epdaS.derivation_Always_PreEdge_prime)
     apply(rename_tac d c ca i e cb a list k option b nat optiona ba optionb bb)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat optiona ba optionb bb)(*strict*)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat optiona ba optionb bb aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
   apply(subgoal_tac "epdaS_step_relation G bb aa ba")
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
    prefer 2
    apply(rule epdaS.position_change_due_to_step_relation)
      apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
      apply(force)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
   apply(subgoal_tac "\<exists>a z. a#z@c = epdaS_conf_scheduler bb")
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa ab z)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa ab z w)(*strict*)
    apply(simp add: option_to_list_def)
    apply(case_tac aa)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa ab z w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb ab z w edge_event edge_pop edge_push)(*strict*)
    apply(case_tac edge_event)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb ab z w edge_event edge_pop edge_push)(*strict*)
     apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb ab z w edge_event edge_pop edge_push aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb z w edge_pop edge_push aa)(*strict*)
    apply(rule List.take_all)
    apply(erule_tac
      x = "nat"
      in allE)
    apply(clarsimp)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
   apply(erule_tac
      x = "nat"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>w. w@epdaS_conf_scheduler bb = a#list@c")
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
    prefer 2
    apply(subgoal_tac "case d (0+nat) of None \<Rightarrow> True | Some (pair e' c') \<Rightarrow> \<exists>w. w@(epdaS_conf_scheduler c') = (epdaS_conf_scheduler ca)")
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
     prefer 2
     apply(rule epda_drop_terminals)
       apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
       apply(force)
      apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
      apply(force)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w)(*strict*)
   apply(subgoal_tac "prefix (a#list) w \<or> prefix w (a#list) ")
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w)(*strict*)
    apply(simp add: prefix_def)
    apply(erule disjE)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w)(*strict*)
     apply(clarsimp)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa cc)(*strict*)
     apply(subgoal_tac "a#list@cc@epdaS_conf_scheduler bb = a#list@c")
      apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa cc)(*strict*)
      prefer 2
      apply(clarsimp)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa cc)(*strict*)
     apply(subgoal_tac "cc @ epdaS_conf_scheduler bb = c")
      apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa cc)(*strict*)
      apply(force)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa cc)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
    apply(subgoal_tac "a#list@c = w @ epdaS_conf_scheduler bb")
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
    apply(subgoal_tac "w@cc@c = w @ epdaS_conf_scheduler bb")
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
     prefer 2
     apply(rule_tac
      t = "w@cc@c"
      and s = "(w@cc)@c"
      in ssubst)
      apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
      apply(simp (no_asm_use))
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
     apply(rule_tac
      t = "w@cc"
      and s = "a#list"
      in ssubst)
      apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
      apply(force)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
     apply(force)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
    apply(case_tac cc)
     apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc)(*strict*)
     apply(clarsimp)
    apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w cc ab lista)(*strict*)
    apply(force)
   apply(rename_tac d c ca i e cb a list k option b nat ba optionb bb aa w)(*strict*)
   apply(rule_tac
      b = "c"
      and d = "epdaS_conf_scheduler bb"
      in mutual_prefix_prefix)
   apply(force)
  apply(rename_tac d c ca i e cb a list k option b ia)(*strict*)
  apply(clarsimp)
  apply(case_tac ia)
   apply(rename_tac d c ca i e cb a list k option b ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c ca i e cb a list k option b ia nat)(*strict*)
  apply(clarsimp)
  done

lemma epda_earliest_word_removal_position_prime: "
  epdaS.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e cn)
  \<Longrightarrow> \<not> P c
  \<Longrightarrow> P cn
  \<Longrightarrow> P = (\<lambda>c. \<not>(\<exists>z. z@ca@epdaS_conf_scheduler cn = epdaS_conf_scheduler c))
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)) \<and>
                  (case d k of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)"
  apply(rule epdaS.existence_of_earliest_satisfaction_point)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epda_maximal_context_preserves_derivation_prime: "
  valid_epda M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> epdaS.belongs M dh
  \<Longrightarrow> epdaS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> epdaS_conf_scheduler c = w @ epdaS_conf_scheduler ca
  \<Longrightarrow> epdaS.derivation M
           (derivation_map dh
             (\<lambda>c. c\<lparr>epdaS_conf_scheduler :=
                      take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler ca)) (epdaS_conf_scheduler c) @ v\<rparr>))"
  apply(simp (no_asm_simp) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: derivation_map_def)
  apply(case_tac "dh (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh nat = Some (pair e c)")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat a ea cb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh (Suc nat) = Some (pair (Some e) c)")
   apply(rename_tac nat a ea cb)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaS.pre_some_position_is_some_position_prime)
      apply(rename_tac nat a ea cb)(*strict*)
      apply(force)
     apply(rename_tac nat a ea cb)(*strict*)
     apply(force)
    apply(rename_tac nat a ea cb)(*strict*)
    apply(force)
   apply(rename_tac nat a ea cb)(*strict*)
   apply(force)
  apply(rename_tac nat a ea cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat ea cb eaa caa)(*strict*)
  apply(subgoal_tac "epdaS_step_relation M cb eaa caa")
   apply(rename_tac nat ea cb eaa caa)(*strict*)
   apply(simp add: derivation_map_def)
   apply(simp add: epda_step_labels_def epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac nat ea cb eaa caa wa)(*strict*)
   apply(case_tac "edge_event eaa")
    apply(rename_tac nat ea cb eaa caa wa)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
   apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "Suc (length (epdaS_conf_scheduler caa)) - length (epdaS_conf_scheduler ca) \<ge> Suc 0")
    apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
   apply(subgoal_tac "length (epdaS_conf_scheduler caa) \<ge> length (epdaS_conf_scheduler ca)")
    apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
    apply(force)
   apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
   apply(subgoal_tac "Suc nat\<le>n")
    apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_string_state caa = w @ (epdaS_string_state ca)")
     apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
     prefer 2
     apply(rule_tac
      j = "n-(Suc nat)"
      in epdaS.derivation_monotonically_dec)
          apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
          apply(force)
         apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
         apply(force)
        apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
        apply(force)
       apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
       apply(force)
      apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
      apply(force)
     apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
     apply(force)
    apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat ea cb eaa caa wa a waa)(*strict*)
    apply(simp add: epdaS_string_state_def)
   apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
   apply(case_tac "Suc nat > n")
    apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
   apply(rule_tac
      m = "Suc nat"
      and n = "n"
      in epdaS.no_some_beyond_maximum_of_domain)
      apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
      apply(force)
     apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
     apply(force)
    apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
    apply(force)
   apply(rename_tac nat ea cb eaa caa wa a)(*strict*)
   apply(force)
  apply(rename_tac nat ea cb eaa caa)(*strict*)
  apply(rule epdaS.position_change_due_to_step_relation)
    apply(rename_tac nat ea cb eaa caa)(*strict*)
    apply(force)+
  done

lemma epda_maximal_context_preserves_derivation_with_Crop: "
  valid_epda M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> epdaS.belongs M dh
  \<Longrightarrow> epdaS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> epdaS_conf_scheduler c = w @ epdaS_conf_scheduler ca
  \<Longrightarrow> dh n1 = Some (pair e2 c2)
  \<Longrightarrow> n1\<le>n
  \<Longrightarrow> dh (n1 + min n2 (n - n1)) = Some (pair e1 c1)
  \<Longrightarrow> epdaS.derivation M
        (derivation_map (derivation_take (derivation_drop dh n1) (min n2 (n - n1)))
          (\<lambda>c. c\<lparr>epdaS_conf_scheduler :=
                   take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler ca)) (epdaS_conf_scheduler c)\<rparr>))"
  apply(simp (no_asm_simp) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
  apply(clarsimp)
  apply(case_tac "dh (Suc (nat + n1))")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh ((nat + n1)) = Some (pair e c)")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "(Suc (nat + n1))"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat a ea cb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh (Suc (nat + n1)) = Some (pair (Some e) c)")
   apply(rename_tac nat a ea cb)(*strict*)
   prefer 2
   apply(rule_tac
      m = "(Suc (nat + n1))"
      in epdaS.pre_some_position_is_some_position_prime)
      apply(rename_tac nat a ea cb)(*strict*)
      apply(force)
     apply(rename_tac nat a ea cb)(*strict*)
     apply(force)
    apply(rename_tac nat a ea cb)(*strict*)
    apply(force)
   apply(rename_tac nat a ea cb)(*strict*)
   apply(force)
  apply(rename_tac nat a ea cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat ea cb eaa caa)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
  apply(subgoal_tac "epdaS_step_relation M cb eaa caa")
   apply(rename_tac nat ea cb eaa caa)(*strict*)
   apply(case_tac nat)
    apply(rename_tac nat ea cb eaa caa)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac ea caa wa)(*strict*)
    apply(case_tac "edge_event ea")
     apply(rename_tac ea caa wa)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
    apply(rename_tac ea caa wa a)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "length (epdaS_conf_scheduler caa) \<ge> length (epdaS_conf_scheduler ca)")
     apply(rename_tac ea caa wa a)(*strict*)
     apply(force)
    apply(rename_tac ea caa wa a)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_string_state caa = w @ (epdaS_string_state ca)")
     apply(rename_tac ea caa wa a)(*strict*)
     prefer 2
     apply(rule_tac
      j = "n-(Suc n1)"
      in epdaS.derivation_monotonically_dec)
          apply(rename_tac ea caa wa a)(*strict*)
          apply(force)
         apply(rename_tac ea caa wa a)(*strict*)
         apply(force)
        apply(rename_tac ea caa wa a)(*strict*)
        apply(force)
       apply(rename_tac ea caa wa a)(*strict*)
       apply(force)
      apply(rename_tac ea caa wa a)(*strict*)
      apply(force)
     apply(rename_tac ea caa wa a)(*strict*)
     apply(force)
    apply(rename_tac ea caa wa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea caa wa a waa)(*strict*)
    apply(simp add: epdaS_string_state_def)
   apply(rename_tac nat ea cb eaa caa nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea cb eaa caa nata)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac ea cb eaa caa nata wa)(*strict*)
   apply(case_tac "edge_event eaa")
    apply(rename_tac ea cb eaa caa nata wa)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
   apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "length (epdaS_conf_scheduler caa) \<ge> length (epdaS_conf_scheduler ca)")
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    apply(force)
   apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
   apply(subgoal_tac "\<exists>w. epdaS_string_state caa = w @ (epdaS_string_state ca)")
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    prefer 2
    apply(rule_tac
      j = "n-(Suc (Suc (nata + n1)))"
      in epdaS.derivation_monotonically_dec)
         apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
         apply(force)
        apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
        apply(force)
       apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
       apply(force)
      apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
      apply(force)
     apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
     apply(force)
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    apply(rule_tac
      t = "(Suc (Suc (nata + n1)) + (n - Suc (Suc (nata + n1))))"
      and s = "n"
      in ssubst)
     apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
     apply(force)
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    apply(force)
   apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea cb eaa caa nata wa a waa)(*strict*)
   apply(simp add: epdaS_string_state_def)
  apply(rename_tac nat ea cb eaa caa)(*strict*)
  apply(rule epdaS.position_change_due_to_step_relation)
    apply(rename_tac nat ea cb eaa caa)(*strict*)
    apply(force)+
  done

lemma epda_maximal_context_preserves_derivation_with_Crop_prime: "
  valid_epda M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> epdaS.belongs M dh
  \<Longrightarrow> epdaS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> epdaS_conf_scheduler c = w @ epdaS_conf_scheduler ca
  \<Longrightarrow> dh n1 = Some (pair e2 c2)
  \<Longrightarrow> n1\<le>n
  \<Longrightarrow> dh (n1 + min n2 (n - n1)) = Some (pair e1 c1)
  \<Longrightarrow> epdaS.derivation M
        (derivation_map (derivation_take (derivation_drop dh n1) (min n2 (n - n1)))
          (\<lambda>c. c\<lparr>epdaS_conf_scheduler :=
                   take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler ca)) (epdaS_conf_scheduler c)@v\<rparr>))"
  apply(simp (no_asm_simp) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
  apply(clarsimp)
  apply(case_tac "dh (Suc (nat + n1))")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh ((nat + n1)) = Some (pair e c)")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "(Suc (nat + n1))"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat a ea cb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh (Suc (nat + n1)) = Some (pair (Some e) c)")
   apply(rename_tac nat a ea cb)(*strict*)
   prefer 2
   apply(rule_tac
      m = "(Suc (nat + n1))"
      in epdaS.pre_some_position_is_some_position_prime)
      apply(rename_tac nat a ea cb)(*strict*)
      apply(force)
     apply(rename_tac nat a ea cb)(*strict*)
     apply(force)
    apply(rename_tac nat a ea cb)(*strict*)
    apply(force)
   apply(rename_tac nat a ea cb)(*strict*)
   apply(force)
  apply(rename_tac nat a ea cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat ea cb eaa caa)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
  apply(subgoal_tac "epdaS_step_relation M cb eaa caa")
   apply(rename_tac nat ea cb eaa caa)(*strict*)
   apply(case_tac nat)
    apply(rename_tac nat ea cb eaa caa)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac ea caa wa)(*strict*)
    apply(case_tac "edge_event ea")
     apply(rename_tac ea caa wa)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
    apply(rename_tac ea caa wa a)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "length (epdaS_conf_scheduler caa) \<ge> length (epdaS_conf_scheduler ca)")
     apply(rename_tac ea caa wa a)(*strict*)
     apply(force)
    apply(rename_tac ea caa wa a)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_string_state caa = w @ (epdaS_string_state ca)")
     apply(rename_tac ea caa wa a)(*strict*)
     prefer 2
     apply(rule_tac
      j = "n-(Suc n1)"
      in epdaS.derivation_monotonically_dec)
          apply(rename_tac ea caa wa a)(*strict*)
          apply(force)
         apply(rename_tac ea caa wa a)(*strict*)
         apply(force)
        apply(rename_tac ea caa wa a)(*strict*)
        apply(force)
       apply(rename_tac ea caa wa a)(*strict*)
       apply(force)
      apply(rename_tac ea caa wa a)(*strict*)
      apply(force)
     apply(rename_tac ea caa wa a)(*strict*)
     apply(force)
    apply(rename_tac ea caa wa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea caa wa a waa)(*strict*)
    apply(simp add: epdaS_string_state_def)
   apply(rename_tac nat ea cb eaa caa nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea cb eaa caa nata)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac ea cb eaa caa nata wa)(*strict*)
   apply(case_tac "edge_event eaa")
    apply(rename_tac ea cb eaa caa nata wa)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
   apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "length (epdaS_conf_scheduler caa) \<ge> length (epdaS_conf_scheduler ca)")
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    apply(force)
   apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
   apply(subgoal_tac "\<exists>w. epdaS_string_state caa = w @ (epdaS_string_state ca)")
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    prefer 2
    apply(rule_tac
      j = "n-(Suc (Suc (nata + n1)))"
      in epdaS.derivation_monotonically_dec)
         apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
         apply(force)
        apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
        apply(force)
       apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
       apply(force)
      apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
      apply(force)
     apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
     apply(force)
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    apply(rule_tac
      t = "(Suc (Suc (nata + n1)) + (n - Suc (Suc (nata + n1))))"
      and s = "n"
      in ssubst)
     apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
     apply(force)
    apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
    apply(force)
   apply(rename_tac ea cb eaa caa nata wa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea cb eaa caa nata wa a waa)(*strict*)
   apply(simp add: epdaS_string_state_def)
  apply(rename_tac nat ea cb eaa caa)(*strict*)
  apply(rule epdaS.position_change_due_to_step_relation)
    apply(rename_tac nat ea cb eaa caa)(*strict*)
    apply(force)+
  done

lemma epda_maximal_context_preserves_belongs: "
  valid_epda M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> epdaS.belongs M dh
  \<Longrightarrow> epdaS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> epdaS_conf_scheduler c = w @ epdaS_conf_scheduler ca
  \<Longrightarrow> dh n1 = Some (pair e2 c2)
  \<Longrightarrow> n1\<le>n
  \<Longrightarrow> dh (n1 + min n2 (n - n1)) = Some (pair e1 c1)
  \<Longrightarrow> epdaS.belongs M (derivation_map (derivation_take (derivation_drop dh n1) (min n2 (n - n1))) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler ca)) (epdaS_conf_scheduler c)\<rparr>))"
  apply(rule epdaS.derivation_belongs)
     apply(force)
    apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
   apply(simp add: epdaS.belongs_def)
   apply(erule_tac
      x = "n1"
      in allE)
   apply(clarsimp)
   apply(simp add: epdaS_configurations_def)
   apply(clarsimp)
   apply(rename_tac q i s x)(*strict*)
   apply(rule_tac
      A = "set (take (length i - length (epdaS_conf_scheduler ca)) i)"
      in set_mp)
    apply(rename_tac q i s x)(*strict*)
    apply(rule_tac
      B = "set i"
      in subset_trans)
     apply(rename_tac q i s x)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac q i s x)(*strict*)
    apply(force)
   apply(rename_tac q i s x)(*strict*)
   apply(force)
  apply(rule epda_maximal_context_preserves_derivation_with_Crop)
           apply(force)+
  done

lemma epda_maximal_context_preserves_belongs_prime: "
  valid_epda M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> epdaS.belongs M dh
  \<Longrightarrow> epdaS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> epdaS_conf_scheduler c = w @ epdaS_conf_scheduler ca
  \<Longrightarrow> dh n1 = Some (pair e2 c2)
  \<Longrightarrow> n1\<le>n
  \<Longrightarrow> dh (n1 + min n2 (n - n1)) = Some (pair e1 c1)
  \<Longrightarrow> set v \<subseteq> epda_events M
  \<Longrightarrow> epdaS.belongs M (derivation_map (derivation_take (derivation_drop dh n1) (min n2 (n - n1))) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler ca)) (epdaS_conf_scheduler c) @ v\<rparr>))"
  apply(rule epdaS.derivation_belongs)
     apply(force)
    apply(simp add: derivation_map_def derivation_take_def derivation_drop_def)
   apply(simp add: epdaS.belongs_def)
   apply(erule_tac
      x = "n1"
      in allE)
   apply(clarsimp)
   apply(simp add: epdaS_configurations_def)
   apply(clarsimp)
   apply(rename_tac q i s x)(*strict*)
   apply(rule_tac
      A = "set (take (length i - length (epdaS_conf_scheduler ca)) i)"
      in set_mp)
    apply(rename_tac q i s x)(*strict*)
    apply(rule_tac
      B = "set i"
      in subset_trans)
     apply(rename_tac q i s x)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac q i s x)(*strict*)
    apply(force)
   apply(rename_tac q i s x)(*strict*)
   apply(force)
  apply(rule epda_maximal_context_preserves_derivation_with_Crop_prime)
           apply(force)+
  done

lemma may_terminated_by_EndStrY: "
  w \<in> may_terminated_by A y
  \<Longrightarrow> \<exists>x. w = x@[y]
  \<Longrightarrow> w \<in> must_terminated_by A y"
  apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
  apply(force)
  done

lemma epda_push_also_must_terminated_by: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> edge_pop e \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> edge_push e \<in> must_terminated_by (epda_gamma G) (epda_box G)"
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(simp add: valid_epda_step_label_def)
  apply(force)
  done

lemma epda_box_stays_at_bottom_prime: "
  valid_epda G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> \<exists>w. epdaS_conf_stack c = w @ [epda_box G]"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaS_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule epdaS.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
   apply(case_tac wa)
    apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i c e1 e2 c1 w)(*strict*)
    apply(subgoal_tac "edge_push e2 \<in> must_terminated_by (epda_gamma G) (epda_box G)")
     apply(rename_tac i c e1 e2 c1 w)(*strict*)
     prefer 2
     apply(rule epda_push_also_must_terminated_by)
       apply(rename_tac i c e1 e2 c1 w)(*strict*)
       apply(force)
      apply(rename_tac i c e1 e2 c1 w)(*strict*)
      apply(force)
     apply(rename_tac i c e1 e2 c1 w)(*strict*)
     apply(rule may_terminated_by_EndStrY)
      apply(rename_tac i c e1 e2 c1 w)(*strict*)
      apply(simp add: valid_epda_step_label_def)
     apply(rename_tac i c e1 e2 c1 w)(*strict*)
     apply(rule_tac
      x = "w"
      in exI)
     apply(force)
    apply(rename_tac i c e1 e2 c1 w)(*strict*)
    apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
    apply(force)
   apply(rename_tac i c e1 e2 c1 w wa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
    apply(rename_tac i c e1 e2 c1 w wa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac i c e1 e2 c1 w wa a list)(*strict*)
   apply(thin_tac "wa = a # list")
   apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
  apply(simp add: valid_epda_def)
  done

lemma epda_box_stays_at_bottom: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations G
  \<Longrightarrow> \<exists>w. epdaS_conf_stack c = w@[epda_box G]"
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac d i e)(*strict*)
  apply(rule epda_box_stays_at_bottom_prime)
    apply(rename_tac d i e)(*strict*)
    apply(force)
   apply(rename_tac d i e)(*strict*)
   apply(force)
  apply(rename_tac d i e)(*strict*)
  apply(force)
  done

lemma epda_stack_is_must_terminated_by_prime: "
  valid_epda G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
   apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaS_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule epdaS.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac i c e1 e2 c1 w)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w a)(*strict*)
  apply(case_tac w)
   apply(rename_tac i c e1 e2 c1 w a)(*strict*)
   apply(clarsimp)
   apply(rename_tac i c e1 e2 c1 a)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac i c e1 e2 c1 w a aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac i c e1 e2 c1 w a aa list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac i c e1 e2 c1 w a aa list)(*strict*)
  apply(thin_tac "w = aa # list")
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w' x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w' x a aa)(*strict*)
  apply(force)
  done

lemma epda_stack_is_must_terminated_by: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)"
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac d i e)(*strict*)
  apply(rule epda_stack_is_must_terminated_by_prime)
    apply(rename_tac d i e)(*strict*)
    apply(force)
   apply(rename_tac d i e)(*strict*)
   apply(force)
  apply(rename_tac d i e)(*strict*)
  apply(force)
  done

lemma valid_epda_push_in_gamma: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> set(edge_push e) \<subseteq> epda_gamma G"
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
  apply(force)
  done

lemma valid_epda_pop_in_gamma: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> set(edge_pop e) \<subseteq> epda_gamma G"
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
  apply(force)
  done

lemma valid_simple_dpda_to_valid_dpda: "
  valid_simple_dpda G
  \<Longrightarrow> valid_dpda G"
  apply(simp add: valid_simple_dpda_def)
  done

lemma valid_dpda_to_valid_pda: "
  valid_dpda G
  \<Longrightarrow> valid_pda G"
  apply(simp add: valid_dpda_def)
  done

lemma valid_pda_to_valid_epda: "
  valid_pda G
  \<Longrightarrow> valid_epda G"
  apply(simp add: valid_pda_def)
  done

lemma DPDA_to_epdaH_determinism: "
  valid_dpda G
  \<Longrightarrow> epdaH.is_forward_edge_deterministicHist_DB_long G"
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long G")
   prefer 2
   apply(rule epdaHS2HF_FEdetermHist)
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
   apply(subgoal_tac "epdaHS.is_forward_edge_deterministic_accessible G")
    prefer 2
    apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
     prefer 2
     apply(simp add: valid_simple_dpda_def valid_dpda_def)
    apply(rule_tac
      ?G1.0 = "G"
      in epdaS_vs_epdaHS.preserve_FEdetermR1)
     apply(clarsimp)
     apply(simp add: valid_dpda_to_valid_pda valid_pda_to_valid_epda valid_simple_dpda_to_valid_dpda)
    apply(force)
   apply(subgoal_tac "epdaHS.is_forward_edge_deterministicHist_DB_long G")
    prefer 2
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply (metis epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
   apply(force)
  apply(force)
  done

lemma epda_is_forward_edge_deterministicHist_DB_long_from_epdaH_to_epdaHS: "
  valid_epda M
  \<Longrightarrow> epdaH.is_forward_edge_deterministicHist_DB_long M
  \<Longrightarrow> epdaHS.is_forward_edge_deterministicHist_DB_long M"
  apply(simp add: epdaH.is_forward_edge_deterministicHist_DB_long_def epdaHS.is_forward_edge_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(erule_tac
      x = "epdaHvHS_Lin2BraConf c"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(rule_tac
      x = "epdaH_vs_epdaHS.Lin2BraDer d"
      in exI)
   apply(rule conjI)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(rule epdaH_vs_epdaHS.Lin2BraConf_preserves_initiality_lift)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def)
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
   apply(rule_tac
      x = "n"
      in exI)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(erule_tac
      x = "epdaHvHS_Lin2BraConf c1"
      in allE)
  apply(erule_tac
      x = "epdaHvHS_Lin2BraConf c2"
      in allE)
  apply(erule_tac
      x = "e1"
      in allE)
  apply(erule_tac
      x = "e2"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(rule_tac
      x = "w1"
      in exI)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(subgoal_tac "c1 \<in> epdaHS_configurations M")
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    prefer 2
    apply(subgoal_tac "X" for X)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     prefer 2
     apply(rule epdaHS.get_accessible_configurations_are_configurations)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(subgoal_tac "c \<in> epdaHS_configurations M")
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     prefer 2
     apply(rule_tac A="ATS.get_accessible_configurations epdaHS_initial_configurations
        epdaHS_step_relation M" in set_mp)
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     apply(simp add: epdaHS.get_accessible_configurations_def)
     apply(case_tac "d n")
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a)(*strict*)
     apply(clarsimp)
     apply(case_tac "a")
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a option conf)(*strict*)
     apply(clarsimp)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 option)(*strict*)
     apply(rule_tac x="d" in exI)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
     apply(rule_tac x="n" in exI)
     apply(clarsimp)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(rule epdaHS.AX_step_relation_preserves_belongsC)
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epda_effects_def epdaHS_configurations_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(rule_tac
      x = "w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(subgoal_tac "c2 \<in> epdaHS_configurations M")
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    prefer 2
    apply(subgoal_tac "X" for X)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     prefer 2
     apply(rule epdaHS.get_accessible_configurations_are_configurations)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(subgoal_tac "c \<in> epdaHS_configurations M")
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     prefer 2
     apply(rule_tac A="ATS.get_accessible_configurations epdaHS_initial_configurations
        epdaHS_step_relation M" in set_mp)
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     apply(simp add: epdaHS.get_accessible_configurations_def)
     apply(case_tac "d n")
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a)(*strict*)
     apply(clarsimp)
     apply(case_tac "a")
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 a option conf)(*strict*)
     apply(clarsimp)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2 option)(*strict*)
     apply(rule_tac x="d" in exI)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
     apply(rule_tac x="n" in exI)
     apply(clarsimp)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(rule epdaHS.AX_step_relation_preserves_belongsC)
      apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epda_effects_def epdaHS_configurations_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epdaH_step_relation_def epdaHvHS_Lin2BraConf_def epdaHS_step_relation_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epdaH_step_relation_def epdaHvHS_Lin2BraConf_def epdaHS_step_relation_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epdaH_step_relation_def epdaHvHS_Lin2BraConf_def epdaHS_step_relation_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
   apply(simp add: epdaH_step_relation_def epdaHvHS_Lin2BraConf_def epdaHS_step_relation_def)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
  apply(force)
  done

lemma epda_epdaS_is_forward_edge_deterministic_accessible_equal_to_epdaH_is_forward_edge_deterministicHist_DB_long: "
  valid_epda M
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible M \<longleftrightarrow> epdaH.is_forward_edge_deterministicHist_DB_long M"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rule epdaHS2HF_DEdetermR_FEdetermHist_DB)
    apply(force)
   apply(rule_tac
      ?G1.0 = "M"
      in epdaS_vs_epdaHS.preserve_FEdetermR1)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule epdaS_vs_epdaHS.preserve_FEdetermR2)
   apply(force)
  apply(rule_tac
      t = "epdaHS.is_forward_edge_deterministic_accessible M"
      in ssubst)
   apply(rule I_epda_HS.epdaHS.AX_is_forward_edge_deterministic_correspond_SB)
   apply(force)
  apply(rule_tac
      t = "ATS_determHIST_SB.is_forward_edge_deterministicHist_SB_long epdaHS_initial_configurations epdaHS_step_relation epda_effects (@) (@) epdaHS_conf_history epda_fixed_scheduler_extendable epdaHS_get_fixed_scheduler M"
      in ssubst)
   apply(rule I_epda_HS.epdaHS.AX_is_forward_edge_deterministic_correspond_DB_SB)
   apply(force)
  apply(rule epda_is_forward_edge_deterministicHist_DB_long_from_epdaH_to_epdaHS)
   apply(force)
  apply(force)
  done

lemma DPDA_is_is_forward_deterministicHist_SB: "
  valid_dpda G
  \<Longrightarrow> epdaH.is_forward_deterministicHist_SB G"
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(rule_tac
      t = "epdaH.is_forward_deterministicHist_SB G"
      and s = "epdaH.is_forward_deterministicHist_DB G"
      in ssubst)
   apply (rule epdaH.is_forward_deterministic_correspond_DB_SB)
   apply(force)
  apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
  apply(rule conjI)
   apply (metis epdaH_is_forward_target_deterministicHist_DB_long)
  apply(rule epdaHS2HF_FEdetermHist)
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
  apply(subgoal_tac "epdaHS.is_forward_edge_deterministic_accessible G")
   prefer 2
   apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
    prefer 2
    apply(simp add: valid_simple_dpda_def valid_dpda_def)
   apply (simp add: valid_dpda_to_valid_pda valid_pda_to_valid_epda valid_simple_dpda_to_valid_dpda)
   apply(rule epdaS_vs_epdaHS.preserve_FEdetermR1)
    apply(force)
   apply(force)
  apply(subgoal_tac "epdaHS.is_forward_edge_deterministicHist_DB_long G")
   prefer 2
   apply(clarsimp)
   apply (metis epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
  apply(force)
  done

theorem Nonblockingness_DPDA_without_empty_steps_from_final_states_is_Livelock_free: "
  valid_dpda M
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states M
  \<Longrightarrow> epdaH.Nonblockingness_branching_restricted M
  \<Longrightarrow> \<not> epdaH_livelock M"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(rule ccontr)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d N)(*strict*)
   prefer 2
   apply(rule_tac
      n = "N"
      and P = "\<lambda>N. \<forall>n\<ge>N. epdaH_conf_history (the (get_configuration (d n))) = epdaH_conf_history (the (get_configuration (d N))) "
      in ex_least_nat_le_prime)
   apply(rename_tac d N)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac d N)(*strict*)
  apply(thin_tac "\<forall>n\<ge>N. epdaH_conf_history (the (get_configuration (d n))) = epdaH_conf_history (the (get_configuration (d N)))")
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N k)(*strict*)
  apply(thin_tac "k\<le>N")
  apply(rename_tac d N k)(*strict*)
  apply(subgoal_tac "\<forall>i\<ge>k. epdaH_conf_state (the (get_configuration (d i))) \<notin> epda_marking M")
   apply(rename_tac d N k)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac d k i)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d k i)(*strict*)
    prefer 2
    apply(rule_tac
      G = "M"
      and d = "d"
      and n = "i"
      and m = "Suc i"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d k i)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d k i)(*strict*)
     apply(force)
    apply(rename_tac d k i)(*strict*)
    apply(force)
   apply(rename_tac d k i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k i e1 e2 c1 c2)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: epdaH_no_livelocks_from_marking_states_def)
   apply(erule_tac
      x = "d"
      in allE)
   apply(erule_tac
      x = "Suc i"
      and P = "\<lambda>x. epdaH.derivation_initial M d \<and> (\<exists>e. (\<exists>c. d x = Some (pair (Some e) c)) \<and> edge_src e \<in> epda_marking M \<and> edge_event e = None) \<longrightarrow> (\<exists>m>x. d m = None \<or> (\<exists>e'. (\<exists>c'. d m = Some (pair (Some e') c')) \<and> (\<exists>y. edge_event e' = Some y)))"
      in allE)
   apply(rename_tac d k i e1 e2 c1 c2)(*strict*)
   apply(erule impE)
    apply(rename_tac d k i e1 e2 c1 c2)(*strict*)
    apply(rule conjI)
     apply(rename_tac d k i e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d k i e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d k i e1 e2 c1 c2 w)(*strict*)
    apply(erule_tac x = "i" and P = "\<lambda>i. k \<le> i \<longrightarrow> epdaH_conf_history (the (case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = epdaH_conf_history (the (case d k of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c))" in allE')
    apply(rename_tac d k i e1 e2 c1 c2 w)(*strict*)
    apply(erule_tac
      x = "Suc i"
      and P = "\<lambda>i. k \<le> i \<longrightarrow> epdaH_conf_history (the (case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = epdaH_conf_history (the (case d k of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c))"
      in allE)
    apply(rename_tac d k i e1 e2 c1 c2 w)(*strict*)
    apply(clarsimp)
    apply(case_tac e2)
    apply(rename_tac d k i e1 e2 c1 c2 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac edge_eventa)
     apply(rename_tac d k i e1 e2 c1 c2 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
    apply(rename_tac d k i e1 e2 c1 c2 w edge_srca edge_eventa edge_popa edge_pusha edge_trga a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d k i e1 c1 c2 w edge_pop edge_push a)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac d k i e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k i e1 e2 c1 c2 m)(*strict*)
   apply(erule disjE)
    apply(rename_tac d k i e1 e2 c1 c2 m)(*strict*)
    apply(erule_tac
      x = "m"
      in allE)+
    apply(force)
   apply(rename_tac d k i e1 e2 c1 c2 m)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k i e1 e2 c1 c2 m e' c' y)(*strict*)
   apply(case_tac m)
    apply(rename_tac d k i e1 e2 c1 c2 m e' c' y)(*strict*)
    apply(force)
   apply(rename_tac d k i e1 e2 c1 c2 m e' c' y nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
   apply(erule_tac x = "nat" and P = "\<lambda>i. k \<le> i \<longrightarrow> epdaH_conf_history (the (case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = epdaH_conf_history (the (case d k of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c))" in allE')
   apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
   apply(erule_tac
      x = "Suc nat"
      and P = "\<lambda>i. k \<le> i \<longrightarrow> epdaH_conf_history (the (case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = epdaH_conf_history (the (case d k of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c))"
      in allE)
   apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
    prefer 2
    apply(rule_tac
      G = "M"
      and d = "d"
      and n = "nat"
      and m = "Suc nat"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
     apply(force)
    apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
    apply(force)
   apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat e1a c1a)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d k i e1 e2 c1 c2 e' c' y nat e1a c1a w wa)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac d N k)(*strict*)
  apply(thin_tac "epdaH_no_livelocks_from_marking_states M")
  apply(erule_tac x = "0" and P = "\<lambda>x. \<exists>y. d x = Some y" in allE')
  apply(erule exE)+
  apply(rename_tac d N k y)(*strict*)
  apply(case_tac y)
  apply(rename_tac d N k y option b)(*strict*)
  apply(subgoal_tac "option = None \<and> b \<in> epdaH_initial_configurations M")
   apply(rename_tac d N k y option b)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac d N k y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d k b)(*strict*)
  apply(simp add: epdaH_initial_configurations_def)
  apply(clarsimp)
  apply(case_tac b)
  apply(rename_tac d k b epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d k)(*strict*)
  apply(case_tac "\<exists>j<k. epdaH_conf_state (the (get_configuration (d j))) \<in> epda_marking M")
   apply(rename_tac d k)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac d k)(*strict*)
   apply(simp add: epdaH.Nonblockingness_branching_restricted_def)
   apply(erule_tac
      x = "derivation_take d k"
      in allE)
   apply(erule_tac
      x = "k"
      and P = "\<lambda>n. epdaH.derivation_initial M (derivation_take d k) \<and> maximum_of_domain (derivation_take d k) n \<longrightarrow> (\<exists>dc. epdaH.derivation M dc \<and> epdaH.belongs M dc \<and> (\<exists>n'. maximum_of_domain dc n') \<and> derivation_append_fit (derivation_take d k) dc n \<and> epdaH_marking_condition M (derivation_append (derivation_take d k) dc n))"
      in allE)
   apply(rename_tac d k)(*strict*)
   apply(erule impE)
    apply(rename_tac d k)(*strict*)
    apply(rule conjI)
     apply(rename_tac d k)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac d k)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d k)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k dc n')(*strict*)
   apply(simp add: epdaH_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac d k dc n' i e c)(*strict*)
   apply(thin_tac "\<forall>j e' c'. i < j \<and> derivation_append (derivation_take d k) dc k j = Some (pair e' c') \<longrightarrow> epdaH_string_state c = epdaH_string_state c'")
   apply(rename_tac d k dc n' i e c)(*strict*)
   apply(simp add: epdaH_marking_configurations_def)
   apply(clarsimp)
   apply(thin_tac "c \<in> epdaH_configurations M")
   apply(case_tac c)
   apply(rename_tac d k dc n' i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k dc n' i e epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(rename_tac q1 h1 s1)
   apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
   apply(case_tac "i\<le>k")
    apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
    apply(erule_tac
      x = "i"
      and P = "\<lambda>i. \<exists>y. d i = Some y"
      in allE)
    apply(clarsimp)
    apply(rename_tac d k dc n' i e q1 h1 s1 y)(*strict*)
    apply(erule_tac
      x = "i"
      and P = "\<lambda>i. k \<le> i \<longrightarrow> epdaH_conf_state (the (get_configuration (d i))) \<notin> epda_marking M"
      in allE)
    apply(erule_tac
      x = "i"
      and P = "\<lambda>i. i < k \<longrightarrow> epdaH_conf_state (the (get_configuration (d i))) \<notin> epda_marking M"
      in allE)
    apply(clarsimp)
    apply(simp add: derivation_append_def derivation_append_fit_def derivation_take_def)
    apply(clarsimp)
    apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
    apply(case_tac "k = i")
     apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
     apply(clarsimp)
     apply(rename_tac d dc n' i e q1 h1 s1)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
    apply(subgoal_tac "i<k")
     apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
    apply(clarsimp)
    apply(simp (no_asm_use) add: get_configuration_def)
    apply(force)
   apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
   apply(subgoal_tac "k<i")
    apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
    prefer 2
    apply(rule_tac
      M = "M"
      and g = "dc"
      in epdaH.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac d k dc n' i e q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
   apply(thin_tac "\<forall>j<k. epdaH_conf_state (the (get_configuration (d j))) \<notin> epda_marking M")
   apply(subgoal_tac "X" for X)
    apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
    prefer 2
    apply(rule_tac
      G = "M"
      and ?d1.0 = "d"
      and ?d2.0 = "derivation_append (derivation_take d k) dc k"
      and x = "k"
      and y = "k"
      and n = "i-k"
      and m = "i-k"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
              apply(force)
             apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
             apply(rule epdaH.derivation_append_preserves_derivation_initial)
               apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
              apply(rule epdaH.derivation_take_preserves_derivation_initial)
              apply(force)
             apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
             apply(rule epdaH.derivation_append_preserves_derivation)
               apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
               apply(rule epdaH.derivation_take_preserves_derivation)
               apply(rule epdaH.derivation_initial_is_derivation)
               apply(force)
              apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
              apply(force)
             apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
             apply(simp add: derivation_take_def)
             apply(case_tac "d k")
              apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
              apply(erule_tac
      x = "k"
      in allE)+
              apply(force)
             apply(rename_tac d k dc n' i e q1 h1 s1 c a)(*strict*)
             apply(clarsimp)
             apply(case_tac a)
             apply(rename_tac d k dc n' i e q1 h1 s1 c a option b)(*strict*)
             apply(clarsimp)
             apply(rename_tac d k dc n' i e q1 h1 s1 c option b)(*strict*)
             apply(simp add: derivation_append_fit_def)
            apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
            apply(subgoal_tac "epdaH.is_forward_deterministicHist_SB M")
             apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
             apply(force)
            apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
            apply(rule DPDA_is_is_forward_deterministicHist_SB)
            apply(force)
           apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
           apply(simp add: derivation_append_def derivation_append_fit_def derivation_take_def)
          apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
          apply(force)
         apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
         apply(force)
        apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
        apply(force)
       apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
       apply(force)
      apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
      apply(force)
     apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
     apply(rule_tac
      t = "k+(i-k)"
      and s = "i"
      in ssubst)
      apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
      apply(force)
     apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
     apply(rule_tac
      t = "epdaH_conf_history (the (get_configuration (d i)))"
      and s = "epdaH_conf_history (the (get_configuration (d k)))"
      in ssubst)
      apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
      apply(erule_tac
      x = "i"
      and P = "\<lambda>i. k \<le> i \<longrightarrow> epdaH_conf_history (the (get_configuration (d i))) = epdaH_conf_history (the (get_configuration (d k)))"
      in allE)
      apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
      apply(force)
     apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
     apply(erule_tac x = "k" and P = "\<lambda>k. \<exists>y. d k = Some y" in allE')
     apply(clarify)
     apply(rename_tac d k dc n' i e q1 h1 s1 c y)(*strict*)
     apply(case_tac y)
     apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
     apply(rule_tac
      t = "epdaH_conf_history (the (get_configuration (d k)))"
      and s = "epdaH_conf_history (the (get_configuration (dc 0)))"
      in ssubst)
      apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
      apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def)
      apply(simp (no_asm_use))
      apply(clarsimp)
      apply(rename_tac d k dc n' i e q1 h1 s1 c option)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
     apply(rule_tac
      t = "epdaH_conf_history (the (get_configuration (derivation_append (derivation_take d k) dc k i)))"
      and s = "epdaH_conf_history (the (get_configuration (dc (i-k))))"
      in ssubst)
      apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
      apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
      apply(clarsimp)
     apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
     apply(subgoal_tac "X" for X)
      apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
      prefer 2
      apply(rule_tac
      G = "M"
      and d = "dc"
      and n = "0"
      and m = "i-k"
      in epdaH.steps_extend_history_derivation)
          apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
          apply(simp add: valid_dpda_def valid_pda_def)
         apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
         apply(force)
        apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
        prefer 2
        apply(clarsimp)
        apply(rename_tac d k dc n' i e q1 h1 s1 c option b)(*strict*)
        apply(simp add: get_configuration_def)
       apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
       apply(rule_tac
      d = "dc"
      in epdaH.belongs_configurations)
        apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
        apply(force)
       apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
       apply(force)
      apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
      apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
      apply(clarsimp)
      apply(rename_tac d k dc n' i e q1 h1 s1 c option)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac d k dc n' i e q1 h1 s1 c y option b)(*strict*)
     apply(simp add: get_configuration_def)
     apply(clarsimp)
     apply(rename_tac d k dc n' i e q1 s1 c option b h)(*strict*)
     apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
     apply(clarsimp)
    apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
    apply(force)
   apply(rename_tac d k dc n' i e q1 h1 s1 c)(*strict*)
   apply(erule_tac
      x = "i"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d k)(*strict*)
  apply(clarsimp)
  apply(rename_tac d k j)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d k j)(*strict*)
   prefer 2
   apply(rule_tac
      n = "k"
      and x = "j"
      and P = "\<lambda>j. epdaH_conf_state (the (get_configuration (d j))) \<in> epda_marking M"
      in ex_max_limited)
    apply(rename_tac d k j)(*strict*)
    apply(force)
   apply(rename_tac d k j)(*strict*)
   apply(force)
  apply(rename_tac d k j)(*strict*)
  apply(thin_tac "j < k")
  apply(thin_tac "epdaH_conf_state (the (get_configuration (d j))) \<in> epda_marking M")
  apply(clarsimp)
  apply(rename_tac d k ka)(*strict*)
  apply(case_tac k)
   apply(rename_tac d k ka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(simp add: get_configuration_def)
   apply(erule_tac
      x = "0"
      in allE)+
   apply(clarsimp)
  apply(rename_tac d k ka nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka nat)(*strict*)
  apply(rename_tac k)
  apply(rename_tac d ka k)(*strict*)
  apply(subgoal_tac "epdaH_conf_history (the (get_configuration (d k))) \<noteq> epdaH_conf_history (the (get_configuration (d (Suc k))))")
   apply(rename_tac d ka k)(*strict*)
   prefer 2
   apply(erule_tac
      x = "k"
      and P = "\<lambda>x. x < Suc k \<longrightarrow> (\<exists>n\<ge>x. epdaH_conf_history (the (get_configuration (d n))) \<noteq> epdaH_conf_history (the (get_configuration (d x))))"
      in allE)
   apply(rename_tac d ka k)(*strict*)
   apply(erule impE)
    apply(rename_tac d ka k)(*strict*)
    apply(force)
   apply(rename_tac d ka k)(*strict*)
   apply(erule exE)+
   apply(rename_tac d ka k n)(*strict*)
   apply(erule conjE)+
   apply(case_tac "n = k")
    apply(rename_tac d ka k n)(*strict*)
    apply(force)
   apply(rename_tac d ka k n)(*strict*)
   apply(erule_tac
      x = "n"
      and P = "\<lambda>n. Suc k \<le> n \<longrightarrow> epdaH_conf_history (the (get_configuration (d n))) = epdaH_conf_history (the (get_configuration (d (Suc k))))"
      in allE)
   apply(rename_tac d ka k n)(*strict*)
   apply(erule impE)
    apply(rename_tac d ka k n)(*strict*)
    apply(force)
   apply(rename_tac d ka k n)(*strict*)
   apply(force)
  apply(rename_tac d ka k)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ka k)(*strict*)
   prefer 2
   apply(rule_tac
      G = "M"
      and d = "d"
      and n = "k"
      and m = "Suc k"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d ka k)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d ka k)(*strict*)
    apply(erule_tac
      x = "Suc k"
      in allE)+
    apply(force)
   apply(rename_tac d ka k)(*strict*)
   apply(force)
  apply(rename_tac d ka k)(*strict*)
  apply(erule exE)+
  apply(rename_tac d ka k e1 e2 c1 c2)(*strict*)
  apply(erule conjE)+
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d ka k e1 e2 c1 c2 w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d ka k e1 e2 c1 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d ka k e1 e2 c1 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d ka k e1 e2 c1 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac h src read pop push trg)
  apply(rename_tac d ka k e1 w h src read pop push trg)(*strict*)
  apply(case_tac "read")
   apply(rename_tac d ka k e1 w h src read pop push trg)(*strict*)
   apply(simp add: get_configuration_def option_to_list_def)
  apply(rename_tac d ka k e1 w h src read pop push trg a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
  apply(thin_tac "epdaH_conf_history (the (get_configuration (Some (pair e1 \<lparr>epdaH_conf_state = src, epdaH_conf_history = h, epdaH_conf_stack = pop @ w\<rparr>)))) \<noteq> epdaH_conf_history (the (get_configuration (Some (pair (Some \<lparr>edge_src = src, edge_event = Some a, edge_pop = pop, edge_push = push, edge_trg = trg\<rparr>) \<lparr>epdaH_conf_state = trg, epdaH_conf_history = h @ option_to_list (Some a), epdaH_conf_stack = push @ w\<rparr>))))")
  apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
  apply(simp add: epdaH.Nonblockingness_branching_restricted_def)
  apply(erule_tac
      x = "derivation_take d (Suc k)"
      in allE)
  apply(erule_tac
      x = "Suc k"
      and P = "\<lambda>n. epdaH.derivation_initial M (derivation_take d (Suc k)) \<and> maximum_of_domain (derivation_take d (Suc k)) n \<longrightarrow> (\<exists>dc. epdaH.derivation M dc \<and> epdaH.belongs M dc \<and> (\<exists>n'. maximum_of_domain dc n') \<and> derivation_append_fit (derivation_take d (Suc k)) dc n \<and> epdaH_marking_condition M (derivation_append (derivation_take d (Suc k)) dc n))"
      in allE)
  apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
  apply(erule impE)
   apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d ka k e1 w h src pop push trg a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n')(*strict*)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e c)(*strict*)
  apply(simp add: epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(thin_tac "c \<in> epdaH_configurations M")
  apply(case_tac c)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
  apply(case_tac "i = Suc k")
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1)(*strict*)
   apply(simp add: derivation_append_def derivation_append_fit_def derivation_take_def)
   apply(clarsimp)
   apply(rename_tac d ka k e1 w h src pop push a dc n' q1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d ka k e1 w h src pop push a dc n' q1)(*strict*)
    prefer 2
    apply(rule_tac
      M = "M"
      and g = "dc"
      in epdaH.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac d ka k e1 w h src pop push a dc n' q1)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x = "Suc k"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
  apply(case_tac "i<Suc k")
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x = "Suc k"
      and P = "\<lambda>j. \<forall>e' c'. i < j \<and> derivation_append (derivation_take d (Suc k)) dc (Suc k) j = Some (pair e' c') \<longrightarrow> epdaH_string_state \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h1, epdaH_conf_stack = s1\<rparr> = epdaH_string_state c'"
      in allE)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
   apply(simp add: derivation_append_def derivation_append_fit_def derivation_take_def)
   apply(simp add: epdaH_string_state_def)
   apply(clarsimp)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
    prefer 2
    apply(rule_tac
      G = "M"
      and d = "d"
      and n = "i"
      and m = "k - i"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
     apply(rule_tac
      d = "d"
      in epdaH.belongs_configurations)
      apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
      apply(force)
     apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
     apply(force)
    apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 s1)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
  apply(subgoal_tac "Suc k<i")
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "derivation_append (derivation_take d (Suc k)) dc (Suc k) i = dc (i-Suc k)")
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
   prefer 2
   apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
   apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. Suc k+Suc x = i")
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
   prefer 2
   apply (metis add_Suc_right add_Suc_shift less_iff_Suc_add)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' i e q1 h1 s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
   prefer 2
   apply(rule_tac
      M = "M"
      and g = "dc"
      in epdaH.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x c)(*strict*)
  apply(subgoal_tac "c = \<lparr>epdaH_conf_state = trg, epdaH_conf_history = h @ [a], epdaH_conf_stack = push @ w\<rparr>")
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x c)(*strict*)
   prefer 2
   apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
   apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
   prefer 2
   apply(rule_tac
      G = "M"
      and ?d1.0 = "d"
      and ?d2.0 = "derivation_append (derivation_take d (Suc k)) dc (Suc k)"
      and x = "Suc k"
      and y = "Suc k"
      and n = "(Suc ((x)))"
      and m = "(Suc ((x)))"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
             apply(force)
            apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
            apply(rule epdaH.derivation_append_preserves_derivation_initial)
              apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
             apply(rule epdaH.derivation_take_preserves_derivation_initial)
             apply(force)
            apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
            apply(rule epdaH.derivation_append_preserves_derivation)
              apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
              apply(rule epdaH.derivation_take_preserves_derivation)
              apply(rule epdaH.derivation_initial_is_derivation)
              apply(force)
             apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
             apply(force)
            apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
            apply(simp add: derivation_take_def)
           apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
           apply(rule DPDA_is_is_forward_deterministicHist_SB)
           apply(force)
          apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
          apply(simp add: derivation_append_def derivation_append_fit_def derivation_take_def)
         apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
         apply(force)
        apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
        apply(simp add: derivation_append_def derivation_append_fit_def derivation_take_def)
       apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
       apply(force)
      apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
      apply(force)
     apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
     apply(force)
    apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
     prefer 2
     apply(rule_tac
      G = "M"
      and d = "dc"
      and n = "0"
      and m = "Suc x"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
        apply(force)
       apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
       prefer 2
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
      apply(rule_tac
      d = "dc"
      in epdaH.belongs_configurations)
       apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
       apply(force)
      apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
      apply(force)
     apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
     apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
    apply(simp add: get_configuration_def)
    apply(clarsimp)
   apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
   apply(simp (no_asm_use) only: derivation_append_fit_def derivation_take_def derivation_append_def)
   apply(force)
  apply(rename_tac d ka k e1 w h src pop push trg a dc n' e q1 h1 s1 x)(*strict*)
  apply(erule_tac
      x = "Suc (Suc(k+x))"
      in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  done

theorem epdaS_to_epdaHS_accessible: "
  valid_epda G
  \<Longrightarrow> epdaS.accessible G
  \<Longrightarrow> epdaHS.accessible G"
  apply(simp add: epdaHS.accessible_def epdaS.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> epdaS.get_accessible_destinations G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "epda_destinations G \<subseteq> epdaS.get_accessible_destinations G")
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> epda_destinations G")
  apply(simp add: epdaS.get_accessible_destinations_def epdaHS.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: epdaS_get_destinations_def)
  apply(case_tac c)
  apply(rename_tac x d i e c epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e epdaS_conf_state epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply(rename_tac n e q i s)
  apply(rename_tac x d n e q i s)(*strict*)
  apply(rule_tac
      x = "epdaS2epdaHS_derivation G d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n e q i s)(*strict*)
   apply(rule epdaS2epdaHS_derivation_preserves_derivation_initial)
    apply(rename_tac x d n e q i s)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac x d n e q i s)(*strict*)
   apply(force)
  apply(rename_tac x d n e q i s)(*strict*)
  apply(rule_tac
      x = "n"
      in exI)
  apply(simp add: epdaS2epdaHS_derivation_def epdaHS_get_destinations_def)
  done

theorem epdaHS_to_epdaH_accessible: "
  valid_epda G
  \<Longrightarrow> epdaHS.accessible G
  \<Longrightarrow> epdaH.accessible G"
  apply(simp add: epdaHS.accessible_def epdaH.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> epdaHS.get_accessible_destinations G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "epda_destinations G \<subseteq> epdaHS.get_accessible_destinations G")
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> epda_destinations G")
  apply(simp add: epdaH.get_accessible_destinations_def epdaHS.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: epdaHS_get_destinations_def)
  apply(case_tac c)
  apply(rename_tac x d i e c epdaHS_conf_statea epdaHS_conf_history epdaHS_conf_scheduler epdaHS_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e epdaHS_conf_state epdaHS_conf_history epdaHS_conf_scheduler epdaHS_conf_stack)(*strict*)
  apply(rename_tac n e q i s)
  apply(rename_tac x d ia n e q i s)(*strict*)
  apply(rule_tac
      x = "epdaH_vs_epdaHS.Lin2BraDer d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d ia n e q i s)(*strict*)
   apply(rule epdaH_vs_epdaHS.Lin2BraConf_preserves_initiality_lift)
    apply(rename_tac x d ia n e q i s)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac x d ia n e q i s)(*strict*)
   apply(force)
  apply(rename_tac x d ia n e q i s)(*strict*)
  apply(rule_tac
      x = "ia"
      in exI)
  apply(simp add: epdaHvHS_Lin2BraConf_def derivation_map_def epdaH_vs_epdaHS.Lin2BraDer_def epdaH_get_destinations_def)
  done

theorem epdaS_to_epdaH_accessible: "
  valid_epda G
  \<Longrightarrow> epdaS.accessible G
  \<Longrightarrow> epdaH.accessible G"
  apply (metis epdaHS_to_epdaH_accessible epdaS_to_epdaHS_accessible)
  done

definition only_executing_edges_from_marking_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "only_executing_edges_from_marking_states G \<equiv>
  \<forall>e \<in> epda_delta G.
  edge_event e = None
  \<longrightarrow> edge_src e \<notin> epda_marking G"

lemma epda_no_empty_steps_from_marking_states__vs__only_executing_edges_from_marking_states: "
  valid_epda G
  \<Longrightarrow> epda_no_empty_steps_from_marking_states G \<longleftrightarrow> only_executing_edges_from_marking_states G"
  apply(simp add: epda_no_empty_steps_from_marking_states_def only_executing_edges_from_marking_states_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(force)
  done

lemma DPDA_only_executing_edges_from_marking_states_implies_epdaH_non_ambiguous_hlp: "
  valid_dpda G
  \<Longrightarrow> only_executing_edges_from_marking_states G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> q1 \<in> epda_marking G
  \<Longrightarrow> q2 \<in> epda_marking G
  \<Longrightarrow> d1 0 = d2 0
  \<Longrightarrow> d1 n1 = Some (pair option \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)
  \<Longrightarrow> d2 n2 = Some (pair optiona \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>)
  \<Longrightarrow> n1 \<le> n2
  \<Longrightarrow> d2 n1 = Some (pair option \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)
  \<Longrightarrow> n1 < n2
  \<Longrightarrow> False"
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      d = "d2"
      and n = "n1"
      and m = "n2"
      in epdaH.step_detail_before_some_position)
     apply(simp add: epdaH.derivation_initial_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e2 c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and n = "Suc n1"
      and m = "n2-Suc n1"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac e2 c2)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac e2 c2)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac e2 c2)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac e2 c2)(*strict*)
    apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
     apply(rename_tac e2 c2)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac e2 c2)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac e2 c2)(*strict*)
     apply(force)
    apply(rename_tac e2 c2)(*strict*)
    apply(force)
   apply(rename_tac e2 c2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2 c2 h)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e2 c2 w)(*strict*)
  apply(case_tac c2)
  apply(rename_tac e2 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2 w epdaH_conf_history)(*strict*)
  apply(rename_tac h)
  apply(rename_tac e2 w h)(*strict*)
  apply(case_tac e2)
  apply(rename_tac e2 w h edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac w h edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac w h qs re po pu qt)(*strict*)
  apply(case_tac re)
   apply(rename_tac w h qs re po pu qt)(*strict*)
   prefer 2
   apply(rename_tac w h qs re po pu qt a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac w h qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac w h qs po pu qt)(*strict*)
  apply(simp add: only_executing_edges_from_marking_states_def)
  apply(erule_tac
      x = "\<lparr>edge_src = qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in ballE)
   apply(rename_tac w h qs po pu qt)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w h qs po pu qt)(*strict*)
  apply(force)
  done

theorem DPDA_only_executing_edges_from_marking_states_implies_epdaH_non_ambiguous: "
  valid_dpda G
  \<Longrightarrow> only_executing_edges_from_marking_states G
  \<Longrightarrow> epdaH_non_ambiguous G"
  apply(simp add: epdaH_non_ambiguous_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2)(*strict*)
  apply(subgoal_tac "d1 0 = d2 0")
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def)
   apply(case_tac "d1 0")
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 b)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 b)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 b a option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 b ba)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2)(*strict*)
  apply(case_tac "d1 n1")
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 a)(*strict*)
  apply(case_tac a)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b)(*strict*)
  apply(case_tac "d2 n2")
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b optiona ba)(*strict*)
  apply(subgoal_tac "b = \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>")
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b optiona ba)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option optiona ba)(*strict*)
  apply(thin_tac "get_configuration (Some (pair option \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>)) = Some \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>")
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option optiona ba)(*strict*)
  apply(subgoal_tac "ba = \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>")
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option optiona ba)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option optiona)(*strict*)
  apply(thin_tac "get_configuration (Some (pair optiona \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>)) = Some \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr>")
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 option optiona)(*strict*)
  apply(rename_tac e1 e2)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
  apply(subgoal_tac "n1 = n2")
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
   prefer 2
   apply(case_tac "n1<n2")
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and x = "0"
      and y = "0"
      and n = "n1"
      and m = "n2"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
               apply(force)
              apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
              apply(force)
             apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
            apply(simp add: epdaH.derivation_initial_def)
           apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
      apply(clarsimp)
      apply(simp add: epda_effects_def)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(simp)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(clarsimp)
    apply(case_tac "d2 n1")
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2 a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(rule_tac
      ?q1.0 = "q1"
      and ?q2.0 = "q2"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and ?n1.0 = "n1"
      and ?n2.0 = "n2"
      in DPDA_only_executing_edges_from_marking_states_implies_epdaH_non_ambiguous_hlp)
               apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
               apply(force)
              apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
              apply(force)
             apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
             apply(force)
            apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
            apply(force)
           apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
   apply(case_tac "n2<n1")
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(thin_tac "\<not> n1 < n2")
    apply(subgoal_tac "False")
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and x = "0"
      and y = "0"
      and n = "n2"
      and m = "n1"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
               apply(force)
              apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
              apply(force)
             apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
            apply(simp add: epdaH.derivation_initial_def)
           apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
      apply(clarsimp)
      apply(simp add: epda_effects_def)
      apply(simp add: get_configuration_def)
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(simp)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(clarsimp)
    apply(case_tac "d1 n2")
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2 a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(rule_tac
      ?q1.0 = "q2"
      and ?q2.0 = "q1"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and ?n1.0 = "n2"
      and ?n2.0 = "n1"
      in DPDA_only_executing_edges_from_marking_states_implies_epdaH_non_ambiguous_hlp)
               apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
               apply(force)
              apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
              apply(force)
             apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
             apply(force)
            apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
            apply(force)
           apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 q1 q2 h s1 s2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
   prefer 2
   apply(rule_tac
      g = "d1"
      and n = "i"
      and m = "n2"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
   prefer 2
   apply(rule_tac
      g = "d2"
      and n = "i"
      and m = "n2"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and n = "i"
      and m = "n2-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
    apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
     apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca ha)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca a)(*strict*)
  apply(case_tac a)
  apply(rename_tac d1 d2 n2 q1 q2 h s1 s2 e1 e2 i e ea c ca a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and n = "0"
      and m = "i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
    apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and d = "d1"
      and n = "i"
      and m = "n2-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
  apply(case_tac "d1 0")
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha a)(*strict*)
  apply(case_tac a)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and n = "0"
      and m = "i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb)(*strict*)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac b)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c ca option b ha h hb epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c option ha h hb epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(case_tac c)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea c option ha h hb epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1 e2 i e ea option ha h hb epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateb epdaH_conf_history epdaH_conf_stackb)(*strict*)
  apply(rename_tac e1 ha h hb qx1 sx1 qx2 hx2 sx3 qs5 h4 s3)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 hx2 sx3 qs5 h4 s3)(*strict*)
  apply(subgoal_tac "hx2 = []")
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 hx2 sx3 qs5 h4 s3)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 hx2 sx3 qs5 h4 s3)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 sx3 qs5 h4 s3)(*strict*)
  apply(subgoal_tac "prefix h h4 \<or> SSX" for SSX)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 sx3 qs5 h4 s3)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 sx3 qs5 h4 s3)(*strict*)
  apply(erule disjE)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 sx3 qs5 h4 s3)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
    prefer 2
    apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and x = "0"
      and y = "0"
      and n = "i"
      and m = "i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
              apply(force)
             apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
             apply(force)
            apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
            apply (metis DPDA_is_is_forward_deterministicHist_SB)
           apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
           apply(simp add: epdaH.derivation_initial_def)
          apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
     apply(clarsimp)
     apply(simp add: epda_effects_def)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha qx1 sx1 qx2 sx3 qs5 h4 s3 c)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 ha h hb qx1 sx1 qx2 sx3 qs5 h4 s3)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and x = "0"
      and y = "0"
      and n = "i"
      and m = "i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
             apply(force)
            apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
            apply(force)
           apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
          apply(simp add: epdaH.derivation_initial_def)
         apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
    apply(clarsimp)
    apply(simp add: epda_effects_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 n2 q1 q2 s1 s2 e1a e2 i e ea e1 h hb qx1 sx1 qx2 sx3 qs5 s3 c)(*strict*)
  apply(clarsimp)
  done

lemma DFA_one_symbol_per_step: "
  valid_dfa G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> length(epdaH_conf_history c) = n"
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
      G = "G"
      and d = "d"
      and n = "n"
      and m = "Suc n"
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
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac c e1 e2 c1 w)(*strict*)
  apply(case_tac e2)
  apply(rename_tac c e1 e2 c1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 c1 w edge_event edge_pop edge_push)(*strict*)
  apply(case_tac edge_event)
   apply(rename_tac c e1 c1 w edge_event edge_pop edge_push)(*strict*)
   prefer 2
   apply(rename_tac c e1 c1 w edge_event edge_pop edge_push a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c e1 c1 w edge_pop edge_push a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac c e1 c1 w edge_event edge_pop edge_push)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 c1 w edge_pop edge_push)(*strict*)
  apply(simp add: option_to_list_def)
  apply(simp add: valid_dfa_def)
  apply(rename_tac c e1 c1 w edge_popa edge_pusha)(*strict*)
  apply(force)
  done

lemma DFA_stack_consists_only_of_box: "
  valid_dfa G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> epdaH_conf_stack c = [epda_box G]"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and d = "d"
      and n = "n"
      and m = "Suc n"
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
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac e2)
  apply(rename_tac n c e1 e2 c1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 c1 w edge_event edge_pop edge_push)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
  apply(rename_tac n c e1 c1 w edge_eventa edge_popa edge_pusha)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x = "\<lparr>edge_src = epdaH_conf_state c1, edge_event = edge_eventa, edge_pop = edge_popa, edge_push = edge_pusha, edge_trg = epdaH_conf_state c\<rparr>"
      in ballE)
   apply(rename_tac n c e1 c1 w edge_eventa edge_popa edge_pusha)(*strict*)
   prefer 2
   apply(rename_tac n c e1 c1 w edge_event edge_pop edge_push)(*strict*)
   apply(force)
  apply(rename_tac n c e1 c1 w edge_eventa edge_popa edge_pusha)(*strict*)
  apply(clarsimp)
  done

definition epda_operational_controllable ::
  "('spec_state, 'event, 'gamma) epda
  \<Rightarrow> ('plant_state, 'event, 'gamma_unused) epda
  \<Rightarrow> 'event set
  \<Rightarrow> bool"
  where
    "epda_operational_controllable S P SigmaUC \<equiv>
  \<forall>d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u.
  epdaH.derivation_initial S d1
  \<longrightarrow> d1 n1 = Some (pair e1 c1)
  \<longrightarrow> epdaH.derivation_initial P d2
  \<longrightarrow> d2 n2 = Some (pair e2 c2)
  \<longrightarrow> d2 (Suc n2) = Some (pair e2' c2')
  \<longrightarrow> epdaH_conf_history c1 = epdaH_conf_history c2
  \<longrightarrow> epdaH_conf_history c2' = epdaH_conf_history c2 @ [u]
  \<longrightarrow> u \<in> SigmaUC
  \<longrightarrow> (\<exists>dc nC eC cC.
        epdaH.derivation S dc
        \<and> dc 0 = Some (pair None c1)
        \<and> dc nC = Some (pair eC cC)
        \<and> epdaH_conf_history cC = epdaH_conf_history c2')"

definition epda_to_des :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event DES"
  where
    "epda_to_des G \<equiv>
  DES (epdaH.unmarked_language G) (epdaH.marked_language G)"

lemma epdaS_epda_sub_preserves_derivation: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> epdaS.derivation G1 d
  \<Longrightarrow> epdaS.derivation G2 d"
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(simp add: epdaS.derivation_def)
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
      in epdaS.step_detail_before_some_position)
     apply(rename_tac i nat a)(*strict*)
     apply(force)
    apply(rename_tac i nat a)(*strict*)
    apply(force)
   apply(rename_tac i nat a)(*strict*)
   apply(force)
  apply(rename_tac i nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS_step_relation_def epda_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(force)
  done

lemma epdaS_epda_sub_preserves_derivation_initial: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> epdaS.derivation_initial G1 d
  \<Longrightarrow> epdaS.derivation_initial G2 d"
  apply(subgoal_tac "epdaS.derivation G2 d")
   prefer 2
   apply(rule epdaS_epda_sub_preserves_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: epdaS.derivation_initial_def)
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
  apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def epda_sub_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma epda_sub_preserves_is_forward_edge_deterministic_accessible: "
  valid_dpda G
  \<Longrightarrow> valid_pda G'
  \<Longrightarrow> epda_sub G' G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G'"
  apply(simp add: valid_dpda_def epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x = "c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x = "c1"
      in allE)
   apply(erule_tac
      x = "c2"
      in allE)
   apply(erule_tac
      x = "e1"
      in allE)
   apply(erule_tac
      x = "e2"
      in allE)
   apply(erule impE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w wa)(*strict*)
   apply(simp add: epda_sub_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(erule_tac
      x = "d"
      in allE)
  apply(case_tac "d i")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
   prefer 2
   apply(erule_tac
      x = "i"
      in allE)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
  apply(rule epdaS_epda_sub_preserves_derivation_initial)
     apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
    apply(simp add: valid_pda_def)
   apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
   apply(simp add: valid_pda_def)
  apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
  apply(force)
  done

lemma epdaS_to_epdaHS_unmarked_language: "
  valid_epda G
  \<Longrightarrow> epdaS.unmarked_language G = epdaHS.unmarked_language G"
  apply(rule order_antisym)
   apply(rule_tac
      t = "epdaS.unmarked_language G"
      and s = "epdaS.finite_unmarked_language G"
      in ssubst)
    apply (metis epdaS_inst_AX_unmarked_language_finite)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule_tac
      ?o1.0 = "x"
      in epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rule_tac
      t = "epdaHS.unmarked_language G"
      and s = "epdaHS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaHS_inst_AX_unmarked_language_finite)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      ?o2.0 = "x"
      in epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_to_epdaHS_unmarked_language: "
  valid_epda G
  \<Longrightarrow> epdaH.unmarked_language G = epdaHS.unmarked_language G"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(force)
  apply(force)
  done

lemma epdaS_to_epdaH_unmarked_language: "
  valid_epda G
  \<Longrightarrow> epdaS.unmarked_language G = epdaH.unmarked_language G"
  apply(rule_tac
      t = "epdaS.unmarked_language G"
      and s = "epdaHS.unmarked_language G"
      in ssubst)
   apply(rule epdaS_to_epdaHS_unmarked_language)
   apply(force)
  apply(rule sym)
  apply(rule epdaH_to_epdaHS_unmarked_language)
  apply(force)
  done

lemma epdaS_to_epdaHS_mlang: "
  valid_epda G
  \<Longrightarrow> epdaS.marked_language G = epdaHS.marked_language G"
  apply(rule order_antisym)
   apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaS.finite_marked_language G"
      in ssubst)
    apply (metis epdaS_inst_lang_finite)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule_tac
      ?o1.0 = "x"
      in epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation1)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rule_tac
      t = "epdaHS.marked_language G"
      and s = "epdaHS.finite_marked_language G"
      in ssubst)
   apply (metis epdaHS_inst_lang_finite)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      ?o2.0 = "x"
      in epdaS_vs_epdaHS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation2)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_to_epdaHS_mlang: "
  valid_epda G
  \<Longrightarrow> epdaH.marked_language G = epdaHS.marked_language G"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(force)
  apply(force)
  done

lemma epdaS_to_epdaH_mlang: "
  valid_epda G
  \<Longrightarrow> epdaS.marked_language G = epdaH.marked_language G"
  apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaHS.marked_language G"
      in ssubst)
   apply(rule epdaS_to_epdaHS_mlang)
   apply(force)
  apply(rule sym)
  apply(rule epdaH_to_epdaHS_mlang)
  apply(force)
  done

lemma epdaS_to_epdaH_nonblockingness_language: "
  valid_epda G
  \<Longrightarrow> (nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)) \<longleftrightarrow> (nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G))"
  apply(rule_tac
      t = "epdaS.unmarked_language G"
      and s = "epdaH.unmarked_language G"
      in ssubst)
   apply(rule epdaS_to_epdaH_unmarked_language)
   apply(force)
  apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaH.marked_language G"
      in ssubst)
   apply(rule epdaS_to_epdaH_mlang)
   apply(force)
  apply(force)
  done

lemma epda_empty_in_epdaH_unmarked_language: "
  valid_epda G
  \<Longrightarrow> [] \<in> epdaH.unmarked_language G"
  apply(simp (no_asm) add: epdaH.unmarked_language_def)
  apply(rule_tac
      x = "der1 \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(simp add: epdaH.derivation_initial_def)
   apply(rule conjI)
    apply(simp add: epdaH.der1_is_derivation)
   apply(simp add: der1_def)
   apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule conjI)
   apply(simp add: epdaH_unmarked_effect_def)
   apply(rule_tac
      x = "0"
      in exI)
   apply(simp add: der1_def)
  apply(simp add: epdaH.der1_is_derivation)
  done

lemma epdaH_unmarked_languageuage_prefix_closed: "
  valid_epda G
  \<Longrightarrow> x@v \<in> epdaH.unmarked_language G
  \<Longrightarrow> x \<in> epdaH.unmarked_language G"
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(clarsimp)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e c)(*strict*)
   prefer 2
   apply(rule_tac
      n = "i"
      and P = "\<lambda>n. n\<le>i \<and> prefix x (epdaH_conf_history (the(get_configuration(d n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c k)(*strict*)
  apply(case_tac k)
   apply(rename_tac d i e c k)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac d i e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e c a)(*strict*)
   apply(case_tac a)
   apply(rename_tac d i e c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c b)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rule_tac
      x = "0"
      in exI)
   apply(clarsimp)
  apply(rename_tac d i e c k nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e c nat)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d"
      and n = "nat"
      and m = "i"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d i e c nat)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac d i e c nat)(*strict*)
    apply(force)
   apply(rename_tac d i e c nat)(*strict*)
   apply(force)
  apply(rename_tac d i e c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def prefix_def)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 c1 c2 ca)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d i e c nat e1 e2 c1 c2 ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 c1 ca epdaH_conf_state epdaH_conf_stack)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(rename_tac d i e c nat e1 e2 c1 ca epdaH_conf_statea epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 s2)
  apply(rename_tac d i e c nat e1 e2 c1 ca q2 s2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d i e c nat e1 e2 c1 ca q2 s2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac d i e c nat e1 e2 c1 ca q2 s2 q1 h1 s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 ca h1 w)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d i e c nat e1 e2 ca h1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 ca h1 w edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d i e c nat e1 ca h1 w qs re po pu qt)(*strict*)
  apply(case_tac re)
   apply(rename_tac d i e c nat e1 ca h1 w qs re po pu qt)(*strict*)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac d i e c nat e1 ca w qs po pu qt)(*strict*)
   apply(rule_tac
      x = "nat"
      in exI)
   apply(clarsimp)
   apply(erule_tac
      x = "nat"
      in allE)
   apply(force)
  apply(rename_tac d i e c nat e1 ca h1 w qs re po pu qt a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      xs = "ca"
      in rev_cases)
   apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a)(*strict*)
   prefer 2
   apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c nat e1 w qs po pu qt a ys)(*strict*)
   apply(force)
  apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 h1 w qs po pu qt a)(*strict*)
  apply(rule_tac
      x = "Suc nat"
      in exI)
  apply(clarsimp)
  done

lemma epdaH_coincide_strict_prefix: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> get_configuration (d1 i1) = Some c1
  \<Longrightarrow> get_configuration (d2 i2) = Some c2
  \<Longrightarrow> strict_prefix (epdaH_conf_history c1) (epdaH_conf_history c2)
  \<Longrightarrow> i1 \<le> i2 \<and> (\<forall>i. i\<le>i1 \<longrightarrow> d1 i = d2 i)"
  apply(case_tac "d1 0")
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac option b)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b optiona ba)(*strict*)
   prefer 2
   apply(rename_tac option b optiona ba a)(*strict*)
   apply(simp add: epdaH.derivation_def epdaH.derivation_initial_def)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac option b optiona ba)(*strict*)
   prefer 2
   apply(rename_tac option b optiona ba a)(*strict*)
   apply(simp add: epdaH.derivation_def epdaH.derivation_initial_def)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac b ba)(*strict*)
  apply(subgoal_tac "b = ba \<and> b \<in> epdaH_initial_configurations G")
   apply(rename_tac b ba)(*strict*)
   prefer 2
   apply(simp add: epdaH_initial_configurations_def epdaH.derivation_initial_def)
  apply(rename_tac b ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ba)(*strict*)
  apply(case_tac "d1 i1 ")
   apply(rename_tac ba)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac ba a)(*strict*)
  apply(case_tac "d2 i2 ")
   apply(rename_tac ba a)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac ba a aa)(*strict*)
  apply(case_tac a)
  apply(rename_tac ba a aa option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac ba a aa option b optiona bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ba option b optiona bb)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac ba option optiona)(*strict*)
  apply(rename_tac c0 e1 e2)
  apply(rename_tac c0 e1 e2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac c0 e1 e2)(*strict*)
   apply(case_tac "i2 < i1")
    apply(rename_tac c0 e1 e2)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac c0 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c0 e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      g = "d1"
      and n = "i2"
      and m = "i1"
      in epdaH.pre_some_position_is_some_position)
       apply(rename_tac c0 e1 e2)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac c0 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c0 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c0 e1 e2 e c)(*strict*)
    apply(case_tac c1)
    apply(rename_tac c0 e1 e2 e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
    apply(case_tac c2)
    apply(rename_tac c0 e1 e2 e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
    apply(rename_tac c0 e1 e2 e c epdaH_conf_state epdaH_conf_history epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(rename_tac qx1 hx1 sx1 qx2 hx2 sx2)
    apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and x = "0"
      and y = "0"
      and n = "i2"
      and m = "i2"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
               apply(force)
              apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
              apply(force)
             apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
            apply(force)
           apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
           apply(force)
          apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
          apply(force)
         apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
         apply(force)
        apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
        apply(force)
       apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
       apply(force)
      apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
      apply(simp add: strict_prefix_def)
      apply(clarsimp)
      apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
      apply(subgoal_tac "X" for X)
       apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
       prefer 2
       apply(rule_tac
      d = "d1"
      and G = "G"
      and n = "i2"
      and m = "i1-i2"
      in epdaH.steps_extend_history_derivation)
           apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
           apply(simp add: valid_dpda_def valid_pda_def)
          apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
          apply(simp add: epdaH.derivation_initial_def)
         apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
         prefer 2
         apply(clarsimp)
         apply(simp add: get_configuration_def)
        apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
        apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
         apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
         apply(rule epdaH.derivation_initial_belongs)
          apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
          apply(simp add: valid_dpda_def valid_pda_def)
         apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
         apply(force)
        apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
        apply(force)
       apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 sx2 ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
      apply(simp add: epda_effects_def)
      apply(subgoal_tac "\<lparr>epdaH_conf_state = qx2, epdaH_conf_history = epdaH_conf_history c @ h @ ca, epdaH_conf_stack = sx2\<rparr> \<in> epdaH_configurations G")
       apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
       apply(simp add: epdaH_configurations_def)
      apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
      apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
       apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
       apply(force)
      apply(rename_tac c0 e1 e2 e c qx1 sx1 qx2 sx2 ca h)(*strict*)
      apply(force)
     apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac c0 e1 e2 e c qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
     prefer 2
     apply(rule_tac
      d = "d1"
      and G = "G"
      and n = "i2"
      and m = "i1-i2"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
       prefer 2
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
      apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
       apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
       apply(force)
      apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
      apply(force)
     apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac c0 e1 e2 qx1 hx1 sx1 qx2 hx2 sx2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c0 e1 e2 qx1 sx1 qx2 hx2 sx2 h)(*strict*)
    apply(simp add: strict_prefix_def)
   apply(rename_tac c0 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c0 e1 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac c0 e1 e2 i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c0 e1 e2 i)(*strict*)
   prefer 2
   apply(rule_tac
      g = "d1"
      and n = "i"
      and m = "i1"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac c0 e1 e2 i)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac c0 e1 e2 i)(*strict*)
    apply(force)
   apply(rename_tac c0 e1 e2 i)(*strict*)
   apply(force)
  apply(rename_tac c0 e1 e2 i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c0 e1 e2 i)(*strict*)
   prefer 2
   apply(rule_tac
      g = "d2"
      and n = "i"
      and m = "i2"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac c0 e1 e2 i)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac c0 e1 e2 i)(*strict*)
    apply(force)
   apply(rename_tac c0 e1 e2 i)(*strict*)
   apply(force)
  apply(rename_tac c0 e1 e2 i)(*strict*)
  apply(clarsimp)
  apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d1"
      and G = "G"
      and n = "i"
      and m = "i1-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c0 e1 e2 i e ea c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d2"
      and G = "G"
      and n = "i"
      and m = "i2-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac c0 e1 e2 i e ea c ca h cb)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
    apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
     apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
    apply(force)
   apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c0 e1 e2 i e ea c ca h)(*strict*)
  apply(clarsimp)
  apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
  apply(subgoal_tac "prefix (epdaH_conf_history c) (epdaH_conf_history ca) \<or> SSX" for SSX)
   apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
  apply(erule disjE)
   apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
    prefer 2
    apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and x = "0"
      and y = "0"
      and n = "i"
      and m = "i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
              apply(force)
             apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
             apply(force)
            apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
            apply (metis DPDA_is_is_forward_deterministicHist_SB)
           apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
           apply(force)
          apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
          apply(force)
         apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
         apply(force)
        apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
        apply(force)
       apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
       apply(force)
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
      apply(force)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
     apply(rule_tac
      x = "cc"
      in bexI)
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
      apply(clarsimp)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(subgoal_tac "ca \<in> epdaH_configurations G")
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
      apply(simp add: epdaH_configurations_def)
      apply(clarsimp)
      apply(rename_tac c0 e1 e2 i e ea c h ha cb cc q s)(*strict*)
      apply(simp add: epda_effects_def)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
      apply(force)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and x = "0"
      and y = "0"
      and n = "i"
      and m = "i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
             apply(force)
            apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
            apply(force)
           apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
          apply(force)
         apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
         apply(force)
        apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
        apply(force)
       apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
       apply(force)
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
      apply(force)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
    apply(rule_tac
      x = "cc"
      in bexI)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(clarsimp)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
    apply(subgoal_tac "c \<in> epdaH_configurations G")
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(simp add: epdaH_configurations_def)
     apply(clarsimp)
     apply(rename_tac c0 e1 e2 i e ea ca h cb cc q s)(*strict*)
     apply(simp add: epda_effects_def)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
     apply(force)
    apply(rename_tac c0 e1 e2 i e ea c ca h ha cb cc)(*strict*)
    apply(force)
   apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c0 e1 e2 i e ea c ca h ha cb)(*strict*)
  apply(clarsimp)
  done

lemma epdaH_first_time_shorter_than_some_time: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> get_configuration (d1 n1) = Some c1
  \<Longrightarrow> get_configuration (d2 n2) = Some c2
  \<Longrightarrow> epdaH_conf_history c1 = epdaH_conf_history c2
  \<Longrightarrow> (\<forall>k<n1. epdaH_conf_history (the(get_configuration(d1 k))) \<noteq> epdaH_conf_history c1)
  \<Longrightarrow> n1\<le>n2"
  apply(subgoal_tac "\<exists>c. c \<in> epdaH_initial_configurations G \<and> d1 0 = Some (pair None c) \<and> d2 0 = Some (pair None c)")
   prefer 2
   apply(case_tac "d1 0")
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(rename_tac a)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(rename_tac a aa)(*strict*)
   apply(case_tac a)
   apply(rename_tac a aa option b)(*strict*)
   apply(case_tac aa)
   apply(rename_tac a aa option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b optiona ba)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(clarsimp)
   apply(rename_tac b ba)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac "d1 n1")
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c a)(*strict*)
  apply(case_tac "d2 n2")
   apply(rename_tac c a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c a aa)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c a aa option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac c a aa option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac c option optiona)(*strict*)
  apply(rename_tac e1 e2)
  apply(rename_tac c e1 e2)(*strict*)
  apply(case_tac "n2<n1")
   apply(rename_tac c e1 e2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c e1 e2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and x = "0"
      and y = "0"
      and n = "n2"
      and m = "n1"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac c e1 e2)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac c e1 e2)(*strict*)
             apply(force)
            apply(rename_tac c e1 e2)(*strict*)
            apply(force)
           apply(rename_tac c e1 e2)(*strict*)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac c e1 e2)(*strict*)
          apply(simp add: epdaH.derivation_initial_def)
         apply(rename_tac c e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2)(*strict*)
    apply(clarsimp)
    apply(simp add: epda_effects_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac c e1 e2)(*strict*)
   apply(simp)
  apply(rename_tac c e1 e2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d1"
      and n = "n2"
      and m = "n1"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac c e1 e2)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac c e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c e1 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e1a e2a c2a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e1a e2a c2a)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and d = "d1"
      and n = "Suc n2"
      and m = "n1-Suc n2"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac c e1 e1a e2a c2a)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c e1 e1a e2a c2a)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac c e1 e1a e2a c2a)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac c e1 e1a e2a c2a)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac c e1 e1a e2a c2a)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c e1 e1a e2a c2a)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c e1 e1a e2a c2a)(*strict*)
     apply(force)
    apply(rename_tac c e1 e1a e2a c2a)(*strict*)
    apply(force)
   apply(rename_tac c e1 e1a e2a c2a)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c e1 e1a e2a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e1a e2a c2a h)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c e1 e1a e2a c2a w)(*strict*)
  apply(case_tac "e2a")
  apply(rename_tac c e1 e1a e2a c2a w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac c e1 e1a e2a c2a w qs re po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e1a c2a w re po pu)(*strict*)
  apply(case_tac re)
   apply(rename_tac c e1 e1a c2a w re po pu)(*strict*)
   prefer 2
   apply(rename_tac c e1 e1a c2a w re po pu a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac c e1 e1a c2a w re po pu)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac c e1 e1a c2a w po pu)(*strict*)
  apply(erule_tac
      x = "n2"
      in allE)
  apply(erule impE)
   apply(rename_tac c e1 e1a c2a w po pu)(*strict*)
   apply(force)
  apply(rename_tac c e1 e1a c2a w po pu)(*strict*)
  apply(force)
  done

lemma epdaH_coincide_on_stable_configurations: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> get_configuration (d1 n1) = Some c1
  \<Longrightarrow> get_configuration (d2 n2) = Some c2
  \<Longrightarrow> (\<forall>e\<in> epda_delta G. edge_event e = None \<longrightarrow> (\<forall>c'. \<not>epdaH_step_relation G c1 e c'))
  \<Longrightarrow> (\<forall>e\<in> epda_delta G. edge_event e = None \<longrightarrow> (\<forall>c'. \<not>epdaH_step_relation G c2 e c'))
  \<Longrightarrow> epdaH_conf_history c1 = epdaH_conf_history c2
  \<Longrightarrow> n1 = n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  apply(subgoal_tac "\<exists>c. c \<in> epdaH_initial_configurations G \<and> d1 0 = Some (pair None c) \<and> d2 0 = Some (pair None c)")
   prefer 2
   apply(case_tac "d1 0")
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(rename_tac a)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(rename_tac a aa)(*strict*)
   apply(case_tac a)
   apply(rename_tac a aa option conf)(*strict*)
   apply(case_tac aa)
   apply(rename_tac a aa option conf optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac option conf optiona confa)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(clarsimp)
   apply(rename_tac conf confa)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac "d1 n1")
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c a)(*strict*)
  apply(case_tac "d2 n2")
   apply(rename_tac c a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c a aa)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c a aa option conf)(*strict*)
  apply(case_tac aa)
  apply(rename_tac c a aa option conf optiona confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c option optiona)(*strict*)
  apply(rename_tac e1 e2)
  apply(rename_tac c e1 e2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac c e1 e2)(*strict*)
   apply(case_tac "n1<n2")
    apply(rename_tac c e1 e2)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and x = "0"
      and y = "0"
      and n = "n1"
      and m = "n2"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac c e1 e2)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac c e1 e2)(*strict*)
               apply(force)
              apply(rename_tac c e1 e2)(*strict*)
              apply(force)
             apply(rename_tac c e1 e2)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac c e1 e2)(*strict*)
            apply(simp add: epdaH.derivation_initial_def)
           apply(rename_tac c e1 e2)(*strict*)
           apply(force)
          apply(rename_tac c e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c e1 e2)(*strict*)
      apply(clarsimp)
      apply(simp add: epda_effects_def)
      apply(simp add: get_configuration_def)
     apply(rename_tac c e1 e2)(*strict*)
     apply(simp)
    apply(rename_tac c e1 e2)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      d = "d2"
      and n = "n1"
      and m = "n2"
      in epdaH.step_detail_before_some_position)
       apply(rename_tac c e1 e2)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac c e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c e2 e1a e2a c2a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c e2 e1a e2a c2a)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and d = "d2"
      and n = "Suc n1"
      and m = "n2-Suc n1"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac c e2 e1a e2a c2a)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac c e2 e1a e2a c2a)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac c e2 e1a e2a c2a)(*strict*)
       prefer 2
       apply(simp add: get_configuration_def)
      apply(rename_tac c e2 e1a e2a c2a)(*strict*)
      apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
       apply(rename_tac c e2 e1a e2a c2a)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac c e2 e1a e2a c2a)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac c e2 e1a e2a c2a)(*strict*)
       apply(force)
      apply(rename_tac c e2 e1a e2a c2a)(*strict*)
      apply(force)
     apply(rename_tac c e2 e1a e2a c2a)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac c e2 e1a e2a c2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac c e2 e1a e2a c2a h)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac c e2 e1a e2a c2a w)(*strict*)
    apply(case_tac "e2a")
    apply(rename_tac c e2 e1a e2a c2a w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(rename_tac qs re po pu qt)
    apply(rename_tac c e2 e1a e2a c2a w qs re po pu qt)(*strict*)
    apply(clarsimp)
    apply(rename_tac c e2 e1a c2a w re po pu)(*strict*)
    apply(case_tac re)
     apply(rename_tac c e2 e1a c2a w re po pu)(*strict*)
     prefer 2
     apply(rename_tac c e2 e1a c2a w re po pu a)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac c e2 e1a c2a w re po pu)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac c e2 e1a c2a w po pu)(*strict*)
    apply(erule_tac
      x = "\<lparr>edge_src = epdaH_conf_state c1, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state c2a\<rparr>"
      and P = "\<lambda>e. edge_event e = None \<longrightarrow> (\<forall>c'. epdaH_conf_history c' = epdaH_conf_history c2a \<longrightarrow> epdaH_conf_state c' = edge_trg e \<longrightarrow> epdaH_conf_state c1 = edge_src e \<longrightarrow> (\<forall>wa. po @ w = edge_pop e @ wa \<longrightarrow> epdaH_conf_stack c' \<noteq> edge_push e @ wa))"
      in ballE)
     apply(rename_tac c e2 e1a c2a w po pu)(*strict*)
     apply(clarsimp)
    apply(rename_tac c e2 e1a c2a w po pu)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2)(*strict*)
   apply(case_tac "n2<n1")
    apply(rename_tac c e1 e2)(*strict*)
    apply(thin_tac "\<not> n1 < n2")
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and x = "0"
      and y = "0"
      and n = "n2"
      and m = "n1"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac c e1 e2)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac c e1 e2)(*strict*)
               apply(force)
              apply(rename_tac c e1 e2)(*strict*)
              apply(force)
             apply(rename_tac c e1 e2)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac c e1 e2)(*strict*)
            apply(simp add: epdaH.derivation_initial_def)
           apply(rename_tac c e1 e2)(*strict*)
           apply(force)
          apply(rename_tac c e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c e1 e2)(*strict*)
      apply(clarsimp)
      apply(simp add: epda_effects_def)
      apply(simp add: get_configuration_def)
     apply(rename_tac c e1 e2)(*strict*)
     apply(simp)
    apply(rename_tac c e1 e2)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c e1 e2)(*strict*)
     prefer 2
     apply(rule_tac
      d = "d1"
      and n = "n2"
      and m = "n1"
      in epdaH.step_detail_before_some_position)
       apply(rename_tac c e1 e2)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac c e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c e1 e1a e2a c2a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c e1 e1a e2a c2a)(*strict*)
     prefer 2
     apply(rule_tac
      G = "G"
      and d = "d1"
      and n = "Suc n2"
      and m = "n1-Suc n2"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac c e1 e1a e2a c2a)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac c e1 e1a e2a c2a)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
       apply(rename_tac c e1 e1a e2a c2a)(*strict*)
       prefer 2
       apply(simp add: get_configuration_def)
      apply(rename_tac c e1 e1a e2a c2a)(*strict*)
      apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
       apply(rename_tac c e1 e1a e2a c2a)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac c e1 e1a e2a c2a)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac c e1 e1a e2a c2a)(*strict*)
       apply(force)
      apply(rename_tac c e1 e1a e2a c2a)(*strict*)
      apply(force)
     apply(rename_tac c e1 e1a e2a c2a)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac c e1 e1a e2a c2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac c e1 e1a e2a c2a h)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac c e1 e1a e2a c2a w)(*strict*)
    apply(case_tac "e2a")
    apply(rename_tac c e1 e1a e2a c2a w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(rename_tac qs re po pu qt)
    apply(rename_tac c e1 e1a e2a c2a w qs re po pu qt)(*strict*)
    apply(clarsimp)
    apply(rename_tac c e1 e1a c2a w re po pu)(*strict*)
    apply(case_tac re)
     apply(rename_tac c e1 e1a c2a w re po pu)(*strict*)
     prefer 2
     apply(rename_tac c e1 e1a c2a w re po pu a)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac c e1 e1a c2a w re po pu)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac c e1 e1a c2a w po pu)(*strict*)
    apply(erule_tac
      x = "\<lparr>edge_src = epdaH_conf_state c2, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = epdaH_conf_state c2a\<rparr>"
      and P = "\<lambda>x. edge_event x = None \<longrightarrow> (\<forall>c'. epdaH_conf_history c' = epdaH_conf_history c2a \<longrightarrow> epdaH_conf_state c' = edge_trg x \<longrightarrow> epdaH_conf_state c2 = edge_src x \<longrightarrow> (\<forall>wa. po @ w = edge_pop x @ wa \<longrightarrow> epdaH_conf_stack c' \<noteq> edge_push x @ wa))"
      in ballE)
     apply(rename_tac c e1 e1a c2a w po pu)(*strict*)
     apply(clarsimp)
    apply(rename_tac c e1 e1a c2a w po pu)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c e1 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e2 i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2 i)(*strict*)
   prefer 2
   apply(rule_tac
      g = "d1"
      and n = "i"
      and m = "n2"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac c e1 e2 i)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac c e1 e2 i)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2 i)(*strict*)
   apply(force)
  apply(rename_tac c e1 e2 i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2 i)(*strict*)
   prefer 2
   apply(rule_tac
      g = "d2"
      and n = "i"
      and m = "n2"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac c e1 e2 i)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac c e1 e2 i)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2 i)(*strict*)
   apply(force)
  apply(rename_tac c e1 e2 i)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d1"
      and G = "G"
      and n = "i"
      and m = "n2-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c e1 e2 i e ea ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
   prefer 2
   apply(rule_tac
      d = "d2"
      and G = "G"
      and n = "i"
      and m = "n2-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
    apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
     apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c e1 e2 i e ea ca cb h)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
  apply(subgoal_tac "prefix (epdaH_conf_history ca) (epdaH_conf_history cb) \<or> SSX" for SSX)
   apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
  apply(erule disjE)
   apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
    prefer 2
    apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d2"
      and x = "0"
      and y = "0"
      and n = "i"
      and m = "i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
              apply(force)
             apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
             apply(force)
            apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
            apply (metis DPDA_is_is_forward_deterministicHist_SB)
           apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
           apply(force)
          apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
          apply(force)
         apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
         apply(force)
        apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
        apply(force)
       apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
       apply(force)
      apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
      apply(force)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
     apply(rule_tac
      x = "cc"
      in bexI)
      apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
      apply(clarsimp)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(subgoal_tac "cb \<in> epdaH_configurations G")
      apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
      apply(simp add: epdaH_configurations_def)
      apply(clarsimp)
      apply(rename_tac c e1 e2 i e ea ca ha cc q s)(*strict*)
      apply(simp add: epda_effects_def)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(rule_tac
      d = "d2"
      in epdaH.belongs_configurations)
      apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
      apply(force)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and ?d1.0 = "d2"
      and ?d2.0 = "d1"
      and x = "0"
      and y = "0"
      and n = "i"
      and m = "i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
             apply(force)
            apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
            apply(force)
           apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
          apply(force)
         apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
         apply(force)
        apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
        apply(force)
       apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
       apply(force)
      apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
      apply(force)
     apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
    apply(rule_tac
      x = "cc"
      in bexI)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(clarsimp)
    apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
    apply(subgoal_tac "ca \<in> epdaH_configurations G")
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(simp add: epdaH_configurations_def)
     apply(clarsimp)
     apply(rename_tac c e1 e2 i e ea cb h cc q s)(*strict*)
     apply(simp add: epda_effects_def)
    apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
     apply(force)
    apply(rename_tac c e1 e2 i e ea ca cb h ha cc)(*strict*)
    apply(force)
   apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c e1 e2 i e ea ca cb h ha)(*strict*)
  apply(clarsimp)
  done

lemma DPDA_conflicting_edges: "
  valid_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> epdaH_step_relation G c e1 c1
  \<Longrightarrow> epdaH_step_relation G c e2 c2
  \<Longrightarrow> edge_event e1 = None
  \<Longrightarrow> edge_event e2 \<noteq> None
  \<Longrightarrow> Q"
  apply(subgoal_tac " epdaH.is_forward_deterministicHist_SB G")
   prefer 2
   apply (metis DPDA_is_is_forward_deterministicHist_SB)
  apply(simp add: epdaH.is_forward_edge_deterministicHist_SB_long_def epdaH.is_forward_deterministicHist_SB_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(erule_tac
      x = "c"
      in ballE)
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(simp add: epdaH.get_accessible_configurations_def)
   apply(erule_tac
      x = "d"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x = "n"
      in allE)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac y)(*strict*)
  apply(erule_tac
      x = "c1"
      in allE)
  apply(erule_tac
      x = "c2"
      in allE)
  apply(erule_tac
      x = "e1"
      in allE)
  apply(erule_tac
      x = "e2"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      x = "[]"
      in exI)
  apply(rule conjI)
   apply(rename_tac y)(*strict*)
   apply(simp add: epdaH_step_relation_def option_to_list_def epda_effects_def)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      x = "[y]"
      in exI)
  apply(rule conjI)
   apply(rename_tac y)(*strict*)
   apply(simp add: epdaH_step_relation_def option_to_list_def epda_effects_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac y w)(*strict*)
   apply(erule_tac
      x = "e2"
      in ballE)
    apply(rename_tac y w)(*strict*)
    apply(simp add: valid_epda_step_label_def may_terminated_by_def option_to_set_def)
   apply(rename_tac y w)(*strict*)
   apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(simp add: epdaH_step_relation_def option_to_list_def)
  apply(rule_tac
      t = "ATS_History.history_fragment_prefixes epda_effects (@) G [y] = ATS_History.history_fragment_prefixes epda_effects (@) G []"
      and s = "ATS_History.history_fragment_prefixes epda_effects (@) G [] \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G [y] \<and> ATS_History.history_fragment_prefixes epda_effects (@) G [y] \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G []"
      in ssubst)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      t = "ATS_History.history_fragment_prefixes epda_effects (@) G [] \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G [y]"
      in subst)
   apply(rename_tac y)(*strict*)
   apply(rule I_epda_HS_H.prefix_to_history_fragment_prefixes)
    apply(rename_tac y)(*strict*)
    apply(simp add: epda_effects_def)
   apply(rename_tac y)(*strict*)
   apply(simp add: epda_effects_def)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def valid_epda_step_label_def)
   apply(clarsimp)
   apply(rename_tac y w)(*strict*)
   apply(erule_tac
      x = "e2"
      and P = "\<lambda>e2. edge_src e2 \<in> epda_states G \<and> edge_trg e2 \<in> epda_states G \<and> option_to_set (edge_event e2) \<subseteq> epda_events G \<and> edge_pop e2 \<in> may_terminated_by (epda_gamma G) (epda_box G) \<and> edge_push e2 \<in> may_terminated_by (epda_gamma G) (epda_box G) \<and> (edge_pop e2 \<in> must_terminated_by (epda_gamma G) (epda_box G)) = (edge_push e2 \<in> must_terminated_by (epda_gamma G) (epda_box G))"
      in ballE)
    apply(rename_tac y w)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_set_def)
   apply(rename_tac y w)(*strict*)
   apply(simp add: epdaH_step_relation_def option_to_list_def)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      t = "ATS_History.history_fragment_prefixes epda_effects (@) G [y] \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) G []"
      in subst)
   apply(rename_tac y)(*strict*)
   apply(rule I_epda_HS_H.prefix_to_history_fragment_prefixes)
    apply(rename_tac y)(*strict*)
    apply(simp add: epda_effects_def)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def valid_epda_step_label_def)
    apply(clarsimp)
    apply(rename_tac y w)(*strict*)
    apply(erule_tac
      x = "e2"
      and P = "\<lambda>e2. edge_src e2 \<in> epda_states G \<and> edge_trg e2 \<in> epda_states G \<and> option_to_set (edge_event e2) \<subseteq> epda_events G \<and> edge_pop e2 \<in> may_terminated_by (epda_gamma G) (epda_box G) \<and> edge_push e2 \<in> may_terminated_by (epda_gamma G) (epda_box G) \<and> (edge_pop e2 \<in> must_terminated_by (epda_gamma G) (epda_box G)) = (edge_push e2 \<in> must_terminated_by (epda_gamma G) (epda_box G))"
      in ballE)
     apply(rename_tac y w)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_set_def)
    apply(rename_tac y w)(*strict*)
    apply(simp add: epdaH_step_relation_def option_to_list_def)
   apply(rename_tac y)(*strict*)
   apply(simp add: epda_effects_def)
  apply(rename_tac y)(*strict*)
  apply(simp add: prefix_def)
  done

theorem epda_Cont_to_epda_operational_controllable: "
  valid_dpda G
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> controllable_sublanguage (epdaH.unmarked_language G) (alphabet_to_language SigmaUC) (epdaH.unmarked_language P) (epdaH.unmarked_language G)
  \<Longrightarrow> epda_operational_controllable G P SigmaUC"
  apply(simp add: epda_operational_controllable_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(case_tac c2')
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
  apply(rename_tac q1 h1 s1 q2 h2 s2 q2' h2' s2')
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u q1 h1 s1 q2 h2 s2 q2' h2' s2')(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
  apply(simp add: controllable_sublanguage_def)
  apply(erule_tac
      x = "h2"
      in ballE)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
   prefer 2
   apply(subgoal_tac "h2 \<in> epdaH.unmarked_language G")
    apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
   apply(thin_tac "h2 \<notin> epdaH.unmarked_language G")
   apply(simp add: epdaH.unmarked_language_def)
   apply(rule_tac
      x = "d1"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_unmarked_effect_def)
   apply(rule_tac
      x = "n1"
      in exI)
   apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
  apply(simp add: controllable_word_def)
  apply(erule_tac
      x = "[u]"
      in ballE)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
   prefer 2
   apply(simp add: alphabet_to_language_def)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
   apply(simp add: epdaH.unmarked_language_def)
   apply(rule_tac
      x = "d2"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_unmarked_effect_def)
   apply(rule_tac
      x = "Suc n2"
      in exI)
   apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2')(*strict*)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2' d)(*strict*)
  apply(thin_tac "epdaH.derivation_initial P d2")
  apply(thin_tac "d2 n2 = Some (pair e2 \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h2, epdaH_conf_stack = s2\<rparr>)")
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2' d)(*strict*)
  apply(thin_tac "d2 (Suc n2) = Some (pair e2' \<lparr>epdaH_conf_state = q2', epdaH_conf_history = h2 @ [u], epdaH_conf_stack = s2'\<rparr>)")
  apply(rename_tac d1 n1 e1 d2 n2 e2 e2' u q1 s1 q2 h2 s2 q2' s2' d)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e c q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
   prefer 2
   apply(rule_tac
      G = "G"
      and ?d1.0 = "d1"
      and ?d2.0 = "d"
      and ?i1.0 = "n1"
      and ?i2.0 = "i"
      in epdaH_coincide_strict_prefix)
        apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
   apply(simp add: strict_prefix_def)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x = "n1"
      in allE)
  apply(clarsimp)
  apply(case_tac "i = n1")
   apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
   prefer 2
   apply(rule_tac
      x = "derivation_drop d n1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
    apply(rule_tac
      m = "i-n1"
      in epdaH.derivation_drop_preserves_derivation_prime)
     apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
   apply(rule conjI)
    apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
   apply(rule_tac
      x = "i-n1"
      in exI)
   apply(simp add: derivation_drop_def)
  apply(rename_tac d1 n1 e1 u q1 s1 h2 d i e q s)(*strict*)
  apply(clarsimp)
  done

theorem epda_epda_operational_controllable_to_Cont: "
  valid_dpda G
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> epda_operational_controllable G P SigmaUC
  \<Longrightarrow> controllable_sublanguage (epdaH.unmarked_language G) (alphabet_to_language SigmaUC) (epdaH.unmarked_language P) (epdaH.unmarked_language G)"
  apply(simp add: controllable_sublanguage_def controllable_word_def)
  apply(clarsimp)
  apply(rename_tac w' u)(*strict*)
  apply(simp add: alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac w' v)(*strict*)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac w' v d da)(*strict*)
  apply(thin_tac "epdaH.derivation G d")
  apply(thin_tac "epdaH.derivation P da")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac v d da i ia e ea c ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac v d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac ca)
  apply(rename_tac v d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1 q2 h2 s2)
  apply(rename_tac v d da i ia e ea c ca q1 h1 s1 q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac v d da i ia e ea q1 h1 s1 q2 s2)(*strict*)
  apply(case_tac ia)
   apply(rename_tac v d da i ia e ea q1 h1 s1 q2 s2)(*strict*)
   apply(clarsimp)
   apply(rename_tac v d da i e ea q1 h1 s1 q2 s2)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac v d da i e q1 h1 s1 q2 s2)(*strict*)
   apply(case_tac "da 0")
    apply(rename_tac v d da i e q1 h1 s1 q2 s2)(*strict*)
    apply(clarsimp)
   apply(rename_tac v d da i e q1 h1 s1 q2 s2 a)(*strict*)
   apply(clarsimp)
   apply(rename_tac v d da i e q1 h1 s1 q2 s2)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
  apply(rename_tac v d da i ia e ea q1 h1 s1 q2 s2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 nat)(*strict*)
  apply(rename_tac ia)
  apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 ia)(*strict*)
  apply(simp add: epda_operational_controllable_def)
  apply(erule_tac
      x = "d"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x = "i"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x = "da"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x = "ia"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 ia)(*strict*)
   prefer 2
   apply(rule_tac
      n = "ia"
      and m = "Suc ia"
      and G = "P"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 ia)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 ia)(*strict*)
    apply(force)
   apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 ia)(*strict*)
   apply(force)
  apply(rename_tac v d da i e ea q1 h1 s1 q2 s2 ia)(*strict*)
  apply(clarsimp)
  apply(rename_tac v d da i e q1 h1 s1 q2 s2 ia e1 e2 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac v d da i e q1 h1 s1 q2 s2 ia e1 e2 c1 epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q3 h3 s3)
  apply(rename_tac v d da i e q1 h1 s1 q2 s2 ia e1 e2 c1 q3 h3 s3)(*strict*)
  apply(clarsimp)
  apply(rename_tac v d da i e q1 h1 s1 q2 s2 ia e1 e2 q3 h3 s3)(*strict*)
  apply(subgoal_tac "h1 = h3")
   apply(rename_tac v d da i e q1 h1 s1 q2 s2 ia e1 e2 q3 h3 s3)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac v d da i e q1 h1 s1 ia e1 e2 h3 w)(*strict*)
   apply(case_tac "e2")
   apply(rename_tac v d da i e q1 h1 s1 ia e1 e2 h3 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(rename_tac qs re po pu qt)
   apply(rename_tac v d da i e q1 h1 s1 ia e1 e2 h3 w qs re po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac v d da i e q1 h1 s1 ia e1 h3 w qs re po pu qt)(*strict*)
   apply(case_tac re)
    apply(rename_tac v d da i e q1 h1 s1 ia e1 h3 w qs re po pu qt)(*strict*)
    apply(simp add: valid_dfa_def)
    apply(force)
   apply(rename_tac v d da i e q1 h1 s1 ia e1 h3 w qs re po pu qt a)(*strict*)
   apply(clarsimp)
   apply(rename_tac v d da i e q1 h1 s1 ia e1 h3 w qs po pu qt a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac v d da i e q1 h1 s1 q2 s2 ia e1 e2 q3 h3 s3)(*strict*)
  apply(clarsimp)
  apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC)(*strict*)
  apply(case_tac nC)
   apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC)(*strict*)
   apply(clarsimp)
  apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
  apply(rule_tac
      x = "derivation_append d dc i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
    apply(force)
   apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
    apply(force)
   apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
   apply(force)
  apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
  apply(rule conjI)
   apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
   apply(rule_tac
      x = "i+nC"
      in exI)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac v d da i e q1 s1 q2 s2 ia e1 e2 q3 h3 s3 dc nC eC cC nat)(*strict*)
  apply(rule epdaH.derivation_initial_is_derivation)
  apply(force)
  done

theorem epda_epda_operational_controllable_vs_Cont: "
  valid_dpda G
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> epda_operational_controllable G P SigmaUC \<longleftrightarrow> controllable_sublanguage (epdaH.unmarked_language G) (alphabet_to_language SigmaUC) (epdaH.unmarked_language P) (epdaH.unmarked_language G)"
  apply (metis epda_Cont_to_epda_operational_controllable epda_epda_operational_controllable_to_Cont)
  done

theorem epda_Cont_eq_to_epda_operational_controllable_eq: "
  valid_dpda G
  \<Longrightarrow> valid_dpda G'
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> controllable_sublanguage (epdaH.unmarked_language G) (alphabet_to_language SigmaUC) (epdaH.unmarked_language P) (epdaH.unmarked_language G) \<longleftrightarrow>
  controllable_sublanguage (epdaH.unmarked_language G') (alphabet_to_language SigmaUC) (epdaH.unmarked_language P) (epdaH.unmarked_language G')
  \<Longrightarrow> epda_operational_controllable G P SigmaUC \<longleftrightarrow> epda_operational_controllable G' P SigmaUC"
  apply(metis epda_Cont_to_epda_operational_controllable epda_epda_operational_controllable_to_Cont)
  done

theorem epda_Cont_eq_to_epda_operational_controllable_eq2: "
  valid_dpda G
  \<Longrightarrow> valid_dpda G'
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> epdaH.unmarked_language G = epdaH.unmarked_language G'
  \<Longrightarrow> epda_operational_controllable G P SigmaUC \<longleftrightarrow> epda_operational_controllable G' P SigmaUC"
  apply(rule epda_Cont_eq_to_epda_operational_controllable_eq)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epda_marking_states_change_preserves_determinism: "
  valid_dpda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible (G\<lparr>epda_marking:= Q\<rparr>)"
  apply(simp add: valid_dpda_def epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x = "c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x = "c1"
      in allE)
   apply(erule_tac
      x = "c2"
      in allE)
   apply(erule_tac
      x = "e1"
      in allE)
   apply(erule_tac
      x = "e2"
      in allE)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(erule_tac
      x = "d"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(thin_tac "epdaS_step_relation (G\<lparr>epda_marking := Q\<rparr>) c e1 c1")
  apply(thin_tac "epdaS_step_relation (G\<lparr>epda_marking := Q\<rparr>) c e2 c2")
  apply(thin_tac "get_configuration (d i) = Some c")
  apply(simp add: epdaS.derivation_initial_def)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
  apply(rename_tac d a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d b)(*strict*)
  apply(rule conjI)
   apply(rename_tac d b)(*strict*)
   prefer 2
   apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
  apply(rename_tac d b)(*strict*)
  apply(thin_tac "b \<in> epdaS_initial_configurations (G\<lparr>epda_marking := Q\<rparr>)")
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac d b i)(*strict*)
  apply(case_tac i)
   apply(rename_tac d b i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d b i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d b nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac d b nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d b nat a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d b nat a)(*strict*)
   prefer 2
   apply(rule_tac
      n = "nat"
      and m = "Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac d b nat a)(*strict*)
     apply(force)
    apply(rename_tac d b nat a)(*strict*)
    apply(force)
   apply(rename_tac d b nat a)(*strict*)
   apply(force)
  apply(rename_tac d b nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d b nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  done

lemma epdaH_epda_stack_is_must_terminated_by_prime: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> epdaH_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaH_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule epdaH.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac i c e1 e2 c1 w)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w a)(*strict*)
  apply(case_tac w)
   apply(rename_tac i c e1 e2 c1 w a)(*strict*)
   apply(clarsimp)
   apply(rename_tac i c e1 e2 c1 a)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(rename_tac i c e1 e2 c1 w a aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac i c e1 e2 c1 w a aa list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac i c e1 e2 c1 w a aa list)(*strict*)
  apply(thin_tac "w = aa # list")
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w' x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w' x a aa)(*strict*)
  apply(force)
  done

lemma epdaH_epda_stack_is_must_terminated_by: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaH.get_accessible_configurations G
  \<Longrightarrow> epdaH_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)"
  apply(simp add: epdaH.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac d i e)(*strict*)
  apply(rule epdaH_epda_stack_is_must_terminated_by_prime)
    apply(rename_tac d i e)(*strict*)
    apply(force)
   apply(rename_tac d i e)(*strict*)
   apply(force)
  apply(rename_tac d i e)(*strict*)
  apply(force)
  done

lemma DPDA_to_epdaH_determinism_SB_FE: "
  valid_dpda G
  \<Longrightarrow> epdaH.is_forward_edge_deterministicHist_SB_long G"
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long G")
   prefer 2
   apply(rule DPDA_to_epdaH_determinism)
   apply(force)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(rule_tac
      t = "epdaH.is_forward_edge_deterministicHist_SB_long G"
      in ssubst)
   apply(rule epdaH.AX_is_forward_edge_deterministic_correspond_DB_SB)
   apply(force)
  apply(force)
  done

lemma DPDA_to_epdaH_determinism_SB_F: "
  valid_dpda G
  \<Longrightarrow> epdaH.is_forward_deterministicHist_SB G"
  apply(rule I_epda_lemmas.DPDA_is_is_forward_deterministicHist_SB)
  apply(force)
  done

interpretation "epdaH_vs_epdaH" : L_Controllable
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
  apply(simp add: L_Controllable_def LOCALE_DEFS_ALL LOCALE_DEFS_autHF)
  apply(simp add: epdaH_inst_AX_initial_configuration_belongs epdaH_inst_AX_step_relation_preserves_belongs epdaH_inst_ATS_axioms)
  done

lemma epda_unmarked_language_is_prefix_closure: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> epdaH_unmarked_effect G d = prefix_closure {epdaH_conf_history c}"
  apply(induct n arbitrary: d e c)
   apply(rename_tac d e c)(*strict*)
   apply(simp add: epdaH_unmarked_effect_def epdaH.derivation_initial_def epdaH_initial_configurations_def prefix_def prefix_closure_def)
   apply(clarsimp)
   apply(rename_tac d c)(*strict*)
   apply(rule antisym)
    apply(rename_tac d c)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c i e ca)(*strict*)
    apply(case_tac i)
     apply(rename_tac d c i e ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac d c i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c e ca nat)(*strict*)
    apply (metis Suc_le_D Zero_not_Suc epdaH.allPreMaxDomSome_prime option.discI)
   apply(rename_tac d c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x = "0"
      in exI)
   apply(clarsimp)
  apply(rename_tac n d e c)(*strict*)
  apply(erule_tac
      x = "derivation_take d n"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaH_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac n d e c)(*strict*)
   prefer 2
   apply(rule epdaH.step_detail_before_some_position)
     apply(rename_tac n d e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac n d e c)(*strict*)
    apply(force)
   apply(rename_tac n d e c)(*strict*)
   apply(force)
  apply(rename_tac n d e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(erule_tac
      x = "e1"
      in meta_allE)
  apply(erule_tac
      x = "c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n d c e1 e2 c1)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d c e1 e2 c1)(*strict*)
   apply (metis maximum_of_domain_derivation_take option.discI)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d c e1 e2 c1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n d c e1 e2 c1 w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n d c e1 e2 c1 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac n d c e1 e2 c1 w q1 h1 s1)(*strict*)
  apply(case_tac c)
  apply(rename_tac n d c e1 e2 c1 w q1 h1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac n d c e1 e2 c1 w q1 h1 s1 q2 h2 s2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac n d e1 e2 w h1)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(rule antisym)
   apply(rename_tac n d e1 e2 w h1)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
   apply(case_tac "i = Suc n")
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d e1 e2 w h1)(*strict*)
    apply(simp add: epdaH_unmarked_effect_def epdaH.derivation_initial_def epdaH_initial_configurations_def prefix_def prefix_closure_def)
   apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
   apply(case_tac "i = n")
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d e2 w h1 e)(*strict*)
    apply(simp add: epdaH_unmarked_effect_def epdaH.derivation_initial_def epdaH_initial_configurations_def prefix_def prefix_closure_def)
   apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
   apply(subgoal_tac "i\<le>Suc n")
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    prefer 2
    apply(rule_tac
      d = "d"
      and i = "i"
      and n = "Suc n"
      in epdaH.allPreMaxDomSome_prime)
      apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
     apply(force)
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    apply(force)
   apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
   apply(subgoal_tac "i<n")
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history \<lparr>epdaH_conf_state = edge_src e2, epdaH_conf_history = h1, epdaH_conf_stack = edge_pop e2 @ w\<rparr> = epdaH_conf_history c @ h")
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    prefer 2
    apply(rule_tac
      d = "d"
      and n = "i"
      and m = "n-i"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
        apply(force)
       apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
      apply (metis (no_types, hide_lams) epdaH.derivation_initial_configurations)
     apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac n d e1 e2 w h1 i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d e1 e2 w i e c h)(*strict*)
   apply(simp add: epda_effects_def)
   apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac n d e1 e2 w h1)(*strict*)
  apply(simp (no_asm) add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac n d e1 e2 w h1 x c)(*strict*)
  apply(case_tac "edge_event e2")
   apply(rename_tac n d e1 e2 w h1 x c)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d e1 e2 w x c)(*strict*)
   apply(subgoal_tac "x\<in> {w. \<exists>i e c. derivation_take d n i = Some (pair e c) \<and> w = epdaH_conf_history c}")
    apply(rename_tac n d e1 e2 w x c)(*strict*)
    prefer 2
    apply(rule_tac
      A = "prefix_closure {x @ c}"
      in set_mp)
     apply(rename_tac n d e1 e2 w x c)(*strict*)
     apply(force)
    apply(rename_tac n d e1 e2 w x c)(*strict*)
    apply(simp (no_asm) add: prefix_closure_def prefix_def)
   apply(rename_tac n d e1 e2 w x c)(*strict*)
   apply(thin_tac "{w. \<exists>i e c. derivation_take d n i = Some (pair e c) \<and> w = epdaH_conf_history c} = prefix_closure {x @ c}")
   apply(clarsimp)
   apply(rename_tac n d e1 e2 w c i e ca)(*strict*)
   apply(rule_tac
      x = "i"
      in exI)
   apply(simp add: derivation_take_def)
   apply(case_tac "i\<le>n")
    apply(rename_tac n d e1 e2 w c i e ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d e1 e2 w c i e ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d e1 e2 w h1 x c a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      xs = "c"
      in rev_cases)
   apply(rename_tac n d e1 e2 w h1 x c a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d e1 e2 w h1 a)(*strict*)
   apply(rule_tac
      x = "Suc n"
      in exI)
   apply(clarsimp)
  apply(rename_tac n d e1 e2 w h1 x c a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d e1 e2 w x a ys)(*strict*)
  apply(subgoal_tac "x\<in> {w. \<exists>i e c. derivation_take d n i = Some (pair e c) \<and> w = epdaH_conf_history c}")
   apply(rename_tac n d e1 e2 w x a ys)(*strict*)
   prefer 2
   apply(rule_tac
      A = "prefix_closure {x @ ys}"
      in set_mp)
    apply(rename_tac n d e1 e2 w x a ys)(*strict*)
    apply(force)
   apply(rename_tac n d e1 e2 w x a ys)(*strict*)
   apply(simp (no_asm) add: prefix_closure_def prefix_def)
  apply(rename_tac n d e1 e2 w x a ys)(*strict*)
  apply(thin_tac "{w. \<exists>i e c. derivation_take d n i = Some (pair e c) \<and> w = epdaH_conf_history c} = prefix_closure {x @ ys}")
  apply(clarsimp)
  apply(rename_tac n d e1 e2 w a ys i e c)(*strict*)
  apply(rule_tac
      x = "i"
      in exI)
  apply(simp add: derivation_take_def)
  apply(case_tac "i\<le>n")
   apply(rename_tac n d e1 e2 w a ys i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d e1 e2 w a ys i e c)(*strict*)
  apply(clarsimp)
  done

theorem DES_controllability_vs_controllable_sublanguage: "
  DES_controllability \<Sigma>UC P C \<longleftrightarrow>
  controllable_sublanguage (des_langUM C) (alphabet_to_language \<Sigma>UC) (des_langUM P) (des_langUM C)"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(simp add: DES_controllability_def controllable_sublanguage_def controllable_language_def controllable_word_def alphabet_to_language_def append_alphabet_def append_language_def)
   apply(force)
  apply(clarsimp)
  apply(simp add: DES_controllability_def controllable_sublanguage_def controllable_language_def controllable_word_def alphabet_to_language_def append_alphabet_def append_language_def)
  apply(force)
  done

theorem DES_controllability_implies_operational_controllability: "
  valid_dfa P
  \<Longrightarrow> valid_dpda C
  \<Longrightarrow> epda_events P = epda_events C
  \<Longrightarrow> \<Sigma>UC \<subseteq> epda_events P
  \<Longrightarrow> ucont = (\<lambda>w. (\<exists>v. \<exists>x\<in> \<Sigma>UC. w = v@[x]))
  \<Longrightarrow> DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des C)
  \<Longrightarrow> epdaH_vs_epdaH.controllable C P ucont"
  apply(simp add: epdaH_vs_epdaH.controllable_def)
  apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "v @ [x] \<notin> epdaH_unmarked_effect P dP")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "edge_event eP' = Some x")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(thin_tac "epdaH_unmarked_effect P dP = epdaH_unmarked_effect C dC")
   apply(simp add: epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(case_tac "i = Suc nP")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x e c)(*strict*)
    apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x c)(*strict*)
    apply(case_tac c)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x epdaH_conf_state epdaH_conf_stack)(*strict*)
    apply(rename_tac q s)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x q s)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x w)(*strict*)
    apply(simp add: valid_dfa_def)
    apply(clarsimp)
    apply(erule_tac
      x = "eP'"
      in ballE)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' v x w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x w)(*strict*)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x w y)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(case_tac "Suc nP < i")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(simp add: derivation_append_def der2_def)
    apply(case_tac "i - nP = Suc 0")
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(subgoal_tac "i<Suc nP")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>i'. i+i' = nP")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    prefer 2
    apply(rule_tac
      x = "nP-i"
      in exI)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e c i')(*strict*)
   apply(case_tac c)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e c i' epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e i' epdaH_conf_state epdaH_conf_stack)(*strict*)
   apply(rename_tac q s)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e i' q s)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e i' q s w)(*strict*)
   apply(simp add: valid_dfa_def)
   apply(clarsimp)
   apply(erule_tac
      x = "eP'"
      in ballE)
    apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e i' q s w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e i' q s w)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP eP cP dC nC eC cC eP' cP' v x i e i' q s w y)(*strict*)
   apply(simp add: option_to_list_def)
   apply(erule_tac
      x = "i"
      in allE)+
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "v @ [x] \<in> epdaH.unmarked_language C")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(rule_tac
      A = "{w. \<exists>a\<in> epdaH.unmarked_language C. \<exists>b. (\<exists>v\<in> \<Sigma>UC. b = [v]) \<and> w = a @ b} \<inter> epdaH.unmarked_language P"
      in set_mp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(simp add: DES_controllability_def epda_to_des_def des_langUM_def des_langM_def controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(thin_tac "DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des C)")
   apply(simp (no_asm))
   apply(rule propSym)
   apply(rule context_conjI)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(thin_tac "epdaH_unmarked_effect P dP = epdaH_unmarked_effect C dC")
    apply(simp add: epdaH_unmarked_effect_def epdaH.unmarked_language_def)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(rule_tac
      x = "derivation_append dP (der2 cP eP' cP') nP"
      in exI)
    apply(rule context_conjI)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation_initial)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
      apply(rule epdaH.der2_is_derivation)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(rule conjI)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(rule_tac
      x = "Suc nP"
      in exI)
     apply(simp add: derivation_append_def der2_def)
     apply(erule_tac
      x = "i"
      in allE)+
     apply(case_tac "i<nP")
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(clarsimp)
     apply(case_tac "i = nP")
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(clarsimp)
     apply(case_tac "i - nP = Suc 0")
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(rule_tac
      x = "v"
      in bexI)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(rule_tac
      A = "epdaH_unmarked_effect C dC"
      in set_mp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(simp add: epdaH_unmarked_effect_def epdaH.unmarked_language_def)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d ia e ea c ca ib eb cb)(*strict*)
    apply(rule_tac
      x = "dC"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d ia e ea c ca ib eb cb)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d ia e ea c ca ib eb cb)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(rule_tac
      A = "epdaH_unmarked_effect P dP"
      in set_mp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(thin_tac "epdaH_unmarked_effect P dP = epdaH_unmarked_effect C dC")
   apply(thin_tac "v @ [x] \<in> epdaH.unmarked_language P")
   apply(simp add: epdaH_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(erule_tac
      x = "i"
      in allE)+
   apply(case_tac "i<nP")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(clarsimp)
   apply(case_tac "i = nP")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(clarsimp)
   apply(case_tac "i - nP = Suc 0")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x i c)(*strict*)
    apply(subgoal_tac "i = Suc nP")
     apply(rename_tac dP nP eP cP dC nC eC cC eP' v x i c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x i c)(*strict*)
    apply(clarsimp)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' v x c)(*strict*)
    apply(rule_tac
      x = "nP"
      in exI)
    apply(clarsimp)
    apply(simp add: epdaH_step_relation_def option_to_list_def)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "epdaH_conf_history cC = epdaH_conf_history cP")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(subgoal_tac "epdaH_unmarked_effect P dP = prefix_closure {epdaH_conf_history cP}")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    prefer 2
    apply(rule epda_unmarked_language_is_prefix_closure)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
       apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(subgoal_tac "epdaH_unmarked_effect C dC = prefix_closure {epdaH_conf_history cC}")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    prefer 2
    apply(rule epda_unmarked_language_is_prefix_closure)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
       apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(rule prefix_closure_single_eq)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "epdaH_conf_history cC = v")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(thin_tac "epdaH_unmarked_effect P dP = epdaH_unmarked_effect C dC")
   apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def epdaH_step_relation_def option_to_list_def derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d e c ia ea ca w)(*strict*)
   apply(case_tac c)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d e c ia ea ca w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac cP)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d e c ia ea ca w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(case_tac cP')
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d e c ia ea ca w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
   apply(case_tac cC)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d e c ia ea ca w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb epdaH_conf_statec epdaH_conf_historyc epdaH_conf_stackc)(*strict*)
   apply(case_tac ca)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x i d e c ia ea ca w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb epdaH_conf_statec epdaH_conf_historyc epdaH_conf_stackc epdaH_conf_stated epdaH_conf_historyd epdaH_conf_stackd)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
   apply(case_tac "i\<le>nP")
    apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x = "i"
      in allE)
    apply(force)
   apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
   apply(clarsimp)
   apply(case_tac "i-nP = Suc 0")
    apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
    apply(clarsimp)
   apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
   apply(subgoal_tac "i = Suc nP")
    apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dP nP eP dC nC eC eP' v x i d e ia ea w epdaH_conf_state epdaH_conf_stack epdaH_conf_historya epdaH_conf_statec epdaH_conf_stackc epdaH_conf_stated epdaH_conf_stackd)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(simp add: epdaH.unmarked_language_def epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      G = "C"
      and ?d1.0 = "dC"
      and ?d2.0 = "d"
      and ?i1.0 = "nC"
      and ?i2.0 = "ia"
      in epdaH_coincide_strict_prefix)
        apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
        apply(force)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(simp add: strict_prefix_def)
   apply(rule_tac
      x = "[x]"
      in exI)
   apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(rule_tac
      x = "map the (drop nC (get_labels d ia))"
      in exI)
  apply(rule_tac
      x = "ea"
      in exI)
  apply(rule_tac
      x = "ca"
      in exI)
  apply(rule_tac
      x = "derivation_drop (derivation_take d ia) nC"
      in exI)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(rule_tac
      m = "ia-nC"
      in epdaH.derivation_drop_preserves_derivation_prime)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(rule_tac epdaH.derivation_take_preserves_derivation)
    apply(simp add: epdaH.derivation_initial_def)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "length (get_labels d ia)"
      and s = "ia"
      in ssubst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def)
   apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "length (get_labels d ia)"
      and s = "ia"
      in ssubst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(simp add: maximum_of_domain_def derivation_take_def derivation_drop_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "length (get_labels d ia)"
      and s = "ia"
      in ssubst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(rule_tac
      t = "map (Some \<circ> the) (drop nC (get_labels d ia))"
      and s = "drop nC (map (Some \<circ> the) (get_labels d ia))"
      in ssubst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply (metis drop_map)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(rule_tac
      t = "map (Some \<circ> the) (get_labels d ia)"
      in subst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(rule epdaH.get_labels_the_Some_on_defined_positions)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(rule_tac
      t = "get_labels (derivation_drop (derivation_take d ia) nC) (ia - nC)"
      in ssubst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(rule get_labels_derivation_drop)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "get_labels (derivation_take d ia) ia"
      in subst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(rule_tac
      G = "C"
      in epdaH.get_labels_derivation_take)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' x i d e c ia ea ca)(*strict*)
  apply(rule_tac
      x = "ia"
      in exI)
  apply(clarsimp)
  apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  apply(clarsimp)
  done

theorem epda_operational_controllable_implies_operational_controllabilityX: "
  valid_dfa P
  \<Longrightarrow> valid_dpda C
  \<Longrightarrow> epda_events P = epda_events C
  \<Longrightarrow> \<Sigma>UC \<subseteq> epda_events P
  \<Longrightarrow> ucont = (\<lambda>w. (\<exists>v. \<exists>x\<in> \<Sigma>UC. w = v@[x]))
  \<Longrightarrow> epda_operational_controllable C P \<Sigma>UC
  \<Longrightarrow> epdaH_vs_epdaH.controllableX C P ucont"
  apply(simp add: epdaH_vs_epdaH.controllableX_def epda_operational_controllable_def)
  apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule_tac x="dC" in allE)
  apply(clarsimp)
  apply(erule_tac x="nC" in allE)
  apply(clarsimp)
  apply(subgoal_tac "ATS.derivation_initial epdaH_initial_configurations
        epdaH_step_relation P (derivation_append dP (der2 cP eP' cP') nP)")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule_tac x="derivation_append dP (der2 cP eP' cP') nP" in allE)
  apply(erule impE)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule_tac x="nP" in allE)
  apply(erule_tac x="eP" in allE)
  apply(erule_tac x="cP" in allE)
  apply(erule impE)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule_tac x="Some eP'" in allE)
  apply(erule_tac x="cP'" in allE)
  apply(erule impE)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule impE)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(thin_tac "v @ [x]
       \<in> epdaH_unmarked_effect P
           (derivation_append dP (der2 cP eP' cP') nP)")
   apply(thin_tac "v @ [x] \<notin> epdaH_unmarked_effect C dC")
   apply(subgoal_tac "epdaH_unmarked_effect P dP = prefix_closure {epdaH_conf_history cP}")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    prefer 2
    apply(rule epda_unmarked_language_is_prefix_closure)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
       apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(subgoal_tac "epdaH_unmarked_effect C dC = prefix_closure {epdaH_conf_history cC}")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    prefer 2
    apply(rule epda_unmarked_language_is_prefix_closure)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
       apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(rule prefix_closure_single_eq)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule_tac x="x" in allE)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_unmarked_effect P (derivation_append dP (der2 cP eP' cP') nP) = prefix_closure {epdaH_conf_history cP'}")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(rule epda_unmarked_language_is_prefix_closure)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
      apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "epdaH_unmarked_effect C dC = prefix_closure {epdaH_conf_history cC}")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(rule epda_unmarked_language_is_prefix_closure)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
      apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "epdaH_conf_history cP @ [x] = epdaH_conf_history cP'")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(subgoal_tac "v @ [x] \<notin> epdaH_unmarked_effect P dP")
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(thin_tac "v @ [x] \<notin> epdaH_unmarked_effect C dC")
   apply(thin_tac "ATS.derivation_initial epdaH_initial_configurations
        epdaH_step_relation C dC")
   apply(thin_tac "maximum_of_domain dC nC")
   apply(thin_tac "dC nC = Some (pair eC cC)")
   apply(thin_tac "epdaH_unmarked_effect P dP = epdaH_unmarked_effect C dC")
   apply(thin_tac "epdaH_unmarked_effect C dC = prefix_closure {epdaH_conf_history cC}")
   apply(simp add: epdaH_unmarked_effect_def)
   apply(rename_tac dP nP eP cP cC eP' cP' v x)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP nP eP cP cC eP' cP' v x i e c)(*strict*)
   apply(case_tac "i\<le>nP")
    apply(rename_tac dP nP eP cP cC eP' cP' v x i e c)(*strict*)
    apply(erule_tac x="i" in allE)
    apply(simp add: derivation_append_def)
   apply(rename_tac dP nP eP cP cC eP' cP' v x i e c)(*strict*)
   apply(case_tac "i=Suc nP")
    apply(rename_tac dP nP eP cP cC eP' cP' v x i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
    apply(simp add: der2_def)
    apply(case_tac "i-nP")
     apply(rename_tac dP nP eP cP cC eP' cP' v x i e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac dP nP eP cP cC eP' cP' v x i e c nat)(*strict*)
    apply(clarsimp)
    apply(case_tac nat)
     apply(rename_tac dP nP eP cP cC eP' cP' v x i e c nat)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP cC eP' cP' v x i e c nat nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac dP nP eP cP cC eP' cP' v x i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP nP eP cP cC eP' cP' v x e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: der2_def)
   apply(clarsimp)
   apply(rename_tac dP nP eP cP cC eP' v x c)(*strict*)
   apply(case_tac c)
   apply(rename_tac dP nP eP cP cC eP' v x c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(case_tac cP)
   apply(rename_tac dP nP eP cP cC eP' v x c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac dP nP eP cC eP' v x epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac dP nP eP cC eP' v x epdaH_conf_historya w)(*strict*)
   apply(case_tac "edge_event eP'")
    apply(rename_tac dP nP eP cC eP' v x epdaH_conf_historya w)(*strict*)
    prefer 2
    apply(rename_tac dP nP eP cC eP' v x epdaH_conf_historya w a)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
   apply(rename_tac dP nP eP cC eP' v x epdaH_conf_historya w)(*strict*)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac dP nP eP eP' v x w)(*strict*)
   apply(erule_tac x="nP" in allE)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(subgoal_tac "epdaH_conf_history cP' = epdaH_conf_history cP @ [x]")
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   prefer 2
   apply(rule prefix_closure_single_eq)
   apply(rule_tac t="epdaH_conf_history cP @ [x]" and s="epdaH_conf_history cP'" in ssubst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule impE)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(clarify)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac x="map the (get_labels dc nCa)" in exI)
  apply(rule_tac x="eCa" in exI)
  apply(rule_tac x="cCa" in exI)
  apply(rule_tac x="derivation_take dc nCa" in exI)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="length (get_labels dc nCa)" and s="nCa" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule get_labels_length)
   apply(blast)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(simp (no_asm) add: derivation_take_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="length(map the (get_labels dc nCa))" and s="length((get_labels dc nCa))" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule length_map)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="length (get_labels dc nCa)" and s="nCa" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule get_labels_length)
   apply(blast)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(simp (no_asm) add: derivation_take_def)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(blast)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule conjI)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule_tac t="get_labels (derivation_take dc nCa) nCa" and s="get_labels dc nCa" in subst)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
    apply(rule_tac G="C" in epdaH.get_labels_derivation_take)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
      apply(unfold valid_dfa_def valid_dpda_def valid_pda_def)[1]
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
    apply(blast)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(simp (no_asm))
   apply(rule epdaH.get_labels_the_Some_on_defined_positions)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
    apply(blast)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(blast)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="epdaH_unmarked_effect P (derivation_append dP (der2 cP eP' cP') nP)" and s="prefix_closure {epdaH_conf_history cP'}" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="epdaH_unmarked_effect C dC" and s="prefix_closure {epdaH_conf_history cC}" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="epdaH_unmarked_effect C
        (derivation_append dC (derivation_take dc nCa) nC)"  and s="prefix_closure {epdaH_conf_history cCa}" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(rule_tac e="if nCa = 0 then eC else eCa" and G="C" and n="nC+nCa" in epda_unmarked_language_is_prefix_closure)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
      apply(unfold valid_dfa_def valid_pda_def valid_dpda_def)[1]
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
     apply(rule_tac epdaH.derivation_append_preserves_derivation_initial)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
       apply(unfold valid_dfa_def valid_pda_def valid_dpda_def)[1]
       apply(force)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
     apply(rule_tac epdaH.derivation_append_preserves_derivation)
       apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
       apply(unfold epdaH.derivation_initial_def)[1]
       apply(force)
      apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
      apply(rule_tac epdaH.derivation_take_preserves_derivation)
      apply(unfold epdaH.derivation_initial_def)[1]
      apply(force)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
     apply(unfold maximum_of_domain_def derivation_take_def)[1]
     apply(simp (no_asm))
     apply(clarify)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa y ya)(*strict*)
     apply(simp (no_asm_simp))
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
     apply(force)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(blast)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(unfold derivation_append_def derivation_take_def)[1]
   apply(simp (no_asm))
   apply(rule conjI)
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
    apply(clarify)
    apply(simp (no_asm_simp))
    apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc eCa cCa)(*strict*)
    apply(thin_tac "v @ [x]
       \<in> epdaH_unmarked_effect P
           (\<lambda>x. if x \<le> nP then dP x else der2 cP eP' cP' (x - nP))")
    apply(thin_tac "ATS.derivation_initial epdaH_initial_configurations
        epdaH_step_relation P
        (\<lambda>x. if x \<le> nP then dP x else der2 cP eP' cP' (x - nP))")
    apply(thin_tac "epdaH_unmarked_effect P
        (\<lambda>x. if x \<le> nP then dP x else der2 cP eP' cP' (x - nP)) =
       prefix_closure {epdaH_conf_history cP'}")
    apply(thin_tac "epdaH_unmarked_effect C dC =
       prefix_closure {epdaH_conf_history cC}")
    apply(clarsimp)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(thin_tac "v @ [x]
       \<in> epdaH_unmarked_effect P
           (\<lambda>x. if x \<le> nP then dP x else der2 cP eP' cP' (x - nP))")
   apply(thin_tac "ATS.derivation_initial epdaH_initial_configurations
        epdaH_step_relation P
        (\<lambda>x. if x \<le> nP then dP x else der2 cP eP' cP' (x - nP))")
   apply(thin_tac "epdaH_unmarked_effect P
        (\<lambda>x. if x \<le> nP then dP x else der2 cP eP' cP' (x - nP)) =
       prefix_closure {epdaH_conf_history cP'}")
   apply(thin_tac "epdaH_unmarked_effect C dC =
       prefix_closure {epdaH_conf_history cC}")
   apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="epdaH_conf_history cCa" and s="epdaH_conf_history cP @ [x]" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(rule_tac t="epdaH_conf_history cP'" and s="epdaH_conf_history cP @ [x]" in ssubst)
   apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
   apply(force)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x dc nCa eCa cCa)(*strict*)
  apply(force)
  done

theorem operational_controllability_implies_DES_controllability: "
  valid_dfa P
  \<Longrightarrow> valid_dpda C
  \<Longrightarrow> epda_events P = epda_events C
  \<Longrightarrow> \<Sigma>UC \<subseteq> epda_events P
  \<Longrightarrow> ucont = (\<lambda>w. (\<exists>v. \<exists>x\<in> \<Sigma>UC. w = v@[x]))
  \<Longrightarrow> epdaH_vs_epdaH.controllable C P ucont
  \<Longrightarrow> epda_operational_controllable C P \<Sigma>UC"
  apply(simp add: epda_operational_controllable_def epdaH_vs_epdaH.controllable_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule_tac
      x = "derivation_take d2 n2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule_tac
      x = "n2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule_tac
      x = "e2"
      in allE)
  apply(erule_tac
      x = "c2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule_tac
      x = "derivation_take d1 n1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule_tac
      x = "n1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule_tac
      x = "e1"
      in allE)
  apply(erule_tac
      x = "c1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule_tac
      t = "epdaH_unmarked_effect P (derivation_take d2 n2)"
      in ssubst)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(rule_tac
      n = "n2"
      in epda_unmarked_language_is_prefix_closure)
       apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
      apply(rule epdaH.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(force)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule_tac
      t = "epdaH_unmarked_effect C (derivation_take d1 n1)"
      in ssubst)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(rule_tac
      n = "n1"
      in epda_unmarked_language_is_prefix_closure)
       apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
      apply(rule epdaH.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(force)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(rule_tac
      t = "epdaH_conf_history c2"
      and s = "epdaH_conf_history c1"
      in ssubst)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 n2 = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaH_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc n2"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 e2' c2' u)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
  apply(erule_tac
      x = "e2a"
      in allE)
  apply(erule_tac
      x = "c2'"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
  apply(erule_tac
      x = "epdaH_conf_history c2 @ [u]"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
    apply(simp add: epdaH_unmarked_effect_def)
    apply(rule_tac
      x = "Suc n2"
      in exI)
    apply(simp add: derivation_append_def derivation_take_def der2_def)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
   apply(rule_tac
      t = "epdaH_unmarked_effect C (derivation_take d1 n1)"
      in ssubst)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
    apply(rule_tac
      n = "n1"
      in epda_unmarked_language_is_prefix_closure)
       apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
      apply(rule epdaH.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(force)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
   apply(simp (no_asm) add: prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC')(*strict*)
  apply(rule_tac
      x = "dC'"
      in exI)
  apply(clarsimp)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
  apply(case_tac "i\<le>n1")
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
   prefer 2
   apply(rule_tac
      x = "i-n1"
      in exI)
   apply(simp add: derivation_append_def derivation_take_def)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
  apply(subgoal_tac "d1 i = Some (pair ea c)")
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def derivation_take_def get_configuration_def)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
   prefer 2
   apply(rule_tac
      G = "C"
      and d = "d1"
      and n = "i"
      and m = "n1-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def valid_dfa_def)
      apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
     prefer 2
     apply(simp add: derivation_append_def derivation_take_def get_configuration_def)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
    apply(rule_tac
      d = "d1"
      in epdaH.belongs_configurations)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def valid_dfa_def)
     apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
   apply(simp add: derivation_append_def derivation_take_def get_configuration_def)
  apply(rename_tac d1 n1 e1 c1 d2 n2 e2 c2 c2' u e2a \<pi>P' e cC' dC' i ea c)(*strict*)
  apply(clarsimp)
  done

theorem controllable_vs_controllableX_part1: "
  valid_dfa P
  \<Longrightarrow> valid_dpda C
  \<Longrightarrow> epda_events P = epda_events C
  \<Longrightarrow> \<Sigma>UC \<subseteq> epda_events P
  \<Longrightarrow> ucont = (\<lambda>w. (\<exists>v. \<exists>x\<in> \<Sigma>UC. w = v@[x]))
  \<Longrightarrow> epdaH_vs_epdaH.controllableX C P ucont
  \<Longrightarrow> epdaH_vs_epdaH.controllable C P ucont"
  apply(simp add: epdaH_vs_epdaH.controllable_def epdaH_vs_epdaH.controllableX_def)
  apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x)(*strict*)
  apply(erule_tac x="dP" in allE)
  apply(clarsimp)
  apply(erule_tac x="nP" in allE)
  apply(clarsimp)
  apply(erule_tac x="dC" in allE)
  apply(clarsimp)
  apply(erule_tac x="nC" in allE)
  apply(clarsimp)
  apply(erule_tac x="eP'" in allE)
  apply(erule_tac x="cP'" in allE)
  apply(clarsimp)
  apply(erule_tac x="v@[x]" in allE)
  apply(clarsimp)
  apply(rename_tac dP nP eP cP dC nC eC cC eP' cP' v x \<pi>P' e cC' dC')(*strict*)
  apply(rule_tac x="\<pi>P'" in exI)
  apply(rule_tac x="e" in exI)
  apply(rule_tac x="cC'" in exI)
  apply(rule_tac x="dC'" in exI)
  apply(clarsimp)
  apply (metis Diff_iff)
  done

theorem DES_controllability_implies_operational_controllabilityX: "
  valid_dfa P
  \<Longrightarrow> valid_dpda C
  \<Longrightarrow> epda_events P = epda_events C
  \<Longrightarrow> \<Sigma>UC \<subseteq> epda_events P
  \<Longrightarrow> ucont = (\<lambda>w. (\<exists>v. \<exists>x\<in> \<Sigma>UC. w = v@[x]))
  \<Longrightarrow> DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des C)
  \<Longrightarrow> epdaH_vs_epdaH.controllableX C P ucont"
  apply(rule epda_operational_controllable_implies_operational_controllabilityX)
       apply(force)
      apply(force)
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(rule operational_controllability_implies_DES_controllability)
       apply(force)
      apply(force)
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(rule DES_controllability_implies_operational_controllability)
       apply(force)
      apply(force)
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(force)
  done

theorem EPDA_relationship_among_controllability_notions: "
  valid_dfa P
  \<Longrightarrow> valid_dpda C
  \<Longrightarrow> epda_events P = epda_events C
  \<Longrightarrow> \<Sigma>UC \<subseteq> epda_events P
  \<Longrightarrow> ucont = (\<lambda>w. (\<exists>v. \<exists>x\<in> \<Sigma>UC. w = v@[x]))
  \<Longrightarrow>
  (epdaH_vs_epdaH.controllable C P ucont
    \<longleftrightarrow> epdaH_vs_epdaH.controllableX C P ucont)
  \<and> (epdaH_vs_epdaH.controllable C P ucont
    \<longleftrightarrow> epda_operational_controllable C P \<Sigma>UC)
  \<and> (epda_operational_controllable C P \<Sigma>UC
    \<longleftrightarrow> DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des C))
  \<and> (DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des C)
    \<longleftrightarrow> controllable_sublanguage (epdaH.unmarked_language C) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language P) (epdaH.unmarked_language C))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule impI)
   apply(rule_tac \<Sigma>UC="\<Sigma>UC" in epda_operational_controllable_implies_operational_controllabilityX)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule impI)
   apply(rule_tac \<Sigma>UC="\<Sigma>UC" in operational_controllability_implies_DES_controllability)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule impI)
   apply(rule_tac \<Sigma>UC="\<Sigma>UC" in DES_controllability_implies_operational_controllability)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac \<Sigma>UC="\<Sigma>UC" and P="(epda_to_des P)" and C="(epda_to_des C)" in DES_controllability_vs_controllable_sublanguage)
  apply(simp add: epda_to_des_def des_langUM_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac SigmaUC="\<Sigma>UC" in epda_epda_operational_controllable_vs_Cont)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac P="L_Controllable.controllableX epdaH_initial_configurations epdaH_step_relation
     epdaH_unmarked_effect epdaH_initial_configurations epdaH_step_relation
     epdaH_unmarked_effect C P ucont" in impI)
   apply(rule_tac \<Sigma>UC="\<Sigma>UC" in controllable_vs_controllableX_part1)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule antisym)
    apply(simp (no_asm))
    apply(rule impI)
    apply(rule_tac P="epda_operational_controllable C P \<Sigma>UC" in mp)
     prefer 2
     apply(force)
    apply(force)
   apply(simp (no_asm))
   apply(rule impI)
   apply(force)
  apply(rule context_conjI)
   apply(rule antisym)
    apply(simp (no_asm))
   apply(simp (no_asm))
   apply(force)
  apply(rule antisym)
   apply(simp (no_asm))
   apply(force)
  apply(simp (no_asm))
  apply(force)
  done

theorem livelock_implies_epdaH_has_livelock: "
  valid_epda G
  \<Longrightarrow> epdaH_livelock G
  \<Longrightarrow> epdaH.has_livelock G"
  apply(simp add: epdaH_livelock_def epdaH.has_livelock_def epdaH.derivation_livelock_def)
  apply(erule exE)+
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d N)(*strict*)
  apply(rule_tac
      x = "N"
      in exI)
  apply(rule allI)
  apply(rename_tac d N n)(*strict*)
  apply(case_tac "d N")
   apply(rename_tac d N n)(*strict*)
   apply(erule_tac
      x = "N"
      in allE)+
   apply(force)
  apply(rename_tac d N n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac d N n a option conf)(*strict*)
  apply(rename_tac eN cN)
  apply(rename_tac d N n a eN cN)(*strict*)
  apply(erule_tac
      x = "n"
      in allE)+
  apply(clarsimp)
  apply(rename_tac d N n eN cN y)(*strict*)
  apply(case_tac y)
  apply(rename_tac d N n eN cN y option conf)(*strict*)
  apply(rename_tac en cn)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply(rule_tac
      t = "epdaH_unmarked_effect G (derivation_take d N)"
      in ssubst)
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   apply(rule_tac
      n = "N"
      in epda_unmarked_language_is_prefix_closure)
      apply(rename_tac d N n eN cN y en cn)(*strict*)
      apply(force)
     apply(rename_tac d N n eN cN y en cn)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac d N n eN cN y en cn)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation maximum_of_domain_derivation_take epdaH.pre_some_position_is_some_position option.distinct(1))
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply(rule_tac
      t = "epdaH_unmarked_effect G (derivation_take d n)"
      in ssubst)
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   apply(rule_tac
      n = "n"
      in epda_unmarked_language_is_prefix_closure)
      apply(rename_tac d N n eN cN y en cn)(*strict*)
      apply(force)
     apply(rename_tac d N n eN cN y en cn)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac d N n eN cN y en cn)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation maximum_of_domain_derivation_take epdaH.pre_some_position_is_some_position option.distinct(1))
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply(rule_tac
      t = "epdaH_conf_history cN"
      and s = "epdaH_conf_history cn"
      in ssubst)
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply(simp add: get_configuration_def)
  done

theorem epdaH_has_livelock_implies_livelock: "
  valid_epda G
  \<Longrightarrow> epdaH.has_livelock G
  \<Longrightarrow> epdaH_livelock G"
  apply(simp add: epdaH_livelock_def epdaH.has_livelock_def epdaH.derivation_livelock_def)
  apply(erule exE)+
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d N)(*strict*)
  apply(rule_tac
      x = "N"
      in exI)
  apply(rule allI)
  apply(rename_tac d N n)(*strict*)
  apply(case_tac "d N")
   apply(rename_tac d N n)(*strict*)
   apply(erule_tac
      x = "N"
      in allE)+
   apply(force)
  apply(rename_tac d N n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac d N n a option conf)(*strict*)
  apply(rename_tac eN cN)
  apply(rename_tac d N n a eN cN)(*strict*)
  apply(erule_tac
      x = "n"
      in allE)+
  apply(clarsimp)
  apply(rename_tac d N n eN cN y)(*strict*)
  apply(case_tac y)
  apply(rename_tac d N n eN cN y option conf)(*strict*)
  apply(rename_tac en cn)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   prefer 2
   apply(rule_tac
      d = "derivation_take d N"
      and n = "N"
      in epda_unmarked_language_is_prefix_closure)
      apply(rename_tac d N n eN cN y en cn)(*strict*)
      apply(force)
     apply(rename_tac d N n eN cN y en cn)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac d N n eN cN y en cn)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation maximum_of_domain_derivation_take epdaH.pre_some_position_is_some_position option.distinct(1))
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   prefer 2
   apply(rule_tac
      d = "derivation_take d n"
      and n = "n"
      in epda_unmarked_language_is_prefix_closure)
      apply(rename_tac d N n eN cN y en cn)(*strict*)
      apply(force)
     apply(rename_tac d N n eN cN y en cn)(*strict*)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac d N n eN cN y en cn)(*strict*)
    apply (metis epdaH.derivation_initial_is_derivation maximum_of_domain_derivation_take epdaH.pre_some_position_is_some_position option.distinct(1))
   apply(rename_tac d N n eN cN y en cn)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d N n eN cN y en cn)(*strict*)
  apply (metis prefix_closure_single_eq)
  done

corollary epda_inter_semantic_relationship: "
  valid_epda G
  \<Longrightarrow> epdaS.marked_language G = epdaH.marked_language G
  \<and> epdaS.marked_language G = epdaHS.marked_language G
  \<and> epdaS.unmarked_language G = epdaH.unmarked_language G
  \<and> epdaS.unmarked_language G = epdaHS.unmarked_language G
  \<and> (epdaS.is_forward_edge_deterministic_accessible G \<longleftrightarrow> epdaH.is_forward_edge_deterministicHist_SB G)
  \<and> (epdaS.is_forward_edge_deterministic_accessible G \<longleftrightarrow> epdaHS.is_forward_edge_deterministic_accessible G)
  \<and> (epdaS.Nonblockingness_linear_DB G \<longleftrightarrow> epdaHS.Nonblockingness_linear_DB G)
  \<and> (epdaS.Nonblockingness_linear_DB G \<longleftrightarrow> epdaH.Nonblockingness_branching G)"
  apply(rule conjI)
   apply (metis epdaS_to_epdaH_mlang)
  apply(rule conjI)
   apply (metis epdaS_to_epdaHS_mlang)
  apply(rule conjI)
   apply (metis epdaS_to_epdaH_unmarked_language)
  apply(rule conjI)
   apply (metis epdaS_to_epdaHS_unmarked_language)
  apply(rule conjI)
   apply(metis epdaH.AX_is_forward_edge_deterministic_correspond_DB_SB epdaH.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long epda_epdaS_is_forward_edge_deterministic_accessible_equal_to_epdaH_is_forward_edge_deterministicHist_DB_long)
  apply(rule conjI)
   apply(metis epdaS_vs_epdaHS.preservation_of_determinism epdaS_vs_epdaHS_TSstructure_rel_def)
  apply(rule context_conjI)
   apply (metis epdaS_vs_epdaHS.preservation_of_Nonblockingnessness epdaS_vs_epdaHS_TSstructure_rel_def)
  apply (metis epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
  done

theorem epdaH_dependency_between_determinism_properties: "
  valid_epda G
  \<Longrightarrow>
  epdaH.is_forward_target_deterministic_accessible G
  \<and> (epdaH.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> epdaH.is_forward_target_deterministicHist_SB G)
  \<and> (epdaH.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> epdaH.is_forward_target_deterministicHist_DB G)
  \<and> (epdaH.is_forward_target_deterministicHist_SB G
  \<longleftrightarrow> epdaH.is_forward_target_deterministicHist_DB G)
  \<and> (epdaH.is_forward_edge_deterministic_accessible G
  \<longrightarrow> epdaH.is_forward_edge_deterministicHist_SB G)
  \<and> (epdaH.is_forward_edge_deterministic_accessible G
  \<longrightarrow> epdaH.is_forward_edge_deterministicHist_DB G)
  \<and> (epdaH.is_forward_edge_deterministicHist_SB G
  \<longleftrightarrow> epdaH.is_forward_edge_deterministicHist_DB G)"
  apply(rule conjI)
   apply (metis epdaH_inst_AX_is_forward_target_deterministic_correspond_DB epdaH_is_forward_target_deterministicHist_DB_long)
  apply(rule conjI)
   apply (metis epdaH.AX_is_forward_target_deterministic_correspond_SB epdaH.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long)
  apply(rule conjI)
   apply (metis epdaH.AX_is_forward_target_deterministic_correspond_DB epdaH.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long)
  apply(rule context_conjI)
   apply (metis epdaH.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long epdaH.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long epdaH_inst_AX_is_forward_target_deterministic_correspond_DB epdaH_inst_AX_is_forward_target_deterministic_correspond_SB)
  apply(rule context_conjI)
   apply (metis epdaH.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_SB)
  apply(rule conjI)
   apply (metis epdaH.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long epdaH.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
  apply (metis epdaH.AX_is_forward_edge_deterministic_correspond_DB_SB epdaH.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long epdaH.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  done

corollary epdaH_operational_Nonblockingness_SB_DB_Restriction: "
  valid_epda G
  \<Longrightarrow> (epdaH.Nonblockingness_branching_restricted G \<longleftrightarrow> epdaH.Nonblockingness_branching G)
  \<and> (epdaH.Nonblockingness_branching_restricted_DB G \<longleftrightarrow> epdaH.Nonblockingness_branching G)"
  apply(rule conjI)
   apply(rule antisym)
    apply(simp add: epdaH.Nonblockingness_branching_restricted_def epdaH.Nonblockingness_branching_def)
   apply(simp add: epdaH.Nonblockingness_branching_restricted_def epdaH.Nonblockingness_branching_def)
  apply(rule antisym)
   apply(simp add: epdaH.Nonblockingness_branching_restricted_DB_def epdaH.Nonblockingness_branching_def)
  apply(simp add: epdaH.Nonblockingness_branching_restricted_DB_def epdaH.Nonblockingness_branching_def)
  done

corollary epdaH_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_epda G
  \<Longrightarrow> epdaH.Nonblockingness_branching G
  \<Longrightarrow> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)"
  apply(metis epdaH.AX_BF_Bra_OpLa)
  done

corollary epdaH_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_epda G
  \<Longrightarrow> epdaH.is_forward_edge_deterministicHist_SB G
  \<Longrightarrow> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)
  \<Longrightarrow> epdaH.Nonblockingness_branching G"
  apply (metis epdaH.is_forward_deterministicHist_SB_def epdaH.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long epdaH_inst_AX_BF_BraSBRest_DetHSB_LaOp_axioms epdaH_inst_AX_is_forward_target_deterministic_correspond_SB epdaH_is_forward_target_deterministic_accessible epdaH_operational_Nonblockingness_SB_DB_Restriction)
  done

theorem epdaHS_dependency_between_determinism_properties: "
  valid_epda G
  \<Longrightarrow>
  epdaHS.is_forward_target_deterministic_accessible G
  \<and> (epdaHS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> epdaHS.is_forward_target_deterministicHist_SB G)
  \<and> (epdaHS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> epdaHS.is_forward_target_deterministicHist_DB G)
  \<and> (epdaHS.is_forward_target_deterministicHist_SB G
  \<longleftrightarrow> epdaHS.is_forward_target_deterministicHist_DB G)
  \<and> (epdaHS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> epdaHS.is_forward_edge_deterministicHist_SB G)
  \<and> (epdaHS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> epdaHS.is_forward_edge_deterministicHist_DB G)
  \<and> (epdaHS.is_forward_edge_deterministicHist_SB G
  \<longleftrightarrow> epdaHS.is_forward_edge_deterministicHist_DB G)"
  apply(rule conjI)
   apply(rule epdaHS_is_forward_target_deterministic_accessible)
   apply(force)
  apply(rule conjI)
   apply (metis epdaHS.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long epdaHS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long epdaHS_is_forward_target_deterministic_accessible)
  apply(rule conjI)
   apply (metis epdaHS.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long epdaHS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_DB_long epdaHS_is_forward_target_deterministic_accessible)
  apply(rule conjI)
   apply (metis epdaHS.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long epdaHS.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long epdaHS_inst_AX_is_forward_target_deterministic_correspond_DB epdaHS_inst_AX_is_forward_target_deterministic_correspond_SB)
  apply(rule conjI)
   apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_SB epdaHS.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  apply(rule conjI)
   apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_DB epdaHS.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long)
  apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_DB_SB epdaHS.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long epdaHS.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  done

corollary epdaHS_operational_Nonblockingness_SB_DB_Restriction: "
  valid_epda G
  \<Longrightarrow> (epdaHS.Nonblockingness_linear G
        \<longleftrightarrow> epdaHS.Nonblockingness_linear_restricted G)
  \<and> (epdaHS.Nonblockingness_linear_DB G
        \<longleftrightarrow> epdaHS.Nonblockingness_linear_restricted_DB G)
  \<and> (epdaHS.Nonblockingness_linear G
        \<longleftrightarrow> epdaHS.Nonblockingness_linear_DB G)
  \<and> (epdaHS.Nonblockingness_linear_restricted G
        \<longleftrightarrow> epdaHS.Nonblockingness_linear_restricted_DB G)"
  apply(rule conjI)
   apply(simp add: epdaHS.Nonblockingness_linear_restricted_DB_def epdaHS.Nonblockingness_linear_restricted_def epdaHS.Nonblockingness_linear_def epdaHS.Nonblockingness_linear_DB_def)
  apply(rule conjI)
   apply(simp add: epdaHS.Nonblockingness_linear_restricted_DB_def epdaHS.Nonblockingness_linear_restricted_def epdaHS.Nonblockingness_linear_def epdaHS.Nonblockingness_linear_DB_def)
  apply(rule conjI)
   apply (metis epdaHS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(metis epdaHS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_1 epdaHS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2)
  done

corollary epdaHS_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_epda G
  \<Longrightarrow> epdaHS.Nonblockingness_linear G
  \<Longrightarrow> nonblockingness_language (epdaHS.unmarked_language G) (epdaHS.marked_language G)"
  apply(metis epdaHS.AX_BF_LinSB_OpLa)
  done

corollary epdaHS_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_epda G
  \<Longrightarrow> epdaHS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (epdaHS.unmarked_language G) (epdaHS.marked_language G)
  \<Longrightarrow> epdaHS.Nonblockingness_linear G"
  apply(subgoal_tac "epdaHS.is_forward_deterministic_accessible G")
   apply(thin_tac "epdaHS.is_forward_edge_deterministic_accessible G")
   apply (metis epdaHS.AX_BF_LinSBRest_DetR_LaOp epdaHS_operational_Nonblockingness_SB_DB_Restriction)
  apply (metis epdaHS.is_forward_deterministic_accessible_def epdaHS_is_forward_target_deterministic_accessible)
  done

theorem epdaS_dependency_between_determinism_properties: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_target_deterministic_accessible G"
  apply (metis epda_is_is_forward_target_deterministic_accessible)
  done

corollary epdaS_operational_Nonblockingness_SB_DB_Restriction: "
  valid_epda G
  \<Longrightarrow> epdaS.Nonblockingness_linear_DB G \<longleftrightarrow> epdaS.Nonblockingness_linear_restricted_DB G"
  apply(simp add: epdaS.Nonblockingness_linear_restricted_DB_def epdaS.Nonblockingness_linear_DB_def)
  done

corollary epdaS_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_epda G
  \<Longrightarrow> epdaS.Nonblockingness_linear_DB G
  \<Longrightarrow> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)"
  apply(metis epdaS.AX_BF_LinDB_OpLa)
  done

corollary epdaS_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<Longrightarrow> epdaS.Nonblockingness_linear_DB G
      \<and> epdaS.Nonblockingness_linear_restricted_DB G"
  apply(subgoal_tac "epdaS.is_forward_deterministic_accessible G")
   apply(rule_tac
      t="epdaS.Nonblockingness_linear_DB G"
      and s="epdaS.Nonblockingness_linear_restricted_DB G"
      in ssubst)
    apply(simp add: epdaS.Nonblockingness_linear_DB_def epdaS.Nonblockingness_linear_restricted_DB_def)
   apply(metis epdaS.AX_BF_LinDBRest_DetR_LaOp)
  apply(simp only: epdaS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(thin_tac "epdaS.is_forward_edge_deterministic_accessible G")
  apply(thin_tac "nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)")
  apply(metis epda_is_is_forward_target_deterministic_accessible)
  done

corollary epda_inter_semantics_determinsim_relationship: "
  valid_epda G
  \<Longrightarrow>
  (epdaS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> epdaHS.is_forward_target_deterministic_accessible G)
  \<and> (epdaS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> epdaH.is_forward_target_deterministic_accessible G)
  \<and> (epdaS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> epdaHS.is_forward_edge_deterministic_accessible G)
  \<and> (epdaH.is_forward_edge_deterministicHist_SB G
  \<longleftrightarrow> epdaHS.is_forward_edge_deterministicHist_SB G)"
  apply(rule_tac
      t="epdaS.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
   apply (metis epdaS_dependency_between_determinism_properties)
  apply(rule_tac
      t="epdaHS.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
   apply (metis epdaHS_is_forward_target_deterministic_accessible)
  apply(rule_tac
      t="epdaH.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
   apply (metis epdaH_dependency_between_determinism_properties)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply (metis epdaS_vs_epdaHS.preservation_of_determinism epdaS_vs_epdaHS_TSstructure_rel_def)
  apply (metis epdaHS.AX_is_forward_edge_deterministic_correspond_SB epdaHS.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long epdaH_vs_epdaHS.is_forward_edge_deterministic_accessible_vs_is_forward_edge_deterministicHist_SB)
  done

lemma epda_unmarked_language_prefix_closed: "
  valid_epda P
  \<Longrightarrow> Nonblockingness2 (epdaH.unmarked_language P) (epdaH.unmarked_language P)"
  apply(simp add: Nonblockingness2_def)
  apply(simp add: epdaH.marked_language_def epdaH.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac x d c)(*strict*)
   prefer 2
   apply(rule epdaH.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac x d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca)(*strict*)
  apply(subgoal_tac "ca \<in> epdaH_initial_configurations P")
   apply(rename_tac x d c ca)(*strict*)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac x d c ca)(*strict*)
  apply(simp add: epdaH_initial_configurations_def)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac x d c ca epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d c i e ca)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k\<le>i. (\<forall>i<k. \<not> (\<lambda>k. \<exists>c' e. d k = Some (pair e c') \<and> length(epdaH_conf_history c')\<ge>(length x)) i) \<and> (\<lambda>k. \<exists>c' e. d k = Some (pair e c') \<and> length(epdaH_conf_history c')\<ge>(length x)) k")
   apply(rename_tac x d c i e ca)(*strict*)
   prefer 2
   apply(rule ex_least_nat_le_prime)
   apply(clarsimp)
   apply(case_tac ca)
   apply(rename_tac x d c i e ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(force)
  apply(rename_tac x d c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca k c' ea)(*strict*)
  apply(case_tac k)
   apply(rename_tac x d c i e ca k c' ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e ca)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d c i e ca k c' ea nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d c i e ca c' ea nat)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="nat"
      and m="i"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac x d c i e ca c' ea nat)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac x d c i e ca c' ea nat)(*strict*)
    apply(force)
   apply(rename_tac x d c i e ca c' ea nat)(*strict*)
   apply(force)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaH_conf_history ca = (epdaH_conf_history c1)@w")
   apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
    prefer 2
    apply(rule_tac
      n="nat"
      and m="i-nat"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
      prefer 2
      apply(simp add: get_configuration_def)
     apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
     apply(rule epdaH.belongs_configurations)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaH_conf_history c' = (epdaH_conf_history c1)@w")
   apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
    prefer 2
    apply(rule_tac
      n="nat"
      and m="Suc 0"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
        apply(force)
       apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
       apply(force)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
      prefer 2
      apply(simp add: get_configuration_def)
     apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
     apply(rule epdaH.belongs_configurations)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
       apply(force)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
      apply(force)
     apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
     apply(force)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaH_conf_history ca = (epdaH_conf_history c')@w")
   apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
    prefer 2
    apply(rule_tac
      n="Suc nat"
      and m="i-Suc nat"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
        apply(force)
       apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
       apply(force)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
      prefer 2
      apply(simp add: get_configuration_def)
     apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
     apply(rule epdaH.belongs_configurations)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
       apply(force)
      apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
      apply(force)
     apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
     apply(force)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d c i e ca c' nat e1 e2 c1 w wa)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wa wb)(*strict*)
  apply(rule_tac
      x="Suc nat"
      in exI)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def valid_epda_def)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w)(*strict*)
  apply(case_tac ca)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w q h s)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w q h s epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w q h s q1 h1 s1)(*strict*)
  apply(case_tac c')
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w q h s q1 h1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb w q h s q1 h1 s1 q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb w q s h1)(*strict*)
  apply(case_tac "edge_event e2")
   apply(rename_tac x d c i e nat e1 e2 wb w q s h1)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "length x = Suc (length h1)")
   apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
   prefer 2
   apply (metis le_SucE)
  apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prefix h1 x \<or> prefix x h1")
   apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
  apply(erule disjE)
   apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb w q s h1 a)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb w q s h1 a ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac d c i e nat e1 e2 wb w q s h1 a ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb w q s h1 a ca aa list)(*strict*)
  apply(clarsimp)
  done

corollary epda_inter_semantics_language_relationship: "
  valid_epda G
  \<Longrightarrow>
  (epdaH.marked_language G \<subseteq> epdaH.unmarked_language G)
  \<and> (epdaS.marked_language G = epdaHS.marked_language G)
  \<and> (epdaHS.marked_language G = epdaH.marked_language G)
  \<and> (epdaS.unmarked_language G = epdaHS.unmarked_language G)
  \<and> (epdaHS.unmarked_language G = epdaH.unmarked_language G)
  \<and> (epdaH.unmarked_language G = prefix_closure (epdaH.unmarked_language G))"
  apply(rule context_conjI)
   apply (metis epdaH.lang_inclusion)
  apply(rule context_conjI)
   apply (metis epdaS_to_epdaHS_mlang)
  apply(rule context_conjI)
   apply (metis epdaH_to_epdaHS_mlang)
  apply(rule context_conjI)
   apply (metis epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(rule context_conjI)
   apply (metis epdaS_to_epdaH_unmarked_language)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule epda_unmarked_language_prefix_closed)
   apply(force)
  apply(simp add: Nonblockingness2_def)
  apply(rule antisym)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(force)
  done

corollary epda_inter_semantics_Nonblockingnessness_relationship: "
  valid_epda G
  \<Longrightarrow> (epdaHS.Nonblockingness_linear G \<longleftrightarrow> epdaH.Nonblockingness_branching G)
  \<and> (epdaH.Nonblockingness_branching G \<longleftrightarrow> epdaS.Nonblockingness_linear_DB G)"
  apply(rule context_conjI)
   apply (metis epdaH_vs_epdaHS.bfbra_to_bflin epdaH_vs_epdaHS.bflin_to_bfbra)
  apply(subgoal_tac "(epdaHS.Nonblockingness_linear G \<longleftrightarrow> epdaS.Nonblockingness_linear_DB G)")
   prefer 2
   apply(subgoal_tac "(epdaHS.Nonblockingness_linear_DB G \<longleftrightarrow> epdaS.Nonblockingness_linear_DB G) \<and> epdaHS.unmarked_language G = epdaS.unmarked_language G \<and> epdaHS.marked_language G = epdaS.marked_language G")
    prefer 2
    apply(rule epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer)
    apply(force)
   apply(rule_tac
      t="epdaHS.Nonblockingness_linear G"
      and s="epdaHS.Nonblockingness_linear_DB G"
      in ssubst)
    prefer 2
    apply(force)
   apply (metis epdaHS_operational_Nonblockingness_SB_DB_Restriction)
  apply(rule_tac
      t="epdaHS.Nonblockingness_linear G"
      and s="epdaS.Nonblockingness_linear_DB G"
      in ssubst)
   apply(force)
  apply(metis)
  done

definition epdaHS_accessible_edges :: "('q,'a,'b)epda \<Rightarrow> ('q,'a,'b)epda_step_label set" where
  "epdaHS_accessible_edges M \<equiv> {e\<in> (epda_delta M). \<exists>d n c. epdaHS.derivation_initial M d \<and> d n = Some (pair (Some e) c)}"

lemma epdaHS_accessible_edges_vs_epdaH_accessible_edges_1: "
  valid_epda G
  \<Longrightarrow> epdaHS_accessible_edges G \<subseteq> epdaH_accessible_edges G"
  apply(simp add: epdaHS_accessible_edges_def epdaH_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac
      x="ATS_Branching_Versus_Linear1.Lin2BraDer epdaHvHS_Lin2BraConf d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n c)(*strict*)
   apply(rule epdaH_vs_epdaHS.Lin2BraConf_preserves_initiality_lift)
    apply(rename_tac x d n c)(*strict*)
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(simp add: epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def)
  done

lemma epdaHS_accessible_edges_vs_epdaH_accessible_edges_2: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> epdaHS_accessible_edges G"
  apply(simp add: epdaHS_accessible_edges_def epdaH_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac
      x="epdaH_vs_epdaHS.Bra2LinDer G d n"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n c)(*strict*)
   apply(rule epdaH_vs_epdaHS.AX_Bra2LinConf_preserves_initiality_lift)
     apply(rename_tac x d n c)(*strict*)
     apply(force)
    apply(rename_tac x d n c)(*strict*)
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
  done

lemma epdaH_accessible_edges_vs_epdaHS_accessible_edges: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_edges G = epdaHS_accessible_edges G"
  apply (metis epdaHS_accessible_edges_vs_epdaH_accessible_edges_1 epdaHS_accessible_edges_vs_epdaH_accessible_edges_2 equalityI)
  done

lemma epdaHS_accessible_edges_vs_epdaS_accessible_edges_1: "
  valid_epda G
  \<Longrightarrow> epdaHS_accessible_edges G \<subseteq> epdaS_accessible_edges G"
  apply(simp add: epdaS_accessible_edges_def epdaHS_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac
      x="epdaHS2epdaS_derivation d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n c)(*strict*)
   apply(rule epdaHS2epdaS_derivation_preserves_derivation_initial)
    apply(rename_tac x d n c)(*strict*)
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  done

lemma epdaHS_accessible_edges_vs_epdaS_accessible_edges_2: "
  valid_epda G
  \<Longrightarrow> epdaS_accessible_edges G \<subseteq> epdaHS_accessible_edges G"
  apply(simp add: epdaS_accessible_edges_def epdaHS_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac
      x="epdaS2epdaHS_derivation G d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n c)(*strict*)
   apply(rule epdaS2epdaHS_derivation_preserves_derivation_initial)
    apply(rename_tac x d n c)(*strict*)
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(simp add: epdaS2epdaHS_derivation_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  done

lemma epdaS_accessible_edges_vs_epdaHS_accessible_edges: "
  valid_epda G
  \<Longrightarrow> epdaS_accessible_edges G = epdaHS_accessible_edges G"
  apply (metis epdaHS_accessible_edges_vs_epdaS_accessible_edges_1 epdaHS_accessible_edges_vs_epdaS_accessible_edges_2 equalityI)
  done

lemma epdaH_accessible_edges_vs_epdaS_accessible_edges: "
  valid_epda G
  \<Longrightarrow> epdaS_accessible_edges G = epdaH_accessible_edges G"
  apply (metis epdaH_accessible_edges_vs_epdaHS_accessible_edges epdaS_accessible_edges_vs_epdaHS_accessible_edges)
  done

lemma accessible_implies_accessible: "
  valid_epda G
  \<Longrightarrow> epdaS.accessible G
  \<Longrightarrow> accessible G"
  apply(simp add: accessible_def)
  apply(rule conjI)
   apply(simp add: all_states_accessible_def epdaS.accessible_def epda_destinations_def)
   apply(erule conjE)
   apply(thin_tac "edge ` epda_delta G
    \<subseteq> ATS_Destinations.get_accessible_destinations epdaS_initial_configurations
        epdaS_step_relation epda_destinations epdaS_get_destinations G")
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "state x \<in> epdaS.get_accessible_destinations G")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "state ` epda_states G
         \<subseteq> ATS_Destinations.get_accessible_destinations epdaS_initial_configurations
             epdaS_step_relation epda_destinations epdaS_get_destinations G")
   apply(simp add: epdaS.get_accessible_destinations_def epdaS_get_destinations_def)
   apply(clarsimp)
   apply(rename_tac x d i e c)(*strict*)
   apply(erule_tac disjE)
    apply(rename_tac x d i e c)(*strict*)
    prefer 2
    apply(case_tac e)
     apply(rename_tac x d i e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d i e c a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c)(*strict*)
   apply(simp add: epdaS_accessible_states_def)
   apply(rule_tac x="d" in exI)
   apply(rule conjI)
    apply(rename_tac d i e c)(*strict*)
    apply(simp add: epdaS.derivation_initial_def)
   apply(rename_tac d i e c)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e c)(*strict*)
    apply(rule_tac x="i" in exI)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac d i e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d 0")
    apply(rename_tac d i e c)(*strict*)
    apply(clarsimp)
    apply(simp add: epdaS.derivation_initial_def)
   apply(rename_tac d i e c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i e c a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c option conf)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
  apply(simp add: all_edges_accessible_def  epdaS.accessible_def epda_destinations_def)
  apply(erule conjE)
  apply(thin_tac "state ` epda_states G
    \<subseteq> ATS_Destinations.get_accessible_destinations epdaS_initial_configurations
        epdaS_step_relation epda_destinations epdaS_get_destinations G ")
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "edge x \<in> epdaS.get_accessible_destinations G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "edge ` epda_delta G
         \<subseteq> ATS_Destinations.get_accessible_destinations epdaS_initial_configurations
             epdaS_step_relation epda_destinations epdaS_get_destinations G")
  apply(simp add: epdaS.get_accessible_destinations_def epdaS_get_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a)(*strict*)
  apply(simp add: epdaS_accessible_edges_def)
  apply(rule_tac x="d" in exI)
  apply(rule conjI)
   apply(rename_tac d i c a)(*strict*)
   apply(simp add: epdaS.derivation_initial_def)
  apply(rename_tac d i c a)(*strict*)
  apply(rule_tac x="i" in exI)
  apply(clarsimp)
  done

theorem epdaH_to_epdaHS_accessible: "
  valid_epda G
  \<Longrightarrow> epdaH.accessible G
  \<Longrightarrow> epdaHS.accessible G"
  apply(simp add: epdaHS.accessible_def epdaH.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> epdaH.get_accessible_destinations G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "epda_destinations G \<subseteq> epdaH.get_accessible_destinations G")
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> epda_destinations G")
  apply(simp add: epdaHS.get_accessible_destinations_def epdaH.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: epdaH_get_destinations_def)
  apply(case_tac c)
  apply(rename_tac x d i e c epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e q h s)(*strict*)
  apply(rule_tac
      x = "epdaH_vs_epdaHS.Bra2LinDer G d i"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d i e q h s)(*strict*)
   apply(rule epdaH_vs_epdaHS.AX_Bra2LinConf_preserves_initiality_lift)
     apply(rename_tac x d i e q h s)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac x d i e q h s)(*strict*)
    apply(force)
   apply(rename_tac x d i e q h s)(*strict*)
   apply(simp add: epda_destinations_def)
  apply(rename_tac x d i e q h s)(*strict*)
  apply(rule_tac
      x = "i"
      in exI)
  apply(simp add: epdaHvHS_Bra2LinConf_def derivation_map_def epdaH_vs_epdaHS.Bra2LinDer_def epdaHS_get_destinations_def)
  done

theorem epdaHS_to_epdaS_accessible: "
  valid_epda G
  \<Longrightarrow> epdaHS.accessible G
  \<Longrightarrow> epdaS.accessible G"
  apply(simp add: epdaS.accessible_def epdaHS.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> epdaHS.get_accessible_destinations G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "epda_destinations G \<subseteq> epdaHS.get_accessible_destinations G")
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> epda_destinations G")
  apply(simp add: epdaS.get_accessible_destinations_def epdaHS.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: epdaHS_get_destinations_def)
  apply(case_tac c)
  apply(rename_tac x d i e c epdaHS_conf_statea epdaHS_conf_history epdaHS_conf_scheduler epdaHS_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n e q h i s)(*strict*)
  apply(rule_tac
      x = "epdaHS2epdaS_derivation d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n e q h i s)(*strict*)
   apply (metis epdaHS2epdaS_derivation_preserves_derivation_initial)
  apply(rename_tac x d n e q h i s)(*strict*)
  apply(rule_tac
      x = "n"
      in exI)
  apply(simp add: epdaS_get_destinations_def epdaHS2epdaS_derivation_def epdaHS_get_destinations_def)
  done

theorem accessible_vs_accessible: "
  valid_epda G
  \<Longrightarrow>
  (epdaS.accessible G \<longleftrightarrow> accessible G)
  \<and> (epdaS.accessible G \<longleftrightarrow> epdaHS.accessible G)
  \<and> (epdaHS.accessible G \<longleftrightarrow> epdaH.accessible G)"
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
    apply(rule accessible_implies_accessible)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule valid_epda_accessible_implies_accessible)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
    apply(rule epdaS_to_epdaHS_accessible)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule epdaHS_to_epdaS_accessible)
    apply(force)
   apply(force)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule epdaHS_to_epdaH_accessible)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule epdaH_to_epdaHS_accessible)
   apply(force)
  apply(force)
  done

lemma epda_box_stays_at_bottom_epdaH: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> \<exists>w. epdaH_conf_stack c = w @ [epda_box G]"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaH_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule epdaH.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G e2")
   apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
   apply(case_tac wa)
    apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i c e1 e2 c1 w)(*strict*)
    apply(subgoal_tac "edge_push e2 \<in> must_terminated_by (epda_gamma G) (epda_box G)")
     apply(rename_tac i c e1 e2 c1 w)(*strict*)
     prefer 2
     apply(rule epda_push_also_must_terminated_by)
       apply(rename_tac i c e1 e2 c1 w)(*strict*)
       apply(force)
      apply(rename_tac i c e1 e2 c1 w)(*strict*)
      apply(force)
     apply(rename_tac i c e1 e2 c1 w)(*strict*)
     apply(rule may_terminated_by_EndStrY)
      apply(rename_tac i c e1 e2 c1 w)(*strict*)
      apply(simp add: valid_epda_step_label_def)
     apply(rename_tac i c e1 e2 c1 w)(*strict*)
     apply(rule_tac
      x="w"
      in exI)
     apply(force)
    apply(rename_tac i c e1 e2 c1 w)(*strict*)
    apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
    apply(force)
   apply(rename_tac i c e1 e2 c1 w wa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
    apply(rename_tac i c e1 e2 c1 w wa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac i c e1 e2 c1 w wa a list)(*strict*)
   apply(thin_tac "wa = a # list")
   apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w wa)(*strict*)
  apply(simp add: valid_epda_def)
  done

lemma never_not_present_implies_always_present: "
  valid_simple_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> maximum_of_domain d nX
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> epdaH_conf_stack c1 = v1 @ x1 # w
  \<Longrightarrow> (\<forall>xa \<le> nX. n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> x1 # w))
  \<Longrightarrow> (\<forall>e2 c2. d (n+k) = Some (pair e2 c2) \<longrightarrow> (\<exists>v2. epdaH_conf_stack c2 = v2 @ x1 # w))"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e2 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (n+k) = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaH_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac k e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="(Suc(n+k))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac k e2 c2)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac k e2 c2)(*strict*)
    apply(force)
   apply(rename_tac k e2 c2)(*strict*)
   apply(force)
  apply(rename_tac k e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k c2 e1a e2a c1a v2)(*strict*)
  apply(subgoal_tac "\<exists>x. edge_pop e2a=[x]")
   apply(rename_tac k c2 e1a e2a c1a v2)(*strict*)
   prefer 2
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2a"
      and P="\<lambda>e2a. length (edge_pop e2a) = Suc 0"
      in ballE)
    apply(rename_tac k c2 e1a e2a c1a v2)(*strict*)
    prefer 2
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac k c2 e1a e2a c1a v2)(*strict*)
   apply(case_tac "edge_pop e2a")
    apply(rename_tac k c2 e1a e2a c1a v2)(*strict*)
    apply(force)
   apply(rename_tac k c2 e1a e2a c1a v2 a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac k c2 e1a e2a c1a v2 a list)(*strict*)
    apply(force)
   apply(rename_tac k c2 e1a e2a c1a v2 a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac k c2 e1a e2a c1a v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k c2 e1a e2a c1a v2 x)(*strict*)
  apply(simp add: valid_simple_dpda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2a"
      in ballE)
   apply(rename_tac k c2 e1a e2a c1a v2 x)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def)
  apply(rename_tac k c2 e1a e2a c1a v2 x)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
  apply(case_tac v1)
   apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="n"
      in allE)
   apply(erule impE)
    apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
    apply (rule epdaH.allPreMaxDomSome_prime)
      apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
     apply(force)
    apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
    apply(force)
   apply(rename_tac k c2 e1a e2a c1a v2 x wa)(*strict*)
   apply(force)
  apply(rename_tac k c2 e1a e2a c1a v2 x wa a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event e2a")
   apply(rename_tac k c2 e1a e2a c1a v2 x wa a list)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac k c2 e1a e2a c1a v2 x wa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac k c2 e1a e2a c1a v2 x a list)(*strict*)
    apply(case_tac v2)
     apply(rename_tac k c2 e1a e2a c1a v2 x a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
     apply(erule_tac
      x="(n+k)"
      in allE)
     apply(erule impE)
      apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
      apply (metis epdaH.allPreMaxDomSome_prime epdaH.derivation_initial_is_derivation not_None_eq)
     apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
     apply(erule impE)
      apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
      apply(force)
     apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
     apply(erule_tac
      x="e1a"
      in allE)
     apply(erule_tac
      x="c1a"
      in allE)
     apply(erule impE)
      apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
      apply(force)
     apply(rename_tac k c2 e1a e2a c1a a list)(*strict*)
     apply(force)
    apply(rename_tac k c2 e1a e2a c1a v2 x a list aa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac k c2 e1a e2a c1a x a list lista)(*strict*)
    apply(case_tac c2)
    apply(rename_tac k c2 e1a e2a c1a x a list lista epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
    apply(clarsimp)
   apply(rename_tac k c2 e1a e2a c1a v2 x wa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac k c2 e1a e2a c1a v2 x wa a list xa)(*strict*)
   apply(rule_tac
      x="xa # v2"
      in exI)
   apply(force)
  apply(rename_tac k c2 e1a e2a c1a v2 x wa a list aa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="v2"
      in exI)
  apply(force)
  done

lemma existence_of_removal: "
  valid_pda G
  \<Longrightarrow> epdaH.derivation G d
  \<Longrightarrow> epdaH.belongs G d
  \<Longrightarrow> d n1 = Some (pair e1 c1)
  \<Longrightarrow> d n2 = Some (pair e2 c2)
  \<Longrightarrow> n1 \<le> n2
  \<Longrightarrow> epdaH_conf_stack c1 = w1 @ x # w2 @ w3
  \<Longrightarrow> epdaH_conf_stack c2 = w3
  \<Longrightarrow> \<exists>n e c. d n = Some (pair e c) \<and> n1 \<le> n \<and> n \<le> n2 \<and> epdaH_conf_stack c = x # w2 @ w3"
  apply(case_tac "n1=n2")
   apply(clarsimp)
  apply(subgoal_tac "\<exists>k \<le> (n2-n1). (\<forall>i<k. \<not>(\<lambda>n. (case (derivation_drop d n1) n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> SSP c)) i) & ((\<lambda>n. (case (derivation_drop d n1) n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> SSP c)))k" for SSP)
   prefer 2
   apply(rule_tac
      P="\<lambda>c. \<not>(suffix (epdaH_conf_stack c) (x # w2@w3))"
      in epdaH.existence_of_earliest_satisfaction_point)
     apply(rule_tac
      m="n2-n1"
      in epdaH.derivation_drop_preserves_derivation_prime)
      apply(force)
     apply(force)
    apply(simp add: derivation_drop_def)
   apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(case_tac k)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
  apply(rename_tac k nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d(Suc (nat+n1))")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(simp add: suffix_def)
  apply(subgoal_tac "\<exists>k. Suc nat+k+n1=n2")
   apply(rename_tac nat option b)(*strict*)
   prefer 2
   apply(rule_tac
      x="n2-n1-Suc nat"
      in exI)
   apply(force)
  apply(rename_tac nat option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b k)(*strict*)
  apply(subgoal_tac "\<forall>i<Suc nat. \<not> case_option False (case_derivation_configuration (\<lambda>e c. \<not> epdaH_conf_stack c \<sqsupseteq> (x # w2 @ epdaH_conf_stack c2))) (d (i + n1))")
   apply(rename_tac nat option b k)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac nat option b k i)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(case_tac i)
    apply(rename_tac nat option b k i)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat option b k i nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat option b k)(*strict*)
  apply(thin_tac "\<forall>i<Suc nat. \<not> case_option False (case_derivation_configuration (\<lambda>e c. \<not> epdaH_conf_stack c \<sqsupseteq> (x # w2 @ epdaH_conf_stack c2))) (if i = 0 then case_option undefined (case_derivation_configuration (\<lambda>e c. Some (pair None c))) (d n1) else d (i + n1))")
  apply(rename_tac nat option b k)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (nat+n1) = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaH_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac nat option b k)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(nat+n1)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat option b k)(*strict*)
     apply(force)
    apply(rename_tac nat option b k)(*strict*)
    apply(force)
   apply(rename_tac nat option b k)(*strict*)
   apply(force)
  apply(rename_tac nat option b k)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b k e1a e2a c1a)(*strict*)
  apply(rule_tac
      x="nat+n1"
      in exI)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat b k e1a e2a c1a c w)(*strict*)
  apply(subgoal_tac "\<exists>x. edge_pop e2a=[x] ")
   apply(rename_tac nat b k e1a e2a c1a c w)(*strict*)
   prefer 2
   apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2a"
      in ballE)
    apply(rename_tac nat b k e1a e2a c1a c w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat b k e1a e2a c1a c w)(*strict*)
   apply(case_tac "edge_pop e2a")
    apply(rename_tac nat b k e1a e2a c1a c w)(*strict*)
    apply(force)
   apply(rename_tac nat b k e1a e2a c1a c w a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac nat b k e1a e2a c1a c w a list)(*strict*)
    apply(force)
   apply(rename_tac nat b k e1a e2a c1a c w a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat b k e1a e2a c1a c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b k e1a e2a c1a c w xa)(*strict*)
  apply(case_tac c)
   apply(rename_tac nat b k e1a e2a c1a c w xa)(*strict*)
   apply(force)
  apply(rename_tac nat b k e1a e2a c1a c w xa a list)(*strict*)
  apply(clarsimp)
  done

lemma successor_min_stack_is_not_empty: "
  valid_simple_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d (Suc n) = Some (pair (Some e2) c)
  \<Longrightarrow> maximum_of_domain d nX
  \<Longrightarrow> d n = Some (pair e1 cn)
  \<Longrightarrow> epdaH_step_relation G cn e2 c
  \<Longrightarrow> edge_event e2 = None
  \<Longrightarrow> edge_pop e2 = [x]
  \<Longrightarrow> edge_push e2 = [xa, x]
  \<Longrightarrow> Some q2 = min_stack d (tl (epdaH_conf_stack cn)) n nX
  \<Longrightarrow> min_stack d (tl (epdaH_conf_stack c)) (Suc n) nX = None
  \<Longrightarrow> P"
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: min_stack_def)
  apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> w)")
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(rename_tac xb e ca)(*strict*)
  apply(case_tac "\<forall>xa \<le> nX. Suc n \<le> xa \<longrightarrow> (\<forall>e c. d xa = Some (pair e c) \<longrightarrow> epdaH_conf_stack c \<noteq> x # epdaH_conf_stack ca)")
   apply(rename_tac xb e ca)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac xb e ca)(*strict*)
  apply(clarsimp)
  apply(case_tac "n=xb")
   apply(rename_tac xb e ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac xb e ca)(*strict*)
  apply(case_tac "Suc n=xb")
   apply(rename_tac xb e ca)(*strict*)
   apply(clarify)
   apply(case_tac c)
   apply(rename_tac xb e ca epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac cn)
   apply(rename_tac xb e ca epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(case_tac ca)
   apply(rename_tac xb e ca epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa epdaH_conf_stateb epdaH_conf_historyb epdaH_conf_stackb)(*strict*)
   apply(clarsimp)
  apply(rename_tac xb e ca)(*strict*)
  apply(subgoal_tac "\<exists>k e c. d k= Some (pair e c) \<and> Suc n \<le> k \<and> k \<le> xb \<and> epdaH_conf_stack c=x # []@(epdaH_conf_stack ca)")
   apply(rename_tac xb e ca)(*strict*)
   prefer 2
   apply(rule existence_of_removal)
          apply(rename_tac xb e ca)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def)
          apply(force)
         apply(rename_tac xb e ca)(*strict*)
         apply(rule epdaH.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac xb e ca)(*strict*)
        apply(rule epdaH.derivation_initial_belongs)
         apply(rename_tac xb e ca)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac xb e ca)(*strict*)
        apply(force)
       apply(rename_tac xb e ca)(*strict*)
       apply(force)
      apply(rename_tac xb e ca)(*strict*)
      apply(force)
     apply(rename_tac xb e ca)(*strict*)
     apply(force)
    apply(rename_tac xb e ca)(*strict*)
    apply(force)
   apply(rename_tac xb e ca)(*strict*)
   apply(force)
  apply(rename_tac xb e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac xb e ca k ea caa)(*strict*)
  apply(erule_tac
      x="k"
      in allE)
  apply(clarsimp)
  done

lemma min_stack_is_in_states: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> maximum_of_domain d nX
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> min_stack d (tl (epdaH_conf_stack c)) n nX = Some qs
  \<Longrightarrow> qs \<in> epda_states G"
  apply(simp add: min_stack_def)
  apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e ca. d x = Some (pair e ca) \<longrightarrow> epdaH_conf_stack ca \<noteq> tl (epdaH_conf_stack c))")
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e cx. d (Min ({ i. (n \<le> i \<and> i \<le> nX \<and> (\<exists>e cx. d i = Some (pair e cx) \<and> epdaH_conf_stack cx = tl (epdaH_conf_stack c)))})) = Some (pair e cx)")
   apply(rename_tac x ea ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac x ea ca eaa cx)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "cx \<in> epdaH_configurations G")
    apply(rename_tac x ea ca eaa cx)(*strict*)
    apply(simp add: epdaH_configurations_def)
    apply(clarsimp)
   apply(rename_tac x ea ca eaa cx)(*strict*)
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac x ea ca eaa cx)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac x ea ca eaa cx)(*strict*)
     apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
    apply(rename_tac x ea ca eaa cx)(*strict*)
    apply(force)
   apply(rename_tac x ea ca eaa cx)(*strict*)
   apply(force)
  apply(rename_tac x ea ca)(*strict*)
  apply(rule_tac
      m="x"
      in epdaH.pre_some_position_is_some_position)
    apply(rename_tac x ea ca)(*strict*)
    apply(rule epdaH.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac x ea ca)(*strict*)
   apply(force)
  apply(rename_tac x ea ca)(*strict*)
  apply(rule Min_le)
   apply(rename_tac x ea ca)(*strict*)
   apply(rule_tac
      B="{i. n \<le> i \<and> i \<le> nX}"
      in finite_subset)
    apply(rename_tac x ea ca)(*strict*)
    apply(force)
   apply(rename_tac x ea ca)(*strict*)
   apply (metis finite_Collect_conjI finite_Collect_le_nat)
  apply(rename_tac x ea ca)(*strict*)
  apply(clarsimp)
  done

lemma min_stack_preserved1: "
  valid_simple_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d (Suc n) = Some (pair e2 c2)
  \<Longrightarrow> maximum_of_domain d nX
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> epdaH_conf_stack c1 \<noteq> wb
  \<Longrightarrow> epdaH_conf_stack c2 \<noteq> wb
  \<Longrightarrow> Some q2 = min_stack d wb n nX
  \<Longrightarrow> min_stack d wb n nX = min_stack d wb (Suc n) nX"
  apply(simp add: min_stack_def)
  apply(clarsimp)
  apply(rename_tac x e c)(*strict*)
  apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e ca. d x = Some (pair e ca) \<longrightarrow> epdaH_conf_stack ca \<noteq> epdaH_conf_stack c)")
   apply(rename_tac x e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e c xa ea ca)(*strict*)
  apply(case_tac "x=n")
   apply(rename_tac x e c xa ea ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac x e c xa ea ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac x e c xa ea ca)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(clarsimp)
  apply(rename_tac x e c xa ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e c xa ea ca xb eb cb)(*strict*)
  apply(rule_tac
      f="\<lambda>x. epdaH_conf_state (the (get_configuration (d (Min x))))"
      in HOL.arg_cong)
  apply(rename_tac x e c xa ea ca xb eb cb)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac x e c xa ea ca xb eb cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac x e c xa ea ca xb eb cb xc ec cc)(*strict*)
   apply(case_tac "xc=n")
    apply(rename_tac x e c xa ea ca xb eb cb xc ec cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac x e c xa ea ca xb eb cb xc ec cc)(*strict*)
   apply(force)
  apply(rename_tac x e c xa ea ca xb eb cb)(*strict*)
  apply(clarsimp)
  done

lemma min_stack_preserved2: "
  valid_simple_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d (Suc n) = Some (pair e2 c2)
  \<Longrightarrow> maximum_of_domain d nX
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> epdaH_conf_stack c1 \<noteq> wb
  \<Longrightarrow> epdaH_conf_stack c2 \<noteq> wb
  \<Longrightarrow> None = min_stack d wb n nX
  \<Longrightarrow> min_stack d wb n nX = min_stack d wb (Suc n) nX"
  apply(simp add: min_stack_def)
  apply(clarsimp)
  apply(rename_tac x e c)(*strict*)
  apply(case_tac "\<forall>x \<le> nX. n \<le> x \<longrightarrow> (\<forall>e ca. d x = Some (pair e ca) \<longrightarrow> epdaH_conf_stack ca \<noteq> epdaH_conf_stack c)")
   apply(rename_tac x e c)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac x e c)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in allE)
  apply(force)
  done

lemma min_stack_preserved: "
  valid_simple_dpda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d (Suc n) = Some (pair e2 c2)
  \<Longrightarrow> maximum_of_domain d nX
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> epdaH_conf_stack c1 \<noteq> wb
  \<Longrightarrow> epdaH_conf_stack c2 \<noteq> wb
  \<Longrightarrow> min_stack d wb n nX = min_stack d wb (Suc n) nX"
  apply(case_tac "min_stack d wb n nX")
   apply(rule min_stack_preserved2)
          apply(force)+
  apply(rename_tac a)(*strict*)
  apply(rule min_stack_preserved1)
         apply(rename_tac a)(*strict*)
         apply(force)+
  done

lemma valid_pda_edge_pop_single: "
  valid_pda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> \<exists>x. edge_pop e = [x]"
  apply(simp add: valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   prefer 2
   apply(force)
  apply(case_tac "edge_pop e")
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_unused_stack_modification_preserves_derivation2: "
  valid_pda G
  \<Longrightarrow> epdaS.derivation G d
  \<Longrightarrow> epdaS.belongs G d
  \<Longrightarrow> \<forall>k \<le> j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ aa # s)
  \<Longrightarrow> epdaS.derivation G (derivation_map (derivation_take d j) (\<lambda>c. c\<lparr>epdaS_conf_stack := butn (epdaS_conf_stack c) (length s) @ s'\<rparr>))"
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(clarsimp)
   apply (rule epdaS.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def)
  apply(clarsimp)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "\<forall>e c. d nat = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ aa # s)")
   apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
   apply(subgoal_tac "\<forall>e c. d (Suc nat) = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ aa # s)")
    apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 w wa)(*strict*)
    apply(simp add: butn_def)
    apply(subgoal_tac "\<exists>x. edge_pop e2 = [x]")
     apply(rename_tac nat e1 e2 c1 c2 w wa)(*strict*)
     prefer 2
     apply(rule valid_pda_edge_pop_single)
      apply(rename_tac nat e1 e2 c1 c2 w wa)(*strict*)
      apply(simp add: valid_simple_dpda_def valid_dpda_def)
     apply(rename_tac nat e1 e2 c1 c2 w wa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 w wa x)(*strict*)
    apply(case_tac wa)
     apply(rename_tac nat e1 e2 c1 c2 w wa x)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 w wa x a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(force)
  done

lemma F_SDPDA_TO_CFG_STD__minimal_stack_does_not_occur: "
  valid_simple_dpda G
  \<Longrightarrow> epdaS.derivation G d
  \<Longrightarrow> d (Suc k) \<noteq> None
  \<Longrightarrow> i < Suc k
  \<Longrightarrow> \<forall>i < Suc k. epdaS_conf_stack (the (get_configuration (d (Suc i)))) \<noteq> A # s
  \<Longrightarrow> epdaS_conf_stack (the (get_configuration (d (Suc 0)))) = w @ B # A # s
  \<Longrightarrow> \<exists>w. epdaS_conf_stack (the (get_configuration (d (Suc i)))) = w @ B # A # s"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i wa y)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (Suc i) = Some (pair e1 c1) \<and> d (Suc (Suc i)) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac i wa y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc k"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac i wa y)(*strict*)
     apply(force)
    apply(rename_tac i wa y)(*strict*)
    apply(force)
   apply(rename_tac i wa y)(*strict*)
   apply(force)
  apply(rename_tac i wa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac i wa y e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
  apply(simp add: valid_simple_dpda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
  apply(subgoal_tac "\<exists>x. edge_pop e2=[x]")
   apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
   apply(case_tac "edge_event e2")
    apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
    prefer 2
    apply(rename_tac i wa y e1 e2 c1 c2 waa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac i wa y e1 e2 c1 c2 waa a x)(*strict*)
    apply(rule_tac
      x="wa"
      in exI)
    apply(force)
   apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i wa y e1 e2 c1 c2 waa x)(*strict*)
   apply(erule disjE)
    apply(rename_tac i wa y e1 e2 c1 c2 waa x)(*strict*)
    apply(clarsimp)
    apply(rename_tac i wa y e1 e2 c1 c2 x)(*strict*)
    apply(case_tac wa)
     apply(rename_tac i wa y e1 e2 c1 c2 x)(*strict*)
     apply(force)
    apply(rename_tac i wa y e1 e2 c1 c2 x a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac i y e1 e2 c1 c2 x list)(*strict*)
    apply(rule_tac
      x="list"
      in exI)
    apply(force)
   apply(rename_tac i wa y e1 e2 c1 c2 waa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac i wa y e1 e2 c1 c2 waa x xa)(*strict*)
   apply(rule_tac
      x="xa # wa"
      in exI)
   apply(force)
  apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
  apply(rule_tac
      G="G"
      in valid_pda_edge_pop_single)
   apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
   apply(simp add: valid_dpda_def)
  apply(rename_tac i wa y e1 e2 c1 c2 waa)(*strict*)
  apply(force)
  done

lemma epdaS_unused_stack_modification_preserves_derivation: "
  valid_pda G
  \<Longrightarrow> epdaS.derivation G d1
  \<Longrightarrow> epdaS.belongs G d1
  \<Longrightarrow> maximum_of_domain d1 (Suc j)
  \<Longrightarrow> d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # s\<rparr>)
  \<Longrightarrow> \<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)
  \<Longrightarrow> d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)
  \<Longrightarrow> epdaS.derivation G (derivation_map d1 (\<lambda>c. c\<lparr>epdaS_conf_stack := butn (epdaS_conf_stack c) (length s) @ A # sa\<rparr>))"
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d1 (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 nat = Some (pair e1 c1) \<and> d1 (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  apply(subgoal_tac "Suc nat \<le> Suc j")
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(\<forall>e c. d1 nat = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s))")
    apply(rename_tac nat e1 e2 c1 c2)(*strict*)
    apply(erule_tac
      x="e1"
      in allE)
    apply(erule_tac
      x="c1"
      in allE)
    apply(erule impE)
     apply(rename_tac nat e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2)(*strict*)
    apply(erule exE)+
    apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
    apply(rule_tac
      t="butn (epdaS_conf_stack c1) (length s)"
      and s="w @ [B]"
      in ssubst)
     apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
     apply(simp add: butn_def)
    apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. epdaS_conf_stack c2 = w @ s")
     apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 w wa)(*strict*)
     apply(simp add: butn_def)
     apply(simp add: epdaS_step_relation_def)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 w wa wb)(*strict*)
     apply(subgoal_tac "\<exists>x. edge_pop e2=[x]")
      apply(rename_tac nat e1 e2 c1 c2 w wa wb)(*strict*)
      apply(clarsimp)
      apply(rename_tac nat e1 e2 c1 c2 w wa wb x)(*strict*)
      apply(case_tac w)
       apply(rename_tac nat e1 e2 c1 c2 w wa wb x)(*strict*)
       apply(clarsimp)
      apply(rename_tac nat e1 e2 c1 c2 w wa wb x a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 w wa wb)(*strict*)
     apply(rule_tac
      G="G"
      in valid_pda_edge_pop_single)
      apply(rename_tac nat e1 e2 c1 c2 w wa wb)(*strict*)
      apply(simp add: valid_dpda_def)
     apply(rename_tac nat e1 e2 c1 c2 w wa wb)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
    apply(case_tac "nat=j")
     apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
    apply(erule_tac
      x="Suc nat"
      in allE)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply (metis epdaS.allPreMaxDomSome_prime not_None_eq)
  done

lemma epdaS_produce_from_before_pop_append: "
  valid_pda G
  \<Longrightarrow> \<lparr>edge_src = src, edge_event = None, edge_pop = [A], edge_push = [B, A], edge_trg = trg\<rparr> \<in> epda_delta G
  \<Longrightarrow> x1 \<in> epdaS_produce_from_before_pop G trg B qs
  \<Longrightarrow> x2 \<in> epdaS_produce_from_before_pop G qs A qt
  \<Longrightarrow> x1 @ x2 \<in> epdaS_produce_from_before_pop G src A qt"
  apply(simp add: epdaS_produce_from_before_pop_def)
  apply(clarsimp)
  apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
  apply(subgoal_tac "\<exists>d1. epdaS.derivation G d1 \<and> epdaS.belongs G d1 \<and> maximum_of_domain d1 (Suc j) \<and> d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # s\<rparr>) \<and> d1 j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # s\<rparr>) \<and> (\<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)) \<and> d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>) ")
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d (Suc j)"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(rule epdaS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(rule epdaS.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event k eb c)(*strict*)
    apply(erule_tac
      x="k"
      and P="\<lambda>x. x \<le> j \<longrightarrow> (\<forall>e c. d x = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s))"
      in allE)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event k eb c)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
  apply(subgoal_tac "\<exists>d2. epdaS.derivation G d2 \<and> epdaS.belongs G d2 \<and> maximum_of_domain d2 (Suc ja) \<and> d2 0 = Some (pair None \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = x2, epdaS_conf_stack = A # sa\<rparr>) \<and> d2 ja = Some (pair ea \<lparr>epdaS_conf_state = qa, epdaS_conf_scheduler = [], epdaS_conf_stack = A # sa\<rparr>) \<and> (\<forall>k \<le> ja. \<forall>e c. d2 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa)) \<and> d2 (Suc ja) = Some (pair e'event \<lparr>epdaS_conf_state = qt, epdaS_conf_scheduler = [], epdaS_conf_stack = sa\<rparr>) ")
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take da (Suc ja)"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(rule epdaS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(rule epdaS.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da q s qa sa j ja e ea e' e'event d1 k eb c)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da q s qa sa j ja e ea e' e'event)(*strict*)
  apply(thin_tac "epdaS.derivation G d")
  apply(thin_tac "epdaS.derivation G da")
  apply(thin_tac "epdaS.belongs G d")
  apply(thin_tac "epdaS.belongs G da")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # s\<rparr>)")
  apply(thin_tac "da 0 = Some (pair None \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = x2, epdaS_conf_stack = A # sa\<rparr>)")
  apply(thin_tac "d j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # s\<rparr>)")
  apply(thin_tac "da ja = Some (pair ea \<lparr>epdaS_conf_state = qa, epdaS_conf_scheduler = [], epdaS_conf_stack = A # sa\<rparr>)")
  apply(thin_tac "\<forall>k \<le> j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)")
  apply(thin_tac "d (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)")
  apply(thin_tac "\<forall>k \<le> ja. \<forall>e c. da k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa)")
  apply(thin_tac "da (Suc ja) = Some (pair e'event \<lparr>epdaS_conf_state = qt, epdaS_conf_scheduler = [], epdaS_conf_stack = sa\<rparr>)")
  apply(clarsimp)
  apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
  apply(subgoal_tac "\<exists>d1. epdaS.derivation G d1 \<and> epdaS.belongs G d1 \<and> maximum_of_domain d1 (Suc j) \<and> d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # A # sa\<rparr>) \<and> d1 j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # A # sa\<rparr>) \<and> (\<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # A # sa)) \<and> d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = A # sa\<rparr>) ")
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map d1 (\<lambda>c. c\<lparr>epdaS_conf_stack := butn (epdaS_conf_stack c) (length s) @ (A # sa)\<rparr>)"
      in exI)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(rule epdaS_unused_stack_modification_preserves_derivation)
          apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
          apply(force)
         apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
         apply(force)
        apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
        apply(force)
       apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
       apply(force)
      apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
      apply(force)
     apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
     apply(force)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(force)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(rule conjI)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
       apply(simp add: valid_pda_def)
      apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
      apply(simp add: derivation_map_def)
     apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
     apply(simp add: butn_def)
     apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # s\<rparr> \<in> epdaS_configurations G")
      apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
      apply(subgoal_tac "\<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = x2, epdaS_conf_stack = A # sa\<rparr> \<in> epdaS_configurations G")
       apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
       apply(simp add: epdaS_configurations_def)
      apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
      apply(rule_tac
      d="d2"
      in epdaS.belongs_configurations)
       apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
       apply(force)
      apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
      apply(force)
     apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
     apply(rule_tac
      d="d1"
      in epdaS.belongs_configurations)
      apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
      apply(force)
     apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
     apply(force)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(force)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(rule conjI)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(rule conjI)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(simp add: derivation_map_def butn_def)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(rule conjI)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(simp add: derivation_map_def butn_def)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(rule conjI)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2 k eb c)(*strict*)
    apply(erule_tac
      x="k"
      and P="\<lambda>x. x \<le> j \<longrightarrow> (\<forall>e c. d1 x = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s))"
      in allE)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2 k eb c)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_map_def butn_def)
    apply(case_tac "d1 k")
     apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2 k eb c)(*strict*)
     apply(clarsimp)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2 k eb c a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2 k eb c a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
   apply(simp add: derivation_map_def butn_def)
  apply(rename_tac q s qa sa j ja e ea e' e'event d1 d2)(*strict*)
  apply(thin_tac "epdaS.derivation G d1")
  apply(thin_tac "epdaS.belongs G d1")
  apply(thin_tac "maximum_of_domain d1 (Suc j)")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # s\<rparr>)")
  apply(thin_tac "d1 j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # s\<rparr>)")
  apply(thin_tac "\<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)")
  apply(thin_tac "d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)")
  apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = x1 @ x2, epdaS_conf_stack = A # sa\<rparr> \<lparr>edge_src = src, edge_event = None, edge_pop = [A], edge_push = [B, A], edge_trg = trg\<rparr> \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1 @ x2, epdaS_conf_stack = B # A # sa\<rparr>) (derivation_append (derivation_map d1 (\<lambda>c. c\<lparr>epdaS_conf_scheduler := take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = A # sa\<rparr>)) (epdaS_conf_scheduler c) @ x2\<rparr>)) d2 (Suc j)) (Suc 0)"
      in exI)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(rule epdaS.derivation_append_preserves_derivation)
     apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def)
     apply(simp add: option_to_list_def)
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation)
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(rule epda_maximal_context_preserves_derivation_prime)
            apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
            apply(simp add: valid_pda_def)
           apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
           apply(force)
          apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
          apply(force)
         apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
         apply(force)
        apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
        apply(force)
       apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
       apply(force)
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(force)
     apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
     apply(force)
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(rule conjI)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(rule_tac
      ca="\<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = x1 @ x2, epdaS_conf_stack = A # sa\<rparr>"
      in epdaS.derivation_belongs)
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(simp add: valid_pda_def)
     apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
     apply(simp add: der2_def derivation_append_def derivation_map_def)
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G \<lparr>edge_src = src, edge_event = None, edge_pop = [A], edge_push = [B, A], edge_trg = trg\<rparr>")
     apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
     apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = x1, epdaS_conf_stack = B # A # sa\<rparr> \<in> epdaS_configurations G")
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(subgoal_tac "\<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = x2, epdaS_conf_stack = A # sa\<rparr> \<in> epdaS_configurations G")
       apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
       apply(simp add: epdaS_configurations_def valid_epda_step_label_def)
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(rule_tac
      d="d2"
      in epdaS.belongs_configurations)
       apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
       apply(force)
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(force)
     apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
     apply(rule_tac
      d="d1"
      in epdaS.belongs_configurations)
      apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
      apply(force)
     apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
     apply(force)
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
    apply(simp add: valid_pda_def valid_epda_def)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(rule_tac
      x="qa"
      in exI)
  apply(rule_tac
      x="sa"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(rule_tac
      x="Suc j+ja+Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(rule_tac
      x="if ja=0 then e' else ea"
      in exI)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
   apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(rule conjI)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 k eb c)(*strict*)
  apply(case_tac k)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 k eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
   apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 k eb c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
  apply(case_tac "nat \<le> j")
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="nat"
      and P="\<lambda>nat. nat \<le> j \<longrightarrow> (\<forall>e c. d1 nat = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # A # sa))"
      in allE)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
   apply(case_tac nat)
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nata)(*strict*)
   apply(case_tac "d1 (Suc nata)")
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nata a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nata a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
  apply(case_tac "Suc nat=j")
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(case_tac "nat \<le> Suc j")
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat=Suc j")
    apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="nat - Suc j"
      and P="\<lambda>x. x \<le> ja \<longrightarrow> (\<forall>e c. d2 x = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa))"
      in allE)
  apply(rename_tac q qa sa j ja e ea e' e'event d2 d1 eb c nat)(*strict*)
  apply(clarsimp)
  done

definition epdaS_produce_and_eliminate_from :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'stack
  \<Rightarrow> 'event list set"
  where
    "epdaS_produce_and_eliminate_from G qi A \<equiv>
  {w. \<exists>d qf s.
  qf \<in> epda_marking G
  \<and> epdaS.derivation G d
  \<and> epdaS.belongs G d
  \<and> d 0 = Some (pair None
      \<lparr>epdaS_conf_state = qi,
      epdaS_conf_scheduler = w,
      epdaS_conf_stack = A # s\<rparr>)
  \<and> (\<exists>j e s'.
    d j = Some (pair e
          \<lparr>epdaS_conf_state = qf,
          epdaS_conf_scheduler = [],
          epdaS_conf_stack = s' @ A # s\<rparr>)
    \<and> (\<forall>k \<le> j. \<forall>e c.
        d k = Some (pair e c)
        \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ [A] @ s)))}"

lemma epdaS_produce_and_eliminate_from_Cons: "
  valid_epda G
  \<Longrightarrow> \<lparr>edge_src = src, edge_event = Some a, edge_pop = [y], edge_push = [y], edge_trg = trg\<rparr> \<in> epda_delta G
  \<Longrightarrow> w \<in> epdaS_produce_and_eliminate_from G trg y
  \<Longrightarrow> a # w \<in> epdaS_produce_and_eliminate_from G src y"
  apply(simp add: epdaS_produce_and_eliminate_from_def)
  apply(clarsimp)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = a # w, epdaS_conf_stack = y # s\<rparr> \<lparr>edge_src = src, edge_event = Some a, edge_pop = [y], edge_push = [y], edge_trg = trg\<rparr> \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = y # s\<rparr>) d (Suc 0)"
      in exI)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(rule_tac
      x="qf"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(rule epdaS.derivation_append_preserves_derivation)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def option_to_list_def)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(force)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(rule conjI)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac d qf s j e s')(*strict*)
      apply(force)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = y # s\<rparr> \<in> epdaS_configurations G")
     apply(rename_tac d qf s j e s')(*strict*)
     apply(subgoal_tac "valid_epda_step_label G \<lparr>edge_src = src, edge_event = Some a, edge_pop = [y], edge_push = [y], edge_trg = trg\<rparr>")
      apply(rename_tac d qf s j e s')(*strict*)
      apply(simp add: epdaS_configurations_def valid_epda_step_label_def option_to_set_def)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(simp add: valid_epda_def)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(rule epdaS.belongs_configurations)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(force)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(force)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(force)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(rule_tac
      x="s"
      in exI)
  apply(rule conjI)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(rule_tac
      x="Suc j"
      in exI)
  apply(rule conjI)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(clarsimp)
  apply(rename_tac d qf s j e s' k ea c)(*strict*)
  apply(case_tac k)
   apply(rename_tac d qf s j e s' k ea c)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac d qf s j e s' k ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d qf s j e s' ea c nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac nat)
   apply(rename_tac d qf s j e s' ea c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d qf s j e s' ea c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_produce_and_eliminate_from_Cons2: "
  valid_pda G
  \<Longrightarrow> \<lparr>edge_src = src, edge_event = None, edge_pop = [y], edge_push = [aa, y], edge_trg = trg\<rparr> \<in> epda_delta G
  \<Longrightarrow> w \<in> epdaS_produce_and_eliminate_from G trg aa
  \<Longrightarrow> w \<in> epdaS_produce_and_eliminate_from G src y"
  apply(simp add: epdaS_produce_and_eliminate_from_def)
  apply(clarsimp)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(subgoal_tac "\<exists>d. epdaS.derivation G d \<and> epdaS.belongs G d \<and> maximum_of_domain d j \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = aa # y # s\<rparr>) \<and> (\<forall>k \<le> j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ aa # y # s)) \<and> d j = Some (pair e \<lparr>epdaS_conf_state = qf, epdaS_conf_scheduler = [], epdaS_conf_stack = s' @ aa # y # s\<rparr>) ")
   apply(rename_tac d qf s j e s')(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map (derivation_take d j) (\<lambda>c. c\<lparr>epdaS_conf_stack := butn (epdaS_conf_stack c) (length s) @ y # s\<rparr>)"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(rule epdaS_unused_stack_modification_preserves_derivation2)
       apply(rename_tac d qf s j e s')(*strict*)
       apply(force)
      apply(rename_tac d qf s j e s')(*strict*)
      apply(force)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(force)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(force)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac d qf s j e s')(*strict*)
       apply(simp add: valid_pda_def)
      apply(rename_tac d qf s j e s')(*strict*)
      apply(simp add: derivation_map_def derivation_take_def)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(simp add: butn_def)
     apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = aa # s\<rparr> \<in> epdaS_configurations G")
      apply(rename_tac d qf s j e s')(*strict*)
      apply(subgoal_tac "valid_epda_step_label G \<lparr>edge_src = src, edge_event = None, edge_pop = [y], edge_push = [aa, y], edge_trg = trg\<rparr>")
       apply(rename_tac d qf s j e s')(*strict*)
       apply(simp add: valid_epda_step_label_def epdaS_configurations_def)
       apply(rule_tac
      w="[y]"
      in may_terminated_by_decompose2)
         apply(rename_tac d qf s j e s')(*strict*)
         apply(force)
        apply(rename_tac d qf s j e s')(*strict*)
        apply(force)
       apply(rename_tac d qf s j e s')(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac d qf s j e s')(*strict*)
      apply(simp add: valid_pda_def valid_epda_def)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(rule epdaS.belongs_configurations)
      apply(rename_tac d qf s j e s')(*strict*)
      apply(force)
     apply(rename_tac d qf s j e s')(*strict*)
     apply(force)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(force)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(simp add: derivation_map_def derivation_take_def)
    apply(simp add: butn_def)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d qf s j e s')(*strict*)
    apply(clarsimp)
    apply(rename_tac d qf s j e s' k ea c)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def)
    apply(erule_tac
      x="k"
      in allE)
    apply(clarsimp)
    apply(case_tac "d k")
     apply(rename_tac d qf s j e s' k ea c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d qf s j e s' k ea c a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac d qf s j e s' k ea c a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d qf s j e s' k ea b wa)(*strict*)
    apply(simp add: butn_def)
   apply(rename_tac d qf s j e s')(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(simp add: butn_def)
  apply(rename_tac d qf s j e s')(*strict*)
  apply(thin_tac "epdaS.derivation G d")
  apply(thin_tac "epdaS.belongs G d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = aa # s\<rparr>)")
  apply(thin_tac "\<forall>k \<le> j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ aa # s)")
  apply(thin_tac "d j = Some (pair e \<lparr>epdaS_conf_state = qf, epdaS_conf_scheduler = [], epdaS_conf_stack = s' @ aa # s\<rparr>)")
  apply(clarsimp)
  apply(rename_tac qf s j e s' d)(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = w, epdaS_conf_stack = y # s\<rparr> \<lparr>edge_src = src, edge_event = None, edge_pop = [y], edge_push = [aa, y], edge_trg = trg\<rparr> \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = aa # y # s\<rparr>) d (Suc 0)"
      in exI)
  apply(rename_tac qf s j e s' d)(*strict*)
  apply(rule_tac
      x="qf"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac qf s j e s' d)(*strict*)
   apply(rule epdaS.derivation_append_preserves_derivation)
     apply(rename_tac qf s j e s' d)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def option_to_list_def)
    apply(rename_tac qf s j e s' d)(*strict*)
    apply(force)
   apply(rename_tac qf s j e s' d)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac qf s j e s' d)(*strict*)
  apply(rule conjI)
   apply(rename_tac qf s j e s' d)(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac qf s j e s' d)(*strict*)
      apply(simp add: valid_pda_def)
     apply(rename_tac qf s j e s' d)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac qf s j e s' d)(*strict*)
    apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = w, epdaS_conf_stack = aa # y # s\<rparr> \<in> epdaS_configurations G")
     apply(rename_tac qf s j e s' d)(*strict*)
     apply(subgoal_tac "valid_epda_step_label G \<lparr>edge_src = src, edge_event = None, edge_pop = [y], edge_push = [aa, y], edge_trg = trg\<rparr>")
      apply(rename_tac qf s j e s' d)(*strict*)
      apply(simp add: valid_epda_step_label_def epdaS_configurations_def)
     apply(rename_tac qf s j e s' d)(*strict*)
     apply(simp add: valid_pda_def valid_epda_def)
    apply(rename_tac qf s j e s' d)(*strict*)
    apply(rule epdaS.belongs_configurations)
     apply(rename_tac qf s j e s' d)(*strict*)
     apply(force)
    apply(rename_tac qf s j e s' d)(*strict*)
    apply(force)
   apply(rename_tac qf s j e s' d)(*strict*)
   apply(force)
  apply(rename_tac qf s j e s' d)(*strict*)
  apply(rule_tac
      x="s"
      in exI)
  apply(rule conjI)
   apply(rename_tac qf s j e s' d)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac qf s j e s' d)(*strict*)
  apply(rule_tac
      x="Suc j"
      in exI)
  apply(rule conjI)
   apply(rename_tac qf s j e s' d)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac qf s j e s' d)(*strict*)
  apply(clarsimp)
  apply(rename_tac qf s j e s' d k ea c)(*strict*)
  apply(case_tac k)
   apply(rename_tac qf s j e s' d k ea c)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac qf s j e s' d k ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac qf s j e s' d ea c nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac nat)
   apply(rename_tac qf s j e s' d ea c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac qf s j e s' d ea c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_produce_and_eliminate_from_epdaS_produce_from_before_pop_append: "
  valid_simple_dpda G
  \<Longrightarrow> \<lparr>edge_src = src, edge_event = None, edge_pop = [A], edge_push = [B, A], edge_trg = trg\<rparr> \<in> epda_delta G
  \<Longrightarrow> r' \<in> epdaS_produce_and_eliminate_from G qs A
  \<Longrightarrow> l' \<in> epdaS_produce_from_before_pop G trg B qs
  \<Longrightarrow> l' @ r' \<in> epdaS_produce_and_eliminate_from G src A"
  apply(simp add: epdaS_produce_and_eliminate_from_def epdaS_produce_from_before_pop_def)
  apply(clarsimp)
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(subgoal_tac "\<exists>d1. epdaS.derivation G d1 \<and> epdaS.belongs G d1 \<and> maximum_of_domain d1 (Suc j) \<and> d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l', epdaS_conf_stack = B # s\<rparr>) \<and> d1 j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # s\<rparr>) \<and> (\<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)) \<and> d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>) ")
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take da (Suc j)"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(rule epdaS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(rule epdaS.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(clarsimp)
    apply(rename_tac d da qf q s j sa e ja e' ea s' k eb c)(*strict*)
    apply(erule_tac
      x="k"
      and P="\<lambda>k. k \<le> j \<longrightarrow> (\<forall>e c. da k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s))"
      in allE)
    apply(rename_tac d da qf q s j sa e ja e' ea s' k eb c)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(thin_tac "epdaS.belongs G da")
  apply(thin_tac " da 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l', epdaS_conf_stack = B # s\<rparr>)")
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(thin_tac " da j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # s\<rparr>)")
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(thin_tac " \<forall>k \<le> j. \<forall>e c. da k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)")
  apply(thin_tac " da (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)")
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(subgoal_tac "\<exists>d2. epdaS.derivation G d2 \<and> epdaS.belongs G d2 \<and> maximum_of_domain d2 ja \<and> d2 0 = Some (pair None \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = r', epdaS_conf_stack = A # sa\<rparr>) \<and> d2 ja = Some (pair ea \<lparr>epdaS_conf_state = qf, epdaS_conf_scheduler = [], epdaS_conf_stack = s' @A # sa\<rparr>) \<and> (\<forall>k \<le> ja. \<forall>e c. d2 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa)) ")
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d ja"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(rule epdaS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(rule epdaS.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(rule conjI)
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(clarsimp)
   apply(rename_tac d da qf q s j sa e ja e' ea s' d1 k eb c)(*strict*)
   apply(erule_tac
      x="k"
      and P="\<lambda>k. k \<le> ja \<longrightarrow> (\<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa))"
      in allE)
   apply(rename_tac d da qf q s j sa e ja e' ea s' d1 k eb c)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(thin_tac "epdaS.derivation G d")
  apply(thin_tac " epdaS.belongs G d")
  apply(thin_tac " d 0 = Some (pair None \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = r', epdaS_conf_stack = A # sa\<rparr>)")
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(thin_tac " \<forall>k \<le> ja. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa)")
  apply(thin_tac " d ja = Some (pair ea \<lparr>epdaS_conf_state = qf, epdaS_conf_scheduler = [], epdaS_conf_stack = s' @ A # sa\<rparr>)")
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(subgoal_tac "\<exists>d1. epdaS.derivation G d1 \<and> epdaS.belongs G d1 \<and> maximum_of_domain d1 (Suc j) \<and> d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l', epdaS_conf_stack = B # A # sa\<rparr>) \<and> d1 j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # A # sa\<rparr>) \<and> (\<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # A # sa)) \<and> d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = A # sa\<rparr>) ")
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   prefer 2
   apply(subgoal_tac "\<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = r', epdaS_conf_stack = A # sa\<rparr> \<in> epdaS_configurations G")
    apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac da qf q s j sa e ja e' ea s' d1 d2)(*strict*)
    apply(rule_tac
      d="d2"
      in epdaS.belongs_configurations)
     apply(rename_tac da qf q s j sa e ja e' ea s' d1 d2)(*strict*)
     apply(force)
    apply(rename_tac da qf q s j sa e ja e' ea s' d1 d2)(*strict*)
    apply(force)
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(thin_tac "\<exists>d2. epdaS.derivation G d2 \<and> epdaS.belongs G d2 \<and> maximum_of_domain d2 ja \<and> d2 0 = Some (pair None \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = r', epdaS_conf_stack = A # sa\<rparr>) \<and> d2 ja = Some (pair ea \<lparr>epdaS_conf_state = qf, epdaS_conf_scheduler = [], epdaS_conf_stack = s' @ A # sa\<rparr>) \<and> (\<forall>k \<le> ja. \<forall>e c. d2 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa))")
   apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
   apply(clarsimp)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule_tac
      x="derivation_map d1 (\<lambda>c. c\<lparr>epdaS_conf_stack := butn (epdaS_conf_stack c) (length s) @ (A # sa)\<rparr>)"
      in exI)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(rule epdaS_unused_stack_modification_preserves_derivation)
          apply(rename_tac da qf q s j sa e e' d1)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def)
         apply(rename_tac da qf q s j sa e e' d1)(*strict*)
         apply(force)
        apply(rename_tac da qf q s j sa e e' d1)(*strict*)
        apply(force)
       apply(rename_tac da qf q s j sa e e' d1)(*strict*)
       apply(force)
      apply(rename_tac da qf q s j sa e e' d1)(*strict*)
      apply(force)
     apply(rename_tac da qf q s j sa e e' d1)(*strict*)
     apply(force)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(force)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule conjI)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac da qf q s j sa e e' d1)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac da qf q s j sa e e' d1)(*strict*)
      apply(simp add: derivation_map_def)
     apply(rename_tac da qf q s j sa e e' d1)(*strict*)
     apply(simp add: butn_def)
     apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l', epdaS_conf_stack = B # s\<rparr> \<in> epdaS_configurations G")
      apply(rename_tac da qf q s j sa e e' d1)(*strict*)
      apply(simp add: epdaS_configurations_def)
     apply(rename_tac da qf q s j sa e e' d1)(*strict*)
     apply(rule_tac
      d="d1"
      in epdaS.belongs_configurations)
      apply(rename_tac da qf q s j sa e e' d1)(*strict*)
      apply(force)
     apply(rename_tac da qf q s j sa e e' d1)(*strict*)
     apply(force)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(force)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule conjI)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule conjI)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(simp add: derivation_map_def butn_def)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule conjI)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(simp add: derivation_map_def butn_def)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(rule conjI)
    apply(rename_tac da qf q s j sa e e' d1)(*strict*)
    apply(clarsimp)
    apply(rename_tac da qf q s j sa e e' d1 k ea c)(*strict*)
    apply(erule_tac
      x="k"
      in allE)
    apply(clarsimp)
    apply(simp add: derivation_map_def butn_def)
    apply(case_tac "d1 k")
     apply(rename_tac da qf q s j sa e e' d1 k ea c)(*strict*)
     apply(clarsimp)
    apply(rename_tac da qf q s j sa e e' d1 k ea c a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac da qf q s j sa e e' d1 k ea c a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac da qf q s j sa e e' d1)(*strict*)
   apply(simp add: derivation_map_def butn_def)
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(thin_tac "\<exists>d1. epdaS.derivation G d1 \<and> epdaS.belongs G d1 \<and> maximum_of_domain d1 (Suc j) \<and> d1 0 = Some (pair None \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l', epdaS_conf_stack = B # s\<rparr>) \<and> d1 j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = B # s\<rparr>) \<and> (\<forall>k \<le> j. \<forall>e c. d1 k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # s)) \<and> d1 (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)")
  apply(rename_tac d da qf q s j sa e ja e' ea s')(*strict*)
  apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = l'@r', epdaS_conf_stack = A # sa\<rparr> \<lparr>edge_src = src, edge_event = None, edge_pop = [A], edge_push = [B, A], edge_trg = trg\<rparr> \<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l'@r', epdaS_conf_stack = B # A # sa\<rparr>) (derivation_append (derivation_map d1 (\<lambda>c. c\<lparr>epdaS_conf_scheduler := take (length (epdaS_conf_scheduler c) - length (epdaS_conf_scheduler \<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = [], epdaS_conf_stack = A # sa\<rparr>)) (epdaS_conf_scheduler c) @ r'\<rparr>)) d2 (Suc j)) (Suc 0)"
      in exI)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(rule_tac
      x="qf"
      in exI)
  apply(rule conjI)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(rule epdaS.derivation_append_preserves_derivation)
     apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def)
     apply(simp add: option_to_list_def)
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation)
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(rule epda_maximal_context_preserves_derivation_prime)
            apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
            apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
           apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
           apply(force)
          apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
          apply(force)
         apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
         apply(force)
        apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
        apply(force)
       apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
       apply(force)
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(force)
     apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
     apply(force)
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(rule conjI)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(rule_tac
      ca="\<lparr>epdaS_conf_state = src, epdaS_conf_scheduler = l'@r', epdaS_conf_stack = A # sa\<rparr>"
      in epdaS.derivation_belongs)
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
     apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
     apply(simp add: der2_def derivation_append_def derivation_map_def)
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G \<lparr>edge_src = src, edge_event = None, edge_pop = [A], edge_push = [B, A], edge_trg = trg\<rparr>")
     apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
     apply(subgoal_tac "\<lparr>epdaS_conf_state = trg, epdaS_conf_scheduler = l', epdaS_conf_stack = B # A # sa\<rparr> \<in> epdaS_configurations G")
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(subgoal_tac "\<lparr>epdaS_conf_state = qs, epdaS_conf_scheduler = r', epdaS_conf_stack = A # sa\<rparr> \<in> epdaS_configurations G")
       apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
       apply(simp add: epdaS_configurations_def valid_epda_step_label_def)
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(rule_tac
      d="d2"
      in epdaS.belongs_configurations)
       apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
       apply(force)
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(force)
     apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
     apply(rule_tac
      d="d1"
      in epdaS.belongs_configurations)
      apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
      apply(force)
     apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
     apply(force)
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(rule_tac
      x="sa"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(rule_tac
      x="Suc j+ja+Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
   apply(rule_tac
      x="if ja=0 then e' else ea"
      in exI)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
   apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 k eb c)(*strict*)
  apply(case_tac k)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 k eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
   apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 k eb c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
  apply(case_tac "nat \<le> j")
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="nat"
      and P="\<lambda>nat. nat \<le> j \<longrightarrow> (\<forall>e c. d1 nat = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ B # A # sa))"
      in allE)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
   apply(case_tac nat)
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nata)(*strict*)
   apply(case_tac "d1 (Suc nata)")
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nata a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nata a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
  apply(case_tac "Suc nat=j")
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(case_tac "nat \<le> Suc j")
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat=Suc j")
    apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="nat - Suc j"
      and P="\<lambda>x. x \<le> ja \<longrightarrow> (\<forall>e c. d2 x = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ A # sa))"
      in allE)
  apply(rename_tac da qf q j sa e ja e' ea s' d2 d1 eb c nat)(*strict*)
  apply(clarsimp)
  done

theorem epda_sub_preserves_epdaH_marked_language: "
  valid_epda G
  \<Longrightarrow> valid_epda G'
  \<Longrightarrow> epda_sub G' G
  \<Longrightarrow> epdaH.marked_language G' \<subseteq> epdaH.marked_language G"
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(rule context_conjI)
   apply(rename_tac x d)(*strict*)
   apply(rule_tac epda_sub_preserves_derivation_initial)
      apply(rename_tac x d)(*strict*)
      prefer 3
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
   apply(simp add: epdaH_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac d i e c)(*strict*)
   apply(rule_tac x="i" in exI)
   apply(rule_tac x="e" in exI)
   apply(rule_tac x="c" in exI)
   apply(clarsimp)
   apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def epda_sub_def)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d conf)(*strict*)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d conf i e c)(*strict*)
  apply(rule_tac x="i" in exI)
  apply(rule_tac x="e" in exI)
  apply(rule_tac x="c" in exI)
  apply(clarsimp)
  apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def epda_sub_def)
  apply(force)
  done

theorem epda_sub_preserves_epdaH_unmarked_language: "
  valid_epda G
  \<Longrightarrow> valid_epda G'
  \<Longrightarrow> epda_sub G' G
  \<Longrightarrow> epdaH.unmarked_language G' \<subseteq> epdaH.unmarked_language G"
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(rule context_conjI)
   apply(rename_tac x d)(*strict*)
   apply(rule_tac epda_sub_preserves_derivation_initial)
      apply(rename_tac x d)(*strict*)
      prefer 3
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

definition epdaH_accessible_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set"
  where
    "epdaH_accessible_states G \<equiv>
  {epdaH_conf_state c | d n e c.
    epdaH.derivation_initial G d
    \<and> d n = Some (pair e c)}"

lemma epda_initial_in_epdaH_accessible_states: "
  valid_epda G
  \<Longrightarrow> epda_initial G \<in> epdaH_accessible_states G"
  apply(simp add: epdaH_accessible_states_def)
  apply(rule_tac x="der1 \<lparr>epdaH_conf_state=epda_initial G,epdaH_conf_history=[],epdaH_conf_stack=[epda_box G]\<rparr>" in exI)
  apply(rule_tac x="0" in exI)
  apply(rule_tac x="None" in exI)
  apply(rule_tac x="\<lparr>epdaH_conf_state=epda_initial G,epdaH_conf_history=[],epdaH_conf_stack=[epda_box G]\<rparr>" in exI)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(simp add: epdaH.derivation_initial_def)
   apply(rule conjI)
    apply(rule epdaH.der1_is_derivation)
   apply(simp add: der1_def epdaH_initial_configurations_def epdaH_configurations_def valid_epda_def)
  apply(simp add: der1_def epdaH_initial_configurations_def epdaH_configurations_def valid_epda_def)
  done

lemma epdaS_step_relation_injective_on_edge: "
  valid_pda G
  \<Longrightarrow> epdaS_step_relation G c e1 c'
  \<Longrightarrow> epdaS_step_relation G c e2 c'
  \<Longrightarrow> e1 = e2"
  apply(subgoal_tac "\<exists>x. edge_pop e1 = [x]")
   prefer 2
   apply(simp add: valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e1"
      in ballE)
    prefer 2
    apply(simp add: epdaS_step_relation_def)
   apply (metis insert_Nil last_triv)
  apply(subgoal_tac "\<exists>x. edge_pop e2 = [x]")
   prefer 2
   apply(simp add: valid_pda_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x="e2"
      in ballE)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def)
   apply(rename_tac x)(*strict*)
   apply (metis insert_Nil last_triv)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x w)(*strict*)
  apply(case_tac e1)
  apply(rename_tac x w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(case_tac e2)
  apply(rename_tac x w edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w edge_event edge_push edge_eventa)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac "edge_event")
   apply(rename_tac x w edge_event edge_push edge_eventa)(*strict*)
   apply(case_tac "edge_eventa")
    apply(rename_tac x w edge_event edge_push edge_eventa)(*strict*)
    apply(force)
   apply(rename_tac x w edge_event edge_push edge_eventa a)(*strict*)
   apply(force)
  apply(rename_tac x w edge_event edge_push edge_eventa a)(*strict*)
  apply(case_tac "edge_eventa")
   apply(rename_tac x w edge_event edge_push edge_eventa a)(*strict*)
   apply(force)
  apply(rename_tac x w edge_event edge_push edge_eventa a aa)(*strict*)
  apply(force)
  done

lemma epda_edge_event_in_effects: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> option_to_list (edge_event e) \<in> epda_effects G"
  apply(simp add: valid_epda_def valid_epda_step_label_def option_to_list_def option_to_set_def epda_effects_def)
  done

lemma apply_epdaS_is_forward_edge_deterministic_accessible_with_compatible_post_configurations: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> epdaH_step_relation G c e1 c1
  \<Longrightarrow> epdaH_step_relation G c e2 c2
  \<Longrightarrow> epdaH_conf_history c1@v1=epdaH_conf_history c2@v2
  \<Longrightarrow> e1=e2"
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long SSG" for SSG)
   prefer 2
   apply(rule I_epda_HS_H.epdaHS2HF_DEdetermR_FEdetermHist_DB)
    apply(force)
   apply(subgoal_tac "epdaHS.is_forward_deterministic_accessible G")
    apply(simp add: epdaHS.is_forward_deterministic_accessible_def)
   apply(rule epdaS_vs_epdaHS_is_forward_deterministic_accessible_preserved)
    apply(force)
   apply(simp add: epdaS.is_forward_deterministic_accessible_def)
   apply (metis epda_is_is_forward_target_deterministic_accessible)
  apply(simp add: epdaH.is_forward_edge_deterministicHist_DB_long_def)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule impE)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
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
  apply(clarsimp)
  apply(erule_tac
      x="option_to_list (edge_event e1)"
      in allE)
  apply(erule impE)
   apply(rule epda_edge_event_in_effects)
    apply(force)
   apply(simp add: epdaH_step_relation_def)
  apply(erule_tac
      x="option_to_list (edge_event e2)"
      in allE)
  apply(erule impE)
   apply(simp add: epdaH_step_relation_def)
  apply(erule impE)
   apply(simp add: epdaH_step_relation_def)
  apply(erule impE)
   apply(rule epda_edge_event_in_effects)
    apply(force)
   apply(simp add: epdaH_step_relation_def)
  apply(simp add: epdaH_step_relation_def)
  apply(simp add: epdaH.history_fragment_prefixes_def)
  apply(clarsimp)
  apply(rename_tac x xa w wa hf'' hf''a)(*strict*)
  apply(simp add: option_to_list_def epda_effects_def)
  apply(case_tac "edge_event e1")
   apply(rename_tac x xa w wa hf'' hf''a)(*strict*)
   apply(case_tac "edge_event e2")
    apply(rename_tac x xa w wa hf'' hf''a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa w wa hf'' hf''a a)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa w wa hf'' hf''a a)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event e2")
   apply(rename_tac x xa w wa hf'' hf''a a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w wa hf'' a)(*strict*)
   apply(case_tac x)
    apply(rename_tac x w wa hf'' a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x w wa hf'' a aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa w wa hf'' hf''a a aa)(*strict*)
  apply(clarsimp)
  done

lemma EDPDA_derivations_coincide: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> d2 (n1 + n) = Some (pair e2 c2)
  \<Longrightarrow> epdaH_conf_history c1 = epdaH_conf_history c2
  \<Longrightarrow> i\<le>n1
  \<Longrightarrow> d1 i = d2 i"
  apply(induct i)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(case_tac "d1 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac "d2 0")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a aa option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa b)(*strict*)
   apply(case_tac aa)
   apply(rename_tac aa b option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac b ba)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> d1 (Suc i) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      m="n1"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1a e2a c1a c2a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 i = Some (pair e1 c1) \<and> d2 (Suc i) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac i e1a e2a c1a c2a)(*strict*)
   prefer 2
   apply(rule_tac
      m="n1+n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i e1a e2a c1a c2a)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e1a e2a c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac i e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac i e1a e2a c1a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
  apply(subgoal_tac "e2a=e2aa")
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1a c1a c2a e2a c2aa)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
  apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
  apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history c1 = epdaH_conf_history c2a @ h")
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and n="Suc i"
      and m="n1-Suc i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
     apply(rule_tac
      d="d1"
      in epdaH.belongs_configurations)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
      apply(force)
     apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
     apply(force)
    apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
  apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history c2 = epdaH_conf_history c2aa @ h")
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and n="Suc i"
      and m="n1+n-Suc i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
     apply(rule_tac
      d="d2"
      in epdaH.belongs_configurations)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
      apply(force)
     apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
     apply(force)
    apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac i e1a e2a c1a c2a e2aa c2aa)(*strict*)
  apply(simp add: epda_effects_def)
  apply(clarsimp)
  apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
  apply(subgoal_tac "e2a=e2aa")
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
   prefer 2
   apply(rule_tac
      ?v2.0="ha"
      and ?v1.0="h"
      and d="d1"
      and n="i"
      in apply_epdaS_is_forward_edge_deterministic_accessible_with_compatible_post_configurations)
         apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
         apply(force)
        apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
        apply(force)
       apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
      apply(force)
     apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
     apply(force)
    apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
    apply(force)
   apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
   apply(force)
  apply(rename_tac i e1a e2a c1a c2a e2aa c2aa h ha)(*strict*)
  apply(force)
  done

lemma SDPDA_derivations_coincide2: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> d1 (Suc n1) = Some (pair e1' c1')
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2')
  \<Longrightarrow> epdaH_conf_history c1=epdaH_conf_history c2
  \<Longrightarrow> epdaH_conf_history c1'=epdaH_conf_history c2'
  \<Longrightarrow> epdaH_conf_history c1'=epdaH_conf_history c1@[a]
  \<Longrightarrow> n1\<le>n2
  \<Longrightarrow> n1=n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  apply(clarsimp)
  apply(subgoal_tac "\<exists>n. n1+n=n2")
   prefer 2
   apply(rule_tac
      x="n2-n1"
      in exI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "(\<forall>i\<le>n1. d1 i = d2 i)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="n1"
      in allE)
   apply(clarsimp)
   apply(case_tac n)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 n1 = Some (pair e1 c1) \<and> d1 (Suc n1) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc n1"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac nat)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e2a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 n1 = Some (pair e1 c1) \<and> d2 (Suc n1) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
    apply(rename_tac nat e2a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc (n1+nat)"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac nat e2a)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac nat e2a)(*strict*)
     apply(force)
    apply(rename_tac nat e2a)(*strict*)
    apply(force)
   apply(rename_tac nat e2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e2a e2aa c2a)(*strict*)
   apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history c2 = epdaH_conf_history c2a @ h")
    apply(rename_tac nat e2a e2aa c2a)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="Suc n1"
      and m="nat"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac nat e2a e2aa c2a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac nat e2a e2aa c2a)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac nat e2a e2aa c2a)(*strict*)
      apply(rule_tac
      d="d2"
      in epdaH.belongs_configurations)
       apply(rename_tac nat e2a e2aa c2a)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac nat e2a e2aa c2a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac nat e2a e2aa c2a)(*strict*)
       apply(force)
      apply(rename_tac nat e2a e2aa c2a)(*strict*)
      apply(force)
     apply(rename_tac nat e2a e2aa c2a)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac nat e2a e2aa c2a)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac nat e2a e2aa c2a)(*strict*)
   apply(simp add: epda_effects_def)
   apply(clarsimp)
   apply(rename_tac nat e2a e2aa c2a h)(*strict*)
   apply(subgoal_tac "e2a=e2aa")
    apply(rename_tac nat e2a e2aa c2a h)(*strict*)
    prefer 2
    apply(rule_tac
      ?v2.0="h@[a]"
      and ?v1.0="[]"
      and d="d1"
      and n="n1"
      in apply_epdaS_is_forward_edge_deterministic_accessible_with_compatible_post_configurations)
          apply(rename_tac nat e2a e2aa c2a h)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac nat e2a e2aa c2a h)(*strict*)
         apply(force)
        apply(rename_tac nat e2a e2aa c2a h)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac nat e2a e2aa c2a h)(*strict*)
       apply(force)
      apply(rename_tac nat e2a e2aa c2a h)(*strict*)
      apply(force)
     apply(rename_tac nat e2a e2aa c2a h)(*strict*)
     apply(force)
    apply(rename_tac nat e2a e2aa c2a h)(*strict*)
    apply(force)
   apply(rename_tac nat e2a e2aa c2a h)(*strict*)
   apply(rule_tac
      t="epdaH_conf_history c1'"
      and s="epdaH_conf_history c2'"
      in ssubst)
    apply(rename_tac nat e2a e2aa c2a h)(*strict*)
    apply(force)
   apply(rename_tac nat e2a e2aa c2a h)(*strict*)
   apply(rule_tac
      t="epdaH_conf_history c2'"
      and s="epdaH_conf_history c2a @ h @ [a]"
      in ssubst)
    apply(rename_tac nat e2a e2aa c2a h)(*strict*)
    apply(force)
   apply(rename_tac nat e2a e2aa c2a h)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e2a c2a h)(*strict*)
   apply(simp add: epdaH_step_relation_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n i)(*strict*)
  apply(rule EDPDA_derivations_coincide)
         apply(rename_tac n i)(*strict*)
         apply(force)+
  done

lemma SDPDA_derivations_coincide3: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> d1 (Suc n1) = Some (pair e1' c1')
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2')
  \<Longrightarrow> epdaH_conf_history c1=epdaH_conf_history c2
  \<Longrightarrow> epdaH_conf_history c1'=epdaH_conf_history c2'
  \<Longrightarrow> epdaH_conf_history c1'=epdaH_conf_history c1@[a]
  \<Longrightarrow> n1=n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  apply(case_tac "n1\<le>n2")
   apply(rule_tac
      a="a"
      in SDPDA_derivations_coincide2)
              apply(force)+
  apply(subgoal_tac "n2 = n1 \<and> (\<forall>i\<le>n2. d2 i = d1 i)")
   apply(force)
  apply(rule_tac
      a="a"
      in SDPDA_derivations_coincide2)
             apply(force)+
  done

definition duplicate_markingH :: "('q,'a,'b)epda \<Rightarrow> bool" where
  "duplicate_markingH G \<equiv> (\<exists>d. epdaH.derivation_initial G d \<and> (\<exists>i j.
  d (i+j+Suc 0) \<noteq> None
  \<and> epdaH_conf_state (the(get_configuration (d i))) \<in> epda_marking G
  \<and> epdaH_conf_state (the(get_configuration (d (i+j+Suc 0)))) \<in> epda_marking G
  \<and> epdaH_conf_history (the(get_configuration (d i))) = epdaH_conf_history (the(get_configuration (d (i+j+Suc 0))))
  ))"

lemma EDPDA_derivations_coincide4: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> \<not> duplicate_markingH G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> c1 \<in> epdaH_marking_configurations G
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> c2 \<in> epdaH_marking_configurations G
  \<Longrightarrow> epdaH_conf_history c1=epdaH_conf_history c2
  \<Longrightarrow> n1\<le>n2
  \<Longrightarrow> n1=n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  apply(subgoal_tac "\<exists>n. n1+n=n2")
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "(\<forall>i\<le>n1. d1 i = d2 i)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac n i)(*strict*)
    apply(rule EDPDA_derivations_coincide)
           apply(rename_tac n i)(*strict*)
           apply(force)
          apply(rename_tac n i)(*strict*)
          apply(force)
         apply(rename_tac n i)(*strict*)
         apply(force)
        apply(rename_tac n i)(*strict*)
        apply(force)
       apply(rename_tac n i)(*strict*)
       apply(force)
      apply(rename_tac n i)(*strict*)
      apply(force)
     apply(rename_tac n i)(*strict*)
     apply(force)
    apply(rename_tac n i)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="n1"
      in allE)
   apply(clarsimp)
   apply(simp add: duplicate_markingH_def)
   apply(erule_tac
      x="d2"
      in allE)
   apply(clarsimp)
   apply(case_tac n)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n nat)(*strict*)
   apply(erule_tac
      x="n1"
      in allE)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: epdaH_marking_configurations_def)
  apply(rule_tac
      x="n2-n1"
      in exI)
  apply(force)
  done

lemma EDPDA_derivations_coincide5: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> \<not> duplicate_markingH G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> c1 \<in> epdaH_marking_configurations G
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> c2 \<in> epdaH_marking_configurations G
  \<Longrightarrow> epdaH_conf_history c1=epdaH_conf_history c2
  \<Longrightarrow> n1=n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  apply(case_tac "n1\<le>n2")
   apply(rule EDPDA_derivations_coincide4)
             apply(force)+
  apply(subgoal_tac "n2 = n1 \<and> (\<forall>i\<le>n2. d2 i = d1 i)")
   apply(force)
  apply(rule EDPDA_derivations_coincide4)
            apply(force)+
  done

lemma epdaS_apply_is_forward_edge_deterministic_accessible: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations G
  \<Longrightarrow> x \<in> epda_delta G
  \<Longrightarrow> y \<in> epda_delta G
  \<Longrightarrow> edge_src x=edge_src y
  \<Longrightarrow> edge_src x=epdaS_conf_state c
  \<Longrightarrow> prefix (edge_pop x) (epdaS_conf_stack c)
  \<Longrightarrow> prefix (edge_pop y) (epdaS_conf_stack c)
  \<Longrightarrow> prefix (option_to_list(edge_event x)) (epdaS_conf_scheduler c)
  \<Longrightarrow> prefix (option_to_list(edge_event y)) (epdaS_conf_scheduler c)
  \<Longrightarrow> x=y"
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(erule_tac
      x="c"
      in ballE)
   prefer 2
   apply(force)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state=edge_trg x,epdaS_conf_scheduler=drop(length(option_to_list (edge_event x)))(epdaS_conf_scheduler c),epdaS_conf_stack=(edge_push x)@(drop(length(edge_pop x))(epdaS_conf_stack c))\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state=edge_trg y,epdaS_conf_scheduler=drop(length(option_to_list (edge_event y)))(epdaS_conf_scheduler c),epdaS_conf_stack=(edge_push y)@(drop(length(edge_pop y))(epdaS_conf_stack c))\<rparr>"
      in allE)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule_tac
      x="y"
      in allE)
  apply(erule impE)
   prefer 2
   apply(force)
  apply(simp add: epdaS_step_relation_def)
  apply(case_tac c)
  apply(rename_tac epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(rule conjI)
   apply(rename_tac c ca cb cc)(*strict*)
   apply (metis List.drop_append dropPrecise)
  apply(rename_tac c ca cb cc)(*strict*)
  apply (metis List.drop_append dropPrecise)
  done

lemma valid_simple_dpda_edge_alt: "
  valid_simple_dpda G
  \<Longrightarrow> x \<in> epda_delta G
  \<Longrightarrow> (\<exists>s1 s2. edge_pop x=[s1] \<and>
  ((edge_event x \<noteq> None \<and> edge_push x=[s1])
  \<or> (edge_event x = None \<and> edge_push x=[s2,s1])
  \<or> (edge_event x = None \<and> edge_push x=[])))"
  apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. length (edge_pop x) = Suc 0"
      in ballE)
   prefer 2
   apply(force)
  apply(erule_tac
      x="x"
      in ballE)
   prefer 2
   apply(force)
  apply(case_tac "edge_event x")
   apply(clarsimp)
   apply(case_tac "edge_pop x")
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_push x")
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
  apply(rename_tac a aa list)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> x \<in> epdaS_accessible_edges G
  \<Longrightarrow> y \<in> epda_delta G
  \<Longrightarrow> edge_src x=edge_src y
  \<Longrightarrow> edge_pop x = edge_pop y
  \<Longrightarrow> prefix (option_to_list (edge_event y)) (option_to_list (edge_event x))
  \<Longrightarrow> x=y"
  apply(simp add: epdaS_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac d n c)(*strict*)
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(case_tac n)
   apply(rename_tac d n c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
  apply(rename_tac d n c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac d c nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac d c nat)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d c nat)(*strict*)
    apply(force)
   apply(rename_tac d c nat)(*strict*)
   apply(force)
  apply(rename_tac d c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c nat e1 c1)(*strict*)
  apply(erule_tac
      x="c1"
      in ballE)
   apply(rename_tac d c nat e1 c1)(*strict*)
   apply(erule_tac
      x="c"
      in allE)
   apply(subgoal_tac "\<exists>c. epdaS_step_relation G c1 y c")
    apply(rename_tac d c nat e1 c1)(*strict*)
    apply(clarsimp)
   apply(rename_tac d c nat e1 c1)(*strict*)
   prefer 2
   apply(simp add: epdaS.get_accessible_configurations_def)
   apply(erule_tac
      x="d"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="nat"
      in allE)
   apply(simp add: get_configuration_def)
  apply(rename_tac d c nat e1 c1)(*strict*)
  apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg y,epdaS_conf_scheduler=drop(length(option_to_list (edge_event y)))(epdaS_conf_scheduler c1),epdaS_conf_stack=(edge_push y)@(drop(length(edge_pop y))(epdaS_conf_stack c1))\<rparr>"
      in exI)
  apply(simp add: epdaS_step_relation_def prefix_def)
  apply(clarsimp)
  apply(rename_tac d c nat e1 c1 ca w)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac "edge_event x")
   apply(rename_tac d c nat e1 c1 ca w)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c nat e1 c1 ca w a)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event y")
   apply(rename_tac d c nat e1 c1 ca w a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c nat e1 c1 ca w a aa)(*strict*)
  apply(clarsimp)
  done

definition duplicate_marking :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "duplicate_marking G \<equiv>
  \<exists>d. epdaS.derivation_initial G d
  \<and> (\<exists>i j. d (i + j + Suc 0) \<noteq> None
     \<and> epdaS_conf_state (the (get_configuration (d i))) \<in> epda_marking G
     \<and> epdaS_conf_state (the (get_configuration (d (i + j + Suc 0))))
          \<in> epda_marking G
     \<and> epdaS_conf_scheduler (the (get_configuration (d i)))
        = epdaS_conf_scheduler (the (get_configuration (d (i + j + Suc 0)))))"

definition duplicate_marking_ALT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "duplicate_marking_ALT G \<equiv>
  \<exists>d i j.
    epdaS.derivation_initial G d
    \<and> d (i + j + Suc 0) \<noteq> None
    \<and> epdaS_conf_state (the (get_configuration (d i)))
        \<in> epda_marking G
    \<and> epdaS_conf_state (the (get_configuration (d (i + j + Suc 0))))
        \<in> epda_marking G
    \<and> epdaS_conf_scheduler (the (get_configuration (d i)))
        = epdaS_conf_scheduler (the (get_configuration (d (i + j + Suc 0))))"

lemma duplicate_marking_ALT_vs_duplicate_marking: "
  duplicate_marking_ALT G = duplicate_marking G"
  apply(simp add: duplicate_marking_ALT_def duplicate_marking_def)
  done

lemma duplicate_marking_to_duplicate_markingH: "
  valid_epda G
  \<Longrightarrow> \<not> duplicate_marking G
  \<Longrightarrow> \<not> duplicate_markingH G"
  apply(simp add: duplicate_marking_def duplicate_markingH_def)
  apply(clarsimp)
  apply(rename_tac d i j y)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaH_vs_epdaHS.Bra2LinDer_preserves_derivation)
      apply(rename_tac d i j y)(*strict*)
      apply(force)
     apply(rename_tac d i j y)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d i j y)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i j y)(*strict*)
     apply(force)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaH_vs_epdaHS.Bra2LinDer_preserves_belongs)
      apply(rename_tac d i j y)(*strict*)
      apply(force)
     apply(rename_tac d i j y)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d i j y)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i j y)(*strict*)
     apply(force)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(subgoal_tac "epdaS.derivation_initial G (epdaHS2epdaS_derivation (epdaH_vs_epdaHS.Bra2LinDer G d (Suc (i + j))))")
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule epdaHS2epdaS_derivation_preserves_derivation_initial)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(rule epdaHS.derivation_initialI)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j y c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "c \<in> epdaHS_configurations G")
    apply(rename_tac d i j y c)(*strict*)
    prefer 2
    apply(rule epdaHS.belongs_configurations)
     apply(rename_tac d i j y c)(*strict*)
     apply(force)
    apply(rename_tac d i j y c)(*strict*)
    apply(force)
   apply(rename_tac d i j y c)(*strict*)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
   apply(case_tac y)
   apply(rename_tac d i j y c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j c option b)(*strict*)
   apply(case_tac "d 0")
    apply(rename_tac d i j c option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i j c option b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i j c option b a optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j option b ba)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(simp add: epdaHS_initial_configurations_def)
   apply(simp add: epdaH.derivation_initial_def)
   apply(clarsimp)
   apply(simp add: epdaH_initial_configurations_def)
  apply(rename_tac d i j y)(*strict*)
  apply(erule_tac
      x="(epdaHS2epdaS_derivation (epdaH_vs_epdaHS.Bra2LinDer G d (Suc (i + j))))"
      in allE)
  apply(rename_tac d i j y)(*strict*)
  apply(erule impE)
   apply(rename_tac d i j y)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i j y)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule_tac
      x="j"
      in allE)
  apply(erule impE)
   apply(rename_tac d i j y)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(case_tac y)
   apply(rename_tac d i j y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j option b)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def get_configuration_def)
  apply(rename_tac d i j y)(*strict*)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in epdaH.pre_some_position_is_some_position)
     apply(rename_tac d i j y)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j y e c)(*strict*)
  apply(erule impE)
   apply(rename_tac d i j y e c)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(case_tac y)
   apply(rename_tac d i j y e c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j e c option b)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def get_configuration_def)
  apply(rename_tac d i j y e c)(*strict*)
  apply(erule disjE)
   apply(rename_tac d i j y e c)(*strict*)
   apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(case_tac y)
   apply(rename_tac d i j y e c option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i j y e c)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def)
  apply(case_tac y)
  apply(rename_tac d i j y e c option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j e c option b)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinConf_def epdaH_vs_epdaHS.Bra2LinDer_def get_configuration_def epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer'_def get_configuration_def)
  apply(subgoal_tac "nat_seq (Suc (i + j)) (i + j)=[]")
   apply(rename_tac d i j e c option b)(*strict*)
   prefer 2
   apply (metis lessI nat_seqEmpty)
  apply(rename_tac d i j e c option b)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "foldl (@) [] (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration (\<lambda>a c2. case a of Some e2 \<Rightarrow> epdaHvHS_Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq i (i + j)))=[]")
   apply(rename_tac d i j e c option b)(*strict*)
   apply(force)
  apply(rename_tac d i j e c option b)(*strict*)
  apply(rule foldl_empty)
  apply(rename_tac d i j e c option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j e c option b n)(*strict*)
  apply(subgoal_tac "i\<le>n \<and> n\<le> i+j")
   apply(rename_tac d i j e c option b n)(*strict*)
   prefer 2
   apply (metis nat_seq_in_interval)
  apply(rename_tac d i j e c option b n)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2")
   apply(rename_tac d i j e c option b n)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d i j e c option b n)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d i j e c option b n)(*strict*)
    apply(force)
   apply(rename_tac d i j e c option b n)(*strict*)
   apply(force)
  apply(rename_tac d i j e c option b n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaHvHS_Bra2LinStep_def)
  apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history SSc' = epdaH_conf_history SSc @ h" for SSc' SSc)
   apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="i"
      and m="n-i"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history SSc' = epdaH_conf_history SSc @ h" for SSc' SSc)
   apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="n"
      and m="Suc 0"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>h\<in> epda_effects G. epdaH_conf_history SSc' = epdaH_conf_history SSc @ h" for SSc' SSc)
   apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="Suc n"
      and m="(i+j) - n"
      in epdaH.steps_extend_history_derivation)
       apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
    apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
  apply(erule bexE)+
  apply(rename_tac d i j e c option b n e1 e2 c1 c2 h ha hb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j e c option b n e1 e2 c1 c2)(*strict*)
  apply(simp add: epda_effects_def)
  apply(simp add: epdaH_step_relation_def)
  done

lemma equal_configurations_at_identical_position_in_marking_derivations: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> \<not> duplicate_markingH G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> d2 m2 = Some (pair e2' c2')
  \<Longrightarrow> c2' \<in> epdaH_marking_configurations G
  \<Longrightarrow> d1 n1 = Some (pair e1 c)
  \<Longrightarrow> d2 n2 = Some (pair e2 c)
  \<Longrightarrow> n1\<le>n2
  \<Longrightarrow> n1=n2"
  apply(subgoal_tac "d1 n1=d2 n1")
   prefer 2
   apply(rule_tac
      ?n1.0="n1"
      and ?n.0="n2-n1"
      in EDPDA_derivations_coincide)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "epdaH.derivation_initial G d1")
  apply(thin_tac "d1 n1 = Some (pair e1 c)")
  apply(subgoal_tac "\<exists>n. n1+n=n2")
   prefer 2
   apply(rule_tac
      x="n2-n1"
      in exI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "n1+n\<le>m2")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply (metis epdaH.allPreMaxDomSome_prime epdaH.derivation_initial_is_derivation not_None_eq)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "\<exists>m. n1+n+m=m2")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule_tac
      x="m2-n1-n"
      in exI)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n m)(*strict*)
  apply(case_tac m)
   apply(rename_tac n m)(*strict*)
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(case_tac n)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n nat)(*strict*)
   apply(simp add: duplicate_markingH_def)
   apply(erule_tac
      x="d2"
      in allE)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(erule_tac
      x="n1"
      in allE)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: epdaH_marking_configurations_def)
  apply(rename_tac n m nat)(*strict*)
  apply(subgoal_tac " n1+m=n1+n+m \<and> (\<forall>i\<le>n1+m. (derivation_append (derivation_take d2 n1) (derivation_drop d2 (n1+n)) n1) i = d2 i)")
   apply(rename_tac n m nat)(*strict*)
   apply(force)
  apply(rename_tac n m nat)(*strict*)
  apply(rule_tac
      ?e1.0="e2'"
      and ?c1.0="c2'"
      in EDPDA_derivations_coincide5)
           apply(rename_tac n m nat)(*strict*)
           apply(force)
          apply(rename_tac n m nat)(*strict*)
          apply(force)
         apply(rename_tac n m nat)(*strict*)
         apply(force)
        apply(rename_tac n m nat)(*strict*)
        apply(rule epdaH.derivation_append_preserves_derivation_initial)
          apply(rename_tac n m nat)(*strict*)
          apply(force)
         apply(rename_tac n m nat)(*strict*)
         apply(rule epdaH.derivation_take_preserves_derivation_initial)
         apply(force)
        apply(rename_tac n m nat)(*strict*)
        apply(rule epdaH.derivation_append_preserves_derivation)
          apply(rename_tac n m nat)(*strict*)
          apply(rule epdaH.derivation_take_preserves_derivation)
          apply(rule epdaH.derivation_initial_is_derivation)
          apply(force)
         apply(rename_tac n m nat)(*strict*)
         apply(rule_tac
      m="m"
      in epdaH.derivation_drop_preserves_derivation)
          apply(rename_tac n m nat)(*strict*)
          apply(rule epdaH.derivation_initial_is_derivation)
          apply(force)
         apply(rename_tac n m nat)(*strict*)
         apply(clarsimp)
        apply(rename_tac n m nat)(*strict*)
        apply(simp add: derivation_take_def derivation_drop_def)
       apply(rename_tac n m nat)(*strict*)
       apply(force)
      apply(rename_tac n m nat)(*strict*)
      apply(simp add: derivation_append_def derivation_take_def derivation_drop_def)
      apply(clarsimp)
      apply(rename_tac n nat)(*strict*)
      apply(rule_tac
      t="Suc (nat + (n1 + n))"
      and s="Suc (n1 + n + nat)"
      in ssubst)
       apply(rename_tac n nat)(*strict*)
       apply(force)
      apply(rename_tac n nat)(*strict*)
      apply(force)
     apply(rename_tac n m nat)(*strict*)
     apply(force)
    apply(rename_tac n m nat)(*strict*)
    apply(force)
   apply(rename_tac n m nat)(*strict*)
   apply(force)
  apply(rename_tac n m nat)(*strict*)
  apply(force)
  done

definition every_state_in_some_accessible_configuration :: "('q,'a,'b)epda \<Rightarrow> bool" where
  "every_state_in_some_accessible_configuration G = (\<forall>q\<in> epda_states G. \<forall>w. set w \<subseteq> epda_events G \<longrightarrow> \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box G]\<rparr>\<in> epdaS.get_accessible_configurations G)"

definition every_state_in_some_accessible_configurationEx :: "('q,'a,'b)epda \<Rightarrow> bool" where
  "every_state_in_some_accessible_configurationEx G = (\<forall>q\<in> epda_states G. \<exists>w. set w \<subseteq> epda_events G \<and> \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box G]\<rparr>\<in> epdaS.get_accessible_configurations G)"

lemma epda_input_replacement_preserves_derivation: "
  valid_epda G
  \<Longrightarrow> set w \<subseteq> epda_events G
  \<Longrightarrow> set wa \<subseteq> epda_events G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d i = Some (derivation_configuration.pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = wa, epdaS_conf_stack = s\<rparr>)
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> epdaS_conf_scheduler c = wb @ wa
  \<Longrightarrow> epdaS.derivation G (derivation_map (derivation_take d i) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := the (right_quotient_word (epdaS_conf_scheduler c) wa) @ w\<rparr>))"
  apply(induct i arbitrary: e q wa wb s)
   apply(rename_tac e q wa wb s)(*strict*)
   apply(simp add: epdaS.derivation_def)
   apply(clarsimp)
   apply(rename_tac q wa s i)(*strict*)
   apply(case_tac i)
    apply(rename_tac q wa s i)(*strict*)
    apply(clarsimp)
    apply(rename_tac q wa s)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def)
   apply(rename_tac q wa s i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac q wa s nat)(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
  apply(rename_tac i e q wa wb s)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac i e q wa wb s)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac i e q wa wb s)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e q wa wb s)(*strict*)
    apply(force)
   apply(rename_tac i e q wa wb s)(*strict*)
   apply(force)
  apply(rename_tac i e q wa wb s)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c = w @ epdaS_string_state c1")
   apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
   prefer 2
   apply(rule epdaS.derivation_monotonically_dec)
        apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
      apply(rule epdaS.derivation_initial_belongs)
       apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac i q wa wb s e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c1 = w @ epdaS_string_state \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = wa, epdaS_conf_stack = s\<rparr>")
   apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
   prefer 2
   apply(rule_tac
      i="i"
      and j="Suc 0"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
        apply(force)
       apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
       apply(force)
      apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
      apply(rule epdaS.derivation_initial_belongs)
       apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
       apply(force)
      apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
      apply(force)
     apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
    apply(force)
   apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
   apply(force)
  apply(rename_tac i q wa wb s e1 e2 c1 wc)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q wa wb s e1 e2 c1 wc wca)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(clarsimp)
  apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="epdaS_conf_state c1"
      in meta_allE)
  apply(erule_tac
      x="epdaS_conf_scheduler c1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="wb"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="epdaS_conf_stack c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
   apply(subgoal_tac "c1 \<in> epdaS_configurations G")
    apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
    apply(simp add: epdaS_configurations_def)
    apply(clarsimp)
    apply(rename_tac i q wa s e1 e2 wb wc x qa sa)(*strict*)
    apply(force)
   apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
   apply(rule epdaS.belongs_configurations)
    apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
    apply(rule epdaS.derivation_initial_belongs)
     apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
    apply(force)
   apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
   apply(force)
  apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i q wa s e1 e2 c1 wb wc ia)(*strict*)
  apply(case_tac "ia\<le>i")
   apply(rename_tac i q wa s e1 e2 c1 wb wc ia)(*strict*)
   apply(erule_tac
      x="ia"
      in allE)
   apply(case_tac ia)
    apply(rename_tac i q wa s e1 e2 c1 wb wc ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def)
   apply(rename_tac i q wa s e1 e2 c1 wb wc ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat)(*strict*)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in epdaS.step_detail_before_some_position)
      apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
    apply(force)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(subgoal_tac "\<exists>w. epdaS_string_state c1a = w @ epdaS_string_state c2")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
    prefer 2
    apply(rule_tac
      i="nat"
      and j="Suc 0"
      in epdaS.derivation_monotonically_dec)
         apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
         apply(force)
        apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
        apply(force)
       apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
       apply(rule epdaS.derivation_initial_belongs)
        apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
        apply(force)
       apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
       apply(force)
      apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
    apply(force)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
   apply(simp add: epdaS_string_state_def)
   apply(subgoal_tac "\<exists>w. epdaS_string_state c = w @ epdaS_string_state c1a")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
    prefer 2
    apply(rule_tac
      i="0"
      and j="nat"
      in epdaS.derivation_monotonically_dec)
         apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
         apply(force)
        apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
        apply(force)
       apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
       apply(rule epdaS.derivation_initial_belongs)
        apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
        apply(force)
       apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
       apply(force)
      apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
    apply(force)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
   apply(simp add: epdaS_string_state_def)
   apply(subgoal_tac "\<exists>w. epdaS_string_state c2 = w @ epdaS_string_state c1")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
    prefer 2
    apply(rule_tac
      i="Suc nat"
      and j="i-Suc nat"
      in epdaS.derivation_monotonically_dec)
         apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
         apply(force)
        apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
        apply(force)
       apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
       apply(rule epdaS.derivation_initial_belongs)
        apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
        apply(force)
       apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
       apply(force)
      apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
    apply(force)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
   apply(simp add: epdaS_string_state_def)
   apply(subgoal_tac "right_quotient_word (wba @ we @ wc @ wa) wa = Some(wba @ we @ wc)")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    prefer 2
    apply(rule_tac
      t="wba @ we @ wc @ wa"
      and s="(wba @ we @ wc) @ wa"
      in ssubst)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    apply (metis right_quotient_word_removes_right_addition)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
   apply(subgoal_tac "right_quotient_word (we @ wc @ wa) wa = Some(we @ wc)")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    prefer 2
    apply(rule_tac
      t="we @ wc @ wa"
      and s="(we @ wc) @ wa"
      in ssubst)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    apply (metis right_quotient_word_removes_right_addition)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
   apply(subgoal_tac "right_quotient_word (wba @ we @ wc @ wa) (wc@wa) = Some(wba @ we)")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    prefer 2
    apply(rule_tac
      t="wba @ we @ wc @ wa"
      and s="(wba @ we) @ (wc @ wa)"
      in ssubst)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    apply (metis right_quotient_word_removes_right_addition)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
   apply(subgoal_tac "right_quotient_word (we @ wc @ wa) (wc@wa) = Some we")
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    prefer 2
    apply(rule_tac
      t="we @ wc @ wa"
      and s="we @ (wc @ wa)"
      in ssubst)
     apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
     apply(force)
    apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
    apply (metis right_quotient_word_removes_right_addition)
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat e1a e2a c1a c2 wba wd we)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q wa s e1 e2 c1 wc nat e1a e2a c1a c2 wb wd we)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac i q wa s e1 e2 c1 wb wc ia)(*strict*)
  apply(thin_tac "\<forall>ia. case ia of 0 \<Rightarrow> (case derivation_map (derivation_take d i) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := the (right_quotient_word (epdaS_conf_scheduler c) (wc @ wa)) @ w\<rparr>) 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case derivation_map (derivation_take d i) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := the (right_quotient_word (epdaS_conf_scheduler c) (wc @ wa)) @ w\<rparr>) ia of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case derivation_map (derivation_take d i) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := the (right_quotient_word (epdaS_conf_scheduler c) (wc @ wa)) @ w\<rparr>) i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> epdaS_step_relation G i'2 i1v i2)))")
  apply(rename_tac i q wa s e1 e2 c1 wb wc ia)(*strict*)
  apply(case_tac "ia")
   apply(rename_tac i q wa s e1 e2 c1 wb wc ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac i q wa s e1 e2 c1 wb wc ia nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q wa s e1 e2 c1 wb wc nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat)(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
  apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
  apply(case_tac "Suc nat > Suc i")
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
  apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
  apply(subgoal_tac "nat=i")
   apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i q wa s e1 e2 c1 wb wc nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def)
  apply(subgoal_tac "right_quotient_word (wc @ wa) wa = Some wc")
   apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
   prefer 2
   apply (metis right_quotient_word_removes_right_addition)
  apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "right_quotient_word wa wa = Some []")
   apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
   prefer 2
   apply (metis right_quotient_word_full)
  apply(rename_tac i q wa s e1 e2 c1 wb wc)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaS_step_relation_def)
  done

lemma epda_input_replacement_preserves_derivation_initial: "
  valid_epda G
  \<Longrightarrow> set w \<subseteq> epda_events G
  \<Longrightarrow> set wa \<subseteq> epda_events G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = wa, epdaS_conf_stack = [epda_box G]\<rparr>)
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> epdaS_conf_scheduler c = wb @ wa
  \<Longrightarrow> epdaS.derivation_initial G (derivation_map (derivation_take d i) (\<lambda>c. c\<lparr>epdaS_conf_scheduler := the (right_quotient_word (epdaS_conf_scheduler c) wa) @ w\<rparr>))"
  apply(simp (no_asm) add: epdaS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: epdaS.derivation_initial_def)
   apply(simp add: derivation_map_def)
   apply(simp add: derivation_take_def)
   apply(clarsimp)
   apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "right_quotient_word (wb @ wa) wa = Some wb")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply (metis right_quotient_word_removes_right_addition)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rule epda_input_replacement_preserves_derivation)
        apply(force)+
  done

lemma DFA_Connected_from_ConnectedEx: "
  valid_dfa G
  \<Longrightarrow> every_state_in_some_accessible_configurationEx G
  \<Longrightarrow> every_state_in_some_accessible_configuration G"
  apply(simp add: every_state_in_some_accessible_configurationEx_def)
  apply(simp add: every_state_in_some_accessible_configuration_def)
  apply(clarsimp)
  apply(rename_tac q w)(*strict*)
  apply(erule_tac
      x="q"
      in ballE)
   apply(rename_tac q w)(*strict*)
   apply(clarsimp)
   apply(rename_tac q w wa)(*strict*)
   prefer 2
   apply(rename_tac q w)(*strict*)
   apply(force)
  apply(rename_tac q w wa)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac q w wa d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac q w wa d i)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac q w wa d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac q w wa d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac q w wa d i option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac q w wa d i option)(*strict*)
  apply(fold get_configuration_def)
  apply(rename_tac e)
  apply(rename_tac q w wa d i e)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac q w wa d i e)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac q w wa d i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac q w wa d i e c)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_string_state c = w @ epdaS_string_state \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = wa, epdaS_conf_stack = [epda_box G]\<rparr>")
   apply(rename_tac q w wa d i e c)(*strict*)
   prefer 2
   apply(rule epdaS.derivation_monotonically_dec)
        apply(rename_tac q w wa d i e c)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
        apply(force)
       apply(rename_tac q w wa d i e c)(*strict*)
       apply(force)
      apply(rename_tac q w wa d i e c)(*strict*)
      apply(rule epdaS.derivation_initial_belongs)
       apply(rename_tac q w wa d i e c)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac q w wa d i e c)(*strict*)
      apply(force)
     apply(rename_tac q w wa d i e c)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac q w wa d i e c)(*strict*)
    apply(force)
   apply(rename_tac q w wa d i e c)(*strict*)
   apply(force)
  apply(rename_tac q w wa d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac q w wa d i e c wb)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(rule_tac
      x="derivation_map (derivation_take d i) (\<lambda>c. c\<lparr>epdaS_conf_scheduler:=the(right_quotient_word (epdaS_conf_scheduler c) wa) @ w\<rparr>)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac q w wa d i e c wb)(*strict*)
   apply(rule epda_input_replacement_preserves_derivation_initial)
         apply(rename_tac q w wa d i e c wb)(*strict*)
         apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
        apply(rename_tac q w wa d i e c wb)(*strict*)
        apply(force)
       apply(rename_tac q w wa d i e c wb)(*strict*)
       apply(force)
      apply(rename_tac q w wa d i e c wb)(*strict*)
      apply(force)
     apply(rename_tac q w wa d i e c wb)(*strict*)
     apply(force)
    apply(rename_tac q w wa d i e c wb)(*strict*)
    apply(force)
   apply(rename_tac q w wa d i e c wb)(*strict*)
   apply(force)
  apply(rename_tac q w wa d i e c wb)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: get_configuration_def derivation_map_def derivation_take_def)
  apply (metis right_quotient_word_full option.sel)
  done

lemma DFA_not_none_read: "
  valid_dfa M
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> edge_event e \<noteq> None"
  apply(simp add: valid_dfa_def)
  done

lemma DFA_push_pop_eq: "
  valid_dfa M
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> edge_push e = edge_pop e"
  apply(simp add: valid_dfa_def)
  done

lemma DFA_derivation_input_restriction_still_simulates: "
  valid_dfa M
  \<Longrightarrow> epdaS.derivation M d1
  \<Longrightarrow> epdaS.derivation M d2
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> d1 0 = Some (pair None c)
  \<Longrightarrow> d2 0 = Some (pair None (c\<lparr>epdaS_conf_scheduler:=take i (epdaS_conf_scheduler c)\<rparr>))
  \<Longrightarrow> i \<le> length (epdaS_conf_scheduler c)
  \<Longrightarrow> j\<le> i
  \<Longrightarrow> i\<le> n1
  \<Longrightarrow> i\<le> n2
  \<Longrightarrow> case_option undefined (\<lambda>x. x) (get_configuration (d2 j)) =
  case_option undefined (\<lambda>c. c\<lparr>epdaS_conf_scheduler:=take (i - j) (epdaS_conf_scheduler c)\<rparr>) (get_configuration (d1 j))"
  apply(induct j)
   apply(simp add: get_configuration_def)
  apply(rename_tac j)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>e c. d1 j = Some (pair e c)")
   apply(rename_tac j)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac j)(*strict*)
     apply(force)
    apply(rename_tac j)(*strict*)
    apply(force)
   apply(rename_tac j)(*strict*)
   apply(force)
  apply(rename_tac j)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 j = Some (pair e c)")
   apply(rename_tac j)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac j)(*strict*)
     apply(force)
    apply(rename_tac j)(*strict*)
    apply(force)
   apply(rename_tac j)(*strict*)
   apply(force)
  apply(rename_tac j)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 (Suc j) = Some (pair (Some e) c)")
   apply(rename_tac j)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac j)(*strict*)
     apply(force)
    apply(rename_tac j)(*strict*)
    apply(force)
   apply(rename_tac j)(*strict*)
   apply(force)
  apply(rename_tac j)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (Suc j) = Some (pair (Some e) c)")
   apply(rename_tac j)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac j)(*strict*)
     apply(force)
    apply(rename_tac j)(*strict*)
    apply(force)
   apply(rename_tac j)(*strict*)
   apply(force)
  apply(rename_tac j)(*strict*)
  apply(erule exE)+
  apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
  apply(subgoal_tac "epdaS_step_relation M ca eb cb")
   apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
   prefer 2
   apply(rule epdaS.position_change_due_to_step_relation)
     apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
     apply(force)
    apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
    apply(force)
   apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
   apply(force)
  apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
  apply(subgoal_tac "epdaS_step_relation M caa ec cc")
   apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in epdaS.position_change_due_to_step_relation)
     apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
     apply(force)
    apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
    apply(force)
   apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
   apply(force)
  apply(rename_tac j e ea eb ec ca caa cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
  apply(subgoal_tac "edge_event eb \<noteq> None \<and> edge_pop eb = [epda_box M] \<and> edge_push eb = [epda_box M]")
   apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
   prefer 2
   apply(simp only: valid_dfa_def)
   apply(erule conjE)+
   apply(erule_tac
      x="eb"
      in ballE)
    apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
    apply(force)
   apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
  apply(subgoal_tac "edge_event ec \<noteq> None \<and> edge_pop ec = [epda_box M] \<and> edge_push ec = [epda_box M]")
   apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
   prefer 2
   apply(simp only: valid_dfa_def)
   apply(erule conjE)+
   apply(erule_tac
      x="ec"
      in ballE)
    apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
    apply(force)
   apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac j e ea eb ec ca cb cc)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac j e ea eb ec ca cb cc y ya w)(*strict*)
  apply(case_tac cc)
  apply(rename_tac j e ea eb ec ca cb cc y ya w epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e ea eb ec ca cb y ya w epdaS_conf_schedulera)(*strict*)
  apply(rename_tac i1)
  apply(rename_tac j e ea eb ec ca cb y ya w i1)(*strict*)
  apply(case_tac cb)
  apply(rename_tac j e ea eb ec ca cb y ya w i1 epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e ea eb ec ca y ya w i1 epdaS_conf_schedulera)(*strict*)
  apply(rename_tac i2)
  apply(rename_tac j e ea eb ec ca y ya w i1 i2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac j e ea eb ec ca ya w i2)(*strict*)
  apply(case_tac ca)
  apply(rename_tac j e ea eb ec ca ya w i2 epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e ea eb ec ya w i2)(*strict*)
  apply(rename_tac h1)
  apply(rename_tac j e ea eb ec ya w h1)(*strict*)
  apply(case_tac ec)
  apply(rename_tac j e ea eb ec ya w h1 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e ea eb ya w h1 edge_trga)(*strict*)
  apply(rename_tac pop1 push1 trg1)
  apply(rename_tac j e ea eb ya pop1 push1 trg1)(*strict*)
  apply(case_tac eb)
  apply(rename_tac j e ea eb ya pop1 push1 trg1 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e ea ya pop1 push1 trg1 edge_src edge_trg)(*strict*)
  apply(rename_tac src2 trg2)
  apply(rename_tac j e ea ya pop1 push1 trg1 src2 trg2)(*strict*)
  apply(thin_tac "d1 j = Some (pair e \<lparr>epdaS_conf_state = src2, epdaS_conf_scheduler = ya # push1, epdaS_conf_stack = epda_box M # pop1\<rparr>)")
  apply(rename_tac j e ea ya pop1 push1 trg1 src2 trg2)(*strict*)
  apply(thin_tac "d1 (Suc j) = Some (pair (Some \<lparr>edge_src = src2, edge_event = Some ya, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = trg2\<rparr>) \<lparr>epdaS_conf_state = trg2, epdaS_conf_scheduler = push1, epdaS_conf_stack = epda_box M # pop1\<rparr>)")
  apply(rename_tac j e ea ya pop1 push1 trg1 src2 trg2)(*strict*)
  apply(thin_tac "d2 j = Some (pair ea \<lparr>epdaS_conf_state = src2, epdaS_conf_scheduler = ya # take (i - Suc j) push1, epdaS_conf_stack = epda_box M # pop1\<rparr>)")
  apply(rename_tac j e ea ya pop1 push1 trg1 src2 trg2)(*strict*)
  apply(thin_tac "d2 (Suc j) = Some (pair (Some \<lparr>edge_src = src2, edge_event = Some ya, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = trg1\<rparr>) \<lparr>epdaS_conf_state = trg1, epdaS_conf_scheduler = take (i - Suc j) push1, epdaS_conf_stack = epda_box M # pop1\<rparr>)")
  apply(rename_tac j e ea ya pop1 push1 trg1 src2 trg2)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def epdaS.is_forward_edge_deterministic_accessible_def)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = src2, epdaS_conf_scheduler = [ya], epdaS_conf_stack = [epda_box M]\<rparr>"
      in ballE)
   apply(rename_tac j ya trg1 src2 trg2)(*strict*)
   prefer 2
   apply(simp add: every_state_in_some_accessible_configuration_def)
   apply(erule_tac
      x="src2"
      in ballE)
    apply(rename_tac j ya trg1 src2 trg2)(*strict*)
    prefer 2
    apply(simp add: valid_pda_def valid_epda_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>edge_src = src2, edge_event = Some ya, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = trg2\<rparr>"
      and P="\<lambda>x. valid_epda_step_label M x"
      in ballE)
     apply(rename_tac j ya trg1 src2 trg2)(*strict*)
     apply(simp add: valid_epda_step_label_def)
    apply(rename_tac j ya trg1 src2 trg2)(*strict*)
    apply(force)
   apply(rename_tac j ya trg1 src2 trg2)(*strict*)
   apply(erule_tac
      x="[ya]"
      in allE)
   apply(erule impE)
    apply(rename_tac j ya trg1 src2 trg2)(*strict*)
    apply(simp add: valid_pda_def valid_epda_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>edge_src = src2, edge_event = Some ya, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = trg2\<rparr>"
      and P="\<lambda>x. valid_epda_step_label M x"
      in ballE)
     apply(rename_tac j ya trg1 src2 trg2)(*strict*)
     apply(simp add: valid_epda_step_label_def)
     apply(simp add: option_to_set_def)
    apply(rename_tac j ya trg1 src2 trg2)(*strict*)
    apply(force)
   apply(rename_tac j ya trg1 src2 trg2)(*strict*)
   apply(force)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = trg1, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = trg2, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = src2, edge_event = Some ya, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = trg1\<rparr>"
      in allE)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = src2, edge_event = Some ya, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = trg2\<rparr>"
      in allE)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(erule impE)
   apply(rename_tac j ya trg1 src2 trg2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac j ya trg1 src2 trg2)(*strict*)
  apply(simp add: epdaS_step_relation_def option_to_list_def)
  done

lemma valid_dfa_Connected_use_FEdetermR: "
  valid_dfa G
  \<Longrightarrow> every_state_in_some_accessible_configuration G
  \<Longrightarrow> e1 \<in> epda_delta G
  \<Longrightarrow> e2 \<in> epda_delta G
  \<Longrightarrow> edge_src e1=edge_src e2
  \<Longrightarrow> edge_event e1=edge_event e2
  \<Longrightarrow> edge_trg e1=p
  \<Longrightarrow> edge_trg e2=q
  \<Longrightarrow> p=q"
  apply(simp add: valid_dfa_def valid_dpda_def epdaS.is_forward_edge_deterministic_accessible_def)
  apply(simp add: every_state_in_some_accessible_configuration_def)
  apply(clarsimp)
  apply(erule_tac
      x="edge_src e1"
      in ballE)
   prefer 2
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e1"
      and P="\<lambda>e1. (\<exists>y. edge_event e1 = Some y) \<and> edge_pop e1 = [epda_box G] \<and> edge_push e1 = [epda_box G]"
      in ballE)
    apply(simp add: valid_epda_step_label_def)
   apply(force)
  apply(erule_tac
      x="case edge_event e1 of None \<Rightarrow> [] | Some x \<Rightarrow> [x]"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = edge_src e1, epdaS_conf_scheduler = case edge_event e1 of None \<Rightarrow> [] | Some x \<Rightarrow> [x], epdaS_conf_stack = [epda_box G]\<rparr>"
      in ballE)
   prefer 2
   apply(erule impE)
    prefer 2
    apply(force)
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x="e1"
      and P="\<lambda>e1. valid_epda_step_label G e1"
      in ballE)
    apply(rename_tac x)(*strict*)
    apply(simp add: valid_epda_step_label_def option_to_set_def)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = edge_trg e1, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = edge_trg e2, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      P="epdaS_step_relation G \<lparr>epdaS_conf_state = edge_src e1, epdaS_conf_scheduler = case edge_event e1 of None \<Rightarrow> [] | Some x \<Rightarrow> [x], epdaS_conf_stack = [epda_box G]\<rparr> e1 \<lparr>epdaS_conf_state = edge_trg e1, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr> \<and> epdaS_step_relation G \<lparr>epdaS_conf_state = edge_src e1, epdaS_conf_scheduler = case edge_event e1 of None \<Rightarrow> [] | Some x \<Rightarrow> [x], epdaS_conf_stack = [epda_box G]\<rparr> e2 \<lparr>epdaS_conf_state = edge_trg e2, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in impE)
   prefer 2
   apply(force)
  apply(simp add: epdaS_step_relation_def)
  apply(simp add: option_to_list_def)
  done

lemma DFA_always_box_stack: "
  valid_dfa G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> epdaS_conf_stack c = [epda_box G]"
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
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
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
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 w)(*strict*)
  apply(unfold valid_dfa_def)
  apply(erule conjE)+
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac n c e1 e2 c1 w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n c e1 e2 c1 w)(*strict*)
  apply(clarify)
  apply(rename_tac n c e1 e2 c1 w y)(*strict*)
  apply(thin_tac "valid_dpda G")
  apply(thin_tac "epdaS.derivation_initial G d")
  apply(rename_tac n c e1 e2 c1 w y)(*strict*)
  apply(thin_tac "epdaS_conf_stack c1 = edge_pop e2 @ w")
  apply(force)
  done

lemma epda_no_use_epda_box_implies_stack_content: "
  valid_epda G
  \<Longrightarrow> (\<forall>r\<in> epda_delta G. epda_box G \<notin> set (edge_pop r) \<and> epda_box G \<notin> set (edge_push r))
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>w. epda_box G \<notin> set w \<and> epdaS_conf_stack c = w @ [epda_box G]"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: epdaS_initial_configurations_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
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
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
  apply(clarsimp)
  apply(case_tac wa)
   apply(rename_tac n c e1 e2 c1 w wa)(*strict*)
   apply (metis append_self_conv in_set_conv_decomp)
  apply(rename_tac n c e1 e2 c1 w wa a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
   apply(rename_tac n c e1 e2 c1 w wa a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac n c e1 e2 c1 w wa a list)(*strict*)
  apply(thin_tac "wa=a#list")
  apply(clarsimp)
  done

definition epda_no_nil_popping_edges :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epda_no_nil_popping_edges M \<equiv>
  \<forall>e \<in> epda_delta M. edge_pop e \<noteq> []"

lemma epda_preserves_epda_box: "
  valid_epda G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> suffix (epdaS_conf_stack c) [epda_box G]"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: suffix_def)
   apply(simp add: epdaS.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: epdaS_initial_configurations_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac i c e1 e2 c1 w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w ca)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e2) ca \<or> prefix ca (edge_pop e2)")
   apply(rename_tac i c e1 e2 c1 w ca)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac i c e1 e2 c1 w ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac i c e1 e2 c1 w ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w ca)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w ca cb)(*strict*)
  apply(case_tac e2)
  apply(rename_tac i c e1 e2 c1 w ca cb edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 c1 w ca cb edge_event edge_push)(*strict*)
  apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(case_tac cb)
   apply(rename_tac i c e1 c1 w ca cb edge_event edge_push)(*strict*)
   apply(force)
  apply(rename_tac i c e1 c1 w ca cb edge_event edge_push a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 c1 ca edge_event aa ab)(*strict*)
  apply(force)
  done

lemma epda_nonempty_stack: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<noteq> []"
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply(subgoal_tac "suffix (epdaS_conf_stack c) [epda_box G]")
   apply(rename_tac d i option)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac d i option)(*strict*)
  apply(metis epda_preserves_epda_box)
  done

definition epda_no_mass_popping_edges :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epda_no_mass_popping_edges M \<equiv>
  \<forall>e \<in> epda_delta M. length (edge_pop e) \<le> Suc 0"

lemma epda_stack_in_gamma: "
  valid_epda G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> set (epdaS_conf_stack c) \<subseteq> epda_gamma G"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x q i s)(*strict*)
  apply(force)
  done

lemma F_DPDA_EB_Nonblockingness_branching_restricted_hlp: "
  valid_dpda G
  \<Longrightarrow> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<Longrightarrow> epdaS.accessible G
  \<Longrightarrow> epdaH.Nonblockingness_branching_restricted G"
  apply(rule epdaH.AX_BF_BraSBRest_DetHDB_LaOp)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
   apply(rule conjI)
    apply(simp add: epdaH.is_forward_target_deterministicHist_DB_long_def)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 n e w1 w2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(clarsimp)
   apply (metis DPDA_to_epdaH_determinism)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in epdaH_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  done

definition epda_to_des_opt :: "
  ('states, 'event, 'stack) epda option
  \<Rightarrow> 'event DES"
  where
    "epda_to_des_opt M \<equiv> (case M of None \<Rightarrow> bot | Some M \<Rightarrow> epda_to_des M)"

lemma epda_to_des_not_empty: "
  valid_epda C
  \<Longrightarrow> epda_to_des C = DES {} {}
  \<Longrightarrow> Q"
  apply(simp add: epda_to_des_def)
  apply(clarsimp)
  apply(subgoal_tac "[] \<in> epdaH.unmarked_language C")
   apply(force)
  apply(rule epda_empty_in_epdaH_unmarked_language)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

lemma epda_to_des_enforces_IsDES: "
  valid_epda G
  \<Longrightarrow> IsDES (epda_to_des G)"
  apply(simp add: IsDES_def)
  apply(simp add: DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
  apply(rule conjI)
   apply(rule epdaH.lang_inclusion)
   apply(force)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x c)(*strict*)
    prefer 2
    apply(rule_tac
      x="x"
      and v="c"
      in epdaH_unmarked_languageuage_prefix_closed)
     apply(rename_tac x c)(*strict*)
     apply(force)
    apply(rename_tac x c)(*strict*)
    apply(force)
   apply(rename_tac x c)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule_tac
      x="x"
      in exI)
  apply(clarsimp)
  done

lemma epdaH_prefixes_of_marked_words_are_unmarked_words: "
  valid_epda G
  \<Longrightarrow> x@v \<in> epdaH.marked_language G
  \<Longrightarrow> x \<in> epdaH.unmarked_language G"
  apply(simp add: epdaH.unmarked_language_def)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(simp add: epdaH_marked_effect_def epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(thin_tac "\<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_string_state c = epdaH_string_state c'")
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e c)(*strict*)
   prefer 2
   apply(rule_tac
      n="i"
      and P="\<lambda>n. n\<le>i \<and> prefix x (epdaH_conf_history (the(get_configuration(d n)))) "
      in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c k)(*strict*)
  apply(case_tac k)
   apply(rename_tac d i e c k)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac d i e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e c a)(*strict*)
   apply(case_tac a)
   apply(rename_tac d i e c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c b)(*strict*)
   apply(simp add: epdaH_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(rename_tac d i e c k nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e c nat)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="nat"
      and m="i"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d i e c nat)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
    apply(rename_tac d i e c nat)(*strict*)
    apply(force)
   apply(rename_tac d i e c nat)(*strict*)
   apply(force)
  apply(rename_tac d i e c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def prefix_def)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 c1 c2 ca)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d i e c nat e1 e2 c1 c2 ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 c1 ca epdaH_conf_state epdaH_conf_stack)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(rename_tac d i e c nat e1 e2 c1 ca epdaH_conf_statea epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 s2)
  apply(rename_tac d i e c nat e1 e2 c1 ca q2 s2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d i e c nat e1 e2 c1 ca q2 s2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac d i e c nat e1 e2 c1 ca q2 s2 q1 h1 s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 e2 ca h1 w)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d i e c nat e1 e2 ca h1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 ca h1 w edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs re po pu qt)
  apply(rename_tac d i e c nat e1 ca h1 w qs re po pu qt)(*strict*)
  apply(case_tac re)
   apply(rename_tac d i e c nat e1 ca h1 w qs re po pu qt)(*strict*)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac d i e c nat e1 ca w qs po pu qt)(*strict*)
   apply(rule_tac
      x="nat"
      in exI)
   apply(clarsimp)
   apply(erule_tac
      x="nat"
      in allE)
   apply(force)
  apply(rename_tac d i e c nat e1 ca h1 w qs re po pu qt a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      xs="ca"
      in rev_cases)
   apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a)(*strict*)
   prefer 2
   apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e c nat e1 w qs po pu qt a ys)(*strict*)
   apply(force)
  apply(rename_tac d i e c nat e1 ca h1 w qs po pu qt a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e c nat e1 h1 w qs po pu qt a)(*strict*)
  apply(rule_tac
      x="Suc nat"
      in exI)
  apply(clarsimp)
  done

lemma duplicate_markingH_to_duplicate_marking: "
  valid_epda G
  \<Longrightarrow> \<not> duplicate_markingH G
  \<Longrightarrow> \<not> duplicate_marking G"
  apply(simp add: duplicate_markingH_def duplicate_marking_def)
  apply(clarsimp)
  apply(rename_tac d i j y)(*strict*)
  apply(subgoal_tac "epdaHS.derivation_initial SSP (epdaS2epdaHS_derivation SSP SSd)" for SSP SSd)
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule epdaS2epdaHS_derivation_preserves_derivation_initial)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(subgoal_tac "epdaH.derivation_initial SSG (ATS_Branching_Versus_Linear1.Lin2BraDer epdaHvHS_Lin2BraConf SSd)" for SSG SSd)
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule epdaH_vs_epdaHS.Lin2BraConf_preserves_initiality_lift)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(erule_tac
      x="(ATS_Branching_Versus_Linear1.Lin2BraDer epdaHvHS_Lin2BraConf (epdaS2epdaHS_derivation G d))"
      in allE)
  apply(rename_tac d i j y)(*strict*)
  apply(erule impE)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule_tac
      x="j"
      in allE)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac d i j y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac d i j y)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d i j y)(*strict*)
    apply(force)
   apply(rename_tac d i j y)(*strict*)
   apply(force)
  apply(rename_tac d i j y)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j y e c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc (i+j)) = Some (pair e c)")
   apply(rename_tac d i j y e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac d i j y e c)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d i j y e c)(*strict*)
    apply(force)
   apply(rename_tac d i j y e c)(*strict*)
   apply(force)
  apply(rename_tac d i j y e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j e c ea ca)(*strict*)
  apply(simp add: get_configuration_def)
  apply(erule impE)
   apply(rename_tac d i j e c ea ca)(*strict*)
   apply(simp add: epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(rename_tac d i j e c ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i j e c ea ca a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i j e c ea ca a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j e c ea ca b)(*strict*)
   apply(simp add: get_configuration_def epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def epdaHvHS_Lin2BraConf_def)
  apply(rename_tac d i j e c ea ca)(*strict*)
  apply(erule impE)
   apply(rename_tac d i j e c ea ca)(*strict*)
   apply(simp add: epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(rename_tac d i j e c ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i j e c ea ca a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i j e c ea ca a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j e c ea ca b)(*strict*)
   apply(simp add: get_configuration_def epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def epdaHvHS_Lin2BraConf_def)
  apply(rename_tac d i j e c ea ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac d i j e c ea ca)(*strict*)
   apply(simp add: epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(rename_tac d i j e c ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i j e c ea ca a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i j e c ea ca a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i j e c ea ca b)(*strict*)
   apply(simp add: epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def epdaHvHS_Lin2BraConf_def)
  apply(rename_tac d i j e c ea ca)(*strict*)
  apply(simp add: epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac d i j e c ea ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i j e c ea ca a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i j e c ea ca a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i j e c ea ca b)(*strict*)
  apply(simp add: epdaS2epdaHS_derivation_def get_configuration_def ATS_Branching_Versus_Linear1.Lin2BraDer_def epdaS.derivation_initial_def epdaS_initial_configurations_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def epdaHvHS_Lin2BraConf_def)
  done

lemma epdaH_trans_der_context: "
  valid_epda G
  \<Longrightarrow> epdaH.trans_der G d c \<pi> c'
  \<Longrightarrow> C = (\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>)
  \<Longrightarrow> set s \<subseteq> epda_gamma G
  \<Longrightarrow> set h \<subseteq> epda_events G
  \<Longrightarrow> C c = c0
  \<Longrightarrow> C c' = c0'
  \<Longrightarrow> epdaH.trans_der G (derivation_map d C) c0 \<pi> c0'"
  apply(rule epdaH.trans_der_context)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(rename_tac a e b)(*strict*)
     apply(simp add: epdaH_step_relation_def)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac ca)(*strict*)
    apply(simp add: epdaH_configurations_def)
    apply(clarsimp)
   apply(force)
  apply(force)
  done

lemma epdaH_trans_der_concatExtend: "
  valid_epda G
  \<Longrightarrow> epdaH.trans_der G d1 c1 \<pi>1 c1'
  \<Longrightarrow> epdaH.trans_der G d2 c2 \<pi>2 c2'
  \<Longrightarrow> epdaH_conf_state c1'=epdaH_conf_state c2
  \<Longrightarrow> epdaH_conf_history c1'=h@epdaH_conf_history c2
  \<Longrightarrow> epdaH_conf_stack c1'=epdaH_conf_stack c2@s
  \<Longrightarrow> epdaH.trans_der G (derivation_append d1 (derivation_map d2 (\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>)) (length \<pi>1)) c1 (\<pi>1@\<pi>2) ((\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>) c2')"
  apply(subgoal_tac "epdaH.trans_der G (derivation_map d2 (\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>)) ((\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>) c2) \<pi>2 ((\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>) c2')")
   prefer 2
   apply(rule epdaH_trans_der_context)
         apply(force)
        apply(force)
       apply(force)
      apply(subgoal_tac "c1' \<in> epdaH_configurations G")
       apply(simp add: epdaH_configurations_def)
       apply(clarsimp)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(simp add: epdaH.trans_der_def)
      apply(clarsimp)
      apply(rename_tac e ea)(*strict*)
      apply(rule epdaH.belongs_configurations)
       apply(rename_tac e ea)(*strict*)
       apply(force)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(subgoal_tac "c1' \<in> epdaH_configurations G")
      apply(simp add: epdaH_configurations_def)
      apply(clarsimp)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(simp add: epdaH.trans_der_def)
     apply(clarsimp)
     apply(rename_tac e ea)(*strict*)
     apply(rule epdaH.belongs_configurations)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "epdaH.trans_der G d2 c2 \<pi>2 c2'")
  apply(subgoal_tac "epdaH.trans_der SSG (derivation_append SSd1 SSd2 (length SSrenPI10)) SSc1 (SSrenPI10 @ SSrenPI20) SSc2'" for SSG SSd1 SSd2 SSc1 SSrenPI10 SSrenPI20 SSc2')
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="(derivation_map d2 (\<lambda>c. c\<lparr>epdaH_conf_history := h @ epdaH_conf_history c, epdaH_conf_stack := epdaH_conf_stack c @ s\<rparr>))"
      in epdaH.trans_der_concat)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epdaH_trans_der_concatExtend_prime: "
  valid_epda G
  \<Longrightarrow> epdaH.trans_der G d1 c1 \<pi>1 c1'
  \<Longrightarrow> epdaH.trans_der G d2 c2 \<pi>2 c2'
  \<Longrightarrow> epdaH_conf_state c1'=epdaH_conf_state c2
  \<Longrightarrow> epdaH_conf_history c1'=h@epdaH_conf_history c2
  \<Longrightarrow> epdaH_conf_stack c1'=epdaH_conf_stack c2@s
  \<Longrightarrow> \<exists>d. epdaH.trans_der G d c1 (\<pi>1@\<pi>2) ((\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>) c2')"
  apply(rule_tac
      x="(derivation_append d1 (derivation_map d2 (\<lambda>c. c\<lparr>epdaH_conf_history:=h@(epdaH_conf_history c),epdaH_conf_stack:=(epdaH_conf_stack c)@s\<rparr>)) (length \<pi>1))"
      in exI)
  apply(rule epdaH_trans_der_concatExtend)
       apply(force)+
  done

lemma epdaH_nonconflicting_reachable_derivations_are_mutual_prefixing: "
  valid_dpda G
  \<Longrightarrow> epdaH.trans_der G d \<lparr>epdaH_conf_state=epda_initial G,epdaH_conf_history=[],epdaH_conf_stack=[epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state=q,epdaH_conf_history=h,epdaH_conf_stack=[X]@s\<rparr>
  \<Longrightarrow> epdaH.trans_der G d1 \<lparr>epdaH_conf_state=q,epdaH_conf_history=[],epdaH_conf_stack=[X]\<rparr> \<pi>1 \<lparr>epdaH_conf_state=q',epdaH_conf_history=[],epdaH_conf_stack=s1\<rparr>
  \<Longrightarrow> epdaH.trans_der G d2 \<lparr>epdaH_conf_state=q,epdaH_conf_history=[],epdaH_conf_stack=[X]\<rparr> \<pi>2 \<lparr>epdaH_conf_state=q',epdaH_conf_history=b#h',epdaH_conf_stack=s2\<rparr>
  \<Longrightarrow> strict_prefix \<pi>1 \<pi>2"
  apply(subgoal_tac "\<exists>d1'. epdaH.trans_der G d1' \<lparr>epdaH_conf_state=epda_initial G,epdaH_conf_history=[],epdaH_conf_stack=[epda_box G]\<rparr> (\<pi>@\<pi>1) \<lparr>epdaH_conf_state=q',epdaH_conf_history=h,epdaH_conf_stack=s1@s\<rparr>")
   apply(subgoal_tac "\<exists>d2'. epdaH.trans_der G d2' \<lparr>epdaH_conf_state=epda_initial G,epdaH_conf_history=[],epdaH_conf_stack=[epda_box G]\<rparr> (\<pi>@\<pi>2) \<lparr>epdaH_conf_state=q',epdaH_conf_history=h@b#h',epdaH_conf_stack=s2@s\<rparr>")
    apply(thin_tac "epdaH.trans_der G d \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state = q, epdaH_conf_history = h, epdaH_conf_stack = [X] @ s\<rparr>")
    apply(thin_tac "epdaH.trans_der G d1 \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = [X]\<rparr> \<pi>1 \<lparr>epdaH_conf_state = q', epdaH_conf_history = [], epdaH_conf_stack = s1\<rparr>")
    apply(thin_tac "epdaH.trans_der G d2 \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = [X]\<rparr> \<pi>2 \<lparr>epdaH_conf_state = q', epdaH_conf_history = b # h', epdaH_conf_stack = s2\<rparr>")
    apply(clarsimp)
    apply(rename_tac d1' d2')(*strict*)
    apply(simp add: epdaH.trans_der_def)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea)(*strict*)
    apply(case_tac "length \<pi> + length \<pi>1 = length \<pi> + length \<pi>2")
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(subgoal_tac "Some (pair e \<lparr>epdaH_conf_state = q', epdaH_conf_history = h, epdaH_conf_stack = s1 @ s\<rparr>)=Some (pair ea \<lparr>epdaH_conf_state = q', epdaH_conf_history = h @ b # h', epdaH_conf_stack = s2 @ s\<rparr>)")
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(rule_tac
      x="0"
      and m="length \<pi>+length \<pi>2"
      and n="length \<pi>+length \<pi>1"
      and y="0"
      and G="G"
      and ?d1.0="d1'"
      and ?d2.0="d2'"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac d1' d2' e ea)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d1' d2' e ea)(*strict*)
               apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(simp add: valid_dpda_def valid_pda_def)
             apply(rule_tac
      t="epdaH.is_forward_deterministicHist_SB G"
      and s="epdaH.is_forward_deterministicHist_DB G"
      in ssubst)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply (rule epdaH.is_forward_deterministic_correspond_DB_SB)
              apply(force)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
             apply(rule conjI)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply (metis epdaH_is_forward_target_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(rule epdaHS2HF_FEdetermHist)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministic_accessible G")
              apply(rename_tac d1' d2' e ea)(*strict*)
              prefer 2
              apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
               apply(rename_tac d1' d2' e ea)(*strict*)
               prefer 2
               apply(simp add: valid_simple_dpda_def valid_dpda_def)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(rule_tac
      ?G1.0="G"
      in epdaS_vs_epdaHS.preserve_FEdetermR1)
               apply(rename_tac d1' d2' e ea)(*strict*)
               apply(simp add: valid_dpda_to_valid_pda valid_pda_to_valid_epda valid_simple_dpda_to_valid_dpda)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(force)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministicHist_DB_long G")
              apply(rename_tac d1' d2' e ea)(*strict*)
              prefer 2
              apply(clarsimp)
              apply (metis epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(force)
            apply(rename_tac d1' d2' e ea)(*strict*)
            apply(force)
           apply(rename_tac d1' d2' e ea)(*strict*)
           apply(force)
          apply(rename_tac d1' d2' e ea)(*strict*)
          apply(force)
         apply(rename_tac d1' d2' e ea)(*strict*)
         apply(force)
        apply(rename_tac d1' d2' e ea)(*strict*)
        apply(force)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      x="b#h'"
      in bexI)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(simp add: epda_effects_def)
      apply(subgoal_tac "\<lparr>epdaH_conf_state = q', epdaH_conf_history = h @ b # h', epdaH_conf_stack = s2 @ s\<rparr> \<in> epdaH_configurations G")
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(simp add: epdaH_configurations_def)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(rule_tac
      d="d2'"
      in epdaH.belongs_configurations)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea)(*strict*)
    apply(clarsimp)
    apply(case_tac "length \<pi> + length \<pi>1 < length \<pi> + length \<pi>2")
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "drop 0 (get_labels d1' (0+((length \<pi> + length \<pi>1)))) = drop 0 (get_labels d2' (0+(length \<pi> + length \<pi>1))) \<and> (\<forall>i\<le>(length \<pi> + length \<pi>1). d1' (0+i) = d2' (0+i))")
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(clarsimp)
      apply(simp add: strict_prefix_def)
      apply(rule_tac
      x="drop(length \<pi>1) \<pi>2"
      in exI)
      apply(rule conjI)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(subgoal_tac "get_labels d2' (length \<pi> + length \<pi>1) = map Some \<pi> @ map Some (take(length \<pi>1) \<pi>2)")
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(clarsimp)
       apply (metis append_Nil append_take_drop_id_hlp length_append length_map length_map_Some length_shorter_append2 map_append takeShorter)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(rule_tac
      m="length \<pi>2-length \<pi>1"
      and v="map Some (drop(length \<pi>1)\<pi>2)"
      in get_labels_drop_tail)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(clarsimp)
       apply (metis append_Nil append_take_drop_id_hlp length_append length_map length_map_Some length_shorter_append2 map_append takeShorter)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(rule_tac
      x="0"
      and m="length \<pi>+length \<pi>2"
      and n="length \<pi>+length \<pi>1"
      and y="0"
      and G="G"
      and ?d1.0="d1'"
      and ?d2.0="d2'"
      in epdaH.same_steps_for_compatible_histories)
                apply(rename_tac d1' d2' e ea)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d1' d2' e ea)(*strict*)
               apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(simp add: valid_dpda_def valid_pda_def)
             apply(rule_tac
      t="epdaH.is_forward_deterministicHist_SB G"
      and s="epdaH.is_forward_deterministicHist_DB G"
      in ssubst)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply (rule epdaH.is_forward_deterministic_correspond_DB_SB)
              apply(force)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
             apply(rule conjI)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply (metis epdaH_is_forward_target_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(rule epdaHS2HF_FEdetermHist)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministic_accessible G")
              apply(rename_tac d1' d2' e ea)(*strict*)
              prefer 2
              apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
               apply(rename_tac d1' d2' e ea)(*strict*)
               prefer 2
               apply(simp add: valid_simple_dpda_def valid_dpda_def)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(rule_tac
      ?G1.0="G"
      in epdaS_vs_epdaHS.preserve_FEdetermR1)
               apply(rename_tac d1' d2' e ea)(*strict*)
               apply (simp add: valid_dpda_to_valid_pda valid_pda_to_valid_epda valid_simple_dpda_to_valid_dpda)
              apply(rename_tac d1' d2' e ea)(*strict*)
              apply(force)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministicHist_DB_long G")
              apply(rename_tac d1' d2' e ea)(*strict*)
              prefer 2
              apply(clarsimp)
              apply (metis epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea)(*strict*)
             apply(force)
            apply(rename_tac d1' d2' e ea)(*strict*)
            apply(force)
           apply(rename_tac d1' d2' e ea)(*strict*)
           apply(force)
          apply(rename_tac d1' d2' e ea)(*strict*)
          apply(force)
         apply(rename_tac d1' d2' e ea)(*strict*)
         apply(force)
        apply(rename_tac d1' d2' e ea)(*strict*)
        apply(force)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      x="b#h'"
      in bexI)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(simp add: epda_effects_def)
      apply(subgoal_tac "\<lparr>epdaH_conf_state = q', epdaH_conf_history = h @ b # h', epdaH_conf_stack = s2 @ s\<rparr> \<in> epdaH_configurations G")
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(simp add: epdaH_configurations_def)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(rule_tac
      d="d2'"
      in epdaH.belongs_configurations)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length \<pi>2 < length \<pi>1")
     apply(rename_tac d1' d2' e ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d1' d2' e ea)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "False")
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea)(*strict*)
    apply(subgoal_tac "\<exists>k\<le>(length \<pi>+length \<pi>2). (\<forall>i<k. \<not> (case SSd i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> SSP c)) \<and> (case SSd k of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> SSP c)" for SSd SSP)
     apply(rename_tac d1' d2' e ea)(*strict*)
     prefer 2
     apply(rule_tac
      d="d2'"
      and P="\<lambda>c. \<exists>w. epdaH_conf_history c=h@[b]@w"
      in epdaH.existence_of_earliest_satisfaction_point)
       apply(rename_tac d1' d2' e ea)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k)(*strict*)
    apply(case_tac k)
     apply(rename_tac d1' d2' e ea k)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1' d2' e ea k nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea nat)(*strict*)
    apply(rename_tac k)
    apply(rename_tac d1' d2' e ea k)(*strict*)
    apply(erule_tac
      x="k"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2' k = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2" for SSd SSn)
     apply(rename_tac d1' d2' e ea k)(*strict*)
     prefer 2
     apply(rule_tac
      m="length \<pi>+length \<pi>2"
      in epdaH.step_detail_before_some_position)
       apply(rename_tac d1' d2' e ea k)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea k)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w)(*strict*)
    apply(subgoal_tac "epdaH_conf_history c1 = h \<and> w = []")
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w)(*strict*)
     prefer 2
     apply(simp add: epdaH_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa)(*strict*)
     apply(case_tac "edge_event e2")
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa)(*strict*)
      apply(simp add: option_to_list_def)
      apply(erule_tac
      x="w"
      in allE)
      apply(force)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa a)(*strict*)
     apply(simp add: option_to_list_def)
     apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. w=w'@[a'])")
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa a)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa a)(*strict*)
     apply(erule disjE)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa a)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w wa a)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 wa a w')(*strict*)
     apply(erule_tac
      x="w'"
      in allE)
     apply(force)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 w)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1' k = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> epdaH_step_relation G c1 e2 c2" for SSd SSn)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2)(*strict*)
     prefer 2
     apply(rule_tac
      m="length \<pi>+length \<pi>1"
      in epdaH.step_detail_before_some_position)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
    apply(subgoal_tac "\<exists>h\<in> epda_effects SSG. epdaH_conf_history SSc' = epdaH_conf_history SSc @ h" for SSG SSc' SSc)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc 0"
      and n="k"
      and d="d1'"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
         apply(force)
        apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
        apply(force)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
       prefer 2
       apply(simp add: get_configuration_def)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
      apply(rule_tac
      d="d1'"
      in epdaH.belongs_configurations)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
    apply(subgoal_tac "\<exists>h\<in> epda_effects SSG. epdaH_conf_history SSc' = epdaH_conf_history SSc @ h" for SSG SSc' SSc)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
     prefer 2
     apply(rule_tac
      m="length \<pi>+length \<pi>1-Suc k"
      and n="Suc k"
      and d="d1'"
      in epdaH.steps_extend_history_derivation)
         apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
         apply(force)
        apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
        apply(force)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
       prefer 2
       apply(simp add: get_configuration_def)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
      apply(rule_tac
      d="d1'"
      in epdaH.belongs_configurations)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
     apply(rule_tac
      t="(Suc k + (length \<pi> + length \<pi>1 - Suc k))"
      and s="length \<pi> + length \<pi>1"
      in ssubst)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
    apply(subgoal_tac "d1' k = d2' k")
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
     prefer 2
     apply(subgoal_tac "drop 0 (get_labels d1' (0+k)) = drop 0 (get_labels d2' (0+(k))) \<and> (\<forall>i\<le>(k). d1' (0+i) = d2' (0+i))")
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
     apply(rule_tac
      x="0"
      and m="length \<pi>+length \<pi>2"
      and n="k"
      and y="0"
      and G="G"
      and ?d1.0="d1'"
      and ?d2.0="d2'"
      in epdaH.same_steps_for_compatible_histories)
                apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
               apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
             apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
             apply(simp add: valid_dpda_def valid_pda_def)
             apply(rule_tac
      t="epdaH.is_forward_deterministicHist_SB G"
      and s="epdaH.is_forward_deterministicHist_DB G"
      in ssubst)
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              apply (rule epdaH.is_forward_deterministic_correspond_DB_SB)
              apply(force)
             apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
             apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
             apply(rule conjI)
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              apply (metis epdaH_is_forward_target_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
             apply(rule epdaHS2HF_FEdetermHist)
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
             apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministic_accessible G")
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              prefer 2
              apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
               apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
               prefer 2
               apply(simp add: valid_simple_dpda_def valid_dpda_def)
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              apply(rule_tac
      ?G1.0="G"
      in epdaS_vs_epdaHS.preserve_FEdetermR1)
               apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
               apply(simp add: valid_dpda_to_valid_pda valid_pda_to_valid_epda valid_simple_dpda_to_valid_dpda)
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              apply(force)
             apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministicHist_DB_long G")
              apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
              prefer 2
              apply(clarsimp)
              apply (metis epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
             apply(force)
            apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
            apply(force)
           apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
           apply(force)
          apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
          apply(force)
         apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
         apply(force)
        apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
        apply(force)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
      apply(simp add: get_configuration_def)
      apply(simp add: epda_effects_def)
      apply(subgoal_tac "\<lparr>epdaH_conf_state = q', epdaH_conf_history = epdaH_conf_history c1a @ h @ ha @ b # h', epdaH_conf_stack = s2 @ s\<rparr> \<in> epdaH_configurations G")
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
       apply(simp add: epdaH_configurations_def)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
      apply(rule_tac
      d="d2'"
      in epdaH.belongs_configurations)
       apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea k e1 e2 c1 c2 e1a e2a c1a c2a h ha)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
    apply(subgoal_tac "d1' (Suc k) = d2' (Suc k)")
     apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
     prefer 2
     apply(subgoal_tac "drop 0 (get_labels d1' (0+(Suc k))) = drop 0 (get_labels d2' (0+(Suc k))) \<and> (\<forall>i\<le>(Suc k). d1' (0+i) = d2' (0+i))")
      apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
     apply(rule_tac
      x="0"
      and m="length \<pi>+length \<pi>2"
      and n="Suc k"
      and y="0"
      and G="G"
      and ?d1.0="d1'"
      and ?d2.0="d2'"
      in epdaH.same_steps_for_compatible_histories)
                apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
               apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
             apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
             apply(simp add: valid_dpda_def valid_pda_def)
             apply(rule_tac
      t="epdaH.is_forward_deterministicHist_SB G"
      and s="epdaH.is_forward_deterministicHist_DB G"
      in ssubst)
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              apply (rule epdaH.is_forward_deterministic_correspond_DB_SB)
              apply(force)
             apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
             apply(simp add: epdaH.is_forward_deterministicHist_DB_def)
             apply(rule conjI)
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              apply (metis epdaH_is_forward_target_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
             apply(rule epdaHS2HF_FEdetermHist)
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
             apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministic_accessible G")
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              prefer 2
              apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
               apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
               prefer 2
               apply(simp add: valid_simple_dpda_def valid_dpda_def)
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              apply(rule_tac
      ?G1.0="G"
      in epdaS_vs_epdaHS.preserve_FEdetermR1)
               apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
               apply(simp add: valid_dpda_to_valid_pda valid_pda_to_valid_epda valid_simple_dpda_to_valid_dpda)
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              apply(force)
             apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
             apply(subgoal_tac "epdaHS.is_forward_edge_deterministicHist_DB_long G")
              apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
              prefer 2
              apply(clarsimp)
              apply (metis epdaHS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
             apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
             apply(force)
            apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
            apply(force)
           apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
           apply(force)
          apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
          apply(force)
         apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
         apply(force)
        apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
        apply(force)
       apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
      apply(simp add: get_configuration_def)
      apply(simp add: epda_effects_def)
      apply(subgoal_tac "\<lparr>epdaH_conf_state = q', epdaH_conf_history = epdaH_conf_history c1a @ b # h', epdaH_conf_stack = s2 @ s\<rparr> \<in> epdaH_configurations G")
       apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
       apply(simp add: epdaH_configurations_def)
      apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
      apply(rule_tac
      d="d2'"
      in epdaH.belongs_configurations)
       apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac d1' d2' e ea k e2 c2 e1a e2a c1a c2a)(*strict*)
    apply(clarsimp)
   apply(thin_tac "\<exists>d1'. epdaH.trans_der G d1' \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr> (\<pi> @ \<pi>1) \<lparr>epdaH_conf_state = q', epdaH_conf_history = h, epdaH_conf_stack = s1 @ s\<rparr>")
   apply(thin_tac "epdaH.trans_der G d1 \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = [X]\<rparr> \<pi>1 \<lparr>epdaH_conf_state = q', epdaH_conf_history = [], epdaH_conf_stack = s1\<rparr>")
   apply(subgoal_tac "\<exists>d. epdaH.trans_der SSG d SSc1 (SSrenPI10 @ SSrenPI20) (SSc2'\<lparr>epdaH_conf_history := SSh @ epdaH_conf_history SSc2', epdaH_conf_stack := epdaH_conf_stack SSc2' @ SSs\<rparr>)" for SSG SSc1 SSrenPI10 SSrenPI20 SSh SSc2' SSs)
    prefer 2
    apply(rule_tac
      ?d1.0="d"
      and ?d2.0="d2"
      and h="h"
      and s="s"
      in epdaH_trans_der_concatExtend_prime)
         apply(simp add: valid_dpda_def valid_pda_def)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
  apply(thin_tac "epdaH.trans_der G d2 \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = [X]\<rparr> \<pi>2 \<lparr>epdaH_conf_state = q', epdaH_conf_history = b # h', epdaH_conf_stack = s2\<rparr>")
  apply(subgoal_tac "\<exists>d. epdaH.trans_der SSG d SSc1 (SSrenPI10 @ SSrenPI20) (SSc2'\<lparr>epdaH_conf_history := SSh @ epdaH_conf_history SSc2', epdaH_conf_stack := epdaH_conf_stack SSc2' @ SSs\<rparr>)" for SSG SSc1 SSrenPI10 SSrenPI20 SSh SSc2' SSs)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="d1"
      and h="h"
      and s="s"
      in epdaH_trans_der_concatExtend_prime)
        apply(simp add: valid_dpda_def valid_pda_def)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma epda_is_forward_target_deterministic: "
  valid_epda G
  \<Longrightarrow> epdaH.is_forward_target_deterministic G"
  apply(simp add: epdaH.is_forward_target_deterministic_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  done

lemma epdaHS2epdaS_derivation_preserves_derivation: "
  valid_epda P
  \<Longrightarrow> epdaHS.derivation P d
  \<Longrightarrow> epdaS.derivation P (epdaHS2epdaS_derivation d)"
  apply(simp add: epdaHS2epdaS_derivation_def)
  apply(simp add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaHS.derivation_def)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(erule_tac
      x="0"
      in allE)
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
      m="Suc nat"
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

lemma epdaS2epdaHS_derivation_preserves_derivation: "
  valid_epda P
  \<Longrightarrow> epdaS.belongs P d
  \<Longrightarrow> epdaS.derivation P d
  \<Longrightarrow> epdaHS.derivation P (epdaS2epdaHS_derivation P d)"
  apply(simp add: epdaS2epdaHS_derivation_def)
  apply(simp add: epdaHS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaS.derivation_def)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(erule_tac
      x="0"
      in allE)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(erule_tac
      x="0"
      in allE)
   apply(force)
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
      m="Suc nat"
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
      j="nat"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 w c)(*strict*)
     apply(force)
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
      j="Suc 0"
      in epdaS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
     apply(force)
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
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(simp add: epdaS_string_state_def)
  apply(rule_tac
      t="right_quotient_word (wa @ option_to_list (edge_event e2) @ epdaS_conf_scheduler c2) (epdaS_conf_scheduler c2)"
      and s="Some(wa @ option_to_list (edge_event e2))"
      in ssubst)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule_tac
      t="right_quotient_word (wa @ option_to_list (edge_event e2) @ epdaS_conf_scheduler c2) (option_to_list (edge_event e2) @ epdaS_conf_scheduler c2)"
      and s="Some wa"
      in ssubst)
   apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 w c wa)(*strict*)
  apply(force)
  done

lemma epdaS2epdaHS_derivation_preserves_belongs: "
  valid_epda P
  \<Longrightarrow> epdaS.belongs P d
  \<Longrightarrow> epdaS.derivation P d
  \<Longrightarrow> epdaHS.belongs P (epdaS2epdaHS_derivation P d)"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac epdaHS.derivation_belongs)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    prefer 3
    apply(rule epdaS2epdaHS_derivation_preserves_derivation)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(simp add: epdaS2epdaHS_derivation_def)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      t="right_quotient_word (epdaS_conf_scheduler c) (epdaS_conf_scheduler c)"
      and s="Some []"
      in ssubst)
   apply(rename_tac c)(*strict*)
   apply (metis right_quotient_word_full)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "c \<in> epdaS_configurations P")
   apply(rename_tac c)(*strict*)
   apply(simp add: epdaHS_configurations_def epdaS_configurations_def)
   apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule epdaS.belongs_configurations)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma translate_epdaS_der_to_epdaH_der: "
valid_dpda G
  \<Longrightarrow> epdaS.derivation G d
  \<Longrightarrow> epdaS.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>epdaS_conf_state = q1, epdaS_conf_scheduler = hx, epdaS_conf_stack = ba # s\<rparr>)
  \<Longrightarrow> d j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # s\<rparr>)
  \<Longrightarrow> \<forall>k\<le>j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ ba # s)
  \<Longrightarrow> d (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = q2, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)
  \<Longrightarrow> \<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = hx, epdaH_conf_stack = ba # s\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # s)) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = hx, epdaH_conf_stack = s\<rparr>)"
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(rule_tac
      x="epdaH_vs_epdaHS.Lin2BraDer (epdaS2epdaHS_derivation G d)"
      in exI)
  apply(rule context_conjI)
   apply(rule epdaH_vs_epdaHS.Lin2BraConf_preserves_steps_lift)
     apply(force)
    apply(rule epdaS2epdaHS_derivation_preserves_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(rule epdaS2epdaHS_derivation_preserves_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule epdaH_vs_epdaHS.Lin2BraDer_preserves_belongs)
     apply(force)
    apply(rule epdaS2epdaHS_derivation_preserves_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(rule epdaS2epdaHS_derivation_preserves_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: get_configuration_def epdaHvHS_Lin2BraConf_def epdaH_vs_epdaHS.Lin2BraDer_def epdaS2epdaHS_derivation_def derivation_map_def)
   apply(rule_tac
      t="right_quotient_word hx hx"
      and s="Some []"
      in ssubst)
    apply (metis right_quotient_word_full)
   apply(force)
  apply(rule conjI)
   apply(simp add: get_configuration_def epdaHvHS_Lin2BraConf_def epdaH_vs_epdaHS.Lin2BraDer_def epdaS2epdaHS_derivation_def derivation_map_def)
   apply(rule_tac
      t="right_quotient_word hx []"
      and s="Some hx"
      in ssubst)
    apply (metis right_quotient_word_neutral)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac k ea c)(*strict*)
   apply(subgoal_tac "\<exists>e c. d k = Some (pair e c)")
    apply(rename_tac k ea c)(*strict*)
    prefer 2
    apply(rule_tac
      m="j"
      in epdaS.pre_some_position_is_some_position)
      apply(rename_tac k ea c)(*strict*)
      apply(force)
     apply(rename_tac k ea c)(*strict*)
     apply(force)
    apply(rename_tac k ea c)(*strict*)
    apply(force)
   apply(rename_tac k ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac k ea c eaa ca)(*strict*)
   apply(erule_tac
      x="k"
      in allE)
   apply(clarsimp)
   apply(rename_tac k ea c eaa ca w)(*strict*)
   apply(simp add: get_configuration_def epdaHvHS_Lin2BraConf_def epdaH_vs_epdaHS.Lin2BraDer_def epdaS2epdaHS_derivation_def derivation_map_def)
   apply(clarsimp)
  apply(simp add: get_configuration_def epdaHvHS_Lin2BraConf_def epdaH_vs_epdaHS.Lin2BraDer_def epdaS2epdaHS_derivation_def derivation_map_def)
  apply(clarsimp)
  apply(rule_tac
      t="right_quotient_word hx []"
      and s="Some hx"
      in ssubst)
   apply (metis right_quotient_word_neutral)
  apply(force)
  done

lemma DPDA_edge_pop_single: "
  valid_dpda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> \<exists>x. edge_pop e=[x]"
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(case_tac "e")
   apply(rename_tac edge_src edge_event edge_popa edge_push edge_trg)(*strict*)
   apply(clarsimp)
   apply(rename_tac edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
   apply(case_tac edge_pop)
    apply(rename_tac edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
    apply(clarsimp)
   apply(rename_tac edge_src edge_event edge_pop edge_push edge_trg a list)(*strict*)
   apply(clarsimp)
  apply(force)
  done

lemma epdaH_drop_unused_stack: "
       valid_dpda G
  \<Longrightarrow> \<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = \<alpha>, epdaH_conf_stack = ba # s\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # s)) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = \<alpha>, epdaH_conf_stack = s\<rparr>)
  \<Longrightarrow> \<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = [ba]\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = \<alpha>, epdaH_conf_stack = [ba]\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ [ba])) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = \<alpha>, epdaH_conf_stack = []\<rparr>)"
  apply(clarsimp)
  apply(rename_tac d1')(*strict*)
  apply(rule_tac
      x="derivation_map (derivation_take d1' (Suc j)) (\<lambda>c. c\<lparr>epdaH_conf_stack:=butn(epdaH_conf_stack c)(length s)\<rparr>)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac d1')(*strict*)
   apply(rule_tac
      P="\<lambda>c. (\<exists>w. epdaH_conf_stack c = w @ ba # s)"
      in epdaH.derivation_map_preserves_derivation23_VAR2)
     apply(rename_tac d1')(*strict*)
     apply(force)
    apply(rename_tac d1')(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' i ea c)(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
   apply(rename_tac d1')(*strict*)
   apply(clarsimp)
   apply(rename_tac d1' a ea b w)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1' a ea b w wa)(*strict*)
   apply(case_tac a)
   apply(rename_tac d1' a ea b w wa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1' ea b w wa epdaH_conf_historya)(*strict*)
   apply(case_tac b)
   apply(rename_tac d1' ea b w wa epdaH_conf_historya epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1' ea w wa)(*strict*)
   apply(rule_tac
      t="edge_pop ea @ wa"
      and s="w @ ba # s"
      in ssubst)
    apply(rename_tac d1' ea w wa)(*strict*)
    apply(force)
   apply(rename_tac d1' ea w wa)(*strict*)
   apply(rule_tac
      t="butn (w @ ba # s) (length s)"
      and s="w@[ba]"
      in ssubst)
    apply(rename_tac d1' ea w wa)(*strict*)
    apply(rule_tac
      t="w@ba#s"
      and s="(w@[ba])@s"
      in ssubst)
     apply(rename_tac d1' ea w wa)(*strict*)
     apply(force)
    apply(rename_tac d1' ea w wa)(*strict*)
    apply (metis butn_prefix_closureise)
   apply(rename_tac d1' ea w wa)(*strict*)
   apply(subgoal_tac "\<exists>x. edge_pop ea=[x]")
    apply(rename_tac d1' ea w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' ea w wa x)(*strict*)
    apply(case_tac w)
     apply(rename_tac d1' ea w wa x)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1' ea)(*strict*)
     apply (metis butn_prefix_closureise)
    apply(rename_tac d1' ea w wa x a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1' ea x list)(*strict*)
    apply(rule_tac
      t="edge_push ea @ list @ ba # s"
      and s="(edge_push ea @ list @ [ba]) @ s"
      in ssubst)
     apply(rename_tac d1' ea x list)(*strict*)
     apply(force)
    apply(rename_tac d1' ea x list)(*strict*)
    apply (metis butn_prefix_closureise)
   apply(rename_tac d1' ea w wa)(*strict*)
   apply(rule DPDA_edge_pop_single)
    apply(rename_tac d1' ea w wa)(*strict*)
    apply(force)
   apply(rename_tac d1' ea w wa)(*strict*)
   apply(force)
  apply(rename_tac d1')(*strict*)
  apply(rule conjI)
   apply(rename_tac d1')(*strict*)
   apply(rule epdaH.derivation_belongs)
      apply(rename_tac d1')(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d1')(*strict*)
     apply(simp add: derivation_map_def derivation_take_def)
    apply(rename_tac d1')(*strict*)
    apply(subgoal_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr> \<in> epdaH_configurations G")
     apply(rename_tac d1')(*strict*)
     apply(simp add: epdaH_configurations_def)
     apply(rule_tac
      t="ba#s"
      and s="[ba]@s"
      in ssubst)
      apply(rename_tac d1')(*strict*)
      apply(force)
     apply(rename_tac d1')(*strict*)
     apply(rule_tac
      t="butn ([ba] @ s) (length s)"
      and s="[ba]"
      in ssubst)
      apply(rename_tac d1')(*strict*)
      apply (metis butn_prefix_closureise)
     apply(rename_tac d1')(*strict*)
     apply(force)
    apply(rename_tac d1')(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d1')(*strict*)
     apply(force)
    apply(rename_tac d1')(*strict*)
    apply(force)
   apply(rename_tac d1')(*strict*)
   apply(force)
  apply(rename_tac d1')(*strict*)
  apply(rule conjI)
   apply(rename_tac d1')(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(rule_tac
      t="ba#s"
      and s="[ba]@s"
      in ssubst)
    apply(rename_tac d1')(*strict*)
    apply(force)
   apply(rename_tac d1')(*strict*)
   apply(rule_tac
      t="butn ([ba] @ s) (length s)"
      and s="[ba]"
      in ssubst)
    apply(rename_tac d1')(*strict*)
    apply (metis butn_prefix_closureise)
   apply(rename_tac d1')(*strict*)
   apply(force)
  apply(rename_tac d1')(*strict*)
  apply(rule conjI)
   apply(rename_tac d1')(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(rule_tac
      t="ba#s"
      and s="[ba]@s"
      in ssubst)
    apply(rename_tac d1')(*strict*)
    apply(force)
   apply(rename_tac d1')(*strict*)
   apply(rule_tac
      t="butn ([ba] @ s) (length s)"
      and s="[ba]"
      in ssubst)
    apply(rename_tac d1')(*strict*)
    apply (metis butn_prefix_closureise)
   apply(rename_tac d1')(*strict*)
   apply(force)
  apply(rename_tac d1')(*strict*)
  apply(rule conjI)
   apply(rename_tac d1')(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(clarsimp)
   apply(rename_tac d1' k ea c)(*strict*)
   apply(erule_tac
      x="k"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. d1' k = Some (pair e c)")
    apply(rename_tac d1' k ea c)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc j"
      in epdaH.pre_some_position_is_some_position)
      apply(rename_tac d1' k ea c)(*strict*)
      apply(force)
     apply(rename_tac d1' k ea c)(*strict*)
     apply(force)
    apply(rename_tac d1' k ea c)(*strict*)
    apply(force)
   apply(rename_tac d1' k ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1' k ea ca w)(*strict*)
   apply(rule_tac
      t="w@ba#s"
      and s="(w@[ba])@s"
      in ssubst)
    apply(rename_tac d1' k ea ca w)(*strict*)
    apply(force)
   apply(rename_tac d1' k ea ca w)(*strict*)
   apply(rule_tac
      x="w"
      in exI)
   apply (metis butn_prefix_closureise)
  apply(rename_tac d1')(*strict*)
  apply(simp add: derivation_map_def derivation_take_def)
  apply (metis butn_empty_prime_prime)
  done

lemma lessI_X: "
  n\<noteq>(0::nat)
  \<Longrightarrow> a+n=b
  \<Longrightarrow> a<b"
  apply(force)
  done

lemma Reachable_epdaS_produce_from_before_pop_CFGprodXORelim: "
  valid_dpda G
  \<Longrightarrow> epdaH.trans_der G dX \<lparr>epdaH_conf_state=epda_initial G,epdaH_conf_history=[],epdaH_conf_stack=[epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state=q1,epdaH_conf_history=h,epdaH_conf_stack=[ba]@sX\<rparr>
  \<Longrightarrow> [] \<in> epdaS_produce_from_before_pop G q1 ba q2
  \<Longrightarrow> \<exists>\<alpha>. b#\<alpha> \<in> epdaS_produce_from_before_pop G q1 ba q2
  \<Longrightarrow> Q"
  apply(simp add: epdaS_produce_from_before_pop_def)
  apply(clarsimp)
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(subgoal_tac "\<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # s)) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = [], epdaH_conf_stack = s\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   prefer 2
   apply(thin_tac "da 0 = Some (pair None \<lparr>epdaS_conf_state = q1, epdaS_conf_scheduler = b # \<alpha>, epdaS_conf_stack = ba # sa\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "epdaS.derivation G da")
   apply(thin_tac "epdaS.belongs G da")
   apply(thin_tac "da ja = Some (pair ea \<lparr>epdaS_conf_state = qa, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # sa\<rparr>)")
   apply(thin_tac "\<forall>k\<le>ja. \<forall>e c. da k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ ba # sa)")
   apply(thin_tac "da (Suc ja) = Some (pair e'a \<lparr>epdaS_conf_state = q2, epdaS_conf_scheduler = [], epdaS_conf_stack = sa\<rparr>)")
   apply(thin_tac "epdaH.trans_der G dX \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = ba # sX\<rparr>")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(rule translate_epdaS_der_to_epdaH_der)
         apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
         apply(force)
        apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
        apply(force)
       apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
       apply(force)
      apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(subgoal_tac "\<exists>d2'. epdaH.derivation G d2' \<and> epdaH.belongs G d2' \<and> d2' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # sa\<rparr>) \<and> d2' ja = Some (pair ea \<lparr>epdaH_conf_state = qa, epdaH_conf_history = b#\<alpha>, epdaH_conf_stack = ba # sa\<rparr>) \<and> (\<forall>k\<le>ja. \<forall>e c. d2' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # sa)) \<and> d2' (Suc ja) = Some (pair e'a \<lparr>epdaH_conf_state = q2, epdaH_conf_history = b#\<alpha>, epdaH_conf_stack = sa\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   prefer 2
   apply(thin_tac "epdaS.derivation G d")
   apply(thin_tac "epdaS.belongs G d")
   apply(thin_tac "d 0 = Some (pair None \<lparr>epdaS_conf_state = q1, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # s\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "d j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # s\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "\<forall>k\<le>j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ ba # s)")
   apply(thin_tac "d (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = q2, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "\<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # s)) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = [], epdaH_conf_stack = s\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "epdaH.trans_der G dX \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = ba # sX\<rparr>")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(rule translate_epdaS_der_to_epdaH_der)
         apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
         apply(force)
        apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
        apply(force)
       apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
       apply(force)
      apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "epdaS.derivation G d")
  apply(thin_tac "epdaS.belongs G d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaS_conf_state = q1, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # s\<rparr>)")
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "d j = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # s\<rparr>)")
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "\<forall>k\<le>j. \<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ ba # s)")
  apply(thin_tac "d (Suc j) = Some (pair e' \<lparr>epdaS_conf_state = q2, epdaS_conf_scheduler = [], epdaS_conf_stack = s\<rparr>)")
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "da 0 = Some (pair None \<lparr>epdaS_conf_state = q1, epdaS_conf_scheduler = b # \<alpha>, epdaS_conf_stack = ba # sa\<rparr>)")
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "epdaS.derivation G da")
  apply(thin_tac "epdaS.belongs G da")
  apply(thin_tac "da ja = Some (pair ea \<lparr>epdaS_conf_state = qa, epdaS_conf_scheduler = [], epdaS_conf_stack = ba # sa\<rparr>)")
  apply(thin_tac "\<forall>k\<le>ja. \<forall>e c. da k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaS_conf_stack c = w @ ba # sa)")
  apply(thin_tac "da (Suc ja) = Some (pair e'a \<lparr>epdaS_conf_state = q2, epdaS_conf_scheduler = [], epdaS_conf_stack = sa\<rparr>)")
  apply(subgoal_tac "\<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = [ba]\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = [ba]\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ [ba])) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = [], epdaH_conf_stack = []\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   prefer 2
   apply(thin_tac "\<exists>d2'. epdaH.derivation G d2' \<and> epdaH.belongs G d2' \<and> d2' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # sa\<rparr>) \<and> d2' ja = Some (pair ea \<lparr>epdaH_conf_state = qa, epdaH_conf_history = b # \<alpha>, epdaH_conf_stack = ba # sa\<rparr>) \<and> (\<forall>k\<le>ja. \<forall>e c. d2' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # sa)) \<and> d2' (Suc ja) = Some (pair e'a \<lparr>epdaH_conf_state = q2, epdaH_conf_history = b # \<alpha>, epdaH_conf_stack = sa\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "epdaH.trans_der G dX \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = ba # sX\<rparr>")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(rule_tac
      s="s"
      in epdaH_drop_unused_stack)
    apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(subgoal_tac "\<exists>d2'. epdaH.derivation G d2' \<and> epdaH.belongs G d2' \<and> d2' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = [ba]\<rparr>) \<and> d2' ja = Some (pair ea \<lparr>epdaH_conf_state = qa, epdaH_conf_history = b#\<alpha>, epdaH_conf_stack = [ba]\<rparr>) \<and> (\<forall>k\<le>ja. \<forall>e c. d2' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ [ba])) \<and> d2' (Suc ja) = Some (pair e'a \<lparr>epdaH_conf_state = q2, epdaH_conf_history = b#\<alpha>, epdaH_conf_stack = []\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   prefer 2
   apply(thin_tac "\<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # s)) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = [], epdaH_conf_stack = s\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "\<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = [ba]\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = [ba]\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ [ba])) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = [], epdaH_conf_stack = []\<rparr>)")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(thin_tac "epdaH.trans_der G dX \<lparr>epdaH_conf_state = epda_initial G, epdaH_conf_history = [], epdaH_conf_stack = [epda_box G]\<rparr> \<pi> \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = ba # sX\<rparr>")
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(rule_tac
      s="sa"
      in epdaH_drop_unused_stack)
    apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "\<exists>d1'. epdaH.derivation G d1' \<and> epdaH.belongs G d1' \<and> d1' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> d1' j = Some (pair e \<lparr>epdaH_conf_state = q, epdaH_conf_history = [], epdaH_conf_stack = ba # s\<rparr>) \<and> (\<forall>k\<le>j. \<forall>e c. d1' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # s)) \<and> d1' (Suc j) = Some (pair e' \<lparr>epdaH_conf_state = q2, epdaH_conf_history = [], epdaH_conf_stack = s\<rparr>)")
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(thin_tac "\<exists>d2'. epdaH.derivation G d2' \<and> epdaH.belongs G d2' \<and> d2' 0 = Some (pair None \<lparr>epdaH_conf_state = q1, epdaH_conf_history = [], epdaH_conf_stack = ba # sa\<rparr>) \<and> d2' ja = Some (pair ea \<lparr>epdaH_conf_state = qa, epdaH_conf_history = b # \<alpha>, epdaH_conf_stack = ba # sa\<rparr>) \<and> (\<forall>k\<le>ja. \<forall>e c. d2' k = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ ba # sa)) \<and> d2' (Suc ja) = Some (pair e'a \<lparr>epdaH_conf_state = q2, epdaH_conf_history = b # \<alpha>, epdaH_conf_stack = sa\<rparr>)")
  apply(rename_tac d \<alpha> da q s qa sa j ja e ea e' e'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
  apply(subgoal_tac "strict_prefix (map the (get_labels d1' (Suc j))) (map the (get_labels d2' (Suc ja)))")
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
   apply(subgoal_tac "Suc j<Suc ja")
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    prefer 2
    apply(simp only: strict_prefix_def)
    apply(erule exE)+
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
    apply(rule_tac
      n="length c"
      in lessI_X)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
     apply(force)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
    apply(rule_tac
      t="Suc j + length c"
      and s="length(map the (get_labels d1' (Suc j)) @ c)"
      in ssubst)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
     apply(simp (no_asm))
     apply (metis get_labels_length)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
    apply(rule_tac
      t="map the (get_labels d1' (Suc j)) @ c"
      and s="map the (get_labels d2' (Suc ja))"
      in ssubst)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
     apply(force)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
    apply(simp (no_asm))
    apply (metis get_labels_length)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "d1' (Suc j) = d2' (Suc j)")
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="Suc j"
      and P="\<lambda>X. X \<le> ja \<longrightarrow> (\<forall>e c. d2' X = Some (pair e c) \<longrightarrow> (\<exists>w. epdaH_conf_stack c = w @ [ba]))"
      in allE)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    apply(erule impE)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
     apply(force)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    apply(force)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
   apply(subgoal_tac "(\<forall>i\<le>Suc j. d1' i = d2' i)")
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    apply(force)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
   apply(rule_tac
      x="0"
      and y="ja-j"
      and n="Suc j"
      in epdaH.equal_labels_is_forward_target_deterministic_coinciding_positions)
           apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
           apply(simp add: valid_dpda_def valid_pda_def)
           apply(force)
          apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
          apply(rule epda_is_forward_target_deterministic)
          apply(simp add: valid_dpda_def valid_pda_def)
         apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
         apply(force)
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
        apply(force)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
      apply(simp add: strict_prefix_def)
      apply(clarsimp)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(subgoal_tac "get_labels SSd (SSn + SSm) = get_labels SSd SSn @ drop SSn (get_labels SSd (SSn + SSm))" for SSd SSn SSm)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       prefer 2
       apply(rule_tac
      d="d2'"
      and n="Suc j"
      and m="Suc ja-Suc j"
      in get_labels_decomp)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "get_labels d1' (Suc j) = map (Some \<circ> the) (get_labels SSd SSn)" for SSd SSn)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       prefer 2
       apply(rule epdaH.get_labels_the_Some_on_defined_positions)
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
        apply(force)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(subgoal_tac "get_labels d2' (Suc j) = map (Some \<circ> the) (get_labels SSd SSn)" for SSd SSn)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       prefer 2
       apply(rule epdaH.get_labels_the_Some_on_defined_positions)
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
        apply(force)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(subgoal_tac "\<exists>e c. d2' (Suc j) = Some (pair e c)")
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
        prefer 2
        apply(rule_tac
      m="Suc ja"
      in epdaH.pre_some_position_is_some_position)
          apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
          apply(force)
         apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
         apply(force)
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
        apply(force)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(subgoal_tac "get_labels d2' (Suc ja) = map (Some \<circ> the) (get_labels SSd SSn)" for SSd SSn)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       prefer 2
       apply(rule epdaH.get_labels_the_Some_on_defined_positions)
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
        apply(force)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      v="drop (Suc j) (get_labels d2' (Suc ja))"
      in append_injr)
      apply(rule_tac
      t="get_labels d2' (Suc j) @ drop (Suc j) (get_labels d2' (Suc ja))"
      and s="get_labels d2' (Suc ja)"
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      t="get_labels d2' (Suc ja)"
      and s="map (Some \<circ> the) (get_labels d2' (Suc ja))"
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      t="map (Some \<circ> the) (get_labels d2' (Suc ja))"
      and s=" map Some (map the (get_labels d2' (Suc ja))) "
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      t="map the (get_labels d2' (Suc ja))"
      and s="map the (get_labels d1' (Suc j)) @ c"
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      t="map Some (map the (get_labels d1' (Suc j)) @ c)"
      and s=" (map Some (map the (get_labels d1' (Suc j)))) @ map Some c"
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply (metis map_append)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      t="map Some (map the (get_labels d1' (Suc j)))"
      and s="get_labels d1' (Suc j)"
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(force)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(rule_tac
      t="drop (Suc j) (get_labels d1' (Suc j) @ map Some c)"
      and s="map Some c"
      in ssubst)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply(subgoal_tac "length (get_labels d1' (Suc j)) = Suc j")
        apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
        apply(force)
       apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
       apply (metis get_labels_length)
      apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' c)(*strict*)
      apply(force)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
     apply(force)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    apply(force)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
   apply(force)
  apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
  apply(rule_tac
      d="dX"
      and ?d1.0="d1'"
      and ?d2.0="d2'"
      and b="b"
      and h'="\<alpha>"
      and ?s2.0="[]"
      in epdaH_nonconflicting_reachable_derivations_are_mutual_prefixing)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
     apply(force)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
    apply(force)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
   apply(simp add: epdaH.trans_der_def)
   apply(clarsimp)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
   apply(rule_tac
      t="length (get_labels d1' (Suc j))"
      and s="Suc j"
      in ssubst)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
    apply(rule epdaH.get_labels_the_Some_on_defined_positions)
     apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
     apply(force)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
    apply(force)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
   apply(force)
  apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2')(*strict*)
  apply(simp add: epdaH.trans_der_def)
  apply(clarsimp)
  apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
  apply(rule_tac
      t="length (get_labels d2' (Suc ja))"
      and s="Suc ja"
      in ssubst)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
  apply(rule conjI)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
   apply(rule epdaH.get_labels_the_Some_on_defined_positions)
    apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
    apply(force)
   apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
   apply(force)
  apply(rename_tac \<alpha> q qa j ja e ea e' e'a d1' d2' eb)(*strict*)
  apply(force)
  done

lemma epdaS_required_edges__vs__epdaH_required_edges__part1: "
  valid_epda G
  \<Longrightarrow> epdaS_required_edges G \<subseteq> epdaH_required_edges G"
  apply(simp add:   epdaS_required_edges_def epdaH_required_edges_def)
  apply(clarsimp)
  apply(rule_tac
      x="epdaH_vs_epdaHS.Lin2BraDer (epdaS2epdaHS_derivation G d)"
      in exI)
  apply(rule context_conjI)
   apply(rule epdaH_vs_epdaHS.Lin2BraConf_preserves_initiality_lift)
    apply(force)
   apply (metis epdaS2epdaHS_derivation_preserves_derivation_initial)
  apply(rule_tac x="n" in exI)
  apply(rule context_conjI)
   apply(simp add: epdaS2epdaHS_derivation_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def)
  apply(clarsimp)
  apply(rule_tac x="k" in exI)
  apply(rule context_conjI)
   apply(simp add: epdaS2epdaHS_derivation_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def)
  apply(simp add: epdaS2epdaHS_derivation_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def)
  apply(clarsimp)
  apply(simp add: epdaS2epdaHS_derivation_def epdaH_vs_epdaHS.Lin2BraDer_def derivation_map_def epdaHvHS_Lin2BraConf_def epdaS_marking_configurations_def epdaH_marking_configurations_def epdaH_configurations_def epdaS_configurations_def)
  apply(clarsimp)
  apply(subgoal_tac "right_quotient_word (epdaS_conf_scheduler (the (get_configuration (d 0))))
                        [] =Some (epdaS_conf_scheduler (the (get_configuration (d 0))))")
   prefer 2
   apply (metis right_quotient_word_neutral)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d 0 = Some (pair e c)")
   apply(rename_tac k ea c)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in epdaS.pre_some_position_is_some_position)
     apply(simp add: epdaS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "cb \<in> epdaS_configurations G")
   apply(simp add: epdaS_configurations_def)
   apply(force)
  apply(rule epdaS.belongs_configurations)
   apply(rule epdaS.derivation_initial_belongs)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epdaS_required_edges__vs__epdaH_required_edges__part2: "
  valid_epda G
  \<Longrightarrow> epdaH_required_edges G \<subseteq> epdaS_required_edges G"
  apply(simp add:   epdaS_required_edges_def epdaH_required_edges_def)
  apply(clarsimp)
  apply(rule_tac x="epdaHS2epdaS_derivation (epdaH_vs_epdaHS.Bra2LinDer G d k)" in exI)
  apply(rule context_conjI)
   apply(rule epdaHS2epdaS_derivation_preserves_derivation_initial)
    apply(force)
   apply(rule epdaHS.derivation_initialI)
    apply(rule epdaH_vs_epdaHS.Bra2LinDer_preserves_derivation)
       apply(force)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rule epdaH.derivation_initial_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      d="d" and n="k"
      in epdaH_vs_epdaHS.Bra2LinDer_preserves_belongs)
       apply(force)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rule epdaH.derivation_initial_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "cb \<in> epdaHS_configurations G")
    prefer 2
    apply(rule_tac e="None" and i="0" in epdaHS.belongs_configurations)
     apply(force)
    apply(force)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer_def)
   apply(case_tac cb)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: epdaHvHS_Bra2LinConf_def)
   apply(simp add: epdaH_vs_epdaHS.Bra2LinDer'_def)
   apply(simp add: epdaHS_initial_configurations_def)
   apply(simp add: epdaH.derivation_initial_def)
   apply(clarsimp)
   apply(simp add: epdaH_initial_configurations_def)
  apply(rule_tac x="n" in exI)
  apply(rule conjI)
   apply(simp add: epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer_def)
  apply(rule_tac x="k" in exI)
  apply(clarsimp)
  apply(simp add: epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer_def epdaHvHS_Bra2LinConf_def epdaS_marking_configurations_def epdaH_marking_configurations_def)
  apply(rule context_conjI)
   apply(simp add: epdaHS2epdaS_derivation_def epdaH_vs_epdaHS.Bra2LinDer_def epdaH_vs_epdaHS.Bra2LinDer'_def epdaHvHS_Bra2LinConf_def epdaS_marking_configurations_def epdaH_marking_configurations_def)
   apply(case_tac k)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc (nat)) (nat)=[]")
    prefer 2
    apply (metis lessI nat_seqEmpty)
   apply(force)
  apply(clarsimp)
  apply(simp add: epdaS_configurations_def epdaH_configurations_def)
  apply(clarsimp)
  done

lemma epdaS_required_edges__vs__epdaH_required_edges: "
  valid_epda G
  \<Longrightarrow> epdaS_required_edges G = epdaH_required_edges G"
  apply(rule antisym)
   apply(simp add: epdaS_required_edges__vs__epdaH_required_edges__part1 epdaS_required_edges__vs__epdaH_required_edges__part2)
  apply(simp add: epdaS_required_edges__vs__epdaH_required_edges__part1 epdaS_required_edges__vs__epdaH_required_edges__part2)
  done

lemma stable_configuration_can_be_reached: "
  valid_dpda G 
  \<Longrightarrow> \<not> epdaH_livelock G 
  \<Longrightarrow> c \<in> epdaH.get_accessible_configurations G 
  \<Longrightarrow> \<exists>d n e c'. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d n = Some (pair e c') \<and> epdaH_conf_history c = epdaH_conf_history c' \<and> (\<forall>e' c''. epdaH_step_relation G c' e' c'' \<longrightarrow> edge_event e' \<noteq> None)"
  apply(simp add: epdaH.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac d i e)(*strict*)
  apply(case_tac "\<forall>n. \<exists>c' e d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d n = Some (pair e c') \<and> epdaH_conf_history c=epdaH_conf_history c' ")
   apply(rename_tac d i e)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d i e)(*strict*)
    apply(force)
   apply(rename_tac d i e)(*strict*)
   apply(simp add: epdaH_livelock_def)
   apply(erule_tac
      x="derivation_append d (\<lambda>x. SOME y. \<exists>c' e d. y=Some (pair e c') \<and> epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d x = Some (pair e c') \<and> epdaH_conf_history c = epdaH_conf_history c') i"
      in allE)
   apply(rename_tac d i e)(*strict*)
   apply(erule impE)
    apply(rename_tac d i e)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac d i e)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d i e)(*strict*)
     apply(force)
    apply(rename_tac d i e)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac d i e)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d i e)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(simp (no_asm) add: epdaH.derivation_def)
     apply(fold epdaH.derivation_def)
     apply(clarsimp)
     apply(rename_tac d i e ia)(*strict*)
     apply(case_tac ia)
      apply(rename_tac d i e ia)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i e)(*strict*)
      apply(case_tac "d 0")
       apply(rename_tac d i e)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i e a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac d i e a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i e b)(*strict*)
      apply(erule_tac
      x="0"
      in allE)
      apply(clarsimp)
      apply(rename_tac d i e b da)(*strict*)
      apply(rule_tac
      t="(SOME y. \<exists>c' e. y = Some (pair e c') \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d 0 = Some (pair e c') \<and> epdaH_conf_history c = epdaH_conf_history c'))"
      and s="Some(pair None c)"
      in ssubst)
       apply(rename_tac d i e b da)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d i e b da)(*strict*)
      apply(rule some_equality)
       apply(rename_tac d i e b da)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      x="der1 c"
      in exI)
       apply(rule conjI)
        apply(rename_tac d i e b da)(*strict*)
        apply(rule epdaH.der1_is_derivation)
       apply(rename_tac d i e b da)(*strict*)
       apply(rule conjI)
        apply(rename_tac d i e b da)(*strict*)
        apply(rule epdaH.der1_belongs)
        apply(rule epdaH.belongs_configurations)
         apply(rename_tac d i e b da)(*strict*)
         apply(force)
        apply(rename_tac d i e b da)(*strict*)
        apply(force)
       apply(rename_tac d i e b da)(*strict*)
       apply(simp add: der1_def)
      apply(rename_tac d i e b da y)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i e ia nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac d i e nat)(*strict*)
     apply(erule_tac x="Suc nat" in allE')
     apply(erule_tac
      x="nat"
      in allE)
     apply(clarsimp)
     apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
     apply(rule_tac
      t="(SOME y. \<exists>c'event e. y = Some (pair e c'event) \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d (Suc nat) = Some (pair e c'event) \<and> epdaH_conf_history c' = epdaH_conf_history c'event))"
      and s="Some (pair ea c')"
      in ssubst)
      apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
      apply(rule some_equality)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      x="da"
      in exI)
       apply(rule conjI)
        apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(rule conjI)
        apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i e nat c' c'event ea eb da db y)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
      apply(subgoal_tac "X" for X)
       apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
       prefer 2
       apply(rule_tac
      G="G"
      and ?d1.0="derivation_append d da i"
      and ?d2.0="derivation_append d dc i"
      and x="i"
      and y="i"
      and n="Suc nat"
      and m="Suc nat"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(simp add: valid_dpda_def valid_pda_def)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(rule epdaH.derivation_append_preserves_derivation_initial)
                   apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                   apply(simp add: valid_dpda_def valid_pda_def)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(simp add: epdaH.derivation_initial_def)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(rule epdaH.derivation_append_preserves_derivation)
                   apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                   apply(force)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(force)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(clarsimp)
                apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                apply(rule epdaH.derivation_append_preserves_derivation_initial)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(simp add: valid_dpda_def valid_pda_def)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(simp add: epdaH.derivation_initial_def)
                apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                apply(rule epdaH.derivation_append_preserves_derivation)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(force)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(force)
                apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                apply(clarsimp)
               apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
               apply (metis DPDA_is_is_forward_deterministicHist_SB)
              apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
              apply(simp add: derivation_append_def)
             apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
             apply(simp add: derivation_append_def)
            apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
            apply(simp add: derivation_append_def)
           apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
           apply(force)
          apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
          apply(simp add: derivation_append_def)
         apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
         apply(simp add: derivation_append_def)
        apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
        apply(simp add: derivation_append_def)
        apply(simp add: get_configuration_def epda_effects_def)
       apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
       apply(force)
      apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="(SOME y. \<exists>c'event e. y = Some (pair e c'event) \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d nat = Some (pair e c'event) \<and> epdaH_conf_history c' = epdaH_conf_history c'event))"
      and s="Some (pair eb c'event)"
      in ssubst)
      apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
      apply(rule some_equality)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      x="db"
      in exI)
       apply(rule conjI)
        apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(rule conjI)
        apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i e nat c' c'event ea eb da db y)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
      apply(subgoal_tac "X" for X)
       apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
       prefer 2
       apply(rule_tac
      G="G"
      and ?d1.0="derivation_append d db i"
      and ?d2.0="derivation_append d dc i"
      and x="i"
      and y="i"
      and n="nat"
      and m="nat"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(simp add: valid_dpda_def valid_pda_def)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(rule epdaH.derivation_append_preserves_derivation_initial)
                   apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                   apply(simp add: valid_dpda_def valid_pda_def)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(simp add: epdaH.derivation_initial_def)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(rule epdaH.derivation_append_preserves_derivation)
                   apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                   apply(force)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(force)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(clarsimp)
                apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                apply(rule epdaH.derivation_append_preserves_derivation_initial)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(simp add: valid_dpda_def valid_pda_def)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(simp add: epdaH.derivation_initial_def)
                apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                apply(rule epdaH.derivation_append_preserves_derivation)
                  apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                  apply(force)
                 apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                 apply(force)
                apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
                apply(clarsimp)
               apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
               apply (metis DPDA_is_is_forward_deterministicHist_SB)
              apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
              apply(simp add: derivation_append_def)
             apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
             apply(simp add: derivation_append_def)
            apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
            apply(simp add: derivation_append_def)
           apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
           apply(force)
          apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
          apply(simp add: derivation_append_def)
         apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
         apply(simp add: derivation_append_def)
        apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
        apply(simp add: derivation_append_def)
        apply(simp add: get_configuration_def epda_effects_def)
       apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
       apply(force)
      apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
      apply(case_tac nat)
       apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i e nat c' c'event ea eb da db c'eventa ec dc nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
     apply(clarsimp)
     apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
     apply(subgoal_tac "X" for X)
      apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
      prefer 2
      apply(rule_tac
      d="da"
      and n="nat"
      and m="Suc nat"
      in epdaH.step_detail_before_some_position)
        apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
       apply(force)
      apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
      apply(force)
     apply(rename_tac d i e nat c' c'event ea eb da db)(*strict*)
     apply(clarsimp)
     apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
     apply(subgoal_tac "epdaH_conf_history c1 = epdaH_conf_history c'")
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
      apply(subgoal_tac "X" for X)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
       prefer 2
       apply(rule_tac
      G="G"
      and ?d1.0="derivation_append d db i"
      and ?d2.0="derivation_append d da i"
      and x="i"
      and y="i"
      and n="nat"
      and m="nat"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                  apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                  apply(simp add: valid_dpda_def valid_pda_def)
                 apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                 apply(rule epdaH.derivation_append_preserves_derivation_initial)
                   apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                   apply(simp add: valid_dpda_def valid_pda_def)
                  apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                  apply(simp add: epdaH.derivation_initial_def)
                 apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                 apply(rule epdaH.derivation_append_preserves_derivation)
                   apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                   apply(force)
                  apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                  apply(force)
                 apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                 apply(clarsimp)
                apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                apply(rule epdaH.derivation_append_preserves_derivation_initial)
                  apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                  apply(simp add: valid_dpda_def valid_pda_def)
                 apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                 apply(simp add: epdaH.derivation_initial_def)
                apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                apply(rule epdaH.derivation_append_preserves_derivation)
                  apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                  apply(force)
                 apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                 apply(force)
                apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
                apply(clarsimp)
               apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
               apply (metis DPDA_is_is_forward_deterministicHist_SB)
              apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
              apply(simp add: derivation_append_def)
             apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
             apply(simp add: derivation_append_def)
            apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
            apply(simp add: derivation_append_def)
           apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
           apply(force)
          apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
          apply(simp add: derivation_append_def)
         apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
         apply(simp add: derivation_append_def)
        apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
        apply(simp add: derivation_append_def)
        apply(simp add: get_configuration_def epda_effects_def)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
      apply(case_tac nat)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
     apply(subgoal_tac "X" for X)
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
      prefer 2
      apply(rule_tac
      G="G"
      and d="da"
      and n="nat"
      and m="Suc 0"
      in epdaH.steps_extend_history_derivation)
          apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
          apply(simp add: valid_dpda_def valid_pda_def)
         apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
         apply(force)
        apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
        prefer 2
        apply(clarsimp)
        apply(simp add: get_configuration_def epda_effects_def)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
       apply(rule_tac
      d="da"
      in epdaH.belongs_configurations)
        apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def epda_effects_def)
     apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1)(*strict*)
     apply(clarsimp)
     apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
     apply(subgoal_tac "X" for X)
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
      prefer 2
      apply(rule_tac
      G="G"
      and d="da"
      and n="0"
      and m="nat"
      in epdaH.steps_extend_history_derivation)
          apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
          apply(simp add: valid_dpda_def valid_pda_def)
         apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
         apply(force)
        apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
        prefer 2
        apply(clarsimp)
        apply(simp add: get_configuration_def epda_effects_def)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
       apply(rule_tac
      d="da"
      in epdaH.belongs_configurations)
        apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
        apply(force)
       apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
       apply(force)
      apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def epda_effects_def)
     apply(rename_tac d i e nat c' c'event eb da db e1 e2 c1 h)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="(SOME y. \<exists>c' e. y = Some (pair e c') \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d 0 = Some (pair e c') \<and> epdaH_conf_history c = epdaH_conf_history c'))"
      and s="Some(pair None c)"
      in ssubst)
     apply(rename_tac d i e)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i e)(*strict*)
    apply(rule some_equality)
     apply(rename_tac d i e)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      x="der1 c"
      in exI)
     apply(rule conjI)
      apply(rename_tac d i e)(*strict*)
      apply(rule epdaH.der1_is_derivation)
     apply(rename_tac d i e)(*strict*)
     apply(rule conjI)
      apply(rename_tac d i e)(*strict*)
      apply(rule epdaH.der1_belongs)
      apply(rule epdaH.belongs_configurations)
       apply(rename_tac d i e)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac d i e)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d i e)(*strict*)
       apply(force)
      apply(rename_tac d i e)(*strict*)
      apply(force)
     apply(rename_tac d i e)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d i e y)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac d i e)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i e n)(*strict*)
    apply(simp add: derivation_append_def)
    apply(case_tac "n\<le>i")
     apply(rename_tac d i e n)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "X" for X)
      apply(rename_tac d i e n)(*strict*)
      prefer 2
      apply(rule_tac
      g="d"
      and n="n"
      and m="i"
      in epdaH.pre_some_position_is_some_position)
        apply(rename_tac d i e n)(*strict*)
        apply(simp add: epdaH.derivation_initial_def)
        apply(force)
       apply(rename_tac d i e n)(*strict*)
       apply(force)
      apply(rename_tac d i e n)(*strict*)
      apply(force)
     apply(rename_tac d i e n)(*strict*)
     apply(force)
    apply(rename_tac d i e n)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="n-i"
      in allE)
    apply(clarsimp)
    apply(rename_tac d i e n c' ea da)(*strict*)
    apply(subgoal_tac "(SOME y. \<exists>c'event e. y = Some (pair e c'event) \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d (n - i) = Some (pair e c'event) \<and> epdaH_conf_history c' = epdaH_conf_history c'event)) = Some (pair ea c')")
     apply(rename_tac d i e n c' ea da)(*strict*)
     apply(force)
    apply(rename_tac d i e n c' ea da)(*strict*)
    apply(rule some_equality)
     apply(rename_tac d i e n c' ea da)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      x="da"
      in exI)
     apply(rule conjI)
      apply(rename_tac d i e n c' ea da)(*strict*)
      apply(force)
     apply(rename_tac d i e n c' ea da)(*strict*)
     apply(rule conjI)
      apply(rename_tac d i e n c' ea da)(*strict*)
      apply(force)
     apply(rename_tac d i e n c' ea da)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e n c' ea da y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and ?d1.0="derivation_append d da i"
      and ?d2.0="derivation_append d db i"
      and x="i"
      and y="i"
      and n="n-i"
      and m="n-i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(rule epdaH.derivation_append_preserves_derivation_initial)
                 apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                 apply(simp add: valid_dpda_def valid_pda_def)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(simp add: epdaH.derivation_initial_def)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(rule epdaH.derivation_append_preserves_derivation)
                 apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                 apply(simp add: epdaH.derivation_initial_def)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(force)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(force)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(rule epdaH.derivation_append_preserves_derivation_initial)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(simp add: epdaH.derivation_initial_def)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(rule epdaH.derivation_append_preserves_derivation)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(simp add: epdaH.derivation_initial_def)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(force)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(clarsimp)
             apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
             apply(thin_tac "(SOME y. \<exists>c' e. y = Some (pair e c') \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d (n - i) = Some (pair e c') \<and> epdaH_conf_history c'event = epdaH_conf_history c')) = None")
             apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
            apply(simp add: derivation_append_def)
           apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
           apply(simp add: derivation_append_def)
          apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
          apply(simp add: derivation_append_def)
         apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
         apply(force)
        apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
        apply(simp add: derivation_append_def)
       apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
      apply(simp add: derivation_append_def)
      apply(simp add: get_configuration_def epda_effects_def)
     apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
     apply(force)
    apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
    apply(force)
   apply(rename_tac d i e)(*strict*)
   apply(erule_tac
      x="i"
      and P="\<lambda>N. \<exists>n\<ge>N. epdaH_conf_history (the (get_configuration (derivation_append d (\<lambda>x. SOME y. \<exists>c' e. y = Some (pair e c') \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d x = Some (pair e c') \<and> epdaH_conf_history c = epdaH_conf_history c')) i n))) \<noteq> epdaH_conf_history (the (get_configuration (derivation_append d (\<lambda>x. SOME y. \<exists>c' e. y = Some (pair e c') \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d x = Some (pair e c') \<and> epdaH_conf_history c = epdaH_conf_history c')) i N)))"
      in allE)
   apply(rename_tac d i e)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e n)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(case_tac "n=i")
    apply(rename_tac d i e n)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e n)(*strict*)
   apply(subgoal_tac "i<n")
    apply(rename_tac d i e n)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i e n)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="n-i"
      in allE)
   apply(clarsimp)
   apply(rename_tac d i e n c' ea da)(*strict*)
   apply(subgoal_tac "(SOME y. \<exists>c'event e. y = Some (pair e c'event) \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d (n - i) = Some (pair e c'event) \<and> epdaH_conf_history c' = epdaH_conf_history c'event)) = Some (pair ea c')")
    apply(rename_tac d i e n c' ea da)(*strict*)
    apply(force)
   apply(rename_tac d i e n c' ea da)(*strict*)
   apply(rule some_equality)
    apply(rename_tac d i e n c' ea da)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="da"
      in exI)
    apply(rule conjI)
     apply(rename_tac d i e n c' ea da)(*strict*)
     apply(force)
    apply(rename_tac d i e n c' ea da)(*strict*)
    apply(rule conjI)
     apply(rename_tac d i e n c' ea da)(*strict*)
     apply(force)
    apply(rename_tac d i e n c' ea da)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e n c' ea da y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and ?d1.0="derivation_append d da i"
      and ?d2.0="derivation_append d db i"
      and x="i"
      and y="i"
      and n="n-i"
      and m="n-i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(rule epdaH.derivation_append_preserves_derivation_initial)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(simp add: epdaH.derivation_initial_def)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(rule epdaH.derivation_append_preserves_derivation)
                apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
                apply(simp add: epdaH.derivation_initial_def)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(force)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(force)
             apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
             apply(rule epdaH.derivation_append_preserves_derivation_initial)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(simp add: epdaH.derivation_initial_def)
             apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
             apply(rule epdaH.derivation_append_preserves_derivation)
               apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
               apply(simp add: epdaH.derivation_initial_def)
              apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
              apply(force)
             apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
             apply(clarsimp)
            apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
            apply(thin_tac "epdaH_conf_history (the (case_option None (case_derivation_configuration (\<lambda>e. Some)) (SOME y. \<exists>c' e. y = Some (pair e c') \<and> (\<exists>d. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d (n - i) = Some (pair e c') \<and> epdaH_conf_history c'event = epdaH_conf_history c')))) \<noteq> epdaH_conf_history c'event")
            apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
            apply (metis DPDA_is_is_forward_deterministicHist_SB)
           apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
           apply(simp add: derivation_append_def)
          apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
          apply(simp add: derivation_append_def)
         apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
         apply(simp add: derivation_append_def)
        apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
        apply(force)
       apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
      apply(simp add: derivation_append_def)
     apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
     apply(simp add: derivation_append_def)
     apply(simp add: get_configuration_def epda_effects_def)
    apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
    apply(force)
   apply(rename_tac d i e n c' ea da c'event eb db)(*strict*)
   apply(force)
  apply(rename_tac d i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e n)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>n. \<exists>d e c'. epdaH.derivation G d \<and> epdaH.belongs G d \<and> d 0 = Some (pair None c) \<and> d n = Some (pair e c') \<and> epdaH_conf_history c=epdaH_conf_history c' "
      and x="0"
      and n="n"
      in ex_max_limited)
    apply(rename_tac d i e n)(*strict*)
    apply(rule_tac
      x="der1 c"
      in exI)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule_tac
      x="c"
      in exI)
    apply(rule conjI)
     apply(rename_tac d i e n)(*strict*)
     apply(rule epdaH.der1_is_derivation)
    apply(rename_tac d i e n)(*strict*)
    apply(rule conjI)
     apply(rename_tac d i e n)(*strict*)
     apply(rule epdaH.der1_belongs)
     apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
      apply(rename_tac d i e n)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d i e n)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d i e n)(*strict*)
      apply(force)
     apply(rename_tac d i e n)(*strict*)
     apply(force)
    apply(rename_tac d i e n)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d i e n)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e n k da ea c')(*strict*)
  apply(rule_tac
      x="da"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="k"
      in exI)
  apply(clarsimp)
  apply(rename_tac d i e n k da ea c' e' x)(*strict*)
  apply(case_tac e')
  apply(rename_tac d i e n k da ea c' e' x edge_src edge_eventa edge_pop edge_push edge_trg)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e n k da ea c' x edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs r po pu qt)
  apply(rename_tac d i e n k da ea c' x qs r po pu qt)(*strict*)
  apply(case_tac r)
   apply(rename_tac d i e n k da ea c' x qs r po pu qt)(*strict*)
   prefer 2
   apply(rename_tac d i e n k da ea c' x qs r po pu qt a)(*strict*)
   apply(force)
  apply(rename_tac d i e n k da ea c' x qs r po pu qt)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(case_tac "k=n")
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e n da ea c' x qs po pu qt)(*strict*)
   apply(erule_tac
      x="c'"
      in allE)
   apply(erule_tac
      x="ea"
      in allE)
   apply(erule_tac
      x="da"
      in allE)
   apply(clarsimp)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(subgoal_tac "k<n")
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc k"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="derivation_append da (der2 c' \<lparr>edge_src = qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr> x) k"
      in allE)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(rule epdaH.derivation_append_preserves_belongs)
     apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
    apply(force)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
     apply(force)
    apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(force)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(erule impE)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
     apply(force)
    apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(force)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(erule_tac
      x="Some \<lparr>edge_src = qs, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = qt\<rparr>"
      in allE)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(thin_tac "\<forall>c'event e d. d n = Some (pair e c'event) \<longrightarrow> d 0 = Some (pair None c) \<longrightarrow> epdaH.belongs G d \<longrightarrow> epdaH.derivation G d \<longrightarrow> epdaH_conf_history c' \<noteq> epdaH_conf_history c'event")
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d i e n k da ea c' x qs po pu qt)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(simp add: option_to_list_def)
  done

lemma epda_to_des__of__valid_epda__not_empty: "
  valid_epda G
  \<Longrightarrow> epda_to_des G \<noteq> bot"
  apply(simp add: epda_to_des_def botDES_def bot_DES_ext_def)
  apply(clarsimp)
  apply (metis empty_iff epda_empty_in_epdaH_unmarked_language)
  done

definition epdaH_livelock_freedom :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_livelock_freedom G \<equiv>
  \<not> epdaH.has_livelock G"

definition epdaH_deadlock_freedom :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_deadlock_freedom G \<equiv>
  \<forall>d n e c.
    epdaH.derivation_initial G d
    \<longrightarrow> maximum_of_domain d n
    \<longrightarrow> (\<not> epdaH_marking_condition G d)
    \<longrightarrow> d n = Some (pair e c)
    \<longrightarrow> (\<exists>e' c'. epdaH_step_relation G c e' c')"

definition epdaH_accessible :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epdaH_accessible G \<equiv>
    (\<forall>e \<in> epda_delta G. \<exists>d n c. 
      epdaH.derivation_initial G d 
      \<and> d n = Some (pair (Some e) c))
  \<and> (\<forall>q \<in> epda_states G. \<exists>d n e c. 
      epdaH.derivation_initial G d 
      \<and> d n = Some (pair e c)
      \<and> q = epdaH_conf_state c)"

lemma epdaH_accessible__to__epdaHaccessible: "
  epdaH_accessible G
  \<Longrightarrow> epdaH.accessible G" 
  apply(simp add: epdaH.accessible_def epdaH_accessible_def epdaH.get_accessible_destinations_def epda_destinations_def epdaH_get_destinations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(erule_tac x="xa" in ballE)
    apply(clarsimp)
    apply(rule_tac x="d" in exI)
    apply(clarsimp)
    apply(rule_tac x="n" in exI)
    apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(erule_tac x="xa" in ballE)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(clarsimp)
   apply(rule_tac x="n" in exI)
   apply(clarsimp)
  apply(force)
  done

lemma epdaHaccessible__to__epdaH_accessible: "
  epdaH.accessible G
  \<Longrightarrow> epdaH_accessible G" 
  apply(simp add: epdaH.accessible_def epdaH_accessible_def epdaH.get_accessible_destinations_def epda_destinations_def epdaH_get_destinations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(subgoal_tac "edge e \<in> {x. (x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and>
                (\<exists>d. ATS.derivation_initial epdaH_initial_configurations epdaH_step_relation G d \<and>
                     (\<exists>i e c. d i = Some (pair e c) \<and>
                              (x = epda_destinations.state (epdaH_conf_state c) \<or>
                               x \<in> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'}))))}")
    prefer 2
    apply(rule_tac A="edge ` epda_delta G" in set_mp)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(clarsimp)
   apply(rule_tac x="i" in exI)
   apply(clarsimp)
   apply(case_tac ea)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "epda_destinations.state q \<in> {x. (x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and>
                (\<exists>d. ATS.derivation_initial epdaH_initial_configurations epdaH_step_relation G d \<and>
                     (\<exists>i e c. d i = Some (pair e c) \<and>
                              (x = epda_destinations.state (epdaH_conf_state c) \<or>
                               x \<in> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'}))))}")
   prefer 2
   apply(rule_tac A="epda_destinations.state ` epda_states G" in set_mp)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(rule_tac x="i" in exI)
  apply(clarsimp)
  apply(case_tac c)
  apply(clarsimp)
  apply(case_tac e)
   apply(clarsimp)
  apply(force)
  done

lemma epdaH_Nonblockingness2: "
  valid_epda G
  \<Longrightarrow> Nonblockingness2 (epdaH.unmarked_language G) (epdaH.marked_language G)"
  apply(subgoal_tac "Nonblockingness2 (epdaS.unmarked_language G) (epdaS.marked_language G)")
   prefer 2
   apply(rule epda_Nonblockingness2)
   apply(force)
  apply (metis epdaS_to_epdaH_mlang epdaS_to_epdaH_unmarked_language)
  done

lemma cfg_like_characterization_of_determinism_for_epda_part1: "
  valid_epda G
  \<Longrightarrow> epdaH.is_forward_deterministicHist_SB G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> epdaH_conf_history c1 = v
  \<Longrightarrow> d1 (Suc n1) = Some (pair e1' c1')
  \<Longrightarrow> epdaH_conf_history c1' = v @ [b]
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> epdaH_conf_history c2 = v
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2')
  \<Longrightarrow> epdaH_conf_history c2' = v @ [b]
  \<Longrightarrow> n1 = n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  oops

lemma cfg_like_characterization_of_determinism_for_epda_part2: "
  valid_epda G
  \<Longrightarrow> epdaH.is_forward_deterministicHist_SB G
  \<Longrightarrow> epdaH.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> epdaH_conf_history c1 = v
  \<Longrightarrow> epdaH.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> epdaH_conf_history c2 = v
  \<Longrightarrow> d2 (Suc n2) = Some (pair e2' c2')
  \<Longrightarrow> epdaH_conf_history c2' = v @ [b]
  \<Longrightarrow> n1 \<le> n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)"
  oops

end

