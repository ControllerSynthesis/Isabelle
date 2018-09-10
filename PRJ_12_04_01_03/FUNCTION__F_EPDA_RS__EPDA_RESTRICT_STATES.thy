section {*FUNCTION\_\_F\_EPDA\_RS\_\_EPDA\_RESTRICT\_STATES*}
theory
  FUNCTION__F_EPDA_RS__EPDA_RESTRICT_STATES

imports
  PRJ_12_04_01_03__ENTRY

begin

definition F_ALT_EPDA_RS :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> ('state, 'event, 'stack) epda option"
  where
    "F_ALT_EPDA_RS G Q \<equiv>
  if epda_initial G \<notin> Q
  then None
  else Some
        \<lparr>epda_states = Q,
        epda_events = epda_events G,
        epda_gamma = epda_gamma G,
        epda_delta = {e. e \<in> epda_delta G \<and> edge_src e \<in> Q \<and> edge_trg e \<in> Q},
        epda_initial = epda_initial G,
        epda_box = epda_box G,
        epda_marking = epda_marking G \<inter> Q\<rparr>"

lemma F_EPDA_RS__vs_F_ALT_EPDA_RS: "
  valid_epda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = F_EPDA_RS G Q"
  apply(simp add: F_ALT_EPDA_RS_def F_EPDA_RS_def F_EPDA_R_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(force)
  done

definition retain_edges_between_retained_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "retain_edges_between_retained_states Gi Q Go \<equiv>
  \<forall>e \<in> epda_delta Gi.
    edge_src e \<in> Q
    \<longrightarrow> edge_trg e \<in> Q
    \<longrightarrow> e \<in> epda_delta Go"

definition F_EPDA_RS__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> bool"
  where
    "F_EPDA_RS__SpecInput G Q \<equiv>
  valid_dpda G
  \<and> Q \<subseteq> epda_states G
  \<and> \<not> epdaH_livelock G
  \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)
  \<and> only_executing_edges_from_marking_states G
  \<and> epdaH.accessible G"

definition F_EPDA_RS__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> ('state, 'event, 'stack) epda option
  \<Rightarrow> bool"
  where
    "F_EPDA_RS__SpecOutput Gi Q Go \<equiv>
  case Go of
    None \<Rightarrow>
        epda_initial Gi \<notin> Q
    | Some Go \<Rightarrow>
        valid_dpda Go
        \<and> \<not> epdaH_livelock Go
        \<and> (Q = epda_states Gi \<longleftrightarrow> Gi = Go)
        \<and> (Q = epda_states Gi \<longleftrightarrow> epda_to_des Gi = epda_to_des Go)
        \<and> retain_edges_between_retained_states Gi Q Go"

lemma F_ALT_EPDA_RS__preserves_valid_pda: "
  valid_pda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = Some G'
  \<Longrightarrow> valid_pda G'"
  apply(simp add: valid_pda_def valid_dpda_def valid_epda_def F_ALT_EPDA_RS_def)
  apply(clarsimp)
  apply(case_tac "epda_initial G \<notin> Q")
   apply(clarsimp)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule_tac
      B="epda_states G"
      in finite_subset)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label G x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  done

lemma F_ALT_EPDA_RS__preserves_valid_dpda: "
  valid_dpda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = Some G'
  \<Longrightarrow> valid_dpda G'"
  apply(simp add: valid_dpda_def)
  apply(rule context_conjI)
   apply(rule F_ALT_EPDA_RS__preserves_valid_pda)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      G="G"
      and G'="G'"
      in epda_sub_preserves_is_forward_edge_deterministic_accessible)
    apply(simp add: valid_dpda_def)
   apply(force)
  apply(simp add: epda_sub_def F_ALT_EPDA_RS_def)
  apply(clarsimp)
  apply(case_tac "epda_initial G \<notin> Q")
   apply(force)
  apply(force)
  done

lemma F_ALT_EPDA_RS__preserves_no_epda_livelock: "
  valid_dpda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = Some G'
  \<Longrightarrow> valid_dpda G'
  \<Longrightarrow> \<not> epdaH_livelock G
  \<Longrightarrow> \<not> epdaH_livelock G'"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule impE)
   apply(rename_tac d N)(*strict*)
   apply(rule_tac
      ?G1.0="G'"
      in epda_sub_preserves_derivation_initial)
      apply(rename_tac d N)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d N)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d N)(*strict*)
    apply(simp add: epda_sub_def F_ALT_EPDA_RS_def)
    apply(rename_tac d)(*strict*)
    apply(case_tac "epda_initial G \<notin> Q")
     apply(rename_tac d)(*strict*)
     apply(force)
    apply(rename_tac d)(*strict*)
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

lemma F_ALT_EPDA_RS__no_modification: "
  valid_dpda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = Some G'
  \<Longrightarrow> valid_dpda G'
  \<Longrightarrow> (Q = epda_states G) = (G = G')"
  apply(rule order_antisym)
   apply(simp add: F_ALT_EPDA_RS_def)
   apply(case_tac "epda_initial G \<notin> Q")
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac G)
   apply(rename_tac epda_statesa epda_eventsa epda_gammaa epda_deltaa epda_initiala epda_boxa epda_markinga)(*strict*)
   apply(clarsimp)
   apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking)(*strict*)
   apply(rule conjI)
    apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking)(*strict*)
    apply(rule order_antisym)
     apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking)(*strict*)
     apply(clarsimp)
     apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking x)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
     apply(clarsimp)
     apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label \<lparr>epda_states = epda_states, epda_events = epda_events, epda_gamma = epda_gamma, epda_delta = epda_delta, epda_initial = epda_initial, epda_box = epda_box, epda_marking = epda_marking\<rparr> x"
      in ballE)
      apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking x)(*strict*)
     apply(simp add: valid_epda_step_label_def)
    apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking)(*strict*)
    apply(clarsimp)
   apply(rename_tac epda_states epda_events epda_gamma epda_delta epda_initial epda_box epda_marking)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(force)
  apply(simp add: F_ALT_EPDA_RS_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac "epda_initial G' \<notin> Q")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(case_tac G')
  apply(rename_tac x epda_statesa epda_eventsa epda_gammaa epda_deltaa epda_initiala epda_boxa epda_markinga)(*strict*)
  apply(clarsimp)
  done

lemma F_ALT_EPDA_RS__lang_modification: "
  valid_dpda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> \<not> epdaH_livelock G
  \<Longrightarrow> epdaH.accessible G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = Some G'
  \<Longrightarrow> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)
  \<Longrightarrow> only_executing_edges_from_marking_states G
  \<Longrightarrow> valid_dpda G'
  \<Longrightarrow> (epda_to_des G = epda_to_des G') \<le> (Q = epda_states G)"
  (*nonambiguous (epdaS/epdaHS or almost epdaH (consider continuations))
accessible
Nonblockingness
\<Longrightarrow> removal of a state changes the marked language
*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: epda_to_des_def)
  apply(clarsimp)
  apply(simp add: epdaH.accessible_def)
  apply(simp add: epda_destinations_def)
  apply(clarsimp)
  apply(thin_tac "edge ` epda_delta G \<subseteq> epdaH.get_accessible_destinations G")
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "epda_destinations.state x \<in> epdaH.get_accessible_destinations G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "epda_destinations.state ` epda_states G \<subseteq> epdaH.get_accessible_destinations G")
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaH.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: epdaH_get_destinations_def)
  apply(case_tac c)
  apply(rename_tac x d i e c epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac x d i e q h s)(*strict*)
  apply(erule disjE)
   apply(rename_tac x d i e q h s)(*strict*)
   prefer 2
   apply(case_tac e)
    apply(rename_tac x d i e q h s)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d i e q h s a)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e q h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "h \<in> epdaH.unmarked_language G")
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(thin_tac "epdaH.unmarked_language G = epdaH.unmarked_language G'")
   apply(simp add: epdaH.unmarked_language_def)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d i e q h s)(*strict*)
    apply(simp add: epdaH_unmarked_effect_def)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
   apply(rename_tac d i e q h s)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac d i e q h s)(*strict*)
  apply(subgoal_tac "\<exists>h'. h@h' \<in> epdaH.marked_language G")
   apply(rename_tac d i e q h s)(*strict*)
   prefer 2
   apply(simp add: nonblockingness_language_def prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac d i e q h s)(*strict*)
  apply(erule exE)+
  apply(rename_tac d i e q h s h')(*strict*)
  apply(rule ccontr)
  apply(subgoal_tac "h@h' \<notin> epdaH.marked_language G'")
   apply(rename_tac d i e q h s h')(*strict*)
   apply(force)
  apply(rename_tac d i e q h s h')(*strict*)
  apply(thin_tac "epdaH.marked_language G = epdaH.marked_language G'")
  apply(thin_tac "epdaH.unmarked_language G = epdaH.unmarked_language G'")
  apply(thin_tac "h \<in> epdaH.unmarked_language G")
  apply(thin_tac "epda_destinations.state q \<in> epda_destinations G")
  apply(thin_tac "q \<in> epda_states G")
  apply(rename_tac d i e q h s h')(*strict*)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac d i e q h s h' da db)(*strict*)
  apply(thin_tac "epdaH_marking_condition G' db")
  apply(thin_tac "epdaH_marking_condition G da")
  apply(thin_tac "epdaH.derivation G da")
  apply(thin_tac "epdaH.derivation G' db")
  apply(thin_tac "nonblockingness_language (epdaH.unmarked_language G') {w. \<exists>d. epdaH.derivation_initial G' d \<and> w \<in> epdaH_marked_effect G' d \<and> epdaH.derivation G' d \<and> epdaH_marking_condition G' d}")
  apply(rename_tac d i e q h s h' da db)(*strict*)
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e q h s h' da db ia ib ea eb c ca)(*strict*)
  apply(simp add: epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac d i e q h s h' da db ia ib ea eb c ca epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e q h s h' da db ia ib ea eb c ca epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e q h s h' da db ia ib ea eb epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 s1 q2 s2)
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(thin_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h @ h', epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations G'")
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(thin_tac "\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h @ h', epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations G")
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(thin_tac "\<forall>j e' c'. ia < j \<and> da j = Some (pair e' c') \<longrightarrow> epdaH_string_state \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h @ h', epdaH_conf_stack = s2\<rparr> = epdaH_string_state c'")
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(thin_tac "\<forall>j e' c'. ib < j \<and> db j = Some (pair e' c') \<longrightarrow> epdaH_string_state \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h @ h', epdaH_conf_stack = s1\<rparr> = epdaH_string_state c'")
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in DPDA_only_executing_edges_from_marking_states_implies_epdaH_non_ambiguous)
    apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(simp add: epdaH_non_ambiguous_def)
  apply(erule_tac
      x="da"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(force)
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(erule_tac
      x="db"
      in allE)
  apply(erule impE)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(rule_tac
      ?G1.0="G'"
      in epda_sub_preserves_derivation_initial)
      apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(simp add: epda_sub_def F_ALT_EPDA_RS_def)
   apply(case_tac "epda_initial G \<notin> Q")
    apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(erule_tac
      x="ia"
      in allE)
  apply(erule_tac
      x="ib"
      in allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(erule impE)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(simp add: epda_sub_def F_ALT_EPDA_RS_def)
   apply(case_tac "epda_initial G \<notin> Q")
    apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e q h s h' da db ia ib ea eb q1 s1 q2 s2)(*strict*)
  apply(clarsimp)
    (*
d is a prefix of da = db
thus d!i=db!i \<Longrightarrow> q \<in> Q
*)
  apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
  apply(case_tac "ib<i")
   apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
    prefer 2
    apply(rule_tac
      g="d"
      and n="ib"
      and m="i"
      in epdaH.pre_some_position_is_some_position)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
     apply(force)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and n="ib"
      and m="i-ib"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
     apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
      apply(force)
     apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
     apply(force)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb c ha)(*strict*)
   apply(case_tac c)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb c ha epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(rename_tac q1 h1 s1)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb c ha q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and ?d1.0="d"
      and ?d2.0="da"
      and x="0"
      and y="0"
      and n="ib"
      and m="ib"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
              apply(force)
             apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
             apply(force)
            apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
            apply (metis DPDA_is_is_forward_deterministicHist_SB)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
           apply(simp add: epdaH.derivation_initial_def)
           apply(erule_tac
      x="0"
      in allE)
           apply(clarsimp)
           apply(case_tac "db 0")
            apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
            apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 a)(*strict*)
           apply(clarsimp)
           apply(case_tac a)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 a option b)(*strict*)
           apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 b)(*strict*)
           apply(simp add: epdaH_initial_configurations_def)
           apply(clarsimp)
           apply(case_tac "d 0")
            apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 b)(*strict*)
            apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 b a)(*strict*)
           apply(clarsimp)
           apply(case_tac a)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 b a option ba)(*strict*)
           apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1 b ba)(*strict*)
           apply(simp add: epdaH_initial_configurations_def)
          apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
          apply(force)
         apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
         apply(force)
        apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
        apply(force)
       apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
       apply(force)
      apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
      apply(force)
     apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
     apply(clarsimp)
     apply(simp add: epda_effects_def)
     apply(simp add: get_configuration_def)
     apply(subgoal_tac "\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h1 @ ha @ h', epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations G")
      apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
      apply(simp add: epdaH_configurations_def)
     apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
     apply(rule_tac
      d="da"
      in epdaH.belongs_configurations)
      apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
      apply(force)
     apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
     apply(force)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
    apply(force)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb ha q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s da db ib ea q2 s2 h1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q s da db ib ea q2 s2 h1)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and n="ib"
      and m="i"
      and G="G"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac d i e q s da db ib ea q2 s2 h1)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
     apply(rename_tac d i e q s da db ib ea q2 s2 h1)(*strict*)
     apply(force)
    apply(rename_tac d i e q s da db ib ea q2 s2 h1)(*strict*)
    apply(force)
   apply(rename_tac d i e q s da db ib ea q2 s2 h1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s da db ib ea q2 s2 h1 e2 c2)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d i e q s da db ib ea h1 e2 c2 w)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d i e q s da db ib ea h1 e2 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and G="G"
      and n="Suc ib"
      and m="i-Suc ib"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
     apply(rule_tac
      d="d"
      in epdaH.belongs_configurations)
      apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
      apply(force)
     apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
     apply(force)
    apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac "edge_event e2")
    apply(rename_tac d i e q s da db ib ea h1 e2 w)(*strict*)
    apply(clarsimp)
    apply(simp add: only_executing_edges_from_marking_states_def)
   apply(rename_tac d i e q s da db ib ea h1 e2 w a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
  apply(case_tac "i<ib")
   apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
   apply(thin_tac "\<not> ib < i")
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
    prefer 2
    apply(rule_tac
      g="da"
      and n="i"
      and m="ib"
      in epdaH.pre_some_position_is_some_position)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
     apply(force)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
    apply(force)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c)(*strict*)
   apply(case_tac c)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
   apply(rename_tac q1 h1 s1)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb c q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="da"
      and n="i"
      and m="ib-i"
      in epdaH.steps_extend_history_derivation)
        apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
       apply(simp add: epdaH.derivation_initial_def)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
     apply(rule_tac
      d="da"
      in epdaH.belongs_configurations)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
      apply(rule epdaH.derivation_initial_belongs)
       apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
      apply(force)
     apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
     apply(erule_tac
      x="i"
      in allE)
     apply(force)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1 ha)(*strict*)
   apply(subgoal_tac "prefix h h1 \<or> prefix h1 h")
    apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1 ha)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1 ha)(*strict*)
   apply(erule disjE)
    apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1 ha)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and ?d1.0="d"
      and ?d2.0="da"
      and x="0"
      and y="0"
      and n="i"
      and m="i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
                apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
                apply(simp add: valid_dpda_def valid_pda_def)
               apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
               apply(force)
              apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
              apply(force)
             apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
             apply (metis DPDA_is_is_forward_deterministicHist_SB)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
            apply(simp add: epdaH.derivation_initial_def)
            apply(erule_tac
      x="0"
      in allE)
            apply(clarsimp)
            apply(case_tac "db 0")
             apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
             apply(clarsimp)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c a)(*strict*)
            apply(clarsimp)
            apply(case_tac a)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c a option b)(*strict*)
            apply(clarsimp)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c b)(*strict*)
            apply(simp add: epdaH_initial_configurations_def)
            apply(clarsimp)
            apply(case_tac "d 0")
             apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c b)(*strict*)
             apply(clarsimp)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c b a)(*strict*)
            apply(clarsimp)
            apply(case_tac a)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c b a option ba)(*strict*)
            apply(clarsimp)
            apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c b ba)(*strict*)
            apply(simp add: epdaH_initial_configurations_def)
           apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
           apply(force)
          apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
          apply(force)
         apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
         apply(force)
        apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
        apply(force)
       apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
       apply(force)
      apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
      apply(clarsimp)
      apply(simp add: epda_effects_def)
      apply(simp add: get_configuration_def)
      apply(subgoal_tac "\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h @ c @ ha, epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations G")
       apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
       apply(simp add: epdaH_configurations_def)
      apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
      apply(rule_tac
      d="da"
      in epdaH.belongs_configurations)
       apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
       apply(rule epdaH.derivation_initial_belongs)
        apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
       apply(force)
      apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
      apply(force)
     apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
     apply(force)
    apply(rename_tac d i e q h s da db ib ea q2 s2 eb q1 s1 ha c)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
    apply(subgoal_tac "\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr> \<in> epdaH_configurations G'")
     apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
     apply(simp add: epdaH_configurations_def F_ALT_EPDA_RS_def Let_def)
     apply(case_tac "epda_initial G \<notin> Q")
      apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
    apply(rule_tac
      d="db"
      in epdaH.belongs_configurations)
     apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
     apply(force)
    apply(rename_tac d i h da db ib ea q2 s2 eb q1 s1 ha)(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
    apply(force)
   apply(rename_tac d i e q h s h' da db ib ea q2 s2 eb q1 h1 s1 ha)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and ?d1.0="da"
      and ?d2.0="d"
      and x="0"
      and y="0"
      and n="i"
      and m="i"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
               apply(simp add: valid_dpda_def valid_pda_def)
              apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
              apply(force)
             apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
             apply(force)
            apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
            apply (metis DPDA_is_is_forward_deterministicHist_SB)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
           apply(simp add: epdaH.derivation_initial_def)
           apply(erule_tac
      x="0"
      in allE)
           apply(clarsimp)
           apply(case_tac "db 0")
            apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
            apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c a)(*strict*)
           apply(clarsimp)
           apply(case_tac a)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c a option b)(*strict*)
           apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c b)(*strict*)
           apply(simp add: epdaH_initial_configurations_def)
           apply(clarsimp)
           apply(case_tac "d 0")
            apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c b)(*strict*)
            apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c b a)(*strict*)
           apply(clarsimp)
           apply(case_tac a)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c b a option ba)(*strict*)
           apply(clarsimp)
           apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c b ba)(*strict*)
           apply(simp add: epdaH_initial_configurations_def)
          apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
          apply(force)
         apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
         apply(force)
        apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
        apply(force)
       apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
       apply(force)
      apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
      apply(force)
     apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
     apply(clarsimp)
     apply(simp add: epda_effects_def)
     apply(simp add: get_configuration_def)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
    apply(simp)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 eb q1 h1 s1 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
   apply(subgoal_tac "\<lparr>epdaH_conf_state = q, epdaH_conf_history = h1, epdaH_conf_stack = s\<rparr> \<in> epdaH_configurations G'")
    apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
    apply(simp add: epdaH_configurations_def F_ALT_EPDA_RS_def Let_def)
    apply(case_tac "epda_initial G \<notin> Q")
     apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
   apply(rule_tac
      d="db"
      in epdaH.belongs_configurations)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
    apply(force)
   apply(rename_tac d i e q s h' da db ib ea q2 s2 h1)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
  apply(subgoal_tac "i=ib")
   apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d i e q h s h' da db ib ea q2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and ?d1.0="d"
      and ?d2.0="da"
      and x="0"
      and y="0"
      and n="ib"
      and m="ib"
      in epdaH.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
              apply(simp add: valid_dpda_def valid_pda_def)
             apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
             apply(force)
            apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
            apply(force)
           apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
           apply (metis DPDA_is_is_forward_deterministicHist_SB)
          apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
          apply(simp add: epdaH.derivation_initial_def)
          apply(erule_tac
      x="0"
      in allE)
          apply(clarsimp)
          apply(case_tac "db 0")
           apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
           apply(clarsimp)
          apply(rename_tac d e q h s h' da db ib ea q2 s2 a)(*strict*)
          apply(clarsimp)
          apply(case_tac a)
          apply(rename_tac d e q h s h' da db ib ea q2 s2 a option b)(*strict*)
          apply(clarsimp)
          apply(rename_tac d e q h s h' da db ib ea q2 s2 b)(*strict*)
          apply(simp add: epdaH_initial_configurations_def)
          apply(clarsimp)
          apply(case_tac "d 0")
           apply(rename_tac d e q h s h' da db ib ea q2 s2 b)(*strict*)
           apply(clarsimp)
          apply(rename_tac d e q h s h' da db ib ea q2 s2 b a)(*strict*)
          apply(clarsimp)
          apply(case_tac a)
          apply(rename_tac d e q h s h' da db ib ea q2 s2 b a option ba)(*strict*)
          apply(clarsimp)
          apply(rename_tac d e q h s h' da db ib ea q2 s2 b ba)(*strict*)
          apply(simp add: epdaH_initial_configurations_def)
         apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
         apply(force)
        apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
        apply(force)
       apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
       apply(force)
      apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
      apply(force)
     apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
     apply(force)
    apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
    apply(clarsimp)
    apply(simp add: epda_effects_def)
    apply(simp add: get_configuration_def)
    apply(subgoal_tac "\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h @ h', epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations G")
     apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
     apply(simp add: epdaH_configurations_def)
    apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
    apply(rule_tac
      d="da"
      in epdaH.belongs_configurations)
     apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
     apply(force)
    apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
    apply(force)
   apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
   apply(force)
  apply(rename_tac d e q h s h' da db ib ea q2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d h da db ib ea q2 s2)(*strict*)
  apply(subgoal_tac "\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = s2\<rparr> \<in> epdaH_configurations G'")
   apply(rename_tac d h da db ib ea q2 s2)(*strict*)
   apply(simp add: epdaH_configurations_def F_ALT_EPDA_RS_def Let_def)
   apply(case_tac "epda_initial G \<notin> Q")
    apply(rename_tac d h da db ib ea q2 s2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d h da db ib ea q2 s2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d h da db ib ea q2 s2)(*strict*)
  apply(rule_tac
      d="db"
      in epdaH.belongs_configurations)
   apply(rename_tac d h da db ib ea q2 s2)(*strict*)
   apply(rule epdaH.derivation_initial_belongs)
    apply(rename_tac d h da db ib ea q2 s2)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac d h da db ib ea q2 s2)(*strict*)
   apply(force)
  apply(rename_tac d h da db ib ea q2 s2)(*strict*)
  apply(erule_tac
      x="ib"
      in allE)
  apply(clarsimp)
  apply(force)
  done

lemma F_EPDA_RS__enforces_retain_edges_between_retained_states: "
  valid_dpda G
  \<Longrightarrow> Q \<subseteq> epda_states G
  \<Longrightarrow> F_ALT_EPDA_RS G Q = Some G'
  \<Longrightarrow> retain_edges_between_retained_states G Q G'"
  apply(simp add: F_EPDA_R_def retain_edges_between_retained_states_def F_ALT_EPDA_RS_def Let_def F_EPDA_RS_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(case_tac "epda_initial G \<notin> Q")
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  done

lemma F_ALT_EPDA_RS__SOUND: "
  F_EPDA_RS__SpecInput G Q
  \<Longrightarrow> F_EPDA_RS__SpecOutput G Q (F_ALT_EPDA_RS G Q)"
  apply(simp add: F_EPDA_RS__SpecOutput_def F_EPDA_RS__SpecInput_def)
  apply(clarsimp)
  apply(case_tac "F_ALT_EPDA_RS G Q")
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_RS_def)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G')
  apply(rename_tac G')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G')(*strict*)
   apply(rule F_ALT_EPDA_RS__preserves_valid_dpda)
     apply(rename_tac G')(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac G')(*strict*)
    apply(force)
   apply(rename_tac G')(*strict*)
   apply(force)
  apply(rename_tac G')(*strict*)
  apply(rule conjI)
   apply(rename_tac G')(*strict*)
   apply(rule F_ALT_EPDA_RS__preserves_no_epda_livelock)
       apply(rename_tac G')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac G')(*strict*)
      apply(force)
     apply(rename_tac G')(*strict*)
     apply(force)
    apply(rename_tac G')(*strict*)
    apply(force)
   apply(rename_tac G')(*strict*)
   apply(force)
  apply(rename_tac G')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G')(*strict*)
   apply(rule F_ALT_EPDA_RS__no_modification)
      apply(rename_tac G')(*strict*)
      apply(force)
     apply(rename_tac G')(*strict*)
     apply(force)
    apply(rename_tac G')(*strict*)
    apply(force)
   apply(rename_tac G')(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule order_antisym)
    apply(rename_tac G')(*strict*)
    apply(force)
   apply(rename_tac G')(*strict*)
   apply(rule F_ALT_EPDA_RS__lang_modification)
          apply(rename_tac G')(*strict*)
          apply(force)
         apply(rename_tac G')(*strict*)
         apply(force)
        apply(rename_tac G')(*strict*)
        apply(force)
       apply(rename_tac G')(*strict*)
       apply(force)
      apply(rename_tac G')(*strict*)
      apply(force)
     apply(rename_tac G')(*strict*)
     apply(force)
    apply(rename_tac G')(*strict*)
    apply(force)
   apply(rename_tac G')(*strict*)
   apply(force)
  apply(rule F_EPDA_RS__enforces_retain_edges_between_retained_states)
    apply(force)
   apply(force)
  apply(force)
  done

theorem F_EPDA_RS__SOUND: "
  F_EPDA_RS__SpecInput G Q
  \<Longrightarrow> F_EPDA_RS__SpecOutput G Q (F_EPDA_RS G Q)"
  apply(rule_tac t="F_EPDA_RS G Q" and s="F_ALT_EPDA_RS G Q" in subst)
   apply(rule F_EPDA_RS__vs_F_ALT_EPDA_RS)
    apply(simp add: F_EPDA_RS__SpecInput_def)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(simp add: F_EPDA_RS__SpecInput_def)
  apply(rule F_ALT_EPDA_RS__SOUND)
  apply(force)
  done

hide_const F_ALT_EPDA_RS
hide_fact F_EPDA_RS__vs_F_ALT_EPDA_RS
hide_fact F_ALT_EPDA_RS__preserves_valid_pda
hide_fact F_ALT_EPDA_RS__preserves_valid_dpda
hide_fact F_ALT_EPDA_RS__preserves_no_epda_livelock
hide_fact F_ALT_EPDA_RS__no_modification
hide_fact F_ALT_EPDA_RS__lang_modification
hide_fact F_ALT_EPDA_RS__SOUND
hide_fact F_EPDA_RS__enforces_retain_edges_between_retained_states

end
