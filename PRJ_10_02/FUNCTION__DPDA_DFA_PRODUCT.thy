section {*FUNCTION\_\_DPDA\_DFA\_PRODUCT*}
theory
  FUNCTION__DPDA_DFA_PRODUCT

imports
  PRJ_10_02__ENTRY

begin

lemma F_DPDA_DFA_PRODUCT__produces__PDA: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_pda R"
  apply(simp add: valid_dpda_def valid_dfa_def F_DPDA_DFA_PRODUCT_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_DFA_PRODUCT__states_def)
   apply(rule_tac
      t="{cons_tuple2 p q |p q. p \<in> epda_states M \<and> q \<in> epda_states D}"
      and s="(\<lambda>(x,y). cons_tuple2 x y) ` ((epda_states M) \<times> (epda_states D))"
      in ssubst)
    apply(force)
   apply(rule finite_imageI)
   apply(force)
  apply(rule conjI)
   apply(simp add: F_DPDA_DFA_PRODUCT__events_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_DFA_PRODUCT__edges_def)
   apply(rule conjI)
    apply(simp add: F_DPDA_DFA_PRODUCT__edges_execute_def)
    apply(rule_tac
      B="(\<lambda>(e,e'). \<lparr>edge_src = cons_tuple2 (edge_src e) (edge_src e'), edge_event = edge_event e, edge_pop = edge_pop e, edge_push = edge_push e, edge_trg = cons_tuple2 (edge_trg e) (edge_trg e')\<rparr>) ` ((epda_delta M) \<times> (epda_delta D))"
      in finite_subset)
     apply(clarsimp)
     apply(rename_tac e e')(*strict*)
     apply(rule inMap)
     apply(rule_tac
      x="(e,e')"
      in bexI)
      apply(rename_tac e e')(*strict*)
      apply(force)
     apply(rename_tac e e')(*strict*)
     apply(force)
    apply(rule finite_imageI)
    apply(force)
   apply(simp add: F_DPDA_DFA_PRODUCT__edges_empty_def)
   apply(rule_tac
      B="(\<lambda>(e,p). \<lparr>edge_src = cons_tuple2 (edge_src e) p, edge_event = None, edge_pop = edge_pop e, edge_push = edge_push e, edge_trg = cons_tuple2 (edge_trg e) p\<rparr>) ` ((epda_delta M) \<times> (epda_states D))"
      in finite_subset)
    apply(clarsimp)
    apply(rename_tac e p)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="(e,p)"
      in bexI)
     apply(rename_tac e p)(*strict*)
     apply(force)
    apply(rename_tac e p)(*strict*)
    apply(force)
   apply(rule finite_imageI)
   apply(force)
  apply(rule conjI)
   apply(simp add: F_DPDA_DFA_PRODUCT__states_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_DFA_PRODUCT__marking_states_def F_DPDA_DFA_PRODUCT__states_def)
   apply(clarsimp)
   apply(rename_tac p q)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_DPDA_DFA_PRODUCT__edges_def)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(simp add: valid_epda_step_label_def F_DPDA_DFA_PRODUCT__edges_execute_def)
    apply(clarsimp)
    apply(rename_tac e e')(*strict*)
    apply(simp add: F_DPDA_DFA_PRODUCT__marking_states_def F_DPDA_DFA_PRODUCT__states_def F_DPDA_DFA_PRODUCT__events_def)
    apply(simp add: option_to_set_def)
    apply(clarsimp)
    apply(rename_tac e e' x)(*strict*)
    apply(erule_tac
      x="e'"
      and P="\<lambda>e'. edge_src e' \<in> epda_states D \<and> edge_trg e' \<in> epda_states D \<and> {y. Some y = edge_event e'} \<subseteq> epda_events D \<and> [epda_box D] \<in> may_terminated_by (epda_gamma D) (epda_box D)"
      in ballE)
     apply(rename_tac e e' x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac e e' x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: valid_epda_step_label_def F_DPDA_DFA_PRODUCT__edges_empty_def)
   apply(clarsimp)
   apply(rename_tac e p)(*strict*)
   apply(simp add: F_DPDA_DFA_PRODUCT__marking_states_def F_DPDA_DFA_PRODUCT__states_def F_DPDA_DFA_PRODUCT__events_def)
   apply(simp add: option_to_set_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_DFA_PRODUCT__edges_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: valid_epda_step_label_def F_DPDA_DFA_PRODUCT__edges_execute_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: valid_epda_step_label_def F_DPDA_DFA_PRODUCT__edges_empty_def)
  apply(clarsimp)
  done

definition slice_edge_A :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epda_step_label
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label"
  where
    "slice_edge_A e \<equiv>
  \<lparr>edge_src = sel_tuple2_1 (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = sel_tuple2_1 (edge_trg e)\<rparr>"

definition slice_conf_A :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epdaH_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaH_conf"
  where
    "slice_conf_A c \<equiv>
  \<lparr>epdaH_conf_state = sel_tuple2_1 (epdaH_conf_state c),
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = epdaH_conf_stack c\<rparr>"

definition slice_edge_B :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epda_step_label
  \<Rightarrow> 'stackB list
  \<Rightarrow> ('stateB, 'event, 'stackB) epda_step_label"
  where
    "slice_edge_B e s \<equiv>
  \<lparr>edge_src = sel_tuple2_2 (edge_src e),
  edge_event = edge_event e,
  edge_pop = s,
  edge_push = s,
  edge_trg = sel_tuple2_2 (edge_trg e)\<rparr>"

definition slice_conf_B :: "
  (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epdaH_conf
  \<Rightarrow> 'stackB list
  \<Rightarrow> ('stateB, 'event, 'stackB) epdaH_conf"
  where
    "slice_conf_B c s \<equiv>
  \<lparr>epdaH_conf_state = sel_tuple2_2 (epdaH_conf_state c),
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = s\<rparr>"

lemma F_DPDA_DFA_PRODUCT__reflects__derivation_initial: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_pda R
  \<Longrightarrow> epdaH.derivation_initial R dR
  \<Longrightarrow> dR n = Some (pair eR \<lparr>epdaH_conf_state = cons_tuple2 q1 q2, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>)
  \<Longrightarrow> \<exists>dM dD nD eM eD. nD \<le> n \<and> epdaH.derivation_initial D dD \<and> epdaH.derivation_initial M dM \<and> dM n = Some (pair eM \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>) \<and> dD nD = Some (pair eD \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr>)"
  apply(induct n arbitrary: eR q1 q2 h s)
   apply(rename_tac eR q1 q2 h s)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in exI)
   apply(rename_tac eR q1 q2 h s)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr>"
      in exI)
   apply(rename_tac eR q1 q2 h s)(*strict*)
   apply(rule conjI)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(rule epdaH.derivation_initialI)
     apply(rename_tac eR q1 q2 h s)(*strict*)
     apply(rule epdaH.der1_is_derivation)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(clarsimp)
    apply(rename_tac eR q1 q2 h s c)(*strict*)
    apply(simp add: get_configuration_def der1_def)
    apply(clarsimp)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 h s)(*strict*)
    apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__states_def)
    apply(clarsimp)
    apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
   apply(rename_tac eR q1 q2 h s)(*strict*)
   apply(rule conjI)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(rule epdaH.derivation_initialI)
     apply(rename_tac eR q1 q2 h s)(*strict*)
     apply(rule epdaH.der1_is_derivation)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(clarsimp)
    apply(rename_tac eR q1 q2 h s c)(*strict*)
    apply(simp add: get_configuration_def der1_def)
    apply(clarsimp)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 h s)(*strict*)
    apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__states_def)
    apply(clarsimp)
   apply(rename_tac eR q1 q2 h s)(*strict*)
   apply(rule conjI)
    apply(rename_tac eR q1 q2 h s)(*strict*)
    apply(rule_tac
      x="None"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac eR q1 q2 h s)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(simp add: der1_def)
  apply(rename_tac n eR q1 q2 h s)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n eR q1 q2 h s)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_DFA_PRODUCT M D"
      and d="dR"
      and n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n eR q1 q2 h s)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n eR q1 q2 h s)(*strict*)
    apply(force)
   apply(rename_tac n eR q1 q2 h s)(*strict*)
   apply(force)
  apply(rename_tac n eR q1 q2 h s)(*strict*)
  apply(clarsimp)
  apply(rename_tac n q1 q2 h s e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(case_tac c1)
  apply(rename_tac n q1 q2 h s e1 e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac n q1 q2 h s e1 e2 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac qx hx sx)
  apply(rename_tac n q1 q2 h s e1 e2 qx hx sx)(*strict*)
  apply(case_tac qx)
  apply(rename_tac n q1 q2 h s e1 e2 qx hx sx a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n q1 q2 h s e1 e2 hx sx a b)(*strict*)
  apply(rename_tac p1 p2)
  apply(rename_tac n q1 q2 h s e1 e2 hx sx p1 p2)(*strict*)
  apply(erule_tac
      x="p1"
      in meta_allE)
  apply(erule_tac
      x="p2"
      in meta_allE)
  apply(erule_tac
      x="hx"
      in meta_allE)
  apply(erule_tac
      x="sx"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n q1 q2 h s e1 e2 hx sx p1 p2 dM dD nD eM eD)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n q1 q2 h s e1 e2 hx sx p1 p2 dM dD nD eM eD edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(clarsimp)
  apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs read pop push qt)
  apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
  apply(subgoal_tac "\<lparr>edge_src = qs, edge_event = read, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr> \<in> F_DPDA_DFA_PRODUCT__edges M D")
   apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def)
   apply(simp add: F_DPDA_DFA_PRODUCT_def)
  apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
  apply(simp add: F_DPDA_DFA_PRODUCT__edges_def)
  apply(subgoal_tac "\<lparr>epdaH_conf_state = cons_tuple2 p1 p2, epdaH_conf_history = hx, epdaH_conf_stack = sx\<rparr> \<in> epdaH_configurations (F_DPDA_DFA_PRODUCT M D)")
   apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
   prefer 2
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
     apply(simp add: valid_pda_def)
    apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
    apply(force)
   apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
   apply(force)
  apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
  apply(erule disjE)
   apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
   apply(simp add: F_DPDA_DFA_PRODUCT__edges_execute_def)
   apply(clarsimp)
   apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD e e')(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w)(*strict*)
   apply(thin_tac "\<lparr>edge_src = cons_tuple2 (edge_src e) (edge_src e'), edge_event = edge_event e', edge_pop = edge_pop e, edge_push = edge_push e, edge_trg = cons_tuple2 (edge_trg e) (edge_trg e')\<rparr> \<in> epda_delta (F_DPDA_DFA_PRODUCT M D)")
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w)(*strict*)
   apply(case_tac "edge_event e'")
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w)(*strict*)
    apply(clarsimp)
    apply(simp add: valid_dfa_def)
    apply(clarsimp)
    apply(force)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w a)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<sigma>)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule_tac
      x="derivation_append dM (der2 \<lparr>epdaH_conf_state = edge_src e, epdaH_conf_history = hx, epdaH_conf_stack = edge_pop e @ w\<rparr> e \<lparr>epdaH_conf_state = edge_trg e, epdaH_conf_history = hx @ option_to_list (Some \<sigma>), epdaH_conf_stack = edge_push e @ w\<rparr>) n"
      in exI)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule_tac
      x="derivation_append dD (der2 \<lparr>epdaH_conf_state = edge_src e', epdaH_conf_history = hx, epdaH_conf_stack = [epda_box D]\<rparr> e' \<lparr>epdaH_conf_state = edge_trg e', epdaH_conf_history = hx @ option_to_list (Some \<sigma>), epdaH_conf_stack = [epda_box D]\<rparr>) nD"
      in exI)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule_tac
      x="Suc nD"
      in exI)
   apply(rule conjI)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(force)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule conjI)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
     apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
     apply(force)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: epdaH_step_relation_def)
     apply(simp add: valid_dfa_def)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule conjI)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
     apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
     apply(force)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
     apply(rule epdaH.der2_is_derivation)
     apply(simp add: epdaH_step_relation_def)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
    apply(clarsimp)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule conjI)
    apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
    apply(rule_tac
      x="Some e"
      in exI)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac n e1 hx dM dD nD eM eD e e' w \<sigma>)(*strict*)
   apply(rule_tac
      x="Some e'"
      in exI)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD qs read pop push qt)(*strict*)
  apply(simp add: F_DPDA_DFA_PRODUCT__edges_empty_def)
  apply(clarsimp)
  apply(rename_tac n q1 q2 h s e1 hx sx p1 p2 dM dD nD eM eD e p)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(thin_tac "\<lparr>edge_src = cons_tuple2 (edge_src e) p, edge_event = None, edge_pop = edge_pop e, edge_push = edge_push e, edge_trg = cons_tuple2 (edge_trg e) p\<rparr> \<in> epda_delta (F_DPDA_DFA_PRODUCT M D)")
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(rule_tac
      x="derivation_append dM (der2 \<lparr>epdaH_conf_state = edge_src e, epdaH_conf_history = hx, epdaH_conf_stack = edge_pop e @ w\<rparr> e \<lparr>epdaH_conf_state = edge_trg e, epdaH_conf_history = hx @ option_to_list None, epdaH_conf_stack = edge_push e @ w\<rparr>) n"
      in exI)
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(rule_tac
      x="dD"
      in exI)
  apply(rule_tac
      x="nD"
      in exI)
  apply(rule conjI)
   apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
   apply(force)
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(rule conjI)
   apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
   apply(force)
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(rule conjI)
   apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
    apply(force)
   apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(simp add: epdaH_step_relation_def)
   apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
   apply(simp add: valid_dfa_def)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(rule conjI)
   apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
   apply(rule_tac
      x="Some e"
      in exI)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n e1 hx dM dD nD eM eD e p w)(*strict*)
  apply(rule_tac
      x="eD"
      in exI)
  apply(simp add: derivation_append_def der2_def)
  apply(simp add: option_to_list_def)
  done

lemma F_DPDA_DFA_PRODUCT__reflects__derivation_initial2: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_pda R
  \<Longrightarrow> epdaH.derivation_initial R dR
  \<Longrightarrow> epdaH.derivation_initial M (\<lambda>n. case dR n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (slice_edge_A e)) (slice_conf_A c)))"
  apply(rule epdaH.derivation_initialI)
   prefer 2
   apply(simp add: get_configuration_def epdaH.derivation_initial_def epdaH.derivation_def)
   apply(case_tac "dR 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a c)(*strict*)
   apply(case_tac a)
   apply(rename_tac a c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def slice_conf_A_def sel_tuple2_1_def F_DPDA_DFA_PRODUCT_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(simp add: epdaH.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def slice_conf_A_def sel_tuple2_1_def F_DPDA_DFA_PRODUCT_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(simp add: get_configuration_def epdaH.derivation_initial_def epdaH.derivation_def)
   apply(clarsimp)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(case_tac "dR 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "dR (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_DFA_PRODUCT M D"
      and d="dR"
      and n="nat"
      and m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(simp add: slice_edge_A_def)
  apply(case_tac c1)
  apply(rename_tac nat e1 e2 c1 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c2 w epdaH_conf_historya)(*strict*)
  apply(case_tac c2)
  apply(rename_tac nat e1 e2 c2 w epdaH_conf_historya epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 w epdaH_conf_historya)(*strict*)
  apply(case_tac e2)
  apply(rename_tac nat e1 e2 w epdaH_conf_historya edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 w epdaH_conf_historya edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac h qs r po pu qt)
  apply(rename_tac nat e1 w h qs r po pu qt)(*strict*)
  apply(case_tac qs)
  apply(rename_tac nat e1 w h qs r po pu qt a b)(*strict*)
  apply(case_tac qt)
  apply(rename_tac nat e1 w h qs r po pu qt a b aa ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 w h r po pu a b aa ba)(*strict*)
  apply(simp add: slice_conf_A_def)
  apply(simp add: F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def)
  apply(erule disjE)
   apply(rename_tac nat e1 w h r po pu a b aa ba)(*strict*)
   apply(simp add: F_DPDA_DFA_PRODUCT__edges_execute_def)
   apply(clarsimp)
   apply(rename_tac nat e1 w h e e')(*strict*)
   apply(case_tac e)
   apply(rename_tac nat e1 w h e e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat e1 w h r po pu a b aa ba)(*strict*)
  apply(simp add: F_DPDA_DFA_PRODUCT__edges_empty_def)
  apply(clarsimp)
  apply(rename_tac nat e1 w h b e)(*strict*)
  apply(case_tac e)
  apply(rename_tac nat e1 w h b e edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_DFA_PRODUCT__preserves__derivation_initial: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_pda R
  \<Longrightarrow> epdaH.derivation_initial D dD
  \<Longrightarrow> epdaH.derivation_initial M dM
  \<Longrightarrow> length h + ints = n
  \<Longrightarrow> dM n = Some (pair eM \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>)
  \<Longrightarrow> dD (length h) = Some (pair eD \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr>)
  \<Longrightarrow> \<exists>dR eR. epdaH.derivation_initial R dR \<and> dR n = Some (pair eR \<lparr>epdaH_conf_state = cons_tuple2 q1 q2, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>)"
  apply(induct n arbitrary: h q1 q2 s eM eD ints)
   apply(rename_tac h q1 q2 s eM eD ints)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 q2 s eM eD)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>epdaH_conf_state = cons_tuple2 q1 q2, epdaH_conf_history = [], epdaH_conf_stack = s\<rparr>"
      in exI)
   apply(rename_tac q1 q2 s eM eD)(*strict*)
   apply(rule conjI)
    apply(rename_tac q1 q2 s eM eD)(*strict*)
    apply(rule epdaH.derivation_initialI)
     apply(rename_tac q1 q2 s eM eD)(*strict*)
     apply(rule epdaH.der1_is_derivation)
    apply(rename_tac q1 q2 s eM eD)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 q2 s eM eD c)(*strict*)
    apply(simp add: get_configuration_def der1_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 s eM eD)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 s)(*strict*)
    apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__states_def)
    apply(clarsimp)
   apply(rename_tac q1 q2 s eM eD)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(simp add: der1_def)
  apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
   prefer 2
   apply(rule_tac
      G="M"
      and d="dM"
      and n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
    apply(force)
   apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
   apply(force)
  apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
  apply(clarsimp)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac qx hx sx)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 qx hx sx)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 qx hx sx edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(clarsimp)
  apply(rename_tac n h q1 q2 s eD ints e1 qx hx sx edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs read pop push qt)
  apply(rename_tac n h q1 q2 s eD ints e1 qx hx sx qs read pop push qt)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n q2 eD ints e1 hx qs read pop push qt w)(*strict*)
  apply(erule_tac
      x="hx"
      in meta_allE)
  apply(erule_tac
      x="qs"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac read)
   apply(rename_tac n q2 eD ints e1 hx qs read pop push qt w)(*strict*)
   apply(clarsimp)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w)(*strict*)
   apply(simp add: option_to_list_def)
   apply(erule_tac
      x="q2"
      in meta_allE)
   apply(erule_tac
      x="pop@w"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="e1"
      in meta_allE)
   apply(erule_tac
      x="eD"
      in meta_allE)
   apply(clarsimp)
   apply(case_tac ints)
    apply(rename_tac n q2 eD ints e1 hx qs pop push qt w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
     prefer 2
     apply(rule_tac
      G="M"
      and d="dM"
      and n="n"
      in epda_at_most_one_symbol_per_step)
       apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
      apply(force)
     apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
     apply(force)
    apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
    apply(clarsimp)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac q2 eD e1 hx qs pop push qt w nat)(*strict*)
   apply(erule_tac
      x="nat"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac q2 eD e1 hx qs pop push qt w nat dR eR)(*strict*)
   apply(rename_tac ints dR eR)
   apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
   apply(subgoal_tac "\<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr> \<in> epdaH_configurations (F_DPDA_DFA_PRODUCT M D)")
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule_tac
      x="derivation_append dR (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr> \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt q2\<rparr> \<lparr>epdaH_conf_state = cons_tuple2 qt q2, epdaH_conf_history = hx, epdaH_conf_stack = push @ w\<rparr>) (length hx + ints)"
      in exI)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule conjI)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation_initial)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
      apply(force)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(rule epdaH.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
      apply(rule epdaH.der2_is_derivation)
      apply(simp add: epdaH_step_relation_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def)
      apply(rule conjI)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(rule disjI2)
       apply(simp add: F_DPDA_DFA_PRODUCT__edges_empty_def)
       apply(rule_tac
      x="\<lparr>edge_src = qs, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr>"
      in exI)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(clarsimp)
       apply(simp add: epdaH_configurations_def F_DPDA_DFA_PRODUCT__states_def)
      apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule_tac
      x="Some \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt q2\<rparr>"
      in exI)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(simp add: valid_pda_def)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(force)
   apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
   apply(force)
  apply(rename_tac n q2 eD ints e1 hx qs read pop push qt w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
   prefer 2
   apply(rule_tac
      G="D"
      and d="dD"
      and n="length hx"
      and m="Suc (length hx)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
    apply(force)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
   apply(force)
  apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q2' h' s')
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 q2' h' s')(*strict*)
  apply(erule_tac
      x="q2'"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="pop@w"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="ints"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
  apply(subgoal_tac "(\<forall>e\<in> epda_delta D. edge_event e \<noteq> None \<and> edge_pop e = [epda_box D] \<and> edge_push e = [epda_box D])")
   apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
   prefer 2
   apply(unfold valid_dfa_def)[1]
   apply(erule conjE)+
   apply(force)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
  apply(clarify)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa y)(*strict*)
  apply(case_tac e2)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa y edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarify)
  apply(simp)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a h' wa y edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarify)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a h' wa y edge_src edge_event edge_pop edge_push edge_trg dR eR)(*strict*)
  apply(simp)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y edge_src edge_trg dR eR)(*strict*)
  apply(rename_tac qxs qxt dR eR)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(rule_tac
      x="derivation_append dR (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs qxs, epdaH_conf_history = h', epdaH_conf_stack = pop @ w\<rparr> \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt qxt\<rparr> \<lparr>epdaH_conf_state = cons_tuple2 qt qxt, epdaH_conf_history = h' @ [y], epdaH_conf_stack = push @ w\<rparr>) (length h' + ints)"
      in exI)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(rule conjI)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(force)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(simp add: epdaH_step_relation_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def)
    apply(simp add: option_to_list_def)
    apply(rule disjI1)
    apply(simp add: F_DPDA_DFA_PRODUCT__edges_execute_def)
    apply(rule_tac
      x="\<lparr>edge_src = qs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr>"
      in exI)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="\<lparr>edge_src = qxs, edge_event = Some y, edge_pop = [epda_box D], edge_push = [epda_box D], edge_trg = qxt\<rparr>"
      in exI)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(clarsimp)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(rule_tac
      x="Some \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt qxt\<rparr>"
      in exI)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  done

lemma F_DPDA_DFA_PRODUCT__reflects__unmarked_language: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> epdaH.unmarked_language R \<subseteq> epdaH.unmarked_language M \<inter> epdaH.unmarked_language D"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH.derivation (F_DPDA_DFA_PRODUCT M D) d")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e q h s)(*strict*)
  apply(case_tac q)
  apply(rename_tac d i e q h s a b)(*strict*)
  apply(rename_tac q1 q2)
  apply(rename_tac d i e q h s q1 q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s q1 q2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e h s q1 q2)(*strict*)
   prefer 2
   apply(rule_tac
      eR="e"
      and n="i"
      in F_DPDA_DFA_PRODUCT__reflects__derivation_initial)
        apply(rename_tac d i e h s q1 q2)(*strict*)
        apply(force)
       apply(rename_tac d i e h s q1 q2)(*strict*)
       apply(force)
      apply(rename_tac d i e h s q1 q2)(*strict*)
      apply(force)
     apply(rename_tac d i e h s q1 q2)(*strict*)
     apply(rule F_DPDA_DFA_PRODUCT__produces__PDA)
       apply(rename_tac d i e h s q1 q2)(*strict*)
       apply(force)
      apply(rename_tac d i e h s q1 q2)(*strict*)
      apply(force)
     apply(rename_tac d i e h s q1 q2)(*strict*)
     apply(force)
    apply(rename_tac d i e h s q1 q2)(*strict*)
    apply(force)
   apply(rename_tac d i e h s q1 q2)(*strict*)
   apply(force)
  apply(rename_tac d i e h s q1 q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="dM"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: epdaH.derivation_initial_def)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      x="dD"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="nD"
      in exI)
   apply(clarsimp)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  done

lemma F_DPDA_DFA_PRODUCT__preserves__unmarked_language: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> epdaH.unmarked_language M \<inter> epdaH.unmarked_language D \<subseteq> epdaH.unmarked_language R"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d da)(*strict*)
  apply(thin_tac "epdaH.derivation M d")
  apply(thin_tac "epdaH.derivation D da")
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d da i ia e ea c ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac ca)
  apply(rename_tac d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da i ia e ea epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 s1 q2 h s2)
  apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="D"
      and d="da"
      and n="ia"
      in DFA_one_symbol_per_step)
     apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
     apply(force)
    apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
    apply(force)
   apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
   apply(force)
  apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="M"
      and d="d"
      and n="i"
      in epda_at_most_one_symbol_per_step)
     apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
    apply(force)
   apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
   apply(force)
  apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>ints. length h+ints=i")
   apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
   prefer 2
   apply(rule_tac
      x="i-length h"
      in exI)
   apply(force)
  apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
   prefer 2
   apply(rule DFA_stack_consists_only_of_box)
     apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
   prefer 2
   apply(rule_tac
      h="h"
      and ints="ints"
      and D="D"
      and M="M"
      in F_DPDA_DFA_PRODUCT__preserves__derivation_initial)
           apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
           apply(force)
          apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
          apply(force)
         apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
         apply(force)
        apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
        apply(rule F_DPDA_DFA_PRODUCT__produces__PDA)
          apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
          apply(force)
         apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
         apply(force)
        apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
        apply(force)
       apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
       apply(force)
      apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
      apply(force)
     apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(rule_tac
      x="dR"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
   apply(rule_tac
      x="length h+ints"
      in exI)
   apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  done

theorem F_DPDA_DFA_PRODUCT__relates__unmarked_language: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> epdaH.unmarked_language R = epdaH.unmarked_language M \<inter> epdaH.unmarked_language D"
  apply(rule order_antisym)
   apply(rule F_DPDA_DFA_PRODUCT__reflects__unmarked_language)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_DPDA_DFA_PRODUCT__preserves__unmarked_language)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DFA_PRODUCT__reflects__marked_language: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> epdaH.marked_language R \<subseteq> epdaH.marked_language M \<inter> epdaH.marked_language D"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH.derivation (F_DPDA_DFA_PRODUCT M D) d")
  apply(subgoal_tac "(\<exists>d. epdaH.derivation_initial M d \<and> x \<in> epdaH_marked_effect M d) \<and> (\<exists>d. epdaH.derivation_initial D d \<and> x \<in> epdaH_marked_effect D d)")
   apply(rename_tac x d)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d da db)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d da db)(*strict*)
    apply(rule_tac
      x="da"
      in exI)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def)
    apply(simp add: epdaH_marking_condition_def epdaH_marked_effect_def)
    apply(clarsimp)
    apply(rename_tac d da db i ia ib ic e ea eb ec c ca cb cc)(*strict*)
    apply(rule_tac
      x="ib"
      in exI)
    apply(clarsimp)
   apply(rename_tac x d da db)(*strict*)
   apply(rule_tac
      x="db"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marking_condition_def epdaH_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac d da db i ia ib ic e ea eb ec c ca cb cc)(*strict*)
   apply(rule_tac
      x="ic"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(thin_tac "epdaH_marking_condition (F_DPDA_DFA_PRODUCT M D) d")
  apply(simp add: epdaH_marked_effect_def epdaH_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i e c)(*strict*)
  apply(thin_tac "\<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> epdaH_string_state c = epdaH_string_state c'")
  apply(rename_tac d i e c)(*strict*)
  apply(thin_tac "c \<in> epdaH_configurations (F_DPDA_DFA_PRODUCT M D)")
  apply(case_tac c)
  apply(rename_tac d i e c epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d i e q h s)(*strict*)
  apply(case_tac q)
  apply(rename_tac d i e q h s a b)(*strict*)
  apply(rename_tac q1 q2)
  apply(rename_tac d i e q h s q1 q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s q1 q2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i e h s q1 q2)(*strict*)
   prefer 2
   apply(rule_tac
      eR="e"
      and n="i"
      in F_DPDA_DFA_PRODUCT__reflects__derivation_initial)
        apply(rename_tac d i e h s q1 q2)(*strict*)
        apply(force)
       apply(rename_tac d i e h s q1 q2)(*strict*)
       apply(force)
      apply(rename_tac d i e h s q1 q2)(*strict*)
      apply(force)
     apply(rename_tac d i e h s q1 q2)(*strict*)
     apply(rule F_DPDA_DFA_PRODUCT__produces__PDA)
       apply(rename_tac d i e h s q1 q2)(*strict*)
       apply(force)
      apply(rename_tac d i e h s q1 q2)(*strict*)
      apply(force)
     apply(rename_tac d i e h s q1 q2)(*strict*)
     apply(force)
    apply(rename_tac d i e h s q1 q2)(*strict*)
    apply(force)
   apply(rename_tac d i e h s q1 q2)(*strict*)
   apply(force)
  apply(rename_tac d i e h s q1 q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="derivation_take dM i"
      in exI)
   apply(rule conjI)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="eM"
      in exI)
   apply(rule_tac
      x="\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in exI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(rule epdaH.belongs_configurations)
     apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
     apply(rule epdaH.derivation_initial_belongs)
      apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
     apply(force)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(force)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD j e' c')(*strict*)
   apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      x="derivation_take dD nD"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      x="nD"
      in exI)
  apply(rule_tac
      x="eD"
      in exI)
  apply(rule_tac
      x="\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr>"
      in exI)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(force)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(force)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e h s q1 q2 dM dD nD eM eD j e' c')(*strict*)
  apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
  done

lemma F_DPDA_DFA_PRODUCT__preserves__marked_language: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> epdaH.marked_language M \<inter> epdaH.marked_language D \<subseteq> epdaH.marked_language R"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaH.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d da)(*strict*)
  apply(thin_tac "epdaH.derivation M d")
  apply(thin_tac "epdaH.derivation D da")
  apply(thin_tac "epdaH_marking_condition M d")
  apply(thin_tac "epdaH_marking_condition D da")
  apply(subgoal_tac "\<exists>d. epdaH.derivation_initial (F_DPDA_DFA_PRODUCT M D) d \<and> x \<in> epdaH_marked_effect (F_DPDA_DFA_PRODUCT M D) d")
   apply(rename_tac x d da)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d da db)(*strict*)
   apply(rule_tac
      x="db"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def)
   apply(simp add: epdaH_marked_effect_def epdaH_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac d da db i ia ib e ea eb c ca cb)(*strict*)
   apply(rule_tac
      x="ib"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d da)(*strict*)
  apply(simp add: epdaH_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac d da i ia e ea c ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(case_tac ca)
  apply(rename_tac d da i ia e ea c ca epdaH_conf_state epdaH_conf_historya epdaH_conf_stack epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da i ia e ea epdaH_conf_state epdaH_conf_stack epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 s1 q2 h s2)
  apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="D"
      and d="da"
      and n="ia"
      in DFA_one_symbol_per_step)
     apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
     apply(force)
    apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
    apply(force)
   apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
   apply(force)
  apply(rename_tac d da i ia e ea q1 s1 q2 h s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
   prefer 2
   apply(rule_tac
      G="M"
      and d="d"
      and n="i"
      in epda_at_most_one_symbol_per_step)
     apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
    apply(force)
   apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
   apply(force)
  apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>ints. length h+ints=i")
   apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
   prefer 2
   apply(rule_tac
      x="i-length h"
      in exI)
   apply(force)
  apply(rename_tac d da i e ea q1 s1 q2 h s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
   prefer 2
   apply(rule DFA_stack_consists_only_of_box)
     apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q1 s1 q2 h s2 ints)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
   prefer 2
   apply(rule_tac
      h="h"
      and ints="ints"
      and D="D"
      and M="M"
      in F_DPDA_DFA_PRODUCT__preserves__derivation_initial)
           apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
           apply(force)
          apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
          apply(force)
         apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
         apply(force)
        apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
        apply(rule F_DPDA_DFA_PRODUCT__produces__PDA)
          apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
          apply(force)
         apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
         apply(force)
        apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
        apply(force)
       apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
       apply(force)
      apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
      apply(force)
     apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q1 s1 q2 h ints)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(rule_tac
      x="derivation_take dR (length h+ints)"
      in exI)
  apply(rule conjI)
   apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(rule_tac
      x="length h+ints"
      in exI)
  apply(rule_tac
      x="eR"
      in exI)
  apply(rule_tac
      x="\<lparr>epdaH_conf_state = cons_tuple2 q1 q2, epdaH_conf_history = h, epdaH_conf_stack = s1\<rparr>"
      in exI)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(rule conjI)
   apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(rule conjI)
   apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
   apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def epdaH_marking_configurations_def epdaH_configurations_def F_DPDA_DFA_PRODUCT__states_def F_DPDA_DFA_PRODUCT__events_def)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(rule conjI)
   apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
   apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def epdaH_marking_configurations_def epdaH_configurations_def F_DPDA_DFA_PRODUCT__states_def F_DPDA_DFA_PRODUCT__events_def)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q1 s1 q2 h ints dR eR j e' c')(*strict*)
  apply(simp add: derivation_take_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__marking_states_def)
  done

theorem F_DPDA_DFA_PRODUCT__relates__marked_language: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> epdaH.marked_language R = (epdaH.marked_language M) \<inter> (epdaH.marked_language D)"
  apply(rule order_antisym)
   apply(rule F_DPDA_DFA_PRODUCT__reflects__marked_language)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_DPDA_DFA_PRODUCT__preserves__marked_language)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DFA_PRODUCT__preserves__determinism: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_pda R
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible R"
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long M")
   prefer 2
   apply(rule DPDA_to_epdaH_determinism)
   apply(force)
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long R")
   apply (metis epda_epdaS_is_forward_edge_deterministic_accessible_equal_to_epdaH_is_forward_edge_deterministicHist_DB_long valid_pda_to_valid_epda)
  apply(subgoal_tac "epdaH.is_forward_edge_deterministicHist_DB_long D")
   prefer 2
   apply(rule DPDA_to_epdaH_determinism)
   apply(simp add: valid_dfa_def)
  apply(clarsimp)
  apply(simp add: epdaH.is_forward_edge_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2)(*strict*)
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
  apply(case_tac c)
  apply(rename_tac c d c1 c2 e1 e2 n w1 w2 option epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 option epdaH_conf_state epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac e q h s)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e q h s)(*strict*)
  apply(case_tac q)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e q h s a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s a b)(*strict*)
  apply(rename_tac q1 q2)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
   prefer 2
   apply(rule_tac F_DPDA_DFA_PRODUCT__reflects__derivation_initial)
        apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
        apply(force)
       apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
       apply(force)
      apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
      apply(force)
     apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
     apply(rule F_DPDA_DFA_PRODUCT__produces__PDA)
       apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
       apply(force)
      apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
      apply(force)
     apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
     apply(force)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
    apply(force)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
   apply(force)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>"
      in allE)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule impE)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="dM"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr>"
      in allE)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule impE)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="dD"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="nD"
      in exI)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule_tac
      x="slice_conf_A c1"
      in allE)
  apply(erule_tac
      x="slice_conf_A c2"
      in allE)
  apply(erule_tac
      x="slice_edge_A e1"
      in allE)
  apply(erule_tac
      x="slice_edge_A e2"
      in allE)
  apply(erule impE)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   prefer 2
   apply(simp add: slice_edge_A_def slice_edge_B_def)
   apply(case_tac e1)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac e2)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 c2 n w1 w2 e h s q1 q2 dM dD nD eM eD edge_src edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac edge_src)
   apply(rename_tac d c1 c2 n w1 w2 e h s q1 q2 dM dD nD eM eD edge_src edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga a b)(*strict*)
   apply(clarsimp)
   apply(case_tac edge_srca)
   apply(clarsimp)
   apply(simp add: sel_tuple2_1_def)
   apply(case_tac edge_trg)
   apply(case_tac edge_trga)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(case_tac "edge_eventa")
    apply(clarsimp)
    apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa)(*strict*)
    apply(simp add: F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def F_DPDA_DFA_PRODUCT__edges_empty_def F_DPDA_DFA_PRODUCT__edges_execute_def)
    apply(erule disjE)+
      apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa)(*strict*)
      apply(clarsimp)
      apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa ea eb e' e'a)(*strict*)
      apply(simp add: option_to_list_def valid_dfa_def)
      apply(clarsimp)
      apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e' e'a)(*strict*)
      apply(erule_tac
      x="e'a"
      in ballE)
       apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e' e'a)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e' e'a)(*strict*)
      apply(clarsimp)
     apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa ea eb e')(*strict*)
     apply(simp add: option_to_list_def valid_dfa_def)
     apply(clarsimp)
     apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e')(*strict*)
     apply(erule_tac
      x="e'"
      in ballE)
      apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e')(*strict*)
     apply(clarsimp)
    apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa)(*strict*)
    apply(erule disjE)+
     apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa ea eb e')(*strict*)
     apply(simp add: option_to_list_def valid_dfa_def)
     apply(clarsimp)
     apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e')(*strict*)
     apply(erule_tac
      x="e'"
      in ballE)
      apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d c1 c2 n e dM dD nD eM eD wa ea eb e')(*strict*)
     apply(clarsimp)
    apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_eventa edge_popa edge_pusha aa ba bb ac bc wa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD edge_popa edge_pusha aa ba bb ac bc wa a)(*strict*)
   apply(simp add: F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def F_DPDA_DFA_PRODUCT__edges_empty_def F_DPDA_DFA_PRODUCT__edges_execute_def)
   apply(clarsimp)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
   apply(erule_tac
      x="slice_conf_B c1 [epda_box D]"
      in allE)
   apply(erule_tac
      x="slice_conf_B c2 [epda_box D]"
      in allE)
   apply(erule_tac
      x="e'"
      in allE)
   apply(erule_tac
      x="e'a"
      in allE)
   apply(erule impE)
    apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
   apply(rule_tac
      x="option_to_list (edge_event e')"
      in exI)
   apply(rule conjI)
    apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
    apply(simp add: epda_effects_def F_DPDA_DFA_PRODUCT__events_def)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
   apply(rule_tac
      x="option_to_list (edge_event e')"
      in exI)
   apply(rule conjI)
    apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
    apply(simp add: epda_effects_def F_DPDA_DFA_PRODUCT__events_def)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
   apply(clarsimp)
   apply(case_tac c1)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d c1 c2 n e h dM dD nD eM eD wa a ea eb e' e'a epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h dM dD nD eM eD wa a ea eb e' e'a)(*strict*)
   apply(simp add: slice_conf_B_def sel_tuple2_2_def)
   apply(simp add: option_to_list_def valid_dfa_def)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(clarsimp)
  apply(thin_tac "\<forall>c1 c2 e1 e2. (\<exists>w1. w1 \<in> epda_effects D \<and> (\<exists>w2. w2 \<in> epda_effects D \<and> epdaH_step_relation D \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr> e1 c1 \<and> epdaH_step_relation D \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr> e2 c2 \<and> epdaH_conf_history c1 = h @ w1 \<and> epdaH_conf_history c2 = h @ w2 \<and> (ATS_History.history_fragment_prefixes epda_effects (@) D w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) D w2 \<or> ATS_History.history_fragment_prefixes epda_effects (@) D w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) D w1 \<or> ATS_History.history_fragment_prefixes epda_effects (@) D w2 = ATS_History.history_fragment_prefixes epda_effects (@) D w1))) \<longrightarrow> e1 = e2")
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: epda_effects_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__events_def)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      x="w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: epda_effects_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__events_def)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d c1 c2 e1 e2 n e h q1 q2 dM dD nD eM eD w wa)(*strict*)
   apply(case_tac e1)
   apply(rename_tac d c1 c2 e1 e2 n e h q1 q2 dM dD nD eM eD w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 c2 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha)(*strict*)
   apply(simp add: slice_edge_A_def)
   apply(case_tac c2)
   apply(rename_tac d c1 c2 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_push)(*strict*)
   apply(case_tac c1)
   apply(rename_tac d c1 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_push epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_push epdaH_conf_statea)(*strict*)
   apply(case_tac e2)
   apply(rename_tac d e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_push epdaH_conf_statea edge_srca edge_eventaa edge_popaa edge_pusha edge_trg)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa edge_event edge_pop edge_push epdaH_conf_statea edge_eventa edge_popa edge_pusha edge_trg)(*strict*)
   apply(rename_tac x1 x2 x3 x4 x5 x6 x7 x8)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 x8)(*strict*)
   apply(simp add: sel_tuple2_1_def)
   apply(case_tac x4)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 x8 a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
   apply(simp add: slice_conf_A_def sel_tuple2_1_def)
   apply(simp add: F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def F_DPDA_DFA_PRODUCT__edges_empty_def F_DPDA_DFA_PRODUCT__edges_execute_def)
   apply(erule disjE)+
      apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
      apply(clarsimp)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a)(*strict*)
      apply(case_tac e')
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
      apply(case_tac ea)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
      apply(case_tac eb)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e')(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(case_tac eb)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 x8 ea)(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 x8 ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
   apply(erule disjE)+
      apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
      apply(clarsimp)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a)(*strict*)
      apply(case_tac ea)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
      apply(case_tac eb)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
      apply(case_tac e')
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
      apply(case_tac e'a)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb edge_srcc edge_eventc edge_popc edge_pushc edge_trgc)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a)(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(case_tac eb)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
     apply(case_tac e'a)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb edge_srcc edge_eventc edge_popc edge_pushc edge_trgc)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e')(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac eb)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(case_tac e')
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
   apply(erule disjE)+
     apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e')(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(case_tac eb)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e')(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac eb)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(case_tac e')
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x5 x6 x7 x8 a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa ea eb)(*strict*)
   apply(case_tac ea)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa ea eb edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac eb)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa ea eb edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d c1 c2 e1 e2 n e h q1 q2 dM dD nD eM eD w wa)(*strict*)
   apply(case_tac e1)
   apply(rename_tac d c1 c2 e1 e2 n e h q1 q2 dM dD nD eM eD w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 c2 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha)(*strict*)
   apply(simp add: slice_edge_A_def)
   apply(case_tac c2)
   apply(rename_tac d c1 c2 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c1 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha)(*strict*)
   apply(case_tac c1)
   apply(rename_tac d c1 e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea)(*strict*)
   apply(case_tac e2)
   apply(rename_tac d e2 n e h q1 q2 dM dD nD eM eD w wa edge_eventa edge_popa edge_pusha epdaH_conf_statea edge_srca edge_eventaa edge_popaa edge_pushaa edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa edge_event edge_pop edge_push epdaH_conf_statea edge_eventa edge_popa edge_pusha edge_trg)(*strict*)
   apply(rename_tac x1 x2 x3 x4 x5 x6 x7 x8)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 x8)(*strict*)
   apply(simp add: sel_tuple2_1_def)
   apply(case_tac x8)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 x8 a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
   apply(simp add: slice_conf_A_def sel_tuple2_1_def)
   apply(simp add: F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def F_DPDA_DFA_PRODUCT__edges_empty_def F_DPDA_DFA_PRODUCT__edges_execute_def)
   apply(erule disjE)+
      apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
      apply(clarsimp)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a)(*strict*)
      apply(case_tac e')
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
      apply(case_tac e'a)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
      apply(case_tac ea)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
      apply(case_tac eb)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb edge_srcc edge_eventc edge_popc edge_pushc edge_trgc)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e')(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(case_tac eb)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b ea)(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
    apply(erule disjE)+
     apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e')(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e' edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e' edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa edge_srcaa edge_eventaa edge_popb edge_pushb edge_trgb)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea)(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
   apply(erule disjE)+
      apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
      apply(clarsimp)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a)(*strict*)
      apply(case_tac ea)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
      apply(case_tac eb)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
      apply(case_tac e')
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
      apply(case_tac e'a)
      apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb edge_srcc edge_eventc edge_popc edge_pushc edge_trgc)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a)(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(case_tac eb)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
     apply(case_tac e'a)
     apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' e'a edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb edge_srcc edge_eventc edge_popc edge_pushc edge_trgc)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e')(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac eb)
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(case_tac e')
    apply(rename_tac d n e h dM dD nD eM eD w wa ea eb e' edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa edge_srcb edge_eventb edge_popb edge_pushb edge_trgb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e h q1 q2 dM dD nD eM eD w wa x1 x2 x3 x4 x5 x6 x7 a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b ea)(*strict*)
   apply(case_tac ea)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b ea edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
   apply(erule disjE)+
     apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e')(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e' edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(case_tac e')
     apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e' edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa edge_srcaa edge_eventaa edge_popb edge_pushb edge_trgb)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e')(*strict*)
    apply(case_tac ea)
    apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e' edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(case_tac e')
    apply(rename_tac d n e h dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea e' edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa edge_srcaa edge_eventaa edge_popb edge_pushb edge_trgb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa x5 x6 x7 a b edge_srca edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea)(*strict*)
   apply(case_tac ea)
   apply(rename_tac d n e h q2 dM dD nD eM eD w wa edge_popa edge_pusha edge_trga ea edge_srca edge_eventa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: slice_conf_A_def)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(simp add: slice_conf_A_def)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes epda_effects (@) M w2 = ATS_History.history_fragment_prefixes epda_effects (@) M w1"
      and s="ATS_History.history_fragment_prefixes epda_effects (@) M w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) M w2 \<and> ATS_History.history_fragment_prefixes epda_effects (@) M w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) M w1"
      in ssubst)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(force)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule disjE)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule disjI1)
   apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1"
      in subset_trans)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2")
    apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
    apply(simp add: epda_effects_def)
    apply(clarsimp)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2"
      in subset_trans)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(force)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2")
   apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
   apply(simp add: epda_effects_def)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(erule disjE)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2"
      in subset_trans)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1")
    apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
    apply(simp add: epda_effects_def)
    apply(clarsimp)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1"
      in subset_trans)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(force)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2 \<subseteq> ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1")
   apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
   apply(simp add: epda_effects_def)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(rule conjI)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1"
      in subset_trans)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1")
    apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
    apply(simp add: epda_effects_def)
    apply(clarsimp)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2"
      in subset_trans)
    apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
    apply(force)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1")
   apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
   apply(simp add: epda_effects_def)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2"
      in subset_trans)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1")
   apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
   apply(simp add: epda_effects_def)
   apply(clarsimp)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(rule_tac
      B="ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1"
      in subset_trans)
   apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
   apply(force)
  apply(rename_tac d c1 c2 e1 e2 n w1 w2 e h s q1 q2 dM dD nD eM eD)(*strict*)
  apply(thin_tac "ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w2 = ATS_History.history_fragment_prefixes epda_effects (@) (F_DPDA_DFA_PRODUCT M D) w1")
  apply(simp add: F_DPDA_DFA_PRODUCT_def epdaHS.history_fragment_prefixes_def F_DPDA_DFA_PRODUCT__events_def)
  apply(simp add: epda_effects_def)
  apply(clarsimp)
  done

theorem F_DPDA_DFA_PRODUCT__generates__DPDA: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_dpda R"
  apply(simp (no_asm) add: valid_dpda_def)
  apply(rule context_conjI)
   apply(rule_tac
      M="M"
      and D="D"
      in F_DPDA_DFA_PRODUCT__produces__PDA)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_DPDA_DFA_PRODUCT__preserves__determinism)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem F_DPDA_DFA_PRODUCT__preserves__no_epdaH_livelock: "
  valid_dpda M
  \<Longrightarrow> \<not> epdaH_livelock M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> \<not> epdaH_livelock R"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      M="M"
      and D="D"
      in F_DPDA_DFA_PRODUCT__produces__PDA)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d N)(*strict*)
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__reflects__derivation_initial2)
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
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="(\<lambda>n. case d n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (slice_edge_A e)) (slice_conf_A c)))"
      in allE)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac d N)(*strict*)
   apply(clarsimp)
   apply(rename_tac d N n)(*strict*)
   apply(case_tac "d n")
    apply(rename_tac d N n)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="n"
      in allE)
    apply(force)
   apply(rename_tac d N n a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d N n a option b)(*strict*)
   apply(force)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="N"
      and P="\<lambda>N. \<exists>n\<ge>N. epdaH_conf_history (the (get_configuration (case_option None (case_derivation_configuration (\<lambda>e c. Some (pair (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (slice_edge_A e)) (slice_conf_A c)))) (d n)))) \<noteq> epdaH_conf_history (the (get_configuration (case_option None (case_derivation_configuration (\<lambda>e c. Some (pair (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (slice_edge_A e)) (slice_conf_A c)))) (d N))))"
      in allE)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n)(*strict*)
  apply(erule_tac x="N" in allE')
  apply(erule_tac x="n" in allE')
  apply(erule exE)+
  apply(rename_tac d N n y ya)(*strict*)
  apply(case_tac y)
  apply(rename_tac d N n y ya option b)(*strict*)
  apply(case_tac ya)
  apply(rename_tac d N n y ya option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n option b optiona ba)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(simp add: slice_conf_A_def)
  done

definition FUN_DPDA_DFA_PRODUCT__SpecInput1 :: "
  ('statesA, 'event, 'stackA) epda
  \<Rightarrow> ('statesB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "FUN_DPDA_DFA_PRODUCT__SpecInput1 G D \<equiv>
  valid_dpda G
  \<and> valid_dfa D"

definition epdaH_reflection_to_DFA_exists :: "
  ('statesA, 'event, 'stackA) epda
  \<Rightarrow> ('statesB, 'event, 'stackB) epda
  \<Rightarrow> ('statesA \<Rightarrow> 'statesB)
  \<Rightarrow> bool"
  where
    "epdaH_reflection_to_DFA_exists R D F \<equiv>
  \<forall>d n c.
    epdaH.derivation_initial R d
    \<longrightarrow> get_configuration (d n) = Some c
    \<longrightarrow>
      (\<exists>d' m.
          epdaH.derivation_initial D d'
          \<and> get_configuration (d' m) = Some
              \<lparr>epdaH_conf_state = F (epdaH_conf_state c),
              epdaH_conf_history = epdaH_conf_history c,
              epdaH_conf_stack = [epda_box D]\<rparr>)"

definition FUN_DPDA_DFA_PRODUCT__SpecOutput1 :: "
  ('statesA, 'event, 'stackA) epda
  \<Rightarrow> ('statesB, 'event, 'stackB) epda
  \<Rightarrow> (('statesA, 'statesB) DT_tuple2, 'event, 'stackA) epda
  \<Rightarrow> bool"
  where
    "FUN_DPDA_DFA_PRODUCT__SpecOutput1 Gi D Go \<equiv>
  valid_dpda Go
  \<and> epdaH.marked_language Go = (epdaH.marked_language Gi) \<inter> (epdaH.marked_language D)
  \<and> epdaH.unmarked_language Go = (epdaH.unmarked_language Gi) \<inter> (epdaH.unmarked_language D)
  \<and> epdaH_reflection_to_DFA_exists Go D sel_tuple2_2"

theorem F_DPDA_DFA_PRODUCT__SOUND1: "
  FUN_DPDA_DFA_PRODUCT__SpecInput1 Gi D
  \<Longrightarrow> FUN_DPDA_DFA_PRODUCT__SpecOutput1 Gi D (F_DPDA_DFA_PRODUCT Gi D)"
  apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def FUN_DPDA_DFA_PRODUCT__SpecInput1_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__generates__DPDA)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__relates__marked_language)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__relates__unmarked_language)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaH_reflection_to_DFA_exists_def)
  apply(clarsimp)
  apply(rename_tac d n c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac d n c)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c option)(*strict*)
  apply(case_tac c)
  apply(rename_tac d n c option epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
  apply(rename_tac e q h s)
  apply(rename_tac d n c e q h s)(*strict*)
  apply(case_tac q)
  apply(rename_tac d n c e q h s a b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n c e q h s a b)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      and M="Gi"
      and D="D"
      in F_DPDA_DFA_PRODUCT__reflects__derivation_initial)
        apply(rename_tac d n c e q h s a b)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac d n c e q h s a b)(*strict*)
       apply(force)
      apply(rename_tac d n c e q h s a b)(*strict*)
      apply(force)
     apply(rename_tac d n c e q h s a b)(*strict*)
     apply(simp add: valid_dpda_def)
    apply(rename_tac d n c e q h s a b)(*strict*)
    apply(force)
   apply(rename_tac d n c e q h s a b)(*strict*)
   apply(force)
  apply(rename_tac d n c e q h s a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e h s a b dM dD nD eM eD)(*strict*)
  apply(rule_tac
      x="dD"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="nD"
      in exI)
  apply(clarsimp)
  done

lemma F_DPDA_DFA_PRODUCT__preserves__nonblockingness_language: "
  valid_dpda G
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT G D
  \<Longrightarrow> epdaH.marked_language G \<subseteq> epdaH.marked_language D
  \<Longrightarrow> epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language D
  \<Longrightarrow> nonblockingness_language (epdaH.unmarked_language R) (epdaH.marked_language R)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__SOUND1)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput1_def)
  apply(clarsimp)
  apply(rule_tac
      t="epdaH.unmarked_language (F_DPDA_DFA_PRODUCT G D)"
      and s="epdaH.unmarked_language G \<inter> epdaH.unmarked_language D"
      in ssubst)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(rule_tac
      t="epdaH.marked_language (F_DPDA_DFA_PRODUCT G D)"
      and s="epdaH.marked_language G \<inter> epdaH.marked_language D"
      in ssubst)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(rule_tac
      t="epdaH.unmarked_language G \<inter> epdaH.unmarked_language D"
      and s="epdaH.unmarked_language G"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="epdaH.marked_language G \<inter> epdaH.marked_language D"
      and s="epdaH.marked_language G"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DFA_PRODUCT__preserves__controllable_sublanguage: "
  valid_dpda G 
  \<Longrightarrow> valid_dfa D 
  \<Longrightarrow> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G) 
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT G D 
  \<Longrightarrow> epdaH.marked_language G \<subseteq> epdaH.marked_language D 
  \<Longrightarrow> epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language D 
  \<Longrightarrow> (controllable_sublanguage (epdaH.unmarked_language G) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language D) (epdaH.unmarked_language G) \<longleftrightarrow> controllable_sublanguage (epdaH.unmarked_language R) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language D) (epdaH.unmarked_language R))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__SOUND1)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput1_def)
  apply(clarsimp)
  apply(rule_tac
      t="epdaH.unmarked_language (F_DPDA_DFA_PRODUCT G D)"
      and s="epdaH.unmarked_language G \<inter> epdaH.unmarked_language D"
      in ssubst)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(rule_tac
      t="epdaH.marked_language (F_DPDA_DFA_PRODUCT G D)"
      and s="epdaH.marked_language G \<inter> epdaH.marked_language D"
      in ssubst)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(rule_tac
      t="epdaH.unmarked_language G \<inter> epdaH.unmarked_language D"
      and s="epdaH.unmarked_language G"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="epdaH.marked_language G \<inter> epdaH.marked_language D"
      and s="epdaH.marked_language G"
      in ssubst)
   apply(force)
  apply(force)
  done

definition FUN_DPDA_DFA_PRODUCT__SpecInput2 :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "FUN_DPDA_DFA_PRODUCT__SpecInput2 G D \<equiv>
  valid_dpda G
  \<and> valid_dfa D
  \<and> nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G)
  \<and> epdaH.marked_language G \<subseteq> epdaH.marked_language D
  \<and> epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language D
  \<and> \<not> epdaH_livelock G"

definition FUN_DPDA_DFA_PRODUCT__SpecOutput2 :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> (('stateB, 'event, 'stackB) epda \<times> 'event set)
  \<Rightarrow> (('stateA, 'stateB) DT_tuple2, 'event, 'stackA) epda
  \<Rightarrow> bool"
  where
    "FUN_DPDA_DFA_PRODUCT__SpecOutput2 Gi X Go \<equiv>
  case X of (P,
  \<Sigma>UC)
  \<Rightarrow> valid_dpda Go
  \<and> epdaH.marked_language Go = (epdaH.marked_language Gi) \<inter> (epdaH.marked_language P)
  \<and> epdaH.unmarked_language Go = (epdaH.unmarked_language Gi) \<inter> (epdaH.unmarked_language P)
  \<and> nonblockingness_language (epdaH.unmarked_language Go) (epdaH.marked_language Go)
  \<and> epdaH_reflection_to_DFA_exists Go P sel_tuple2_2
  \<and> \<not> epdaH_livelock Go
  \<and> (controllable_language 
    (epdaH.unmarked_language Gi) 
    \<Sigma>UC 
    (epdaH.unmarked_language P)
  \<longleftrightarrow> controllable_language 
        (epdaH.unmarked_language Go)
        \<Sigma>UC
        (epdaH.unmarked_language P))"

theorem F_DPDA_DFA_PRODUCT__SOUND2: "
  FUN_DPDA_DFA_PRODUCT__SpecInput2 Gi P
  \<Longrightarrow> FUN_DPDA_DFA_PRODUCT__SpecOutput2 Gi (P, \<Sigma>UC) (F_DPDA_DFA_PRODUCT Gi P)"
  apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput2_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__generates__DPDA)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__relates__marked_language)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__relates__unmarked_language)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_DPDA_DFA_PRODUCT__preserves__nonblockingness_language)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(simp add: epdaH_reflection_to_DFA_exists_def)
   apply(clarsimp)
   apply(rename_tac d n c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d n")
    apply(rename_tac d n c)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d n c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n c option)(*strict*)
   apply(case_tac c)
   apply(rename_tac d n c option epdaH_conf_statea epdaH_conf_historya epdaH_conf_stack)(*strict*)
   apply(rename_tac e q h s)
   apply(rename_tac d n c e q h s)(*strict*)
   apply(case_tac q)
   apply(rename_tac d n c e q h s a b)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d n c e q h s a b)(*strict*)
    prefer 2
    apply(rule_tac
      n="n"
      and M="Gi"
      and D="P"
      in F_DPDA_DFA_PRODUCT__reflects__derivation_initial)
         apply(rename_tac d n c e q h s a b)(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac d n c e q h s a b)(*strict*)
        apply(force)
       apply(rename_tac d n c e q h s a b)(*strict*)
       apply(force)
      apply(rename_tac d n c e q h s a b)(*strict*)
      apply(simp add: valid_dpda_def)
     apply(rename_tac d n c e q h s a b)(*strict*)
     apply(force)
    apply(rename_tac d n c e q h s a b)(*strict*)
    apply(force)
   apply(rename_tac d n c e q h s a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e h s a b dM dD nD eM eD)(*strict*)
   apply(rule_tac
      x="dD"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="nD"
      in exI)
   apply(clarsimp)
  apply(rule conjI)
   apply(rule F_DPDA_DFA_PRODUCT__preserves__no_epdaH_livelock)
      prefer 4
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="epdaH.unmarked_language (F_DPDA_DFA_PRODUCT Gi P)"
      and s="epdaH.unmarked_language Gi"
      in ssubst)
   apply(force)
  apply(force)
  done

theorem F_DPDA_DFA_PRODUCT__SOUND3: "
  valid_dpda G 
  \<Longrightarrow> valid_dfa D 
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT G D 
  \<Longrightarrow> valid_dpda R \<and> epdaH.marked_language R = epdaH.marked_language G \<inter> epdaH.marked_language D \<and> epdaH.unmarked_language R = epdaH.unmarked_language G \<inter> epdaH.unmarked_language D \<and> epdaH_reflection_to_DFA_exists R D sel_tuple2_2 \<and> (\<not> epdaH_livelock G \<longrightarrow> \<not> epdaH_livelock R) \<and> (epdaH.marked_language G \<subseteq> epdaH.marked_language D \<longrightarrow> epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language D \<longrightarrow> ((nonblockingness_language (epdaH.unmarked_language G) (epdaH.marked_language G) \<longrightarrow> nonblockingness_language (epdaH.unmarked_language R) (epdaH.marked_language R)) \<and> (controllable_language (epdaH.unmarked_language G) \<Sigma>UC (epdaH.unmarked_language D) \<longleftrightarrow> controllable_language (epdaH.unmarked_language R) \<Sigma>UC (epdaH.unmarked_language D))))"
  apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput2_def FUN_DPDA_DFA_PRODUCT__SpecOutput2_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__SOUND1)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput1_def)
  apply(clarsimp)
  apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule impI)
   apply(rule F_DPDA_DFA_PRODUCT__preserves__no_epdaH_livelock)
      prefer 4
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule impI)
  apply(rule impI)
  apply(rule_tac
      t="epdaH.unmarked_language G \<inter> epdaH.unmarked_language D"
      and s="epdaH.unmarked_language G"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="epdaH.marked_language G \<inter> epdaH.marked_language D"
      and s="epdaH.marked_language G"
      in ssubst)
   apply(force)
  apply(force)
  done

definition strip_plant :: "
  (('controller_state, 'plant_state) DT_tuple2, 'event, 'controller_stack) epda_step_label option
  \<Rightarrow> ('controller_state, 'event, 'controller_stack) epda_step_label option"
  where 
    "strip_plant e \<equiv> 
  (case e of None \<Rightarrow> None | Some e \<Rightarrow> 
  Some \<lparr>edge_src = sel_tuple2_1 (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = sel_tuple2_1 (edge_trg e)\<rparr>)"

lemma F_DPDA_DFA_PRODUCT__preserves__derivation_initial_strengthend: "
  valid_dpda M
  \<Longrightarrow> valid_dfa D
  \<Longrightarrow> R = F_DPDA_DFA_PRODUCT M D
  \<Longrightarrow> valid_pda R
  \<Longrightarrow> epdaH.derivation_initial D dD
  \<Longrightarrow> epdaH.derivation_initial M dM
  \<Longrightarrow> length h + ints = n
  \<Longrightarrow> dM n = Some (pair eM \<lparr>epdaH_conf_state = q1, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>)
  \<Longrightarrow> dD (length h) = Some (pair eD \<lparr>epdaH_conf_state = q2, epdaH_conf_history = h, epdaH_conf_stack = [epda_box D]\<rparr>)
  \<Longrightarrow> \<exists>dR eR. epdaH.derivation_initial R dR 
      \<and> dR n = Some (pair eR \<lparr>epdaH_conf_state = cons_tuple2 q1 q2, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>)
      \<and> get_labels dM n = map strip_plant (get_labels dR n)"
  apply(induct n arbitrary: h q1 q2 s eM eD ints)
   apply(rename_tac h q1 q2 s eM eD ints)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 q2 s eM eD)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>epdaH_conf_state = cons_tuple2 q1 q2, epdaH_conf_history = [], epdaH_conf_stack = s\<rparr>"
      in exI)
   apply(rename_tac q1 q2 s eM eD)(*strict*)
   apply(rule conjI)
    apply(rename_tac q1 q2 s eM eD)(*strict*)
    apply(rule epdaH.derivation_initialI)
     apply(rename_tac q1 q2 s eM eD)(*strict*)
     apply(rule epdaH.der1_is_derivation)
    apply(rename_tac q1 q2 s eM eD)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 q2 s eM eD c)(*strict*)
    apply(simp add: get_configuration_def der1_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 s eM eD)(*strict*)
    apply(simp add: epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac q1 q2 s)(*strict*)
    apply(simp add: epdaH_initial_configurations_def epdaH_configurations_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__states_def)
    apply(clarsimp)
   apply(rename_tac q1 q2 s eM eD)(*strict*)
   apply(rule conjI)
    apply(rule_tac
      x="None"
      in exI)
    apply(simp add: der1_def)
   apply(simp add: get_labels_def)
   apply (metis (full_types) Suc_n_not_le_n le_0_eq nat_seq_in_interval) 
  apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
   prefer 2
   apply(rule_tac
      G="M"
      and d="dM"
      and n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
    apply(force)
   apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
   apply(force)
  apply(rename_tac n h q1 q2 s eM eD ints)(*strict*)
  apply(clarsimp)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac qx hx sx)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 qx hx sx)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n h q1 q2 s eD ints e1 e2 qx hx sx edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(clarsimp)
  apply(rename_tac n h q1 q2 s eD ints e1 qx hx sx edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac qs read pop push qt)
  apply(rename_tac n h q1 q2 s eD ints e1 qx hx sx qs read pop push qt)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n q2 eD ints e1 hx qs read pop push qt w)(*strict*)
  apply(erule_tac
      x="hx"
      in meta_allE)
  apply(erule_tac
      x="qs"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac read)
   apply(rename_tac n q2 eD ints e1 hx qs read pop push qt w)(*strict*)
   apply(clarsimp)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w)(*strict*)
   apply(simp add: option_to_list_def)
   apply(erule_tac
      x="q2"
      in meta_allE)
   apply(erule_tac
      x="pop@w"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="e1"
      in meta_allE)
   apply(erule_tac
      x="eD"
      in meta_allE)
   apply(clarsimp)
   apply(case_tac ints)
    apply(rename_tac n q2 eD ints e1 hx qs pop push qt w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
     prefer 2
     apply(rule_tac
      G="M"
      and d="dM"
      and n="n"
      in epda_at_most_one_symbol_per_step)
       apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
      apply(force)
     apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
     apply(force)
    apply(rename_tac n q2 eD e1 hx qs pop push qt w)(*strict*)
    apply(clarsimp)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac q2 eD e1 hx qs pop push qt w nat)(*strict*)
   apply(erule_tac
      x="nat"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac q2 eD e1 hx qs pop push qt w nat dR eR)(*strict*)
   apply(rename_tac ints dR eR)
   apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
   apply(subgoal_tac "\<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr> \<in> epdaH_configurations (F_DPDA_DFA_PRODUCT M D)")
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule_tac
      x="derivation_append dR (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr> \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt q2\<rparr> \<lparr>epdaH_conf_state = cons_tuple2 qt q2, epdaH_conf_history = hx, epdaH_conf_stack = push @ w\<rparr>) (length hx + ints)"
      in exI)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule conjI)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation_initial)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
      apply(force)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(rule epdaH.derivation_append_preserves_derivation)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(rule epdaH.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
      apply(rule epdaH.der2_is_derivation)
      apply(simp add: epdaH_step_relation_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def)
      apply(rule conjI)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(rule disjI2)
       apply(simp add: F_DPDA_DFA_PRODUCT__edges_empty_def)
       apply(rule_tac
      x="\<lparr>edge_src = qs, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr>"
      in exI)
       apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
       apply(clarsimp)
       apply(simp add: epdaH_configurations_def F_DPDA_DFA_PRODUCT__states_def)
      apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule conjI)
     apply(rule_tac
      x="Some \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt q2\<rparr>"
      in exI)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rule_tac t="get_labels dM (Suc (length hx + ints))" and s="get_labels dM (length hx + ints) @ [Some \<lparr>edge_src = qs, edge_event = None, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr>]" in ssubst)
     apply(rule get_labels__seperate_last)   
     apply(force)
    apply(rule_tac t="get_labels
          (derivation_append dR
            (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr>
              \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt q2\<rparr>
              \<lparr>epdaH_conf_state = cons_tuple2 qt q2, epdaH_conf_history = hx, epdaH_conf_stack = push @ w\<rparr>)
            (length hx + ints))
          (Suc (length hx + ints))" and s="get_labels
          (derivation_append dR
            (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr>
              \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt q2\<rparr>
              \<lparr>epdaH_conf_state = cons_tuple2 qt q2, epdaH_conf_history = hx, epdaH_conf_stack = push @ w\<rparr>)
            (length hx + ints))
          ((length hx + ints)) @[Some \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push,
              edge_trg = cons_tuple2 qt q2\<rparr>]" in ssubst)
     apply(rule_tac c="\<lparr>epdaH_conf_state = cons_tuple2 qt q2, epdaH_conf_history = hx, epdaH_conf_stack = push @ w\<rparr>"  in get_labels__seperate_last)  
     apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
    apply(rule conjI)
     prefer 2
     apply(simp add: strip_plant_def)
    apply(rule_tac t="(get_labels
          (derivation_append dR
            (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs q2, epdaH_conf_history = hx, epdaH_conf_stack = pop @ w\<rparr>
              \<lparr>edge_src = cons_tuple2 qs q2, edge_event = None, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt q2\<rparr>
              \<lparr>epdaH_conf_state = cons_tuple2 qt q2, epdaH_conf_history = hx, epdaH_conf_stack = push @ w\<rparr>)
            (length hx + ints))
          (length hx + ints))" in ssubst)
     apply(rule get_labels__derivation_append__trivial)   
    apply(force)
   apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
     apply(simp add: valid_pda_def)
    apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
    apply(force)
   apply(rename_tac q2 eD e1 hx qs pop push qt w ints dR eR)(*strict*)
   apply(force)
  apply(rename_tac n q2 eD ints e1 hx qs read pop push qt w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
   prefer 2
   apply(rule_tac
      G="D"
      and d="dD"
      and n="length hx"
      and m="Suc (length hx)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
    apply(force)
   apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
   apply(force)
  apply(rename_tac n q2 eD ints e1 hx qs pop push qt w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 c1 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q2' h' s')
  apply(rename_tac q2 ints e1 hx qs pop push qt w a e1a e2 q2' h' s')(*strict*)
  apply(erule_tac
      x="q2'"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="pop@w"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="ints"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
  apply(subgoal_tac "(\<forall>e\<in> epda_delta D. edge_event e \<noteq> None \<and> edge_pop e = [epda_box D] \<and> edge_push e = [epda_box D])")
   apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
   prefer 2
   apply(unfold valid_dfa_def)[1]
   apply(erule conjE)+
   apply(force)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa)(*strict*)
  apply(clarify)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa y)(*strict*)
  apply(case_tac e2)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a e2 h' wa y edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarify)
  apply(simp)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a h' wa y edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(simp add: option_to_list_def)
  apply(clarify)
  apply(rename_tac ints e1 hx qs pop push qt w a e1a h' wa y edge_src edge_event edge_pop edge_push edge_trg dR eR)(*strict*)
  apply(simp)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y edge_src edge_trg dR eR)(*strict*)
  apply(rename_tac qxs qxt dR eR)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(rule_tac
      x="derivation_append dR (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs qxs, epdaH_conf_history = h', epdaH_conf_stack = pop @ w\<rparr> \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt qxt\<rparr> \<lparr>epdaH_conf_state = cons_tuple2 qt qxt, epdaH_conf_history = h' @ [y], epdaH_conf_stack = push @ w\<rparr>) (length h' + ints)"
      in exI)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(rule conjI)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation_initial)
     apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(force)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(rule epdaH.derivation_append_preserves_derivation)
     apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(rule epdaH.der2_is_derivation)
    apply(simp add: epdaH_step_relation_def F_DPDA_DFA_PRODUCT_def F_DPDA_DFA_PRODUCT__edges_def)
    apply(simp add: option_to_list_def)
    apply(rule disjI1)
    apply(simp add: F_DPDA_DFA_PRODUCT__edges_execute_def)
    apply(rule_tac
      x="\<lparr>edge_src = qs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr>"
      in exI)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="\<lparr>edge_src = qxs, edge_event = Some y, edge_pop = [epda_box D], edge_push = [epda_box D], edge_trg = qxt\<rparr>"
      in exI)
    apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
    apply(clarsimp)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
  apply(rule conjI)
   apply(rule_tac
      x="Some \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = cons_tuple2 qt qxt\<rparr>"
      in exI)
   apply(rename_tac ints e1 qs pop push qt w e1a h' y qxs qxt dR eR)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rule_tac t="get_labels dM (Suc (length h' + ints))" 
      and s="get_labels dM (length h' + ints) @ [Some \<lparr>edge_src = qs, edge_event = Some y, edge_pop = pop, edge_push = push, edge_trg = qt\<rparr>]" in ssubst)
   apply(rule get_labels__seperate_last)   
   apply(force)
  apply(rule_tac t="(get_labels
          (derivation_append dR
            (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs qxs, epdaH_conf_history = h', epdaH_conf_stack = pop @ w\<rparr>
              \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt qxt\<rparr>
              \<lparr>epdaH_conf_state = cons_tuple2 qt qxt, epdaH_conf_history = h' @ [y],
                 epdaH_conf_stack = push @ w\<rparr>)
            (length h' + ints))
          (Suc (length h' + ints)))" and s="(get_labels
          (derivation_append dR
            (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs qxs, epdaH_conf_history = h', epdaH_conf_stack = pop @ w\<rparr>
              \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt qxt\<rparr>
              \<lparr>epdaH_conf_state = cons_tuple2 qt qxt, epdaH_conf_history = h' @ [y],
                 epdaH_conf_stack = push @ w\<rparr>)
            (length h' + ints))
          ( (length h' + ints))) @[Some \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt qxt\<rparr>]" in ssubst)
   apply(rule_tac c="\<lparr>epdaH_conf_state = cons_tuple2 qt qxt, epdaH_conf_history = h' @ [y],
               epdaH_conf_stack = push @ w\<rparr>"  in get_labels__seperate_last)  
   apply(simp add: derivation_append_def der2_def)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(simp add: strip_plant_def)
  apply(rule_tac t="(get_labels
          (derivation_append dR
            (der2 \<lparr>epdaH_conf_state = cons_tuple2 qs qxs, epdaH_conf_history = h', epdaH_conf_stack = pop @ w\<rparr>
              \<lparr>edge_src = cons_tuple2 qs qxs, edge_event = Some y, edge_pop = pop, edge_push = push,
                 edge_trg = cons_tuple2 qt qxt\<rparr>
              \<lparr>epdaH_conf_state = cons_tuple2 qt qxt, epdaH_conf_history = h' @ [y],
                 epdaH_conf_stack = push @ w\<rparr>)
            (length h' + ints))
          (length h' + ints))" in ssubst)
   apply(rule get_labels__derivation_append__trivial)   
  apply(force)
  done

lemma F_DPDA_DFA_PRODUCT__epda_to_des: "
  valid_dfa P
  \<Longrightarrow> valid_dpda G
  \<Longrightarrow> inf (epda_to_des G) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT G P)"
  apply(simp add: epda_to_des_def inf_DES_ext_def infDES_def)
  apply (metis FUN_DPDA_DFA_PRODUCT__SpecInput1_def FUN_DPDA_DFA_PRODUCT__SpecOutput1_def F_DPDA_DFA_PRODUCT__SOUND1)
  done

lemma no_epdaH_livelock_implies_F_DPDA_DFA_PRODUCT__epdaH_livelock_freedom: "
  valid_dfa P
  \<Longrightarrow> valid_dpda SOL 
  \<Longrightarrow> \<not> epdaH_livelock SOL
  \<Longrightarrow> epdaH_livelock_freedom (F_DPDA_DFA_PRODUCT SOL P)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__preserves__no_epdaH_livelock)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaH_livelock_freedom_def)
  apply(thin_tac "\<not> epdaH_livelock SOL")
  apply (metis F_DPDA_DFA_PRODUCT__generates__DPDA valid_pda_to_valid_epda epdaH_has_livelock_implies_livelock valid_dpda_to_valid_pda)
  done

lemma F_DPDA_DFA_PRODUCT__Nonblockingness_branching: "
  valid_dpda S \<Longrightarrow>
    valid_dfa P \<Longrightarrow>
    DES_nonblockingness (epda_to_des SOL) \<Longrightarrow>
    DES_controllability \<Sigma>UC (epda_to_des P)
     (epda_to_des SOL) \<Longrightarrow>
    valid_dpda SOL \<Longrightarrow>
    inf (epda_to_des SOL) (epda_to_des P) =
    epda_to_des (F_DPDA_DFA_PRODUCT SOL P) \<Longrightarrow>
    epda_to_des (F_DPDA_DFA_PRODUCT SOL P)
    \<in> SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P)
        (inf (epda_to_des P) (epda_to_des S)) \<Sigma>UC \<Longrightarrow>
    ATS_Language0.Nonblockingness_branching epdaH_configurations
     epdaH_initial_configurations epda_step_labels
     epdaH_step_relation epdaH_marking_condition
     (F_DPDA_DFA_PRODUCT SOL P)"
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(clarsimp)
  apply(thin_tac "DES_specification_satisfied
     (inf (epda_to_des P) (epda_to_des S))
     (epda_to_des (F_DPDA_DFA_PRODUCT SOL P))")
  apply(thin_tac "DES_controllability \<Sigma>UC (epda_to_des P)
     (epda_to_des (F_DPDA_DFA_PRODUCT SOL P))")
  apply(thin_tac "DES_controllability \<Sigma>UC (epda_to_des P)
     (epda_to_des SOL)")
  apply(thin_tac "epda_to_des (F_DPDA_DFA_PRODUCT SOL P)
    \<le> epda_to_des P")
  apply(thin_tac "DES_nonblockingness (epda_to_des SOL)")
  apply(thin_tac "valid_dpda S")
  apply(subgoal_tac "valid_dpda (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__generates__DPDA)
  apply(thin_tac "inf (epda_to_des SOL) (epda_to_des P) =
    epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
  apply(thin_tac "IsDES (epda_to_des (F_DPDA_DFA_PRODUCT SOL P))")
  apply(simp add: DES_nonblockingness_def des_langUM_def des_langM_def epda_to_des_def)
  apply(thin_tac "valid_dfa P")
  apply(thin_tac "valid_dpda SOL")
  apply(metis epdaH_operational_Nonblockingness_from_language_Nonblockingness epda_inter_semantic_relationship valid_dpda_def valid_pda_def)
  done

lemma epdaHNonblockingness_branching__to__epdaH_deadlock_freedom: "
    valid_dfa P \<Longrightarrow>
    valid_dpda SOL \<Longrightarrow>
    ATS_Language0.Nonblockingness_branching epdaH_configurations
     epdaH_initial_configurations epda_step_labels
     epdaH_step_relation epdaH_marking_condition
     (F_DPDA_DFA_PRODUCT SOL P) \<Longrightarrow>
    epdaH_deadlock_freedom (F_DPDA_DFA_PRODUCT SOL P)"
  apply(subgoal_tac "valid_dpda (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply (metis F_DPDA_DFA_PRODUCT__generates__DPDA)
  apply(thin_tac "valid_dfa P")
  apply(thin_tac "valid_dpda SOL")
  apply(simp add: epdaH_deadlock_freedom_def epdaH.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(erule_tac x="n" in allE)
  apply(clarsimp)
  apply(case_tac x)
   apply(clarsimp)
   apply(simp add: epdaH_marking_condition_def)
   apply(clarsimp)
   apply(subgoal_tac "i\<le>n")
    prefer 2
    apply(rule_tac M="(F_DPDA_DFA_PRODUCT SOL P)" and d="derivation_append d dc n" in epdaH.allPreMaxDomSome_prime)
      apply (metis (full_types) epdaH.derivation_append_from_derivation_append_fit epdaH.derivation_initial_is_derivation valid_dpda_def valid_pda_def)
     apply(force)
    apply (metis concat_has_max_dom monoid_add_class.add.right_neutral)
   apply(case_tac "i=n")
    apply(clarsimp)
    apply(erule_tac x="n" and P="%i. \<forall>e c. c \<in> epdaH_marking_configurations (F_DPDA_DFA_PRODUCT SOL P) \<longrightarrow>
               d i = Some (pair e c) \<longrightarrow>
               (\<exists>j>i. \<exists>e' c'. d j = Some (pair e' c') \<and> epdaH_string_state c \<noteq> epdaH_string_state c')" in allE)
    apply(clarsimp)
    apply(case_tac "c \<in> epdaH_marking_configurations (F_DPDA_DFA_PRODUCT SOL P)")
     apply(clarsimp)
     apply (metis epdaH.derivation_initial_is_derivation epdaH.noSomeAfterMaxDom not_None_eq)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(subgoal_tac "i<n")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "d i = Some (pair ea ca)")
    prefer 2
    apply(simp add: derivation_append_def)
   apply(erule_tac x="i" and P="%i. \<forall> e c. c \<in> epdaH_marking_configurations (F_DPDA_DFA_PRODUCT SOL P) \<longrightarrow>
               d i = Some (pair e c) \<longrightarrow>
               (\<exists>j>i. \<exists>e' c'. d j = Some (pair e' c') \<and> epdaH_string_state c \<noteq> epdaH_string_state c')" in allE)
   apply(clarsimp)
   apply(subgoal_tac "j\<le>n")
    prefer 2
    apply (metis (poly_guards_query) epdaH.derivation_initial_is_derivation epdaH.noSomeAfterMaxDom le_neq_implies_less nat_le_linear option.distinct(2))
   apply(clarsimp)
   apply(erule_tac x="j" in allE)
   apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac nc)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="F_DPDA_DFA_PRODUCT SOL P" and n="n" and m="n+Suc nc" and d="derivation_append d dc n" in epdaH.step_detail_before_some_position)
     apply(simp add: epdaH.derivation_initial_def)
     apply (metis epdaH.derivation_append_from_derivation_append_fit valid_dpda_def valid_pda_def) 
    apply(simp add: derivation_append_def maximum_of_domain_def)
   apply(force)
  apply(clarsimp)
  apply(simp add: derivation_append_def maximum_of_domain_def)
  apply(clarsimp)
  apply(rule_tac x="e2" in exI)
  apply(rule_tac x="c2" in exI)
  apply(clarsimp)
  done

end
