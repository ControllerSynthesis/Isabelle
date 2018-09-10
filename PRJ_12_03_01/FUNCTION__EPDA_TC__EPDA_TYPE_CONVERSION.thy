section {*FUNCTION\_\_EPDA\_TC\_\_EPDA\_TYPE\_CONVERSION*}
theory
  FUNCTION__EPDA_TC__EPDA_TYPE_CONVERSION

imports
  PRJ_12_03_01__ENTRY

begin

definition F_EPDA_TC__edge1__RL :: "
  ('stateB DT_symbol \<Rightarrow> 'stateA)
  \<Rightarrow> ('stackB DT_symbol \<Rightarrow> 'stackA)
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label"
  where
    "F_EPDA_TC__edge1__RL fq fg e \<equiv>
  \<lparr>edge_src = fq (edge_src e),
  edge_event = edge_event e,
  edge_pop = map fg (edge_pop e),
  edge_push = map fg (edge_push e),
  edge_trg = fq (edge_trg e)\<rparr>"

definition F_EPDA_TC__edge__RL :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label"
  where
    "F_EPDA_TC__edge__RL G e \<equiv>
  F_EPDA_TC__edge1__RL
    (inv_into (epda_states G) (SOME f. inj_on f (epda_states G)))
    (inv_into (epda_gamma G) (SOME f. inj_on f (epda_gamma G)))
    e"

lemma F_EPDA_TC__edge_reversal: "
  valid_epda G
  \<Longrightarrow> x \<in> epda_delta G
  \<Longrightarrow> F_EPDA_TC__edge__RL G (F_EPDA_TC__edge (SOME f. inj_on f (epda_states G)) (SOME f. inj_on f (epda_gamma G)) x) = x"
  apply(simp add: F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def)
  apply(subgoal_tac "valid_epda_step_label G x")
   prefer 2
   apply(simp add: valid_epda_def)
  apply(simp add: valid_epda_step_label_def)
  apply(case_tac x)
  apply(rename_tac edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac src read pop push trg)
  apply(rename_tac src read pop push trg)(*strict*)
  apply(simp add: F_EPDA_TC__edge_def)
  apply(rule conjI)
   apply(rename_tac src read pop push trg)(*strict*)
   apply (metis valid_epda_def SOME_injective_is_injective inv_into_f_eq)
  apply(rename_tac src read pop push trg)(*strict*)
  apply(rule conjI)
   apply(rename_tac src read pop push trg)(*strict*)
   apply(rule inv_into_f_eq_map2)
    apply(rename_tac src read pop push trg)(*strict*)
    apply (metis valid_epda_def SOME_injective_is_injective)
   apply(rename_tac src read pop push trg)(*strict*)
   apply (metis epda_step_label.simps(3) valid_epda_pop_in_gamma)
  apply(rename_tac src read pop push trg)(*strict*)
  apply(rule conjI)
   apply(rename_tac src read pop push trg)(*strict*)
   apply(rule inv_into_f_eq_map2)
    apply(rename_tac src read pop push trg)(*strict*)
    apply (metis valid_epda_def SOME_injective_is_injective)
   apply(rename_tac src read pop push trg)(*strict*)
   apply (metis epda_step_label.simps(4) valid_epda_push_in_gamma)
  apply(rename_tac src read pop push trg)(*strict*)
  apply (metis valid_epda_def SOME_injective_is_injective inv_into_f_eq)
  done

lemma F_EPDA_TC__edge__RL__preserves__epda_delta: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta (F_EPDA_TC G)
  \<Longrightarrow> F_EPDA_TC__edge__RL G e \<in> epda_delta G"
  apply(simp add: F_EPDA_TC_def F_EPDA_TC__epda_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t="F_EPDA_TC__edge__RL G (F_EPDA_TC__edge (SOME f. inj_on f (epda_states G)) (SOME f. inj_on f (epda_gamma G)) x)"
      and s="x"
      in ssubst)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule F_EPDA_TC__edge_reversal)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

definition F_EPDA_TC__epdaS_conf1__LR :: "
  ('stateA \<Rightarrow> 'stateB DT_symbol)
  \<Rightarrow> ('stackA \<Rightarrow> 'stackB DT_symbol)
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf"
  where
    "F_EPDA_TC__epdaS_conf1__LR fq fg c \<equiv>
  \<lparr>epdaS_conf_state = fq (epdaS_conf_state c),
  epdaS_conf_scheduler = epdaS_conf_scheduler c,
  epdaS_conf_stack = map fg (epdaS_conf_stack c)\<rparr>"

definition F_EPDA_TC__epdaS_conf__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf"
  where
    "F_EPDA_TC__epdaS_conf__LR G c \<equiv>
  F_EPDA_TC__epdaS_conf1__LR
    (SOME f. inj_on f (epda_states G))
    (SOME f. inj_on f (epda_gamma G))
    c"

definition F_EPDA_TC__epdaS_conf1__LRRev :: "
  ('stateB DT_symbol \<Rightarrow> 'stateA)
  \<Rightarrow> ('stackB DT_symbol \<Rightarrow> 'stackA)
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf"
  where
    "F_EPDA_TC__epdaS_conf1__LRRev fq fg c \<equiv>
  \<lparr>epdaS_conf_state = fq (epdaS_conf_state c),
  epdaS_conf_scheduler = epdaS_conf_scheduler c,
  epdaS_conf_stack = map fg (epdaS_conf_stack c)\<rparr>"

definition F_EPDA_TC__epdaS_conf__LRRev :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf"
  where
    "F_EPDA_TC__epdaS_conf__LRRev G c \<equiv>
  F_EPDA_TC__epdaS_conf1__LRRev
    (inv_into (epda_states G) (SOME f. inj_on f (epda_states G)))
    (inv_into (epda_gamma G) (SOME f. inj_on f (epda_gamma G)))
    c"

lemma F_EPDA_TC__edge__preserves__valid_epda_step_labels: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> valid_epda_step_label G e
  \<Longrightarrow> G' = F_EPDA_TC__epda G fq fg
  \<Longrightarrow> inj_on fq (epda_states G)
  \<Longrightarrow> inj_on fg (epda_gamma G)
  \<Longrightarrow> e' = F_EPDA_TC__edge fq fg e
  \<Longrightarrow> valid_epda_step_label G' e'"
  apply(simp add: F_EPDA_TC__epda_def Let_def)
  apply(subgoal_tac "\<exists>f. inj_on f (epda_states G) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (epda_states G))")
   prefer 2
   apply(rule exists_SOME_injective_is_injective)
   apply(simp add: valid_epda_def)
  apply(erule exE)+
  apply(rename_tac f)(*strict*)
  apply(rule_tac
      t="(SOME f::'a \<Rightarrow> 'd DT_symbol. inj_on f (epda_states G))"
      and s="f"
      in ssubst)
   apply(rename_tac f)(*strict*)
   apply(force)
  apply(rename_tac f)(*strict*)
  apply(erule conjE)
  apply(thin_tac "f = (SOME f. inj_on f (epda_states G))")
  apply(subgoal_tac "\<exists>f. inj_on f (epda_gamma G) \<and> f = (SOME f::'c\<Rightarrow>'e DT_symbol. inj_on f (epda_gamma G))")
   apply(rename_tac f)(*strict*)
   prefer 2
   apply(rule exists_SOME_injective_is_injective)
   apply(simp add: valid_epda_def)
  apply(rename_tac f)(*strict*)
  apply(erule exE)+
  apply(rename_tac f fa)(*strict*)
  apply(rule_tac
      t="(SOME f::'c \<Rightarrow> 'e DT_symbol. inj_on f (epda_gamma G))"
      and s="fa"
      in ssubst)
   apply(rename_tac f fa)(*strict*)
   apply(force)
  apply(rename_tac f fa)(*strict*)
  apply(erule conjE)
  apply(thin_tac "fa = (SOME f. inj_on f (epda_gamma G))")
  apply(simp add: valid_epda_def valid_epda_step_label_def F_EPDA_TC__edge_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac f fa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f fa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac f fa)(*strict*)
   apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
   apply(clarsimp)
   apply(rename_tac f fa a aa)(*strict*)
   apply(erule_tac
      P="edge_pop e = a @ [epda_box G]"
      in disjE)
    apply(rename_tac f fa a aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="map fg a"
      in exI)
    apply(rule conjI)
     apply(rename_tac f fa a aa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac f fa a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply(case_tac "xa=epda_box G")
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply(simp add: inj_on_def)
    apply(erule_tac
      x="xa"
      and A="epda_gamma G"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fg x = fg y \<longrightarrow> x = y"
      in ballE)
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(erule_tac
      x="epda_box G"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fa x = fa y \<longrightarrow> x = y"
      in ballE)
      apply(rename_tac f fa a aa xa)(*strict*)
      apply(force)
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply (metis DiffE List.set_simps(1) subsetD)
   apply(rename_tac f fa a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac f fa aa)(*strict*)
   apply(rule_tac
      x="map fg (edge_pop e)"
      in exI)
   apply(rule conjI)
    apply(rename_tac f fa aa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f fa aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac f fa aa xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac f fa aa xa)(*strict*)
    apply(force)
   apply(rename_tac f fa aa xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "xa=epda_box G")
    apply(rename_tac f fa aa xa)(*strict*)
    apply(force)
   apply(rename_tac f fa aa xa)(*strict*)
   apply(rule_tac
      f="fg"
      in inj_onD)
      apply(rename_tac f fa aa xa)(*strict*)
      apply(force)
     apply(rename_tac f fa aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa aa xa)(*strict*)
    apply(force)
   apply(rename_tac f fa aa xa)(*strict*)
   apply(force)
  apply(rename_tac f fa)(*strict*)
  apply(rule conjI)
   apply(rename_tac f fa)(*strict*)
   apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
   apply(clarsimp)
   apply(rename_tac f fa a aa)(*strict*)
   apply(erule_tac
      P="edge_push e = aa @ [epda_box G]"
      in disjE)
    apply(rename_tac f fa a aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="map fg aa"
      in exI)
    apply(rule conjI)
     apply(rename_tac f fa a aa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac f fa a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply(case_tac "xa=epda_box G")
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply(simp add: inj_on_def)
    apply(erule_tac
      x="xa"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fg x = fg y \<longrightarrow> x = y"
      in ballE)
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(erule_tac
      x="epda_box G"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fa x = fa y \<longrightarrow> x = y"
      in ballE)
      apply(rename_tac f fa a aa xa)(*strict*)
      apply(force)
     apply(rename_tac f fa a aa xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa xa)(*strict*)
    apply (metis DiffE List.set_simps(1) subsetD)
   apply(rename_tac f fa a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac f fa a)(*strict*)
   apply(rule_tac
      x="map fg (edge_push e)"
      in exI)
   apply(rule conjI)
    apply(rename_tac f fa a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f fa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac f fa a xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac f fa a xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "xa=epda_box G")
    apply(rename_tac f fa a xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a xa)(*strict*)
   apply(rule_tac
      f="fg"
      in inj_onD)
      apply(rename_tac f fa a xa)(*strict*)
      apply(force)
     apply(rename_tac f fa a xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a xa)(*strict*)
   apply(force)
  apply(rename_tac f fa)(*strict*)
  apply(simp add: may_terminated_by_def must_terminated_by_def append_language_def kleene_star_def)
  apply(rule order_antisym)
   apply(rename_tac f fa)(*strict*)
   apply(clarsimp)
   apply(rename_tac f fa a aa ab)(*strict*)
   apply(case_tac "edge_pop e")
    apply(rename_tac f fa a aa ab)(*strict*)
    apply(force)
   apply(rename_tac f fa a aa ab ac list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. edge_pop e = w' @ [x']")
    apply(rename_tac f fa a aa ab ac list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac f fa a aa ab ac list)(*strict*)
   apply(thin_tac "edge_pop e = ac # list")
   apply(clarsimp)
   apply(rename_tac f fa a aa w' x')(*strict*)
   apply(subgoal_tac "(set w' \<subseteq> epda_gamma G - {epda_box G} \<and> x' = epda_box G)")
    apply(rename_tac f fa a aa w' x')(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac f fa a aa w' x')(*strict*)
     apply(force)
    apply(rename_tac f fa a aa w' x')(*strict*)
    apply(simp add: inj_on_def)
    apply(force)
   apply(rename_tac f fa a aa w' x')(*strict*)
   apply(clarsimp)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac f fa a aa w' ab xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(case_tac "xa=epda_box G")
    apply(rename_tac f fa a aa w' ab xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(simp add: inj_on_def)
   apply(erule_tac
      x="xa"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fg x = fg y \<longrightarrow> x = y"
      in ballE)
    apply(rename_tac f fa a aa w' ab xa)(*strict*)
    apply(erule_tac
      x="epda_box G"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fa x = fa y \<longrightarrow> x = y"
      in ballE)
     apply(rename_tac f fa a aa w' ab xa)(*strict*)
     apply(force)
    apply(rename_tac f fa a aa w' ab xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply (metis DiffE List.set_simps(1) subsetD)
  apply(rename_tac f fa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f fa a aa ab)(*strict*)
  apply(case_tac "edge_push e")
   apply(rename_tac f fa a aa ab)(*strict*)
   apply(force)
  apply(rename_tac f fa a aa ab ac list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_push e = w' @ [x']")
   apply(rename_tac f fa a aa ab ac list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac f fa a aa ab ac list)(*strict*)
  apply(thin_tac "edge_push e = ac # list")
  apply(clarsimp)
  apply(rename_tac f fa a aa w' x')(*strict*)
  apply(subgoal_tac "(set w' \<subseteq> epda_gamma G - {epda_box G} \<and> x' = epda_box G)")
   apply(rename_tac f fa a aa w' x')(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac f fa a aa w' x')(*strict*)
    apply(force)
   apply(rename_tac f fa a aa w' x')(*strict*)
   apply(simp add: inj_on_def)
   apply(force)
  apply(rename_tac f fa a aa w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac f fa a aa w' ab xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(force)
  apply(rename_tac f fa a aa w' ab xa)(*strict*)
  apply(case_tac "xa=epda_box G")
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(force)
  apply(rename_tac f fa a aa w' ab xa)(*strict*)
  apply(simp add: inj_on_def)
  apply(erule_tac
      x="xa"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fg x = fg y \<longrightarrow> x = y"
      in ballE)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(erule_tac
      x="epda_box G"
      and P="\<lambda>x. \<forall>y\<in> epda_gamma G. fa x = fa y \<longrightarrow> x = y"
      in ballE)
    apply(rename_tac f fa a aa w' ab xa)(*strict*)
    apply(force)
   apply(rename_tac f fa a aa w' ab xa)(*strict*)
   apply(force)
  apply(rename_tac f fa a aa w' ab xa)(*strict*)
  apply (metis DiffE List.set_simps(1) subsetD)
  done

lemma F_EPDA_TC__preserves__valid_pda_hlp: "
  valid_pda G
  \<Longrightarrow> inj_on fq (epda_states G)
  \<Longrightarrow> inj_on fg (epda_gamma G)
  \<Longrightarrow> valid_pda (F_EPDA_TC__epda G fq fg)"
  apply(simp add: valid_pda_def F_EPDA_TC__epda_def)
  apply(clarsimp)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EPDA_TC__edge_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      G="G"
      in F_EPDA_TC__edge__preserves__valid_epda_step_labels)
        apply(rename_tac x)(*strict*)
        apply(simp add: valid_epda_def)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(simp add: F_EPDA_TC__epda_def)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

theorem F_EPDA_TC__preserves__valid_pda: "
  valid_pda G
  \<Longrightarrow> valid_pda (F_EPDA_TC G)"
  apply(simp add: F_EPDA_TC_def)
  apply(rule F_EPDA_TC__preserves__valid_pda_hlp)
    apply(force)
   apply(rule SOME_injective_is_injective)
   apply(simp add: valid_pda_def valid_epda_def)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_pda_def valid_epda_def)
  done

lemma F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_configurations: "
  valid_pda G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> inj_on fq (epda_states G)
  \<Longrightarrow> inj_on fg (epda_gamma G)
  \<Longrightarrow> F_EPDA_TC__epdaS_conf1__LR fq fg c \<in> epdaS_configurations (F_EPDA_TC__epda G fq fg)"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rule conjI)
   apply(rename_tac q i s)(*strict*)
   apply(simp add: F_EPDA_TC__epda_def Let_def)
  apply(rename_tac q i s)(*strict*)
  apply(rule conjI)
   apply(rename_tac q i s)(*strict*)
   apply(simp add: F_EPDA_TC__epda_def Let_def)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EPDA_TC__epda_def Let_def)
  apply(force)
  done

lemma F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_initial_configurations: "
  valid_pda G
  \<Longrightarrow> c \<in> epdaS_initial_configurations G
  \<Longrightarrow> inj_on fq (epda_states G)
  \<Longrightarrow> inj_on fg (epda_gamma G)
  \<Longrightarrow> F_EPDA_TC__epdaS_conf1__LR fq fg c \<in> epdaS_initial_configurations (F_EPDA_TC__epda G fq fg)"
  apply(simp add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__epdaS_conf1__LR_def)
   apply(simp add: F_EPDA_TC__epda_def Let_def)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__epda_def Let_def)
   apply(simp add: F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rule F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_configurations)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_marking_configurations: "
  valid_pda G
  \<Longrightarrow> c \<in> epdaS_marking_configurations G
  \<Longrightarrow> inj_on fq (epda_states G)
  \<Longrightarrow> inj_on fg (epda_gamma G)
  \<Longrightarrow> F_EPDA_TC__epdaS_conf1__LR fq fg c \<in> epdaS_marking_configurations (F_EPDA_TC__epda G fq fg)"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__epda_def Let_def)
   apply(simp add: F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rule F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_configurations)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

definition F_EPDA_TC__relation_epda__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epda__LR G1 G2 \<equiv>
  valid_pda G1
  \<and> G2 = F_EPDA_TC G1"

definition F_EPDA_TC__relation_epdaS_conf__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2 \<equiv>
  F_EPDA_TC__relation_epda__LR G1 G2
  \<and> c1 \<in> epdaS_configurations G1
  \<and> c2 = F_EPDA_TC__epdaS_conf__LR G1 c1"

definition F_EPDA_TC__relation_epdaS_initial_conf__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 c1 c2 \<equiv>
  F_EPDA_TC__relation_epda__LR G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_EPDA_TC__epdaS_conf__LR G1 c1"

definition F_EPDA_TC__relation_effect__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_effect__LR G1 G2 w1 w2 \<equiv>
  F_EPDA_TC__relation_epda__LR G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_EPDA_TC__relation_epda__LR G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(subgoal_tac "valid_pda (F_EPDA_TC G1)")
   apply(rename_tac G1)(*strict*)
   apply(simp add: valid_pda_def)
   apply(force)
  apply(rename_tac G1)(*strict*)
  apply(rule F_EPDA_TC__preserves__valid_pda)
  apply(force)
  done

definition F_EPDA_TC__edge__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label"
  where
    "F_EPDA_TC__edge__LR G e \<equiv>
  F_EPDA_TC__edge
    (SOME f. inj_on f (epda_states G))
    (SOME f. inj_on f (epda_gamma G))
    e"

definition F_EPDA_TC__relation_epdaS_step__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> (('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label, ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e c1' c2 d \<equiv>
  d = der2 (F_EPDA_TC__epdaS_conf__LR G1 c1) (F_EPDA_TC__edge__LR G1 e) (F_EPDA_TC__epdaS_conf__LR G1 c1')"

definition F_EPDA_TC__relation_epdaS_initial__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> (('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label, ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_initial__LR G1 G2 c1 d \<equiv>
  d = der1 (F_EPDA_TC__epdaS_conf__LR G1 c1)"

lemma F_EPDA_TC__preserves__epdaS_configurations: "
  F_EPDA_TC__relation_epda__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_EPDA_TC__epdaS_conf__LR G1 c1 \<in> epdaS_configurations G2"
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(simp add: F_EPDA_TC_def)
  apply(rule F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_configurations)
     apply(force)
    apply(force)
   apply(rule SOME_injective_is_injective)
   apply(simp add: valid_pda_def valid_epda_def)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_pda_def valid_epda_def)
  done

lemma F_EPDA_TC__preserves__epdaS_initial_configurations: "
  F_EPDA_TC__relation_epda__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_EPDA_TC__epdaS_conf__LR G1 c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(simp add: F_EPDA_TC_def)
  apply(rule F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_initial_configurations)
     apply(force)
    apply(force)
   apply(rule SOME_injective_is_injective)
   apply(simp add: valid_pda_def valid_epda_def)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_pda_def valid_epda_def)
  done

lemma F_EPDA_TC__preserves__epdaS_marking_configurations: "
  F_EPDA_TC__relation_epda__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> F_EPDA_TC__epdaS_conf__LR G1 c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(simp add: F_EPDA_TC_def)
  apply(rule F_EPDA_TC__epdaS_conf1__LR__preserves__epdaS_marking_configurations)
     apply(force)
    apply(force)
   apply(rule SOME_injective_is_injective)
   apply(simp add: valid_pda_def valid_epda_def)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_pda_def valid_epda_def)
  done

lemma F_EPDA_TC__preserves__simulation_initial: "
  F_EPDA_TC__relation_epda__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> epdaS.derivation_initial G2 (der1 (F_EPDA_TC__epdaS_conf__LR G1 c1))"
  apply(rule epdaS.derivation_initialI)
   apply(rule epdaS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_EPDA_TC__preserves__epdaS_initial_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EPDA_TC__relation_epdaS_initial__LR G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epdaS_initial__LR_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_EPDA_TC__preserves__simulation_initial)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__LR_def)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(simp add: F_EPDA_TC__relation_epda__LR_def valid_pda_def valid_dpda_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(metis epdaS_inst_AX_initial_configuration_belongs subsetD)
  done

lemma F_EPDA_TC__preserves__simulation_step: "
  epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS_step_relation (F_EPDA_TC G1) (F_EPDA_TC__epdaS_conf__LR G1 c1) (F_EPDA_TC__edge__LR G1 e1) (F_EPDA_TC__epdaS_conf__LR G1 c1')"
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(rule conjI)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_EPDA_TC_def F_EPDA_TC__epda_def F_EPDA_TC__edge__LR_def)
  apply(rename_tac w)(*strict*)
  apply(rule conjI)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__edge__LR_def F_EPDA_TC__epdaS_conf1__LR_def F_EPDA_TC__edge_def)
  apply(rename_tac w)(*strict*)
  apply(rule conjI)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__edge__LR_def F_EPDA_TC__epdaS_conf1__LR_def F_EPDA_TC__edge_def)
  apply(rename_tac w)(*strict*)
  apply(rule conjI)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__edge__LR_def F_EPDA_TC__epdaS_conf1__LR_def F_EPDA_TC__edge_def)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__edge__LR_def F_EPDA_TC__epdaS_conf1__LR_def F_EPDA_TC__edge_def)
  done

lemma F_EPDA_TC__relation_epdaS_step__LR_maps_to_derivation: "
  F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_EPDA_TC__relation_epdaS_step__LR_def)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
   prefer 2
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(clarsimp)
  apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rule F_EPDA_TC__preserves__simulation_step)
  apply(force)
  done

lemma F_EPDA_TC__relation_epdaS_step__LR_maps_to_derivation_belongs: "
  F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.belongs G2 d2"
  apply(simp add: F_EPDA_TC__relation_epdaS_step__LR_def)
  apply(rule epdaS.der2_belongs_prime)
    prefer 3
    apply(rule F_EPDA_TC__relation_epdaS_step__LR_maps_to_derivation)
      apply(simp add: F_EPDA_TC__relation_epdaS_step__LR_def)
     apply(force)
    apply(force)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
   apply(clarsimp)
   apply(subgoal_tac "valid_pda (F_EPDA_TC G1)")
    apply(simp add: valid_pda_def)
    apply(force)
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(force)
  apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(clarsimp)
  apply(rule F_EPDA_TC__preserves__epdaS_configurations)
   apply(force)
  apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EPDA_TC__relation_epdaS_step__LR_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_EPDA_TC__relation_epdaS_step__LR_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_EPDA_TC__relation_epdaS_step__LR_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_EPDA_TC__relation_epdaS_step__LR_maps_to_derivation_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_EPDA_TC__relation_epdaS_step__LR_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: der2_def get_configuration_def F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: der2_def get_configuration_def F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.AX_step_relation_preserves_belongsC)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial_conf__LR F_EPDA_TC__relation_epda__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_F_EPDA_TC__StateSimLR" : ATS_Simulation_Configuration_Weak
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
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EPDA_TC__relation_epdaS_conf__LR"
  (* relation_initial_configuration *)
  "F_EPDA_TC__relation_epdaS_initial_conf__LR"
  (* relation_effect *)
  "F_EPDA_TC__relation_effect__LR"
  (* relation_TSstructure *)
  "F_EPDA_TC__relation_epda__LR"
  (* relation_initial_simulation *)
  "F_EPDA_TC__relation_epdaS_initial__LR"
  (* relation_step_simulation *)
  "F_EPDA_TC__relation_epdaS_step__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add:  epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(rule F_EPDA_TC__preserves__epdaS_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="F_EPDA_TC__epdaS_conf__LR G1 c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_EPDA_TC__preserves__epdaS_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_initial__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EPDA_TC__epdaS_conf__LR G1 ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EPDA_TC__preserves__epdaS_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial_conf__LR F_EPDA_TC__relation_epda__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__LR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EPDA_TC__relation_effect__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EPDA_TC__relation_epdaS_initial_conf__LR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation_preserves_marked_effect: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_initial__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__LR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EPDA_TC__relation_effect__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EPDA_TC__relation_epdaS_initial_conf__LR_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial_conf__LR F_EPDA_TC__relation_effect__LR F_EPDA_TC__relation_epda__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_step__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__LR G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__LR_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__LR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="F_EPDA_TC__epdaS_conf__LR G1 c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(subgoal_tac "c'=c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x="F_EPDA_TC__epdaS_conf__LR G1 c1'"
      in exI)
  apply(subgoal_tac "F_EPDA_TC__epdaS_conf__LR G1 c=ca")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__LR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="Suc deri1n"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e option b)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def get_configuration_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_initial__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__LR G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__LR_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__LR_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__LR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="F_EPDA_TC__epdaS_conf__LR G1 c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_EPDA_TC__relation_epdaS_conf__LR F_EPDA_TC__relation_epdaS_initial_conf__LR F_EPDA_TC__relation_effect__LR F_EPDA_TC__relation_epda__LR F_EPDA_TC__relation_epdaS_initial__LR F_EPDA_TC__relation_epdaS_step__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "epdaS_epdaS_F_EPDA_TC__StateSimLR" : ATS_Simulation_Configuration_WeakLR_FULL
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
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EPDA_TC__relation_epdaS_conf__LR"
  (* relation_initial_configuration *)
  "F_EPDA_TC__relation_epdaS_initial_conf__LR"
  (* relation_effect *)
  "F_EPDA_TC__relation_effect__LR"
  (* relation_TSstructure *)
  "F_EPDA_TC__relation_epda__LR"
  (* relation_initial_simulation *)
  "F_EPDA_TC__relation_epdaS_initial__LR"
  (* relation_step_simulation *)
  "F_EPDA_TC__relation_epdaS_step__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms )
  done

lemma F_EPDA_TC__preserves_lang1: "
  valid_pda G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_EPDA_TC G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def Suc_n_not_n epdaS.AX_marked_language_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_EPDA_TC G)"
      and s="epdaS.finite_marked_language (F_EPDA_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply(subgoal_tac "valid_pda (F_EPDA_TC G)")
    prefer 2
    apply(rule F_EPDA_TC__preserves__valid_pda)
    apply(force)
   apply(simp add: valid_pda_def)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EPDA_TC__relation_effect__LR SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_F_EPDA_TC__StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__LR_def)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(force)
  done

lemma F_EPDA_TC__preserves_unmarked_language1: "
  valid_pda G
  \<Longrightarrow> epdaS.unmarked_language G \<subseteq> epdaS.unmarked_language (F_EPDA_TC G)"
  apply(rule_tac
      t="epdaS.unmarked_language G"
      and s="epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def Suc_n_not_n epdaS.AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_EPDA_TC G)"
      and s="epdaS.finite_unmarked_language (F_EPDA_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply(subgoal_tac "valid_pda (F_EPDA_TC G)")
    prefer 2
    apply(rule F_EPDA_TC__preserves__valid_pda)
    apply(force)
   apply(simp add: valid_pda_def)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EPDA_TC__relation_effect__LR SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_F_EPDA_TC__StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__LR_def)
  apply(force)
  done

definition F_EPDA_TC__relation_epda__RL :: "
  ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epda__RL G2 G1 \<equiv>
  valid_pda G1
  \<and> G2 = F_EPDA_TC G1"

definition F_EPDA_TC__relation_epdaS_conf__RL :: "
  ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_conf__RL G2 G1 c2 c1 \<equiv>
  F_EPDA_TC__relation_epda__RL G2 G1
  \<and> c1 \<in> epdaS_configurations G1
  \<and> c2 = F_EPDA_TC__epdaS_conf__LR G1 c1"

definition F_EPDA_TC__relation_epdaS_initial_conf__RL :: "
  ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_initial_conf__RL G2 G1 c2 c1 \<equiv>
  F_EPDA_TC__relation_epda__RL G2 G1
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_EPDA_TC__epdaS_conf__LR G1 c1"

definition F_EPDA_TC__relation_effect__RL :: "
  ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_effect__RL G1 G2 w1 w2 \<equiv>
  F_EPDA_TC__relation_epda__RL G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_EPDA_TC__relation_epda__RL G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply(subgoal_tac "valid_pda (F_EPDA_TC G2)")
   apply(rename_tac G2)(*strict*)
   apply(simp add: valid_pda_def)
   apply(force)
  apply(rename_tac G2)(*strict*)
  apply(rule F_EPDA_TC__preserves__valid_pda)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> valid_epda G2)"
  apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis valid_dpda_def valid_pda_def)
  done

definition F_EPDA_TC__relation_epdaS_step__LRRL :: "
  ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> (('stateA, 'event, 'stackA) epda_step_label, ('stateA, 'event, 'stackA) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_step__LRRL G2 G1 c1 e c1' c2 d \<equiv>
  d = der2 (F_EPDA_TC__epdaS_conf__LRRev G1 c1) (F_EPDA_TC__edge__RL G1 e) (F_EPDA_TC__epdaS_conf__LRRev G1 c1')"

definition F_EPDA_TC__relation_epdaS_initial__LRRL :: "
  ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> (('stateA, 'event, 'stackA) epda_step_label, ('stateA, 'event, 'stackA) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__relation_epdaS_initial__LRRL G1 G2 c1 d \<equiv>
  d = der1 (F_EPDA_TC__epdaS_conf__LRRev G2 c1)"

lemma F_EPDA_TC__C_rev_preserves_configurations: "
  F_EPDA_TC__relation_epda__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_EPDA_TC__epdaS_conf__LRRev G2 c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EPDA_TC_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def F_EPDA_TC__epda_def)
  apply(clarsimp)
  apply(rename_tac i s x)(*strict*)
  apply(rule conjI)
   apply(rename_tac i s x)(*strict*)
   apply(rule_tac
      t="inv_into (epda_states G2) (SOME f. inj_on f (epda_states G2)) ((SOME f. inj_on f (epda_states G2)) x)"
      and s="x"
      in ssubst)
    apply(rename_tac i s x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i s x)(*strict*)
   apply(rule inv_into_f_eq)
     apply(rename_tac i s x)(*strict*)
     apply(rule SOME_injective_is_injective)
     apply(simp add: valid_pda_def valid_epda_def)
    apply(rename_tac i s x)(*strict*)
    apply(force)
   apply(rename_tac i s x)(*strict*)
   apply(force)
  apply(rename_tac i s x)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x xb)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. s=w1@[xb]@w2")
   apply(rename_tac i s x xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac i x w1 w2 xa)(*strict*)
   apply(rule_tac
      t="inv_into (epda_gamma G2) (SOME f. inj_on f (epda_gamma G2)) ((SOME f. inj_on f (epda_gamma G2)) xa)"
      and s="xa"
      in ssubst)
    apply(rename_tac i x w1 w2 xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i x w1 w2 xa)(*strict*)
   apply(rule inv_into_f_eq)
     apply(rename_tac i x w1 w2 xa)(*strict*)
     apply(rule SOME_injective_is_injective)
     apply(simp add: valid_pda_def valid_epda_def)
    apply(rename_tac i x w1 w2 xa)(*strict*)
    apply(force)
   apply(rename_tac i x w1 w2 xa)(*strict*)
   apply(force)
  apply(rename_tac i s x xb)(*strict*)
  apply (metis ConsApp in_set_conv_decomp_first insert_Nil)
  done



lemma F_EPDA_TC__C_rev_preserves_initial_configurations: "
  F_EPDA_TC__relation_epda__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_EPDA_TC__epdaS_conf__LRRev G2 c1 \<in> epdaS_initial_configurations G2"
  apply(subgoal_tac "valid_pda (F_EPDA_TC G1)")
   prefer 2
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def)
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(force)
  apply(subgoal_tac "c1 \<in> epdaS.get_accessible_configurations G1")
   prefer 2
   apply (simp add: F_EPDA_TC__preserves__valid_pda F_EPDA_TC__relation_epda__RL_def epdaS.initial_configurations_are_get_accessible_configurations valid_pda_to_valid_epda)
  apply(simp add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule conjI)
   apply(rule propSym)
   apply(rule conjI)
    apply(rule F_EPDA_TC__C_rev_preserves_configurations)
     apply(force)
    apply(force)
   apply(simp add: F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def inv_into_def)
   apply(simp add: valid_pda_def valid_epda_def F_EPDA_TC__relation_epda__RL_def F_EPDA_TC_def epdaS_configurations_def F_EPDA_TC__epda_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def)
   apply(clarsimp)
   apply(rule some_equality)
    apply(rule context_conjI)
     apply(force)
    apply(force)
   apply(rule_tac f="(SOME f. inj_on f (epda_states G2))" in inj_onD)
      apply(rule SOME_injective_is_injective)
      apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def valid_epda_def SOME_injective_is_injective)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: epdaS.get_accessible_configurations_def F_EPDA_TC__relation_epda__RL_def F_EPDA_TC_def epdaS_configurations_def F_EPDA_TC__epda_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def)
  apply(clarsimp)
  apply(subgoal_tac "(epda_box G2) = xa")
   prefer 2
   apply(rule_tac f="(SOME f. inj_on f (epda_gamma G2))" in inj_onD)
      apply(rule SOME_injective_is_injective)
      apply(simp add: valid_pda_def valid_epda_def epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def valid_epda_def SOME_injective_is_injective)
     apply(force)
    apply(simp add: valid_pda_def valid_epda_def epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def valid_epda_def SOME_injective_is_injective)
   apply(force)
  apply(simp add: epdaS.get_accessible_configurations_def F_EPDA_TC__relation_epda__RL_def F_EPDA_TC_def epdaS_configurations_def F_EPDA_TC__epda_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def)
  apply(clarsimp)
  apply(rule inv_into_f_f)
   apply(rule SOME_injective_is_injective)
   apply(simp add: valid_pda_def valid_epda_def epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def valid_epda_def SOME_injective_is_injective)
  apply(simp add: valid_pda_def valid_epda_def epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def valid_epda_def SOME_injective_is_injective)
  done

lemma F_EPDA_TC__epdaS_conf__LR_reverse: "
  valid_pda G2
  \<Longrightarrow> c1 \<in> epdaS_configurations (F_EPDA_TC G2)
  \<Longrightarrow> c1 = F_EPDA_TC__epdaS_conf__LR G2 (F_EPDA_TC__epdaS_conf__LRRev G2 c1)"
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LR_def F_EPDA_TC__epdaS_conf1__LRRev_def F_EPDA_TC_def F_EPDA_TC__epda_def epdaS_initial_configurations_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i s x)(*strict*)
  apply(rule conjI)
   apply(rename_tac i s x)(*strict*)
   apply (metis f_inv_into_f inMap2)
  apply(rename_tac i s x)(*strict*)
  apply(rule listEqI)
   apply(rename_tac i s x)(*strict*)
   apply(clarsimp)
  apply(rename_tac i s x ia)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1 w2. s=w1@[s!ia]@w2")
   apply(rename_tac i s x ia)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s x ia w1 w2)(*strict*)
   apply(subgoal_tac "s!ia \<in> (SOME f. inj_on f (epda_gamma G2)) ` epda_gamma G2")
    apply(rename_tac i s x ia w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac i x ia w1 w2 xa)(*strict*)
    apply (metis f_inv_into_f imageI)
   apply(rename_tac i s x ia w1 w2)(*strict*)
   apply(force)
  apply(rename_tac i s x ia)(*strict*)
  apply (metis ConsApp nth_take_drop_split)
  done

lemma F_EPDA_TC__epdaS_conf__LR_reverse2: "
  valid_pda G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G2
  \<Longrightarrow> c1 = F_EPDA_TC__epdaS_conf__LRRev G2 (F_EPDA_TC__epdaS_conf__LR G2 c1)"
  apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LR_def F_EPDA_TC__epdaS_conf1__LRRev_def F_EPDA_TC_def F_EPDA_TC__epda_def epdaS_initial_configurations_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(rule conjI)
   apply(rename_tac q i s)(*strict*)
   apply(rule sym)
   apply(rule inv_into_f_eq)
     apply(rename_tac q i s)(*strict*)
     apply(rule SOME_injective_is_injective)
     apply(simp add: valid_pda_def valid_epda_def)
    apply(rename_tac q i s)(*strict*)
    apply(force)
   apply(rename_tac q i s)(*strict*)
   apply(force)
  apply(rename_tac q i s)(*strict*)
  apply(rule listEqI)
   apply(rename_tac q i s)(*strict*)
   apply(clarsimp)
  apply(rename_tac q i s ia)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1 w2. s=w1@[s!ia]@w2")
   apply(rename_tac q i s ia)(*strict*)
   prefer 2
   apply (metis ConsApp nth_take_drop_split)
  apply(rename_tac q i s ia)(*strict*)
  apply(clarsimp)
  apply(rename_tac q i s ia w1 w2)(*strict*)
  apply(subgoal_tac "s!ia \<in> epda_gamma G2")
   apply(rename_tac q i s ia w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac q i s ia w1 w2)(*strict*)
  apply(rule sym)
  apply(rule inv_into_f_eq)
    apply(rename_tac q i s ia w1 w2)(*strict*)
    apply(rule SOME_injective_is_injective)
    apply(simp add: valid_pda_def valid_epda_def)
   apply(rename_tac q i s ia w1 w2)(*strict*)
   apply(force)
  apply(rename_tac q i s ia w1 w2)(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EPDA_TC__relation_epdaS_initial__LRRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EPDA_TC__relation_epdaS_conf__RL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epdaS_initial__LRRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_EPDA_TC__C_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__RL_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule F_EPDA_TC__C_rev_preserves_initial_configurations)
     apply(rename_tac G1 G2 c1)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1)(*strict*)
   apply(rule F_EPDA_TC__epdaS_conf__LR_reverse)
    apply(rename_tac G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G2 c1)(*strict*)
   apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_EPDA_TC__relation_epda__LR_def epdaS_inst_AX_initial_configuration_belongs subsetD)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_EPDA_TC__C_rev_preserves_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_EPDA_TC__relation_epda__LR_def F_EPDA_TC__relation_epda__RL_def epdaS.AX_initial_configuration_belongs nset_mp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule F_EPDA_TC__epdaS_conf__LR_reverse)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_EPDA_TC__relation_epda__LR_def F_EPDA_TC__relation_epda__RL_def epdaS.AX_initial_configuration_belongs nset_mp)
  done

lemma F_EPDA_TCRev_preserves_step_relation: "
  F_EPDA_TC__relation_epda__RL G1 G2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS_step_relation G2 (F_EPDA_TC__epdaS_conf__LRRev G2 c1) (F_EPDA_TC__edge__RL G2 e1) (F_EPDA_TC__epdaS_conf__LRRev G2 c1')"
  apply(simp add: epdaS_step_relation_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__relation_epda__RL_def F_EPDA_TC__epdaS_conf1__LRRev_def)
  apply(subgoal_tac "F_EPDA_TC__edge__RL G2 e1 \<in> epda_delta G2")
   prefer 2
   apply(rule F_EPDA_TC__edge__RL__preserves__epda_delta)
    apply(simp add: valid_pda_def)
   apply(force)
  apply(subgoal_tac "valid_pda (F_EPDA_TC G2)")
   prefer 2
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(simp add: valid_pda_def)
  apply(subgoal_tac "valid_epda_step_label (F_EPDA_TC G2) e1")
   prefer 2
   apply(simp add: valid_pda_def valid_epda_def)
   apply(force)
  apply(simp add: valid_epda_step_label_def F_EPDA_TC_def F_EPDA_TC__epda_def)
  apply(clarsimp)
  apply(rename_tac x xa xb w)(*strict*)
  apply(simp add: F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EPDA_TC__relation_epdaS_conf__RL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EPDA_TC__relation_epdaS_step__LRRL_def)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(rule F_EPDA_TCRev_preserves_step_relation)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(simp add: F_EPDA_TC__relation_epda__RL_def)
      apply(simp add: valid_pda_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_EPDA_TC__C_rev_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
    apply(rule F_EPDA_TC__preserves__epdaS_configurations)
     apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
     apply(simp add: F_EPDA_TC__relation_epda__LR_def F_EPDA_TC__relation_epda__RL_def)
    apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: get_configuration_def der2_def F_EPDA_TC__relation_epdaS_conf__RL_def F_EPDA_TC__relation_epda__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule sym)
   apply(rule F_EPDA_TC__epdaS_conf__LR_reverse2)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(simp add: maximum_of_domain_def der2_def)
  apply(simp add: get_configuration_def F_EPDA_TC__relation_epdaS_conf__RL_def F_EPDA_TC__relation_epda__RL_def)
  apply(clarsimp)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "valid_pda (F_EPDA_TC G2)")
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   prefer 2
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule F_EPDA_TC__C_rev_preserves_configurations)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(simp add: F_EPDA_TC__relation_epda__RL_def)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule epdaS.AX_step_relation_preserves_belongsC)
     apply(rename_tac G2 c2 e1 c1')(*strict*)
     apply(simp add: valid_pda_def)
     apply(force)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule F_EPDA_TC__preserves__epdaS_configurations)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(simp add: F_EPDA_TC__relation_epda__LR_def)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule F_EPDA_TC__epdaS_conf__LR_reverse)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule epdaS.AX_step_relation_preserves_belongsC)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(simp add: valid_pda_def)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule F_EPDA_TC__preserves__epdaS_configurations)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial_conf__RL F_EPDA_TC__relation_epda__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation epdaS_epdaS_F_EPDA_TC__StateSimRL_step_relation_step_simulation epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs)
  done

interpretation "epdaS_epdaS_F_EPDA_TC__StateSimRL" : ATS_Simulation_Configuration_Weak
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
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EPDA_TC__relation_epdaS_conf__RL"
  (* relation_initial_configuration *)
  "F_EPDA_TC__relation_epdaS_initial_conf__RL"
  (* relation_effect *)
  "F_EPDA_TC__relation_effect__RL"
  (* relation_TSstructure *)
  "F_EPDA_TC__relation_epda__RL"
  (* relation_initial_simulation *)
  "F_EPDA_TC__relation_epdaS_initial__LRRL"
  (* relation_step_simulation *)
  "F_EPDA_TC__relation_epdaS_step__LRRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add:  epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_EPDA_TC__C_rev_preserves_marking_configurations: "
  F_EPDA_TC__relation_epda__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> F_EPDA_TC__epdaS_conf__LRRev G2 c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def F_EPDA_TC_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def F_EPDA_TC_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def F_EPDA_TC__epda_def epdaS_configurations_def)
   apply(clarsimp)
   apply(rename_tac x s xa)(*strict*)
   apply(rule_tac
      t="inv_into (epda_states G2) (SOME f. inj_on f (epda_states G2)) ((SOME f. inj_on f (epda_states G2)) x)"
      and s="x"
      in ssubst)
    apply(rename_tac x s xa)(*strict*)
    apply(rule inv_into_f_eq)
      apply(rename_tac x s xa)(*strict*)
      apply(rule SOME_injective_is_injective)
      apply(simp add: valid_pda_def valid_epda_def)
     apply(rename_tac x s xa)(*strict*)
     apply(simp add: valid_pda_def valid_epda_def)
     apply(force)
    apply(rename_tac x s xa)(*strict*)
    apply(force)
   apply(rename_tac x s xa)(*strict*)
   apply(force)
  apply(rule F_EPDA_TC__C_rev_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_step_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EPDA_TC__epdaS_conf__LRRev G2 ca"
      in ssubst)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(rule F_EPDA_TC__epdaS_conf__LR_reverse2)
     apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(simp add: F_EPDA_TC__relation_epda__RL_def)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EPDA_TC__C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="F_EPDA_TC__epdaS_conf__LRRev G2 c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def derivation_append_def get_configuration_def)
     apply(rule F_EPDA_TC__epdaS_conf__LR_reverse2)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(simp add: F_EPDA_TC__relation_epda__RL_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_EPDA_TC__C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def derivation_append_def get_configuration_def F_EPDA_TC__relation_epdaS_initial_conf__RL_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_initial__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EPDA_TC__epdaS_conf__LRRev G2 ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(rule F_EPDA_TC__epdaS_conf__LR_reverse2)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(simp add: F_EPDA_TC__relation_epda__RL_def)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EPDA_TC__C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial_conf__RL F_EPDA_TC__relation_epda__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__RL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EPDA_TC__relation_effect__RL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EPDA_TC__relation_epdaS_initial_conf__RL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_initial__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__RL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EPDA_TC__relation_effect__RL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EPDA_TC__relation_epdaS_initial_conf__RL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial_conf__RL F_EPDA_TC__relation_effect__RL F_EPDA_TC__relation_epda__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__relation_epdaS_conf__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__RL G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__RL_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__RL_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: derivation_append_fit_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a i ea caa e c)(*strict*)
   apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(subgoal_tac "c'=c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x="F_EPDA_TC__epdaS_conf__LRRev G2 c1'"
      in exI)
  apply(simp add: derivation_append_def)
  apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__RL_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca)(*strict*)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
   apply(case_tac n)
    apply(rename_tac G1 G2 c2 e1 d2 n deri1 deri1n deri2 deri2n f a ea ca e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 d2 deri1 deri1n deri2 f a ea ca e c)(*strict*)
    apply(rule F_EPDA_TC__epdaS_conf__LR_reverse2)
     apply(rename_tac G1 G2 c2 e1 d2 deri1 deri1n deri2 f a ea ca e c)(*strict*)
     apply(simp add: F_EPDA_TC__relation_epda__RL_def)
    apply(rename_tac G1 G2 c2 e1 d2 deri1 deri1n deri2 f a ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 d2 n deri1 deri1n deri2 deri2n f a ea ca e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 d2 deri1 deri1n deri2 deri2n f a ea ca e c nat)(*strict*)
   apply(rule F_EPDA_TC__epdaS_conf__LR_reverse2)
    apply(rename_tac G1 G2 c2 e1 d2 deri1 deri1n deri2 deri2n f a ea ca e c nat)(*strict*)
    apply(simp add: F_EPDA_TC__relation_epda__RL_def)
   apply(rename_tac G1 G2 c2 e1 d2 deri1 deri1n deri2 deri2n f a ea ca e c nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a e ca)(*strict*)
  apply(simp add: F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EPDA_TC__relation_epdaS_initial__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EPDA_TC__relation_epdaS_initial_conf__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EPDA_TC__relation_effect__RL G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__RL_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__relation_epdaS_conf__RL_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
   apply(simp add: F_EPDA_TC__relation_epdaS_initial_conf__RL_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca i ea caa e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_EPDA_TC__relation_epdaS_conf__RL F_EPDA_TC__relation_epdaS_initial_conf__RL F_EPDA_TC__relation_effect__RL F_EPDA_TC__relation_epda__RL F_EPDA_TC__relation_epdaS_initial__LRRL F_EPDA_TC__relation_epdaS_step__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EPDA_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "epdaS_epdaS_F_EPDA_TC__StateSimRL" : ATS_Simulation_Configuration_WeakLR_FULL
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
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EPDA_TC__relation_epdaS_conf__RL"
  (* relation_initial_configuration *)
  "F_EPDA_TC__relation_epdaS_initial_conf__RL"
  (* relation_effect *)
  "F_EPDA_TC__relation_effect__RL"
  (* relation_TSstructure *)
  "F_EPDA_TC__relation_epda__RL"
  (* relation_initial_simulation *)
  "F_EPDA_TC__relation_epdaS_initial__LRRL"
  (* relation_step_simulation *)
  "F_EPDA_TC__relation_epdaS_step__LRRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms )
  done

lemma F_EPDA_TC__preserves_lang2: "
  valid_pda G
  \<Longrightarrow> epdaS.marked_language G \<supseteq> epdaS.marked_language (F_EPDA_TC G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def epdaS_inst_lang_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_EPDA_TC G)"
      and s="epdaS.finite_marked_language (F_EPDA_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply(subgoal_tac "valid_pda (F_EPDA_TC G)")
    prefer 2
    apply(rule F_EPDA_TC__preserves__valid_pda)
    apply(force)
   apply(simp add: valid_pda_def)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EPDA_TC__relation_effect__RL SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in epdaS_epdaS_F_EPDA_TC__StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__RL_def)
  done

lemma F_EPDA_TC__preserves_unmarked_language2: "
  valid_pda G
  \<Longrightarrow> epdaS.unmarked_language G \<supseteq> epdaS.unmarked_language (F_EPDA_TC G)"
  apply(rule_tac
      t="epdaS.unmarked_language G"
      and s="epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def epdaS_inst_AX_unmarked_language_finite n_not_Suc_n)
  apply(rule_tac
      t="epdaS.unmarked_language (F_EPDA_TC G)"
      and s="epdaS.finite_unmarked_language (F_EPDA_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply(subgoal_tac "valid_pda (F_EPDA_TC G)")
    prefer 2
    apply(rule F_EPDA_TC__preserves__valid_pda)
    apply(force)
   apply(simp add: valid_pda_def)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EPDA_TC__relation_effect__RL SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in epdaS_epdaS_F_EPDA_TC__StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_EPDA_TC__relation_epda__RL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EPDA_TC__relation_effect__RL_def)
  done

theorem F_EPDA_TC__preserves_lang: "
  valid_pda G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_EPDA_TC G)"
  apply(rule order_antisym)
   apply (metis F_EPDA_TC__preserves_lang1)
  apply (metis F_EPDA_TC__preserves_lang2)
  done

theorem F_EPDA_TC__preserves_unmarked_language: "
  valid_pda G
  \<Longrightarrow> epdaS.unmarked_language G = epdaS.unmarked_language (F_EPDA_TC G)"
  apply(rule order_antisym)
   apply (metis F_EPDA_TC__preserves_unmarked_language1)
  apply (metis F_EPDA_TC__preserves_unmarked_language2)
  done

lemma F_EPDA_TC__preserves_derivation: "
  valid_dpda G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> epdaS.derivation_initial (F_EPDA_TC G) (\<lambda>n. case d n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair (case e of None \<Rightarrow> None | Some e' \<Rightarrow> Some (F_EPDA_TC__edge__LR G e')) (F_EPDA_TC__epdaS_conf__LR G c)))"
  apply(simp add: epdaS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(rule F_EPDA_TC__preserves__epdaS_initial_configurations)
    apply(rename_tac b)(*strict*)
    apply(simp add: F_EPDA_TC__relation_epda__LR_def)
    apply(simp add: valid_dpda_def)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(case_tac ia)
   apply(rename_tac ia)(*strict*)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
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
  apply(rule F_EPDA_TC__preserves__simulation_step)
  apply(force)
  done

theorem F_EPDA_TC__preserves_coblockbreeness: "
  valid_dpda G
  \<Longrightarrow> epdaS.accessible G
  \<Longrightarrow> epdaS.accessible (F_EPDA_TC G)"
  apply(simp add: epdaS.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaS.get_accessible_destinations_def epda_destinations_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(thin_tac "edge ` epda_delta G \<subseteq> {x. ((x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and> (\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>i e c. d i = Some (pair e c) \<and> x \<in> epdaS_get_destinations G (pair e c))))}")
   apply(rename_tac xa)(*strict*)
   apply(simp add: epdaS_get_destinations_def)
   apply(subgoal_tac "xa \<in> (SOME f. inj_on f (epda_states G)) ` epda_states G")
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(simp add: F_EPDA_TC_def F_EPDA_TC__epda_def)
   apply(rename_tac xa)(*strict*)
   apply(thin_tac "xa \<in> epda_states (F_EPDA_TC G)")
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "epda_destinations.state x \<in> {x. ((x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and> (\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>i e c. d i = Some (pair e c) \<and> (x = epda_destinations.state (epdaS_conf_state c) \<or> x \<in> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'})))))}")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule_tac
      A="epda_destinations.state ` epda_states G"
      in set_mp)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "epda_destinations.state ` epda_states G \<subseteq> {x. ((x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and> (\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>i e c. d i = Some (pair e c) \<and> (x = epda_destinations.state (epdaS_conf_state c) \<or> x \<in> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'})))))}")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d i e c)(*strict*)
   apply(erule disjE)
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
   apply(rule_tac
      x=" \<lambda>n. case d n of None \<Rightarrow> None| Some (pair e c) \<Rightarrow> Some (pair (case e of None \<Rightarrow> None | Some e' \<Rightarrow> Some (F_EPDA_TC__edge__LR G e')) (F_EPDA_TC__epdaS_conf__LR G c)) "
      in exI)
   apply(rename_tac d i e c)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e c)(*strict*)
    prefer 2
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="(case e of None \<Rightarrow> None | Some e' \<Rightarrow> Some (F_EPDA_TC__edge__LR G e'))"
      in exI)
    apply(rule_tac
      x="(F_EPDA_TC__epdaS_conf__LR G c)"
      in exI)
    apply(clarsimp)
    apply(simp add: F_EPDA_TC__epdaS_conf__LR_def F_EPDA_TC__epdaS_conf1__LR_def)
   apply(rename_tac d i e c)(*strict*)
   apply(rule F_EPDA_TC__preserves_derivation)
     apply(rename_tac d i e c)(*strict*)
     apply(force)
    apply(rename_tac d i e c)(*strict*)
    apply(force)
   apply(rename_tac d i e c)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "epda_destinations.state ` epda_states G \<subseteq> {x. ((x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and> (\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>i e c. d i = Some (pair e c) \<and> x \<in> epdaS_get_destinations G (pair e c))))}")
  apply(rename_tac xa)(*strict*)
  apply(simp add: epdaS_get_destinations_def)
  apply(subgoal_tac "xa \<in> F_EPDA_TC__edge (SOME f. inj_on f (epda_states G)) (SOME f. inj_on f (epda_gamma G)) ` epda_delta G")
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(simp add: F_EPDA_TC_def F_EPDA_TC__epda_def)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "xa \<in> epda_delta (F_EPDA_TC G)")
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "edge x \<in> {x. ((x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and> (\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>i e c. d i = Some (pair e c) \<and> (x = epda_destinations.state (epdaS_conf_state c) \<or> x \<in> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'})))))}")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      A="edge ` epda_delta G"
      in set_mp)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "edge ` epda_delta G \<subseteq> {x. ((x \<in> epda_destinations.state ` epda_states G \<or> x \<in> edge ` epda_delta G) \<and> (\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>i e c. d i = Some (pair e c) \<and> (x = epda_destinations.state (epdaS_conf_state c) \<or> x \<in> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {edge e'})))))}")
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a)(*strict*)
  apply(rule_tac
      x=" \<lambda>n. case d n of None \<Rightarrow> None| Some (pair e c) \<Rightarrow> Some (pair (case e of None \<Rightarrow> None | Some e' \<Rightarrow> Some (F_EPDA_TC__edge__LR G e')) (F_EPDA_TC__epdaS_conf__LR G c)) "
      in exI)
  apply(rename_tac d i c a)(*strict*)
  apply(rule conjI)
   apply(rename_tac d i c a)(*strict*)
   prefer 2
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="(case (Some a) of None \<Rightarrow> None | Some e' \<Rightarrow> Some (F_EPDA_TC__edge__LR G e'))"
      in exI)
   apply(rule conjI)
    apply(rename_tac d i c a)(*strict*)
    apply(rule_tac
      x="(F_EPDA_TC__epdaS_conf__LR G c)"
      in exI)
    apply(clarsimp)
   apply(rename_tac d i c a)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__edge__LR_def)
  apply(rename_tac d i c a)(*strict*)
  apply(rule F_EPDA_TC__preserves_derivation)
    apply(rename_tac d i c a)(*strict*)
    apply(force)
   apply(rename_tac d i c a)(*strict*)
   apply(force)
  apply(rename_tac d i c a)(*strict*)
  apply(force)
  done

interpretation "epdaH_epdaH_Derivation_Map" : ATS_Derivation_Map
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaH_configurations"
  (* initial_configurations1 *)
  "epdaH_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaH_step_relation"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaH_configurations"
  (* initial_configurations2 *)
  "epdaH_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaH_step_relation"
  (* gen_rel *)
  "(\<lambda>G1 G2. G1=F_EPDA_TC G2)"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  done

definition F_EPDA_TC__epdaS_conf1__LRRevH :: "
  ('stateB DT_symbol \<Rightarrow> 'stateA)
  \<Rightarrow> ('stackB DT_symbol \<Rightarrow> 'stackA)
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaH_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaH_conf"
  where
    "F_EPDA_TC__epdaS_conf1__LRRevH fq fg c \<equiv>
  \<lparr>epdaH_conf_state = fq (epdaH_conf_state c),
  epdaH_conf_history = epdaH_conf_history c,
  epdaH_conf_stack = map fg (epdaH_conf_stack c)\<rparr>"

definition F_EPDA_TC__epdaS_conf__LRRevH :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaH_conf
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaH_conf"
  where
    "F_EPDA_TC__epdaS_conf__LRRevH G c \<equiv>
  F_EPDA_TC__epdaS_conf1__LRRevH
    (inv_into (epda_states G) (SOME f. inj_on f (epda_states G)))
    (inv_into (epda_gamma G) (SOME f. inj_on f (epda_gamma G)))
    c"

theorem F_EPDA_TC__preserves_epdaH_no_livelocks_from_marking_states: "
  valid_dpda G
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states G
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states (F_EPDA_TC G)"
  apply(simp add: epdaH_no_livelocks_from_marking_states_def)
  apply(clarsimp)
  apply(rename_tac d n e c)(*strict*)
  apply(subgoal_tac "\<exists>f. inj_on f (epda_states G) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (epda_states G))")
   apply(rename_tac d n e c)(*strict*)
   prefer 2
   apply(rule exists_SOME_injective_is_injective)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n e c)(*strict*)
   prefer 2
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(simp add: valid_dpda_def)
   apply(force)
  apply(rename_tac d n e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n e c)(*strict*)
   prefer 2
   apply(rule_tac
      fe="\<lambda>G1 G2 e. F_EPDA_TC__edge__RL G2 e"
      and fc="\<lambda>G1 G2 c. F_EPDA_TC__epdaS_conf__LRRevH G2 c"
      and ?G2.0="G"
      in epdaH_epdaH_Derivation_Map.der_map_preserves_derivation_initial)
        apply(rename_tac d n e c)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac d n e c)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(force)
      apply(rename_tac d n e c)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d n e c)(*strict*)
     apply(force)
    apply(rename_tac d n e c)(*strict*)
    apply(simp add: epdaH_epdaH_Derivation_Map.der_map_preserves_steps_def)
    apply(clarsimp)
    apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(rule conjI)
     apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
     prefer 2
     apply(case_tac c1)
     apply(rename_tac d n e c G2 c1 ea c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
     apply(case_tac c2)
     apply(rename_tac d n e c G2 c1 ea c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
     apply(case_tac ea)
     apply(rename_tac d n e c G2 c1 ea c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n e c G2 epdaH_conf_historya edge_srca edge_eventa edge_popa edge_pusha edge_trga w)(*strict*)
     apply(rename_tac h qs r po pus qt w)
     apply(rename_tac d n e c G2 h qs r po pus qt w)(*strict*)
     apply(simp add: F_EPDA_TC__epdaS_conf__LRRevH_def F_EPDA_TC__epdaS_conf1__LRRevH_def F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def)
    apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
     prefer 2
     apply(rule_tac
      e="ea"
      and G="G2"
      in F_EPDA_TC__edge__RL__preserves__epda_delta)
      apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
     apply(force)
    apply(rename_tac d n e c G2 c1 ea c2)(*strict*)
    apply(force)
   apply(rename_tac d n e c)(*strict*)
   apply(simp add: epdaH_epdaH_Derivation_Map.der_map_preserves_configurations_initial_def)
   apply(clarsimp)
   apply(rename_tac d n e c G2 ca)(*strict*)
   apply(subgoal_tac "\<exists>f. inj_on f (epda_gamma G2) \<and> f = (SOME f::'c\<Rightarrow>'e DT_symbol. inj_on f (epda_gamma G2))")
    apply(rename_tac d n e c G2 ca)(*strict*)
    prefer 2
    apply(rule exists_SOME_injective_is_injective)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d n e c G2 ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>f. inj_on f (epda_states G2) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (epda_states G2))")
    apply(rename_tac d n e c G2 ca)(*strict*)
    prefer 2
    apply(rule exists_SOME_injective_is_injective)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d n e c G2 ca)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__epdaS_conf__LRRevH_def F_EPDA_TC__epdaS_conf1__LRRevH_def F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def epdaH_initial_configurations_def epdaH_configurations_def F_EPDA_TC_def F_EPDA_TC__epda_def)
   apply(rule_tac
      t="inv_into (epda_gamma G2) (SOME f. inj_on f (epda_gamma G2)) ((SOME f. inj_on f (epda_gamma G2)) (epda_box G2))"
      and s="epda_box G2"
      in ssubst)
    apply(rename_tac d n e c G2 ca)(*strict*)
    apply(rule Hilbert_Choice.inv_into_f_f)
     apply(rename_tac d n e c G2 ca)(*strict*)
     apply(force)
    apply(rename_tac d n e c G2 ca)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d n e c G2 ca)(*strict*)
   apply(rule_tac
      t="inv_into (epda_states G2) (SOME f. inj_on f (epda_states G2)) ((SOME f. inj_on f (epda_states G2)) (epda_initial G2))"
      in ssubst)
    apply(rename_tac d n e c G2 ca)(*strict*)
    apply(rule Hilbert_Choice.inv_into_f_f)
     apply(rename_tac d n e c G2 ca)(*strict*)
     apply(force)
    apply(rename_tac d n e c G2 ca)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d n e c G2 ca)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d n e c)(*strict*)
  apply(erule_tac
      x="epdaH_epdaH_Derivation_Map.der_map (F_EPDA_TC G) G (\<lambda>G1. F_EPDA_TC__edge__RL) (\<lambda>G1. F_EPDA_TC__epdaS_conf__LRRevH) d"
      in allE)
  apply(rename_tac d n e c)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(erule impE)
   apply(rename_tac d n e c)(*strict*)
   apply(rule conjI)
    apply(rename_tac d n e c)(*strict*)
    apply(force)
   apply(rename_tac d n e c)(*strict*)
   apply(simp add: epdaH_epdaH_Derivation_Map.der_map_def)
   apply(simp add: F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def)
   apply(simp add: F_EPDA_TC_def F_EPDA_TC__epda_def)
   apply(clarsimp)
   apply(rename_tac d n e c x)(*strict*)
   apply(rule_tac
      t="inv_into (epda_states G) (SOME f. inj_on f (epda_states G)) ((SOME f. inj_on f (epda_states G)) x)"
      and s="x"
      in ssubst)
    apply(rename_tac d n e c x)(*strict*)
    apply(rule Hilbert_Choice.inv_into_f_f)
     apply(rename_tac d n e c x)(*strict*)
     apply(force)
    apply(rename_tac d n e c x)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(rename_tac d n e c x)(*strict*)
   apply(force)
  apply(rename_tac d n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e c m)(*strict*)
  apply(erule disjE)
   apply(rename_tac d n e c m)(*strict*)
   apply(rule_tac
      x="m"
      in exI)
   apply(rule conjI)
    apply(rename_tac d n e c m)(*strict*)
    apply(force)
   apply(rename_tac d n e c m)(*strict*)
   apply(rule disjI1)
   apply(simp add: epdaH_epdaH_Derivation_Map.der_map_def)
   apply(case_tac "d m")
    apply(rename_tac d n e c m)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n e c m a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d n e c m a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n e c m)(*strict*)
  apply(rule_tac
      x="m"
      in exI)
  apply(rule conjI)
   apply(rename_tac d n e c m)(*strict*)
   apply(force)
  apply(rename_tac d n e c m)(*strict*)
  apply(rule disjI2)
  apply(simp add: epdaH_epdaH_Derivation_Map.der_map_def)
  apply(clarsimp)
  apply(rename_tac d n e c m e' c' y)(*strict*)
  apply(case_tac "d m")
   apply(rename_tac d n e c m e' c' y)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n e c m e' c' y a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n e c m e' c' y a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e c m e' y option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac d n e c m e' y option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n e c m e' y option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e c m y b a)(*strict*)
  apply(simp add: F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def)
  done

theorem F_EPDA_TC__preserves_no_livelock: "
  valid_pda G
  \<Longrightarrow> \<not> epdaH_livelock G
  \<Longrightarrow> \<not> epdaH_livelock (F_EPDA_TC G)"
  apply(simp add: epdaH_livelock_def)
  apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(subgoal_tac "\<exists>f. inj_on f (epda_states G) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (epda_states G))")
   apply(rename_tac d N)(*strict*)
   prefer 2
   apply(rule exists_SOME_injective_is_injective)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d N)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d N)(*strict*)
   prefer 2
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(simp add: valid_dpda_def)
  apply(rename_tac d N)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d N)(*strict*)
   prefer 2
   apply(rule_tac
      fe="\<lambda>G1 G2 e. F_EPDA_TC__edge__RL G2 e"
      and fc="\<lambda>G1 G2 c. F_EPDA_TC__epdaS_conf__LRRevH G2 c"
      and ?G2.0="G"
      in epdaH_epdaH_Derivation_Map.der_map_preserves_derivation_initial)
        apply(rename_tac d N)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac d N)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac d)(*strict*)
       apply(force)
      apply(rename_tac d N)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d N)(*strict*)
     apply(force)
    apply(rename_tac d N)(*strict*)
    apply(simp add: epdaH_epdaH_Derivation_Map.der_map_preserves_steps_def)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(rename_tac d G2 c1 e c2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(rule conjI)
     apply(rename_tac d G2 c1 e c2)(*strict*)
     prefer 2
     apply(case_tac c1)
     apply(rename_tac d G2 c1 e c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
     apply(case_tac c2)
     apply(rename_tac d G2 c1 e c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
     apply(case_tac e)
     apply(rename_tac d G2 c1 e c2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac d G2 epdaH_conf_historya edge_srca edge_eventa edge_popa edge_pusha edge_trga w)(*strict*)
     apply(rename_tac h qs r po pus qt w)
     apply(rename_tac d G2 h qs r po pus qt w)(*strict*)
     apply(simp add: F_EPDA_TC__epdaS_conf__LRRevH_def F_EPDA_TC__epdaS_conf1__LRRevH_def F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def)
    apply(rename_tac d G2 c1 e c2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d G2 c1 e c2)(*strict*)
     prefer 2
     apply(rule_tac
      e="e"
      and G="G2"
      in F_EPDA_TC__edge__RL__preserves__epda_delta)
      apply(rename_tac d G2 c1 e c2)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac d G2 c1 e c2)(*strict*)
     apply(force)
    apply(rename_tac d G2 c1 e c2)(*strict*)
    apply(force)
   apply(rename_tac d N)(*strict*)
   apply(simp add: epdaH_epdaH_Derivation_Map.der_map_preserves_configurations_initial_def)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(rename_tac d G2 c)(*strict*)
   apply(subgoal_tac "\<exists>f. inj_on f (epda_gamma G2) \<and> f = (SOME f::'c\<Rightarrow>'e DT_symbol. inj_on f (epda_gamma G2))")
    apply(rename_tac d G2 c)(*strict*)
    prefer 2
    apply(rule exists_SOME_injective_is_injective)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d G2 c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>f. inj_on f (epda_states G2) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (epda_states G2))")
    apply(rename_tac d G2 c)(*strict*)
    prefer 2
    apply(rule exists_SOME_injective_is_injective)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d G2 c)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__epdaS_conf__LRRevH_def F_EPDA_TC__epdaS_conf1__LRRevH_def F_EPDA_TC__edge__RL_def F_EPDA_TC__edge1__RL_def epdaH_initial_configurations_def epdaH_configurations_def F_EPDA_TC_def F_EPDA_TC__epda_def)
   apply(rule_tac
      t="inv_into (epda_gamma G2) (SOME f. inj_on f (epda_gamma G2)) ((SOME f. inj_on f (epda_gamma G2)) (epda_box G2))"
      and s="epda_box G2"
      in ssubst)
    apply(rename_tac d G2 c)(*strict*)
    apply(rule Hilbert_Choice.inv_into_f_f)
     apply(rename_tac d G2 c)(*strict*)
     apply(force)
    apply(rename_tac d G2 c)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d G2 c)(*strict*)
   apply(rule_tac
      t="inv_into (epda_states G2) (SOME f. inj_on f (epda_states G2)) ((SOME f. inj_on f (epda_states G2)) (epda_initial G2))"
      in ssubst)
    apply(rename_tac d G2 c)(*strict*)
    apply(rule Hilbert_Choice.inv_into_f_f)
     apply(rename_tac d G2 c)(*strict*)
     apply(force)
    apply(rename_tac d G2 c)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d G2 c)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="epdaH_epdaH_Derivation_Map.der_map (F_EPDA_TC G) G (\<lambda>G1. F_EPDA_TC__edge__RL) (\<lambda>G1. F_EPDA_TC__epdaS_conf__LRRevH) d"
      in allE)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac d N)(*strict*)
   apply(clarsimp)
   apply(rename_tac d N n)(*strict*)
   apply(simp add: epdaH_epdaH_Derivation_Map.der_map_def)
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
   apply(clarsimp)
  apply(rename_tac d N)(*strict*)
  apply(erule_tac
      x="N"
      and P="\<lambda>N. \<exists>n\<ge>N. epdaH_conf_history (the (get_configuration (epdaH_epdaH_Derivation_Map.der_map (F_EPDA_TC G) G (\<lambda>G1. F_EPDA_TC__edge__RL) (\<lambda>G1. F_EPDA_TC__epdaS_conf__LRRevH) d n))) \<noteq> epdaH_conf_history (the (get_configuration (epdaH_epdaH_Derivation_Map.der_map (F_EPDA_TC G) G (\<lambda>G1. F_EPDA_TC__edge__RL) (\<lambda>G1. F_EPDA_TC__epdaS_conf__LRRevH) d N)))"
      in allE)
  apply(rename_tac d N)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(simp add: epdaH_epdaH_Derivation_Map.der_map_def get_configuration_def)
  apply(erule_tac x="n" in allE')
  apply(erule_tac
      x="N"
      in allE)
  apply(clarsimp)
  apply(rename_tac d N n y ya)(*strict*)
  apply(case_tac y)
  apply(rename_tac d N n y ya option b)(*strict*)
  apply(case_tac ya)
  apply(rename_tac d N n y ya option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d N n option b optiona ba)(*strict*)
  apply(simp add: F_EPDA_TC__epdaS_conf__LRRevH_def F_EPDA_TC__epdaS_conf1__LRRevH_def)
  done

definition F_EPDA_TC__isom_relation_step_label__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__isom_relation_step_label__LR G1 G2 p1 p2 \<equiv>
  p1 \<in> epda_delta G1
  \<and> p2 \<in> epda_delta G2
  \<and> F_EPDA_TC__edge__LR G1 p1 = p2"

definition F_EPDA_TC__isom_relation_conf__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<equiv>
  c1 \<in> epdaS_configurations G1
  \<and> c2 \<in> epdaS_configurations G2
  \<and> c2 = F_EPDA_TC__epdaS_conf__LR G1 c1"

definition F_EPDA_TC__isom_relation_initial_conf__LR :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> ('stateA, 'event, 'stackA) epdaS_conf
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__isom_relation_initial_conf__LR G1 G2 c1 c2 \<equiv>
  c1 \<in> epdaS_initial_configurations G1
  \<and> c2 \<in> epdaS_initial_configurations G2
  \<and> c2 = F_EPDA_TC__epdaS_conf__LR G1 c1"

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_TSstructure_closed1: "
  (\<forall>G1. Ex (F_EPDA_TC__relation_epda__LR G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_pda_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_TSstructure_closed2: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_pda_def)
  apply (metis F_EPDA_TC__preserves__valid_pda valid_pda_def One_nat_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_closed1: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1. Ex (F_EPDA_TC__isom_relation_conf__LR G1 G2 c1) \<longrightarrow> c1 \<in> epdaS_configurations G1))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 x)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_closed2: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<longrightarrow> c2 \<in> epdaS_configurations G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_for_initial_closed1: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<longrightarrow> c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> c2 \<in> epdaS_initial_configurations G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(metis F_EPDA_TC__preserves__epdaS_initial_configurations F_EPDA_TC__relation_epda__LR_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_for_initial_closed2: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<longrightarrow> c2 \<in> epdaS_initial_configurations G2 \<longrightarrow> c1 \<in> epdaS_initial_configurations G1))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply (metis (poly_guards_query) F_EPDA_TC__epdaS_conf__LR_reverse2 F_EPDA_TC__C_rev_preserves_initial_configurations F_EPDA_TC__relation_epda__RL_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_label_closed1: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>e1. Ex (F_EPDA_TC__isom_relation_step_label__LR G1 G2 e1) \<longrightarrow> e1 \<in> epda_step_labels G1))"
  apply(clarsimp)
  apply(rename_tac G1 G2 e1 x)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def epda_step_labels_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_label_closed2: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>e1 e2. F_EPDA_TC__isom_relation_step_label__LR G1 G2 e1 e2 \<longrightarrow> e2 \<in> epda_step_labels G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 e1 e2)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def epda_step_labels_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_bijection_on: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> bijection_on (F_EPDA_TC__isom_relation_conf__LR G1 G2) (epdaS_configurations G1) (epdaS_configurations G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(rule bijection_on_intro)
     apply(rename_tac G1 G2)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 a)(*strict*)
     apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
     apply(clarsimp)
     apply(rename_tac G1 a)(*strict*)
     apply (metis (mono_tags, hide_lams) F_EPDA_TC__preserves__epdaS_configurations F_EPDA_TC__relation_epda__LR_def)
    apply(rename_tac G1 G2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 b)(*strict*)
    apply(simp add: F_EPDA_TC__relation_epda__LR_def F_EPDA_TC__isom_relation_conf__LR_def)
    apply(clarsimp)
    apply(rename_tac G1 b)(*strict*)
    apply(rule_tac
      x="F_EPDA_TC__epdaS_conf__LRRev G1 b"
      in bexI)
     apply(rename_tac G1 b)(*strict*)
     apply (metis F_EPDA_TC__epdaS_conf__LR_reverse)
    apply(rename_tac G1 b)(*strict*)
    apply (metis F_EPDA_TC__C_rev_preserves_configurations F_EPDA_TC__relation_epda__RL_def)
   apply(rename_tac G1 G2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 a b1 b2)(*strict*)
   apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def)
  apply(rename_tac G1 G2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 b a1 a2)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 a1 a2)(*strict*)
  apply (metis F_EPDA_TC__epdaS_conf__LR_reverse2 F_EPDA_TC__relation_epda__LR_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_label_bijection_on: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> bijection_on (F_EPDA_TC__isom_relation_step_label__LR G1 G2) (epda_step_labels G1) (epda_step_labels G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(rule bijection_on_intro)
     apply(rename_tac G1 G2)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 a)(*strict*)
     apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def F_EPDA_TC__relation_epda__LR_def epda_step_labels_def F_EPDA_TC_def F_EPDA_TC__epda_def F_EPDA_TC__edge__LR_def)
    apply(rename_tac G1 G2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 b)(*strict*)
    apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def F_EPDA_TC__relation_epda__LR_def epda_step_labels_def)
    apply(clarsimp)
    apply(rename_tac G1 b)(*strict*)
    apply(rule_tac
      x="F_EPDA_TC__edge__RL G1 b"
      in bexI)
     apply(rename_tac G1 b)(*strict*)
     prefer 2
     apply (metis F_EPDA_TC__edge__RL__preserves__epda_delta valid_pda_def)
    apply(rename_tac G1 b)(*strict*)
    apply(simp add: F_EPDA_TC_def F_EPDA_TC__epda_def)
    apply(clarsimp)
    apply(rename_tac G1 x)(*strict*)
    apply(rule_tac
      t="F_EPDA_TC__edge__RL G1 (F_EPDA_TC__edge (SOME f. inj_on f (epda_states G1)) (SOME f. inj_on f (epda_gamma G1)) x)"
      and s="x"
      in ssubst)
     apply(rename_tac G1 x)(*strict*)
     apply(rule F_EPDA_TC__edge_reversal)
      apply(rename_tac G1 x)(*strict*)
      apply(simp add: valid_pda_def)
     apply(rename_tac G1 x)(*strict*)
     apply(force)
    apply(rename_tac G1 x)(*strict*)
    apply(simp add: F_EPDA_TC__edge__LR_def)
   apply(rename_tac G1 G2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 a b1 b2)(*strict*)
   apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 a1 a2)(*strict*)
  apply (metis F_EPDA_TC__edge__LR_def F_EPDA_TC__edge_reversal epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_marking_configuration1_equivalent: "
  (\<forall>G1. valid_epda G1 \<longrightarrow> (\<forall>d1. epdaS.derivation_initial G1 d1 \<longrightarrow> epdaS_marking_condition G1 d1 = (\<exists>i c1. get_configuration (d1 i) = Some c1 \<and> c1 \<in> epdaS_marking_configurations G1)))"
  apply(clarsimp)
  apply(rename_tac G1 d1)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(rule antisym)
   apply(rename_tac G1 d1)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d1 i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d1 i c1)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: get_configuration_def)
  apply(case_tac "d1 i")
   apply(rename_tac G1 d1 i c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d1 i c1 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G1 d1 i c1 a option conf)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_preserves_marking_configuration: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<longrightarrow> (c1 \<in> epdaS_marking_configurations G1) = (c2 \<in> epdaS_marking_configurations G2)))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(rule antisym)
   apply(rename_tac G1 G2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def)
   apply (metis F_EPDA_TC__preserves__epdaS_marking_configurations)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: F_EPDA_TC__isom_relation_conf__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply (metis F_EPDA_TC__epdaS_conf__LR_reverse2 F_EPDA_TC__C_rev_preserves_marking_configurations F_EPDA_TC__relation_epda__LR_def F_EPDA_TC__relation_epda__RL_def)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_step_preservation1: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1 c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>e2. F_EPDA_TC__isom_relation_step_label__LR G1 G2 e1 e2 \<longrightarrow> (\<forall>c2'. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1' c2' \<longrightarrow> epdaS_step_relation G2 c2 e2 c2')))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' e2 c2')(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def F_EPDA_TC__isom_relation_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule F_EPDA_TC__preserves__simulation_step)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_step_preservation2: "
  (\<forall>G1 G2. F_EPDA_TC__relation_epda__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e2 c2'. epdaS_step_relation G2 c2 e2 c2' \<longrightarrow> (\<forall>e1. F_EPDA_TC__isom_relation_step_label__LR G1 G2 e1 e2 \<longrightarrow> (\<forall>c1'. F_EPDA_TC__isom_relation_conf__LR G1 G2 c1' c2' \<longrightarrow> epdaS_step_relation G1 c1 e1 c1')))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e2 c2' e1 c1')(*strict*)
  apply(simp add: F_EPDA_TC__isom_relation_step_label__LR_def F_EPDA_TC__isom_relation_conf__LR_def F_EPDA_TC__relation_epda__LR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   prefer 2
   apply(rule F_EPDA_TCRev_preserves_step_relation)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: F_EPDA_TC__relation_epda__RL_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      t="c1"
      and s="(F_EPDA_TC__epdaS_conf__LRRev G1 (F_EPDA_TC__epdaS_conf__LR G1 c1))"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (rule F_EPDA_TC__epdaS_conf__LR_reverse2)
    apply(force)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      t="c1'"
      and s="(F_EPDA_TC__epdaS_conf__LRRev G1 (F_EPDA_TC__epdaS_conf__LR G1 c1'))"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (rule F_EPDA_TC__epdaS_conf__LR_reverse2)  
    apply(force)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      t="e1"
      and s="(F_EPDA_TC__edge__RL G1 (F_EPDA_TC__edge__LR G1 e1))"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: F_EPDA_TC__edge1__RL_def F_EPDA_TC__isom_relation_step_label__LR_def F_EPDA_TC__relation_epda__LR_def epda_step_labels_def F_EPDA_TC_def F_EPDA_TC__epda_def F_EPDA_TC__edge__LR_def)
   apply(rule sym)
   apply(rule F_EPDA_TC__edge_reversal)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: valid_pda_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_F_EPDA_TC__ISOM_inst_ATS_Isomorphism_axioms: "
  ATS_Isomorphism_axioms valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition (\<lambda>G c. c \<in> epdaS_marking_configurations G) (\<lambda>G c. c \<in> epdaS_marking_configurations G) F_EPDA_TC__relation_epda__LR F_EPDA_TC__isom_relation_conf__LR F_EPDA_TC__isom_relation_step_label__LR"
  apply(simp add: ATS_Isomorphism_axioms_def)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_TSstructure_closed1 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_TSstructure_closed2 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_closed1 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_closed2 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_for_initial_closed1 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_for_initial_closed2 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_label_closed1 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_label_closed2 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_bijection_on epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_label_bijection_on epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_marking_configuration1_equivalent epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_relation_configuration_preserves_marking_configuration epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_step_preservation1 epdaS_epdaS_F_EPDA_TC__ISOM_inst_AX_step_preservation2 )
  done

interpretation "epdaS_epdaS_F_EPDA_TC__ISOM" : ATS_Isomorphism
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
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* marking_configuration1 *)
  "(\<lambda>G c. c \<in> epdaS_marking_configurations G)"
  (* marking_configuration2 *)
  "(\<lambda>G c. c \<in> epdaS_marking_configurations G)"
  (* relation_TSstructure *)
  "F_EPDA_TC__relation_epda__LR"
  (* relation_configuration *)
  "F_EPDA_TC__isom_relation_conf__LR"
  (* relation_label *)
  "F_EPDA_TC__isom_relation_step_label__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EPDA_TC__ISOM_inst_ATS_Isomorphism_axioms)
  done

theorem F_EPDA_TC__preserves_DPDA: "
  valid_dpda G
  \<Longrightarrow> valid_dpda (F_EPDA_TC G)"
  apply(simp add: valid_dpda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule F_EPDA_TC__preserves__valid_pda)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      and ?G2.0="F_EPDA_TC G"
      in epdaS_epdaS_F_EPDA_TC__ISOM.is_forward_edge_deterministic_accessible_preservation)
    apply(simp add: F_EPDA_TC__relation_epda__LR_def)
   apply(force)
  apply(force)
  done

definition F_EPDA_TC__SpecInput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__SpecInput G \<equiv>
  valid_dpda G"

definition F_EPDA_TC__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> (\<not> epdaH_livelock Gi \<longrightarrow> \<not> epdaH_livelock Go)
  \<and> epdaS.unmarked_language Gi = epdaS.unmarked_language Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> (epdaH_no_livelocks_from_marking_states Gi \<longrightarrow> epdaH_no_livelocks_from_marking_states Go)
  \<and> (epdaS.accessible Gi \<longrightarrow> epdaS.accessible Go)"

theorem F_EPDA_TC__SOUND: "
  F_EPDA_TC__SpecInput G
  \<Longrightarrow> F_EPDA_TC__SpecOutput G (F_EPDA_TC G)"
  apply(simp add: F_EPDA_TC__SpecOutput_def F_EPDA_TC__SpecInput_def)
  apply(rule conjI)
   apply(simp add:
      F_EPDA_TC__preserves_DPDA)
  apply(rule conjI)
   apply(rule impI)
   apply(rule F_EPDA_TC__preserves_no_livelock)
    apply(simp add: valid_dpda_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_EPDA_TC__preserves_unmarked_language)
   apply(simp add: valid_dpda_def)
  apply(rule conjI)
   apply(rule F_EPDA_TC__preserves_lang)
   apply(simp add: valid_dpda_def)
  apply(rule conjI)
   apply(simp add: F_EPDA_TC__preserves_epdaH_no_livelocks_from_marking_states)
  apply(rule impI)
  apply(rule
      F_EPDA_TC__preserves_coblockbreeness)
   apply(force)
  apply(force)
  done

definition F_EPDA_TC__SpecInput2 :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__SpecInput2 G \<equiv>
  valid_dpda G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epdaS.accessible G
  \<and> epdaH_no_livelocks_from_marking_states G"

definition F_EPDA_TC__SpecOutput2 :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_TC__SpecOutput2 Gi Go \<equiv>
  valid_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epdaS.accessible Go
  \<and> epdaH_no_livelocks_from_marking_states Go"

theorem F_EPDA_TC__SOUND2: "
  F_EPDA_TC__SpecInput2 G
  \<Longrightarrow> F_EPDA_TC__SpecOutput2 G (F_EPDA_TC G)"
  apply(simp add: F_EPDA_TC__SpecInput2_def F_EPDA_TC__SpecOutput2_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule F_EPDA_TC__preserves_DPDA)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EPDA_TC__preserves_lang)
   apply(simp add: valid_dpda_def)
  apply(rule context_conjI)
   apply(rule_tac
      t="epdaS.unmarked_language (F_EPDA_TC G)"
      and s="epdaS.unmarked_language G"
      in subst)
    apply(rule F_EPDA_TC__preserves_unmarked_language)
    apply(simp add: valid_dpda_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_EPDA_TC__preserves_coblockbreeness)
    apply(force)
   apply(force)
  apply(rule F_EPDA_TC__preserves_epdaH_no_livelocks_from_marking_states)
   apply(force)
  apply(force)
  done

end
