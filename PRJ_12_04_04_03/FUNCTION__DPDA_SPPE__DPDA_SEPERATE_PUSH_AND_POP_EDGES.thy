section {*FUNCTION\_\_DPDA\_SPPE\_\_DPDA\_SEPERATE\_PUSH\_AND\_POP\_EDGES*}
theory
  FUNCTION__DPDA_SPPE__DPDA_SEPERATE_PUSH_AND_POP_EDGES

imports
  PRJ_12_04_04_03__ENTRY

begin

definition F_DPDA_SPPE__edge_else__LR :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_SPPE__edge_else__LR e \<equiv>
  \<lparr>edge_src = case edge_src e of cons_state_or_edge_old q \<Rightarrow> q,
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = case edge_trg e of cons_state_or_edge_old q \<Rightarrow> q\<rparr>"

definition F_DPDA_SPPE__edge_then_2__LR :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_SPPE__edge_then_2__LR e X \<equiv>
  \<lparr>edge_src = cons_state_or_edge_new e,
  edge_event = None,
  edge_pop = [X],
  edge_push = edge_push e @ [X],
  edge_trg = cons_state_or_edge_old (edge_trg e)\<rparr>"

lemma F_DPDA_SPPE__edge_then_2__LR_vs_F_DPDA_SPPE__edge_then_2: "
  F_DPDA_SPPE__edge_then_2 e S = (\<lambda>X. F_DPDA_SPPE__edge_then_2__LR e X) ` S"
  apply(simp add: F_DPDA_SPPE__edge_then_2__LR_def F_DPDA_SPPE__edge_then_2_def)
  apply(force)
  done

definition push_and_pop_edges_seperated :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "push_and_pop_edges_seperated G \<equiv>
  \<not> (\<exists>e \<in> epda_delta G. F_DPDA_SPPE__edge_if e)"

definition push_and_pop_edges_seperated_ALT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "push_and_pop_edges_seperated_ALT G \<equiv>
  \<not> (\<exists>e \<in> epda_delta G.
      edge_event e = None
      \<and> (\<exists>w b. edge_push e = w @ [b]
             \<and> edge_pop e \<noteq> [b]))"

lemma push_and_pop_edges_seperated_ALT_vs_push_and_pop_edges_seperated: "
  push_and_pop_edges_seperated_ALT G = push_and_pop_edges_seperated G"
  apply(simp add: push_and_pop_edges_seperated_ALT_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
  done

definition F_DPDA_SPPE__conf_old__LR :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_SPPE__conf_old__LR c \<equiv>
  \<lparr>epdaS_conf_state = cons_state_or_edge_old (epdaS_conf_state c),
  epdaS_conf_scheduler = epdaS_conf_scheduler c,
  epdaS_conf_stack = epdaS_conf_stack c\<rparr>"

definition F_DPDA_SPPE__conf_old__LR_rev :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_SPPE__conf_old__LR_rev c \<equiv>
  case epdaS_conf_state c of cons_state_or_edge_old q
  \<Rightarrow> \<lparr>epdaS_conf_state = q,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = epdaS_conf_stack c\<rparr>
  | cons_state_or_edge_new e
  \<Rightarrow> \<lparr>epdaS_conf_state = edge_trg e,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = edge_push e @ epdaS_conf_stack c\<rparr>"

lemma F_DPDA_SPPE__preserves_epda: "
  valid_dpda G
  \<Longrightarrow> valid_epda (F_DPDA_SPPE G)"
  apply(simp add: valid_epda_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_def valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_SPPE__edge_else_def)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G xa")
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
   apply(rename_tac xa)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G xa")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. edge_pop xa=[x]")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. length (edge_pop xa) = Suc 0"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    apply(case_tac "edge_pop xa")
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa a list)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_then_def)
  apply(erule disjE)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rule conjI)
    apply(rename_tac xa xb)(*strict*)
    apply(simp add: option_to_set_def)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac xa a aa ab)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
  apply(clarsimp)
  apply(rename_tac x xa xb)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_then_2_def)
  apply(clarsimp)
  apply(rename_tac xa xb X)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb X)(*strict*)
   apply(simp add: option_to_set_def)
  apply(rename_tac xa xb X)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb X)(*strict*)
   apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac xa xb X a aa)(*strict*)
   apply(case_tac "X=epda_box G")
    apply(rename_tac xa xb X a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(force)
   apply(rename_tac xa xb X a aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa xb X)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb X)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_if_def)
   apply(clarsimp)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac xa xb X w b a aa)(*strict*)
   apply(erule_tac
      P="[] = a \<and> set w \<subseteq> epda_gamma G - {epda_box G} \<and> b = epda_box G"
      in disjE)
    apply(rename_tac xa xb X w b a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa xb X w b a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac xa xb X w b a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa xb X w b a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(case_tac "X=epda_box G")
    apply(rename_tac xa xb X w b)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb w b)(*strict*)
    apply(rule_tac
      x="edge_push xa"
      in exI)
    apply(force)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(rule_tac
      x="w@[b,X]"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa xb X w b)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(rule_tac
      t="w@[b,X]"
      and s="edge_push xa@[X]"
      in ssubst)
    apply(rename_tac xa xb X w b)(*strict*)
    apply(force)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(rule set_concat_subset)
    apply(rename_tac xa xb X w b)(*strict*)
    apply(force)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(force)
  apply(rename_tac xa xb X)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(clarsimp)
  apply(rename_tac xa xb X w b)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="w@[b,X]"
      and s="edge_push xa@[X]"
      in ssubst)
    apply(rename_tac xa xb X w b)(*strict*)
    apply(force)
   apply(rename_tac xa xb X w b)(*strict*)
   apply(simp only: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac xa xb w b a aa)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa xb w b a aa)(*strict*)
    apply(rule_tac
      A="set(edge_push xa)"
      in set_mp)
     apply(rename_tac xa xb w b a aa)(*strict*)
     apply(force)
    apply(rename_tac xa xb w b a aa)(*strict*)
    apply(force)
   apply(rename_tac xa xb w b a aa)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa xb w b a aa)(*strict*)
    apply(erule_tac
      P="[] = a \<and> set w \<subseteq> epda_gamma G - {epda_box G} \<and> b = epda_box G"
      in disjE)
     apply(rename_tac xa xb w b a aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac xa xb w b a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb w aa x)(*strict*)
    apply(force)
   apply(rename_tac xa xb w b a aa)(*strict*)
   apply(force)
  apply(rename_tac xa xb X w b)(*strict*)
  apply(clarsimp)
  apply(simp only: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  done

lemma F_DPDA_SPPE__preserves_PDA: "
  valid_dpda G
  \<Longrightarrow> valid_pda (F_DPDA_SPPE G)"
  apply(simp add: valid_pda_def)
  apply(rule conjI)
   apply(rule F_DPDA_SPPE__preserves_epda)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: valid_epda_def valid_pda_def valid_dpda_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(erule disjE)
    apply(rename_tac e x)(*strict*)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(clarsimp)
  done

theorem F_DPDA_SPPE__preserves_read_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> read_edges_seperated (F_DPDA_SPPE G)"
  apply(simp add: read_edges_seperated_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: FB_neutral_edge_def FB_executing_edge_def F_DPDA_SPPE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac e x y)(*strict*)
   apply(erule disjE)
    apply(rename_tac e x y)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac e x y)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(simp add: FB_executing_edge_def)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(simp add: strict_executing_edge_def F_DPDA_SEE__edge_else_def FB_executing_edge_def empty_push_edge_def multiple_push_edge_def)
  done

theorem F_DPDA_SPPE__preserves_neutral_edges_removed: "
  valid_dpda G
  \<Longrightarrow> neutral_edges_removed G
  \<Longrightarrow> neutral_edges_removed (F_DPDA_SPPE G)"
  apply(simp add: neutral_edges_removed_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "edge_pop x \<noteq> []")
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule disjE)
     apply(rename_tac x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa)(*strict*)
     apply(erule_tac
      x="xa"
      in ballE)
      apply(rename_tac xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac xa)(*strict*)
     apply(simp add: FB_neutral_edge_def F_DPDA_SPPE__edge_if_def)
     apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(rename_tac x xa)(*strict*)
    apply(erule_tac
      x="xa"
      in ballE)
     apply(rename_tac x xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def FB_neutral_edge_def F_DPDA_SPPE__edge_if_def)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_2_def FB_neutral_edge_def F_DPDA_SPPE__edge_if_def)
   apply(erule_tac
      x="xa"
      in ballE)
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. length (edge_pop xa) = Suc 0"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(erule disjE)
    apply(rename_tac x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(erule_tac
      x="xa"
      and P="\<lambda>xa. length (edge_pop xa) = Suc 0"
      in ballE)
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  done

theorem F_DPDA_SPPE__produces_pop_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> read_edges_seperated (F_DPDA_SPPE G)
  \<Longrightarrow> pop_edges_seperated (F_DPDA_SPPE G)"
  apply(simp add: pop_edges_seperated_def read_edges_seperated_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_SPPE_def empty_push_edge_def strict_empty_push_edge_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: FB_neutral_edge_def FB_executing_edge_def F_DPDA_SPPE__edge_then_def)
   apply(erule disjE)
    apply(rename_tac e x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_if_def)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_if_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_if_def)
  apply(simp add: FB_executing_edge_def strict_executing_edge_def)
  apply(case_tac "edge_event x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x a)(*strict*)
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  done

theorem F_DPDA_SPPE__produces_push_and_pop_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated (F_DPDA_SPPE G)"
  apply(simp add: push_and_pop_edges_seperated_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: FB_neutral_edge_def FB_executing_edge_def F_DPDA_SPPE__edge_then_def)
   apply(erule disjE)
    apply(rename_tac e x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_if_def)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_if_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_if_def)
  apply(clarsimp)
  done

definition F_DPDA_SPPE__relation_structure__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_structure__LR G1 G2 \<equiv>
  valid_dpda G1
  \<and> G2 = F_DPDA_SPPE G1"

definition F_DPDA_SPPE__relation_configuration__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_configuration__LR G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR c1"

definition F_DPDA_SPPE__relation_initial_configuration__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_configuration__LR G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR c1"

definition F_DPDA_SPPE__relation_effect__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_effect__LR G1 G2 w1 w2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> w1 = w2"

definition F_DPDA_SPPE__conf_old__LRR :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_SPPE__conf_old__LRR c e \<equiv>
  \<lparr>epdaS_conf_state = cons_state_or_edge_new e,
  epdaS_conf_scheduler = epdaS_conf_scheduler c,
  epdaS_conf_stack = drop (Suc 0) (epdaS_conf_stack c)\<rparr>"

definition F_DPDA_SPPE__relation_step_simulation__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label, (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_step_simulation__LR G1 G2 c1 e c1' c2 d \<equiv>
  if F_DPDA_SPPE__edge_if e
  then d = der3
    (F_DPDA_SPPE__conf_old__LR c1)
      (F_DPDA_SPPE__edge_then_1 e)
    (F_DPDA_SPPE__conf_old__LRR c1 e)
      (F_DPDA_SPPE__edge_then_2__LR e (hd (tl (epdaS_conf_stack c1))))
    (F_DPDA_SPPE__conf_old__LR c1')
  else d = der2
    (F_DPDA_SPPE__conf_old__LR c1)
      (F_DPDA_SPPE__edge_else e)
    (F_DPDA_SPPE__conf_old__LR c1')"

definition F_DPDA_SPPE__relation_initial_simulation__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label, (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_simulation__LR G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_SPPE__conf_old__LR c1)"

lemma F_DPDA_SPPE__conf_old__LR_preserves_configurations: "
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_def)
  apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE_def)
  done

lemma F_DPDA_SPPE__conf_old__LR_preserves_initial_configurations: "
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
  apply(rule F_DPDA_SPPE__conf_old__LR_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma F_DPDA_SPPE__conf_old__LR_preserves_marking_configurations: "
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE_def)
  apply(rule F_DPDA_SPPE__conf_old__LR_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma F_DPDA_SPPE__initial_simulation_preserves_derivation: "
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> epdaS.derivation_initial G2 (der1 (F_DPDA_SPPE__conf_old__LR c1))"
  apply(rule epdaS.derivation_initialI)
   apply(rule epdaS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_DPDA_SPPE__conf_old__LR_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial  G2 d2 \<and> F_DPDA_SPPE__relation_initial_configuration__LR G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_SPPE__relation_initial_simulation__LR G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__LR G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_initial_simulation__LR_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_DPDA_SPPE__initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_initial_configuration__LR_def)
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
  apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def valid_pda_def valid_dpda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_DPDA_SPPE__relation_structure__LR G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply (metis F_DPDA_SPPE__preserves_epda)
  done

lemma F_DPDA_SPPE__relation_step_simulation__LR_maps_to_derivation: "
  F_DPDA_SPPE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_SPPE__relation_configuration__LR G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(clarsimp)
   apply(rule epdaS.der3_is_derivation)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
    apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__conf_old__LRR_def)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(rule conjI)
     apply(rename_tac w)(*strict*)
     prefer 2
     apply(simp add: option_to_list_def FB_executing_edge_def F_DPDA_SPPE__edge_if_def)
     apply(clarsimp)
     apply(rename_tac w wa b)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
     apply(clarsimp)
     apply(simp add: F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def)
     apply(clarsimp)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac w)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def)
    apply(clarsimp)
    apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_1_def)
   apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__edge_then_2__LR_def F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__conf_old__LRR_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac w b wa)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE_def)
    apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
     apply(rename_tac w b wa)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_if_def)
    apply(rename_tac w b wa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(rule disjI2)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def)
    apply(subgoal_tac "\<exists>x. edge_pop e1=[x]")
     apply(rename_tac w b wa)(*strict*)
     prefer 2
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(clarsimp)
     apply(erule_tac
      x="e1"
      in ballE)
      apply(rename_tac w b wa)(*strict*)
      prefer 2
      apply(clarsimp)
     apply(rename_tac w b wa)(*strict*)
     apply(case_tac "edge_pop e1")
      apply(rename_tac w b wa)(*strict*)
      apply(force)
     apply(rename_tac w b wa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac w b wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w b wa x)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_conf_stack c1 = w@[epda_box G1]")
     apply(rename_tac w b wa x)(*strict*)
     prefer 2
     apply(rule epda_box_stays_at_bottom)
      apply(rename_tac w b wa x)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac w b wa x)(*strict*)
     apply(force)
    apply(rename_tac w b wa x)(*strict*)
    apply(clarsimp)
    apply(rename_tac w b wa x wb)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G1 e1")
     apply(rename_tac w b wa x wb)(*strict*)
     prefer 2
     apply(simp add: valid_epda_def valid_dpda_def valid_pda_def)
    apply(rename_tac w b wa x wb)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(case_tac wa)
     apply(rename_tac w b wa x wb)(*strict*)
     apply(clarsimp)
     apply(rename_tac w b)(*strict*)
     apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
    apply(rename_tac w b wa x wb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w b x wb a list)(*strict*)
    apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac w b x wb a list aa ab)(*strict*)
    apply(case_tac list)
     apply(rename_tac w b x wb a list aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac w b x aa ab)(*strict*)
     apply(simp add: valid_epda_def valid_dpda_def valid_pda_def)
    apply(rename_tac w b x wb a list aa ab ac lista)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. list = w' @ [x']")
     apply(rename_tac w b x wb a list aa ab ac lista)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w b x wb a list aa ab ac lista)(*strict*)
    apply(thin_tac "list = ac # lista")
    apply(clarsimp)
    apply(rename_tac w b x a aa ab w')(*strict*)
    apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
     apply(rename_tac w b x a aa ab w')(*strict*)
     apply(simp add: epdaS_configurations_def)
     apply(clarsimp)
    apply(rename_tac w b x a aa ab w')(*strict*)
    apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_SPPE__relation_structure__LR_def epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(clarsimp)
   apply(rename_tac w b wa)(*strict*)
   apply(subgoal_tac "\<exists>w. epdaS_conf_stack c1 = w@[epda_box G1]")
    apply(rename_tac w b wa)(*strict*)
    prefer 2
    apply(rule epda_box_stays_at_bottom)
     apply(rename_tac w b wa)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
     apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
     apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
    apply(rename_tac w b wa)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
   apply(rename_tac w b wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w b wa wb)(*strict*)
   apply(subgoal_tac "\<exists>x. edge_pop e1=[x]")
    apply(rename_tac w b wa wb)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
    apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac w b wa wb)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac w b wa wb)(*strict*)
    apply(case_tac "edge_pop e1")
     apply(rename_tac w b wa wb)(*strict*)
     apply(force)
    apply(rename_tac w b wa wb a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w b wa wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac w b wa wb x)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G1 e1")
    apply(rename_tac w b wa wb x)(*strict*)
    apply(case_tac wa)
     apply(rename_tac w b wa wb x)(*strict*)
     apply(clarsimp)
     apply(rename_tac w b)(*strict*)
     apply(simp add: valid_epda_step_label_def)
     apply(clarsimp)
     apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
    apply(rename_tac w b wa wb x a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
     apply(rename_tac w b wa wb x a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w b wa wb x a list)(*strict*)
    apply(thin_tac "wa = a # list")
    apply(clarsimp)
    apply(rename_tac w b x w')(*strict*)
    apply(case_tac w')
     apply(rename_tac w b x w')(*strict*)
     apply(clarsimp)
    apply(rename_tac w b x w' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w b wa wb x)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE__edge_else_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def)
  apply(rule_tac
      x="e1"
      in bexI_image_disjI2)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_SPPE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__LR G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_SPPE__relation_step_simulation__LR_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.der3_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: der3_def get_configuration_def F_DPDA_SPPE__relation_configuration__LR_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule_tac
      x="Suc(Suc 0)"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule der3_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(simp add: der3_def get_configuration_def F_DPDA_SPPE__relation_configuration__LR_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_preserves_get_accessible_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_DPDA_SPPE__relation_step_simulation__LR_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_belongs_prime)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: get_configuration_def der2_def F_DPDA_SPPE__relation_configuration__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp (no_asm) add: get_configuration_def der2_def)
  apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
  apply(rule epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_configuration__LR F_DPDA_SPPE__relation_structure__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulation epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulation)
  done

interpretation "epdaS_epdaS_SPP_StateSimLR" : ATS_Simulation_Configuration_Weak
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
  "F_DPDA_SPPE__relation_configuration__LR"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__LR"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__LR"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulation_marking_condition: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
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
   apply(simp add: epdaS_epdaS_SPP_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_SPP_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
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
   apply(rule_tac
      t="c"
      and s="F_DPDA_SPPE__conf_old__LR ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_SPPE__conf_old__LR_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
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
    apply(simp add: epdaS_epdaS_SPP_StateSimLR.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_SPP_StateSimLR.simulating_derivation_DEF_def)
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
      and s="F_DPDA_SPPE__conf_old__LR c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_preserves_marking_configurations)
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

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_initial_simulation__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
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
   apply(simp add: epdaS_epdaS_SPP_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_SPP_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR_def)
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
      and s="F_DPDA_SPPE__conf_old__LR ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_SPPE__conf_old__LR_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_preserves_marking_configurations)
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

lemma epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_configuration__LR F_DPDA_SPPE__relation_structure__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_SPP_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_SPP_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_SPP_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_SPP_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_SPPE__relation_effect__LR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_DPDA_SPPE__relation_effect__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_SPPE__relation_initial_configuration__LR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulation_marked_effect: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_initial_simulation__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_SPPE__relation_effect__LR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
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
   apply(simp add: F_DPDA_SPPE__relation_effect__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_SPPE__relation_initial_configuration__LR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_DPDA_SPPE__relation_configuration__LR F_DPDA_SPPE__relation_initial_configuration__LR F_DPDA_SPPE__relation_effect__LR F_DPDA_SPPE__relation_structure__LR F_DPDA_SPPE__relation_initial_simulation__LR F_DPDA_SPPE__relation_step_simulation__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_SPP_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_SPP_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_SPP_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_SPP_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulation_marked_effect)
  done

interpretation "epdaS_epdaS_SPP_StateSimLR" : ATS_Simulation_Configuration_Weak_Marked_Effect
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
  "F_DPDA_SPPE__relation_configuration__LR"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__LR"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__LR"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms )
  done

lemma F_DPDA_SPPE__preserves_lang1: "
  valid_dpda G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_DPDA_SPPE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in subst)
   apply (rule epdaS.AX_marked_language_finite)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_SPPE G)"
      and s="epdaS.finite_marked_language (F_DPDA_SPPE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_DPDA_SPPE__preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_DPDA_SPPE__relation_effect__LR SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_SPP_StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
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
  apply(simp add: F_DPDA_SPPE__relation_effect__LR_def)
  done

definition F_DPDA_SPPE__relation_structure__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_structure__RL G1 G2 \<equiv>
  valid_dpda G2
  \<and> G1 = F_DPDA_SPPE G2"

definition F_DPDA_SPPE__relation_configuration__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_configuration__RL G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR_rev c1"

definition F_DPDA_SPPE__relation_initial_configuration__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_configuration__RL G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR_rev c1"

definition F_DPDA_SPPE__relation_effect__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_effect__RL G1 G2 w1 w2 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_SPP_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_DPDA_SPPE__relation_structure__RL G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply(rule F_DPDA_SPPE__preserves_epda)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis valid_dpda_def valid_pda_def)
  done

definition F_DPDA_SPPE__relation_step_simulation__LRRL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event , 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event , 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 c1 e c1' c2 d \<equiv>
  case edge_trg e of cons_state_or_edge_old q
  \<Rightarrow> (case edge_src e of cons_state_or_edge_old q
    \<Rightarrow> d = der2
        (F_DPDA_SPPE__conf_old__LR_rev c1)
          (F_DPDA_SPPE__edge_else__LR e)
        (F_DPDA_SPPE__conf_old__LR_rev c1')
    | cons_state_or_edge_new e
    \<Rightarrow> d = der1 (F_DPDA_SPPE__conf_old__LR_rev c1))
  | cons_state_or_edge_new e
  \<Rightarrow> d = der2
      (F_DPDA_SPPE__conf_old__LR_rev c1)
        e
      (F_DPDA_SPPE__conf_old__LR_rev c1')"

definition F_DPDA_SPPE__relation_initial_simulation__LRRL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_simulation__LRRL G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_SPPE__conf_old__LR_rev c1)"

lemma F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR_rev c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def)
  apply(case_tac q)
   apply(rename_tac q i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
   apply(force)
  apply(rename_tac q i s epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE_def)
  apply(erule disjE)
   apply(rename_tac i s epda_step_label_ext)(*strict*)
   apply(force)
  apply(rename_tac i s epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G2 x")
   apply(rename_tac i s x)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x)(*strict*)
  apply(rule conjI)
   apply(rename_tac i s x)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac i s x)(*strict*)
  apply(rule valid_epda_push_in_gamma)
   apply(rename_tac i s x)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__conf_old__LR_rev_preserves_initial_configurations: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR_rev c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial  G2 d2 \<and> F_DPDA_SPPE__relation_initial_configuration__RL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_SPPE__relation_initial_simulation__LRRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__RL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_initial_simulation__LRRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_DPDA_SPPE__relation_initial_configuration__RL_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(rule F_DPDA_SPPE__preserves_epda)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__relation_step_simulation__LRRL_maps_to_derivation: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_SPPE__relation_configuration__RL G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LRRL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac q qa)(*strict*)
    apply(clarsimp)
    apply(rule epdaS.der2_is_derivation)
    apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE__edge_else__LR_def)
    apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q qa w)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def)
     apply(erule disjE)
      apply(rename_tac q qa w x)(*strict*)
      apply(simp add: F_DPDA_SPPE__edge_then_1_def)
     apply(rename_tac q qa w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_2_def)
     apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_else_def)
    apply(simp add: F_DPDA_SPPE__edge_if_def)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(case_tac x)
    apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(force)
   apply(rename_tac q epda_step_label_ext)(*strict*)
   apply(clarsimp)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(rename_tac e)
  apply(rename_tac e)(*strict*)
  apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_rev_def)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(clarsimp)
  apply(rename_tac e w)(*strict*)
  apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e w)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac e w x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_then_def)
  apply(erule disjE)
   apply(rename_tac e w x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
  apply(rename_tac e w x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_then_1_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_if_def)
  done

lemma epdaS_epdaS_SPP_StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__RL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LRRL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule F_DPDA_SPPE__relation_step_simulation__LRRL_maps_to_derivation)
        apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_step_simulation__LRRL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_belongs_prime)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE__relation_structure__RL_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
     apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(rule epdaS.get_accessible_configurations_are_configurations)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(rule F_DPDA_SPPE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply (metis)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: get_configuration_def der2_def)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(simp (no_asm) add: der2_def get_configuration_def)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(rule F_DPDA_SPPE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(rule epdaS.der1_belongs)
    apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
    apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
     apply(rule epdaS.get_accessible_configurations_are_configurations)
     apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
     apply(rule F_DPDA_SPPE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(rule F_DPDA_SPPE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext w)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext w)(*strict*)
   apply(simp add: F_DPDA_SPPE_def epda_step_labels_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext w x)(*strict*)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_exta w x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule disjE)
     apply(rename_tac G2 c1 e1 c1' q epda_step_label_exta w x)(*strict*)
     prefer 2
     apply(simp add: F_DPDA_SPPE__edge_then_2_def)
     apply(simp add: option_to_list_def)
     apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_exta w x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' q epda_step_label_ext w x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule F_DPDA_SPPE__relation_step_simulation__LRRL_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_step_simulation__LRRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule epdaS.der2_belongs_prime)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE__relation_structure__RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations)
     apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
    apply(rule epdaS.get_accessible_configurations_are_configurations)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(rule F_DPDA_SPPE__preserves_epda)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(simp add: get_configuration_def der2_def)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
  apply(simp (no_asm) add: der2_def get_configuration_def)
  apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
  apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(rule F_DPDA_SPPE__preserves_epda)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
  apply(rule epdaS.der2_is_derivation)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_configuration__RL F_DPDA_SPPE__relation_structure__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulation epdaS_epdaS_SPP_StateSimRL_step_relation_step_simulation
      epdaS_epdaS_SPP_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs
      epdaS_epdaS_SPP_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_SPP_StateSimRL" : ATS_Simulation_Configuration_Weak
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
  "F_DPDA_SPPE__relation_configuration__RL"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__RL"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__RL"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LRRL"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LRRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_DPDA_SPPE__conf_old__LR_rev_preserves_marking_configurations: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR_rev c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE_def)
   apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac q)(*strict*)
    apply(force)
   apply(rename_tac epda_step_label_ext)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE_def)
   apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac q)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE_def)
    apply(clarsimp)
   apply(rename_tac epda_step_label_ext)(*strict*)
   apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac epda_step_label_ext q)(*strict*)
    apply(clarsimp)
   apply(rename_tac epda_step_label_ext epda_step_label_exta)(*strict*)
   apply(clarsimp)
   apply(rename_tac epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE_def)
   apply(clarsimp)
  apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_relation_step_simulation_marking_condition: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: epdaS_epdaS_SPP_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_SPP_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
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
   apply(rule_tac
      t="c"
      and s="F_DPDA_SPPE__conf_old__LR_rev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      t="ca"
      and s="the (get_configuration (derivation_append deri1 (der2 c1 e1 c1') deri1n i))"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_SPP_StateSimRL.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_SPP_StateSimRL.simulating_derivation_DEF_def)
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
      and s="F_DPDA_SPPE__conf_old__LR_rev c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_marking_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(simp add: epdaS.get_accessible_configurations_def)
    apply(rule_tac
      x="derivation_append deri1 (der2 c1 e1 c1') deri1n "
      in exI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation_initial)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
       apply (rule F_DPDA_SPPE__preserves_epda)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply (metis epdaS.derivation_initial_is_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(rule epdaS.der2_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c option b)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      x="Suc deri1n"
      in exI)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def der2_def)
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

lemma epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_initial_simulation__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
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
   apply(simp add: epdaS_epdaS_SPP_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_SPP_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
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
      and s="F_DPDA_SPPE__conf_old__LR_rev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def)
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

lemma epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_configuration__RL F_DPDA_SPPE__relation_structure__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_SPP_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_SPP_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_SPP_StateSimRL_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_SPP_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_SPP_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_SPPE__relation_effect__RL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_DPDA_SPPE__relation_effect__RL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_SPPE__relation_initial_configuration__RL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca q)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca epda_step_label_ext)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulation_marked_effect: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_SPPE__relation_initial_simulation__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial  G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial  G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_SPPE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_SPPE__relation_effect__RL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: F_DPDA_SPPE__relation_effect__RL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_SPPE__relation_initial_configuration__RL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca q)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca epda_step_label_ext)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_DPDA_SPPE__relation_configuration__RL F_DPDA_SPPE__relation_initial_configuration__RL F_DPDA_SPPE__relation_effect__RL F_DPDA_SPPE__relation_structure__RL F_DPDA_SPPE__relation_initial_simulation__LRRL F_DPDA_SPPE__relation_step_simulation__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_SPP_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_SPP_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_SPP_StateSimRL_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_SPP_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_SPP_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulation_marked_effect)
  done

interpretation "epdaS_epdaS_SPP_StateSimRL" : ATS_Simulation_Configuration_Weak_Marked_Effect
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
  "F_DPDA_SPPE__relation_configuration__RL"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__RL"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__RL"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LRRL"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LRRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms)
  done

lemma F_DPDA_SPPE__preserves_lang2: "
  valid_dpda G
  \<Longrightarrow> epdaS.marked_language G \<supseteq> epdaS.marked_language (F_DPDA_SPPE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in subst)
   apply (rule epdaS.AX_marked_language_finite)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_SPPE G)"
      and s="epdaS.finite_marked_language (F_DPDA_SPPE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_DPDA_SPPE__preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_DPDA_SPPE__relation_effect__RL SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in epdaS_epdaS_SPP_StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_effect__RL_def)
  done

theorem F_DPDA_SPPE__preserves_lang: "
  valid_dpda G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_DPDA_SPPE G)"
  apply(rule order_antisym)
   apply (metis F_DPDA_SPPE__preserves_lang1)
  apply (metis F_DPDA_SPPE__preserves_lang2)
  done

lemma F_DPDA_SPPE__conf_old__LR_rev_reflects_steps2: "
  x \<in> epda_delta G
  \<Longrightarrow> epdaS_step_relation (F_DPDA_SPPE G) c (F_DPDA_SPPE__edge_else x) c1
  \<Longrightarrow> epdaS_step_relation G (F_DPDA_SPPE__conf_old__LR_rev c) x (F_DPDA_SPPE__conf_old__LR_rev c1)"
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE__edge_else_def)
  done

lemma F_DPDA_SPPE__conf_old__LR_rev_reflects_steps1: "
  x \<in> epda_delta G
  \<Longrightarrow> epdaS_step_relation (F_DPDA_SPPE G) c (F_DPDA_SPPE__edge_then_1 x) c1
  \<Longrightarrow> epdaS_step_relation G (F_DPDA_SPPE__conf_old__LR_rev c) x (F_DPDA_SPPE__conf_old__LR_rev c1)"
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def F_DPDA_SPPE__edge_then_1_def)
  apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(erule disjE)
    apply(rename_tac xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_if_def)
   apply(rename_tac xa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(simp add: FB_neutral_edge_def F_DPDA_SPPE__edge_else_def)
  done

lemma F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations2: "
  valid_dpda G2
  \<Longrightarrow> c1' \<in> epdaS_configurations (F_DPDA_SPPE G2)
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR_rev c1' \<in> epdaS_configurations G2"
  apply(simp add: F_DPDA_SPPE__conf_old__LR_rev_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(case_tac q)
   apply(rename_tac q i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(simp add: F_DPDA_SPPE_def)
   apply(erule disjE)
    apply(rename_tac i s qa)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(clarsimp)
  apply(rename_tac q i s epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext)(*strict*)
  apply(simp add: F_DPDA_SPPE_def)
  apply(erule disjE)
   apply(rename_tac i s epda_step_label_ext)(*strict*)
   apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G2 x")
   apply(rename_tac i s x)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x)(*strict*)
  apply(rule conjI)
   apply(rename_tac i s x)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac i s x)(*strict*)
  apply(rule valid_epda_push_in_gamma)
   apply(rename_tac i s x)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__preserves_epdaS_step_relation: "
  c1' \<in> epdaS_configurations (F_DPDA_SPPE G2)
  \<Longrightarrow> epdaS_step_relation (F_DPDA_SPPE G2) c1' e1 c1
  \<Longrightarrow> valid_dpda G2
  \<Longrightarrow> c1 \<in> epdaS_configurations (F_DPDA_SPPE G2)
  \<Longrightarrow> edge_trg e1 = cons_state_or_edge_new e
  \<Longrightarrow> epdaS_step_relation G2 (F_DPDA_SPPE__conf_old__LR_rev c1') e (F_DPDA_SPPE__conf_old__LR_rev c1)"
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(erule disjE)
    apply(rename_tac w x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__conf_old__LR_rev_def option_to_list_def FB_neutral_edge_def)
   apply(rename_tac w x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(rename_tac w x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  done

theorem F_DPDA_SPPE__preserves_is_forward_edge_deterministic_accessible: "
  valid_dpda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible (F_DPDA_SPPE G)"
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e2 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e1)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w wa)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e2)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e1) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e2) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e1 \<in> epda_delta (F_DPDA_SPPE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (F_DPDA_SPPE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(erule_tac
      x="F_DPDA_SPPE__conf_old__LR_rev c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="F_DPDA_SPPE__conf_old__LR_rev c1"
      in allE)
   apply(erule_tac
      x="F_DPDA_SPPE__conf_old__LR_rev c2"
      in allE)
   apply(subgoal_tac " (\<exists>x\<in> epda_delta G \<inter> {e. F_DPDA_SPPE__edge_if e}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G)) \<or> (\<exists>x\<in> epda_delta G \<inter> {e. \<not> F_DPDA_SPPE__edge_if e }. e1 = F_DPDA_SPPE__edge_else x)")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_SPPE_def)
    apply(blast)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G \<inter> {e. F_DPDA_SPPE__edge_if e}. e2 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G)) \<or> (\<exists>x\<in> epda_delta G \<inter> {e. \<not> F_DPDA_SPPE__edge_if e }. e2 = F_DPDA_SPPE__edge_else x)")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_SPPE_def)  
    apply(blast)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G \<inter> {e. F_DPDA_SPPE__edge_if e}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G)"
      in disjE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule_tac
      P="e1 = F_DPDA_SPPE__edge_then_1 x"
      in disjE)
     apply(rename_tac c c1 c2 e1 e2 x)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e2 x)(*strict*)
     apply(erule disjE)
      apply(rename_tac c c1 c2 e2 x)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 e2 x xa)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e2 x xa)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(erule_tac
      x="x"
      in allE)
       apply(erule_tac
      x="xa"
      in allE)
       apply(erule impE)
        apply(rename_tac c c1 c2 x xa)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(rule conjI)
        apply(rename_tac c c1 c2 x xa)(*strict*)
        apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps1)
         apply(rename_tac c c1 c2 x xa)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 x xa)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps1)
        apply(rename_tac c c1 c2 x xa)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e2 x xa)(*strict*)
      apply(simp add: F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def epdaS_step_relation_def)
      apply(clarsimp)
     apply(rename_tac c c1 c2 e2 x)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(erule_tac
      x="x"
      in allE)
     apply(erule_tac
      x="xa"
      in allE)
     apply(erule impE)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(rule conjI)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps1)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps2)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 x)(*strict*)
    apply(erule disjE)
     apply(rename_tac c c1 c2 e1 e2 x)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 x xa)(*strict*)
     apply(erule disjE)
      apply(rename_tac c c1 c2 e1 e2 x xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 e1 x xa)(*strict*)
      apply(simp add: F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def epdaS_step_relation_def)
      apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 x xa)(*strict*)
     apply(simp add: option_to_list_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def epdaS_step_relation_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE_def)
     apply(clarsimp)
     apply(rename_tac c c1 c2 x xa X w b wa ba wb)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_else_def)
     apply(erule disjE)
      apply(rename_tac c c1 c2 x xa X w b wa ba wb)(*strict*)
      apply(clarsimp)
     apply(rename_tac c c1 c2 x xa X w b wa ba wb)(*strict*)
     apply(erule disjE)
      apply(rename_tac c c1 c2 x xa X w b wa ba wb)(*strict*)
      apply(clarsimp)
     apply(rename_tac c c1 c2 x xa X w b wa ba wb)(*strict*)
     apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 x)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 x xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_else_def)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def epdaS_step_relation_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_else_def)
    apply(erule_tac
      P="\<exists>y. edge_event xa = Some y"
      in disjE)
     apply(rename_tac c c1 c2 x xa X w b wa wb)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 x xa X w b wa wb)(*strict*)
    apply(erule disjE)
     apply(rename_tac c c1 c2 x xa X w b wa wb)(*strict*)
     apply(clarsimp)
    apply(rename_tac c c1 c2 x xa X w b wa wb)(*strict*)
    apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e2 x)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e2 x)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e2 x xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule disjE)
     apply(rename_tac c c1 c2 e2 x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(erule_tac
      x="x"
      in allE)
     apply(erule_tac
      x="xa"
      in allE)
     apply(erule impE)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(rule conjI)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps2)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps1)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e2 x xa)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def epdaS_step_relation_def)
    apply(clarsimp)
   apply(rename_tac c c1 c2 e2 x)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(erule_tac
      x="x"
      in allE)
   apply(erule_tac
      x="xa"
      in allE)
   apply(erule impE)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps2)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_rev_reflects_steps2)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "F_DPDA_SPPE__conf_old__LR_rev c \<in> epdaS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(thin_tac "F_DPDA_SPPE__conf_old__LR_rev c \<notin> epdaS.get_accessible_configurations G")
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(rule_tac
      ?c1.0="c"
      in epdaS_epdaS_SPP_StateSimRL.get_accessible_configurations_transfer)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply (metis F_DPDA_SPPE__conf_old__LR_rev_preserves_configurations2 F_DPDA_SPPE__preserves_epda epdaS.get_accessible_configurations_are_configurations2)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(rename_tac c c1 c2 e1 e2 cA cB)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__preserves_DPDA: "
  valid_dpda G
  \<Longrightarrow> valid_dpda (F_DPDA_SPPE G)"
  apply(simp (no_asm) add: valid_dpda_def)
  apply(rule conjI)
   apply(rule F_DPDA_SPPE__preserves_PDA)
   apply(force)
  apply (metis F_DPDA_SPPE__preserves_is_forward_edge_deterministic_accessible)
  done

definition F_DPDA_SPPE__conf_old__LR_revX :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_SPPE__conf_old__LR_revX c \<equiv>
  case epdaS_conf_state c of cons_state_or_edge_old q
  \<Rightarrow> \<lparr>epdaS_conf_state = q,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = epdaS_conf_stack c\<rparr>
  | cons_state_or_edge_new e
  \<Rightarrow> \<lparr>epdaS_conf_state = edge_src e,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = edge_pop e @ epdaS_conf_stack c\<rparr>"

definition F_DPDA_SPPE__relation_configuration__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR c1"

definition F_DPDA_SPPE__relation_initial_configuration__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_configuration__LR2 G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR c1"

definition F_DPDA_SPPE__relation_effect__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_effect__LR2 G1 G2 w1 w2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> w1 = w2"

definition F_DPDA_SPPE__relation_step_simulation__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label, (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_step_simulation__LR2 G1 G2 c1 e c1' c2 d \<equiv>
  if F_DPDA_SPPE__edge_if e
  then d = der3
      (F_DPDA_SPPE__conf_old__LR c1)
        (F_DPDA_SPPE__edge_then_1 e)
      (F_DPDA_SPPE__conf_old__LRR c1 e)
        (F_DPDA_SPPE__edge_then_2__LR e (hd (tl (epdaS_conf_stack c1))))
      (F_DPDA_SPPE__conf_old__LR c1')
  else d = der2
      (F_DPDA_SPPE__conf_old__LR c1)
        (F_DPDA_SPPE__edge_else e)
      (F_DPDA_SPPE__conf_old__LR c1')"

definition F_DPDA_SPPE__relation_initial_simulation__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label, (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_simulation__LR2 G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_SPPE__conf_old__LR c1)"

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulationX: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial  G2 d2 \<and> F_DPDA_SPPE__relation_initial_configuration__LR2 G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_SPPE__relation_initial_simulation__LR2 G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_initial_simulation__LR2_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_DPDA_SPPE__initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_initial_configuration__LR2_def)
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
  apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def valid_pda_def valid_dpda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__relation_step_simulation__LR2_maps_to_derivation: "
  F_DPDA_SPPE__relation_step_simulation__LR2 G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(clarsimp)
   apply(rule epdaS.der3_is_derivation)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
    apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__conf_old__LRR_def)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(rule conjI)
     apply(rename_tac w)(*strict*)
     prefer 2
     apply(simp add: option_to_list_def FB_executing_edge_def F_DPDA_SPPE__edge_if_def)
     apply(clarsimp)
     apply(rename_tac w wa b)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
     apply(clarsimp)
     apply(simp add: F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def)
     apply(clarsimp)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac w)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def)
    apply(clarsimp)
    apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
     apply(rename_tac w)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_1_def)
   apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__edge_then_2__LR_def F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__conf_old__LRR_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac w b wa)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE_def)
    apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
     apply(rename_tac w b wa)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__edge_else_def)
    apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__edge_else_def)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__edge_else_def)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>x. edge_pop e1=[x]")
     apply(rename_tac w b wa)(*strict*)
     prefer 2
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(clarsimp)
     apply(erule_tac
      x="e1"
      in ballE)
      apply(rename_tac w b wa)(*strict*)
      prefer 2
      apply(clarsimp)
     apply(rename_tac w b wa)(*strict*)
     apply(case_tac "edge_pop e1")
      apply(rename_tac w b wa)(*strict*)
      apply(force)
     apply(rename_tac w b wa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac w b wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w b wa x)(*strict*)
    apply(subgoal_tac "\<exists>w. epdaS_conf_stack c1 = w@[epda_box G1]")
     apply(rename_tac w b wa x)(*strict*)
     prefer 2
     apply(rule epda_box_stays_at_bottom)
      apply(rename_tac w b wa x)(*strict*)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac w b wa x)(*strict*)
     apply(force)
    apply(rename_tac w b wa x)(*strict*)
    apply(clarsimp)
    apply(rename_tac w b wa x wb)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G1 e1")
     apply(rename_tac w b wa x wb)(*strict*)
     prefer 2
     apply(simp add: valid_epda_def valid_dpda_def valid_pda_def)
    apply(rename_tac w b wa x wb)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(case_tac wa)
     apply(rename_tac w b wa x wb)(*strict*)
     apply(clarsimp)
     apply(rename_tac w b)(*strict*)
     apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
    apply(rename_tac w b wa x wb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w b x wb a list)(*strict*)
    apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac w b x wb a list aa ab)(*strict*)
    apply(case_tac list)
     apply(rename_tac w b x wb a list aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac w b x aa ab)(*strict*)
     apply(simp add: valid_epda_def valid_dpda_def valid_pda_def)
    apply(rename_tac w b x wb a list aa ab ac lista)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. list = w' @ [x']")
     apply(rename_tac w b x wb a list aa ab ac lista)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w b x wb a list aa ab ac lista)(*strict*)
    apply(thin_tac "list = ac # lista")
    apply(clarsimp)
    apply(rename_tac w b x a aa ab w')(*strict*)
    apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
     apply(rename_tac w b x a aa ab w')(*strict*)
     apply(simp add: epdaS_configurations_def)
     apply(clarsimp)
    apply(rename_tac w b x a aa ab w')(*strict*)
    apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_SPPE__relation_structure__LR_def epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(clarsimp)
   apply(rename_tac w b wa)(*strict*)
   apply(subgoal_tac "\<exists>w. epdaS_conf_stack c1 = w@[epda_box G1]")
    apply(rename_tac w b wa)(*strict*)
    prefer 2
    apply(rule epda_box_stays_at_bottom)
     apply(rename_tac w b wa)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
     apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
     apply(simp add: valid_epda_def valid_pda_def valid_dpda_def)
    apply(rename_tac w b wa)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
   apply(rename_tac w b wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w b wa wb)(*strict*)
   apply(subgoal_tac "\<exists>x. edge_pop e1=[x]")
    apply(rename_tac w b wa wb)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
    apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac w b wa wb)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac w b wa wb)(*strict*)
    apply(case_tac "edge_pop e1")
     apply(rename_tac w b wa wb)(*strict*)
     apply(force)
    apply(rename_tac w b wa wb a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w b wa wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac w b wa wb x)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G1 e1")
    apply(rename_tac w b wa wb x)(*strict*)
    apply(case_tac wa)
     apply(rename_tac w b wa wb x)(*strict*)
     apply(clarsimp)
     apply(rename_tac w b)(*strict*)
     apply(simp add: valid_epda_step_label_def)
     apply(clarsimp)
     apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def)
    apply(rename_tac w b wa wb x a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
     apply(rename_tac w b wa wb x a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w b wa wb x a list)(*strict*)
    apply(thin_tac "wa = a # list")
    apply(clarsimp)
    apply(rename_tac w b x w')(*strict*)
    apply(case_tac w')
     apply(rename_tac w b x w')(*strict*)
     apply(clarsimp)
    apply(rename_tac w b x w' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w b wa wb x)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_def F_DPDA_SPPE__edge_else_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def)
  apply(rule_tac
      x="e1"
      in bexI_image_disjI2)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulationX: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_SPPE__relation_step_simulation__LR2 G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_SPPE__relation_step_simulation__LR2_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.der3_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: der3_def get_configuration_def F_DPDA_SPPE__relation_configuration__LR2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule_tac
      x="Suc(Suc 0)"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule der3_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(simp add: der3_def get_configuration_def F_DPDA_SPPE__relation_configuration__LR2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_preserves_get_accessible_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_DPDA_SPPE__relation_step_simulation__LR2_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_belongs_prime)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_SPPE__conf_old__LR_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: get_configuration_def der2_def F_DPDA_SPPE__relation_configuration__LR2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp (no_asm) add: get_configuration_def der2_def)
  apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
  apply(rule epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axiomsX: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_SPPE__relation_configuration__LR2 F_DPDA_SPPE__relation_initial_configuration__LR2 F_DPDA_SPPE__relation_structure__LR F_DPDA_SPPE__relation_initial_simulation__LR2 F_DPDA_SPPE__relation_step_simulation__LR2"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_relation_initial_simulationX epdaS_epdaS_SPP_StateSimLR_inst_relation_step_simulationX epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_SPP_StateSimLRX" : ATS_Simulation_Configuration_Weak
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
  "F_DPDA_SPPE__relation_configuration__LR2"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__LR2"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__LR2"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR2"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR2"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axiomsX)
  done

definition F_DPDA_SPPE__relation_configuration__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR_revX c1"

definition F_DPDA_SPPE__relation_initial_configuration__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_configuration__RL2 G1 G2 c1 c2 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_SPPE__conf_old__LR_revX c1"

definition F_DPDA_SPPE__relation_effect__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_effect__RL2 G1 G2 w1 w2 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<and> w1 = w2"

definition F_DPDA_SPPE__relation_step_simulation__LR2RL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event , 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event , 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_step_simulation__LR2RL G1 G2 c1 e c1' c2 d \<equiv>
  case edge_trg e of cons_state_or_edge_old q
  \<Rightarrow> (case edge_src e of cons_state_or_edge_old q
    \<Rightarrow> d = der2
        (F_DPDA_SPPE__conf_old__LR_revX c1)
          (F_DPDA_SPPE__edge_else__LR e)
        (F_DPDA_SPPE__conf_old__LR_revX c1')
    | cons_state_or_edge_new e
    \<Rightarrow> d = der2
        (F_DPDA_SPPE__conf_old__LR_revX c1)
          e
        (F_DPDA_SPPE__conf_old__LR_revX c1'))
  | cons_state_or_edge_new e
  \<Rightarrow> d = der1 (F_DPDA_SPPE__conf_old__LR_revX c1)"

definition F_DPDA_SPPE__relation_initial_simulation__LR2RL :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_initial_simulation__LR2RL G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_SPPE__conf_old__LR_revX c1)"

lemma F_DPDA_SPPE__conf_old__LR_revX_preserves_configurations: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR_revX c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_revX_def)
  apply(case_tac q)
   apply(rename_tac q i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
   apply(force)
  apply(rename_tac q i s epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE_def)
  apply(erule disjE)
   apply(rename_tac i s epda_step_label_ext)(*strict*)
   apply(force)
  apply(rename_tac i s epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G2 x")
   apply(rename_tac i s x)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x)(*strict*)
  apply(rule conjI)
   apply(rename_tac i s x)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac i s x)(*strict*)
  apply(rule valid_epda_pop_in_gamma)
   apply(rename_tac i s x)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__conf_old__LR_revX_preserves_initial_configurations: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_DPDA_SPPE__conf_old__LR_revX c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: F_DPDA_SPPE__conf_old__LR_revX_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulationX: "
  (\<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial  G2 d2 \<and> F_DPDA_SPPE__relation_initial_configuration__RL2 G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_SPPE__relation_initial_simulation__LR2RL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_initial_simulation__LR2RL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_DPDA_SPPE__conf_old__LR_revX_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_DPDA_SPPE__relation_initial_configuration__RL2_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(rule F_DPDA_SPPE__preserves_epda)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_DPDA_SPPE__relation_step_simulation__LR2RL_maps_to_derivation: "
  F_DPDA_SPPE__relation_structure__RL G1 G2
  \<Longrightarrow> F_DPDA_SPPE__relation_step_simulation__LR2RL G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac q qa)(*strict*)
    apply(clarsimp)
    apply(rule epdaS.der2_is_derivation)
    apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_revX_def F_DPDA_SPPE__edge_else__LR_def)
    apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q qa w)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def)
     apply(erule disjE)
      apply(rename_tac q qa w x)(*strict*)
      apply(simp add: F_DPDA_SPPE__edge_then_1_def)
     apply(rename_tac q qa w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_2_def)
     apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_else_def)
    apply(simp add: F_DPDA_SPPE__edge_if_def)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(case_tac x)
    apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(force)
   apply(rename_tac q epda_step_label_ext)(*strict*)
   prefer 2
   apply(rename_tac epda_step_label_ext)(*strict*)
   apply(clarsimp)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac q epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(rename_tac e)
  apply(rename_tac q e)(*strict*)
  apply(simp add: epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_revX_def)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
  apply(clarsimp)
  apply(rename_tac q e w)(*strict*)
  apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac q e w)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac q e w x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac q e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac q e w x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_then_def)
  apply(erule disjE)
   apply(rename_tac q e w x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
   apply(rename_tac e w X)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(rename_tac q e w x)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE__edge_then_1_def)
  done

lemma epdaS_epdaS_SPP_StateSimRL_step_relation_step_simulationX: "
  \<forall>G1 G2. F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_SPPE__relation_step_simulation__LR2RL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule F_DPDA_SPPE__relation_step_simulation__LR2RL_maps_to_derivation)
        apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_belongs_prime)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE__relation_structure__RL_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
     apply(rule F_DPDA_SPPE__conf_old__LR_revX_preserves_configurations)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(rule epdaS.get_accessible_configurations_are_configurations)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(rule F_DPDA_SPPE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply (metis )
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: get_configuration_def der2_def)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(simp (no_asm) add: der2_def get_configuration_def)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(rule F_DPDA_SPPE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(rule epdaS.der1_belongs)
    apply(rule F_DPDA_SPPE__conf_old__LR_revX_preserves_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
    apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
     apply(rule epdaS.get_accessible_configurations_are_configurations)
     apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
     apply(rule F_DPDA_SPPE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(rule F_DPDA_SPPE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__conf_old__LR_revX_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext w)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' epda_step_label_ext w)(*strict*)
   apply(simp add: F_DPDA_SPPE_def epda_step_labels_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' epda_step_label_ext w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' epda_step_label_ext w x)(*strict*)
    apply(rename_tac G2 c1 e1 c1' epda_step_label_exta w x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule disjE)
     apply(rename_tac G2 c1 e1 c1' epda_step_label_exta w x)(*strict*)
     prefer 2
     apply(simp add: F_DPDA_SPPE__edge_then_2_def)
     apply(simp add: option_to_list_def)
     apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' epda_step_label_exta w x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' epda_step_label_exta)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac G2 c1 e1 c1' epda_step_label_ext w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' epda_step_label_ext w x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule F_DPDA_SPPE__relation_step_simulation__LR2RL_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule epdaS.der2_belongs_prime)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
     apply (metis epdaS_epdaS_SPP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE__relation_structure__RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule F_DPDA_SPPE__conf_old__LR_revX_preserves_configurations)
     apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
    apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
    apply(rule epdaS.get_accessible_configurations_are_configurations)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(rule F_DPDA_SPPE__preserves_epda)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(simp add: get_configuration_def der2_def)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
  apply(simp (no_asm) add: der2_def get_configuration_def)
  apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
  apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
    apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
    apply(rule F_DPDA_SPPE__preserves_epda)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext)(*strict*)
  apply(rule epdaS.der2_is_derivation)
  apply(force)
  done

lemma epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_SPPE__relation_configuration__RL2 F_DPDA_SPPE__relation_initial_configuration__RL2 F_DPDA_SPPE__relation_structure__RL F_DPDA_SPPE__relation_initial_simulation__LR2RL F_DPDA_SPPE__relation_step_simulation__LR2RL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_SPP_StateSimRL_inst_relation_initial_simulationX epdaS_epdaS_SPP_StateSimRL_step_relation_step_simulationX epdaS_epdaS_SPP_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_SPP_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_SPP_StateSimRLX" : ATS_Simulation_Configuration_Weak
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
  "F_DPDA_SPPE__relation_configuration__RL2"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__RL2"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__RL2"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR2RL"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR2RL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX)
  done

definition F_DPDA_SPPE__relation_labels__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_labels__LR2 G1 G2 e1 e2 \<equiv>
  F_DPDA_SPPE__relation_structure__LR G1 G2
  \<and> e1 \<in> F_DPDA_DRE__revert_F_DPDA_SPPE G1 {e2}"

definition F_DPDA_SPPE__relation_labels__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__relation_labels__RL2 G2 G1 e2 e1 \<equiv>
  F_DPDA_SPPE__relation_structure__RL G2 G1
  \<and> e1 \<in> F_DPDA_DRE__revert_F_DPDA_SPPE G1 {e2}"

lemma SPP_ATS_Simulation_Configuration_WeakReach_axioms_inst_ATS_Simulation_Configuration_WeakRL_axioms: "
  ATS_Simulation_Configuration_WeakReach_axioms epda_step_labels epdaS_step_relation epdaS_configurations epda_step_labels epdaS_step_relation F_DPDA_SPPE__relation_configuration__RL2 F_DPDA_SPPE__relation_structure__RL F_DPDA_SPPE__relation_step_simulation__LR2RL F_DPDA_SPPE__relation_labels__RL2"
  apply(simp add: ATS_Simulation_Configuration_WeakReach_axioms_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
    apply(subgoal_tac "n=0")
     apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
    apply(rule_tac
      d="(der1 (F_DPDA_SPPE__conf_old__LR_revX c1))"
      in epdaS.maximum_of_domainUnique)
      apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
   apply(rename_tac e)
   apply(rename_tac G1 G2 c1 e1 c1' n e)(*strict*)
   apply(subgoal_tac "\<exists>c. epdaS_step_relation G2 (F_DPDA_SPPE__conf_old__LR_revX c1) e c")
    apply(rename_tac G1 G2 c1 e1 c1' n e)(*strict*)
    prefer 2
    apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg e,epdaS_conf_scheduler=drop(length(option_to_list (edge_event e)))(epdaS_conf_scheduler(F_DPDA_SPPE__conf_old__LR_revX c1)),epdaS_conf_stack=edge_push e@(drop(length(edge_pop e))(epdaS_conf_stack(F_DPDA_SPPE__conf_old__LR_revX c1)))\<rparr>"
      in exI)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_revX_def der1_def get_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
    apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e)}. e1 = F_DPDA_SPPE__edge_else x)")
     apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
     prefer 2
     apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' n e w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def)
     apply(erule disjE)
      apply(rename_tac G1 G2 c1 e1 c1' n e w x)(*strict*)
      apply(simp add: F_DPDA_SPPE__edge_then_1_def)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 c1' n e)(*strict*)
      apply(simp add: option_to_list_def)
      apply(case_tac "edge_event e")
       apply(rename_tac G1 G2 c1 c1' n e)(*strict*)
       apply(clarsimp)
      apply(rename_tac G1 G2 c1 c1' n e a)(*strict*)
      apply(clarsimp)
      apply(simp add: F_DPDA_SPPE__edge_if_def)
     apply(rename_tac G1 G2 c1 e1 c1' n e w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_2_def)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' n e w x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_else_def)
   apply(rename_tac G1 G2 c1 e1 c1' n e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(erule_tac
      x="der2 (F_DPDA_SPPE__conf_old__LR_revX c1) e c"
      in allE)
   apply(erule impE)
    apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
    apply(simp add: get_configuration_def der2_def der1_def)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(erule impE)
    apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
    apply(erule_tac
      x="Suc 0"
      in allE)
    apply(simp add: maximum_of_domain_def der2_def)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(erule_tac
      x="Suc 0"
      in allE)
   apply(simp add: maximum_of_domain_def der2_def)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e)}. e1 = F_DPDA_SPPE__edge_else x)")
    apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
    prefer 2
    apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n e c x y)(*strict*)
    apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
    apply(simp add: epdaS_step_relation_def)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' n e c x y)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(rename_tac G1 G2 c1 e1 c1' n e c x y)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n e c x y)(*strict*)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n e c x y w wa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n q)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e)}. e1 = F_DPDA_SPPE__edge_else x)")
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    prefer 2
    apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_SPPE__edge_if e}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)"
      in disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule_tac
      P="e1 = F_DPDA_SPPE__edge_then_1 x"
      in disjE)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n q qa x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule_tac
      x="F_DPDA_SPPE__edge_else__LR \<lparr>edge_src = cons_state_or_edge_old (edge_src x), edge_event = edge_event x, edge_pop = edge_pop x, edge_push = edge_push x, edge_trg = cons_state_or_edge_old (edge_trg x)\<rparr>"
      in exI)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
   apply(simp add: F_DPDA_SPPE__edge_else__LR_def F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' n x w)(*strict*)
    apply(case_tac x)
    apply(rename_tac G1 G2 c1 c1' n x w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n q epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n q epda_step_label_ext)(*strict*)
  apply(rename_tac e)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
   apply(rule_tac
      x="(F_DPDA_SPPE__conf_old__LR_revX c1')"
      in exI)
   apply(simp add: der2_def)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e )}. e1 = F_DPDA_SPPE__edge_else x)")
   apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
   prefer 2
   apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_SPPE__edge_if e}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)"
      in disjE)
   apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(erule_tac
      P="e1 = F_DPDA_SPPE__edge_then_1 x"
      in disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n q e x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac G1 G2 c1 e1 c1' n q e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n e X)(*strict*)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(rule disjI1)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(rule disjI2)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n q e x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  done

interpretation "epdaS_epdaS_SPP_StateSimRLX" : ATS_Simulation_Configuration_WeakReach
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
  "F_DPDA_SPPE__relation_configuration__RL2"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__RL2"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__RL2"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR2RL"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR2RL"
  (* relation_labelsLR *)
  "F_DPDA_SPPE__relation_labels__RL2"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX SPP_ATS_Simulation_Configuration_WeakReach_axioms_inst_ATS_Simulation_Configuration_WeakRL_axioms )
  done

lemma SPP_ATS_Simulation_Configuration_WeakReach_axioms_inst_ATS_Simulation_Configuration_WeakRL_axiomsX: "
  ATS_Simulation_Configuration_WeakReach_axioms epda_step_labels epdaS_step_relation epdaS_configurations epda_step_labels epdaS_step_relation F_DPDA_SPPE__relation_configuration__LR2 F_DPDA_SPPE__relation_structure__LR F_DPDA_SPPE__relation_step_simulation__LR2 F_DPDA_SPPE__relation_labels__LR2"
  apply(simp add: ATS_Simulation_Configuration_WeakReach_axioms_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule_tac
      x="(F_DPDA_SPPE__edge_then_1 e1)"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
    apply(simp add: der3_def)
   apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_labels__LR2_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def epda_step_labels_def F_DPDA_SPPE__edge_then_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule_tac
      x="(F_DPDA_SPPE__edge_else e1)"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_labels__LR2_def)
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def epda_step_labels_def F_DPDA_SPPE__edge_then_def)
  done

interpretation "epdaS_epdaS_SPP_StateSimLRX" : ATS_Simulation_Configuration_WeakReach
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
  "F_DPDA_SPPE__relation_configuration__LR2"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__LR2"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__LR2"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR2"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR2"
  (* relation_labelsLR *)
  "F_DPDA_SPPE__relation_labels__LR2"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axiomsX SPP_ATS_Simulation_Configuration_WeakReach_axioms_inst_ATS_Simulation_Configuration_WeakRL_axiomsX )
  done

definition F_DPDA_SPPE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__SpecInput G \<equiv>
  valid_dpda G
  \<and> neutral_edges_removed G
  \<and> read_edges_seperated G"

definition F_DPDA_SPPE__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_SPPE__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> neutral_edges_removed Go
  \<and> read_edges_seperated Go
  \<and> push_and_pop_edges_seperated Go
  \<and> pop_edges_seperated Go"

lemma F_DPDA_DRE__revert_F_DPDA_SPPE_SOUND_scheduled_case: "
  F_DPDA_SPPE__SpecInput G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_SPPE G' (epdaS_accessible_edges (F_DPDA_SPPE G')) = epdaS_accessible_edges G'"
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def epdaS_accessible_edges_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x p d n c)(*strict*)
   apply(subgoal_tac "\<exists>d2 n2 e2 c2. epdaS.derivation_initial  SSG2 d2 \<and> d2 n2 = Some (pair e2 c2) \<and> (case SSe1 of None \<Rightarrow> True | Some e1' \<Rightarrow> \<exists>k d2'. epdaS.derivation SSG2 d2' \<and> the (get_configuration (d2' 0)) = the (get_configuration (d2 n2)) \<and> (case get_label (derivation_append d2 d2' n2 k) of None \<Rightarrow> False | Some e2' \<Rightarrow> F_DPDA_SPPE__relation_labels__RL2 SSG1 SSG2 e1' e2'))" for SSe1 SSG1 SSG2)
    apply(rename_tac x p d n c)(*strict*)
    prefer 2
    apply(rule_tac
      ?G2.0="G'"
      and ?d1.0="d"
      and ?G1.0="F_DPDA_SPPE G'"
      in epdaS_epdaS_SPP_StateSimRLX.ATS_Simulation_Configuration_WeakReach_exists)
      apply(rename_tac x p d n c)(*strict*)
      apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
      apply(simp add: F_DPDA_SPPE__SpecInput_def)
     apply(rename_tac x p d n c)(*strict*)
     apply(force)
    apply(rename_tac x p d n c)(*strict*)
    apply(force)
   apply(rename_tac x p d n c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2')(*strict*)
   apply(case_tac "get_label (derivation_append d2 d2' n2 k)")
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2')(*strict*)
    apply(force)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac "derivation_append d2 d2' n2 k")
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a)(*strict*)
    apply(force)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a aa)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a aa option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(subgoal_tac "\<exists>c. d2' 0 = Some (pair None c)")
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    prefer 2
    apply (metis epdaS.some_position_has_details_at_0)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b ca)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(subgoal_tac "epdaS.derivation_initial G' (derivation_append d2 d2' n2)")
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    prefer 2
    apply(rule epdaS.derivation_append_preserves_derivation_initial)
      apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
      apply(simp add: F_DPDA_SPPE__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(force)
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation)
      apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(force)
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule_tac
      x="derivation_append d2 d2' n2"
      in exI)
   apply(rule conjI)
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(force)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule_tac
      x="k"
      in exI)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(clarsimp)
   apply(erule_tac
      P="p \<in> F_DPDA_SPPE__edge_then x (epda_gamma G')"
      in disjE)
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(erule disjE)
     apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def)
     apply(erule_tac
      P="p = \<lparr>edge_src = cons_state_or_edge_old (edge_src x), edge_event = None, edge_pop = edge_pop x, edge_push = [], edge_trg = cons_state_or_edge_new x\<rparr>"
      in disjE)
      apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
      apply(clarsimp)
     apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(erule disjE)
      apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
      apply(clarsimp)
     apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(clarsimp)
    apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac x p d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__edge_then_1_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(subgoal_tac "\<exists>d2 n2 e2 c2. epdaS.derivation_initial  SSG2 d2 \<and> d2 n2 = Some (pair e2 c2) \<and> (case SSe1 of None \<Rightarrow> True | Some e1' \<Rightarrow> \<exists>k d2'. epdaS.derivation SSG2 d2' \<and> the (get_configuration (d2' 0)) = the (get_configuration (d2 n2)) \<and> (case get_label (derivation_append d2 d2' n2 k) of None \<Rightarrow> False | Some e2' \<Rightarrow> F_DPDA_SPPE__relation_labels__LR2 SSG1 SSG2 e1' e2'))" for SSG2 SSe1 SSG1)
   apply(rename_tac x d n c)(*strict*)
   prefer 2
   apply(rule_tac
      ?G1.0="G'"
      and ?d1.0="d"
      and ?G2.0="F_DPDA_SPPE G'"
      in epdaS_epdaS_SPP_StateSimLRX.ATS_Simulation_Configuration_WeakReach_exists)
     apply(rename_tac x d n c)(*strict*)
     apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
     apply(simp add: F_DPDA_SPPE__SpecInput_def)
    apply(rename_tac x d n c)(*strict*)
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2')(*strict*)
  apply(case_tac "get_label (derivation_append d2 d2' n2 k)")
   apply(rename_tac x d n c d2 n2 e2 k c2 d2')(*strict*)
   apply(force)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(case_tac "derivation_append d2 d2' n2 k")
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a)(*strict*)
   apply(force)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(subgoal_tac "\<exists>c. d2' 0 = Some (pair None c)")
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   prefer 2
   apply (metis epdaS.some_position_has_details_at_0)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b ca)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(subgoal_tac "epdaS.derivation_initial (F_DPDA_SPPE G') (derivation_append d2 d2' n2)")
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   prefer 2
   apply(rule epdaS.derivation_append_preserves_derivation_initial)
     apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(rule F_DPDA_SPPE__preserves_epda)
     apply(simp add: F_DPDA_SPPE__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(force)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule epdaS.derivation_append_preserves_derivation)
     apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(force)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(rule_tac
      x="a"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule_tac
      t="epda_delta (F_DPDA_SPPE G')"
      and s="epda_step_labels (F_DPDA_SPPE G')"
      in ssubst)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(simp add: epda_step_labels_def)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule_tac
      i="k"
      and d="derivation_append d2 d2' n2"
      in epdaS.belongs_step_labels)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(rule epdaS.derivation_initial_belongs)
     apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(rule F_DPDA_SPPE__preserves_epda)
     apply(simp add: F_DPDA_SPPE__SpecInput_def valid_dpda_def valid_pda_def)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(force)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(force)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule_tac
      x="derivation_append d2 d2' n2"
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(simp add: F_DPDA_SPPE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b xa)(*strict*)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__relation_labels__LR2_def)
  apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__relation_labels__LR2_def)
  done

lemma F_DPDA_SPPE__SOUND: "
  F_DPDA_SPPE__SpecInput G
  \<Longrightarrow> F_DPDA_SPPE__SpecOutput G (F_DPDA_SPPE G)"
  apply(simp add: F_DPDA_SPPE__SpecInput_def F_DPDA_SPPE__SpecOutput_def)
  apply(rule context_conjI)
   apply(rule F_DPDA_SPPE__preserves_DPDA)
   apply(force)
  apply(rule conjI)
   apply (rule F_DPDA_SPPE__preserves_lang)
   apply(force)
  apply(rule context_conjI)
   apply (metis F_DPDA_SPPE__preserves_neutral_edges_removed)
  apply(rule context_conjI)
   apply (metis F_DPDA_SPPE__preserves_read_edges_seperated)
  apply(rule context_conjI)
   apply (metis F_DPDA_SPPE__produces_push_and_pop_edges_seperated)
  apply (metis F_DPDA_SPPE__produces_pop_edges_seperated)
  done

lemma epdaS_epdaS_SPP_StateSimLRRequired__inst__AX_relation_configuration_compatible_with_marking_configurations: "
(\<forall>G1 G2.
        F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 c2 \<longrightarrow>
            c1 \<in> epdaS_marking_configurations G1 \<longrightarrow> c2 \<in> epdaS_marking_configurations G2))"
  apply(clarsimp)
  apply(simp add: epdaS_marking_configurations_def)
  apply(subgoal_tac "c2 \<in> epdaS_configurations G2")
   prefer 2
   apply(simp add: F_DPDA_SPPE__relation_configuration__LR2_def)
   apply(clarsimp)
   apply (metis F_DPDA_SPPE__conf_old__LR_preserves_configurations)
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE__relation_structure__LR_def F_DPDA_SPPE_def F_DPDA_SPPE__relation_configuration__LR2_def F_DPDA_SPPE__conf_old__LR_def)
  done

lemma epdaS_epdaS_SPP_StateSimLRRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant: "
(\<forall>G1 G2.
        F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 c2 \<longrightarrow>
            (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                  (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                         (\<forall>d2. F_DPDA_SPPE__relation_step_simulation__LR2 G1 G2 c1 e1 c1' c2
                                d2 \<longrightarrow>
                               maximum_of_domain d2 0 \<longrightarrow>
                               c1' \<notin> epdaS_marking_configurations G1)))))"
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def der1_def der2_def der3_def)
  apply(simp add: maximum_of_domain_def der1_def der2_def der3_def)
  done

lemma epdaS_epdaS_SPP_StateSimLRRequired__inst__AX_relation_step_simulationReach: "
(\<forall>G1 G2.
        F_DPDA_SPPE__relation_structure__LR G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1 c2 \<longrightarrow>
            (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                  (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                         (\<forall>d2. epdaS.derivation G2 d2 \<longrightarrow>
                               epdaS.belongs G2 d2 \<longrightarrow>
                               the (get_configuration (d2 0)) = c2 \<longrightarrow>
                               F_DPDA_SPPE__relation_step_simulation__LR2 G1 G2 c1 e1 c1' c2
                                d2 \<longrightarrow>
                               (\<forall>n. maximum_of_domain d2 n \<longrightarrow>
                                    F_DPDA_SPPE__relation_configuration__LR2 G1 G2 c1'
                                     (the (get_configuration (d2 n))) \<longrightarrow>
                                    (\<exists>k e2. (\<exists>c2. d2 k = Some (pair (Some e2) c2)) \<and>
                                            F_DPDA_SPPE__relation_labels__LR2 G1 G2 e1 e2) \<or>
                                    n = 0 \<and>
                                    (\<exists>e2. Ex (epdaS_step_relation G2 c2 e2) \<and>
                                          F_DPDA_SPPE__relation_labels__LR2 G1 G2 e1 e2)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2_def)
  apply(case_tac "F_DPDA_SPPE__edge_if e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule_tac
      x="(F_DPDA_SPPE__edge_then_1 e1)"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
    apply(simp add: der3_def)
   apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_labels__LR2_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def epda_step_labels_def F_DPDA_SPPE__edge_then_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule_tac
      x="(F_DPDA_SPPE__edge_else e1)"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G1 G2 c1 e1 c1' n)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_labels__LR2_def)
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def epda_step_labels_def F_DPDA_SPPE__edge_then_def)
  done

lemma epdaS_epdaS_SPP_StateSimLRRequired__inst__ATS_Simulation_Configuration_WeakRequired_axioms: "
ATS_Simulation_Configuration_WeakRequired_axioms epda_step_labels epdaS_step_relation
     epdaS_configurations epda_step_labels epdaS_step_relation
     F_DPDA_SPPE__relation_configuration__LR2 F_DPDA_SPPE__relation_structure__LR
     F_DPDA_SPPE__relation_step_simulation__LR2 F_DPDA_SPPE__relation_labels__LR2
     epdaS_marking_configurations epdaS_marking_configurations"
  apply(simp add:     ATS_Simulation_Configuration_WeakRequired_axioms_def epdaS_epdaS_SPP_StateSimLRRequired__inst__AX_relation_step_simulationReach epdaS_epdaS_SPP_StateSimLRRequired__inst__AX_relation_configuration_compatible_with_marking_configurations epdaS_epdaS_SPP_StateSimLRRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant)
  done

interpretation "epdaS_epdaS_SPP_StateSimLRRequired" : ATS_Simulation_Configuration_WeakRequired
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
  "F_DPDA_SPPE__relation_configuration__LR2"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__LR2"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__LR2"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR2"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR2"
  (* relation_labelsLR *)
  "F_DPDA_SPPE__relation_labels__LR2"
  (* marking_configurations1 *)
  "epdaS_marking_configurations"
  (* marking_configurations2 *)
  "epdaS_marking_configurations"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_SPP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axiomsX SPP_ATS_Simulation_Configuration_WeakReach_axioms_inst_ATS_Simulation_Configuration_WeakRL_axiomsX
      epdaS_epdaS_SPP_StateSimLRRequired__inst__ATS_Simulation_Configuration_WeakRequired_axioms)
  done

lemma epdaS_epdaS_SPP_StateSimRLRequired__inst__AX_relation_configuration_compatible_with_marking_configurations: "
(\<forall>G1 G2.
        F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow>
            c1 \<in> epdaS_marking_configurations G1 \<longrightarrow> c2 \<in> epdaS_marking_configurations G2))"
  apply(clarsimp)
  apply(simp add: epdaS_marking_configurations_def)
  apply(subgoal_tac "c2 \<in> epdaS_configurations G2")
   prefer 2
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def)
   apply(clarsimp)
   apply (metis (full_types) F_DPDA_SPPE__conf_old__LR_revX_preserves_configurations)
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__conf_old__LR_revX_def)
  apply(clarsimp)
  done

lemma epdaS_epdaS_SPP_StateSimRLRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant: "
(\<forall>G1 G2.
        F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow>
            (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                  (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                         (\<forall>d2. F_DPDA_SPPE__relation_step_simulation__LR2RL G1 G2 c1 e1 c1' c2
                                d2 \<longrightarrow>
                               maximum_of_domain d2 0 \<longrightarrow>
                               c1' \<notin> epdaS_marking_configurations G1)))))"
  apply(clarsimp)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
  apply(case_tac "edge_trg e1")
   apply(case_tac "edge_src e1")
    apply(clarsimp)
    apply(simp add: maximum_of_domain_def der1_def der2_def der3_def)
   apply(simp add: maximum_of_domain_def der1_def der2_def der3_def)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def der1_def der2_def der3_def)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(simp add: epdaS_marking_configurations_def F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
  apply(clarsimp)
  done

lemma epdaS_epdaS_SPP_StateSimRLRequired__inst__AX_relation_step_simulationReach: "
(\<forall>G1 G2.
        F_DPDA_SPPE__relation_structure__RL G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow>
            (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                  (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                         (\<forall>d2. epdaS.derivation G2 d2 \<longrightarrow>
                               epdaS.belongs G2 d2 \<longrightarrow>
                               the (get_configuration (d2 0)) = c2 \<longrightarrow>
                               F_DPDA_SPPE__relation_step_simulation__LR2RL G1 G2 c1 e1 c1' c2
                                d2 \<longrightarrow>
                               (\<forall>n. maximum_of_domain d2 n \<longrightarrow>
                                    F_DPDA_SPPE__relation_configuration__RL2 G1 G2 c1'
                                     (the (get_configuration (d2 n))) \<longrightarrow>
                                    (\<exists>k e2. (\<exists>c2. d2 k = Some (pair (Some e2) c2)) \<and>
                                            F_DPDA_SPPE__relation_labels__RL2 G1 G2 e1 e2) \<or>
                                    n = 0 \<and>
                                    (\<exists>e2. Ex (epdaS_step_relation G2 c2 e2) \<and>
                                          F_DPDA_SPPE__relation_labels__RL2 G1 G2 e1 e2)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_step_simulation__LR2RL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
    apply(subgoal_tac "n=0")
     apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
    apply(rule_tac
      d="(der1 (F_DPDA_SPPE__conf_old__LR_revX c1))"
      in epdaS.maximum_of_domainUnique)
      apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext)(*strict*)
   apply(rename_tac e)
   apply(rename_tac G1 G2 c1 e1 c1' n e)(*strict*)
   apply(subgoal_tac "\<exists>c. epdaS_step_relation G2 (F_DPDA_SPPE__conf_old__LR_revX c1) e c")
    apply(rename_tac G1 G2 c1 e1 c1' n e)(*strict*)
    prefer 2
    apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg e,epdaS_conf_scheduler=drop(length(option_to_list (edge_event e)))(epdaS_conf_scheduler(F_DPDA_SPPE__conf_old__LR_revX c1)),epdaS_conf_stack=edge_push e@(drop(length(edge_pop e))(epdaS_conf_stack(F_DPDA_SPPE__conf_old__LR_revX c1)))\<rparr>"
      in exI)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def epdaS_step_relation_def F_DPDA_SPPE__conf_old__LR_revX_def der1_def get_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
    apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e)}. e1 = F_DPDA_SPPE__edge_else x)")
     apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
     prefer 2
     apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' n e w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_def)
     apply(erule disjE)
      apply(rename_tac G1 G2 c1 e1 c1' n e w x)(*strict*)
      apply(simp add: F_DPDA_SPPE__edge_then_1_def)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 c1' n e)(*strict*)
      apply(simp add: option_to_list_def)
      apply(case_tac "edge_event e")
       apply(rename_tac G1 G2 c1 c1' n e)(*strict*)
       apply(clarsimp)
      apply(rename_tac G1 G2 c1 c1' n e a)(*strict*)
      apply(clarsimp)
      apply(simp add: F_DPDA_SPPE__edge_if_def)
     apply(rename_tac G1 G2 c1 e1 c1' n e w x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_2_def)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n e w)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' n e w x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_else_def)
   apply(rename_tac G1 G2 c1 e1 c1' n e)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule disjE)
    apply(erule_tac
      x="c"
      in allE)
    apply(simp add: get_configuration_def der1_def)
   apply(subgoal_tac "False")
    apply(force)
   apply(case_tac "n=0")
    prefer 2
    apply(simp add: maximum_of_domain_def get_configuration_def der2_def der1_def)
   apply(clarsimp)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e)}. e1 = F_DPDA_SPPE__edge_else x)")
    prefer 2
    apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
    apply(force)
   apply(erule disjE)
    apply(clarsimp)
    apply(simp add: epdaS_step_relation_def)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule disjE)
     apply(simp add: F_DPDA_SPPE__edge_then_1_def)
     apply(clarsimp)
     apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__conf_old__LR_revX_def F_DPDA_SPPE__relation_labels__RL2_def F_DPDA_SPPE__edge_if_def F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__conf_old__LR_revX_def F_DPDA_SPPE__relation_labels__RL2_def F_DPDA_SPPE__edge_if_def F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def)
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__conf_old__LR_revX_def F_DPDA_SPPE__relation_labels__RL2_def F_DPDA_SPPE__edge_if_def F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n q)(*strict*)
  apply(case_tac "edge_src e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e)}. e1 = F_DPDA_SPPE__edge_else x)")
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    prefer 2
    apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_SPPE__edge_if e}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)"
      in disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_def)
    apply(erule_tac
      P="e1 = F_DPDA_SPPE__edge_then_1 x"
      in disjE)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa x)(*strict*)
     apply(simp add: F_DPDA_SPPE__edge_then_1_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_2_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n q qa x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule_tac
      x="F_DPDA_SPPE__edge_else__LR \<lparr>edge_src = cons_state_or_edge_old (edge_src x), edge_event = edge_event x, edge_pop = edge_pop x, edge_push = edge_push x, edge_trg = cons_state_or_edge_old (edge_trg x)\<rparr>"
      in exI)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
   apply(simp add: F_DPDA_SPPE__edge_else__LR_def F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' n x w)(*strict*)
    apply(case_tac x)
    apply(rename_tac G1 G2 c1 c1' n x w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__edge_else_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n q epda_step_label_ext)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n q epda_step_label_ext)(*strict*)
  apply(rename_tac e)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
   apply(rule_tac
      x="(F_DPDA_SPPE__conf_old__LR_revX c1')"
      in exI)
   apply(simp add: der2_def)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. (F_DPDA_SPPE__edge_if e)}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)) \<or> (\<exists>x\<in> epda_delta G2 \<inter> { e. (\<not> F_DPDA_SPPE__edge_if e )}. e1 = F_DPDA_SPPE__edge_else x)")
   apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
   prefer 2
   apply(simp add: epda_step_labels_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_SPPE__edge_if e}. e1 \<in> F_DPDA_SPPE__edge_then x (epda_gamma G2)"
      in disjE)
   apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(erule_tac
      P="e1 = F_DPDA_SPPE__edge_then_1 x"
      in disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n q e x)(*strict*)
    apply(simp add: F_DPDA_SPPE__edge_then_1_def)
   apply(rename_tac G1 G2 c1 e1 c1' n q e x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n e X)(*strict*)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(rule disjI1)
   apply(simp add: F_DPDA_SPPE__edge_then_def)
   apply(rule disjI2)
   apply(simp add: F_DPDA_SPPE__edge_then_2_def)
  apply(rename_tac G1 G2 c1 e1 c1' n q e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n q e x)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_else_def)
  done

lemma epdaS_epdaS_SPP_StateSimRLRequired__inst___ATS_Simulation_Configuration_WeakRL_axioms: "
  ATS_Simulation_Configuration_WeakRequired_axioms epda_step_labels epdaS_step_relation
     epdaS_configurations epda_step_labels epdaS_step_relation
     F_DPDA_SPPE__relation_configuration__RL2 F_DPDA_SPPE__relation_structure__RL
     F_DPDA_SPPE__relation_step_simulation__LR2RL F_DPDA_SPPE__relation_labels__RL2
     epdaS_marking_configurations epdaS_marking_configurations"
  apply(simp add: ATS_Simulation_Configuration_WeakRequired_axioms_def)
  apply(simp add: epdaS_epdaS_SPP_StateSimRLRequired__inst__AX_relation_step_simulationReach epdaS_epdaS_SPP_StateSimRLRequired__inst__AX_relation_configuration_compatible_with_marking_configurations epdaS_epdaS_SPP_StateSimRLRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant)
  done

interpretation "epdaS_epdaS_SPP_StateSimRLRequired" : ATS_Simulation_Configuration_WeakRequired
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
  "F_DPDA_SPPE__relation_configuration__RL2"
  (* relation_initial_configuration *)
  "F_DPDA_SPPE__relation_initial_configuration__RL2"
  (* relation_effect *)
  "F_DPDA_SPPE__relation_effect__RL2"
  (* relation_TSstructure *)
  "F_DPDA_SPPE__relation_structure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_SPPE__relation_initial_simulation__LR2RL"
  (* relation_step_simulation *)
  "F_DPDA_SPPE__relation_step_simulation__LR2RL"
  (* relation_labelsLR *)
  "F_DPDA_SPPE__relation_labels__RL2"
  (* marking_configurations1 *)
  "epdaS_marking_configurations"
  (* marking_configurations2 *)
  "epdaS_marking_configurations"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_SPP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX epdaS_epdaS_SPP_StateSimRLRequired__inst___ATS_Simulation_Configuration_WeakRL_axioms )
  done

lemma F_DPDA_DRE__revert_F_DPDA_SPPE_SOUND_scheduled_case_epdaS_required_edges: "
  F_DPDA_SPPE__SpecInput G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_SPPE G' (epdaS_required_edges (F_DPDA_SPPE G')) = epdaS_required_edges G'"
  apply(rule order_antisym)
   apply(simp add: epdaS_required_edges_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>m. n+m=k")
    prefer 2
    apply(rule_tac x="k-n" in exI)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac ?G1.0="F_DPDA_SPPE G'" and ?G2.0="G'" and ?n1'="n+m" in epdaS_epdaS_SPP_StateSimRLRequired.ATS_Simulation_Configuration_WeakRequired_exists_ALT)
          apply(simp add: F_DPDA_SPPE__relation_structure__RL_def)
          apply(simp add: F_DPDA_SPPE__SpecInput_def)
         apply(simp add: F_DPDA_SPPE__SpecInput_def)
         apply(clarsimp)
         apply (metis epdaS.is_forward_deterministic_accessible_def epdaS_dependency_between_determinism_properties valid_dpda_def valid_pda_def)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="d2" in exI)
   apply(clarsimp)
   apply(rule_tac x="n2" in exI)
   apply(clarsimp)
   apply(simp add: F_DPDA_SPPE__relation_labels__RL2_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
   apply(clarsimp)
   apply(rule conjI)
    prefer 2
    apply(rule_tac x="n2'" in exI)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__relation_configuration__RL2_def epdaS_marking_configurations_def)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac ?c1.0="ca" in
      F_DPDA_SPPE__conf_old__LR_revX_preserves_configurations)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__conf_old__LR_revX_def F_DPDA_SPPE_def)
    apply(case_tac "epdaS_conf_state ca")
     apply(clarsimp)
    apply(clarsimp)
   apply(simp add: F_DPDA_SPPE_def)
   apply(erule disjE)
    apply(clarsimp)
    apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__relation_labels__LR2_def F_DPDA_SPPE__SpecInput_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def F_DPDA_SPPE__conf_old__LR_revX_def)
    apply(clarsimp)
    apply(force)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def F_DPDA_SPPE__edge_then_def F_DPDA_SPPE__edge_else_def F_DPDA_SPPE__edge_then_1_def F_DPDA_SPPE__edge_then_2_def F_DPDA_SPPE__relation_labels__LR2_def F_DPDA_SPPE__SpecInput_def F_DPDA_SPPE__edge_if_def F_DPDA_SPPE__relation_configuration__RL2_def F_DPDA_SPPE__relation_structure__RL_def F_DPDA_SPPE_def F_DPDA_SPPE__conf_old__LR_revX_def)
  apply(clarsimp)
  apply(simp add: epdaS_required_edges_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_SPPE_def)
  apply(subgoal_tac "\<exists>m. n+m=k")
   prefer 2
   apply(rule_tac x="k-n" in exI)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G2.0="F_DPDA_SPPE G'" and ?G1.0="G'" and ?n1'="n+m" in epdaS_epdaS_SPP_StateSimLRRequired.ATS_Simulation_Configuration_WeakRequired_exists_ALT)
         apply(simp add: F_DPDA_SPPE__relation_structure__LR_def)
         apply(simp add: F_DPDA_SPPE__SpecInput_def)
        apply(simp add: F_DPDA_SPPE__SpecInput_def)
        apply(clarsimp)
        apply(simp add: epdaS.is_forward_deterministic_accessible_def)
        apply(rule conjI)
         prefer 2
         apply(rule F_DPDA_SPPE__preserves_is_forward_edge_deterministic_accessible)
         apply(force)
        apply(rule epdaS_is_forward_target_deterministic_accessible)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="e2" in exI)
  apply(rule conjI)
   apply(rule_tac
      t="epda_delta SSX" 
      and s="epda_step_labels SSX" for SSX
      in ssubst)
    apply(simp add: epda_step_labels_def)
   apply(rule_tac
      i="n2" and d="d2"
      in epdaS.belongs_step_labels)
    prefer 2
    apply(force)
   apply(rule epdaS.derivation_initial_belongs)
    apply(rule F_DPDA_SPPE__preserves_epda)
    apply(simp add: F_DPDA_SPPE__SpecInput_def)
   apply(force)
  apply(rule conjI)
   apply(rule_tac x="d2" in exI)
   apply(clarsimp)
   apply(rule_tac x="n2" in exI)
   apply(clarsimp)
   apply(rule_tac x="n2'" in exI)
   apply(clarsimp)
   apply (metis (erased, hide_lams) F_DPDA_SPPE__relation_configuration__LR2_def epdaS_epdaS_SPP_StateSimLRRequired.AX_relation_configuration_compatible_with_marking_configurations)
  apply(simp add: F_DPDA_SPPE__relation_labels__LR2_def F_DPDA_DRE__revert_F_DPDA_SPPE_def)
  done

end
