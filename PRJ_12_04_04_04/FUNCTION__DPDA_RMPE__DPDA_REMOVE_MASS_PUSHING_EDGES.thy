section {*FUNCTION\_\_DPDA\_RMPE\_\_DPDA\_REMOVE\_MASS\_PUSHING\_EDGES*}
theory
  FUNCTION__DPDA_RMPE__DPDA_REMOVE_MASS_PUSHING_EDGES

imports
  PRJ_12_04_04_04__ENTRY

begin

definition mass_push_edges_splitted :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "mass_push_edges_splitted G \<equiv>
  \<not> (\<exists>e \<in> epda_delta G. F_DPDA_RMPUE__edge_if e)"

definition mass_push_edges_splitted_ALT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "mass_push_edges_splitted_ALT G \<equiv>
  \<not> (\<exists>e \<in> epda_delta G. length (edge_push e) > 2)"

lemma mass_push_edges_splitted_ALT_vs_mass_push_edges_splitted: "
  mass_push_edges_splitted_ALT G = mass_push_edges_splitted G"
  apply(simp add: F_DPDA_RMPUE__edge_if_def mass_push_edges_splitted_ALT_def mass_push_edges_splitted_def)
  apply(force)
  done

definition F_DPDA_RMPUE__edge_else__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_RMPUE__edge_else__RL e \<equiv>
  \<lparr>edge_src = case edge_src e of cons_state_or_edge_nat_old q \<Rightarrow> q,
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = case edge_trg e of cons_state_or_edge_nat_old q \<Rightarrow> q\<rparr>"

definition F_DPDA_RMPUE__edge_then_i_th__LR :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> nat
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label option"
  where
    "F_DPDA_RMPUE__edge_then_i_th__LR e i \<equiv>
  if i = 0
  then None
  else Some \<lparr>edge_src = the (F_DPDA_RMPUE__state e (i - Suc 0)),
            edge_event = None,
            edge_pop = [(rev (edge_push e)) ! (i-Suc 0)],
            edge_push = [(rev (edge_push e)) !i] @ [(rev (edge_push e)) ! (i-Suc 0)],
            edge_trg = the (F_DPDA_RMPUE__state e i)\<rparr>"

definition F_DPDA_RMPUE__conf_i_th__LR :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> nat
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf option"
  where
    "F_DPDA_RMPUE__conf_i_th__LR c e i \<equiv>
  if i<length (edge_push e)
  then Some \<lparr>epdaS_conf_state = the (F_DPDA_RMPUE__state e i),
            epdaS_conf_scheduler = epdaS_conf_scheduler c,
            epdaS_conf_stack =
                (if i = 0
                then edge_pop e
                else drop (length (edge_push e) - (Suc i)) (edge_push e))
                @ tl (epdaS_conf_stack c)\<rparr>
  else None"

definition F_DPDA_RMPUE__conf_old__LR :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_RMPUE__conf_old__LR c \<equiv>
  \<lparr>epdaS_conf_state = cons_state_or_edge_nat_old (epdaS_conf_state c),
  epdaS_conf_scheduler = epdaS_conf_scheduler c,
  epdaS_conf_stack = epdaS_conf_stack c\<rparr>"

definition F_DPDA_RMPUE__conf_old__LR_rev :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_RMPUE__conf_old__LR_rev c \<equiv>
  case epdaS_conf_state c of cons_state_or_edge_nat_old q
  \<Rightarrow> \<lparr>epdaS_conf_state = q,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = epdaS_conf_stack c\<rparr>
  | cons_state_or_edge_nat_new e n
  \<Rightarrow> \<lparr>epdaS_conf_state = edge_trg e,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = take (length (edge_push e) - Suc n) (edge_push e) @ epdaS_conf_stack c\<rparr>"

lemma F_DPDA_RMPUE__preserves_epda: "
  valid_dpda G
  \<Longrightarrow> valid_epda (F_DPDA_RMPUE G)"
  apply(simp add: valid_epda_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule finite_imageI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule finite_imageI)
   apply (metis finite_less_ub le_SucI le_refl)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp only: F_DPDA_RMPUE__edge_then_def)
   apply(rule finite_big_union2)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      s="(\<exists>m. \<forall>n\<in> N. n < m)" for N
      in ssubst)
     apply(rename_tac x)(*strict*)
     apply(rule finite_nat_set_iff_bounded)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      x="length(edge_push x)"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G xa")
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac xa)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G xa")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac xa xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: F_DPDA_RMPUE__state_def)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      in ballE)
    apply(rename_tac xa xb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa xb)(*strict*)
   apply(subgoal_tac "cons_state_or_edge_nat_new xa xb \<in> (\<lambda>i. the (if i = 0 then Some (cons_state_or_edge_nat_old (edge_src xa)) else if Suc i < length (edge_push xa) then Some (cons_state_or_edge_nat_new xa i) else if Suc i = length (edge_push xa) then Some (cons_state_or_edge_nat_old (edge_trg xa)) else None)) ` {i. Suc i \<le> length (edge_push xa)}")
    apply(rename_tac xa xb)(*strict*)
    apply(force)
   apply(rename_tac xa xb)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="xb"
      in bexI)
    apply(rename_tac xa xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa xb)(*strict*)
   apply(force)
  apply(rename_tac xa xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G. the (F_DPDA_RMPUE__state xa (Suc xb)) \<in> (\<lambda>i. the (F_DPDA_RMPUE__state x i)) ` {i. Suc i \<le> length (edge_push x)})")
    apply(rename_tac xa xb)(*strict*)
    prefer 2
    apply(rule_tac
      x="xa"
      in bexI)
     apply(rename_tac xa xb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa xb)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="Suc xb"
      in bexI)
     apply(rename_tac xa xb)(*strict*)
     apply(force)
    apply(rename_tac xa xb)(*strict*)
    apply(force)
   apply(rename_tac xa xb)(*strict*)
   apply(force)
  apply(rename_tac xa xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: suffix_def option_to_set_def)
  apply(rename_tac xa xb)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_if_def)
  apply(subgoal_tac "set(edge_push xa)\<subseteq> epda_gamma G")
   apply(rename_tac xa xb)(*strict*)
   prefer 2
   apply(rule valid_epda_push_in_gamma)
    apply(rename_tac xa xb)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac xa xb)(*strict*)
   apply(force)
  apply(rename_tac xa xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def F_DPDA_RMPUE__edge_if_def)
   apply(clarsimp)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(case_tac "rev (edge_push xa) ! xb = epda_box G")
    apply(rename_tac xa xb a aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      A="set (edge_push xa)"
      in set_mp)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(rule rev_nth_in_set)
   apply(force)
  apply(rename_tac xa xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def F_DPDA_RMPUE__edge_if_def)
   apply(clarsimp)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(case_tac "rev (edge_push xa) ! xb = epda_box G")
    apply(rename_tac xa xb a aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="[rev (edge_push xa) ! Suc xb]"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(rule_tac
      A="set (edge_push xa)"
      in set_mp)
      apply(rename_tac xa xb a aa)(*strict*)
      apply(force)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(rule rev_nth_in_set)
     apply(force)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(erule_tac
      P="edge_push xa = aa @ [epda_box G]"
      in disjE)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "rev aa ! xb \<in> set aa")
      apply(rename_tac xa xb a aa)(*strict*)
      prefer 2
      apply(rule rev_nth_in_set)
      apply(force)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(force)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb a)(*strict*)
    apply(subgoal_tac "rev (edge_push xa) ! Suc xb \<in> set(edge_push xa)")
     apply(rename_tac xa xb a)(*strict*)
     prefer 2
     apply(rule rev_nth_in_set)
     apply(force)
    apply(rename_tac xa xb a)(*strict*)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(rule_tac
      A="set (edge_push xa)"
      in set_mp)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(force)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(rule rev_nth_in_set)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(erule_tac
      P="edge_push xa = aa @ [epda_box G]"
      in disjE)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "rev aa ! xb \<in> set aa")
      apply(rename_tac xa xb a aa)(*strict*)
      prefer 2
      apply(rule rev_nth_in_set)
      apply(force)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(force)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb a)(*strict*)
    apply(subgoal_tac "rev (edge_push xa) ! Suc xb \<in> set(edge_push xa)")
     apply(rename_tac xa xb a)(*strict*)
     prefer 2
     apply(rule rev_nth_in_set)
     apply(force)
    apply(rename_tac xa xb a)(*strict*)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(rule_tac
      A="set (edge_push xa)"
      in set_mp)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(rule rev_nth_in_set)
   apply(force)
  apply(rename_tac xa xb)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac xa xb)(*strict*)
   apply(clarsimp)
   apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def F_DPDA_RMPUE__edge_if_def)
   apply(clarsimp)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(rule_tac
      A="set (edge_push xa)"
      in set_mp)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(force)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(rule rev_nth_in_set)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(erule_tac
      P="edge_push xa = aa @ [epda_box G]"
      in disjE)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xb a aa ab)(*strict*)
    apply(subgoal_tac "rev aa ! xb \<in> set aa")
     apply(rename_tac xa xb a aa ab)(*strict*)
     prefer 2
     apply(rule rev_nth_in_set)
     apply(force)
    apply(rename_tac xa xb a aa ab)(*strict*)
    apply(force)
   apply(rename_tac xa xb a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa xb a)(*strict*)
   apply(subgoal_tac "rev (edge_push xa) ! Suc xb \<in> set(edge_push xa)")
    apply(rename_tac xa xb a)(*strict*)
    prefer 2
    apply(rule rev_nth_in_set)
    apply(force)
   apply(rename_tac xa xb a)(*strict*)
   apply(force)
  apply(rename_tac xa xb)(*strict*)
  apply(clarsimp)
  apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def F_DPDA_RMPUE__edge_if_def)
  done

lemma F_DPDA_RMPUE__preserves_PDA: "
  valid_dpda G
  \<Longrightarrow> valid_pda (F_DPDA_RMPUE G)"
  apply(simp add: valid_pda_def)
  apply(rule conjI)
   apply(rule F_DPDA_RMPUE__preserves_epda)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: valid_epda_def valid_pda_def valid_dpda_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  done

theorem F_DPDA_RMPUE__preserves_read_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> read_edges_seperated (F_DPDA_RMPUE G)"
  apply(simp add: read_edges_seperated_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def FB_executing_edge_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(simp add: FB_executing_edge_def)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(simp add: strict_executing_edge_def F_DPDA_SEE__edge_else_def FB_executing_edge_def empty_push_edge_def multiple_push_edge_def)
  done

theorem F_DPDA_RMPUE__preserves_neutral_edges_removed: "
  valid_dpda G
  \<Longrightarrow> neutral_edges_removed G
  \<Longrightarrow> neutral_edges_removed (F_DPDA_RMPUE G)"
  apply(simp add: neutral_edges_removed_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "edge_pop x \<noteq> []")
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(clarsimp)
    apply(rename_tac xa xb)(*strict*)
    apply(simp add: FB_neutral_edge_def)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def FB_neutral_edge_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(force)
  done

theorem F_DPDA_RMPUE__preserves_push_and_pop_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> push_and_pop_edges_seperated (F_DPDA_RMPUE G)"
  apply(simp add: push_and_pop_edges_seperated_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: FB_neutral_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def F_DPDA_SPPE__edge_if_def)
  apply(clarsimp)
  apply(rename_tac x w b)(*strict*)
  apply(force)
  done

theorem F_DPDA_RMPUE__produces_mass_push_edges_splitted: "
  valid_dpda G
  \<Longrightarrow> mass_push_edges_splitted (F_DPDA_RMPUE G)"
  apply(simp add: mass_push_edges_splitted_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__edge_then_def)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__edge_else_def)
  done

theorem F_DPDA_RMPUE__preserves_pop_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> pop_edges_seperated G
  \<Longrightarrow> pop_edges_seperated (F_DPDA_RMPUE G)"
  apply(simp add: pop_edges_seperated_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: FB_neutral_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: strict_empty_push_edge_def empty_push_edge_def)
  apply(rename_tac e)(*strict*)
  apply(simp add: strict_empty_push_edge_def empty_push_edge_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def F_DPDA_SPPE__edge_if_def)
  done

lemma bexE_image_disj: "
  \<exists>X \<in> (f1 ` A) \<union> (f2 ` B). P X
  \<Longrightarrow> ((\<exists>X \<in> f1 ` A. P X) \<Longrightarrow> Q)
 \<Longrightarrow> ((\<exists>X \<in> f2 ` B. P X) \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  apply(force)
  done

theorem F_DPDA_RMPUE__produces_push_edges_seperated: "
  valid_dpda G
  \<Longrightarrow> valid_pda (F_DPDA_RMPUE G)
  \<Longrightarrow> read_edges_seperated (F_DPDA_RMPUE G)
  \<Longrightarrow> mass_push_edges_splitted (F_DPDA_RMPUE G)
  \<Longrightarrow> push_and_pop_edges_seperated (F_DPDA_RMPUE G)
  \<Longrightarrow> push_edges_seperated (F_DPDA_RMPUE G)"
  apply(simp add: push_and_pop_edges_seperated_def mass_push_edges_splitted_def F_DPDA_RMPUE__edge_if_def push_edges_seperated_def read_edges_seperated_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      and P="\<lambda>e. FB_executing_edge e \<longrightarrow> strict_executing_edge e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      and P="\<lambda>e. \<not> Suc (Suc 0) < length (edge_push e)"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: multiple_push_edge_def)
  apply(subgoal_tac "length (edge_push e) = Suc (Suc 0)")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (edge_pop e) = Suc 0")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: valid_pda_def)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "valid_epda_step_label (F_DPDA_RMPUE G) e")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: valid_epda_def valid_pda_def)
  apply(rename_tac e)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(simp add: strict_multiple_push_edge_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(case_tac "edge_event e")
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(simp add: FB_executing_edge_def)
   apply(simp add: strict_executing_edge_def)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_DPDA_RMPUE_def)
  apply(erule bexE_image_disj)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x)(*strict*)
   apply(simp add: FB_neutral_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(simp add: FB_executing_edge_def strict_executing_edge_def)
  apply(simp add: F_DPDA_RMPUE__edge_if_def)
  apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(erule_tac
      P="\<exists>y. edge_event x = Some y"
      in disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_push x = w' @ [x']")
   apply(rename_tac x a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x a list)(*strict*)
  apply(thin_tac "edge_push x= a # list")
  apply(clarsimp)
  apply(rename_tac x w' x')(*strict*)
  apply(simp add: suffix_def)
  done

definition F_DPDA_RMPUE__relation_structure__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_structure__LR G1 G2 \<equiv>
  valid_dpda G1
  \<and> G2 = F_DPDA_RMPUE G1
  \<and> push_and_pop_edges_seperated G1
  \<and> read_edges_seperated G1"

definition F_DPDA_RMPUE__relation_configuration__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<equiv>
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_RMPUE__conf_old__LR c1"

definition F_DPDA_RMPUE__relation_initial_configuration__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_initial_configuration__LR G1 G2 c1 c2 \<equiv>
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_RMPUE__conf_old__LR c1"

definition F_DPDA_RMPUE__relation_effect__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_effect__LR G1 G2 w1 w2 \<equiv>
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_DPDA_RMPUE__relation_structure__LR G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply (metis F_DPDA_RMPUE__preserves_epda)
  done

definition F_DPDA_RMPUE__relation_step_simulation__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label, (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e c1' c2 d \<equiv>
  if F_DPDA_RMPUE__edge_if e
  then d = (\<lambda>n.
    if n < length (edge_push e)
    then Some (pair (F_DPDA_RMPUE__edge_then_i_th__LR e n) (the (F_DPDA_RMPUE__conf_i_th__LR (F_DPDA_RMPUE__conf_old__LR c1) e n)))
    else None)
  else d = der2
    (F_DPDA_RMPUE__conf_old__LR c1)
      (F_DPDA_RMPUE__edge_else e)
    (F_DPDA_RMPUE__conf_old__LR c1')"

definition F_DPDA_RMPUE__relation_initial_simulation__LR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label, (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_initial_simulation__LR G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_RMPUE__conf_old__LR c1)"

lemma F_DPDA_RMPUE__conf_old__LR_preserves_configurations: "
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_def)
  apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE_def)
  done

lemma F_DPDA_RMPUE__conf_old__LR_preserves_initial_configurations: "
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
  apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma F_DPDA_RMPUE__conf_old__LR_preserves_marking_configurations: "
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE_def)
  apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma F_DPDA_RMPUE__initial_simulation_preserves_derivation: "
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> epdaS.derivation_initial G2 (der1 (F_DPDA_RMPUE__conf_old__LR c1))"
  apply(rule epdaS.derivation_initialI)
   apply(rule epdaS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_DPDA_RMPUE__relation_initial_configuration__LR G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_RMPUE__relation_initial_simulation__LR G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_initial_simulation__LR_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_DPDA_RMPUE__initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_initial_configuration__LR_def)
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
  apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def valid_pda_def valid_dpda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__relation_step_simulation__LR_maps_to_derivation: "
  F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_RMPUE__edge_if e1")
   apply(clarsimp)
   apply(simp add: epdaS.derivation_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac i)(*strict*)
    apply(rule conjI)
     apply(rename_tac i)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(case_tac i)
      apply(rename_tac i)(*strict*)
      apply(clarsimp)
     apply(rename_tac i nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(case_tac i)
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
     apply(simp add: F_DPDA_RMPUE__edge_then_i_th__LR_def)
    apply(rename_tac i nat)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
    apply(clarsimp)
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac i)(*strict*)
    apply(case_tac i)
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
     apply(simp add: F_DPDA_RMPUE__edge_if_def)
    apply(rename_tac i nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_i_th__LR_def)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac nat w)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(simp add: F_DPDA_RMPUE__edge_else_def F_DPDA_RMPUE__edge_then_def)
    apply(case_tac "F_DPDA_RMPUE__edge_if e1")
     apply(rename_tac nat w)(*strict*)
     apply(rule_tac
      x="e1"
      in bexI_image_disjI1)
      apply(force)
     apply(force)
    apply(rule_tac
      x="e1"
      in bexI_image_disjI2)
     apply(force)
    apply(clarsimp)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(rename_tac nat w)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(simp only: F_DPDA_RMPUE__conf_i_th__LR_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac nat w)(*strict*)
     apply(simp only: F_DPDA_RMPUE__state_def)
     apply(clarsimp)
    apply(rename_tac nat w)(*strict*)
    apply(clarsimp)
    apply(simp only: F_DPDA_RMPUE__state_def)
    apply(clarsimp)
   apply(rename_tac nat w)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(rule conjI)
     apply(rename_tac nat w)(*strict*)
     apply(clarsimp)
     apply(simp only: F_DPDA_RMPUE__conf_i_th__LR_def)
     apply(clarsimp)
     apply(simp only: F_DPDA_RMPUE__state_def)
     apply(clarsimp)
    apply(rename_tac nat w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "Suc (Suc nat)=length(edge_push e1)")
     apply(rename_tac nat w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(clarsimp)
    apply(simp only: F_DPDA_RMPUE__conf_i_th__LR_def)
    apply(clarsimp)
    apply(simp only: F_DPDA_RMPUE__state_def)
    apply(clarsimp)
   apply(rename_tac nat w)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__conf_i_th__LR_def option_to_list_def)
   apply(rename_tac nat w)(*strict*)
   apply(simp add: F_DPDA_RMPUE__conf_i_th__LR_def option_to_list_def F_DPDA_RMPUE__conf_old__LR_def)
   apply(subgoal_tac "valid_epda_step_label G1 e1")
    apply(rename_tac nat w)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac nat w)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(subgoal_tac "length (edge_pop e1) = Suc 0")
    apply(rename_tac nat w)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac nat w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>x. edge_pop e1 = [x]")
    apply(rename_tac nat w)(*strict*)
    prefer 2
    apply(case_tac "edge_pop e1")
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w a list)(*strict*)
    apply(case_tac list)
     apply(rename_tac nat w a list)(*strict*)
     apply(force)
    apply(rename_tac nat w a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat w x)(*strict*)
   apply(case_tac nat)
    apply(rename_tac nat w x)(*strict*)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
    apply(clarsimp)
    apply(simp add: push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac w x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w x)(*strict*)
    apply(simp add: suffix_def)
    apply(erule disjE)
     apply(rename_tac w x)(*strict*)
     apply(clarsimp)
     apply(rename_tac w x y)(*strict*)
     apply(simp add: read_edges_seperated_def)
     apply(erule_tac
      x="e1"
      in ballE)
      apply(rename_tac w x y)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac w x y)(*strict*)
     apply(simp add: FB_executing_edge_def)
     apply(simp add: strict_executing_edge_def)
    apply(rename_tac w x)(*strict*)
    apply(case_tac "edge_push e1")
     apply(rename_tac w x)(*strict*)
     apply(force)
    apply(rename_tac w x a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. edge_push e1 = w' @ [x']")
     apply(rename_tac w x a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w x a list)(*strict*)
    apply(thin_tac "edge_push e1= a # list")
    apply(clarify)
    apply(rename_tac w x a list w' x')(*strict*)
    apply(erule_tac
      x="w'"
      in allE)
    apply(erule_tac
      x="x'"
      in allE)
    apply(clarsimp)
    apply(rename_tac w w' x')(*strict*)
    apply(rule last_drop_rev_nth)
    apply(force)
   apply(rename_tac nat w x nata)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
   apply(clarsimp)
   apply(rename_tac w x nata)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
   apply(clarsimp)
   apply(rule_tac
      t="rev (edge_push e1) ! (Suc nata)"
      and s="drop (length (edge_push e1) - (Suc (Suc nata))) (edge_push e1) ! 0"
      in ssubst)
    apply(rename_tac w x nata)(*strict*)
    apply(rule rev_drop_nth)
    apply(force)
   apply(rename_tac w x nata)(*strict*)
   apply(rule_tac
      x="tl(drop (length (edge_push e1) - Suc (Suc nata)) (edge_push e1))@w"
      in exI)
   apply(case_tac "drop (length (edge_push e1) - Suc (Suc nata)) (edge_push e1)")
    apply(rename_tac w x nata)(*strict*)
    apply(force)
   apply(rename_tac w x nata a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac w x nata a list)(*strict*)
    apply(force)
   apply(rename_tac w x nata a list)(*strict*)
   apply(rule_tac
      t="rev (edge_push e1) ! Suc (Suc nata)"
      and s="drop (length (edge_push e1) - (Suc (Suc (Suc nata)))) (edge_push e1) ! 0"
      in ssubst)
    apply(rename_tac w x nata a list)(*strict*)
    apply(rule rev_drop_nth)
    apply(force)
   apply(rename_tac w x nata a list)(*strict*)
   apply(case_tac "drop (length (edge_push e1) - Suc (Suc (Suc nata))) (edge_push e1)")
    apply(rename_tac w x nata a list)(*strict*)
    apply(force)
   apply(rename_tac w x nata a list aa lista)(*strict*)
   apply(rule drop_nth_tl_double_head)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE__edge_else_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def F_DPDA_RMPUE__relation_structure__LR_def F_DPDA_RMPUE_def)
  apply(rule_tac
      x="e1"
      in bexI_image_disjI2)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  done

lemma F_DPDA_RMPUE__conf_i_th__LR_F_DPDA_RMPUE__conf_old__LR_preserve_configuration: "
  valid_dpda G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> epdaS_conf_stack c1 \<in> must_terminated_by (epda_gamma G1) (epda_box G1)
  \<Longrightarrow> F_DPDA_RMPUE__edge_if e1
  \<Longrightarrow> e1 \<in> epda_delta G1
  \<Longrightarrow> the (F_DPDA_RMPUE__conf_i_th__LR (F_DPDA_RMPUE__conf_old__LR c1) e1 0) \<in> epdaS_configurations (F_DPDA_RMPUE G1)"
  apply(simp add: epdaS_configurations_def F_DPDA_RMPUE__conf_i_th__LR_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(rule conjI)
   apply(rename_tac q i s)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(force)
  apply(rename_tac q i s)(*strict*)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_def)
  apply(subgoal_tac "valid_epda_step_label G1 e1")
   apply(rename_tac q i s)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__state_def F_DPDA_RMPUE_def)
  apply(rule conjI)
   apply(rename_tac q i s)(*strict*)
   apply(rule valid_epda_pop_in_gamma)
    apply(rename_tac q i s)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac q i s)(*strict*)
   apply(force)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: must_terminated_by_def may_terminated_by_def kleene_star_def append_language_def F_DPDA_RMPUE__edge_if_def)
  apply(clarsimp)
  apply(rename_tac q i x a aa ab)(*strict*)
  apply(case_tac a)
   apply(rename_tac q i x a aa ab)(*strict*)
   apply(clarsimp)
  apply(rename_tac q i x a aa ab ac list)(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_RMPUE__edge_if e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_RMPUE__relation_step_simulation__LR_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
       apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(clarsimp)
      apply(simp add: F_DPDA_RMPUE__edge_then_i_th__LR_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
     apply(rule F_DPDA_RMPUE__conf_i_th__LR_F_DPDA_RMPUE__conf_old__LR_preserve_configuration)
         apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
         apply(force)
        apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
        apply(clarsimp)
        apply(rename_tac G1 c1 e1 c1')(*strict*)
        apply(rule set_mp)
         apply(rename_tac G1 c1 e1 c1')(*strict*)
         apply(rule epdaS.get_accessible_configurations_are_configurations)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac G1 c1 e1 c1')(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
       apply(rule epda_stack_is_must_terminated_by)
        apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
        apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_RMPUE__relation_structure__LR_def)
       apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(simp add: epda_step_labels_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: get_configuration_def F_DPDA_RMPUE__conf_i_th__LR_def F_DPDA_RMPUE__relation_configuration__LR_def F_DPDA_RMPUE__conf_old__LR_def F_DPDA_RMPUE__state_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(simp add: epdaS_step_relation_def)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
    apply(subgoal_tac "\<exists>x. edge_pop e1 = [x]")
     apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' w)(*strict*)
    apply(erule_tac
      x="e1"
      in ballE)
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 c1 e1 c1' w)(*strict*)
    apply(case_tac "edge_pop e1")
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' w a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule_tac
      x="length(edge_push e1)-Suc 0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp only: maximum_of_domain_def)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(simp add: get_configuration_def)
     apply(simp add: F_DPDA_RMPUE__conf_i_th__LR_def)
     apply(rule conjI)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_if_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(simp add: F_DPDA_RMPUE__conf_old__LR_def)
     apply(rule conjI)
      apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
      apply(simp add: F_DPDA_RMPUE__state_def)
      apply(simp add: epdaS_step_relation_def)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(rule conjI)
      apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
      apply(simp add: epdaS_step_relation_def)
      apply(simp add: option_to_list_def)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
      apply(clarsimp)
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      apply(simp add: read_edges_seperated_def push_and_pop_edges_seperated_def)
      apply(erule_tac
      x="e1"
      and P="\<lambda>e1. \<not> F_DPDA_SPPE__edge_if e1"
      in ballE)
       apply(rename_tac G1 c1 e1 c1' w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      apply(erule_tac
      x="e1"
      in ballE)
       apply(rename_tac G1 c1 e1 c1' w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      apply(case_tac "edge_event e1")
       apply(rename_tac G1 c1 e1 c1' w)(*strict*)
       apply(clarsimp)
      apply(rename_tac G1 c1 e1 c1' w a)(*strict*)
      apply(clarsimp)
      apply(simp add: FB_executing_edge_def)
      apply(simp add: strict_executing_edge_def empty_push_edge_def multiple_push_edge_def F_DPDA_SPPE__edge_if_def F_DPDA_RMPUE__edge_if_def)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(simp add: epdaS_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
     apply(subgoal_tac "\<exists>x. edge_pop e1=[x]")
      apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' w)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def valid_dpda_def valid_pda_def)
     apply(clarsimp)
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     apply(erule_tac
      x="e1"
      in ballE)
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 c1 e1 c1' w)(*strict*)
     apply(case_tac "edge_pop e1")
      apply(rename_tac G1 c1 e1 c1' w)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' w a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac G1 c1 e1 c1' w a list)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' w a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_DPDA_RMPUE__relation_step_simulation__LR_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_belongs_prime)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply (metis (full_types) epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: get_configuration_def der2_def F_DPDA_RMPUE__relation_configuration__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp (no_asm) add: get_configuration_def der2_def)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
  apply(rule epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_configuration__LR F_DPDA_RMPUE__relation_structure__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_RMP_StateSimLR_inst_relation_initial_simulation epdaS_epdaS_RMP_StateSimLR_inst_relation_step_simulation epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_RMP_StateSimLR" : ATS_Simulation_Configuration_Weak
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
  "F_DPDA_RMPUE__relation_configuration__LR"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__LR"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__LR"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__LR"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_relation_step_simulation_marking_condition: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
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
   apply(simp add: epdaS_epdaS_RMP_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_RMP_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
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
      and s="F_DPDA_RMPUE__conf_old__LR ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_marking_configurations)
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
    apply(simp add: epdaS_epdaS_RMP_StateSimLR.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_RMP_StateSimLR.simulating_derivation_DEF_def)
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
      and s="F_DPDA_RMPUE__conf_old__LR c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_marking_configurations)
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

lemma epdaS_epdaS_RMP_StateSimLR_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_initial_simulation__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
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
   apply(simp add: epdaS_epdaS_RMP_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_RMP_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__LR_def)
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
      and s="F_DPDA_RMPUE__conf_old__LR ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_RMPUE__conf_old__LR_preserves_marking_configurations)
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

lemma epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_configuration__LR F_DPDA_RMPUE__relation_structure__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_RMP_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_RMP_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_RMP_StateSimLR_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_RMP_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_RMP_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_RMP_StateSimLR_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_RMPUE__relation_effect__LR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_DPDA_RMPUE__relation_effect__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_RMPUE__relation_initial_configuration__LR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_relation_initial_simulation_marked_effect: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_initial_simulation__LR G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__LR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_RMPUE__relation_effect__LR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
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
   apply(simp add: F_DPDA_RMPUE__relation_effect__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_RMPUE__relation_initial_configuration__LR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_initial_configuration__LR F_DPDA_RMPUE__relation_effect__LR F_DPDA_RMPUE__relation_structure__LR F_DPDA_RMPUE__relation_initial_simulation__LR F_DPDA_RMPUE__relation_step_simulation__LR"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_RMP_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_RMP_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_RMP_StateSimLR_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_RMP_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_RMP_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_RMP_StateSimLR_inst_relation_initial_simulation_marked_effect)
  done

interpretation "epdaS_epdaS_RMP_StateSimLR" : ATS_Simulation_Configuration_Weak_Marked_Effect
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
  "F_DPDA_RMPUE__relation_configuration__LR"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__LR"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__LR"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__LR"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__LR"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms )
  done

lemma F_DPDA_RMPUE__preserves_lang1: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_DPDA_RMPUE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in subst)
   apply (rule epdaS.AX_marked_language_finite)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_RMPUE G)"
      and s="epdaS.finite_marked_language (F_DPDA_RMPUE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_DPDA_RMPUE__preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_DPDA_RMPUE__relation_effect__LR SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_RMP_StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
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
  apply(simp add: F_DPDA_RMPUE__relation_effect__LR_def)
  done

definition F_DPDA_RMPUE__relation_TSstructure__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<equiv>
  valid_dpda G2
  \<and> G1 = F_DPDA_RMPUE G2
  \<and> push_and_pop_edges_seperated G2
  \<and> read_edges_seperated G2"

definition F_DPDA_RMPUE__relation_configuration__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1 c2 \<equiv>
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_RMPUE__conf_old__LR_rev c1"

definition F_DPDA_RMPUE__relation_initial_configuration__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_initial_configuration__RL G1 G2 c1 c2 \<equiv>
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_RMPUE__conf_old__LR_rev c1"

definition F_DPDA_RMPUE__relation_effect__RL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_effect__RL G1 G2 w1 w2 \<equiv>
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<and> w1 = w2"

definition F_DPDA_RMPUE__relation_step_simulation__LRRL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event , 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event , 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 c1 e c1' c2 d \<equiv>
  case edge_trg e of cons_state_or_edge_nat_old q
  \<Rightarrow> (case edge_src e of cons_state_or_edge_nat_old q
    \<Rightarrow> d = der2
      (F_DPDA_RMPUE__conf_old__LR_rev c1)
        (F_DPDA_RMPUE__edge_else__RL e)
      (F_DPDA_RMPUE__conf_old__LR_rev c1')
    | cons_state_or_edge_nat_new e' n
    \<Rightarrow> d = der1 (F_DPDA_RMPUE__conf_old__LR_rev c1))
  | cons_state_or_edge_nat_new e' n
  \<Rightarrow> (case edge_src e of cons_state_or_edge_nat_old q
    \<Rightarrow> d = der2
      (F_DPDA_RMPUE__conf_old__LR_rev c1)
        e'
      (F_DPDA_RMPUE__conf_old__LR_rev c1')
    | cons_state_or_edge_nat_new e' n
    \<Rightarrow> d = der1 (F_DPDA_RMPUE__conf_old__LR_rev c1))"

definition F_DPDA_RMPUE__relation_initial_simulation__LRRL :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event , 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event , 'stack) epda_step_label, ('state, 'event , 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_initial_simulation__LRRL G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_RMPUE__conf_old__LR_rev c1)"

lemma F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR_rev c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
  apply(case_tac q)
   apply(rename_tac q i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(erule disjE)
    apply(rename_tac i s qa)(*strict*)
    apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa x ia)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 x")
    apply(rename_tac i s qa x ia)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(clarsimp)
    apply(case_tac ia)
     apply(rename_tac i s qa x ia)(*strict*)
     apply(clarsimp)
    apply(rename_tac i s qa x ia nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s qa x nat)(*strict*)
    apply(case_tac "Suc (Suc nat) < length (edge_push x)")
     apply(rename_tac i s qa x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac i s qa x nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac i s qa x ia)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac q i s epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE_def)
  apply(erule disjE)
   apply(rename_tac i s epda_step_label_ext nat)(*strict*)
   apply(force)
  apply(rename_tac i s epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x ia)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac ia)
   apply(rename_tac i s epda_step_label_ext nat x ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x ia nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
  apply(case_tac "Suc (Suc nata) < length (edge_push x)")
   apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x nata)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G2 x")
   apply(rename_tac i s x nata)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x nata)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(rule_tac
      B="set (edge_push x)"
      in subset_trans)
   apply(rename_tac i s x nata)(*strict*)
   apply (metis List.set_take_subset)
  apply(rename_tac i s x nata)(*strict*)
  apply(rule valid_epda_push_in_gamma)
   apply(rename_tac i s x nata)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x nata)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__conf_old__LR_rev_preserves_initial_configurations: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR_rev c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_DPDA_RMPUE__relation_initial_configuration__RL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_RMPUE__relation_initial_simulation__LRRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_initial_simulation__LRRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_DPDA_RMPUE__relation_initial_configuration__RL_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(rule F_DPDA_RMPUE__preserves_epda)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__relation_step_simulation__LRRL_maps_to_derivation: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LRRL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac q qa)(*strict*)
    apply(clarsimp)
    apply(rule epdaS.der2_is_derivation)
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE__edge_else__RL_def)
    apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q qa w)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa w x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_then_def)
     apply(clarsimp)
     apply(rename_tac q qa w x xa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__state_def)
     apply(case_tac xa)
      apply(rename_tac q qa w x xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac q w x)(*strict*)
      apply(case_tac "Suc (Suc 0) < length (edge_push x)")
       apply(rename_tac q w x)(*strict*)
       apply(clarsimp)
      apply(rename_tac q w x)(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_if_def)
     apply(rename_tac q qa w x xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac q qa w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(clarsimp)
    apply(thin_tac " c1 \<in> epdaS.get_accessible_configurations (F_DPDA_RMPUE G2)")
    apply(rename_tac w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(case_tac x)
    apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(force)
   apply(rename_tac q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(rename_tac epda_step_label_ext nat q)(*strict*)
   prefer 2
   apply(rename_tac epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(clarsimp)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac epda_step_label_ext nat q)(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_rev_def)
  apply(clarsimp)
  apply(rename_tac epda_step_label_ext nat q w)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL_def)
  apply(clarsimp)
  apply(thin_tac "c1 \<in> epdaS.get_accessible_configurations (F_DPDA_RMPUE G2)")
  apply(rename_tac epda_step_label_ext nat q w)(*strict*)
  apply(simp add: F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac epda_step_label_ext nat q w)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac epda_step_label_ext nat q w x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac epda_step_label_ext nat q w)(*strict*)
  apply(clarsimp)
  apply(rename_tac epda_step_label_ext nat q w x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(rename_tac epda_step_label_exta nat q w x)(*strict*)
  apply(clarsimp)
  apply(rename_tac epda_step_label_ext nat q w x xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(simp add: F_DPDA_RMPUE__edge_if_def)
  apply(case_tac "Suc (Suc xa) < length (edge_push x)")
   apply(rename_tac epda_step_label_ext nat q w x xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac epda_step_label_ext nat q w x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac epda_step_label_ext q w xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac epda_step_label_ext q w xa)(*strict*)
   prefer 2
   apply(rename_tac epda_step_label_ext q w xa nat)(*strict*)
   apply(force)
  apply(rename_tac epda_step_label_ext q w xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac epda_step_label_ext w)(*strict*)
  apply(rename_tac e w)
  apply(rename_tac e w)(*strict*)
  apply(simp add: option_to_list_def)
  apply(simp add: read_edges_seperated_def)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e w)(*strict*)
  apply(case_tac "edge_event e")
   apply(rename_tac e w)(*strict*)
   prefer 2
   apply(rename_tac e w a)(*strict*)
   apply(clarsimp)
   apply(simp add: FB_executing_edge_def strict_executing_edge_def)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac e w)(*strict*)
  apply(clarsimp)
  apply(simp add: FB_executing_edge_def strict_executing_edge_def)
  apply(simp add: push_and_pop_edges_seperated_def)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e w)(*strict*)
  apply(simp add: F_DPDA_SPPE__edge_if_def)
  apply(subgoal_tac "\<exists>x. edge_pop e=[x]")
   apply(rename_tac e w)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      and P="\<lambda>e. valid_epda_step_label G2 e"
      in ballE)
    apply(rename_tac e w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e w)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e w)(*strict*)
   apply(case_tac "edge_pop e")
    apply(rename_tac e w)(*strict*)
    apply(clarsimp)
   apply(rename_tac e w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w x)(*strict*)
  apply(case_tac "edge_push e")
   apply(rename_tac e w x)(*strict*)
   apply(force)
  apply(rename_tac e w x a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_push e = w' @ [x']")
   apply(rename_tac e w x a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac e w x a list)(*strict*)
  apply(thin_tac "edge_push e= a # list")
  apply(clarsimp)
  apply(rename_tac e w w' x')(*strict*)
  apply (metis One_nat_def append_take_drop_id last_drop_rev_nth length_0_conv less_zeroE)
  done

lemma epdaS_epdaS_RMP_StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LRRL_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule F_DPDA_RMPUE__relation_step_simulation__LRRL_maps_to_derivation)
        apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LRRL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_belongs_prime)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_RMPUE__relation_structure__LR_def F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
     apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations)
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
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply (metis)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: get_configuration_def der2_def)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(simp (no_asm) add: der2_def get_configuration_def)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(rule epdaS.der1_belongs)
    apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
    apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
     apply(rule epdaS.get_accessible_configurations_are_configurations)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(rule F_DPDA_RMPUE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(thin_tac "c1 \<in> epdaS.get_accessible_configurations G1")
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q epda_step_label_ext nat w)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext nat w)(*strict*)
   apply(simp add: F_DPDA_RMPUE_def epda_step_labels_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext nat w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext nat w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(rename_tac G2 c1 e1 c1' q epda_step_label_exta nat w x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' q epda_step_label_ext nat w x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(case_tac "Suc (Suc xa) < length (edge_push x)")
     apply(rename_tac G2 c1 c1' q epda_step_label_ext nat w x xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' q epda_step_label_ext nat w x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' epda_step_label_ext nat w)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "Suc (Suc nat) = length (edge_push epda_step_label_ext)")
     apply(rename_tac G2 c1 c1' epda_step_label_ext nat w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' epda_step_label_ext nat w)(*strict*)
    apply(clarsimp)
    apply(case_tac nat)
     apply(rename_tac G2 c1 c1' epda_step_label_ext nat w)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' epda_step_label_ext nat w nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' epda_step_label_ext w nata)(*strict*)
    apply(rule take_nth_rev)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' q epda_step_label_ext nat w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' q epda_step_label_ext nat w x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule F_DPDA_RMPUE__relation_step_simulation__LRRL_maps_to_derivation)
       apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LRRL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule epdaS.der2_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations)
        apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
       apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
       apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
       apply(rule epdaS.get_accessible_configurations_are_configurations)
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
       apply(rule F_DPDA_RMPUE__preserves_epda)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def epda_step_labels_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE_def)
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(erule disjE)
      apply(rename_tac G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(clarsimp)
      apply(rename_tac G2 c1 e1 c1' epda_step_label_ext nat q x)(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_then_def)
      apply(rename_tac G2 c1 e1 c1' epda_step_label_exta nat q x)(*strict*)
      apply(clarsimp)
      apply(rename_tac G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
      apply(simp add: F_DPDA_RMPUE__state_def)
      apply(case_tac xa)
       apply(rename_tac G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
       apply(clarsimp)
       apply(rename_tac G2 c1 c1' epda_step_label_exta nat x)(*strict*)
       apply(case_tac "Suc (Suc 0) < length (edge_push x)")
        apply(rename_tac G2 c1 c1' epda_step_label_exta nat x)(*strict*)
        apply(clarsimp)
       apply(rename_tac G2 c1 c1' epda_step_label_exta nat x)(*strict*)
       apply(clarsimp)
      apply(rename_tac G2 c1 c1' epda_step_label_exta nat q x xa nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(clarsimp)
     apply(rename_tac G2 c1 c1' epda_step_label_ext nat q x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
     apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
       apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
       apply(rule F_DPDA_RMPUE__preserves_epda)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule epdaS.AX_step_relation_preserves_belongsC)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
    apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     apply(rule epdaS.get_accessible_configurations_are_configurations)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(rule F_DPDA_RMPUE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(simp add: get_configuration_def der2_def)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(simp (no_asm) add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(rule epdaS.der1_belongs)
   apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
    apply(rule epdaS.get_accessible_configurations_are_configurations)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(rule F_DPDA_RMPUE__preserves_epda)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(simp add: der1_def get_configuration_def)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(rule F_DPDA_RMPUE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(rename_tac e1 n e2 m)
  apply(rename_tac G1 G2 c1 c2 e1a c1' e1 n e2 m)(*strict*)
  apply(subgoal_tac "e1=e2 \<and> n=Suc m")
   apply(rename_tac G1 G2 c1 c2 e1a c1' e1 n e2 m)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1a c1' e1 n e2 m)(*strict*)
   apply(thin_tac "c1 \<in> epdaS.get_accessible_configurations G1")
   apply(rename_tac G1 G2 c1 e1a c1' e1 n e2 m)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1a c1' e1 n e2 m)(*strict*)
   apply(simp add: epda_step_labels_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1a c1' e1 n e2 m)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1a c1' e1 n e2 m x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' e1 n e2 m x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(case_tac "Suc (Suc xa) < length (edge_push x)")
     apply(rename_tac G2 c1 c1' e1 n e2 m x xa)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' e1 n e2 m x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' e1 e2 m xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac G2 c1 c1' e1 e2 m xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' e1 e2 m xa nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 c1 e1a c1' e1 n e2 m)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' e1 n e2 m x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G1 G2 c1 c2 e1a c1' e1 n e2 m)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1a c1' e2 m)(*strict*)
  apply(thin_tac "c1 \<in> epdaS.get_accessible_configurations G1")
  apply(rename_tac G1 G2 c1 e1a c1' e2 m)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1a c1' e2 m)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
  apply(simp only: epdaS_step_relation_def)
  apply(subgoal_tac "\<lparr>epdaS_conf_state = edge_trg e2, epdaS_conf_scheduler = option_to_list (edge_event e1a) @ epdaS_conf_scheduler c1', epdaS_conf_stack = take (length (edge_push e2) - Suc m) (edge_push e2) @ epdaS_conf_stack c1\<rparr> = \<lparr>epdaS_conf_state = edge_trg e2, epdaS_conf_scheduler = epdaS_conf_scheduler c1', epdaS_conf_stack = take (length (edge_push e2) - Suc (Suc m)) (edge_push e2) @ epdaS_conf_stack c1'\<rparr>")
   apply(rename_tac G2 c1 e1a c1' e2 m)(*strict*)
   apply(clarsimp)
  apply(rename_tac G2 c1 e1a c1' e2 m)(*strict*)
  apply(subgoal_tac "\<exists>x y. edge_pop e1a = [x] \<and> edge_push e1a = [y,x]")
   apply(rename_tac G2 c1 e1a c1' e2 m)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G2 c1 e1a c1' e2 m w)(*strict*)
   apply(simp add: epda_step_labels_def F_DPDA_RMPUE_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1a c1' e2 m w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1a c1' e2 m w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(clarsimp)
   apply(rename_tac G2 c1 e1a c1' e2 m w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' e2 m w x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G2 c1 e1a c1' e2 m)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
   apply(simp add: option_to_list_def)
   apply(simp add: F_DPDA_RMPUE_def epda_step_labels_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
    prefer 2
    apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' e2 m x y w xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
  apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
  apply(simp add: F_DPDA_RMPUE_def epda_step_labels_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
   prefer 2
   apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' e2 m x y w xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G2 c1 e1a c1' e2 m x y w)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1a c1' e2 m x y w xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 c1' e2 m w xa xb)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac xb)
   apply(rename_tac G2 c1 c1' e2 m w xa xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac G2 c1 c1' e2 m w xa xb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 c1' e2 w nat)(*strict*)
  apply(case_tac "Suc (Suc (Suc nat)) < length (edge_push e2)")
   apply(rename_tac G2 c1 c1' e2 w nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 c1' e2 w nat)(*strict*)
  apply(clarsimp)
  apply(rule take_rev_append_nth)
  apply(force)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_DPDA_RMPUE__relation_TSstructure__RL G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis F_DPDA_RMPUE__preserves_epda)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> valid_epda G2)"
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis valid_dpda_def valid_pda_def)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_configuration__RL F_DPDA_RMPUE__relation_TSstructure__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulation epdaS_epdaS_RMP_StateSimRL_step_relation_step_simulation epdaS_epdaS_RMP_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_RMP_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_RMP_StateSimRL" : ATS_Simulation_Configuration_Weak
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
  "F_DPDA_RMPUE__relation_configuration__RL"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__RL"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__RL"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_TSstructure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__LRRL"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__LRRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_DPDA_RMPUE__conf_old__LR_rev_preserves_marking_configurations: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR_rev c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE_def)
   apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac q)(*strict*)
    apply(force)
   apply(rename_tac epda_step_label_ext nat)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE_def)
   apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac q)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE_def)
    apply(clarsimp)
   apply(rename_tac epda_step_label_ext nat)(*strict*)
   apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
   apply(rename_tac epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac epda_step_label_ext nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE_def)
   apply(clarsimp)
  apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_relation_step_simulation_marking_condition: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: epdaS_epdaS_RMP_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_RMP_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
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
      and s="F_DPDA_RMPUE__conf_old__LR_rev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_marking_configurations)
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
    apply(simp add: epdaS_epdaS_RMP_StateSimRL.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_RMP_StateSimRL.simulating_derivation_DEF_def)
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
      and s="F_DPDA_RMPUE__conf_old__LR_rev c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_marking_configurations)
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
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
       apply (rule F_DPDA_RMPUE__preserves_epda)
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

lemma epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_initial_simulation__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
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
   apply(simp add: epdaS_epdaS_RMP_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_RMP_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
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
      and s="F_DPDA_RMPUE__conf_old__LR_rev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_DPDA_RMPUE__conf_old__LR_rev_preserves_marking_configurations)
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

lemma epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_configuration__RL F_DPDA_RMPUE__relation_TSstructure__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_RMP_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_RMP_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_RMP_StateSimRL_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_RMP_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_RMP_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__RL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_RMPUE__relation_effect__RL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_DPDA_RMPUE__relation_effect__RL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_RMPUE__relation_initial_configuration__RL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca q)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulation_marked_effect: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_DPDA_RMPUE__relation_initial_simulation__LRRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_DPDA_RMPUE__relation_initial_configuration__RL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_DPDA_RMPUE__relation_effect__RL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: F_DPDA_RMPUE__relation_effect__RL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_DPDA_RMPUE__relation_initial_configuration__RL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca q)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca epda_step_label_ext nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_DPDA_RMPUE__relation_configuration__RL F_DPDA_RMPUE__relation_initial_configuration__RL F_DPDA_RMPUE__relation_effect__RL F_DPDA_RMPUE__relation_TSstructure__RL F_DPDA_RMPUE__relation_initial_simulation__LRRL F_DPDA_RMPUE__relation_step_simulation__LRRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_RMP_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_RMP_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_RMP_StateSimRL_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_RMP_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_RMP_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulation_marked_effect)
  done

interpretation "epdaS_epdaS_RMP_StateSimRL" : ATS_Simulation_Configuration_Weak_Marked_Effect
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
  "F_DPDA_RMPUE__relation_configuration__RL"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__RL"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__RL"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_TSstructure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__LRRL"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__LRRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add:  epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms)
  done

lemma F_DPDA_RMPUE__preserves_lang2: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> epdaS.marked_language G \<supseteq> epdaS.marked_language (F_DPDA_RMPUE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in subst)
   apply (rule epdaS.AX_marked_language_finite)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_RMPUE G)"
      and s="epdaS.finite_marked_language (F_DPDA_RMPUE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_DPDA_RMPUE__preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_DPDA_RMPUE__relation_effect__RL SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in epdaS_epdaS_RMP_StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_effect__RL_def)
  done

theorem F_DPDA_RMPUE__preserves_lang: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_DPDA_RMPUE G)"
  apply(rule order_antisym)
   apply (metis F_DPDA_RMPUE__preserves_lang1)
  apply (metis F_DPDA_RMPUE__preserves_lang2)
  done

lemma F_DPDA_RMPUE__conf_old__LR_rev_reflects_steps_OO: "
  x \<in> epda_delta G
  \<Longrightarrow> epdaS_step_relation (F_DPDA_RMPUE G) c (F_DPDA_RMPUE__edge_else x) c1
  \<Longrightarrow> epdaS_step_relation G (F_DPDA_RMPUE__conf_old__LR_rev c) x (F_DPDA_RMPUE__conf_old__LR_rev c1)"
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def F_DPDA_RMPUE__edge_else_def)
  done

lemma F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations2: "
  valid_dpda G2
  \<Longrightarrow> c1' \<in> epdaS_configurations (F_DPDA_RMPUE G2)
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR_rev c1' \<in> epdaS_configurations G2"
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(case_tac q)
   apply(rename_tac q i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(erule disjE)
    apply(rename_tac i s qa)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac i s qa x ia)(*strict*)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(case_tac ia)
     apply(rename_tac i s qa x ia)(*strict*)
     apply(clarsimp)
     apply(rename_tac i s x)(*strict*)
     apply(subgoal_tac "valid_epda_step_label G2 x")
      apply(rename_tac i s x)(*strict*)
      apply(simp add: valid_epda_step_label_def)
     apply(rename_tac i s x)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i s qa x ia nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s qa x nat)(*strict*)
    apply(case_tac "Suc (Suc nat) < length (edge_push x)")
     apply(rename_tac i s qa x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac i s qa x nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s x nat)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G2 x")
     apply(rename_tac i s x nat)(*strict*)
     apply(simp add: valid_epda_step_label_def)
    apply(rename_tac i s x nat)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s qa)(*strict*)
   apply(clarsimp)
  apply(rename_tac q i s epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat)(*strict*)
  apply(simp add: F_DPDA_RMPUE_def)
  apply(erule disjE)
   apply(rename_tac i s epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x ia)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac ia)
   apply(rename_tac i s epda_step_label_ext nat x ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x ia nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
  apply(case_tac "Suc (Suc nata) < length (edge_push x)")
   apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x nata)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G2 x")
   apply(rename_tac i s x nata)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x nata)(*strict*)
  apply(rule conjI)
   apply(rename_tac i s x nata)(*strict*)
   apply(simp add: valid_epda_step_label_def)
  apply(rename_tac i s x nata)(*strict*)
  apply(rule_tac
      B="set (edge_push x)"
      in subset_trans)
   apply(rename_tac i s x nata)(*strict*)
   apply (metis List.set_take_subset)
  apply(rename_tac i s x nata)(*strict*)
  apply(rule valid_epda_push_in_gamma)
   apply(rename_tac i s x nata)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x nata)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__conf_old__LR_rev_preserves_steps_ON: "
  e1 \<in> epda_delta (F_DPDA_RMPUE G2)
  \<Longrightarrow> epdaS_step_relation (F_DPDA_RMPUE G2) c1' e1 c1
  \<Longrightarrow> valid_dpda G2
  \<Longrightarrow> push_and_pop_edges_seperated G2
  \<Longrightarrow> read_edges_seperated G2
  \<Longrightarrow> edge_trg e1 = cons_state_or_edge_nat_new e n
  \<Longrightarrow> edge_src e1 = cons_state_or_edge_nat_old q
  \<Longrightarrow> epdaS_step_relation G2 (F_DPDA_RMPUE__conf_old__LR_rev c1') e (F_DPDA_RMPUE__conf_old__LR_rev c1)"
  apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "n=Suc 0")
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
    apply(clarsimp)
    apply(rename_tac w x xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac w x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac w x)(*strict*)
     prefer 2
     apply(rename_tac w x xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(case_tac "Suc (Suc 0) < length (edge_push x)")
     apply(rename_tac w x)(*strict*)
     apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
   apply(clarsimp)
   apply(rename_tac w x xa)(*strict*)
   apply(case_tac "Suc (Suc xa) < length (edge_push x)")
    apply(rename_tac w x xa)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac w x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
   apply(simp add: option_to_list_def)
   apply(case_tac "edge_event e")
    apply(rename_tac w)(*strict*)
    prefer 2
    apply(rename_tac w a)(*strict*)
    apply(clarsimp)
    apply(simp add: push_and_pop_edges_seperated_def read_edges_seperated_def)
    apply(erule_tac
      x="e"
      and P="\<lambda>e. \<not> F_DPDA_SPPE__edge_if e"
      in ballE)
     apply(rename_tac w a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w a)(*strict*)
    apply(erule_tac
      x="e"
      in ballE)
     apply(rename_tac w a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w a)(*strict*)
    apply(simp add: strict_executing_edge_def F_DPDA_SPPE__edge_if_def empty_push_edge_def multiple_push_edge_def FB_executing_edge_def)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
    apply(subgoal_tac "\<exists>x. edge_pop e=[x]")
     apply(rename_tac w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac w a)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(simp add: push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(case_tac "edge_push e")
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. edge_push e = w' @ [x']")
    apply(rename_tac w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w a list)(*strict*)
   apply(thin_tac "edge_push e= a # list")
   apply(clarsimp)
   apply(rename_tac w w' x')(*strict*)
   apply (metis Suc_length Suc_lessD butn_def hd_conv_nth hd_rev length_0_conv length_drop length_rotate1 not_Cons_self nth_drop_0 rotate_simps take_1_rev take_eq_Nil take_last list.sel(2))
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(rename_tac w x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  done

lemma F_DPDA_RMPUE__state_injective: "
  the (F_DPDA_RMPUE__state xa x) = the (F_DPDA_RMPUE__state xa xb)
  \<Longrightarrow> Suc x < length (edge_push xa)
  \<Longrightarrow> Suc xb < length (edge_push xa)
  \<Longrightarrow> x = xb"
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac x)
   apply(clarsimp)
   apply(case_tac xb)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(case_tac xb)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat nata)(*strict*)
  apply(clarsimp)
  done

lemma RMP_edge_pop_is_single: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> x \<in> epda_delta G
  \<Longrightarrow> F_DPDA_RMPUE__edge_if x
  \<Longrightarrow> \<exists>y. edge_pop x = [y]"
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in ballE)
   prefer 2
   apply(force)
  apply(case_tac "edge_pop x")
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(case_tac "list")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rename_tac a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma RMP_edge_event_is_none: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> x \<in> epda_delta G
  \<Longrightarrow> F_DPDA_RMPUE__edge_if x
  \<Longrightarrow> edge_event x = None"
  apply(simp add: F_DPDA_RMPUE__edge_if_def read_edges_seperated_def push_and_pop_edges_seperated_def)
  apply(simp add: FB_executing_edge_def empty_push_edge_def multiple_push_edge_def F_DPDA_SPPE__edge_if_def)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. (\<exists>y. edge_event x = Some y) \<or> (\<forall>w b. edge_push x = w @ [b] \<longrightarrow> edge_pop x = [b])"
      in ballE)
   prefer 2
   apply(force)
  apply(erule_tac
      x="x"
      in ballE)
   prefer 2
   apply(force)
  apply(case_tac "edge_push x")
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_push x = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "edge_push x= a # list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(case_tac "edge_event x")
   apply(rename_tac w' x')(*strict*)
   apply(force)
  apply(rename_tac w' x' a)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_executing_edge_def)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac w' x' a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w' x' a)(*strict*)
  apply(case_tac "edge_pop x")
   apply(rename_tac w' x' a)(*strict*)
   apply(force)
  apply(rename_tac w' x' a aa list)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__edge_then_not_between_OO: "
  edge_src e1 = cons_state_or_edge_nat_old q
  \<Longrightarrow> edge_trg e1 = cons_state_or_edge_nat_old qa
  \<Longrightarrow> e1 \<in> F_DPDA_RMPUE__edge_then x
  \<Longrightarrow> x \<in> epda_delta G
  \<Longrightarrow> F_DPDA_RMPUE__edge_if x
  \<Longrightarrow> Q"
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac xa)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(case_tac "Suc (Suc 0) < length (edge_push x)")
    apply(force)
   apply(simp add: F_DPDA_RMPUE__edge_if_def)
  apply(rename_tac xa nat)(*strict*)
  apply(clarsimp)
  done

theorem F_DPDA_RMPUE__preserves_is_forward_edge_deterministic_accessible: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible (F_DPDA_RMPUE G)"
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
  apply(subgoal_tac "e1 \<in> epda_delta (F_DPDA_RMPUE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (F_DPDA_RMPUE G)")
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
      x="F_DPDA_RMPUE__conf_old__LR_rev c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="F_DPDA_RMPUE__conf_old__LR_rev c1"
      in allE)
   apply(erule_tac
      x="F_DPDA_RMPUE__conf_old__LR_rev c2"
      in allE)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G \<inter> Collect F_DPDA_RMPUE__edge_if. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G \<inter> {e. \<not> F_DPDA_RMPUE__edge_if e}. e1 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G \<inter> Collect F_DPDA_RMPUE__edge_if. e2 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G \<inter> {e. \<not> F_DPDA_RMPUE__edge_if e}. e2 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(subgoal_tac "F_DPDA_RMPUE__conf_old__LR_rev c \<in> epdaS.get_accessible_configurations G")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(thin_tac "F_DPDA_RMPUE__conf_old__LR_rev c \<notin> epdaS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(rule_tac
      ?c1.0="c"
      in epdaS_epdaS_RMP_StateSimRL.get_accessible_configurations_transfer)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply (metis F_DPDA_RMPUE__conf_old__LR_rev_preserves_configurations2 F_DPDA_RMPUE__preserves_epda epdaS.get_accessible_configurations_are_configurations2)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(rename_tac c c1 c2 e1 e2 cA cB)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1=edge_src e2")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(rename_tac c c1 c2 e1 e2 q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_trg e1")
    apply(rename_tac c c1 c2 e1 e2 q qa)(*strict*)
    apply(erule_tac
      P="\<exists>x\<in> epda_delta G \<inter> Collect F_DPDA_RMPUE__edge_if. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
     apply(rename_tac c c1 c2 e1 e2 q qa)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 q qa x)(*strict*)
     apply(rule_tac
      q="q"
      and ?e1.0="e1"
      in F_DPDA_RMPUE__edge_then_not_between_OO)
         apply(rename_tac c c1 c2 e1 e2 q qa x)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 q qa x)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 q qa x)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 q qa x)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q qa x)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 q qa)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e2 q qa x)(*strict*)
    apply(erule_tac
      x="x"
      in allE)
    apply(subgoal_tac "epdaS_step_relation G (F_DPDA_RMPUE__conf_old__LR_rev c) x (F_DPDA_RMPUE__conf_old__LR_rev c1)")
     apply(rename_tac c c1 c2 e2 q qa x)(*strict*)
     prefer 2
     apply(rule F_DPDA_RMPUE__conf_old__LR_rev_reflects_steps_OO)
      apply(rename_tac c c1 c2 e2 q qa x)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e2 q qa x)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e2 q qa x)(*strict*)
    apply(clarsimp)
    apply(case_tac "edge_trg e2")
     apply(rename_tac c c1 c2 e2 q qa x qb)(*strict*)
     apply(erule disjE)
      apply(rename_tac c c1 c2 e2 q qa x qb)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 e2 q qa x qb xa)(*strict*)
      apply(rule_tac
      q="q"
      and ?e1.0="e2"
      in F_DPDA_RMPUE__edge_then_not_between_OO)
          apply(rename_tac c c1 c2 e2 q qa x qb xa)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e2 q qa x qb xa)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e2 q qa x qb xa)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e2 q qa x qb xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e2 q qa x qb xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e2 q qa x qb)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 q qa x qb xa)(*strict*)
     apply(erule_tac
      x="xa"
      in allE)
     apply(erule impE)
      apply(rename_tac c c1 c2 q qa x qb xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac c c1 c2 q qa x qb xa)(*strict*)
     apply(rule F_DPDA_RMPUE__conf_old__LR_rev_reflects_steps_OO)
      apply(rename_tac c c1 c2 q qa x qb xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 q qa x qb xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e2 q qa x epda_step_label_ext nat)(*strict*)
    apply(rename_tac e n)
    apply(rename_tac c c1 c2 e2 q qa x e n)(*strict*)
    apply(erule disjE)
     apply(rename_tac c c1 c2 e2 q qa x e n)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
     apply(erule_tac
      x="e"
      in allE)
     apply(erule impE)
      apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(rename_tac c c1 c2 e2 q qa e n xa)(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_then_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q qa e n xa x)(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_else_def)
      apply(simp add: epdaS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q e n xa x w wa wb)(*strict*)
      apply(simp add: F_DPDA_RMPUE__state_def)
      apply(case_tac "Suc (Suc x) < length (edge_push xa)")
       apply(rename_tac c c1 c2 q e n xa x w wa wb)(*strict*)
       apply(clarsimp)
      apply(rename_tac c c1 c2 q e n xa x w wa wb)(*strict*)
      apply(clarsimp)
     apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
     apply(rule_tac
      q="q"
      in F_DPDA_RMPUE__conf_old__LR_rev_preserves_steps_ON)
           apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
           prefer 2
           apply(force)
          apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e2 q qa x e n xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e2 q qa x e n)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 q qa x e n xa)(*strict*)
    apply(erule_tac
      x="xa"
      in allE)
    apply(erule impE)
     apply(rename_tac c c1 c2 q qa x e n xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c c1 c2 q qa x e n xa)(*strict*)
    apply(rule F_DPDA_RMPUE__conf_old__LR_rev_reflects_steps_OO)
     apply(rename_tac c c1 c2 q qa x e n xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 q qa x e n xa)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 q epda_step_label_ext nat)(*strict*)
   apply(rename_tac e n)
   apply(rename_tac c c1 c2 e1 e2 q e n)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G \<inter> Collect F_DPDA_RMPUE__edge_if. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
    apply(rename_tac c c1 c2 e1 e2 q e n)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
    apply(erule_tac
      x="e"
      in allE)
    apply(subgoal_tac "epdaS_step_relation G (F_DPDA_RMPUE__conf_old__LR_rev c) e (F_DPDA_RMPUE__conf_old__LR_rev c1)")
     apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
     prefer 2
     apply(rule_tac
      q="q"
      in F_DPDA_RMPUE__conf_old__LR_rev_preserves_steps_ON)
           apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
           prefer 2
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 q e n x)(*strict*)
    apply(clarsimp)
    apply(case_tac "edge_trg e2")
     apply(rename_tac c c1 c2 e1 e2 q e n x qa)(*strict*)
     apply(erule disjE)
      apply(rename_tac c c1 c2 e1 e2 q e n x qa)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 e1 e2 q e n x qa xa)(*strict*)
      apply(rule_tac
      q="q"
      in F_DPDA_RMPUE__edge_then_not_between_OO)
          apply(rename_tac c c1 c2 e1 e2 q e n x qa xa)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 q e n x qa xa)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 q e n x qa xa)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 q e n x qa xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 q e n x qa xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q e n x qa)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 q e n x qa xa)(*strict*)
     apply(erule_tac
      x="xa"
      in allE)
     apply(erule impE)
      apply(rename_tac c c1 c2 e1 q e n x qa xa)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(rename_tac c c1 c2 e1 q n x qa xa)(*strict*)
      apply(simp add: epdaS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 e1 q n x qa xa w wa wb)(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__edge_else_def F_DPDA_RMPUE__state_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q n x xa w wa wb xb)(*strict*)
      apply(case_tac "Suc (Suc xb) < length (edge_push x)")
       apply(rename_tac c c1 c2 q n x xa w wa wb xb)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac c c1 c2 q n x xa w wa wb xb)(*strict*)
      apply(clarsimp)
     apply(rename_tac c c1 c2 e1 q e n x qa xa)(*strict*)
     apply(rule F_DPDA_RMPUE__conf_old__LR_rev_reflects_steps_OO)
      apply(rename_tac c c1 c2 e1 q e n x qa xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 q e n x qa xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 q e n x epda_step_label_ext nat)(*strict*)
    apply(rename_tac e n)
    apply(rename_tac c c1 c2 e1 e2 q ea na x e n)(*strict*)
    apply(erule disjE)
     apply(rename_tac c c1 c2 e1 e2 q ea na x e n)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
     apply(erule_tac
      x="e"
      in allE)
     apply(subgoal_tac "epdaS_step_relation G (F_DPDA_RMPUE__conf_old__LR_rev c) e (F_DPDA_RMPUE__conf_old__LR_rev c2)")
      apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
      prefer 2
      apply(rule_tac
      q="q"
      in F_DPDA_RMPUE__conf_old__LR_rev_preserves_steps_ON)
            apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
            prefer 2
            apply(force)
           apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q ea na x e n xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
     apply(subgoal_tac "F_DPDA_RMPUE__conf_old__LR_rev c1=F_DPDA_RMPUE__conf_old__LR_rev c2")
      apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
      prefer 2
      apply(simp add: epdaS_step_relation_def)
      apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "n=Suc 0")
      apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
      prefer 2
      apply(thin_tac "edge_trg e1 = cons_state_or_edge_nat_new e na")
      apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
      apply(rename_tac c c1 c2 e1 e2 q x e n xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q x e n xa xb xc)(*strict*)
      apply(case_tac xc)
       apply(rename_tac c c1 c2 q x e n xa xb xc)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 q x e n xa xb)(*strict*)
       apply(case_tac "Suc (Suc 0) < length (edge_push xa)")
        apply(rename_tac c c1 c2 q x e n xa xb)(*strict*)
        apply(clarsimp)
       apply(rename_tac c c1 c2 q x e n xa xb)(*strict*)
       apply(clarsimp)
      apply(rename_tac c c1 c2 q x e n xa xb xc nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q x e n xa xb nat)(*strict*)
      apply(case_tac "Suc (Suc (Suc nat)) < length (edge_push xa)")
       apply(rename_tac c c1 c2 q x e n xa xb nat)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac c c1 c2 q x e n xa xb nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q x e xb nat)(*strict*)
      apply(case_tac "epdaS_conf_state c")
       apply(rename_tac c c1 c2 q x e xb nat qa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 q x e xb nat epda_step_label_exta nata)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
     apply(subgoal_tac "na=Suc 0")
      apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
      prefer 2
      apply(thin_tac "edge_trg e2 = cons_state_or_edge_nat_new e n")
      apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q na x e xa xb xc)(*strict*)
      apply(case_tac xb)
       apply(rename_tac c c1 c2 q na x e xa xb xc)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 q na x e xa xc)(*strict*)
       apply(case_tac "Suc (Suc 0) < length (edge_push x)")
        apply(rename_tac c c1 c2 q na x e xa xc)(*strict*)
        apply(clarsimp)
       apply(rename_tac c c1 c2 q na x e xa xc)(*strict*)
       apply(clarsimp)
      apply(rename_tac c c1 c2 q na x e xa xb xc nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q na x e xa xc nat)(*strict*)
      apply(case_tac "Suc (Suc (Suc nat)) < length (edge_push x)")
       apply(rename_tac c c1 c2 q na x e xa xc nat)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac c c1 c2 q na x e xa xc nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 q e xa xc nat)(*strict*)
      apply(case_tac "epdaS_conf_state c")
       apply(rename_tac c c1 c2 q e xa xc nat qa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 q e xa xc nat epda_step_label_exta nata)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q na x e n xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 q x e xa)(*strict*)
     apply(subgoal_tac "c1=c2")
      apply(rename_tac c c1 c2 e1 e2 q x e xa)(*strict*)
      apply(rule_tac
      G="F_DPDA_RMPUE G"
      in epdaS_step_relation_injective_on_edge)
        apply(rename_tac c c1 c2 e1 e2 q x e xa)(*strict*)
        apply (metis F_DPDA_RMPUE__preserves_PDA)
       apply(rename_tac c c1 c2 e1 e2 q x e xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 q x e xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 q x e xa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__conf_old__LR_rev_def)
     apply(simp add: epdaS_step_relation_def)
    apply(rename_tac c c1 c2 e1 e2 q ea na x e n)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 q ea na x e n xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac c c1 c2 e1 e2 q e n)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e2 q e n x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac c c1 c2 e1 e2 epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e n)
  apply(rename_tac c c1 c2 e1 e2 e n)(*strict*)
  apply(erule_tac
      P="\<exists>x\<in> epda_delta G \<inter> Collect F_DPDA_RMPUE__edge_if. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2 e n)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac c c1 c2 e2 e n x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac c c1 c2 e2 e n x q)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e2 e n x epda_step_label_exta nat)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 e n)(*strict*)
  apply(erule disjE)
   apply(rename_tac c c1 c2 e1 e2 e n)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e n x xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac c c1 c2 e1 e n x xa q)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e n x xa epda_step_label_exta nat)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 e n x xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e n x xa xb xc)(*strict*)
  apply(case_tac xb)
   apply(rename_tac c c1 c2 e n x xa xb xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e n x xa xc)(*strict*)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac c c1 c2 e n x xa xc q)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e n x xa xc epda_step_label_exta nat)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e n x xa xb xc nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e n x xa xc nat)(*strict*)
  apply(case_tac xc)
   apply(rename_tac c c1 c2 e n x xa xc nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e n x xa nat)(*strict*)
   apply(case_tac "epdaS_conf_state c")
    apply(rename_tac c c1 c2 e n x xa nat q)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e n x xa nat epda_step_label_exta nata)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e n x xa xc nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e n x xa nat nata)(*strict*)
  apply(subgoal_tac "nat=nata")
   apply(rename_tac c c1 c2 e n x xa nat nata)(*strict*)
   prefer 2
   apply (metis DT_state_or_edge_nat.simps(2) nat.inject)
  apply(rename_tac c c1 c2 e n x xa nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e n x xa nata)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e n x xa nata w)(*strict*)
  apply(case_tac "epdaS_conf_state c")
   apply(rename_tac c c1 c2 e n x xa nata w q)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e n x xa nata w epda_step_label_exta nat)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__preserves_DPDA: "
  valid_dpda G
  \<Longrightarrow> push_and_pop_edges_seperated G
  \<Longrightarrow> read_edges_seperated G
  \<Longrightarrow> valid_dpda (F_DPDA_RMPUE G)"
  apply(simp (no_asm) add: valid_dpda_def)
  apply(rule conjI)
   apply(rule F_DPDA_RMPUE__preserves_PDA)
   apply(force)
  apply (metis F_DPDA_RMPUE__preserves_is_forward_edge_deterministic_accessible)
  done

definition F_DPDA_RMPUE__conf_old__LR_revX :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_DPDA_RMPUE__conf_old__LR_revX c \<equiv>
  case epdaS_conf_state c of cons_state_or_edge_nat_old q
  \<Rightarrow> \<lparr>epdaS_conf_state = q,
     epdaS_conf_scheduler = epdaS_conf_scheduler c,
     epdaS_conf_stack = epdaS_conf_stack c\<rparr>
  | cons_state_or_edge_nat_new e n
  \<Rightarrow> \<lparr>epdaS_conf_state = edge_src e,
     epdaS_conf_scheduler = epdaS_conf_scheduler c,
     epdaS_conf_stack = (edge_pop e) @ drop (Suc n) (epdaS_conf_stack c)\<rparr>"

definition F_DPDA_RMPUE__relation_labels__LR2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_labels__LR2 G1 G2 e1 e2 \<equiv>
  F_DPDA_RMPUE__relation_structure__LR G1 G2
  \<and> e1 \<in> F_DPDA_DRE__revert_F_DPDA_RMPUE G1 {e2}"

definition F_DPDA_RMPUE__relation_labels__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_labels__RL2 G1 G2 e2 e1 \<equiv>
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<and> e1 \<in> F_DPDA_DRE__revert_F_DPDA_RMPUE G2 {e2}"

lemma epdaS_epdaS_RMP_StateSimLRReach_ATS_Simulation_Configuration_WeakReach_axioms: "
  ATS_Simulation_Configuration_WeakReach_axioms epda_step_labels epdaS_step_relation epdaS_configurations epda_step_labels epdaS_step_relation F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_structure__LR F_DPDA_RMPUE__relation_step_simulation__LR F_DPDA_RMPUE__relation_labels__LR2"
  apply(simp add: ATS_Simulation_Configuration_WeakReach_axioms_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def epda_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_RMPUE__edge_if e1")
   apply(rename_tac G1 c1 e1 c1' d2 n)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(subgoal_tac "Suc 0 < length (edge_push e1)")
    apply(rename_tac G1 c1 e1 c1' n)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__edge_then_i_th__LR_def)
   apply(simp add: F_DPDA_RMPUE__relation_labels__LR2_def)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(rule disjI1)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' d2 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule_tac
      x="(F_DPDA_RMPUE__edge_else e1)"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G1 c1 e1 c1' n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_labels__LR2_def)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
  apply(rename_tac G1 c1 e1 c1' n)(*strict*)
  apply(simp only: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(clarsimp)
  done

interpretation "epdaS_epdaS_RMP_StateSimLRReach" : ATS_Simulation_Configuration_WeakReach
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
  "F_DPDA_RMPUE__relation_configuration__LR"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__LR"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__LR"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__LR"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__LR"
  (* relation_labelsLR *)
  "F_DPDA_RMPUE__relation_labels__LR2"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLRReach_ATS_Simulation_Configuration_WeakReach_axioms)
  done

definition F_DPDA_RMPUE__relation_configuration__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 c2 \<equiv>
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_DPDA_RMPUE__conf_old__LR_revX c1"

definition F_DPDA_RMPUE__relation_initial_configuration__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_initial_configuration__RL2 G1 G2 c1 c2 \<equiv>
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_DPDA_RMPUE__conf_old__LR_revX c1"

definition F_DPDA_RMPUE__relation_initial_simulation__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event , 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event , 'stack) epda_step_label, ('state, 'event , 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_initial_simulation__RL2 G1 G2 c1 d \<equiv>
  d = der1 (F_DPDA_RMPUE__conf_old__LR_revX c1)"

definition F_DPDA_RMPUE__relation_step_simulation__RL2 :: "
  (('state, 'event, 'stack) DT_state_or_edge_nat, 'event , 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event , 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__relation_step_simulation__RL2 G1 G2 c1 e c1' c2 d \<equiv>
  case edge_trg e of cons_state_or_edge_nat_old q
  \<Rightarrow> (case edge_src e of cons_state_or_edge_nat_old q
    \<Rightarrow> d = der2
      (F_DPDA_RMPUE__conf_old__LR_revX c1)
        (F_DPDA_RMPUE__edge_else__RL e)
      (F_DPDA_RMPUE__conf_old__LR_revX c1')
    | cons_state_or_edge_nat_new e' n
    \<Rightarrow> d = der2
      (F_DPDA_RMPUE__conf_old__LR_revX c1)
        e'
      (F_DPDA_RMPUE__conf_old__LR_revX c1'))
    | cons_state_or_edge_nat_new e' n
  \<Rightarrow> (case edge_src e of cons_state_or_edge_nat_old q
    \<Rightarrow> d = der1 (F_DPDA_RMPUE__conf_old__LR_revX c1)
    | cons_state_or_edge_nat_new e' n
    \<Rightarrow> d = der1 (F_DPDA_RMPUE__conf_old__LR_revX c1))"

lemma F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR_revX c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
  apply(case_tac q)
   apply(rename_tac q i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(erule disjE)
    apply(rename_tac i s qa)(*strict*)
    apply(clarsimp)
   apply(rename_tac i s qa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s qa x ia)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 x")
    apply(rename_tac i s qa x ia)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(clarsimp)
    apply(case_tac ia)
     apply(rename_tac i s qa x ia)(*strict*)
     apply(clarsimp)
    apply(rename_tac i s qa x ia nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s qa x nat)(*strict*)
    apply(case_tac "Suc (Suc nat) < length (edge_push x)")
     apply(rename_tac i s qa x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac i s qa x nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac i s qa x ia)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac q i s epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE_def)
  apply(erule disjE)
   apply(rename_tac i s epda_step_label_ext nat)(*strict*)
   apply(force)
  apply(rename_tac i s epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x ia)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac ia)
   apply(rename_tac i s epda_step_label_ext nat x ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x ia nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
  apply(case_tac "Suc (Suc nata) < length (edge_push x)")
   apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i s epda_step_label_ext nat x nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s x nata)(*strict*)
  apply(subgoal_tac "valid_epda_step_label G2 x")
   apply(rename_tac i s x nata)(*strict*)
   prefer 2
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i s x nata)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(rule conjI)
   apply(rename_tac i s x nata)(*strict*)
   apply(rule valid_epda_pop_in_gamma)
    apply(rename_tac i s x nata)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s x nata)(*strict*)
   apply(force)
  apply(rename_tac i s x nata)(*strict*)
  apply (metis set_drop_subset subset_trans)
  done

lemma F_DPDA_RMPUE__conf_old__LR_revX_preserves_initial_configurations: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_DPDA_RMPUE__conf_old__LR_revX c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
  apply(rule conjI)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulationX: "
  (\<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_DPDA_RMPUE__relation_initial_configuration__RL2 G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_DPDA_RMPUE__relation_initial_simulation__RL2 G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_initial_simulation__RL2_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_DPDA_RMPUE__conf_old__LR_revX_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_DPDA_RMPUE__relation_initial_configuration__RL2_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(rule F_DPDA_RMPUE__preserves_epda)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma pre_states_are_also_new: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> ea \<in> epda_delta G2
  \<Longrightarrow> F_DPDA_RMPUE__edge_if ea
  \<Longrightarrow> Suc (Suc (Suc n)) = length (edge_push ea)
  \<Longrightarrow> epdaS.derivation_initial G1 d
  \<Longrightarrow> d i = Some (pair e \<lparr>epdaS_conf_state = cons_state_or_edge_nat_new ea (Suc n), epdaS_conf_scheduler = option_to_list None @ epdaS_conf_scheduler c1', epdaS_conf_stack = rev (edge_push ea) ! Suc n # w\<rparr>)
  \<Longrightarrow> k \<le> n
  \<Longrightarrow> k \<le> i \<and> epdaS_conf_state (the (get_configuration (d (i - k)))) = cons_state_or_edge_nat_new ea (Suc n - k)"
  apply(induct k)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (i-k) = Some (pair e c)")
   apply(rename_tac k)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac k)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac k)(*strict*)
    apply(rule epdaS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k eb c)(*strict*)
  apply(case_tac "k=i")
   apply(rename_tac k eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac eb c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE_def)
  apply(rename_tac k eb c)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac k eb c)(*strict*)
   apply(clarsimp)
  apply(rename_tac k eb c nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (nat-k) = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaS_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac k eb c nat)(*strict*)
   prefer 2
   apply(rule epdaS.step_detail_before_some_position)
     apply(rename_tac k eb c nat)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(force)
    apply(rename_tac k eb c nat)(*strict*)
    apply(force)
   apply(rename_tac k eb c nat)(*strict*)
   apply(force)
  apply(rename_tac k eb c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac k eb c nat e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac k eb c nat e1 e2 c1 c2 wa)(*strict*)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e2 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e2 = F_DPDA_RMPUE__edge_else x)")
   apply(rename_tac k eb c nat e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(blast)
  apply(rename_tac k eb c nat e1 e2 c1 c2 wa)(*strict*)
  apply(erule disjE)
   apply(rename_tac k eb c nat e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac k eb c nat e1 c1 c2 wa x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply (metis F_DPDA_RMPUE__edge_else_def DT_state_or_edge_nat.simps(3) Suc_diff_le equal_derivation_conf_coincide le_SucE)
  apply(rename_tac k eb c nat e1 e2 c1 c2 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k eb c nat e1 e2 c1 c2 wa x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
  apply(clarsimp)
  apply(rename_tac k eb c nat e1 c1 c2 wa x xa)(*strict*)
  apply(subgoal_tac "Suc nat - k=Suc (nat-k)")
   apply(rename_tac k eb c nat e1 c1 c2 wa x xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k eb c nat e1 c1 c2 wa x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k c nat e1 c1 wa x xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac k c nat e1 c1 wa x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k c nat e1 c1 wa x)(*strict*)
   apply(case_tac "Suc (Suc 0) < length (edge_push x)")
    apply(rename_tac k c nat e1 c1 wa x)(*strict*)
    apply(clarsimp)
   apply(rename_tac k c nat e1 c1 wa x)(*strict*)
   apply(clarsimp)
  apply(rename_tac k c nat e1 c1 wa x xa nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac k c nat e1 c1 wa x nata)(*strict*)
  apply(case_tac "Suc (Suc (Suc nata)) < length (edge_push x)")
   apply(rename_tac k c nat e1 c1 wa x nata)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac k c nat e1 c1 wa x nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac k c nat e1 c1 wa nata)(*strict*)
  apply (metis Suc_leD Suc_le_mono diff_Suc_Suc diff_diff_cancel diff_le_self le_Suc_eq)
  done

lemma stack_content_translates_back: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> ea \<in> epda_delta G2
  \<Longrightarrow> F_DPDA_RMPUE__edge_if ea
  \<Longrightarrow> Suc (Suc (Suc n)) = length (edge_push ea)
  \<Longrightarrow> epdaS.derivation_initial G1 d
  \<Longrightarrow> d i = Some (pair e \<lparr>epdaS_conf_state = cons_state_or_edge_nat_new ea (Suc n), epdaS_conf_scheduler = option_to_list None @ epdaS_conf_scheduler c1', epdaS_conf_stack = rev (edge_push ea) ! Suc n # w\<rparr>)
  \<Longrightarrow> \<forall>k\<le>n. k \<le> i \<and> epdaS_conf_state (the (get_configuration (d (i - k)))) = cons_state_or_edge_nat_new ea (Suc n - k)
  \<Longrightarrow> d (i - n) = Some (pair eb c)
  \<Longrightarrow> i \<noteq> n
  \<Longrightarrow> d (i - Suc n) = Some (pair ec ca)
  \<Longrightarrow> k \<le> Suc n
  \<Longrightarrow> epdaS_conf_stack (the (get_configuration (d (i - Suc n + k)))) = drop (length (edge_push ea) - Suc k) (edge_push ea) @ drop (Suc 0) (epdaS_conf_stack ca)"
  apply(induct k)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (i-Suc n) = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaS_step_relation SSG c1 e2 c2" for SSd SSn SSG)
    prefer 2
    apply(rule epdaS.step_detail_before_some_position)
      apply(simp add: epdaS.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rename_tac e2 c2)(*strict*)
   apply(subgoal_tac "Suc(i-Suc n)=i-n")
    apply(rename_tac e2 c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac e2)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e2 wa)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e2 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e2 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac e2 wa)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac e2 wa)(*strict*)
   apply(erule disjE)
    apply(rename_tac e2 wa)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac wa x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(erule_tac
      x="n"
      in allE)
    apply(clarsimp)
   apply(rename_tac e2 wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e2 wa x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
   apply(clarsimp)
   apply(rename_tac wa x xa)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac wa x xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac wa x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac wa x)(*strict*)
    apply(case_tac "Suc (Suc 0) < length (edge_push x)")
     apply(rename_tac wa x)(*strict*)
     apply(clarsimp)
     apply(rename_tac wa)(*strict*)
     apply(case_tac "edge_push ea")
      apply(rename_tac wa)(*strict*)
      apply(force)
     apply(rename_tac wa a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. edge_push ea = w' @ [x']")
      apply(rename_tac wa a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac wa a list)(*strict*)
     apply(thin_tac "edge_push ea = a # list")
     apply(clarsimp)
    apply(rename_tac wa x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(rename_tac wa x xa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac wa x nat)(*strict*)
   apply(case_tac "Suc (Suc nat) < length (edge_push x)")
    apply(rename_tac wa x nat)(*strict*)
    apply(clarsimp)
    apply(case_tac "Suc (Suc (Suc nat)) < length (edge_push x)")
     apply(rename_tac wa x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac wa x nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac wa x nat)(*strict*)
   apply(subgoal_tac "Suc (Suc nat) = length (edge_push x)")
    apply(rename_tac wa x nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac wa x nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (i-Suc n+k) = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> epdaS_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac k)(*strict*)
   prefer 2
   apply(rule epdaS.step_detail_before_some_position)
     apply(rename_tac k)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(force)
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaS_step_relation_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e2 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e2 = F_DPDA_RMPUE__edge_else x)")
   apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(blast)
  apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
  apply(subgoal_tac "Suc (i - Suc n + k) = i-n+k")
   apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
  apply(subgoal_tac "Suc (i + k - Suc n) = i-n+k")
   apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac k e1 c1 c2 wa x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(erule_tac
      x="n-k"
      in allE)
   apply(clarsimp)
  apply(rename_tac k e1 e2 c1 c2 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 e2 c1 c2 wa x)(*strict*)
  apply(subgoal_tac "n-k \<le> i \<and> epdaS_conf_state (the (case d (i - (n-k)) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c)) = cons_state_or_edge_nat_new ea (Suc n - (n-k))")
   apply(rename_tac k e1 e2 c1 c2 wa x)(*strict*)
   prefer 2
   apply(erule_tac
      x="n-k"
      in allE)
   apply(clarsimp)
  apply(rename_tac k e1 e2 c1 c2 wa x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
  apply(clarsimp)
  apply(rename_tac k e1 c1 c2 wa x xa)(*strict*)
  apply(case_tac "edge_push ea")
   apply(rename_tac k e1 c1 c2 wa x xa)(*strict*)
   apply(force)
  apply(rename_tac k e1 c1 c2 wa x xa a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_push ea = w' @ [x']")
   apply(rename_tac k e1 c1 c2 wa x xa a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac k e1 c1 c2 wa x xa a list)(*strict*)
  apply(thin_tac "edge_push ea = a # list")
  apply(clarsimp)
  apply(rename_tac k e1 c1 c2 wa x xa w' x')(*strict*)
  apply(case_tac w')
   apply(rename_tac k e1 c1 c2 wa x xa w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac k e1 c1 c2 wa x xa w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w'' x'. w' = w'' @ [x']")
   apply(rename_tac k e1 c1 c2 wa x xa w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac k e1 c1 c2 wa x xa w' x' a list)(*strict*)
  apply(thin_tac "w' = a # list")
  apply(clarsimp)
  apply(rename_tac k e1 c1 c2 wa x xa x' w'' x'a)(*strict*)
  apply(case_tac xa)
   apply(rename_tac k e1 c1 c2 wa x xa x' w'' x'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac k e1 c1 c2 wa x x' w'' x'a)(*strict*)
   apply(case_tac "Suc (Suc 0) < length (edge_push x)")
    apply(rename_tac k e1 c1 c2 wa x x' w'' x'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac k e1 c1 c2 wa x x' w'' x'a)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_if_def)
  apply(rename_tac k e1 c1 c2 wa x xa x' w'' x'a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 c1 c2 wa x x' w'' x'a nat)(*strict*)
  apply(case_tac "Suc (Suc (Suc nat)) < length (edge_push x)")
   apply(rename_tac k e1 c1 c2 wa x x' w'' x'a nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat)(*strict*)
   defer
   apply(rename_tac k e1 c1 c2 wa x x' w'' x'a nat)(*strict*)
   apply(subgoal_tac "Suc (Suc nat) = length (edge_push x)")
    apply(rename_tac k e1 c1 c2 wa x x' w'' x'a nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k e1 c1 c2 wa x x' w'' x'a nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat)(*strict*)
  apply(subgoal_tac "\<exists>x. x#drop (length w'' - nat) w'' = drop (length w'' - Suc nat) w''")
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat)(*strict*)
   prefer 2
   apply(rule drop_with_elem_head)
   apply(force)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(rule_tac
      t="drop (length w'' - Suc nat) w''"
      and s="x # drop (length w'' - nat) w''"
      in ssubst)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
   apply(force)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(rule_tac
      t="(x # drop (length w'' - nat) w'') @ x'a # x' # drop (Suc 0) (epdaS_conf_stack ca)"
      and s="x # (drop (length w'' - nat) w'' @ x'a # x' # drop (Suc 0) (epdaS_conf_stack ca))"
      in ssubst)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(rule_tac
      t="drop (length w'' - nat) w'' @ x'a # x' # drop (Suc 0) (epdaS_conf_stack ca)"
      and s="(x'a # rev w'') ! nat # wa"
      in ssubst)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
   apply(force)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(rule_tac
      t="rev w'' ! nat # (x'a # rev w'') ! nat # wa"
      and s="(rev w'' ! nat # (x'a # rev w'') ! nat#[]) @ wa"
      in ssubst)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
   apply(force)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(rule_tac
      t="[rev w'' ! nat, (x'a # rev w'') ! nat]"
      and s="[x,(x'a # rev w'') ! nat]"
      in ssubst)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(clarsimp)
  apply(rule drop_with_elem_head2)
   apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
   apply(force)
  apply(rename_tac e1 c1 c2 wa x' w'' x'a nat x)(*strict*)
  apply(force)
  done

lemma F_DPDA_RMPUE__relation_step_simulation__RL2_maps_to_derivation: "
  F_DPDA_RMPUE__relation_TSstructure__RL G1 G2
  \<Longrightarrow> F_DPDA_RMPUE__relation_step_simulation__RL2 G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac q qa)(*strict*)
    apply(clarsimp)
    apply(rule epdaS.der2_is_derivation)
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def F_DPDA_RMPUE__edge_else__RL_def)
    apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q qa w)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa w x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_then_def)
     apply(clarsimp)
     apply(rename_tac q qa w x xa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__state_def)
     apply(case_tac xa)
      apply(rename_tac q qa w x xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac q w x)(*strict*)
      apply(case_tac "Suc (Suc 0) < length (edge_push x)")
       apply(rename_tac q w x)(*strict*)
       apply(clarsimp)
      apply(rename_tac q w x)(*strict*)
      apply(simp add: F_DPDA_RMPUE__edge_if_def)
     apply(rename_tac q qa w x xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac q qa w)(*strict*)
    apply(clarsimp)
    apply(rename_tac q qa w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(clarsimp)
    apply(thin_tac " c1 \<in> epdaS.get_accessible_configurations (F_DPDA_RMPUE G2)")
    apply(rename_tac w x)(*strict*)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(case_tac x)
    apply(rename_tac w x edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(force)
   apply(rename_tac q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(rename_tac epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
   apply(clarsimp)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac q epda_step_label_ext nat)(*strict*)
  apply(rename_tac e n)
  apply(rename_tac q e n)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_conf_stack c1'=(edge_push e)@w")
   apply(rename_tac q e n)(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac q e n)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac q e n)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(rule conjI)
    apply(rename_tac q e n)(*strict*)
    apply(clarsimp)
    apply(rename_tac q e n w wa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q e n w wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac q e n w wa x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
     apply(clarsimp)
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(case_tac "Suc (Suc xa) < length (edge_push x)")
      apply(rename_tac q e n w wa x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac e n w wa x xa)(*strict*)
     apply(case_tac xa)
      apply(rename_tac e n w wa x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac e n w wa x xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac q e n w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac q e n w wa x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac q e n)(*strict*)
   apply(rule conjI)
    apply(rename_tac q e n)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(rename_tac q e n)(*strict*)
   apply(rule conjI)
    apply(rename_tac q e n)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(clarsimp)
    apply(rename_tac q e n w wa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q e n w wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac q e n w wa x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
     apply(clarsimp)
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(case_tac "Suc (Suc xa) < length (edge_push x)")
      apply(rename_tac q e n w wa x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac e n w wa x xa)(*strict*)
     apply(case_tac xa)
      apply(rename_tac e n w wa x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac e n w wa x xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac q e n w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac q e n w wa x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac q e n)(*strict*)
   apply(rule conjI)
    apply(rename_tac q e n)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(clarsimp)
    apply(rename_tac q e n w wa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac q e n w wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac q e n w wa x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
     apply(clarsimp)
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(case_tac "Suc (Suc xa) < length (edge_push x)")
      apply(rename_tac q e n w wa x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac e n w wa x xa)(*strict*)
     apply(case_tac xa)
      apply(rename_tac e n w wa x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac e n w wa x xa nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac e w wa nat)(*strict*)
     apply(subgoal_tac "Suc (Suc (Suc nat)) = length (edge_push e)")
      apply(rename_tac e w wa nat)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac e w wa nat)(*strict*)
     apply(clarsimp)
     apply (metis RMP_edge_event_is_none)
    apply(rename_tac q e n w wa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(clarsimp)
   apply(rename_tac q e n)(*strict*)
   apply(clarsimp)
   apply(rename_tac q e n w wa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac q e n w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac q e n w wa x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def)
    apply(clarsimp)
    apply(rename_tac q e n w wa x xa)(*strict*)
    apply(case_tac "Suc (Suc xa) < length (edge_push x)")
     apply(rename_tac q e n w wa x xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac q e n w wa x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e n w wa x xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac e n w wa x xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac e n w wa x xa nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac e w wa nat)(*strict*)
    apply(subgoal_tac "Suc (Suc (Suc nat)) = length (edge_push e)")
     apply(rename_tac e w wa nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac e w wa nat)(*strict*)
    apply(clarsimp)
    prefer 2
    apply(rename_tac q e n w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac q e n w wa x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac e w wa nat)(*strict*)
   apply (metis append_eq_conv_conj drop_Suc_Cons)
  apply(rename_tac q e n)(*strict*)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
   apply(rename_tac q e n)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(blast)
  apply(rename_tac q e n)(*strict*)
  apply(erule disjE)
   apply(rename_tac q e n)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac q e n x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac q e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac q e n x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac q e n x xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac "Suc (Suc xa) < length (edge_push x)")
   apply(rename_tac q e n x xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac q e n x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e n x xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac e n x xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac e n x xa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e nat)(*strict*)
  apply(subgoal_tac "Suc (Suc (Suc nat)) = length (edge_push e)")
   apply(rename_tac e nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)
  apply(rename_tac e n)(*strict*)
  apply(rule_tac
      t="edge_push e"
      and s="drop (length(edge_push e)-Suc(Suc (Suc n))) (edge_push e)"
      in ssubst)
   apply(rename_tac e n)(*strict*)
   apply (metis diff_Suc_Suc diff_self_eq_0 drop_0)
  apply(rename_tac e n)(*strict*)
  apply(subgoal_tac "\<exists>w. epdaS_conf_stack c1 = drop (length (edge_push e) - Suc (Suc n)) (edge_push e) @ w")
   apply(rename_tac e n)(*strict*)
   apply(erule exE)+
   apply(rename_tac e n w)(*strict*)
   apply(rule_tac
      x="w"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e n w wa)(*strict*)
   apply(case_tac "edge_push e")
    apply(rename_tac e n w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac e n w wa a list)(*strict*)
   apply(clarsimp)
   apply(case_tac list)
    apply(rename_tac e n w wa a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac e n w wa a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac e n w a aa lista)(*strict*)
   apply(rule_tac
      t="(rev lista @ [aa, a]) ! Suc (length lista)"
      and s="([aa, a]) ! (Suc (length lista)- (length (rev lista)))"
      in ssubst)
    apply(rename_tac e n w a aa lista)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac e n w a aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac e n)(*strict*)
  apply(subgoal_tac "\<exists>w. c1=\<lparr>epdaS_conf_state = cons_state_or_edge_nat_new e (Suc n), epdaS_conf_scheduler = option_to_list None @ epdaS_conf_scheduler c1', epdaS_conf_stack = rev (edge_push e) ! Suc n # w\<rparr>")
   apply(rename_tac e n)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e n w)(*strict*)
   apply(case_tac c1)
   apply(rename_tac e n w epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
   apply(clarsimp)
  apply(rename_tac e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac e n w)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
  apply(clarsimp)
  apply(thin_tac "epdaS_step_relation G1 \<lparr>epdaS_conf_state = cons_state_or_edge_nat_new e (Suc n), epdaS_conf_scheduler = option_to_list None @ epdaS_conf_scheduler c1', epdaS_conf_stack = rev (edge_push e) ! Suc n # w\<rparr> \<lparr>edge_src = cons_state_or_edge_nat_new e (Suc n), edge_event = None, edge_pop = [rev (edge_push e) ! Suc n], edge_push = [rev (edge_push e) ! Suc (Suc n), rev (edge_push e) ! Suc n], edge_trg = cons_state_or_edge_nat_old (edge_trg e)\<rparr> c1'")
  apply(rename_tac e n w)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac e n w d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac e n w d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac e n w d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac e n w d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e n w d i option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac e n w d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac ea n w d i e)(*strict*)
  apply(subgoal_tac "\<forall>k\<le>n. i\<ge>k \<and> epdaS_conf_state (the(get_configuration(d (i-k)))) = cons_state_or_edge_nat_new ea ((Suc n)-k) ")
   apply(rename_tac ea n w d i e)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac ea n w d i e k)(*strict*)
   apply(rule pre_states_are_also_new)
         apply(rename_tac ea n w d i e k)(*strict*)
         apply(force)
        apply(rename_tac ea n w d i e k)(*strict*)
        apply(force)
       apply(rename_tac ea n w d i e k)(*strict*)
       apply(force)
      apply(rename_tac ea n w d i e k)(*strict*)
      apply(force)
     apply(rename_tac ea n w d i e k)(*strict*)
     apply(force)
    apply(rename_tac ea n w d i e k)(*strict*)
    apply(force)
   apply(rename_tac ea n w d i e k)(*strict*)
   apply(force)
  apply(rename_tac ea n w d i e)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (i-n) = Some (pair e c)")
   apply(rename_tac ea n w d i e)(*strict*)
   prefer 2
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      m="i"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac ea n w d i e)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ea n w d i e)(*strict*)
    apply(rule epdaS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac ea n w d i e)(*strict*)
   apply(force)
  apply(rename_tac ea n w d i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea n w d i e eb c)(*strict*)
  apply(case_tac "i=n")
   apply(rename_tac ea n w d i e eb c)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac ea n w d e eb c)(*strict*)
   apply(simp add: epdaS.derivation_initial_def F_DPDA_RMPUE__relation_TSstructure__RL_def epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac ea n w d e c)(*strict*)
   apply(simp add: F_DPDA_RMPUE_def get_configuration_def)
  apply(rename_tac ea n w d i e eb c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (i-Suc n) = Some (pair e c)")
   apply(rename_tac ea n w d i e eb c)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in epdaS.pre_some_position_is_some_position)
     apply(rename_tac ea n w d i e eb c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ea n w d i e eb c)(*strict*)
    apply(rule epdaS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac ea n w d i e eb c)(*strict*)
   apply(force)
  apply(rename_tac ea n w d i e eb c)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea n w d i e eb c ec ca)(*strict*)
  apply(subgoal_tac "\<forall>k\<le>Suc n. epdaS_conf_stack (the(get_configuration(d (i-Suc n+k)))) = drop (length (edge_push ea) - Suc k) (edge_push ea) @ drop(Suc 0)(epdaS_conf_stack ca) ")
   apply(rename_tac ea n w d i e eb c ec ca)(*strict*)
   apply(erule_tac
      x="Suc n"
      and P="\<lambda>k. k \<le> Suc n \<longrightarrow> epdaS_conf_stack (the (get_configuration (d (i - Suc n + k)))) = drop (length (edge_push ea) - Suc k) (edge_push ea) @ drop (Suc 0) (epdaS_conf_stack ca)"
      in allE)
   apply(rename_tac ea n w d i e eb c ec ca)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "(Suc (i - Suc n + n)) = i")
    apply(rename_tac ea n w d i e eb c ec ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ea n w d i e eb c ec ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac ea n w d i e eb c ec ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea n w d i e eb c ec ca k)(*strict*)
  apply(rule stack_content_translates_back)
            apply(rename_tac ea n w d i e eb c ec ca k)(*strict*)
            apply(force)+
  done

lemma epdaS_epdaS_RMP_StateSimRL_step_relation_step_simulationX: "
  \<forall>G1 G2. F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_DPDA_RMPUE__relation_step_simulation__RL2 G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule F_DPDA_RMPUE__relation_step_simulation__RL2_maps_to_derivation)
        apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_belongs_prime)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
       apply (metis epdaS_epdaS_RMP_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_DPDA_RMPUE__relation_structure__LR_def F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(rule F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations)
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
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply (metis)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(simp add: get_configuration_def der2_def)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(simp (no_asm) add: der2_def get_configuration_def)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rule_tac
      ?e1.0="e1"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q qa)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
    prefer 2
    apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac ex1 n1 ex2 n2)
    apply(rename_tac G1 G2 c1 c2 e1 c1' ex1 n1 ex2 n2)(*strict*)
    apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
     apply(rename_tac G1 G2 c1 c2 e1 c1' ex1 n1 ex2 n2)(*strict*)
     prefer 2
     apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(simp add: F_DPDA_RMPUE_def)
     apply(blast)
    apply(rename_tac G1 G2 c1 c2 e1 c1' ex1 n1 ex2 n2)(*strict*)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 c2 e1 c1' ex1 n1 ex2 n2)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 c1' ex1 n1 ex2 n2 x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' ex1 n1 ex2 n2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' ex1 n1 ex2 n2 x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 c1' ex1 n1 ex2 n2 x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(case_tac "Suc (Suc xa) < length (edge_push x)")
     apply(rename_tac G1 G2 c1 c2 c1' ex1 n1 ex2 n2 x xa)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 c1' ex1 n1 ex2 n2 x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 c1' ex1 ex2 n2 xa)(*strict*)
    apply(case_tac "xa")
     apply(rename_tac G1 G2 c1 c2 c1' ex1 ex2 n2 xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 c1' ex1 ex2 n2 xa nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(rule epdaS.der1_is_derivation)
    apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(rule epdaS.der1_belongs)
     apply(rule F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations)
       apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
      apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
      apply(rule epdaS.get_accessible_configurations_are_configurations)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(simp add: der1_def get_configuration_def)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(rule_tac
      ?e1.0="\<lparr>edge_src = cons_state_or_edge_nat_new ex2 (Suc nat), edge_event = None, edge_pop = [rev (edge_push ex2) ! Suc nat], edge_push = [rev (edge_push ex2) ! Suc (Suc nat), rev (edge_push ex2) ! Suc nat], edge_trg = cons_state_or_edge_nat_new ex2 (Suc (Suc nat))\<rparr>"
      in epdaS.der2_preserves_get_accessible_configurations)
       apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
       apply(rule F_DPDA_RMPUE__preserves_epda)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex2 nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
    apply(thin_tac "c1 \<in> epdaS.get_accessible_configurations G1")
    apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex2 nat w)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' epda_step_label_ext nat q)(*strict*)
   apply(rename_tac ex nx q)
   apply(rename_tac G1 G2 c1 c2 e1 c1' ex nx q)(*strict*)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' ex nx q)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac G1 G2 c1 c2 e1 c1' ex nx q)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 c2 e1 c1' ex nx q)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 c1' ex nx q x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' ex nx q)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' ex nx q x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 c1' ex nx q x xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__state_def)
   apply(case_tac "Suc (Suc xa) < length (edge_push x)")
    apply(rename_tac G1 G2 c1 c2 c1' ex nx q x xa)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 c1' ex nx q x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 c1' ex q xa)(*strict*)
   apply(case_tac "xa")
    apply(rename_tac G1 G2 c1 c2 c1' ex q xa)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 c1 c2 c1' ex q xa nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 c1' ex q xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(rule epdaS.der1_belongs)
    apply(rule F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations)
      apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
     apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
     apply(rule epdaS.get_accessible_configurations_are_configurations)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(rule F_DPDA_RMPUE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(rule_tac
      ?e1.0="\<lparr>edge_src = cons_state_or_edge_nat_old (edge_src ex), edge_event = None, edge_pop = [rev (edge_push ex) ! 0], edge_push = [rev (edge_push ex) ! Suc 0, rev (edge_push ex) ! 0], edge_trg = cons_state_or_edge_nat_new ex (Suc 0)\<rparr>"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 c1' ex)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
   apply(thin_tac "c1 \<in> epdaS.get_accessible_configurations G1")
   apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
   apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' ex w)(*strict*)
   apply(simp add: valid_dpda_def valid_pda_def push_and_pop_edges_seperated_def)
   apply(clarsimp)
   apply(erule_tac
      x="ex"
      and P="\<lambda>ex. \<not> F_DPDA_SPPE__edge_if ex"
      in ballE)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G2 c1 c1' ex w)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_if_def)
   apply(erule disjE)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w y)(*strict*)
    apply(simp add: read_edges_seperated_def)
    apply(erule_tac
      x="ex"
      and P="\<lambda>ex. length (edge_pop ex) = Suc 0"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w y)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w y)(*strict*)
    apply(simp add: FB_executing_edge_def strict_executing_edge_def)
   apply(rename_tac G2 c1 c1' ex w)(*strict*)
   apply(case_tac "edge_push ex")
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 c1' ex w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. edge_push ex = w' @ [x']")
    apply(rename_tac G2 c1 c1' ex w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G2 c1 c1' ex w a list)(*strict*)
   apply(thin_tac "edge_push ex = a # list")
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(rule F_DPDA_RMPUE__relation_step_simulation__RL2_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q epda_step_label_ext nat)(*strict*)
  apply(rename_tac ex nx)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q ex nx)(*strict*)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q ex nx)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(blast)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q ex nx)(*strict*)
  apply(erule disjE)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q ex nx)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 c1' q ex nx x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q ex nx)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q ex nx x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 c1' q ex nx x xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac "Suc (Suc xa) < length (edge_push x)")
   apply(rename_tac G1 G2 c1 c2 c1' q ex nx x xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 c1' q ex nx x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 c1' ex nx x xa)(*strict*)
  apply(case_tac "xa")
   apply(rename_tac G1 G2 c1 c2 c1' ex nx x xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 c1' ex nx x xa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
  apply(subgoal_tac "Suc (Suc (Suc nat)) = length (edge_push ex)")
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(rule epdaS.der2_belongs)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     apply(rule F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations)
       apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
      apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
      apply(rule epdaS.get_accessible_configurations_are_configurations)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def epda_step_labels_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE_def)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(rule F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(rule_tac
      ?e1.0="\<lparr>edge_src = cons_state_or_edge_nat_new ex (Suc nat), edge_event = None, edge_pop = [rev (edge_push ex) ! Suc nat], edge_push = [rev (edge_push ex) ! Suc (Suc nat), rev (edge_push ex) ! Suc nat], edge_trg = cons_state_or_edge_nat_old (edge_trg ex)\<rparr>"
      in epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(rule epdaS.AX_step_relation_preserves_belongsC)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(rule F_DPDA_RMPUE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
    apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
    apply(rule epdaS.get_accessible_configurations_are_configurations)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
    apply(rule F_DPDA_RMPUE__preserves_epda)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(simp add: get_configuration_def der2_def)
   apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
  apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
  apply(simp (no_asm) add: der1_def get_configuration_def)
  apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(rule_tac
      ?e1.0="\<lparr>edge_src = cons_state_or_edge_nat_new ex (Suc nat), edge_event = None, edge_pop = [rev (edge_push ex) ! Suc nat], edge_push = [rev (edge_push ex) ! Suc (Suc nat), rev (edge_push ex) ! Suc nat], edge_trg = cons_state_or_edge_nat_old (edge_trg ex)\<rparr>"
      in epdaS.der2_preserves_get_accessible_configurations)
     apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(rule F_DPDA_RMPUE__preserves_epda)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 c1' ex nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' ex nat)(*strict*)
  apply(simp add: der2_def)
  done

lemma epdaS_epdaS_RMP_StateSimRLReach_inst_ATS_Simulation_Configuration_WeakReach_axioms: "
  ATS_Simulation_Configuration_WeakReach_axioms epda_step_labels epdaS_step_relation epdaS_configurations epda_step_labels epdaS_step_relation F_DPDA_RMPUE__relation_configuration__RL2 F_DPDA_RMPUE__relation_TSstructure__RL F_DPDA_RMPUE__relation_step_simulation__RL2 F_DPDA_RMPUE__relation_labels__RL2"
  apply(simp add: ATS_Simulation_Configuration_WeakReach_axioms_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n q qa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule_tac
      x="(F_DPDA_RMPUE__edge_else__RL e1)"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     prefer 2
     apply(rule disjI2)
     apply(simp add: F_DPDA_RMPUE__edge_else_def F_DPDA_RMPUE__edge_else__RL_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(rule_tac
      t="epda_delta G2"
      and s="epda_step_labels G2"
      in ssubst)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     apply(simp add: epda_step_labels_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(rule_tac
      i="Suc 0"
      and d="(der2 (F_DPDA_RMPUE__conf_old__LR_revX c1) (F_DPDA_RMPUE__edge_else__RL e1) (F_DPDA_RMPUE__conf_old__LR_revX c1'))"
      in epdaS.belongs_step_labels)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q epda_step_label_ext nat)(*strict*)
   apply(rename_tac ex nx)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule_tac
      x="ex"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' n q ex nx x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n q ex nx x xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__state_def)
   apply(case_tac "Suc (Suc xa) < length (edge_push x)")
    apply(rename_tac G1 G2 c1 c1' n q ex nx x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n q ex nx x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
   apply(subgoal_tac "Suc (Suc xa) = length (edge_push x)")
    apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
   apply(clarsimp)
   apply(case_tac xa)
    apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex nx x xa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rule_tac
      x="Suc nat"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext nat q)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(subgoal_tac "n=0")
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
     apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
     prefer 2
     apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(simp add: F_DPDA_RMPUE_def)
     apply(blast)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c1' epda_step_label_ext nat q x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_exta nat q x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(case_tac "Suc (Suc xa) < length (edge_push x)")
     apply(rename_tac G1 G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' epda_step_label_exta q xa)(*strict*)
    apply(rename_tac ex qx xa)
    apply(rename_tac G1 G2 c1 c1' ex qx xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac G1 G2 c1 c1' ex qx xa)(*strict*)
     prefer 2
     apply(rename_tac G1 G2 c1 c1' ex qx xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex qx xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
    apply(subgoal_tac "\<exists>c. epdaS_step_relation G2 (F_DPDA_RMPUE__conf_old__LR_revX c1) ex c")
     apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
     apply(erule_tac
      x="der2 (F_DPDA_RMPUE__conf_old__LR_revX c1) ex c"
      in allE)
     apply(erule impE)
      apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
      apply(simp add: get_configuration_def der2_def der1_def)
     apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
     apply(erule impE)
      apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
      apply(rule epdaS.der2_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
     apply(erule disjE)
      apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
      apply(erule_tac
      x="Suc 0"
      in allE)
      apply(simp add: maximum_of_domain_def der2_def)
     apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(erule_tac x="ex"in allE)
     apply(erule disjE)
      apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
      apply(simp add: der2_def)
     apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def)
     apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
     apply(erule conjE)
     apply(simp add: F_DPDA_RMPUE__edge_then_def)
     apply(erule_tac
      x="0"
      in allE)
     apply(clarsimp)
     apply(simp add: F_DPDA_RMPUE__state_def)
    apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
    apply(rule epdaS_step_exists)
         apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
         apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
         apply(clarsimp)
         apply(rename_tac G2 c1 c1' ex)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
        apply(rule_tac
      i="0"
      and d="der1 (F_DPDA_RMPUE__conf_old__LR_revX c1)"
      in epdaS.belongs_configurations)
         apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
        apply(simp add: der1_def)
       apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
      apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
     apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
     apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
     apply(rule_tac
      x="epdaS_conf_scheduler c1'"
      in exI)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
     apply(case_tac "edge_event ex")
      apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
     apply(simp add: strict_executing_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__relation_TSstructure__RL_def read_edges_seperated_def)
     apply(clarsimp)
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(erule_tac
      x="ex"
      in ballE)
      apply(rename_tac G2 c1 c1' ex w a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
    apply(simp add: strict_executing_edge_def push_and_pop_edges_seperated_def FB_executing_edge_def F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__relation_TSstructure__RL_def read_edges_seperated_def)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(erule_tac
      x="ex"
      and P="\<lambda>ex. length (edge_pop ex) = Suc 0"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(erule_tac
      x="ex"
      and P="\<lambda>ex. \<not> F_DPDA_SPPE__edge_if ex"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(erule_tac
      x="ex"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(case_tac "edge_event ex")
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_if_def)
    apply(case_tac "edge_pop ex")
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w a)(*strict*)
    apply(case_tac "edge_push ex")
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w a aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. edge_push ex = w' @ [x']")
     apply(rename_tac G2 c1 c1' ex w a aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G2 c1 c1' ex w a aa list)(*strict*)
    apply(thin_tac "edge_push ex = aa # list")
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(rule epdaS.maximum_of_domainUnique)
     apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(rename_tac ex1 n1 ex2 n2)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
   apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(blast)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
  apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
   apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2 x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac "Suc (Suc xa) < length (edge_push x)")
   apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x xa)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 ex2 n2 xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac G1 G2 c1 c1' n ex1 ex2 n2 xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 ex2 n2 xa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
  apply(subgoal_tac "n=0")
   apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
   prefer 2
   apply(rule epdaS.maximum_of_domainUnique)
     apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
  apply(subgoal_tac "\<exists>c. epdaS_step_relation G2 (F_DPDA_RMPUE__conf_old__LR_revX c1) ex2 c")
   apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
   apply(erule_tac
      x="der2 (F_DPDA_RMPUE__conf_old__LR_revX c1) ex2 c"
      in allE)
   apply(erule impE)
    apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
    apply(simp add: get_configuration_def der2_def der1_def)
   apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
   apply(erule impE)
    apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
    apply(erule_tac
      x="Suc 0"
      in allE)
    apply(simp add: maximum_of_domain_def der2_def)
   apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
   apply(erule_tac
      x="Suc 0"
      in allE)
   apply(erule_tac x="ex2"in allE)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 c1' ex2 nat c)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(erule conjE)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__state_def)
  apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
  apply(rule epdaS_step_exists)
       apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
       apply(clarsimp)
       apply(rename_tac G2 c1 c1' ex2 nat)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
      apply(rule_tac
      i="0"
      and d="der1 (F_DPDA_RMPUE__conf_old__LR_revX c1)"
      in epdaS.belongs_configurations)
       apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
      apply(simp add: der1_def)
     apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
   apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
   apply(rule_tac
      x="epdaS_conf_scheduler c1'"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' ex2 nat w)(*strict*)
   apply(case_tac "edge_event ex2")
    apply(rename_tac G1 G2 c1 c1' ex2 nat w)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c1' ex2 nat w a)(*strict*)
   apply(clarsimp)
   apply(simp add: strict_executing_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__relation_TSstructure__RL_def read_edges_seperated_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' ex2 nat w a)(*strict*)
   apply(erule_tac
      x="ex2"
      in ballE)
    apply(rename_tac G2 c1 c1' ex2 nat w a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G2 c1 c1' ex2 nat w a)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
  apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
  done

lemma epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_DPDA_RMPUE__relation_configuration__RL2 F_DPDA_RMPUE__relation_initial_configuration__RL2 F_DPDA_RMPUE__relation_TSstructure__RL F_DPDA_RMPUE__relation_initial_simulation__RL2 F_DPDA_RMPUE__relation_step_simulation__RL2"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_RMP_StateSimRL_inst_relation_initial_simulationX epdaS_epdaS_RMP_StateSimRL_step_relation_step_simulationX epdaS_epdaS_RMP_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_RMP_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_RMP_StateSimRLReach" : ATS_Simulation_Configuration_WeakReach
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
  "F_DPDA_RMPUE__relation_configuration__RL2"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__RL2"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__RL"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_TSstructure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__RL2"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__RL2"
  (* relation_labelsRL *)
  "F_DPDA_RMPUE__relation_labels__RL2"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX epdaS_epdaS_RMP_StateSimRLReach_inst_ATS_Simulation_Configuration_WeakReach_axioms)
  done

definition F_DPDA_RMPUE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__SpecInput G \<equiv>
  valid_dpda G
  \<and> neutral_edges_removed G
  \<and> read_edges_seperated G
  \<and> push_and_pop_edges_seperated G
  \<and> pop_edges_seperated G"

definition F_DPDA_RMPUE__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> neutral_edges_removed Go
  \<and> read_edges_seperated Go
  \<and> mass_push_edges_splitted Go
  \<and> push_and_pop_edges_seperated Go
  \<and> push_edges_seperated Go
  \<and> pop_edges_seperated Go"

lemma F_DPDA_RMPUE__SOUND: "
  F_DPDA_RMPUE__SpecInput G
  \<Longrightarrow> F_DPDA_RMPUE__SpecOutput G (F_DPDA_RMPUE G)"
  apply(simp add: F_DPDA_RMPUE__SpecInput_def F_DPDA_RMPUE__SpecOutput_def)
  apply(rule context_conjI)
   apply(rule F_DPDA_RMPUE__preserves_DPDA)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply (rule F_DPDA_RMPUE__preserves_lang)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply (metis F_DPDA_RMPUE__preserves_neutral_edges_removed)
  apply(rule context_conjI)
   apply (metis F_DPDA_RMPUE__preserves_read_edges_seperated)
  apply(rule context_conjI)
   apply (rule F_DPDA_RMPUE__produces_mass_push_edges_splitted)
   apply(force)
  apply(rule context_conjI)
   apply (metis F_DPDA_RMPUE__preserves_push_and_pop_edges_seperated)
  apply(rule context_conjI)
   apply (rule F_DPDA_RMPUE__produces_push_edges_seperated)
       apply(force)
      apply(simp add: valid_dpda_def)
     apply(force)
    apply(force)
   apply(force)
  apply (metis F_DPDA_RMPUE__preserves_pop_edges_seperated)
  done

lemma F_DPDA_DRE__revert_F_DPDA_RMPUE_SOUND_scheduled_case_rev_id: "
       F_DPDA_RMPUE__SpecInput G' \<Longrightarrow>
       x \<in> epda_delta G' \<Longrightarrow>
       p \<in> epda_delta (F_DPDA_RMPUE G') \<Longrightarrow>
       p \<in> F_DPDA_RMPUE__edge_then x \<or> p = F_DPDA_RMPUE__edge_else x \<Longrightarrow>
       epdaS.derivation_initial (F_DPDA_RMPUE G')
        d \<Longrightarrow>
       d n = Some (pair (Some p) c) \<Longrightarrow>
       epdaS.derivation_initial G' d2 \<Longrightarrow>
       d2 n2 = Some (pair e2 c2) \<Longrightarrow>
              a \<in> F_DPDA_DRE__revert_F_DPDA_RMPUE G' {p} \<Longrightarrow> a = x"
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>p1. edge_pop a=[p1]")
   prefer 2
   apply(simp add: F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac x="a" and P="\<lambda>a. valid_epda_step_label G' a"in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="a"
      in ballE)
    prefer 2
    apply(force)
   apply(case_tac "edge_pop a")
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>p1. edge_pop x=[p1]")
   prefer 2
   apply(simp add: F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label G' x"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="x"
      in ballE)
    prefer 2
    apply(force)
   apply(case_tac "edge_pop x")
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. edge_push a \<noteq> [] \<longrightarrow> edge_push a=w@(edge_pop a)")
   prefer 2
   apply(clarsimp)
   apply(simp add: FB_executing_edge_def strict_executing_edge_def read_edges_seperated_def F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
   apply(clarsimp)
   apply(erule_tac
      x="a"
      and P="\<lambda>a. valid_epda_step_label G' a"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="a"
      and P="\<lambda>a. length (edge_pop a) = Suc 0"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="a"
      and P="\<lambda>a. (\<exists>y. edge_event a = Some y) \<longrightarrow> edge_push a = edge_pop a"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="a"
      in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac "edge_push a")
    apply(clarsimp)
   apply(subgoal_tac "\<exists>w' x'. edge_push a = w' @ [x']")
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(thin_tac "edge_push a = aa # list")
   apply(clarsimp)
   apply(erule_tac
      P="p \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>w. edge_push x \<noteq> [] \<longrightarrow> edge_push x=w@(edge_pop x)")
   prefer 2
   apply(clarsimp)
   apply(simp add: FB_executing_edge_def strict_executing_edge_def read_edges_seperated_def F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label G' x"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. length (edge_pop x) = Suc 0"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. (\<exists>y. edge_event x = Some y) \<longrightarrow> edge_push x = edge_pop x"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="x"
      in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac "edge_push x")
    apply(clarsimp)
   apply(subgoal_tac "\<exists>w' x'. edge_push x = w' @ [x']")
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(thin_tac "edge_push x = aa # list")
   apply(clarsimp)
   apply(erule_tac
      P="p \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(erule_tac
      P="p \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
   apply(erule disjE)
    apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def F_DPDA_RMPUE__edge_else_def)
    apply(clarsimp)
    apply(rename_tac p1 p1a i ia)
    apply(case_tac i)
     apply(case_tac ia)
      prefer 2
      apply(clarsimp)
     apply(clarsimp)
     apply(case_tac "Suc (Suc 0) < length (edge_push x)")
      apply(case_tac "Suc (Suc 0) < length (edge_push a)")
       prefer 2
       apply(clarsimp)
      apply(clarsimp)
     apply(clarsimp)
     apply(case_tac "Suc (Suc 0) < length (edge_push a)")
      apply(clarsimp)
     apply(clarsimp)
     apply(subgoal_tac "Suc (Suc 0) = length (edge_push x)")
      prefer 2
      apply(force)
     apply(subgoal_tac "Suc (Suc 0) = length (edge_push a)")
      prefer 2
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "edge_event a=None")
      apply(subgoal_tac "edge_event x=None")
       apply(case_tac a)
       apply(case_tac x)
       apply(clarsimp)
       apply(erule_tac
      P="edge_push \<noteq> []"
      in impE)
        apply(force)
       apply(erule impE)
        apply(force)
       apply(clarsimp)
       apply(case_tac w)
        apply(clarsimp)
       apply(case_tac list)
        prefer 2
        apply(clarsimp)
       apply(clarsimp)
       apply(case_tac wa)
        apply(clarsimp)
       apply(case_tac list)
        prefer 2
        apply(clarsimp)
       apply(clarsimp)
      apply(simp add: F_DPDA_RMPUE__SpecInput_def)
      apply(simp add: FB_executing_edge_def strict_executing_edge_def read_edges_seperated_def F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
      apply(clarsimp)
      apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label G' x"
      in ballE)
       prefer 2
       apply(force)
      apply(erule_tac
      x="x"
      and P="\<lambda>x. length (edge_pop x) = Suc 0"
      in ballE)
       prefer 2
       apply(force)
      apply(erule_tac
      x="x"
      and P="\<lambda>x. (\<exists>y. edge_event x = Some y) \<longrightarrow> edge_push x = edge_pop x"
      in ballE)
       prefer 2
       apply(force)
      apply(erule_tac
      x="x"
      in ballE)
       prefer 2
       apply(force)
      apply(clarsimp)
      apply(case_tac "edge_event x")
       apply(clarsimp)
      apply(clarsimp)
     apply(simp add: F_DPDA_RMPUE__SpecInput_def)
     apply(simp add: FB_executing_edge_def strict_executing_edge_def read_edges_seperated_def F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
     apply(clarsimp)
     apply(erule_tac
      x="a"
      and P="\<lambda>a. valid_epda_step_label G' a"
      in ballE)
      prefer 2
      apply(force)
     apply(erule_tac
      x="a"
      and P="\<lambda>a. length (edge_pop a) = Suc 0"
      in ballE)
      prefer 2
      apply(force)
     apply(erule_tac
      x="a"
      and P="\<lambda>a. (\<exists>y. edge_event a = Some y) \<longrightarrow> edge_push a = edge_pop a"
      in ballE)
      prefer 2
      apply(force)
     apply(erule_tac
      x="a"
      in ballE)
      prefer 2
      apply(force)
     apply(clarsimp)
     apply(case_tac "edge_event a")
      apply(clarsimp)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac ia)
     apply(clarsimp)
    apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def F_DPDA_RMPUE__edge_else_def)
   apply(clarsimp)
   apply(rename_tac p1a i)
   apply(case_tac i)
    apply(clarsimp)
    apply(case_tac "Suc (Suc 0) < length (edge_push x)")
     apply(clarsimp)
    apply(clarsimp)
    apply(subgoal_tac "Suc (Suc 0) = length (edge_push x)")
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(subgoal_tac "edge_event x=None")
     apply(case_tac a)
     apply(case_tac x)
     apply(clarsimp)
     apply(case_tac "edge_pusha")
      apply(clarsimp)
     apply(subgoal_tac "\<exists>w' x'. edge_pusha = w' @ [x']")
      prefer 2
      apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
      apply(force)
     apply(thin_tac "edge_pusha = a # list")
     apply(clarsimp)
     apply(case_tac "w'")
      apply(clarsimp)
     apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__SpecInput_def)
    apply(simp add: FB_executing_edge_def strict_executing_edge_def read_edges_seperated_def F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
    apply(clarsimp)
    apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_epda_step_label G' x"
      in ballE)
     prefer 2
     apply(force)
    apply(erule_tac
      x="x"
      and P="\<lambda>x. length (edge_pop x) = Suc 0"
      in ballE)
     prefer 2
     apply(force)
    apply(erule_tac
      x="x"
      and P="\<lambda>x. (\<exists>y. edge_event x = Some y) \<longrightarrow> edge_push x = edge_pop x"
      in ballE)
     prefer 2
     apply(force)
    apply(erule_tac
      x="x"
      in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(case_tac "edge_event x")
     apply(clarsimp)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(erule_tac
      P="F_DPDA_RMPUE__edge_else x \<in> F_DPDA_RMPUE__edge_then a"
      in disjE)
   apply(simp add: F_DPDA_RMPUE__edge_then_def F_DPDA_RMPUE__state_def F_DPDA_RMPUE__edge_else_def)
   apply(clarsimp)
   apply(rename_tac p1a i)
   apply(case_tac i)
    apply(clarsimp)
    apply(case_tac "Suc (Suc 0) < length (edge_push a)")
     apply(clarsimp)
    apply(clarsimp)
    apply(subgoal_tac "Suc (Suc 0) = length (edge_push a)")
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(subgoal_tac "edge_event a=None")
     apply(case_tac a)
     apply(case_tac x)
     apply(clarsimp)
     apply(case_tac "edge_push")
      apply(clarsimp)
     apply(subgoal_tac "\<exists>w' x'. edge_push = w' @ [x']")
      prefer 2
      apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
      apply(force)
     apply(thin_tac "edge_push = a # list")
     apply(clarsimp)
     apply(case_tac "w'")
      apply(clarsimp)
     apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__SpecInput_def)
    apply(simp add: FB_executing_edge_def strict_executing_edge_def read_edges_seperated_def F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def valid_epda_def push_and_pop_edges_seperated_def F_DPDA_SPPE__edge_if_def)
    apply(clarsimp)
    apply(erule_tac
      x="a"
      and P="\<lambda>a. valid_epda_step_label G' a"
      in ballE)
     prefer 2
     apply(force)
    apply(erule_tac
      x="a"
      and P="\<lambda>a. length (edge_pop a) = Suc 0"
      in ballE)
     prefer 2
     apply(force)
    apply(erule_tac
      x="a"
      and P="\<lambda>a. (\<exists>y. edge_event a = Some y) \<longrightarrow> edge_push a = edge_pop a"
      in ballE)
     prefer 2
     apply(force)
    apply(erule_tac
      x="a"
      in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(case_tac "edge_event a")
     apply(clarsimp)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__edge_else_def)
  done

lemma F_DPDA_DRE__revert_F_DPDA_RMPUE_SOUND_scheduled_case: "
  F_DPDA_RMPUE__SpecInput G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_RMPUE G' (epdaS_accessible_edges (F_DPDA_RMPUE G')) = epdaS_accessible_edges G'"
  apply(rule order_antisym)
   apply(simp add: epdaS_accessible_edges_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: epdaS_accessible_edges_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(clarsimp)
   apply(rename_tac x d n c)(*strict*)
   apply(subgoal_tac "\<exists>d2 n2 e2 c2. epdaS.derivation_initial SSG2 d2 \<and> d2 n2 = Some (pair e2 c2) \<and> (case SSe1 of None \<Rightarrow> True | Some e1' \<Rightarrow> \<exists>k d2'. epdaS.derivation SSG2 d2' \<and> the (get_configuration (d2' 0)) = the (get_configuration (d2 n2)) \<and> (case get_label (derivation_append d2 d2' n2 k) of None \<Rightarrow> False | Some e2' \<Rightarrow> F_DPDA_RMPUE__relation_labels__LR2 SSG1 SSG2 e1' e2'))" for SSe1 SSG1 SSG2)
    apply(rename_tac x d n c)(*strict*)
    prefer 2
    apply(rule_tac
      ?G1.0="G'"
      and ?d1.0="d"
      and ?G2.0="F_DPDA_RMPUE G'"
      in epdaS_epdaS_RMP_StateSimLRReach.ATS_Simulation_Configuration_WeakReach_exists)
      apply(rename_tac x d n c)(*strict*)
      apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
      apply(simp add: F_DPDA_RMPUE__SpecInput_def)
     apply(rename_tac x d n c)(*strict*)
     apply(force)
    apply(rename_tac x d n c)(*strict*)
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2')(*strict*)
   apply(case_tac "(get_label (derivation_append d2 d2' n2 k))")
    apply(rename_tac x d n c d2 n2 e2 k c2 d2')(*strict*)
    apply(force)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(rule_tac
      x="a"
      in exI)
   apply(simp add: F_DPDA_RMPUE__relation_labels__LR2_def F_DPDA_DRE__revert_F_DPDA_RNE_def)
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
   apply(subgoal_tac "epdaS.derivation_initial (F_DPDA_RMPUE G') (derivation_append d2 d2' n2)")
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    prefer 2
    apply(rule epdaS.derivation_append_preserves_derivation_initial)
      apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(simp add: F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def)
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
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b ca)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(rule_tac
      t="epda_delta (F_DPDA_RMPUE G')"
      and s="epda_step_labels (F_DPDA_RMPUE G')"
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
      apply(rule F_DPDA_RMPUE__preserves_epda)
      apply(simp add: F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def)
     apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
     apply(force)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(force)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
    apply(force)
   apply(rename_tac x d n c d2 n2 e2 k c2 d2' a b)(*strict*)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(clarsimp)
  apply(rename_tac x p d n c)(*strict*)
  apply(subgoal_tac "\<exists>d2 n2 e2 c2. epdaS.derivation_initial SSG2 d2 \<and> d2 n2 = Some (pair e2 c2) \<and> (case SSe1 of None \<Rightarrow> True | Some e1' \<Rightarrow> \<exists>k d2'. epdaS.derivation SSG2 d2' \<and> the (get_configuration (d2' 0)) = the (get_configuration (d2 n2)) \<and> (case get_label (derivation_append d2 d2' n2 k) of None \<Rightarrow> False | Some e2' \<Rightarrow> F_DPDA_RMPUE__relation_labels__RL2 SSG1 SSG2 e1' e2'))" for SSe1 SSG1 SSG2)
   apply(rename_tac x p d n c)(*strict*)
   prefer 2
   apply(rule_tac
      ?G2.0="G'"
      and ?d1.0="d"
      and ?G1.0="F_DPDA_RMPUE G'"
      in epdaS_epdaS_RMP_StateSimRLReach.ATS_Simulation_Configuration_WeakReach_exists)
     apply(rename_tac x p d n c)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
     apply(simp add: F_DPDA_RMPUE__SpecInput_def)
    apply(rename_tac x p d n c)(*strict*)
    apply(force)
   apply(rename_tac x p d n c)(*strict*)
   apply(force)
  apply(rename_tac x p d n c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p d n c d2 n2 e2 k c2 d2')(*strict*)
  apply(case_tac "(get_label (derivation_append d2 d2' n2 k))")
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
     apply(simp add: F_DPDA_RMPUE__SpecInput_def valid_dpda_def valid_pda_def)
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
  apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def)
  apply(clarsimp)
  apply(rule F_DPDA_DRE__revert_F_DPDA_RMPUE_SOUND_scheduled_case_rev_id)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_RMP_StateSimRLRequired__inst__AX_relation_configuration_compatible_with_marking_configurations: "
(\<forall>G1 G2.
        F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow>
            c1 \<in> epdaS_marking_configurations G1 \<longrightarrow> c2 \<in> epdaS_marking_configurations G2))"
  apply(clarsimp)
  apply(simp add: epdaS_marking_configurations_def)
  apply(subgoal_tac "c2 \<in> epdaS_configurations G2")
   prefer 2
   apply (metis (full_types) F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations F_DPDA_RMPUE__relation_configuration__RL2_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def F_DPDA_RMPUE_def F_DPDA_RMPUE__conf_old__LR_revX_def)
  apply(case_tac c1)
  apply(clarsimp)
  done

lemma epdaS_epdaS_RMP_StateSimRLRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant: "
  (\<forall>G1 G2.
        F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow>
            (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                  (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                         (\<forall>d2. F_DPDA_RMPUE__relation_step_simulation__RL2 G1 G2 c1 e1 c1' c2
                                d2 \<longrightarrow>
                               maximum_of_domain d2 0 \<longrightarrow>
                               c1' \<notin> epdaS_marking_configurations G1)))))"
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
  apply(case_tac "edge_trg e1")
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(clarsimp)
    apply(simp add: maximum_of_domain_def der2_def)
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def der2_def)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def der2_def)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def der2_def der1_def)
   apply(clarsimp)
   apply(simp add: epdaS_step_relation_def epdaS_marking_configurations_def F_DPDA_RMPUE__relation_configuration__RL2_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def der2_def der1_def)
  apply(simp add: epdaS_step_relation_def epdaS_marking_configurations_def F_DPDA_RMPUE__relation_configuration__RL2_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE_def)
  apply(clarsimp)
  done

lemma epdaS_epdaS_RMP_StateSimRLRequired__inst__AX_relation_step_simulationReach: "
  \<forall>G1 G2.
       F_DPDA_RMPUE__relation_TSstructure__RL G1 G2 \<longrightarrow>
       (\<forall>c1 c2.
           F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1 c2 \<longrightarrow>
           (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                 (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                        (\<forall>d2. epdaS.derivation G2 d2 \<longrightarrow>
                              epdaS.belongs G2 d2 \<longrightarrow>
                              the (get_configuration (d2 0)) = c2 \<longrightarrow>
                              F_DPDA_RMPUE__relation_step_simulation__RL2 G1 G2 c1 e1 c1' c2
                               d2 \<longrightarrow>
                              (\<forall>n. maximum_of_domain d2 n \<longrightarrow>
                                   F_DPDA_RMPUE__relation_configuration__RL2 G1 G2 c1'
                                    (the (get_configuration (d2 n))) \<longrightarrow>
                                   (\<exists>k e2. (\<exists>c2. d2 k = Some (pair (Some e2) c2)) \<and>
                                           F_DPDA_RMPUE__relation_labels__RL2 G1 G2 e1 e2) \<or>
                                   n = 0 \<and>
                                   (\<exists>e2. Ex (epdaS_step_relation G2 c2 e2) \<and>
                                         F_DPDA_RMPUE__relation_labels__RL2 G1 G2 e1 e2))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__RL2_def)
  apply(case_tac "edge_trg e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_src e1")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n q qa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule_tac
      x="(F_DPDA_RMPUE__edge_else__RL e1)"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     prefer 2
     apply(rule disjI2)
     apply(simp add: F_DPDA_RMPUE__edge_else_def F_DPDA_RMPUE__edge_else__RL_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(rule_tac
      t="epda_delta G2"
      and s="epda_step_labels G2"
      in ssubst)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     apply(simp add: epda_step_labels_def)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(rule_tac
      i="Suc 0"
      and d="(der2 (F_DPDA_RMPUE__conf_old__LR_revX c1) (F_DPDA_RMPUE__edge_else__RL e1) (F_DPDA_RMPUE__conf_old__LR_revX c1'))"
      in epdaS.belongs_step_labels)
     apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n q qa)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n q epda_step_label_ext nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q epda_step_label_ext nat)(*strict*)
   apply(rename_tac ex nx)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule_tac
      x="ex"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
    apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
    apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
    apply(simp add: F_DPDA_RMPUE_def)
    apply(blast)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
    apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' n q ex nx x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n q ex nx x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n q ex nx x xa)(*strict*)
   apply(simp add: F_DPDA_RMPUE__state_def)
   apply(case_tac "Suc (Suc xa) < length (edge_push x)")
    apply(rename_tac G1 G2 c1 c1' n q ex nx x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n q ex nx x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
   apply(subgoal_tac "Suc (Suc xa) = length (edge_push x)")
    apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
   apply(clarsimp)
   apply(case_tac xa)
    apply(rename_tac G1 G2 c1 c1' n ex nx x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex nx x xa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex nat)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
   apply(rule_tac
      x="Suc nat"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_src e1")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext nat q)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(subgoal_tac "n=0")
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
     apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
     prefer 2
     apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
     apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
     apply(simp add: F_DPDA_RMPUE_def)
     apply(blast)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c1' epda_step_label_ext nat q x)(*strict*)
     apply(simp add: F_DPDA_RMPUE__edge_else_def)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_ext nat q x)(*strict*)
    apply(simp add: F_DPDA_RMPUE__edge_then_def)
    apply(rename_tac G1 G2 c1 e1 c1' epda_step_label_exta nat q x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
    apply(simp add: F_DPDA_RMPUE__state_def)
    apply(case_tac "Suc (Suc xa) < length (edge_push x)")
     apply(rename_tac G1 G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' epda_step_label_exta nat q x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' epda_step_label_exta q xa)(*strict*)
    apply(rename_tac ex qx xa)
    apply(rename_tac G1 G2 c1 c1' ex qx xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac G1 G2 c1 c1' ex qx xa)(*strict*)
     prefer 2
     apply(rename_tac G1 G2 c1 c1' ex qx xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex qx xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
    apply(subgoal_tac "\<exists>c. epdaS_step_relation G2 (F_DPDA_RMPUE__conf_old__LR_revX c1) ex c")
     apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
     apply(clarsimp)
     apply(simp add: der1_def get_configuration_def)
     apply(erule_tac x="ex" in allE)
     apply(erule disjE)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c1' ex c)(*strict*)
     apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def)
     apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
     apply(erule conjE)
     apply(simp add: F_DPDA_RMPUE__edge_then_def)
     apply(erule_tac
      x="0"
      in allE)
     apply(clarsimp)
     apply(simp add: F_DPDA_RMPUE__state_def)
    apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
    apply(rule epdaS_step_exists)
         apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
         apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
         apply(clarsimp)
         apply(rename_tac G2 c1 c1' ex)(*strict*)
         apply(simp add: valid_dpda_def valid_pda_def)
        apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
        apply(rule_tac
      i="0"
      and d="der1 (F_DPDA_RMPUE__conf_old__LR_revX c1)"
      in epdaS.belongs_configurations)
         apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
        apply(simp add: der1_def)
       apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
      apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
     apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
     apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
     apply(rule_tac
      x="epdaS_conf_scheduler c1'"
      in exI)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
     apply(case_tac "edge_event ex")
      apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
     apply(simp add: strict_executing_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__relation_TSstructure__RL_def read_edges_seperated_def)
     apply(clarsimp)
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(erule_tac
      x="ex"
      in ballE)
      apply(rename_tac G2 c1 c1' ex w a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac G1 G2 c1 c1' ex)(*strict*)
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c1' ex w)(*strict*)
    apply(simp add: strict_executing_edge_def push_and_pop_edges_seperated_def FB_executing_edge_def F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__relation_TSstructure__RL_def read_edges_seperated_def)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(erule_tac
      x="ex"
      and P="\<lambda>ex. length (edge_pop ex) = Suc 0"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(erule_tac
      x="ex"
      and P="\<lambda>ex. \<not> F_DPDA_SPPE__edge_if ex"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(erule_tac
      x="ex"
      in ballE)
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(case_tac "edge_event ex")
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     prefer 2
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w)(*strict*)
    apply(clarsimp)
    apply(simp add: F_DPDA_SPPE__edge_if_def)
    apply(case_tac "edge_pop ex")
     apply(rename_tac G2 c1 c1' ex w)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w a)(*strict*)
    apply(case_tac "edge_push ex")
     apply(rename_tac G2 c1 c1' ex w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G2 c1 c1' ex w a aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. edge_push ex = w' @ [x']")
     apply(rename_tac G2 c1 c1' ex w a aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G2 c1 c1' ex w a aa list)(*strict*)
    apply(thin_tac "edge_push ex = aa # list")
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(rule epdaS.maximum_of_domainUnique)
     apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat q)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n epda_step_label_ext nat epda_step_label_exta nata)(*strict*)
  apply(rename_tac ex1 n1 ex2 n2)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x) \<or> (\<exists>x\<in> epda_delta G2 \<inter> {e. (\<not> F_DPDA_RMPUE__edge_if e)}. e1 = F_DPDA_RMPUE__edge_else x)")
   apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def)
   apply(simp add: F_DPDA_RMPUE_def)
   apply(blast)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
  apply(erule_tac
      P="\<exists>x\<in> epda_delta G2 \<inter> {e. F_DPDA_RMPUE__edge_if e}. e1 \<in> F_DPDA_RMPUE__edge_then x"
      in disjE)
   apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x)(*strict*)
   apply(simp add: F_DPDA_RMPUE__edge_else_def)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' n ex1 n1 ex2 n2 x)(*strict*)
  apply(simp add: F_DPDA_RMPUE__edge_then_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x xa)(*strict*)
  apply(simp add: F_DPDA_RMPUE__state_def)
  apply(case_tac "Suc (Suc xa) < length (edge_push x)")
   apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x xa)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 n1 ex2 n2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 ex2 n2 xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac G1 G2 c1 c1' n ex1 ex2 n2 xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex1 ex2 n2 xa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
  apply(subgoal_tac "n=0")
   apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
   prefer 2
   apply(rule epdaS.maximum_of_domainUnique)
     apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c1' n ex2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
  apply(subgoal_tac "\<exists>c. epdaS_step_relation G2 (F_DPDA_RMPUE__conf_old__LR_revX c1) ex2 c")
   apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
   apply(clarsimp)
   apply(erule_tac x="ex2" in allE)
   apply(erule disjE)
    apply(simp add: der1_def get_configuration_def)
   apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(erule conjE)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__state_def)
  apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
  apply(rule epdaS_step_exists)
       apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
       apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
       apply(clarsimp)
       apply(rename_tac G2 c1 c1' ex2 nat)(*strict*)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
      apply(rule_tac
      i="0"
      and d="der1 (F_DPDA_RMPUE__conf_old__LR_revX c1)"
      in epdaS.belongs_configurations)
       apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
      apply(simp add: der1_def)
     apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
    apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def)
   apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
   apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
   apply(rule_tac
      x="epdaS_conf_scheduler c1'"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c1' ex2 nat w)(*strict*)
   apply(case_tac "edge_event ex2")
    apply(rename_tac G1 G2 c1 c1' ex2 nat w)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c1' ex2 nat w a)(*strict*)
   apply(clarsimp)
   apply(simp add: strict_executing_edge_def FB_executing_edge_def F_DPDA_RMPUE__edge_if_def F_DPDA_RMPUE__relation_TSstructure__RL_def read_edges_seperated_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' ex2 nat w a)(*strict*)
   apply(erule_tac
      x="ex2"
      in ballE)
    apply(rename_tac G2 c1 c1' ex2 nat w a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G2 c1 c1' ex2 nat w a)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac G1 G2 c1 c1' ex2 nat)(*strict*)
  apply(simp add: epdaS_step_relation_def F_DPDA_RMPUE__conf_old__LR_revX_def prefix_def)
  done

lemma epdaS_epdaS_RMP_StateSimRLRequired__inst__ATS_Simulation_Configuration_WeakRequired_axioms: "
  ATS_Simulation_Configuration_WeakRequired_axioms epda_step_labels epdaS_step_relation
     epdaS_configurations epda_step_labels epdaS_step_relation
     F_DPDA_RMPUE__relation_configuration__RL2 F_DPDA_RMPUE__relation_TSstructure__RL
     F_DPDA_RMPUE__relation_step_simulation__RL2 F_DPDA_RMPUE__relation_labels__RL2
     epdaS_marking_configurations epdaS_marking_configurations"
  apply(simp add: ATS_Simulation_Configuration_WeakRequired_axioms_def
      epdaS_epdaS_RMP_StateSimRLRequired__inst__AX_relation_configuration_compatible_with_marking_configurations
      epdaS_epdaS_RMP_StateSimRLRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant
      epdaS_epdaS_RMP_StateSimRLRequired__inst__AX_relation_step_simulationReach)
  done

interpretation "epdaS_epdaS_RMP_StateSimRLRequired" : ATS_Simulation_Configuration_WeakRequired
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
  "F_DPDA_RMPUE__relation_configuration__RL2"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__RL2"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__RL"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_TSstructure__RL"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__RL2"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__RL2"
  (* relation_labelsRL *)
  "F_DPDA_RMPUE__relation_labels__RL2"
  (* marking_configurations1 *)
  "epdaS_marking_configurations"
  (* marking_configurations2 *)
  "epdaS_marking_configurations"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add:   epdaS_epdaS_RMP_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axiomsX epdaS_epdaS_RMP_StateSimRLRequired__inst__ATS_Simulation_Configuration_WeakRequired_axioms)
  done

lemma epdaS_epdaS_RMP_StateSimLRRequired__inst__AX_relation_configuration_compatible_with_marking_configurations: "
(\<forall>G1 G2.
        F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow>
            c1 \<in> epdaS_marking_configurations G1 \<longrightarrow> c2 \<in> epdaS_marking_configurations G2))"
  apply(clarsimp)
  apply(simp add: epdaS_marking_configurations_def)
  apply(subgoal_tac "c2 \<in> epdaS_configurations G2")
   prefer 2
   apply (metis F_DPDA_RMPUE__conf_old__LR_preserves_configurations F_DPDA_RMPUE__relation_configuration__LR_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def F_DPDA_RMPUE__relation_configuration__LR_def F_DPDA_RMPUE__relation_TSstructure__RL_def F_DPDA_RMPUE__relation_configuration__RL2_def F_DPDA_RMPUE_def F_DPDA_RMPUE__conf_old__LR_revX_def F_DPDA_RMPUE__conf_old__LR_def)
  done

lemma epdaS_epdaS_RMP_StateSimLRRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant: "
 (\<forall>G1 G2.
        F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow>
        (\<forall>c1 c2.
            F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow>
            (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                  (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                         (\<forall>d2. F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2
                                d2 \<longrightarrow>
                               maximum_of_domain d2 0 \<longrightarrow>
                               c1' \<notin> epdaS_marking_configurations G1)))))"
  apply(clarsimp)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_RMPUE__edge_if e1")
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def der2_def)
   apply(clarsimp)
   apply(case_tac "Suc 0 < length (edge_push e1)")
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__edge_if_def)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def der2_def)
  done

lemma epdaS_epdaS_RMP_StateSimLRquired__inst__AX_relation_step_simulationReach: "
   \<forall>G1 G2.
       F_DPDA_RMPUE__relation_structure__LR G1 G2 \<longrightarrow>
       (\<forall>c1 c2.
           F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1 c2 \<longrightarrow>
           (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow>
                 (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow>
                        (\<forall>d2. epdaS.derivation G2 d2 \<longrightarrow>
                              epdaS.belongs G2 d2 \<longrightarrow>
                              the (get_configuration (d2 0)) = c2 \<longrightarrow>
                              F_DPDA_RMPUE__relation_step_simulation__LR G1 G2 c1 e1 c1' c2
                               d2 \<longrightarrow>
                              (\<forall>n. maximum_of_domain d2 n \<longrightarrow>
                                   F_DPDA_RMPUE__relation_configuration__LR G1 G2 c1'
                                    (the (get_configuration (d2 n))) \<longrightarrow>
                                   (\<exists>k e2. (\<exists>c2. d2 k = Some (pair (Some e2) c2)) \<and>
                                           F_DPDA_RMPUE__relation_labels__LR2 G1 G2 e1 e2) \<or>
                                   n = 0 \<and>
                                   (\<exists>e2. Ex (epdaS_step_relation G2 c2 e2) \<and>
                                         F_DPDA_RMPUE__relation_labels__LR2 G1 G2 e1 e2))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def epda_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' d2 n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_step_simulation__LR_def)
  apply(case_tac "F_DPDA_RMPUE__edge_if e1")
   apply(rename_tac G1 c1 e1 c1' d2 n)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(subgoal_tac "Suc 0 < length (edge_push e1)")
    apply(rename_tac G1 c1 e1 c1' n)(*strict*)
    prefer 2
    apply(simp add: F_DPDA_RMPUE__edge_if_def)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_RMPUE__edge_then_i_th__LR_def)
   apply(simp add: F_DPDA_RMPUE__relation_labels__LR2_def)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(simp add: F_DPDA_RMPUE__edge_then_def)
   apply(rule disjI1)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' d2 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule_tac
      x="(F_DPDA_RMPUE__edge_else e1)"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G1 c1 e1 c1' n)(*strict*)
  apply(simp add: F_DPDA_RMPUE__relation_labels__LR2_def)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n)(*strict*)
   apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
  apply(rename_tac G1 c1 e1 c1' n)(*strict*)
  apply(simp only: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(clarsimp)
  done

lemma epdaS_epdaS_RMP_StateSimLRRequired__inst__ATS_Simulation_Configuration_WeakRequired_axioms: "
  ATS_Simulation_Configuration_WeakRequired_axioms epda_step_labels epdaS_step_relation
     epdaS_configurations epda_step_labels epdaS_step_relation
     F_DPDA_RMPUE__relation_configuration__LR F_DPDA_RMPUE__relation_structure__LR
     F_DPDA_RMPUE__relation_step_simulation__LR F_DPDA_RMPUE__relation_labels__LR2
     epdaS_marking_configurations epdaS_marking_configurations"
  apply(simp add: ATS_Simulation_Configuration_WeakRequired_axioms_def
      epdaS_epdaS_RMP_StateSimLRRequired__inst__AX_relation_configuration_compatible_with_marking_configurations
      epdaS_epdaS_RMP_StateSimLRRequired__inst__AX_relation_step_simulation_no_reach_marking_with_empty_simulant
      epdaS_epdaS_RMP_StateSimLRquired__inst__AX_relation_step_simulationReach
      )
  done

interpretation "epdaS_epdaS_RMP_StateSimLRRequired" : ATS_Simulation_Configuration_WeakRequired
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
  "F_DPDA_RMPUE__relation_configuration__LR"
  (* relation_initial_configuration *)
  "F_DPDA_RMPUE__relation_initial_configuration__LR"
  (* relation_effect *)
  "F_DPDA_RMPUE__relation_effect__LR"
  (* relation_TSstructure *)
  "F_DPDA_RMPUE__relation_structure__LR"
  (* relation_initial_simulation *)
  "F_DPDA_RMPUE__relation_initial_simulation__LR"
  (* relation_step_simulation *)
  "F_DPDA_RMPUE__relation_step_simulation__LR"
  (* relation_labelsLR *)
  "F_DPDA_RMPUE__relation_labels__LR2"
  (* marking_configurations1 *)
  "epdaS_marking_configurations"
  (* marking_configurations2 *)
  "epdaS_marking_configurations"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_RMP_StateSimLRRequired__inst__ATS_Simulation_Configuration_WeakRequired_axioms)
  done

lemma F_DPDA_DRE__revert_F_DPDA_RMPUE_SOUND_scheduled_case_epdaS_required_edges: "
  F_DPDA_RMPUE__SpecInput G'
  \<Longrightarrow> F_DPDA_DRE__revert_F_DPDA_RMPUE G' (epdaS_required_edges (F_DPDA_RMPUE G')) = epdaS_required_edges G'"
  apply(rule order_antisym)
   apply(simp add: epdaS_required_edges_def)
   apply(clarsimp)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>m. n+m=k")
    prefer 2
    apply(rule_tac x="k-n" in exI)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac ?G1.0="F_DPDA_RMPUE G'" and ?G2.0="G'" and ?n1'="n+m" in epdaS_epdaS_RMP_StateSimRLRequired.ATS_Simulation_Configuration_WeakRequired_exists_ALT)
          apply(simp add: F_DPDA_RMPUE__relation_TSstructure__RL_def)
          apply(simp add: F_DPDA_RMPUE__SpecInput_def)
         apply(simp add: F_DPDA_RMPUE__SpecInput_def)
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
   apply(simp add: F_DPDA_RMPUE__relation_labels__RL2_def)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
   apply(clarsimp)
   apply(rule conjI)
    prefer 2
    apply(rule_tac x="n2'" in exI)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__relation_configuration__RL2_def epdaS_marking_configurations_def)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac ?c1.0="ca" in
      F_DPDA_RMPUE__conf_old__LR_revX_preserves_configurations)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: F_DPDA_RMPUE__conf_old__LR_revX_def F_DPDA_RMPUE_def)
    apply(case_tac "epdaS_conf_state ca")
     apply(clarsimp)
    apply(clarsimp)
   apply(rule_tac ?n2.0="n2" and d="d" and ?d2.0="d2" in F_DPDA_DRE__revert_F_DPDA_RMPUE_SOUND_scheduled_case_rev_id)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(simp add: epdaS_required_edges_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  apply(subgoal_tac "\<exists>m. n+m=k")
   prefer 2
   apply(rule_tac x="k-n" in exI)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G2.0="F_DPDA_RMPUE G'" and ?G1.0="G'" and ?n1'="n+m" in epdaS_epdaS_RMP_StateSimLRRequired.ATS_Simulation_Configuration_WeakRequired_exists_ALT)
         apply(simp add: F_DPDA_RMPUE__relation_structure__LR_def)
         apply(simp add: F_DPDA_RMPUE__SpecInput_def)
        apply(simp add: F_DPDA_RMPUE__SpecInput_def)
        apply(clarsimp)
        apply(simp add: epdaS.is_forward_deterministic_accessible_def)
        apply(rule conjI)
         prefer 2
         apply(rule F_DPDA_RMPUE__preserves_is_forward_edge_deterministic_accessible)
           apply(force)
          apply(force)
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
    apply(rule F_DPDA_RMPUE__preserves_epda)
    apply(simp add: F_DPDA_RMPUE__SpecInput_def)
   apply(force)
  apply(rule conjI)
   apply(rule_tac x="d2" in exI)
   apply(clarsimp)
   apply(rule_tac x="n2" in exI)
   apply(clarsimp)
   apply(rule_tac x="n2'" in exI)
   apply(clarsimp)
   apply (metis F_DPDA_RMPUE__conf_old__LR_preserves_marking_configurations F_DPDA_RMPUE__relation_configuration__LR_def)
  apply(simp add: F_DPDA_RMPUE__relation_labels__LR2_def F_DPDA_DRE__revert_F_DPDA_RMPUE_def)
  done

end

