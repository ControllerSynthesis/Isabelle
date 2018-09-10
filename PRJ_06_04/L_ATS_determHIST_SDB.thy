section {*L\_ATS\_determHIST\_SDB*}
theory
  L_ATS_determHIST_SDB

imports
  L_ATS_determHIST_DB
  L_ATS_determHIST_SB

begin

locale ATS_determHIST_SDB =
  ATS_SchedF_SDB
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler :: 'conf \<Rightarrow> 'fixed_scheduler"
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  +
  ATS_determHIST_SB
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler :: 'conf \<Rightarrow> 'fixed_scheduler"
  +
  ATS_determHIST_DB
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable get_fixed_scheduler get_fixed_scheduler_DB histories history_fragments empty_history empty_history_fragment set_history extend_history join_history_fragments get_history

context ATS_determHIST_SDB begin

lemma AX_is_forward_edge_deterministic_correspond_DB_SB: "
  TSstructure G
  \<Longrightarrow> is_forward_edge_deterministicHist_SB_long G = is_forward_edge_deterministicHist_DB_long G"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(simp add: is_forward_edge_deterministicHist_SB_long_def is_forward_edge_deterministicHist_DB_long_def)
   apply(clarsimp)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
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
      x="w1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="w2"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e1 c1) n) (Suc n)) = ((get_fixed_scheduler c1))")
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
     apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e2 c2) n) (Suc n)) = ((get_fixed_scheduler c2))")
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(clarsimp)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
     apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(rule derivation_append_preserves_derivation_initial)
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(rule derivation_append_preserves_derivation)
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
        apply(rule derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
       apply(rule der2_is_derivation)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
      apply(case_tac "d n")
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(simp add: der2_def)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
     apply(rule derivation_append_preserves_derivation_initial)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
     apply(rule derivation_append_preserves_derivation)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
       apply(rule derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(rule der2_is_derivation)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
     apply(simp add: get_configuration_def)
     apply(case_tac "d n")
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: get_accessible_configurations_def)
  apply(simp add: is_forward_edge_deterministicHist_SB_long_def is_forward_edge_deterministicHist_DB_long_def get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="i"
      in allE)
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
      x="w1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w2"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e1 c1) i) (Suc i)) = ((get_fixed_scheduler c1))")
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
   apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e2 c2) i) (Suc i)) = ((get_fixed_scheduler c2))")
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
   apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
     apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(rule derivation_append_preserves_derivation_initial)
      apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(rule derivation_append_preserves_derivation)
      apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
      apply(rule derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
     apply(rule der2_is_derivation)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(case_tac "d i")
     apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2 a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2 a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2 option)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
  apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
   apply(rule derivation_append_preserves_derivation_initial)
     apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
     apply(rule derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(rule der2_is_derivation)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d i")
    apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 e1 e2 i w1 w2 option)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac c d c1 c2 e1 e2 i w1 w2)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  done

lemma AX_is_forward_target_deterministic_correspond_DB_SB: "
  TSstructure G
  \<Longrightarrow> is_forward_target_deterministicHist_SB_long G = is_forward_target_deterministicHist_DB_long G"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(simp add: is_forward_target_deterministicHist_SB_long_def is_forward_target_deterministicHist_DB_long_def)
   apply(clarsimp)
   apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
    apply(erule_tac
      x="c1"
      in allE)
    apply(erule_tac
      x="c2"
      in allE)
    apply(erule impE)
     apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
     apply(rule_tac
      x="e"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="w1"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="w2"
      in exI)
     apply(clarsimp)
     apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e c1) n) (Suc n)) = ((get_fixed_scheduler c1))")
      apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
      apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e c2) n) (Suc n)) = ((get_fixed_scheduler c2))")
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
      apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
        apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(rule derivation_append_preserves_derivation_initial)
         apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(rule derivation_append_preserves_derivation)
         apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
         apply(rule derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
        apply(rule der2_is_derivation)
        apply(force)
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
       apply(case_tac "d n")
        apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e w1 w2 a)(*strict*)
       apply(clarsimp)
       apply(case_tac a)
       apply(rename_tac c d n c1 c2 e w1 w2 a option b)(*strict*)
       apply(clarsimp)
       apply(rename_tac c d n c1 c2 e w1 w2 option)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
     apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
      apply(rule derivation_append_preserves_derivation_initial)
        apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
      apply(rule derivation_append_preserves_derivation)
        apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
        apply(rule derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(rule der2_is_derivation)
       apply(force)
      apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
      apply(simp add: get_configuration_def)
      apply(case_tac "d n")
       apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e w1 w2 a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac c d n c1 c2 e w1 w2 a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac c d n c1 c2 e w1 w2 option)(*strict*)
      apply(simp add: der2_def)
     apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
   apply(simp add: get_accessible_configurations_def)
  apply(simp add: is_forward_target_deterministicHist_SB_long_def is_forward_target_deterministicHist_DB_long_def get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="w1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="w2"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e c1) i) (Suc i)) = ((get_fixed_scheduler c1))")
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   apply(subgoal_tac "(get_fixed_scheduler_DB G (derivation_append d (der2 c e c2) i) (Suc i)) = ((get_fixed_scheduler c2))")
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
     apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(rule derivation_append_preserves_derivation_initial)
      apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(rule derivation_append_preserves_derivation)
      apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
      apply(rule derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
     apply(rule der2_is_derivation)
     apply(force)
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "d i")
     apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 i e w1 w2 a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac c d c1 c2 i e w1 w2 a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d c1 c2 i e w1 w2 option)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
  apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   apply(rule derivation_append_preserves_derivation_initial)
     apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
     apply(rule derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(rule der2_is_derivation)
    apply(force)
   apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d i")
    apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 i e w1 w2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c d c1 c2 i e w1 w2 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d c1 c2 i e w1 w2 option)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac c d c1 c2 i e w1 w2)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  done

lemma is_forward_deterministic_correspond_DB_SB: "
  TSstructure G
  \<Longrightarrow> is_forward_deterministicHist_SB G = is_forward_deterministicHist_DB G"
  apply (metis AX_is_forward_edge_deterministic_correspond_DB_SB AX_is_forward_target_deterministic_correspond_DB_SB is_forward_deterministicHist_DB_def is_forward_deterministicHist_SB_def)
  done

end

end
