section {*L\_ATS\_SchedF\_SDB*}
theory
  L_ATS_SchedF_SDB

imports
  L_ATS_SchedF_DB
  L_ATS_SchedF_SB

begin

locale ATS_SchedF_SDB =
  ATS_SchedF_SB
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
  +
  ATS_SchedF_DB
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
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable get_fixed_scheduler get_fixed_scheduler_DB
    +

assumes AX_state_based_vs_derivation_based_get_fixed_scheduler: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> get_fixed_scheduler_DB G d n = get_fixed_scheduler c"

context ATS_SchedF_SDB
begin

lemma Nonblockingness_branching_SB_DB_restricted: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_branching_restricted G \<longleftrightarrow> Nonblockingness_branching_restricted_DB G"
  apply(rule order_antisym)
   apply(simp add: Nonblockingness_branching_restricted_def Nonblockingness_branching_restricted_DB_def)
   apply(clarsimp)
   apply(rename_tac dh n)(*strict*)
   apply(erule_tac
      x="dh"
      in allE)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
    apply(rename_tac dh n)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n e c)(*strict*)
    apply(subgoal_tac "get_fixed_scheduler_DB G dh n = get_fixed_scheduler c")
     apply(rename_tac dh n e c)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac dh n e c)(*strict*)
    apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
      apply(rename_tac dh n e c)(*strict*)
      apply(force)
     apply(rename_tac dh n e c)(*strict*)
     apply(force)
    apply(rename_tac dh n e c)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(rule some_position_has_details_before_max_dom)
     apply(rename_tac dh n)(*strict*)
     apply(rule derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(simp add: Nonblockingness_branching_restricted_def Nonblockingness_branching_restricted_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac dh n)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e c)(*strict*)
   apply(subgoal_tac "get_fixed_scheduler_DB G dh n = get_fixed_scheduler c")
    apply(rename_tac dh n e c)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac dh n e c)(*strict*)
   apply(rule AX_state_based_vs_derivation_based_get_fixed_scheduler)
     apply(rename_tac dh n e c)(*strict*)
     apply(force)
    apply(rename_tac dh n e c)(*strict*)
    apply(force)
   apply(rename_tac dh n e c)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(rule some_position_has_details_before_max_dom)
    apply(rename_tac dh n)(*strict*)
    apply(rule derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(force)
  done

end

end
