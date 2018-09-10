section {*L\_ATS\_Sched\_SDB*}
theory
  L_ATS_Sched_SDB

imports
  L_ATS_SchedF_SDB
  L_ATS_SchedUF_SDB
  L_ATS_Sched_DB
  L_ATS_Sched_SB

begin

locale ATS_Sched_SDB =
  ATS_Sched_SB
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
  "scheduler_fragments :: 'TSstructure \<Rightarrow> 'scheduler_fragment set"
  "empty_scheduler_fragment :: 'TSstructure \<Rightarrow> 'scheduler_fragment"
  "join_scheduler_fragments :: 'scheduler_fragment \<Rightarrow> 'scheduler_fragment \<Rightarrow> 'scheduler_fragment"
  "unfixed_schedulers :: 'TSstructure \<Rightarrow> 'unfixed_scheduler set"
  "empty_unfixed_scheduler :: 'TSstructure \<Rightarrow> 'unfixed_scheduler"
  "unfixed_scheduler_right_quotient :: 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'scheduler_fragment option"
  "extend_unfixed_scheduler :: 'scheduler_fragment \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler"
  "unfixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'unfixed_scheduler \<Rightarrow> bool"
  "schedulers :: 'TSstructure \<Rightarrow> 'scheduler set"
  "initial_schedulers :: 'TSstructure \<Rightarrow> 'scheduler set"
  "empty_scheduler :: 'TSstructure \<Rightarrow> 'scheduler"
  "get_scheduler :: 'conf \<Rightarrow> 'scheduler"
  "extend_scheduler :: 'scheduler_fragment \<Rightarrow> 'scheduler \<Rightarrow> 'scheduler"
  "join_fixed_scheduler_unfixed_scheduler :: 'fixed_scheduler \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'scheduler"
  "set_unfixed_scheduler :: 'conf \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  "get_unfixed_scheduler :: 'conf \<Rightarrow> 'unfixed_scheduler"
  "get_fixed_scheduler :: 'conf \<Rightarrow> 'fixed_scheduler"
  +
  ATS_Sched_DB
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
  "scheduler_fragments :: 'TSstructure \<Rightarrow> 'scheduler_fragment set"
  "empty_scheduler_fragment :: 'TSstructure \<Rightarrow> 'scheduler_fragment"
  "join_scheduler_fragments :: 'scheduler_fragment \<Rightarrow> 'scheduler_fragment \<Rightarrow> 'scheduler_fragment"
  "unfixed_schedulers :: 'TSstructure \<Rightarrow> 'unfixed_scheduler set"
  "empty_unfixed_scheduler :: 'TSstructure \<Rightarrow> 'unfixed_scheduler"
  "unfixed_scheduler_right_quotient :: 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'scheduler_fragment option"
  "extend_unfixed_scheduler :: 'scheduler_fragment \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler"
  "unfixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'unfixed_scheduler \<Rightarrow> bool"
  "schedulers :: 'TSstructure \<Rightarrow> 'scheduler set"
  "initial_schedulers :: 'TSstructure \<Rightarrow> 'scheduler set"
  "empty_scheduler :: 'TSstructure \<Rightarrow> 'scheduler"
  "get_scheduler :: 'conf \<Rightarrow> 'scheduler"
  "extend_scheduler :: 'scheduler_fragment \<Rightarrow> 'scheduler \<Rightarrow> 'scheduler"
  "join_fixed_scheduler_unfixed_scheduler :: 'fixed_scheduler \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'scheduler"
  "set_unfixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  "get_unfixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler"
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  +
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
  ATS_SchedUF_SDB
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "scheduler_fragments :: 'TSstructure \<Rightarrow> 'scheduler_fragment set"
  "empty_scheduler_fragment :: 'TSstructure \<Rightarrow> 'scheduler_fragment"
  "join_scheduler_fragments :: 'scheduler_fragment \<Rightarrow> 'scheduler_fragment \<Rightarrow> 'scheduler_fragment"
  "unfixed_schedulers :: 'TSstructure \<Rightarrow> 'unfixed_scheduler set"
  "empty_unfixed_scheduler :: 'TSstructure \<Rightarrow> 'unfixed_scheduler"
  "unfixed_scheduler_right_quotient :: 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'scheduler_fragment option"
  "extend_unfixed_scheduler :: 'scheduler_fragment \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler"
  "unfixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'unfixed_scheduler \<Rightarrow> bool"
  "set_unfixed_scheduler :: 'conf \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  "get_unfixed_scheduler :: 'conf \<Rightarrow> 'unfixed_scheduler"
  "set_unfixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  "get_unfixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable scheduler_fragments empty_scheduler_fragment join_scheduler_fragments unfixed_schedulers empty_unfixed_scheduler unfixed_scheduler_right_quotient extend_unfixed_scheduler unfixed_scheduler_extendable schedulers initial_schedulers empty_scheduler get_scheduler extend_scheduler join_fixed_scheduler_unfixed_scheduler set_unfixed_scheduler get_unfixed_scheduler get_fixed_scheduler set_unfixed_scheduler_DB get_unfixed_scheduler_DB get_fixed_scheduler_DB
    +

assumes AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G d n) \<longleftrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_nth d n)"

context ATS_Sched_SDB begin

theorem Nonblockingness_linear_vs_Nonblockingness_linear_DB: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_linear G \<longleftrightarrow> Nonblockingness_linear_DB G"
  apply(rule order_antisym)
  prefer 2
  apply(clarsimp)
  apply(simp add: Nonblockingness_linear_def Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF dh' x)(*strict*)
  apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
  apply(rename_tac dh n dc sUF dh' x)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(subgoal_tac "\<not>unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)")
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(force)
  apply(rename_tac dh n dc x)(*strict*)
  apply (metis maximum_of_domain_def AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  apply(rename_tac dh n dc sUF dh' x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)")
  apply(rename_tac dh n dc sUF x)(*strict*)
  prefer 2
  apply (metis maximum_of_domain_def AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="dc"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(rule_tac
      x="x"
      in exI)
  apply(force)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(simp add: replace_unfixed_scheduler_def)
  apply(subgoal_tac "sUF = get_unfixed_scheduler_nth dc 0")
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(subgoal_tac "(map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0))) = (map_unfixed_scheduler_DB G dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler_nth dc 0)))")
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(simp add: replace_unfixed_scheduler_DB_def)
  apply(rename_tac dh n dc x)(*strict*)
  apply(thin_tac "marking_condition G (derivation_append (replace_unfixed_scheduler_DB G dh (get_unfixed_scheduler_nth dc 0) n) dc n)")
  apply(rename_tac dh n dc x)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB G dh n"
      and s="get_unfixed_scheduler_nth dh n"
      in ssubst)
  apply(rename_tac dh n dc x)(*strict*)
  apply(simp add: get_unfixed_scheduler_nth_def get_configuration_def)
  apply(case_tac "dh n")
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac dh n dc x a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n dc x a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x option b)(*strict*)
  apply(rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
  apply(rename_tac dh n dc x option b)(*strict*)
  apply(force)+
  apply(rename_tac dh n dc x)(*strict*)
  apply(simp add: map_unfixed_scheduler_def map_unfixed_scheduler_DB_def)
  apply(rule ext)
  apply(rename_tac dh n dc x xa)(*strict*)
  apply(case_tac "dh xa")
  apply(rename_tac dh n dc x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x xa a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n dc x xa a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x xa option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB G dh xa"
      and s="get_unfixed_scheduler b"
      in ssubst)
  apply(rename_tac dh n dc x xa option b)(*strict*)
  apply(rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
  apply(rename_tac dh n dc x xa option b)(*strict*)
  apply(force)+
  apply(rename_tac dh n dc x xa option b)(*strict*)
  apply(rule sym)
  apply(rule AX_state_based_vs_derivation_based_set_unfixed_scheduler)
  apply(rename_tac dh n dc x xa option b)(*strict*)
  apply(force)+
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(simp add: get_unfixed_scheduler_nth_def get_scheduler_nth_def get_configuration_def)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
  apply(rename_tac dh n dc sUF x)(*strict*)
  prefer 2
  apply(rule some_position_has_details_at_0)
  apply(force)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x c)(*strict*)
  apply(simp add: map_unfixed_scheduler_DB_def derivation_append_fit_def replace_unfixed_scheduler_DB_def)
  apply(case_tac "dh n")
  apply(rename_tac dh n dc sUF x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n dc sUF x c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(thin_tac "marking_condition G (derivation_append (\<lambda>na. case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e (set_unfixed_scheduler_DB G dh na (extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh na) (get_unfixed_scheduler_DB G dh n))) sUF))))) (dh na)) dc n)")
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(rule_tac
      t="extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n))) sUF"
      and s="sUF"
      in ssubst)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(rule_tac
      t="unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n)"
      and s="Some(empty_scheduler_fragment G)"
      in ssubst)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(rule AX_unfixed_scheduler_right_quotient_all)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(force)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(rule AX_get_unfixed_scheduler_DB_closed)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(force)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(simp add: derivation_initial_def)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply (metis derivation_initial_belongs)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(force)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(clarsimp)
  apply(rule AX_extend_unfixed_scheduler_left_neutral)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(force)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply(force)
  apply(rename_tac dh n dc sUF x option b)(*strict*)
  apply (metis maximum_of_domain_def AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound)
  apply(clarsimp)
  apply(simp add: Nonblockingness_linear_def Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac dh n dc dh' x)(*strict*)
  apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)")
   apply(rename_tac dh n dc dh' x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac dh n dc x)(*strict*)
   apply(subgoal_tac "\<not>unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac dh n dc x)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac dh n dc x)(*strict*)
   apply (metis maximum_of_domain_def AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  apply(rename_tac dh n dc dh' x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
   apply(rename_tac dh n dc x)(*strict*)
   prefer 2
   apply (metis maximum_of_domain_def AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="dc"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac dh n dc x)(*strict*)
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x c)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac dh n dc x c)(*strict*)
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(rename_tac dh n dc x c)(*strict*)
     apply(simp add: derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dc x c)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(rule_tac
      x="get_unfixed_scheduler_nth dc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(simp add: get_unfixed_scheduler_nth_def)
   apply(simp add: get_configuration_def)
   apply (metis belongs_configurations AX_get_unfixed_scheduler_closed)
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(simp add: replace_unfixed_scheduler_def)
  apply(rule conjI)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0))) dc n)")
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(simp add: derivation_append_fit_def get_unfixed_scheduler_nth_def map_unfixed_scheduler_def get_configuration_def)
   apply(rule AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler)
       apply(rename_tac dh n dc x c e ca)(*strict*)
       apply(force)
      apply(rename_tac dh n dc x c e ca)(*strict*)
      prefer 2
      apply(rule belongs_configurations)
       apply(rename_tac dh n dc x c e ca)(*strict*)
       apply(force)
      apply(rename_tac dh n dc x c e ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(rule_tac
      d="dh"
      in belongs_configurations)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     apply(rule derivation_initial_belongs)
      apply(rename_tac dh n dc x c e ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(subgoal_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca))) (get_unfixed_scheduler c) = get_unfixed_scheduler c")
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(rule_tac
      t="unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca)"
      and s="Some (empty_scheduler_fragment G)"
      in ssubst)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply (metis belongs_configurations derivation_initial_belongs AX_unfixed_scheduler_right_quotient_all AX_get_unfixed_scheduler_closed)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(clarsimp)
   apply (metis AX_extend_unfixed_scheduler_left_neutral belongs_configurations AX_get_unfixed_scheduler_closed)
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(simp add: get_scheduler_nth_def get_unfixed_scheduler_nth_def)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      t="get_fixed_scheduler_DB G dh n"
      and s="get_fixed_scheduler ca"
      in ssubst)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply (metis AX_state_based_vs_derivation_based_get_fixed_scheduler)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(rule sym)
   apply(simp add: derivation_append_fit_def map_unfixed_scheduler_def)
   apply(rule_tac
      t="get_fixed_scheduler ca"
      and s="get_fixed_scheduler c"
      in ssubst)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    prefer 2
    apply(rule AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply (metis belongs_configurations)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(subgoal_tac "(extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca))) (get_unfixed_scheduler c)) = get_unfixed_scheduler c")
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(clarsimp)
    apply(rule AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler)
       apply(rename_tac dh n dc x c e ca)(*strict*)
       apply(force)
      apply(rename_tac dh n dc x c e ca)(*strict*)
      apply (metis belongs_configurations derivation_initial_belongs)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     apply (metis belongs_configurations)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(rule_tac
      t="unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca)"
      and s="Some(empty_scheduler_fragment G)"
      in ssubst)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(rule AX_unfixed_scheduler_right_quotient_all)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(rule AX_get_unfixed_scheduler_closed)
     apply(rename_tac dh n dc x c e ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply (metis belongs_configurations derivation_initial_belongs)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(clarsimp)
   apply(rule AX_extend_unfixed_scheduler_left_neutral)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(rule AX_get_unfixed_scheduler_closed)
    apply(rename_tac dh n dc x c e ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply (metis belongs_configurations)
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(force)
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(subgoal_tac "(map_unfixed_scheduler_DB G dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler_nth dc 0)))=(map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0)))")
   apply(rename_tac dh n dc x c e ca)(*strict*)
   apply(simp add: replace_unfixed_scheduler_DB_def)
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0))) dc n)")
  apply(rename_tac dh n dc x c e ca)(*strict*)
  apply(simp add: map_unfixed_scheduler_DB_def map_unfixed_scheduler_def)
  apply(rule ext)
  apply(rename_tac dh n dc x c e ca na)(*strict*)
  apply(case_tac "dh na")
   apply(rename_tac dh n dc x c e ca na)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dc x c e ca na a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n dc x c e ca na a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x c e ca na option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB G dh na"
      and s="get_unfixed_scheduler b"
      in ssubst)
   apply(rename_tac dh n dc x c e ca na option b)(*strict*)
   apply(rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
     apply(rename_tac dh n dc x c e ca na option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x c e ca na option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca na option b)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x c e ca na option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_nth dh n"
      and s="get_unfixed_scheduler ca"
      in ssubst)
   apply(rename_tac dh n dc x c e ca na option b)(*strict*)
   apply(simp add: get_unfixed_scheduler_nth_def get_configuration_def derivation_append_fit_def)
  apply(rename_tac dh n dc x c e ca na option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB G dh n"
      and s="get_unfixed_scheduler ca"
      in ssubst)
   apply(rename_tac dh n dc x c e ca na option b)(*strict*)
   apply(rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
     apply(rename_tac dh n dc x c e ca na option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x c e ca na option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca na option b)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x c e ca na option b)(*strict*)
  apply(rule AX_state_based_vs_derivation_based_set_unfixed_scheduler)
    apply(rename_tac dh n dc x c e ca na option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x c e ca na option b)(*strict*)
   apply(force)+
  done

lemma Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_1: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_linear_restricted G
  \<Longrightarrow> Nonblockingness_linear_restricted_DB G"
  apply(simp add: Nonblockingness_linear_restricted_DB_def Nonblockingness_linear_restricted_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n)(*strict*)
   apply (metis maximum_of_domain_def AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(rule_tac
      x="dc"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh n=Some (pair e c)")
   apply(rename_tac dh n dc x)(*strict*)
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(rename_tac dh n dc x)(*strict*)
     apply(simp add: derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dc x)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0=Some (pair None c)")
   apply(rename_tac dh n dc x)(*strict*)
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(rule_tac
      x="get_unfixed_scheduler c"
      in exI)
  apply(rule conjI)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(rule AX_get_unfixed_scheduler_closed)
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply (metis belongs_configurations)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(subgoal_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca))) (get_unfixed_scheduler c) = get_unfixed_scheduler c")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   prefer 2
   apply(subgoal_tac "unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca) = Some (empty_scheduler_fragment G)")
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply(clarsimp)
    apply (metis AX_extend_unfixed_scheduler_left_neutral belongs_configurations AX_get_unfixed_scheduler_closed)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply (metis derivation_initial_belongs derivation_initial_is_derivation AX_state_based_vs_derivation_based_get_unfixed_scheduler AX_unfixed_scheduler_right_quotient_all AX_get_unfixed_scheduler_DB_closed)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(subgoal_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler c) = get_unfixed_scheduler c")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   prefer 2
   apply(subgoal_tac "unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n) = Some (empty_scheduler_fragment G)")
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply(clarsimp)
    apply (metis AX_extend_unfixed_scheduler_left_neutral belongs_configurations AX_get_unfixed_scheduler_closed)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply (metis derivation_initial_belongs derivation_initial_is_derivation AX_unfixed_scheduler_right_quotient_all AX_get_unfixed_scheduler_DB_closed)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(simp add: replace_unfixed_scheduler_def)
  apply(subgoal_tac "map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0)) = map_unfixed_scheduler_DB G dh (\<lambda>ca. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient ca (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler c)) ")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   prefer 2
   apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0))) dc n)")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(simp add: map_unfixed_scheduler_def)
   apply(simp add: map_unfixed_scheduler_DB_def)
   apply(rule ext)
   apply(rename_tac dh n dc x e c ca na)(*strict*)
   apply(case_tac "dh na")
    apply(rename_tac dh n dc x e c ca na)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x e c ca na a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n dc x e c ca na a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e c ca na option b)(*strict*)
   apply(simp add: get_unfixed_scheduler_nth_def get_configuration_def)
   apply(rule_tac
      t="get_unfixed_scheduler b"
      and s="get_unfixed_scheduler_DB G dh na"
      in subst)
    apply(rename_tac dh n dc x e c ca na option b)(*strict*)
    apply (rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
      apply(rename_tac dh n dc x e c ca na option b)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x e c ca na option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e c ca na option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e c ca na option b)(*strict*)
   apply(rule_tac
      t="get_unfixed_scheduler ca"
      and s="get_unfixed_scheduler_DB G dh n"
      in subst)
    apply(rename_tac dh n dc x e c ca na option b)(*strict*)
    apply (rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
      apply(rename_tac dh n dc x e c ca na option b)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x e c ca na option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e c ca na option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e c ca na option b)(*strict*)
   apply(rule sym)
   apply (rule AX_state_based_vs_derivation_based_set_unfixed_scheduler)
     apply(rename_tac dh n dc x e c ca na option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e c ca na option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e c ca na option b)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(thin_tac "map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0)) = map_unfixed_scheduler_DB G dh (\<lambda>ca. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient ca (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler c))")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler_DB G dh (\<lambda>ca. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient ca (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler c))) dc n)")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(simp add: map_unfixed_scheduler_DB_def)
   apply(rule_tac
      t="unfixed_scheduler_extendable G (get_unfixed_scheduler c)"
      and s="fixed_scheduler_extendable G (get_fixed_scheduler c)"
      in ssubst)
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply (metis belongs_configurations AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(rule_tac
      t="fixed_scheduler_extendable G (get_fixed_scheduler c)"
      and s="fixed_scheduler_extendable G (get_fixed_scheduler_DB G dh n)"
      in ssubst)
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply (metis belongs_configurations derivation_initial_belongs AX_state_based_vs_derivation_based_get_fixed_scheduler AX_state_based_vs_derivation_based_get_unfixed_scheduler AX_state_based_vs_derivation_based_set_unfixed_scheduler AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(rule_tac
      t="fixed_scheduler_extendable G (get_fixed_scheduler_DB G dh n)"
      and s="unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)"
      in ssubst)
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply (metis AX_join_fixed_scheduler_unfixed_scheduler_closed' derivation_initial_belongs derivation_initial_is_derivation maximum_of_domain_def AX_state_based_vs_derivation_based_get_fixed_scheduler AX_state_based_vs_derivation_based_get_unfixed_scheduler AX_get_fixed_scheduler_DB_in_fixed_schedulers AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB AX_get_unfixed_scheduler_DB_closed)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(thin_tac "map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0)) = map_unfixed_scheduler_DB G dh (\<lambda>ca. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient ca (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler c))")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler_DB G dh (\<lambda>ca. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient ca (get_unfixed_scheduler_DB G dh n))) (get_unfixed_scheduler c))) dc n)")
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(simp add: get_scheduler_nth_def map_unfixed_scheduler_DB_def)
   apply(simp add: get_configuration_def)
   apply(thin_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca))) (get_unfixed_scheduler c) = get_unfixed_scheduler c")
   apply(rule_tac
      t="get_fixed_scheduler_DB G dh n"
      and s="get_fixed_scheduler ca"
      in ssubst)
    apply(rename_tac dh n dc x e c ca)(*strict*)
    apply (metis AX_state_based_vs_derivation_based_get_fixed_scheduler)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply(rule_tac
      t="get_fixed_scheduler ca"
      and s="get_fixed_scheduler c"
      in ssubst)
    apply(rename_tac dh n dc x e c ca)(*strict*)
    prefer 2
    apply (metis belongs_configurations AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler)
   apply(rename_tac dh n dc x e c ca)(*strict*)
   apply (metis belongs_configurations derivation_initial_belongs AX_state_based_vs_derivation_based_set_unfixed_scheduler AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler)
  apply(rename_tac dh n dc x e c ca)(*strict*)
  apply(simp add: replace_unfixed_scheduler_DB_def)
  apply(force)
  done

lemma Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_linear_restricted_DB G
  \<Longrightarrow> Nonblockingness_linear_restricted G"
  apply(simp add: Nonblockingness_linear_restricted_DB_def Nonblockingness_linear_restricted_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n)(*strict*)
   apply (metis maximum_of_domain_def AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(rule_tac
      x="dc"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh n=Some (pair e c)")
   apply(rename_tac dh n dc sUF x)(*strict*)
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(rename_tac dh n dc sUF x)(*strict*)
     apply(simp add: derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dc sUF x)(*strict*)
    apply(force)
   apply(rename_tac dh n dc sUF x)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0=Some (pair None c)")
   apply(rename_tac dh n dc sUF x)(*strict*)
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x e c ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x e c ca)(*strict*)
  apply(simp add: replace_unfixed_scheduler_def)
  apply(rule conjI)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(simp add: replace_unfixed_scheduler_DB_def)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler_DB G dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G dh n))) sUF)) dc n)")
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(simp add: map_unfixed_scheduler_DB_def map_unfixed_scheduler_def get_unfixed_scheduler_nth_def get_configuration_def)
   apply(rule_tac
      t="extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca))) (get_unfixed_scheduler c)"
      and s="get_unfixed_scheduler c"
      in ssubst)
    apply(rename_tac dh n dc sUF x e c ca)(*strict*)
    apply(rule_tac
      t="unfixed_scheduler_right_quotient (get_unfixed_scheduler ca) (get_unfixed_scheduler ca)"
      and s="Some (empty_scheduler_fragment G)"
      in ssubst)
     apply(rename_tac dh n dc sUF x e c ca)(*strict*)
     apply (metis belongs_configurations derivation_initial_belongs AX_unfixed_scheduler_right_quotient_all AX_get_unfixed_scheduler_closed)
    apply(rename_tac dh n dc sUF x e c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc sUF x e ca)(*strict*)
    apply (metis AX_extend_unfixed_scheduler_left_neutral belongs_configurations AX_get_unfixed_scheduler_closed)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(subgoal_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n))) sUF=sUF")
    apply(rename_tac dh n dc sUF x e c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc sUF x e ca)(*strict*)
    apply(rule_tac
      t="get_unfixed_scheduler (set_unfixed_scheduler_DB G dh n sUF)"
      and s="sUF"
      in ssubst)
     apply(rename_tac dh n dc sUF x e ca)(*strict*)
     apply (metis maximum_of_domain_def AX_state_based_vs_derivation_based_get_unfixed_scheduler AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound)
    apply(rename_tac dh n dc sUF x e ca)(*strict*)
    apply (metis AX_state_based_vs_derivation_based_set_unfixed_scheduler)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(rule_tac
      t="unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n)"
      and s="Some (empty_scheduler_fragment G)"
      in ssubst)
    apply(rename_tac dh n dc sUF x e c ca)(*strict*)
    apply (metis derivation_initial_belongs derivation_initial_is_derivation AX_unfixed_scheduler_right_quotient_all AX_get_unfixed_scheduler_DB_closed)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc sUF x e ca)(*strict*)
   apply (metis AX_extend_unfixed_scheduler_left_neutral)
  apply(rename_tac dh n dc sUF x e c ca)(*strict*)
  apply(rule_tac
      t="map_unfixed_scheduler dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_nth dh n))) (get_unfixed_scheduler_nth dc 0))"
      and s="map_unfixed_scheduler_DB G dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G dh n))) sUF)"
      in ssubst)
   apply(rename_tac dh n dc sUF x e c ca)(*strict*)
   prefer 2
   apply(simp add: replace_unfixed_scheduler_DB_def)
  apply(rename_tac dh n dc sUF x e c ca)(*strict*)
  apply(rule ext)
  apply(rename_tac dh n dc sUF x e c ca xa)(*strict*)
  apply(simp add: replace_unfixed_scheduler_DB_def)
  apply(thin_tac "marking_condition G (derivation_append (map_unfixed_scheduler_DB G dh (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G dh n))) sUF)) dc n)")
  apply(rename_tac dh n dc sUF x e c ca xa)(*strict*)
  apply(simp add: map_unfixed_scheduler_DB_def map_unfixed_scheduler_def)
  apply(case_tac "dh xa")
   apply(rename_tac dh n dc sUF x e c ca xa)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x e c ca xa a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n dc sUF x e c ca xa a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
  apply(simp add: get_unfixed_scheduler_nth_def get_configuration_def)
  apply(rule_tac
      t="get_unfixed_scheduler b"
      and s="get_unfixed_scheduler_DB G dh xa"
      in subst)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply (rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
     apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler ca"
      and s="get_unfixed_scheduler_DB G dh n"
      in subst)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply (rule AX_state_based_vs_derivation_based_get_unfixed_scheduler)
     apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler c"
      and s="sUF"
      in ssubst)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply(simp add: get_scheduler_nth_def get_configuration_def)
   defer
   apply(rule sym)
   apply (rule AX_state_based_vs_derivation_based_set_unfixed_scheduler)
     apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
     apply(force)
    apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
  apply(simp add: derivation_append_fit_def)
  apply(subgoal_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n))) sUF=sUF")
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   prefer 2
   apply(rule_tac
      t="unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n)"
      and s="Some (empty_scheduler_fragment G)"
      in ssubst)
    apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
    apply (metis derivation_initial_belongs derivation_initial_is_derivation AX_unfixed_scheduler_right_quotient_all AX_get_unfixed_scheduler_DB_closed)
   apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc sUF x e ca xa option b)(*strict*)
   apply (metis AX_extend_unfixed_scheduler_left_neutral)
  apply(rename_tac dh n dc sUF x e c ca xa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc sUF x e ca xa option b)(*strict*)
  apply(thin_tac "extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh n) (get_unfixed_scheduler_DB G dh n))) sUF = sUF")
  apply(rename_tac dh n dc sUF x e ca xa option b)(*strict*)
  apply (metis maximum_of_domain_def AX_state_based_vs_derivation_based_get_unfixed_scheduler AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound)
  done

theorem Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_linear_restricted_DB G \<longleftrightarrow> Nonblockingness_linear_restricted G"
  apply(metis Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_1 Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2)
  done

end

end
