section {*L\_ATS\_SchedUF\_SDB*}
theory
  L_ATS_SchedUF_SDB

imports
  L_ATS_SchedUF_DB
  L_ATS_SchedUF_SB

begin

locale ATS_SchedUF_SDB =
  ATS_SchedUF_SB
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
  +
  ATS_SchedUF_DB
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
  "set_unfixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  "get_unfixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect scheduler_fragments empty_scheduler_fragment join_scheduler_fragments unfixed_schedulers empty_unfixed_scheduler unfixed_scheduler_right_quotient extend_unfixed_scheduler unfixed_scheduler_extendable set_unfixed_scheduler get_unfixed_scheduler set_unfixed_scheduler_DB get_unfixed_scheduler_DB
    +

assumes AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G d n)
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> get_unfixed_scheduler (set_unfixed_scheduler_DB G d n sUF) = sUF"

assumes AX_state_based_vs_derivation_based_get_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> get_unfixed_scheduler_DB G d n = get_unfixed_scheduler c"

assumes AX_state_based_vs_derivation_based_set_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> set_unfixed_scheduler_DB G d n sUF = set_unfixed_scheduler c sUF"

end

