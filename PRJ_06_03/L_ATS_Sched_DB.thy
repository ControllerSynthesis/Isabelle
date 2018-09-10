section {*L\_ATS\_Sched\_DB*}
theory
  L_ATS_Sched_DB

imports
  L_ATS_Sched_DB0

begin

print_locale ATS_Sched_DB0

locale ATS_Sched_DB =
  ATS_Sched_DB0
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
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable scheduler_fragments empty_scheduler_fragment join_scheduler_fragments unfixed_schedulers empty_unfixed_scheduler unfixed_scheduler_right_quotient extend_unfixed_scheduler unfixed_scheduler_extendable schedulers initial_schedulers empty_scheduler get_scheduler extend_scheduler join_fixed_scheduler_unfixed_scheduler set_unfixed_scheduler_DB get_unfixed_scheduler_DB get_fixed_scheduler_DB
    +

assumes AX_replace_unfixed_scheduler_DB_sound: "
  TSstructure G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G d n)
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> unfixed_scheduler_extendable G sUF
  \<Longrightarrow> get_unfixed_scheduler_DB G (replace_unfixed_scheduler_DB G d sUF n) n = sUF"

end

