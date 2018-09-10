section {*L\_ATS\_Sched*}
theory
  L_ATS_Sched

imports
  L_ATS_Scheduler_Fragment

begin

locale ATS_Sched =
  ATS_Scheduler_Fragment
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
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect scheduler_fragments empty_scheduler_fragment join_scheduler_fragments
    +
  fixes schedulers :: "'TSstructure \<Rightarrow> 'scheduler set"
  fixes initial_schedulers :: "'TSstructure \<Rightarrow> 'scheduler set"
  fixes empty_scheduler :: "'TSstructure \<Rightarrow> 'scheduler"
  fixes get_scheduler :: "'conf \<Rightarrow> 'scheduler"

fixes extend_scheduler :: "'scheduler_fragment \<Rightarrow> 'scheduler \<Rightarrow> 'scheduler"

assumes AX_extend_scheduler_compatible_to_join_scheduler_fragments: "
  TSstructure G
  \<Longrightarrow> sE1 \<in> scheduler_fragments G
  \<Longrightarrow> sE2 \<in> scheduler_fragments G
  \<Longrightarrow> s1 \<in> schedulers G
  \<Longrightarrow> extend_scheduler (join_scheduler_fragments sE1 sE2) s1 = extend_scheduler sE1 (extend_scheduler sE2 s1)"

assumes AX_extend_scheduler_left_injective: "
  TSstructure G
  \<Longrightarrow> sE1 \<in> scheduler_fragments G
  \<Longrightarrow> sE2 \<in> scheduler_fragments G
  \<Longrightarrow> s \<in> schedulers G
  \<Longrightarrow> extend_scheduler sE1 s = extend_scheduler sE2 s
  \<Longrightarrow> sE1 = sE2"

assumes AX_extend_scheduler_right_injective: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> s1 \<in> schedulers G
  \<Longrightarrow> s2 \<in> schedulers G
  \<Longrightarrow> extend_scheduler sE s1 = extend_scheduler sE s2
  \<Longrightarrow> s1 = s2"

assumes AX_empty_scheduler_in_schedulers: "
  TSstructure G
  \<Longrightarrow> empty_scheduler G \<in> schedulers G"

assumes AX_get_scheduler_closed: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> get_scheduler c \<in> schedulers G"

assumes AX_initial_schedulers_in_schedulers: "
  TSstructure G
  \<Longrightarrow> s \<in> initial_schedulers G
  \<Longrightarrow> s \<in> schedulers G"

assumes AX_extend_scheduler_closed: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> s \<in> schedulers G
  \<Longrightarrow> extend_scheduler sE s \<in> schedulers G"

assumes AX_extend_scheduler_left_neutral: "
  TSstructure G
  \<Longrightarrow> s \<in> schedulers G
  \<Longrightarrow> extend_scheduler (empty_scheduler_fragment G) s = s"

assumes AX_extend_scheduler_left_neutral_unique: "
  TSstructure G
  \<Longrightarrow> s \<in> schedulers G
  \<Longrightarrow> extend_scheduler sE s = s
  \<Longrightarrow> sE = empty_scheduler_fragment G"

context ATS_Sched begin

definition get_scheduler_nth :: "
  ('label, 'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'scheduler"
  where
    "get_scheduler_nth d n \<equiv>
  get_scheduler (the (get_configuration (d n)))"

end

end
