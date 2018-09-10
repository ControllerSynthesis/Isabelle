section {*L\_ATS\_SchedF\_Basic*}
theory
  L_ATS_SchedF_Basic

imports
  PRJ_06_03__ENTRY

begin

locale ATS_SchedF_Basic =
  ATS_Language
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect
    +
  fixes fixed_schedulers :: "'TSstructure \<Rightarrow> 'fixed_scheduler set"
  fixes empty_fixed_scheduler :: "'TSstructure \<Rightarrow> 'fixed_scheduler"
  fixes fixed_scheduler_extendable :: "'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"

assumes AX_empty_fixed_scheduler_in_fixed_schedulers: "
  TSstructure G
  \<Longrightarrow> empty_fixed_scheduler G \<in> fixed_schedulers G"

end

