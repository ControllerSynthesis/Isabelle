section {*L\_ATS\_SchedF\_DB*}
theory
  L_ATS_SchedF_DB

imports
  L_ATS_SchedF_Basic

begin

locale ATS_SchedF_DB =
  ATS_SchedF_Basic
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
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable
    +
  fixes get_fixed_scheduler_DB :: "'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"

assumes AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> get_fixed_scheduler_DB G d n \<in> fixed_schedulers G"

assumes AX_get_fixed_scheduler_DB_restrict: "
  TSstructure G
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = get_fixed_scheduler_DB G d1 x"

assumes AX_schedF_db_extendable_translates_backwards: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> belongs G d1
  \<Longrightarrow> d1 (n + x) \<noteq> None
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler_DB G d1 (n + x))
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler_DB G d1 n)"

context ATS_SchedF_DB begin

definition Nonblockingness_branching_restricted_DB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_branching_restricted_DB G \<equiv>
  \<forall>dh n.
  derivation_initial G dh
  \<and> maximum_of_domain dh n
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler_DB G dh n)
  \<longrightarrow> (\<exists>dc n'.
  derivation G dc
  \<and> belongs G dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh dc n
  \<and> marking_condition G (derivation_append dh dc n))"

end

end
