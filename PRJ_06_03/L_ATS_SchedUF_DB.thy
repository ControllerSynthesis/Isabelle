section {*L\_ATS\_SchedUF\_DB*}
theory
  L_ATS_SchedUF_DB

imports
  L_ATS_SchedUF_Basic

begin

print_locale ATS_SchedUF_Basic

locale ATS_SchedUF_DB =
  ATS_SchedUF_Basic
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
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect scheduler_fragments empty_scheduler_fragment join_scheduler_fragments unfixed_schedulers empty_unfixed_scheduler unfixed_scheduler_right_quotient extend_unfixed_scheduler unfixed_scheduler_extendable
    +
  fixes set_unfixed_scheduler_DB :: "'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  fixes get_unfixed_scheduler_DB :: "'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler"

assumes AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G d j)
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> j \<le> n
  \<Longrightarrow> the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G d i) (get_unfixed_scheduler_DB G d j)) \<in> scheduler_fragments G"

assumes AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G d 0)"

assumes AX_get_unfixed_scheduler_DB_closed: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> get_unfixed_scheduler_DB G d n \<in> unfixed_schedulers G"

assumes AX_set_unfixed_scheduler_DB_preserves_initial_configurations: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> c \<in> initial_configurations G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G d 0)
  \<Longrightarrow> unfixed_scheduler_extendable G sUF
  \<Longrightarrow> set_unfixed_scheduler_DB G d 0 sUF \<in> initial_configurations G"

assumes AX_get_unfixed_scheduler_DB_invariant_under_derivation_take: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> n \<le> m
  \<Longrightarrow> get_unfixed_scheduler_DB G d n = get_unfixed_scheduler_DB G (derivation_take d m) n"

context ATS_SchedUF_DB begin

definition PB_Nonblockingness_RestDB :: "
  'TSstructure
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_RestDB G dh n \<equiv>
  unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)"

definition PB_Nonblockingness_branching_DB_restricted :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_branching_DB_restricted G \<equiv>
  Nonblockingness_pattern G
  PB_Nonblockingness_RestDB
  PB_Nonblockingness_NoAdapt"

definition map_unfixed_scheduler_DB :: "
  'TSstructure
  \<Rightarrow> ('label, 'conf) derivation
  \<Rightarrow> ('unfixed_scheduler \<Rightarrow> 'unfixed_scheduler)
  \<Rightarrow> ('label, 'conf) derivation"
  where
    "map_unfixed_scheduler_DB G d C \<equiv>
  \<lambda>n. case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow> Some (pair e (set_unfixed_scheduler_DB G d n (C (get_unfixed_scheduler_DB G d n))))"

definition replace_unfixed_scheduler_DB :: "
  'TSstructure
  \<Rightarrow> ('label, 'conf) derivation
  \<Rightarrow> 'unfixed_scheduler
  \<Rightarrow> nat
  \<Rightarrow> ('label, 'conf) derivation"
  where
    "replace_unfixed_scheduler_DB G d1 sUF n = map_unfixed_scheduler_DB G d1 (\<lambda>c. extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G d1 n))) sUF)"

end

end

