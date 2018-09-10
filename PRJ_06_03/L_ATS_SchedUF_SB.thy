section {*L\_ATS\_SchedUF\_SB*}
theory
  L_ATS_SchedUF_SB

imports
  L_ATS_SchedUF_Basic

begin

locale ATS_SchedUF_SB =
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
  fixes set_unfixed_scheduler :: "'conf \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'conf"
  fixes get_unfixed_scheduler :: "'conf \<Rightarrow> 'unfixed_scheduler"

assumes AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> c2 \<in> configurations G
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler c1)
  \<Longrightarrow> set_unfixed_scheduler c1 (get_unfixed_scheduler c2) = c2
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler c2)"

assumes AX_get_unfixed_scheduler_closed: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> get_unfixed_scheduler c \<in> unfixed_schedulers G"

assumes AX_set_unfixed_scheduler_set: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> sUF1 \<in> unfixed_schedulers G
  \<Longrightarrow> sUF2 \<in> unfixed_schedulers G
  \<Longrightarrow> set_unfixed_scheduler (set_unfixed_scheduler c sUF1) sUF2 = set_unfixed_scheduler c sUF2"

assumes AX_get_set_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> get_unfixed_scheduler (set_unfixed_scheduler c sUF) = sUF"

assumes AX_set_unfixed_scheduler_get: "
  TSstructure G
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> c2 \<in> configurations G
  \<Longrightarrow> \<exists>sUF\<in> unfixed_schedulers G. set_unfixed_scheduler c1 sUF = set_unfixed_scheduler c2 sUF
  \<Longrightarrow> set_unfixed_scheduler c1 (get_unfixed_scheduler c2) = c2"

assumes AX_unfixed_scheduler_right_quotient_split: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> d m = Some (pair e2 c2)
  \<Longrightarrow> d k = Some (pair e3 c3)
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> m\<le>k
  \<Longrightarrow> (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler c1) (get_unfixed_scheduler c3))) = join_scheduler_fragments (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler c1) (get_unfixed_scheduler c2))) (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler c2) (get_unfixed_scheduler c3)))"

context ATS_SchedUF_SB begin

definition map_unfixed_scheduler :: "
  ('label, 'conf) derivation
  \<Rightarrow> ('unfixed_scheduler \<Rightarrow> 'unfixed_scheduler)
  \<Rightarrow> ('label, 'conf) derivation"
  where
    "map_unfixed_scheduler d C \<equiv>
  (\<lambda>n. case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow> Some (pair e (set_unfixed_scheduler c (C (get_unfixed_scheduler c)))))"

definition map_unfixed_scheduler_ALT :: "
  ('label, 'conf) derivation
  \<Rightarrow> ('unfixed_scheduler \<Rightarrow> 'unfixed_scheduler)
  \<Rightarrow> ('label, 'conf) derivation"
  where
    "map_unfixed_scheduler_ALT d C \<equiv>
  derivation_map d (\<lambda>c. set_unfixed_scheduler c (C (get_unfixed_scheduler c)))"

lemma map_unfixed_scheduler_ALT_vs_map_unfixed_scheduler: "
  map_unfixed_scheduler_ALT d C = map_unfixed_scheduler d C"
  apply(simp add: map_unfixed_scheduler_ALT_def map_unfixed_scheduler_def derivation_map_def)
  done

definition get_unfixed_scheduler_nth :: "
  ('label, 'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'unfixed_scheduler"
  where
    "get_unfixed_scheduler_nth d n \<equiv>
  get_unfixed_scheduler (the (get_configuration (d n)))"

definition replace_unfixed_scheduler :: "
  'TSstructure
  \<Rightarrow> ('label, 'conf) derivation
  \<Rightarrow> 'unfixed_scheduler
  \<Rightarrow> nat
  \<Rightarrow> ('label, 'conf) derivation"
  where
    "replace_unfixed_scheduler G d1 sUF n
  \<equiv> map_unfixed_scheduler
      d1
      (\<lambda>c. extend_unfixed_scheduler
       (the
         (unfixed_scheduler_right_quotient
           c
           (get_unfixed_scheduler_nth d1 n)))
       sUF)"

definition PB_Nonblockingness_RestSB :: "
  'TSstructure
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_RestSB G dh n \<equiv>
  unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)"

definition PB_Nonblockingness_branching_SB_restricted :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_branching_SB_restricted G \<equiv>
  Nonblockingness_pattern G
  PB_Nonblockingness_RestSB
  PB_Nonblockingness_NoAdapt"

definition PB_Nonblockingness_AdaptSB :: "
  'TSstructure
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_AdaptSB G dh nh dc nc dh' \<equiv>
  if (unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh nh))
  then
  dh' = replace_unfixed_scheduler G dh (get_unfixed_scheduler_nth dc 0) nh
  else dh' = dh"

end

end

