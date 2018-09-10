section {*L\_ATS\_SchedUF\_Basic*}
theory
  L_ATS_SchedUF_Basic

imports
  L_ATS_Scheduler_Fragment

begin

locale ATS_SchedUF_Basic =
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

fixes unfixed_schedulers :: "'TSstructure \<Rightarrow> 'unfixed_scheduler set"
fixes empty_unfixed_scheduler :: "'TSstructure \<Rightarrow> 'unfixed_scheduler"
fixes unfixed_scheduler_right_quotient :: "'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'scheduler_fragment option"
fixes extend_unfixed_scheduler :: "'scheduler_fragment \<Rightarrow> 'unfixed_scheduler \<Rightarrow> 'unfixed_scheduler"
fixes unfixed_scheduler_extendable :: "'TSstructure \<Rightarrow> 'unfixed_scheduler \<Rightarrow> bool"

assumes AX_extend_unfixed_scheduler_preserves_unfixed_scheduler_extendable: "
  TSstructure G
  \<Longrightarrow> unfixed_scheduler_extendable G sUF
  \<Longrightarrow> unfixed_scheduler_extendable G (extend_unfixed_scheduler sE sUF)"

assumes AX_extend_unfixed_scheduler_unfixed_scheduler_right_quotient_empty: "
  TSstructure G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient sUF (empty_unfixed_scheduler G))) (empty_unfixed_scheduler G) = sUF"

assumes AX_extend_unfixed_scheduler_left_neutral: "
  TSstructure G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> extend_unfixed_scheduler (empty_scheduler_fragment G) sUF = sUF"

assumes AX_unfixed_scheduler_right_quotient_all: "
  TSstructure G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> unfixed_scheduler_right_quotient sUF sUF = Some (empty_scheduler_fragment G)"

assumes AX_empty_unfixed_scheduler_in_unfixed_schedulers: "
  TSstructure G
  \<Longrightarrow> empty_unfixed_scheduler G \<in> unfixed_schedulers G"

assumes AX_extend_unfixed_scheduler_closed: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> unfixed_scheduler_extendable G sUF
  \<Longrightarrow> extend_unfixed_scheduler sE sUF \<in> unfixed_schedulers G"

context ATS_SchedUF_Basic
begin

lemma AX_extend_unfixed_scheduler_closed_prime: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> (unfixed_scheduler_extendable G sUF) \<or> (sE = empty_scheduler_fragment G)
  \<Longrightarrow> extend_unfixed_scheduler sE sUF \<in> unfixed_schedulers G"
  apply(erule disjE)
   apply (metis AX_extend_unfixed_scheduler_closed)
  apply (metis AX_extend_unfixed_scheduler_left_neutral)
  done

end

end
