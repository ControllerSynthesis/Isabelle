section {*L\_ATS\_Scheduler\_Fragment*}
theory
  L_ATS_Scheduler_Fragment

imports
  PRJ_06_03__ENTRY

begin

locale ATS_Scheduler_Fragment =
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
  fixes scheduler_fragments :: "'TSstructure \<Rightarrow> 'scheduler_fragment set"
  fixes empty_scheduler_fragment :: "'TSstructure \<Rightarrow> 'scheduler_fragment"
  fixes join_scheduler_fragments :: "'scheduler_fragment \<Rightarrow> 'scheduler_fragment \<Rightarrow> 'scheduler_fragment"

assumes AX_join_scheduler_fragments_foldl_split: "
  f = join_scheduler_fragments
  \<Longrightarrow> e = empty_scheduler_fragment G
  \<Longrightarrow> foldl f e (w @ v) = f (foldl f e w) (foldl f e v)"

assumes AX_empty_scheduler_fragment_in_scheduler_fragments: "
  TSstructure G
  \<Longrightarrow> empty_scheduler_fragment G \<in> scheduler_fragments G"

assumes AX_join_scheduler_fragments_closed: "
  TSstructure G
  \<Longrightarrow> sE1 \<in> scheduler_fragments G
  \<Longrightarrow> sE2 \<in> scheduler_fragments G
  \<Longrightarrow> join_scheduler_fragments sE1 sE2 \<in> scheduler_fragments G"

assumes AX_join_scheduler_fragments_associative: "
  TSstructure G
  \<Longrightarrow> sE1 \<in> scheduler_fragments G
  \<Longrightarrow> sE2 \<in> scheduler_fragments G
  \<Longrightarrow> sE3 \<in> scheduler_fragments G
  \<Longrightarrow> join_scheduler_fragments sE1 (join_scheduler_fragments sE2 sE3) = join_scheduler_fragments (join_scheduler_fragments sE1 sE2) sE3"

assumes AX_join_scheduler_fragments_neutral_left: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> join_scheduler_fragments sE (empty_scheduler_fragment G) = sE"

assumes AX_join_scheduler_fragments_neutral_right: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> join_scheduler_fragments (empty_scheduler_fragment G) sE = sE"

assumes AX_foldl_join_scheduler_fragments: "
  TSstructure G
  \<Longrightarrow> sE \<in> scheduler_fragments G
  \<Longrightarrow> set w \<subseteq> scheduler_fragments G
  \<Longrightarrow> foldl join_scheduler_fragments sE w = join_scheduler_fragments sE (foldl join_scheduler_fragments (empty_scheduler_fragment G) w)"

end

