section {*L\_ATS\_Sched\_SB*}
theory
  L_ATS_Sched_SB

imports
  L_ATS_SchedF_SB
  L_ATS_SchedUF_SB
  L_ATS_Sched_Basic

begin

print_locale ATS_Sched_Basic

locale ATS_Sched_SB =
  ATS_Sched_Basic
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
  +
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
  ATS_SchedF_SB
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
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable scheduler_fragments empty_scheduler_fragment join_scheduler_fragments unfixed_schedulers empty_unfixed_scheduler unfixed_scheduler_right_quotient extend_unfixed_scheduler unfixed_scheduler_extendable schedulers initial_schedulers empty_scheduler get_scheduler extend_scheduler join_fixed_scheduler_unfixed_scheduler set_unfixed_scheduler get_unfixed_scheduler get_fixed_scheduler
    +
  assumes AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler: "
  TSstructure G
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> c2 \<in> configurations G
  \<Longrightarrow> set_unfixed_scheduler c1 (get_unfixed_scheduler c2) = c2
  \<Longrightarrow> get_fixed_scheduler c1 = get_fixed_scheduler c2"

assumes AX_not_extendable_fixed_scheduler_implies_empty_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> \<not> fixed_scheduler_extendable G (get_fixed_scheduler c)
  \<Longrightarrow> get_unfixed_scheduler c = empty_unfixed_scheduler G"

assumes AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> get_scheduler c = join_fixed_scheduler_unfixed_scheduler (get_fixed_scheduler c) (get_unfixed_scheduler c)"

assumes AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler c) = fixed_scheduler_extendable G (get_fixed_scheduler c)"

context ATS_Sched_SB begin

corollary Nonblockingness_branching_restricted_vs_PB_Nonblockingness_branching_SB_restricted: "
  TSstructure G
  \<Longrightarrow> PB_Nonblockingness_branching_SB_restricted G = Nonblockingness_branching_restricted G"
  apply(simp add: Nonblockingness_branching_restricted_def PB_Nonblockingness_branching_SB_restricted_def Nonblockingness_pattern_def PB_Nonblockingness_RestSB_def PB_Nonblockingness_NoAdapt_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac dh n)(*strict*)
   apply(erule_tac
      x="dh"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)")
    apply(rename_tac dh n)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(simp add: get_unfixed_scheduler_nth_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac dh n)(*strict*)
    prefer 2
    apply(rule_tac
      c="the (get_configuration (dh n))"
      in AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(simp add: get_configuration_def maximum_of_domain_def)
    apply(clarsimp)
    apply(rename_tac dh n y)(*strict*)
    apply(case_tac y)
    apply(rename_tac dh n y option conf)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n option conf)(*strict*)
    apply (metis derivation_initial_configurations)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(simp add: get_unfixed_scheduler_nth_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule_tac
      c="the (get_configuration (dh n))"
      in AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(simp add: get_configuration_def maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac dh n y)(*strict*)
   apply(case_tac y)
   apply(rename_tac dh n y option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n option conf)(*strict*)
   apply (metis derivation_initial_configurations)
  apply(rename_tac dh n)(*strict*)
  apply(force)
  done

definition PB_Nonblockingness_linear_SB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_linear_SB G \<equiv>
  Nonblockingness_pattern G
  PB_Nonblockingness_NoRest
  PB_Nonblockingness_AdaptSB"

definition Nonblockingness_linear :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_linear G \<equiv>
  \<forall>dh n.
  derivation_initial G dh
  \<and> maximum_of_domain dh n
  \<longrightarrow> (\<exists>dc dh' n'.
  (
  if (unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n))
  then
  dh' = replace_unfixed_scheduler G dh (get_unfixed_scheduler_nth dc 0) n
  else dh' = dh
  )
  \<and> derivation G dc
  \<and> belongs G dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh' dc n
  \<and> marking_condition G (derivation_append dh' dc n))"

corollary PB_Nonblockingness_linear_SB_vs_Nonblockingness_linear: "
  PB_Nonblockingness_linear_SB G = Nonblockingness_linear G"
  apply(simp only: PB_Nonblockingness_AdaptSB_def PB_Nonblockingness_NoRest_def Nonblockingness_pattern_def PB_Nonblockingness_linear_SB_def Nonblockingness_linear_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac dh n)(*strict*)
   apply(erule_tac
      x="dh"
      in allE)
   apply(erule impE)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(erule impE)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(erule exE)+
   apply(rename_tac dh n dh' dc)(*strict*)
   apply(rule_tac
      x="dc"
      in exI)
   apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)")
    apply(rename_tac dh n dh' dc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dh n dh' dc)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(erule impE)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(erule exE)+
  apply(rename_tac dh n dc dh')(*strict*)
  apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)")
   apply(rename_tac dh n dc dh')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n dc dh')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(force)
  done

definition PB_Nonblockingness_linear_SB_restricted :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_linear_SB_restricted G \<equiv>
  Nonblockingness_pattern G
  PB_Nonblockingness_RestSB
  PB_Nonblockingness_AdaptSB"

definition Nonblockingness_linear_restricted :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_linear_restricted G \<equiv>
  \<forall>dh n.
  derivation_initial G dh
  \<and> maximum_of_domain dh n
  \<and> unfixed_scheduler_extendable G (get_unfixed_scheduler_nth dh n)
  \<longrightarrow> (\<exists>dc dh' n'.
  dh' = replace_unfixed_scheduler G dh (get_unfixed_scheduler_nth dc 0) n
  \<and> derivation G dc
  \<and> belongs G dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh' dc n
  \<and> marking_condition G (derivation_append dh' dc n))"

corollary PB_Nonblockingness_linear_SB_restricted_vs_Nonblockingness_linear_restricted: "
  PB_Nonblockingness_linear_SB_restricted G = Nonblockingness_linear_restricted G"
  apply(simp add: Nonblockingness_linear_restricted_def PB_Nonblockingness_linear_SB_restricted_def Nonblockingness_pattern_def PB_Nonblockingness_RestSB_def PB_Nonblockingness_AdaptSB_def)
  apply(force)
  done

lemma get_unfixed_scheduler_nth_direct: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> get_unfixed_scheduler_nth d n = get_unfixed_scheduler c"
  apply(simp add: get_unfixed_scheduler_nth_def get_configuration_def)
  done

lemma map_unfixed_scheduler_split: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> (\<And>n e c. d n = Some (pair e c) \<Longrightarrow> f (get_unfixed_scheduler c) \<in> unfixed_schedulers G )
  \<Longrightarrow> (\<And>sUF. sUF \<in> unfixed_schedulers G \<Longrightarrow> g sUF \<in> unfixed_schedulers G )
  \<Longrightarrow> map_unfixed_scheduler d (\<lambda>sUF. g (f sUF)) = map_unfixed_scheduler (map_unfixed_scheduler d (\<lambda>sUF. f sUF)) (\<lambda>sUF. g sUF)"
  apply(simp add: map_unfixed_scheduler_def)
  apply(rule ext)
  apply(rename_tac n)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n option b)(*strict*)
  apply(subgoal_tac "b \<in> configurations G")
   apply(rename_tac n option b)(*strict*)
   prefer 2
   apply(rule belongs_configurations)
    apply(rename_tac n option b)(*strict*)
    apply(force)
   apply(rename_tac n option b)(*strict*)
   apply(force)
  apply(rename_tac n option b)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler (set_unfixed_scheduler b (f (get_unfixed_scheduler b)))"
      and s="f (get_unfixed_scheduler b)"
      in ssubst)
   apply(rename_tac n option b)(*strict*)
   apply(rule AX_get_set_unfixed_scheduler)
     apply(rename_tac n option b)(*strict*)
     apply(force)
    apply(rename_tac n option b)(*strict*)
    apply(force)
   apply(rename_tac n option b)(*strict*)
   apply(force)
  apply(rename_tac n option b)(*strict*)
  apply(rule_tac
      t="set_unfixed_scheduler (set_unfixed_scheduler b (f (get_unfixed_scheduler b))) (g ((f (get_unfixed_scheduler b))))"
      and s="set_unfixed_scheduler b (g ((f (get_unfixed_scheduler b))))"
      in ssubst)
   apply(rename_tac n option b)(*strict*)
   apply(rule AX_set_unfixed_scheduler_set)
      apply(rename_tac n option b)(*strict*)
      apply(force)
     apply(rename_tac n option b)(*strict*)
     apply(force)
    apply(rename_tac n option b)(*strict*)
    apply(force)
   apply(rename_tac n option b)(*strict*)
   apply(force)
  apply(rename_tac n option b)(*strict*)
  apply(force)
  done

theorem Nonblockingness_linear_implies_Nonblockingness_linear_restricted: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_linear G
  \<Longrightarrow> Nonblockingness_linear_restricted G"
  apply(simp add: Nonblockingness_linear_restricted_def Nonblockingness_linear_def)
  apply(force)
  done

end

end
