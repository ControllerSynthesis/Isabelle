section {*L\_ATS\_Sched\_DB0*}
theory
  L_ATS_Sched_DB0

imports
  L_ATS_SchedF_DB
  L_ATS_SchedUF_DB
  L_ATS_Sched_Basic

begin

locale ATS_Sched_DB0 =
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
  +
  ATS_SchedF_DB
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
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable scheduler_fragments empty_scheduler_fragment join_scheduler_fragments unfixed_schedulers empty_unfixed_scheduler unfixed_scheduler_right_quotient extend_unfixed_scheduler unfixed_scheduler_extendable schedulers initial_schedulers empty_scheduler get_scheduler extend_scheduler join_fixed_scheduler_unfixed_scheduler set_unfixed_scheduler_DB get_unfixed_scheduler_DB get_fixed_scheduler_DB
    +
  assumes AX_join_fixed_scheduler_unfixed_scheduler_closed': "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> join_fixed_scheduler_unfixed_scheduler (get_fixed_scheduler_DB G d n) (get_unfixed_scheduler_DB G d n) \<in> schedulers G"

assumes AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> join_fixed_scheduler_unfixed_scheduler (get_fixed_scheduler_DB G d n) (get_unfixed_scheduler_DB G d n) = get_scheduler_nth d n"

assumes AX_sched_modification_preserves_steps: "
  TSstructure G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> derivation G dh
  \<Longrightarrow> belongs G dh
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> fixed_scheduler_extendable G sF
  \<Longrightarrow> unfixed_scheduler_extendable G sUF
  \<Longrightarrow> dh (Suc m) = Some (pair (Some e2) c2)
  \<Longrightarrow> dh m = Some (pair e1 c1)
  \<Longrightarrow> step_relation G c1 e2 c2
  \<Longrightarrow> step_relation G (set_unfixed_scheduler_DB G dh m (extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh m) (get_unfixed_scheduler_DB G dh n))) sUF)) e2 (set_unfixed_scheduler_DB G dh (Suc m) (extend_unfixed_scheduler (the (unfixed_scheduler_right_quotient (get_unfixed_scheduler_DB G dh (Suc m)) (get_unfixed_scheduler_DB G dh n))) sUF))"

assumes AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> sUF = get_unfixed_scheduler_DB G d n
  \<Longrightarrow> sF = get_fixed_scheduler_DB G d n
  \<Longrightarrow> fixed_scheduler_extendable G sF \<longleftrightarrow> unfixed_scheduler_extendable G sUF"

context ATS_Sched_DB0 begin

corollary Nonblockingness_branching_restricted_vs_PB_Nonblockingness_branching_DB_restricted: "
  TSstructure G
  \<Longrightarrow> PB_Nonblockingness_branching_DB_restricted G = Nonblockingness_branching_restricted_DB G"
  apply(simp add: Nonblockingness_branching_restricted_DB_def PB_Nonblockingness_branching_DB_restricted_def Nonblockingness_pattern_def PB_Nonblockingness_RestDB_def PB_Nonblockingness_NoAdapt_def)
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
   apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac dh n)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="dh"
      and n="n"
      in AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB)
        apply(rename_tac dh n)(*strict*)
        apply(force)
       apply(rename_tac dh n)(*strict*)
       apply(force)
      apply(rename_tac dh n)(*strict*)
      apply(simp add: get_configuration_def maximum_of_domain_def)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
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
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="dh"
      and n="n"
      in AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB)
       apply(rename_tac dh n)(*strict*)
       apply(force)
      apply(rename_tac dh n)(*strict*)
      apply(force)
     apply(rename_tac dh n)(*strict*)
     apply(simp add: get_configuration_def maximum_of_domain_def)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(force)
  done

definition PB_Nonblockingness_AdaptDB :: "
  'TSstructure
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_AdaptDB G dh nh dc nc dh' \<equiv>
  \<exists>sUF.
  if (unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh nh))
  then
  sUF \<in> unfixed_schedulers G
  \<and> unfixed_scheduler_extendable G sUF
  \<and> join_fixed_scheduler_unfixed_scheduler (get_fixed_scheduler_DB G dh nh) sUF = get_scheduler_nth dc 0
  \<and> dh' = replace_unfixed_scheduler_DB G dh sUF nh
  else dh' = dh"

definition PB_Nonblockingness_linear_DB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_linear_DB G \<equiv>
  Nonblockingness_pattern G
  PB_Nonblockingness_NoRest
  PB_Nonblockingness_AdaptDB"

definition Nonblockingness_linear_DB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_linear_DB G \<equiv>
  \<forall>dh n.
  derivation_initial G dh
  \<and> maximum_of_domain dh n
  \<longrightarrow> (\<exists>dc sUF dh' n'.
  (
  if (unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n))
  then
  sUF \<in> unfixed_schedulers G
  \<and> unfixed_scheduler_extendable G sUF
  \<and> join_fixed_scheduler_unfixed_scheduler (get_fixed_scheduler_DB G dh n) sUF = get_scheduler_nth dc 0
  \<and> dh' = replace_unfixed_scheduler_DB G dh sUF n
  else dh' = dh
  )
  \<and> derivation G dc
  \<and> belongs G dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh' dc n
  \<and> marking_condition G (derivation_append dh' dc n))"

corollary PB_Nonblockingness_linear_DB_vs_Nonblockingness_linear_DB: "
  PB_Nonblockingness_linear_DB G = Nonblockingness_linear_DB G"
  apply(simp add: PB_Nonblockingness_AdaptDB_def PB_Nonblockingness_linear_DB_def Nonblockingness_pattern_def Nonblockingness_linear_DB_def PB_Nonblockingness_NoRest_def)
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
   apply(rename_tac dh n dh' dc x)(*strict*)
   apply(rule_tac
      x="dc"
      in exI)
   apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac dh n dh' dc x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc x)(*strict*)
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
  apply(rename_tac dh n dc sUF dh')(*strict*)
  apply(rule_tac
      x="dh'"
      in exI)
  apply(rule_tac
      x="dc"
      in exI)
  apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
   apply(rename_tac dh n dc sUF dh')(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF dh')(*strict*)
  apply(force)
  done

definition PB_Nonblockingness_linear_DB_restricted :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_linear_DB_restricted G \<equiv>
  Nonblockingness_pattern G
  PB_Nonblockingness_RestDB
  PB_Nonblockingness_AdaptDB"

definition Nonblockingness_linear_restricted_DB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_linear_restricted_DB G \<equiv>
  \<forall>dh n.
  derivation_initial G dh
  \<and> maximum_of_domain dh n
  \<and> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)
  \<longrightarrow> (\<exists>dc sUF dh' n'.
  sUF \<in> unfixed_schedulers G
  \<and> unfixed_scheduler_extendable G sUF
  \<and> join_fixed_scheduler_unfixed_scheduler (get_fixed_scheduler_DB G dh n) sUF = get_scheduler_nth dc 0
  \<and> dh' = replace_unfixed_scheduler_DB G dh sUF n
  \<and> derivation G dc
  \<and> belongs G dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh' dc n
  \<and> marking_condition G (derivation_append dh' dc n))"

corollary PB_Nonblockingness_linear_DB_restricted_vs_Nonblockingness_linear_restricted_DB: "
PB_Nonblockingness_linear_DB_restricted G = Nonblockingness_linear_restricted_DB G"
  apply(simp add: PB_Nonblockingness_linear_DB_restricted_def Nonblockingness_linear_restricted_DB_def Nonblockingness_pattern_def PB_Nonblockingness_RestDB_def PB_Nonblockingness_AdaptDB_def)
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
   apply(rename_tac dh n dc sUF x)(*strict*)
   apply(rule_tac
      x="dc"
      in exI)
   apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac dh n dc sUF x)(*strict*)
    apply(force)
   apply(rename_tac dh n dc sUF x)(*strict*)
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
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(rule_tac
      x="replace_unfixed_scheduler_DB G dh sUF n"
      in exI)
  apply(rule_tac
      x="dc"
      in exI)
  apply(case_tac "unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)")
   apply(rename_tac dh n dc sUF x)(*strict*)
   apply(force)
  apply(rename_tac dh n dc sUF x)(*strict*)
  apply(force)
  done

theorem Nonblockingness_linear_DB_implies_Nonblockingness_linear_restricted_DB: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_linear_DB G
  \<Longrightarrow> Nonblockingness_linear_restricted_DB G"
  apply(simp add: Nonblockingness_linear_restricted_DB_def Nonblockingness_linear_DB_def)
  apply(force)
  done

lemma map_unfixed_scheduler_DB_preserves_maximum_of_domain: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d'=map_unfixed_scheduler_DB G d C
  \<Longrightarrow> maximum_of_domain d' n"
  apply(simp add: map_unfixed_scheduler_DB_def maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma sched_modification_preserves_derivation_initial: "
  TSstructure G
  \<Longrightarrow> derivation_initial G dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)
  \<Longrightarrow> unfixed_scheduler_extendable G sUF
  \<Longrightarrow> sUF \<in> unfixed_schedulers G
  \<Longrightarrow> dh' = map_unfixed_scheduler_DB G dh (\<lambda>c.
              extend_unfixed_scheduler
              (the(unfixed_scheduler_right_quotient c (get_unfixed_scheduler_DB G dh n)))
              sUF
              )
  \<Longrightarrow> derivation_initial G dh'"
  apply(subgoal_tac "fixed_scheduler_extendable G (get_fixed_scheduler_DB G dh n)")
   prefer 2
   apply(rule_tac
      t="fixed_scheduler_extendable G (get_fixed_scheduler_DB G dh n)"
      and s="unfixed_scheduler_extendable G (get_unfixed_scheduler_DB G dh n)"
      in ssubst)
    apply(rule_tac
      n="n"
      in AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB)
        apply(force)
       apply(force)
      apply(simp add: maximum_of_domain_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "belongs G dh")
   prefer 2
   apply(rule derivation_initial_belongs)
    apply(force)
   apply(force)
  apply(simp add: derivation_initial_def)
  apply(clarsimp)
  apply(simp add: map_unfixed_scheduler_DB_def)
  apply(case_tac "dh 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(rule conjI)
   apply(rename_tac b)(*strict*)
   prefer 2
   apply(rule AX_set_unfixed_scheduler_DB_preserves_initial_configurations)
         apply(rename_tac b)(*strict*)
         apply(force)
        apply(rename_tac b)(*strict*)
        apply(force)
       apply(rename_tac b)(*strict*)
       apply(force)
      apply(rename_tac b)(*strict*)
      apply(force)
     apply(rename_tac b)(*strict*)
     apply(rule AX_extend_unfixed_scheduler_closed)
        apply(rename_tac b)(*strict*)
        apply(force)
       apply(rename_tac b)(*strict*)
       apply(rule_tac
      n="n"
      in AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB)
            apply(rename_tac b)(*strict*)
            apply(force)
           apply(rename_tac b)(*strict*)
           apply(simp add: derivation_initial_def)
          apply(rename_tac b)(*strict*)
          apply(simp add: maximum_of_domain_def)
         apply(rename_tac b)(*strict*)
         apply(force)
        apply(rename_tac b)(*strict*)
        apply(force)
       apply(rename_tac b)(*strict*)
       apply(force)
      apply(rename_tac b)(*strict*)
      apply(force)
     apply(rename_tac b)(*strict*)
     apply(force)
    apply(rename_tac b)(*strict*)
    apply(rule AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration)
     apply(rename_tac b)(*strict*)
     apply(force)
    apply(rename_tac b)(*strict*)
    apply(simp add: derivation_initial_def)
   apply(rename_tac b)(*strict*)
   apply (metis AX_extend_unfixed_scheduler_preserves_unfixed_scheduler_extendable)
  apply(rename_tac b)(*strict*)
  apply(simp (no_asm) add: derivation_def)
  apply(clarsimp)
  apply(rename_tac b i)(*strict*)
  apply(case_tac i)
   apply(rename_tac b i)(*strict*)
   apply(clarsimp)
  apply(rename_tac b i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac b nat)(*strict*)
  apply(case_tac "dh (Suc nat)")
   apply(rename_tac b nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac b nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh nat = Some (pair e1 c1) \<and> dh (Suc nat) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac b nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in step_detail_before_some_position)
     apply(rename_tac b nat a)(*strict*)
     apply(force)
    apply(rename_tac b nat a)(*strict*)
    apply(force)
   apply(rename_tac b nat a)(*strict*)
   apply(force)
  apply(rename_tac b nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac b nat e1 e2 c1 c2)(*strict*)
  apply(rule AX_sched_modification_preserves_steps)
           apply(rename_tac b nat e1 e2 c1 c2)(*strict*)
           apply(force)+
  done

end

end
