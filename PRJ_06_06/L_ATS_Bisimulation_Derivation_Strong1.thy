section {*L\_ATS\_Bisimulation\_Derivation\_Strong1*}
theory
  L_ATS_Bisimulation_Derivation_Strong1

imports
  PRJ_06_06__PRE

begin

(*
translation of
  is_forward_edge_deterministic_accessible
  marked language
  unmarked language
using
  bisimulation relation on derivations where steps are mimicked stongly.
*)

print_locale ATS_SchedUF_DB

locale ATS_Bisimulation_Derivation_Strong1 =
  Sys1 :
  ATS_SchedUF_DB
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "effects1 :: 'TSstructure1 \<Rightarrow> 'event1 set"
  "marking_condition1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> bool"
  "marked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> 'event1 set"
  "unmarked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> 'event1 set"
  "scheduler_fragments1 :: 'TSstructure1 \<Rightarrow> 'scheduler_fragment1 set"
  "empty_scheduler_fragment1 :: 'TSstructure1 \<Rightarrow> 'scheduler_fragment1"
  "join_scheduler_fragments1 :: 'scheduler_fragment1 \<Rightarrow> 'scheduler_fragment1 \<Rightarrow> 'scheduler_fragment1"
  "unfixed_schedulers1 :: 'TSstructure1 \<Rightarrow> 'unfixed_scheduler1 set"
  "empty_unfixed_scheduler1 :: 'TSstructure1 \<Rightarrow> 'unfixed_scheduler1"
  "unfixed_scheduler_right_quotient1 :: 'unfixed_scheduler1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'scheduler_fragment1 option"
  "extend_unfixed_scheduler1 :: 'scheduler_fragment1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'unfixed_scheduler1"
  "unfixed_scheduler_extendable1 :: 'TSstructure1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> bool"
  "set_unfixed_scheduler_DB1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'conf1"
  "get_unfixed_scheduler_DB1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler1"
  +
  Sys2 :
  ATS_SchedUF_DB
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "effects2 :: 'TSstructure2 \<Rightarrow> 'event2 set"
  "marking_condition2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> bool"
  "marked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> 'event2 set"
  "unmarked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> 'event2 set"
  "scheduler_fragments2 :: 'TSstructure2 \<Rightarrow> 'scheduler_fragment2 set"
  "empty_scheduler_fragment2 :: 'TSstructure2 \<Rightarrow> 'scheduler_fragment2"
  "join_scheduler_fragments2 :: 'scheduler_fragment2 \<Rightarrow> 'scheduler_fragment2 \<Rightarrow> 'scheduler_fragment2"
  "unfixed_schedulers2 :: 'TSstructure2 \<Rightarrow> 'unfixed_scheduler2 set"
  "empty_unfixed_scheduler2 :: 'TSstructure2 \<Rightarrow> 'unfixed_scheduler2"
  "unfixed_scheduler_right_quotient2 :: 'unfixed_scheduler2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'scheduler_fragment2 option"
  "extend_unfixed_scheduler2 :: 'scheduler_fragment2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'unfixed_scheduler2"
  "unfixed_scheduler_extendable2 :: 'TSstructure2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> bool"
  "set_unfixed_scheduler_DB2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'conf2"
  "get_unfixed_scheduler_DB2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler2"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 scheduler_fragments1 empty_scheduler_fragment1 join_scheduler_fragments1 unfixed_schedulers1 empty_unfixed_scheduler1 unfixed_scheduler_right_quotient1 extend_unfixed_scheduler1 unfixed_scheduler_extendable1 set_unfixed_scheduler_DB1 get_unfixed_scheduler_DB1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 scheduler_fragments2 empty_scheduler_fragment2 join_scheduler_fragments2 unfixed_schedulers2 empty_unfixed_scheduler2 unfixed_scheduler_right_quotient2 extend_unfixed_scheduler2 unfixed_scheduler_extendable2 set_unfixed_scheduler_DB2 get_unfixed_scheduler_DB2
    +

fixes TSstructure_rel :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"

fixes effect_rel :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"

fixes label_relation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2 \<Rightarrow> bool"

fixes derivation_bisimulation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> bool"

assumes AX_TSstructure_rel_on_TSstructure1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> TSstructure1 G1"

assumes AX_TSstructure_rel_on_TSstructure2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> TSstructure2 G2"

assumes AX_AX_initial_contained1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> \<exists>c2. derivation_bisimulation G1 G2 (der1 c1) (der1 c2)"

assumes AX_AX_initial_contained2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> c2 \<in> initial_configurations2 G2
  \<Longrightarrow> \<exists>c1. derivation_bisimulation G1 G2 (der1 c1) (der1 c2)"

assumes AX_on_derivation_initial1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> Sys1.derivation_initial G1 d1"

assumes AX_on_finite1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> \<exists>n. maximum_of_domain d1 n"

assumes AX_on_derivation_initial2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> Sys2.derivation_initial G2 d2"

assumes AX_on_finite2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> \<exists>n. maximum_of_domain d2 n"

assumes AX_equal_length: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> n1=n2"

assumes AX_simulate12: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> step_relation1 G1 (the(get_configuration(d1 n))) e1 c1'
  \<Longrightarrow> \<exists>e2 c2'.
  step_relation2 G2 (the(get_configuration(d2 n))) e2 c2'
  \<and> label_relation G1 G2 e1 e2
  \<and> (
  let d1' = (derivation_append d1 (der2 (the(get_configuration(d1 n))) e1 c1') n) in (
  let d2' = (derivation_append d2 (der2 (the(get_configuration(d2 n))) e2 c2') n) in derivation_bisimulation G1 G2 d1' d2'))"

assumes AX_simulate21: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> step_relation2 G2 (the(get_configuration(d2 n))) e2 c2'
  \<Longrightarrow> \<exists>e1 c1'.
  step_relation1 G1 (the(get_configuration(d1 n))) e1 c1'
  \<and> label_relation G1 G2 e1 e2
  \<and> (
  let d1' = (derivation_append d1 (der2 (the(get_configuration(d1 n))) e1 c1') n) in (
  let d2' = (derivation_append d2 (der2 (the(get_configuration(d2 n))) e2 c2') n) in derivation_bisimulation G1 G2 d1' d2'))"

assumes AX_bisimulation_compatible_with_crop1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh' n
  \<Longrightarrow> derivation_append_fit dh' dc n
  \<Longrightarrow> derivation_bisimulation G1 G2 (derivation_append dh' dc n) dc'
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> dh x = dc' x"

assumes AX_bisimulation_compatible_with_crop2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> derivation_append_fit dh dc' n
  \<Longrightarrow> derivation_bisimulation G1 G2 dc (derivation_append dh dc' n)
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> dh' x = dc x"

assumes AX_bisimulation_compatible_with_unfixed_scheduler_extendable1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 d1 m)
  \<Longrightarrow> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 d2 m)"

assumes AX_bisimulation_compatible_with_unfixed_scheduler_extendable2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 d2 m)
  \<Longrightarrow> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 d1 m)"

assumes AX_accept_id1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> marking_condition1 G1 d1
  \<Longrightarrow> marking_condition2 G2 d2"

assumes AX_accept_id2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> marking_condition2 G2 d2
  \<Longrightarrow> marking_condition1 G1 d1"

assumes AX_unAX_marked_effect_id1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o1 \<in> unmarked_effect1 G1 d1
  \<Longrightarrow> \<exists>o2. effect_rel G1 G2 o1 o2
  \<and> o2 \<in> unmarked_effect2 G2 d2"

assumes AX_unAX_marked_effect_id2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o2 \<in> unmarked_effect2 G2 d2
  \<Longrightarrow> \<exists>o1. effect_rel G1 G2 o1 o2
  \<and> o1 \<in> unmarked_effect1 G1 d1"

assumes AX_marked_effect_id1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o1 \<in> marked_effect1 G1 d1
  \<Longrightarrow> marking_condition1 G1 d1
  \<Longrightarrow> \<exists>o2. effect_rel G1 G2 o1 o2
  \<and> o2 \<in> marked_effect2 G2 d2"

assumes AX_marked_effect_id2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o2 \<in> marked_effect2 G2 d2
  \<Longrightarrow> marking_condition2 G2 d2
  \<Longrightarrow> \<exists>o1. effect_rel G1 G2 o1 o2
  \<and> o1 \<in> marked_effect1 G1 d1"

assumes AX_step_labels_unique1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> e21 \<in> step_labels2 G2
  \<Longrightarrow> e22 \<in> step_labels2 G2
  \<Longrightarrow> label_relation G1 G2 e1 e21
  \<Longrightarrow> label_relation G1 G2 e1 e22
  \<Longrightarrow> e21 = e22"

assumes AX_step_labels_unique2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e11 \<in> step_labels1 G1
  \<Longrightarrow> e12 \<in> step_labels1 G1
  \<Longrightarrow> e2 \<in> step_labels2 G2
  \<Longrightarrow> label_relation G1 G2 e11 e2
  \<Longrightarrow> label_relation G1 G2 e12 e2
  \<Longrightarrow> e11 = e12"

assumes AX_step_labels_exists1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> \<exists>e2 \<in> step_labels2 G2. label_relation G1 G2 e1 e2"

assumes AX_step_labels_exists2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e2 \<in> step_labels2 G2
  \<Longrightarrow> \<exists>e1 \<in> step_labels1 G1. label_relation G1 G2 e1 e2"

context ATS begin

lemma derivation_Some_before_maximum_of_domain: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> d m \<noteq> None"
  apply(subgoal_tac "derivation_ALT G d")
   apply(simp add: derivation_ALT_def maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac y c)(*strict*)
   apply(erule_tac x="n" in allE)
   apply(erule_tac x="m" in allE)+
   apply(force)
  apply(metis derivation_ALT_vs_derivation)
  done

lemma derivation_Some_before_maximum_of_domain_prime: "
  derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> d m \<noteq> None"
  apply(subgoal_tac "derivation_ALT G d")
   apply(simp add: derivation_ALT_def maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac y c)(*strict*)
   apply(erule_tac x="n" in allE)
   apply(erule_tac x="m" in allE)+
   apply(force)
  apply(metis derivation_ALT_vs_derivation)
  done

end

context ATS_Bisimulation_Derivation_Strong1 begin

lemma simulation_lift1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys1.derivation_initial G1 d1
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> \<exists>d2. derivation_bisimulation G1 G2 d1 d2"
  apply(induct n arbitrary: d1)
   apply(rename_tac d1)(*strict*)
   apply(rule_tac
      t="d1"
      and s="der1(the(get_configuration(d1 0)))"
      in ssubst)
    apply(rename_tac d1)(*strict*)
    apply(rule ext)
    apply(rename_tac d1 x)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(subgoal_tac "\<exists>c. d1 0 = Some (pair None c)")
     apply(rename_tac d1 x)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1 x c)(*strict*)
     apply(rule Sys1.none_position_after_max_dom)
       apply(rename_tac d1 x c)(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
       apply(force)
      apply(rename_tac d1 x c)(*strict*)
      apply(force)
     apply(rename_tac d1 x c)(*strict*)
     apply(force)
    apply(rename_tac d1 x)(*strict*)
    apply(rule Sys1.some_position_has_details_at_0)
    apply(simp add: Sys1.derivation_initial_def)
    apply(force)
   apply(rename_tac d1)(*strict*)
   apply(subgoal_tac "\<exists>c2. derivation_bisimulation G1 G2 (der1 (the (get_configuration (d1 0)))) (der1 c2)")
    apply(rename_tac d1)(*strict*)
    apply(force)
   apply(rename_tac d1)(*strict*)
   apply(rule AX_AX_initial_contained1)
    apply(rename_tac d1)(*strict*)
    apply(force)
   apply(rename_tac d1)(*strict*)
   apply(simp add: Sys1.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d1 0")
    apply(rename_tac d1)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac d1 a option b)(*strict*)
   apply(force)
  apply(rename_tac n d1)(*strict*)
  apply(erule_tac
      x="derivation_take d1 n"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac n d1)(*strict*)
   apply(rule Sys1.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac n d1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d1)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(rule_tac n="Suc n" in Sys1.derivationNoFromNone2_prime)
     apply(rename_tac n d1)(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
     apply(force)
    apply(rename_tac n d1)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n d1)(*strict*)
   apply(force)
  apply(rename_tac n d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d1 x)(*strict*)
  apply(rename_tac d2)
  apply(rename_tac n d1 d2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 n = Some (pair e1 c1) \<and> d1 (Suc n) = Some (pair (Some e2) c2) \<and> step_relation1 G1 c1 e2 c2")
   apply(rename_tac n d1 d2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in Sys1.step_detail_before_some_position)
     apply(rename_tac n d1 d2)(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
    apply(rename_tac n d1 d2)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n d1 d2)(*strict*)
   apply(force)
  apply(rename_tac n d1 d2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d1 d2 e1 e2 c1 c2)(*strict*)
  apply(rename_tac e0 e1 c0 c1')
  apply(rename_tac n d1 d2 e0 e1 c0 c1')(*strict*)
  apply(subgoal_tac "\<exists>n2. maximum_of_domain d2 n2")
   apply(rename_tac n d1 d2 e0 e1 c0 c1')(*strict*)
   prefer 2
   apply (rule AX_on_finite2)
   apply(force)
  apply(rename_tac n d1 d2 e0 e1 c0 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
  apply(subgoal_tac "n=n2")
   apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
   prefer 2
   apply(rule AX_equal_length)
     apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
     apply(force)
    apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(rule Sys1.derivation_Some_before_maximum_of_domain)
      apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
      apply(force)
     apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
     apply(force)
    apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
    apply(force)
   apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
   apply(force)
  apply(rename_tac n d1 d2 e0 e1 c0 c1' n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 e0 e1 c0 c1' n2)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
  apply(subgoal_tac " \<exists>e2 c2'. step_relation2 G2 (the(get_configuration(d2 n))) e2 c2' \<and> label_relation G1 G2 e1 e2 \<and> (let d1' = (derivation_append (derivation_take d1 n) (der2 (the(get_configuration((derivation_take d1 n) n))) e1 c1') n) in (let d2' = (derivation_append d2 (der2 (the(get_configuration(d2 n))) e2 c2') n) in derivation_bisimulation G1 G2 d1' d2'))")
   apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
   prefer 2
   apply(rule AX_simulate12)
      apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(rule_tac n="Suc n" in Sys1.derivationNoFromNone2_prime)
       apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
       apply(force)
      apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac d1 d2 e0 e1 c0 c1' n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2')(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take d1 n) (der2 (the (get_configuration (derivation_take d1 n n))) e1 c1') n) = d1")
   apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2')(*strict*)
   prefer 2
   apply(rule ext)
   apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' x)(*strict*)
   apply(simp add: derivation_append_def derivation_take_def der2_def get_configuration_def)
   apply(case_tac "x-n")
    apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' x)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' x nat)(*strict*)
   apply(subgoal_tac "x=Suc nat+n")
    apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' x nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' nat)(*strict*)
   apply(rule sym)
   apply(rule Sys1.none_position_after_max_dom)
     apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' nat)(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
     apply(force)
    apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' nat)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2' nat)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e0 e1 c0 c1' n e2 c2')(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma simulation_lift2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys2.derivation_initial G2 d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> \<exists>d1. derivation_bisimulation G1 G2 d1 d2"
  apply(induct n arbitrary: d2)
   apply(rename_tac d2)(*strict*)
   apply(rule_tac
      t="d2"
      and s="der1(the(get_configuration(d2 0)))"
      in ssubst)
    apply(rename_tac d2)(*strict*)
    apply(rule ext)
    apply(rename_tac d2 x)(*strict*)
    apply(simp add: der1_def get_configuration_def)
    apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
     apply(rename_tac d2 x)(*strict*)
     apply(clarsimp)
     apply(rename_tac d2 x c)(*strict*)
     apply(rule Sys2.none_position_after_max_dom)
       apply(rename_tac d2 x c)(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
       apply(force)
      apply(rename_tac d2 x c)(*strict*)
      apply(force)
     apply(rename_tac d2 x c)(*strict*)
     apply(force)
    apply(rename_tac d2 x)(*strict*)
    apply(rule Sys2.some_position_has_details_at_0)
    apply(simp add: Sys2.derivation_initial_def)
    apply(force)
   apply(rename_tac d2)(*strict*)
   apply(subgoal_tac "\<exists>c1. derivation_bisimulation G1 G2 (der1 c1) (der1 (the (get_configuration (d2 0))))")
    apply(rename_tac d2)(*strict*)
    apply(force)
   apply(rename_tac d2)(*strict*)
   apply(rule AX_AX_initial_contained2)
    apply(rename_tac d2)(*strict*)
    apply(force)
   apply(rename_tac d2)(*strict*)
   apply(simp add: Sys2.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d2 0")
    apply(rename_tac d2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d2 a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac d2 a option b)(*strict*)
   apply(force)
  apply(rename_tac n d2)(*strict*)
  apply(erule_tac
      x="derivation_take d2 n"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac n d2)(*strict*)
   apply(rule Sys2.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac n d2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d2)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(rule_tac n="Suc n" in Sys2.derivationNoFromNone2_prime)
     apply(rename_tac n d2)(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
     apply(force)
    apply(rename_tac n d2)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n d2)(*strict*)
   apply(force)
  apply(rename_tac n d2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d2 d1)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 n = Some (pair e1 c1) \<and> d2 (Suc n) = Some (pair (Some e2) c2) \<and> step_relation2 G2 c1 e2 c2")
   apply(rename_tac n d2 d1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in Sys2.step_detail_before_some_position)
     apply(rename_tac n d2 d1)(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
    apply(rename_tac n d2 d1)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n d2 d1)(*strict*)
   apply(force)
  apply(rename_tac n d2 d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d2 d1 e1 e2 c1 c2)(*strict*)
  apply(rename_tac e0 e2 c0 c2')
  apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
  apply(subgoal_tac "\<exists>n1. maximum_of_domain d1 n1")
   apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
   prefer 2
   apply (rule AX_on_finite1)
   apply(force)
  apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d2 d1 e0 e2 c0 c2' n1)(*strict*)
  apply(subgoal_tac "n1=n")
   apply(rename_tac n d2 d1 e0 e2 c0 c2' n1)(*strict*)
   prefer 2
   apply(rule AX_equal_length)
     apply(rename_tac n d2 d1 e0 e2 c0 c2' n1)(*strict*)
     apply(force)
    apply(rename_tac n d2 d1 e0 e2 c0 c2' n1)(*strict*)
    apply(force)
   apply(rename_tac n d2 d1 e0 e2 c0 c2' n1)(*strict*)
   apply (metis Nat.add_0_right Sys2.der1_is_derivation der1_maximum_of_domain Sys2.derivationNoFromNone_prime maximum_of_domain_derivation_take Sys2.no_some_beyond_maximum_of_domain less_add_Suc2)
  apply(rename_tac n d2 d1 e0 e2 c0 c2' n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
  apply(subgoal_tac " \<exists>e1 c1'. step_relation1 G1 (the(get_configuration(d1 n))) e1 c1' \<and> label_relation G1 G2 e1 e2 \<and> (let d1' = (derivation_append d1 (der2 (the(get_configuration(d1 n))) e1 c1') n) in (let d2' = (derivation_append (derivation_take d2 n) (der2 (the(get_configuration((derivation_take d2 n) n))) e2 c2') n) in derivation_bisimulation G1 G2 d1' d2'))")
   apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
   prefer 2
   apply(rule AX_simulate21)
      apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
      apply(force)
     apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
     apply(force)
    apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(rule_tac n="Suc n" in Sys2.derivationNoFromNone2_prime)
      apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
      apply(force)
     apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
    apply(force)
   apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac n d2 d1 e0 e2 c0 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1')(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take d2 n) (der2 (the (get_configuration (derivation_take d2 n n))) e2 c2') n) = d2")
   apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1')(*strict*)
   prefer 2
   apply(rule ext)
   apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' x)(*strict*)
   apply(simp add: derivation_append_def derivation_take_def der2_def get_configuration_def)
   apply(case_tac "x-n")
    apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' x)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' x nat)(*strict*)
   apply(subgoal_tac "x=Suc nat+n")
    apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' x nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' nat)(*strict*)
   apply(rule sym)
   apply(rule Sys2.none_position_after_max_dom)
     apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' nat)(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
     apply(force)
    apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' nat)(*strict*)
    apply(force)
   apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1' nat)(*strict*)
   apply(force)
  apply(rename_tac n d2 d1 e0 e2 c0 c2' e1 c1')(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma Nonblockingness_translation1_hlp1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> ATS.derivation_initial initial_configurations2 step_relation2 G2 dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh' n
  \<Longrightarrow> ATS.derivation step_relation1 G1 dc
  \<Longrightarrow> ATS.belongs configurations1 step_labels1 G1 dc
  \<Longrightarrow> maximum_of_domain dc n'
  \<Longrightarrow> derivation_append_fit dh' dc n
  \<Longrightarrow> marking_condition1 G1 (derivation_append dh' dc n)
  \<Longrightarrow> \<not> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh' n)
  \<Longrightarrow> \<not> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh n)
  \<Longrightarrow> \<exists>dc. ATS.derivation step_relation2 G2 dc \<and>
               ATS.belongs configurations2 step_labels2 G2 dc \<and>
               Ex (maximum_of_domain dc) \<and>
               derivation_append_fit dh dc n \<and>
               marking_condition2 G2 (derivation_append dh dc n)"
  apply(subgoal_tac "\<exists>dc'. derivation_bisimulation G1 G2 (derivation_append dh' dc n) dc'")
   prefer 2
   apply(rule_tac
      ?n.0="n+n'"
      in simulation_lift1)
     apply(force)
    prefer 2
    apply(rule concat_has_max_dom)
     apply(simp add: Sys1.map_unfixed_scheduler_DB_def maximum_of_domain_def)
    apply(clarsimp)
   apply(rule Sys1.derivation_append_preserves_derivation_initial_prime)
       apply(rule AX_TSstructure_rel_on_TSstructure1)
       apply(force)
      apply (metis AX_on_derivation_initial1)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac dc')(*strict*)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' n'")
   apply(rename_tac dc')(*strict*)
   prefer 2
   apply (metis AX_on_finite2)
  apply(rename_tac dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dc' n'a)(*strict*)
  apply(subgoal_tac "n'a = n+n'")
   apply(rename_tac dc' n'a)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      ?d1.0="derivation_append dh' dc n"
      in AX_equal_length)
     apply(rename_tac dc' n'a)(*strict*)
     apply(force)
    apply(rename_tac dc' n'a)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dc' n'a)(*strict*)
     apply(force)
    apply(rename_tac dc' n'a)(*strict*)
    apply(force)
   apply(rename_tac dc' n'a)(*strict*)
   apply(force)
  apply(rename_tac dc' n'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dc')(*strict*)
  apply(rule_tac
      x="derivation_drop dc' n"
      in exI)
  apply(rule conjI)
   apply(rename_tac dc')(*strict*)
   apply(rule Sys2.derivation_drop_preserves_derivation)
    apply(rename_tac dc')(*strict*)
    apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
     apply(rename_tac dc')(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
    apply(rename_tac dc')(*strict*)
    apply(rule AX_on_derivation_initial2)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(rule conjI)
   apply(rename_tac dc')(*strict*)
   apply(rule Sys2.derivation_drop_preserves_belongs)
     apply(rename_tac dc')(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dc')(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dc')(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(rule Sys2.derivation_initial_belongs)
     apply(rename_tac dc')(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure2)
    apply(rename_tac dc')(*strict*)
    apply(rule AX_on_derivation_initial2)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(rule_tac
      M="G2"
      in Sys2.some_position_has_details_before_max_dom)
     apply(rename_tac dc')(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dc')(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dc')(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(rule conjI)
   apply(rename_tac dc')(*strict*)
   apply(rule_tac
      x="n'"
      in exI)
   apply(rule_tac
      t="n'"
      and s="(n+n')-n"
      in ssubst)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(rule Sys2.derivation_drop_makes_maximum_of_domain)
     apply(rename_tac dc')(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dc')(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
      apply(force)
     apply(rename_tac dc')(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(subgoal_tac "(derivation_append dh (derivation_drop dc' n) n) = dc'")
   apply(rename_tac dc')(*strict*)
   apply(rule conjI)
    apply(rename_tac dc')(*strict*)
    prefer 2
    apply(rule AX_accept_id1)
     apply(rename_tac dc')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(subgoal_tac "derivation_append dh (derivation_drop dc' n) n n = dc' n")
    apply(rename_tac dc')(*strict*)
    apply(thin_tac "derivation_append dh (derivation_drop dc' n) n = dc'")
    apply(simp add: derivation_append_def)
    apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
     apply(rename_tac dc')(*strict*)
     apply(clarsimp)
     apply(rename_tac dc' e c)(*strict*)
     apply(simp add: derivation_drop_def)
    apply(rename_tac dc')(*strict*)
    apply(rule_tac
      M="G2"
      in Sys2.some_position_has_details_before_max_dom)
      apply(rename_tac dc')(*strict*)
      apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
       apply(rename_tac dc')(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
      apply(rename_tac dc')(*strict*)
      apply(rule AX_on_derivation_initial2)
      apply(force)
     apply(rename_tac dc')(*strict*)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(rule ext)
  apply(rename_tac dc' x)(*strict*)
  apply(case_tac "x>n")
   apply(rename_tac dc' x)(*strict*)
   apply(simp add: derivation_append_def derivation_drop_def)
  apply(rename_tac dc' x)(*strict*)
  apply(thin_tac "marking_condition1 G1 (derivation_append dh' dc n)")
  apply(simp add: derivation_append_def)
  apply(subgoal_tac "n\<ge>x")
   apply(rename_tac dc' x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dc' x)(*strict*)
  apply(clarsimp)
  apply (rule AX_bisimulation_compatible_with_crop1)
       apply(rename_tac dc' x)(*strict*)
       apply(force)
      apply(rename_tac dc' x)(*strict*)
      apply(force)
     apply(rename_tac dc' x)(*strict*)
     apply(force)
    apply(rename_tac dc' x)(*strict*)
    apply(force)
   apply(rename_tac dc' x)(*strict*)
   apply(fold derivation_append_def)
   apply(force)
  apply(rename_tac dc' x)(*strict*)
  apply(force)
  done

lemma Nonblockingness_translation2_hlp1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> ATS.derivation_initial initial_configurations1 step_relation1 G1 dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> derivation_bisimulation G1 G2 dh dh'
  \<Longrightarrow> maximum_of_domain dh' n
  \<Longrightarrow> ATS.derivation step_relation2 G2 dc
  \<Longrightarrow> ATS.belongs configurations2 step_labels2 G2 dc
  \<Longrightarrow> maximum_of_domain dc n'
  \<Longrightarrow> derivation_append_fit dh' dc n
  \<Longrightarrow> marking_condition2 G2 (derivation_append dh' dc n)
  \<Longrightarrow> \<not> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh' n)
  \<Longrightarrow> \<not> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh n)
  \<Longrightarrow> \<exists>dc. ATS.derivation step_relation1 G1 dc \<and>
               ATS.belongs configurations1 step_labels1 G1 dc \<and>
               Ex (maximum_of_domain dc) \<and>
               derivation_append_fit dh dc n \<and>
               marking_condition1 G1 (derivation_append dh dc n)"
  apply(subgoal_tac "\<exists>dc'. derivation_bisimulation G1 G2 dc' (derivation_append dh' dc n)")
   prefer 2
   apply(rule_tac
      ?n.0="n+n'"
      in simulation_lift2)
     apply(force)
    prefer 2
    apply(rule concat_has_max_dom)
     apply(simp add: Sys2.map_unfixed_scheduler_DB_def maximum_of_domain_def)
    apply(clarsimp)
   apply(rule Sys2.derivation_append_preserves_derivation_initial_prime)
       apply(rule AX_TSstructure_rel_on_TSstructure2)
       apply(force)
      apply (metis AX_on_derivation_initial2)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac dc')(*strict*)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' n'")
   apply(rename_tac dc')(*strict*)
   prefer 2
   apply (metis AX_on_finite1)
  apply(rename_tac dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dc' n'a)(*strict*)
  apply(subgoal_tac "n'a = n+n'")
   apply(rename_tac dc' n'a)(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="derivation_append dh' dc n"
      in AX_equal_length)
     apply(rename_tac dc' n'a)(*strict*)
     apply(force)
    apply(rename_tac dc' n'a)(*strict*)
    apply(force)
   apply(rename_tac dc' n'a)(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac dc' n'a)(*strict*)
    apply(force)
   apply(rename_tac dc' n'a)(*strict*)
   apply(force)
  apply(rename_tac dc' n'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dc')(*strict*)
  apply(rule_tac
      x="derivation_drop dc' n"
      in exI)
  apply(rule conjI)
   apply(rename_tac dc')(*strict*)
   apply(rule Sys1.derivation_drop_preserves_derivation)
    apply(rename_tac dc')(*strict*)
    apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
     apply(rename_tac dc')(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
    apply(rename_tac dc')(*strict*)
    apply(rule AX_on_derivation_initial1)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(rule conjI)
   apply(rename_tac dc')(*strict*)
   apply(rule Sys1.derivation_drop_preserves_belongs)
     apply(rename_tac dc')(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dc')(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dc')(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(rule Sys1.derivation_initial_belongs)
     apply(rename_tac dc')(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure1)
    apply(rename_tac dc')(*strict*)
    apply(rule AX_on_derivation_initial1)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(rule_tac
      M="G1"
      in Sys1.some_position_has_details_before_max_dom)
     apply(rename_tac dc')(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dc')(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dc')(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(rule conjI)
   apply(rename_tac dc')(*strict*)
   apply(rule_tac
      x="n'"
      in exI)
   apply(rule_tac
      t="n'"
      and s="(n+n')-n"
      in ssubst)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(rule Sys1.derivation_drop_makes_maximum_of_domain)
     apply(rename_tac dc')(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dc')(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
      apply(force)
     apply(rename_tac dc')(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(subgoal_tac "(derivation_append dh (derivation_drop dc' n) n) = dc'")
   apply(rename_tac dc')(*strict*)
   apply(rule conjI)
    apply(rename_tac dc')(*strict*)
    prefer 2
    apply(rule AX_accept_id2)
     apply(rename_tac dc')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(subgoal_tac "derivation_append dh (derivation_drop dc' n) n n = dc' n")
    apply(rename_tac dc')(*strict*)
    apply(thin_tac "derivation_append dh (derivation_drop dc' n) n = dc'")
    apply(simp add: derivation_append_def)
    apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
     apply(rename_tac dc')(*strict*)
     apply(clarsimp)
     apply(rename_tac dc' e c)(*strict*)
     apply(simp add: derivation_drop_def)
    apply(rename_tac dc')(*strict*)
    apply(rule_tac
      M="G1"
      in Sys1.some_position_has_details_before_max_dom)
      apply(rename_tac dc')(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
       apply(rename_tac dc')(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
      apply(rename_tac dc')(*strict*)
      apply(rule AX_on_derivation_initial1)
      apply(force)
     apply(rename_tac dc')(*strict*)
     apply(force)
    apply(rename_tac dc')(*strict*)
    apply(force)
   apply(rename_tac dc')(*strict*)
   apply(force)
  apply(rename_tac dc')(*strict*)
  apply(rule ext)
  apply(rename_tac dc' x)(*strict*)
  apply(case_tac "x>n")
   apply(rename_tac dc' x)(*strict*)
   apply(simp add: derivation_append_def derivation_drop_def)
  apply(rename_tac dc' x)(*strict*)
  apply(thin_tac "marking_condition2 G2 (derivation_append dh' dc n)")
  apply(simp add: derivation_append_def)
  apply(subgoal_tac "n\<ge>x")
   apply(rename_tac dc' x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dc' x)(*strict*)
  apply(clarsimp)
  apply(fold derivation_append_def)
  apply (metis AX_bisimulation_compatible_with_crop2)
  done

theorem ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> o1 \<in> Sys1.finite_unmarked_language G1
  \<Longrightarrow> \<exists>o2. effect_rel G1 G2 o1 o2
  \<and> o2 \<in> Sys2.unmarked_language G2"
  apply(simp add: Sys1.finite_unmarked_language_def Sys2.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d x)(*strict*)
  apply(subgoal_tac "\<exists>d'. derivation_bisimulation G1 G2 d d'")
   apply(rename_tac d x)(*strict*)
   prefer 2
   apply(rule simulation_lift1)
     apply(rename_tac d x)(*strict*)
     apply(force)
    apply(rename_tac d x)(*strict*)
    apply(force)
   apply(rename_tac d x)(*strict*)
   apply(force)
  apply(rename_tac d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d')(*strict*)
  apply(subgoal_tac "\<exists>o2. effect_rel G1 G2 o1 o2 \<and> o2 \<in> unmarked_effect2 G2 d'")
   apply(rename_tac d x d')(*strict*)
   prefer 2
   apply(rule AX_unAX_marked_effect_id1)
    apply(rename_tac d x d')(*strict*)
    apply(force)
   apply(rename_tac d x d')(*strict*)
   apply(force)
  apply(rename_tac d x d')(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d' o2)(*strict*)
  apply(rule_tac
      x="o2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac d x d' o2)(*strict*)
   apply (metis AX_on_derivation_initial2)
  apply(rename_tac d x d' o2)(*strict*)
  apply (metis Sys2.derivation_initial_is_derivation)
  done

theorem ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> o2 \<in> Sys2.finite_unmarked_language G2
  \<Longrightarrow> \<exists>o1. effect_rel G1 G2 o1 o2
  \<and> o1 \<in> Sys1.unmarked_language G1"
  apply(simp add: Sys2.finite_unmarked_language_def Sys1.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d x)(*strict*)
  apply(subgoal_tac "\<exists>d'. derivation_bisimulation G1 G2 d' d")
   apply(rename_tac d x)(*strict*)
   prefer 2
   apply(rule simulation_lift2)
     apply(rename_tac d x)(*strict*)
     apply(force)
    apply(rename_tac d x)(*strict*)
    apply(force)
   apply(rename_tac d x)(*strict*)
   apply(force)
  apply(rename_tac d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d')(*strict*)
  apply(subgoal_tac "\<exists>o1. effect_rel G1 G2 o1 o2 \<and> o1 \<in> unmarked_effect1 G1 d'")
   apply(rename_tac d x d')(*strict*)
   prefer 2
   apply(rule AX_unAX_marked_effect_id2)
    apply(rename_tac d x d')(*strict*)
    apply(force)
   apply(rename_tac d x d')(*strict*)
   apply(force)
  apply(rename_tac d x d')(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d' o1)(*strict*)
  apply(rule_tac
      x="o1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac d x d' o1)(*strict*)
   apply (metis AX_on_derivation_initial1)
  apply(rename_tac d x d' o1)(*strict*)
  apply (metis Sys1.derivation_initial_is_derivation)
  done

theorem ATS_Bisimulation_Derivation_Strong1_marked_language_translation1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> o1 \<in> Sys1.finite_marked_language G1
  \<Longrightarrow> \<exists>o2. effect_rel G1 G2 o1 o2
  \<and> o2 \<in> Sys2.marked_language G2"
  apply(simp add: Sys1.finite_marked_language_def Sys2.marked_language_def)
  apply(clarsimp)
  apply(rename_tac d x)(*strict*)
  apply(subgoal_tac "\<exists>d'. derivation_bisimulation G1 G2 d d'")
   apply(rename_tac d x)(*strict*)
   prefer 2
   apply(rule simulation_lift1)
     apply(rename_tac d x)(*strict*)
     apply(force)
    apply(rename_tac d x)(*strict*)
    apply(force)
   apply(rename_tac d x)(*strict*)
   apply(force)
  apply(rename_tac d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d')(*strict*)
  apply(subgoal_tac "\<exists>o2. effect_rel G1 G2 o1 o2 \<and> o2 \<in> marked_effect2 G2 d'")
   apply(rename_tac d x d')(*strict*)
   prefer 2
   apply(rule AX_marked_effect_id1)
     apply(rename_tac d x d')(*strict*)
     apply(force)
    apply(rename_tac d x d')(*strict*)
    apply(force)
   apply(rename_tac d x d')(*strict*)
   apply(force)
  apply(rename_tac d x d')(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d' o2)(*strict*)
  apply(rule_tac
      x="o2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac d x d' o2)(*strict*)
   apply (metis AX_on_derivation_initial2)
  apply(rename_tac d x d' o2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d x d' o2)(*strict*)
   apply (metis Sys2.derivation_initial_is_derivation)
  apply(rename_tac d x d' o2)(*strict*)
  apply (metis AX_accept_id1)
  done

theorem ATS_Bisimulation_Derivation_Strong1_marked_language_translation2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> o2 \<in> Sys2.finite_marked_language G2
  \<Longrightarrow> \<exists>o1. effect_rel G1 G2 o1 o2
  \<and> o1 \<in> Sys1.marked_language G1"
  apply(simp add: Sys2.finite_marked_language_def Sys1.marked_language_def)
  apply(clarsimp)
  apply(rename_tac d x)(*strict*)
  apply(subgoal_tac "\<exists>d'. derivation_bisimulation G1 G2 d' d")
   apply(rename_tac d x)(*strict*)
   prefer 2
   apply(rule simulation_lift2)
     apply(rename_tac d x)(*strict*)
     apply(force)
    apply(rename_tac d x)(*strict*)
    apply(force)
   apply(rename_tac d x)(*strict*)
   apply(force)
  apply(rename_tac d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d')(*strict*)
  apply(subgoal_tac "\<exists>o1. effect_rel G1 G2 o1 o2 \<and> o1 \<in> marked_effect1 G1 d'")
   apply(rename_tac d x d')(*strict*)
   prefer 2
   apply(rule AX_marked_effect_id2)
     apply(rename_tac d x d')(*strict*)
     apply(force)
    apply(rename_tac d x d')(*strict*)
    apply(force)
   apply(rename_tac d x d')(*strict*)
   apply(force)
  apply(rename_tac d x d')(*strict*)
  apply(clarsimp)
  apply(rename_tac d x d' o1)(*strict*)
  apply(rule_tac
      x="o1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac d x d' o1)(*strict*)
   apply (metis AX_on_derivation_initial1)
  apply(rename_tac d x d' o1)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d x d' o1)(*strict*)
   apply (metis Sys1.derivation_initial_is_derivation)
  apply(rename_tac d x d' o1)(*strict*)
  apply (metis AX_accept_id2)
  done

lemma preserve_FEdetermR1_hlp: "
  TSstructure_rel G1 G2
  \<Longrightarrow> step_relation2 G2 c e2 c2
  \<Longrightarrow> Sys2.derivation_initial G2 d2
  \<Longrightarrow> d2 i = Some (pair e c)
  \<Longrightarrow> derivation_bisimulation G1 G2 d1 (derivation_take d2 i)
  \<Longrightarrow> maximum_of_domain d1 i
  \<Longrightarrow> Sys1.derivation_initial G1 d1
  \<Longrightarrow> d1 i = Some (pair ea ca)
  \<Longrightarrow> e2' \<in> step_labels1 G1
  \<Longrightarrow> label_relation G1 G2 e2' e2
  \<Longrightarrow> \<exists>c2. step_relation1 G1 ca e2' c2"
  apply(subgoal_tac "\<exists>e1 c1'. step_relation1 G1 (the(get_configuration(d1 SSn))) e1 c1' \<and> label_relation G1 G2 e1 e2 \<and> (let d1' = (derivation_append d1 (der2 (the(get_configuration(d1 SSn))) e1 c1') SSn) in (let d2' = (derivation_append SSd2 (der2 (the(get_configuration(SSd2 SSn))) e2 SSc2') SSn) in derivation_bisimulation G1 G2 d1' d2'))" for SSd2 SSc2' SSn)
   prefer 2
   apply(rule_tac
      ?d2.0="(derivation_take d2 i)"
      in AX_simulate21)
      apply(force)
     apply(force)
    apply (metis Sys2.derivation_take_id_prime Sys2.derivation_initial_is_derivation maximum_of_domain_derivation_take AX_equal_length AX_on_finite2)
   apply(rule_tac
      t="(the (get_configuration (derivation_take d2 i i)))"
      and s="c"
      in ssubst)
    apply(simp add: get_configuration_def derivation_take_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e1 c1')(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      x="c1'"
      in exI)
  apply(subgoal_tac "e2'=e1")
   apply(rename_tac e1 c1')(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 c1')(*strict*)
  apply (metis Sys1.belongs_configurations Sys1.derivation_initial_belongs Sys1.AX_step_relation_preserves_belongs Sys2.belongs_configurations Sys2.derivation_initial_belongs Sys2.AX_step_relation_preserves_belongsE AX_TSstructure_rel_on_TSstructure1 AX_TSstructure_rel_on_TSstructure2 AX_step_labels_unique2)
  done

lemma preserve_FEdetermR1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys1.is_forward_edge_deterministic_accessible G1
  \<Longrightarrow> Sys2.is_forward_edge_deterministic_accessible G2"
  apply(simp add: Sys1.is_forward_edge_deterministic_accessible_def Sys2.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: Sys1.get_accessible_configurations_def Sys2.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
  apply(rename_tac d2 i e)
  apply(rename_tac c c1 c2 e1 e2 d2 i e)(*strict*)
  apply(subgoal_tac "\<exists>d1. derivation_bisimulation G1 G2 d1 (derivation_take d2 i)")
   apply(rename_tac c c1 c2 e1 e2 d2 i e)(*strict*)
   prefer 2
   apply(rule_tac
      n="i"
      in simulation_lift2)
     apply(rename_tac c c1 c2 e1 e2 d2 i e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d2 i e)(*strict*)
    apply (metis Sys2.derivation_take_preserves_derivation_initial)
   apply(rename_tac c c1 c2 e1 e2 d2 i e)(*strict*)
   apply (metis Sys2.der1_is_derivation der1_maximum_of_domain Sys2.derivation_take_id_prime_prime Sys2.derivationNoFromNone_prime Sys2.maximum_of_domainUnique maximum_of_domain_def maximum_of_domain_derivation_take Zero_not_Suc le0)
  apply(rename_tac c c1 c2 e1 e2 d2 i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
  apply(subgoal_tac "maximum_of_domain d1 i")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
   prefer 2
   apply (metis Sys2.der2_is_derivation der2_maximum_of_domain Sys2.derivationNoFromNone maximum_of_domain_derivation_take Sys2.no_some_beyond_maximum_of_domain add_Suc_shift AX_equal_length less_add_Suc1 AX_on_finite1 plus_nat.add_0)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
  apply(subgoal_tac "Sys1.derivation_initial G1 d1")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
   prefer 2
   apply(rule AX_on_derivation_initial1)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 i = Some (pair e c)")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
   prefer 2
   apply(rule Sys1.some_position_has_details_before_max_dom)
     apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
     apply(rule Sys1.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
  apply(erule_tac
      x="ca"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
   apply(rule_tac
      x="d1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e1' \<in> step_labels1 G1. label_relation G1 G2 e1' e1")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
   prefer 2
   apply(rule AX_step_labels_exists2)
    apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
   apply (metis Sys2.belongs_configurations Sys2.derivation_initial_belongs Sys2.AX_step_relation_preserves_belongs AX_TSstructure_rel_on_TSstructure2)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1')(*strict*)
  apply(subgoal_tac "\<exists>e2' \<in> step_labels1 G1. label_relation G1 G2 e2' e2")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1')(*strict*)
   prefer 2
   apply(rule AX_step_labels_exists2)
    apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1')(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1')(*strict*)
   apply (metis Sys2.belongs_configurations Sys2.derivation_initial_belongs Sys2.AX_step_relation_preserves_belongs AX_TSstructure_rel_on_TSstructure2)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1')(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
  apply(subgoal_tac "e1'=e2'")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e2')(*strict*)
   apply (metis Sys2.belongs_configurations Sys2.derivation_initial_belongs Sys2.AX_step_relation_preserves_belongs AX_TSstructure_rel_on_TSstructure2 AX_step_labels_unique1)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
  apply(subgoal_tac "\<exists>c1 c2. step_relation1 G1 ca e1' c1 \<and> step_relation1 G1 ca e2' c2")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
  apply(thin_tac "\<forall>c1 c2 e1 e2. step_relation1 G1 ca e1 c1 \<and> step_relation1 G1 ca e2 c2 \<longrightarrow> e1 = e2")
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
  apply(subgoal_tac "\<exists>c1. step_relation1 G1 ca e1' c1")
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
   apply(subgoal_tac "\<exists>c2. step_relation1 G1 ca e2' c2")
    apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
   apply(rule preserve_FEdetermR1_hlp)
            apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
            apply(force)
           apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
           prefer 2
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
          prefer 3
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
  apply(rule preserve_FEdetermR1_hlp)
           apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d2 i e d1 ea ca e1' e2')(*strict*)
  apply(force)
  done

lemma preserve_FEdetermR2_hlp: "
  TSstructure_rel G1 G2
  \<Longrightarrow> step_relation1 G1 c e2 c2
  \<Longrightarrow> Sys1.derivation_initial G1 d1
  \<Longrightarrow> d1 i = Some (pair e c)
  \<Longrightarrow> derivation_bisimulation G1 G2 (derivation_take d1 i) d2
  \<Longrightarrow> maximum_of_domain d2 i
  \<Longrightarrow> Sys2.derivation_initial G2 d2
  \<Longrightarrow> d2 i = Some (pair ea ca)
  \<Longrightarrow> e2' \<in> step_labels2 G2
  \<Longrightarrow> label_relation G1 G2 e2 e2'
  \<Longrightarrow> \<exists>c2. step_relation2 G2 ca e2' c2"
  apply(subgoal_tac "\<exists>e2 c2'. step_relation2 G2 (the(get_configuration(d2 SSn))) e2 c2' \<and> label_relation G1 G2 SSe1 e2 \<and> (let d1' = (derivation_append SSd1 (der2 (the(get_configuration(SSd1 SSn))) SSe1 SSc1') SSn) in (let d2' = (derivation_append d2 (der2 (the(get_configuration(d2 SSn))) e2 c2') SSn) in derivation_bisimulation G1 G2 d1' d2'))" for SSe1 SSd1 SSc1' SSn)
   prefer 2
   apply(rule_tac
      ?n="i"
      and ?d1.0="(derivation_take d1 i)"
      in AX_simulate12)
      apply(force)
     apply (metis AX_equal_length AX_on_finite1)
    apply(force)
   apply(rule_tac
      t="(the (get_configuration (derivation_take d1 i i)))"
      and s="c"
      in ssubst)
    apply(simp add: get_configuration_def derivation_take_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e2a c2')(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      x="c2'"
      in exI)
  apply(subgoal_tac "e2a=e2'")
   apply(rename_tac e2a c2')(*strict*)
   apply(clarsimp)
  apply(rename_tac e2a c2')(*strict*)
  apply (metis Sys1.belongs_configurations Sys1.derivation_initial_belongs Sys1.AX_step_relation_preserves_belongsE Sys2.belongs_configurations Sys2.derivation_initial_belongs Sys2.AX_step_relation_preserves_belongs AX_TSstructure_rel_on_TSstructure1 AX_TSstructure_rel_on_TSstructure2 AX_step_labels_unique1)
  done

lemma preserve_FEdetermR2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys2.is_forward_edge_deterministic_accessible G2
  \<Longrightarrow> Sys1.is_forward_edge_deterministic_accessible G1"
  apply(simp add: Sys1.is_forward_edge_deterministic_accessible_def Sys2.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: Sys1.get_accessible_configurations_def Sys2.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
  apply(rename_tac d1 i e)
  apply(rename_tac c c1 c2 e1 e2 d1 i e)(*strict*)
  apply(subgoal_tac "\<exists>d2. derivation_bisimulation G1 G2 (derivation_take d1 i) d2")
   apply(rename_tac c c1 c2 e1 e2 d1 i e)(*strict*)
   prefer 2
   apply(rule_tac
      n="i"
      in simulation_lift1)
     apply(rename_tac c c1 c2 e1 e2 d1 i e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d1 i e)(*strict*)
    apply (metis Sys1.derivation_take_preserves_derivation_initial)
   apply(rename_tac c c1 c2 e1 e2 d1 i e)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d1 i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
  apply(subgoal_tac "maximum_of_domain d2 i")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>n. maximum_of_domain d2 n")
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
    prefer 2
    apply (metis AX_on_finite2)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 n)(*strict*)
   apply(subgoal_tac "i=n")
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 n)(*strict*)
    prefer 2
    apply(rule AX_equal_length)
      apply(rename_tac c c1 c2 e1 e2 d1 i e d2 n)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 d1 i e d2 n)(*strict*)
     apply(simp add: maximum_of_domain_def derivation_take_def)
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 n)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 n)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
  apply(subgoal_tac "Sys2.derivation_initial G2 d2")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
   prefer 2
   apply(rule AX_on_derivation_initial2)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
   prefer 2
   apply(rule Sys2.some_position_has_details_before_max_dom)
     apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
     apply(rule Sys2.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
  apply(erule_tac
      x="ca"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
   apply(rule_tac
      x="d2"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e1' \<in> step_labels2 G2. label_relation G1 G2 e1 e1'")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
   prefer 2
   apply(rule AX_step_labels_exists1)
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
   apply (metis Sys1.belongs_configurations Sys1.derivation_initial_belongs Sys1.AX_step_relation_preserves_belongsE AX_TSstructure_rel_on_TSstructure1)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1')(*strict*)
  apply(subgoal_tac "\<exists>e2' \<in> step_labels2 G2. label_relation G1 G2 e2 e2'")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1')(*strict*)
   prefer 2
   apply(rule AX_step_labels_exists1)
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1')(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1')(*strict*)
   apply (metis Sys1.belongs_configurations Sys1.derivation_initial_belongs Sys1.AX_step_relation_preserves_belongsE AX_TSstructure_rel_on_TSstructure1)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1')(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
  apply(subgoal_tac "e1'=e2'")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e2')(*strict*)
   apply (metis Sys1.belongs_configurations Sys1.derivation_initial_belongs Sys1.AX_step_relation_preserves_belongsE AX_TSstructure_rel_on_TSstructure1 AX_step_labels_unique2)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
  apply(subgoal_tac "\<exists>c1 c2. step_relation2 G2 ca e1' c1 \<and> step_relation2 G2 ca e2' c2")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
  apply(thin_tac "\<forall>c1 c2 e1 e2. step_relation2 G2 ca e1 c1 \<and> step_relation2 G2 ca e2 c2 \<longrightarrow> e1 = e2")
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
  apply(subgoal_tac "\<exists>c1. step_relation2 G2 ca e1' c1")
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
   apply(subgoal_tac "\<exists>c2. step_relation2 G2 ca e2' c2")
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
   apply(rule preserve_FEdetermR2_hlp)
            apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
            apply(force)
           apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
           prefer 2
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
          prefer 3
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
  apply(rule preserve_FEdetermR2_hlp)
           apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d1 i e d2 ea ca e1' e2')(*strict*)
  apply(force)
  done

theorem preservation_of_determinism: "
  TSstructure_rel G1 G2
  \<Longrightarrow>
  Sys1.is_forward_edge_deterministic_accessible G1 \<longleftrightarrow> Sys2.is_forward_edge_deterministic_accessible G2"
  apply(metis preserve_FEdetermR2 preserve_FEdetermR1)
  done

theorem language_translation: "
  TSstructure_rel G1 G2
  \<Longrightarrow> left_total_on (effect_rel G1 G2) (Sys1.finite_marked_language G1) (Sys2.marked_language G2)
  \<and> right_total_on (effect_rel G1 G2) (Sys1.marked_language G1) (Sys2.finite_marked_language G2)
  \<and> left_total_on (effect_rel G1 G2) (Sys1.finite_unmarked_language G1) (Sys2.unmarked_language G2)
  \<and> right_total_on (effect_rel G1 G2) (Sys1.unmarked_language G1) (Sys2.finite_unmarked_language G2)"
  apply(rule conjI)
   apply(simp add: left_total_on_def)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule_tac ?o1.0="a" in ATS_Bisimulation_Derivation_Strong1_marked_language_translation1)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp add: right_total_on_def)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac b)(*strict*)
    prefer 2
    apply(rule_tac ?o2.0="b" in ATS_Bisimulation_Derivation_Strong1_marked_language_translation2)
     apply(rename_tac b)(*strict*)
     apply(force)
    apply(rename_tac b)(*strict*)
    apply(force)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp add: left_total_on_def)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule_tac ?o1.0="a" in ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(simp add: right_total_on_def)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac b)(*strict*)
   prefer 2
   apply(rule_tac ?o2.0="b" in ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2)
    apply(rename_tac b)(*strict*)
    apply(force)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rename_tac b)(*strict*)
  apply(force)
  done

end

end
