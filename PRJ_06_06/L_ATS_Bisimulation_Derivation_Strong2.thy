section {*L\_ATS\_Bisimulation\_Derivation\_Strong2*}
theory
  L_ATS_Bisimulation_Derivation_Strong2

imports
  L_ATS_Bisimulation_Derivation_Strong1

begin

locale ATS_Bisimulation_Derivation_Strong2 =
  Sys1 :
  ATS_Sched_DB
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "effects1 :: 'TSstructure1 \<Rightarrow> 'event1 set"
  "marking_condition1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> bool"
  "marked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> 'event1 set"
  "unmarked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> 'event1 set"
  "fixed_schedulers1 :: 'TSstructure1 \<Rightarrow> 'fixed_scheduler1 set"
  "empty_fixed_scheduler1 :: 'TSstructure1 \<Rightarrow> 'fixed_scheduler1"
  "fixed_scheduler_extendable1 :: 'TSstructure1 \<Rightarrow> 'fixed_scheduler1 \<Rightarrow> bool"
  "scheduler_fragments1 :: 'TSstructure1 \<Rightarrow> 'scheduler_fragment1 set"
  "empty_scheduler_fragment1 :: 'TSstructure1 \<Rightarrow> 'scheduler_fragment1"
  "join_scheduler_fragments1 :: 'scheduler_fragment1 \<Rightarrow> 'scheduler_fragment1 \<Rightarrow> 'scheduler_fragment1"
  "unfixed_schedulers1 :: 'TSstructure1 \<Rightarrow> 'unfixed_scheduler1 set"
  "empty_unfixed_scheduler1 :: 'TSstructure1 \<Rightarrow> 'unfixed_scheduler1"
  "unfixed_scheduler_right_quotient1 :: 'unfixed_scheduler1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'scheduler_fragment1 option"
  "extend_unfixed_scheduler1 :: 'scheduler_fragment1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'unfixed_scheduler1"
  "unfixed_scheduler_extendable1 :: 'TSstructure1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> bool"
  "schedulers1 :: 'TSstructure1 \<Rightarrow> 'scheduler1 set"
  "initial_schedulers1 :: 'TSstructure1 \<Rightarrow> 'scheduler1 set"
  "empty_scheduler1 :: 'TSstructure1 \<Rightarrow> 'scheduler1"
  "get_scheduler1 :: 'conf1 \<Rightarrow> 'scheduler1"
  "extend_scheduler1 :: 'scheduler_fragment1 \<Rightarrow> 'scheduler1 \<Rightarrow> 'scheduler1"
  "join_fixed_scheduler_unfixed_scheduler1 :: 'fixed_scheduler1 \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'scheduler1"
  "set_unfixed_scheduler_DB1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler1 \<Rightarrow> 'conf1"
  "get_unfixed_scheduler_DB1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler1"
  "get_fixed_scheduler_DB1 :: 'TSstructure1 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler1"
  +
  Sys2 :
  ATS_Sched_DB
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "effects2 :: 'TSstructure2 \<Rightarrow> 'event2 set"
  "marking_condition2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> bool"
  "marked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> 'event2 set"
  "unmarked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> 'event2 set"
  "fixed_schedulers2 :: 'TSstructure2 \<Rightarrow> 'fixed_scheduler2 set"
  "empty_fixed_scheduler2 :: 'TSstructure2 \<Rightarrow> 'fixed_scheduler2"
  "fixed_scheduler_extendable2 :: 'TSstructure2 \<Rightarrow> 'fixed_scheduler2 \<Rightarrow> bool"
  "scheduler_fragments2 :: 'TSstructure2 \<Rightarrow> 'scheduler_fragment2 set"
  "empty_scheduler_fragment2 :: 'TSstructure2 \<Rightarrow> 'scheduler_fragment2"
  "join_scheduler_fragments2 :: 'scheduler_fragment2 \<Rightarrow> 'scheduler_fragment2 \<Rightarrow> 'scheduler_fragment2"
  "unfixed_schedulers2 :: 'TSstructure2 \<Rightarrow> 'unfixed_scheduler2 set"
  "empty_unfixed_scheduler2 :: 'TSstructure2 \<Rightarrow> 'unfixed_scheduler2"
  "unfixed_scheduler_right_quotient2 :: 'unfixed_scheduler2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'scheduler_fragment2 option"
  "extend_unfixed_scheduler2 :: 'scheduler_fragment2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'unfixed_scheduler2"
  "unfixed_scheduler_extendable2 :: 'TSstructure2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> bool"
  "schedulers2 :: 'TSstructure2 \<Rightarrow> 'scheduler2 set"
  "initial_schedulers2 :: 'TSstructure2 \<Rightarrow> 'scheduler2 set"
  "empty_scheduler2 :: 'TSstructure2 \<Rightarrow> 'scheduler2"
  "get_scheduler2 :: 'conf2 \<Rightarrow> 'scheduler2"
  "extend_scheduler2 :: 'scheduler_fragment2 \<Rightarrow> 'scheduler2 \<Rightarrow> 'scheduler2"
  "join_fixed_scheduler_unfixed_scheduler2 :: 'fixed_scheduler2 \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'scheduler2"
  "set_unfixed_scheduler_DB2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler2 \<Rightarrow> 'conf2"
  "get_unfixed_scheduler_DB2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> nat \<Rightarrow> 'unfixed_scheduler2"
  "get_fixed_scheduler_DB2 :: 'TSstructure2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler2"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 fixed_schedulers1 empty_fixed_scheduler1 fixed_scheduler_extendable1 scheduler_fragments1 empty_scheduler_fragment1 join_scheduler_fragments1 unfixed_schedulers1 empty_unfixed_scheduler1 unfixed_scheduler_right_quotient1 extend_unfixed_scheduler1 unfixed_scheduler_extendable1 schedulers1 initial_schedulers1 empty_scheduler1 get_scheduler1 extend_scheduler1 join_fixed_scheduler_unfixed_scheduler1 set_unfixed_scheduler_DB1 get_unfixed_scheduler_DB1 get_fixed_scheduler_DB1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 fixed_schedulers2 empty_fixed_scheduler2 fixed_scheduler_extendable2 scheduler_fragments2 empty_scheduler_fragment2 join_scheduler_fragments2 unfixed_schedulers2 empty_unfixed_scheduler2 unfixed_scheduler_right_quotient2 extend_unfixed_scheduler2 unfixed_scheduler_extendable2 schedulers2 initial_schedulers2 empty_scheduler2 get_scheduler2 extend_scheduler2 join_fixed_scheduler_unfixed_scheduler2 set_unfixed_scheduler_DB2 get_unfixed_scheduler_DB2 get_fixed_scheduler_DB2
    +
  fixes TSstructure_rel :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"

fixes effect_rel :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"

fixes label_relation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2 \<Rightarrow> bool"

fixes derivation_bisimulation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('label1, 'conf1) derivation \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> bool"

assumes AX_2_TSstructure_rel_on_TSstructure1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> TSstructure1 G1"

assumes AX_2_TSstructure_rel_on_TSstructure2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> TSstructure2 G2"

assumes AX_2_AX_initial_contained1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> \<exists>c2. derivation_bisimulation G1 G2 (der1 c1) (der1 c2)"

assumes AX_2_AX_initial_contained2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> c2 \<in> initial_configurations2 G2
  \<Longrightarrow> \<exists>c1. derivation_bisimulation G1 G2 (der1 c1) (der1 c2)"

assumes AX_2_on_derivation_initial1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> Sys1.derivation_initial G1 d1"

assumes AX_2_on_finite1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> \<exists>n. maximum_of_domain d1 n"

assumes AX_2_on_derivation_initial2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> Sys2.derivation_initial G2 d2"

assumes AX_2_on_finite2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> \<exists>n. maximum_of_domain d2 n"

assumes AX_2_equal_length: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> n1=n2"

assumes AX_2_simulate12: "
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

assumes AX_2_simulate21: "
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

assumes AX_2_bisimulation_compatible_with_crop1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh' n
  \<Longrightarrow> derivation_append_fit dh' dc n
  \<Longrightarrow> derivation_bisimulation G1 G2 (derivation_append dh' dc n) dc'
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> dh x = dc' x"

assumes AX_2_bisimulation_compatible_with_crop2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> derivation_append_fit dh dc' n
  \<Longrightarrow> derivation_bisimulation G1 G2 dc (derivation_append dh dc' n)
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> dh' x = dc x"

assumes AX_2_bisimulation_compatible_with_unfixed_scheduler_extendable1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 d1 m)
  \<Longrightarrow> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 d2 m)"

assumes AX_2_bisimulation_compatible_with_unfixed_scheduler_extendable2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 d2 m)
  \<Longrightarrow> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 d1 m)"

assumes AX_2_bisimulation_compatible_with_replace_and_schedF1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh' n
  \<Longrightarrow> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh n)
  \<Longrightarrow> unfixed_scheduler_extendable1 G1 sUF
  \<Longrightarrow> sUF \<in> unfixed_schedulers1 G1
  \<Longrightarrow> derivation_bisimulation G1 G2 (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) dc'
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> get_fixed_scheduler_DB2 G2 dh x = get_fixed_scheduler_DB2 G2 dc' x
  \<and> Sys2.replace_unfixed_scheduler_DB G2 dh (get_unfixed_scheduler_DB2 G2 dc' n) n x = dc' x"

assumes AX_2_bisimulation_compatible_with_replace_and_schedF2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dh' dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh' n)
  \<Longrightarrow> unfixed_scheduler_extendable2 G2 sUF'
  \<Longrightarrow> sUF' \<in> unfixed_schedulers2 G2
  \<Longrightarrow> derivation_bisimulation G1 G2 dc (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh sUF' n) dc' n)
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> get_fixed_scheduler_DB1 G1 dh' x = get_fixed_scheduler_DB1 G1 dc x
  \<and> Sys1.replace_unfixed_scheduler_DB G1 dh' (get_unfixed_scheduler_DB1 G1 dc n) n x = dc x"

assumes AX_2_accept_id1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> marking_condition1 G1 d1
  \<Longrightarrow> marking_condition2 G2 d2"

assumes AX_2_accept_id2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> marking_condition2 G2 d2
  \<Longrightarrow> marking_condition1 G1 d1"

assumes AX_2_unmarked_effect_id1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o1 \<in> unmarked_effect1 G1 d1
  \<Longrightarrow> \<exists>o2. effect_rel G1 G2 o1 o2
  \<and> o2 \<in> unmarked_effect2 G2 d2"

assumes AX_2_unmarked_effect_id2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o2 \<in> unmarked_effect2 G2 d2
  \<Longrightarrow> \<exists>o1. effect_rel G1 G2 o1 o2
  \<and> o1 \<in> unmarked_effect1 G1 d1"

assumes AX_2_marked_effect_id1: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o1 \<in> marked_effect1 G1 d1
  \<Longrightarrow> marking_condition1 G1 d1
  \<Longrightarrow> \<exists>o2. effect_rel G1 G2 o1 o2
  \<and> o2 \<in> marked_effect2 G2 d2"

assumes AX_2_marked_effect_id2: "
  derivation_bisimulation G1 G2 d1 d2
  \<Longrightarrow> o2 \<in> marked_effect2 G2 d2
  \<Longrightarrow> marking_condition2 G2 d2
  \<Longrightarrow> \<exists>o1. effect_rel G1 G2 o1 o2
  \<and> o1 \<in> marked_effect1 G1 d1"

assumes AX_2_step_labels_unique1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> e21 \<in> step_labels2 G2
  \<Longrightarrow> e22 \<in> step_labels2 G2
  \<Longrightarrow> label_relation G1 G2 e1 e21
  \<Longrightarrow> label_relation G1 G2 e1 e22
  \<Longrightarrow> e21 = e22"

assumes AX_2_step_labels_unique2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e11 \<in> step_labels1 G1
  \<Longrightarrow> e12 \<in> step_labels1 G1
  \<Longrightarrow> e2 \<in> step_labels2 G2
  \<Longrightarrow> label_relation G1 G2 e11 e2
  \<Longrightarrow> label_relation G1 G2 e12 e2
  \<Longrightarrow> e11 = e12"

assumes AX_2_step_labels_exists1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> \<exists>e2 \<in> step_labels2 G2. label_relation G1 G2 e1 e2"

assumes AX_2_step_labels_exists2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> e2 \<in> step_labels2 G2
  \<Longrightarrow> \<exists>e1 \<in> step_labels1 G1. label_relation G1 G2 e1 e2"

sublocale ATS_Bisimulation_Derivation_Strong2  \<subseteq> ATS_Bisimulation_Derivation_Strong1
  apply(unfold_locales)
                      apply(rename_tac G1 G2)(*strict*)
                      apply(rule AX_2_TSstructure_rel_on_TSstructure1)
                      apply(force)
                      apply(rename_tac G1 G2)(*strict*)
                      apply(rule AX_2_TSstructure_rel_on_TSstructure2)
                      apply(force)
                      apply(rename_tac G1 G2 c1)(*strict*)
                      apply(rule AX_2_AX_initial_contained1)
                      apply(rename_tac G1 G2 c1)(*strict*)
                      apply(force)
                      apply(rename_tac G1 G2 c1)(*strict*)
                      apply(force)
                      apply(rename_tac G1 G2 c2)(*strict*)
                      apply(rule AX_2_AX_initial_contained2)
                      apply(rename_tac G1 G2 c2)(*strict*)
                      apply(force)
                      apply(rename_tac G1 G2 c2)(*strict*)
                      apply(force)
                      apply(rename_tac G1 G2 d1 d2)(*strict*)
                      apply(rule AX_2_on_derivation_initial1)
                      apply(force)
                     apply(rename_tac G1 G2 d1 d2)(*strict*)
                     apply(rule AX_2_on_finite1)
                     apply(force)
                    apply(rename_tac G1 G2 d1 d2)(*strict*)
                    apply(rule AX_2_on_derivation_initial2)
                    apply(force)
                   apply(rename_tac G1 G2 d1 d2)(*strict*)
                   apply(rule AX_2_on_finite2)
                   apply(force)
                  apply(rename_tac G1 G2 d1 d2 n1 n2)(*strict*)
                  apply(rule AX_2_equal_length)
                    apply(rename_tac G1 G2 d1 d2 n1 n2)(*strict*)
                    apply(force)
                   apply(rename_tac G1 G2 d1 d2 n1 n2)(*strict*)
                   apply(force)
                  apply(rename_tac G1 G2 d1 d2 n1 n2)(*strict*)
                  apply(force)
                 apply(rename_tac G1 G2 d1 d2 n e1 c1')(*strict*)
                 apply(rule AX_2_simulate12)
                    apply(rename_tac G1 G2 d1 d2 n e1 c1')(*strict*)
                    apply(force)
                   apply(rename_tac G1 G2 d1 d2 n e1 c1')(*strict*)
                   apply(force)
                  apply(rename_tac G1 G2 d1 d2 n e1 c1')(*strict*)
                  apply(force)
                 apply(rename_tac G1 G2 d1 d2 n e1 c1')(*strict*)
                 apply(force)
                apply(rename_tac G1 G2 d1 d2 n e2 c2')(*strict*)
                apply(rule AX_2_simulate21)
                   apply(rename_tac G1 G2 d1 d2 n e2 c2')(*strict*)
                   apply(force)
                  apply(rename_tac G1 G2 d1 d2 n e2 c2')(*strict*)
                  apply(force)
                 apply(rename_tac G1 G2 d1 d2 n e2 c2')(*strict*)
                 apply(force)
                apply(rename_tac G1 G2 d1 d2 n e2 c2')(*strict*)
                apply(force)
               apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
               apply(rule AX_2_bisimulation_compatible_with_crop1)
                    apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
                    apply(force)
                   apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
                   apply(force)
                  apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
                  apply(force)
                 apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
                 apply(force)
                apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
                apply(force)
               apply(rename_tac G1 G2 dh' dh n dc dc' x)(*strict*)
               apply(force)
              apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
              apply(rule AX_2_bisimulation_compatible_with_crop2)
                   apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
                   apply(force)
                  apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
                  apply(force)
                 apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
                 apply(force)
                apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
                apply(force)
               apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
               apply(force)
              apply(rename_tac G1 G2 dh' dh n dc' dc x)(*strict*)
              apply(force)
             apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
             apply(rule AX_2_bisimulation_compatible_with_unfixed_scheduler_extendable1)
                 apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
                 apply(force)
                apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
                apply(force)
               apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
               apply(force)
              apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
              apply(force)
             apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
             apply(force)
            apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
            apply(rule AX_2_bisimulation_compatible_with_unfixed_scheduler_extendable2)
                apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
                apply(force)
               apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
               apply(force)
              apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
              apply(force)
             apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
             apply(force)
            apply(rename_tac G1 G2 d1 d2 n m)(*strict*)
            apply(force)
           apply(rename_tac G1 G2 d1 d2)(*strict*)
           apply(rule AX_2_accept_id1)
            apply(rename_tac G1 G2 d1 d2)(*strict*)
            apply(force)
           apply(rename_tac G1 G2 d1 d2)(*strict*)
           apply(force)
          apply(rename_tac G1 G2 d1 d2)(*strict*)
          apply(rule AX_2_accept_id2)
           apply(rename_tac G1 G2 d1 d2)(*strict*)
           apply(force)
          apply(rename_tac G1 G2 d1 d2)(*strict*)
          apply(force)
         apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
         apply(rule AX_2_unmarked_effect_id1)
          apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
          apply(force)
         apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
        apply(rule AX_2_unmarked_effect_id2)
         apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
       apply(rule AX_2_marked_effect_id1)
         apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 d1 d2 o1)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
      apply(rule AX_2_marked_effect_id2)
        apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 d1 d2 o2)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
     apply(rule AX_2_step_labels_unique1)
          apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
          apply(force)
         apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 e1 e21 e22)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
    apply(rule AX_2_step_labels_unique2)
         apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
         apply(force)
        apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 e11 e12 e2)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 e1)(*strict*)
   apply(rule AX_2_step_labels_exists1)
    apply(rename_tac G1 G2 e1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 e1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 e2)(*strict*)
  apply(rule AX_2_step_labels_exists2)
   apply(rename_tac G1 G2 e2)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 e2)(*strict*)
  apply(force)
  done

context ATS_Bisimulation_Derivation_Strong2 begin

theorem Nonblockingness_translation1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys1.Nonblockingness_linear_DB G1
  \<Longrightarrow> Sys2.Nonblockingness_linear_DB G2"
  apply(simp add: Sys2.Nonblockingness_linear_DB_def Sys1.Nonblockingness_linear_DB_def)
  apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>dh'. derivation_bisimulation G1 G2 dh' dh")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule simulation_lift2)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh')(*strict*)
  apply(erule_tac
      x="dh'"
      in allE)
  apply(subgoal_tac "\<exists>n1. maximum_of_domain dh' n1")
   apply(rename_tac dh n dh')(*strict*)
   prefer 2
   apply(rule AX_on_finite1)
   apply(force)
  apply(rename_tac dh n dh')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n1)(*strict*)
  apply(erule_tac
      x="n1"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n dh' n1)(*strict*)
   apply(rule AX_on_derivation_initial1)
   apply(force)
  apply(rename_tac dh n dh' n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n1 dc sUF dh'a n')(*strict*)
  apply(subgoal_tac "n1=n")
   apply(rename_tac dh n dh' n1 dc sUF dh'a n')(*strict*)
   prefer 2
   apply (metis AX_equal_length)
  apply(rename_tac dh n dh' n1 dc sUF dh'a n')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
  apply(case_tac "unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh' n)")
   apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac dh n dh' dc n')(*strict*)
   apply(subgoal_tac "\<not> unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh n)")
    apply(rename_tac dh n dh' dc n')(*strict*)
    apply(clarsimp)
    apply(rule Nonblockingness_translation1_hlp1)
               apply(rename_tac dh n dh' dc n')(*strict*)
               apply(force)+
   apply(rename_tac dh n dh' dc n')(*strict*)
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable2 eq_imp_le)
  apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh n)")
   apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
   prefer 2
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable1 le_refl)
  apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n')(*strict*)
  apply(subgoal_tac "\<exists>e c. dh' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF n')(*strict*)
   prefer 2
   apply(rule Sys1.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF n')(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
      apply(rename_tac dh n dh' dc sUF n')(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n')(*strict*)
     apply (metis AX_on_derivation_initial1)
    apply(rename_tac dh n dh' dc sUF n')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(subgoal_tac "ATS.derivation_initial initial_configurations1 step_relation1 G1 (Sys1.map_unfixed_scheduler_DB G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF))")
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   prefer 2
   apply(rule Sys1.sched_modification_preserves_derivation_initial)
         apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
         prefer 7
         apply(force)
        apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure1)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
       apply(rule AX_on_derivation_initial1)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(subgoal_tac "\<exists>dc'. derivation_bisimulation G1 G2 (derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF)) dc n) dc'")
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   prefer 2
   apply(rule_tac
      ?n.0="n+n'"
      in simulation_lift1)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(rule Sys1.derivation_append_preserves_derivation_initial_prime)
        apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure1)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
      apply(simp add: Sys1.map_unfixed_scheduler_DB_def maximum_of_domain_def)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(rule_tac
      t="ATS_SchedUF_DB.map_unfixed_scheduler_DB set_unfixed_scheduler_DB1 get_unfixed_scheduler_DB1 G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF)"
      and s="ATS_SchedUF_DB.replace_unfixed_scheduler_DB unfixed_scheduler_right_quotient1 extend_unfixed_scheduler1 set_unfixed_scheduler_DB1 get_unfixed_scheduler_DB1 G1 dh' sUF n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(simp (no_asm) add: Sys1.replace_unfixed_scheduler_DB_def)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(simp add: Sys1.map_unfixed_scheduler_DB_def maximum_of_domain_def)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply (metis AX_on_finite2)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'a)(*strict*)
  apply(rename_tac n'')
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(subgoal_tac "n''=n+n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      ?d1.0="derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF)) dc n"
      in AX_equal_length)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(rule Sys1.map_unfixed_scheduler_DB_preserves_maximum_of_domain)
        apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure1)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply (metis AX_on_derivation_initial1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(rule_tac
      x="derivation_drop dc' n"
      in exI)
  apply(rule_tac
      x="get_unfixed_scheduler_DB2 G2 dc' n"
      in exI)
  apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule AX_on_derivation_initial2)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule Sys2.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys2.AX_get_unfixed_scheduler_DB_closed)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_initial_belongs)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule AX_on_derivation_initial2)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(subgoal_tac "get_fixed_scheduler_DB2 G2 dh n = get_fixed_scheduler_DB2 G2 dc' n")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply (metis Sys1.replace_unfixed_scheduler_DB_def AX_2_bisimulation_compatible_with_replace_and_schedF1 le_refl)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   defer
   apply(rule context_conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="Sys2.get_scheduler_nth (derivation_drop dc' n) 0"
      and s="Sys2.get_scheduler_nth dc' n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.get_scheduler_nth_def derivation_drop_def get_configuration_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_drop_preserves_derivation)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_drop_preserves_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial2)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule Sys2.derivation_initial_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule_tac
      x="n'"
      in exI)
    apply(rule_tac
      t="n'"
      and s="(n+n')-n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_drop_makes_maximum_of_domain)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial2)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(subgoal_tac "(derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh n))) (get_unfixed_scheduler_DB2 G2 dc' n))) (derivation_drop dc' n) n) = dc'")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     prefer 2
     apply(rule AX_accept_id1)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp (no_asm) add: Sys1.replace_unfixed_scheduler_DB_def)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(subgoal_tac "derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh n))) (get_unfixed_scheduler_DB2 G2 dc' n))) (derivation_drop dc' n) n n = dc' n")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(thin_tac "derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh n))) (get_unfixed_scheduler_DB2 G2 dc' n))) (derivation_drop dc' n) n = dc'")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: derivation_append_def derivation_drop_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(case_tac "x>n")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(thin_tac "marking_condition1 G1 (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB unfixed_scheduler_right_quotient1 extend_unfixed_scheduler1 set_unfixed_scheduler_DB1 get_unfixed_scheduler_DB1 G1 dh' sUF n) dc n)")
   apply(simp add: derivation_append_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(subgoal_tac "n\<ge>x")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(clarsimp)
   apply(fold Sys1.replace_unfixed_scheduler_DB_def)
   apply(fold Sys2.replace_unfixed_scheduler_DB_def)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(thin_tac "marking_condition1 G1 (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n)")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(fold derivation_append_def)
   apply (metis AX_2_bisimulation_compatible_with_replace_and_schedF1)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      n="n+n'"
      in AX_bisimulation_compatible_with_unfixed_scheduler_extendable1)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: maximum_of_domain_def Sys1.replace_unfixed_scheduler_DB_def Sys1.map_unfixed_scheduler_DB_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB1 G1 (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n"
      and s="get_unfixed_scheduler_DB1 G1 (derivation_take (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n) n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys1.AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_append_preserves_derivation_initial)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_append_preserves_derivation)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
    apply(simp add: Sys1.map_unfixed_scheduler_DB_def)
    apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="derivation_take (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n"
      and s="Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n"
      and s="derivation_take ((Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) ) n"
      in ssubst)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule derivation_take_derivation_append_ignore)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
   apply(simp add: Sys1.map_unfixed_scheduler_DB_def)
   apply(clarsimp)
   apply(subgoal_tac "dh' x = None")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(rule Sys1.none_position_after_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply (metis AX_on_derivation_initial1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB1 G1 (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) n"
      and s="sUF"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule Sys1.AX_replace_unfixed_scheduler_DB_sound)
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply (metis AX_TSstructure_rel_on_TSstructure1)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_on_derivation_initial1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(force)
  done

theorem Nonblockingness_translation_rest1: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys1.Nonblockingness_linear_restricted_DB G1
  \<Longrightarrow> Sys2.Nonblockingness_linear_restricted_DB G2"
  apply(simp add: Sys2.Nonblockingness_linear_restricted_DB_def Sys1.Nonblockingness_linear_restricted_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>dh'. derivation_bisimulation G1 G2 dh' dh")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule simulation_lift2)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh')(*strict*)
  apply(erule_tac
      x="dh'"
      in allE)
  apply(subgoal_tac "\<exists>n1. maximum_of_domain dh' n1")
   apply(rename_tac dh n dh')(*strict*)
   prefer 2
   apply(rule AX_on_finite1)
   apply(force)
  apply(rename_tac dh n dh')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n1)(*strict*)
  apply(erule_tac
      x="n1"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n dh' n1)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' n1)(*strict*)
    apply(rule AX_on_derivation_initial1)
    apply(force)
   apply(rename_tac dh n dh' n1)(*strict*)
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable2 AX_equal_length le_refl)
  apply(rename_tac dh n dh' n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n1 dc sUF x)(*strict*)
  apply(subgoal_tac "n1=n")
   apply(rename_tac dh n dh' n1 dc sUF x)(*strict*)
   prefer 2
   apply (metis AX_equal_length)
  apply(rename_tac dh n dh' n1 dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh' n)")
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   prefer 2
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable2 le_refl)
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   prefer 2
   apply(rule Sys1.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF x)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
      apply(rename_tac dh n dh' dc sUF x)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF x)(*strict*)
     apply (metis AX_on_derivation_initial1)
    apply(rename_tac dh n dh' dc sUF x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
  apply(subgoal_tac "ATS.derivation_initial initial_configurations1 step_relation1 G1 (Sys1.map_unfixed_scheduler_DB G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF))")
   apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
   prefer 2
   apply(rule Sys1.sched_modification_preserves_derivation_initial)
         apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
         prefer 7
         apply(force)
        apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure1)
        apply(force)
       apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
       apply(rule AX_on_derivation_initial1)
       apply(force)
      apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
  apply(rename_tac n' e c)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(subgoal_tac "\<exists>dc'. derivation_bisimulation G1 G2 (derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF)) dc n) dc'")
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   prefer 2
   apply(rule_tac
      ?n.0="n+n'"
      in simulation_lift1)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(rule Sys1.derivation_append_preserves_derivation_initial_prime)
        apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure1)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
      apply(simp add: Sys1.map_unfixed_scheduler_DB_def maximum_of_domain_def)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(simp add: Sys1.map_unfixed_scheduler_DB_def maximum_of_domain_def)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply (metis AX_on_finite2)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'a)(*strict*)
  apply(rename_tac n'')
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(subgoal_tac "n''=n+n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      ?d1.0="derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh' (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh' n))) sUF)) dc n"
      in AX_equal_length)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(rule Sys1.map_unfixed_scheduler_DB_preserves_maximum_of_domain)
        apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure1)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply (metis AX_on_derivation_initial1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(rule_tac
      x="derivation_drop dc' n"
      in exI)
  apply(rule_tac
      x="get_unfixed_scheduler_DB2 G2 dc' n"
      in exI)
  apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule AX_on_derivation_initial2)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule Sys2.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys2.AX_get_unfixed_scheduler_DB_closed)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_initial_belongs)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule AX_on_derivation_initial2)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(subgoal_tac "get_fixed_scheduler_DB2 G2 dh n = get_fixed_scheduler_DB2 G2 dc' n")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply (metis Sys1.replace_unfixed_scheduler_DB_def AX_2_bisimulation_compatible_with_replace_and_schedF1 le_refl)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   defer
   apply(rule context_conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="Sys2.get_scheduler_nth (derivation_drop dc' n) 0"
      and s="Sys2.get_scheduler_nth dc' n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.get_scheduler_nth_def derivation_drop_def get_configuration_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.derivation_initial_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_drop_preserves_derivation)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_drop_preserves_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial2)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule Sys2.derivation_initial_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial2)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule_tac
      x="n'"
      in exI)
    apply(rule_tac
      t="n'"
      and s="(n+n')-n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_drop_makes_maximum_of_domain)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys2.derivation_initial G2 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial2)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(subgoal_tac "(derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh n))) (get_unfixed_scheduler_DB2 G2 dc' n))) (derivation_drop dc' n) n) = dc'")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     prefer 2
     apply(rule AX_accept_id1)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
     apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(subgoal_tac "derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh n))) (get_unfixed_scheduler_DB2 G2 dc' n))) (derivation_drop dc' n) n n = dc' n")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(thin_tac "derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh n))) (get_unfixed_scheduler_DB2 G2 dc' n))) (derivation_drop dc' n) n = dc'")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
     apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
     apply(simp add: derivation_append_def derivation_drop_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(case_tac "x>n")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(thin_tac "marking_condition1 G1        (derivation_append          (ATS_SchedUF_DB.replace_unfixed_scheduler_DB            unfixed_scheduler_right_quotient1 extend_unfixed_scheduler1            set_unfixed_scheduler_DB1 get_unfixed_scheduler_DB1 G1 dh' sUF            n)          dc n)")
   apply(simp add: derivation_append_def)
   apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(subgoal_tac "n\<ge>x")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(clarsimp)
   apply(fold Sys1.replace_unfixed_scheduler_DB_def)
   apply(fold Sys2.replace_unfixed_scheduler_DB_def)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(thin_tac "marking_condition1 G1 (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n)")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(fold derivation_append_def)
   apply (metis AX_2_bisimulation_compatible_with_replace_and_schedF1)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      n="n+n'"
      in AX_bisimulation_compatible_with_unfixed_scheduler_extendable1)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: maximum_of_domain_def Sys1.replace_unfixed_scheduler_DB_def Sys1.map_unfixed_scheduler_DB_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB1 G1 (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n"
      and s="get_unfixed_scheduler_DB1 G1 (derivation_take (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n) n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys1.AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_append_preserves_derivation_initial)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_append_preserves_derivation)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
    apply(simp add: Sys1.map_unfixed_scheduler_DB_def)
    apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="derivation_take (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n"
      and s="Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) dc n) n"
      and s="derivation_take ((Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) ) n"
      in ssubst)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule derivation_take_derivation_append_ignore)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
   apply(simp add: Sys1.map_unfixed_scheduler_DB_def)
   apply(clarsimp)
   apply(subgoal_tac "dh' x = None")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(rule Sys1.none_position_after_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply (metis AX_on_derivation_initial1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB1 G1 (Sys1.replace_unfixed_scheduler_DB G1 dh' sUF n) n"
      and s="sUF"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule Sys1.AX_replace_unfixed_scheduler_DB_sound)
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply (metis AX_TSstructure_rel_on_TSstructure1)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_on_derivation_initial1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(force)
  done

theorem Nonblockingness_translation2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys2.Nonblockingness_linear_DB G2
  \<Longrightarrow> Sys1.Nonblockingness_linear_DB G1"
  apply(simp add: Sys1.Nonblockingness_linear_DB_def Sys2.Nonblockingness_linear_DB_def)
  apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>dh'. derivation_bisimulation G1 G2 dh dh'")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule simulation_lift1)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh')(*strict*)
  apply(erule_tac
      x="dh'"
      in allE)
  apply(subgoal_tac "\<exists>n1. maximum_of_domain dh' n1")
   apply(rename_tac dh n dh')(*strict*)
   prefer 2
   apply(rule AX_on_finite2)
   apply(force)
  apply(rename_tac dh n dh')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n1)(*strict*)
  apply(erule_tac
      x="n1"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n dh' n1)(*strict*)
   apply(rule AX_on_derivation_initial2)
   apply(force)
  apply(rename_tac dh n dh' n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n1 dc sUF dh'a n')(*strict*)
  apply(subgoal_tac "n1=n")
   apply(rename_tac dh n dh' n1 dc sUF dh'a n')(*strict*)
   prefer 2
   apply (metis AX_equal_length)
  apply(rename_tac dh n dh' n1 dc sUF dh'a n')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
  apply(case_tac "unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh' n)")
   apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac dh n dh' dc n')(*strict*)
   apply(subgoal_tac "\<not> unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh n)")
    apply(rename_tac dh n dh' dc n')(*strict*)
    apply(clarsimp)
    apply(rule Nonblockingness_translation2_hlp1)
               apply(rename_tac dh n dh' dc n')(*strict*)
               apply(force)+
   apply(rename_tac dh n dh' dc n')(*strict*)
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable1 eq_imp_le)
  apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh n)")
   apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
   prefer 2
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable2 le_refl)
  apply(rename_tac dh n dh' dc sUF dh'a n')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n')(*strict*)
  apply(subgoal_tac "\<exists>e c. dh' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF n')(*strict*)
   prefer 2
   apply(rule Sys2.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF n')(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF n')(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n')(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF n')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(subgoal_tac "ATS.derivation_initial initial_configurations2 step_relation2 G2 (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF))")
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   prefer 2
   apply(rule Sys2.sched_modification_preserves_derivation_initial)
         apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
         prefer 7
         apply(force)
        apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure2)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
       apply(rule AX_on_derivation_initial2)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(subgoal_tac "\<exists>dc'. derivation_bisimulation G1 G2 dc' (derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF)) dc n)")
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   prefer 2
   apply(rule_tac
      ?n.0="n+n'"
      in simulation_lift2)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(rule Sys2.derivation_append_preserves_derivation_initial_prime)
        apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure2)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
      apply(simp add: Sys2.map_unfixed_scheduler_DB_def maximum_of_domain_def)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(rule_tac
      t="ATS_SchedUF_DB.map_unfixed_scheduler_DB set_unfixed_scheduler_DB2 get_unfixed_scheduler_DB2 G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF)"
      and s="ATS_SchedUF_DB.replace_unfixed_scheduler_DB unfixed_scheduler_right_quotient2 extend_unfixed_scheduler2 set_unfixed_scheduler_DB2 get_unfixed_scheduler_DB2 G2 dh' sUF n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(simp (no_asm) add: Sys2.replace_unfixed_scheduler_DB_def)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(simp add: Sys2.map_unfixed_scheduler_DB_def maximum_of_domain_def)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply (metis AX_on_finite1)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'a)(*strict*)
  apply(rename_tac n'')
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(subgoal_tac "n''=n+n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF)) dc n"
      in AX_equal_length)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    prefer 2
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(rule Sys2.map_unfixed_scheduler_DB_preserves_maximum_of_domain)
        apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure2)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       apply(simp add: Sys2.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply (metis AX_on_derivation_initial2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(rule_tac
      x="derivation_drop dc' n"
      in exI)
  apply(rule_tac
      x="get_unfixed_scheduler_DB1 G1 dc' n"
      in exI)
  apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule AX_on_derivation_initial1)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule Sys1.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys1.AX_get_unfixed_scheduler_DB_closed)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_initial_belongs)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule AX_on_derivation_initial1)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(subgoal_tac "get_fixed_scheduler_DB1 G1 dh n = get_fixed_scheduler_DB1 G1 dc' n")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply (metis Sys2.replace_unfixed_scheduler_DB_def AX_2_bisimulation_compatible_with_replace_and_schedF2 le_refl)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   defer
   apply(rule context_conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="Sys1.get_scheduler_nth (derivation_drop dc' n) 0"
      and s="Sys1.get_scheduler_nth dc' n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys1.get_scheduler_nth_def derivation_drop_def get_configuration_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_drop_preserves_derivation)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_drop_preserves_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial1)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule Sys1.derivation_initial_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule_tac
      x="n'"
      in exI)
    apply(rule_tac
      t="n'"
      and s="(n+n')-n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_drop_makes_maximum_of_domain)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial1)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(subgoal_tac "(derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh n))) (get_unfixed_scheduler_DB1 G1 dc' n))) (derivation_drop dc' n) n) = dc'")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     prefer 2
     apply(rule AX_accept_id2)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp (no_asm) add: Sys2.replace_unfixed_scheduler_DB_def)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(subgoal_tac "derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh n))) (get_unfixed_scheduler_DB1 G1 dc' n))) (derivation_drop dc' n) n n = dc' n")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(thin_tac "derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh n))) (get_unfixed_scheduler_DB1 G1 dc' n))) (derivation_drop dc' n) n = dc'")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: derivation_append_def derivation_drop_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(case_tac "x>n")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(thin_tac "marking_condition2 G2 (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB unfixed_scheduler_right_quotient2 extend_unfixed_scheduler2 set_unfixed_scheduler_DB2 get_unfixed_scheduler_DB2 G2 dh' sUF n) dc n)")
   apply(simp add: derivation_append_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(subgoal_tac "n\<ge>x")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(clarsimp)
   apply(fold Sys2.replace_unfixed_scheduler_DB_def)
   apply(fold Sys1.replace_unfixed_scheduler_DB_def)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(thin_tac "marking_condition2 G2 (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n)")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(fold derivation_append_def)
   apply (metis AX_2_bisimulation_compatible_with_replace_and_schedF2)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      n="n+n'"
      in AX_bisimulation_compatible_with_unfixed_scheduler_extendable2)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB2 G2 (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n"
      and s="get_unfixed_scheduler_DB2 G2 (derivation_take (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n) n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys2.AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_append_preserves_derivation_initial)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_append_preserves_derivation)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
    apply(simp add: Sys2.map_unfixed_scheduler_DB_def)
    apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="derivation_take (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n"
      and s="Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n"
      and s="derivation_take ((Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) ) n"
      in ssubst)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule derivation_take_derivation_append_ignore)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
   apply(simp add: Sys2.map_unfixed_scheduler_DB_def)
   apply(clarsimp)
   apply(subgoal_tac "dh' x = None")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(rule Sys2.none_position_after_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB2 G2 (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) n"
      and s="sUF"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule Sys2.AX_replace_unfixed_scheduler_DB_sound)
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply (metis AX_TSstructure_rel_on_TSstructure2)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(force)
  done

theorem Nonblockingness_translation_rest2: "
  TSstructure_rel G1 G2
  \<Longrightarrow> Sys2.Nonblockingness_linear_restricted_DB G2
  \<Longrightarrow> Sys1.Nonblockingness_linear_restricted_DB G1"
  apply(simp add: Sys2.Nonblockingness_linear_restricted_DB_def Sys1.Nonblockingness_linear_restricted_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>dh'. derivation_bisimulation G1 G2 dh dh'")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule simulation_lift1)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh')(*strict*)
  apply(erule_tac
      x="dh'"
      in allE)
  apply(subgoal_tac "\<exists>n2. maximum_of_domain dh' n2")
   apply(rename_tac dh n dh')(*strict*)
   prefer 2
   apply(rule AX_on_finite2)
   apply(force)
  apply(rename_tac dh n dh')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n2)(*strict*)
  apply(erule_tac
      x="n2"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n dh' n2)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' n2)(*strict*)
    apply(rule AX_on_derivation_initial2)
    apply(force)
   apply(rename_tac dh n dh' n2)(*strict*)
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable1 AX_equal_length le_refl)
  apply(rename_tac dh n dh' n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' n2 dc sUF x)(*strict*)
  apply(subgoal_tac "n2=n")
   apply(rename_tac dh n dh' n2 dc sUF x)(*strict*)
   prefer 2
   apply (metis AX_equal_length)
  apply(rename_tac dh n dh' n2 dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable2 G2 (get_unfixed_scheduler_DB2 G2 dh' n)")
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   prefer 2
   apply (metis AX_bisimulation_compatible_with_unfixed_scheduler_extendable1 le_refl)
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(subgoal_tac "unfixed_scheduler_extendable1 G1 (get_unfixed_scheduler_DB1 G1 dh n)")
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   prefer 2
   apply (metis )
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   prefer 2
   apply(rule Sys2.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF x)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF x)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF x)(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF x)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
  apply(subgoal_tac "Sys2.derivation_initial G2 (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF))")
   apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
   prefer 2
   apply(rule Sys2.sched_modification_preserves_derivation_initial)
         apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
         prefer 7
         apply(force)
        apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure2)
        apply(force)
       apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
       apply(rule AX_on_derivation_initial2)
       apply(force)
      apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF x e c)(*strict*)
  apply(rename_tac n' e c)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(subgoal_tac "\<exists>dc'. derivation_bisimulation G1 G2 dc' (derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF)) dc n)")
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   prefer 2
   apply(rule_tac
      ?n.0="n+n'"
      in simulation_lift2)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(rule Sys2.derivation_append_preserves_derivation_initial_prime)
        apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
        apply(rule AX_TSstructure_rel_on_TSstructure2)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
      apply(simp add: Sys2.map_unfixed_scheduler_DB_def maximum_of_domain_def)
     apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
    apply(simp add: Sys2.map_unfixed_scheduler_DB_def maximum_of_domain_def)
   apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply (metis AX_on_finite1)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'a)(*strict*)
  apply(rename_tac n'')
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(subgoal_tac "n''=n+n'")
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF)) dc n"
      in AX_equal_length)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(rule Sys2.map_unfixed_scheduler_DB_preserves_maximum_of_domain)
       apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
       apply(rule AX_TSstructure_rel_on_TSstructure2)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' n'')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(rule_tac
      x="derivation_drop dc' n"
      in exI)
  apply(rule_tac
      x="get_unfixed_scheduler_DB1 G1 dc' n"
      in exI)
  apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule AX_on_derivation_initial1)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' n = Some (pair e c)")
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   prefer 2
   apply(rule Sys1.some_position_has_details_before_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys1.AX_get_unfixed_scheduler_DB_closed)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_initial_belongs)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure1)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule AX_on_derivation_initial1)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(subgoal_tac "get_fixed_scheduler_DB1 G1 dh n = get_fixed_scheduler_DB1 G1 dc' n")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply (metis Sys2.replace_unfixed_scheduler_DB_def AX_2_bisimulation_compatible_with_replace_and_schedF2 le_refl)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   defer
   apply(rule context_conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="ATS_Sched.get_scheduler_nth get_scheduler1 (derivation_drop dc' n) 0"
      and s="ATS_Sched.get_scheduler_nth get_scheduler1 dc' n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys1.get_scheduler_nth_def derivation_drop_def get_configuration_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys1.derivation_initial_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_drop_preserves_derivation)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys1.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_drop_preserves_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial1)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule Sys1.derivation_initial_belongs)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure1)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(rule AX_on_derivation_initial1)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule_tac
      x="n'"
      in exI)
    apply(rule_tac
      t="n'"
      and s="(n+n')-n"
      in ssubst)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys1.derivation_drop_makes_maximum_of_domain)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(subgoal_tac "Sys1.derivation_initial G1 dc'")
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply(simp add: Sys1.derivation_initial_def)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(rule AX_on_derivation_initial1)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(subgoal_tac "(derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh n))) (get_unfixed_scheduler_DB1 G1 dc' n))) (derivation_drop dc' n) n) = dc'")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     prefer 2
     apply(rule AX_accept_id2)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
     apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(subgoal_tac "derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh n))) (get_unfixed_scheduler_DB1 G1 dc' n))) (derivation_drop dc' n) n n = dc' n")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(thin_tac "derivation_append (Sys1.map_unfixed_scheduler_DB G1 dh (\<lambda>c. extend_unfixed_scheduler1 (the (unfixed_scheduler_right_quotient1 c (get_unfixed_scheduler_DB1 G1 dh n))) (get_unfixed_scheduler_DB1 G1 dc' n))) (derivation_drop dc' n) n = dc'")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: derivation_append_def derivation_drop_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
     apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
     apply(simp add: derivation_append_def derivation_drop_def)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(simp add: Sys1.replace_unfixed_scheduler_DB_def)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(case_tac "x>n")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(simp add: derivation_append_def derivation_drop_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
   apply(thin_tac "marking_condition2 G2 (derivation_append (Sys2.map_unfixed_scheduler_DB G2 dh' (\<lambda>c. extend_unfixed_scheduler2 (the (unfixed_scheduler_right_quotient2 c (get_unfixed_scheduler_DB2 G2 dh' n))) sUF)) dc n)")
   apply(simp add: derivation_append_def)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(subgoal_tac "n\<ge>x")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(clarsimp)
   apply(fold Sys1.replace_unfixed_scheduler_DB_def)
   apply(fold Sys2.replace_unfixed_scheduler_DB_def)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(thin_tac "marking_condition2 G2 (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n)")
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(subgoal_tac "get_fixed_scheduler_DB1 G1 dh x = get_fixed_scheduler_DB1 G1 dc' x \<and> Sys1.replace_unfixed_scheduler_DB G1 dh (get_unfixed_scheduler_DB1 G1 dc' n) n x = dc' x")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    prefer 2
    apply(rule Sys1.some_position_has_details_before_max_dom)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
      apply(rule Sys1.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(erule exE)+
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
   apply(fold derivation_append_def)
   apply(rule_tac
      dc="dc'"
      and dc'="dc"
      and sUF'="sUF"
      in AX_2_bisimulation_compatible_with_replace_and_schedF2)
          apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
          apply(force)
         apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
         apply(force)
        apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
        apply(force)
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
       apply(force)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x eb cb)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      n="n+n'"
      in AX_bisimulation_compatible_with_unfixed_scheduler_extendable2)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB2 G2 (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n"
      and s="get_unfixed_scheduler_DB2 G2 (derivation_take (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n) n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule Sys2.AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_TSstructure_rel_on_TSstructure2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_append_preserves_derivation_initial)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply (metis AX_TSstructure_rel_on_TSstructure2)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.derivation_append_preserves_derivation)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(force)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
    apply(simp add: Sys2.map_unfixed_scheduler_DB_def)
    apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule Sys2.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="derivation_take (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n"
      and s="Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) dc n) n"
      and s="derivation_take ((Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) ) n"
      in ssubst)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(rule derivation_take_derivation_append_ignore)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(rule ext)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: Sys2.replace_unfixed_scheduler_DB_def)
   apply(simp add: Sys2.map_unfixed_scheduler_DB_def)
   apply(clarsimp)
   apply(subgoal_tac "dh' x = None")
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(rule Sys2.none_position_after_max_dom)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca x)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule_tac
      t="get_unfixed_scheduler_DB2 G2 (Sys2.replace_unfixed_scheduler_DB G2 dh' sUF n) n"
      and s="sUF"
      in ssubst)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(rule Sys2.AX_replace_unfixed_scheduler_DB_sound)
       apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
       apply (metis AX_TSstructure_rel_on_TSstructure2)
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(force)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply(subgoal_tac "Sys2.derivation_initial G2 dh'")
      apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
      apply(simp add: Sys2.derivation_initial_def)
     apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
     apply (metis AX_on_derivation_initial2)
    apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
    apply(force)
   apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
   apply(force)
  apply(rename_tac dh n dh' dc sUF n' e c dc' ea ca)(*strict*)
  apply(force)
  done

theorem preservation_of_Nonblockingnessness: "
  TSstructure_rel G1 G2
  \<Longrightarrow>
  (Sys1.Nonblockingness_linear_DB G1 \<longleftrightarrow> Sys2.Nonblockingness_linear_DB G2)
  \<and> (Sys1.Nonblockingness_linear_restricted_DB G1 \<longleftrightarrow> Sys2.Nonblockingness_linear_restricted_DB G2)"
  apply(metis Nonblockingness_translation1 Nonblockingness_translation2 Nonblockingness_translation_rest1 Nonblockingness_translation_rest2)
  done

end

end
