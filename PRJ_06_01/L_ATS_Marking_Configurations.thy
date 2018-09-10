section {*L\_ATS\_Marking\_Configurations*}
theory
  L_ATS_Marking_Configurations

imports
  L_ATS_Language

begin

locale ATS_Marking_Configurations =
  ATS_Language
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event set"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect
    +

fixes marking_configurations :: "'TSstructure \<Rightarrow> 'conf set"
fixes marked_configuration_effect :: "'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'event set"
fixes unmarked_configuration_effect :: "'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'event set"

assumes AX_marking_condition_coincides_with_marking_configurations: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> marking_condition G d
  \<longleftrightarrow> (\<exists>i e c.
        d i = Some (pair e c)
        \<and> c \<in> marking_configurations G)"

assumes AX_marked_configuration_effect_coincides_with_marked_effect: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> marking_condition G (derivation_take d n)
  \<Longrightarrow> marked_effect G d
  = \<Union>{marked_configuration_effect G c| c. \<exists>i e.
        d i = Some (pair e c)
        \<and> c \<in> marking_configurations G}"

assumes AX_unmarked_configuration_effect_coincides_with_unmarked_effect: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> unmarked_effect G d
  = \<Union>{unmarked_configuration_effect G c| c. \<exists>i e.
        d i = Some (pair e c)}"

context ATS_Marking_Configurations
begin

lemma derivation_append_preserves_marking_condition: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> derivation_initial G (derivation_append d d' n)
  \<Longrightarrow> belongs G d
  \<Longrightarrow> belongs G d'
  \<Longrightarrow> marking_condition G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> marking_condition G (derivation_append d d' n)"
  apply(rule_tac
      t="marking_condition G (derivation_append d d' n)"
      and s="(\<exists>i e c. ((derivation_append d d' n) i = Some (pair e c)) \<and> c \<in> (marking_configurations G))"
      in ssubst)
   apply(rule AX_marking_condition_coincides_with_marking_configurations)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>i e c. (d i = Some (pair e c)) \<and> c \<in> (marking_configurations G)")
   prefer 2
   apply(rule_tac
      s="marking_condition G d"
      in subst)
    apply(rule AX_marking_condition_coincides_with_marking_configurations)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rule_tac
      d="d"
      in no_some_beyond_maximum_of_domain)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: derivation_initial_def)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(force)
  done

lemma marking_can_not_be_disabled: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> marking_condition G (derivation_take d n)
  \<Longrightarrow> marking_condition G d"
  apply(rule_tac
      t="marking_condition G d"
      in ssubst)
   apply(rule AX_marking_condition_coincides_with_marking_configurations)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      s="marking_condition G (derivation_take d n)"
      in subst)
    apply(rule AX_marking_condition_coincides_with_marking_configurations)
     apply(force)
    apply(rule derivation_take_preserves_derivation_initial)
    apply(force)
   apply(force)
  apply(thin_tac "marking_condition G (derivation_take d n)")
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: derivation_take_def)
  apply(case_tac "i\<le>n")
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(force)
  done

lemma marked_effect_persists: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> marking_condition G (derivation_take d n)
  \<Longrightarrow> marked_effect G (derivation_take d n) \<subseteq> marked_effect G d"
  apply(rule_tac
      t="marked_effect G SSd" for SSd
      in ssubst)
   apply(rule AX_marked_configuration_effect_coincides_with_marked_effect)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="marked_effect G SSd" for SSd
      in ssubst)
   apply(rule_tac
      n="n"
      in AX_marked_configuration_effect_coincides_with_marked_effect)
     apply(force)
    apply(rule derivation_take_preserves_derivation_initial)
    apply(force)
   apply (metis derivation_initial_is_derivation derivation_take_def derivation_take_id_prime derivation_take_preserves_derivation derivation_take_twice)
  apply(simp (no_asm))
  apply(clarsimp)
  apply(rename_tac x c i e)(*strict*)
  apply(simp add: derivation_take_def)
  apply(case_tac "i\<le>n")
   apply(rename_tac x c i e)(*strict*)
   apply(force)
  apply(rename_tac x c i e)(*strict*)
  apply(force)
  done

lemma unmarked_effect_persists: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> unmarked_effect G (derivation_take d n) \<subseteq> unmarked_effect G d"
  apply(rule_tac
      t="unmarked_effect G d"
      in ssubst)
   apply(rule AX_unmarked_configuration_effect_coincides_with_unmarked_effect)
    apply(force)
   apply(force)
  apply(rule_tac
      t="unmarked_effect G (derivation_take d n)"
      in ssubst)
   apply(rule AX_unmarked_configuration_effect_coincides_with_unmarked_effect)
    apply(force)
   apply(rule derivation_take_preserves_derivation_initial)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x c i e)(*strict*)
  apply(simp add: derivation_take_def)
  apply(case_tac "i\<le>n")
   apply(rename_tac x c i e)(*strict*)
   apply(force)
  apply(rename_tac x c i e)(*strict*)
  apply(force)
  done

definition marking_relevant_step_labels :: "
  'TSstructure
  \<Rightarrow> 'label set"
  where
    "marking_relevant_step_labels G \<equiv>
  {e.
    \<exists>d n c.
      derivation_initial G d
      \<and> d n = Some (pair (Some e) c)
      \<and> (\<exists>k\<ge>n. \<exists>e c. d k = Some (pair e c) \<and> c \<in> marking_configurations G)}"

end

end
