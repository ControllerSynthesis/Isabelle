section {*L\_ATS\_Language*}
theory
  L_ATS_Language

imports
  L_ATS_Language0

begin

locale ATS_Language =
  ATS_Language0
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

assumes AX_effect_inclusion1: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> marking_condition G d
  \<Longrightarrow> marked_effect G d \<subseteq> unmarked_effect G d"

assumes AX_effect_inclusion2: "
  TSstructure G
  \<Longrightarrow> unmarked_language G \<subseteq> effects G"

assumes AX_marking_condition_implies_existence_of_effect: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> marking_condition G d
  \<Longrightarrow> marked_effect G d \<noteq> {}"

assumes AX_unmarked_effect_persists: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> unmarked_effect G (derivation_take d n) \<subseteq> unmarked_effect G d"

context ATS_Language
begin

lemma lang_inclusion: "
  TSstructure M
  \<Longrightarrow> marked_language M \<subseteq> unmarked_language M"
  apply(simp add: marked_language_def unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      A="marked_effect M d"
      in set_mp)
   apply(rename_tac x d)(*strict*)
   apply(rule AX_effect_inclusion1)
     apply(rename_tac x d)(*strict*)
     apply(auto)
  done

lemma Nonblockingness_branching_implies_non_empty_lang: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_branching G
  \<Longrightarrow> marked_language G = {}
  \<Longrightarrow> c \<in> initial_configurations G
  \<Longrightarrow> Q"
  apply(simp add: Nonblockingness_branching_def)
  apply(erule_tac
      x="der1 c"
      in allE)
  apply(subgoal_tac "derivation_initial G (der1 c) \<and> maximum_of_domain (der1 c) 0")
   apply(clarsimp)
   prefer 2
   apply(simp add: derivation_initial_def)
   apply(rule conjI)
    apply(rule der1_is_derivation)
   apply(simp add: maximum_of_domain_def der1_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(erule impE)
   apply(force)
  apply(clarsimp)
  apply(rename_tac dc x)(*strict*)
  apply(simp add: marked_language_def)
  apply(subgoal_tac "derivation_initial G (derivation_append (der1 c) dc 0)")
   apply(rename_tac dc x)(*strict*)
   prefer 2
   apply(rule derivation_append_preserves_derivation_initial)
     apply(rename_tac dc x)(*strict*)
     apply(force)
    apply(rename_tac dc x)(*strict*)
    apply(force)
   apply(rename_tac dc x)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac dc x)(*strict*)
     apply(simp add: derivation_initial_def)
    apply(rename_tac dc x)(*strict*)
    apply(force)
   apply(rename_tac dc x)(*strict*)
   apply(simp add: der1_def)
   apply(case_tac "dc 0")
    apply(rename_tac dc x)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_def derivation_append_fit_def)
   apply(rename_tac dc x a)(*strict*)
   apply(simp add: derivation_def derivation_append_fit_def)
   apply(case_tac a)
   apply(rename_tac dc x a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dc x option b)(*strict*)
   apply(case_tac option)
    apply(rename_tac dc x option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac dc x option b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dc x)(*strict*)
  apply(subgoal_tac "marked_effect G (derivation_append (der1 c) dc 0) \<noteq> {}")
   apply(rename_tac dc x)(*strict*)
   prefer 2
   apply(rule AX_marking_condition_implies_existence_of_effect)
     apply(rename_tac dc x)(*strict*)
     apply(force)
    apply(rename_tac dc x)(*strict*)
    apply(force)
   apply(rename_tac dc x)(*strict*)
   apply(force)
  apply(rename_tac dc x)(*strict*)
  apply(subgoal_tac "\<exists>x. x \<in> marked_effect G (derivation_append (der1 c) dc 0)")
   apply(rename_tac dc x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dc x)(*strict*)
  apply(thin_tac "marked_effect G (derivation_append (der1 c) dc 0)\<noteq>{}")
  apply(clarsimp)
  apply(rename_tac dc x xa)(*strict*)
  apply(erule_tac
      x="xa"
      in allE)
  apply(erule_tac
      x="derivation_append (der1 c) dc 0"
      in allE)
  apply(clarsimp)
  apply(simp add: derivation_initial_def)
  done

end

end
