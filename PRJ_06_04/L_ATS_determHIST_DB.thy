section {*L\_ATS\_determHIST\_DB*}
theory
  L_ATS_determHIST_DB

imports
  PRJ_06_04__ENTRY

begin

locale ATS_determHIST_DB =
  ATS_History
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
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
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect histories history_fragments empty_history empty_history_fragment set_history extend_history join_history_fragments get_history fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable get_fixed_scheduler_DB

context ATS_determHIST_DB begin

definition is_forward_edge_deterministicHist_DB_long :: "'TSstructure \<Rightarrow> bool" where
  "is_forward_edge_deterministicHist_DB_long G \<equiv> (
  \<forall>c d n. derivation_initial G d \<and> get_configuration(d n) = Some c
  \<longrightarrow> (\<forall>c1 c2 e1 e2 w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> step_relation G c e1 c1
  \<and> step_relation G c e2 c2
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> ((history_fragment_prefixes G w1 \<subseteq> history_fragment_prefixes G w2
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler_DB G (derivation_append d (der2 c e1 c1) n) (Suc n)))
  \<or> (history_fragment_prefixes G w2 \<subseteq> history_fragment_prefixes G w1
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler_DB G (derivation_append d (der2 c e2 c2) n) (Suc n)))
  \<or> (history_fragment_prefixes G w2 = history_fragment_prefixes G w1))
  \<longrightarrow> e1=e2))"

definition compatible_history_fragment_DB :: "
  'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> nat \<Rightarrow> 'conf \<Rightarrow> 'conf \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'label \<Rightarrow> bool"
  where
    "compatible_history_fragment_DB G d n c c1 c2 e1 e2 \<equiv>
  \<exists>w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> (let
  d1 = derivation_append d (der2 c e1 c1) n;
  d2 = derivation_append d (der2 c e2 c2) n;
  pw1 = history_fragment_prefixes G w1;
  pw2 = history_fragment_prefixes G w2;
  ext1 = fixed_scheduler_extendable G (get_fixed_scheduler_DB G d1 (Suc n));
  ext2 = fixed_scheduler_extendable G (get_fixed_scheduler_DB G d2 (Suc n))
  in
  ((pw1 \<subseteq> pw2 \<and> ext1) \<or> (pw2 \<subseteq> pw1 \<and> ext2) \<or> (pw1 = pw2)))"

definition is_forward_edge_deterministicHist_DB :: "'TSstructure \<Rightarrow> bool" where
  "is_forward_edge_deterministicHist_DB G \<equiv>
  \<forall>d n c.
  derivation_initial G d
  \<longrightarrow> get_configuration (d n) = Some c
  \<longrightarrow> (\<forall>c1 c2 e1 e2.
  step_relation G c e1 c1
  \<longrightarrow> step_relation G c e2 c2
  \<longrightarrow> compatible_history_fragment_DB G d n c c1 c2 e1 e2
  \<longrightarrow> e1 = e2)"

corollary is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long: "
  is_forward_edge_deterministicHist_DB G = is_forward_edge_deterministicHist_DB_long G"
  apply(simp add: is_forward_edge_deterministicHist_DB_def is_forward_edge_deterministicHist_DB_long_def Let_def compatible_history_fragment_DB_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(erule_tac
      x="d"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="c1"
      in allE)
   apply(erule_tac
      x="c2"
      in allE)
   apply(erule_tac
      x="e1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="w1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="w2"
      in allE)
   apply(erule impE)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d n c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w2"
      in allE)
  apply(clarsimp)
  apply(force)
  done

lemma is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long: "
  TSstructure G
  \<Longrightarrow> is_forward_edge_deterministic_accessible G
  \<Longrightarrow> is_forward_edge_deterministicHist_DB_long G"
  apply(simp add: is_forward_edge_deterministic_accessible_def is_forward_edge_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
  apply(simp add: get_accessible_configurations_def)
  done

definition is_forward_target_deterministicHist_DB_long :: "'TSstructure \<Rightarrow> bool" where
  "is_forward_target_deterministicHist_DB_long G \<equiv> (
  \<forall>c d n. derivation_initial G d \<and> get_configuration(d n) = Some c
  \<longrightarrow> (\<forall>c1 c2 e w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> step_relation G c e c1
  \<and> step_relation G c e c2
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> ((history_fragment_prefixes G w1 \<subseteq> history_fragment_prefixes G w2
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler_DB G (derivation_append d (der2 c e c1) n) (Suc n)))
  \<or> (history_fragment_prefixes G w2 \<subseteq> history_fragment_prefixes G w1
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler_DB G (derivation_append d (der2 c e c2) n) (Suc n)))
  \<or> (history_fragment_prefixes G w2 = history_fragment_prefixes G w1))
  \<longrightarrow> c1=c2))"

definition is_forward_target_deterministicHist_DB :: "'TSstructure \<Rightarrow> bool" where
  "is_forward_target_deterministicHist_DB G \<equiv>
  \<forall>d n c.
  derivation_initial G d
  \<longrightarrow> get_configuration (d n) = Some c
  \<longrightarrow> (\<forall>c1 c2 e.
  step_relation G c e c1
  \<longrightarrow> step_relation G c e c2
  \<longrightarrow> compatible_history_fragment_DB G d n c c1 c2 e e
  \<longrightarrow> c1 = c2)"

corollary is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long: "
is_forward_target_deterministicHist_DB G = is_forward_target_deterministicHist_DB_long G"
  apply(simp add: is_forward_target_deterministicHist_DB_def is_forward_target_deterministicHist_DB_long_def compatible_history_fragment_DB_def Let_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
   apply(erule_tac
      x="d"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="n"
      in allE)
   apply(erule_tac
      x="c"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="c1"
      in allE)
   apply(erule_tac
      x="c2"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="w1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="w2"
      in allE)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d n c c1 c2 e w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule impE)
   apply(rename_tac d n c c1 c2 e w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d n c c1 c2 e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="w1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="w2"
      in exI)
  apply(clarsimp)
  done

lemma is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_DB_long: "
  TSstructure G
  \<Longrightarrow> is_forward_target_deterministic_accessible G
  \<Longrightarrow> is_forward_target_deterministicHist_DB_long G"
  apply(simp add: is_forward_target_deterministic_accessible_def is_forward_target_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
  apply(simp add: get_accessible_configurations_def)
  done

definition is_forward_deterministicHist_DB :: "'TSstructure \<Rightarrow> bool" where
  "is_forward_deterministicHist_DB G \<equiv> is_forward_target_deterministicHist_DB_long G \<and> is_forward_edge_deterministicHist_DB_long G"

end

end
