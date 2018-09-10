section {*L\_ATS\_determHIST\_SB*}
theory
  L_ATS_determHIST_SB

imports
  PRJ_06_04__ENTRY

begin

locale ATS_determHIST_SB =
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
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect histories history_fragments empty_history empty_history_fragment set_history extend_history join_history_fragments get_history fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable get_fixed_scheduler
    +

assumes AX_history_no_mod_after_nonextendable_fixed_sched: "
  TSstructure G
  \<Longrightarrow> \<not> fixed_scheduler_extendable G (get_fixed_scheduler c)
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> step_relation G c e c'
  \<Longrightarrow> get_history c = get_history c'"

context ATS_determHIST_SB begin

lemma history_no_mod_after_nonextendable_fixed_sched_lift: "
  TSstructure G
  \<Longrightarrow> \<not> fixed_scheduler_extendable G (get_fixed_scheduler c)
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> get_configuration (d x) = Some c
  \<Longrightarrow> get_configuration (d y) = Some c'
  \<Longrightarrow> x\<le>y
  \<Longrightarrow> get_history c = get_history c'"
  apply(induct "y-x" arbitrary: x c)
   apply(rename_tac x c)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa x c)(*strict*)
  apply(erule_tac
      x="Suc x"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac xa x c)(*strict*)
   prefer 2
   apply(rule_tac
      m="y"
      in step_detail_before_some_position)
     apply(rename_tac xa x c)(*strict*)
     apply(force)
    apply(rename_tac xa x c)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "d y")
     apply(rename_tac xa x c)(*strict*)
     apply(clarsimp)
    apply(rename_tac xa x c a)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa x c)(*strict*)
   apply(force)
  apply(rename_tac xa x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x c e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac xa x c e1 e2 c2)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac xa x c e1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa x c e1 e2 c2)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac xa x c e1 e2 c2)(*strict*)
   apply (metis belongs_configurations AX_fixed_scheduler_extendable_translates_backwards)
  apply(rename_tac xa x c e1 e2 c2)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac xa x c e1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa x c e1 e2 c2)(*strict*)
  apply (metis AX_history_no_mod_after_nonextendable_fixed_sched belongs_configurations)
  done

definition compatible_history_fragment_SB :: "
  'TSstructure
  \<Rightarrow> 'conf
  \<Rightarrow> 'conf
  \<Rightarrow> 'conf
  \<Rightarrow> bool"
  where
    "compatible_history_fragment_SB G c c1 c2 \<equiv>
  \<exists>w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> (let
  pw1 = history_fragment_prefixes G w1;
  pw2 = history_fragment_prefixes G w2;
  ext1 = fixed_scheduler_extendable G (get_fixed_scheduler c1);
  ext2 = fixed_scheduler_extendable G (get_fixed_scheduler c2)
  in
  ((pw1 \<subseteq> pw2 \<and> ext1) \<or> (pw2 \<subseteq> pw1 \<and> ext2) \<or> (pw1 = pw2)))"

definition compatible_history_fragment_SB2 :: "
  'TSstructure
  \<Rightarrow> 'conf
  \<Rightarrow> 'conf
  \<Rightarrow> 'conf
  \<Rightarrow> bool"
  where
    "compatible_history_fragment_SB2 G c c1 c2 \<equiv>
  \<exists>w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> (let
  pw1 = history_fragment_prefixes G w1;
  pw2 = history_fragment_prefixes G w2;
  ext1 = fixed_scheduler_extendable G (get_fixed_scheduler c1);
  ext2 = fixed_scheduler_extendable G (get_fixed_scheduler c2)
  in
  ((pw1 \<subseteq> pw2 \<and> ext1) \<or> (pw2 \<subseteq> pw1 \<and> ext2) \<or> (pw1 = pw2 \<and> ext1 = ext2)))"

definition is_forward_edge_deterministicHist_SB2 :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_edge_deterministicHist_SB2 G \<equiv>
  \<forall>c \<in> get_accessible_configurations G. \<forall>c1 c2 e1 e2.
  step_relation G c e1 c1
  \<longrightarrow> step_relation G c e2 c2
  \<longrightarrow> compatible_history_fragment_SB2 G c c1 c2
  \<longrightarrow> e1 = e2"

definition is_forward_edge_deterministicHist_SB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_edge_deterministicHist_SB G \<equiv>
  \<forall>c \<in> get_accessible_configurations G. \<forall>c1 c2 e1 e2.
  step_relation G c e1 c1
  \<longrightarrow> step_relation G c e2 c2
  \<longrightarrow> compatible_history_fragment_SB G c c1 c2
  \<longrightarrow> e1 = e2"

definition is_forward_edge_deterministicHist_SB_long :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_edge_deterministicHist_SB_long G \<equiv> (\<forall>c\<in> (get_accessible_configurations G). \<forall>c1 c2 e1 e2 w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> step_relation G c e1 c1
  \<and> step_relation G c e2 c2
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> ((history_fragment_prefixes G w1 \<subseteq> history_fragment_prefixes G w2
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler c1))
  \<or> (history_fragment_prefixes G w2 \<subseteq> history_fragment_prefixes G w1
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler c2))
  \<or> (history_fragment_prefixes G w2 = history_fragment_prefixes G w1))
  \<longrightarrow> e1=e2)"

lemma is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_SB: "
  TSstructure G
  \<Longrightarrow> is_forward_edge_deterministic_accessible G
  \<Longrightarrow> is_forward_edge_deterministicHist_SB G"
  apply(simp add: is_forward_edge_deterministic_accessible_def)
  apply(simp add: is_forward_edge_deterministicHist_SB_def)
  done

corollary is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long: "
  is_forward_edge_deterministicHist_SB G
  = is_forward_edge_deterministicHist_SB_long G"
  apply(simp add: is_forward_edge_deterministicHist_SB_long_def is_forward_edge_deterministicHist_SB_def compatible_history_fragment_SB_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac c c1 c2 e1 e2 w1 w2)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w1 w2)(*strict*)
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
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2 w1 w2)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 w1 w2)(*strict*)
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
  apply(simp add: Let_def)
  apply(force)
  done

lemma is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_SB_long: "
  TSstructure G
  \<Longrightarrow> is_forward_edge_deterministic_accessible G
  \<Longrightarrow> is_forward_edge_deterministicHist_SB_long G"
  apply(simp add: is_forward_edge_deterministic_accessible_def is_forward_edge_deterministicHist_SB_long_def)
  apply(clarsimp)
  done

definition is_forward_target_deterministicHist_SB_long :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_target_deterministicHist_SB_long G \<equiv>
  \<forall>c\<in> (get_accessible_configurations G). \<forall>c1 c2 e w1 w2.
  w1 \<in> history_fragments G
  \<and> w2 \<in> history_fragments G
  \<and> step_relation G c e c1
  \<and> step_relation G c e c2
  \<and> get_history c1 = extend_history (get_history c) w1
  \<and> get_history c2 = extend_history (get_history c) w2
  \<and> ((history_fragment_prefixes G w1 \<subseteq> history_fragment_prefixes G w2
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler c1))
  \<or> (history_fragment_prefixes G w2 \<subseteq> history_fragment_prefixes G w1
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler c2))
  \<or> (history_fragment_prefixes G w2 = history_fragment_prefixes G w1))
  \<longrightarrow> c1=c2"

definition is_forward_target_deterministicHist_SB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_target_deterministicHist_SB G \<equiv>
  \<forall>c \<in> get_accessible_configurations G. \<forall>c1 c2 e.
  step_relation G c e c1
  \<longrightarrow> step_relation G c e c2
  \<longrightarrow> compatible_history_fragment_SB G c c1 c2
  \<longrightarrow> c1 = c2"

corollary is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long: "
  is_forward_target_deterministicHist_SB G
  = is_forward_target_deterministicHist_SB_long G"
  apply(simp add: is_forward_target_deterministicHist_SB_long_def is_forward_target_deterministicHist_SB_def compatible_history_fragment_SB_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e w1 w2)(*strict*)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac c c1 c2 e w1 w2)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac c c1 c2 e w1 w2)(*strict*)
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
  apply(rename_tac c c1 c2 e w1 w2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c c1 c2 e w1 w2)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac c c1 c2 e w1 w2)(*strict*)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e w1 w2)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="w1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="w2"
      in exI)
  apply(clarsimp)
  done

lemma is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long: "
  TSstructure G
  \<Longrightarrow> is_forward_target_deterministic_accessible G
  \<Longrightarrow> is_forward_target_deterministicHist_SB_long G"
  apply(simp add: is_forward_target_deterministic_accessible_def is_forward_target_deterministicHist_SB_long_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e w1 w2)(*strict*)
  apply(force)
  done

definition is_forward_deterministicHist_SB :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_deterministicHist_SB G \<equiv> is_forward_target_deterministicHist_SB_long G \<and> is_forward_edge_deterministicHist_SB_long G"

lemma is_forward_deterministicHist_derivations_coincide: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> derivation_initial G d2
  \<Longrightarrow> is_forward_deterministicHist_SB G
  \<Longrightarrow> d1 x = d2 y
  \<Longrightarrow> d1 (x+n) \<noteq> None
  \<Longrightarrow> d2 (y+m) \<noteq> None
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> d1 (x+n) = l
  \<Longrightarrow> d2 (y+n) = r
  \<Longrightarrow> \<exists>hf\<in> history_fragments G. extend_history (get_history (the(get_configuration(d1(x+n))))) hf = get_history(the(get_configuration(d2(y+m))))
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler (the(get_configuration(d1(x+n)))))
  \<Longrightarrow> l=r"
  apply(rule_tac
      t="l"
      and s="d1 (x+n)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="r"
      and s="d2 (y+n)"
      in ssubst)
   apply(force)
  apply(thin_tac "d1 (x+n) = l")
  apply(thin_tac "d2 (y+n) = r")
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf ya yaa)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (x+n) = Some (pair e1 c1) \<and> d1 (Suc (x+n)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac n hf ya yaa)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (x+n)"
      in step_detail_before_some_position)
     apply(rename_tac n hf ya yaa)(*strict*)
     apply (metis derivation_initial_is_derivation)
    apply(rename_tac n hf ya yaa)(*strict*)
    apply(force)
   apply(rename_tac n hf ya yaa)(*strict*)
   apply(force)
  apply(rename_tac n hf ya yaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf ya e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (y+n) = Some (pair e1 c1) \<and> d2 (Suc (y+n)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac n hf ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="(y+m)"
      in step_detail_before_some_position)
     apply(rename_tac n hf ya e1 e2 c1 c2)(*strict*)
     apply (metis derivation_initial_is_derivation)
    apply(rename_tac n hf ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n hf ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n hf ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf ya e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac ya)
  apply(rename_tac n hf ya e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 x = Some (pair e c)")
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
   prefer 2
   apply(rule_tac
      M="G"
      in pre_some_position_is_some_position)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
     apply (metis derivation_initial_is_derivation)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
   apply(force)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
  apply(subgoal_tac "c \<in> configurations G")
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   prefer 2
   apply(rule belongs_configurations)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
    apply(rule derivation_initial_belongs)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
     apply(force)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   apply(force)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
  apply(subgoal_tac "c1 \<in> configurations G")
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in stays_in_configuration)
        apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
        apply(force)
       apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
       apply (metis derivation_initial_is_derivation)
      apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
     apply(force)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   apply(force)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
  apply(subgoal_tac "c1a \<in> configurations G")
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="y"
      and d="d2"
      in stays_in_configuration)
        apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
        apply(force)
       apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
       apply (metis derivation_initial_is_derivation)
      apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
      apply(force)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
     apply(force)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   apply(force)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
  apply(subgoal_tac "\<exists>hf\<in> history_fragments G. get_history c2 = extend_history (get_history c1) hf")
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   prefer 2
   apply(rule AX_steps_extend_history)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
     apply(force)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
   apply(force)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
   apply(rule_tac
      x="join_history_fragments hfa hf"
      in bexI)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
    apply(rule AX_extend_history_add)
         apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
         apply(force)
        apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
        prefer 4
        apply(force)
       apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
      apply(rule AX_get_history_closed)
       apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
   apply(rule AX_join_history_fragments_closed)
     apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
    apply(force)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
   apply(force)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
   apply (metis AX_fixed_scheduler_extendable_translates_backwards)
  apply(rename_tac n hf e1 e2 c1 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
  apply(subgoal_tac "\<exists>hf\<in> history_fragments G. get_history c2 = extend_history (get_history c1a) hf")
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
   prefer 2
   apply(rule AX_steps_extend_history)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
   apply(force)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb)(*strict*)
  apply(subgoal_tac "\<exists>hf\<in> history_fragments G. get_history c2a = extend_history (get_history c1a) hf")
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb)(*strict*)
   prefer 2
   apply(rule AX_steps_extend_history)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb)(*strict*)
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb)(*strict*)
   apply(force)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
  apply(subgoal_tac "c1a \<in> get_accessible_configurations G")
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   prefer 2
   apply(simp add: get_accessible_configurations_def)
   apply(rule_tac
      x="d1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="x+n"
      in exI)
   apply(simp add: get_configuration_def)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
  apply(subgoal_tac "b \<in> configurations G")
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   prefer 2
   apply(rule_tac
      m="y+n"
      and d="d2"
      in stays_in_configuration)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
       apply (metis derivation_initial_is_derivation)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   apply(force)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
  apply(subgoal_tac "c2a \<in> configurations G")
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   prefer 2
   apply(rule_tac
      m="y"
      and d="d2"
      in stays_in_configuration)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
       apply (metis derivation_initial_is_derivation)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   apply(force)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
  apply(subgoal_tac "\<exists>hf\<in> history_fragments G. get_history b = extend_history (get_history c2a) hf")
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc (y+n)"
      and m="m-Suc n"
      and d="d2"
      in steps_extend_history_derivation)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
      apply (metis derivation_initial_is_derivation)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(simp add: is_forward_deterministicHist_SB_def is_forward_edge_deterministicHist_SB_long_def)
   apply(clarsimp)
   apply(erule_tac
      x="c1a"
      in ballE)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(erule_tac
      x="c2"
      in allE)
   apply(erule_tac
      x="c2a"
      in allE)
   apply(erule_tac
      x="e2"
      in allE)
   apply(erule_tac
      x="e2a"
      in allE)
   apply(erule impE)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="hfb"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="hfc"
      in exI)
   apply(rule conjI)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(subgoal_tac "history_fragment_prefixes G hfc \<subseteq> history_fragment_prefixes G hfb \<or> history_fragment_prefixes G hfb \<subseteq> history_fragment_prefixes G hfc")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    apply(subgoal_tac "history_fragment_prefixes G hfc \<subset> history_fragment_prefixes G hfb \<longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler c2a)")
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    apply(thin_tac "history_fragment_prefixes G hfc \<subseteq> history_fragment_prefixes G hfb \<or> history_fragment_prefixes G hfb \<subseteq> history_fragment_prefixes G hfc")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    prefer 2
    apply(simp add: history_fragment_prefixes_def)
    apply(clarsimp)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
    apply(subgoal_tac "hfa=(join_history_fragments xa hf'')")
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
     prefer 2
     apply(rule_tac
      ?h="get_history c1a"
      and ?h'="extend_history (get_history c1a) hfa"
      in AX_join_history_fragments_injective)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
         apply(rule AX_get_history_closed)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
    apply(clarsimp)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(subgoal_tac "(\<exists>hf\<in> history_fragments G. join_history_fragments xa hf = join_history_fragments xaa hf''a) \<or> (\<exists>hf\<in> history_fragments G. join_history_fragments (join_history_fragments xaa hf''a) hf = xa)")
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     prefer 2
     apply(rule_tac
      ?hf2.0="join_history_fragments hf'' hf"
      and ?hf4.0="hfd"
      in AX_mutual_prefix)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(rule AX_join_history_fragments_closed)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule sym)
     apply(rule_tac
      h="get_history c1a"
      in AX_join_history_fragments_injective)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(rule AX_get_history_closed)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(rule AX_join_history_fragments_closed)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule_tac
      t="extend_history (get_history c1a) (join_history_fragments (join_history_fragments xaa hf''a) hfd)"
      and s="extend_history (extend_history (get_history c1a) (join_history_fragments xaa hf''a)) hfd"
      in ssubst)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_extend_history_add)
           apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
           apply(force)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          prefer 4
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         prefer 4
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(rule AX_get_history_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule_tac
      t="extend_history (get_history c1a) (join_history_fragments xa (join_history_fragments hf'' hf))"
      and s="extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf"
      in ssubst)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule_tac
      t="extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf"
      and s="extend_history (get_history c1a) (join_history_fragments (join_history_fragments xa hf'') hf)"
      in ssubst)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule sym)
      apply(rule AX_extend_history_add)
           apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
           apply(force)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          prefer 4
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         prefer 4
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(rule AX_get_history_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule_tac
      t="join_history_fragments xa (join_history_fragments hf'' hf)"
      and s="join_history_fragments (join_history_fragments xa hf'') hf"
      in ssubst)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule sym)
     apply(rule AX_join_history_fragments_asso)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(clarsimp)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(rule_tac
      x="join_history_fragments (join_history_fragments hf''a hfa) hf''"
      in bexI)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(rule_tac
      t="join_history_fragments (join_history_fragments xa hf''a) hfa"
      and s="join_history_fragments xa (join_history_fragments hf''a hfa)"
      in ssubst)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(rule AX_join_history_fragments_asso)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(rule sym)
     apply(rule AX_join_history_fragments_asso)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(rule AX_join_history_fragments_closed)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(rule AX_join_history_fragments_closed)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(simp add: history_fragment_prefixes_def)
   apply(rule impI)
   apply(subgoal_tac "hfc \<noteq> hfb")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(clarsimp)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
   apply(subgoal_tac "hfc \<in> {hf' \<in> history_fragments G. \<exists>hf''a\<in> history_fragments G. join_history_fragments hf' hf''a = join_history_fragments xa hf''}")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
    prefer 2
    apply(rule_tac
      A="{hf' \<in> history_fragments G. \<exists>hf''\<in> history_fragments G. join_history_fragments hf' hf'' = hfc}"
      in set_mp)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
    apply(simp (no_asm))
    apply(rule conjI)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
     apply(force)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
    apply(rule_tac
      x="empty_history_fragment G"
      in bexI)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
     apply (metis AX_join_history_fragments_empty1)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
    apply (metis AX_empty_history_fragment_is_history_fragment)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
   apply(clarsimp)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
   apply(subgoal_tac "hfd = empty_history_fragment G")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
    apply(clarsimp)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(thin_tac "{hf' \<in> history_fragments G. \<exists>hf''\<in> history_fragments G. join_history_fragments hf' hf'' = hfc} \<subseteq> {hf' \<in> history_fragments G. \<exists>hf''a\<in> history_fragments G. join_history_fragments hf' hf''a = join_history_fragments xa hf''}")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(subgoal_tac "hfc = join_history_fragments (join_history_fragments xa hf'') hf")
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule_tac
      h="get_history c1a"
      and h'="extend_history (extend_history (get_history c1a) hfc) (empty_history_fragment G)"
      in AX_join_history_fragments_injective)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
         apply (metis AX_get_history_closed)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
        apply (metis AX_join_history_fragments_closed)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
      apply(rule_tac
      t="extend_history (get_history c1a) (join_history_fragments (join_history_fragments xa hf'') hf)"
      and s="extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf"
      in ssubst)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
       apply(rule AX_extend_history_add)
            apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
            apply(force)
           apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
           prefer 4
           apply(force)
          apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
          apply (metis AX_get_history_closed)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
     apply (metis AX_get_history_closed AX_extend_history_empty1)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(thin_tac "extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf = extend_history (extend_history (get_history c1a) hfc) (empty_history_fragment G)")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(rule_tac
      x="join_history_fragments hf'' hf"
      in bexI)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
     apply (metis AX_join_history_fragments_asso)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply (metis AX_join_history_fragments_closed)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
   apply(subgoal_tac "get_history c2a = get_history b")
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "join_history_fragments hfc hfd = hfc")
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
     apply (metis AX_get_history_closed AX_extend_history_empty2)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
    apply (metis AX_get_history_closed AX_join_history_fragments_empty1 AX_extend_history_empty2)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
   apply(rule_tac
      x="Suc(y+n)"
      and y="y+m"
      and d="d2"
      in history_no_mod_after_nonextendable_fixed_sched_lift)
         apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
       apply (metis derivation_initial_is_derivation)
      apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
      apply (metis derivation_initial_belongs)
     apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
   apply(force)
  apply(rename_tac n hf e2 c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(simp add: is_forward_deterministicHist_SB_def is_forward_target_deterministicHist_SB_long_def)
  apply(clarsimp)
  apply(erule_tac
      x="c1a"
      in ballE)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule_tac
      x="c2a"
      in allE)
  apply(erule impE)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(rule_tac
      x="e2a"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="hfb"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="hfc"
      in exI)
  apply(rule conjI)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(subgoal_tac "history_fragment_prefixes G hfc \<subseteq> history_fragment_prefixes G hfb \<or> history_fragment_prefixes G hfb \<subseteq> history_fragment_prefixes G hfc")
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   prefer 2
   apply(simp add: history_fragment_prefixes_def)
   apply(clarsimp)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
   apply(subgoal_tac "hfa=(join_history_fragments xa hf'')")
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
    prefer 2
    apply(rule_tac
      ?h="get_history c1a"
      and ?h'="extend_history (get_history c1a) hfa"
      in AX_join_history_fragments_injective)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
        apply(rule AX_get_history_closed)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
    apply(force)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfd xa xaa hf'' hf''a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
   apply(subgoal_tac "(\<exists>hf\<in> history_fragments G. join_history_fragments xa hf = join_history_fragments xaa hf''a) \<or> (\<exists>hf\<in> history_fragments G. join_history_fragments (join_history_fragments xaa hf''a) hf = xa)")
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    prefer 2
    apply(rule_tac
      ?hf2.0="join_history_fragments hf'' hf"
      and ?hf4.0="hfd"
      in AX_mutual_prefix)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(rule sym)
    apply(rule_tac
      h="get_history c1a"
      in AX_join_history_fragments_injective)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(rule AX_get_history_closed)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_join_history_fragments_closed)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(rule_tac
      t="extend_history (get_history c1a) (join_history_fragments (join_history_fragments xaa hf''a) hfd)"
      and s="extend_history (extend_history (get_history c1a) (join_history_fragments xaa hf''a)) hfd"
      in ssubst)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule AX_extend_history_add)
          apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         prefer 4
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        prefer 4
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_get_history_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(rule_tac
      t="extend_history (get_history c1a) (join_history_fragments xa (join_history_fragments hf'' hf))"
      and s="extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf"
      in ssubst)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(rule_tac
      t="extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf"
      and s="extend_history (get_history c1a) (join_history_fragments (join_history_fragments xa hf'') hf)"
      in ssubst)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(rule sym)
     apply(rule AX_extend_history_add)
          apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
          apply(force)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
         prefer 4
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        prefer 4
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(rule AX_get_history_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(rule AX_join_history_fragments_closed)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(rule_tac
      t="join_history_fragments xa (join_history_fragments hf'' hf)"
      and s="join_history_fragments (join_history_fragments xa hf'') hf"
      in ssubst)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(rule sym)
    apply(rule AX_join_history_fragments_asso)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
    apply(force)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa xaa hf'' hf''a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
   apply(rule_tac
      x="join_history_fragments (join_history_fragments hf''a hfa) hf''"
      in bexI)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(rule_tac
      t="join_history_fragments (join_history_fragments xa hf''a) hfa"
      and s="join_history_fragments xa (join_history_fragments hf''a hfa)"
      in ssubst)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(rule AX_join_history_fragments_asso)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(rule sym)
    apply(rule AX_join_history_fragments_asso)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(rule AX_join_history_fragments_closed)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(force)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
   apply(rule AX_join_history_fragments_closed)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(rule AX_join_history_fragments_closed)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
    apply(force)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfd xa hf'' hf''a hfa)(*strict*)
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(subgoal_tac "history_fragment_prefixes G hfc \<subset> history_fragment_prefixes G hfb \<longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler c2a)")
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(thin_tac "history_fragment_prefixes G hfc \<subseteq> history_fragment_prefixes G hfb \<or> history_fragment_prefixes G hfb \<subseteq> history_fragment_prefixes G hfc")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(simp add: history_fragment_prefixes_def)
  apply(rule impI)
  apply(subgoal_tac "hfc \<noteq> hfb")
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfb hfc hfd)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply(subgoal_tac "hfc \<in> {hf' \<in> history_fragments G. \<exists>hf''a\<in> history_fragments G. join_history_fragments hf' hf''a = join_history_fragments xa hf''}")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  prefer 2
  apply(rule_tac
    A="{hf' \<in> history_fragments G. \<exists>hf''\<in> history_fragments G. join_history_fragments hf' hf'' = hfc}"
    in set_mp)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply(simp (no_asm))
  apply(rule conjI)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply(rule_tac
    x="empty_history_fragment G"
    in bexI)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply (metis AX_join_history_fragments_empty1)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply (metis AX_empty_history_fragment_is_history_fragment)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'')(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(subgoal_tac "hfd = empty_history_fragment G")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply(thin_tac "{hf' \<in> history_fragments G. \<exists>hf''\<in> history_fragments G. join_history_fragments hf' hf'' = hfc} \<subseteq> {hf' \<in> history_fragments G. \<exists>hf''a\<in> history_fragments G. join_history_fragments hf' hf''a = join_history_fragments xa hf''}")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply(subgoal_tac "hfc = join_history_fragments (join_history_fragments xa hf'') hf")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  prefer 2
  apply(rule sym)
  apply(rule_tac
    h="get_history c1a"
    and h'="extend_history (extend_history (get_history c1a) hfc) (empty_history_fragment G)"
    in AX_join_history_fragments_injective)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
       apply(force)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
      apply (metis AX_get_history_closed)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
     apply (metis AX_join_history_fragments_closed)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(force)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
   apply(rule_tac
    t="extend_history (get_history c1a) (join_history_fragments (join_history_fragments xa hf'') hf)"
    and s="extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf"
    in ssubst)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(rule AX_extend_history_add)
         apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
         apply(force)
        apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
        prefer 4
        apply(force)
       apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
       apply (metis AX_get_history_closed)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
      apply (metis)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
    apply(force)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
   apply(force)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply (metis AX_get_history_closed AX_extend_history_empty1)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply(thin_tac "extend_history (extend_history (get_history c1a) (join_history_fragments xa hf'')) hf = extend_history (extend_history (get_history c1a) hfc) (empty_history_fragment G)")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply(rule_tac
    x="join_history_fragments hf'' hf"
    in bexI)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply (metis AX_join_history_fragments_asso)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc xa hf'' hf''a)(*strict*)
  apply (metis AX_join_history_fragments_closed)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(subgoal_tac "get_history c2a = get_history b")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "join_history_fragments hfc hfd = hfc")
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply (metis AX_get_history_closed AX_extend_history_empty2)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply (metis AX_get_history_closed AX_join_history_fragments_empty1 AX_extend_history_empty2)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(rule_tac
    x="Suc(y+n)"
    and y="y+m"
    and d="d2"
    in history_no_mod_after_nonextendable_fixed_sched_lift)
      apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
      apply(force)
     apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
     apply(force)
    apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
    apply (metis derivation_initial_is_derivation)
   apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
   apply (metis derivation_initial_belongs)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac n hf c2 e1a e2a c1a c2a option b e c hfa hfc hfd xa hf'' hf''a)(*strict*)
  apply(force)
  done

lemma same_steps_for_compatible_histories_hlp: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> derivation_initial G d2
  \<Longrightarrow> is_forward_deterministicHist_SB G
  \<Longrightarrow> d1 x = d2 y
  \<Longrightarrow> d1 (x + n) \<noteq> None
  \<Longrightarrow> d2 (y + m) \<noteq> None
  \<Longrightarrow> n \<le> m
  \<Longrightarrow> d1 (x + n) = l
  \<Longrightarrow> d2 (y + n) = r
  \<Longrightarrow> \<exists>hf\<in> history_fragments G.
      extend_history (get_history (the (get_configuration (d1 (x + n))))) hf =
      get_history (the (get_configuration (d2 (y + m))))
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler (the(get_configuration(d1(x+n)))))
  \<Longrightarrow> k\<le>n
  \<Longrightarrow> drop x (get_labels d1 (x+k)) = drop y (get_labels d2 (y+k)) \<and> (\<forall>i\<le>k. d1 (x+i) = d2 (y+i))"
  apply(induct k)
   apply(clarsimp)
   apply(rename_tac hf ya yaa)(*strict*)
   apply (metis Nat.add_0_right get_labelsEmpty get_labels_derivation_drop)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k hf ya yaa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 (Suc (x+k)) = Some (pair (Some e) c)")
   apply(rename_tac k hf ya yaa)(*strict*)
   prefer 2
   apply(rule_tac
      m="x+n"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac k hf ya yaa)(*strict*)
      apply(rule derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac k hf ya yaa)(*strict*)
     apply(force)
    apply(rename_tac k hf ya yaa)(*strict*)
    apply(force)
   apply(rename_tac k hf ya yaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac k hf ya yaa)(*strict*)
  apply(subgoal_tac "d1 (x+Suc k) = d2 (y+Suc k)")
   apply(rename_tac k hf ya yaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k hf ya yaa e c)(*strict*)
   apply(rule conjI)
    apply(rename_tac k hf ya yaa e c)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac k hf ya yaa e c i)(*strict*)
    apply(case_tac "i=Suc k")
     apply(rename_tac k hf ya yaa e c i)(*strict*)
     apply(clarsimp)
    apply(rename_tac k hf ya yaa e c i)(*strict*)
    apply(clarsimp)
   apply(rename_tac k hf ya yaa e c)(*strict*)
   apply(rule_tac
      t="get_labels d1 (Suc (x + k))"
      and s="get_labels d1 (x + k)@[Some e]"
      in ssubst)
    apply(rename_tac k hf ya yaa e c)(*strict*)
    apply (metis derivation_initial_is_derivation get_labels_drop_last)
   apply(rename_tac k hf ya yaa e c)(*strict*)
   apply(rule_tac
      t="get_labels d2 (Suc (y + k))"
      and s="get_labels d2 (y + k)@[Some e]"
      in ssubst)
    apply(rename_tac k hf ya yaa e c)(*strict*)
    apply (metis derivation_initial_is_derivation get_labels_drop_last)
   apply(rename_tac k hf ya yaa e c)(*strict*)
   apply(clarsimp)
   apply (metis diff_add_0 drop_0 get_labels_length)
  apply(rename_tac k hf ya yaa)(*strict*)
  apply(erule_tac
      x="k"
      in allE)
  apply(clarsimp)
  apply(rename_tac k hf ya yaa e c)(*strict*)
  apply(rule_tac
      x="x+k"
      and m="m-k"
      and n="Suc 0"
      and y="y+k"
      and G="G"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in is_forward_deterministicHist_derivations_coincide)
             apply(rename_tac k hf ya yaa e c)(*strict*)
             apply(force)
            apply(rename_tac k hf ya yaa e c)(*strict*)
            apply(force)
           apply(rename_tac k hf ya yaa e c)(*strict*)
           apply(force)
          apply(rename_tac k hf ya yaa e c)(*strict*)
          apply(force)
         apply(rename_tac k hf ya yaa e c)(*strict*)
         prefer 5
         apply(force)
        apply(rename_tac k hf ya yaa e c)(*strict*)
        prefer 5
        apply(force)
       apply(rename_tac k hf ya yaa e c)(*strict*)
       apply(force)
      apply(rename_tac k hf ya yaa e c)(*strict*)
      apply(force)
     apply(rename_tac k hf ya yaa e c)(*strict*)
     apply(force)
    apply(rename_tac k hf ya yaa e c)(*strict*)
    apply(force)
   apply(rename_tac k hf ya yaa e c)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac ya)
   apply(rename_tac k hf ya yaa e c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac k hf ya e c option b)(*strict*)
   apply(rule_tac
      d="d1"
      and i="Suc (x+k)"
      and j="x+n"
      in fixed_scheduler_extendable_translates_backwards_lift)
         apply(rename_tac k hf ya e c option b)(*strict*)
         apply(force)
        apply(rename_tac k hf ya e c option b)(*strict*)
        apply(rule derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac k hf ya e c option b)(*strict*)
       apply(rule_tac
      d="d1"
      in belongs_configurations)
        apply(rename_tac k hf ya e c option b)(*strict*)
        apply(rule derivation_initial_belongs)
         apply(rename_tac k hf ya e c option b)(*strict*)
         apply(force)
        apply(rename_tac k hf ya e c option b)(*strict*)
        apply(force)
       apply(rename_tac k hf ya e c option b)(*strict*)
       apply(force)
      apply(rename_tac k hf ya e c option b)(*strict*)
      apply(force)
     apply(rename_tac k hf ya e c option b)(*strict*)
     apply(force)
    apply(rename_tac k hf ya e c option b)(*strict*)
    apply(force)
   apply(rename_tac k hf ya e c option b)(*strict*)
   apply(force)
  apply(rename_tac k hf ya yaa e c)(*strict*)
  apply(clarsimp)
  apply(case_tac yaa)
  apply(rename_tac k hf ya yaa e c option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac k hf ya e c option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac ya)
  apply(rename_tac k hf ya e c option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac k hf e c option b optiona ba)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (x+k) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac k hf e c option b optiona ba)(*strict*)
   prefer 2
   apply(rule_tac
      m="x+n"
      in step_detail_before_some_position)
     apply(rename_tac k hf e c option b optiona ba)(*strict*)
     apply(rule derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac k hf e c option b optiona ba)(*strict*)
    apply(force)
   apply(rename_tac k hf e c option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac k hf e c option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
  apply(subgoal_tac "\<exists>hf\<in> history_fragments G. get_history ba = extend_history (get_history c) hf")
   apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="n-Suc k"
      and n="(Suc (x + k))"
      and d="d1"
      in steps_extend_history_derivation)
       apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
       apply(force)
      apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
      apply(rule derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
     apply(rule_tac
      d="d1"
      in belongs_configurations)
      apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
      apply(rule derivation_initial_belongs)
       apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
       apply(force)
      apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
      apply(force)
     apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
     apply(force)
    apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac k hf e c option b optiona ba e1 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
  apply(rule_tac
      t="get_history b"
      and s="extend_history (extend_history (get_history c) hfa) hf"
      in ssubst)
   apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
   apply(force)
  apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
  apply(rule_tac
      x="join_history_fragments hfa hf"
      in bexI)
   apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
   apply(rule AX_extend_history_add)
        apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
        apply(force)
       apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
     prefer 4
     apply(rule AX_join_history_fragments_closed)
       apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
       apply(force)
      apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
      apply(force)
     apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
     apply(force)
    apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
    apply(rule AX_get_history_closed)
     apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
     apply(force)
    apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
    apply(rule_tac
      d="d1"
      in belongs_configurations)
     apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
     apply(rule derivation_initial_belongs)
      apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
      apply(force)
     apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
     apply(force)
    apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
    apply(force)
   apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
   apply(force)
  apply(rename_tac k hf e c option b optiona ba e1 c1 hfa)(*strict*)
  apply(force)
  done

lemma same_steps_for_compatible_histories: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> derivation_initial G d2
  \<Longrightarrow> is_forward_deterministicHist_SB G
  \<Longrightarrow> d1 x = d2 y
  \<Longrightarrow> d1 (x + n) \<noteq> None
  \<Longrightarrow> d2 (y + m) \<noteq> None
  \<Longrightarrow> n \<le> m
  \<Longrightarrow> d1 (x + n) = l
  \<Longrightarrow> d2 (y + n) = r
  \<Longrightarrow> \<exists>hf\<in> history_fragments G.
      extend_history (get_history (the (get_configuration (d1 (x + n))))) hf =
      get_history (the (get_configuration (d2 (y + m))))
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler (the(get_configuration(d1(x+n)))))
  \<Longrightarrow> drop x (get_labels d1 (x+n)) = drop y (get_labels d2 (y+n)) \<and> (\<forall>i\<le>n. d1 (x+i) = d2 (y+i))"
  apply(rule_tac
      l="l"
      and r="r"
      and n="n"
      and m="m"
      in same_steps_for_compatible_histories_hlp)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         prefer 6
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end

end
