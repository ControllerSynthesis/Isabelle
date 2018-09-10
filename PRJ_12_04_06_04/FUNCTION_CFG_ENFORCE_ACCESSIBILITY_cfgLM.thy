section {*FUNCTION\_CFG\_ENFORCE\_ACCESSIBILITY\_cfgLM*}
theory
  FUNCTION_CFG_ENFORCE_ACCESSIBILITY_cfgLM

imports
  FUNCTION_CFG_ENFORCE_ACCESSIBILITY_cfgLM_EXTRA

begin

definition F_CFG_EASTD_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg"
  where
    "F_CFG_EASTD_ALT G \<equiv>
  let
    N = F_CFG_APLM__fp G (cfg_nonterminals G) {cfg_initial G}
  in
    \<lparr>cfg_nonterminals = N,
    cfg_events = cfg_events G,
    cfg_initial = cfg_initial G,
    cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> N}\<rparr>"

definition F_CFG_EASTD__SpecInput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__SpecInput G \<equiv>
  valid_cfg G
  \<and> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G"

definition F_CFG_EASTD__SpecOutput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__SpecOutput Gi Go \<equiv>
  valid_cfg Go
  \<and> cfg_sub Go Gi
  \<and> cfgLM.marked_language Go = cfgLM.marked_language Gi
  \<and> cfgLM.initial_marking_derivations Go = cfgLM.initial_marking_derivations Gi
  \<and> cfg_nonterminals Go = cfgLM_accessible_nonterminals Gi \<inter> cfgSTD_Nonblockingness_nonterminals Gi
  \<and> cfg_nonterminals Go = cfgLM_accessible_nonterminals Go \<inter> cfgSTD_Nonblockingness_nonterminals Go
  \<and> cfg_nonterminals Go = cfgLM_language_relevant_nonterminals Go
  \<and> cfg_productions Go = cfgLM_language_relevant_productions Go
  \<and> cfgLM.marked_language Go \<noteq> {}"

lemma F_CFG_EASTD_ALT_preserves_valid_cfg: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> valid_cfg (F_CFG_EASTD_ALT G)"
  apply(simp add: F_CFG_EASTD_ALT_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(simp (no_asm) add: Let_def valid_cfg_def)
  apply(rule conjI)
   apply(simp add: Let_def valid_cfg_def)
  apply(rule conjI)
   apply(rule_tac
      B="cfgLM_accessible_nonterminals G"
      in finite_subset)
    apply(simp (no_asm_simp))
   apply(rule_tac
      B="cfg_nonterminals G"
      in finite_subset)
    apply(simp (no_asm) add: cfgLM_accessible_nonterminals_def)
    apply(force)
   apply(simp add: Let_def valid_cfg_def)
  apply(rule conjI)
   apply(rule_tac
      A="cfgLM_accessible_nonterminals G"
      in set_mp)
    apply(simp (no_asm_simp))
   apply(simp (no_asm) add: cfgLM_accessible_nonterminals_def)
   apply(rule conjI)
    apply(simp add: valid_cfg_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgLM.derivation_initialI)
     apply(rule cfgLM.der1_is_derivation)
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(simp add: get_configuration_def der1_def)
    apply(clarsimp)
    apply(simp add: valid_cfg_def cfg_initial_configurations_def cfg_configurations_def)
   apply(rule_tac
      x="0"
      in exI)
   apply(simp add: get_configuration_def der1_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(force)
  apply(rule conjI)
   apply(simp add: Let_def valid_cfg_def)
  apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
   apply(force)
  apply(thin_tac "cfgLM_accessible_nonterminals G = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: valid_cfg_def)
  apply(rename_tac e)(*strict*)
  apply(rule one_step_preserves_cfgLM_accessible_nonterminals)
     apply(rename_tac e)(*strict*)
     apply(force)+
  done

lemma F_CFG_EASTD_ALT_is_cfg_sub: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfg_sub (F_CFG_EASTD_ALT G) G"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_preserves_valid_cfg)
    apply(force)
   apply(force)
  apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(simp add: cfg_sub_def)
  apply(rule conjI)
   apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="cfgSTD_Nonblockingness_nonterminals G"
      and s="cfg_nonterminals G"
      in ssubst)
    apply(force)
   apply(simp (no_asm) add: cfgLM_accessible_nonterminals_def)
   apply(force)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_preserves_language: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM.marked_language G = cfgLM.marked_language (F_CFG_EASTD_ALT G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_is_cfg_sub)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_preserves_valid_cfg)
    apply(force)
   apply(force)
  apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(rule antisym)
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: cfgLM.marked_language_def)
   apply(clarsimp)
   apply(rename_tac x d)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d)(*strict*)
    prefer 2
    apply(rule cfg_sub_preserves_cfgLM_derivation_initial)
      apply(rename_tac x d)(*strict*)
      apply(force)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    apply(simp add: cfg_marked_effect_def)
   apply(rename_tac x d)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfg_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac x d e c i)(*strict*)
   apply(simp add: cfg_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac x d e c i ia ea ca)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac x d e c i ia ea ca)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac x d e c i ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac x d e c i ia ea ca)(*strict*)
    apply(force)
   apply(rename_tac x d e c i ia ea ca)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac x d)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    apply(simp add: cfg_marked_effect_def)
   apply(rename_tac x d)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfg_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac x d i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(simp add: cfg_marking_configuration_def cfg_configurations_def)
   apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule cfg_sub_preserves_derivation_initial_contra)
      apply(rename_tac x d)(*strict*)
      apply(force)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(rule allI)+
  apply(rename_tac x d i e c)(*strict*)
  apply(rule impI)
  apply(rule cfg_sub_preserves_derivation_initial_contra2)
       apply(rename_tac x d i e c)(*strict*)
       apply(force)
      apply(rename_tac x d i e c)(*strict*)
      apply(force)
     apply(rename_tac x d i e c)(*strict*)
     apply(force)
    apply(rename_tac x d i e c)(*strict*)
    apply(force)
   apply(rename_tac x d i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d i e c)(*strict*)
  apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
   apply(rename_tac x d i e c)(*strict*)
   apply(force)
  apply(rename_tac x d i e c)(*strict*)
  apply(thin_tac "cfgLM_accessible_nonterminals G = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(clarsimp)
  apply(rename_tac x d i e c ea ca c')(*strict*)
  apply(simp add: cfgLM_step_relation_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c ea c' l r)(*strict*)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(case_tac c')
  apply(rename_tac x d i e c ea c' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e c ea l r)(*strict*)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(rule conjI)
   apply(rename_tac x d i e c ea l r)(*strict*)
   prefer 2
   apply(simp add: cfg_sub_def valid_cfg_def)
  apply(rename_tac x d i e c ea l r)(*strict*)
  apply(rule one_step_preserves_cfgLM_accessible_nonterminals)
     apply(rename_tac x d i e c ea l r)(*strict*)
     apply(force)
    apply(rename_tac x d i e c ea l r)(*strict*)
    apply(force)
   apply(rename_tac x d i e c ea l r)(*strict*)
   apply(force)
  apply(rename_tac x d i e c ea l r)(*strict*)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_idemp_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM_accessible_nonterminals (F_CFG_EASTD_ALT G) = cfgLM_accessible_nonterminals G"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_is_cfg_sub)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_preserves_valid_cfg)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(rule antisym)
   apply(simp add: F_CFG_EASTD_ALT_def Let_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> cfgLM_accessible_nonterminals G")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      s="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and t="cfgLM_accessible_nonterminals G"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp (no_asm_use) add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n c w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(rule_tac
      t="\<lparr>cfg_nonterminals = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}, cfg_events = cfg_events G, cfg_initial = cfg_initial G, cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> cfgSTD_Nonblockingness_nonterminals G \<and> (\<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA (prod_lhs p) # w2)))}\<rparr>"
      and s="\<lparr>cfg_nonterminals = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}, cfg_events = cfg_events G, cfg_initial = cfg_initial G, cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}}\<rparr>"
      in ssubst)
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(simp add: cfgLM_accessible_nonterminals_def)
   apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="{A \<in> cfgSTD_Nonblockingness_nonterminals G. \<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2))}"
      in ssubst)
    apply(rename_tac x d n c w1 w2)(*strict*)
    apply(force)
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(rule cfg_sub_preserves_derivation_initial_contra)
      apply(rename_tac x d n c w1 w2)(*strict*)
      apply(force)
     apply(rename_tac x d n c w1 w2)(*strict*)
     apply(force)
    apply(rename_tac x d n c w1 w2)(*strict*)
    apply(force)
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(rule allI)+
  apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
  apply(rule impI)
  apply(rule cfg_sub_preserves_derivation_initial_contra2)
       apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
       apply(force)
      apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
      apply(force)
     apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
     apply(force)
    apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
    apply(force)
   apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
  apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="{A \<in> cfgSTD_Nonblockingness_nonterminals G. \<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2))}"
      in ssubst)
   apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
   apply(force)
  apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
  apply(thin_tac "{A \<in> cfgSTD_Nonblockingness_nonterminals G. \<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2))} = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(rename_tac x d n c w1 w2 i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 i e ca ea cb c')(*strict*)
  apply(simp add: cfgLM_step_relation_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 i e ca ea c' l r)(*strict*)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(case_tac c')
  apply(rename_tac x d n c w1 w2 i e ca ea c' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(rule conjI)
   apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
   prefer 2
   apply(simp add: cfg_sub_def valid_cfg_def)
  apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
  apply(rule_tac
      t="{A \<in> cfgSTD_Nonblockingness_nonterminals G. \<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2))}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
   apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
   apply(simp (no_asm_use) add: cfgLM_accessible_nonterminals_def)
   apply(force)
  apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
  apply(rule one_step_preserves_cfgLM_accessible_nonterminals)
     apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
    apply(force)
   apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
   apply(force)
  apply(rename_tac x d n c w1 w2 i e ca ea l r da na cb w1a w2a)(*strict*)
  apply(simp (no_asm_use) add: cfgLM_accessible_nonterminals_def)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_preserves_Eliminability: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfg_nonterminals (F_CFG_EASTD_ALT G) = cfgLM_accessible_nonterminals (F_CFG_EASTD_ALT G) \<inter> cfgSTD_Nonblockingness_nonterminals (F_CFG_EASTD_ALT G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_idemp_cfgLM_accessible_nonterminals)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_is_cfg_sub)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_preserves_valid_cfg)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(rule inter_eq_intro)
    apply(simp add: F_CFG_EASTD_ALT_def Let_def)
   prefer 2
   apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> {A \<in> cfg_nonterminals G. \<exists>d n c. cfgLM.derivation_initial G d \<and> get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2)}")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(unfold cfgLM_accessible_nonterminals_def)[1]
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(subgoal_tac "x \<in> {A \<in> cfg_nonterminals G. \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} ({y. (\<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>)}) \<and> setA w' = {}}")
   apply(rename_tac x d n c w1 w2)(*strict*)
   prefer 2
   apply(simp (no_asm_use) only: cfgSTD_Nonblockingness_nonterminals_def)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 da w')(*strict*)
  apply(subgoal_tac "\<exists>d n e. cfgSTD.derivation G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA x]\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = w'\<rparr>)")
   apply(rename_tac x d n c w1 w2 da w')(*strict*)
   prefer 2
   apply(rule_tac
      x="da"
      in exI)
   apply(simp add: cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.derivation_from_to_def )
   apply(clarsimp)
   apply(rename_tac x d n c w1 w2 da w' na xa)(*strict*)
   apply(case_tac "da 0")
    apply(rename_tac x d n c w1 w2 da w' na xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d n c w1 w2 da w' na xa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n c w1 w2 da w' na xa)(*strict*)
   apply(rule_tac
      x="na"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d n c w1 w2 da w')(*strict*)
  apply(thin_tac "cfgSTD.derivation_from_to G da {pair None \<lparr>cfg_conf = [teA x]\<rparr>} ({y. (\<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>)})")
  apply(rename_tac x d n c w1 w2 da w')(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 w' da na e)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac x d n c w1 w2 w' da na e)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac x d n c w1 w2 w' da na e a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac x d n c w1 w2 w' da na e a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 w' da na e option)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n c w1 w2 w' da na e option cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
  apply(subgoal_tac "x \<in> {A \<in> cfg_nonterminals \<lparr>cfg_nonterminals = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}, cfg_events = cfg_events G, cfg_initial = cfg_initial G, cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}}\<rparr>. \<exists>d w'. cfgSTD.derivation_from_to \<lparr>cfg_nonterminals = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}, cfg_events = cfg_events G, cfg_initial = cfg_initial G, cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}}\<rparr> d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} ({ y. (\<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>)}) \<and> setA w' = {}}")
   apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "cfgSTD.derivation \<lparr>cfg_nonterminals = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}, cfg_events = cfg_events G, cfg_initial = cfg_initial G, cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}}\<rparr> da ")
   apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
    prefer 2
    apply(rule_tac
      x="da"
      in exI)
    apply(rule_tac
      x="w'"
      in exI)
    apply(simp add: cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.derivation_from_to_def )
    apply(rule_tac
      x="na"
      in exI)
    apply(clarsimp)
    apply(case_tac "da (Suc na)")
     apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w' da na e option a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac x d n w1 w2 w' da na e option a)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and d="da"
      and n="na"
      and m="Suc na"
      in cfgSTD.step_detail_before_some_position)
       apply(rename_tac x d n w1 w2 w' da na e option a)(*strict*)
       apply(force)
      apply(rename_tac x d n w1 w2 w' da na e option a)(*strict*)
      apply(force)
     apply(rename_tac x d n w1 w2 w' da na e option a)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w' da na e option a)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d n w1 w2 w' da na e option e2 c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x d n w1 w2 da na e option e2 c2 l r)(*strict*)
    apply(simp add: setAConcat)
   apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
   apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
    apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
   apply(simp (no_asm) only: cfgLM_accessible_nonterminals_def)
   apply(simp (no_asm))
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
    prefer 2
    apply(rule_tac
      x="d"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="n"
      in exI)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
  apply(rule cfg_sub_preserves_cfg_derivation_contra)
      apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
      apply(force)
     apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
   apply(force)
  apply(rename_tac x d n w1 w2 w' da na e option)(*strict*)
  apply(rule allI)+
  apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
  apply(rule impI)
  apply(rule cfg_sub_preserves_cfg_derivation_contra2)
         apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
         apply(force)
        apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
        apply(force)
       apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
       apply(force)
      apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
      apply(force)
     apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
    apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
   apply(simp (no_asm) only: cfgLM_accessible_nonterminals_def)
   apply(simp (no_asm))
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(rename_tac x d n w1 w2 w' da na e option i ea c)(*strict*)
  apply(simp add: cfgSTD_step_relation_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w' da na e option i ea c eb c' l r)(*strict*)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(case_tac c')
  apply(rename_tac x d n w1 w2 w' da na e option i ea c eb c' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(rule conjI)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
   prefer 2
   apply(simp add: cfg_sub_def valid_cfg_def)
  apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
  apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="cfgLM_accessible_nonterminals G"
      in ssubst)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
   apply(force)
  apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
  apply(rule one_step_preserves_cfgLM_accessible_nonterminals)
     apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
   apply(force)
  apply(rename_tac x d n w1 w2 w' da na e option i ea c eb l r)(*strict*)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_makes_precise_accessible_and_Nonblockingness: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfg_nonterminals (F_CFG_EASTD_ALT G) = cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G"
  apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} \<subseteq> cfg_nonterminals G")
   apply(blast)
  apply(rule_tac B="cfgLM_accessible_nonterminals G" in subset_trans)
   apply(rule F_CFG_APLM_F_CFG_APLM__fp_invariant_03_unfold)
   apply(simp add: F_CFG_APLM__fp_valid_input_def)
   apply(simp add: valid_cfg_def)
  apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(force)
  done

lemma cfg_with_cfgLM_Nonblockingness_nonterminals_has_nonempty_cfgLM_marked_language: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM.marked_language G \<noteq> {}"
  apply(simp add: cfgLM.marked_language_def)
  apply(subgoal_tac "cfg_initial G \<in> cfgLM_Nonblockingness_nonterminals G")
   prefer 2
   apply(simp add: valid_cfg_def)
   apply(force)
  apply(thin_tac "cfg_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G")
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rule_tac x="filterB w'" in exI)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(simp add: cfg_marked_effect_def)
  apply(rule conjI)
   apply(rule_tac x="e" in exI)
   apply(rule_tac x="\<lparr>cfg_conf = w'\<rparr>" in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(force)
   apply (metis liftBDeConv2)
  apply(rule conjI)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def cfg_marking_condition_def cfg_marking_configuration_def)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  apply(rule_tac d="d" in cfgLM.belongs_configurations)
   apply(rule cfgLM.derivation_belongs)
      apply(force)
     apply(force)
    apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def cfg_marking_condition_def cfg_marking_configuration_def)
   apply(force)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_preserves_cfgLM_initial_marking_derivations: "
  valid_cfg Gi
  \<Longrightarrow> valid_cfg Go
  \<Longrightarrow> cfg_sub Go Gi
  \<Longrightarrow> cfg_nonterminals Gi = cfgSTD_Nonblockingness_nonterminals Gi
  \<Longrightarrow> Go = F_CFG_EASTD_ALT Gi
  \<Longrightarrow> cfgLM.initial_marking_derivations Gi \<subseteq> cfgLM.initial_marking_derivations Go"
  apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(clarsimp)
  apply(rename_tac d)
  apply(rule conjI)
   prefer 2
   apply(simp add: cfg_marking_condition_def)
   apply(simp add: cfg_marking_configuration_def cfg_configurations_def cfg_sub_def)
   apply(clarsimp)
   apply(rule_tac x="i" in exI)
   apply(clarsimp)
   apply(simp add: F_CFG_EASTD_ALT_def Let_def)
   apply(force)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(clarsimp)
  apply(rename_tac w)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_preserves_valid_cfg)
    apply(force)
   apply(force)
  apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(rule cfg_sub_preserves_derivation_initial_contra)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule allI)+
  apply(rule impI)
  apply(rule cfg_sub_preserves_derivation_initial_contra2)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   prefer 2
   apply(force)
  apply(rule_tac
      t="F_CFG_APLM__fp Gi (cfgSTD_Nonblockingness_nonterminals Gi) {cfg_initial Gi}"
      and s="cfgLM_accessible_nonterminals Gi"
      in ssubst)
   apply(force)
  apply(thin_tac "cfgLM_accessible_nonterminals Gi = F_CFG_APLM__fp Gi (cfgSTD_Nonblockingness_nonterminals Gi) {cfg_initial Gi}")
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def cfg_configurations_def)
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(case_tac c')
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(simp add: setBConcat)
  apply(rule conjI)
   prefer 2
   apply(simp add: cfg_sub_def valid_cfg_def)
  apply(rule one_step_preserves_cfgLM_accessible_nonterminals)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_makes_equal_cfgLM_initial_marking_derivations: "
  valid_cfg Gi
  \<Longrightarrow> valid_cfg Go
  \<Longrightarrow> cfg_sub Go Gi
  \<Longrightarrow> cfg_nonterminals Gi = cfgSTD_Nonblockingness_nonterminals Gi
  \<Longrightarrow> Go = F_CFG_EASTD_ALT Gi
  \<Longrightarrow> cfgLM.initial_marking_derivations Go = cfgLM.initial_marking_derivations Gi"
  apply(rule antisym)
   apply(rule cfg_sub_preserves_cfgLM_initial_marking_derivations)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_CFG_EASTD_ALT_preserves_cfgLM_initial_marking_derivations)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_CFG_EASTD_ALT_enforces_cfgLM_language_relevant_productions: "
  valid_cfg Gi
  \<Longrightarrow> valid_cfg Go
  \<Longrightarrow> cfg_sub Go Gi
  \<Longrightarrow> cfg_nonterminals Gi = cfgSTD_Nonblockingness_nonterminals Gi
  \<Longrightarrow> Go = F_CFG_EASTD_ALT Gi
  \<Longrightarrow> cfg_productions Go = cfgLM_language_relevant_productions Go"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="Gi"
      in F_CFG_EASTD_ALT_preserves_Eliminability)
    apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="Gi" in F_CFG_EASTD_ALT_makes_precise_accessible_and_Nonblockingness)
    apply(simp add: F_CFG_EASTD__SpecInput_def)
   apply(simp add: F_CFG_EASTD__SpecInput_def)
  apply(subgoal_tac "
cfgLM_accessible_nonterminals (F_CFG_EASTD_ALT Gi) \<inter> cfgSTD_Nonblockingness_nonterminals (F_CFG_EASTD_ALT Gi) = cfgLM_language_relevant_nonterminals (F_CFG_EASTD_ALT Gi)")
   prefer 2
   apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_in_cfgSTD_Nonblockingness_nonterminals_grammar)
      prefer 2
      apply(force)
     prefer 2
     apply(force)
    apply(force)
   apply(rule antisym)
    apply(force)
   apply(simp (no_asm) add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(force)
  apply(rule antisym)
   prefer 2
   apply(simp add: cfgLM_language_relevant_productions_def)
   apply(clarsimp)
   apply(subgoal_tac "x \<in> cfg_step_labels (F_CFG_EASTD_ALT Gi)")
    prefer 2
    apply(rule cfgLM.belongs_step_labels)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: cfg_step_labels_def)
  apply(rule_tac t="cfg_productions Go" and s="{p \<in> cfg_productions Gi.
     prod_lhs p
     \<in> F_CFG_APLM__fp Gi (cfgSTD_Nonblockingness_nonterminals Gi) {cfg_initial Gi}}" in ssubst)
   apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(rule_tac
      t="F_CFG_APLM__fp X (cfgSTD_Nonblockingness_nonterminals X) {cfg_initial X}"
      and s="cfgLM_accessible_nonterminals X" for X
      in ssubst)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_CFG_APLMSoundL)
    apply(force)
   apply(force)
  apply(simp add: cfgLM_language_relevant_productions_def)
  apply(clarsimp)
  apply(case_tac x)
  apply(clarsimp)
  apply(rename_tac A w)
  apply(subgoal_tac "A \<in> cfgSTD_Nonblockingness_nonterminals Gi \<and>
           (\<exists>d. cfgLM.derivation_initial
                 Gi d \<and>
                (\<exists>n c. get_configuration (d n) = Some c \<and>
                       (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2)))")
   prefer 2
   apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac Go="F_CFG_EASTD_ALT Gi" and Gi="Gi" in F_CFG_EASTD_ALT_makes_equal_cfgLM_initial_marking_derivations)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "d n")
   apply(simp add: get_configuration_def)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(clarsimp)
  apply(case_tac a)
  apply(clarsimp)
  apply(rename_tac e)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<in> SSX" for SSX)
   prefer 2
   apply(rule_tac d="d" in cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "prod_lhs \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfgSTD_Nonblockingness_nonterminals Gi \<and>
           setA (prod_rhs \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<subseteq> cfgSTD_Nonblockingness_nonterminals Gi \<and>
           setB (prod_rhs \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<subseteq> cfg_events Gi")
   prefer 2
   apply(simp add: valid_cfg_def)
   apply(force)
  apply(subgoal_tac "setA (liftB w1 @ w @ w2) \<subseteq> cfg_nonterminals Gi")
   prefer 2
   apply(simp add:  cfg_configurations_def setA_liftB setAConcat)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac w="liftB w1 @ w @ w2" and G="Gi" in construct_elimininating_derivation_prime)
     apply(force)
    apply(rule antisym)
     prefer 2
     apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB v\<rparr> \<in> SSX" for SSX)
   prefer 2
   apply(rule_tac d="da" in cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_belongs)
       apply(force)
      apply(force)
     apply(simp add: cfg_configurations_def)
     apply(simp add: setBConcat)
    apply(force)
   apply(force)
  apply(subgoal_tac "derivation_append d (derivation_append (der2 \<lparr>cfg_conf = liftB w1 @ [teA A] @ w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr>  \<lparr>cfg_conf = liftB w1 @ w @ w2\<rparr>) da (Suc 0)) n \<in> cfgLM.initial_marking_derivations  (F_CFG_EASTD_ALT Gi)")
   prefer 2
   apply(rule_tac A="cfgLM.initial_marking_derivations  (Gi)" in set_mp)
    apply(force)
   apply(thin_tac "cfgLM.initial_marking_derivations A = VB" for A VB)
   apply(simp add: cfgLM.initial_marking_derivations_def cfg_marking_condition_def)
   apply(rule context_conjI)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(force)
     apply(force)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rule cfgLM.der2_is_derivation)
       apply(simp add: cfgLM_step_relation_def)
       apply(rule_tac x="liftB w1" in exI)
       apply(clarsimp)
       apply(simp add: setA_liftB)
      apply(force)
     apply(simp add: der2_def)
    apply(clarsimp)
    apply(simp add: derivation_append_def der2_def)
   apply(rule_tac x="n+Suc 0+na" in exI)
   apply(simp add: setA_liftB)
   apply(simp add: derivation_append_def der2_def cfg_marking_configuration_def cfg_configurations_def)
   apply(simp add: setA_liftB)
   apply(clarsimp)
   apply(rule_tac t="liftB w1 @ w @ w2" and s="liftB v" in ssubst)
    apply(force)
   apply(simp (no_asm) add: setA_liftB)
  apply(thin_tac "       ATS_Language0.initial_marking_derivations cfg_initial_configurations
        cfgLM_step_relation cfg_marking_condition (F_CFG_EASTD_ALT Gi) =
       ATS_Language0.initial_marking_derivations cfg_initial_configurations
        cfgLM_step_relation cfg_marking_condition Gi ")
  apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(rule_tac x="derivation_append d
          (derivation_append
            (der2 \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr>
              \<lparr>cfg_conf = liftB w1 @ w @ w2\<rparr>)
            da (Suc 0))
          n" in exI)
  apply(clarsimp)
  apply(rule_tac x="Suc n" in exI)
  apply(simp add: derivation_append_def der2_def)
  done

theorem SOUND_FUN_CFGLMACX: "
  F_CFG_EASTD__SpecInput G
  \<Longrightarrow> F_CFG_EASTD__SpecOutput G (F_CFG_EASTD_ALT G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_preserves_valid_cfg)
    apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
    apply(force)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_EASTD_ALT_is_cfg_sub)
    apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_APLMSoundL)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_EASTD_ALT_preserves_language)
    apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_EASTD_ALT_preserves_Eliminability)
    apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_CFG_EASTD_ALT_makes_precise_accessible_and_Nonblockingness)
    apply(simp add: F_CFG_EASTD__SpecInput_def)
   apply(simp add: F_CFG_EASTD__SpecInput_def)
  apply(subgoal_tac "
cfgLM_accessible_nonterminals (F_CFG_EASTD_ALT G) \<inter> cfgSTD_Nonblockingness_nonterminals (F_CFG_EASTD_ALT G) = cfgLM_language_relevant_nonterminals (F_CFG_EASTD_ALT G)")
   prefer 2
   apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_in_cfgSTD_Nonblockingness_nonterminals_grammar)
      prefer 2
      apply(force)
     prefer 2
     apply(force)
    apply(simp add: F_CFG_EASTD_ALT_def F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
   apply(rule antisym)
    apply(force)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(force)
  apply(subgoal_tac "cfgLM.initial_marking_derivations (F_CFG_EASTD_ALT G) = cfgLM.initial_marking_derivations G")
   prefer 2
   apply(rule F_CFG_EASTD_ALT_makes_equal_cfgLM_initial_marking_derivations)
       apply(simp add: F_CFG_EASTD_ALT_def F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
      apply(force)
     apply(simp add: F_CFG_EASTD_ALT_def F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
    apply(simp add: F_CFG_EASTD_ALT_def F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
   apply(simp add: F_CFG_EASTD_ALT_def F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "cfgLM.marked_language (F_CFG_EASTD_ALT G) \<noteq> {}")
   prefer 2
   apply(rule cfg_with_cfgLM_Nonblockingness_nonterminals_has_nonempty_cfgLM_marked_language)
    apply(force)
   apply(rule_tac t="cfgLM_Nonblockingness_nonterminals (F_CFG_EASTD_ALT G)" and s="cfgSTD_Nonblockingness_nonterminals (F_CFG_EASTD_ALT G)" in ssubst)
    prefer 2
    apply(force)
   apply (metis cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals)
  apply(subgoal_tac "cfg_productions (F_CFG_EASTD_ALT G) = cfgLM_language_relevant_productions (F_CFG_EASTD_ALT G)")
   prefer 2
   apply(rule F_CFG_EASTD_ALT_enforces_cfgLM_language_relevant_productions)
       prefer 2
       apply(force)
      prefer 2
      apply(force)
     apply(simp add: F_CFG_EASTD__SpecInput_def)
    apply(simp add: F_CFG_EASTD__SpecInput_def)
   apply(force)
  apply(simp add: F_CFG_EASTD_ALT_def F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  done

end
