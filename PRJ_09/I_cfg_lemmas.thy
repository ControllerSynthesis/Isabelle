section {*I\_cfg\_lemmas*}
theory
  I_cfg_lemmas

imports
  I_cfgSTD
  I_cfgLM_misc
  I_cfgRM
  I_cfgSTD_cfgRM
  I_cfgSTD_cfgLM
  I_cfgLM_cfgRM

begin

lemma combine_derivation_to_terminating_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G dc
  \<Longrightarrow> dc 0 = Some (pair None \<lparr>cfg_conf = liftA c'\<rparr>)
  \<Longrightarrow> dc nc = Some (pair ec \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> cfgRM.derivation G d2'
  \<Longrightarrow> d2' 0 = Some (pair None \<lparr>cfg_conf = liftA w1\<rparr>)
  \<Longrightarrow> d2' n2' = Some (pair e2'a \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> cfgLM.derivation_initial G d1
  \<Longrightarrow> d1 (Suc (n1'a + n)) = Some (pair e1 \<lparr>cfg_conf = liftB w\<delta>1 @ teA A2 # liftA w1\<rparr>)
  \<Longrightarrow> d1 (Suc (Suc (n1'a + n))) = Some (pair e2 \<lparr>cfg_conf = liftB w\<delta>1 @ liftA c' @ liftA w1\<rparr>)
  \<Longrightarrow> d1 n1'a = Some (pair e0 \<lparr>cfg_conf = liftB w\<delta>1 @ teA B0 # liftA r0\<rparr>)
  \<Longrightarrow> \<exists>d eX eY.
  cfgLM.derivation_initial G d \<and>
  d n1'a = Some (pair e0 \<lparr>cfg_conf = liftB w\<delta>1 @ teA B0 # liftA r0\<rparr>) \<and>
  d (Suc (n1'a + n)) = Some (pair e1 \<lparr>cfg_conf = liftB w\<delta>1 @ teA A2 # liftA w1\<rparr>) \<and>
  d (Suc (Suc (n1'a + n))) = Some (pair e2 \<lparr>cfg_conf = liftB w\<delta>1 @ liftA c' @ liftA w1\<rparr>) \<and>
  d (Suc (Suc (n1'a + n)) + nc) = Some (pair eX \<lparr>cfg_conf = liftB w\<delta>1 @ liftA w1\<rparr>) \<and>
  d (Suc (Suc (n1'a + n)) + nc + n2') = Some (pair eY \<lparr>cfg_conf = liftB w\<delta>1\<rparr>)"
  apply(subgoal_tac "\<exists>d' e. cfgLM.derivation G d' \<and> maximum_of_domain d' n2' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=liftA w1\<rparr>) \<and> d' n2' = Some (pair e \<lparr>cfg_conf=[]\<rparr>)")
   prefer 2
   apply(rule_tac
      d="derivation_take d2' n2'"
      in cfg_derivation_can_be_translated_to_cfgLM_derivation)
        apply(force)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(rule cfgRM.derivation_take_preserves_derivation)
       apply(force)
      apply(simp add: maximum_of_domain_def derivation_take_def)
     apply(simp add: maximum_of_domain_def derivation_take_def)
    apply(simp add: maximum_of_domain_def derivation_take_def)
   apply(force)
  apply(thin_tac "d2' n2' = Some (pair e2'a \<lparr>cfg_conf = []\<rparr>)")
  apply(thin_tac "cfgRM.derivation G d2'")
  apply(thin_tac "d2' 0 = Some (pair None \<lparr>cfg_conf = liftA w1\<rparr>)")
  apply(clarsimp)
  apply(rename_tac d' e)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_append d1 (derivation_map dc (\<lambda>v. \<lparr>cfg_conf = (liftB w\<delta>1)@(cfg_conf v)@(liftA w1)\<rparr>)) (Suc (Suc (n1'a + n)))) (derivation_map d' (\<lambda>v. \<lparr>cfg_conf = (liftB w\<delta>1)@(cfg_conf v)\<rparr>)) ((Suc (Suc (n1'a + n)))+nc)"
      in exI)
  apply(rule conjI)
   apply(rename_tac d' e)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac d' e)(*strict*)
     apply(force)
    apply(rename_tac d' e)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac d' e)(*strict*)
      apply(force)
     apply(rename_tac d' e)(*strict*)
     apply(force)
    apply(rename_tac d' e)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac d' e)(*strict*)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d' e)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(rename_tac d' e)(*strict*)
      apply(force)
     apply(rename_tac d' e)(*strict*)
     apply(clarsimp)
     apply(rename_tac d' e a ea b)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d' e a ea b l r)(*strict*)
     apply(rule_tac
      x="liftB w\<delta>1 @ l"
      in exI)
     apply(clarsimp)
     apply (metis setA_liftB_subset setA_app empty_subsetI subset_empty)
    apply(rename_tac d' e)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_map_def)
   apply(rename_tac d' e)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac d' e)(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac d' e)(*strict*)
       apply(rule cfgLM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d' e)(*strict*)
      apply(rule cfgLM.derivation_map_preserves_derivation2)
       apply(rename_tac d' e)(*strict*)
       apply(force)
      apply(rename_tac d' e)(*strict*)
      apply(clarsimp)
      apply(rename_tac d' e a ea b)(*strict*)
      apply(simp add: cfgLM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac d' e a ea b l r)(*strict*)
      apply(rule_tac
      x="liftB w\<delta>1 @ l"
      in exI)
      apply(clarsimp)
      apply (metis setA_liftB_subset setA_app empty_subsetI subset_empty)
     apply(rename_tac d' e)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_map_def)
    apply(rename_tac d' e)(*strict*)
    apply(rule cfgLM.derivation_map_preserves_derivation2)
     apply(rename_tac d' e)(*strict*)
     apply(force)
    apply(rename_tac d' e)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' e a ea b)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d' e a ea b l r)(*strict*)
    apply(rule_tac
      x="liftB w\<delta>1 @ l"
      in exI)
    apply(clarsimp)
    apply (metis setA_liftB_subset setA_app empty_subsetI subset_empty)
   apply(rename_tac d' e)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def derivation_map_def)
   apply(clarsimp)
  apply(rename_tac d' e)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rule conjI)
   apply(rename_tac d' e)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e)(*strict*)
  apply(clarsimp)
  done

lemma cfgRM_Nonblockingness_branching_to_cfgRM_Nonblockingness_branching_hlp_mod: "
       valid_cfg G \<Longrightarrow>
       cfgRM_accessible_nonterminals G \<subseteq> cfgRM_Nonblockingness_nonterminals G \<Longrightarrow>
       ATS.derivation_initial cfg_initial_configurations
        cfgRM_step_relation G dh \<Longrightarrow>
       maximum_of_domain dh n \<Longrightarrow>
       dh n = Some (pair e \<lparr>cfg_conf = w\<rparr>) \<Longrightarrow>
       \<exists>dc. cfgRM.derivation G dc \<and>
            cfgLM.belongs G dc \<and>
            Ex (maximum_of_domain dc) \<and>
            derivation_append_fit dh dc n \<and>
            cfg_marking_condition G (derivation_append dh dc n)"
  apply(induct "length(filterA w)" arbitrary: dh n e w)
   apply(rename_tac w dh n e)(*strict*)
   apply(subgoal_tac "\<exists>wx. liftB wx = w")
    apply(rename_tac w dh n e)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w"
      in exI)
    apply(rule liftBDeConv2)
    apply(rule filterA_setA)
    apply(force)
   apply(rename_tac w dh n e)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB wx\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply (metis cfgRM.der1_is_derivation)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule cfgLM.der1_belongs)
    apply(rule cfgRM.belongs_configurations)
     apply(rename_tac dh n e wx)(*strict*)
     apply(rule cfgRM.derivation_initial_belongs)
      apply(rename_tac dh n e wx)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply (metis der1_maximum_of_domain)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(simp add: derivation_append_fit_def der1_def)
   apply(rename_tac dh n e wx)(*strict*)
   apply(simp add: cfg_marking_condition_def derivation_append_def der1_def cfg_marking_configuration_def)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: setA_liftB)
   apply(rule cfgRM.belongs_configurations)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule cfgRM.derivation_initial_belongs)
     apply(rename_tac dh n e wx)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx)(*strict*)
   apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w = wx1 @[teA A]@ liftB wx2")
   apply(rename_tac x w dh n e)(*strict*)
   prefer 2
   apply(rule filterA_gt_0_then_rm_nonterminal)
   apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(subgoal_tac "A \<in> cfgRM_Nonblockingness_nonterminals G")
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfgRM_accessible_nonterminals G"
      in set_mp)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(thin_tac "cfgRM_accessible_nonterminals G \<subseteq> cfgRM_Nonblockingness_nonterminals G")
   apply(simp add: cfgRM_accessible_nonterminals_def)
   apply(subgoal_tac "\<lparr>cfg_conf = wx1 @ teA A # liftB wx2\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    prefer 2
    apply(rule cfgRM.belongs_configurations)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(rule cfgRM.derivation_initial_belongs)
      apply(rename_tac x dh n e wx1 A wx2)(*strict*)
      apply(force)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule conjI)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(simp add: cfg_configurations_def setAConcat)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfgRM_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(case_tac na)
   apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' nat)(*strict*)
  apply(rename_tac na)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule_tac
      x="wx1@ w' @ liftB wx2"
      in meta_allE)
  apply(erule_tac
      x="derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) n) (n+Suc na)"
      in meta_allE)
  apply(erule_tac
      x="n+Suc na"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule setA_empty_filterA_empty)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule cfgRM.derivation_take_preserves_derivation_initial)
   apply(rule cfgRM.derivation_append_preserves_derivation_initial)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
      apply (metis cfgRM_derivations_are_cfg_derivations)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na i eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2 l r)(*strict*)
    apply(rule_tac
      x="wx1 @ l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat setA_liftB)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(simp add: derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) dc (Suc na)) (Suc na+x)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule cfgRM.derivation_take_preserves_derivation)
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(rule cfgRM.derivation_map_preserves_derivation)
       apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
       apply (metis cfgRM_derivations_are_cfg_derivations)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x i eb c)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2 l r)(*strict*)
     apply(rule_tac
      x="wx1 @ l"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat setA_liftB)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(simp add: derivation_map_def)
   apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
   apply(case_tac "dc 0")
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule cfgRM.derivation_belongs)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(rule_tac
      d="dh"
      in cfgRM.belongs_configurations)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(rule cfgRM.derivation_initial_belongs)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule_tac
      x="(Suc na + x)"
      in exI)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def derivation_append_fit_def derivation_take_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) n) (Suc (n + na))) dc (Suc (n + na))) = (derivation_append dh (derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) dc (Suc na)) (Suc na + x)) n)")
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule ext)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def derivation_append_fit_def derivation_take_def)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "dc (xa - Suc (n + na))")
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(rule_tac
      d="dc"
      and n="x"
      and m="(xa - Suc (n + na))"
      in cfgRM.no_some_beyond_maximum_of_domain)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  done

corollary cfgRM_accessible_nonterminals_contained_in_cfgRM_Nonblockingness_nonterminals_implies_cfgRM_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgRM_accessible_nonterminals G \<subseteq> cfgRM_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G"
  apply(simp add: cfgRM.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac dh n)(*strict*)
   apply(simp add: maximum_of_domain_def get_configuration_def)
  apply(rename_tac dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w)(*strict*)
  apply(rule cfgRM_Nonblockingness_branching_to_cfgRM_Nonblockingness_branching_hlp_mod)
      apply(rename_tac dh n e w)(*strict*)
      apply(force)
     apply(rename_tac dh n e w)(*strict*)
     apply(force)
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  done

corollary cfg_dependency_between_language_properties1: "
  valid_cfg G
  \<Longrightarrow>
  cfgSTD.marked_language G = cfgLM.marked_language G
  \<and> cfgSTD.marked_language G = cfgRM.marked_language G
  \<and> cfgLM.unmarked_language G \<subseteq> cfgSTD.unmarked_language G
  \<and> cfgRM.unmarked_language G \<subseteq> cfgSTD.unmarked_language G
  \<and> cfgSTD.marked_language G \<subseteq> cfgSTD.unmarked_language G
  \<and> cfgLM.marked_language G \<subseteq> cfgLM.unmarked_language G
  \<and> cfgRM.marked_language G \<subseteq> cfgRM.unmarked_language G"
  apply(rule conjI)
   apply (metis CFG_lang_lm_lang_equal)
  apply(rule conjI)
   apply (metis CFG_lang_rm_lang_equal)
  apply(rule conjI)
   apply(simp add: cfgSTD.unmarked_language_def cfgLM.unmarked_language_def cfgSTD.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac x d)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def)
   apply (metis cfgLM_derivations_are_cfg_derivations)
  apply(rule conjI)
   apply(simp add: cfgSTD.unmarked_language_def cfgRM.unmarked_language_def cfgSTD.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac x d)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_initial_def)
   apply (metis cfgRM_derivations_are_cfg_derivations)
  apply(rule conjI)
   apply (metis cfgSTD.lang_inclusion)
  apply(rule conjI)
   apply (metis cfgLM.lang_inclusion)
  apply (metis cfgRM.lang_inclusion)
  done

lemma CFGlm2rm_single_step: "
  valid_cfg G
  \<Longrightarrow> e=\<lparr>prod_lhs=A,prod_rhs=liftB w\<rparr>
  \<Longrightarrow> \<lparr>prod_lhs=A,prod_rhs=liftB w\<rparr>\<in> cfg_productions G
  \<Longrightarrow> CFGlm2rm G [e] = [e]"
  apply(subgoal_tac "(\<exists>d' e'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>) \<and> d' (Suc 0) = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>) \<and> [e]=CFGlm2rm G (map the (get_labels d' (Suc 0))))")
   prefer 2
   apply(rule_tac
      d="der2 \<lparr>cfg_conf=[teA A]\<rparr> e \<lparr>cfg_conf=liftB w\<rparr>"
      in lemma_4_10)
        apply(force)
       apply(rule cfgRM.der2_is_derivation)
       apply(simp add: cfgRM_step_relation_def)
       apply(rule_tac
      x="[]"
      in exI)
       apply(force)
      apply(rule cfgRM.der2_belongs)
        apply(simp add: cfg_configurations_def)
        apply(clarsimp)
        apply (metis prod_lhs_in_nonterms)
       apply(simp add: cfg_step_labels_def)
      apply(simp add: cfg_configurations_def)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = liftB w\<rparr>"
      in ballE)
       apply(force)
      apply(force)
     apply(simp add: der2_def)
    apply(simp add: der2_def)
   apply(rule sym)
   apply(rule_tac
      t="get_labels (der2 \<lparr>cfg_conf = [teA A]\<rparr> e \<lparr>cfg_conf = liftB w\<rparr>) (Suc 0)"
      and s="[Some e]"
      in ssubst)
    apply (metis der2_get_labels)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d' e')(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc 0)=[Suc 0]")
   apply(rename_tac d' e')(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac e')
    apply(rename_tac d' e')(*strict*)
    apply(clarsimp)
    apply(rename_tac d')(*strict*)
    apply (metis cfgLM.derivation_Always_PreEdge_prime cfgLM_derivations_are_cfg_derivations)
   apply(rename_tac d' e' a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' 0 = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac d' a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d' a)(*strict*)
      apply(force)
     apply(rename_tac d' a)(*strict*)
     apply(force)
    apply(rename_tac d' a)(*strict*)
    apply(force)
   apply(rename_tac d' a)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d' a l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac d' a l r)(*strict*)
    prefer 2
    apply(rename_tac d' a l r aa list)(*strict*)
    apply(force)
   apply(rename_tac d' a l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' a)(*strict*)
   apply(case_tac a)
   apply(rename_tac d' a prod_lhsa prod_rhsa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e')(*strict*)
  apply (metis natUptTo_n_n)
  done

corollary cfg_dependency_between_language_properties2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.unmarked_language G \<subseteq> cfgRM.unmarked_language G
  \<and> cfgSTD.unmarked_language G \<subseteq> cfgLM.unmarked_language G"
  apply(rule context_conjI)
   apply(metis cfgSTD_unmarked_in_cfgRM_unmarked)
  apply(metis cfgSTD_unmarked_in_cfgLM_unmarked)
  done

corollary cfg_dependency_between_language_properties3: "
  valid_cfg G
  \<Longrightarrow> cfgLM.unmarked_language G = prefix_closure (cfgLM.unmarked_language G)
  \<and> cfgRM.unmarked_language G = prefix_closure (cfgRM.unmarked_language G)
  \<and> cfgSTD.unmarked_language G = prefix_closure (cfgSTD.unmarked_language G)"
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(force)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def cfgLM.unmarked_language_def)
   apply(clarsimp)
   apply(rename_tac x d c)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfg_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac x d c e ca i z)(*strict*)
   apply(case_tac ca)
   apply(rename_tac x d c e ca i z cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d c e i z)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = liftB (x @ c) @ z\<rparr>"
      in exI)
   apply(clarsimp)
   apply(simp add: liftB_commutes_over_concat)
   apply(force)
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(force)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def cfgRM.unmarked_language_def)
   apply(clarsimp)
   apply(rename_tac x d c)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfg_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac x d c e ca i z)(*strict*)
   apply(case_tac ca)
   apply(rename_tac x d c e ca i z cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d c e i z)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = liftB (x @ c) @ z\<rparr>"
      in exI)
   apply(clarsimp)
   apply(simp add: liftB_commutes_over_concat)
   apply(force)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_closure_def prefix_def cfgSTD.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d c e ca i z)(*strict*)
  apply(case_tac ca)
  apply(rename_tac x d c e ca i z cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i z)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB (x @ c) @ z\<rparr>"
      in exI)
  apply(clarsimp)
  apply(simp add: liftB_commutes_over_concat)
  apply(force)
  done

corollary cfgSTD_Nonblockingness_branching_implies_equal_langBF: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> (nonblockingness_language (cfgSTD.unmarked_language G) (cfgSTD.marked_language G)
  \<longleftrightarrow> nonblockingness_language (cfgLM.unmarked_language G) (cfgLM.marked_language G))
  \<and> (nonblockingness_language (cfgSTD.unmarked_language G) (cfgSTD.marked_language G)
  \<longleftrightarrow> nonblockingness_language (cfgRM.unmarked_language G) (cfgRM.marked_language G))
  \<and> nonblockingness_language (cfgSTD.unmarked_language G) (cfgSTD.marked_language G)"
  apply(rule conjI)
   apply (metis cfgLM_inst_Nonblockingness_branching_correspond1 cfgSTD_Nonblockingness_branching_to_cfgLM_Nonblockingness_branching cfgSTD_inst_Nonblockingness_branching_correspond1)
  apply(rule conjI)
   apply (metis cfgRM_inst_Nonblockingness_branching_correspond1 cfgSTD.AX_BF_Bra_OpLa cfgSTD_Nonblockingness_branching_to_cfgRM_Nonblockingness_branching)
  apply (metis cfgRM_inst_Nonblockingness_branching_correspond1 cfgSTD.AX_BF_Bra_OpLa cfgSTD_Nonblockingness_branching_to_cfgRM_Nonblockingness_branching)
  done

lemma cfgRM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching_hlp: "
       valid_cfg G \<Longrightarrow>
       cfgRM.Nonblockingness_branching G \<Longrightarrow>
       ATS.derivation_initial cfg_initial_configurations
        cfgSTD_step_relation G dh \<Longrightarrow>
       maximum_of_domain dh n \<Longrightarrow>
       dh n = Some (pair e \<lparr>cfg_conf = w\<rparr>) \<Longrightarrow>
       \<exists>dc. cfgSTD.derivation G dc \<and>
            cfgLM.belongs G dc \<and>
            Ex (maximum_of_domain dc) \<and>
            derivation_append_fit dh dc n \<and>
            cfg_marking_condition G (derivation_append dh dc n)"
  apply(induct "length(filterA w)" arbitrary: dh n e w)
   apply(rename_tac w dh n e)(*strict*)
   apply(subgoal_tac "\<exists>wx. liftB wx = w")
    apply(rename_tac w dh n e)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w"
      in exI)
    apply(rule liftBDeConv2)
    apply(rule filterA_setA)
    apply(force)
   apply(rename_tac w dh n e)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB wx\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply (metis cfgSTD.der1_is_derivation)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule cfgSTD.der1_belongs)
    apply(rule cfgSTD.belongs_configurations)
     apply(rename_tac dh n e wx)(*strict*)
     apply(rule cfgSTD.derivation_initial_belongs)
      apply(rename_tac dh n e wx)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply (metis der1_maximum_of_domain)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(simp add: derivation_append_fit_def der1_def)
   apply(rename_tac dh n e wx)(*strict*)
   apply(simp add: cfg_marking_condition_def derivation_append_def der1_def cfg_marking_configuration_def)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: setA_liftB)
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac dh n e wx)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx)(*strict*)
   apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w = wx1 @[teA A]@liftB wx2")
   apply(rename_tac x w dh n e)(*strict*)
   prefer 2
   apply(rule filterA_gt_0_then_rm_nonterminal)
   apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(subgoal_tac "A \<in> cfgRM_Nonblockingness_nonterminals G")
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfgRM_accessible_nonterminals G"
      in set_mp)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(rule cfgRM_Nonblockingness_branching_implies_cfgRM_accessible_nonterminals_contained_in_cfgRM_Nonblockingness_nonterminals)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      A="cfgSTD_accessible_nonterminals_ALT G"
      in set_mp)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(rule cfgSTD_accessible_nonterminals_ALT_contained_in_cfgRM_accessible_nonterminals)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(simp add: cfgSTD_accessible_nonterminals_ALT_def)
   apply(subgoal_tac "\<lparr>cfg_conf = wx1 @ teA A # liftB wx2\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    prefer 2
    apply(rule cfgSTD.belongs_configurations)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(rule cfgSTD.derivation_initial_belongs)
      apply(rename_tac x dh n e wx1 A wx2)(*strict*)
      apply(force)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule conjI)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(simp add: cfg_configurations_def setAConcat)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfgRM_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(case_tac na)
   apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' nat)(*strict*)
  apply(rename_tac na)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule_tac
      x="wx1@ w' @ liftB wx2"
      in meta_allE)
  apply(erule_tac
      x="derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) n) (n+Suc na)"
      in meta_allE)
  apply(erule_tac
      x="n+Suc na"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule setA_empty_filterA_empty)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_derivation)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
      apply (metis cfgRM_derivations_are_cfg_derivations)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na i eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2 l r)(*strict*)
    apply(rule_tac
      x="wx1 @ l"
      in exI)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(simp add: derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) dc (Suc na)) (Suc na+x)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule cfgSTD.derivation_take_preserves_derivation)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(rule cfgSTD.derivation_map_preserves_derivation)
       apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
       apply (metis cfgRM_derivations_are_cfg_derivations)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x i eb c)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2 l r)(*strict*)
     apply(rule_tac
      x="wx1 @ l"
      in exI)
     apply(clarsimp)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(simp add: derivation_map_def)
   apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
   apply(case_tac "dc 0")
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(rule_tac
      d="dh"
      in cfgRM.belongs_configurations)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule_tac
      x="(Suc na + x)"
      in exI)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def derivation_append_fit_def derivation_take_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) n) (Suc (n + na))) dc (Suc (n + na))) = (derivation_append dh (derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) dc (Suc na)) (Suc na + x)) n)")
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule ext)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def derivation_append_fit_def derivation_take_def)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "dc (xa - Suc (n + na))")
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(rule_tac
      d="dc"
      and n="x"
      and m="(xa - Suc (n + na))"
      in cfgSTD.no_some_beyond_maximum_of_domain)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  done

corollary cfgRM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G"
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac dh n)(*strict*)
   apply(simp add: maximum_of_domain_def get_configuration_def)
  apply(rename_tac dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w)(*strict*)
  apply(rule cfgRM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching_hlp)
      apply(rename_tac dh n e w)(*strict*)
      apply(force)
     apply(rename_tac dh n e w)(*strict*)
     apply(force)
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  done

lemma construct_elimininating_derivation_rm: "
  valid_cfg G'
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> \<exists>d n e v.
  cfgRM.derivation G' d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>)
  \<and> d n = Some (pair e \<lparr>cfg_conf=liftB v\<rparr>)"
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
   prefer 2
   apply(rule canElimCombine)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def)
  apply(simp add: cfgSTD.derivation_to_def)
  apply(simp add: cfgSTD.derivation_from_def)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac d w' n x)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' n x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation G' d' \<and> maximum_of_domain d' n \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d' n = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac d w' n x)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac d w' n x)(*strict*)
        apply(force)
       apply(rename_tac d w' n x)(*strict*)
       apply(force)
      apply(rename_tac d w' n x)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac d w' n x)(*strict*)
     apply(force)
    apply(rename_tac d w' n x)(*strict*)
    apply(force)
   apply(rename_tac d w' n x)(*strict*)
   apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x d' e)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="filterB w'"
      in exI)
  apply (metis liftBDeConv2)
  done

end
