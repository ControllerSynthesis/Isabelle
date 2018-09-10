section {*FUNCTION\_\_VALID\_ITEM\_SETS\_CONFLICTFREE*}
theory
  FUNCTION__VALID_ITEM_SETS_CONFLICTFREE

imports
  FUNCTION__VALID_ITEM_SETS

begin

definition item_shift_reduce_conflict :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> bool"
  where
    "item_shift_reduce_conflict G k I1 I2 \<equiv>
  case cfg_item_rhs2 I1 of
    teB a # \<beta> \<Rightarrow>
      cfg_item_rhs2 I2 = []
      \<and> cfg_item_look_ahead I2 \<in> cfgSTD_first G k (cfg_item_rhs2 I1 @ liftB (cfg_item_look_ahead I1))
    | _  \<Rightarrow> False"

definition item_reduce_reduce_conflict :: "
  ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> bool"
  where
    "item_reduce_reduce_conflict I1 I2 \<equiv>
  cfg_item_rhs2 I1 = []
  \<and> cfg_item_rhs2 I2 = []
  \<and> cfg_item_look_ahead I1 = cfg_item_look_ahead I2
  \<and> I1 \<noteq> I2"

definition conflict_free :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "conflict_free G G' k \<equiv>
  \<forall>w.
    set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
    \<longrightarrow> (\<forall>I1 I2.
            I1 \<in> valid_item_set G' k w
            \<and> I2 \<in> valid_item_set G' k w
            \<and> item_core I1 \<in> cfg_productions G
            \<and> item_core I2 \<in> cfg_productions G
            \<longrightarrow> (\<not> (item_reduce_reduce_conflict I1 I2)))
  \<and> (\<forall>I1 I2.
      I1 \<in> valid_item_set G' k w
      \<and> I2 \<in> valid_item_set G' k w
      \<and> item_core I1 \<in> cfg_productions G
      \<and> item_core I2 \<in> cfg_productions G
      \<longrightarrow> (\<not> (item_shift_reduce_conflict G' k I1 I2)))"

definition conflict_free_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "conflict_free_ALT G G' k \<equiv>
  \<forall>w I1 I2.
    setA w \<subseteq> cfg_nonterminals G'
    \<longrightarrow> setB w \<subseteq> cfg_events G'
    \<longrightarrow> I1 \<in> valid_item_set G' k w
    \<longrightarrow> I2 \<in> valid_item_set G' k w
    \<longrightarrow> item_core I1 \<in> cfg_productions G
    \<longrightarrow> item_core I2 \<in> cfg_productions G
    \<longrightarrow> (\<not> item_reduce_reduce_conflict I1 I2
      \<and> \<not> item_shift_reduce_conflict G' k I1 I2)"

lemma conflict_free_vs_conflict_free_ALT: "
  conflict_free G G' k = conflict_free_ALT G G' k"
  apply(simp add: conflict_free_ALT_def conflict_free_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(erule_tac x="w" in allE)
   apply(erule impE)
    apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(erule_tac x="w" in allE)
   apply(erule impE)
    apply (metis two_elements_construct_domain_setA)
   apply(erule impE)
    apply (metis two_elements_construct_domain_setB)
   apply(clarsimp)
  apply(erule_tac x="w" in allE)
  apply(erule impE)
   apply (metis two_elements_construct_domain_setA)
  apply(erule impE)
   apply (metis two_elements_construct_domain_setB)
  apply(clarsimp)
  done

lemma from_dollaraugmented_to_input_derivation: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfgRM.derivation_initial G' d
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> d (Suc 0) \<noteq> None
  \<Longrightarrow> cfgRM.derivation G (derivation_drop (derivation_map d (\<lambda>c. c\<lparr>cfg_conf := drop (Suc 0) (butlast (cfg_conf c)) \<rparr>)) (Suc 0))"
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
   prefer 2
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_CFG_AUGMENT__input_def valid_cfg_def)
  apply(simp (no_asm) add: cfgRM.derivation_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(case_tac i)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(case_tac y)
   apply(rename_tac y option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat)(*strict*)
  apply(simp add: derivation_drop_def derivation_map_def)
  apply(case_tac "d (Suc (Suc nat))")
   apply(rename_tac y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac y nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (Suc nat) = Some (pair e1 c1) \<and> d (Suc (Suc nat)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
   apply(rename_tac y nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(Suc nat)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac y nat a)(*strict*)
     apply(force)
    apply(rename_tac y nat a)(*strict*)
    apply(force)
   apply(rename_tac y nat a)(*strict*)
   apply(force)
  apply(rename_tac y nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf c1=[teB Do]@w@[teB Do]")
   apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
    apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
   apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 w)(*strict*)
  apply(simp add: derivation_drop_def derivation_map_def)
  apply(case_tac nat)
   apply(rename_tac y nat e1 e2 c1 c2 w)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 w)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 w l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac e1 e2 c1 c2 w l r)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c1 c2 w l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 w r list)(*strict*)
   apply(case_tac r)
    apply(rename_tac e1 e2 c1 c2 w r list)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c1 c2 w r list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
    apply(rename_tac e1 e2 c1 c2 w r list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac e1 e2 c1 c2 w r list a lista)(*strict*)
   apply(thin_tac "r=a#lista")
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 list w')(*strict*)
   apply(rule conjI)
    apply(rename_tac e1 e2 c1 c2 list w')(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(clarsimp)
    apply(rename_tac e1 c1 c2 list w')(*strict*)
    apply(erule disjE)
     apply(rename_tac e1 c1 c2 list w')(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac e1 c1 c2 list w')(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 list w')(*strict*)
   apply(rule_tac
      x="list"
      in exI)
   apply(rule_tac
      x="w'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac e1 e2 c1 c2 list w')(*strict*)
    apply (metis butlast_snoc_3)
   apply(rename_tac e1 e2 c1 c2 list w')(*strict*)
   apply (metis setA_Concat2 empty_subsetI subset_empty)
  apply(rename_tac y nat e1 e2 c1 c2 w nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac y e1 e2 c1 c2 w nata)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac y e1 e2 c1 c2 w nata l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac y e1 e2 c1 c2 w nata l r)(*strict*)
   apply(force)
  apply(rename_tac y e1 e2 c1 c2 w nata l r a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac y e1 e2 c1 c2 w nata r list)(*strict*)
  apply(case_tac r)
   apply(rename_tac y e1 e2 c1 c2 w nata r list)(*strict*)
   apply(force)
  apply(rename_tac y e1 e2 c1 c2 w nata r list a lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
   apply(rename_tac y e1 e2 c1 c2 w nata r list a lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac y e1 e2 c1 c2 w nata r list a lista)(*strict*)
  apply(thin_tac "r=a#lista")
  apply(clarsimp)
  apply(rename_tac y e1 e2 c1 c2 nata list w')(*strict*)
  apply(rule conjI)
   apply(rename_tac y e1 e2 c1 c2 nata list w')(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(rename_tac y e1 c1 c2 nata list w')(*strict*)
   apply(erule disjE)
    apply(rename_tac y e1 c1 c2 nata list w')(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac y e1 c1 c2 nata list w')(*strict*)
   apply(clarsimp)
  apply(rename_tac y e1 e2 c1 c2 nata list w')(*strict*)
  apply(rule_tac
      x="list"
      in exI)
  apply(rule_tac
      x="w'"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac y e1 e2 c1 c2 nata list w')(*strict*)
   apply (metis butlast_snoc_3)
  apply(rename_tac y e1 e2 c1 c2 nata list w')(*strict*)
  apply (metis setA_Concat2 empty_subsetI subset_empty)
  done

lemma from_dollaraugmented_to_input_derivation_initial: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> d (Suc 0) \<noteq> None
  \<Longrightarrow> cfgRM.derivation_initial G' d
  \<Longrightarrow> cfgRM.derivation_initial G (derivation_drop (derivation_map d (\<lambda>c. c\<lparr>cfg_conf := drop (Suc 0) (butlast (cfg_conf c)) \<rparr>)) (Suc 0))"
  apply(rule cfgRM.derivation_initialI)
   apply(rule from_dollaraugmented_to_input_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: cfgRM.derivation_initial_def)
   apply(force)
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac y c)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "d 0")
     apply(rename_tac y c)(*strict*)
     apply(clarsimp)
    apply(rename_tac y c a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac y c a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac y c b)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: derivation_drop_def derivation_map_def)
  apply(simp add: cfgRM.derivation_initial_def)
  apply(case_tac "d 0")
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
  apply(rename_tac c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(simp add: get_configuration_def cfg_initial_configurations_def cfg_configurations_def)
  apply(clarsimp)
  apply(simp add: valid_cfg_def F_CFG_AUGMENT__input_def)
  done

lemma cfg_LRk_to_cfg_LRkDo: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> cfg_LRk G k
  \<Longrightarrow> cfg_LRkDo G' Do S' k"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(force)
  apply(subgoal_tac "teB Do \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_events G) \<notin> cfg_events G")
    apply(force)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(unfold cfg_LRkDo_def)
  apply(rule allI)+
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule impI)+
  apply(erule conjE)+
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf \<lparr>cfg_conf = \<delta>1 @ [teA A1] @ liftB y1\<rparr>=[teB Do]@w@[teB Do]")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v c)(*strict*)
    apply(case_tac "d2 0")
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v c a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v c a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v c b)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf \<lparr>cfg_conf = \<delta>2 @ [teA A2] @ liftB y2\<rparr>=[teB Do]@w@[teB Do]")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w c)(*strict*)
    apply(case_tac "d1 0")
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w c a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w c a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w c b)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(unfold cfg_LRk_def)
  apply(erule_tac
      x="derivation_drop (derivation_map d1 (\<lambda>c. c\<lparr>cfg_conf:=drop(Suc 0)(butlast(cfg_conf c))\<rparr>)) (Suc 0)"
      in allE)
  apply(erule_tac
      x="n1"
      in allE)
  apply(erule_tac
      x="drop (Suc 0) \<delta>1"
      in allE)
  apply(erule_tac
      x="A1"
      in allE)
  apply(erule_tac
      x="butlast y1"
      in allE)
  apply(erule_tac
      x="if n1=0 then None else e1"
      in allE)
  apply(erule_tac
      x="e1'"
      in allE)
  apply(erule_tac
      x="\<omega>1"
      in allE)
  apply(erule_tac
      x="derivation_drop (derivation_map d2 (\<lambda>c. c\<lparr>cfg_conf:=drop(Suc 0)(butlast(cfg_conf c))\<rparr>)) (Suc 0)"
      in allE)
  apply(erule_tac
      x="n2"
      in allE)
  apply(erule_tac
      x="drop (Suc 0) \<delta>2"
      in allE)
  apply(erule_tac
      x="A2"
      in allE)
  apply(erule_tac
      x="butlast y2"
      in allE)
  apply(erule_tac
      x="if n2=0 then None else e2"
      in allE)
  apply(erule_tac
      x="e2'"
      in allE)
  apply(erule_tac
      x="\<omega>2"
      in allE)
  apply(erule_tac
      x="v"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 y1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(case_tac "\<delta>1")
    apply(rename_tac d1 n1 \<delta>1 y1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 y1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   apply(case_tac "\<delta>2")
    apply(rename_tac d1 n1 \<delta>1 y1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 y1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "d1 (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "d1 0")
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w wa)(*strict*)
    apply(case_tac a)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w wa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa b)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(rule from_dollaraugmented_to_input_derivation_initial)
      apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf \<lparr>cfg_conf = \<delta>1 @ [teA A1] @ liftB y1\<rparr>=[teB Do]@w@[teB Do]")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c)(*strict*)
    apply(case_tac "d1 0")
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(case_tac "\<delta>1")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
   apply(case_tac y1)
    apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. y1 = w' @ [x']")
    apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(thin_tac "y1=a#lista")
   apply(clarsimp)
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list w' x')(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(case_tac "\<delta>1")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
   apply(case_tac y1)
    apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. y1 = w' @ [x']")
    apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac d1 n1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(thin_tac "y1=a#lista")
   apply(clarsimp)
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa list w' x')(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v wa list w')(*strict*)
   apply (metis butlast_snoc_3)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "d2 (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "d2 0")
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w wa)(*strict*)
    apply(case_tac a)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w wa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa b)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(rule from_dollaraugmented_to_input_derivation_initial)
      apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf \<lparr>cfg_conf = \<delta>2 @ [teA A2] @ liftB y2\<rparr>=[teB Do]@w@[teB Do]")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c)(*strict*)
    apply(case_tac "d2 0")
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa c)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(case_tac "\<delta>2")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
   apply(case_tac y2)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. y2 = w' @ [x']")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(thin_tac "y2=a#lista")
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w wa list w' x')(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(case_tac "\<delta>2")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
   apply(case_tac y2)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. y2 = w' @ [x']")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(thin_tac "y2=a#lista")
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w wa list w' x')(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w list w')(*strict*)
   apply (metis butlast_snoc_3)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(case_tac "\<delta>2")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
   apply(case_tac y2)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. y2 = w' @ [x']")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 y2 e2 e2' \<omega>2 v w wa list a lista)(*strict*)
   apply(thin_tac "y2=a#lista")
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w wa list w' x')(*strict*)
   apply(case_tac "\<delta>1")
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w wa list w' x')(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w wa list w' x' a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
  apply(case_tac y2)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. y2 = w' @ [x']")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v w wa a list)(*strict*)
  apply(thin_tac "y2=a#list")
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' x')(*strict*)
  apply(case_tac y1)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' x')(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. y1 = w' @ [x']")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' x' a list)(*strict*)
  apply(thin_tac "y1=a#list")
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' x' w'nonterminal x'nonterminal)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' w'nonterminal)(*strict*)
  apply(case_tac "\<delta>2")
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' w'nonterminal)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 v w wa w' w'nonterminal a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w w' w'nonterminal list)(*strict*)
  apply(case_tac "\<delta>1")
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w w' w'nonterminal list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w w' w'nonterminal list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
  apply(simp add: kPrefix_def)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf \<lparr>cfg_conf = teB Do # list @ \<omega>2 @ liftB w' @ [teB Do]\<rparr>=[teB Do]@w@[teB Do]")
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and i="Suc n2"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c)(*strict*)
    apply(case_tac "d2 0")
     apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf \<lparr>cfg_conf = teB Do # lista @ \<omega>1 @ liftB w'nonterminal @ [teB Do]\<rparr>=[teB Do]@w@[teB Do]")
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and i="Suc n1"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c)(*strict*)
    apply(case_tac "d1 0")
     apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista c)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def get_configuration_def cfg_configurations_def)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d1 n1 A1 e1 e1' \<omega>1 d2 n2 A2 e2 e2' \<omega>2 v w' w'nonterminal list lista)(*strict*)
  apply(thin_tac "cfgRM.derivation_initial G' d1")
  apply(thin_tac "d1 (Suc n1) = Some (pair e1 \<lparr>cfg_conf = teB Do # lista @ teA A1 # liftB w'nonterminal @ [teB Do]\<rparr>)")
  apply(thin_tac "d1 (Suc (Suc n1)) = Some (pair (Some e1') \<lparr>cfg_conf = teB Do # lista @ \<omega>1 @ liftB w'nonterminal @ [teB Do]\<rparr>)")
  apply(thin_tac "cfgRM.derivation_initial G' d2")
  apply(thin_tac "d2 (Suc n2) = Some (pair e2 \<lparr>cfg_conf = teB Do # list @ teA A2 # liftB w' @ [teB Do]\<rparr>)")
  apply(thin_tac "d2 (Suc (Suc n2)) = Some (pair (Some e2') \<lparr>cfg_conf = teB Do # list @ \<omega>2 @ liftB w' @ [teB Do]\<rparr>)")
  apply(thin_tac "d1 (Suc 0) = Some (pair (Some \<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf = [teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
  apply(thin_tac "cfgRM.derivation_initial G (derivation_drop (derivation_map d1 (\<lambda>c. c\<lparr>cfg_conf := drop (Suc 0) (butlast (cfg_conf c))\<rparr>)) (Suc 0))")
  apply(thin_tac "d2 (Suc 0) = Some (pair (Some \<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf = [teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
  apply(thin_tac "cfgRM.derivation_initial G (derivation_drop (derivation_map d2 (\<lambda>c. c\<lparr>cfg_conf := drop (Suc 0) (butlast (cfg_conf c))\<rparr>)) (Suc 0))")
  apply(thin_tac "teA A2 \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "teA A1 \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(clarsimp)
  apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista)(*strict*)
  apply(case_tac "take (k - length w'nonterminal) [Do]")
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista)(*strict*)
   apply(clarsimp)
   apply(case_tac "take (k - (length v + length w')) [Do]")
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista a listb)(*strict*)
   apply(case_tac "k - (length v + length w')")
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista a listb)(*strict*)
    apply(force)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista a listb nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(subgoal_tac "teB Do \<in> set(liftB w'nonterminal)")
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(subgoal_tac "teB Do \<notin> set(liftB w'nonterminal)")
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(force)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in nset_mp)
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(force)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(force)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(rule_tac
      A="set(liftB(take k w'nonterminal))"
      in set_mp)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply (metis set_liftB_commute List.set_take_subset)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(rule_tac
      t="take k w'nonterminal"
      and s="v @ w' @ [Do]"
      in ssubst)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(force)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista a listb)(*strict*)
  apply(clarsimp)
  apply(case_tac "k-length w'nonterminal")
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista a listb)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista a listb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
  apply(case_tac "take (k - (length v + length w')) [Do]")
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "teB Do \<in> set (liftB(w'nonterminal@[Do]))")
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(subgoal_tac "teB Do \<notin> set (liftB(w'nonterminal@[Do]))")
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(force)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    prefer 2
    apply(simp (no_asm) add: liftB_commutes_over_concat)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(rule_tac
      t="w'nonterminal@[Do]"
      and s="take k v @ take (k - length v) w'"
      in ssubst)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(force)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(rule_tac
      B="set(liftB(v@w'))"
      in nset_mp)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(simp (no_asm) add: liftB_commutes_over_concat)
    apply(rule conjI)
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(rule le_supI1)
     apply (smt set_liftB_commute List.set_take_subset)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(rule le_supI2)
    apply (smt set_liftB_commute List.set_take_subset)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in nset_mp)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(simp (no_asm) add: liftB_commutes_over_concat)
    apply(rule conjI)
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(rule_tac
      B="set(lista @ \<omega>1 @ liftB v)"
      in subset_trans)
      apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
      apply(simp (no_asm))
      apply(force)
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(rule_tac
      t="lista @ \<omega>1 @ liftB v"
      and s="list @ \<omega>2"
      in ssubst)
      apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
      apply(force)
     apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
     apply(force)
    apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
    apply(force)
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat)(*strict*)
   apply(force)
  apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat a listb)(*strict*)
  apply(clarsimp)
  apply(case_tac "(k - (length v + length w'))")
   apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat a listb)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<omega>1 \<omega>2 v w' w'nonterminal list lista nat a listb nata)(*strict*)
  apply(clarsimp)
  done

lemma cfg_LRkDo_implies_no_reduce_reduce_item_conflict: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> cfg_LRkDo G' Do S' k
  \<Longrightarrow> \<forall>I1 I2. I1 \<in> valid_item_set G' k w \<and> I2 \<in> valid_item_set G' k w \<and> (item_core I1 \<in> cfg_productions G) \<and> (item_core I2 \<in> cfg_productions G) \<longrightarrow> (\<not> (item_reduce_reduce_conflict I1 I2))"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(force)
  apply(subgoal_tac "teB Do \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_events G) \<notin> cfg_events G")
    apply(force)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac I1 I2)(*strict*)
  apply(simp add: item_reduce_reduce_conflict_def)
  apply(clarsimp)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za)(*strict*)
  apply(case_tac n)
   apply(rename_tac n na A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za)(*strict*)
   apply(clarsimp)
   apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
     apply(clarsimp)
    apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "d 0")
     apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
     apply(clarsimp)
    apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za a)(*strict*)
    apply(clarsimp)
    apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
    apply(force)
   apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e2 z \<delta>' e1a e2a za)(*strict*)
   apply(simp add: item_core_def)
   apply(clarsimp)
   apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> z \<delta>' e1a e2a za)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> z \<delta>' e1a e2a za)(*strict*)
    prefer 2
    apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> z \<delta>' e1a e2a za a list)(*strict*)
    apply(force)
   apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> z \<delta>' e1a e2a za)(*strict*)
   apply(clarsimp)
   apply(rename_tac na Aa \<alpha>' ya d da \<delta>' e1a e2a za)(*strict*)
   apply(case_tac ya)
    apply(rename_tac na Aa \<alpha>' ya d da \<delta>' e1a e2a za)(*strict*)
    prefer 2
    apply(rename_tac na Aa \<alpha>' ya d da \<delta>' e1a e2a za a list)(*strict*)
    apply(force)
   apply(rename_tac na Aa \<alpha>' ya d da \<delta>' e1a e2a za)(*strict*)
   apply(clarsimp)
   apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta>' @ \<alpha>'\<rparr>"
      and P="\<lambda>e. setA (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_nonterminals G)) (cfg_nonterminals G) \<and> setB (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_events G)) (cfg_events G)"
      in ballE)
    apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta>' @ \<alpha>'\<rparr>"
      in ballE)
    apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
    apply(force)
   apply(rename_tac na Aa \<alpha>' d da \<delta>' e1a e2a za)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat)(*strict*)
  apply(case_tac na)
   apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
   apply(subgoal_tac "da (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "da 0")
     apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat a)(*strict*)
    apply(clarsimp)
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e2a za nat)(*strict*)
   apply(simp add: item_core_def)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' za nat)(*strict*)
   apply(case_tac "\<delta>'")
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' za nat)(*strict*)
    prefer 2
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' za nat a list)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' za nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta> @ \<alpha>\<rparr>"
      and P="\<lambda>e. setA (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_nonterminals G)) (cfg_nonterminals G) \<and> setB (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_events G)) (cfg_events G)"
      in ballE)
    apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta> @ \<alpha>\<rparr>"
      in ballE)
    apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> ya d da \<delta> e1 e2 z nat)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(rename_tac na A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
  apply(unfold cfg_LRkDo_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="nat"
      in allE)
  apply(erule_tac
      x="\<delta>"
      in allE)
  apply(erule_tac
      x="A"
      in allE)
  apply(erule_tac
      x="filterB z"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="the e2"
      in allE)
  apply(erule_tac
      x="\<alpha>"
      in allE)
  apply(erule_tac
      x="da"
      in allE)
  apply(erule_tac
      x="nata"
      in allE)
  apply(erule_tac
      x="\<delta>'"
      in allE)
  apply(erule_tac
      x="Aa"
      in allE)
  apply(erule_tac
      x="filterB za"
      in allE)
  apply(erule_tac
      x="e1a"
      in allE)
  apply(erule_tac
      x="the e2a"
      in allE)
  apply(erule_tac
      x="\<alpha>'"
      in allE)
  apply(erule_tac
      x="[]"
      in allE)
  apply(erule impE)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
  apply(rule conjI)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
  apply(rule conjI)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
   apply(clarsimp)
   apply (metis liftBDeConv2)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (Suc nat) = Some (pair e1 c1) \<and> d (Suc (Suc nat)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(Suc nat)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
     apply(force)
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
   apply(force)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 e2 z \<delta>' e1a e2a za nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a e2a za nat nata e2b)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. da (Suc nata) = Some (pair e1 c1) \<and> da (Suc (Suc nata)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a e2a za nat nata e2b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(Suc nata)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a e2a za nat nata e2b)(*strict*)
     apply(force)
    apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a e2a za nat nata e2b)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a e2a za nat nata e2b)(*strict*)
   apply(force)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a e2a za nat nata e2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
   apply (metis liftBDeConv2)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
   apply (metis liftBDeConv2)
  apply(rename_tac A Aa \<alpha> \<alpha>' ya d da \<delta> e1 z \<delta>' e1a za nat nata e2b e2)(*strict*)
  apply(simp add: kPrefix_def)
  apply(metis liftBDeConv1 filterB_take)
  done

lemma cfg_LRkDo_implies_no_shift_reduce_item_conflict: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> cfg_LRkDo G' Do S' k
  \<Longrightarrow> \<forall>I1 I2. I1 \<in> valid_item_set G' k w \<and> I2 \<in> valid_item_set G' k w \<and> (item_core I1 \<in> cfg_productions G) \<and> (item_core I2 \<in> cfg_productions G) \<longrightarrow> (\<not> (item_shift_reduce_conflict G' k I1 I2))"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(force)
  apply(subgoal_tac "teB Do \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_events G) \<notin> cfg_events G")
    apply(force)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac I1 I2)(*strict*)
  apply(simp add: item_shift_reduce_conflict_def)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' \<beta> \<beta>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za)(*strict*)
  apply(case_tac "\<beta>")
   apply(rename_tac n na A Aa \<alpha> \<alpha>' \<beta> \<beta>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za)(*strict*)
   apply(force)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' \<beta> \<beta>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' \<beta>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac n na A Aa \<alpha> \<alpha>' \<beta>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' \<beta>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b)(*strict*)
  apply(case_tac n)
   apply(rename_tac n na A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
     apply(clarsimp)
    apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "d 0")
     apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
     apply(clarsimp)
    apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b a)(*strict*)
    apply(clarsimp)
    apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
    apply(force)
   apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e2 z \<delta>' e1a e2a za list b)(*strict*)
   apply(simp add: item_core_def)
   apply(clarsimp)
   apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> z \<delta>' e1a e2a za list b)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> z \<delta>' e1a e2a za list b)(*strict*)
    prefer 2
    apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> z \<delta>' e1a e2a za list b a lista)(*strict*)
    apply(force)
   apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> z \<delta>' e1a e2a za list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta>' @ \<alpha>' @ teB b # list\<rparr>"
      and P="\<lambda>e. setA (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_nonterminals G)) (cfg_nonterminals G) \<and> setB (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_events G)) (cfg_events G)"
      in ballE)
    apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta>' @ \<alpha>' @ teB b # list\<rparr>"
      in ballE)
    apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
    apply(force)
   apply(rename_tac na Aa \<alpha>' y ya d da \<delta>' e1a e2a za list b)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(rename_tac n na A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat)(*strict*)
  apply(case_tac na)
   apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
   apply(subgoal_tac "da (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def)
    apply(case_tac "da 0")
     apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat a)(*strict*)
    apply(clarsimp)
    apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e2a za list b nat)(*strict*)
   apply(simp add: item_core_def)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' za list b nat)(*strict*)
   apply(case_tac "\<delta>'")
    apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' za list b nat)(*strict*)
    prefer 2
    apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' za list b nat a lista)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' za list b nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta> @ \<alpha>\<rparr>"
      and P="\<lambda>e. setA (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_nonterminals G)) (cfg_nonterminals G) \<and> setB (prod_rhs e) \<subseteq> insert (F_FRESH (cfg_events G)) (cfg_events G)"
      in ballE)
    apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = \<delta> @ \<alpha>\<rparr>"
      in ballE)
    apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> y ya d da \<delta> e1 e2 z list b nat)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(rename_tac na A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac A Aa \<alpha> \<alpha>' y ya d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata)(*strict*)
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db e1b n)(*strict*)
  apply(case_tac n)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db e1b n)(*strict*)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
   apply(unfold cfg_LRkDo_def)[1]
   apply(erule_tac
      x="da"
      in allE)
   apply(erule_tac
      x="nata"
      in allE)
   apply(erule_tac
      x="\<delta>'"
      in allE)
   apply(erule_tac
      x="Aa"
      in allE)
   apply(erule_tac
      x="filterB za"
      in allE)
   apply(erule_tac
      x="e1a"
      in allE)
   apply(erule_tac
      x="the e2a"
      in allE)
   apply(erule_tac
      x="\<alpha>'"
      in allE)
   apply(erule_tac
      x="d"
      in allE)
   apply(erule_tac
      x="nat"
      in allE)
   apply(erule_tac
      x="\<delta>"
      in allE)
   apply(erule_tac
      x="A"
      in allE)
   apply(erule_tac
      x="filterB z"
      in allE)
   apply(erule_tac
      x="e1"
      in allE)
   apply(erule_tac
      x="the e2"
      in allE)
   apply(erule_tac
      x="\<alpha>@teB b#list"
      in allE)
   apply(erule_tac
      x="filterB (teB b# list)"
      in allE)
   apply(erule impE)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
   apply(rule conjI)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
   apply(rule conjI)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
    apply(clarsimp)
    apply (metis liftBDeConv2)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (Suc nat) = Some (pair e1 c1) \<and> d (Suc (Suc nat)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(Suc nat)"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
      apply(force)
     apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
     apply(force)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db)(*strict*)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a e2a za list b nat nata x db e2b)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. da (Suc nata) = Some (pair e1 c1) \<and> da (Suc (Suc nata)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a e2a za list b nat nata x db e2b)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(Suc nata)"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a e2a za list b nat nata x db e2b)(*strict*)
      apply(force)
     apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a e2a za list b nat nata x db e2b)(*strict*)
     apply(force)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a e2a za list b nat nata x db e2b)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a e2a za list b nat nata x db e2b)(*strict*)
   apply(clarsimp)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule conjI)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis liftBDeConv2)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule conjI)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule conjI)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis liftBDeConv2)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule conjI)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis setA_Concat2 setA_liftB setA_take_head liftB.simps(2) liftBDeConv2 append_eq_appendI subset_empty)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(simp add: kPrefix_def)
   apply(rule_tac
      t="take k (filterB za)"
      and s="filterB (take k za)"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis filterB_take)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule_tac
      t="take k za"
      and s="liftB (take k x)"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule_tac
      t="filterB (liftB (take k x))"
      and s="take k x"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis filterB_take take_liftB_co)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule liftB_inj)
   apply(rule_tac
      t="liftB (take k x)"
      and s="take k (liftB x)"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (smt take_liftB)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule_tac
      t="liftB x"
      and s="teB b # list @ liftB y"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply(force)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule_tac
      t="liftB (take k (b # filterB list @ filterB z))"
      and s=" (take k (liftB (b # filterB list @ filterB z))) "
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis take_liftB)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(simp (no_asm) add: liftB_commutes_over_concat)
   apply(rule_tac
      t="liftB (filterB z)"
      and s="z"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (metis liftBDeConv2)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply(rule_tac
      t="liftB (filterB list)"
      and s="list"
      in ssubst)
    apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
    apply (rule liftBDeConv2)
    apply (metis setA_Concat2 setA_liftB setA_take_head subset_empty)
   apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 z \<delta>' e1a za list b nat nata x db e2b e2)(*strict*)
   apply (metis append_Cons take_liftB take_shift)
  apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db e1b n natb)(*strict*)
  apply(clarsimp)
  apply(rename_tac A Aa \<alpha> \<alpha>' y d da \<delta> e1 e2 z \<delta>' e1a e2a za list b nat nata x db e1b natb)(*strict*)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n3)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n3)(*strict*)
  apply(rename_tac n)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation G' d' \<and> maximum_of_domain d' (Suc n) \<and> d' 0 = Some (pair None \<lparr>cfg_conf = teB a # \<beta> @ liftB z\<rparr>) \<and> d' (Suc n) = Some (pair e \<lparr>cfg_conf=liftB x\<rparr>)")
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
   prefer 2
   apply(rule_tac
      d="db"
      in cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
        apply(force)
       apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
       apply(force)
      apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
      apply(force)
     apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
   apply (metis setA_liftB)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x db e1b n)(*strict*)
  apply(thin_tac "cfgSTD.derivation G' db")
  apply(thin_tac "maximum_of_domain db (Suc n)")
  apply(thin_tac "db 0 = Some (pair None \<lparr>cfg_conf = teB a # \<beta> @ liftB z\<rparr>)")
  apply(thin_tac "db (Suc n) = Some (pair e1b \<lparr>cfg_conf = liftB x\<rparr>)")
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' n = Some (pair e1 c1) \<and> d' (Suc n) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e)(*strict*)
   apply(force)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e)(*strict*)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b e2b c1)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b e2b c1 l r)(*strict*)
  apply(case_tac e2b)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b e2b c1 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A2 \<omega>2)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b e2b c1 l r A2 \<omega>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b c1 l r A2 \<omega>2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b c1 l r A2 \<omega>2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
  apply(subgoal_tac "\<exists>w. [teB a]@w@(liftB z)=l @ teA A2 # r")
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d'"
      and i="0"
      and j="n"
      in CFGRM_terminals_stays_context)
         apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
         apply(force)
        apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
        apply(force)
       apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
       apply(force)
      apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
      apply (metis setA_liftB)
     apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
   apply(force)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2 w)(*strict*)
  apply(case_tac l)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2 w)(*strict*)
   apply(force)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b l r A2 \<omega>2 w aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b r A2 \<omega>2 w list)(*strict*)
  apply(subgoal_tac "suffix r (liftB z)")
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b r A2 \<omega>2 w list)(*strict*)
   prefer 2
   apply(rule_tac
      l="[]"
      and v="w"
      and w="list"
      and A="A2"
      and ra="r"
      in suffix_tails_terminal)
     apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b r A2 \<omega>2 w list)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b r A2 \<omega>2 w list)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b r A2 \<omega>2 w list)(*strict*)
   apply(force)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b r A2 \<omega>2 w list)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 list c)(*strict*)
  apply(rename_tac \<alpha>' y')
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(subgoal_tac "\<exists>d. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>) \<and> d (Suc n1) = Some (pair e1 \<lparr>cfg_conf = \<delta>2' @ teA A # y2'\<rparr>) \<and> d(Suc (Suc n1)) = Some (pair e2 \<lparr>cfg_conf = \<delta>2' @ \<alpha> @ teB a # \<beta> @ y2'\<rparr>) \<and> d (Suc (Suc n1)+n) = Some (pair (if n=0 then e2 else e1b) \<lparr>cfg_conf = \<delta>2' @ \<alpha> @ teB a # \<alpha>' @ teA A2 # y' @ liftB z @ (drop k y2')\<rparr>) \<and> d (Suc(Suc n1)+Suc n) = Some (pair (Some \<lparr>prod_lhs = A2, prod_rhs = \<omega>2\<rparr>) \<lparr>cfg_conf = \<delta>2' @ \<alpha> @ teB a # \<alpha>' @ \<omega>2 @ y' @ liftB z @ (drop k y2')\<rparr>) \<and> maximum_of_domain d (Suc(Suc n1)+Suc n) ")
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(thin_tac "cfgRM.derivation G' d1")
   apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
   apply(thin_tac "d1 (Suc n1) = Some (pair e1 \<lparr>cfg_conf = \<delta>2' @ teA A # y2'\<rparr>)")
   apply(thin_tac "d1 (Suc (Suc n1)) = Some (pair e2 \<lparr>cfg_conf = \<delta>2' @ \<alpha> @ teB a # \<beta> @ y2'\<rparr>)")
   apply(thin_tac "maximum_of_domain d1 (Suc (Suc n1))")
   apply(thin_tac "cfgRM.derivation G' d'")
   apply(thin_tac "maximum_of_domain d' (Suc n)")
   apply(thin_tac "d' 0 = Some (pair None \<lparr>cfg_conf = teB a # \<beta> @ liftB z\<rparr>)")
   apply(thin_tac "d' (Suc n) = Some (pair (Some \<lparr>prod_lhs = A2, prod_rhs = \<omega>2\<rparr>) \<lparr>cfg_conf = teB a # \<alpha>' @ \<omega>2 @ y' @ liftB z\<rparr>)")
   apply(thin_tac "d' n = Some (pair e1b \<lparr>cfg_conf = teB a # \<alpha>' @ teA A2 # y' @ liftB z\<rparr>)")
   apply(clarsimp)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(unfold cfg_LRkDo_def)[1]
   apply(erule_tac
      x="d2"
      in allE)
   apply(erule_tac
      x="n2"
      in allE)
   apply(erule_tac
      x="\<delta>1"
      in allE)
   apply(erule_tac
      x="B"
      in allE)
   apply(erule_tac
      x="filterB y1"
      in allE)
   apply(erule_tac
      x="e1a"
      in allE)
   apply(erule_tac
      x="the e2a"
      in allE)
   apply(erule_tac
      x="\<omega>"
      in allE)
   apply(erule_tac
      x="d"
      in allE)
   apply(erule_tac
      x="(Suc (n1 + n))"
      in allE)
   apply(erule_tac
      x="\<delta>2' @ \<alpha> @ teB a # \<alpha>'"
      in allE)
   apply(erule_tac
      x="A2"
      in allE)
   apply(erule_tac
      x="filterB (y'@y2')"
      in allE)
   apply(erule_tac
      x="if n=0 then e2 else e1b"
      in allE)
   apply(erule_tac
      x="\<lparr>prod_lhs = A2, prod_rhs = \<omega>2\<rparr>"
      in allE)
   apply(erule_tac
      x="\<omega>2"
      in allE)
   apply(erule_tac
      x="filterB (teB a # \<alpha>' @ \<omega>2)"
      in allE)
   apply(erule impE)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(clarsimp)
    apply (metis liftBDeConv2)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (Suc n2) = Some (pair e1 c1) \<and> d2 (Suc (Suc n2)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G' c1 e2 c2")
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(Suc n2)"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
      apply(force)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(clarsimp)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply (metis liftBDeConv2)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(clarsimp)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule_tac
      t="liftB (filterB (y' @ y2'))"
      and s="y'@y2'"
      in ssubst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply (rule liftBDeConv2)
     apply (metis setA_Concat2 setA_app empty_subsetI subset_empty)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="liftB z"
      and s="take k y2'"
      in subst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule_tac
      t="take k y2' @ drop k y2'"
      and s="y2'"
      in ssubst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(rule append_take_drop_id)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(clarsimp)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(rule_tac
      t="liftB (filterB (y' @ y2'))"
      and s="y'@y2'"
      in ssubst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
     apply (rule liftBDeConv2)
     apply (metis setA_Concat2 setA_app empty_subsetI subset_empty)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(clarsimp)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule_tac
      t="liftB z"
      and s="take k y2'"
      in subst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule_tac
      t="take k y2' @ drop k y2'"
      and s="y2'"
      in ssubst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(rule append_take_drop_id)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(clarsimp)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(rule conjI)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
    apply(clarsimp)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule_tac
      t="liftB (filterB (\<alpha>' @ \<omega>2))"
      and s="\<alpha>'@\<omega>2"
      in ssubst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply (rule liftBDeConv2)
     apply(rule order_antisym)
      apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
      apply(rule_tac
      B="setA(teB a # \<alpha>' @ \<omega>2 @ y' @ liftB z)"
      in subset_trans)
       apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
       apply(simp (no_asm))
       apply(simp add: setAConcat)
      apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
      apply(rule_tac
      t="teB a # \<alpha>' @ \<omega>2 @ y' @ liftB z"
      and s="liftB x"
      in ssubst)
       apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
       apply(force)
      apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
      apply(simp (no_asm))
      apply(rule setA_liftB_empty)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d)(*strict*)
   apply(clarsimp)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="a # filterB (\<alpha>' @ \<omega>2) @ filterB (y' @ y2')"
      and s="filterB (teB a # \<alpha>' @ \<omega>2 @ y' @ y2')"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(simp add: filterB_commutes_over_concat)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="y2'"
      and s="take k y2' @ (drop k y2')"
      in subst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule append_take_drop_id)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="teB a # \<alpha>' @ \<omega>2 @ y' @ take k y2' @ drop k y2'"
      and s="(teB a # \<alpha>' @ \<omega>2 @ y' @ take k y2') @ drop k y2'"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="take k y2'"
      and s="liftB z"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="(teB a # \<alpha>' @ \<omega>2 @ y' @ liftB z)"
      and s="liftB x"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="kPrefix k (filterB y1)"
      and s="take k (filterB y1)"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="kPrefix k (filterB (liftB x @ drop k y2'))"
      and s="take k (filterB (liftB x @ drop k y2'))"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="take k (filterB y1)"
      and s="filterB(take k y1)"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply (metis filterB_take)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      t="take k (filterB (liftB x @ drop k y2'))"
      and s="filterB(take k ((liftB x @ drop k y2')))"
      in subst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply (rule filterB_take)
    apply(simp (no_asm) add: setAConcat)
    apply(rule conjI)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(rule setA_liftB_empty)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply (metis setADropIndexSubset2 subset_empty)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      f="filterB"
      in arg_cong)
   apply(rule_tac
      t="take k y1"
      and s="liftB (take k x)"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(simp (no_asm))
   apply(rule_tac
      t="take k (liftB x)"
      and s="liftB (take k x)"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply (metis take_liftB)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(simp (no_asm))
   apply(case_tac "length y2' \<le> k")
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule disjI1)
   apply(clarsimp)
   apply(rule_tac
      t="liftB z"
      and s="take k y2'"
      in ssubst)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(rule_tac
      j="length(take k y2')"
      in le_trans)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(rule_tac
      t="length (take k y2')"
      and s="k"
      in ssubst)
     apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
     apply(rule take_all_length)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
    apply(force)
   apply(rename_tac A B \<alpha> \<omega> z d2 \<delta>2' e1 e2 y2' \<delta>1 e1a y1 \<beta> a n1 n2 x n e1b A2 \<omega>2 \<alpha>' y' d e2b)(*strict*)
   apply(force)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(thin_tac "cfg_LRkDo G' Do S' k")
  apply(thin_tac "teB Do \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "item_core \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr> \<in> cfg_productions G")
  apply(thin_tac "item_core \<lparr>cfg_item_lhs = B, cfg_item_rhs1 = \<omega>, cfg_item_rhs2 = [], cfg_item_look_ahead = take k x\<rparr> \<in> cfg_productions G")
  apply(thin_tac "cfgRM.derivation G' d2")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
  apply(thin_tac "d2 (Suc n2) = Some (pair e1a \<lparr>cfg_conf = \<delta>1 @ teA B # y1\<rparr>)")
  apply(thin_tac "d2 (Suc (Suc n2)) = Some (pair e2a \<lparr>cfg_conf = \<delta>1 @ \<omega> @ y1\<rparr>)")
  apply(thin_tac "take k y1 = liftB (take k x)")
  apply(thin_tac "\<delta>2' @ \<alpha> = \<delta>1 @ \<omega>")
  apply(thin_tac "maximum_of_domain d1 (Suc (Suc n1))")
  apply(thin_tac "maximum_of_domain d2 (Suc (Suc n2))")
  apply(thin_tac "setA y1 = {}")
  apply(thin_tac "\<lparr>prod_lhs = A2, prod_rhs = \<omega>2\<rparr> \<in> cfg_productions G'")
  apply(thin_tac "liftB x = teB a # \<alpha>' @ \<omega>2 @ y' @ liftB z")
  apply(thin_tac "setA (y' @ liftB z) = {}")
  apply(rule_tac
      x="derivation_append d1 (derivation_map d' (\<lambda>v. \<lparr>cfg_conf = \<delta>2' @ \<alpha> @ cfg_conf v @ (drop k y2')\<rparr>)) (Suc (Suc n1))"
      in exI)
  apply(rule conjI)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation2)
     apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
     apply(force)
    apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' \<beta> a n1 n d' e1b A2 \<omega>2 \<alpha>' y' aa e b)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' \<beta> a n1 n d' e1b A2 \<omega>2 \<alpha>' y' aa e b l r)(*strict*)
    apply(rule_tac
      x="\<delta>2' @ \<alpha> @ l"
      in exI)
    apply(rule_tac
      x="r @ drop k y2'"
      in exI)
    apply(clarsimp)
    apply(simp (no_asm) add: setAConcat)
    apply(clarsimp)
    apply(rule setA_drop)
    apply(simp add: setAConcat)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' \<beta> a n1 n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(simp add: derivation_map_def)
   apply(rule_tac
      t="liftB z"
      and s="take k y2'"
      in ssubst)
    apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' \<beta> a n1 n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' \<beta> a n1 n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(rule sym)
   apply(rule append_take_drop_id)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(rule conjI)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(rule conjI)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(rule conjI)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(rule conjI)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
   apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' \<beta> a n1 n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' a n1 d' A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(rule_tac
      t="liftB z"
      and s="take k y2'"
      in ssubst)
    apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' a n1 d' A2 \<omega>2 \<alpha>' y')(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> z d1 \<delta>2' e1 e2 y2' a n1 d' A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(rule sym)
   apply(rule append_take_drop_id)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(rule conjI)
   apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac A B \<alpha> \<omega> z d1 d2 \<delta>2' e1 e2 y2' \<delta>1 e1a e2a y1 \<beta> a n1 n2 x n d' e1b A2 \<omega>2 \<alpha>' y')(*strict*)
  apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def)
  done

theorem cfg_LRk_implies_conflict_free: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> cfg_LRk G k
  \<Longrightarrow> conflict_free G G' k"
  apply(simp add: conflict_free_def)
  apply(rule allI)
  apply(rename_tac w)(*strict*)
  apply(rule impI)
  apply(rule conjI)
   apply(rename_tac w)(*strict*)
   apply(rule cfg_LRkDo_implies_no_reduce_reduce_item_conflict)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule cfg_LRk_to_cfg_LRkDo)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(rule cfg_LRkDo_implies_no_shift_reduce_item_conflict)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(rule cfg_LRk_to_cfg_LRkDo)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(force)
  done

theorem cfg_LRk_implies_conflict_free_ALT: "
  valid_cfg G
  \<Longrightarrow> E_F = F_FRESH (cfg_events G)
  \<Longrightarrow> S_F = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G_AUG = F_CFG_AUGMENT G S_F E_F
  \<Longrightarrow> cfg_LRk G k
  \<Longrightarrow> conflict_free G G_AUG k"
  apply(rule cfg_LRk_implies_conflict_free)
   apply(unfold F_CFG_AUGMENT__input_def)
   apply(force)
  apply(force)
  done

end

