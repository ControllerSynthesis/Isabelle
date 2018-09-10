section {*FUNCTION\_\_LR\_PARSER\_\_part3*}
theory
  FUNCTION__LR_PARSER__part3

imports
  FUNCTION__LR_PARSER__part2

begin

theorem Lemma6__33: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> parserS.marked_language P \<supseteq> cfgRM.marked_language G"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(simp add: AF_LR_PARSER_input_def,force)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "valid_parser P")
   prefer 2
   apply(rule_tac
      G="G"
      in AF_LR_PARSER_valid_parser)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: parserS.marked_language_def cfgRM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(subgoal_tac "cfgRM.belongs G d")
   apply(rename_tac x d)(*strict*)
   prefer 2
   apply(rule cfgRM.derivation_initial_belongs)
    apply(rename_tac x d)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfg_marked_effect_def cfg_marking_condition_def cfg_marking_configuration_def cfg_configurations_def cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d e i c ea ia cb)(*strict*)
  apply(subgoal_tac "ia=i")
   apply(rename_tac x d e i c ea ia cb)(*strict*)
   prefer 2
   apply(subgoal_tac "\<forall>e c. \<not>(cfgRM_step_relation G \<lparr>cfg_conf=cb\<rparr> e c)")
    apply(rename_tac x d e i c ea ia cb)(*strict*)
    apply(subgoal_tac "\<forall>e c'. \<not>(cfgRM_step_relation G c e c')")
     apply(rename_tac x d e i c ea ia cb)(*strict*)
     apply(subgoal_tac "ia\<le>i")
      apply(rename_tac x d e i c ea ia cb)(*strict*)
      apply(subgoal_tac "i\<le>ia")
       apply(rename_tac x d e i c ea ia cb)(*strict*)
       apply(force)
      apply(rename_tac x d e i c ea ia cb)(*strict*)
      apply(rule cfgRM.dead_end_at_some_is_max_dom_prime)
          apply(rename_tac x d e i c ea ia cb)(*strict*)
          apply(force)
         apply(rename_tac x d e i c ea ia cb)(*strict*)
         apply(force)
        apply(rename_tac x d e i c ea ia cb)(*strict*)
        apply(force)
       apply(rename_tac x d e i c ea ia cb)(*strict*)
       apply(force)
      apply(rename_tac x d e i c ea ia cb)(*strict*)
      apply(force)
     apply(rename_tac x d e i c ea ia cb)(*strict*)
     apply(rule cfgRM.dead_end_at_some_is_max_dom_prime)
         apply(rename_tac x d e i c ea ia cb)(*strict*)
         apply(force)
        apply(rename_tac x d e i c ea ia cb)(*strict*)
        apply(force)
       apply(rename_tac x d e i c ea ia cb)(*strict*)
       apply(force)
      apply(rename_tac x d e i c ea ia cb)(*strict*)
      apply(force)
     apply(rename_tac x d e i c ea ia cb)(*strict*)
     apply(force)
    apply(rename_tac x d e i c ea ia cb)(*strict*)
    apply(rule allI)+
    apply(rename_tac x d e i c ea ia cb eb c')(*strict*)
    apply(rule CFGRM_noStep)
    apply(force)
   apply(rename_tac x d e i c ea ia cb)(*strict*)
   apply(rule allI)+
   apply(rename_tac x d e i c ea ia cb eb ca)(*strict*)
   apply(rule CFGRM_noStep)
   apply(force)
  apply(rename_tac x d e i c ea ia cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i)(*strict*)
  apply(subgoal_tac "\<exists>d'. d' 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) \<and> cfgRM.derivation G d' \<and> d' i = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>) \<and> maximum_of_domain d' i \<and> cfgRM.belongs G d'")
   apply(rename_tac x d e i)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d i"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d e i)(*strict*)
    apply(simp add: derivation_take_def)
    apply(simp add: cfgRM.derivation_initial_def)
    apply(case_tac "d 0")
     apply(rename_tac x d e i)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d e i a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac x d e i a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d e i b)(*strict*)
    apply(simp add: cfg_initial_configurations_def)
   apply(rename_tac x d e i)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e i)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac x d e i)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e i)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac x d e i)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e i)(*strict*)
    apply(simp add: derivation_take_def)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac x d e i)(*strict*)
   apply(rule cfgRM.derivation_take_preserves_belongs)
   apply(force)
  apply(rename_tac x d e i)(*strict*)
  apply(erule exE)+
  apply(rename_tac x d e i d')(*strict*)
  apply(clarsimp)
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "d i = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>)")
  apply(thin_tac "cfgRM.belongs G d")
  apply(thin_tac "cfgRM.derivation_initial G d")
  apply(clarsimp)
  apply(rename_tac x e i d')(*strict*)
  apply(rename_tac d)
  apply(rename_tac x e i d)(*strict*)
  apply(subgoal_tac "None \<notin> set (get_labels d i)")
   apply(rename_tac x e i d)(*strict*)
   prefer 2
   apply(rule cfgRM.get_labels_only_Some)
    apply(rename_tac x e i d)(*strict*)
    apply(force)
   apply(rename_tac x e i d)(*strict*)
   apply(force)
  apply(rename_tac x e i d)(*strict*)
  apply(subgoal_tac "\<exists>\<pi>' dP e. tau (parser_marker P) \<pi>' = map Some (List.rev (foldl ((@)) [] (map (\<lambda>x. case x of Some a \<Rightarrow> [a] | None \<Rightarrow> []) (get_labels d i)))) \<and> length \<pi>'=length (List.rev(foldl ((@)) [] (map (\<lambda>x. case x of Some a \<Rightarrow> [a] | None \<Rightarrow> []) (get_labels d i))))+length x \<and> parserS.derivation P dP \<and> maximum_of_domain dP (length \<pi>') \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#[]),parserS_conf_scheduler=x@[]@[Do]\<rparr>) \<and> dP (length \<pi>') = Some (pair e \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#[teA (cfg_initial G)]),parserS_conf_scheduler=[]@[Do]\<rparr>) \<and> get_labels dP (length \<pi>') = \<pi>'")
   apply(rename_tac x e i d)(*strict*)
   prefer 2
   apply(rule_tac
      A="S'"
      and \<alpha>="[teB Do, teA (cfg_initial G)]"
      and \<beta>="[teB Do]"
      and z="[]"
      in Lemma6__32)
                  apply(rename_tac x e i d)(*strict*)
                  apply(force)
                 apply(rename_tac x e i d)(*strict*)
                 apply(simp (no_asm_simp))
                 apply(simp add: two_elements_construct_domain_def)
                 apply(rule disjI1)
                 apply(rule inMap)
                 apply(rule_tac
      x="cfg_initial G"
      in bexI)
                  apply(rename_tac x e i d)(*strict*)
                  apply(force)
                 apply(rename_tac x e i d)(*strict*)
                 apply(rule cfg_initial_in_nonterms)
                 apply(simp add: AF_LR_PARSER_input_def)
                apply(rename_tac x e i d)(*strict*)
                apply(force)
               apply(rename_tac x e i d)(*strict*)
               apply(simp add: cfgRM.belongs_def)
               apply(erule_tac
      x="i"
      in allE)
               apply(simp add: cfg_configurations_def)
               apply(rule_tac
      t="set x"
      and s="setB (liftB x)"
      in ssubst)
                apply(rename_tac x e i d)(*strict*)
                apply(rule liftB_BiElem)
               apply(rename_tac x e i d)(*strict*)
               apply(force)
              apply(rename_tac x e i d)(*strict*)
              apply(force)
             apply(rename_tac x e i d)(*strict*)
             prefer 3
             apply(force)
            apply(rename_tac x e i d)(*strict*)
            prefer 3
            apply(force)
           apply(rename_tac x e i d)(*strict*)
           prefer 4
           apply(force)
          apply(rename_tac x e i d)(*strict*)
          prefer 4
          apply(clarsimp)
          apply(force)
         apply(rename_tac x e i d)(*strict*)
         prefer 7
         apply(force)
        apply(rename_tac x e i d)(*strict*)
        prefer 5
        apply(rule_tac
      A="{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>}"
      in set_mp)
         apply(rename_tac x e i d)(*strict*)
         apply(rule_tac
      t="valid_item_set G' k ([teB Do] @ [teA (cfg_initial G)])"
      and s="valid_item_set G' k [teB Do,teA (cfg_initial G)]"
      in ssubst)
          apply(rename_tac x e i d)(*strict*)
          apply(force)
         apply(rename_tac x e i d)(*strict*)
         apply(rule_tac
      t="valid_item_set G' k [teB Do,teA (cfg_initial G)]"
      and s="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])))"
      in ssubst)
          apply(rename_tac x e i d)(*strict*)
          apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
                 apply(rename_tac x e i d)(*strict*)
                 apply(force)
                apply(simp add: AF_LR_PARSER_input_def)
                apply(force)
               apply(rename_tac x e i d)(*strict*)
               apply(simp add: AF_LR_PARSER_input_def)
              apply(rename_tac x e i d)(*strict*)
              apply(force)
             apply(rename_tac x e i d)(*strict*)
             apply(force)
            apply(rename_tac x e i d)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def valid_cfg_def)
           apply(rename_tac x e i d)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def valid_cfg_def)
          apply(rename_tac x e i d)(*strict*)
          apply(force)
         apply(rename_tac x e i d)(*strict*)
         apply(rule_tac
      B="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in subset_trans)
          apply(rename_tac x e i d)(*strict*)
          apply(rule Set.equalityD1)
          apply(rule sym)
          apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_2)
                    apply(rename_tac x e i d)(*strict*)
                    apply(simp add: AF_LR_PARSER_input_def)
                   apply(rename_tac x e i d)(*strict*)
                   apply(simp add: AF_LR_PARSER_input_def)
                   apply(force)
                  apply(rename_tac x e i d)(*strict*)
                  apply(simp add: AF_LR_PARSER_input_def)
                 apply(rename_tac x e i d)(*strict*)
                 apply(simp add: AF_LR_PARSER_input_def)
                apply(rename_tac x e i d)(*strict*)
                apply(simp add: AF_LR_PARSER_input_def)
               apply(rename_tac x e i d)(*strict*)
               apply(simp add: AF_LR_PARSER_input_def)
              apply(rename_tac x e i d)(*strict*)
              apply(simp add: AF_LR_PARSER_input_def)
             apply(rename_tac x e i d)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac x e i d)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac x e i d)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac x e i d)(*strict*)
         apply(force)
        apply(rename_tac x e i d)(*strict*)
        apply(force)
       apply(rename_tac x e i d)(*strict*)
       prefer 2
       apply(simp add: valid_item_def)
       apply(rule_tac
      x="\<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in bexI)
        apply(rename_tac x e i d)(*strict*)
        apply(clarsimp)
       apply(rename_tac x e i d)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
      apply(rename_tac x e i d)(*strict*)
      prefer 4
      apply(clarsimp)
      apply(rule_tac
      t="cfgSTD_first G' k [teB Do]"
      and s="{kPrefix SSk (filterB SSw)}" for SSk SSw
      in ssubst)
       apply(rename_tac x e i d)(*strict*)
       apply(rule cfgSTD_first_on_terminal_string_is_kPrefix)
       apply(force)
      apply(rename_tac x e i d)(*strict*)
      apply(simp add: kPrefix_def)
     apply(rename_tac x e i d)(*strict*)
     prefer 3
     apply(rule_tac
      t="List.rev (map Some (List.rev (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))))"
      and s=" (map Some ((foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))))"
      in ssubst)
      apply(rename_tac x e i d)(*strict*)
      apply(rule rev_map_rev)
     apply(rename_tac x e i d)(*strict*)
     apply(rule_tac
      t="filter (case_option False (\<lambda>x. True)) (get_labels d i)"
      and s="(get_labels d i)"
      in ssubst)
      apply(rename_tac x e i d)(*strict*)
      apply(rule filter_only_Some)
      apply(force)
     apply(rename_tac x e i d)(*strict*)
     apply(rule sym)
     apply(rule map_foldl_map_only_Some)
     apply(force)
    apply(rename_tac x e i d)(*strict*)
    apply(rule map_Some_subset)
    apply(rule_tac
      t="set (map Some (List.rev (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))))"
      and s="set (List.rev (map Some (List.rev (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i))))))"
      in subst)
     apply(rename_tac x e i d)(*strict*)
     apply(rule set_rev)
    apply(rename_tac x e i d)(*strict*)
    apply(rule_tac
      t="List.rev (map Some (List.rev (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))))"
      and s="map Some (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))"
      in ssubst)
     apply(rename_tac x e i d)(*strict*)
     apply(rule rev_map_rev)
    apply(rename_tac x e i d)(*strict*)
    apply(rule_tac
      t="map Some (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))"
      and s="get_labels d i"
      in ssubst)
     apply(rename_tac x e i d)(*strict*)
     apply(rule map_foldl_map_only_Some)
     apply(force)
    apply(rename_tac x e i d)(*strict*)
    apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
     apply(rename_tac x e i d)(*strict*)
     apply(simp add: cfg_step_labels_def)
    apply(rename_tac x e i d)(*strict*)
    apply(rule cfgRM.belongs_getLabel_are_in_step_labels)
       apply(rename_tac x e i d)(*strict*)
       apply(force)
      apply(rename_tac x e i d)(*strict*)
      apply(force)
     apply(rename_tac x e i d)(*strict*)
     apply(force)
    apply(rename_tac x e i d)(*strict*)
    apply(force)
   apply(rename_tac x e i d)(*strict*)
   apply(rule_tac
      t="length (List.rev (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i))))"
      and s="length ((foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i))))"
      in ssubst)
    apply(rename_tac x e i d)(*strict*)
    apply(rule length_rev)
   apply(rename_tac x e i d)(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))"
      and s="length (map Some (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i))))"
      in ssubst)
    apply(rename_tac x e i d)(*strict*)
    apply(rule length_map_Some)
   apply(rename_tac x e i d)(*strict*)
   apply(rule_tac
      t="map Some (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i)))"
      and s="get_labels d i"
      in ssubst)
    apply(rename_tac x e i d)(*strict*)
    apply(rule map_foldl_map_only_Some)
    apply(force)
   apply(rename_tac x e i d)(*strict*)
   apply(rule sym)
   apply(rule get_labels_length)
   apply(force)
  apply(rename_tac x e i d)(*strict*)
  apply(subgoal_tac "set x \<subseteq> cfg_events G")
   apply(rename_tac x e i d)(*strict*)
   prefer 2
   apply(simp add: cfgRM.belongs_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(simp add: cfg_configurations_def)
   apply(rule_tac
      t="set x"
      and s="setB (liftB x)"
      in ssubst)
    apply(rename_tac x e i d)(*strict*)
    apply(rule liftB_BiElem)
   apply(rename_tac x e i d)(*strict*)
   apply(force)
  apply(rename_tac x e i d)(*strict*)
  apply(simp add: parserS_marked_effect_def)
  apply(simp add: parserS_marking_condition_def)
  apply(erule exE)+
  apply(rename_tac x e i d \<pi>')(*strict*)
  apply(erule conjE)+
  apply(clarsimp)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      x="dP"
      in exI)
  apply(simp add: parserS.derivation_initial_def)
  apply(simp add: parserS_initial_configurations_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(force)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO M (epda_initial M) (teB Do)"
      and s="parser_initial P"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(force)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(rule_tac
      t="parser_bottom P"
      and s="Do"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Do"
      and s="parser_bottom P"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule valid_parser_initial_in_nonterms)
   apply(force)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule valid_parser_bottom_in_parser_events)
   apply(force)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      t="parser_events P"
      and s="cfg_events G'"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      t="parser_bottom P"
      and s="Do"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule_tac
      B="cfg_events G"
      in subset_trans)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(force)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
   apply(clarsimp)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule_tac
      B="cfg_events G"
      in nset_mp)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(force)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(subgoal_tac "teA (cfg_initial G) \<in> epda_events M")
   apply(rename_tac x e i d dP ea)(*strict*)
   prefer 2
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule_tac
      A="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in set_mp)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: two_elements_construct_domain_def)
   apply(rule disjI1)
   apply(rule inMap)
   apply(rule_tac
      x="cfg_initial G"
      in bexI)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(force)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule cfg_initial_in_nonterms)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      x="(length (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) (get_labels d i))) + length x)"
      in exI)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)], parserS_conf_scheduler = [Do]\<rparr>"
      in exI)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_marking_configurations_def)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule_tac
      x="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])"
      in bexI)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(rule_tac
      x="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      in exI)
    apply(rule_tac
      t="[teB Do, teA (cfg_initial G)]"
      and s="[teB Do]@[teA (cfg_initial G)]"
      in ssubst)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(subgoal_tac "length [teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])")
     apply(rename_tac x e i d dP ea)(*strict*)
     prefer 2
     apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac x e i d dP ea)(*strict*)
          apply(force)
         apply(rename_tac x e i d dP ea)(*strict*)
         apply(force)
        apply(rename_tac x e i d dP ea)(*strict*)
        apply(force)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(subgoal_tac "(last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) \<in> epda_states M")
     apply(rename_tac x e i d dP ea)(*strict*)
     prefer 2
     apply(rule_tac
      ?q0.0="epda_initial M"
      and w="[teB Do]"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
           apply(rename_tac x e i d dP ea)(*strict*)
           apply(force)
          apply(rename_tac x e i d dP ea)(*strict*)
          apply(force)
         apply(rename_tac x e i d dP ea)(*strict*)
         apply(force)
        apply(rename_tac x e i d dP ea)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(force)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(subgoal_tac "length [teA (cfg_initial G)] = length (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) [teA (cfg_initial G)])")
     apply(rename_tac x e i d dP ea)(*strict*)
     prefer 2
     apply(rule_tac
      M="M"
      and q="(last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]))"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac x e i d dP ea)(*strict*)
          apply(force)
         apply(rename_tac x e i d dP ea)(*strict*)
         apply(force)
        apply(rename_tac x e i d dP ea)(*strict*)
        apply(force)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(force)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(force)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ([teB Do]@[teA (cfg_initial G)])"
      and s=" F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do] @ F_DFA_GOTO_SEQUENCE M (last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) [teA (cfg_initial G)] "
      in ssubst)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(rule F_DFA_GOTO_SEQUENCE_append_split)
          apply(rename_tac x e i d dP ea)(*strict*)
          apply(force)
         apply(rename_tac x e i d dP ea)(*strict*)
         apply(force)
        apply(rename_tac x e i d dP ea)(*strict*)
        apply(force)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do] @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) [teA (cfg_initial G)])"
      and s="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) [teA (cfg_initial G)])"
      in subst)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(rule last_append)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) [teA (cfg_initial G)]"
      and s="[F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])) (teA (cfg_initial G))]"
      in ssubst)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(rename_tac x e i d dP ea)(*strict*)
         apply(force)
        apply(rename_tac x e i d dP ea)(*strict*)
        apply(force)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(force)
      apply(rename_tac x e i d dP ea)(*strict*)
      apply(force)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(force)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(rule conjI)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule_tac
      t="parser_nonterms P"
      and s="(epda_states M)- {epda_initial M, last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G),teB Do]), F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))}"
      in ssubst)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(rule AF_LR_PARSER_final_sequence_contains_nonterms)
            apply(rename_tac x e i d dP ea)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac x e i d dP ea)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
           apply(force)
          apply(rename_tac x e i d dP ea)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac x e i d dP ea)(*strict*)
         apply(force)
        apply(rename_tac x e i d dP ea)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac x e i d dP ea)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(force)
     apply(rename_tac x e i d dP ea)(*strict*)
     apply(force)
    apply(rename_tac x e i d dP ea)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(force)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      t="parser_events P"
      and s="cfg_events G'"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(rule_tac
      t="parser_bottom P"
      and s="Do"
      in ssubst)
   apply(rename_tac x e i d dP ea)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac x e i d dP ea)(*strict*)
  apply(clarsimp)
  apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
  done

corollary Lemma6__34: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> parserS.marked_language P = cfgRM.marked_language G"
  apply(rule order_antisym)
   apply(rule Lemma6__30)
   apply(force)
  apply(rule Lemma6__33)
  apply(force)
  done

corollary AF_LR_PARSER_is_PARSERl: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> k > 0
  \<Longrightarrow> valid_bounded_parser P k"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(simp add: AF_LR_PARSER_input_def,force)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(unfold valid_bounded_parser_def)
  apply(rule conjI)
   apply(rule_tac
      G="G"
      in AF_LR_PARSER_valid_parser)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rule ballI)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "\<exists>y. (e,y) \<in> AF_LR_PARSER__rules G G' M k")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(clarsimp)
   apply(rename_tac a b)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp only: AF_LR_PARSER__rules_def)
  apply(erule exE)
  apply(rename_tac e y)(*strict*)
  apply(simp (no_asm_use))
  apply(erule disjE)
   apply(rename_tac e y)(*strict*)
   apply(clarsimp)
   apply(rename_tac q q_seq I ya qA)(*strict*)
   apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = ya\<rparr>")
    apply(rename_tac q q_seq I ya qA)(*strict*)
    apply(simp add: valid_item_def)
   apply(rename_tac q q_seq I ya qA)(*strict*)
   apply(subgoal_tac "(if q_seq = [] then q else last q_seq) \<in> epda_states M")
    apply(rename_tac q q_seq I ya qA)(*strict*)
    apply(rule_tac
      M="M"
      and q="(if q_seq = [] then q else last q_seq)"
      in F_LR_MACHINE_States_contain_Items)
        apply(rename_tac q q_seq I ya qA)(*strict*)
        apply(simp add: AF_LR_PARSER__rules_def)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(force)
      apply(rename_tac q q_seq I ya qA)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac q q_seq I ya qA)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I ya qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I ya qA)(*strict*)
   apply(case_tac q_seq)
    apply(rename_tac q q_seq I ya qA)(*strict*)
    apply(simp (no_asm_simp))
   apply(rename_tac q q_seq I ya qA a list)(*strict*)
   apply(rule_tac
      t="(if q_seq = [] then q else last q_seq)"
      and s="last(q_seq)"
      in ssubst)
    apply(rename_tac q q_seq I ya qA a list)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I ya qA a list)(*strict*)
   apply(rule_tac
      A="set (q_seq)"
      in set_mp)
    apply(rename_tac q q_seq I ya qA a list)(*strict*)
    apply(rule_tac
      q="q"
      and w="cfg_item_rhs2 I"
      in F_EPDA_GOTO_SEQUENCESound_main3)
        apply(rename_tac q q_seq I ya qA a list)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac q q_seq I ya qA a list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac q q_seq I ya qA a list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac q q_seq I ya qA a list)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac q q_seq I ya qA a list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac q q_seq I ya qA a list)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac q q_seq I ya qA a list)(*strict*)
      apply(rule prod_rhs_in_cfg_events)
       apply(rename_tac q q_seq I ya qA a list)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I ya qA a list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
      apply(force)
     apply(rename_tac q q_seq I ya qA a list)(*strict*)
     apply(rule prod_rhs_in_nonterms)
      apply(rename_tac q q_seq I ya qA a list)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I ya qA a list)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
     apply(force)
    apply(rename_tac q q_seq I ya qA a list)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I ya qA a list)(*strict*)
   apply(force)
  apply(rename_tac e y)(*strict*)
  apply(erule exE)+
  apply(rename_tac e y q a ya qA)(*strict*)
  apply(erule conjE)+
  apply(erule bexE)+
  apply(rename_tac e y q a ya qA I)(*strict*)
  apply(erule conjE)+
  apply(simp (no_asm_simp))
  apply(subgoal_tac "length ya \<le> (k - Suc 0)")
   apply(rename_tac e y q a ya qA I)(*strict*)
   apply(force)
  apply(rename_tac e y q a ya qA I)(*strict*)
  apply(rule cfgSTD_firstk_shorter_than_k)
  apply(force)
  done

lemma F_CFG_AUGMENT__input_from_AF_LR_PARSER_input: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> F_CFG_AUGMENT__input G Do S' G'"
  apply(simp add: F_CFG_AUGMENT__input_def AF_LR_PARSER_input_def)
  done

lemma AF_LR_PARSER_every_rules_pops_one: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> e \<in> parser_rules P
  \<Longrightarrow> length (rule_rpop e) = Suc 0"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "e \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M (Suc 0)")
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_def)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(erule disjE)
   apply(rename_tac b)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac q a y qA I)(*strict*)
   apply(subgoal_tac "length y \<le> 0")
    apply(rename_tac q a y qA I)(*strict*)
    prefer 2
    apply(rule cfgSTD_firstk_shorter_than_k)
    apply(force)
   apply(rename_tac q a y qA I)(*strict*)
   apply(force)
  apply(rename_tac b)(*strict*)
  apply(clarsimp)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr> \<in> parser_rules P")
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(simp only: AF_LR_PARSER_input_def valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      A="cfg_productions G"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      in ballE)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(clarsimp)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(clarsimp)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def AF_LR_PARSER_input_def)
    apply(rename_tac q q_seq I y)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)} = F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
    apply(rename_tac q q_seq I y qA)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
        apply(rename_tac q q_seq I y qA)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(subgoal_tac "length (cfg_item_rhs2 I) = length (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac q q_seq I y qA)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac q I y)(*strict*)
  apply(subgoal_tac "(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))) \<in> epda_states (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0))")
   apply(rename_tac q I y)(*strict*)
   prefer 2
   apply(case_tac "cfg_item_rhs2 I")
    apply(rename_tac q I y)(*strict*)
    apply(clarsimp)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y a list)(*strict*)
   apply(rule_tac
      t="(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))"
      and s="last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))"
      in ssubst)
    apply(rename_tac q I y a list)(*strict*)
    apply(force)
   apply(rename_tac q I y a list)(*strict*)
   apply(rule_tac
      t="(F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0))"
      and s="M"
      in ssubst)
    apply(rename_tac q I y a list)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y a list)(*strict*)
   apply(rule_tac
      ?q0.0="q"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
         apply(rename_tac q I y a list)(*strict*)
         apply(force)
        apply(rename_tac q I y a list)(*strict*)
        apply(force)
       apply(rename_tac q I y a list)(*strict*)
       apply(force)
      apply(rename_tac q I y a list)(*strict*)
      apply(force)
     apply(rename_tac q I y a list)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac q I y a list)(*strict*)
    apply(rule_tac
      t="a#list"
      and s="cfg_item_rhs2 I"
      in ssubst)
     apply(rename_tac q I y a list)(*strict*)
     apply(force)
    apply(rename_tac q I y a list)(*strict*)
    apply(thin_tac "cfg_item_rhs2 I = a#list")
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(rename_tac q I y a list)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac q I y a list)(*strict*)
    apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
     apply(rename_tac q I y a list)(*strict*)
     apply(simp (no_asm_use) add: AF_LR_PARSER_input_def valid_cfg_def)
     apply(rename_tac q I y)(*strict*)
     apply(erule conjE)+
     apply(erule_tac
      A="cfg_productions G"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      in ballE)
      apply(rename_tac q I y)(*strict*)
      apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
       apply(rename_tac q I y)(*strict*)
       apply(force)
      apply(rename_tac q I y)(*strict*)
      apply(force)
     apply(rename_tac q I y)(*strict*)
     apply(force)
    apply(rename_tac q I y a list)(*strict*)
    apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
       apply(rename_tac q I y a list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac q I y a list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac q I y a list)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac q I y a list)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y a list)(*strict*)
   apply(force)
  apply(rename_tac q I y)(*strict*)
  apply(subgoal_tac "cfg_item_look_ahead (\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>) \<noteq> []")
   apply(rename_tac q I y)(*strict*)
   prefer 2
   apply(rule_tac
      q="(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))"
      and k="0"
      and G="G"
      in F_LR_MACHINE_items_with_core_from_old_grammar_have_nonempty_lookahead)
         apply(rename_tac q I y)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def AF_LR_PARSER_input_def)
        apply(simp add: F_CFG_AUGMENT__input_def AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac q I y)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac q I y)(*strict*)
      apply(force)
     apply(rename_tac q I y)(*strict*)
     apply(force)
    apply(rename_tac q I y)(*strict*)
    apply(force)
   apply(rename_tac q I y)(*strict*)
   apply(simp add: item_core_def)
  apply(rename_tac q I y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length y \<le> Suc 0")
   apply(rename_tac q I y)(*strict*)
   apply(case_tac y)
    apply(rename_tac q I y)(*strict*)
    apply(force)
   apply(rename_tac q I y a list)(*strict*)
   apply(force)
  apply(rename_tac q I y)(*strict*)
  apply(subgoal_tac "\<exists>w. (if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))=valid_item_set G' (Suc 0) w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   apply(rename_tac q I y)(*strict*)
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G' (Suc 0) w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
    apply(rename_tac q I y)(*strict*)
    prefer 2
    apply(rule LRM_contains_theEqClasses)
      apply(rename_tac q I y)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
     apply(force)
    apply(rename_tac q I y)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac q I y)(*strict*)
  apply(clarsimp)
  apply(rename_tac q I y w)(*strict*)
  apply(subgoal_tac "valid_item G' (Suc 0) \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>")
   apply(rename_tac q I y w)(*strict*)
   apply(simp add: valid_item_def)
  apply(rename_tac q I y w)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac q I y w)(*strict*)
   apply(force)
  apply(force)
  done

lemma AF_LR_PARSER_every_rules_pushes_at_most_one: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> e \<in> parser_rules P
  \<Longrightarrow> length (rule_rpush e) \<le> Suc 0"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "e \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M (Suc 0)")
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_def)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(erule disjE)
   apply(rename_tac b)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac q a y qA I)(*strict*)
   apply(subgoal_tac "length y \<le> 0")
    apply(rename_tac q a y qA I)(*strict*)
    prefer 2
    apply(rule cfgSTD_firstk_shorter_than_k)
    apply(force)
   apply(rename_tac q a y qA I)(*strict*)
   apply(force)
  apply(rename_tac b)(*strict*)
  apply(clarsimp)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr> \<in> parser_rules P")
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(simp only: AF_LR_PARSER_input_def valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      A="cfg_productions G"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      in ballE)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(clarsimp)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(clarsimp)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def AF_LR_PARSER_input_def)
    apply(rename_tac q q_seq I y)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)} = F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
    apply(rename_tac q q_seq I y qA)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
        apply(rename_tac q q_seq I y qA)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(subgoal_tac "length (cfg_item_rhs2 I) = length (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac q q_seq I y qA)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac q I y)(*strict*)
  apply(subgoal_tac "(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))) \<in> epda_states (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0))")
   apply(rename_tac q I y)(*strict*)
   prefer 2
   apply(case_tac "cfg_item_rhs2 I")
    apply(rename_tac q I y)(*strict*)
    apply(clarsimp)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y a list)(*strict*)
   apply(rule_tac
      t="(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))"
      and s="last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))"
      in ssubst)
    apply(rename_tac q I y a list)(*strict*)
    apply(force)
   apply(rename_tac q I y a list)(*strict*)
   apply(rule_tac
      t="(F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0))"
      and s="M"
      in ssubst)
    apply(rename_tac q I y a list)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y a list)(*strict*)
   apply(rule_tac
      ?q0.0="q"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
         apply(rename_tac q I y a list)(*strict*)
         apply(force)
        apply(rename_tac q I y a list)(*strict*)
        apply(force)
       apply(rename_tac q I y a list)(*strict*)
       apply(force)
      apply(rename_tac q I y a list)(*strict*)
      apply(force)
     apply(rename_tac q I y a list)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac q I y a list)(*strict*)
    apply(rule_tac
      t="a#list"
      and s="cfg_item_rhs2 I"
      in ssubst)
     apply(rename_tac q I y a list)(*strict*)
     apply(force)
    apply(rename_tac q I y a list)(*strict*)
    apply(thin_tac "cfg_item_rhs2 I = a#list")
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(rename_tac q I y a list)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac q I y a list)(*strict*)
    apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
     apply(rename_tac q I y a list)(*strict*)
     apply(simp (no_asm_use) add: AF_LR_PARSER_input_def valid_cfg_def)
     apply(rename_tac q I y)(*strict*)
     apply(erule conjE)+
     apply(erule_tac
      A="cfg_productions G"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      in ballE)
      apply(rename_tac q I y)(*strict*)
      apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
       apply(rename_tac q I y)(*strict*)
       apply(force)
      apply(rename_tac q I y)(*strict*)
      apply(force)
     apply(rename_tac q I y)(*strict*)
     apply(force)
    apply(rename_tac q I y a list)(*strict*)
    apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
       apply(rename_tac q I y a list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac q I y a list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac q I y a list)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac q I y a list)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y a list)(*strict*)
   apply(force)
  apply(rename_tac q I y)(*strict*)
  apply(subgoal_tac "cfg_item_look_ahead (\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>) \<noteq> []")
   apply(rename_tac q I y)(*strict*)
   prefer 2
   apply(rule_tac
      q="(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))"
      and G="G"
      and k="0"
      in F_LR_MACHINE_items_with_core_from_old_grammar_have_nonempty_lookahead)
         apply(rename_tac q I y)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def AF_LR_PARSER_input_def)
        apply(rename_tac q I y)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(force)
     apply(rename_tac q I y)(*strict*)
     apply(force)
    apply(rename_tac q I y)(*strict*)
    apply(force)
   apply(rename_tac q I y)(*strict*)
   apply(rename_tac q I y)(*strict*)
   apply(simp add: item_core_def)
  apply(rename_tac q I y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. (if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))=valid_item_set G' (Suc 0) w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   apply(rename_tac q I y)(*strict*)
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G' (Suc 0) w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
    apply(rename_tac q I y)(*strict*)
    prefer 2
    apply(rule_tac LRM_contains_theEqClasses)
      apply(rename_tac q I y)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
     apply(force)
    apply(rename_tac q I y)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac q I y)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac q I y)(*strict*)
  apply(clarsimp)
  apply(rename_tac q I y w)(*strict*)
  apply(subgoal_tac "valid_item G' (Suc 0) \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>")
   apply(rename_tac q I y w)(*strict*)
   apply(simp add: valid_item_def)
  apply(rename_tac q I y w)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac q I y w)(*strict*)
   apply(force)
  apply(force)
  done

lemma AF_LR_PARSER_reach_final_then_stack_empty: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> d n = Some (pair e \<lparr>parserS_conf_stack = x, parserS_conf_scheduler = [parser_bottom P]\<rparr>)
  \<Longrightarrow> x = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s)
  \<Longrightarrow> last x = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])
  \<Longrightarrow> set (teB Do # s) \<subseteq> epda_events M
  \<Longrightarrow> teB Do # s = [teB Do, teA (cfg_initial G)]"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "\<lparr>cfg_item_lhs=cfg_initial G',cfg_item_rhs1=[teB Do,teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr> \<in> valid_item_set G' k (teB Do#s)")
   prefer 2
   apply(rule_tac
      t="valid_item_set G' k (teB Do#s)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#s))"
      in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(force)
      apply(rule_tac
      B="cfg_events G'"
      in two_elements_construct_domain_setA)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rule_tac
      A="cfg_nonterminals G'"
      in two_elements_construct_domain_setB)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(force)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])"
      and s="valid_item_set G' k [teB Do,teA (cfg_initial G)]"
      in subst)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(force)
      apply(rule_tac
      B="cfg_events G'"
      in two_elements_construct_domain_setA)
      apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
      apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
       apply(force)
      apply(simp add: valid_cfg_def)
     apply(rule_tac
      A="cfg_nonterminals G'"
      in two_elements_construct_domain_setB)
     apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
      apply(force)
     apply(simp add: valid_cfg_def)
    apply(force)
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr> \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr> \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rule conjI)
     apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(simp add: der2_def)
   apply(fold der2_def)
   apply(rule der2_maximum_of_domain)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
  apply(case_tac na)
   apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
   apply(subgoal_tac "\<delta>=[]")
    apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
    prefer 2
    apply(case_tac \<delta>)
     apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac na da \<delta> e1 e2 z a list)(*strict*)
    apply(force)
   apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
   apply(subgoal_tac "z=[]")
    apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
    prefer 2
    apply(case_tac z)
     apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac na da \<delta> e1 e2 z a list)(*strict*)
    apply(force)
   apply(rename_tac na da \<delta> e1 e2 z)(*strict*)
   apply(clarsimp)
  apply(rename_tac na da \<delta> e1 e2 z nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
  apply(subgoal_tac "da (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
   apply(force)
  apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
  apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> da (Suc (Suc nat)) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
   apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
           apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
        apply(force)
       apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
   apply(force)
  apply(rename_tac da \<delta> e1 e2 z nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac da \<delta> e1 e2 z nat w)(*strict*)
  apply(case_tac \<delta>)
   apply(rename_tac da \<delta> e1 e2 z nat w)(*strict*)
   apply(clarsimp)
  apply(rename_tac da \<delta> e1 e2 z nat w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac da e1 e2 z nat w list)(*strict*)
  apply(case_tac z)
   apply(rename_tac da e1 e2 z nat w list)(*strict*)
   apply(clarsimp)
  apply(rename_tac da e1 e2 z nat w list a lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. z = w' @ [x']")
   apply(rename_tac da e1 e2 z nat w list a lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac da e1 e2 z nat w list a lista)(*strict*)
  apply(thin_tac "z=a#lista")
  apply(clarsimp)
  done

lemma AF_LR_PARSER_dollar_rule_implies_in_lang__stack_irrelevant: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> valid_bounded_parser P (Suc 0)
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>parserS_conf_stack = [parser_initial P], parserS_conf_scheduler = w @ [parser_bottom P]\<rparr>)
  \<Longrightarrow> d n = Some (pair e1 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = [parser_bottom P]\<rparr>)
  \<Longrightarrow> parser_fixed_input_length_rec1 d n = 0
  \<Longrightarrow> e2 \<in> parser_rules P
  \<Longrightarrow> rule_rpop e2 = [Do]
  \<Longrightarrow> last (rule_lpop e2) = valid_item_set G' (Suc 0) (teB Do # s)
  \<Longrightarrow> set s \<subseteq> epda_events M
  \<Longrightarrow> w \<in> cfgSTD.marked_language G"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "set w \<subseteq> cfg_events G'")
   prefer 2
   apply(subgoal_tac "\<lparr>parserS_conf_stack = [parser_initial P], parserS_conf_scheduler = w @ [parser_bottom P]\<rparr> \<in> parserS_configurations P")
    prefer 2
    apply(rule_tac
      d="d"
      and i="0"
      in parserS.belongs_configurations)
     apply(force)
    apply(force)
   apply(simp add: parserS_configurations_def)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(subgoal_tac "\<forall>\<pi>'. \<pi>'=get_labels d n \<longrightarrow> (viable_prefix G' (teB Do#s) \<and> (length \<pi>') = length (tau (parser_marker P) \<pi>') + length w \<and> (\<exists>dG e dGn. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf=s\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf=[]@(liftB w)\<rparr>) \<and> (get_labels dG dGn) = (List.rev (tau (parser_marker P) \<pi>'))))")
   prefer 2
   apply(subgoal_tac "\<forall>\<Phi> w'' \<pi>' YSEQ. \<Phi>=\<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = [parser_bottom P]\<rparr> \<and> w''=w@[parser_bottom P] \<and> \<pi>'=get_labels d n \<and> YSEQ=[] \<longrightarrow> (\<exists>XSEQ y x. \<Phi> = \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#XSEQ),parserS_conf_scheduler=y\<rparr> \<and> w''=x@y \<and> viable_prefix G' (teB Do#XSEQ) \<and> (length \<pi>') = length (tau (parser_marker P) \<pi>') + length x \<and> (\<exists>dG e dGn. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf=XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf=YSEQ@(liftB x)\<rparr>) \<and> (get_labels dG dGn) = (List.rev (tau (parser_marker P) \<pi>'))))")
    prefer 2
    apply(rule allI)+
    apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
    apply(rule impI)
    apply(rule Lemma6__29)
           apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
           apply(force)
          apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
          apply(clarsimp)
          apply(rule F_CFG_AUGMENT__viable_prefix_Do)
          apply(rule F_CFG_AUGMENT__input_from_AF_LR_PARSER_input)
          apply(force)
         apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
         apply(force)
        apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
        apply(force)
       apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
       apply(force)
      apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
      apply(force)
     apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="parser_initial P"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
      apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
     apply(rule sym)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(rename_tac \<Phi> w'' \<pi>' YSEQ)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rename_tac XSEQ dG e dGn)(*strict*)
   apply(subgoal_tac "s=XSEQ")
    apply(rename_tac XSEQ dG e dGn)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and G'="G'"
      and Do="Do"
      and S'="S'"
      and M="M"
      in F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_inj)
                apply(rename_tac XSEQ dG e dGn)(*strict*)
                apply(simp add: AF_LR_PARSER_input_def)
               apply(rename_tac XSEQ dG e dGn)(*strict*)
               apply(simp add: AF_LR_PARSER_input_def)
               apply(force)
              apply(rename_tac XSEQ dG e dGn)(*strict*)
              apply(simp add: AF_LR_PARSER_input_def)
             apply(rename_tac XSEQ dG e dGn)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac XSEQ dG e dGn)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac XSEQ dG e dGn)(*strict*)
          apply(force)
         apply(rename_tac XSEQ dG e dGn)(*strict*)
         apply(force)
        apply(rename_tac XSEQ dG e dGn)(*strict*)
        apply(force)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(force)
      apply(rename_tac XSEQ dG e dGn)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rename_tac XSEQ dG e dGn)(*strict*)
      apply(rule_tac
      B="set (teB Do # XSEQ)"
      in subset_trans)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(force)
      apply(rename_tac XSEQ dG e dGn)(*strict*)
      apply(rule viable_prefix_in_CFG)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(force)
      apply(rename_tac XSEQ dG e dGn)(*strict*)
      apply(force)
     apply(rename_tac XSEQ dG e dGn)(*strict*)
     apply(force)
    apply(rename_tac XSEQ dG e dGn)(*strict*)
    apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ))"
      and s="valid_item_set G' (Suc 0) (teB Do # XSEQ)"
      in subst)
     apply(rename_tac XSEQ dG e dGn)(*strict*)
     apply(rule F_LR_MACHINE_all_SOUND_NotNil)
            apply(rename_tac XSEQ dG e dGn)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(simp add: AF_LR_PARSER_input_def)
           apply(force)
          apply(rename_tac XSEQ dG e dGn)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac XSEQ dG e dGn)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac XSEQ dG e dGn)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(rule two_elements_construct_domain_setA)
       apply(rule viable_prefix_in_CFG)
        apply(rename_tac XSEQ dG e dGn)(*strict*)
        apply(force)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(force)
      apply(rename_tac XSEQ dG e dGn)(*strict*)
      apply(rule two_elements_construct_domain_setB)
      apply(rule viable_prefix_in_CFG)
       apply(rename_tac XSEQ dG e dGn)(*strict*)
       apply(force)
      apply(rename_tac XSEQ dG e dGn)(*strict*)
      apply(force)
     apply(rename_tac XSEQ dG e dGn)(*strict*)
     apply(force)
    apply(rename_tac XSEQ dG e dGn)(*strict*)
    apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G' (Suc 0) (teB Do # XSEQ)")
     apply(rename_tac XSEQ dG e dGn)(*strict*)
     apply(force)
    apply(rename_tac XSEQ dG e dGn)(*strict*)
    apply(rule Fact6_12__6)
    apply(force)
   apply(rename_tac XSEQ dG e dGn)(*strict*)
   apply(clarsimp)
   apply(rename_tac dG e dGn)(*strict*)
   apply(rule_tac
      x="dG"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="dGn"
      in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac dG e dGn)(*strict*)
  apply(subgoal_tac "rule_rpush e2 = [Do]")
   apply(rename_tac dG e dGn)(*strict*)
   prefer 2
   apply(subgoal_tac "length (rule_rpush e2) \<le> Suc 0")
    apply(rename_tac dG e dGn)(*strict*)
    prefer 2
    apply(rule AF_LR_PARSER_every_rules_pushes_at_most_one)
        apply(rename_tac dG e dGn)(*strict*)
        apply(force)
       apply(rename_tac dG e dGn)(*strict*)
       apply(force)
      apply(rename_tac dG e dGn)(*strict*)
      apply(force)
     apply(rename_tac dG e dGn)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn)(*strict*)
   apply(case_tac "rule_rpush e2")
    apply(rename_tac dG e dGn)(*strict*)
    prefer 2
    apply(rename_tac dG e dGn a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac dG e dGn a)(*strict*)
    apply(subgoal_tac "e2 \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M (Suc 0)")
     apply(rename_tac dG e dGn a)(*strict*)
     prefer 2
     apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_def)
    apply(rename_tac dG e dGn a)(*strict*)
    apply(simp add: AF_LR_PARSER__rules_def)
    apply(clarsimp)
    apply(rename_tac dG e dGn a b)(*strict*)
    apply(erule disjE)
     apply(rename_tac dG e dGn a b)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn a b)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn)(*strict*)
   apply(subgoal_tac "e2 \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M (Suc 0)")
    apply(rename_tac dG e dGn)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_def)
   apply(rename_tac dG e dGn)(*strict*)
   apply(simp add: AF_LR_PARSER__rules_def)
   apply(clarsimp)
   apply(rename_tac dG e dGn b)(*strict*)
   apply(erule disjE)
    apply(rename_tac dG e dGn b)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dG e dGn qA I)(*strict*)
   apply(subgoal_tac "Do \<in> cfg_events G")
    apply(rename_tac dG e dGn qA I)(*strict*)
    apply(subgoal_tac "Do \<notin> cfg_events G")
     apply(rename_tac dG e dGn qA I)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn qA I)(*strict*)
    apply(rule_tac
      t="Do"
      and s="F_FRESH (cfg_events G)"
      in ssubst)
     apply(rename_tac dG e dGn qA I)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac dG e dGn qA I)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
   apply(rename_tac dG e dGn qA I)(*strict*)
   apply(rule_tac
      A="setB (take (Suc 0) (cfg_item_rhs2 I))"
      in set_mp)
    apply(rename_tac dG e dGn qA I)(*strict*)
    apply(rule_tac
      B="setB (cfg_item_rhs2 I)"
      in subset_trans)
     apply(rename_tac dG e dGn qA I)(*strict*)
     apply(rule setBTakeIndexSubset2)
    apply(rename_tac dG e dGn qA I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
    apply(clarsimp)
    apply(rename_tac dG e dGn qA I x)(*strict*)
    apply(erule_tac
      A="cfg_productions G"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>"
      in ballE)
     apply(rename_tac dG e dGn qA I x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dG e dGn qA I x)(*strict*)
    apply(simp add: setBConcat concat_asso)
    apply(force)
   apply(rename_tac dG e dGn qA I)(*strict*)
   apply(rule_tac
      t="take (Suc 0) (cfg_item_rhs2 I)"
      and s="[teB Do]"
      in ssubst)
    apply(rename_tac dG e dGn qA I)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn qA I)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac dG e dGn)(*strict*)
  apply(subgoal_tac "e2 \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M (Suc 0)")
   apply(rename_tac dG e dGn)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_def)
  apply(rename_tac dG e dGn)(*strict*)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(clarsimp)
  apply(rename_tac dG e dGn b)(*strict*)
  apply(erule disjE)
   apply(rename_tac dG e dGn b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dG e dGn b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
  apply(subgoal_tac "teA (cfg_item_lhs I) \<in> epda_events M")
   apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in cfg_prod_in_two_elements_construct_domain_subset_trans2)
     apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
    apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
    apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
   apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
   apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
      apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
  apply(subgoal_tac "qA=F_DFA_GOTO M q (teA (cfg_item_lhs I))")
   apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_F_EPDA_GOTO_elem)
        apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
        apply(force)
       apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
       apply(force)
      apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
      apply(force)
     apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
   apply(force)
  apply(rename_tac dG e dGn q q_seq I qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac dG e dGn q q_seq I)(*strict*)
  apply(thin_tac "F_DFA_GOTO M q (teA (cfg_item_lhs I)) \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
   apply(rename_tac dG e dGn q q_seq I)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac dG e dGn q q_seq I)(*strict*)
    apply(simp only: AF_LR_PARSER_input_def valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      A="cfg_productions G"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      in ballE)
     apply(rename_tac dG e dGn q q_seq I)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac dG e dGn q q_seq I)(*strict*)
      apply(clarsimp)
     apply(rename_tac dG e dGn q q_seq I)(*strict*)
     apply(clarsimp)
    apply(rename_tac dG e dGn q q_seq I)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q q_seq I)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac dG e dGn q q_seq I)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def AF_LR_PARSER_input_def)
    apply(force)
   apply(rename_tac dG e dGn q q_seq I)(*strict*)
   apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac dG e dGn q q_seq I)(*strict*)
  apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
   apply(rename_tac dG e dGn q q_seq I)(*strict*)
   prefer 2
   apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)} = F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
    apply(rename_tac dG e dGn q q_seq I)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
        apply(rename_tac dG e dGn q q_seq I)(*strict*)
        apply(force)
       apply(rename_tac dG e dGn q q_seq I)(*strict*)
       apply(force)
      apply(rename_tac dG e dGn q q_seq I)(*strict*)
      apply(force)
     apply(rename_tac dG e dGn q q_seq I)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn q q_seq I)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q q_seq I)(*strict*)
   apply(force)
  apply(rename_tac dG e dGn q q_seq I)(*strict*)
  apply(thin_tac "q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(clarsimp)
  apply(rename_tac dG e dGn q I)(*strict*)
  apply(case_tac I)
  apply(rename_tac dG e dGn q I cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_ahead)(*strict*)
  apply(clarsimp)
  apply(rename_tac dG e dGn q cfg_item_lhs cfg_item_rhs2a cfg_item_look_ahead)(*strict*)
  apply(rename_tac A v y)
  apply(rename_tac dG e dGn q A v y)(*strict*)
  apply(subgoal_tac "\<exists>n. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = v, cfg_item_rhs2 = [], cfg_item_look_ahead = [Do]\<rparr> \<in> valid_item_set_n G' (Suc 0) n (teB Do # s)")
   apply(rename_tac dG e dGn q A v y)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_def)
  apply(rename_tac dG e dGn q A v y)(*strict*)
  apply(clarsimp)
  apply(rename_tac dG e dGn q A v y na)(*strict*)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac dG e dGn q A v y na da \<delta> e1a e2 z)(*strict*)
  apply(case_tac z)
   apply(rename_tac dG e dGn q A v y na da \<delta> e1a e2 z)(*strict*)
   apply(clarsimp)
  apply(rename_tac dG e dGn q A v y na da \<delta> e1a e2 z a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac dG e dGn q A v y na da \<delta> e1a e2 list)(*strict*)
  apply(thin_tac "cfgSTD.Nonblockingness_branching G")
  apply(rename_tac dG e dGn q A v y na da \<delta> e1a e2 list)(*strict*)
  apply(thin_tac "valid_bounded_parser P (Suc 0)")
  apply(thin_tac "valid_dfa M")
  apply(thin_tac "some_step_from_every_configuration M")
  apply(thin_tac "parserS.derivation P d")
  apply(thin_tac "parserS.belongs P d")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "d 0 = Some (pair None \<lparr>parserS_conf_stack = [parser_initial P], parserS_conf_scheduler = w @ [parser_bottom P]\<rparr>)")
  apply(thin_tac "d n = Some (pair e1 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<delta> @ v), parserS_conf_scheduler = [parser_bottom P]\<rparr>)")
  apply(rename_tac dG e dGn q A v y na da \<delta> e1 e2 list)(*strict*)
  apply(thin_tac "parser_fixed_input_length_rec1 d n = 0")
  apply(thin_tac "\<lparr>rule_lpop = q # F_DFA_GOTO_SEQUENCE M q v, rule_rpop = [Do], rule_lpush = [q, F_DFA_GOTO M q (teA A)], rule_rpush = [Do]\<rparr> \<in> parser_rules P")
  apply(thin_tac "(if F_DFA_GOTO_SEQUENCE M q v = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = [], cfg_item_rhs2 = v, cfg_item_look_ahead = y\<rparr>))) = valid_item_set G' (Suc 0) (\<delta> @ v)")
  apply(thin_tac "viable_prefix G' (\<delta> @ v)")
  apply(thin_tac "length (get_labels d n) = length (tau (parser_marker P) (get_labels d n)) + length w")
  apply(thin_tac "get_labels dG dGn = rev (tau (parser_marker P) (get_labels d n))")
  apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
  apply(thin_tac "q \<in> epda_states M")
  apply(thin_tac "\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = [], cfg_item_rhs2 = v, cfg_item_look_ahead = y\<rparr> \<in> q")
  apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G")
  apply(thin_tac "\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = v, cfg_item_rhs2 = [], cfg_item_look_ahead = [Do]\<rparr> \<in> valid_item_set G' (Suc 0) (\<delta> @ v)")
  apply(thin_tac "teA A \<in> epda_events M")
  apply(subgoal_tac "list=[]")
   apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
   prefer 2
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
   apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> d (Suc n) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
    apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
            apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
         apply(force)
        apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac dG e dGn A v n d \<delta> e1 e2 list)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
    apply(force)
   apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
   apply(clarsimp)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2 list wa)(*strict*)
   apply(case_tac list)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 list wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2 list wa a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. list = w' @ [x']")
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 list wa a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2 list wa a lista)(*strict*)
   apply(thin_tac "list=a#lista")
   apply(clarsimp)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
   apply(subgoal_tac "teB Do \<in> set wa")
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
    apply(force)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
   apply(rule_tac
      t="wa"
      and s="s@teB Do#w'"
      in ssubst)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
    apply(rule_tac
      w="[teB Do]"
      in append_linj)
    apply(rule_tac
      t="[teB Do]@wa"
      and s="\<delta>@v@teB Do#w'"
      in ssubst)
     apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
     apply(force)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
    apply(rule_tac
      t="\<delta> @ v @ teB Do # w'"
      and s="(\<delta> @ v) @ teB Do # w'"
      in ssubst)
     apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
     apply(force)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
    apply(rule_tac
      t="\<delta>@v"
      and s="teB Do#s"
      in ssubst)
     apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
     apply(force)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
    apply(simp (no_asm))
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2 wa w')(*strict*)
   apply(simp (no_asm))
  apply(rename_tac dG e dGn q A v y n d \<delta> e1 e2 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
  apply(rule F_CFG_AUGMENT__lang_prime)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
   apply(rule F_CFG_AUGMENT__input_from_AF_LR_PARSER_input)
   apply(force)
  apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgRM.derivation G' d \<and> maximum_of_domain d dGn \<and> d 0 = Some (pair None \<lparr>cfg_conf = teB Do#s@[teB Do]\<rparr>) \<and> d dGn = Some (pair e \<lparr>cfg_conf = teB Do#liftB w@[teB Do]\<rparr>)")
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map dG (\<lambda>c. \<lparr>cfg_conf=teB Do#(cfg_conf c)@[teB Do]\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation2)
     apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
     apply(rule_tac
      G'="G'"
      and G="G"
      and Do="Do"
      and S'="S'"
      in F_CFG_AUGMENT__preserves_RMderivation)
         apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
     apply(force)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2 a ea b l r)(*strict*)
    apply(rule_tac
      x="teB Do#l"
      in exI)
    apply(rule_tac
      x="r@[teB Do]"
      in exI)
    apply(clarsimp)
    apply(simp only: setAConcat concat_asso)
    apply(force)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
   apply(rule conjI)
    apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac dG e dGn A v n d \<delta> e1 e2)(*strict*)
  apply(thin_tac "cfgRM.derivation G dG")
  apply(thin_tac "maximum_of_domain dG dGn")
  apply(thin_tac "dG 0 = Some (pair None \<lparr>cfg_conf = s\<rparr>)")
  apply(thin_tac "dG dGn = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)")
  apply(clarsimp)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(simp add: cfgSTD.marked_language_def)
  apply(rule_tac
      x="derivation_append d da (Suc n)"
      in exI)
  apply(subgoal_tac "cfgSTD.derivation G' (derivation_append d da (Suc n))")
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_concat2)
      apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
     apply(force)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(rule cfgRM_derivations_are_cfg_derivations)
    apply(force)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(force)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(rule conjI)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
     apply(force)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(simp add: cfgSTD.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(simp add: cfg_initial_configurations_def)
    apply(simp add: cfg_configurations_def)
    apply(rule cfg_initial_in_nonterms)
    apply(force)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(force)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(rule conjI)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(simp add: cfg_marked_effect_def)
   apply(rule_tac
      x="if dGn=0 then e2 else e"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = teB Do # liftB w @ [teB Do]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(rule_tac
      x="Suc n+dGn"
      in exI)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(clarsimp)
   apply(simp (no_asm) only: setAConcat concat_asso)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(rule_tac
      t="liftB (w@[Do])"
      and s="liftB w @ liftB [Do]"
      in ssubst)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(force)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(rule conjI)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(force)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(rule_tac
      x="Suc n+dGn"
      in exI)
  apply(rule_tac
      x="if dGn=0 then e2 else e"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = teB Do # liftB w @ [teB Do]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(rule conjI)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(simp (no_asm) only: setAConcat concat_asso)
   apply(clarsimp)
   apply(rule setA_liftB)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(simp (no_asm) only: setBConcat setAConcat concat_asso)
  apply(clarsimp)
  apply(subgoal_tac "Do \<in> cfg_events G'")
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(rule_tac
      t="setA (liftB w)"
      and s="{}"
      in ssubst)
    apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(force)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(rule_tac
      t="setB (liftB w)"
      and s="set w"
      in subst)
   apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
   apply(rule liftB_BiElem)
  apply(rename_tac e dGn A v n d \<delta> e1 e2 da)(*strict*)
  apply(force)
  done

lemma AF_LR_PARSER_just_read_input_not_seen_dollar_Nonblockingness: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> parserS.is_forward_deterministic_accessible P
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> valid_bounded_parser P (Suc 0)
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>parserS_conf_stack = [parser_initial P], parserS_conf_scheduler = w @ [parser_bottom P]\<rparr>)
  \<Longrightarrow> d n = Some (pair e1 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = [parser_bottom P]\<rparr>)
  \<Longrightarrow> parser_fixed_input_length_rec1 d n = 0
  \<Longrightarrow> e2 \<in> parser_rules P
  \<Longrightarrow> rule_rpop e2 = [Do]
  \<Longrightarrow> last (rule_lpop e2) = valid_item_set G' (Suc 0) (teB Do # s)
  \<Longrightarrow> set s \<subseteq> epda_events M
  \<Longrightarrow> parserS.Nonblockingness_configuration P \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = [parser_bottom P]\<rparr>"
  (*
  EXAMPLE:
  S \<rightarrow> $A$
  A \<rightarrow> B
  B \<rightarrow> \<lambda>
  B \<rightarrow> aB
  we have: 7|\<guillemotleft>aa$ \<Rightarrow> 76|\<guillemotleft>a$ \<Rightarrow> 766|\<guillemotleft>$
  and 6|$ \<Rightarrow> 62|$ in parser_rules
  therefore there is: 766|\<guillemotleft>$ \<Rightarrow>* 74|$\<guillemotleft>
  it exists: 766|\<guillemotleft>$ \<Rightarrow> 7662|$\<guillemotleft> \<Rightarrow> 762|$\<guillemotleft> \<Rightarrow> 71|$\<guillemotleft> \<Rightarrow> 74|$\<guillemotleft>

  if there is a derivation which eliminates the entire input but has not seen $ yet, and there is a reduce rule which sees $ and which is applicable for some stack with the current top stack, then (without checking the applicability of the rule) the derivation can be continued to an accepting derivation by applying a sequence of $-reduce rules leading to the final state.
*)
  apply(subgoal_tac "w \<in> parserS.marked_language P")
   prefer 2
   apply(subgoal_tac "w \<in> cfgSTD.marked_language G")
    prefer 2
    apply(rule AF_LR_PARSER_dollar_rule_implies_in_lang__stack_irrelevant)
                   apply(force)+
   apply(rule_tac
      t="parserS.marked_language P"
      and s="cfgRM.marked_language G"
      in ssubst)
    apply(rule Lemma6__34)
    apply(force)
   apply(rule_tac
      t="cfgRM.marked_language G"
      and s="cfgSTD.marked_language G"
      in subst)
    apply(rule CFG_lang_rm_lang_equal)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(force)
  apply(simp add: parserS.marked_language_def)
  apply(clarsimp)
  apply(rename_tac da)(*strict*)
  apply(simp add: parserS_marked_effect_def parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac da c i e cb)(*strict*)
  apply(subgoal_tac "\<exists>d. (parserS.derivation_initial P d \<and> parserS.derivation P d \<and> d 0 = Some (pair None c) \<and> d i = Some (pair e cb) \<and> cb \<in> parserS_marking_configurations P) \<and> maximum_of_domain d i ")
   apply(rename_tac da c i e cb)(*strict*)
   prefer 2
   apply(rule_tac
      d="da"
      in derivation_extend_with_maximum_of_domain)
     apply(rename_tac da c i e cb)(*strict*)
     apply(force)
    apply(rename_tac da c i e cb)(*strict*)
    apply(force)
   apply(rename_tac da c i e cb)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac da c i e cb)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac da c i e cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac da c i e cb)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac da c i e cb)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac da c i e cb)(*strict*)
  apply(thin_tac "parserS.derivation_initial P da")
  apply(thin_tac "parserS.derivation P da")
  apply(thin_tac "da 0 = Some (pair None c)")
  apply(thin_tac "da i = Some (pair e cb)")
  apply(thin_tac "cb \<in> parserS_marking_configurations P")
  apply(clarsimp)
  apply(rename_tac c i e cb da)(*strict*)
  apply(subgoal_tac "\<forall>k. k\<le> ord_class.min n i \<longrightarrow> (d k = da k)")
   apply(rename_tac c i e cb da)(*strict*)
   prefer 2
   apply(subgoal_tac "d 0 = da 0")
    apply(rename_tac c i e cb da)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom P]")
     apply(rename_tac c i e cb da)(*strict*)
     prefer 2
     apply(simp add: parserS.belongs_def)
     apply(erule_tac
      x="0"
      in allE)
     apply(clarsimp)
     apply(simp add: parserS_configurations_def)
     apply(force)
    apply(rename_tac c i e cb da)(*strict*)
    apply(case_tac c)
    apply(rename_tac c i e cb da parserS_conf_stack parserS_conf_schedulera)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e cb da parserS_conf_stack w)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
    apply(simp add: parserS_initial_configurations_def)
   apply(rename_tac c i e cb da)(*strict*)
   apply(clarsimp)
   apply(rename_tac c i e cb da k)(*strict*)
   apply(rule_tac
      t="d k"
      and s="derivation_take d k k"
      in ssubst)
    apply(rename_tac c i e cb da k)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac c i e cb da k)(*strict*)
   apply(rule_tac
      t="da k"
      and s="derivation_take da k k"
      in ssubst)
    apply(rename_tac c i e cb da k)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac c i e cb da k)(*strict*)
   apply(rule_tac
      t="derivation_take d k"
      and s="derivation_take da k"
      in ssubst)
    apply(rename_tac c i e cb da k)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c i e cb da k)(*strict*)
   apply(rule parserS.derivationsCoincide_CropProperR)
               apply(rename_tac c i e cb da k)(*strict*)
               apply(force)+
             apply(rename_tac c i e cb da k)(*strict*)
             apply(rule parserS.derivation_initial_belongs)
              apply(rename_tac c i e cb da k)(*strict*)
              apply(simp add: valid_bounded_parser_def)
             apply(rename_tac c i e cb da k)(*strict*)
             apply(force)
            apply(rename_tac c i e cb da k)(*strict*)
            apply(force)
           apply(rename_tac c i e cb da k)(*strict*)
           apply(force)
          apply(rename_tac c i e cb da k)(*strict*)
          apply(force)
         apply(rename_tac c i e cb da k)(*strict*)
         apply(force)
        apply(rename_tac c i e cb da k)(*strict*)
        apply(force)
       apply(rename_tac c i e cb da k)(*strict*)
       apply(force)
      apply(rename_tac c i e cb da k)(*strict*)
      apply(force)
     apply(rename_tac c i e cb da k)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da k)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da k)(*strict*)
   apply(force)
  apply(rename_tac c i e cb da)(*strict*)
  apply(case_tac "i<n")
   apply(rename_tac c i e cb da)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(erule impE)
    apply(rename_tac c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da)(*strict*)
   apply(clarsimp)
   apply(thin_tac "parserS.derivation_initial P da")
   apply(thin_tac "parserS.derivation P da")
   apply(thin_tac "da i = Some (pair e cb)")
   apply(thin_tac "maximum_of_domain da i")
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
    apply(rename_tac c i e cb da)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in parserS.step_detail_before_some_position)
      apply(rename_tac c i e cb da)(*strict*)
      apply(force)
     apply(rename_tac c i e cb da)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da)(*strict*)
   apply(clarsimp)
   apply(rename_tac c i e cb da e2a c2)(*strict*)
   apply(simp add: parserS_marking_configurations_def)
   apply(clarsimp)
   apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
   apply(subgoal_tac "length (rule_rpop e2a) = Suc 0")
    apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
    prefer 2
    apply(rule AF_LR_PARSER_every_rules_pops_one)
        apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
        apply(force)
       apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
       apply(force)
      apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
      apply(force)
     apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
    apply(rule_tac
      t="parser_rules P"
      and s="parser_step_labels P"
      in ssubst)
     apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
     apply(simp add: parser_step_labels_def)
    apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
    apply(rule parserS.belongs_step_labels)
     apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
   apply(case_tac "rule_rpop e2a")
    apply(rename_tac c i e cb da e2a c2 f w)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f w a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac c i e cb da e2a c2 f w a list)(*strict*)
    prefer 2
    apply(rename_tac c i e cb da e2a c2 f w a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
   apply(subgoal_tac "e2a \<in> parser_rules P")
    apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
    prefer 2
    apply(rule_tac
      t="parser_rules P"
      and s="parser_step_labels P"
      in ssubst)
     apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
     apply(simp add: parser_step_labels_def)
    apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
    apply(rule parserS.belongs_step_labels)
     apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
   apply(subgoal_tac "valid_parser_step_label P e2a")
    apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
    prefer 2
    apply(simp add: valid_bounded_parser_def valid_parser_def)
   apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c2 = w @ [parser_bottom P]")
    apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
    prefer 2
    apply(simp add: parserS.belongs_def)
    apply(erule_tac
      x="Suc i"
      in allE)
    apply(clarsimp)
    apply(simp add: parserS_configurations_def)
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f w a)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c i e cb da e2a c2 f w x k wb)(*strict*)
   apply(thin_tac "parserS_conf_stack cb = x @ rule_lpop e2a")
   apply(thin_tac "parserS_conf_stack c2 = x @ rule_lpush e2a")
   apply(thin_tac "w @ [f] = x @ rule_lpop e2a")
   apply(thin_tac "set (rule_lpop e2a) \<subseteq> parser_nonterms P")
   apply(thin_tac "rule_lpop e2a \<noteq> []")
   apply(thin_tac "rule_lpush e2a \<noteq> []")
   apply(simp add: kPrefix_def)
   apply(rename_tac c i e cb da e2a c2 f k wb)(*strict*)
   apply(case_tac k)
    apply(rename_tac c i e cb da e2a c2 f k wb)(*strict*)
    apply(clarsimp)
   apply(rename_tac c i e cb da e2a c2 f k wb nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_rec1 d (Suc i) = Suc 0")
    apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
   apply(subgoal_tac "Suc 0 \<le> parser_fixed_input_length_rec1 d n")
    apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
    prefer 2
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc i)) \<ge> length (parserS_conf_scheduler \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = [parser_bottom P]\<rparr>) - (parser_fixed_input_length_recN d ((Suc i)+(n-Suc i)))")
     apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
     prefer 2
     apply(rule PARSER_UnseenPartStrictlyDecreases)
         apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
         apply(simp add: valid_bounded_parser_def)
         apply(force)
        apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
        apply(force)
       apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
       apply(force)
      apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
      apply(force)
     apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
    apply(rule_tac
      s="parser_fixed_input_length_recN d n"
      and t="parser_fixed_input_length_rec1 d n"
      in subst)
     apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
     apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
        apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
        apply(force)
       apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
       apply(force)
      apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
      apply(force)
     apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da e2a c2 f wb nat)(*strict*)
   apply(force)
  apply(rename_tac c i e cb da)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parserS.belongs P da")
   apply(rename_tac c i e cb da)(*strict*)
   prefer 2
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac c i e cb da)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac c i e cb da)(*strict*)
   apply(force)
  apply(rename_tac c i e cb da)(*strict*)
  apply(simp add: parserS.Nonblockingness_configuration_def)
  apply(rule_tac
      x="derivation_drop da n"
      in exI)
  apply(rule conjI)
   apply(rename_tac c i e cb da)(*strict*)
   apply(rule_tac
      m="i-n"
      in parserS.derivation_drop_preserves_derivation)
    apply(rename_tac c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da)(*strict*)
   apply(force)
  apply(rename_tac c i e cb da)(*strict*)
  apply(rule conjI)
   apply(rename_tac c i e cb da)(*strict*)
   apply(rule parserS.derivation_drop_preserves_belongs)
     apply(rename_tac c i e cb da)(*strict*)
     apply(force)
    apply(rename_tac c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da)(*strict*)
   apply(force)
  apply(rename_tac c i e cb da)(*strict*)
  apply(rule conjI)
   apply(rename_tac c i e cb da)(*strict*)
   apply(simp add: derivation_drop_def)
  apply(rename_tac c i e cb da)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(rule conjI)
   apply(rename_tac c i e cb da)(*strict*)
   apply(simp add: derivation_drop_def)
   apply(rule_tac
      d="d"
      and i="n"
      in parserS.belongs_configurations)
    apply(rename_tac c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac c i e cb da)(*strict*)
   apply(force)
  apply(rename_tac c i e cb da)(*strict*)
  apply(rule_tac
      x="i-n"
      in exI)
  apply(rule_tac
      x="if i-n=0 then None else e"
      in exI)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule conjI)
   apply(rename_tac c i e cb da)(*strict*)
   apply(simp add: derivation_drop_def)
   apply(clarsimp)
  apply(rename_tac c i e cb da)(*strict*)
  apply(force)
  done

corollary F_LR_PARSER_nonblockingness_language: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> valid_parser P
  \<Longrightarrow> nonblockingness_language (parserS.unmarked_language P) (parserS.marked_language P)"
  apply(subgoal_tac "cfgRM.Nonblockingness_branching G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__preserves_Nonblockingness)
     apply(simp add: F_CFG_AUGMENT__input_def)
     apply(simp add: AF_LR_PARSER_input_def)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(force)
  apply(rule_tac
      t="parserS.marked_language P"
      and s="cfgRM.marked_language G"
      in ssubst)
   apply(rule Lemma6__34)
   apply(force)
  apply(simp add: nonblockingness_language_def)
  apply(simp add: parserS.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  apply(simp add: parserS_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(subgoal_tac "\<exists>d'. (parserS.derivation P d' \<and> parser_fixed_input_length_recN d' i=parser_fixed_input_length_recN d i \<and> d' 0 = Some (pair None c) \<and> d' i = Some (pair e c')) \<and> maximum_of_domain d' i")
   apply(rename_tac d c c' i e v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and i="i"
      in derivation_extend_with_maximum_of_domain)
     apply(rename_tac d c c' i e v)(*strict*)
     apply(force)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(simp add: derivation_take_def)
   apply(fold derivation_take_def)
   apply(rule parser_fixed_input_length_recN_with_derivation_take)
   apply(force)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(thin_tac "parserS.derivation P d")
  apply(thin_tac "d 0 = Some (pair None c)")
  apply(thin_tac "d i = Some (pair e c')")
  apply(clarsimp)
  apply(rename_tac d c c' i e v d')(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN d i"
      and s="parser_fixed_input_length_recN d' i"
      in ssubst)
   apply(rename_tac d c c' i e v d')(*strict*)
   apply(force)
  apply(rename_tac d c c' i e v d')(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN d' i = parser_fixed_input_length_recN d i")
  apply(clarsimp)
  apply(rename_tac c c' i e v d')(*strict*)
  apply(rename_tac d)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "valid_parser P")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in AF_LR_PARSER_valid_parser)
         apply(rename_tac c c' i e v d)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' i e v d)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac c c' i e v d)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d)(*strict*)
    apply(force)
   apply(rename_tac c c' i e v d)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "parserS.belongs P d")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(rule parserS.derivation_belongs)
      apply(rename_tac c c' i e v d)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d)(*strict*)
    apply(simp add: parserS_initial_configurations_def)
   apply(rename_tac c c' i e v d)(*strict*)
   apply(force)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "valid_cfg G'")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__makes_CFG)
   apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT__input_def)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "valid_dfa M")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(rename_tac c c' i e v d)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "some_step_from_every_configuration M")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' i e v d)(*strict*)
    apply(force)
   apply(rename_tac c c' i e v d)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom P]")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom P]")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' i e v d wa)(*strict*)
  apply(subgoal_tac "\<exists>s. set s \<subseteq> epda_events M \<and> parserS_conf_stack c' = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#s)")
   apply(rename_tac c c' i e v d wa)(*strict*)
   prefer 2
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac c' i e v d wa)(*strict*)
   apply(rule_tac
      i="i"
      and e="e"
      in F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_everywhere)
          apply(rename_tac c' i e v d wa)(*strict*)
          apply(force)
         apply(rename_tac c' i e v d wa)(*strict*)
         apply(force)
        apply(rename_tac c' i e v d wa)(*strict*)
        apply(force)
       apply(rename_tac c' i e v d wa)(*strict*)
       apply(force)
      apply(rename_tac c' i e v d wa)(*strict*)
      apply(force)
     apply(rename_tac c' i e v d wa)(*strict*)
     apply(force)
    apply(rename_tac c' i e v d wa)(*strict*)
    apply(force)
   apply(rename_tac c' i e v d wa)(*strict*)
   apply(force)
  apply(rename_tac c c' i e v d wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' i e v d wa s)(*strict*)
  apply(rename_tac n e w' d v' s)
  apply(rename_tac c c' n e w' d v' s)(*strict*)
  apply(subgoal_tac "\<forall>\<Phi> w'' \<pi>' YSEQ. \<Phi>=\<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = v'@[parser_bottom P]\<rparr> \<and> w''=w'@v'@[parser_bottom P] \<and> \<pi>'=get_labels d n \<and> YSEQ=[] \<longrightarrow> (\<exists>XSEQ y x. \<Phi> = \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#XSEQ),parserS_conf_scheduler=y\<rparr> \<and> w''=x@y \<and> viable_prefix G' (teB Do#XSEQ) \<and> (length \<pi>') = length (tau (parser_marker P) \<pi>') + length x \<and> (\<exists>dG e dGn. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf=XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf=YSEQ@(liftB x)\<rparr>) \<and> (get_labels dG dGn) = (List.rev (tau (parser_marker P) \<pi>'))))")
   apply(rename_tac c c' n e w' d v' s)(*strict*)
   prefer 2
   apply(rule allI)+
   apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
   apply(rule impI)
   apply(rule Lemma6__29)
          apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
          apply(force)
         apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac c c' n e w' d v' s)(*strict*)
     apply(case_tac c)
     apply(rename_tac c c' n e w' d v' s parserS_conf_stacka parserS_conf_schedulera)(*strict*)
     apply(clarsimp)
     apply(rename_tac c' n e w' d v' s)(*strict*)
     apply(rule_tac
      t="parser_initial P"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
      apply(rename_tac c' n e w' d v' s)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
     apply(rename_tac c' n e w' d v' s)(*strict*)
     apply(rule sym)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(rename_tac c' n e w' d v' s)(*strict*)
         apply(force)
        apply(rename_tac c' n e w' d v' s)(*strict*)
        apply(force)
       apply(rename_tac c' n e w' d v' s)(*strict*)
       apply(force)
      apply(rename_tac c' n e w' d v' s)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac c' n e w' d v' s)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
   apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G' (Suc 0) (teB Do # YSEQ)")
    apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
    apply(erule exE)
    apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ I)(*strict*)
    apply(rule Fact6_12__1)
    apply(force)
   apply(rename_tac c c' n e w' d v' s \<Phi> w'' \<pi>' YSEQ)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c' n e w' d v' s)(*strict*)
   apply(rule_tac
      t="valid_item_set G' (Suc 0) [teB Do]"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
    apply(rename_tac c c' n e w' d v' s)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
           apply(rename_tac c c' n e w' d v' s)(*strict*)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(rename_tac c c' n e w' d v' s)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' n e w' d v' s)(*strict*)
        apply(force)
       apply(rename_tac c c' n e w' d v' s)(*strict*)
       apply(force)
      apply(rename_tac c c' n e w' d v' s)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(rename_tac c c' n e w' d v' s)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(rename_tac c c' n e w' d v' s)(*strict*)
    apply(force)
   apply(rename_tac c c' n e w' d v' s)(*strict*)
   apply(rule hasElem_prefix_closureise)
   apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_1)
             apply(rename_tac c c' n e w' d v' s)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac c c' n e w' d v' s)(*strict*)
            apply(force)
           apply(rename_tac c c' n e w' d v' s)(*strict*)
           apply(force)
          apply(rename_tac c c' n e w' d v' s)(*strict*)
          apply(force)
         apply(rename_tac c c' n e w' d v' s)(*strict*)
         apply(force)
        apply(rename_tac c c' n e w' d v' s)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' n e w' d v' s)(*strict*)
      apply(force)
     apply(rename_tac c c' n e w' d v' s)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' n e w' d v' s)(*strict*)
    apply(force)
   apply(rename_tac c c' n e w' d v' s)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' n e w' d v' s)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
  apply(subgoal_tac "s=XSEQ")
   apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_inj)
               apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
               apply(simp add: AF_LR_PARSER_input_def)
              apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
              apply(simp add: AF_LR_PARSER_input_def)
              apply(force)
             apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rule_tac
      B="set (teB Do # XSEQ)"
      in subset_trans)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(force)
     apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
     apply(rule_tac
      B="epda_events M"
      in subset_trans)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(rule viable_prefix_in_CFG)
       apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
       apply(force)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(force)
     apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
   apply(rule_tac
      t="(F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0))"
      and s="M"
      in ssubst)
    apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
   apply(rule_tac
      t="F_FRESH (cfg_events G)"
      and s="Do"
      in ssubst)
    apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ))"
      and s="valid_item_set G' (Suc 0) (teB Do # XSEQ)"
      in subst)
    apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil)
           apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(rule viable_prefix_in_CFG)
       apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
       apply(force)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(force)
     apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(rule viable_prefix_in_CFG)
      apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
      apply(force)
     apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
   apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G' (Suc 0) (teB Do # XSEQ)")
    apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
   apply(rule Fact6_12__6)
   apply(force)
  apply(rename_tac c c' n e w' d v' s XSEQ dG ea dGn)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn)(*strict*)
  apply(case_tac n)
   apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn)(*strict*)
   apply(clarsimp)
   apply(rename_tac c' d v' XSEQ dG ea dGn)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(subgoal_tac "cfgRM.marked_language G \<noteq> {}")
    apply(rename_tac c' d v' XSEQ dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac c' d v' XSEQ dG ea dGn)(*strict*)
   apply(rule CFGRM_Nonblockingness_is_lang_notempty)
    apply(rename_tac c' d v' XSEQ dG ea dGn)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac c' d v' XSEQ dG ea dGn)(*strict*)
   apply(force)
  apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN d n"
      and s="parser_fixed_input_length_rec1 d n"
      in ssubst)
   apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
   apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
      apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
      apply(rule AF_LR_PARSER_is_PARSERl)
       apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
       apply(force)
      apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
      apply(force)
     apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
     apply(force)
    apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
    apply(force)
   apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
   apply(force)
  apply(rename_tac c c' n e w' d v' XSEQ dG ea dGn nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' e w' d v' XSEQ dG ea dGn nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac c c' e w' d v' XSEQ dG ea dGn n)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac c c' e w' d v' XSEQ dG ea dGn n)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac c c' e w' d v' XSEQ dG ea dGn n)(*strict*)
     apply(blast)
    apply(rename_tac c c' e w' d v' XSEQ dG ea dGn n)(*strict*)
    apply(blast)
   apply(rename_tac c c' e w' d v' XSEQ dG ea dGn n)(*strict*)
   apply(arith)
  apply(rename_tac c c' e w' d v' XSEQ dG ea dGn n)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n eb)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
  apply(subgoal_tac "length (rule_rpop e) = Suc 0")
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
   prefer 2
   apply(rule AF_LR_PARSER_every_rules_pops_one)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
   apply(rule_tac
      t="parser_rules P"
      and s="parser_step_labels P"
      in ssubst)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
    apply(simp add: parser_step_labels_def)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
   apply(rule parserS.belongs_step_labels)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
  apply(case_tac "rule_rpop e")
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e)(*strict*)
   apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a list)(*strict*)
   prefer 2
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
  apply(subgoal_tac "\<exists>d1. cfgSTD.derivation G' d1 \<and> maximum_of_domain d1 dGn \<and> d1 0 = Some (pair None \<lparr>cfg_conf = teB Do # XSEQ\<rparr>) \<and> d1 dGn = Some (pair ea \<lparr>cfg_conf = teB Do # liftB w'\<rparr>)")
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map dG (\<lambda>c. \<lparr>cfg_conf=teB Do#(cfg_conf c)\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_derivation2)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
     apply(rule_tac
      G="G"
      and S'="S'"
      and Do="Do"
      and G'="G'"
      in F_CFG_AUGMENT__preserves_derivation)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a aa eb b l r)(*strict*)
    apply(rule_tac
      x="teB Do#l"
      in exI)
    apply(rule_tac
      x="r"
      in exI)
    apply(clarsimp)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
   apply(rule conjI)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a)(*strict*)
  apply(thin_tac "cfgRM.derivation G dG")
  apply(thin_tac "maximum_of_domain dG dGn")
  apply(thin_tac "dG 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>)")
  apply(thin_tac "dG dGn = Some (pair ea \<lparr>cfg_conf = liftB w'\<rparr>)")
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(case_tac "take (length (rule_rpush e)) v' = []")
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
   apply(rule_tac
      t="take (length (rule_rpush e)) v'"
      and s="[]"
      in ssubst)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
   apply(clarsimp)
   apply(simp add: viable_prefix_def)
   apply(clarsimp)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(subgoal_tac "\<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgRM.derivation G' d' \<and> cfgRM.belongs G' d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=\<beta>@y\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}")
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    prefer 2
    apply(rule_tac
      n="Suc na"
      and ?w1.0="\<delta> @ \<alpha>"
      and ?w3.0="[]"
      in CFGRM_Nonblockingness_to_elimination)
          apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
        apply(rule cfgRM.derivation_belongs)
           apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
           apply(force)
          apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
         apply(simp add: cfg_configurations_def)
         apply(rule cfg_initial_in_nonterms)
         apply(force)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
       apply(simp add: cfgRM.derivation_initial_def)
       apply(simp add: cfg_initial_configurations_def)
       apply(simp add: cfg_configurations_def)
       apply(rule cfg_initial_in_nonterms)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
   apply(subgoal_tac "\<exists>w'. \<beta>@y=w'@[teB Do]")
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
    prefer 2
    apply(subgoal_tac "da (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__FirstStep)
            apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
          apply(force)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
    apply(subgoal_tac "\<exists>e w. da (Suc na) = Some (pair e \<lparr>cfg_conf = w @ [teB Do]\<rparr>)")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
     prefer 2
     apply(rule_tac
      G="G'"
      and m="Suc 0"
      in terminals_at_ending_are_never_modified_list)
          apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
          apply(rule cfgRM_derivations_are_cfg_derivations)
          apply(force)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
         apply(force)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb wa)(*strict*)
    apply(case_tac y)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa)(*strict*)
     apply(case_tac na)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<beta> d' n' w eb)(*strict*)
      apply(case_tac \<beta>)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<beta> d' n' w eb)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c' w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
       apply(simp add: parserS.belongs_def)
       apply(erule_tac
      x="Suc n"
      in allE)
       apply(clarsimp)
       apply(simp add: parserS_configurations_def)
       apply(clarsimp)
       apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
       apply(subgoal_tac "\<not> set (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<subseteq> parser_nonterms P")
        apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
        apply(force)
       apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
       apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<notin> parser_nonterms P")
        apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
        apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<in> set (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
         apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
         apply(force)
        apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
        apply(rule last_in_set)
        apply(subgoal_tac "length [teB Do, teA (cfg_initial G), teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
         apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
         prefer 2
         apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
              apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
              apply(force)
             apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
             apply(force)
            apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
            apply(force)
           apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
           apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
          apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
          apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
           apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
          apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
          apply(simp add: two_elements_construct_domain_def AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
          apply(rule disjI2)
          apply(rule disjI1)
          apply(clarsimp)
          apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
           apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
           apply(force)
          apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
          apply(rule cfg_initial_in_nonterms)
          apply(force)
         apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
         apply(force)
        apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
        apply(force)
       apply(rename_tac w' d v' dG ea dGn n e a d1 da d' n' w eb)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<beta> d' n' w eb aa list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. \<beta> = w' @ [x']")
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<beta> d' n' w eb aa list)(*strict*)
       prefer 2
       apply(rule NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<beta> d' n' w eb aa list)(*strict*)
      apply(thin_tac "\<beta>=aa#list")
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
     apply(subgoal_tac "\<exists>e w. da (Suc nat) = Some (pair e \<lparr>cfg_conf = w @ [teB Do]\<rparr>)")
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
      prefer 2
      apply(rule_tac
      G="G'"
      and m="Suc 0"
      in terminals_at_ending_are_never_modified_list)
           apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
           apply(rule cfgRM_derivations_are_cfg_derivations)
           apply(force)
          apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
          apply(force)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
         apply(force)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da \<alpha> \<beta> A \<delta> e1 e2 d' n' w eb wa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb wa aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. y = w' @ [x']")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb wa aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb wa aa list)(*strict*)
    apply(thin_tac "y=aa#list")
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
   apply(subgoal_tac "\<exists>w'. w=w'@[teB Do]")
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
    prefer 2
    apply(subgoal_tac "\<exists>e w. d' n' = Some (pair e \<lparr>cfg_conf = w @ [teB Do]\<rparr>)")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
     prefer 2
     apply(rule_tac
      G="G'"
      and m="0"
      in terminals_at_ending_are_never_modified_list)
          apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
          apply(rule cfgRM_derivations_are_cfg_derivations)
          apply(force)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
         apply(force)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' w eb w'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
   apply(rule_tac
      x="w'@(filterB w'b)"
      in exI)
   apply(rule conjI)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
    apply(rule_tac
      t="cfgRM.marked_language G"
      and s="cfgSTD.marked_language G"
      in subst)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
     apply(rule CFG_lang_rm_lang_equal)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
    apply(rule_tac
      Do="Do"
      and S'="S'"
      and G'="G'"
      in F_CFG_AUGMENT__lang_prime)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgSTD.marked_language_def)
    apply(subgoal_tac "\<exists>d1. cfgSTD.derivation G' d1 \<and> maximum_of_domain d1 dGn \<and> d1 0 = Some (pair None \<lparr>cfg_conf = teB Do # XSEQ@\<beta>@y\<rparr>) \<and> d1 dGn = Some (pair ea \<lparr>cfg_conf = teB Do # liftB w'@\<beta>@y\<rparr>)")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_map d1 (\<lambda>c. \<lparr>cfg_conf=(cfg_conf c)@\<beta>@y\<rparr>)"
      in exI)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
      apply(rule cfgSTD.derivation_map_preserves_derivation2)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b aa ec b l r)(*strict*)
      apply(rule_tac
      x="l"
      in exI)
      apply(rule_tac
      x="r@\<beta>@y"
      in exI)
      apply(clarsimp)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
    apply(thin_tac "cfgSTD.derivation G' d1")
    apply(thin_tac "maximum_of_domain d1 dGn")
    apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = \<delta>@\<alpha>\<rparr>)")
    apply(thin_tac "d1 dGn = Some (pair ea \<lparr>cfg_conf = teB Do#liftB w'\<rparr>)")
    apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgSTD.derivation G' d \<and> maximum_of_domain d (Suc na+dGn) \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>) \<and> d (Suc na+dGn) = Some (pair (if dGn=0 then (Some e2) else ea) \<lparr>cfg_conf = teB Do # liftB w'@\<beta>@y\<rparr>)")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_append da d1 (Suc na)"
      in exI)
     apply(rule context_conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
      apply(rule cfgSTD.derivation_concat2)
         apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(force)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
      apply(clarsimp)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
      apply(rule concat_has_max_dom)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
     apply(simp add: derivation_append_def)
     apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b d1)(*strict*)
    apply(thin_tac "cfgRM.derivation G' da")
    apply(thin_tac "maximum_of_domain da (Suc na)")
    apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
    apply(thin_tac "da na = Some (pair e1 \<lparr>cfg_conf = \<delta> @ teA A # y\<rparr>)")
    apply(thin_tac "da (Suc na) = Some (pair (Some e2) \<lparr>cfg_conf = \<delta> @ \<alpha> @ w'a @ [teB Do]\<rparr>)")
    apply(thin_tac "cfgSTD.derivation G' d1")
    apply(thin_tac "maximum_of_domain d1 dGn")
    apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = teB Do # XSEQ @ w'a @ [teB Do]\<rparr>)")
    apply(thin_tac "d1 dGn = Some (pair ea \<lparr>cfg_conf = teB Do # liftB w' @ w'a @ [teB Do]\<rparr>)")
    apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgSTD.derivation G' d \<and> maximum_of_domain d n' \<and> d 0 = Some (pair None \<lparr>cfg_conf = teB Do # liftB w'@w'a @ [teB Do]\<rparr>) \<and> d n' = Some (pair eb \<lparr>cfg_conf = teB Do # liftB w'@w'b @ [teB Do]\<rparr>)")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_map d' (\<lambda>c. \<lparr>cfg_conf=teB Do # liftB w'@(cfg_conf c)\<rparr>)"
      in exI)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
      apply(rule cfgSTD.derivation_map_preserves_derivation2)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da aa ec b l r)(*strict*)
      apply(rule_tac
      x="teB Do # liftB w'@l"
      in exI)
      apply(rule_tac
      x="r"
      in exI)
      apply(clarsimp)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 d' n' eb w'a w'b da)(*strict*)
    apply(thin_tac "maximum_of_domain d' n'")
    apply(thin_tac "cfgRM.derivation G' d'")
    apply(thin_tac "cfgLM.belongs G' d'")
    apply(thin_tac "d' 0 = Some (pair None \<lparr>cfg_conf = w'a @ [teB Do]\<rparr>)")
    apply(thin_tac "d' n' = Some (pair eb \<lparr>cfg_conf = w'b @ [teB Do]\<rparr>)")
    apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
    apply(rule_tac
      x="derivation_append da db (Suc na+dGn)"
      in exI)
    apply(subgoal_tac "cfgSTD.derivation G' (derivation_append da db (Suc na + dGn))")
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     prefer 2
     apply(rule cfgSTD.derivation_concat2)
        apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(clarsimp)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
     apply(simp add: derivation_append_def)
     apply(simp add: cfg_initial_configurations_def)
     apply(simp add: cfg_configurations_def)
     apply(rule cfg_initial_in_nonterms)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
    apply(rule conjI)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(simp add: cfg_marked_effect_def)
     apply(rule_tac
      x="if n'=0 then ((if dGn = 0 then Some e2 else ea)) else eb"
      in exI)
     apply(rule_tac
      x="\<lparr>cfg_conf = teB Do # liftB w' @ w'b @ [teB Do]\<rparr>"
      in exI)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
      apply(rule_tac
      x="Suc (na + dGn)+n'"
      in exI)
      apply(simp add: derivation_append_def)
      apply(clarsimp)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(rule conjI)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
      apply(clarsimp)
      apply(simp only: setAConcat concat_asso)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(clarsimp)
     apply(rule_tac
    t="liftB (w' @ filterB w'b @ [Do])"
    and s="liftB (w') @ liftB (filterB w'b @ [Do])"
    in ssubst)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(clarsimp)
   apply(rule_tac
    t="liftB (filterB w'b @ [Do])"
    and s="liftB (filterB w'b) @ liftB [Do]"
    in ssubst)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(clarsimp)
   apply(rule liftBDeConv2)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
  apply(rule conjI)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(rule_tac
    x="Suc (na + dGn)+n'"
    in exI)
  apply(rule_tac
    x="if n'=0 then ((if dGn = 0 then Some e2 else ea)) else eb"
    in exI)
  apply(rule_tac
    x="\<lparr>cfg_conf = teB Do # liftB w' @ w'b @ [teB Do]\<rparr>"
    in exI)
  apply(rule conjI)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(rule conjI)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
   apply(rule setA_liftB)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
  apply(rule_tac
    e="if n'=0 then (if dGn = 0 then Some e2 else ea) else eb"
    and d="derivation_append da db (Suc (na + dGn))"
    and i="Suc (na + dGn)+n'"
    in cfgSTD.belongs_configurations)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(rule_tac
    ca="\<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>"
    in cfgSTD.derivation_belongs)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(rule CFG_derivation_initial_pos0)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(rule cfg_initial_in_nonterms)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a na \<alpha> \<beta> y \<delta> e2 n' eb w'a w'b da db)(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 da na \<alpha> \<beta> y A \<delta> e1 e2 d' n' eb w'a w'b)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(subgoal_tac "e \<in> parser_rules P")
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  prefer 2
  apply(rule_tac
    t="parser_rules P"
    and s="parser_step_labels P"
    in ssubst)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(rule parserS.belongs_step_labels)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(subgoal_tac "rule_rpush e = [a]")
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  prefer 2
  apply(subgoal_tac "length (rule_rpush e) \<le> Suc 0")
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  prefer 2
  apply(rule AF_LR_PARSER_every_rules_pushes_at_most_one)
      apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(case_tac "rule_rpush e")
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa list)(*strict*)
  apply(case_tac list)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa list)(*strict*)
  prefer 2
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa list ab lista)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e")
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 aa)(*strict*)
  apply(simp add: valid_parser_def)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  prefer 2
  apply(rule_tac
    m="Suc n"
    in parserS.step_detail_before_some_position)
   apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 e1 c1)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 e1 c1 x xa)(*strict*)
  apply(case_tac v')
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 e1 c1 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d v' XSEQ dG ea dGn n e a d1 e1 c1 x xa aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x list)(*strict*)
  apply(rename_tac w)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
  apply(subgoal_tac "\<exists>s. set s \<subseteq> epda_events M \<and> (parserS_conf_stack c1) = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#s)")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
  prefer 2
  apply(rule_tac
    i="n"
    in F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_everywhere)
        apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
  prefer 2
  apply(case_tac c1)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 x w)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
  apply(case_tac c)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w)(*strict*)
  apply(clarsimp)
  (*
the reduce rule is of the form:
(\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>)| q q_seq (I::('a, 'b) DT_cfg_item) y qA.
  q \<in> epda_states M
  \<and> I \<in> q
  \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G
  \<and> (cfg_item_rhs1 I=[])
  \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I)))
  \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))
  \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq)}

where y=[a]
then there is a special I' in last XSEQ: it has
 because of (qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))))
  the same lookahead y!
for this I' obtain the sententialRM
*)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w s)(*strict*)
  apply(subgoal_tac "e \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M (Suc 0)")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w s)(*strict*)
  prefer 2
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n e a d1 e1 c1 x w s)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s aa b)(*strict*)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(erule disjE)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s aa b)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s aa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(subgoal_tac "teA (cfg_item_lhs I) \<in> epda_events M")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    in cfg_prod_in_two_elements_construct_domain_subset_trans2)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(subgoal_tac "qA=F_DFA_GOTO M q (teA (cfg_item_lhs I))")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_F_EPDA_GOTO_elem)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(thin_tac "F_DFA_GOTO M q (teA (cfg_item_lhs I)) \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  prefer 2
  apply(rule_tac
    B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
    in subset_trans)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(simp only: AF_LR_PARSER_input_def valid_cfg_def)
  apply(erule conjE)+
  apply(erule_tac
    A="cfg_productions G"
    and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
    in ballE)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
    apply(clarsimp)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
   apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(rule_tac
    B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in subset_trans)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  prefer 2
  apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)} = F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q q_seq I)(*strict*)
  apply(thin_tac "q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(clarsimp)
  (*
  P / d
  0 : | c = \<langle> <$> , w'.a.w.$ \<rangle>
  n : e1 | c1 = \<langle> <$.s> , a.w.$ \<rangle>
  Suc n: \<langle> q.<q/rhs2 I>, a, q.<q/lhs I>, a \<rangle> | c' = \<langle> <$.XSEQ>, a.w.$ \<rangle>

  x.q.<q/lhs I> = <$.XSEQ>
  x.q.<q/rhs2 I>= <$.s>
  \<lparr>lhs I,rhs2 I,[],a\<rparr> \<in> last(q.<q/rhs2 I>)

  thus: \<lparr>lhs I,rhs2 I,[],a\<rparr> \<in> last(x.q.<q/rhs2 I>)
  thus: \<lparr>lhs I,rhs2 I,[],a\<rparr> \<in> last(<$.s>)
  thus: \<lparr>lhs I,rhs2 I,[],a\<rparr> \<in> last(q0.<$.s>)
  thus: SententialRM G' ($.s.[].a) (from F_LR_MACHINE_preserves_SententialRM)
  missing: a derivation from s to w'
    * possibly using 29?
*)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(subgoal_tac "\<forall>\<Phi> w'' \<pi>' YSEQ. \<Phi>=\<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = a # w @ [parser_bottom P]\<rparr> \<and> w''=w'@ a # w@[parser_bottom P] \<and> \<pi>'=get_labels d n \<and> YSEQ=[] \<longrightarrow> (\<exists>XSEQ y x. \<Phi> = \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#XSEQ),parserS_conf_scheduler=y\<rparr> \<and> w''=x@y \<and> viable_prefix G' (teB Do#XSEQ) \<and> (length \<pi>') = length (tau (parser_marker P) \<pi>') + length x \<and> (\<exists>dG e dGn. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf=XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf=YSEQ@(liftB x)\<rparr>) \<and> (get_labels dG dGn) = (List.rev (tau (parser_marker P) \<pi>'))))")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  prefer 2
  apply(rule allI)+
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
  apply(rule impI)
  apply(rule_tac
    dPn="n"
    and dP="derivation_take d n"
    in Lemma6__29)
        apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
       prefer 2
       apply(rule parserS.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
      prefer 2
      apply(rule maximum_of_domain_derivation_take)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
     prefer 2
     apply(rule_tac
    t="\<pi>'"
    and s="take n \<pi>'"
    in subst)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
      apply(rule take_all)
      apply(rule_tac
    t="length \<pi>'"
    and s="n"
    in ssubst)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
       apply(rule get_labels_length)
       apply(force)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
     apply(rule_tac
    n="0"
    in derivation_take_preserves_get_labels)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
    prefer 2
    apply(rule parserS.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def)
   apply(clarsimp)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
   apply(case_tac c)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I parserS_conf_stacka parserS_conf_schedulera)(*strict*)
   apply(clarsimp)
   apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
   apply(rule_tac
    t="parser_initial P"
    and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
    in ssubst)
    apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
   apply(rule sym)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
       apply(force)
      apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
      apply(force)
     apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
     apply(force)
    apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
  prefer 2
  apply(simp add: derivation_take_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
  apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G' (Suc 0) (teB Do # YSEQ)")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
  apply(erule exE)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ Ia)(*strict*)
  apply(rule Fact6_12__1)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I \<Phi> w'' \<pi>' YSEQ)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(rule_tac
    t="valid_item_set G' (Suc 0) [teB Do]"
    and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
    in ssubst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
         apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(rule hasElem_prefix_closureise)
  apply(rule_tac
    G="G"
    in F_LR_MACHINE_prefix_closureise_additionalItems_1)
           apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
         apply(force)
        apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(subgoal_tac "s=XSEQa")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    in F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_inj)
             apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
            apply(force)
           apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rule_tac
    B="set (teB Do # XSEQa)"
    in subset_trans)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
   apply(rule_tac
    B="epda_events M"
    in subset_trans)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(rule viable_prefix_in_CFG)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(rule_tac
    t="(F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0))"
    and s="M"
    in ssubst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(rule_tac
    t="F_FRESH (cfg_events G)"
    and s="Do"
    in ssubst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(rule_tac
    t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa))"
    and s="valid_item_set G' (Suc 0) (teB Do # XSEQa)"
    in subst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(rule F_LR_MACHINE_all_SOUND_NotNil)
         apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(rule viable_prefix_in_CFG)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(rule viable_prefix_in_CFG)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G' (Suc 0) (teB Do # XSEQa)")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(rule Fact6_12__6)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w s q I XSEQa dGa e dGna)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(subgoal_tac "SententialRM G' ((teB Do#XSEQa)@(cfg_item_rhs2 \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = [a]\<rparr>)@(liftB(cfg_item_look_ahead \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = [a]\<rparr>)))")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  prefer 2
  apply(rule_tac
    q="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa))"
    and G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_LR_MACHINE_preserves_SententialRM)
             apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
            apply(force)
           apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(rule viable_prefix_in_CFG)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa)"
    and s="x @ q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)"
    in ssubst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(rule_tac
    t="last (epda_initial M # x @ q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))"
    and s="(if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))"
    in ssubst)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (teB Do # XSEQa) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa))")
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   prefer 2
   apply(rule_tac
    M="M"
    and q="epda_initial M"
    in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
        apply(force)
       apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
       apply(force)
      apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
      apply(force)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(rule viable_prefix_in_CFG)
     apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
     apply(force)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(rule conjI)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(clarsimp)
   apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa)"
    and s="x @ [q]"
    in ssubst)
    apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
    apply(force)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa)"
    and s="x @ q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)"
    in ssubst)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(simp (no_asm))
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "a\<noteq>Do")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  prefer 2
  apply(subgoal_tac "c' \<in> parserS_configurations P")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  prefer 2
  apply(rule_tac
    d="d"
    and i="Suc n"
    in parserS.belongs_configurations)
   apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
   apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(force)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac w' d XSEQ dG ea dGn n d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(simp add: AF_LR_PARSER_def AF_LR_PARSER_input_def)
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(thin_tac "cfgRM.Nonblockingness_branching  G")
  apply(rename_tac c c' w' d XSEQ dG ea dGn n a d1 e1 c1 x w q I XSEQa dGa e dGna)(*strict*)
  apply(thin_tac "parserS_conf_stack c = [parser_initial P]")
  apply(thin_tac "c \<in> parserS_configurations P")
  apply(thin_tac "parserS.derivation P d")
  apply(thin_tac "d 0 = Some (pair None c)")
  apply(thin_tac "d (Suc n) = Some (pair (Some \<lparr>rule_lpop = q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I), rule_rpop = [a], rule_lpush = [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))], rule_rpush = [a]\<rparr>) c')")
  apply(thin_tac "maximum_of_domain d (Suc n)")
  apply(thin_tac "valid_parser P")
  apply(thin_tac "parserS.belongs P d")
  apply(thin_tac "valid_dfa M")
  apply(thin_tac "some_step_from_every_configuration M")
  apply(thin_tac "parserS_conf_scheduler c = w' @ a # w @ [parser_bottom P]")
  apply(thin_tac "parserS_conf_scheduler c' = a # w @ [parser_bottom P]")
  apply(thin_tac "set XSEQ \<subseteq> epda_events M")
  apply(thin_tac "parserS_conf_stack c' = x @ [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))]")
  apply(thin_tac "viable_prefix G' (teB Do # XSEQ)")
  apply(thin_tac "length (get_labels d (Suc n)) = length (tau (parser_marker P) (get_labels d (Suc n))) + length w'")
  apply(thin_tac "get_labels dG dGn = rev (tau (parser_marker P) (get_labels d (Suc n)))")
  apply(thin_tac "cfgSTD.derivation G' d1")
  apply(thin_tac "maximum_of_domain d1 dGn")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = teB Do # XSEQ\<rparr>)")
  apply(thin_tac "d1 dGn = Some (pair ea \<lparr>cfg_conf = teB Do # liftB w'\<rparr>)")
  apply(thin_tac "\<lparr>rule_lpop = q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I), rule_rpop = [a], rule_lpush = [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))], rule_rpush = [a]\<rparr> \<in> parser_rules P")
  apply(thin_tac "d n = Some (pair e1 c1)")
  apply(thin_tac "parserS_conf_stack c1 = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa)")
  apply(thin_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ) = x @ [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))]")
  apply(thin_tac "parserS_conf_scheduler c1 = a # w @ [parser_bottom P]")
  apply(thin_tac "set XSEQa \<subseteq> epda_events M")
  apply(thin_tac "x @ q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQa)")
  apply(thin_tac "q \<in> epda_states M")
  apply(thin_tac "I \<in> q")
  apply(thin_tac "\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G")
  apply(thin_tac "cfg_item_rhs1 I = []")
  apply(thin_tac "\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = [a]\<rparr> \<in> (if F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = [] then q else last (F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)))")
  apply(thin_tac "teA (cfg_item_lhs I) \<in> epda_events M")
  apply(thin_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
  apply(thin_tac "viable_prefix G' (teB Do # XSEQa)")
  apply(thin_tac "length (get_labels d n) = length (tau (parser_marker P) (get_labels d n)) + length w'")
  apply(thin_tac "get_labels dGa dGna = rev (tau (parser_marker P) (get_labels d n))")
  apply(clarsimp)
  apply(rename_tac w' a XSEQa dGa e dGna)(*strict*)
  apply(rename_tac w a s d e n)
  apply(rename_tac w a s d e n)(*strict*)
  apply(simp add: SententialRM_def)
  apply(clarsimp)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule_tac
    t="cfgRM.marked_language G"
    and s="cfgSTD.marked_language G"
    in subst)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule CFG_lang_rm_lang_equal)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(subgoal_tac "\<exists>da. (cfgRM.derivation G' da \<and> cfgLM.belongs G' da \<and> cfgRM.derivation_initial G' da \<and> da na = Some (pair ea \<lparr>cfg_conf = teB Do # s @ teB a # v\<rparr>)) \<and> maximum_of_domain da na")
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  prefer 2
  apply(rule_tac
    d="da"
    in derivation_extend_with_maximum_of_domain)
   apply(rename_tac w a s d e n da ea na v)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule cfgRM.derivation_take_preserves_derivation)
  apply(force)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule cfgRM.derivation_take_preserves_belongs)
  apply(force)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(rule cfgRM.derivation_take_preserves_derivation_initial)
  apply(force)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac w a s d e n da ea na v)(*strict*)
  apply(thin_tac "cfgRM.derivation G' da")
  apply(thin_tac "cfgLM.belongs G' da")
  apply(thin_tac "cfgRM.derivation_initial G' da")
  apply(thin_tac "da na = Some (pair ea \<lparr>cfg_conf = teB Do # s @ teB a # v\<rparr>)")
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  apply(subgoal_tac "\<exists>v'. v=v'@[teB Do]")
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  prefer 2
  apply(subgoal_tac "da 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  prefer 2
  apply(rule CFGRM_derivation_initial_pos0)
   apply(rename_tac w a s d e n ea na v da)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  apply(case_tac na)
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na v da nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  apply(subgoal_tac "da (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  prefer 2
  apply(rule F_CFG_AUGMENT__FirstStep)
         apply(rename_tac w a s d e n ea v da nat)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac w a s d e n ea v da nat)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w a s d e n ea v da nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea v da nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a s d e n ea v da nat)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac w a s d e n ea v da nat)(*strict*)
    apply(rule cfgRM_derivations_are_cfg_derivations)
    apply(force)
   apply(rename_tac w a s d e n ea v da nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  apply(subgoal_tac "\<exists>e w. da (Suc nat) = Some (pair e \<lparr>cfg_conf = w @ [teB Do]\<rparr>)")
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  prefer 2
  apply(rule_tac
    G="G'"
    and m="Suc 0"
    in terminals_at_ending_are_never_modified_list)
       apply(rename_tac w a s d e n ea v da nat)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac w a s d e n ea v da nat)(*strict*)
      apply(force)
     apply(rename_tac w a s d e n ea v da nat)(*strict*)
     apply(force)
    apply(rename_tac w a s d e n ea v da nat)(*strict*)
    apply(force)
   apply(rename_tac w a s d e n ea v da nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea v da nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea v da nat wa)(*strict*)
  apply(case_tac v)
  apply(rename_tac w a s d e n ea v da nat wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea v da nat wa aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. v = w' @ [x']")
  apply(rename_tac w a s d e n ea v da nat wa aa list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac w a s d e n ea v da nat wa aa list)(*strict*)
  apply(thin_tac "v=aa#list")
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na v da)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na da v')(*strict*)
  apply(subgoal_tac "\<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgRM.derivation G d' \<and> cfgRM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=v'\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}")
  apply(rename_tac w a s d e n ea na da v')(*strict*)
  prefer 2
  apply(subgoal_tac "\<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgRM.derivation G' d' \<and> cfgRM.belongs G' d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=v'\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}")
  apply(rename_tac w a s d e n ea na da v')(*strict*)
  prefer 2
  apply(rule_tac
    n="na"
    and ?w1.0="teB Do # s @ [teB a]"
    and ?w3.0="[teB Do]"
    and d="da"
    in CFGRM_Nonblockingness_to_elimination)
        apply(rename_tac w a s d e n ea na da v')(*strict*)
        apply(force)
       apply(rename_tac w a s d e n ea na da v')(*strict*)
       apply(force)
      apply(rename_tac w a s d e n ea na da v')(*strict*)
      apply(force)
     apply(rename_tac w a s d e n ea na da v')(*strict*)
     apply(force)
    apply(rename_tac w a s d e n ea na da v')(*strict*)
    apply(force)
   apply(rename_tac w a s d e n ea na da v')(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea na da v')(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea na da v')(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(rule_tac
    x="d'"
    in exI)
  apply(rule_tac
    x="n'"
    in exI)
  apply(clarsimp)
  apply(case_tac na)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb)(*strict*)
  apply(simp add: cfgRM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac w a s d e n da v' d' n' wa eb)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> da (Suc nat) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__on_old_grammar_basically)
          apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
      apply(force)
     apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(rule CFGRM_derivation_initial_pos0)
     apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
     apply(force)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(force)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = teB Do # s @ teB a # v' @ [teB Do]\<rparr> \<in> cfg_configurations G'")
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  prefer 2
  apply(rule_tac
    d="da"
    and i="Suc nat"
    in cfgSTD.belongs_configurations)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(subgoal_tac "setA v' \<subseteq> cfg_nonterminals G \<and> setB v' \<subseteq> cfg_events G")
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  prefer 2
  apply(rule conjI)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(rule_tac
    G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__in_nonterms_of_G)
        apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp only: setAConcat concat_asso)+
    apply(simp)
    apply(erule conjE)+
    apply(simp only: setAConcat concat_asso)+
    apply(force)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(rule_tac
    G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__in_cfg_events_of_G)
       apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(simp only: setBConcat concat_asso)+
   apply(simp)
   apply(erule conjE)+
   apply(simp only: setBConcat concat_asso)+
   apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(rule_tac
    G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__reflects_derivationRM)
         apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
     apply(force)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(rule_tac
    G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__in_nonterms_of_G)
         apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp only: setAConcat concat_asso)+
     apply(simp)
     apply(erule conjE)+
     apply(simp only: setAConcat concat_asso)+
     apply(force)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(force)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(rule cfgSTD.derivation_belongs)
    apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
   apply(force)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(rename_tac w a s d e n ea da v' d' n' wa eb nat)(*strict*)
  apply(rule cfgRM_derivations_are_cfg_derivations)
  apply(force)
  apply(rename_tac w a s d e n ea na da v')(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(rule_tac
    x="w @ a #filterB wa"
    in exI)
  apply(clarsimp)
  apply(rule_tac
    Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__lang_prime)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(simp add: F_CFG_AUGMENT__input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgSTD.marked_language_def)
  apply(subgoal_tac "\<exists>d. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = teB Do#s\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = teB Do#liftB w\<rparr>) ")
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  prefer 2
  apply(rule_tac
    x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=teB Do#(cfg_conf c)\<rparr>)"
    in exI)
  apply(rule conjI)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation2)
   apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
   apply(rule_tac
    G="G"
    and Do="Do"
    and S'="S'"
    and G'="G'"
    in F_CFG_AUGMENT__preserves_derivation)
       apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb aa ec b l r)(*strict*)
  apply(rule_tac
    x="teB Do#l"
    in exI)
  apply(rule_tac
    x="r"
    in exI)
  apply(clarsimp)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(force)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac w a s d e n ea na da v' d' n' wa eb)(*strict*)
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = s\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)")
  apply(clarsimp)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = teB Do#s@teB a # v' @ [teB Do]\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = teB Do#liftB w@teB a # v' @ [teB Do]\<rparr>) ")
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  prefer 2
  apply(rule_tac
    x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=(cfg_conf c)@teB a # v' @ [teB Do]\<rparr>)"
    in exI)
  apply(rule conjI)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation2)
   apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
   apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d aa ec b l r)(*strict*)
  apply(rule_tac
    x="l"
    in exI)
  apply(rule_tac
    x="r@teB a # v' @ [teB Do]"
    in exI)
  apply(clarsimp)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(thin_tac "cfgSTD.derivation G' d")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = teB Do # s\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = teB Do # liftB w\<rparr>)")
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d. cfgSTD.derivation G' d \<and> maximum_of_domain d (na+n) \<and> cfgSTD.derivation_initial G' d \<and> d (na+n) = Some (pair (if n=0 then ea else e) \<lparr>cfg_conf = teB Do # liftB w @ teB a # v' @ [teB Do]\<rparr>)")
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  prefer 2
  apply(rule_tac
    x="derivation_append da d na"
    in exI)
  apply(rule context_conjI)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule cfgSTD.derivation_concat2)
     apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
    apply(force)
   apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
   apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule concat_has_max_dom)
   apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
   apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
    apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
    apply(force)
   apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
   apply(rule CFGRM_to_CFG_derivation_initial)
    apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
    apply(force)
   apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
   apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(force)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac w a s e n ea na da v' d' n' wa eb d)(*strict*)
  apply(thin_tac "cfgRM.derivation G' da")
  apply(thin_tac "cfgLM.belongs G' da")
  apply(thin_tac "cfgRM.derivation_initial G' da")
  apply(thin_tac "da na = Some (pair ea \<lparr>cfg_conf = teB Do # s @ teB a # v' @ [teB Do]\<rparr>)")
  apply(thin_tac "maximum_of_domain da na")
  apply(thin_tac "cfgSTD.derivation G' d")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = teB Do # s @ teB a # v' @ [teB Do]\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = teB Do # liftB w @ teB a # v' @ [teB Do]\<rparr>)")
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(subgoal_tac "\<exists>d'. cfgSTD.derivation G' d' \<and> maximum_of_domain d' n' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = teB Do # liftB w @ teB a # v' @ [teB Do]\<rparr>) \<and> d' n' = Some (pair eb \<lparr>cfg_conf = teB Do # liftB w @ teB a # wa @ [teB Do]\<rparr>) ")
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  prefer 2
  apply(rule_tac
    x="derivation_map d' (\<lambda>c. \<lparr>cfg_conf=teB Do # liftB w @ teB a # (cfg_conf c)@[teB Do]\<rparr>)"
    in exI)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation2)
   apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
   apply(rule_tac
    G="G"
    and S'="S'"
    and Do="Do"
    and G'="G'"
    in F_CFG_AUGMENT__preserves_derivation)
       apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' d' n' wa eb d aa ec b l r)(*strict*)
  apply(rule_tac
    x="teB Do # liftB w @ teB a # l"
    in exI)
  apply(rule_tac
    x="r@[teB Do]"
    in exI)
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(force)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac w a e n ea na v' d' n' wa eb d)(*strict*)
  apply(thin_tac "maximum_of_domain d' n'")
  apply(thin_tac "cfgRM.derivation G d'")
  apply(thin_tac "cfgLM.belongs G d'")
  apply(thin_tac "d' 0 = Some (pair None \<lparr>cfg_conf = v'\<rparr>)")
  apply(thin_tac "d' n' = Some (pair eb \<lparr>cfg_conf = wa\<rparr>)")
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule_tac
    x="derivation_append d d' (na+n)"
    in exI)
  apply(subgoal_tac "cfgSTD.derivation G' (derivation_append d d' (na+n))")
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  prefer 2
  apply(rule cfgSTD.derivation_concat2)
    apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
    apply(force)
   apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
   apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule context_conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
   apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
   apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(rule_tac
    x="if n'=0 then (if n=0 then ea else e) else eb"
    in exI)
  apply(rule_tac
    x="\<lparr>cfg_conf = teB Do # liftB w @ teB a # wa @ [teB Do]\<rparr>"
    in exI)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule_tac
    x="na+n+n'"
    in exI)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(clarsimp)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(clarsimp)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule setA_liftB)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp (no_asm) only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(simp (no_asm) only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(rule liftBDeConv2)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(rule_tac
    x="na+n+n'"
    in exI)
  apply(rule_tac
    x="if n'=0 then (if n=0 then ea else e) else eb"
    in exI)
  apply(rule_tac
    x="\<lparr>cfg_conf = teB Do # liftB w @ teB a # wa @ [teB Do]\<rparr>"
    in exI)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(rule conjI)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(clarsimp)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rule setA_liftB)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule_tac
    e="if n'=0 then (if n=0 then ea else e) else eb"
    and d="derivation_append d d' (na + n)"
    and i="na+n+n'"
    in cfgSTD.belongs_configurations)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(force)
  apply(rename_tac w a e n ea na v' n' wa eb d d')(*strict*)
  apply(simp add: derivation_append_def)
  apply(force)
  done

end
