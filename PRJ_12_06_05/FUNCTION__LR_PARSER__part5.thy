section {*FUNCTION\_\_LR\_PARSER\_\_part5*}
theory
  FUNCTION__LR_PARSER__part5

imports
  FUNCTION__LR_PARSER__part4

begin

lemma setA_drop_subset: "
  setA (drop n w) \<subseteq> setA w"
  apply(induct w arbitrary: n)
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac n)
   apply(force)
  apply(force)
  done

lemma setB_drop_subset: "
  setB (drop n w) \<subseteq> setB w"
  apply(induct w arbitrary: n)
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac n)
   apply(force)
  apply(force)
  done

lemma F_LRk_PARSER__rules_vs_AF_LR_PARSER__rules: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> F_LRk_PARSER__rules G F G' M k = AF_LR_PARSER__rules G G' M k"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp (no_asm) only: F_LRk_PARSER__rules_def AF_LR_PARSER__rules_def)
  apply(rule union_pair_wise_equal)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(case_tac I)
    apply(rename_tac A w1 w2 l)
    apply(clarsimp)
    apply(simp add: item_core_def)
    apply(subgoal_tac "length w2 = length q_seq")
     apply(case_tac "q_seq=[]")
      apply(rule_tac x="q" in exI)
      apply(rule_tac x="q_seq" in exI)
      apply(clarsimp)
      apply(rule_tac x="\<lparr>cfg_item_lhs=A,item_rhs1=[],item_rhs2=[],item_look_ahead=l\<rparr>" in exI)
      apply(clarsimp)
     apply(clarsimp)
     apply(rule_tac x="q" in exI)
     apply(rule_tac x="q_seq" in exI)
     apply(clarsimp)
     apply(rule_tac x="\<lparr>cfg_item_lhs=A,item_rhs1=[],item_rhs2=w2,item_look_ahead=l\<rparr>" in exI)
     apply(clarsimp)
     apply(thin_tac "qA \<in> F_EPDA_GOTO
              (F_LR_MACHINE
                (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
                  (F_FRESH (cfg_events G)))
                F k)
              q (teA A)")
     apply(rule_tac xs="q_seq" in rev_cases)
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "set w2
      \<subseteq> epda_events
           (F_LR_MACHINE
             (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
               (F_FRESH (cfg_events G)))
             F k)")
      prefer 2
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
      apply(erule_tac x="\<lparr>prod_lhs = A, prod_rhs = w2\<rparr>" in ballE)
       prefer 2
       apply(force)
      apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check cfg_step_label.select_convs(2))
     apply(subgoal_tac "SSX = F_EPDA_GOTO_SEQUENCE
           (F_LR_MACHINE
             (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
               (F_FRESH (cfg_events G)))
             F k)
           q w2" for SSX)
      prefer 2
      apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(subgoal_tac "X" for X)
      prefer 2
      apply(rule_tac G=" (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
            (F_FRESH (cfg_events G)))" in LRM_contains_theEqClasses)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "X" for X)
      prefer 2
      apply(rule_tac q="valid_item_set
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           k w" and G="G" and n="length w2" in F_LR_MACHINE_shifted_item_in_next_states)
                   apply(force)
                  apply(force)
                 apply(force)
                apply(force)
               apply(force)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(subgoal_tac "ys@[y] = F_DFA_GOTO_SEQUENCE
         (F_LR_MACHINE
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           F k)
         (valid_item_set
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           k w)
         w2")
      prefer 2
      apply(force)
     apply(clarsimp)
     apply(rule_tac xs="F_DFA_GOTO_SEQUENCE
               (F_LR_MACHINE
                 (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
                   (F_FRESH (cfg_events G)))
                 F k)
               (valid_item_set
                 (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
                   (F_FRESH (cfg_events G)))
                 k w)
               w2" in rev_cases)
      apply(force)
     apply(force)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac w="w2" in F_EPDA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
      apply(erule_tac x="\<lparr>prod_lhs = A, prod_rhs = w2\<rparr>" in ballE)
       prefer 2
       apply(force)
      apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check cfg_step_label.select_convs(2))
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="q" in exI)
   apply(rule_tac x="q_seq" in exI)
   apply(rule_tac xs="q_seq" in rev_cases)
    apply(clarsimp)
    apply(subgoal_tac "length (cfg_item_rhs2 I) = length []")
     prefer 2
     apply(rule_tac q="q" in F_EPDA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
      apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>" in ballE)
       prefer 2
       apply(force)
      apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check cfg_step_label.select_convs(2))
     apply(force)
    apply(rule_tac x="I\<lparr>cfg_item_look_ahead:=y\<rparr>" in exI)
    apply(case_tac I)
    apply(rename_tac A w1 w2 l)
    apply(clarsimp)
    apply(simp add: item_core_def)
   apply(clarsimp)
   apply(rule_tac x="I\<lparr>cfg_item_look_ahead:=ya\<rparr>" in exI)
   apply(case_tac I)
   apply(rename_tac A w1 w2 l)
   apply(clarsimp)
   apply(simp add: item_core_def)
   apply(subgoal_tac "set w2
      \<subseteq> epda_events
           (F_LR_MACHINE
             (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
               (F_FRESH (cfg_events G)))
             F k)")
    prefer 2
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(erule_tac x="\<lparr>prod_lhs = A, prod_rhs = w2\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check cfg_step_label.select_convs(2))
   apply(subgoal_tac "SSX = F_EPDA_GOTO_SEQUENCE
           (F_LR_MACHINE
             (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
               (F_FRESH (cfg_events G)))
             F k)
           q w2" for SSX)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G=" (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
            (F_FRESH (cfg_events G)))" in LRM_contains_theEqClasses)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac q="valid_item_set
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           k w" and G="G" and n="length w2" in F_LR_MACHINE_shifted_item_in_next_states)
                 apply(force)
                apply(force)
               apply(force)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "ys@[y] = F_DFA_GOTO_SEQUENCE
         (F_LR_MACHINE
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           F k)
         (valid_item_set
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           k w)
         w2")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(rule_tac xs="F_DFA_GOTO_SEQUENCE
               (F_LR_MACHINE
                 (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
                   (F_FRESH (cfg_events G)))
                 F k)
               (valid_item_set
                 (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
                   (F_FRESH (cfg_events G)))
                 k w)
               w2" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac z="ya" and w="w" and A="A" and  v="w2" and \<alpha>="[]" and \<beta>="[]" and k="k" and G'="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
            (F_FRESH (cfg_events G)))"  in valid_item_set_shift_symbol_back_mult)
    prefer 2
    apply(force)
   apply(rule_tac t="valid_item_set
           (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
             (F_FRESH (cfg_events G)))
           k (w @ w2)" and s="yb" in ssubst)
    prefer 2
    apply(force)
   apply(rule_tac t="yb" and s="last(F_DFA_GOTO_SEQUENCE
        (F_LR_MACHINE
          (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
            (F_FRESH (cfg_events G)))
          F k)
        (valid_item_set
          (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
            (F_FRESH (cfg_events G)))
          k w)
        w2)" in ssubst)
    apply(force)
   apply(rule_tac t="valid_item_set
            (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
              (F_FRESH (cfg_events G)))
            k w" in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply (rule two_elements_construct_domain_setA)
     apply(force)
    apply (rule two_elements_construct_domain_setB)
    apply(force)
   apply(case_tac "w=[]")
    apply(clarsimp)
    apply(rule_tac t="valid_item_set
            (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
              (F_FRESH (cfg_events G)))
            k w2" in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply (rule two_elements_construct_domain_setA)
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
     apply (rule two_elements_construct_domain_setB)
     apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(force)
   apply(clarsimp)
   apply(rule_tac t="valid_item_set
            (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G))
              (F_FRESH (cfg_events G)))
            k (w@w2)" in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply (rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
    apply (rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
   apply(clarsimp)
   apply(rule_tac t="F_DFA_GOTO_SEQUENCE
              (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)
              (epda_initial
                (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                  k))
              (w @ w2)" in ssubst)
    apply(rule F_DFA_GOTO_SEQUENCE_append_split_SHORT)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
     apply(force)
    apply(force)
   apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE
        (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)
        (epda_initial
          (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k))
        w)")
    prefer 2
    apply(rule_tac q="(epda_initial
          (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k))" in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
     apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(force)
   apply(rule_tac t="last (epda_initial
                      (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                        k) #
                     F_DFA_GOTO_SEQUENCE
                      (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                        k)
                      (epda_initial
                        (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                          k))
                      w)" and s="last (F_DFA_GOTO_SEQUENCE
                      (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                        k)
                      (epda_initial
                        (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                          k))
                      w)" in ssubst)
    apply(rule last_Cons_not_empty)
     apply(force)
    apply(force)
   apply(rule last_append_not_empty)
    prefer 2
    apply(force)
   apply(subgoal_tac "length w2 = length (F_DFA_GOTO_SEQUENCE
        (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)
        (last (F_DFA_GOTO_SEQUENCE
                (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                  k)
                (epda_initial
                  (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                    k))
                w))
        w2)")
    prefer 2
    apply(rule_tac q="(last (F_DFA_GOTO_SEQUENCE
                (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                  k)
                (epda_initial
                  (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                    k))
                w))" in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(rule_tac A="set(F_DFA_GOTO_SEQUENCE
              (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)
              (epda_initial
                (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                  k))
              w)" in set_mp)
       prefer 2
       apply(rule_tac xs="F_DFA_GOTO_SEQUENCE
              (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)
              (epda_initial
                (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F
                  k))
              w" in rev_cases)
        apply(force)
       apply(force)
      apply(rule_tac q="(epda_initial
            (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k))" and w="w" in F_DFA_GOTO_SEQUENCESound_main3)
           apply(force)
          apply(force)
         apply(force)
        apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
       apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac q aa y qA I)(*strict*)
   apply(rule_tac
      x="I"
      in bexI)
    apply(rename_tac q aa y qA I)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q aa y qA I)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac M="F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k" in LRM_contains_theEqClasses)
      prefer 3
      apply(force)
     prefer 2
     apply(force)
    apply(force)
   apply(simp add: item_core_def)
   apply(clarsimp)
   apply(subgoal_tac "valid_item ((F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))) k I")
    prefer 2
    apply(rule_tac \<gamma>="w" in  Fact6_12__2)
     apply(force)
    apply(force)
   apply(rule_tac
      t="cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) ((k - Suc 0)) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))"
      and s="F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (k - Suc 0) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))"
      in ssubst)
    apply(rename_tac aa y qA I w)(*strict*)
    apply(simp add: cfgSTD_first_compatible_def)
    apply(rule sym)
    apply(erule_tac x="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))" in allE)
    apply(erule_tac x="(drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))" in allE)
    apply(erule_tac x="(k - Suc 0)" in allE)
    apply(erule impE)
     apply(force)
    apply(erule impE)
     apply(force)
    apply(erule impE)
     apply(simp add: simpY)
     apply(simp add: valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> " in ballE)
      prefer 2
      apply(force)
     apply(clarsimp)
     apply(simp add: simpY)
     apply(clarsimp)
     apply(case_tac I)
     apply(clarsimp)
     apply(rename_tac A w1 w2 R)
     apply(case_tac w2)
      apply(clarsimp)
     apply(clarsimp)
     apply(simp add: F_CFG_AUGMENT_def)
     apply(case_tac k)
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "x \<in> setA list")
      apply(force)
     apply(rule_tac A="setA (drop nat list)" in set_mp)
      prefer 2
      apply(force)
     apply(rule setA_drop_subset)
    apply(erule impE)
     apply(simp add: simpY)
     apply(simp add: valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
      prefer 2
      apply(force)
     apply(clarsimp)
     apply(simp add: simpY)
     apply(clarsimp)
     apply(case_tac I)
     apply(clarsimp)
     apply(rename_tac A w1 w2 R)
     apply(case_tac w2)
      apply(clarsimp)
     apply(clarsimp)
     apply(rule conjI)
      apply(simp add: F_CFG_AUGMENT_def)
      apply(case_tac k)
       apply(force)
      apply(clarsimp)
      apply(subgoal_tac "x \<in> setB list")
       apply(force)
      apply(rule_tac A="setB (drop nat list)" in set_mp)
       prefer 2
       apply(force)
      apply(rule setB_drop_subset)
     apply(clarsimp)
     apply(simp add: valid_item_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac q aa y qA I)(*strict*)
  apply(rule_tac
      x="I"
      in exI)
  apply(rule conjI)
   apply(force)
  apply(rename_tac q aa y qA I)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac M="F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k" in LRM_contains_theEqClasses)
     prefer 3
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "valid_item ((F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))) k I")
   prefer 2
   apply(rule_tac \<gamma>="w" in  Fact6_12__2)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (k - Suc 0) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))"
      and s="cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (k - Suc 0) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))"
      in ssubst)
   apply(rename_tac aa y qA I w)(*strict*)
   apply(simp add: cfgSTD_first_compatible_def)
   apply(erule_tac x="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))" in allE)
   apply(erule_tac x="(drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))" in allE)
   apply(erule_tac x="k - (Suc 0)" in allE)
   apply(erule impE)
    apply(force)
   apply(erule impE)
    apply(force)
   apply(erule impE)
    apply(simp add: simpY)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> " in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(simp add: simpY)
    apply(clarsimp)
    apply(case_tac I)
    apply(clarsimp)
    apply(rename_tac A w1 w2 R)
    apply(case_tac w2)
     apply(clarsimp)
    apply(clarsimp)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(case_tac k)
     apply(force)
    apply(clarsimp)
    apply(subgoal_tac "x \<in> setA list")
     apply(force)
    apply(rule_tac A="setA (drop nat list)" in set_mp)
     prefer 2
     apply(force)
    apply(rule setA_drop_subset)
   apply(erule impE)
    apply(simp add: simpY)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(simp add: simpY)
    apply(clarsimp)
    apply(case_tac I)
    apply(clarsimp)
    apply(rename_tac A w1 w2 R)
    apply(case_tac w2)
     apply(clarsimp)
    apply(clarsimp)
    apply(rule conjI)
     apply(simp add: F_CFG_AUGMENT_def)
     apply(case_tac k)
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "x \<in> setB list")
      apply(force)
     apply(rule_tac A="setB (drop nat list)" in set_mp)
      prefer 2
      apply(force)
     apply(rule setB_drop_subset)
    apply(simp add: valid_item_def)
   apply(force)
  apply(simp add: item_core_def)
  done

theorem F_LRk_PARSER_vs_AF_LR_PARSER: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> F_LRk_PARSER G F G' M k Do = AF_LR_PARSER G G' M k Do"
  apply(simp (no_asm) only: F_LRk_PARSER_def AF_LR_PARSER_def)
  apply(rule_tac
      t="AF_LR_PARSER__rules G G' M k"
      and s="F_LRk_PARSER__rules G F G' M k"
      in subst)
   apply(rule F_LRk_PARSER__rules_vs_AF_LR_PARSER__rules)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LRk_PARSER__rules_vs_F_LR_PARSER__rules: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgSTD_first_compatible F (Suc 0)
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F (Suc 0)
  \<Longrightarrow> F_LRk_PARSER__rules G F G' M (Suc 0) = F_LR_PARSER__rules G G' M"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp (no_asm) only: F_LRk_PARSER__rules_def F_LR_PARSER__rules_def)
  apply(rule union_pair_wise_equal)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac M="F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0)" in LRM_contains_theEqClasses)
     prefer 3
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(rule order_antisym)
   prefer 2
   apply(rule subsetI)
   apply(clarsimp)
   apply(rule conjI)
    apply(force)
   apply(rule_tac x="I" in exI)
   apply(clarsimp)
   apply(simp add: cfgSTD_first_compatible_def)
   apply(erule_tac x="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))" in allE)
   apply(erule_tac x="(drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))" in allE)
   apply(erule_tac x="0" in allE)
   apply(clarsimp)
   apply(subgoal_tac "valid_item (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (Suc 0) I")
    prefer 2
    apply(rule Fact6_12__2)
     apply(force)
    apply(force)
   apply(erule impE)
    apply(simp add: simpY)
    apply(simp add: item_core_def)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(case_tac I)
    apply(rename_tac A w1 w2 l)
    apply(clarsimp)
    apply(simp add: simpY)
    apply(case_tac w2)
     apply(force)
    apply(force)
   apply(erule impE)
    apply(simp add: item_core_def)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def)
    apply(case_tac I)
    apply(rename_tac A w1 w2 l)
    apply(clarsimp)
    apply(simp add: simpY)
    apply(case_tac w2)
     apply(force)
    apply(clarsimp)
    apply(erule disjE)
     apply(force)
    apply(erule disjE)
     apply(force)
    apply(clarsimp)
    apply(force)
   apply(clarsimp)
   apply(thin_tac "F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) 0
        (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I)) =
       cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) 0
        (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))")
   apply(simp add: cfgSTD_first_def)
   apply(rule inMap)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" and w="drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I)" in canElimCombine)
     apply(force)
    apply(rule_tac B="cfg_nonterminals G" in subset_trans)
     prefer 2
     apply(force)
    apply(simp add: simpY)
    apply(simp add: item_core_def)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(case_tac I)
    apply(rename_tac A w1 w2 l)
    apply(clarsimp)
    apply(simp add: simpY)
    apply(case_tac w2)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>v. liftB v = w'")
    apply(clarsimp)
    apply(rule_tac x="v" in exI)
    apply(rule_tac x="d" in exI)
    apply(rule conjI)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(clarsimp)
     apply(rule_tac G="G" in F_CFG_AUGMENT__preserves_derivation)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(clarsimp)
    apply(rule_tac x="x" in exI)
    apply(rule_tac x="n" in exI)
    apply(clarsimp)
    apply(case_tac "d 0")
     apply(clarsimp)
    apply(clarsimp)
    apply(simp add: maximum_of_domain_def)
   apply(rule_tac x="filterB w'" in exI)
   apply (metis liftBDeConv2)
  apply(rule subsetI)
  apply(clarsimp)
  apply(rule context_conjI)
   prefer 2
   apply(force)
  apply(simp add: cfgSTD_first_compatible_def)
  apply(erule_tac x="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))" in allE)
  apply(erule_tac x="(drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))" in allE)
  apply(erule_tac x="0" in allE)
  apply(clarsimp)
  apply(subgoal_tac "valid_item (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (Suc 0) I")
   prefer 2
   apply(rule Fact6_12__2)
    apply(force)
   apply(force)
  apply(erule impE)
   apply(simp add: simpY)
   apply(simp add: item_core_def)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac I)
   apply(rename_tac A w1 w2 l)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(case_tac w2)
    apply(force)
   apply(force)
  apply(erule impE)
   apply(simp add: item_core_def)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(erule_tac x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>" in ballE)
    prefer 2
    apply(force)
   apply(simp add: valid_item_def)
   apply(case_tac I)
   apply(rename_tac A w1 w2 l)
   apply(clarsimp)
   apply(simp add: simpY)
   apply(case_tac w2)
    apply(force)
   apply(clarsimp)
   apply(erule disjE)
    apply(force)
   apply(erule disjE)
    apply(force)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) 0
        (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I)) =
       cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) 0
        (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))")
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  done

theorem F_LR_PARSER_vs_F_LRk_PARSER: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgSTD_first_compatible F (Suc 0)
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F (Suc 0)
  \<Longrightarrow> F_LRk_PARSER G F G' M (Suc 0) Do = F_LR_PARSER G G' M Do"
  apply(simp (no_asm) only: F_LRk_PARSER_def F_LR_PARSER_def)
  apply(rule_tac
      t="F_LRk_PARSER__rules G F G' M (Suc 0)"
      and s="F_LR_PARSER__rules G G' M"
      in ssubst)
   apply(rule F_LRk_PARSER__rules_vs_F_LR_PARSER__rules)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

definition F_LR_PARSER__SpecInput :: "
  ('nonterminal DT_symbol, 'event DT_symbol) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event DT_symbol) cfg
    \<times> ('nonterminal DT_symbol, 'event DT_symbol) DT_first_function
    \<times> (('nonterminal DT_symbol, 'event DT_symbol) DT_cfg_item set,
        ('nonterminal DT_symbol, 'event DT_symbol) DT_two_elements,
        nat) epda
    \<times> nat
    \<times> 'event DT_symbol
  \<Rightarrow> bool"
  where
    "F_LR_PARSER__SpecInput G X \<equiv>
  case X of
  (G', F, M, n, Do) \<Rightarrow>
    \<exists>S'.
      valid_cfg G
      \<and> cfgSTD_first_compatible F n
      \<and> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
      \<and> cfgSTD.Nonblockingness_branching G
      \<and> Do = F_FRESH (cfg_events G)
      \<and> S' = F_FRESH (cfg_nonterminals G)
      \<and> G' = F_CFG_AUGMENT G S' Do
      \<and> M = F_LR_MACHINE G' F n
      \<and> cfg_LRk G n"

definition can_detect_parser_bottom_only_in_Nonblockingness_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "can_detect_parser_bottom_only_in_Nonblockingness_configurations G \<equiv>
  \<forall>d e n. parserS.derivation_initial G d
  \<longrightarrow> maximum_of_domain d n
  \<longrightarrow> parser_fixed_input_length_rec1 d n = 0
  \<longrightarrow> parserS_conf_scheduler (the (get_configuration (d n))) = [parser_bottom G]
  \<longrightarrow> e \<in> parser_rules G
  \<longrightarrow> rule_rpop e = [parser_bottom G]
  \<longrightarrow> last (parserS_conf_stack (the (get_configuration (d n)))) = last (rule_lpop e)
  \<longrightarrow> parserS.Nonblockingness_configuration G (the (get_configuration (d n)))"

definition F_LR_PARSER__SpecOutput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('stack, 'event, 'marker) parser \<times> nat
  \<Rightarrow> bool"
  where
    "F_LR_PARSER__SpecOutput Gi X \<equiv>
  case X of (Go, k) \<Rightarrow>
  valid_parser Go
  \<and> parserFS.is_forward_edge_deterministic_accessible Go
  \<and> cfgSTD.marked_language Gi = parserS.marked_language Go
  \<and> parser_initial Go \<notin> parser_marking Go
  \<and> (k > 0
      \<longrightarrow> valid_bounded_parser Go k)
  \<and> (k = Suc 0
      \<longrightarrow>
      nonblockingness_language (parserS.unmarked_language Go) (parserS.marked_language Go)
      \<and> (\<forall>r \<in> parser_rules Go. rule_rpop r \<noteq> [])
      \<and> parser_no_access_final_with_read Go
      \<and> can_detect_parser_bottom_only_in_Nonblockingness_configurations Go)"

lemma FUNRLP_all_rules_pop: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []"
  apply(rule ballI)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "length (rule_rpop r) = Suc 0")
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(rule AF_LR_PARSER_every_rules_pops_one)
      apply(rename_tac r)(*strict*)
      apply(force)
     apply(rename_tac r)(*strict*)
     apply(force)
    apply(rename_tac r)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(force)
  done

lemma F_LR_PARSER_shift_rules_do_not_reach_final_state: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> valid_bounded_parser P (Suc 0)
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> parser_no_access_final_with_read P"
  apply(simp add: parser_no_access_final_with_read_def)
  apply(clarsimp)
  apply(rename_tac e a)(*strict*)
  apply(subgoal_tac "e \<in> (\<lambda>(x,y). x) ` (AF_LR_PARSER__rules G G' M (Suc 0))")
   apply(rename_tac e a)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac e a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(erule disjE)
   apply(rename_tac a aa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a q qA I)(*strict*)
  apply(thin_tac "[] \<in> cfgSTD_first G' 0 (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))")
  apply(rename_tac a q qA I)(*strict*)
  apply(subgoal_tac "qA \<in> {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])}")
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(rule_tac
      t="{last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])}"
      and s="parser_marking P"
      in subst)
    apply(rename_tac a q qA I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(rename_tac a q qA I)(*strict*)
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(subgoal_tac "qA = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(thin_tac "qA \<in> {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])}")
  apply(rename_tac a q qA I)(*strict*)
  apply(thin_tac "qA \<in> parser_marking P")
  apply(subgoal_tac "teB a \<in> epda_events M")
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def kPrefix_def)
   apply(rule_tac
      A="set (cfg_item_rhs2 I)"
      in set_mp)
    apply(rename_tac a q qA I)(*strict*)
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(rename_tac a q qA I)(*strict*)
     apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
    apply(rename_tac a q qA I)(*strict*)
    apply(rule_tac
      B="set (cfg_item_rhs1 I @ cfg_item_rhs2 I)"
      in subset_trans)
     apply(rename_tac a q qA I)(*strict*)
     apply(simp)
    apply(rename_tac a q qA I)(*strict*)
    apply(rule_tac
      G="G"
      in cfg_prod_in_two_elements_construct_domain_subset_trans)
      apply(rename_tac a q qA I)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac a q qA I)(*strict*)
     apply(force)
    apply(rename_tac a q qA I)(*strict*)
    apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
       apply(rename_tac a q qA I)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac a q qA I)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac a q qA I)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac a q qA I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac a q qA I)(*strict*)
   apply(case_tac "cfg_item_rhs2 I")
    apply(rename_tac a q qA I)(*strict*)
    apply(simp (no_asm_simp))
    apply(force)
   apply(rename_tac a q qA I aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a q qA I)(*strict*)
  apply(subgoal_tac "qA=F_DFA_GOTO M q (teB a)")
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(subgoal_tac "{F_DFA_GOTO M q (teB a)} = F_EPDA_GOTO M q (teB a)")
    apply(rename_tac a q qA I)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
        apply(rename_tac a q qA I)(*strict*)
        apply(force)
       apply(rename_tac a q qA I)(*strict*)
       apply(force)
      apply(rename_tac a q qA I)(*strict*)
      apply(force)
     apply(rename_tac a q qA I)(*strict*)
     apply(force)
    apply(rename_tac a q qA I)(*strict*)
    apply(force)
   apply(rename_tac a q qA I)(*strict*)
   apply(blast)
  apply(rename_tac a q qA I)(*strict*)
  apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teB a)")
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> F_DFA_GOTO M q (teB a)")
   apply(rename_tac a q qA I)(*strict*)
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(rule unequal1)
  apply(rule_tac
      x="\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do, teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr>"
      in bexI)
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(rule_tac
      A="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])))-{I. (valid_item G' (Suc 0) I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
    apply(rename_tac a q qA I)(*strict*)
    apply(subgoal_tac "length [teB Do, teA (cfg_initial G)] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
     apply(rename_tac a q qA I)(*strict*)
     prefer 2
     apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac a q qA I)(*strict*)
          apply(force)
         apply(rename_tac a q qA I)(*strict*)
         apply(force)
        apply(rename_tac a q qA I)(*strict*)
        apply(force)
       apply(rename_tac a q qA I)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac a q qA I)(*strict*)
      apply(simp add: F_LR_MACHINE_def)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac a q qA I)(*strict*)
       apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
      apply(rename_tac a q qA I)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
      apply(clarsimp)
      apply(rename_tac a q I)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac a q qA I)(*strict*)
     apply(force)
    apply(rename_tac a q qA I)(*strict*)
    apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
     apply(rename_tac a q qA I)(*strict*)
     apply(force)
    apply(rename_tac a q qA I)(*strict*)
    apply(force)
   apply(rename_tac a q qA I)(*strict*)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) - {I. valid_item G' (Suc 0) I \<and> item_core I \<in> cfg_productions G}"
      and s="{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>}"
      in ssubst)
    apply(rename_tac a q qA I)(*strict*)
    apply(rule_tac
      G="G"
      and S'="S'"
      and Do="Do"
      and G'="G'"
      in F_LR_MACHINE_prefix_closureise_additionalItems_2)
              apply(rename_tac a q qA I)(*strict*)
              apply(simp add: AF_LR_PARSER_input_def)
             apply(simp only: AF_LR_PARSER_input_def)
             apply(force)
            apply(rename_tac a q qA I)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac a q qA I)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac a q qA I)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac a q qA I)(*strict*)
         apply(force)
        apply(rename_tac a q qA I)(*strict*)
        apply(force)
       apply(rename_tac a q qA I)(*strict*)
       apply(force)
      apply(rename_tac a q qA I)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac a q qA I)(*strict*)
     apply(force)
    apply(rename_tac a q qA I)(*strict*)
    apply(force)
   apply(rename_tac a q qA I)(*strict*)
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(rule_tac
      t="M"
      and s="(F_LR_MACHINE G' F (Suc 0))"
      in ssubst)
   apply(rename_tac a q qA I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac a q qA I)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO (F_LR_MACHINE G' F (Suc 0)) q (teB a)"
      and s="F_VALID_ITEM_SET_GOTO G' F (Suc 0) (teB a) q"
      in subst)
   apply(rename_tac a q qA I)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
        apply(rename_tac a q qA I)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac a q qA I)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac a q qA I)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac a q qA I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac a q qA I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac a q qA I)(*strict*)
  apply(simp only: F_VALID_ITEM_SET_GOTO_def)
  apply(case_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F (Suc 0) (F_VALID_ITEM_SET_GOTO__basis (teB a) q)")
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(subgoal_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F (Suc 0) (F_VALID_ITEM_SET_GOTO__basis (teB a) q). I \<in> (F_VALID_ITEM_SET_GOTO__basis (teB a) q) \<or> (cfg_item_rhs1 I=[])")
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_fresh)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis (teB a) q \<subseteq> Collect(valid_item G' (Suc 0))")
    apply(rename_tac a q qA I)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
    apply(clarsimp)
    apply(rename_tac a q I x)(*strict*)
    apply(rule_tac
      q="q"
      in F_LR_MACHINE_States_contain_Items)
        apply(rename_tac a q I x)(*strict*)
        apply(force)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(force)
      apply(rename_tac a q I x)(*strict*)
      apply(force)
     apply(rename_tac a q I x)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac a q I x)(*strict*)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(erule_tac
      x="\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>"
      in ballE)
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(erule disjE)
   apply(rename_tac a q qA I)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a q qA I)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(clarsimp)
  apply(rename_tac a q I I1)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(case_tac "cfg_item_rhs2 I")
   apply(rename_tac a q I I1)(*strict*)
   apply(clarsimp)
  apply(rename_tac a q I I1 aa list)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_PARSER_enforces_can_detect_parser_bottom_only_in_Nonblockingness_configurations: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> valid_bounded_parser P (Suc 0)
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> parserS.is_forward_deterministic_accessible P
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> can_detect_parser_bottom_only_in_Nonblockingness_configurations P"
  apply(simp add: can_detect_parser_bottom_only_in_Nonblockingness_configurations_def)
  apply(clarsimp)
  apply(rename_tac d e n)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac d e n)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_before_max_dom)
     apply(rename_tac d e n)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(blast)
    apply(rename_tac d e n)(*strict*)
    apply(blast)
   apply(rename_tac d e n)(*strict*)
   apply(force)
  apply(rename_tac d e n)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac d e n)(*strict*)
   prefer 2
   apply (metis parserS.derivation_initial_is_derivation parserS.some_position_has_details_at_0)
  apply(rename_tac d e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n ea c ca)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca = w @ [parser_bottom (F_PARSER_RITU P)]")
   apply(rename_tac d e n ea c ca)(*strict*)
   prefer 2
   apply(simp add: parserS_configurations_def)
   apply(simp add: F_PARSER_RITU_def)
  apply(rename_tac d e n ea c ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom (F_PARSER_RITU P)]")
   apply(rename_tac d e n ea c ca)(*strict*)
   prefer 2
   apply(simp add: parserS.derivation_initial_def parserS_initial_configurations_def)
   apply(case_tac c)
   apply(rename_tac d e n ea c ca parserS_conf_stacka parserS_conf_schedulera)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e n ea ca parserS_conf_schedulera)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac d e n ea c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n ea c ca w)(*strict*)
  apply(case_tac ca)
  apply(rename_tac d e n ea c ca w parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n ea c w parserS_conf_stack)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d e n ea c wa w)(*strict*)
  apply(subgoal_tac "c \<in> parserS_initial_configurations P")
   apply(rename_tac d e n ea c wa w)(*strict*)
   prefer 2
   apply(simp add: parserS.derivation_initial_def)
  apply(rename_tac d e n ea c wa w)(*strict*)
  apply(simp add: parserS_initial_configurations_def)
  apply(case_tac c)
  apply(rename_tac d e n ea c wa w parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n ea wa w)(*strict*)
  apply(subgoal_tac "\<exists>XSEQ y x. SSrenPHI = \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE SSM (epda_initial SSM) (teB SSDo # XSEQ), parserS_conf_scheduler = y\<rparr> \<and> SSw = x @ y \<and> viable_prefix SSG' (teB SSDo # XSEQ) \<and> length SSrenPIprime = length (tau (parser_marker SSP) SSrenPIprime) + length x \<and> (\<exists>dG e dGn. cfgRM.derivation SSG dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf = SSYSEQ @ liftB x\<rparr>) \<and> get_labels dG dGn = rev (tau (parser_marker SSP) SSrenPIprime))" for SSrenPHI SSM SSw SSG' SSDo SSG SSYSEQ SSP SSrenPIprime)
   apply(rename_tac d e n ea wa w)(*strict*)
   prefer 2
   apply(rule_tac
      YSEQ="[]"
      and w="wa @ [parser_bottom (F_PARSER_RITU P)]"
      in Lemma6__29)
          apply(rename_tac d e n ea wa w)(*strict*)
          apply(force)
         apply(rename_tac d e n ea wa w)(*strict*)
         apply (metis F_CFG_AUGMENT__viable_prefix_Do F_CFG_AUGMENT__input_from_AF_LR_PARSER_input)
        apply(rename_tac d e n ea wa w)(*strict*)
        apply(rule parserS.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac d e n ea wa w)(*strict*)
       apply(force)
      apply(rename_tac d e n ea wa w)(*strict*)
      apply(force)
     apply(rename_tac d e n ea wa w)(*strict*)
     apply(rule parserS.derivation_initial_belongs)
      apply(rename_tac d e n ea wa w)(*strict*)
      apply(simp add: valid_bounded_parser_def)
     apply(rename_tac d e n ea wa w)(*strict*)
     apply(force)
    apply(rename_tac d e n ea wa w)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
      in ssubst)
     apply(rename_tac d e n ea wa w)(*strict*)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(rename_tac d e n ea wa w)(*strict*)
         apply(force)
        apply(rename_tac d e n ea wa w)(*strict*)
        apply(force)
       apply(rename_tac d e n ea wa w)(*strict*)
       apply(force)
      apply(rename_tac d e n ea wa w)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac d e n ea wa w)(*strict*)
     apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(rename_tac d e n ea wa w)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO M (epda_initial M) (teB Do)"
      and s="parser_initial P"
      in ssubst)
     apply(rename_tac d e n ea wa w)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
    apply(rename_tac d e n ea wa w)(*strict*)
    apply(force)
   apply(rename_tac d e n ea wa w)(*strict*)
   apply(force)
  apply(rename_tac d e n ea wa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
  apply(rule_tac
      t="parser_bottom (F_PARSER_RITU P)"
      and s="parser_bottom P"
      in ssubst)
   apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
   apply(force)
  apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
  apply(rule_tac
      d="d"
      in AF_LR_PARSER_just_read_input_not_seen_dollar_Nonblockingness)
                  apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
                  apply(force)
                 apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
                 apply(force)
                apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
                apply(force)
               apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
               apply(force)
              apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
              apply(force)
             apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
             apply(force)
            apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
            apply(force)
           apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
           apply(simp add: parserS.derivation_initial_def)
          apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
          apply(rule parserS.derivation_initial_belongs)
           apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
           apply(simp add: valid_bounded_parser_def)
          apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
          apply(force)
         apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
         apply(force)
        apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
        apply(force)
       apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
       apply(force)
      apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
      apply(force)
     apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
     apply(force)
    apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_PARSER_RITU_def AF_LR_PARSER_def)
   apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
   apply(rule_tac
      t="last (rule_lpop e)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ))"
      in ssubst)
    apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
    apply(force)
   apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
   apply(rule sym)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
         apply(force)
        apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
       apply(force)
      apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
      apply(force)
     apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
     apply(rule_tac
      B="cfg_events G'"
      in two_elements_construct_domain_setA)
     apply(rule set_take_head2)
      apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
     apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
     apply (metis viable_prefix_in_CFG set_subset_Cons subset_trans)
    apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
    apply(rule_tac
      A="cfg_nonterminals G'"
      in two_elements_construct_domain_setB)
    apply(rule set_take_head2)
     apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
    apply (metis viable_prefix_in_CFG set_subset_Cons subset_trans)
   apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
   apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac d e n ea wa XSEQ dG eb dGn)(*strict*)
  apply (metis viable_prefix_in_CFG set_subset_Cons subset_trans)
  done

lemma F_LR_PARSER_initial_not_in_final: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> parser_initial P \<notin> parser_marking P"
  apply(rule_tac
      t="parser_marking P"
      and s="{last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])}"
      in ssubst)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rule_tac
      t="parser_initial P"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(simp (no_asm))
  apply(rule_tac
      t="F_DFA_GOTO M (epda_initial M) (teB Do)"
      and s="last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
   prefer 2
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])"
      in ssubst)
    prefer 2
    apply(subgoal_tac "last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G),teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G),teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G),teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])")
     prefer 2
     apply(rule_tac
      G="G"
      in F_LR_MACHINE_DFAGTOTO_differs)
             apply(simp only: AF_LR_PARSER_input_def)
            apply(simp only: AF_LR_PARSER_input_def)
            apply(force)
           apply(simp only: AF_LR_PARSER_input_def)
          apply(simp only: AF_LR_PARSER_input_def)
         apply(simp only: AF_LR_PARSER_input_def)
        apply(simp only: AF_LR_PARSER_input_def)
       apply(simp only: AF_LR_PARSER_input_def)
      apply(simp only: AF_LR_PARSER_input_def)
     apply(simp only: AF_LR_PARSER_input_def)
    apply(force)
   apply(subgoal_tac "length [teB Do, teA (cfg_initial G)] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
    prefer 2
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(simp add: F_LR_MACHINE_def)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(clarsimp)
     apply(simp add: valid_cfg_def)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
      in ssubst)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(subgoal_tac "length [teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])")
   prefer 2
   apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: F_LR_MACHINE_def)
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(clarsimp)
  apply(force)
  done

theorem F_LRk_PARSER__SOUND: "
  F_LR_PARSER__SpecInput G (G', F, M, k, Do)
  \<Longrightarrow> F_LR_PARSER__SpecOutput G (((\<lambda>G (G', F, M, n, Do) . F_LRk_PARSER G F G' M n Do) G (G', F, M, k, Do)), k)"
  apply(simp add: F_LR_PARSER__SpecOutput_def F_LR_PARSER__SpecInput_def)
  apply(subgoal_tac "AF_LR_PARSER_input G F Do (F_FRESH (cfg_nonterminals G)) G' M (F_LRk_PARSER G F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) k (F_FRESH (cfg_events G))) k")
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def)
   apply(rule F_LRk_PARSER_vs_AF_LR_PARSER)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
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
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(force)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 2
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule_tac parserS_vs_parserFS.preserve_FEdetermR1)
    apply(rule conjI)
     prefer 2
     apply(force)
    apply(simp add: valid_bounded_parser_def)
   apply(rule F_LR_PARSER_is_forward_edge_deterministic_accessible)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule sym)
   apply (metis CFG_lang_rm_lang_equal Lemma6__34 bot_nat_def)
  apply(rule context_conjI)
   apply(rule F_LR_PARSER_initial_not_in_final)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule impI)
   apply(rule_tac
      G="G"
      and G'="G'"
      and Do="Do"
      and S'="F_FRESH (cfg_nonterminals G)"
      and M="M"
      in AF_LR_PARSER_is_PARSERl)
    apply(force)
   apply(force)
  apply(rule impI)
  apply(subgoal_tac "nonblockingness_language (parserS.unmarked_language (F_LRk_PARSER G F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0)) (Suc 0) (F_FRESH (cfg_events G)))) (parserS.marked_language (F_LRk_PARSER G F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F (Suc 0)) (Suc 0) (F_FRESH (cfg_events G))))")
   prefer 2
   apply(rule F_LR_PARSER_nonblockingness_language)
         apply(force)
        apply (metis CFGRM_CFG_translate_Nonblockingness_id)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: valid_bounded_parser_def)
  apply(simp add: nonblockingness_language_def nonblockingness_language_def)
  apply(rule conjI)
   apply (metis FUNRLP_all_rules_pop)
  apply(rule conjI)
   apply (metis F_LR_PARSER_shift_rules_do_not_reach_final_state)
  apply (metis F_LR_PARSER_enforces_can_detect_parser_bottom_only_in_Nonblockingness_configurations F_LR_PARSER_is_forward_edge_deterministic_accessible FUNRLP_all_rules_pop valid_bounded_parser_vs_valid_parser parser_is_forward_edge_deterministic_accessible_implies_is_forward_deterministic_accessible)
  done

theorem F_LR_PARSER__SOUND: "
  F_LR_PARSER__SpecInput G (G', F, M, Suc 0, Do)
  \<Longrightarrow> F_LR_PARSER__SpecOutput G (((\<lambda>G (G', F, M, k, Do). F_LR_PARSER G G' M Do) G (G', F, M, Suc 0, Do)), Suc 0)"
  apply(rule_tac t="(case (G', F, M, Suc 0, Do) of (G', F, M, k, Do) \<Rightarrow> F_LR_PARSER G G' M Do, Suc 0)" and s="(((\<lambda>G (G', F, M, n, Do) . F_LRk_PARSER G F G' M n Do) G (G', F, M, SSk, Do)), SSk)" for SSk in subst)
   prefer 2
   apply(rule F_LRk_PARSER__SOUND)
   apply(force)
  apply(clarsimp)
  apply(simp add: F_LR_PARSER__SpecInput_def)
  apply(clarsimp)
  apply(rule F_LR_PARSER_vs_F_LRk_PARSER)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end
